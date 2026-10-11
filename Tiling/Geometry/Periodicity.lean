import Tiling.Geometry.Plane
import Mathlib.MeasureTheory.Group.AEStabilizer
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Polygonal

def HasFLC {E : Type*} [NormedAddCommGroup E] (S : Set E) : Prop :=
  (∀ Q : Set E, Bornology.IsBounded Q → (S ∩ Q).Finite) ∧
    ∀ R : ℝ, 0 < R → ((S - S) ∩ Metric.closedBall 0 R).Finite

def HasPatchFLC {E : Type*} [NormedAddCommGroup E] (S : Set E) : Prop :=
  ∀ Q : Set E, IsOpen Q → Bornology.IsBounded Q →
    (Set.range fun s : S => (((-(s : E)) +ᵥ S) ∩ Q)).Finite

structure PlanarLattice where
  basis : Fin 2 → Plane
  independent : LinearIndependent ℝ basis

def PlanarLattice.toAddSubgroup (L : PlanarLattice) : AddSubgroup Plane :=
  AddSubgroup.closure (Set.range L.basis)

def periodGroup {E : Type*} [AddCommGroup E] (S : Set E) : AddSubgroup E :=
  AddAction.stabilizer E S

def aePeriodGroup (S : Set Plane) : AddSubgroup Plane :=
  AddAction.aestabilizer Plane volume S

def IsLatticePeriodic (S : Set Plane) : Prop :=
  ∃ L : PlanarLattice, (L.toAddSubgroup : Set Plane) ⊆ periodGroup S

def IsQuasiPeriodic (S : Set Plane) : Prop :=
  ∃ (n : ℕ) (part : Fin n → Set Plane),
    (∀ i, (part i).Nonempty ∧ IsLatticePeriodic (part i)) ∧
    Set.PairwiseDisjoint Set.univ part ∧ (⋃ i, part i) = S

def IsInvariantAlong (D : Set Plane) (δ : Submodule ℝ Plane) : Prop :=
  ∀ u ∈ δ, u +ᵥ D = D

/-- Literal invariance under translations by the given period. -/
def RelativeDense (S : Set Plane) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, ∃ s ∈ S, dist z s < ρ

theorem hasPatchFLC_iff_hasFLC
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E] {S : Set E}
    (hlocal : ∀ Q : Set E, Bornology.IsBounded Q → (S ∩ Q).Finite) :
    HasPatchFLC S ↔ HasFLC S := by
  classical
  constructor
  · intro hpatch
    refine ⟨hlocal, ?_⟩
    intro R hR
    let Q : Set E := Metric.ball 0 (R + 1)
    let P : Set (Set E) := Set.range fun s : S => ((-(s : E)) +ᵥ S) ∩ Q
    have hP : P.Finite := hpatch Q Metric.isOpen_ball Metric.isBounded_ball
    have heach : ∀ p ∈ P, p.Finite := by
      rintro p ⟨s, rfl⟩
      have hfin := hlocal ((s : E) +ᵥ Q) (Metric.isBounded_ball.vadd (s : E))
      apply (hfin.image fun x => -(s : E) + x).subset
      rintro x ⟨⟨y, hy, rfl⟩, hxQ⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      exact ⟨-(s : E) +ᵥ y, hxQ, by simp [vadd_eq_add]⟩
    apply (hP.sUnion heach).subset
    rintro x ⟨⟨s, hs, t, ht, rfl⟩, hball⟩
    refine Set.mem_sUnion.mpr ⟨((-(t : E)) +ᵥ S) ∩ Q,
      ⟨⟨t, ht⟩, rfl⟩, ?_⟩
    refine ⟨⟨s, hs, by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩, ?_⟩
    exact Metric.closedBall_subset_ball (by linarith) hball
  · intro hS Q _hQopen hQ
    obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
    let R' := max R 0 + 1
    have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 0]
    let D := (S - S) ∩ Metric.closedBall (0 : E) R'
    have hD : D.Finite := hS.2 R' hR'
    apply hD.finite_subsets.subset
    rintro p ⟨s, rfl⟩ x ⟨hxS, hxQ⟩
    obtain ⟨t, ht, rfl⟩ := hxS
    refine ⟨⟨t, ht, s, s.2, by simp [vadd_eq_add, sub_eq_add_neg, add_comm]⟩, ?_⟩
    exact Metric.closedBall_subset_closedBall (by
      dsimp [R']; linarith [le_max_left R 0]) (hR hxQ)

theorem HasFLC.vadd
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) (u : E) : HasFLC (u +ᵥ S) := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    have hfinite := hS.1 ((-u) +ᵥ Q) (hQ.vadd (-u))
    apply (hfinite.image fun s ↦ u + s).subset
    rintro x ⟨hxS, hxQ⟩
    obtain ⟨s, hs, rfl⟩ := hxS
    refine ⟨s, ⟨hs, ?_⟩, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using hxQ
  · have hdif : (u +ᵥ S) - (u +ᵥ S) = S - S := by
      ext x
      constructor
      · rintro ⟨a, ⟨s, hs, rfl⟩, b, ⟨t, ht, rfl⟩, rfl⟩
        exact ⟨s, hs, t, ht, by
          change s - t = (u + s) - (u + t)
          abel⟩
      · rintro ⟨s, hs, t, ht, rfl⟩
        exact ⟨u + s, ⟨s, hs, rfl⟩, u + t, ⟨t, ht, rfl⟩, by
          change (u + s) - (u + t) = s - t
          abel⟩
    rw [hdif]
    exact hS.2

theorem HasFLC.mono
    {E : Type*} [NormedAddCommGroup E] {S T : Set E}
    (hT : HasFLC T) (hST : S ⊆ T) : HasFLC S := by
  refine ⟨fun Q hQ => (hT.1 Q hQ).subset (Set.inter_subset_inter_left Q hST), ?_⟩
  intro R hR
  exact (hT.2 R hR).subset (Set.inter_subset_inter_left _ (Set.sub_subset_sub hST hST))

theorem HasFLC.differences_locallyFinite
    {E : Type*} [NormedAddCommGroup E]
    {S : Set E} (hS : HasFLC S) :
    ∀ Q : Set E, Bornology.IsBounded Q → ((S - S) ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
  let R' := max R 0 + 1
  have hR' : 0 < R' := by dsimp [R']; linarith [le_max_right R 0]
  apply (hS.2 R' hR').subset
  exact inter_subset_inter_right _
    (hR.trans (Metric.closedBall_subset_closedBall (by
      dsimp [R']
      linarith [le_max_left R 0])))

private theorem finite_inter_add_finset
    {E : Type*} [NormedAddCommGroup E]
    {A : Set E}
    (hA : ∀ Q : Set E, Bornology.IsBounded Q → (A ∩ Q).Finite)
    (F : Finset E) (Q : Set E) (hQ : Bornology.IsBounded Q) :
    ((A + (F : Set E)) ∩ Q).Finite := by
  have hadd : A + (F : Set E) = ⋃ f : (F : Set E), (f : E) +ᵥ A := by
    ext x
    constructor
    · rintro ⟨a, ha, f, hf, rfl⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨f, hf⟩, a, ha, by simp [vadd_eq_add, add_comm]⟩
    · rw [Set.mem_iUnion]
      rintro ⟨f, a, ha, rfl⟩
      exact ⟨a, ha, f, f.2, by simp [vadd_eq_add, add_comm]⟩
  rw [hadd, iUnion_inter]
  apply Set.finite_iUnion
  intro f
  have hfinite := hA ((-(f : E)) +ᵥ Q) (hQ.vadd (-(f : E)))
  apply (hfinite.image fun a ↦ (f : E) + a).subset
  rintro x ⟨⟨a, ha, rfl⟩, hxaQ⟩
  refine ⟨a, ⟨ha, ?_⟩, rfl⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [vadd_eq_add] using hxaQ

theorem HasFLC.add_finset
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) (F : Finset E) :
    HasFLC (S + (F : Set E)) := by
  classical
  refine ⟨fun Q hQ ↦ finite_inter_add_finset hS.1 F Q hQ, ?_⟩
  intro R hR
  let G : Finset E := F.image₂ (· - ·) F
  have hsubset :
      (S + (F : Set E)) - (S + (F : Set E)) ⊆ (S - S) + (G : Set E) := by
    rintro x ⟨a, ⟨s, hs, f, hf, rfl⟩, b, ⟨t, ht, g, hg, rfl⟩, rfl⟩
    refine ⟨s - t, ⟨s, hs, t, ht, rfl⟩, f - g, ?_, ?_⟩
    · exact Finset.mem_image₂.mpr ⟨f, hf, g, hg, rfl⟩
    · change (s - t) + (f - g) = (s + f) - (t + g)
      abel
  apply (finite_inter_add_finset
    (hS.differences_locallyFinite) G (Metric.closedBall 0 R)
      Metric.isBounded_closedBall).subset
  exact inter_subset_inter_left _ hsubset

theorem HasFLC.uniformlyDiscrete
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S : Set E} (hS : HasFLC S) :
    ∃ δ : ℝ, 0 < δ ∧ S.Pairwise (fun s t => δ ≤ dist s t) := by
  let D : Set E := ((S - S) ∩ Metric.closedBall 0 1) \ {0}
  have hDfinite : D.Finite := (hS.2 1 one_pos).subset sdiff_subset
  have h0D : (0 : E) ∉ D := by simp [D]
  have hnhds : Dᶜ ∈ 𝓝 (0 : E) :=
    hDfinite.isClosed.isOpen_compl.mem_nhds h0D
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let δ := min r 1
  have hδ : 0 < δ := lt_min hr one_pos
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  by_contra hdist
  have hdist_lt : dist s t < δ := lt_of_not_ge hdist
  let d := s - t
  have hdne : d ≠ 0 := sub_ne_zero.mpr hst
  have hdmem : d ∈ S - S := ⟨s, hs, t, ht, rfl⟩
  have hdnorm : ‖d‖ = dist s t := by simp [d, dist_eq_norm]
  have hdclosed : d ∈ Metric.closedBall (0 : E) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, hdnorm]
    exact hdist_lt.le.trans (min_le_right _ _)
  have hdD : d ∈ D := ⟨⟨hdmem, hdclosed⟩, by simpa using hdne⟩
  have hdball : d ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, hdnorm]
    exact hdist_lt.trans_le (min_le_left _ _)
  exact (hball hdball) hdD

theorem rankTwo_of_flcCoset_and_independentRationalImages
    {P V : Set Plane} {lambda gamma : Plane} (hP : HasFLC P) (hV : V.Finite)
    (f : Plane →ₗ[ℚ] Plane) (hfind : LinearIndependent ℚ ![f lambda, f gamma])
    (hcoset : ∃ v : Plane,
      {x : Plane | ∃ m n : ℤ, x = v + m • lambda + n • gamma} ⊆ V + P) :
    LinearIndependent ℝ ![lambda, gamma] := by
  classical
  have hQ : HasFLC (V + P) := by
    simpa [hV.coe_toFinset, add_comm] using hP.add_finset hV.toFinset
  obtain ⟨delta, hdelta, hsep⟩ := hQ.uniformlyDiscrete
  have hlambda : lambda ≠ 0 := by
    intro hzero
    have hfzero : f lambda = 0 := by simp [hzero]
    have hbad := hfind.eq_zero_of_pair (s := (1 : ℚ)) (t := (0 : ℚ))
      (by simp [hfzero])
    exact one_ne_zero hbad.1
  by_contra hli
  have hrel_data : ∃ (a b : ℝ),
      (a ≠ 0 ∨ b ≠ 0) ∧ a • lambda + b • gamma = 0 := by
    have hdep : ∃ g : Fin 2 → ℝ,
        (∑ i, g i • ![lambda, gamma] i = 0) ∧ ∃ i, g i ≠ 0 :=
      (Fintype.not_linearIndependent_iff (v := ![lambda, gamma])).mp hli
    obtain ⟨g, hg, hgzero⟩ := hdep
    have hrel' : g 0 • lambda + g 1 • gamma = 0 := by
      simpa [Fin.sum_univ_two] using hg
    have hab' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
      obtain ⟨i, hi⟩ := hgzero
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    exact ⟨g 0, g 1, hab', hrel'⟩
  obtain ⟨a, b, hab, hrel⟩ := hrel_data
  have hb : b ≠ 0 := by
    intro hb
    have hal : a • lambda = 0 := by simpa [hb] using hrel
    have ha : a ≠ 0 := by
      intro ha
      exact hab.elim (fun h => h ha) (fun h => h hb)
    exact hlambda ((smul_eq_zero.mp hal).resolve_left ha)
  let r : ℝ := -a / b
  have hratio : gamma = r • lambda := by
    have hbg : b • gamma = -(a • lambda) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hrel)
    calc
      gamma = (1 : ℝ) • gamma := by simp
      _ = (b⁻¹ * b) • gamma := by rw [inv_mul_cancel₀ hb]
      _ = b⁻¹ • (b • gamma) := by rw [mul_smul]
      _ = b⁻¹ • (-(a • lambda)) := by rw [hbg]
      _ = r • lambda := by
        dsimp [r]
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hri : Irrational r := by
    rw [irrational_iff_ne_rational]
    intro a b hb hq
    let q : ℚ := a / b
    have hqreal : r = (q : ℝ) := by
      dsimp [q]
      simpa using hq
    have hqrel : gamma = q • lambda := by
      calc
        gamma = r • lambda := hratio
        _ = (q : ℝ) • lambda := by rw [hqreal]
        _ = q • lambda := Rat.cast_smul_eq_qsmul ℝ q lambda
    have hfq : f gamma = (q : ℚ) • f lambda := by
      rw [hqrel, map_smul]
    have hzero : (q : ℚ) • f lambda + (-1 : ℚ) • f gamma = 0 := by
      rw [hfq]
      module
    have hbad := hfind.eq_zero_of_pair hzero
    norm_num at hbad
  have hnormlambda : 0 < ‖lambda‖ := norm_pos_iff.mpr hlambda
  -- Irrational dependence creates arbitrarily small nonzero integer combinations.
  have hdense : Dense (AddSubgroup.closure ({r, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr (by simpa using hri)
  obtain ⟨z, hzmem, hz⟩ := hdense.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr (div_pos hdelta hnormlambda))
  obtain ⟨n, m, hnm⟩ := AddSubgroup.mem_closure_pair.mp hzmem
  have hzcomb : (n : ℝ) * r + (m : ℝ) = z := by
    simpa [zsmul_eq_mul] using hnm
  let c : Plane := m • lambda + n • gamma
  have hcomb_eq : c = z • lambda := by
    dsimp [c]
    rw [hratio, ← Int.cast_smul_eq_zsmul ℝ, ← Int.cast_smul_eq_zsmul ℝ,
      smul_smul, ← add_smul]
    congr 1
    linarith [hzcomb]
  have hcomb_ne : c ≠ 0 := by
    rw [hcomb_eq]
    exact smul_ne_zero (ne_of_gt hz.1) hlambda
  obtain ⟨v, hv⟩ := hcoset
  let x : Plane := c + v
  have hxQ : x ∈ V + P := by
    apply hv
    refine ⟨m, n, ?_⟩
    dsimp [x, c]
    ac_rfl
  have hvQ : v ∈ V + P := hv ⟨0, 0, by simp⟩
  have hxne : x ≠ v := by
    intro hxeq
    apply hcomb_ne
    exact add_right_cancel (show c + v = 0 + v by simpa [x] using hxeq)
  have hdist : dist x v < delta := by
    change dist (c + v) v < delta
    rw [← vadd_eq_add, dist_vadd_left, hcomb_eq, norm_smul, Real.norm_eq_abs,
      abs_of_pos hz.1]
    exact (lt_div_iff₀ hnormlambda).mp hz.2
  exact (not_lt_of_ge (hsep hxQ hvQ hxne)) hdist

theorem planarLattice_boundedCosetRepresentative (L : PlanarLattice) :
    ∃ R : ℝ, 0 < R ∧ ∀ x : Plane,
      ∃ g ∈ L.toAddSubgroup, ‖x - g‖ ≤ R := by
  classical
  let b : Module.Basis (Fin 2) ℝ Plane :=
    basisOfLinearIndependentOfCardEqFinrank L.independent
      (by simp [Complex.finrank_real_complex])
  have hb : (b : Fin 2 → Plane) = L.basis :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let R : ℝ := 1 + ∑ i : Fin 2, ‖L.basis i‖
  refine ⟨R, by
    dsimp [R]
    linarith [Finset.sum_nonneg (fun i (_hi : i ∈ (Finset.univ : Finset (Fin 2))) =>
      norm_nonneg (L.basis i))], ?_⟩
  intro x
  let c : Fin 2 → ℝ := b.repr x
  let g : Plane := ∑ i : Fin 2, (Int.floor (c i) : ℝ) • L.basis i
  have hg : g ∈ L.toAddSubgroup := by
    apply L.toAddSubgroup.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul]
    apply AddSubgroup.zsmul_mem
    exact AddSubgroup.subset_closure (Set.mem_range_self i)
  refine ⟨g, hg, ?_⟩
  have hx : x = ∑ i : Fin 2, c i • L.basis i := by
    rw [← hb]
    exact (b.sum_repr x).symm
  change ‖x - ∑ i : Fin 2, (Int.floor (c i) : ℝ) • L.basis i‖ ≤ R
  rw [hx, ← Finset.sum_sub_distrib]
  simp only [← sub_smul]
  calc
    ‖∑ i : Fin 2, (c i - (Int.floor (c i) : ℝ)) • L.basis i‖
        ≤ ∑ i : Fin 2, ‖(c i - (Int.floor (c i) : ℝ)) • L.basis i‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 2, ‖L.basis i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs]
      have hlo := Int.floor_le (c i)
      have hhi := Int.lt_floor_add_one (c i)
      have habs : |c i - (Int.floor (c i) : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      exact mul_le_of_le_one_left (norm_nonneg _) habs
    _ ≤ R := by dsimp [R]; linarith

/-- Root-authorized Part-II reusable seam; exact frozen candidate type, not yet proved. -/
theorem periodicOpen_inclusion_commensurable :
∀ (A B : Set ℝ) (β γ : ℝ), IsOpen A → A.Nonempty → IsOpen B →
    B ≠ Set.univ → A ⊆ B → 0 < β → 0 < γ →
    β ∈ periodGroup B → γ ∈ periodGroup A →
      ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (m : ℝ) * β = (n : ℝ) * γ
  := by
  intro A B β γ hA hAn hB hBproper hAB hβ hγ hβper hγper
  by_contra hcomm
  have hratio : Irrational (γ / β) := by
    intro hnrat
    change γ / β ∈ Set.range ((↑) : ℚ → ℝ) at hnrat
    obtain ⟨q, hq⟩ := hnrat
    have hqpos : 0 < (q : ℝ) := by
      rw [hq]
      exact div_pos hγ hβ
    have hqpos' : 0 < q := by exact_mod_cast hqpos
    have hnumpos : 0 < q.num := Rat.num_pos.mpr hqpos'
    have hmpos : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnumpos.ne'
    have hnpos : 0 < q.den := q.den_pos
    have hnumcast : ((q.num.natAbs : ℕ) : ℝ) = (q.num : ℝ) := by
      rw [Nat.cast_natAbs, abs_of_nonneg hnumpos.le]
    have hqrepr : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      simp [Rat.cast_def]
    have hratio' : γ / β = (q.num : ℝ) / (q.den : ℝ) := by
      rw [hq.symm, hqrepr]
    have hmul : (q.den : ℝ) * γ = (q.num : ℝ) * β := by
      field_simp [ne_of_gt hβ, Nat.cast_ne_zero.mpr hnpos.ne'] at hratio'
      nlinarith [hratio']
    apply hcomm
    refine ⟨q.num.natAbs, q.den, hmpos, hnpos, ?_⟩
    simpa [hnumcast] using hmul.symm
  have hdense : Dense (AddSubgroup.closure ({γ, β} : Set ℝ) : Set ℝ) :=
    (dense_addSubgroupClosure_pair_iff (a := γ) (b := β)).mpr hratio
  have hBuniv : B = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro y
    obtain ⟨a, ha⟩ := hAn
    let U : Set ℝ := {x | y - x ∈ A}
    have hUopen : IsOpen U := by
      dsimp [U]
      exact hA.preimage (continuous_const.sub continuous_id)
    have hUnonempty : U.Nonempty := ⟨y - a, by simp [U, ha]⟩
    obtain ⟨x, hxH, hxU⟩ := hdense.exists_mem_open hUopen hUnonempty
    have hxA : y - x ∈ A := hxU
    have hxB : x +ᵥ A ⊆ B := by
      intro z hz
      obtain ⟨m, n, hmn⟩ := AddSubgroup.mem_closure_pair.mp hxH
      have hmA : m • γ ∈ periodGroup A := (periodGroup A).zsmul_mem hγper m
      have hnB : n • β ∈ periodGroup B := (periodGroup B).zsmul_mem hβper n
      have hmA' : (m • γ) +ᵥ A = A := by
        simpa [periodGroup] using hmA
      have hnB' : (n • β) +ᵥ B = B := by
        simpa [periodGroup] using hnB
      change ∃ a ∈ A, x + a = z at hz
      obtain ⟨a, ha, rfl⟩ := hz
      have hma : m • γ + a ∈ A := by
        have : m • γ +ᵥ a ∈ (m • γ) +ᵥ A := ⟨a, ha, rfl⟩
        rw [hmA'] at this
        simpa using this
      have hna : n • β + (m • γ + a) ∈ B := by
        have : m • γ + a ∈ B := hAB hma
        have ht : n • β +ᵥ (m • γ + a) ∈ (n • β) +ᵥ B := ⟨_, this, rfl⟩
        rw [hnB'] at ht
        simpa using ht
      rw [← hmn]
      simpa [add_assoc, add_comm, add_left_comm] using hna
    have hyB : y ∈ B := by
      have : x + (y - x) ∈ B := hxB ⟨y - x, hxA, rfl⟩
      simpa using this
    exact hyB
  exact hBproper hBuniv

theorem periodicRegularOpen_translatedContainment :
∀ (D : Set Plane), IsOpen D → interior (closure D) = D → IsLatticePeriodic D →
    ∀ a : Plane, a +ᵥ D ⊆ D → a +ᵥ D = D
  := by
  classical
  intro D hDopen hDreg hDperiod a ha
  obtain ⟨L, hL⟩ := hDperiod
  have hp (u : Plane) (hu : u ∈ L.toAddSubgroup) : u +ᵥ D = D :=
    AddAction.mem_stabilizer_iff.mp (hL hu)
  have hn (n : ℕ) : ∀ x ∈ D, n • a + x ∈ D := by
    induction n with
    | zero => intro x hx; simpa only [zero_nsmul, zero_add] using hx
    | succ n ih =>
      intro x hx
      have hm : a + (n • a + x) ∈ D := ha ⟨n • a + x, ih x hx, rfl⟩
      simpa only [succ_nsmul, add_assoc, add_comm, add_left_comm] using hm
  obtain ⟨R, hR, hrep⟩ := planarLattice_boundedCosetRepresentative L
  -- Compact recurrence of lattice-reduced multiples provides approximate backward shifts.
  choose g hg hgbound using fun n : ℕ => hrep (n • a)
  let r : ℕ → Plane := fun n => n • a - g n
  have hrbound : ∀ n, r n ∈ Metric.closedBall (0 : Plane) R := by
    intro n
    simpa [r, Metric.mem_closedBall, dist_zero_right] using hgbound n
  obtain ⟨z, _hz, φ, hφ, hlim⟩ :=
    (ProperSpace.isCompact_closedBall (0 : Plane) R).tendsto_subseq hrbound
  have hnext : Tendsto (fun n => r (φ (n + 1))) atTop (𝓝 z) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun n => r (φ (n + 1)) - r (φ n) - a)
      atTop (𝓝 (-a)) := by
    simpa using (hnext.sub hlim).sub_const a
  have hsub : -a +ᵥ D ⊆ closure D := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_closure_of_tendsto (hdiff.add_const x)
    apply Filter.Eventually.of_forall
    intro n
    let k : ℕ := φ (n + 1) - φ n - 1
    have hk : φ (n + 1) = φ n + k + 1 := by
      have hstep : φ n < φ (n + 1) := hφ (by omega)
      dsimp [k]
      omega
    have hshift : r (φ (n + 1)) - r (φ n) - a =
        (g (φ n) - g (φ (n + 1))) + k • a := by
      dsimp [r]
      rw [hk, add_nsmul, add_nsmul, one_nsmul]
      abel
    rw [hshift, add_assoc]
    rw [← hp (g (φ n) - g (φ (n + 1))) (L.toAddSubgroup.sub_mem (hg _) (hg _))]
    exact ⟨k • a + x, hn k x hx, rfl⟩
  have hneg : -a +ᵥ D ⊆ D := by
    simpa only [hDreg] using (hDopen.vadd (-a)).subset_interior_iff.mpr hsub
  apply Set.Subset.antisymm ha
  intro x hx
  exact ⟨-a + x, hneg ⟨x, hx, rfl⟩, by simp [vadd_eq_add]⟩


end Tiling.Polygonal
