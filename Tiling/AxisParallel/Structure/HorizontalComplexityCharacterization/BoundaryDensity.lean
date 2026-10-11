import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Structure.HorizontalBoundaryChains
import Tiling.AxisParallel.Structure.PlateThickness
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.EdgeOffsets

/-!
# Horizontal boundary density

Closed-support coverage, complete component-boundary lines, and finite signed
boundary-step words imply finite horizontal complexity when component
boundaries are relatively dense.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Bornology Function Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel

private abbrev NontrivialDecomposition
    (K : Region) (T : Set Tiling.Plane) : Prop :=
  ¬ ∃ P : Continuous.VerticalPlate K T,
    ¬ Continuous.IsVerticalColumn P ∧ P.centres = T

private def adjacentGapSet (z : ℤ → ℝ) : Set ℝ :=
  {g : ℝ | ∃ i : ℤ, g = z (i + 1) - z i}

private def closedSupportUnion (K : Region) (T : Set Tiling.Plane) :
    Set Tiling.Plane :=
  ⋃ t : ↥T, (t.1 : Tiling.Plane) +ᵥ K.support

private theorem closedTranslatedSupports_cover :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → closedSupportUnion K T = univ := by
  intro K T hTile
  have hSupport : regularSupport K T = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
  have hClosure : closure (openUnion K T) = closedSupportUnion K T :=
    closure_openUnion_eq_iUnion_support hTile.2.1
  apply Set.Subset.antisymm (fun _ _ ↦ Set.mem_univ _)
  intro z _
  rw [← hClosure]
  apply interior_subset
  change z ∈ regularSupport K T
  rw [hSupport]
  exact Set.mem_univ z

private theorem fixedHorizontalLine_closedSupportCover :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → ∀ y : ℝ,
        {z : Tiling.Plane | z.im = y} ⊆ closedSupportUnion K T := by
  intro K T hTile y z _
  rw [closedTranslatedSupports_cover hTile]
  exact Set.mem_univ z

theorem componentBoundaryLine_subset_translatedFrontiers :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      ∀ c ∈ componentBoundarySet K T,
        {z : Tiling.Plane | z.re = c} ⊆
          ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  intro K T hTile c hc z hz
  rw [componentBoundarySet_eq] at hc
  obtain ⟨P, hcP⟩ := Set.mem_iUnion.mp hc
  have hBaseDisjoint (Q : Continuous.VerticalPlate K T) (hPQ : P ≠ Q) :
      Disjoint P.base Q.base := by
    let _ : Countable T := hTile.1.to_subtype
    let _ : Countable (Continuous.VerticalPlate K T) := by
      apply Function.Surjective.countable
        (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
      intro R
      obtain ⟨r, hr⟩ := R.nonempty_supp
      refine ⟨r, ?_⟩
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr
    have hSupportDisjoint : Disjoint P.support Q.support := by
      have hPartition := regularSupport_pairwiseDisjoint
        (@Continuous.VerticalPlate.centres K T)
        (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
        (Continuous.iUnion_verticalPlateCentres K T) hTile
      exact hPartition.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
    obtain ⟨-, hPSupport⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile P
    obtain ⟨-, hQSupport⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile Q
    rw [Set.disjoint_left]
    intro r hrP hrQ
    let q : Tiling.Plane := ⟨r, 0⟩
    have hqP : q ∈ P.support := by
      rw [hPSupport]
      exact hrP
    have hqQ : q ∈ Q.support := by
      rw [hQSupport]
      exact hrQ
    exact Set.disjoint_left.mp hSupportDisjoint hqP hqQ
  have hcNotBase (Q : Continuous.VerticalPlate K T) : c ∉ Q.base := by
    obtain ⟨hPRegular, -⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile P
    have hPBaseOpen : IsOpen P.base := by
      rw [hPRegular]
      exact isOpen_interior
    by_cases hPQ : P = Q
    · subst Q
      intro hcBase
      exact hcP.2 (by rwa [hPBaseOpen.interior_eq])
    · intro hcQ
      obtain ⟨hQRegular, -⟩ :=
        Continuous.VerticalPlate.support_isVerticalSlab hTile Q
      have hQBaseOpen : IsOpen Q.base := by
        rw [hQRegular]
        exact isOpen_interior
      have hMeet : (Q.base ∩ P.base).Nonempty :=
        (mem_closure_iff.mp (frontier_subset_closure hcP))
          Q.base hQBaseOpen hcQ
      obtain ⟨r, hrQ, hrP⟩ := hMeet
      exact Set.disjoint_left.mp (hBaseDisjoint Q hPQ) hrP hrQ
  have hzCover : z ∈ closedSupportUnion K T := by
    rw [closedTranslatedSupports_cover hTile]
    exact Set.mem_univ z
  rw [closedSupportUnion, Set.mem_iUnion] at hzCover
  obtain ⟨t, hzt⟩ := hzCover
  rw [Set.mem_iUnion]
  refine ⟨t, ?_⟩
  rw [frontier, (K.isPolygonal.isClosed.vadd (t.1 : Tiling.Plane)).closure_eq]
  refine ⟨hzt, ?_⟩
  intro hzInterior
  let Q : Continuous.VerticalPlate K T :=
    Continuous.VerticalPlate.ofCentre (K := K) t
  have htQ : (t.1 : Tiling.Plane) ∈ Q.centres :=
    Continuous.VerticalPlate.mem_centres_ofCentre t
  have hzOpen : z ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    change z ∈ (t.1 : Tiling.Plane) +ᵥ interior K.support
    rw [← interior_vadd]
    exact hzInterior
  have hzUnion : z ∈ openUnion K Q.centres := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨t.1, htQ⟩, hzOpen⟩
  have hUnionOpen : IsOpen (openUnion K Q.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q : Q.centres ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _ isOpen_interior
  have hzSupport : z ∈ Q.support := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport, regularSupport]
    exact interior_maximal subset_closure hUnionOpen hzUnion
  apply hcNotBase Q
  rw [Continuous.VerticalPlate.base_eq]
  exact ⟨z, hzSupport, hz⟩

private theorem componentBoundary_completeTranslatedBoundaryLine :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      ∀ c ∈ componentBoundarySet K T,
        {z : Tiling.Plane | z.re = c} ⊆
          ⋃ t : ↥T, frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  intro K T hTile _hNontrivial
  exact componentBoundaryLine_subset_translatedFrontiers hTile

private theorem finiteSignedStepWordValues :
    ∀ (G : Finset ℝ) (N : ℕ),
      {x : ℝ | ∃ (sgn : Fin 2) (n : Fin (N + 1)) (w : Fin n.1 → ℝ),
        (∀ i, w i ∈ G) ∧
        x = if sgn = 0 then ∑ i, w i else -∑ i, w i}.Finite := by
  intro G N
  let Code := Fin 2 × (Σ n : Fin (N + 1), Fin n.1 → ↥(G : Set ℝ))
  let value : Code → ℝ := fun code ↦
    if code.1 = 0 then ∑ i, (code.2.2 i : ℝ)
    else -∑ i, (code.2.2 i : ℝ)
  apply (Set.finite_range value).subset
  rintro x ⟨sgn, n, w, hw, rfl⟩
  let w' : Fin n.1 → ↥(G : Set ℝ) := fun i ↦ ⟨w i, hw i⟩
  refine ⟨(sgn, ⟨n, w'⟩), ?_⟩
  dsimp only [value, w']

private theorem adjacent_gap_lt_two_mul
    {Z : Set ℝ} (z : ℤ → ℝ) (hmono : StrictMono z)
    (hrange : Set.range z = Z)
    {M : ℝ} (hrel : ∀ x : ℝ, ∃ a ∈ Z, |a - x| < M)
    (i : ℤ) : z (i + 1) - z i < 2 * M := by
  have hstep : z i < z (i + 1) := hmono (by omega)
  obtain ⟨a, haZ, ha⟩ := hrel ((z i + z (i + 1)) / 2)
  rw [← hrange] at haZ
  obtain ⟨j, rfl⟩ := haZ
  rcases le_or_gt j i with hji | hij
  · have hzle : z j ≤ z i := hmono.monotone hji
    have hgap : (z (i + 1) - z i) / 2 ≤
        |z j - (z i + z (i + 1)) / 2| := by
      rw [abs_of_nonpos] <;> linarith
    linarith
  · have hij' : i + 1 ≤ j := by omega
    have hzle : z (i + 1) ≤ z j := hmono.monotone hij'
    have hgap : (z (i + 1) - z i) / 2 ≤
        |z j - (z i + z (i + 1)) / 2| := by
      rw [abs_of_nonneg] <;> linarith
    linarith

private theorem finite_adjacent_gaps_of_hasFLC
    {Z : Set ℝ} (z : ℤ → ℝ)
    (hmono : StrictMono z) (hrange : Set.range z = Z)
    (hrelDense : ∃ M : ℝ, 0 < M ∧
      ∀ x : ℝ, ∃ a ∈ Z, |a - x| < M)
    (hflc : Tiling.AxisParallel.HasFLC Z) :
    {g : ℝ | ∃ i : ℤ, g = z (i + 1) - z i}.Finite := by
  obtain ⟨M, hM, hrel⟩ := hrelDense
  apply (hflc.2 (2 * M) (by positivity)).subset
  intro g hg
  obtain ⟨i, rfl⟩ := hg
  have hgap : 0 < z (i + 1) - z i := sub_pos.mpr (hmono (by omega))
  refine ⟨?_, ?_⟩
  · refine ⟨z (i + 1), ?_, z i, ?_, rfl⟩
    · rw [← hrange]
      exact Set.mem_range_self _
    · rw [← hrange]
      exact Set.mem_range_self _
  · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_of_pos hgap]
    exact (adjacent_gap_lt_two_mul z hmono hrange hrel i).le

private theorem sum_adjacent_gaps (z : ℤ → ℝ) (i : ℤ) :
    ∀ n : ℕ,
      z (i + (n : ℤ)) - z i =
        ∑ k ∈ Finset.range n,
          (z (i + (k + 1 : ℕ)) - z (i + (k : ℕ))) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      calc
        z (i + ((n : ℤ) + 1)) - z i =
            (z (i + (n : ℤ)) - z i) +
              (z (i + ((n : ℤ) + 1)) - z (i + (n : ℤ))) := by ring
        _ = ∑ k ∈ Finset.range n,
              (z (i + (k + 1 : ℕ)) - z (i + (k : ℕ))) +
              (z (i + ((n : ℤ) + 1)) - z (i + (n : ℤ))) := by rw [ih]

private theorem nat_mul_le_difference
    (z : ℤ → ℝ) {delta : ℝ}
    (hdelta : ∀ i : ℤ, delta ≤ z (i + 1) - z i)
    (i : ℤ) (n : ℕ) :
    (n : ℝ) * delta ≤ z (i + (n : ℤ)) - z i := by
  rw [sum_adjacent_gaps]
  calc
    (n : ℝ) * delta = ∑ _k ∈ Finset.range n, delta := by simp
    _ ≤ ∑ k ∈ Finset.range n,
        (z (i + (k + 1 : ℕ)) - z (i + (k : ℕ))) := by
      apply Finset.sum_le_sum
      intro k _hk
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by omega
      rw [hcast, ← add_assoc]
      exact hdelta (i + (k : ℤ))

private theorem bounded_differences_finite_of_finite_adjacent_gaps
    (z : ℤ → ℝ) (hmono : StrictMono z)
    (hG : {g : ℝ | ∃ i : ℤ, g = z (i + 1) - z i}.Finite)
    (R : ℝ) (_hR : 0 < R) :
    ((Set.range z - Set.range z) ∩ Metric.closedBall 0 R).Finite := by
  let G : Set ℝ := {g : ℝ | ∃ i : ℤ, g = z (i + 1) - z i}
  have hGne : G.Nonempty := ⟨z (0 + 1) - z 0, 0, rfl⟩
  have hGfinne : hG.toFinset.Nonempty :=
    (Set.Finite.toFinset_nonempty hG).2 (by simpa [G] using hGne)
  let delta : ℝ := hG.toFinset.min' hGfinne
  have hdeltaMemFin : delta ∈ hG.toFinset :=
    Finset.min'_mem hG.toFinset hGfinne
  have hdeltaMem : delta ∈ G := by
    simpa [G] using (Set.Finite.mem_toFinset hG).mp hdeltaMemFin
  have hdeltaPos : 0 < delta := by
    obtain ⟨i, hi⟩ := hdeltaMem
    rw [hi]
    exact sub_pos.mpr (hmono (by omega))
  have hdeltaLe : ∀ i : ℤ, delta ≤ z (i + 1) - z i := by
    intro i
    apply Finset.min'_le
    exact (Set.Finite.mem_toFinset hG).mpr ⟨i, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_gt (R / delta)
  have hG' : G.Finite := by simpa [G] using hG
  let _ : Fintype ↥G := hG'.fintype
  let Code := Fin 2 × (Σ n : Fin (N + 1), Fin n.1 → ↥G)
  let value : Code → ℝ := fun code ↦
    if code.1 = 0 then ∑ k, (code.2.2 k : ℝ)
    else -∑ k, (code.2.2 k : ℝ)
  apply (Set.finite_range value).subset
  intro d hd
  rcases hd.1 with ⟨x, ⟨j, rfl⟩, y, ⟨i, rfl⟩, rfl⟩
  have hball : |z j - z i| ≤ R := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hd.2
  rcases le_total i j with hij | hji
  · let n : ℕ := (j - i).toNat
    have hncast : (n : ℤ) = j - i :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hij)
    have hijn : i + (n : ℤ) = j := by rw [hncast]; omega
    have hnonneg : 0 ≤ z j - z i := sub_nonneg.mpr (hmono.monotone hij)
    have hmul : (n : ℝ) * delta ≤ R := by
      calc
        (n : ℝ) * delta ≤ z (i + (n : ℤ)) - z i :=
          nat_mul_le_difference z hdeltaLe i n
        _ = z j - z i := by rw [hijn]
        _ = |z j - z i| := (abs_of_nonneg hnonneg).symm
        _ ≤ R := hball
    have hnle : (n : ℝ) ≤ R / delta := (le_div_iff₀ hdeltaPos).2 (by
      simpa only [mul_comm] using hmul)
    have hnN : n < N := by exact_mod_cast hnle.trans_lt hN
    let n' : Fin (N + 1) := ⟨n, hnN.trans (Nat.lt_succ_self N)⟩
    let f : Fin n → ↥G := fun k ↦
      ⟨z (i + (k.1 + 1 : ℕ)) - z (i + (k.1 : ℕ)),
        ⟨i + (k.1 : ℤ), by congr 2; omega⟩⟩
    refine ⟨((0 : Fin 2), ⟨n', f⟩), ?_⟩
    change value ((0 : Fin 2), ⟨n', f⟩) = z j - z i
    simp only [value, ↓reduceIte, f]
    rw [Fin.sum_univ_eq_sum_range (α := ℝ)
      (fun k : ℕ ↦ z (i + (k + 1 : ℕ)) - z (i + (k : ℕ))) n]
    calc
      ∑ k ∈ Finset.range n,
          (z (i + (k + 1 : ℕ)) - z (i + (k : ℕ))) =
          z (i + (n : ℤ)) - z i := (sum_adjacent_gaps z i n).symm
      _ = z j - z i := by rw [hijn]
  · let n : ℕ := (i - j).toNat
    have hncast : (n : ℤ) = i - j :=
      Int.toNat_of_nonneg (sub_nonneg.mpr hji)
    have hjin : j + (n : ℤ) = i := by rw [hncast]; omega
    have hnonneg : 0 ≤ z i - z j := sub_nonneg.mpr (hmono.monotone hji)
    have hmul : (n : ℝ) * delta ≤ R := by
      calc
        (n : ℝ) * delta ≤ z (j + (n : ℤ)) - z j :=
          nat_mul_le_difference z hdeltaLe j n
        _ = z i - z j := by rw [hjin]
        _ = |z j - z i| := by rw [abs_sub_comm, abs_of_nonneg hnonneg]
        _ ≤ R := hball
    have hnle : (n : ℝ) ≤ R / delta := (le_div_iff₀ hdeltaPos).2 (by
      simpa only [mul_comm] using hmul)
    have hnN : n < N := by exact_mod_cast hnle.trans_lt hN
    let n' : Fin (N + 1) := ⟨n, hnN.trans (Nat.lt_succ_self N)⟩
    let f : Fin n → ↥G := fun k ↦
      ⟨z (j + (k.1 + 1 : ℕ)) - z (j + (k.1 : ℕ)),
        ⟨j + (k.1 : ℤ), by congr 2; omega⟩⟩
    refine ⟨((1 : Fin 2), ⟨n', f⟩), ?_⟩
    change value ((1 : Fin 2), ⟨n', f⟩) = z j - z i
    simp only [value, Fin.isValue, one_ne_zero, ↓reduceIte, f]
    rw [Fin.sum_univ_eq_sum_range (α := ℝ)
      (fun k : ℕ ↦ z (j + (k + 1 : ℕ)) - z (j + (k : ℕ))) n]
    calc
      -∑ k ∈ Finset.range n,
          (z (j + (k + 1 : ℕ)) - z (j + (k : ℕ))) =
          -(z (j + (n : ℤ)) - z j) := by rw [sum_adjacent_gaps]
      _ = z j - z i := by rw [hjin]; ring

private theorem range_locallyFinite_of_bounded_differences
    (z : ℤ → ℝ)
    (hDiff : ∀ R : ℝ, 0 < R →
      ((Set.range z - Set.range z) ∩ Metric.closedBall 0 R).Finite) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (Set.range z ∩ Q).Finite := by
  intro Q hQ
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hQ
  let R : ℝ := |r| + |z 0| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hImage : ((fun x : ℝ ↦ x - z 0) '' (Set.range z ∩ Q)).Finite := by
    apply (hDiff R hR).subset
    rintro d ⟨x, ⟨hxZ, hxQ⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨x, hxZ, z 0, Set.mem_range_self 0, rfl⟩
    · rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      have hxabs : |x| ≤ r := by
        have hxball := hr hxQ
        simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hxball
      have htri : |x - z 0| ≤ |x| + |z 0| := by
        simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le x 0 (z 0))
      calc
        |x - z 0| ≤ |x| + |z 0| := htri
        _ ≤ |r| + |z 0| := add_le_add (hxabs.trans (le_abs_self r)) le_rfl
        _ ≤ R := by dsimp [R]; linarith
  exact hImage.of_finite_image fun x _ y _ hxy ↦ by linarith

theorem flc_iff_finiteAdjacentGaps
    {Z : Set ℝ} (z : ℤ → ℝ)
    (hmono : StrictMono z) (hrange : Set.range z = Z)
    (hrelDense : ∃ M : ℝ, 0 < M ∧
      ∀ x : ℝ, ∃ a ∈ Z, |a - x| < M) :
    Tiling.AxisParallel.HasFLC Z ↔
      {g : ℝ | ∃ i : ℤ, g = z (i + 1) - z i}.Finite := by
  constructor
  · exact finite_adjacent_gaps_of_hasFLC z hmono hrange hrelDense
  · intro hG
    rw [← hrange]
    have hDiff : ∀ R : ℝ, 0 < R →
        ((Set.range z - Set.range z) ∩ Metric.closedBall 0 R).Finite :=
      bounded_differences_finite_of_finite_adjacent_gaps z hmono hG
    exact ⟨range_locallyFinite_of_bounded_differences z hDiff, hDiff⟩

private theorem projectedCentres_tileRelativelyDense :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      ∃ H : ℝ, 0 < H ∧ ∀ x : ℝ,
        ∃ t ∈ T, |t.re - x| < H := by
  intro K T hTile
  obtain ⟨D, hD⟩ := K.isPolygonal.isBounded.subset_closedBall
    (0 : Tiling.Plane)
  let H : ℝ := max D 0 + 1
  refine ⟨H, by dsimp [H]; linarith [le_max_right D 0], ?_⟩
  intro x
  let z : Tiling.Plane := (x : ℂ)
  have hzCover : z ∈ closedSupportUnion K T := by
    rw [closedTranslatedSupports_cover hTile]
    exact Set.mem_univ z
  rw [closedSupportUnion, Set.mem_iUnion] at hzCover
  obtain ⟨t, hzt⟩ := hzCover
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
  let k : Tiling.Plane := -(t.1 : Tiling.Plane) +ᵥ z
  have hk : k ∈ K.support := by simpa only [k] using hzt
  have hkClosed : k ∈ Metric.closedBall (0 : Tiling.Plane) D := hD hk
  have hkBound : ‖k‖ ≤ max D 0 := by
    have : ‖k‖ ≤ D := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hkClosed
    exact this.trans (le_max_left D 0)
  refine ⟨t.1, t.2, ?_⟩
  have hRe : t.1.re - x = -k.re := by
    simp only [k, z, vadd_eq_add, Complex.neg_re, Complex.add_re,
      Complex.ofReal_re]
    ring
  calc
    |t.1.re - x| = |k.re| := by rw [hRe, abs_neg]
    _ ≤ ‖k‖ := Complex.abs_re_le_norm k
    _ ≤ max D 0 := hkBound
    _ < H := by dsimp [H]; linarith

private theorem adjacentProjectedGap_hasBoundedBoundaryWords :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      (∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
        (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty) →
      ∀ z : ℤ → ℝ, StrictMono z →
        Set.range z = Continuous.horizontalCentreProjection T →
        ∃ N : ℕ, ∀ i : ℤ,
          ∃ (sgn₀ sgn₁ : Fin 2)
            (n₀ n₁ : Fin (N + 1))
            (w₀ : Fin n₀.1 → ℝ) (w₁ : Fin n₁.1 → ℝ),
            (∀ j, w₀ j ∈ K.horizontalStepAlphabet) ∧
            (∀ j, w₁ j ∈ K.horizontalStepAlphabet) ∧
            z (i + 1) - z i =
              (if sgn₁ = 0 then ∑ j, w₁ j else -∑ j, w₁ j) -
                (if sgn₀ = 0 then ∑ j, w₀ j else -∑ j, w₀ j) := by
  intro K T hTile hNontrivial hDense z hmono hrange
  obtain ⟨H, hH, hProjectedDense⟩ :=
    projectedCentres_tileRelativelyDense hTile
  have hRel : ∀ x : ℝ, ∃ a ∈ Continuous.horizontalCentreProjection T,
      |a - x| < H := by
    intro x
    obtain ⟨t, ht, htx⟩ := hProjectedDense x
    exact ⟨t.re, ⟨t, ht, rfl⟩, htx⟩
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  let vK : ↥K.vertices := ⟨v, hv⟩
  obtain ⟨M, hM, hBoundaryDense⟩ := hDense
  let delta : ℝ := K.horizontalStepAlphabet.min'
    K.horizontalStepAlphabet_nonempty
  have hdelta : 0 < delta := K.horizontalStepAlphabet_pos
    (K.horizontalStepAlphabet.min'_mem K.horizontalStepAlphabet_nonempty)
  have hdeltaLe : ∀ d ∈ K.horizontalStepAlphabet, delta ≤ d := by
    intro d hd
    exact K.horizontalStepAlphabet.min'_le d hd
  let R : ℝ := M + 2 * H
  obtain ⟨N, hN⟩ := exists_nat_gt (R / delta)
  have hWord (c : ℝ) (hcBoundary : c ∈ componentBoundarySet K T)
      (t : ↥T)
      (hbound : |(vK.1 + (t.1 : Tiling.Plane)).re - c| ≤ R) :
      ∃ (sgn : Fin 2) (n : Fin (N + 1)) (word : Fin n.1 → ℝ),
        (∀ j, word j ∈ K.horizontalStepAlphabet) ∧
        (if sgn = 0 then ∑ j, word j else -∑ j, word j) =
          (vK.1 + (t.1 : Tiling.Plane)).re - c := by
    by_cases heq : (vK.1 + (t.1 : Tiling.Plane)).re = c
    · refine ⟨0, ⟨0, Nat.zero_lt_succ N⟩, fun j ↦ Fin.elim0 j, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp [heq]
    · obtain ⟨n, _hn, step, hstep, hsum, hnR⟩ :=
        horizontalBoundaryStepCount_le hTile
          (componentBoundary_completeTranslatedBoundaryLine
            hTile hNontrivial c hcBoundary)
          hdelta hdeltaLe vK t heq hbound
      have hnle : (n : ℝ) ≤ R / delta := by
        apply (le_div_iff₀ hdelta).2
        simpa only [mul_comm] using hnR
      have hnN : n < N := by
        exact_mod_cast hnle.trans_lt hN
      let n' : Fin (N + 1) :=
        ⟨n, hnN.trans (Nat.lt_succ_self N)⟩
      by_cases hlt : (vK.1 + (t.1 : Tiling.Plane)).re < c
      · refine ⟨1, n', step, hstep, ?_⟩
        simp only [Fin.isValue, one_ne_zero, ↓reduceIte]
        rw [abs_of_neg (sub_neg.mpr hlt)] at hsum
        linarith
      · have hgt : c < (vK.1 + (t.1 : Tiling.Plane)).re :=
          lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
        refine ⟨0, n', step, hstep, ?_⟩
        simp only [↓reduceIte]
        rw [abs_of_pos (sub_pos.mpr hgt)] at hsum
        exact hsum.symm
  refine ⟨N, fun i ↦ ?_⟩
  have hzi : z i ∈ Continuous.horizontalCentreProjection T := by
    rw [← hrange]
    exact Set.mem_range_self i
  have hzi1 : z (i + 1) ∈ Continuous.horizontalCentreProjection T := by
    rw [← hrange]
    exact Set.mem_range_self (i + 1)
  change z i ∈ Complex.re '' T at hzi
  change z (i + 1) ∈ Complex.re '' T at hzi1
  obtain ⟨t₀, ht₀, ht₀re⟩ := hzi
  obtain ⟨t₁, ht₁, ht₁re⟩ := hzi1
  let t₀T : ↥T := ⟨t₀, ht₀⟩
  let t₁T : ↥T := ⟨t₁, ht₁⟩
  obtain ⟨c, hcBoundary, hcRange⟩ := hBoundaryDense (v.re + z i)
  have hgap : z (i + 1) - z i < 2 * H :=
    adjacent_gap_lt_two_mul z hmono hrange hRel i
  have hp₀ : (vK.1 + (t₀T.1 : Tiling.Plane)).re = v.re + z i := by
    simp only [vK, t₀T, Complex.add_re]
    rw [ht₀re]
  have hp₁ : (vK.1 + (t₁T.1 : Tiling.Plane)).re = v.re + z (i + 1) := by
    simp only [vK, t₁T, Complex.add_re]
    rw [ht₁re]
  have hbound₀ : |(vK.1 + (t₀T.1 : Tiling.Plane)).re - c| ≤ R := by
    rw [hp₀, abs_of_nonpos (sub_nonpos.mpr hcRange.1)]
    dsimp only [R]
    linarith [hcRange.2, hH]
  have hbound₁ : |(vK.1 + (t₁T.1 : Tiling.Plane)).re - c| ≤ R := by
    rw [hp₁, abs_le]
    dsimp only [R]
    constructor <;> linarith [hcRange.1, hcRange.2,
      hmono (show i < i + 1 by omega), hgap]
  obtain ⟨sgn₀, n₀, word₀, hword₀, hvalue₀⟩ :=
    hWord c hcBoundary t₀T hbound₀
  obtain ⟨sgn₁, n₁, word₁, hword₁, hvalue₁⟩ :=
    hWord c hcBoundary t₁T hbound₁
  refine ⟨sgn₀, sgn₁, n₀, n₁, word₀, word₁,
    hword₀, hword₁, ?_⟩
  calc
    z (i + 1) - z i =
        ((vK.1 + (t₁T.1 : Tiling.Plane)).re - c) -
          ((vK.1 + (t₀T.1 : Tiling.Plane)).re - c) := by
            rw [hp₀, hp₁]
            ring
    _ = (if sgn₁ = 0 then ∑ j, word₁ j else -∑ j, word₁ j) -
          (if sgn₀ = 0 then ∑ j, word₀ j else -∑ j, word₀ j) := by
            rw [hvalue₀, hvalue₁]

private theorem adjacentProjectedGaps_finite_of_relativelyDenseBoundaries :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → NontrivialDecomposition K T →
      (∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
        (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty) →
      ∀ z : ℤ → ℝ, StrictMono z →
        Set.range z = Continuous.horizontalCentreProjection T →
        (adjacentGapSet z).Finite := by
  intro K T hTile hNontrivial hDense z hmono hrange
  obtain ⟨N, hWords⟩ := adjacentProjectedGap_hasBoundedBoundaryWords
    hTile hNontrivial hDense z hmono hrange
  let Values : Set ℝ :=
    {x : ℝ | ∃ (sgn : Fin 2) (n : Fin (N + 1))
      (word : Fin n.1 → ℝ),
      (∀ j, word j ∈ K.horizontalStepAlphabet) ∧
      x = if sgn = 0 then ∑ j, word j else -∑ j, word j}
  have hValues : Values.Finite := by
    simpa only [Values] using
      finiteSignedStepWordValues K.horizontalStepAlphabet N
  apply (hValues.sub hValues).subset
  intro g hg
  obtain ⟨i, rfl⟩ := hg
  obtain ⟨sgn₀, sgn₁, n₀, n₁, word₀, word₁,
    hword₀, hword₁, hgap⟩ := hWords i
  refine ⟨_, ⟨sgn₁, n₁, word₁, hword₁, rfl⟩,
    _, ⟨sgn₀, n₀, word₀, hword₀, rfl⟩, hgap.symm⟩

theorem finiteHorizontalComplexity_of_relativelyDenseBoundaries :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      (∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
        (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty) →
      Continuous.HasFiniteHorizontalComplexity T := by
  intro K T hTile hNontrivial hDense
  obtain ⟨z, hmono, hrange⟩ :=
    exists_increasingProjectedCentreEnumeration hTile hNontrivial
  obtain ⟨H, hH, hProjectedDense⟩ :=
    projectedCentres_tileRelativelyDense hTile
  have hRel : ∃ H : ℝ, 0 < H ∧
      ∀ x : ℝ, ∃ a ∈ Continuous.horizontalCentreProjection T,
        |a - x| < H := by
    refine ⟨H, hH, ?_⟩
    intro x
    obtain ⟨t, ht, htx⟩ := hProjectedDense x
    exact ⟨t.re, ⟨t, ht, rfl⟩, htx⟩
  exact (flc_iff_finiteAdjacentGaps z hmono hrange hRel).2
    (adjacentProjectedGaps_finite_of_relativelyDenseBoundaries
      hTile hNontrivial hDense z hmono hrange)

private theorem horizontalFootprint_pos_candidate (K : Region) :
    0 < (MeasureTheory.volume
      (interior (closure (Complex.re '' K.openCarrier)))).toReal := by
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  have hCarrierOpen : IsOpen K.openCarrier := isOpen_interior
  have hCarrierNonempty : K.openCarrier.Nonempty :=
    K.isPolygonal.interior_nonempty K.nonempty
  have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re K.openCarrier hCarrierOpen
  have hProjectionNonempty : (Complex.re '' K.openCarrier).Nonempty :=
    hCarrierNonempty.image Complex.re
  have hAOpen : IsOpen A := by
    simp only [A]
    exact isOpen_interior
  have hANonempty : A.Nonempty := by
    apply hProjectionNonempty.mono
    simpa only [A] using hProjectionOpen.subset_interior_closure
  have hCarrierBounded : Bornology.IsBounded K.openCarrier :=
    K.isPolygonal.isBounded.subset interior_subset
  have hProjectionBounded : Bornology.IsBounded
      (Complex.re '' K.openCarrier) :=
    RCLike.lipschitzWith_re.isBounded_image hCarrierBounded
  have hABounded : Bornology.IsBounded A := by
    apply hProjectionBounded.closure.subset
    simpa only [A] using
      (interior_subset :
        interior (closure (Complex.re '' K.openCarrier)) ⊆
          closure (Complex.re '' K.openCarrier))
  have hVolumePosENN : 0 < MeasureTheory.volume A :=
    hAOpen.measure_pos MeasureTheory.volume hANonempty
  have hVolumeNeTop : MeasureTheory.volume A ≠ ⊤ :=
    (hABounded.measure_lt_top (μ := MeasureTheory.volume)).ne
  have hVolumePos : 0 < (MeasureTheory.volume A).toReal :=
    ENNReal.toReal_pos hVolumePosENN.ne' hVolumeNeTop
  simpa only [A] using hVolumePos

private theorem verticalPlateBases_pairwiseDisjoint_candidate
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P Q : Continuous.VerticalPlate K T)
    (hPQ : P ≠ Q) : Disjoint P.base Q.base := by
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (Continuous.VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
    intro R
    obtain ⟨r, hr⟩ := R.nonempty_supp
    refine ⟨r, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr
  have hSupportDisjoint : Disjoint P.support Q.support := by
    have hPartition := regularSupport_pairwiseDisjoint
      (@Continuous.VerticalPlate.centres K T)
      (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
      (Continuous.iUnion_verticalPlateCentres K T) hTile
    exact hPartition.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
  obtain ⟨-, hPSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  obtain ⟨-, hQSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile Q
  rw [Set.disjoint_left]
  intro z hzP hzQ
  let q : Tiling.Plane := ⟨z, 0⟩
  have hqP : q ∈ P.support := by
    rw [hPSupport]
    exact hzP
  have hqQ : q ∈ Q.support := by
    rw [hQSupport]
    exact hzQ
  exact Set.disjoint_left.mp hSupportDisjoint hqP hqQ

private theorem base_window_nonempty_candidate
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : Continuous.VerticalPlate K T)
    (hPnoncolumn : ¬ Continuous.IsVerticalColumn P)
    (x : ℝ) :
    (P.base ∩ Ioo x
      (x + 8 * Metric.diam
        (closure (interior (closure (Complex.re '' K.openCarrier)))))).Nonempty := by
  have hThickness := noncolumnPlate_thickness hTile P hPnoncolumn x
  change (1 / 2 : ℝ) *
      (MeasureTheory.volume
        (interior (closure (Complex.re '' K.openCarrier)))).toReal <
    (MeasureTheory.volume
      (P.base ∩ Ioo x
        (x + 8 * Metric.diam
          (closure (interior (closure (Complex.re '' K.openCarrier))))))).toReal
    at hThickness
  have hHalf : 0 < (1 / 2 : ℝ) *
      (MeasureTheory.volume
        (interior (closure (Complex.re '' K.openCarrier)))).toReal :=
    mul_pos (by norm_num) (horizontalFootprint_pos_candidate K)
  have hPositive := hHalf.trans hThickness
  by_contra hEmpty
  have hEq : P.base ∩ Ioo x
      (x + 8 * Metric.diam
        (closure (interior (closure (Complex.re '' K.openCarrier))))) =
      (∅ : Set ℝ) := Set.not_nonempty_iff_eq_empty.mp hEmpty
  rw [hEq, MeasureTheory.measure_empty] at hPositive
  exact (lt_irrefl 0 hPositive)

private theorem frontier_between_disjoint_open_candidate
    {P Q : Set ℝ}
    (hPopen : IsOpen P) (hQopen : IsOpen Q)
    (hPQ : Disjoint P Q) {p q : ℝ}
    (hp : p ∈ P) (hq : q ∈ Q) :
    ∃ z ∈ frontier P, z ∈ Icc (min p q) (max p q) := by
  have hqClosure : q ∉ closure P := by
    intro hqClosure
    obtain ⟨z, hzQ, hzP⟩ := mem_closure_iff.mp hqClosure Q hQopen hq
    exact Set.disjoint_left.mp hPQ hzP hzQ
  let lo := min p q
  let hi := max p q
  have hpIcc : p ∈ Icc lo hi := by
    exact ⟨min_le_left _ _, le_max_left _ _⟩
  have hqIcc : q ∈ Icc lo hi := by
    exact ⟨min_le_right _ _, le_max_right _ _⟩
  have hIccPre : IsPreconnected (Icc lo hi) := isPreconnected_Icc
  have hnotSubset : ¬ Icc lo hi ⊆ P := by
    intro hsubset
    have hqNotP : q ∉ P := by
      intro hqP
      exact Set.disjoint_left.mp hPQ hqP hq
    exact hqNotP (hsubset hqIcc)
  have hclosureNotSubset : ¬ closure P ∩ Icc lo hi ⊆ P := by
    intro hsubset
    apply hnotSubset
    exact hIccPre.subset_of_closure_inter_subset hPopen
      ⟨p, hpIcc, hp⟩ hsubset
  obtain ⟨z, hzClosureIcc, hzNotP⟩ := Set.not_subset.mp hclosureNotSubset
  refine ⟨z, ?_, hzClosureIcc.2⟩
  change z ∈ closure P \ interior P
  refine ⟨hzClosureIcc.1, ?_⟩
  simpa only [hPopen.interior_eq] using hzNotP

/-- Two distinct noncolumn vertical plates force uniformly relatively dense
component boundaries, with the exact lower BoundaryDensity API telescope. -/
theorem componentBoundarySet_relativelyDense_of_two_noncolumnPlates
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hTwo : ∃ P Q : Continuous.VerticalPlate K T,
      P ≠ Q ∧ ¬ Continuous.IsVerticalColumn P ∧
        ¬ Continuous.IsVerticalColumn Q) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ,
      (componentBoundarySet K T ∩ Icc x (x + M)).Nonempty := by
  obtain ⟨P, Q, hPQ, hPnoncolumn, hQnoncolumn⟩ := hTwo
  let M : ℝ := 8 * Metric.diam
    (closure (interior (closure (Complex.re '' K.openCarrier))))
  have hM : 0 < M := by
    dsimp [M]
    have hD : 0 < Metric.diam
        (closure (interior (closure (Complex.re '' K.openCarrier)))) := by
      have hCarrierOpen : IsOpen K.openCarrier := isOpen_interior
      have hCarrierNonempty : K.openCarrier.Nonempty :=
        K.isPolygonal.interior_nonempty K.nonempty
      have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
        Complex.isOpenMap_re K.openCarrier hCarrierOpen
      have hProjectionNonempty :
          (Complex.re '' K.openCarrier).Nonempty :=
        hCarrierNonempty.image Complex.re
      have hA : (interior (closure (Complex.re '' K.openCarrier))).Nonempty :=
        hProjectionNonempty.mono hProjectionOpen.subset_interior_closure
      have hAopen : IsOpen (interior (closure (Complex.re '' K.openCarrier))) :=
        isOpen_interior
      have hAreg : (interior (closure (Complex.re '' K.openCarrier))).Nontrivial := by
        rw [← Set.not_subsingleton_iff]
        intro hsub
        have hzero : MeasureTheory.volume
            (interior (closure (Complex.re '' K.openCarrier))) = 0 :=
          hsub.measure_zero MeasureTheory.volume
        exact (ne_of_gt (hAopen.measure_pos MeasureTheory.volume hA)) hzero
      have hCarrierBounded : Bornology.IsBounded K.openCarrier :=
        K.isPolygonal.isBounded.subset interior_subset
      have hProjectionBounded : Bornology.IsBounded
          (Complex.re '' K.openCarrier) :=
        RCLike.lipschitzWith_re.isBounded_image hCarrierBounded
      have hABounded : Bornology.IsBounded
          (interior (closure (Complex.re '' K.openCarrier))) := by
        apply hProjectionBounded.closure.subset
        exact interior_subset
      apply Metric.diam_pos
      · exact hAreg.mono subset_closure
      · exact hABounded.closure
    nlinarith
  refine ⟨M, hM, ?_⟩
  intro x
  have hPnonempty := base_window_nonempty_candidate hTile P hPnoncolumn x
  have hQnonempty := base_window_nonempty_candidate hTile Q hQnoncolumn x
  obtain ⟨p, hpP, hpI⟩ := hPnonempty
  obtain ⟨q, hqQ, hqI⟩ := hQnonempty
  change x < p ∧ p < x + M at hpI
  change x < q ∧ q < x + M at hqI
  have hPopen : IsOpen P.base := by
    obtain ⟨hRegular, -⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile P
    rw [hRegular]
    exact isOpen_interior
  have hQopen : IsOpen Q.base := by
    obtain ⟨hRegular, -⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile Q
    rw [hRegular]
    exact isOpen_interior
  obtain ⟨z, hzFrontier, hzBetween⟩ :=
    frontier_between_disjoint_open_candidate hPopen hQopen
      (verticalPlateBases_pairwiseDisjoint_candidate hTile P Q hPQ)
      hpP hqQ
  refine ⟨z, ?_, ?_⟩
  · rw [componentBoundarySet_eq]
    exact Set.mem_iUnion.mpr ⟨P, hzFrontier⟩
  · have hpBounds : p ∈ Icc x (x + M) := by
      exact ⟨le_of_lt hpI.1, le_of_lt hpI.2⟩
    have hqBounds : q ∈ Icc x (x + M) := by
      exact ⟨le_of_lt hqI.1, le_of_lt hqI.2⟩
    exact ⟨(le_min hpBounds.1 hqBounds.1).trans hzBetween.1,
      hzBetween.2.trans (max_le hpBounds.2 hqBounds.2)⟩


end Tiling.AxisParallel.Structure
