import Tiling.Approximation.RationalLinear
import Tiling.Geometry.Periodicity

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology
open Tiling.Approximation
open Tiling.Polygonal (RelativeDense)

noncomputable section

namespace Tiling.RationalSlopes.Approximation

def RationalMesh (d : ℕ) : Set Plane :=
  {z | ∃ p q : ℤ, z = Complex.mk ((p : ℝ) / d) ((q : ℝ) / d)}

theorem boundedSteps_generate :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∀ y₀ ∈ Y, ∃ steps : Finset Plane, (steps : Set Plane) ⊆ Y - Y ∧
      ∀ y ∈ Y, y - y₀ ∈ AddSubgroup.closure (steps : Set Plane) := by
  classical
  intro Y hYFLC ⟨rho, hrho, hYdense⟩ y0 hy0
  let stepSet := (Y - Y) ∩ Metric.closedBall 0 (3 * rho)
  have hstepFinite : stepSet.Finite := hYFLC.2 (3 * rho) (by linarith)
  let steps := hstepFinite.toFinset
  refine ⟨steps, ?_, ?_⟩
  · intro d hd
    have hdSet : d ∈ stepSet :=
      hstepFinite.mem_toFinset.mp (show d ∈ hstepFinite.toFinset from hd)
    exact hdSet.1
  · intro y hy
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (dist y y0 / rho)
    have hratioNonneg : 0 ≤ dist y y0 / rho := div_nonneg dist_nonneg hrho.le
    have hnRealPos : 0 < (n : ℝ) := lt_of_le_of_lt hratioNonneg hn
    have hnPos : 0 < n := by exact_mod_cast hnRealPos
    have hsmall : dist y y0 / (n : ℝ) < rho := by
      rw [div_lt_iff₀ hnRealPos]
      have := (div_lt_iff₀ hrho).mp hn
      nlinarith
    let c : Fin (n + 1) → Plane := fun i ↦
      y0 + ((i : ℝ) / (n : ℝ)) • (y - y0)
    choose q hqY hqDist using fun i : Fin (n + 1) ↦ hYdense (c i)
    let p : Fin (n + 1) → Plane := fun i ↦
      if i = 0 then y0 else if i = Fin.last n then y else q i
    have hpY : ∀ i, p i ∈ Y := by
      intro i
      simp only [p]
      split
      · exact hy0
      · split
        · exact hy
        · exact hqY i
    have hcZero : c 0 = y0 := by simp [c]
    have hcLast : c (Fin.last n) = y := by
      change y0 + ((n : ℝ) / (n : ℝ)) • (y - y0) = y
      rw [div_self (ne_of_gt hnRealPos), one_smul]
      abel
    have hpClose : ∀ i, dist (p i) (c i) < rho := by
      intro i
      by_cases hi0 : i = 0
      · subst i
        rw [hcZero]
        simp [p, hrho]
      · by_cases hiLast : i = Fin.last n
        · subst i
          rw [hcLast]
          have hlast0 : Fin.last n ≠ (0 : Fin (n + 1)) := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_last, Fin.val_zero] at this
            omega
          simp [p, hlast0, hrho]
        · simpa only [p, hi0, hiLast, if_false, dist_comm] using hqDist i
    have hcStep : ∀ i : Fin n,
        dist (c i.succ) (c i.castSucc) = dist y y0 / (n : ℝ) := by
      intro i
      rw [dist_eq_norm]
      change ‖(y0 + (((i.val + 1 : ℕ) : ℝ) / (n : ℝ)) • (y - y0)) -
          (y0 + ((i.val : ℝ) / (n : ℝ)) • (y - y0))‖ =
        dist y y0 / (n : ℝ)
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      have hcoef :
          ((i.val + 1 : ℕ) : ℝ) / (n : ℝ) - (i.val : ℝ) / (n : ℝ) =
            ((n : ℝ)⁻¹) := by
        push_cast
        field_simp
        ring
      rw [hcoef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnRealPos),
        dist_eq_norm, norm_sub_rev, div_eq_mul_inv]
      ring
    have hpStep : ∀ i : Fin n, dist (p i.succ) (p i.castSucc) < 3 * rho := by
      intro i
      have h₁ := dist_triangle (p i.succ) (c i.succ) (p i.castSucc)
      have h₂ := dist_triangle (c i.succ) (c i.castSucc) (p i.castSucc)
      rw [hcStep i] at h₂
      have hclose₁ := hpClose i.succ
      have hclose₂ := hpClose i.castSucc
      rw [dist_comm (p i.castSucc)] at hclose₂
      linarith
    have hstepMem : ∀ i : Fin n, p i.succ - p i.castSucc ∈ steps := by
      intro i
      apply hstepFinite.mem_toFinset.mpr
      refine ⟨?_, ?_⟩
      · exact ⟨p i.succ, hpY i.succ, p i.castSucc, hpY i.castSucc, rfl⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        simpa only [dist_eq_norm] using (hpStep i).le
    let pNat : ℕ → Plane := fun k ↦
      if hk : k < n + 1 then p ⟨k, hk⟩ else 0
    have hsum :
        ∑ k ∈ Finset.range n, (pNat (k + 1) - pNat k) ∈
          AddSubgroup.closure (steps : Set Plane) := by
      apply AddSubgroup.sum_mem
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hk1 : k + 1 < n + 1 := by omega
      have hk0 : k < n + 1 := by omega
      have hmem := hstepMem (⟨k, hkn⟩ : Fin n)
      apply AddSubgroup.subset_closure
      simp only [pNat, dif_pos hk1, dif_pos hk0]
      change p ⟨k + 1, hk1⟩ - p ⟨k, hk0⟩ ∈ steps
      simpa using hmem
    rw [Finset.sum_range_sub] at hsum
    have hpNatLast : pNat n = y := by
      have hnlt : n < n + 1 := by omega
      simp only [pNat, dif_pos hnlt]
      have hfin : (⟨n, hnlt⟩ : Fin (n + 1)) = Fin.last n := by ext; rfl
      rw [hfin]
      have hlast0 : Fin.last n ≠ (0 : Fin (n + 1)) := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      simp only [p, if_neg hlast0, if_pos]
    have hpNatZero : pNat 0 = y0 := by
      have hzero : 0 < n + 1 := by omega
      simp only [pNat, dif_pos hzero]
      simp [p]
    rwa [hpNatLast, hpNatZero] at hsum

theorem commonMesh_of_finiteZGeneration :
  ∀ (steps : Finset Plane) (φ : ℝ →ₗ[ℚ] ℚ), ∃ d : ℕ, 0 < d ∧
    deformPoint φ '' (AddSubgroup.closure (steps : Set Plane) : Set Plane) ⊆ RationalMesh d := by
  intro steps φ
  classical
  let coords : Finset ℚ :=
    (steps.image (fun z : Plane => φ z.re)) ∪
      (steps.image (fun z : Plane => φ z.im))
  obtain ⟨d, hd, hcoord⟩ := finiteRational_denominator coords
  refine ⟨d, hd, ?_⟩
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hclosed : ∀ w ∈ (AddSubgroup.closure (steps : Set Plane) : Set Plane),
      deformPoint φ w ∈
        {z | ∃ p q : ℤ, z = Complex.mk ((p : ℝ) / d) ((q : ℝ) / d)} := by
    -- The rational mesh is an additive subgroup; closure induction then reduces
    -- the claim to the finite generators.
    let mesh : AddSubgroup Plane := {
      carrier := {w | ∃ p q : ℤ, w = Complex.mk ((p : ℝ) / d) ((q : ℝ) / d)}
      zero_mem' := by
        refine ⟨0, 0, ?_⟩
        apply Complex.ext <;> simp
      add_mem' := by
        intro a b ha hb
        rcases ha with ⟨pa, qa, rfl⟩
        rcases hb with ⟨pb, qb, rfl⟩
        refine ⟨pa + pb, qa + qb, ?_⟩
        apply Complex.ext <;> simp [Int.cast_add, add_div]
      neg_mem' := by
        intro a ha
        rcases ha with ⟨p, q, rfl⟩
        refine ⟨-p, -q, ?_⟩
        apply Complex.ext <;> simp [Int.cast_neg, neg_div]
    }
    intro w hw
    change deformPoint φ w ∈ (mesh : Set Plane)
    induction hw using AddSubgroup.closure_induction with
    | mem u hu =>
        rcases hcoord (φ u.re)
          (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨u, hu, rfl⟩))) with ⟨p, hp⟩
        rcases hcoord (φ u.im)
          (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨u, hu, rfl⟩))) with ⟨q, hq⟩
        exact ⟨p, q, by simp [deformPoint, hp, hq]⟩
    | zero => exact ⟨0, 0, by apply Complex.ext <;> simp [deformPoint]⟩
    | add a b ha hb iha ihb =>
        change deformPointLinear φ (a + b) ∈ (mesh : Set Plane)
        rw [map_add]
        exact mesh.add_mem iha ihb
    | neg a ha iha =>
        change deformPointLinear φ (-a) ∈ (mesh : Set Plane)
        rw [map_neg]
        exact mesh.neg_mem iha
  exact hclosed x hx


theorem flcApproximation_commonMesh :
  ∀ (T : Set Plane) (V : Finset Plane), 0 ∈ T →
    Tiling.Polygonal.HasFLC T → RelativeDense T →
      ∀ φ : ℝ →ₗ[ℚ] ℚ, ∃ d : ℕ, 0 < d ∧
        deformPoint φ '' (T ∪ (V : Set Plane)) ⊆ RationalMesh d := by
  classical
  intro T V hzero hT hdense φ
  obtain ⟨steps, hsub, hgenerated⟩ := boundedSteps_generate T hT hdense 0 hzero
  obtain ⟨d, hd, hmesh⟩ := commonMesh_of_finiteZGeneration (steps ∪ V) φ
  refine ⟨d, hd, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  apply hmesh
  refine ⟨z, ?_, rfl⟩
  rcases hz with hz | hz
  · have hclosure : AddSubgroup.closure (steps : Set Plane) ≤
        AddSubgroup.closure ((steps ∪ V : Finset Plane) : Set Plane) :=
      AddSubgroup.closure_mono (by intro x hx; exact Finset.mem_union_left _ hx)
    exact hclosure (by simpa only [sub_zero] using hgenerated z hz)
  · exact AddSubgroup.subset_closure (Finset.mem_union_right _ hz)

private theorem denseSegmentChain
    (Y : Set Plane) (rho L R : ℝ) (hrho : 0 < rho) (hL : 0 < L)
    (hLR : L + 2 * rho < R)
    (a b : ↥Y)
    (hdense : ∀ s : ℝ, ∃ y ∈ Y, dist ((a : Plane) + s • ((b : Plane) - a)) y < rho)
    (hLab : L < dist (a : Plane) b) :
    ∃ N : ℕ, 0 < N ∧ ∃ point : Fin (N + 1) → ↥Y,
      point 0 = a ∧ point (Fin.last N) = b ∧
      (∀ i : Fin N, dist (point i.castSucc : Plane) (point i.succ) < R) ∧
      (N : ℝ) ≤ dist (a : Plane) b / L + 1 := by
  let D := dist (a : Plane) b
  let N := Nat.ceil (D / L)
  have hDL : 1 < D / L := by
    apply (lt_div_iff₀ hL).2
    simpa [D] using hLab
  have hNpos : 0 < N := Nat.ceil_pos.mpr (lt_trans zero_lt_one hDL)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstepLe : D / (N : ℝ) ≤ L := by
    have hceil : D / L ≤ (N : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hNreal]
    have := (div_le_iff₀ hL).mp hceil
    nlinarith
  have hNle : (N : ℝ) ≤ D / L + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by simp [D]) hL.le))
  let c : Fin (N + 1) → Plane := fun i ↦
    (a : Plane) + ((i : ℝ) / (N : ℝ)) •
      ((b : Plane) - (a : Plane))
  choose q hqY hqdist using fun i : Fin (N + 1) ↦ hdense ((i : ℝ) / (N : ℝ))
  let p : Fin (N + 1) → Plane := fun i ↦
    if i = 0 then a else if i = Fin.last N then b else q i
  have hpY (i : Fin (N + 1)) : p i ∈ Y := by
    simp only [p]
    split
    · exact a.2
    · split
      · exact b.2
      · exact hqY i
  have hcZero : c 0 = a := by simp [c]
  have hcLast : c (Fin.last N) = b := by
    change (a : Plane) + ((N : ℝ) / (N : ℝ)) •
      ((b : Plane) - (a : Plane)) = b
    rw [div_self (ne_of_gt hNreal), one_smul]
    abel
  have hpClose (i : Fin (N + 1)) : dist (p i) (c i) < rho := by
    by_cases hi0 : i = 0
    · subst i
      rw [hcZero]
      simp [p, hrho]
    · by_cases hilast : i = Fin.last N
      · subst i
        rw [hcLast]
        have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_zero] at this
          omega
        simp [p, hlast0, hrho]
      · simpa [p, c, hi0, hilast, dist_comm] using hqdist i
  have hcStep (i : Fin N) :
      dist (c i.succ) (c i.castSucc) = D / (N : ℝ) := by
    rw [dist_eq_norm]
    change ‖((a : Plane) + (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) •
        ((b : Plane) - (a : Plane))) -
      ((a : Plane) + ((i.val : ℝ) / (N : ℝ)) •
        ((b : Plane) - (a : Plane)))‖ = D / (N : ℝ)
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    have hcoef : (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) -
        (i.val : ℝ) / (N : ℝ) = (N : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [hcoef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNreal),
      show ‖(b : Plane) - (a : Plane)‖ = D by
        rw [norm_sub_rev]
        simp [D, dist_eq_norm], div_eq_mul_inv]
    ring
  have hpStep (i : Fin N) :
      dist (p i.castSucc) (p i.succ) < R := by
    calc
      dist (p i.castSucc) (p i.succ) ≤
          dist (p i.castSucc) (c i.castSucc) +
            dist (c i.castSucc) (c i.succ) + dist (c i.succ) (p i.succ) :=
        dist_triangle4 _ _ _ _
      _ < rho + (D / (N : ℝ)) + rho := by
        rw [dist_comm (c i.castSucc) (c i.succ), hcStep]
        have hlast := hpClose i.succ
        rw [dist_comm] at hlast
        linarith [hpClose i.castSucc, hlast]
      _ ≤ rho + L + rho := by linarith
      _ < R := by linarith
  let point : Fin (N + 1) → ↥Y := fun i ↦ ⟨p i, hpY i⟩
  refine ⟨N, hNpos, point, ?_, ?_, ?_, hNle⟩
  · apply Subtype.ext
    simp [point, p]
  · apply Subtype.ext
    have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    simp [point, p, hlast0]
  · exact hpStep

private theorem deformPoint_sub (φ : ℝ →ₗ[ℚ] ℚ) (a b : Plane) :
    deformPoint φ (a - b) = deformPoint φ a - deformPoint φ b :=
  (deformPointLinear φ).map_sub a b

private theorem finitePointControl (D : Finset Plane) (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ d ∈ D, ‖deformPoint φ d - d‖ < η := by
  classical
  refine ⟨D.image Complex.re ∪ D.image Complex.im, η / 2, half_pos hη, ?_⟩
  intro φ hφ d hd
  have hre := hφ.2 d.re (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩))
  have him := hφ.2 d.im (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩))
  have hn : ‖deformPoint φ d - d‖ ≤ |(φ d.re : ℝ) - d.re| + |(φ d.im : ℝ) - d.im| :=
    Complex.norm_le_abs_re_add_abs_im (deformPoint φ d - d)
  linarith

private theorem globalRelativeError_of_segmentDensity
    (Y : Set Plane) (hY : Tiling.Polygonal.HasFLC Y) (rho : ℝ) (hrho : 0 < rho)
    (hdense : ∀ a ∈ Y, ∀ b ∈ Y, ∀ s : ℝ, ∃ y ∈ Y, dist (a + s • (b - a)) y < rho) :
    ∀ c : ℝ, 0 < c → c < 1 → ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ a ∈ Y, ∀ b ∈ Y,
          ‖deformPoint φ (a - b) - (a - b)‖ ≤ c * dist a b := by
  classical
  intro c hc _
  obtain ⟨δ, hδ, hsep⟩ := hY.uniformlyDiscrete
  let S := (Y - Y) ∩ Metric.closedBall 0 (4 * rho)
  have hS : S.Finite := hY.2 (4 * rho) (by linarith)
  let D := hS.toFinset
  let η := min (c * δ) (c * rho / 2)
  have hη : 0 < η := lt_min (mul_pos hc hδ) (half_pos (mul_pos hc hrho))
  obtain ⟨F, ε, hε, hcontrol⟩ := finitePointControl D η hη
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ a ha b hb
  let e : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom - AddMonoidHom.id Plane
  have he (z : Plane) : e z = deformPoint φ z - z := rfl
  have hstep (x : Plane) (hx : x ∈ Y) (y : Plane) (hy : y ∈ Y)
      (hxy : dist x y < 4 * rho) : ‖e (x - y)‖ < η := by
    apply hcontrol φ hφ (x - y)
    apply hS.mem_toFinset.mpr
    refine ⟨⟨x, hx, y, hy, rfl⟩, ?_⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] using hxy.le
  by_cases hab : a = b
  · subst b
    change ‖e (a - a)‖ ≤ c * dist a a
    simp
  by_cases hshort : dist a b ≤ rho
  · have hdist : dist a b < 4 * rho := by linarith
    have hδab : δ ≤ dist a b := hsep ha hb hab
    calc
      ‖deformPoint φ (a - b) - (a - b)‖ ≤ η := (hstep a ha b hb hdist).le
      _ ≤ c * δ := min_le_left _ _
      _ ≤ c * dist a b := mul_le_mul_of_nonneg_left hδab hc.le
  · have hlong : rho < dist b a := by simpa only [dist_comm] using lt_of_not_ge hshort
    obtain ⟨N, hN, p, hp0, hpN, hpstep, hcount⟩ :=
      denseSegmentChain Y rho rho (4 * rho) hrho hrho (by linarith)
        ⟨b, hb⟩ ⟨a, ha⟩ (hdense b hb a ha) hlong
    let pNat : ℕ → Plane := fun k ↦ if hk : k < N + 1 then p ⟨k, hk⟩ else 0
    have hpNat0 : pNat 0 = b := by
      simp only [pNat, dif_pos (by omega : 0 < N + 1)]
      exact congrArg Subtype.val hp0
    have hpNatN : pNat N = a := by
      simp only [pNat, dif_pos (by omega : N < N + 1)]
      exact congrArg Subtype.val hpN
    have hbound (k : ℕ) (hk : k ∈ Finset.range N) :
        ‖e (pNat (k + 1) - pNat k)‖ ≤ η := by
      have hkn := Finset.mem_range.mp hk
      have hk1 : k + 1 < N + 1 := by omega
      have hk0 : k < N + 1 := by omega
      simp only [pNat, dif_pos hk1, dif_pos hk0]
      exact (hstep _ (p ⟨k + 1, hk1⟩).2 _ (p ⟨k, hk0⟩).2
        (by simpa [dist_comm] using hpstep (⟨k, hkn⟩ : Fin N))).le
    have hsum : ∑ k ∈ Finset.range N, e (pNat (k + 1) - pNat k) = e (a - b) := by
      rw [← map_sum, Finset.sum_range_sub, hpNat0, hpNatN]
    have hNnonneg : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hηle : η ≤ c * rho / 2 := min_le_right _ _
    have hcountMul : (N : ℝ) * rho ≤ dist a b + rho := by
      have hh := (le_div_iff₀ hrho).mp (show (N : ℝ) ≤ (dist b a + rho) / rho by
        calc
          (N : ℝ) ≤ dist b a / rho + 1 := hcount
          _ = (dist b a + rho) / rho := by field_simp)
      simpa only [dist_comm] using hh
    calc
      ‖deformPoint φ (a - b) - (a - b)‖ = ‖e (a - b)‖ := rfl
      _ = ‖∑ k ∈ Finset.range N, e (pNat (k + 1) - pNat k)‖ := by rw [hsum]
      _ ≤ ∑ k ∈ Finset.range N, ‖e (pNat (k + 1) - pNat k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range N, η := Finset.sum_le_sum hbound
      _ = (N : ℝ) * η := by simp
      _ ≤ c * dist a b := by
        have := mul_le_mul_of_nonneg_left hηle hNnonneg
        nlinarith [mul_le_mul_of_nonneg_left hcountMul hc.le]

theorem approximation_globalRelativeError :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∀ c : ℝ, 0 < c → c < 1 → ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ a ∈ Y, ∀ b ∈ Y,
          ‖deformPoint φ (a - b) - (a - b)‖ ≤ c * dist a b := by
  intro Y hY ⟨rho, hrho, hdense⟩
  exact globalRelativeError_of_segmentDensity Y hY rho hrho
    (fun _ _ _ _ s ↦ hdense _)

private theorem deformation_lowerBound (φ : ℝ →ₗ[ℚ] ℚ) (a b : Plane) (c : ℝ)
    (herror : ‖deformPoint φ (a - b) - (a - b)‖ ≤ c * dist a b) :
    (1 - c) * dist a b ≤ dist (deformPoint φ a) (deformPoint φ b) := by
  have htriangle : dist a b ≤ ‖deformPoint φ (a - b) - (a - b)‖ +
      dist (deformPoint φ a) (deformPoint φ b) := by
    rw [dist_eq_norm, dist_eq_norm, ← deformPoint_sub]
    calc
      ‖a - b‖ = ‖((a - b) - deformPoint φ (a - b)) + deformPoint φ (a - b)‖ := by
        congr 1
        abel
      _ ≤ ‖(a - b) - deformPoint φ (a - b)‖ + ‖deformPoint φ (a - b)‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  nlinarith

private theorem finiteScalarReflection (Z : Finset ℝ) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ z ∈ Z, (φ z : ℝ) = 0 ↔ z = 0 := by
  classical
  obtain ⟨F, ε, hε, hreflect⟩ := finiteApproximation_signAndEquality (insert 0 Z)
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ z hz
  have heq := (hreflect φ hφ).2 z (Finset.mem_insert_of_mem hz) 0 (Finset.mem_insert_self _ _)
  simpa only [map_zero, Rat.cast_eq_zero] using heq

private theorem boundedDifference_mem {Y : Set Plane} {M : ℝ}
    (hfinite : ((Y - Y) ∩ Metric.closedBall 0 M).Finite)
    {a b : Plane} (ha : a ∈ Y) (hb : b ∈ Y) (hab : dist a b < M) :
    a - b ∈ hfinite.toFinset := by
  apply hfinite.mem_toFinset.mpr
  exact ⟨⟨a, ha, b, hb, rfl⟩, by simpa [Metric.mem_closedBall, dist_eq_norm] using hab.le⟩

theorem approximation_boundedMetricAndRelationControl :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∀ (M η : ℝ) (normals : Finset RationalNormal), 0 < M → 0 < η →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          Set.InjOn (deformPoint φ) Y ∧
          (∀ a ∈ Y, ∀ b ∈ Y, dist a b < M →
            dist (deformPoint φ a - deformPoint φ b) (a - b) < η) ∧
          (∀ a ∈ Y, ∀ b ∈ Y,
            dist (deformPoint φ a) (deformPoint φ b) < M / 2 → dist a b < M) ∧
          (∀ a ∈ Y, ∀ b ∈ Y,
            dist (deformPoint φ a) (deformPoint φ b) < M / 2 →
              ∀ n ∈ normals,
                normalEval n (deformPoint φ a - deformPoint φ b) = 0 ↔
                  normalEval n (a - b) = 0) := by
  classical
  intro Y hY hdense M η normals hM hη
  obtain ⟨F0, ε0, hε0, hglobal⟩ := approximation_globalRelativeError Y hY hdense
    (1 / 4) (by norm_num) (by norm_num)
  have hfinite := hY.2 M hM
  let D := hfinite.toFinset
  obtain ⟨F1, ε1, hε1, hlocal⟩ := finitePointControl D η hη
  let Z := (D.product normals).image (fun p ↦ normalEval p.2 p.1)
  obtain ⟨F2, ε2, hε2, hreflect⟩ := finiteScalarReflection Z
  let F := F0 ∪ (F1 ∪ F2)
  let ε := min ε0 (min ε1 ε2)
  refine ⟨F, ε, lt_min hε0 (lt_min hε1 hε2), ?_⟩
  intro φ hφ
  have hφ0 : IsFiniteApproximation F0 ε0 φ := finiteApproximation_strengthen F0 F ε0 ε φ
    (by intro x hx; exact Finset.mem_union_left _ hx) (min_le_left _ _) hφ
  have hφ1 : IsFiniteApproximation F1 ε1 φ := finiteApproximation_strengthen F1 F ε1 ε φ
    (by intro x hx; exact Finset.mem_union_right _ (Finset.mem_union_left _ hx))
    (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ2 : IsFiniteApproximation F2 ε2 φ := finiteApproximation_strengthen F2 F ε2 ε φ
    (by intro x hx; exact Finset.mem_union_right _ (Finset.mem_union_right _ hx))
    (le_trans (min_le_right _ _) (min_le_right _ _)) hφ
  have hlower (a : Plane) (ha : a ∈ Y) (b : Plane) (hb : b ∈ Y) :
      (1 - 1 / 4) * dist a b ≤ dist (deformPoint φ a) (deformPoint φ b) :=
    deformation_lowerBound φ a b _ (hglobal φ hφ0 a ha b hb)
  have hinverse (a : Plane) (ha : a ∈ Y) (b : Plane) (hb : b ∈ Y)
      (hab : dist (deformPoint φ a) (deformPoint φ b) < M / 2) : dist a b < M := by
    have := hlower a ha b hb
    nlinarith
  refine ⟨?_, ?_, hinverse, ?_⟩
  · intro a ha b hb hab
    have := hlower a ha b hb
    rw [hab, dist_self] at this
    exact dist_eq_zero.mp (by nlinarith [dist_nonneg (x := a) (y := b)])
  · intro a ha b hb hab
    rw [← deformPoint_sub, dist_eq_norm]
    exact hlocal φ hφ1 (a - b) (boundedDifference_mem hfinite ha hb hab)
  · intro a ha b hb hab n hn
    have hd : a - b ∈ D := boundedDifference_mem hfinite ha hb (hinverse a ha b hb hab)
    have hz : normalEval n (a - b) ∈ Z :=
      Finset.mem_image.mpr ⟨(a - b, n), Finset.mem_product.mpr ⟨hd, hn⟩, rfl⟩
    rw [← deformPoint_sub, rationalNormal_commutes]
    exact hreflect φ hφ2 _ hz

/-- Exact bounded scalar-displacement reflection needed by both period/gap lifting branches. -/
theorem approximation_reflectsBoundedDisplacement :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∀ M : ℝ, 0 < M → ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ a ∈ Y, ∀ b ∈ Y, ∀ c ∈ Y, ∀ d ∈ Y,
          dist (deformPoint φ a) (deformPoint φ b) < M / 2 →
          dist (deformPoint φ c) (deformPoint φ d) < M / 2 →
            (((deformPoint φ a - deformPoint φ b).re =
                (deformPoint φ c - deformPoint φ d).re) ↔ (a - b).re = (c - d).re) ∧
            (((deformPoint φ a - deformPoint φ b).im =
                (deformPoint φ c - deformPoint φ d).im) ↔ (a - b).im = (c - d).im) ∧
            ((deformPoint φ a - deformPoint φ b = deformPoint φ c - deformPoint φ d) ↔
              a - b = c - d) := by
  classical
  intro Y hY hdense M hM
  obtain ⟨F0, ε0, hε0, hmetric⟩ := approximation_boundedMetricAndRelationControl Y hY hdense
    M 1 ∅ hM zero_lt_one
  have hfinite := hY.2 M hM
  let D := hfinite.toFinset
  let Z := D.image Complex.re ∪ D.image Complex.im
  obtain ⟨F1, ε1, hε1, hequality⟩ := finiteApproximation_signAndEquality Z
  refine ⟨F0 ∪ F1, min ε0 ε1, lt_min hε0 hε1, ?_⟩
  intro φ hφ a ha b hb c hc d hd hab hcd
  have hφ0 : IsFiniteApproximation F0 ε0 φ := finiteApproximation_strengthen _ _ _ _ _
    (by intro x hx; exact Finset.mem_union_left _ hx) (min_le_left _ _) hφ
  have hφ1 : IsFiniteApproximation F1 ε1 φ := finiteApproximation_strengthen _ _ _ _ _
    (by intro x hx; exact Finset.mem_union_right _ hx) (min_le_right _ _) hφ
  have hdab : a - b ∈ D := boundedDifference_mem hfinite ha hb ((hmetric φ hφ0).2.2.1 a ha b hb hab)
  have hdcd : c - d ∈ D := boundedDifference_mem hfinite hc hd ((hmetric φ hφ0).2.2.1 c hc d hd hcd)
  have hre : (deformPoint φ a - deformPoint φ b).re =
      (deformPoint φ c - deformPoint φ d).re ↔ (a - b).re = (c - d).re := by
    rw [← deformPoint_sub, ← deformPoint_sub]
    change (φ (a - b).re : ℝ) = (φ (c - d).re : ℝ) ↔ (a - b).re = (c - d).re
    rw [Rat.cast_inj]
    exact (hequality φ hφ1).2 _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hdab, rfl⟩))
      _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hdcd, rfl⟩))
  have him : (deformPoint φ a - deformPoint φ b).im =
      (deformPoint φ c - deformPoint φ d).im ↔ (a - b).im = (c - d).im := by
    rw [← deformPoint_sub, ← deformPoint_sub]
    change (φ (a - b).im : ℝ) = (φ (c - d).im : ℝ) ↔ (a - b).im = (c - d).im
    rw [Rat.cast_inj]
    exact (hequality φ hφ1).2 _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hdab, rfl⟩))
      _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hdcd, rfl⟩))
  refine ⟨hre, him, ?_⟩
  rw [Complex.ext_iff, Complex.ext_iff, hre, him]

private theorem hasFLC_image_of_coarseBound
    (Y : Set Plane) (hY : Tiling.Polygonal.HasFLC Y)
    (f : Plane →+ Plane)
    (hlower : ∀ a ∈ Y, ∀ b ∈ Y,
      (1 / 2 : ℝ) * dist a b ≤ dist (f a) (f b)) :
    Tiling.Polygonal.HasFLC (f '' Y) := by
  classical
  constructor
  · intro Q hQ
    by_cases hne : Y.Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : Plane)
      let S : Set Plane := Y ∩ Metric.closedBall y₀ (2 * (R + dist (f y₀) 0))
      have hSfinite : S.Finite := by
        exact hY.1 _ Metric.isBounded_closedBall
      apply (hSfinite.image f).subset
      rintro z ⟨⟨x, hxY, rfl⟩, hzQ⟩
      refine ⟨x, ⟨hxY, ?_⟩, rfl⟩
      have hfxR : dist (f x) 0 ≤ R := hQR hzQ
      have himage : dist (f x) (f y₀) ≤ R + dist (f y₀) 0 := by
        calc
          dist (f x) (f y₀) ≤ dist (f x) 0 + dist 0 (f y₀) := dist_triangle _ _ _
          _ = dist (f x) 0 + dist (f y₀) 0 := by rw [dist_comm 0 (f y₀)]
          _ ≤ R + dist (f y₀) 0 := by nlinarith [hfxR]
      have hsource := hlower x hxY y₀ hy₀
      rw [Metric.mem_closedBall]
      nlinarith
    · have hempty : f '' Y = ∅ := Set.image_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hne)
      simp [hempty]
  · intro R hR
    let D : Set Plane := (Y - Y) ∩ Metric.closedBall 0 (2 * R)
    have hDfinite : D.Finite := hY.2 (2 * R) (by positivity)
    apply (hDfinite.image f).subset
    rintro z ⟨⟨fa, hfa, fb, hfb, hzEq⟩, hz⟩
    rcases hfa with ⟨a, ha, rfl⟩
    rcases hfb with ⟨b, hb, rfl⟩
    refine ⟨a - b, ?_, ?_⟩
    · refine ⟨⟨a, ha, b, hb, rfl⟩, ?_⟩
      rw [Metric.mem_closedBall]
      have hsource := hlower a ha b hb
      have himage : dist (f a - f b) 0 = dist (f a) (f b) := by simp [dist_eq_norm]
      have hab : dist (a - b) 0 = dist a b := by simp [dist_eq_norm]
      rw [hab]
      have hz' : dist (f a - f b) 0 ≤ R := by simpa [hzEq] using hz
      rw [himage] at hz'
      nlinarith
    · simpa [map_sub] using hzEq

theorem approximation_preservesFLC :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        Tiling.Polygonal.HasFLC (deformPoint φ '' Y) := by
  intro Y hY hdense
  obtain ⟨F, ε, hε, hglobal⟩ := approximation_globalRelativeError Y hY hdense
    (1 / 2) (by norm_num) (by norm_num)
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  apply hasFLC_image_of_coarseBound Y hY (deformPointLinear φ).toAddMonoidHom
  intro a ha b hb
  change (1 / 2 : ℝ) * dist a b ≤ dist (deformPoint φ a) (deformPoint φ b)
  simpa only [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] using
    deformation_lowerBound φ a b (1 / 2) (hglobal φ hφ a ha b hb)

/-- The global vector relative-error estimate yields image density by an elementary
Lipschitz-perturbation recurrence; no carrier periods or ambient extension theorem is used. -/
theorem approximation_uniformImageDensity :
  ∀ Y : Set Plane, Tiling.Polygonal.HasFLC Y → RelativeDense Y →
    ∃ F : Finset ℝ, ∃ ε ρ : ℝ, 0 < ε ∧ 0 < ρ ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ z : Plane, ∃ y ∈ deformPoint φ '' Y, dist z y < ρ := by
  classical
  intro Y hY hdense
  obtain ⟨F, ε, hε, hglobal⟩ := approximation_globalRelativeError Y hY hdense
    (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨rho, hrho, hsource⟩ := hdense
  refine ⟨F, ε, 6 * rho, hε, by positivity, ?_⟩
  intro φ hφ z
  let f := deformPointLinear φ
  let e : Plane →+ Plane := f.toAddMonoidHom - AddMonoidHom.id Plane
  have he (x : Plane) : e x = deformPoint φ x - x := rfl
  have hlip (x : Plane) (hx : x ∈ Y) (y : Plane) (hy : y ∈ Y) :
      dist (e x) (e y) ≤ (1 / 2) * dist x y := by
    rw [dist_eq_norm, ← map_sub]
    exact hglobal φ hφ x hx y hy
  have hnext (p : Plane) (hp : p ∈ Y) :
      ∃ q ∈ Y, dist (f q) z < 3 * rho / 2 + dist (f p) z / 2 := by
    obtain ⟨q, hq, hqclose⟩ := hsource (z - e p)
    have hqnear : dist q (z - e p) < rho := by simpa only [dist_comm] using hqclose
    have hcenter : dist (z - e p) p = dist (f p) z := by
      rw [dist_eq_norm, dist_eq_norm, norm_sub_rev (f p)]
      congr 1
      dsimp [e, f, deformPointLinear]
      abel
    have hqp : dist q p < rho + dist (f p) z := by
      have := dist_triangle q (z - e p) p
      rw [hcenter] at this
      linarith
    have hvector : f q - z = (q - (z - e p)) + (e q - e p) := by
      dsimp [e, f, deformPointLinear]
      abel
    have herror : dist (f q) z ≤ dist q (z - e p) + dist (e q) (e p) := by
      simp only [dist_eq_norm]
      rw [hvector]
      exact norm_add_le (q - (z - e p)) (e q - e p)
    refine ⟨q, hq, ?_⟩
    have hg := hlip q hq p hp
    linarith
  obtain ⟨p0, hp0, _⟩ := hsource 0
  let E0 := dist (f p0) z
  have hiter : ∀ k : ℕ, ∃ p ∈ Y,
      dist (f p) z ≤ (1 / 2 : ℝ) ^ k * E0 + 3 * rho := by
    intro k
    induction k with
    | zero =>
        refine ⟨p0, hp0, ?_⟩
        simp only [pow_zero, one_mul]
        dsimp [E0]
        linarith
    | succ k ih =>
        obtain ⟨p, hp, he⟩ := ih
        obtain ⟨q, hq, hqerror⟩ := hnext p hp
        refine ⟨q, hq, ?_⟩
        rw [pow_succ]
        nlinarith
  have hE0 : 0 ≤ E0 := dist_nonneg
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hrho (by linarith : 0 < E0 + 1))
    (by norm_num : (1 / 2 : ℝ) < 1)
  have hsmall : (1 / 2 : ℝ) ^ N * E0 < rho := by
    have hmul := (lt_div_iff₀ (by linarith : 0 < E0 + 1)).mp hN
    have hpow := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) N
    nlinarith
  obtain ⟨p, hp, herror⟩ := hiter N
  refine ⟨f p, ⟨p, hp, rfl⟩, ?_⟩
  rw [dist_comm]
  linarith

/-- Centres relatively dense on one rational affine line need their own bounded-gap proof;
they do not satisfy plane RelativeDense. The finite decoration is just algebraic here. -/
theorem approximation_lineRelativeError :
  ∀ (T : Set Plane) (W : Finset Plane) (n : RationalNormal) (a : Plane),
    W.Nonempty → Tiling.Polygonal.HasFLC T →
    (∀ t ∈ T, normalEval n (t - a) = 0) →
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ z : Plane, normalEval n (z - a) = 0 →
      ∃ t ∈ T, dist z t < ρ) →
      ∀ c : ℝ, 0 < c → c < 1 → ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∀ x ∈ (W : Set Plane) + T, ∀ y ∈ (W : Set Plane) + T,
            ‖deformPoint φ (x - y) - (x - y)‖ ≤ c * dist x y := by
  classical
  intro T W n a _ hT hsupport ⟨rho, hrho, hlineDense⟩ c hc hc1
  have hsegmentDense : ∀ t ∈ T, ∀ u ∈ T, ∀ s : ℝ,
      ∃ q ∈ T, dist (t + s • (u - t)) q < rho := by
    intro t ht u hu s
    apply hlineDense
    have htline := hsupport t ht
    have huline := hsupport u hu
    simp only [normalEval, Complex.sub_re, Complex.sub_im] at htline huline
    simp only [normalEval, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
    linear_combination (1 - s) * htline + s * huline
  obtain ⟨F0, ε0, hε0, hTerror⟩ := globalRelativeError_of_segmentDensity T hT rho hrho
    hsegmentDense (c / 4) (by positivity) (by linarith)
  let cloud := (W : Set Plane) + T
  have hcloud : Tiling.Polygonal.HasFLC cloud := by
    simpa only [cloud, add_comm] using hT.add_finset W
  let offsets : Finset Plane := W - W
  obtain ⟨R, hR⟩ := offsets.finite_toSet.isBounded.subset_closedBall (0 : Plane)
  let L := max 1 R
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hoffsetBound (z : Plane) (hz : z ∈ offsets) : ‖z‖ ≤ L := by
    have hzR := hR hz
    have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hzR
    exact hn.trans (le_max_right _ _)
  obtain ⟨δ, hδ, hsep⟩ := hcloud.uniformlyDiscrete
  have hfinite := hcloud.2 L hL
  let D := hfinite.toFinset
  obtain ⟨F1, ε1, hε1, hoffset⟩ := finitePointControl offsets (c * L / 4) (by positivity)
  obtain ⟨F2, ε2, hε2, hshortError⟩ := finitePointControl D (c * δ) (mul_pos hc hδ)
  let F := F0 ∪ (F1 ∪ F2)
  let ε := min ε0 (min ε1 ε2)
  refine ⟨F, ε, lt_min hε0 (lt_min hε1 hε2), ?_⟩
  intro φ hφ x hx y hy
  have hφ0 : IsFiniteApproximation F0 ε0 φ := finiteApproximation_strengthen F0 F ε0 ε φ
    (by intro z hz; exact Finset.mem_union_left _ hz) (min_le_left _ _) hφ
  have hφ1 : IsFiniteApproximation F1 ε1 φ := finiteApproximation_strengthen F1 F ε1 ε φ
    (by intro z hz; exact Finset.mem_union_right _ (Finset.mem_union_left _ hz))
    (le_trans (min_le_right _ _) (min_le_left _ _)) hφ
  have hφ2 : IsFiniteApproximation F2 ε2 φ := finiteApproximation_strengthen F2 F ε2 ε φ
    (by intro z hz; exact Finset.mem_union_right _ (Finset.mem_union_right _ hz))
    (le_trans (min_le_right _ _) (min_le_right _ _)) hφ
  let e : Plane →+ Plane := (deformPointLinear φ).toAddMonoidHom - AddMonoidHom.id Plane
  by_cases hxy : x = y
  · subst y
    change ‖e (x - x)‖ ≤ c * dist x x
    simp
  by_cases hsmall : dist x y < L
  · have hdiff : x - y ∈ D := boundedDifference_mem hfinite hx hy hsmall
    have hδxy : δ ≤ dist x y := hsep hx hy hxy
    exact (hshortError φ hφ2 _ hdiff).le.trans
      (mul_le_mul_of_nonneg_left hδxy hc.le)
  · have hlarge : L ≤ dist x y := le_of_not_gt hsmall
    rcases hx with ⟨w, hw, t, ht, rfl⟩
    rcases hy with ⟨v, hv, s, hs, rfl⟩
    have hdiff : w - v ∈ offsets := Finset.mem_sub.mpr ⟨w, hw, v, hv, rfl⟩
    have hnorm := hoffsetBound _ hdiff
    have hTS : dist t s ≤ dist (w + t) (v + s) + L := by
      rw [dist_eq_norm, dist_eq_norm]
      calc
        ‖t - s‖ = ‖((w + t) - (v + s)) - (w - v)‖ := by congr 1; abel
        _ ≤ ‖(w + t) - (v + s)‖ + ‖w - v‖ := norm_sub_le _ _
        _ ≤ ‖(w + t) - (v + s)‖ + L := by linarith
    have hdecomp : (w + t) - (v + s) = (t - s) + (w - v) := by abel
    have hdecError : ‖e (w - v)‖ ≤ c * L / 4 := (hoffset φ hφ1 _ hdiff).le
    have hlineError : ‖e (t - s)‖ ≤ c / 4 * dist t s := hTerror φ hφ0 t ht s hs
    change ‖e ((w + t) - (v + s))‖ ≤ c * dist (w + t) (v + s)
    rw [hdecomp, map_add]
    calc
      ‖e (t - s) + e (w - v)‖ ≤ ‖e (t - s)‖ + ‖e (w - v)‖ := norm_add_le _ _
      _ ≤ c * dist (w + t) (v + s) := by
        nlinarith [mul_le_mul_of_nonneg_left hTS hc.le,
          mul_le_mul_of_nonneg_left hlarge hc.le]

end Tiling.RationalSlopes.Approximation
