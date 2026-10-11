import Mathlib.Algebra.Order.Archimedean.Real.Basic
import TranslationalTilings.Basic

/-!
# Backward finite differences

This file supplies the backward-difference convention used in the paper and
relates it to Mathlib's forward differences.  It also proves the two bounded
finite-difference rigidity lemmas and the finite elimination identity used in
the periodic decomposition arguments.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The paper's backward difference, `f(x) - f(x-h)`. -/
def backwardDiff {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (f : G → R) : G → R := fun x ↦ f x - f (x - h)

/-- The `n`-fold backward difference in a fixed direction. -/
def backwardDiffIter {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (n : ℕ) (f : G → R) : G → R :=
  (backwardDiff h)^[n] f

/-- Restriction of a function to an integral affine line. -/
def lineRestriction {G R : Type*} [AddCommGroup G]
    (f : G → R) (x h : G) : ℤ → R := fun n ↦ f (x + n • h)

/-- Difference directions which eliminate all summands except `target`. -/
noncomputable def eliminationDirections
    {ι G : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup G]
    (target : ι) (e : G) (period : ι → G)
    (targetCoefficient : ι → ℤ) : List G :=
  (Finset.univ.erase target).toList.map fun i ↦
    e - targetCoefficient i • period target

/-- Apply a list of backward-difference operators, from right to left. -/
def applyDifferences {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (f : G → R) : G → R :=
  directions.foldr backwardDiff f

/-- A backward difference is a translated forward difference. -/
theorem backwardDiff_eq_fwdDiff {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R) :
    backwardDiff h f = fun x ↦ fwdDiff h f (x - h) := by
  funext x
  simp [backwardDiff, fwdDiff]

/-- Backward difference is additive in the function. -/
theorem backwardDiff_add {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h : G) (f g : G → R) :
    backwardDiff h (f + g) = backwardDiff h f + backwardDiff h g := by
  funext x
  simp only [backwardDiff, Pi.add_apply]
  abel

/-- Backward differences in two directions commute. -/
theorem backwardDiff_comm {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (h k : G) (f : G → R) :
    backwardDiff h (backwardDiff k f) =
      backwardDiff k (backwardDiff h f) := by
  funext x
  simp only [backwardDiff]
  rw [show x - k - h = x - h - k by abel]
  abel

/-- Backward difference commutes with convolution by a finite tile. -/
theorem backwardDiff_tileConv {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (h : G) (F : Finset G) (f : G → R) :
    backwardDiff h (tileConv F f) = tileConv F (backwardDiff h f) := by
  funext x
  simp only [backwardDiff, tileConv, Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [show x - h - a = x - a - h by abel]

/-- The backward difference in a period direction vanishes. -/
theorem backwardDiff_eq_zero_of_periodic {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) (f : G → R)
    (hf : Function.Periodic f h) : backwardDiff h f = 0 := by
  funext x
  simp [backwardDiff, hf.sub_eq]

/-- Adding a period to a difference direction does not change the difference. -/
theorem backwardDiff_sub_period_eq {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h k : G) (f : G → R)
    (hf : Function.Periodic f k) :
    backwardDiff (h + k) f = backwardDiff h f := by
  funext x
  simp only [backwardDiff]
  rw [show x - (h + k) = (x - h) - k by abel, hf.sub_eq]

/-- Restricting a directional difference to its line gives the unit integer difference. -/
theorem lineRestriction_backwardDiff {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (f : G → R) (x h : G) :
    lineRestriction (backwardDiff h f) x h =
      backwardDiff 1 (lineRestriction f x h) := by
  funext n
  simp only [lineRestriction, backwardDiff]
  congr 1
  rw [sub_smul]
  simp
  abel_nf

private theorem periodic_of_backwardDiff_one_eq_zero
    {R : Type*} [AddCommGroup R] (f : ℤ → R)
    (hdiff : backwardDiff 1 f = 0) : Function.Periodic f 1 := by
  intro z
  have hz := congrFun hdiff (z + 1)
  simp only [backwardDiff, Pi.zero_apply] at hz
  have : f (z + 1) = f ((z + 1) - 1) := sub_eq_zero.mp hz
  simpa using this

private theorem backwardDiff_periodic {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] {p : G} {f : G → R}
    (hf : Function.Periodic f p) (h : G) :
    Function.Periodic (backwardDiff h f) p := by
  intro x
  simp only [backwardDiff]
  rw [hf x]
  congr 1
  rw [show x + p - h = (x - h) + p by abel, hf (x - h)]

private theorem periodic_backwardDiff_eq_zero_of_int_bounded
    (f : ℤ → ℤ) (C : ℕ) (hbounded : ∀ z, Int.natAbs (f z) ≤ C)
    (hperiod : Function.Periodic (backwardDiff 1 f) 1) :
    backwardDiff 1 f = 0 := by
  let c : ℤ := backwardDiff 1 f 0
  have hconst (z : ℤ) : backwardDiff 1 f z = c := by
    have hz := hperiod.zsmul_eq z
    simpa [c] using hz
  have hline (m : ℕ) : f (m : ℤ) = f 0 + m • c := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hs := hconst ((m + 1 : ℕ) : ℤ)
        simp only [backwardDiff] at hs
        have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
        rw [hsub, ih] at hs
        rw [eq_add_of_sub_eq hs]
        simp only [add_nsmul]
        abel
  by_contra hc
  have hc' : c ≠ 0 := by
    intro hcz
    apply hc
    funext z
    simp [hconst z, hcz]
  let m : ℕ := 2 * C + 1
  have hupper : Int.natAbs (f (m : ℤ) - f 0) ≤ 2 * C := by
    calc
      Int.natAbs (f (m : ℤ) - f 0) ≤
          Int.natAbs (f (m : ℤ)) + Int.natAbs (f 0) := Int.natAbs_sub_le ..
      _ ≤ C + C := Nat.add_le_add (hbounded _) (hbounded _)
      _ = 2 * C := by omega
  have hcabs : 1 ≤ Int.natAbs c := by
    exact Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hc')
  have hlower : m ≤ Int.natAbs (f (m : ℤ) - f 0) := by
    rw [hline]
    simp only [add_sub_cancel_left]
    simpa [nsmul_eq_mul, Int.natAbs_mul] using
      Nat.mul_le_mul_left m hcabs
  dsimp [m] at hupper hlower
  omega

private theorem periodic_backwardDiff_eq_zero_of_real_bounded
    (f : ℤ → ℝ) (C : ℝ) (hbounded : ∀ z, |f z| ≤ C)
    (hperiod : Function.Periodic (backwardDiff 1 f) 1) :
    backwardDiff 1 f = 0 := by
  let c : ℝ := backwardDiff 1 f 0
  have hconst (z : ℤ) : backwardDiff 1 f z = c := by
    have hz := hperiod.zsmul_eq z
    simpa [c] using hz
  have hline (m : ℕ) : f (m : ℤ) = f 0 + m • c := by
    induction m with
    | zero => simp
    | succ m ih =>
        have hs := hconst ((m + 1 : ℕ) : ℤ)
        simp only [backwardDiff] at hs
        have hsub : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by omega
        rw [hsub, ih] at hs
        rw [eq_add_of_sub_eq hs]
        simp only [add_nsmul]
        abel
  by_contra hc
  have hc' : c ≠ 0 := by
    intro hcz
    apply hc
    funext z
    simp [hconst z, hcz]
  have hcpos : 0 < |c| := abs_pos.mpr hc'
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * C / |c|)
  have hgrowth : 2 * C < (m : ℝ) * |c| := by
    simpa [mul_comm] using (div_lt_iff₀' hcpos).mp hm
  have hupper : |f (m : ℤ) - f 0| ≤ 2 * C := by
    calc
      |f (m : ℤ) - f 0| ≤ |f (m : ℤ)| + |f 0| := abs_sub ..
      _ ≤ C + C := add_le_add (hbounded _) (hbounded _)
      _ = 2 * C := by ring
  have hvalue : |f (m : ℤ) - f 0| = (m : ℝ) * |c| := by
    rw [hline]
    simp [nsmul_eq_mul, abs_mul]
  linarith

/-- A bounded integer-valued function with a vanishing iterated unit difference is constant. -/
theorem bounded_of_backwardDiffIter_eq_zero_is_constant
    (n : ℕ) (hn : 0 < n) (f : ℤ → ℤ)
    (hbounded : ∃ C : ℕ, ∀ z, Int.natAbs (f z) ≤ C)
    (hdiff : backwardDiffIter 1 n f = 0) : Function.Periodic f 1 := by
  induction n generalizing f with
  | zero => omega
  | succ m ih =>
      let g : ℤ → ℤ := backwardDiff 1 f
      have hgdiff : backwardDiffIter 1 m g = 0 := by
        simpa only [backwardDiffIter, Function.iterate_succ_apply] using hdiff
      by_cases hm : m = 0
      · subst m
        have hgzero : g = 0 := by
          simpa only [backwardDiffIter, Function.iterate_zero, id_eq] using hgdiff
        exact periodic_of_backwardDiff_one_eq_zero f hgzero
      · obtain ⟨C, hC⟩ := hbounded
        have hgbounded : ∃ D : ℕ, ∀ z, Int.natAbs (g z) ≤ D := by
          refine ⟨2 * C, fun z ↦ ?_⟩
          calc
            Int.natAbs (g z) = Int.natAbs (f z - f (z - 1)) := by
              rfl
            _ ≤ Int.natAbs (f z) + Int.natAbs (f (z - 1)) := Int.natAbs_sub_le ..
            _ ≤ C + C := Nat.add_le_add (hC _) (hC _)
            _ = 2 * C := by omega
        have hgperiod : Function.Periodic g 1 :=
          ih (Nat.pos_of_ne_zero hm) g hgbounded hgdiff
        exact periodic_of_backwardDiff_one_eq_zero f
          (periodic_backwardDiff_eq_zero_of_int_bounded f C hC hgperiod)

/-- A bounded real-valued function with a vanishing iterated unit difference is constant. -/
theorem bounded_real_of_backwardDiffIter_eq_zero_is_constant
    (n : ℕ) (hn : 0 < n) (f : ℤ → ℝ)
    (hbounded : ∃ C : ℝ, ∀ z, |f z| ≤ C)
    (hdiff : backwardDiffIter 1 n f = 0) : Function.Periodic f 1 := by
  induction n generalizing f with
  | zero => omega
  | succ m ih =>
      let g : ℤ → ℝ := backwardDiff 1 f
      have hgdiff : backwardDiffIter 1 m g = 0 := by
        simpa only [backwardDiffIter, Function.iterate_succ_apply] using hdiff
      by_cases hm : m = 0
      · subst m
        have hgzero : g = 0 := by
          simpa only [backwardDiffIter, Function.iterate_zero, id_eq] using hgdiff
        exact periodic_of_backwardDiff_one_eq_zero f hgzero
      · obtain ⟨C, hC⟩ := hbounded
        have hgbounded : ∃ D : ℝ, ∀ z, |g z| ≤ D := by
          refine ⟨2 * C, fun z ↦ ?_⟩
          calc
            |g z| = |f z - f (z - 1)| := by rfl
            _ ≤ |f z| + |f (z - 1)| := abs_sub ..
            _ ≤ C + C := add_le_add (hC _) (hC _)
            _ = 2 * C := by ring
        have hgperiod : Function.Periodic g 1 :=
          ih (Nat.pos_of_ne_zero hm) g hgbounded hgdiff
        exact periodic_of_backwardDiff_one_eq_zero f
          (periodic_backwardDiff_eq_zero_of_real_bounded f C hC hgperiod)

private theorem backwardDiff_zero {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (h : G) :
    backwardDiff h (0 : G → R) = 0 := by
  funext x
  simp [backwardDiff]

private theorem applyDifferences_zero {G R : Type*}
    [AddCommGroup G] [AddCommGroup R] (directions : List G) :
    applyDifferences directions (0 : G → R) = 0 := by
  induction directions with
  | nil => rfl
  | cons h directions ih =>
      change backwardDiff h (applyDifferences directions (0 : G → R)) = 0
      rw [ih, backwardDiff_zero]

private theorem applyDifferences_add {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (f g : G → R) :
    applyDifferences directions (f + g) =
      applyDifferences directions f + applyDifferences directions g := by
  induction directions with
  | nil => rfl
  | cons h directions ih =>
      change backwardDiff h (applyDifferences directions (f + g)) =
        backwardDiff h (applyDifferences directions f) +
          backwardDiff h (applyDifferences directions g)
      rw [ih, backwardDiff_add]

private theorem applyDifferences_finset_sum {G R α : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (s : Finset α) (f : α → G → R) :
    applyDifferences directions (∑ i ∈ s, f i) =
      ∑ i ∈ s, applyDifferences directions (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [applyDifferences_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [applyDifferences_add, ih]

private theorem backwardDiff_applyDifferences {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (h : G) (directions : List G) (f : G → R) :
    backwardDiff h (applyDifferences directions f) =
      applyDifferences directions (backwardDiff h f) := by
  induction directions with
  | nil => rfl
  | cons k directions ih =>
      change backwardDiff h (backwardDiff k (applyDifferences directions f)) =
        backwardDiff k (applyDifferences directions (backwardDiff h f))
      rw [backwardDiff_comm, ih]

private theorem applyDifferences_eq_zero_of_mem {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (h : G) (f : G → R)
    (hmem : h ∈ directions) (hzero : backwardDiff h f = 0) :
    applyDifferences directions f = 0 := by
  induction directions with
  | nil => simp at hmem
  | cons k directions ih =>
      rcases List.mem_cons.mp hmem with rfl | hmem
      · change backwardDiff h (applyDifferences directions f) = 0
        rw [backwardDiff_applyDifferences, hzero, applyDifferences_zero]
      · change backwardDiff k (applyDifferences directions f) = 0
        rw [ih hmem, backwardDiff_zero]

private theorem iterate_backwardDiff_periodic {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    {p : G} {f : G → R} (hf : Function.Periodic f p)
    (e : G) (n : ℕ) :
    Function.Periodic (backwardDiffIter e n f) p := by
  induction n with
  | zero => simpa [backwardDiffIter]
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply']
      exact backwardDiff_periodic ih e

private theorem applyDifferences_eq_iter_of_periodic {G R : Type*}
    [AddCommGroup G] [AddCommGroup R]
    (directions : List G) (e p : G) (f : G → R)
    (hf : Function.Periodic f p)
    (hdir : ∀ d ∈ directions, ∃ b : ℤ, d = e - b • p) :
    applyDifferences directions f =
      backwardDiffIter e directions.length f := by
  induction directions with
  | nil => simp [applyDifferences, backwardDiffIter]
  | cons d directions ih =>
      obtain ⟨b, rfl⟩ := hdir d (by simp)
      have htail : ∀ k ∈ directions, ∃ b : ℤ, k = e - b • p :=
        fun k hk ↦ hdir k (by simp [hk])
      have hper : Function.Periodic
          (backwardDiffIter e directions.length f) ((-b) • p) :=
        (iterate_backwardDiff_periodic hf e directions.length).zsmul (-b)
      change backwardDiff (e - b • p) (applyDifferences directions f) =
        backwardDiffIter e (directions.length + 1) f
      rw [ih htail]
      have hstep := backwardDiff_sub_period_eq e ((-b) • p)
        (backwardDiffIter e directions.length f) hper
      rw [show e - b • p = e + (-b) • p by
        rw [sub_eq_add_neg, neg_zsmul]]
      rw [hstep]
      simp only [backwardDiffIter, Function.iterate_succ_apply']

/-- The prescribed difference directions eliminate all periodic summands except the target. -/
theorem eliminate_periodic_summands
    {ι G R : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [AddCommGroup R]
    (target : ι) (lhs : G → R) (summand : ι → G → R)
    (e : G) (period : ι → G) (targetCoefficient : ι → ℤ)
    (decomp : lhs = ∑ i, summand i)
    (hperiod : ∀ i, Function.Periodic (summand i) (period i))
    (represent : ∀ i, i ≠ target → ∃ a : ℤ,
      e = a • period i + targetCoefficient i • period target) :
    applyDifferences
        (eliminationDirections target e period targetCoefficient) lhs =
      backwardDiffIter e (Fintype.card ι - 1) (summand target) := by
  classical
  rw [decomp, applyDifferences_finset_sum]
  rw [Finset.sum_eq_single target]
  · have hdirs : ∀ d ∈ eliminationDirections target e period targetCoefficient,
        ∃ b : ℤ, d = e - b • period target := by
      intro d hd
      simp only [eliminationDirections, List.mem_map, Finset.mem_toList] at hd
      obtain ⟨i, -, rfl⟩ := hd
      exact ⟨targetCoefficient i, rfl⟩
    rw [applyDifferences_eq_iter_of_periodic _ e (period target)
      (summand target) (hperiod target) hdirs]
    congr 2
    simp [eliminationDirections]
  · intro i hi hne
    obtain ⟨a, ha⟩ := represent i hne
    have hmem : e - targetCoefficient i • period target ∈
        eliminationDirections target e period targetCoefficient := by
      apply List.mem_map_of_mem
      simp [hne]
    apply applyDifferences_eq_zero_of_mem _ _ _ hmem
    apply backwardDiff_eq_zero_of_periodic
    rw [ha]
    simp only [add_sub_cancel_right]
    exact (hperiod i).zsmul a
  · simp

end TranslationalTilings
