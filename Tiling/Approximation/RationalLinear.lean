import Tiling.Geometry.Plane
import Mathlib.Data.Real.Sign

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

open Module

namespace Tiling.Approximation

def IsFiniteApproximation (F : Finset ℝ) (ε : ℝ) (φ : ℝ →ₗ[ℚ] ℚ) : Prop :=
  φ 1 = 1 ∧ ∀ x ∈ F, |(φ x : ℝ) - x| < ε

structure RationalNormal where
  x : ℚ
  y : ℚ
  nonzero : x ≠ 0 ∨ y ≠ 0

def normalEval (n : RationalNormal) (z : Plane) : ℝ :=
  (n.x : ℝ) * z.re + (n.y : ℝ) * z.im

def normalDirection (n : RationalNormal) : Submodule ℝ Plane :=
  LinearMap.ker
    (((n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM).toLinearMap)

def deformPoint (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane) : Plane :=
  Complex.mk (φ z.re) (φ z.im)

def deformPointLinear (φ : ℝ →ₗ[ℚ] ℚ) : Plane →ₗ[ℚ] Plane where
  toFun := deformPoint φ
  map_add' z w := by
    apply Complex.ext <;> simp [deformPoint, map_add]
  map_smul' q z := by
    apply Complex.ext <;> dsimp [deformPoint] <;>
      simp only [Complex.smul_re, Complex.smul_im, map_smul] <;> simp [Rat.smul_def]

private def finiteBasisWeight {ι : Type*} (b : Basis ι ℚ ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ (b.repr x).support, |((b.repr x j) : ℝ)|

private theorem finiteBasisWeight_nonneg {ι : Type*} (b : Basis ι ℚ ℝ) (x : ℝ) :
    0 ≤ finiteBasisWeight b x :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

private theorem finiteBasisError {ι : Type*} (b : Basis ι ℚ ℝ)
    (φ : ℝ →ₗ[ℚ] ℚ) (x : ℝ) :
    (φ x : ℝ) - x = ∑ j ∈ (b.repr x).support,
      ((b.repr x j) : ℝ) * ((φ (b j) : ℝ) - b j) := by
  have hx : ∑ j ∈ (b.repr x).support, (b.repr x j) • b j = x := by
    simpa only [b.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum] using
      b.repr.symm_apply_apply x
  have hφ : (φ x : ℝ) = ∑ j ∈ (b.repr x).support,
      ((b.repr x j) : ℝ) * (φ (b j) : ℝ) := by
    have hφrat := congrArg φ hx
    rw [← hφrat]
    simp only [map_sum, Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [φ.map_smul]
    simp only [Rat.smul_def, Rat.cast_mul, Rat.cast_id]
  have hval : x = ∑ j ∈ (b.repr x).support, ((b.repr x j) : ℝ) * b j := by
    simpa only [Rat.smul_def] using hx.symm
  calc
    (φ x : ℝ) - x =
        (∑ j ∈ (b.repr x).support, ((b.repr x j) : ℝ) * (φ (b j) : ℝ)) -
        (∑ j ∈ (b.repr x).support, ((b.repr x j) : ℝ) * b j) :=
      congrArg₂ (fun a c : ℝ ↦ a - c) hφ hval
    _ = _ := by simp only [mul_sub, Finset.sum_sub_distrib]

private theorem finitePositiveGap (F : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, x ≠ 0 → ε ≤ |x| := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a F _ ih =>
    obtain ⟨ε, hε, hbound⟩ := ih
    by_cases ha : a = 0
    · refine ⟨ε, hε, ?_⟩
      intro x hx hx0
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (hx0 ha).elim
      · exact hbound x hx hx0
    · refine ⟨min ε |a|, lt_min hε (abs_pos.mpr ha), ?_⟩
      intro x hx hx0
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound x hx hx0)

private theorem finiteSignOfError (φ : ℝ →ₗ[ℚ] ℚ) (x : ℝ)
    (herror : x ≠ 0 → |(φ x : ℝ) - x| < |x|) :
    Real.sign (φ x : ℝ) = Real.sign x := by
  obtain hx | rfl | hx := lt_trichotomy x 0
  · have herr := (abs_lt.mp (herror (ne_of_lt hx))).2
    rw [abs_of_neg hx] at herr
    have himage : (φ x : ℝ) < 0 := by linarith
    rw [Real.sign_of_neg himage, Real.sign_of_neg hx]
  · simp only [map_zero, Rat.cast_zero]
  · have herr := (abs_lt.mp (herror (ne_of_gt hx))).1
    rw [abs_of_pos hx] at herr
    have himage : 0 < (φ x : ℝ) := by linarith
    rw [Real.sign_of_pos himage, Real.sign_of_pos hx]

theorem exists_finiteApproximation :
  ∀ (F : Finset ℝ) (ε : ℝ), 0 < ε →
    ∃ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ := by
  classical
  intro F ε hε
  -- A basis containing 1 makes rational fixation exact, independently of the tests.
  have hlin : LinearIndepOn ℚ id ({1} : Set ℝ) :=
    (linearIndepOn_singleton_iff ℚ).mpr one_ne_zero
  let b := Basis.extend hlin
  let j₀ : hlin.extend (Set.subset_univ _) :=
    ⟨1, hlin.subset_extend _ (by simp)⟩
  have hbj₀ : b j₀ = 1 := Basis.extend_apply_self hlin j₀
  let B : ℝ := ∑ x ∈ F, finiteBasisWeight b x
  have hB : 0 ≤ B := Finset.sum_nonneg fun x _ ↦ finiteBasisWeight_nonneg b x
  let δ : ℝ := ε / (B + 1)
  have hden : 0 < B + 1 := by linarith
  have hδ : 0 < δ := div_pos hε hden
  choose g hg using fun j ↦ exists_rat_near (b j) hδ
  let f : hlin.extend (Set.subset_univ _) → ℚ := fun j ↦ if b j = 1 then 1 else g j
  let φ : ℝ →ₗ[ℚ] ℚ := b.constr ℚ f
  have hφbasis : ∀ j, |(φ (b j) : ℝ) - b j| < δ := by
    intro j
    simp only [φ, b.constr_basis]
    by_cases hj : b j = 1
    · simp only [f, if_pos hj, Rat.cast_one, hj, sub_self, abs_zero]
      exact hδ
    · simpa only [f, if_neg hj, abs_sub_comm] using hg j
  refine ⟨φ, ?_, ?_⟩
  · calc
      φ 1 = φ (b j₀) := congrArg φ hbj₀.symm
      _ = f j₀ := b.constr_basis ℚ f j₀
      _ = 1 := by simp only [f, hbj₀, if_pos]
  · intro x hx
    have hweight : finiteBasisWeight b x ≤ B :=
      Finset.single_le_sum (fun y _ ↦ finiteBasisWeight_nonneg b y) hx
    have hmul : finiteBasisWeight b x * δ < ε := by
      have hlt : finiteBasisWeight b x < B + 1 := lt_of_le_of_lt hweight (by linarith)
      have hbound := mul_lt_mul_of_pos_right hlt hδ
      have heq : (B + 1) * δ = ε := by
        dsimp [δ]
        field_simp
      linarith
    rw [finiteBasisError b φ x]
    calc
      |∑ j ∈ (b.repr x).support, ((b.repr x j) : ℝ) * ((φ (b j) : ℝ) - b j)|
          ≤ ∑ j ∈ (b.repr x).support,
            |((b.repr x j) : ℝ) * ((φ (b j) : ℝ) - b j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ (b.repr x).support, |((b.repr x j) : ℝ)| * δ := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hφbasis j).le (abs_nonneg _)
      _ = finiteBasisWeight b x * δ := by
        simp only [finiteBasisWeight, Finset.sum_mul]
      _ < ε := hmul

theorem finiteApproximation_strengthen :
  ∀ (F G : Finset ℝ) (ε δ : ℝ) (φ : ℝ →ₗ[ℚ] ℚ),
    F ⊆ G → δ ≤ ε → IsFiniteApproximation G δ φ → IsFiniteApproximation F ε φ := by
  intro F G ε δ φ hFG hδε hφ
  refine ⟨hφ.1, ?_⟩
  intro x hx
  exact lt_of_lt_of_le (hφ.2 x (hFG hx)) hδε

theorem finiteApproximation_signAndEquality :
  ∀ Z : Finset ℝ, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
    ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
      (∀ z ∈ Z, Real.sign (φ z : ℝ) = Real.sign z) ∧
      (∀ z ∈ Z, ∀ w ∈ Z, φ z = φ w ↔ z = w) := by
  classical
  intro Z
  let D := (Z ×ˢ Z).image (fun p : ℝ × ℝ ↦ p.1 - p.2)
  let F := Z ∪ D
  obtain ⟨ε, hε, hbound⟩ := finitePositiveGap F
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  have hsign : ∀ x ∈ F, Real.sign (φ x : ℝ) = Real.sign x := by
    intro x hx
    apply finiteSignOfError
    intro hx0
    exact (hφ.2 x hx).trans_le (hbound x hx hx0)
  refine ⟨fun z hz ↦ hsign z (Finset.mem_union_left _ hz), ?_⟩
  intro z hz w hw
  constructor
  · intro heq
    have hdiff : z - w ∈ F := Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(z, w), Finset.mem_product.mpr ⟨hz, hw⟩, rfl⟩)
    have hzero : φ (z - w) = 0 := by rw [map_sub, heq, sub_self]
    have hsignzero := hsign (z - w) hdiff
    rw [hzero, Rat.cast_zero, Real.sign_zero] at hsignzero
    exact sub_eq_zero.mp (Real.sign_eq_zero_iff.mp hsignzero.symm)
  · rintro rfl
    rfl

theorem finiteRational_denominator :
  ∀ Q : Finset ℚ, ∃ d : ℕ, 0 < d ∧
    ∀ q ∈ Q, ∃ p : ℤ, (q : ℝ) = (p : ℝ) / d := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a Q _ ih =>
    obtain ⟨d, hd, hrepr⟩ := ih
    refine ⟨a.den * d, Nat.mul_pos a.den_pos hd, ?_⟩
    intro q hq
    have haR : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_ne_zero
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      refine ⟨a.num * (d : ℤ), ?_⟩
      rw [Rat.cast_def]
      push_cast
      field_simp
    · obtain ⟨p, hp⟩ := hrepr q hq
      refine ⟨p * (a.den : ℤ), ?_⟩
      rw [hp]
      push_cast
      field_simp

theorem rationalNormal_commutes :
  ∀ (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (z : Plane),
    normalEval n (deformPoint φ z) = (φ (normalEval n z) : ℝ) := by
  intro φ n z
  simp only [normalEval, deformPoint]
  have hx := map_smul φ n.x z.re
  have hy := map_smul φ n.y z.im
  simp only [Rat.smul_def] at hx hy
  calc
    (n.x : ℝ) * φ z.re + (n.y : ℝ) * φ z.im =
        (φ ((n.x : ℝ) * z.re + (n.y : ℝ) * z.im) : ℝ) := by
          rw [map_add, hx, hy]
          push_cast
          ring
    _ = (φ (normalEval n z) : ℝ) := rfl

theorem rationalDirection_preservesCoset :
  ∀ (φ : ℝ →ₗ[ℚ] ℚ) (n : RationalNormal) (z w : Plane),
    z - w ∈ normalDirection n → deformPoint φ z - deformPoint φ w ∈ normalDirection n := by
  intro φ n z w h
  change normalEval n (z - w) = 0 at h
  change normalEval n (deformPoint φ z - deformPoint φ w) = 0
  have hzw : normalEval n (z - w) = normalEval n z - normalEval n w := by
    simp [normalEval, Complex.sub_re, Complex.sub_im]
    ring
  have hφzw : φ (normalEval n z) - φ (normalEval n w) = 0 := by
    rw [← map_sub, ← hzw, h]
    simp
  rw [show normalEval n (deformPoint φ z - deformPoint φ w) =
      normalEval n (deformPoint φ z) - normalEval n (deformPoint φ w) by
        simp [normalEval, Complex.sub_re, Complex.sub_im]; ring]
  rw [rationalNormal_commutes, rationalNormal_commutes]
  exact_mod_cast hφzw


end Tiling.Approximation
