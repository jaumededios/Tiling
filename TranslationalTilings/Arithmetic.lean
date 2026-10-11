import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.NumberTheory.Primorial
import TranslationalTilings.Basic

/-!
# Arithmetic and norms for translational tilings

This file collects the elementary arithmetic modulus and the two norms used
throughout the discrete formalization.  The Euclidean norm is explicitly the
`PiLp 2` norm; the ordinary product norm on `Fin d → ℝ` would instead be the
supremum norm.

The public API records divisibility and size estimates for the dilation
modulus, algebraic laws for the lattice `ℓ¹` norm, and comparisons between the
`ℓ¹` and Euclidean norms and diameters.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- A dilation divisible by `ell` and by every prime up to the stated cutoff. -/
def dilationModulus (ell oscillation tileCard : ℕ) : ℕ :=
  Nat.lcm ell (primorial (2 * oscillation * tileCard))

/-- The dilation modulus specialized to indicator functions. -/
def indicatorDilationModulus (ell tileCard : ℕ) : ℕ :=
  dilationModulus ell 1 tileCard

/-- The coordinatewise `ℓ¹` norm on the integer lattice. -/
def l1Norm {d : ℕ} (x : Lattice d) : ℕ :=
  ∑ i, Int.natAbs (x i)

/-- The `ℓ¹` diameter of a finite lattice set. -/
def l1Diameter {d : ℕ} (F : Finset (Lattice d)) : ℕ :=
  (F ×ˢ F).sup fun xy ↦ l1Norm (xy.1 - xy.2)

/-- The Euclidean (`ℓ²`) norm on the integer lattice. -/
noncomputable def euclideanNorm {d : ℕ} (x : Lattice d) : ℝ :=
  ‖(WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ)) :
      EuclideanSpace ℝ (Fin d))‖

/-- The Euclidean diameter of a finite lattice set, with value zero when empty. -/
noncomputable def euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) : ℝ :=
  if h : (F ×ˢ F).Nonempty then
    (F ×ˢ F).sup' h fun xy ↦ euclideanNorm (xy.1 - xy.2)
  else 0

/-- The dilation modulus is positive whenever the input period `ell` is positive. -/
theorem dilationModulus_pos {ell oscillation tileCard : ℕ}
    (hell : 0 < ell) : 0 < dilationModulus ell oscillation tileCard := by
  exact Nat.lcm_pos hell (primorial_pos _)

/-- The input period `ell` divides every associated dilation modulus. -/
theorem ell_dvd_dilationModulus (ell oscillation tileCard : ℕ) :
    ell ∣ dilationModulus ell oscillation tileCard := by
  exact Nat.dvd_lcm_left ell (primorial (2 * oscillation * tileCard))

/-- Every prime below the cutoff divides the dilation modulus. -/
theorem prime_dvd_dilationModulus {ell oscillation tileCard p : ℕ}
    (hp : p.Prime) (hpB : p ≤ 2 * oscillation * tileCard) :
    p ∣ dilationModulus ell oscillation tileCard := by
  exact (hp.dvd_primorial_iff.mpr hpB).trans
    (Nat.dvd_lcm_right ell (primorial (2 * oscillation * tileCard)))

/-- A prime factor coprime to `primorial B` must be strictly larger than `B`. -/
theorem prime_factor_gt_of_coprime_primorial {B r p : ℕ}
    (hr : Nat.Coprime r (primorial B))
    (hp : p.Prime) (hpr : p ∣ r) : B < p := by
  by_contra h
  have hpB : p ≤ B := Nat.le_of_not_gt h
  have hpPrimorial : p ∣ primorial B := hp.dvd_primorial_iff.mpr hpB
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, hpr, hpPrimorial⟩) hr

/-- An explicit exponential upper bound for the dilation modulus. -/
theorem dilationModulus_le_explicit (ell oscillation tileCard : ℕ) :
    dilationModulus ell oscillation tileCard ≤
      ell * 4 ^ (2 * oscillation * tileCard) := by
  rcases ell.eq_zero_or_pos with rfl | hell
  · simp [dilationModulus]
  calc
    dilationModulus ell oscillation tileCard ≤
        ell * primorial (2 * oscillation * tileCard) := by
      exact Nat.lcm_le_mul hell (primorial_pos _)
    _ ≤ ell * 4 ^ (2 * oscillation * tileCard) :=
      Nat.mul_le_mul_left ell (primorial_le_four_pow _)

/-- The lattice `ℓ¹` norm vanishes exactly at the zero vector. -/
theorem l1Norm_eq_zero {d : ℕ} {x : Lattice d} :
    l1Norm x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hi : Int.natAbs (x i) = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun _ _ ↦ Nat.zero_le _)).mp hx i (Finset.mem_univ i)
    exact Int.natAbs_eq_zero.mp hi
  · rintro rfl
    simp [l1Norm]

/-- Negation preserves the lattice `ℓ¹` norm. -/
theorem l1Norm_neg {d : ℕ} (x : Lattice d) : l1Norm (-x) = l1Norm x := by
  simp [l1Norm]

/-- The lattice `ℓ¹` norm satisfies the triangle inequality. -/
theorem l1Norm_add_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x + y) ≤ l1Norm x + l1Norm y := by
  unfold l1Norm
  calc
    ∑ i, Int.natAbs ((x + y) i) ≤
        ∑ i, (Int.natAbs (x i) + Int.natAbs (y i)) := by
      exact Finset.sum_le_sum fun i _ ↦ by
        simpa using Int.natAbs_add_le (x i) (y i)
    _ = (∑ i, Int.natAbs (x i)) + ∑ i, Int.natAbs (y i) :=
      Finset.sum_add_distrib

/-- The `ℓ¹` norm of a difference is bounded by the sum of the two norms. -/
theorem l1Norm_sub_le {d : ℕ} (x y : Lattice d) :
    l1Norm (x - y) ≤ l1Norm x + l1Norm y := by
  simpa [sub_eq_add_neg, l1Norm_neg] using l1Norm_add_le x (-y)

/-- Integer scalar multiplication scales `l1Norm` by the scalar's absolute value. -/
theorem l1Norm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    l1Norm (n • x) = Int.natAbs n * l1Norm x := by
  simp [l1Norm, Int.natAbs_mul, Finset.mul_sum]

/-- If a finite tile contains zero, every member has `ℓ¹` norm at most its diameter. -/
theorem mem_tile_norm_le_diameter {d : ℕ}
    {F : Finset (Lattice d)} (h0 : 0 ∈ F) {x : Lattice d} (hx : x ∈ F) :
    l1Norm x ≤ l1Diameter F := by
  simpa [l1Diameter] using
    (Finset.le_sup (f := fun xy : Lattice d × Lattice d ↦
      l1Norm (xy.1 - xy.2)) (show (x, 0) ∈ F ×ˢ F by simp [hx, h0]))

/-- The Euclidean norm of an integer vector is at most its `ℓ¹` norm. -/
theorem euclideanNorm_le_l1Norm {d : ℕ} (x : Lattice d) :
    euclideanNorm x ≤ (l1Norm x : ℝ) := by
  let v : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ))
  have hsquares : ‖v‖ ^ 2 ≤ (∑ i, |(x i : ℝ)|) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [v, sq_abs] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i ↦ |(x i : ℝ)|) (fun _ _ ↦ abs_nonneg _))
  have hnonneg : 0 ≤ ∑ i, |(x i : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hnorm : ‖v‖ ≤ ∑ i, |(x i : ℝ)| :=
    (sq_le_sq₀ (norm_nonneg v) hnonneg).mp hsquares
  simpa [euclideanNorm, l1Norm, v, Int.cast_abs] using hnorm

/-- Integer scalar multiplication scales `euclideanNorm` by the scalar's absolute value. -/
theorem euclideanNorm_zsmul {d : ℕ} (n : ℤ) (x : Lattice d) :
    euclideanNorm (n • x) = (Int.natAbs n : ℝ) * euclideanNorm x := by
  let v : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ))
  have hv :
      (WithLp.toLp 2 (fun i : Fin d ↦ (((n • x) i : ℤ) : ℝ)) :
          EuclideanSpace ℝ (Fin d)) = (n : ℝ) • v := by
    ext i
    simp [v, smul_eq_mul]
  rw [euclideanNorm, hv]
  simpa [v, euclideanNorm, Real.norm_eq_abs, ← Int.cast_abs] using
    (norm_smul (n : ℝ) v)

/-- Every nonzero integer vector has Euclidean norm at least one. -/
theorem one_le_euclideanNorm {d : ℕ} {x : Lattice d} (hx : x ≠ 0) :
    (1 : ℝ) ≤ euclideanNorm x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    apply not_forall.mp
    intro h
    exact hx (funext h)
  let v : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun j : Fin d ↦ (x j : ℝ))
  calc
    (1 : ℝ) ≤ ‖(x i : ℝ)‖ := by
      rw [Real.norm_eq_abs, ← Int.cast_abs, ← Int.cast_one, Int.cast_le]
      rw [← Int.natCast_natAbs]
      exact_mod_cast Int.natAbs_pos.mpr hi
    _ ≤ ‖v‖ := PiLp.norm_apply_le v i
    _ = euclideanNorm x := rfl

/-- The `ℓ¹` norm is at most `sqrt d` times the Euclidean norm in dimension `d`. -/
theorem l1Norm_le_sqrt_dim_mul_euclideanNorm {d : ℕ} (x : Lattice d) :
    (l1Norm x : ℝ) ≤ Real.sqrt d * euclideanNorm x := by
  let v : EuclideanSpace ℝ (Fin d) :=
    WithLp.toLp 2 (fun i : Fin d ↦ (x i : ℝ))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (s := (Finset.univ : Finset (Fin d)))
    (fun _ ↦ (1 : ℝ)) (fun i ↦ |(x i : ℝ)|)
  have hsquares :
      (∑ i, |(x i : ℝ)|) ^ 2 ≤ (Real.sqrt d * ‖v‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d),
      EuclideanSpace.real_norm_sq_eq]
    simpa [sq_abs] using hcs
  have hleft : 0 ≤ ∑ i, |(x i : ℝ)| :=
    Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hright : 0 ≤ Real.sqrt d * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hnorm : ∑ i, |(x i : ℝ)| ≤ Real.sqrt d * ‖v‖ :=
    (sq_le_sq₀ hleft hright).mp hsquares
  simpa [l1Norm, euclideanNorm, v, Int.cast_abs] using hnorm

/-- The Euclidean diameter of a finite lattice set is at most its `ℓ¹` diameter. -/
theorem euclideanDiameter_le_l1Diameter {d : ℕ}
    (F : Finset (Lattice d)) :
    euclideanDiameter F ≤ l1Diameter F := by
  classical
  by_cases h : (F ×ˢ F).Nonempty
  · rw [euclideanDiameter, dif_pos h]
    refine Finset.sup'_le h _ fun xy hxy ↦ ?_
    exact (euclideanNorm_le_l1Norm (xy.1 - xy.2)).trans
      (Nat.cast_le.mpr (Finset.le_sup (f := fun zw : Lattice d × Lattice d ↦
        l1Norm (zw.1 - zw.2)) hxy))
  · simp [euclideanDiameter, h]

/-- The `ℓ¹` diameter is at most `sqrt d` times the Euclidean diameter. -/
theorem l1Diameter_le_sqrt_dim_mul_euclideanDiameter {d : ℕ}
    (F : Finset (Lattice d)) :
    (l1Diameter F : ℝ) ≤ Real.sqrt d * euclideanDiameter F := by
  classical
  by_cases h : (F ×ˢ F).Nonempty
  · obtain ⟨xy, hxy, hsup⟩ := Finset.exists_mem_eq_sup
      (F ×ˢ F) h (fun zw ↦ l1Norm (zw.1 - zw.2))
    rw [l1Diameter, hsup, euclideanDiameter, dif_pos h]
    exact (l1Norm_le_sqrt_dim_mul_euclideanNorm (xy.1 - xy.2)).trans
      (mul_le_mul_of_nonneg_left
        (Finset.le_sup' (f := fun zw : Lattice d × Lattice d ↦
          euclideanNorm (zw.1 - zw.2)) hxy)
        (Real.sqrt_nonneg _))
  · have hempty : F ×ˢ F = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [l1Diameter, euclideanDiameter, hempty]

end TranslationalTilings
