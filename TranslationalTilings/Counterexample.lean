import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.NumberTheory.Real.Irrational
import TranslationalTilings.Basic
import TranslationalTilings.FiniteDifference
import TranslationalTilings.LatticeGeometry

/-!
# An eight-element higher-level tiling which is not weakly periodic

This file formalizes the explicit construction in Section 2 of Greenfeld--Tao.  The construction
uses a four-periodic sign pattern and the carry in addition of two irrational fractional parts.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings.Counterexample

/-- The irrational slope `√2` used by the counterexample. -/
noncomputable def alpha : ℝ := Real.sqrt 2

/-- The alternating sign function determined by the lattice coordinates. -/
def chi (x : Plane) : ℤ :=
  (-1) ^ Int.natAbs (x 1 / 2 + x 0)

/-- The carry arising from addition of two irrational fractional parts. -/
noncomputable def carry (x : Plane) : ℤ :=
  Int.floor (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
    Int.floor (alpha * (x 0 : ℝ)) -
    Int.floor (alpha * (x 1 : ℝ))

/-- The positive level set selected by the sign and carry functions. -/
noncomputable def counterexampleSet : Set Plane :=
  {x | if chi x = 1 then carry x = 1 else carry x = 0}

/-- The vertical cancellation vector. -/
def v₁ : Plane := ![0, 2]

/-- The horizontal cancellation vector. -/
def v₂ : Plane := ![1, 0]

/-- The diagonal cancellation vector. -/
def v₃ : Plane := ![2, -2]

/-- The eight-element tile assembled from three cancellation pairs. -/
def counterexampleTile : Finset Plane :=
  (Finset.univ : Finset (Fin 3 → Bool)).image fun t ↦
    (if t 0 then v₁ else 0) +
    (if t 1 then v₂ else 0) +
    (if t 2 then v₃ else 0)

/-- The slope `alpha = √2` is irrational. -/
theorem irrational_alpha : Irrational alpha := by
  simpa [alpha] using irrational_sqrt_two

/-- Coordinate formula for the sign function `chi`. -/
theorem chi_eq_formula (m₁ m₂ : ℤ) :
    chi ![m₁, m₂] = (-1) ^ Int.natAbs (m₂ / 2 + m₁) := by
  rfl

private theorem chi_eq_negOnePow (x : Plane) :
    chi x = ((x 1 / 2 + x 0).negOnePow : ℤ) := by
  unfold chi
  exact (Int.coe_negOnePow ℤ (x 1 / 2 + x 0)).symm

/-- The sign function takes only the values `-1` and `1`. -/
theorem chi_mem (x : Plane) : chi x = -1 ∨ chi x = 1 := by
  rcases neg_one_pow_eq_or ℤ (Int.natAbs (x 1 / 2 + x 0)) with h | h
  · exact Or.inr h
  · exact Or.inl h

private theorem chi_sub_v₁ (x : Plane) : chi (x - v₁) = -chi x := by
  rw [chi_eq_negOnePow, chi_eq_negOnePow]
  have hdiv : (x 1 - 2) / 2 = x 1 / 2 - 1 := by omega
  have hexp : (x - v₁) 1 / 2 + (x - v₁) 0 = x 1 / 2 + x 0 - 1 := by
    simp only [v₁, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero, hdiv]
    omega
  rw [hexp, Int.negOnePow_sub, Int.negOnePow_one]
  norm_num

private theorem chi_sub_v₂ (x : Plane) : chi (x - v₂) = -chi x := by
  rw [chi_eq_negOnePow, chi_eq_negOnePow]
  have hexp : (x - v₂) 1 / 2 + (x - v₂) 0 = x 1 / 2 + x 0 - 1 := by
    simp only [v₂, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    omega
  rw [hexp, Int.negOnePow_sub, Int.negOnePow_one]
  norm_num

private theorem chi_sub_v₃ (x : Plane) : chi (x - v₃) = -chi x := by
  rw [chi_eq_negOnePow, chi_eq_negOnePow]
  have hexp : (x - v₃) 1 / 2 + (x - v₃) 0 = x 1 / 2 + x 0 - 1 := by
    simp only [v₃, Pi.sub_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    omega
  rw [hexp, Int.negOnePow_sub, Int.negOnePow_one]
  norm_num

/-- The sign function is scalar-periodic with period four. -/
theorem chi_scalarPeriodic_four : ScalarPeriodic 4 chi := by
  intro x z
  have hdiv : (x 1 + 4 * z 1) / 2 = x 1 / 2 + 2 * z 1 := by omega
  have hexp : (x + ((4 : ℕ) : ℤ) • z) 1 / 2 +
      (x + ((4 : ℕ) : ℤ) • z) 0 =
      x 1 / 2 + x 0 + (2 * z 1 + 4 * z 0) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    norm_num
    rw [hdiv]
    omega
  rw [chi_eq_negOnePow, chi_eq_negOnePow, hexp, Int.negOnePow_add]
  have heven : Even (2 * z 1 + 4 * z 0) := ⟨z 1 + 2 * z 0, by ring⟩
  rw [Int.negOnePow_even _ heven]
  norm_num

/-- The vertical two-point tile annihilates `chi` by convolution. -/
theorem chi_cancel_vertical : tileConv {0, v₁} chi = 0 := by
  funext x
  have hv : v₁ ≠ 0 := by simp [v₁]
  simp only [tileConv]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    simp [chi_sub_v₁]
  · simpa using hv.symm

/-- The horizontal two-point tile annihilates `chi` by convolution. -/
theorem chi_cancel_horizontal : tileConv {0, v₂} chi = 0 := by
  funext x
  have hv : v₂ ≠ 0 := by simp [v₂]
  simp only [tileConv]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    simp [chi_sub_v₂]
  · simpa using hv.symm

/-- The diagonal two-point tile annihilates `chi` by convolution. -/
theorem chi_cancel_diagonal : tileConv {0, v₃} chi = 0 := by
  funext x
  have hv : v₃ ≠ 0 := by simp [v₃]
  simp only [tileConv]
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    simp [chi_sub_v₃]
  · simpa using hv.symm

/-- Paper Lemma 2.1, using the concrete witness `chi`. -/
theorem chi_lemma :
    ScalarPeriodic 4 chi ∧
      (∀ x, chi x = -1 ∨ chi x = 1) ∧
      tileConv {0, v₁} chi = 0 ∧ tileConv {0, v₂} chi = 0 :=
  ⟨chi_scalarPeriodic_four, chi_mem, chi_cancel_vertical, chi_cancel_horizontal⟩

/-- The carry term is always zero or one. -/
theorem carry_zero_or_one (x : Plane) : carry x = 0 ∨ carry x = 1 := by
  let a : ℝ := alpha * (x 0 : ℝ)
  let b : ℝ := alpha * (x 1 : ℝ)
  have hab : alpha * ((x 0 + x 1 : ℤ) : ℝ) = a + b := by
    simp [a, b]
    ring
  have hlo : Int.floor a + Int.floor b ≤ Int.floor (a + b) := Int.le_floor_add a b
  have hhi : Int.floor (a + b) - 1 ≤ Int.floor a + Int.floor b :=
    Int.le_floor_add_floor a b
  rw [carry, hab]
  change Int.floor (a + b) - Int.floor a - Int.floor b = 0 ∨
    Int.floor (a + b) - Int.floor a - Int.floor b = 1
  omega

/-- Express the carry as the defect in additivity of fractional parts. -/
theorem carry_eq_fract (x : Plane) :
    (carry x : ℝ) =
      Int.fract (alpha * (x 0 : ℝ)) +
      Int.fract (alpha * (x 1 : ℝ)) -
      Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ)) := by
  rw [carry]
  push_cast
  simp only [Int.fract]
  ring

/-- Express the counterexample-set indicator using `chi` and the carry. -/
theorem indicator_counterexampleSet (x : Plane) :
    ((setIndicator counterexampleSet x : ℤ) : ℝ) =
      (chi x : ℝ) *
        (Int.fract (alpha * (x 0 : ℝ)) +
          Int.fract (alpha * (x 1 : ℝ)) -
          Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ)) -
          (1 / 2 : ℝ)) + (1 / 2 : ℝ) := by
  rw [← carry_eq_fract x]
  rcases chi_mem x with hchi | hchi <;>
    rcases carry_zero_or_one x with hcarry | hcarry
  all_goals
    simp [counterexampleSet, setIndicator, hchi, hcarry] <;> norm_num

private def cubePoint (t : Fin 3 → Bool) : Plane :=
  (if t 0 then v₁ else 0) +
    (if t 1 then v₂ else 0) +
    (if t 2 then v₃ else 0)

private def cubeStep : Fin 3 → Plane := ![v₁, v₂, v₃]

private theorem cubePoint_eq_sum (t : Fin 3 → Bool) :
    cubePoint t = ∑ i, if t i then cubeStep i else 0 := by
  simp [cubePoint, cubeStep, Fin.sum_univ_three]

private theorem cubePoint_injective : Function.Injective cubePoint := by
  decide

/-- The concrete counterexample tile has exactly eight elements. -/
theorem counterexampleTile_card : counterexampleTile.card = 8 := by
  rw [counterexampleTile]
  change ((Finset.univ : Finset (Fin 3 → Bool)).image cubePoint).card = 8
  rw [Finset.card_image_of_injective _ cubePoint_injective]
  decide

/-- Factor the tile indicator into its three two-point factors. -/
theorem counterexampleTile_indicator_factorization :
    tileMonoidAlgebra ℤ Plane counterexampleTile =
      tileMonoidAlgebra ℤ Plane {0, v₁} *
        tileMonoidAlgebra ℤ Plane {0, v₂} *
        tileMonoidAlgebra ℤ Plane {0, v₃} := by
  classical
  have hleft : tileMonoidAlgebra ℤ Plane counterexampleTile =
      ∑ t : Fin 3 → Bool, AddMonoidAlgebra.single (cubePoint t) (1 : ℤ) := by
    unfold tileMonoidAlgebra counterexampleTile
    change ∑ x ∈ (Finset.univ.image cubePoint), AddMonoidAlgebra.single x (1 : ℤ) = _
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact cubePoint_injective hab
  have hpair (i : Fin 3) : tileMonoidAlgebra ℤ Plane {0, cubeStep i} =
      ∑ b : Bool, AddMonoidAlgebra.single (if b then cubeStep i else 0) (1 : ℤ) := by
    have hi : cubeStep i ≠ 0 := by
      fin_cases i <;> decide
    rw [Fintype.sum_bool]
    unfold tileMonoidAlgebra
    rw [Finset.sum_insert]
    · rw [Finset.sum_singleton]
      norm_num
      ac_rfl
    · simpa using hi.symm
  rw [hleft]
  calc
    (∑ t : Fin 3 → Bool, AddMonoidAlgebra.single (cubePoint t) (1 : ℤ)) =
        ∑ t : Fin 3 → Bool, ∏ i,
          AddMonoidAlgebra.single (if t i then cubeStep i else 0) (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro t _
      simp [AddMonoidAlgebra.prod_single, cubePoint_eq_sum]
    _ = ∏ i : Fin 3, ∑ b : Bool,
          AddMonoidAlgebra.single (if b then cubeStep i else 0) (1 : ℤ) :=
      (Fintype.prod_sum (fun (i : Fin 3) (b : Bool) ↦
        AddMonoidAlgebra.single (if b then cubeStep i else 0) (1 : ℤ))).symm
    _ = ∏ i : Fin 3, tileMonoidAlgebra ℤ Plane {0, cubeStep i} := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hpair i).symm
    _ = tileMonoidAlgebra ℤ Plane {0, v₁} *
          tileMonoidAlgebra ℤ Plane {0, v₂} *
          tileMonoidAlgebra ℤ Plane {0, v₃} := by
      rw [Fin.prod_univ_three]
      rfl

private def toggleBit (i : Fin 3) (t : Fin 3 → Bool) : Fin 3 → Bool :=
  Function.update t i (!t i)

private theorem toggleBit_involutive (i : Fin 3) : Function.Involutive (toggleBit i) := by
  intro t
  funext j
  by_cases hji : j = i
  · subst j
    simp [toggleBit]
  · simp [toggleBit, hji]

private def toggleBitEquiv (i : Fin 3) : (Fin 3 → Bool) ≃ (Fin 3 → Bool) where
  toFun := toggleBit i
  invFun := toggleBit i
  left_inv := toggleBit_involutive i
  right_inv := toggleBit_involutive i

private theorem cubePoint_toggleBit (i : Fin 3) (t : Fin 3 → Bool) :
    cubePoint (toggleBit i t) =
      if t i then cubePoint t - cubeStep i else cubePoint t + cubeStep i := by
  fin_cases i <;>
    cases h₀ : t 0 <;> cases h₁ : t 1 <;> cases h₂ : t 2 <;>
    ext j <;> fin_cases j <;>
    simp [toggleBit, cubePoint, cubeStep, v₁, v₂, v₃, h₀, h₁, h₂]

private theorem sum_cube_eq_zero_of_antiperiodic (i : Fin 3) (f : Plane → ℝ)
    (hf : ∀ x, f (x - cubeStep i) = -f x) (x : Plane) :
    ∑ t : Fin 3 → Bool, f (x - cubePoint t) = 0 := by
  have hf_add (y : Plane) : f (y + cubeStep i) = -f y := by
    have h := hf (y + cubeStep i)
    rw [add_sub_cancel_right] at h
    linarith
  have htoggle (t : Fin 3 → Bool) :
      f (x - cubePoint (toggleBit i t)) = -f (x - cubePoint t) := by
    rw [cubePoint_toggleBit]
    by_cases hti : t i
    · rw [if_pos hti]
      rw [show x - (cubePoint t - cubeStep i) =
        (x - cubePoint t) + cubeStep i by abel]
      exact hf_add (x - cubePoint t)
    · rw [if_neg hti]
      rw [show x - (cubePoint t + cubeStep i) =
        (x - cubePoint t) - cubeStep i by abel]
      exact hf (x - cubePoint t)
  have hreindex := (toggleBitEquiv i).sum_comp (fun t ↦ f (x - cubePoint t))
  have hneg : (∑ t : Fin 3 → Bool, f (x - cubePoint t)) =
      -∑ t : Fin 3 → Bool, f (x - cubePoint t) := by
    calc
      (∑ t : Fin 3 → Bool, f (x - cubePoint t)) =
          ∑ t : Fin 3 → Bool, f (x - cubePoint (toggleBit i t)) := hreindex.symm
      _ = ∑ t : Fin 3 → Bool, -f (x - cubePoint t) := by
        apply Finset.sum_congr rfl
        intro t _
        exact htoggle t
      _ = -∑ t : Fin 3 → Bool, f (x - cubePoint t) := by
        rw [Finset.sum_neg_distrib]
  linarith

private theorem cube_sum_chi (x : Plane) :
    ∑ t : Fin 3 → Bool, (chi (x - cubePoint t) : ℝ) = 0 := by
  apply sum_cube_eq_zero_of_antiperiodic 0 (fun y ↦ (chi y : ℝ))
  intro y
  simp [cubeStep, chi_sub_v₁]

private theorem cube_sum_chi_fract_first (x : Plane) :
    ∑ t : Fin 3 → Bool,
      (chi (x - cubePoint t) : ℝ) *
        Int.fract (alpha * ((x - cubePoint t) 0 : ℝ)) = 0 := by
  change ∑ t : Fin 3 → Bool,
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * (y 0 : ℝ)))
      (x - cubePoint t) = 0
  refine sum_cube_eq_zero_of_antiperiodic 0
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * (y 0 : ℝ))) ?_ x
  intro y
  simp only [cubeStep, Matrix.cons_val_zero]
  rw [chi_sub_v₁]
  have hcoord : (y - v₁) 0 = y 0 := by simp [v₁]
  rw [hcoord, Int.cast_neg, neg_mul]

private theorem cube_sum_chi_fract_second (x : Plane) :
    ∑ t : Fin 3 → Bool,
      (chi (x - cubePoint t) : ℝ) *
        Int.fract (alpha * ((x - cubePoint t) 1 : ℝ)) = 0 := by
  change ∑ t : Fin 3 → Bool,
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * (y 1 : ℝ)))
      (x - cubePoint t) = 0
  refine sum_cube_eq_zero_of_antiperiodic 1
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * (y 1 : ℝ))) ?_ x
  intro y
  change (chi (y - v₂) : ℝ) * Int.fract (alpha * ((y - v₂) 1 : ℝ)) =
    -((chi y : ℝ) * Int.fract (alpha * (y 1 : ℝ)))
  rw [chi_sub_v₂]
  have hcoord : (y - v₂) 1 = y 1 := by simp [v₂]
  rw [hcoord, Int.cast_neg, neg_mul]

private theorem cube_sum_chi_fract_sum (x : Plane) :
    ∑ t : Fin 3 → Bool,
      (chi (x - cubePoint t) : ℝ) *
        Int.fract
          (alpha * ((((x - cubePoint t) 0 + (x - cubePoint t) 1 : ℤ)) : ℝ)) = 0 := by
  change ∑ t : Fin 3 → Bool,
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * ((y 0 + y 1 : ℤ) : ℝ)))
      (x - cubePoint t) = 0
  refine sum_cube_eq_zero_of_antiperiodic 2
    (fun y ↦ (chi y : ℝ) * Int.fract (alpha * ((y 0 + y 1 : ℤ) : ℝ))) ?_ x
  intro y
  change (chi (y - v₃) : ℝ) *
      Int.fract (alpha * (((y - v₃) 0 + (y - v₃) 1 : ℤ) : ℝ)) =
    -((chi y : ℝ) * Int.fract (alpha * ((y 0 + y 1 : ℤ) : ℝ)))
  rw [chi_sub_v₃]
  have hcoord : (y - v₃) 0 + (y - v₃) 1 = y 0 + y 1 := by
    simp [v₃]
  rw [hcoord, Int.cast_neg, neg_mul]

/-- The counterexample tile covers its target at level four. -/
theorem counterexample_tiles_level_four :
    TilesAtLevel counterexampleTile counterexampleSet Set.univ 4 := by
  intro x
  have hcast : ((tileConv counterexampleTile (setIndicator counterexampleSet) x : ℤ) : ℝ) =
      ∑ t : Fin 3 → Bool,
        ((setIndicator counterexampleSet (x - cubePoint t) : ℤ) : ℝ) := by
    unfold tileConv counterexampleTile
    push_cast
    change (∑ y ∈ Finset.univ.image cubePoint,
      ((setIndicator counterexampleSet (x - y) : ℤ) : ℝ)) = _
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact cubePoint_injective hab
  rw [show setIndicator (Set.univ : Set Plane) x = 1 by simp [setIndicator]]
  norm_num
  apply (Int.cast_injective (α := ℝ))
  rw [hcast]
  simp_rw [indicator_counterexampleSet]
  have hχ := cube_sum_chi x
  have h₀ := cube_sum_chi_fract_first x
  have h₁ := cube_sum_chi_fract_second x
  have h₂ := cube_sum_chi_fract_sum x
  have hχhalf :
      (∑ t : Fin 3 → Bool, (chi (x - cubePoint t) : ℝ) * (1 / 2 : ℝ)) = 0 := by
    rw [← Finset.sum_mul, hχ, zero_mul]
  simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  norm_num at hχ h₀ h₁ h₂ hχhalf ⊢
  linarith

/-- Fractional parts of multiples of an irrational number have infinite range. -/
theorem irrational_fract_range_infinite {β : ℝ} (hβ : Irrational β) :
    Set.Infinite (Set.range fun n : ℤ ↦ Int.fract (β * n)) := by
  apply Set.infinite_range_of_injective
  intro m n hmn
  by_contra hne
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp hmn
  have hsub : ((m - n : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hne
  apply hβ.ne_rational z (m - n)
  apply (eq_div_iff hsub).2
  rw [Int.cast_sub]
  calc
    β * ((m : ℝ) - n) = β * m - β * n := by ring
    _ = z := hz

private noncomputable def realPartIndicator {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (i : Fin D.numberOfParts) : Plane → ℝ :=
  fun x ↦ (setIndicator (D.part i) x : ℤ)

private theorem realPartIndicator_periodic {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (i : Fin D.numberOfParts) :
    Function.Periodic (realPartIndicator D i) (D.period i) := by
  intro x
  unfold realPartIndicator
  have hmem := D.periodic_part i x
  by_cases hx : x ∈ D.part i
  · have hx' : x + D.period i ∈ D.part i := hmem.mpr hx
    simp [setIndicator, hx, hx']
  · have hx' : x + D.period i ∉ D.part i := fun h ↦ hx (hmem.mp h)
    simp [setIndicator, hx, hx']

private theorem real_indicator_eq_sum_parts {A : Set Plane}
    (D : WeakPeriodicDecomposition A) :
    (fun x ↦ ((setIndicator A x : ℤ) : ℝ)) =
      ∑ i, realPartIndicator D i := by
  funext x
  simp only [Finset.sum_apply]
  by_cases hx : x ∈ A
  · have hxUnion : x ∈ ⋃ i, D.part i := by
      rw [D.iUnion_parts]
      exact hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxUnion
    have hothers : ∀ j ∈ (Finset.univ : Finset (Fin D.numberOfParts)),
        j ≠ i → realPartIndicator D j x = 0 := by
      intro j _ hji
      have hdisj : Disjoint (D.part j) (D.part i) :=
        D.pairwiseDisjoint (by simp) (by simp) hji
      have hj : x ∉ D.part j := fun hxj ↦
        (Set.disjoint_left.mp hdisj) hxj hi
      simp [realPartIndicator, setIndicator, hj]
    rw [Finset.sum_eq_single i hothers (by simp)]
    simp [realPartIndicator, setIndicator, hx, hi]
  · have hpart (i : Fin D.numberOfParts) : x ∉ D.part i := by
      intro hi
      apply hx
      rw [← D.iUnion_parts]
      exact Set.mem_iUnion.mpr ⟨i, hi⟩
    simp [realPartIndicator, setIndicator, hx, hpart]

private def horizontalFactor {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (i : Fin D.numberOfParts) : ℤ :=
  if D.period i 1 = 0 then D.period i 0 else 1

private def horizontalProduct {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : ℤ :=
  ∏ i, horizontalFactor D i

private def horizontalPeriod {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Plane :=
  ![4 * horizontalProduct D, 0]

private noncomputable def horizontalIndicator {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Plane → ℝ :=
  fun x ↦ ∑ i, if D.period i 1 = 0 then realPartIndicator D i x else 0

private theorem horizontalFactor_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (i : Fin D.numberOfParts) :
    horizontalFactor D i ≠ 0 := by
  unfold horizontalFactor
  by_cases hi : D.period i 1 = 0
  · simp only [if_pos hi]
    intro hi0
    apply D.period_ne_zero i
    funext j
    fin_cases j
    · exact hi0
    · exact hi
  · simp [hi]

private theorem horizontalProduct_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : horizontalProduct D ≠ 0 := by
  rw [horizontalProduct, Finset.prod_ne_zero_iff]
  exact fun i _ ↦ horizontalFactor_ne_zero D i

private theorem horizontalPeriod_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : horizontalPeriod D ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 0
  simp [horizontalPeriod, horizontalProduct_ne_zero D] at hcoord

private theorem horizontalIndicator_periodic {A : Set Plane}
    (D : WeakPeriodicDecomposition A) :
    Function.Periodic (horizontalIndicator D) (horizontalPeriod D) := by
  intro x
  unfold horizontalIndicator
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : D.period i 1 = 0
  · simp only [if_pos hi]
    let a : ℤ := 4 * ∏ j ∈ (Finset.univ.erase i), horizontalFactor D j
    have hprod : horizontalProduct D =
        D.period i 0 * ∏ j ∈ (Finset.univ.erase i), horizontalFactor D j := by
      rw [horizontalProduct, ← Finset.mul_prod_erase Finset.univ
        (horizontalFactor D) (Finset.mem_univ i)]
      simp [horizontalFactor, hi]
    have htarget : horizontalPeriod D = a • D.period i := by
      funext j
      fin_cases j
      · simp [horizontalPeriod, a, hprod, Pi.smul_apply]
        ring
      · simp [horizontalPeriod, a, hi, Pi.smul_apply]
    rw [htarget]
    exact (realPartIndicator_periodic D i).zsmul a x
  · simp [hi]

private theorem signed_second_periodic_horizontal {A : Set Plane}
    (D : WeakPeriodicDecomposition A) :
    Function.Periodic
      (fun x : Plane ↦ (chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ)))
      (horizontalPeriod D) := by
  intro x
  let z : Plane := ![horizontalProduct D, 0]
  have htarget : horizontalPeriod D = (4 : ℤ) • z := by
    funext i
    fin_cases i <;> simp [horizontalPeriod, z, Pi.smul_apply]
  have hchi := chi_scalarPeriodic_four x z
  norm_num at hchi
  rw [htarget]
  have hcoord : (x + (4 : ℤ) • z) 1 = x 1 := by
    simp [z]
  change (chi (x + (4 : ℤ) • z) : ℝ) *
      Int.fract (alpha * ((x + (4 : ℤ) • z) 1 : ℝ)) =
    (chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ))
  rw [hcoord, show (4 : ℤ) • z = 4 * z by simp, hchi]

private theorem finite_range_comp {X Y Z : Type*} (f : X → Y) (g : Z → X)
    (hf : (Set.range f).Finite) : (Set.range fun z ↦ f (g z)).Finite := by
  apply hf.subset
  rintro y ⟨z, rfl⟩
  exact ⟨g z, rfl⟩

private theorem finite_range_add (f g : Plane → ℝ)
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) :
    (Set.range fun x ↦ f x + g x).Finite := by
  apply (hf.image2 (· + ·) hg).subset
  rintro y ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, g x, ⟨x, rfl⟩, rfl⟩

private theorem finite_range_mul (f g : Plane → ℝ)
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) :
    (Set.range fun x ↦ f x * g x).Finite := by
  apply (hf.image2 (· * ·) hg).subset
  rintro y ⟨x, rfl⟩
  exact ⟨f x, ⟨x, rfl⟩, g x, ⟨x, rfl⟩, rfl⟩

private theorem finite_range_realPartIndicator {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (i : Fin D.numberOfParts) :
    (Set.range (realPartIndicator D i)).Finite := by
  apply (Set.toFinite ({0, 1} : Set ℝ)).subset
  rintro y ⟨x, rfl⟩
  by_cases hx : x ∈ D.part i <;>
    simp [realPartIndicator, setIndicator, hx]

private theorem finite_range_horizontalIndicator {A : Set Plane}
    (D : WeakPeriodicDecomposition A) :
    (Set.range (horizontalIndicator D)).Finite := by
  let term : Fin D.numberOfParts → Plane → ℝ := fun i x ↦
    if D.period i 1 = 0 then realPartIndicator D i x else 0
  have hterm (i : Fin D.numberOfParts) : (Set.range (term i)).Finite := by
    by_cases hi : D.period i 1 = 0
    · simpa [term, hi] using finite_range_realPartIndicator D i
    · simp [term, hi]
  have hsum (s : Finset (Fin D.numberOfParts)) :
      (Set.range fun x ↦ ∑ i ∈ s, term i x).Finite := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        simpa [Finset.sum_insert hi] using finite_range_add (term i)
          (fun x ↦ ∑ j ∈ s, term j x) (hterm i) ih
  change (Set.range fun x ↦ ∑ i, term i x).Finite
  simpa using hsum (Finset.univ : Finset (Fin D.numberOfParts))

private abbrev RightIndex {A : Set Plane} (D : WeakPeriodicDecomposition A) :=
  Fin D.numberOfParts ⊕ Fin 4

private noncomputable def rightSummand {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : RightIndex D → Plane → ℝ
  | Sum.inl i =>
      if D.period i 1 = 0 then 0 else realPartIndicator D i
  | Sum.inr j => ![
      (fun x : Plane ↦ -(chi x : ℝ) * Int.fract (alpha * (x 0 : ℝ))),
      (fun x : Plane ↦ (chi x : ℝ) *
        Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ))),
      (fun x : Plane ↦ (1 / 2 : ℝ) * (chi x : ℝ)),
      (fun _ : Plane ↦ -(1 / 2 : ℝ))] j

private def rightPeriod {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : RightIndex D → Plane
  | Sum.inl i => if D.period i 1 = 0 then ![0, 1] else D.period i
  | Sum.inr j => ![![0, 4], ![4, -4], ![0, 4], ![0, 1]] j

private theorem rightPeriod_second_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (j : RightIndex D) :
    rightPeriod D j 1 ≠ 0 := by
  rcases j with i | j
  · by_cases hi : D.period i 1 = 0 <;> simp [rightPeriod, hi]
  · fin_cases j <;> norm_num [rightPeriod]

private theorem rightSummand_periodic {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (j : RightIndex D) :
    Function.Periodic (rightSummand D j) (rightPeriod D j) := by
  rcases j with i | j
  · by_cases hi : D.period i 1 = 0
    · simp [rightSummand, hi, Function.Periodic]
    · simpa [rightSummand, rightPeriod, hi] using realPartIndicator_periodic D i
  · fin_cases j
    · intro x
      have hchi := chi_scalarPeriodic_four x ![0, 1]
      norm_num at hchi
      change -(chi (x + (![0, 4] : Plane)) : ℝ) *
          Int.fract (alpha * ((x + (![0, 4] : Plane)) 0 : ℝ)) =
        -(chi x : ℝ) * Int.fract (alpha * (x 0 : ℝ))
      have hcoord : (x + (![0, 4] : Plane)) 0 = x 0 := by simp
      rw [hcoord]
      have hchi' : chi (x + (![0, 4] : Plane)) = chi x := by simpa using hchi
      rw [hchi']
    · intro x
      have hchi := chi_scalarPeriodic_four x ![1, -1]
      norm_num at hchi
      have hsum : (x + (![4, -4] : Plane)) 0 +
          (x + (![4, -4] : Plane)) 1 = x 0 + x 1 := by
        simp
        ring
      change (chi (x + (![4, -4] : Plane)) : ℝ) *
          Int.fract (alpha * (((x + (![4, -4] : Plane)) 0 +
            (x + (![4, -4] : Plane)) 1 : ℤ) : ℝ)) =
        (chi x : ℝ) * Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ))
      rw [hsum]
      have hchi' : chi (x + (![4, -4] : Plane)) = chi x := by simpa using hchi
      rw [hchi']
    · intro x
      have hchi := chi_scalarPeriodic_four x ![0, 1]
      norm_num at hchi
      change (1 / 2 : ℝ) * (chi (x + (![0, 4] : Plane)) : ℝ) =
        (1 / 2 : ℝ) * (chi x : ℝ)
      have hchi' : chi (x + (![0, 4] : Plane)) = chi x := by simpa using hchi
      rw [hchi']
    · simp [rightSummand, Function.Periodic]

private def rightVerticalProduct {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : ℤ :=
  ∏ j, rightPeriod D j 1

private theorem rightVerticalProduct_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : rightVerticalProduct D ≠ 0 := by
  rw [rightVerticalProduct, Finset.prod_ne_zero_iff]
  exact fun j _ ↦ rightPeriod_second_ne_zero D j

private def commonDifference {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Plane :=
  ![0, 4 * horizontalProduct D * rightVerticalProduct D]

private theorem commonDifference_ne_zero {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : commonDifference D ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero 1
  simp [commonDifference, horizontalProduct_ne_zero D,
    rightVerticalProduct_ne_zero D] at hcoord

private theorem commonDifference_representation {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (j : RightIndex D) :
    ∃ a b : ℤ, commonDifference D =
      a • rightPeriod D j + b • horizontalPeriod D := by
  let rest : ℤ := ∏ k ∈ (Finset.univ.erase j), rightPeriod D k 1
  have hprod : rightVerticalProduct D = rightPeriod D j 1 * rest := by
    rw [rightVerticalProduct, ← Finset.mul_prod_erase Finset.univ
      (fun k ↦ rightPeriod D k 1) (Finset.mem_univ j)]
  refine ⟨4 * horizontalProduct D * rest,
    -(rest * rightPeriod D j 0), ?_⟩
  funext i
  fin_cases i
  · simp [commonDifference, horizontalPeriod]
    ring
  · simp [commonDifference, horizontalPeriod, hprod]
    ring

private theorem right_decomposition
    (D : WeakPeriodicDecomposition counterexampleSet) :
    (fun x : Plane ↦
      (chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ)) - horizontalIndicator D x) =
      ∑ j, rightSummand D j := by
  funext x
  have hind := congrFun (real_indicator_eq_sum_parts D) x
  have hformula := indicator_counterexampleSet x
  simp only [Finset.sum_apply] at hind ⊢
  rw [Fintype.sum_sum_type]
  simp only [rightSummand]
  have hsplit : (∑ i, realPartIndicator D i x) =
      horizontalIndicator D x +
        ∑ i, if D.period i 1 = 0 then 0 else realPartIndicator D i x := by
    rw [horizontalIndicator]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : D.period i 1 = 0 <;> simp [hi]
  rw [hsplit] at hind
  have hright : (∑ j : Fin 4, ![
      (fun x : Plane ↦ -(chi x : ℝ) * Int.fract (alpha * (x 0 : ℝ))),
      (fun x : Plane ↦ (chi x : ℝ) *
        Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ))),
      (fun x : Plane ↦ (1 / 2 : ℝ) * (chi x : ℝ)),
      (fun _ : Plane ↦ -(1 / 2 : ℝ))] j x) =
      -(chi x : ℝ) * Int.fract (alpha * (x 0 : ℝ)) +
      (chi x : ℝ) * Int.fract (alpha * ((x 0 + x 1 : ℤ) : ℝ)) +
      (1 / 2 : ℝ) * (chi x : ℝ) - (1 / 2 : ℝ) := by
    simp [Fin.sum_univ_succ]
    ring
  rw [hright]
  have hind' : ((setIndicator counterexampleSet x : ℤ) : ℝ) =
      horizontalIndicator D x +
        ∑ i, (if D.period i 1 = 0 then (0 : Plane → ℝ)
          else realPartIndicator D i) x := by
    rw [hind]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : D.period i 1 = 0 <;> simp [hi]
  linear_combination hind' - hformula

private theorem backwardDiffIter_zero (e : Plane) (n : ℕ) :
    backwardDiffIter e n (0 : Plane → ℝ) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply']
      change backwardDiff e (backwardDiffIter e n (0 : Plane → ℝ)) = 0
      rw [ih]
      funext x
      simp [backwardDiff]

private theorem backwardDiff_preserves_period {p : Plane} {f : Plane → ℝ}
    (hf : Function.Periodic f p) (e : Plane) :
    Function.Periodic (backwardDiff e f) p := by
  intro x
  simp only [backwardDiff]
  rw [hf x]
  congr 1
  rw [show x + p - e = (x - e) + p by abel, hf (x - e)]

private theorem backwardDiffIter_preserves_period {p : Plane} {f : Plane → ℝ}
    (hf : Function.Periodic f p) (e : Plane) (n : ℕ) :
    Function.Periodic (backwardDiffIter e n f) p := by
  induction n with
  | zero => simpa [backwardDiffIter]
  | succ n ih =>
      rw [backwardDiffIter, Function.iterate_succ_apply']
      exact backwardDiff_preserves_period ih e

private theorem applyDifferences_eq_iter_of_periodic
    (directions : List Plane) (e p : Plane) (f : Plane → ℝ)
    (hf : Function.Periodic f p)
    (hdir : ∀ d ∈ directions, ∃ b : ℤ, d = e - b • p) :
    applyDifferences directions f = backwardDiffIter e directions.length f := by
  induction directions with
  | nil => simp [applyDifferences, backwardDiffIter]
  | cons d directions ih =>
      obtain ⟨b, rfl⟩ := hdir d (by simp)
      have htail : ∀ k ∈ directions, ∃ b : ℤ, k = e - b • p :=
        fun k hk ↦ hdir k (by simp [hk])
      have hperiod : Function.Periodic
          (backwardDiffIter e directions.length f) ((-b) • p) := by
        exact (backwardDiffIter_preserves_period hf e directions.length).zsmul (-b)
      change backwardDiff (e - b • p) (applyDifferences directions f) =
        backwardDiffIter e (directions.length + 1) f
      rw [ih htail]
      rw [show e - b • p = e + (-b) • p by
        rw [sub_eq_add_neg, neg_zsmul]]
      rw [backwardDiff_sub_period_eq e ((-b) • p) _ hperiod]
      simp only [backwardDiffIter, Function.iterate_succ_apply']

private theorem lineRestriction_backwardDiffIter (e x : Plane) (n : ℕ)
    (f : Plane → ℝ) :
    lineRestriction (backwardDiffIter e n f) x e =
      backwardDiffIter 1 n (lineRestriction f x e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      calc
        lineRestriction (backwardDiffIter e (n + 1) f) x e =
            lineRestriction (backwardDiff e (backwardDiffIter e n f)) x e := by
              simp only [backwardDiffIter, Function.iterate_succ_apply']
        _ = backwardDiff 1 (lineRestriction (backwardDiffIter e n f) x e) :=
          lineRestriction_backwardDiff (backwardDiffIter e n f) x e
        _ = backwardDiff 1 (backwardDiffIter 1 n (lineRestriction f x e)) := by
          rw [ih]
        _ = backwardDiffIter 1 (n + 1) (lineRestriction f x e) := by
          simp only [backwardDiffIter, Function.iterate_succ_apply']

private def periodSubgroup (f : Plane → ℝ) : AddSubgroup Plane where
  carrier := {p | Function.Periodic f p}
  zero_mem' := Function.periodic_with_period_zero f
  add_mem' hp hq := hp.add_period hq
  neg_mem' hp := hp.neg

private theorem finite_range_of_periodicOn_finite_quotient
    (H : AddSubgroup Plane) (f : Plane → ℝ) [Finite (Plane ⧸ H)]
    (hf : PeriodicOn H f) : (Set.range f).Finite := by
  let representative : Plane ⧸ H → Plane := fun c ↦
    Classical.choose (QuotientAddGroup.mk'_surjective H c)
  let quotientFunction : Plane ⧸ H → ℝ := fun c ↦ f (representative c)
  apply (Set.finite_range quotientFunction).subset
  rintro y ⟨x, rfl⟩
  refine ⟨QuotientAddGroup.mk' H x, ?_⟩
  have hrep : QuotientAddGroup.mk' H (representative (QuotientAddGroup.mk' H x)) =
      QuotientAddGroup.mk' H x :=
    Classical.choose_spec (QuotientAddGroup.mk'_surjective H
      (QuotientAddGroup.mk' H x))
  have hmem : representative (QuotientAddGroup.mk' H x) - x ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp hrep
  have hperiod := hf _ hmem x
  change f (representative (QuotientAddGroup.mk' H x)) = f x
  rw [show x + (representative (QuotientAddGroup.mk' H x) - x) =
      representative (QuotientAddGroup.mk' H x) by abel] at hperiod
  exact hperiod

private def rightTargetCoefficient {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (j : RightIndex D) : ℤ :=
  -(∏ k ∈ (Finset.univ.erase j), rightPeriod D k 1) * rightPeriod D j 0

private noncomputable def allSummand {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Option (RightIndex D) → Plane → ℝ
  | none => 0
  | some j => rightSummand D j

private def allPeriod {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Option (RightIndex D) → Plane
  | none => horizontalPeriod D
  | some j => rightPeriod D j

private def allTargetCoefficient {A : Set Plane}
    (D : WeakPeriodicDecomposition A) : Option (RightIndex D) → ℤ
  | none => 0
  | some j => rightTargetCoefficient D j

private theorem commonDifference_representation_fixed {A : Set Plane}
    (D : WeakPeriodicDecomposition A) (j : RightIndex D) :
    ∃ a : ℤ, commonDifference D = a • rightPeriod D j +
      rightTargetCoefficient D j • horizontalPeriod D := by
  let rest : ℤ := ∏ k ∈ (Finset.univ.erase j), rightPeriod D k 1
  have hprod : rightVerticalProduct D = rightPeriod D j 1 * rest := by
    rw [rightVerticalProduct, ← Finset.mul_prod_erase Finset.univ
      (fun k ↦ rightPeriod D k 1) (Finset.mem_univ j)]
  refine ⟨4 * horizontalProduct D * rest, ?_⟩
  funext i
  fin_cases i
  · simp [commonDifference, horizontalPeriod, rightTargetCoefficient]
    ring
  · simp [commonDifference, horizontalPeriod, rightTargetCoefficient, hprod]
    ring

private theorem finite_range_chi_real :
    (Set.range fun x : Plane ↦ (chi x : ℝ)).Finite := by
  apply (Set.toFinite ({-1, 1} : Set ℝ)).subset
  rintro y ⟨x, rfl⟩
  rcases chi_mem x with h | h <;> simp [h]

/-- The constructed tiling set has no finite weak-periodic decomposition. -/
theorem counterexample_not_weaklyPeriodic :
    ¬ WeaklyPeriodic counterexampleSet := by
  rintro ⟨D⟩
  let lhs : Plane → ℝ := fun x ↦
    (chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ)) - horizontalIndicator D x
  have hlhsPeriod : Function.Periodic lhs (horizontalPeriod D) :=
    (signed_second_periodic_horizontal D).sub (horizontalIndicator_periodic D)
  have hdecomp : lhs = ∑ j, allSummand D j := by
    change (fun x : Plane ↦
      (chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ)) - horizontalIndicator D x) = _
    rw [right_decomposition D]
    funext x
    simp [allSummand, Fintype.sum_option]
  have hallPeriod (j : Option (RightIndex D)) :
    Function.Periodic (allSummand D j) (allPeriod D j) := by
    rcases j with _ | j
    · simp [allSummand, Function.Periodic]
    · exact rightSummand_periodic D j
  have hrepresent (j : Option (RightIndex D)) (hj : j ≠ none) :
      ∃ a : ℤ, commonDifference D = a • allPeriod D j +
        allTargetCoefficient D j • allPeriod D none := by
    obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.mp hj
    simpa [allPeriod, allTargetCoefficient] using
      commonDifference_representation_fixed D j
  let directions : List Plane := eliminationDirections none (commonDifference D)
    (allPeriod D) (allTargetCoefficient D)
  have heliminate := eliminate_periodic_summands none lhs (allSummand D)
    (commonDifference D) (allPeriod D) (allTargetCoefficient D)
    hdecomp hallPeriod hrepresent
  have hdirection : ∀ d ∈ directions, ∃ b : ℤ,
      d = commonDifference D - b • horizontalPeriod D := by
    intro d hd
    simp only [directions, eliminationDirections, List.mem_map,
      Finset.mem_toList] at hd
    obtain ⟨j, _, rfl⟩ := hd
    exact ⟨allTargetCoefficient D j, by simp [allPeriod]⟩
  have hiterate : applyDifferences directions lhs =
      backwardDiffIter (commonDifference D) directions.length lhs :=
    applyDifferences_eq_iter_of_periodic directions (commonDifference D)
      (horizontalPeriod D) lhs hlhsPeriod hdirection
  rw [hiterate] at heliminate
  have hlength : directions.length = Fintype.card (Option (RightIndex D)) - 1 := by
    simp [directions, eliminationDirections]
  rw [hlength] at heliminate
  rw [show allSummand D none = (0 : Plane → ℝ) by rfl,
    backwardDiffIter_zero] at heliminate
  let order : ℕ := Fintype.card (Option (RightIndex D)) - 1
  have hdiff : backwardDiffIter (commonDifference D) order lhs = 0 := by
    exact heliminate
  have horder : 0 < order := by
    simp [order, RightIndex, Fintype.card_option, Fintype.card_sum]
  have hchiAbs (x : Plane) : |(chi x : ℝ)| = 1 := by
    rcases chi_mem x with h | h <;> simp [h]
  have hhorizontalBound (x : Plane) :
      |horizontalIndicator D x| ≤ (D.numberOfParts : ℝ) := by
    calc
      |horizontalIndicator D x| =
          |∑ i, if D.period i 1 = 0 then realPartIndicator D i x else 0| := rfl
      _ ≤ ∑ i, |if D.period i 1 = 0 then realPartIndicator D i x else 0| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin D.numberOfParts, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : D.period i 1 = 0
        · simp only [if_pos hi]
          by_cases hx : x ∈ D.part i <;>
            simp [realPartIndicator, setIndicator, hx]
        · simp [hi]
      _ = (D.numberOfParts : ℝ) := by simp
  have hlhsBound (x : Plane) : |lhs x| ≤ 1 + D.numberOfParts := by
    calc
      |lhs x| ≤
          |(chi x : ℝ) * Int.fract (alpha * (x 1 : ℝ))| +
            |horizontalIndicator D x| := abs_sub ..
      _ ≤ 1 + D.numberOfParts := by
        have hfract : |Int.fract (alpha * (x 1 : ℝ))| ≤ 1 := by
          rw [abs_of_nonneg (Int.fract_nonneg _)]
          exact (Int.fract_lt_one _).le
        rw [abs_mul, hchiAbs]
        exact add_le_add (by simpa using hfract) (hhorizontalBound x)
  have hlineDiff (x : Plane) :
      backwardDiffIter 1 order (lineRestriction lhs x (commonDifference D)) = 0 := by
    have h := congrArg
      (fun f : Plane → ℝ ↦ lineRestriction f x (commonDifference D)) hdiff
    rw [lineRestriction_backwardDiffIter] at h
    rw [show lineRestriction (0 : Plane → ℝ) x (commonDifference D) = 0 by
      funext z
      rfl] at h
    exact h
  have hlinePeriod (x : Plane) :
      Function.Periodic (lineRestriction lhs x (commonDifference D)) 1 := by
    apply bounded_real_of_backwardDiffIter_eq_zero_is_constant order horder
    · exact ⟨1 + D.numberOfParts, fun z ↦ hlhsBound _⟩
    · exact hlineDiff x
  have hcommonPeriod : Function.Periodic lhs (commonDifference D) := by
    intro x
    simpa [lineRestriction] using hlinePeriod x 0
  let H : AddSubgroup Plane := generatedPair (horizontalPeriod D) (commonDifference D)
  have hHperiod : PeriodicOn H lhs := by
    have hle : generatedPair (horizontalPeriod D) (commonDifference D) ≤
        periodSubgroup lhs := by
      rw [generatedPair, AddSubgroup.closure_le]
      intro p hp
      rcases hp with (rfl | rfl)
      · exact hlhsPeriod
      · exact hcommonPeriod
    exact fun p hp ↦ hle hp
  have hwedge : wedge (horizontalPeriod D) (commonDifference D) ≠ 0 := by
    simp [wedge, horizontalPeriod, commonDifference,
      horizontalProduct_ne_zero D, rightVerticalProduct_ne_zero D]
  have hindex : H.index ≠ 0 := by
    rw [show H = generatedPair (horizontalPeriod D) (commonDifference D) by rfl,
      index_generatedPair hwedge]
    exact Int.natAbs_ne_zero.mpr hwedge
  let _ : Finite (Plane ⧸ H) := AddSubgroup.index_ne_zero_iff_finite.mp hindex
  have hlhsFinite : (Set.range lhs).Finite :=
    finite_range_of_periodicOn_finite_quotient H lhs hHperiod
  have hsumFinite : (Set.range fun x ↦ lhs x + horizontalIndicator D x).Finite :=
    finite_range_add lhs (horizontalIndicator D) hlhsFinite
      (finite_range_horizontalIndicator D)
  have hproductFinite : (Set.range fun x ↦
      (chi x : ℝ) * (lhs x + horizontalIndicator D x)).Finite :=
    finite_range_mul (fun x ↦ (chi x : ℝ))
      (fun x ↦ lhs x + horizontalIndicator D x) finite_range_chi_real hsumFinite
  let verticalPoint : ℤ → Plane := fun n ↦ ![0, n]
  have hrecover (n : ℤ) : Int.fract (alpha * n) =
      (chi (verticalPoint n) : ℝ) *
        (lhs (verticalPoint n) + horizontalIndicator D (verticalPoint n)) := by
    rcases chi_mem (verticalPoint n) with hchi | hchi <;>
      simp [lhs, verticalPoint, hchi]
  have hfractFinite :
      (Set.range fun n : ℤ ↦ Int.fract (alpha * n)).Finite := by
    rw [show (fun n : ℤ ↦ Int.fract (alpha * n)) = fun n ↦
        (chi (verticalPoint n) : ℝ) *
          (lhs (verticalPoint n) + horizontalIndicator D (verticalPoint n)) by
      funext n
      exact hrecover n]
    exact finite_range_comp
      (fun x ↦ (chi x : ℝ) * (lhs x + horizontalIndicator D x))
      verticalPoint hproductFinite
  exact (irrational_fract_range_infinite irrational_alpha) hfractFinite

/-- Paper Theorem 1.3(ii). -/
theorem exists_eight_element_level_four_not_weaklyPeriodic :
    ∃ (F : Finset Plane) (A : Set Plane),
      F.card = 8 ∧ TilesAtLevel F A Set.univ 4 ∧ ¬ WeaklyPeriodic A :=
  ⟨counterexampleTile, counterexampleSet, counterexampleTile_card,
    counterexample_tiles_level_four, counterexample_not_weaklyPeriodic⟩

end TranslationalTilings.Counterexample
