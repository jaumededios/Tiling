import Mathlib.Algebra.GCDMonoid.FinsetLemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import TranslationalTilings.FiniteDifference
import TranslationalTilings.NumberTheory.CompleteExponentialSum

/-!
# Polynomial sequences on the circle

This file supplies the coefficient-facing circle-polynomial API.  It proves
the finite-difference/Newton bridge, converts finite-order coefficients into
a primitive integral phase, and records the exact period and complete-sum
transport used by the analytic argument.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- A polynomial of degree at most `d` with coefficients in the unit circle. -/
structure CirclePolynomial (d : ℕ) where
  /-- The coefficient of each monomial degree from zero through `d`. -/
  coeff : Fin (d + 1) → Torus

/-- Evaluate a circle polynomial at an integer. -/
def CirclePolynomial.eval (P : CirclePolynomial d) (n : ℤ) : Torus :=
  ∑ i : Fin (d + 1), (n ^ (i : ℕ)) • P.coeff i

instance : CoeFun (CirclePolynomial d) (fun _ ↦ ℤ → Torus) :=
  ⟨CirclePolynomial.eval⟩

/-- All positive-degree coefficients of `P` vanish. -/
def CirclePolynomial.CoefficientConstant (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → P.coeff i = 0

/-- The integer-valued polynomial function represented by `P` is constant. -/
def CirclePolynomial.FunctionConstant (P : CirclePolynomial d) : Prop :=
  ∃ c : Torus, ∀ n : ℤ, P n = c

/-- Every positive-degree coefficient of `P` has finite additive order. -/
def CirclePolynomial.HasTorsionNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) → IsOfFinAddOrder (P.coeff i)

/-- Every positive-degree coefficient of `P` is represented by a rational point. -/
def CirclePolynomial.HasRationalNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i : Fin (d + 1), 0 < (i : ℕ) →
    ∃ q : ℚ, P.coeff i = ((q : ℝ) : Torus)

/-- The positive monomial degrees of a polynomial of degree at most `d`. -/
def CirclePolynomial.nonconstantIndices (d : ℕ) : Finset (Fin (d + 1)) :=
  Finset.univ.filter fun i ↦ 0 < (i : ℕ)

/-- The least common multiple of the additive orders of all nonconstant coefficients. -/
noncomputable def CirclePolynomial.commonDenominator
    (P : CirclePolynomial d) : ℕ :=
  (CirclePolynomial.nonconstantIndices d).lcm
    fun i ↦ addOrderOf (P.coeff i)

/-- The values of `P` avoid the metric ball of radius `eps` centered at `c`. -/
def CirclePolynomial.AvoidsBall (P : CirclePolynomial d)
    (c : Torus) (eps : ℝ) : Prop :=
  ∀ n : ℤ, P n ∉ Metric.ball c eps

/-- Every value of `P` admits a representative in the closed half-circle `[0, 1/2]`. -/
def CirclePolynomial.HasHalfCircleLifts (P : CirclePolynomial d) : Prop :=
  ∀ n : ℤ, ∃ t : ℝ,
    t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) ∧ P n = (t : Torus)

/-- The integer-valued polynomial function `P` has natural period `Q`. -/
def CirclePolynomial.PeriodicWith (P : CirclePolynomial d) (Q : ℕ) : Prop :=
  Function.Periodic P (Q : ℤ)

/-- Multiply every coefficient of a circle polynomial by the integer `k`. -/
def CirclePolynomial.zsmul (k : ℤ)
    (P : CirclePolynomial d) : CirclePolynomial d :=
  ⟨fun i ↦ k • P.coeff i⟩

/-- The normalized average of the first `N` values of a complex sequence. -/
noncomputable def cesaroAverage (f : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f n

/-- The normalized symmetric average over the integer interval `[-N, N]`. -/
noncomputable def symmetricCesaroAverage (f : ℤ → ℂ) (N : ℕ) : ℂ :=
  ((2 * N + 1 : ℕ) : ℂ)⁻¹ *
    ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n

/-- Equidistribution of a natural-number-indexed torus sequence against continuous tests. -/
def Equidistributed (u : ℕ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n))
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))

/-- Equidistribution of an integer-indexed torus sequence under symmetric averaging. -/
def EquidistributedInt (u : ℤ → Torus) : Prop :=
  ∀ f : C(Torus, ℂ), Filter.Tendsto
    (fun N : ℕ ↦ symmetricCesaroAverage (fun n ↦ f (u n)) N)
    Filter.atTop (nhds (∫ x, f x ∂AddCircle.haarAddCircle))

/-- The complete character sum of `P` over the integer interval `[1, Q]`. -/
noncomputable def completeSum (P : CirclePolynomial d) (Q : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 Q, circlePhase (P n)

/-- Vanishing positive-degree coefficients make the represented function constant. -/
theorem CirclePolynomial.functionConstant_of_coefficientConstant
    (P : CirclePolynomial d) (hP : P.CoefficientConstant) :
  P.FunctionConstant := by
  refine ⟨P.coeff 0, fun n ↦ ?_⟩
  rw [CirclePolynomial.eval, Fin.sum_univ_succ]
  rw [Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [hP i.succ (by simp), smul_zero]

/-- A nonconstant represented function has a nonzero positive-degree coefficient. -/
theorem CirclePolynomial.not_coefficientConstant_of_not_functionConstant
    (P : CirclePolynomial d) (hP : ¬ P.FunctionConstant) :
  ¬ P.CoefficientConstant := by
  exact fun hcoeff ↦ hP (P.functionConstant_of_coefficientConstant hcoeff)

/-- The integer falling factorial `n (n-1) ⋯ (n-k+1)`. -/
def intFallingFactorial (n : ℤ) (k : ℕ) : ℤ :=
  ∏ j ∈ Finset.range k, (n - j)

private theorem intFallingFactorial_succ (n : ℤ) (k : ℕ) :
    intFallingFactorial n (k + 1) =
      intFallingFactorial n k * (n - k) := by
  simp [intFallingFactorial, Finset.prod_range_succ]

private theorem intFallingFactorial_shift (n : ℤ) (k : ℕ) :
    intFallingFactorial (n + 1) (k + 1) =
      intFallingFactorial n (k + 1) +
        (k + 1 : ℕ) * intFallingFactorial n k := by
  induction k with
  | zero => simp [intFallingFactorial]
  | succ k ih =>
      rw [intFallingFactorial_succ (n + 1) (k + 1),
        intFallingFactorial_succ n (k + 1), ih,
        intFallingFactorial_succ n k]
      push_cast
      ring

private theorem periodic_of_backwardDiff_one_eq_zero_torus
    (f : ℤ → Torus) (h : backwardDiff 1 f = 0) :
    Function.Periodic f 1 := by
  intro n
  have hn := congrFun h (n + 1)
  simp only [backwardDiff, Pi.zero_apply] at hn
  simpa using sub_eq_zero.mp hn

/-- A circle-valued function with vanishing `(d+1)`st difference has a Newton expansion. -/
theorem circle_newton_expansion
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ a : Fin (d + 1) → Torus, ∀ n : ℤ,
    f n = ∑ i : Fin (d + 1),
      intFallingFactorial n (i : ℕ) • a i := by
  induction d generalizing f with
  | zero =>
      have hdiff : backwardDiff 1 f = 0 := by
        simpa [backwardDiffIter] using h
      have hperiod := periodic_of_backwardDiff_one_eq_zero_torus f hdiff
      have hf (n : ℤ) : f n = f 0 := by
        have hn := hperiod.zsmul_eq n
        simpa using hn
      refine ⟨fun _ ↦ f 0, fun n ↦ ?_⟩
      simpa [intFallingFactorial] using hf n
  | succ d ih =>
      let g : ℤ → Torus := backwardDiff 1 f
      have hg : backwardDiffIter 1 (d + 1) g = 0 := by
        simpa only [backwardDiffIter, Function.iterate_succ_apply] using h
      obtain ⟨a, ha⟩ := ih g hg
      let c : Fin (d + 1) → Torus := fun i ↦
        DivisibleBy.div (a i) (i.val + 1 : ℤ)
      have hc (i : Fin (d + 1)) : (i.val + 1 : ℤ) • c i = a i := by
        exact DivisibleBy.div_cancel _ (by omega)
      let F : ℤ → Torus := fun n ↦
        ∑ i : Fin (d + 1),
          intFallingFactorial (n + 1) (i.val + 1) • c i
      have hF : backwardDiff 1 F = g := by
        funext n
        simp only [backwardDiff]
        change F n - F (n - 1) = g n
        rw [ha n]
        simp only [F]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [show n - 1 + 1 = n by ring, sub_eq_add_neg, ← sub_zsmul]
        rw [show intFallingFactorial (n + 1) (i.val + 1) -
              intFallingFactorial n (i.val + 1) =
              (i.val + 1 : ℤ) * intFallingFactorial n i.val by
          rw [intFallingFactorial_shift]
          push_cast
          ring]
        rw [mul_comm, mul_zsmul, hc]
      let r : ℤ → Torus := f - F
      have hr : backwardDiff 1 r = 0 := by
        funext n
        have hFn := congrFun hF n
        change F n - F (n - 1) = g n at hFn
        simp only [backwardDiff, r, Pi.sub_apply]
        rw [show (f n - F n) - (f (n - 1) - F (n - 1)) =
            (f n - f (n - 1)) - (F n - F (n - 1)) by abel]
        change g n - (F n - F (n - 1)) = 0
        rw [hFn]
        exact sub_self _
      have hrperiod := periodic_of_backwardDiff_one_eq_zero_torus r hr
      have hrconst (n : ℤ) : r n = r 0 := by
        have hn := hrperiod.zsmul_eq n
        simpa using hn
      let b : Fin (d + 2) → Torus := fun j ↦
        Fin.cases (r 0) c j + Fin.lastCases 0 a j
      refine ⟨b, fun n ↦ ?_⟩
      have hfn : f n = r 0 + F n := by
        have hn := hrconst n
        change f n - F n = r 0 at hn
        exact eq_add_of_sub_eq hn
      rw [hfn]
      change r 0 + F n = ∑ j : Fin (d + 2),
        intFallingFactorial n j.val •
          (Fin.cases (r 0) c j + Fin.lastCases 0 a j)
      simp_rw [smul_add]
      rw [Finset.sum_add_distrib]
      have hfirst :
          (∑ j : Fin (d + 2),
              intFallingFactorial n j.val • Fin.cases (r 0) c j) =
            r 0 + ∑ i : Fin (d + 1),
              intFallingFactorial n (i.val + 1) • c i := by
        rw [Fin.sum_univ_succ]
        simp [intFallingFactorial]
      have hsecond :
          (∑ j : Fin (d + 2),
              intFallingFactorial n j.val • Fin.lastCases 0 a j) =
            ∑ i : Fin (d + 1), intFallingFactorial n i.val • a i := by
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hfirst, hsecond]
      simp only [F]
      rw [add_assoc]
      congr 1
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [intFallingFactorial_shift, add_zsmul]
      congr 1
      rw [show ((i.val + 1 : ℕ) : ℤ) = (i.val + 1 : ℤ) by norm_num,
        mul_comm (i.val + 1 : ℤ) (intFallingFactorial n i.val),
        mul_zsmul, hc]

private noncomputable def fallingPolynomial (k : ℕ) : Polynomial ℤ :=
  ∏ j ∈ Finset.range k,
    ((Polynomial.X : Polynomial ℤ) - Polynomial.C (j : ℤ))

private theorem fallingPolynomial_natDegree_le (k : ℕ) :
    (fallingPolynomial k).natDegree ≤ k := by
  unfold fallingPolynomial
  calc
    (∏ j ∈ Finset.range k,
        (Polynomial.X - Polynomial.C (j : ℤ))).natDegree
        ≤ ∑ j ∈ Finset.range k,
            (Polynomial.X - Polynomial.C (j : ℤ)).natDegree :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _j ∈ Finset.range k, 1 := by
      exact Finset.sum_le_sum fun _ _ ↦ Polynomial.natDegree_X_sub_C_le _
    _ = k := by simp

private theorem fallingPolynomial_eval (n : ℤ) (k : ℕ) :
    Polynomial.eval n (fallingPolynomial k) = intFallingFactorial n k := by
  simp [fallingPolynomial, intFallingFactorial, Polynomial.eval_prod]

private theorem fallingPolynomial_eval_fin
    (n : ℤ) {k d : ℕ} (hkd : k ≤ d) :
    intFallingFactorial n k =
      ∑ j : Fin (d + 1),
        (fallingPolynomial k).coeff j.val * n ^ j.val := by
  have hdegree : (fallingPolynomial k).natDegree < d + 1 :=
    (fallingPolynomial_natDegree_le k).trans_lt (Nat.lt_succ_of_le hkd)
  calc
    intFallingFactorial n k = Polynomial.eval n (fallingPolynomial k) :=
      (fallingPolynomial_eval n k).symm
    _ = ∑ j ∈ Finset.range ((fallingPolynomial k).natDegree + 1),
          (fallingPolynomial k).coeff j * n ^ j :=
      Polynomial.eval_eq_sum_range n
    _ = ∑ j ∈ Finset.range (d + 1),
          (fallingPolynomial k).coeff j * n ^ j := by
      apply Finset.sum_subset
      · exact Finset.range_mono (Nat.succ_le_succ
          (Nat.le_of_lt_succ hdegree))
      · intro j hj hjnot
        have hjdegree : (fallingPolynomial k).natDegree < j := by
          have : ¬j < (fallingPolynomial k).natDegree + 1 := by
            simpa only [Finset.mem_range] using hjnot
          omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hjdegree, zero_mul]
    _ = ∑ j : Fin (d + 1),
          (fallingPolynomial k).coeff j.val * n ^ j.val := by
      exact (Fin.sum_univ_eq_sum_range
        (fun j ↦ (fallingPolynomial k).coeff j * n ^ j) (d + 1)).symm

/-- Convert a circle-valued falling-factorial expansion to the monomial basis. -/
theorem fallingFactorial_to_monomial_circle
    (a : Fin (d + 1) → Torus) :
  ∃ b : Fin (d + 1) → Torus, ∀ n : ℤ,
    (∑ i : Fin (d + 1), intFallingFactorial n (i : ℕ) • a i) =
      ∑ i : Fin (d + 1), n ^ (i : ℕ) • b i := by
  let b : Fin (d + 1) → Torus := fun j ↦
    ∑ i : Fin (d + 1), (fallingPolynomial i.val).coeff j.val • a i
  refine ⟨b, fun n ↦ ?_⟩
  calc
    (∑ i : Fin (d + 1), intFallingFactorial n i.val • a i) =
        ∑ i : Fin (d + 1),
          (∑ j : Fin (d + 1),
            (fallingPolynomial i.val).coeff j.val * n ^ j.val) • a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fallingPolynomial_eval_fin n (Nat.le_of_lt_succ i.isLt)]
    _ = ∑ i : Fin (d + 1), ∑ j : Fin (d + 1),
          n ^ j.val • (fallingPolynomial i.val).coeff j.val • a i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∑ j : Fin (d + 1),
              (fallingPolynomial i.val).coeff j.val * n ^ j.val) • a i =
            ∑ j : Fin (d + 1),
              ((fallingPolynomial i.val).coeff j.val * n ^ j.val) • a i by
        exact Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm, mul_zsmul]
    _ = ∑ j : Fin (d + 1), ∑ i : Fin (d + 1),
          n ^ j.val • (fallingPolynomial i.val).coeff j.val • a i :=
      Finset.sum_comm
    _ = ∑ j : Fin (d + 1), n ^ j.val • b j := by
      apply Finset.sum_congr rfl
      intro j _
      simp [b, Finset.smul_sum]

/-- A circle-valued function with vanishing `(d+1)`st difference is represented
by a circle polynomial. -/
theorem exists_circlePolynomial_of_difference
    (f : ℤ → Torus) (h : backwardDiffIter 1 (d + 1) f = 0) :
  ∃ P : CirclePolynomial d, ∀ n : ℤ, P n = f n := by
  obtain ⟨a, ha⟩ := circle_newton_expansion f h
  obtain ⟨b, hb⟩ := fallingFactorial_to_monomial_circle a
  refine ⟨⟨b⟩, fun n ↦ ?_⟩
  rw [CirclePolynomial.eval, ← hb n, ← ha n]

/-- Rationality and finite additive order are equivalent for all nonconstant coefficients. -/
theorem rational_iff_torsion_nonconstant (P : CirclePolynomial d) :
    P.HasRationalNonconstantCoeffs ↔ P.HasTorsionNonconstantCoeffs := by
  constructor
  · intro hrat i hi
    obtain ⟨q, hq⟩ := hrat i hi
    rw [hq, AddCircle.isOfFinAddOrder_iff_exists_rat_eq_div]
    exact ⟨q, by norm_num⟩
  · intro htor i hi
    obtain ⟨m, _, _, hm⟩ :=
      AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder (htor i hi)
    refine ⟨(m : ℚ) / addOrderOf (P.coeff i), ?_⟩
    calc
      P.coeff i =
          (((m : ℝ) / addOrderOf (P.coeff i) * 1 : ℝ) : Torus) := hm.symm
      _ = ((((m : ℚ) / addOrderOf (P.coeff i) : ℚ) : ℝ) : Torus) := by
        norm_num

/-- The common denominator is positive when all nonconstant coefficients are torsion. -/
theorem commonDenominator_pos
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  0 < P.commonDenominator := by
  rw [Nat.pos_iff_ne_zero]
  intro hzero
  rw [CirclePolynomial.commonDenominator, Finset.lcm_eq_zero_iff] at hzero
  obtain ⟨i, hi, horder⟩ := hzero
  have hi' : 0 < (i : ℕ) := by
    simpa [CirclePolynomial.nonconstantIndices] using hi
  exact (hP i hi').addOrderOf_pos.ne' horder

/-- A nontorsion nonconstant coefficient forces the common denominator to vanish. -/
theorem commonDenominator_eq_zero_of_coeff_addOrderOf_eq_zero
    (P : CirclePolynomial d) {i : Fin (d + 1)}
    (hi : 0 < (i : ℕ)) (horder : addOrderOf (P.coeff i) = 0) :
  P.commonDenominator = 0 := by
  rw [CirclePolynomial.commonDenominator, Finset.lcm_eq_zero_iff]
  refine ⟨i, ?_, horder⟩
  simp only [CirclePolynomial.nonconstantIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hi

/-- The common denominator annihilates every nonconstant coefficient. -/
theorem coeff_zsmul_commonDenominator
    (P : CirclePolynomial d) (_hP : P.HasTorsionNonconstantCoeffs)
    (i : Fin (d + 1)) (hi : 0 < (i : ℕ)) :
  (P.commonDenominator : ℤ) • P.coeff i = 0 := by
  rw [← addOrderOf_dvd_iff_zsmul_eq_zero,
    Int.natCast_dvd_natCast]
  exact Finset.dvd_lcm (by
    simp only [CirclePolynomial.nonconstantIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hi)

/-- Torsion nonconstant coefficients make `P` periodic with its common denominator. -/
theorem periodic_commonDenominator
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  P.PeriodicWith P.commonDenominator := by
  intro n
  unfold CirclePolynomial.eval
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val = 0
  · simp [hi]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    have hmod : (n + (P.commonDenominator : ℤ)) ^ i.val ≡
        n ^ i.val [ZMOD (P.commonDenominator : ℤ)] := by
      apply Int.ModEq.pow
      rw [Int.modEq_iff_dvd]
      exact ⟨-1, by ring⟩
    have hdiv : (P.commonDenominator : ℤ) ∣
        (n + (P.commonDenominator : ℤ)) ^ i.val - n ^ i.val := by
      rw [← Int.dvd_neg]
      simpa [Int.modEq_iff_dvd] using hmod
    rw [← sub_eq_zero, sub_eq_add_neg, ← sub_zsmul]
    obtain ⟨m, hm⟩ := hdiv
    rw [hm, mul_comm, mul_zsmul,
      coeff_zsmul_commonDenominator P hP i hipos, smul_zero]

/-- Multiplying coefficients can only reduce the common denominator by divisibility. -/
theorem commonDenominator_zsmul_dvd
    (P : CirclePolynomial d) (_hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  (P.zsmul k).commonDenominator ∣ P.commonDenominator := by
  apply Finset.lcm_dvd
  intro i hi
  apply (addOrderOf_dvd_of_mem_zmultiples
    (AddSubgroup.mem_zmultiples_iff.mpr ⟨k, rfl⟩)).trans
  exact Finset.dvd_lcm (by
    simpa [CirclePolynomial.commonDenominator,
      CirclePolynomial.nonconstantIndices] using hi)

/-- The original denominator divides the multiplier times the scaled denominator. -/
theorem commonDenominator_dvd_natAbs_mul_zsmul
    (P : CirclePolynomial d) (_hP : P.HasTorsionNonconstantCoeffs)
    (k : ℤ) :
  P.commonDenominator ∣
    Int.natAbs k * (P.zsmul k).commonDenominator := by
  apply Finset.lcm_dvd
  intro i hi
  rw [← Int.natCast_dvd_natCast,
    addOrderOf_dvd_iff_zsmul_eq_zero]
  have hi' : i ∈ CirclePolynomial.nonconstantIndices d := hi
  have horder : addOrderOf ((P.zsmul k).coeff i) ∣
      (P.zsmul k).commonDenominator := Finset.dvd_lcm hi'
  have hz : ((P.zsmul k).commonDenominator : ℤ) •
      (k • P.coeff i) = 0 := by
    rw [← addOrderOf_dvd_iff_zsmul_eq_zero,
      Int.natCast_dvd_natCast]
    exact horder
  rw [smul_smul] at hz
  by_cases hk : 0 ≤ k
  · rw [Int.natCast_mul, Int.natCast_natAbs, abs_of_nonneg hk,
      mul_comm]
    exact hz
  · rw [Int.natCast_mul, Int.natCast_natAbs,
      abs_of_neg (lt_of_not_ge hk), neg_mul, neg_smul, mul_comm]
    simpa using congrArg Neg.neg hz

private theorem sum_range_mul_period
    (g : ℕ → ℂ) (q m : ℕ) (hperiod : Function.Periodic g q) :
    ∑ n ∈ Finset.range (m * q), g n =
      m • ∑ n ∈ Finset.range q, g n := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, succ_nsmul]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      have hn := (hperiod.nsmul m) n
      simpa [add_comm, add_left_comm, add_assoc, mul_comm] using hn

private theorem completeSum_eq_sum_range (P : CirclePolynomial d) (Q : ℕ) :
    completeSum P Q =
      ∑ n ∈ Finset.range Q, circlePhase (P ((n + 1 : ℕ) : ℤ)) := by
  rw [completeSum, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  simp [add_comm]

/-- Repeating a period preserves the normalized complete character sum. -/
theorem normalized_completeSum_repeat
    (P : CirclePolynomial d) (Q Q' : ℕ)
    (hQ : 0 < Q) (hQ' : 0 < Q') (hdiv : Q' ∣ Q)
    (hperiod : P.PeriodicWith Q') :
  (Q : ℂ)⁻¹ * completeSum P Q =
    (Q' : ℂ)⁻¹ * completeSum P Q' := by
  obtain ⟨m, rfl⟩ := hdiv
  have hm : 0 < m := by
    by_contra hm
    simp only [Nat.not_lt, Nat.le_zero] at hm
    subst m
    simp at hQ
  let g : ℕ → ℂ := fun n ↦ circlePhase (P ((n + 1 : ℕ) : ℤ))
  have hg : Function.Periodic g Q' := by
    intro n
    apply congrArg circlePhase
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm,
      add_left_comm] using hperiod (((n + 1 : ℕ) : ℤ))
  rw [completeSum_eq_sum_range, completeSum_eq_sum_range]
  rw [Nat.mul_comm Q' m]
  change ((m * Q' : ℕ) : ℂ)⁻¹ *
      (∑ n ∈ Finset.range (m * Q'), g n) =
    (Q' : ℂ)⁻¹ * ∑ n ∈ Finset.range Q', g n
  rw [sum_range_mul_period g Q' m hg]
  simp only [nsmul_eq_mul]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr hm.ne', Nat.cast_ne_zero.mpr hQ'.ne']

/-- Regression check for normalized complete sums when the nominal period is zero. -/
theorem normalized_completeSum_repeat_zero_regression :
  let P : CirclePolynomial 0 := ⟨fun _ ↦ 0⟩
  (0 : ℂ)⁻¹ * completeSum P 0 ≠
    (1 : ℂ)⁻¹ * completeSum P 1 := by
  let P : CirclePolynomial 0 := ⟨fun _ ↦ 0⟩
  have hzero : completeSum P 0 = 0 := by
    simp [completeSum]
  have hone : completeSum P 1 = 1 := by
    rw [completeSum, show Finset.Icc 1 1 = {1} by simp]
    simp [P, CirclePolynomial.eval, circlePhase]
  change (0 : ℂ)⁻¹ * completeSum P 0 ≠
    (1 : ℂ)⁻¹ * completeSum P 1
  rw [hzero, hone]
  norm_num

/-- Clear the circle coefficients to obtain a primitive integral polynomial phase. -/
theorem exists_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ∃ A : IntegralPolynomialPhase d,
    A.modulus = P.commonDenominator ∧ A.Primitive ∧
    ∀ n : ℤ, P n = P.coeff 0 +
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus) := by
  let Q := P.commonDenominator
  have hQ : 0 < Q := commonDenominator_pos P hP
  have hexists (i : Fin d) : ∃ m < Q,
      (((m : ℝ) / Q * 1 : ℝ) : Torus) = P.coeff i.succ := by
    rw [← AddCircle.nsmul_eq_zero_iff hQ]
    simpa [Q] using coeff_zsmul_commonDenominator P hP i.succ (by simp)
  let numerator : Fin d → ℕ := fun i ↦ Classical.choose (hexists i)
  have hnumerator_lt (i : Fin d) : numerator i < Q :=
    (Classical.choose_spec (hexists i)).1
  have hnumerator_eq (i : Fin d) :
      ((((numerator i : ℕ) : ℝ) / Q * 1 : ℝ) : Torus) =
        P.coeff i.succ :=
    (Classical.choose_spec (hexists i)).2
  let A : IntegralPolynomialPhase d :=
    { modulus := Q
      modulus_pos := hQ
      coeff := fun i ↦ (numerator i : ℤ) }
  have hprimitive : A.Primitive := by
    rw [IntegralPolynomialPhase.Primitive, Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpgcd⟩ := Nat.exists_prime_and_dvd hne
    have hpQ : p ∣ Q := (Nat.dvd_gcd_iff.mp hpgcd).1
    have hpg : p ∣ Finset.univ.gcd fun i : Fin d ↦
        Int.natAbs (A.coeff i) := (Nat.dvd_gcd_iff.mp hpgcd).2
    have hpnum (i : Fin d) : p ∣ numerator i := by
      have := (Finset.dvd_gcd_iff.mp hpg) i (Finset.mem_univ i)
      simpa [A, numerator] using this
    have horder_dvd (i : Fin d) :
        addOrderOf (P.coeff i.succ) ∣ Q / p := by
      rw [← hnumerator_eq i]
      apply (Nat.dvd_div_iff_mul_dvd hpQ).2
      have hpgcdnum : p ∣ (numerator i).gcd Q :=
        Nat.dvd_gcd (hpnum i) hpQ
      obtain ⟨t, ht⟩ := hpgcdnum
      refine ⟨t, ?_⟩
      have horder := AddCircle.gcd_mul_addOrderOf_div_eq
        (1 : ℝ) (numerator i) hQ
      rw [ht] at horder
      simpa [mul_assoc, mul_left_comm, mul_comm] using horder.symm
    have hQdvd : Q ∣ Q / p := by
      apply Finset.lcm_dvd
      intro i hi
      have hipos : 0 < i.val := by
        simpa only [CirclePolynomial.nonconstantIndices,
          Finset.mem_filter, Finset.mem_univ, true_and] using hi
      have hi0 : i ≠ 0 := by
        intro hi0
        subst i
        simp at hipos
      let j : Fin d := i.pred hi0
      rw [← Fin.succ_pred i hi0]
      exact horder_dvd j
    have hp_le_Q : p ≤ Q := Nat.le_of_dvd hQ hpQ
    have hQdivpos : 0 < Q / p := Nat.div_pos hp_le_Q hp.pos
    have hle : Q ≤ Q / p := Nat.le_of_dvd hQdivpos hQdvd
    exact (Nat.not_le_of_lt (Nat.div_lt_self hQ hp.one_lt)) hle
  refine ⟨A, rfl, hprimitive, fun n ↦ ?_⟩
  rw [CirclePolynomial.eval, Fin.sum_univ_succ]
  norm_num only [Fin.val_zero, pow_zero, one_zsmul]
  congr 1
  have hterm (i : Fin d) :
      n ^ (i.val + 1) • P.coeff i.succ =
        ((((((numerator i : ℕ) : ℤ) * n ^ (i.val + 1) : ℤ) : ℝ) /
          (Q : ℝ) : ℝ) : Torus) := by
    rw [← hnumerator_eq i, ← QuotientAddGroup.mk_zsmul]
    congr 1
    push_cast
    simp only [zsmul_eq_mul]
    field_simp
    push_cast
    ring
  have hsum :
      (∑ i : Fin d, n ^ (i.succ : ℕ) • P.coeff i.succ) =
        ∑ i : Fin d,
        ((((((numerator i : ℕ) : ℤ) * n ^ (i.val + 1) : ℤ) : ℝ) /
          (Q : ℝ) : ℝ) : Torus) := by
    apply Finset.sum_congr rfl
    intro i _
    simpa using hterm i
  rw [hsum]
  rw [← QuotientAddGroup.mk_sum]
  congr 1
  simp [A, IntegralPolynomialPhase.evalNumerator, div_eq_mul_inv,
    Finset.sum_mul]

/-- A chosen primitive integral phase obtained by clearing the torsion denominators of `P`. -/
noncomputable def CirclePolynomial.integralPhase
    (P : CirclePolynomial d)
    (hP : P.HasTorsionNonconstantCoeffs) : IntegralPolynomialPhase d :=
  Classical.choose (exists_integralPhase P hP)

/-- The chosen integral phase has modulus equal to the common denominator. -/
theorem integralPhase_modulus
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).modulus = P.commonDenominator :=
  (Classical.choose_spec (exists_integralPhase P hP)).1

/-- The chosen integral phase is primitive. -/
theorem integralPhase_primitive
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  (P.integralPhase hP).Primitive :=
  (Classical.choose_spec (exists_integralPhase P hP)).2.1

/-- Evaluation of the chosen integral phase recovers the circle polynomial after scaling. -/
theorem integralPhase_eval
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) (n : ℤ) :
  P n = P.coeff 0 +
    ((((P.integralPhase hP).evalNumerator n : ℝ) /
      (P.integralPhase hP).modulus : ℝ) : Torus) :=
  (Classical.choose_spec (exists_integralPhase P hP)).2.2 n

private theorem circlePhase_add (x y : Torus) :
    circlePhase (x + y) = circlePhase x * circlePhase y := by
  simp [circlePhase, fourier_apply, AddCircle.toCircle_add,
    Circle.coe_mul]

private theorem norm_circlePhase (x : Torus) : ‖circlePhase x‖ = 1 := by
  rw [circlePhase, fourier_one]
  exact Circle.norm_coe _

/-- The norm of the circle complete sum equals that of the associated integral phase sum. -/
theorem norm_completeSum_eq_integralPhase
    (P : CirclePolynomial d) (hP : P.HasTorsionNonconstantCoeffs) :
  ‖completeSum P P.commonDenominator‖ =
    ‖integralCompleteSum (P.integralPhase hP)‖ := by
  rw [completeSum, integralCompleteSum]
  have hmodulus := integralPhase_modulus P hP
  rw [← hmodulus]
  have hsum :
      (∑ n ∈ Finset.Icc 1 (P.integralPhase hP).modulus,
          circlePhase (P n)) =
        circlePhase (P.coeff 0) *
          ∑ n ∈ Finset.Icc 1 (P.integralPhase hP).modulus,
            circlePhase
              (((((P.integralPhase hP).evalNumerator n : ℤ) : ℝ) /
                (P.integralPhase hP).modulus : ℝ) : Torus) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    rw [integralPhase_eval, circlePhase_add]
  rw [hsum, norm_mul, norm_circlePhase, one_mul]

end TranslationalTilings
