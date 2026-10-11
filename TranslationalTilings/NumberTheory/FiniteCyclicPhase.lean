import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content

/-!
# Finite cyclic polynomial phases

This file gives the exact finite-cyclic representation used by the complete-sum
argument: integral coefficient vectors, their associated integer polynomials,
and the bridge between interval and `ZMod` enumerations of a complete period.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

namespace TranslationalTilings

/-- The prime-modulus polynomial estimate consumed by the independently
buildable Chen recursion. -/
def PolynomialPrimeSumBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)),
    0 < f.natDegree → f.natDegree < p →
      ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
        (f.natDegree - 1 : ℝ) * Real.sqrt p

/-- The unit real circle. -/
abbrev Torus := AddCircle (1 : ℝ)

/-- The positive first Fourier character on the unit circle. -/
noncomputable def circlePhase (x : Torus) : ℂ := fourier 1 x

/-- A rational polynomial phase, stored by its positive-degree integral
coefficients and positive denominator. -/
structure IntegralPolynomialPhase (d : ℕ) where
  /-- The positive denominator of the phase. -/
  modulus : ℕ
  /-- Positivity of the denominator. -/
  modulus_pos : 0 < modulus
  /-- The coefficients of degrees `1, ..., d`. -/
  coeff : Fin d → ℤ

/-- The integer numerator obtained by evaluating an integral polynomial phase. -/
def IntegralPolynomialPhase.evalNumerator
    (A : IntegralPolynomialPhase d) (n : ℤ) : ℤ :=
  ∑ i : Fin d, A.coeff i * n ^ ((i : ℕ) + 1)

/-- Primitivity means that the denominator is coprime to all nonconstant
coefficients. -/
def IntegralPolynomialPhase.Primitive
    (A : IntegralPolynomialPhase d) : Prop :=
  Nat.Coprime A.modulus
    (Finset.univ.gcd fun i : Fin d ↦ Int.natAbs (A.coeff i))

/-- The complete exponential sum of an integral polynomial phase over one
period of its denominator. -/
noncomputable def integralCompleteSum
    (A : IntegralPolynomialPhase d) : ℂ :=
  ∑ n ∈ Finset.Icc 1 A.modulus,
    circlePhase
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus)

/-- The polynomial obtained by deleting the constant coefficient. -/
noncomputable def _root_.Polynomial.nonconstantPart
    (f : Polynomial ℤ) : Polynomial ℤ :=
  f - Polynomial.C (f.coeff 0)

/-- The natural-number absolute value of the integral content of a polynomial. -/
def _root_.Polynomial.contentNat (f : Polynomial ℤ) : ℕ :=
  Int.natAbs (Polynomial.content f)

/-- The natural content of the nonconstant part of an integral polynomial. -/
noncomputable def _root_.Polynomial.nonconstantContentNat
    (f : Polynomial ℤ) : ℕ :=
  Polynomial.contentNat (Polynomial.nonconstantPart f)

/-- The integral polynomial represented by a coefficient-vector phase. -/
noncomputable def IntegralPolynomialPhase.toPolynomial
    (A : IntegralPolynomialPhase d) : Polynomial ℤ :=
  ∑ i : Fin d,
    Polynomial.monomial ((i : ℕ) + 1) (A.coeff i)

/-- A complete additive-character sum of an integral polynomial modulo `q`. -/
noncomputable def polynomialCompleteSum
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) : ℂ :=
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  ∑ x : ZMod q,
    ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))

/-- Integer evaluation of the associated polynomial agrees with the stored
numerator evaluation. -/
theorem IntegralPolynomialPhase.eval_toPolynomial
    (A : IntegralPolynomialPhase d) (n : ℤ) :
  A.toPolynomial.eval n = A.evalNumerator n := by
  simp [IntegralPolynomialPhase.toPolynomial,
    IntegralPolynomialPhase.evalNumerator, Polynomial.eval_finsetSum]

/-- Evaluation of the associated polynomial modulo `q` agrees with reduction
of the stored numerator. -/
theorem IntegralPolynomialPhase.eval_toPolynomial_zmod
    (A : IntegralPolynomialPhase d) (q : ℕ) (hq : 0 < q) (n : ℤ) :
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  Polynomial.eval (n : ZMod q)
      (A.toPolynomial.map (Int.castRingHom (ZMod q))) =
    (A.evalNumerator n : ZMod q) := by
  let _ : NeZero q := ⟨Nat.ne_of_gt hq⟩
  simp [IntegralPolynomialPhase.toPolynomial,
    IntegralPolynomialPhase.evalNumerator, Polynomial.eval_finsetSum]

/-- The associated polynomial has degree at most the length of the coefficient
vector. -/
theorem IntegralPolynomialPhase.natDegree_toPolynomial_le
    (A : IntegralPolynomialPhase d) :
  A.toPolynomial.natDegree ≤ d := by
  unfold IntegralPolynomialPhase.toPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le (A.coeff i)).trans
    (Nat.succ_le_iff.mpr i.isLt)

/-- A primitive coefficient-vector phase yields a polynomial whose
nonconstant content is coprime to the denominator. -/
theorem IntegralPolynomialPhase.primitive_toPolynomial
    (A : IntegralPolynomialPhase d) (hA : A.Primitive) :
  Nat.Coprime A.modulus
    (Polynomial.nonconstantContentNat A.toPolynomial) := by
  apply Nat.Coprime.of_dvd_right _ hA
  rw [Finset.dvd_gcd_iff]
  intro i _
  change Int.natAbs (Polynomial.content (Polynomial.nonconstantPart A.toPolynomial)) ∣
    Int.natAbs (A.coeff i)
  rw [Int.natAbs_dvd_natAbs]
  apply Polynomial.content_dvd_coeff (n := (i : ℕ) + 1)
    (p := Polynomial.nonconstantPart A.toPolynomial)
    |>.trans
  have hconstant : A.toPolynomial.coeff 0 = 0 := by
    simp [IntegralPolynomialPhase.toPolynomial]
  have hcoeff : A.toPolynomial.coeff ((i : ℕ) + 1) = A.coeff i := by
    simp only [IntegralPolynomialPhase.toPolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hdegree : (j : ℕ) + 1 ≠ (i : ℕ) + 1 := by
        intro h
        exact hji (Fin.ext (Nat.succ_injective h))
      rw [Polynomial.coeff_monomial, if_neg hdegree]
    · simp
  simp [Polynomial.nonconstantPart, hconstant, hcoeff]

private theorem sum_Icc_cast_eq_sum_zmod
    (q : ℕ) [NeZero q] (g : ZMod q → ℂ) :
    ∑ n ∈ Finset.Icc 1 q, g n = ∑ x : ZMod q, g x := by
  have hfin (i : Fin q) : ZMod.finEquiv q i = (i.val : ZMod q) := by
    cases q with
    | zero => exact Fin.elim0 i
    | succ q =>
        exact (Fin.cast_val_eq_self i).symm
  calc
    ∑ n ∈ Finset.Icc 1 q, g n = ∑ n ∈ Finset.range q, g (n + 1) := by
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      simp [add_comm]
    _ = ∑ i : Fin q, g ((i : ℕ) + 1) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ g (n + 1)) q).symm
    _ = ∑ x : ZMod q, g (x + 1) := by
      apply Fintype.sum_equiv (ZMod.finEquiv q).toEquiv
      intro i
      change g ((i.val : ℕ) + 1) = g (ZMod.finEquiv q i + 1)
      rw [hfin]
    _ = ∑ x : ZMod q, g x := by
      exact Fintype.sum_bijective (fun x : ZMod q ↦ x + 1)
        (AddGroup.addRight_bijective 1) _ _ (fun _ ↦ rfl)

/-- The interval-indexed complete sum of a phase equals its `ZMod`-indexed
polynomial complete sum. -/
theorem integralCompleteSum_eq_polynomialCompleteSum
    (A : IntegralPolynomialPhase d) :
  integralCompleteSum A =
    polynomialCompleteSum A.modulus A.modulus_pos A.toPolynomial := by
  let _ : NeZero A.modulus := ⟨Nat.ne_of_gt A.modulus_pos⟩
  let g : ZMod A.modulus → ℂ := fun x ↦
    ZMod.stdAddChar
      (Polynomial.eval x (A.toPolynomial.map (Int.castRingHom _)))
  have hphase (n : ℕ) :
      circlePhase
          ((((A.evalNumerator (n : ℤ) : ℤ) : ℝ) / A.modulus : ℝ) : Torus) =
        g n := by
    dsimp only [g]
    have hcast : (n : ZMod A.modulus) = ((n : ℤ) : ZMod A.modulus) := by
      norm_num
    rw [hcast]
    rw [A.eval_toPolynomial_zmod A.modulus A.modulus_pos (n : ℤ)]
    rw [ZMod.stdAddChar_coe]
    simp only [circlePhase, fourier_coe_apply]
    push_cast
    congr 1
    field_simp
  calc
    integralCompleteSum A = ∑ n ∈ Finset.Icc 1 A.modulus, g n := by
      apply Finset.sum_congr rfl
      intro n _
      exact hphase n
    _ = ∑ x : ZMod A.modulus, g x :=
      sum_Icc_cast_eq_sum_zmod A.modulus g
    _ = polynomialCompleteSum A.modulus A.modulus_pos A.toPolynomial := by
      rfl

end TranslationalTilings
