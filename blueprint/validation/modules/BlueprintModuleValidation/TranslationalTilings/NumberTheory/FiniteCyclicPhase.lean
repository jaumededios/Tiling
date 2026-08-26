import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3  blueprint/05b-chen-complete-sums.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05b-chen-complete-sums.md:103; TranslationalTilings.PolynomialPrimeSumBound -/
namespace TranslationalTilings
def PolynomialPrimeSumBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)),
    0 < f.natDegree → f.natDegree < p →
      ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
        (f.natDegree - 1 : ℝ) * Real.sqrt p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:143; TranslationalTilings.Torus -/
namespace TranslationalTilings
abbrev Torus := AddCircle (1 : ℝ)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:145; TranslationalTilings.circlePhase -/
namespace TranslationalTilings
noncomputable def circlePhase (x : Torus) : ℂ := fourier 1 x
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:147; TranslationalTilings.IntegralPolynomialPhase -/
namespace TranslationalTilings
structure IntegralPolynomialPhase (d : ℕ) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  coeff : Fin d → ℤ
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:152; TranslationalTilings.IntegralPolynomialPhase.evalNumerator -/
namespace TranslationalTilings
def IntegralPolynomialPhase.evalNumerator
    (A : IntegralPolynomialPhase d) (n : ℤ) : ℤ :=
  ∑ i : Fin d, A.coeff i * n ^ ((i : ℕ) + 1)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:156; TranslationalTilings.IntegralPolynomialPhase.Primitive -/
namespace TranslationalTilings
def IntegralPolynomialPhase.Primitive
    (A : IntegralPolynomialPhase d) : Prop :=
  Nat.Coprime A.modulus
    (Finset.univ.gcd fun i : Fin d ↦ Int.natAbs (A.coeff i))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:161; TranslationalTilings.integralCompleteSum -/
namespace TranslationalTilings
noncomputable def integralCompleteSum
    (A : IntegralPolynomialPhase d) : ℂ :=
  ∑ n ∈ Finset.Icc 1 A.modulus,
    circlePhase
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:167; Polynomial.nonconstantPart -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.nonconstantPart
    (f : Polynomial ℤ) : Polynomial ℤ :=
  f - Polynomial.C (f.coeff 0)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:171; Polynomial.contentNat -/
namespace TranslationalTilings
def _root_.Polynomial.contentNat (f : Polynomial ℤ) : ℕ :=
  Int.natAbs (Polynomial.content f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:174; Polynomial.nonconstantContentNat -/
namespace TranslationalTilings
noncomputable def _root_.Polynomial.nonconstantContentNat
    (f : Polynomial ℤ) : ℕ :=
  Polynomial.contentNat (Polynomial.nonconstantPart f)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:178; TranslationalTilings.IntegralPolynomialPhase.toPolynomial -/
namespace TranslationalTilings
noncomputable def IntegralPolynomialPhase.toPolynomial
    (A : IntegralPolynomialPhase d) : Polynomial ℤ :=
  ∑ i : Fin d,
    Polynomial.monomial ((i : ℕ) + 1) (A.coeff i)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:183; TranslationalTilings.polynomialCompleteSum -/
namespace TranslationalTilings
noncomputable def polynomialCompleteSum
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) : ℂ :=
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  ∑ x : ZMod q,
    ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:193; TranslationalTilings.IntegralPolynomialPhase.eval_toPolynomial -/
namespace TranslationalTilings
axiom IntegralPolynomialPhase.eval_toPolynomial
    (A : IntegralPolynomialPhase d) (n : ℤ) :
  A.toPolynomial.eval n = A.evalNumerator n
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:197; TranslationalTilings.IntegralPolynomialPhase.eval_toPolynomial_zmod -/
namespace TranslationalTilings
axiom IntegralPolynomialPhase.eval_toPolynomial_zmod
    (A : IntegralPolynomialPhase d) (q : ℕ) (hq : 0 < q) (n : ℤ) :
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  Polynomial.eval (n : ZMod q)
      (A.toPolynomial.map (Int.castRingHom (ZMod q))) =
    (A.evalNumerator n : ZMod q)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:204; TranslationalTilings.IntegralPolynomialPhase.natDegree_toPolynomial_le -/
namespace TranslationalTilings
axiom IntegralPolynomialPhase.natDegree_toPolynomial_le
    (A : IntegralPolynomialPhase d) :
  A.toPolynomial.natDegree ≤ d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:208; TranslationalTilings.IntegralPolynomialPhase.primitive_toPolynomial -/
namespace TranslationalTilings
axiom IntegralPolynomialPhase.primitive_toPolynomial
    (A : IntegralPolynomialPhase d) (hA : A.Primitive) :
  Nat.Coprime A.modulus
    (Polynomial.nonconstantContentNat A.toPolynomial)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:213; TranslationalTilings.integralCompleteSum_eq_polynomialCompleteSum -/
namespace TranslationalTilings
axiom integralCompleteSum_eq_polynomialCompleteSum
    (A : IntegralPolynomialPhase d) :
  integralCompleteSum A =
    polynomialCompleteSum A.modulus A.modulus_pos A.toPolynomial
end TranslationalTilings
