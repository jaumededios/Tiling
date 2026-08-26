import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
import TranslationalTilings.NumberTheory.ChenCompleteSum
import TranslationalTilings.NumberTheory.QuadraticCompleteSum
import TranslationalTilings.NumberTheory.PolynomialWeilBound

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3  blueprint/05b-chen-complete-sums.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05b-chen-complete-sums.md:109; TranslationalTilings.polynomialPrimeSumBound -/
namespace TranslationalTilings
theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:617; TranslationalTilings.chen_prime_base -/
namespace TranslationalTilings
axiom chen_prime_base
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:874; TranslationalTilings.primePower_completeSum_bound -/
namespace TranslationalTilings
axiom primePower_completeSum_bound
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1151; TranslationalTilings.ack_theorem_2_2_finiteProduct -/
namespace TranslationalTilings
axiom ack_theorem_2_2_finiteProduct
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1288; TranslationalTilings.quadratic_polynomialCompleteSum_parity_bound -/
namespace TranslationalTilings
axiom quadratic_polynomialCompleteSum_parity_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    if Even q then Real.sqrt (2 * q) else Real.sqrt q
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1294; TranslationalTilings.quadratic_polynomialCompleteSum_bound -/
namespace TranslationalTilings
axiom quadratic_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ Real.sqrt (2 * q)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1351; TranslationalTilings.stechkinNatConstant -/
namespace TranslationalTilings
def stechkinNatConstant (d : ℕ) : ℕ :=
  2 ^ (10 * (d + 1) ^ 8)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1354; TranslationalTilings.chenLocalFactor_le -/
namespace TranslationalTilings
axiom chenLocalFactor_le (d p : ℕ) (hd : 3 ≤ d) :
  chenLocalFactor d p ≤ d ^ 2
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1357; TranslationalTilings.chenExceptionalPrimes_card_le -/
namespace TranslationalTilings
axiom chenExceptionalPrimes_card_le (d : ℕ) :
  (chenExceptionalPrimes d).card ≤ (d + 1) ^ 6
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1360; TranslationalTilings.chenGlobalFactor_le_degreePow -/
namespace TranslationalTilings
axiom chenGlobalFactor_le_degreePow (d : ℕ) (hd : 3 ≤ d) :
  chenGlobalFactor d ≤
    ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1364; TranslationalTilings.nat_le_two_pow -/
namespace TranslationalTilings
axiom nat_le_two_pow (d : ℕ) : d ≤ 2 ^ d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1366; TranslationalTilings.chenMajorant_exponent_le -/
namespace TranslationalTilings
axiom chenMajorant_exponent_le (d : ℕ) :
  2 * d * (d + 1) ^ 6 ≤ 10 * (d + 1) ^ 8
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1369; TranslationalTilings.chenDegreePow_le_natConstant -/
namespace TranslationalTilings
axiom chenDegreePow_le_natConstant (d : ℕ) :
  (d ^ 2) ^ ((d + 1) ^ 6) ≤ stechkinNatConstant d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1372; TranslationalTilings.chenDegreePow_cast -/
namespace TranslationalTilings
axiom chenDegreePow_cast (d : ℕ) :
  ((((d ^ 2) ^ ((d + 1) ^ 6) : ℕ) : ℝ)) =
    ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1376; TranslationalTilings.chenGlobalFactor_le_stechkinNatConstant -/
namespace TranslationalTilings
axiom chenGlobalFactor_le_stechkinNatConstant
    (d : ℕ) (hd : 3 ≤ d) :
  chenGlobalFactor d ≤ stechkinNatConstant d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1380; TranslationalTilings.stechkinNatConstant_mono -/
namespace TranslationalTilings
axiom stechkinNatConstant_mono {e d : ℕ} (hed : e ≤ d) :
  stechkinNatConstant e ≤ stechkinNatConstant d
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1383; TranslationalTilings.polynomialCompleteSum_effective -/
namespace TranslationalTilings
axiom polynomialCompleteSum_effective
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1391; TranslationalTilings.polynomialCompleteSum_effective_of_primeBound -/
namespace TranslationalTilings
axiom polynomialCompleteSum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1400; TranslationalTilings.integral_complete_exponential_sum_effective -/
namespace TranslationalTilings
axiom integral_complete_exponential_sum_effective
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1407; TranslationalTilings.integral_complete_exponential_sum_effective_of_primeBound -/
namespace TranslationalTilings
axiom integral_complete_exponential_sum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d)
end TranslationalTilings
