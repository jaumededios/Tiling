import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
import TranslationalTilings.NumberTheory.FiniteCyclicPhase

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3  blueprint/05b-chen-complete-sums.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05b-chen-complete-sums.md:1191; TranslationalTilings.quadraticPolynomial -/
namespace TranslationalTilings
noncomputable def quadraticPolynomial (A B C : ℤ) : Polynomial ℤ :=
  Polynomial.monomial 2 A + Polynomial.monomial 1 B + Polynomial.C C
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1194; TranslationalTilings.quadraticGaussSum -/
namespace TranslationalTilings
noncomputable def quadraticGaussSum
    (q : ℕ) (hq : 0 < q) (A : ℤ) : ℂ :=
  polynomialCompleteSum q hq (quadraticPolynomial A 0 0)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1198; TranslationalTilings.quadraticGaussSum_one -/
namespace TranslationalTilings
axiom quadraticGaussSum_one (A : ℤ) :
  quadraticGaussSum 1 (by omega) A = 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1201; TranslationalTilings.quadraticGaussSum_oddPrime_base -/
namespace TranslationalTilings
axiom quadraticGaussSum_oddPrime_base
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) :
  ‖quadraticGaussSum p hp.pos A‖ = Real.sqrt p
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1206; TranslationalTilings.quadraticGaussSum_oddPrime_recurrence -/
namespace TranslationalTilings
axiom quadraticGaussSum_oddPrime_recurrence
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) (a : ℕ) :
  quadraticGaussSum (p ^ (a + 2)) (pow_pos hp.pos _) A =
    (p : ℂ) * quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1212; TranslationalTilings.quadraticCompleteSum_oddPrime_completeSquare -/
namespace TranslationalTilings
axiom quadraticCompleteSum_oddPrime_completeSquare
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a)
    (A B C : ℤ) (hA : ¬ p ∣ Int.natAbs A) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A‖
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1219; TranslationalTilings.quadraticGaussSum_two_base_two -/
namespace TranslationalTilings
axiom quadraticGaussSum_two_base_two
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 4 (by omega) A‖ = Real.sqrt 8
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1223; TranslationalTilings.quadraticGaussSum_two_base_three -/
namespace TranslationalTilings
axiom quadraticGaussSum_two_base_three
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 8 (by omega) A‖ = 4
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1227; TranslationalTilings.quadraticGaussSum_two_recurrence -/
namespace TranslationalTilings
axiom quadraticGaussSum_two_recurrence
    (A : ℤ) (hA : Odd A) (a : ℕ) (ha : 2 ≤ a) :
  quadraticGaussSum (2 ^ (a + 2)) (pow_pos (by omega) _) A =
    2 * quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1232; TranslationalTilings.quadraticCompleteSum_two_completeSquare -/
namespace TranslationalTilings
axiom quadraticCompleteSum_two_completeSquare
    (A B C : ℤ) (hA : Odd A) (hB : Even B)
    (a : ℕ) (ha : 2 ≤ a) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A‖
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1239; TranslationalTilings.quadraticCompleteSum_mod_two_norm -/
namespace TranslationalTilings
axiom quadraticCompleteSum_mod_two_norm
    (A B C : ℤ) :
  ‖polynomialCompleteSum 2 (by omega) (quadraticPolynomial A B C)‖ =
    if Even (A + B) then 2 else 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1244; Polynomial.eq_quadraticPolynomial_of_natDegree_le -/
namespace TranslationalTilings
axiom _root_.Polynomial.eq_quadraticPolynomial_of_natDegree_le
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2) :
  f = quadraticPolynomial (f.coeff 2) (f.coeff 1) (f.coeff 0)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1248; TranslationalTilings.linear_polynomialCompleteSum_eq_zero -/
namespace TranslationalTilings
axiom linear_polynomialCompleteSum_eq_zero
    (hq : 1 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  polynomialCompleteSum q (Nat.zero_lt_of_lt hq) f = 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1253; TranslationalTilings.linear_polynomialCompleteSum_bound -/
namespace TranslationalTilings
axiom linear_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ 1
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1258; TranslationalTilings.quadratic_primePower_linear_unit_eq_zero -/
namespace TranslationalTilings
axiom quadratic_primePower_linear_unit_eq_zero
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hlinear : ¬ p ∣ Int.natAbs (f.coeff 1))
    (hquadratic : p ∣ Int.natAbs (f.coeff 2)) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f = 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1265; TranslationalTilings.quadratic_oddPrimePower_norm -/
namespace TranslationalTilings
axiom quadratic_oddPrimePower_norm
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hquadratic : ¬ p ∣ Int.natAbs (f.coeff 2)) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ =
    Real.sqrt (p ^ a)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1272; TranslationalTilings.quadratic_twoPower_linear_odd_eq_zero -/
namespace TranslationalTilings
axiom quadratic_twoPower_linear_odd_eq_zero
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Odd (f.coeff 1)) :
  polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f = 0
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1277; TranslationalTilings.quadratic_twoPower_quadratic_odd_norm -/
namespace TranslationalTilings
axiom quadratic_twoPower_quadratic_odd_norm
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Even (f.coeff 1)) (hquadratic : Odd (f.coeff 2)) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f‖ =
    Real.sqrt (2 * 2 ^ a)
end TranslationalTilings

/- blueprint/05b-chen-complete-sums.md:1283; TranslationalTilings.quadratic_mod_two_bound -/
namespace TranslationalTilings
axiom quadratic_mod_two_bound
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime 2 (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum 2 (by omega) f‖ ≤ 2
end TranslationalTilings
