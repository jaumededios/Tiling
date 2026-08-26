import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic.Order
import TranslationalTilings.NumberTheory.Stepanov.ReciprocalRoots

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

open TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1993; TranslationalTilings.exists_prime_addChar_reciprocalRoots_le -/
namespace TranslationalTilings
axiom exists_prime_addChar_reciprocalRoots_le
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ∃ r ≤ f.natDegree - 1, ∃ alpha : Fin r → ℂ,
      (∑ x : ZMod p, psi (f.eval x)) = -∑ i, alpha i ∧
      ∀ i, ‖alpha i‖ ≤ Real.sqrt p
end TranslationalTilings

/- blueprint/05a-weil-stepanov.md:2002; TranslationalTilings.polynomial_addChar_sum_prime_of_ne_one -/
namespace TranslationalTilings
axiom polynomial_addChar_sum_prime_of_ne_one
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, psi (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p
end TranslationalTilings

/- blueprint/05a-weil-stepanov.md:2010; TranslationalTilings.polynomial_addChar_sum_prime -/
namespace TranslationalTilings
axiom polynomial_addChar_sum_prime
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p
end TranslationalTilings
