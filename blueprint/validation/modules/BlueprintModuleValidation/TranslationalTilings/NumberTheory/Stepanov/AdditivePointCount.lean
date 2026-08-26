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
import TranslationalTilings.NumberTheory.Stepanov.TranslationProduct

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:1818; TranslationalTilings.Stepanov.additiveAuxiliaryPolynomial_natDegree_le -/
namespace TranslationalTilings.Stepanov
axiom additiveAuxiliaryPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    (additiveAuxiliaryPolynomial par f e).natDegree ≤
      par.S + d * (p - 1) * p ^ (n - 1) + p ^ n * par.K
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1830; TranslationalTilings.Stepanov.tracePhaseFiberCard -/
namespace TranslationalTilings.Stepanov
noncomputable def tracePhaseFiberCard
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n : ℕ) (b : ZMod p) : ℕ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact (Finset.univ.filter fun x : GaloisField p n ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b).card
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1851; TranslationalTilings.Stepanov.stepanov_traceFiberCard_upper -/
namespace TranslationalTilings.Stepanov
axiom stepanov_traceFiberCard_upper
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p) (b : ZMod p) :
    (tracePhaseFiberCard f n b : ℝ) ≤ (p : ℝ) ^ (n - 1) +
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1867; TranslationalTilings.Stepanov.additive_stepanov_point_count -/
namespace TranslationalTilings.Stepanov
axiom additive_stepanov_point_count
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ b : ZMod p,
      |(tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1)| ≤
        C * (Real.sqrt p) ^ n
end TranslationalTilings.Stepanov
