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
import TranslationalTilings.NumberTheory.Stepanov.AdditivePointCount
import TranslationalTilings.NumberTheory.Stepanov.ArtinLSeries

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:1895; TranslationalTilings.Stepanov.extensionExponentialSum_bound -/
namespace TranslationalTilings.Stepanov
axiom extensionExponentialSum_bound
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖extensionExponentialSum psi f n‖ ≤
        C * (Real.sqrt p) ^ n
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1920; TranslationalTilings.Stepanov.exists_unbounded_aligned_powers -/
namespace TranslationalTilings.Stepanov
axiom exists_unbounded_aligned_powers
    {s : ℕ} (u : Fin s → Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, Filter.Tendsto (fun m ↦ u i ^ n m)
        Filter.atTop (nhds 1)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1926; TranslationalTilings.Stepanov.maximalRootMultiplicity -/
namespace TranslationalTilings.Stepanov
noncomputable def maximalRootMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) : ℕ := by
  classical
  exact (roots.filter fun z ↦ ‖z‖ = rho).card
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1931; TranslationalTilings.Stepanov.exists_normalized_powerSum_tendsto_maximalMultiplicity -/
namespace TranslationalTilings.Stepanov
axiom exists_normalized_powerSum_tendsto_maximalMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hle : ∀ z ∈ roots, ‖z‖ ≤ rho)
    (hmax : ∃ z ∈ roots, ‖z‖ = rho) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Filter.Tendsto
        (fun m ↦
          (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum)
        Filter.atTop
        (nhds (maximalRootMultiplicity roots rho : ℂ))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1942; TranslationalTilings.Stepanov.norm_le_of_power_sum_bound -/
namespace TranslationalTilings.Stepanov
axiom norm_le_of_power_sum_bound
    (roots : Multiset ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hpow : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖(roots.map fun z ↦ z ^ n).sum‖ ≤ C * R ^ n) :
    ∀ z ∈ roots, ‖z‖ ≤ R
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1965; TranslationalTilings.Stepanov.reciprocalRoots_norm_le -/
namespace TranslationalTilings.Stepanov
axiom reciprocalRoots_norm_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∀ omega ∈ reciprocalRoots psi f, ‖omega‖ ≤ Real.sqrt p
end TranslationalTilings.Stepanov
