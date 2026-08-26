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

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:918; TranslationalTilings.Stepanov.artinSchreierPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def artinSchreierPolynomial
    {K : Type*} [Field K] (p : ℕ) (c : K) : Polynomial K :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C c
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:922; TranslationalTilings.Stepanov.artinSchreierPolynomial_monic -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierPolynomial_monic
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Monic
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:926; TranslationalTilings.Stepanov.artinSchreierPolynomial_natDegree -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierPolynomial_natDegree
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).natDegree = p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:930; TranslationalTilings.Stepanov.artinSchreierPolynomial_derivative -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierPolynomial_derivative
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).derivative = -1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:934; TranslationalTilings.Stepanov.artinSchreierPolynomial_separable -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierPolynomial_separable
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Separable
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:938; TranslationalTilings.Stepanov.artinSchreierSplittingRoot -/
namespace TranslationalTilings.Stepanov
noncomputable def artinSchreierSplittingRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).SplittingField :=
  Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits (artinSchreierPolynomial p c))
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map, artinSchreierPolynomial_natDegree c]
      exact (Fact.out : p.Prime).ne_zero))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:947; TranslationalTilings.Stepanov.artinSchreierSplittingRoot_isRoot -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierSplittingRoot_isRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ((artinSchreierPolynomial p c).map
      (algebraMap K (artinSchreierPolynomial p c).SplittingField)).IsRoot
        (artinSchreierSplittingRoot c)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:954; TranslationalTilings.Stepanov.artinSchreier_root_sub_root_mem_bot -/
namespace TranslationalTilings.Stepanov
axiom artinSchreier_root_sub_root_mem_bot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    {c : K} {x y : L}
    (hx : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) x = 0)
    (hy : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) y = 0) :
    x - y ∈ (⊥ : Subfield L)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:962; TranslationalTilings.Stepanov.artinSchreier_splittingField_adjoin_root_eq_top -/
namespace TranslationalTilings.Stepanov
axiom artinSchreier_splittingField_adjoin_root_eq_top
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    IntermediateField.adjoin K {artinSchreierSplittingRoot c} =
      (⊤ : IntermediateField K
        (artinSchreierPolynomial p c).SplittingField)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:969; TranslationalTilings.Stepanov.exists_artinSchreierAutShift -/
namespace TranslationalTilings.Stepanov
axiom exists_artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ∃ phi : Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
        (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField),
      (∀ sigma,
        (phi sigma : (artinSchreierPolynomial p c).SplittingField) =
          sigma (artinSchreierSplittingRoot c) -
            artinSchreierSplittingRoot c) ∧
      Function.Injective phi
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:980; TranslationalTilings.Stepanov.artinSchreierAutShift -/
namespace TranslationalTilings.Stepanov
noncomputable def artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
      (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField) :=
  Classical.choose (exists_artinSchreierAutShift c)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:987; TranslationalTilings.Stepanov.artinSchreierAutShift_apply -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierAutShift_apply
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K)
    (sigma : Additive (Polynomial.Gal (artinSchreierPolynomial p c))) :
    (artinSchreierAutShift c sigma :
      (artinSchreierPolynomial p c).SplittingField) =
        sigma (artinSchreierSplittingRoot c) -
          artinSchreierSplittingRoot c
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:996; TranslationalTilings.Stepanov.artinSchreierAutShift_injective -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierAutShift_injective
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : Function.Injective (artinSchreierAutShift c)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1000; TranslationalTilings.Stepanov.artinSchreier_minpoly_natDegree_dvd_prime -/
namespace TranslationalTilings.Stepanov
axiom artinSchreier_minpoly_natDegree_dvd_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree ∣ p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1005; TranslationalTilings.Stepanov.artinSchreier_minpoly_natDegree_eq_one_or_prime -/
namespace TranslationalTilings.Stepanov
axiom artinSchreier_minpoly_natDegree_eq_one_or_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree = 1 ∨
      (minpoly K (artinSchreierSplittingRoot c)).natDegree = p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1011; TranslationalTilings.Stepanov.artinSchreierPolynomial_irreducible_iff_no_root -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierPolynomial_irreducible_iff_no_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Irreducible (artinSchreierPolynomial p c) ↔
      ¬ ∃ x : K, x ^ p - x = c
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1017; TranslationalTilings.Stepanov.not_artinSchreierPolynomial_irreducible_iff_root -/
namespace TranslationalTilings.Stepanov
axiom not_artinSchreierPolynomial_irreducible_iff_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ¬ Irreducible (artinSchreierPolynomial p c) ↔
      ∃ x : K, x ^ p - x = c
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1023; TranslationalTilings.Stepanov.artinSchreierRatFuncPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def artinSchreierRatFuncPolynomial
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p)) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1029; TranslationalTilings.Stepanov.ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap -/
namespace TranslationalTilings.Stepanov
axiom ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap
    {p : ℕ} [Fact p.Prime]
    (h : RatFunc (ZMod p)) (g : Polynomial (ZMod p))
    (heq : h ^ p - h =
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g) :
    ∃ A : Polynomial (ZMod p),
      h = algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) A
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1037; TranslationalTilings.Stepanov.polynomial_pow_sub_self_natDegree -/
namespace TranslationalTilings.Stepanov
axiom polynomial_pow_sub_self_natDegree
    {p : ℕ} [Fact p.Prime]
    (A : Polynomial (ZMod p)) (hA : 0 < A.natDegree) :
    (A ^ p - A).natDegree = p * A.natDegree
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1042; TranslationalTilings.Stepanov.no_ratFunc_artinSchreier_root -/
namespace TranslationalTilings.Stepanov
axiom no_ratFunc_artinSchreier_root
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ¬ ∃ h : RatFunc (ZMod p),
      h ^ p - h =
        -algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1049; TranslationalTilings.Stepanov.artinSchreierRatFuncPolynomial_irreducible -/
namespace TranslationalTilings.Stepanov
axiom artinSchreierRatFuncPolynomial_irreducible
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (artinSchreierRatFuncPolynomial f)
end TranslationalTilings.Stepanov
