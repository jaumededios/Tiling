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
import TranslationalTilings.NumberTheory.Stepanov.ArtinSchreier
import TranslationalTilings.NumberTheory.Stepanov.HasseMultiplicity
import TranslationalTilings.NumberTheory.Stepanov.NewtonWaring

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:1532; TranslationalTilings.Stepanov.polynomialTranslate -/
namespace TranslationalTilings.Stepanov
noncomputable def polynomialTranslate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (beta : ZMod p) :
    Polynomial (Polynomial (ZMod p)) :=
  P.comp (Polynomial.X + Polynomial.C (Polynomial.C beta))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1538; TranslationalTilings.Stepanov.translationProduct -/
namespace TranslationalTilings.Stepanov
noncomputable def translationProduct
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  ∏ beta : ZMod p, polynomialTranslate P beta
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1544; TranslationalTilings.Stepanov.translationProduct_translate -/
namespace TranslationalTilings.Stepanov
axiom translationProduct_translate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (gamma : ZMod p) :
    polynomialTranslate (translationProduct P) gamma = translationProduct P
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1549; TranslationalTilings.Stepanov.exists_translationProductQuotient -/
namespace TranslationalTilings.Stepanov
axiom exists_translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    ∃ Q : Polynomial (Polynomial (ZMod p)),
      translationProduct P =
          Q.comp (Polynomial.X ^ p - Polynomial.X) ∧
        Q.natDegree ≤ p - 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1557; TranslationalTilings.Stepanov.translationProductQuotient -/
namespace TranslationalTilings.Stepanov
noncomputable def translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  if hP : P.natDegree < p then
    Classical.choose (exists_translationProductQuotient P hP)
  else 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1565; TranslationalTilings.Stepanov.translationProductQuotient_spec -/
namespace TranslationalTilings.Stepanov
axiom translationProductQuotient_spec
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    translationProduct P =
        (translationProductQuotient P).comp
          (Polynomial.X ^ p - Polynomial.X) ∧
      (translationProductQuotient P).natDegree ≤ p - 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1573; TranslationalTilings.Stepanov.translationProductQuotient_coeff_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom translationProductQuotient_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) (a : ℕ) :
    ((translationProductQuotient P).coeff a).natDegree < p * S
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1594; TranslationalTilings.Stepanov.zeroBlockNormPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) : Polynomial (ZMod p) :=
  (translationProductQuotient P).eval
    (Polynomial.C (f.coeff 0) - f ^ (p ^ u))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1601; TranslationalTilings.Stepanov.zeroBlockNormPolynomial_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom zeroBlockNormPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) :
    (zeroBlockNormPolynomial f u P).natDegree <
      p * S + f.natDegree * p ^ u * (p - 1)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1610; TranslationalTilings.Stepanov.X_pow_dvd_zeroBlockNormPolynomial -/
namespace TranslationalTilings.Stepanov
axiom X_pow_dvd_zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) (hu : u ≤ n)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n u)) :
    Polynomial.X ^ (p ^ n) ∣ zeroBlockNormPolynomial f u P
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1619; TranslationalTilings.Stepanov.zeroBlockNormPolynomial_eq_zero -/
namespace TranslationalTilings.Stepanov
axiom zeroBlockNormPolynomial_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p)
    (hcoeff : ∀ i, (P.coeff i).natDegree < par.S)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n par.u)) :
    zeroBlockNormPolynomial f par.u P = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1644; TranslationalTilings.Stepanov.zeroBlockArtinSchreierPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def zeroBlockArtinSchreierPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
        (f ^ (p ^ u) - Polynomial.C (f.coeff 0)))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1653; TranslationalTilings.Stepanov.zeroBlockArtinSchreierPolynomial_translate -/
namespace TranslationalTilings.Stepanov
axiom zeroBlockArtinSchreierPolynomial_translate
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    zeroBlockArtinSchreierPolynomial f u =
      (artinSchreierRatFuncPolynomial (eraseConstant f)).comp
        (Polynomial.X + Polynomial.C
          (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
            (lowerTracePolynomial f u)))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1662; TranslationalTilings.Stepanov.zeroBlockArtinSchreierPolynomial_irreducible -/
namespace TranslationalTilings.Stepanov
axiom zeroBlockArtinSchreierPolynomial_irreducible
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (zeroBlockArtinSchreierPolynomial f u)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1668; TranslationalTilings.Stepanov.zeroBlockEval -/
namespace TranslationalTilings.Stepanov
noncomputable def zeroBlockEval
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (P : Polynomial (Polynomial (ZMod p))) (z : L) : L :=
  P.eval₂
    ((algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))) z
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1676; TranslationalTilings.Stepanov.zeroBlockNorm_eq_zero_implies_exists_zero_factor -/
namespace TranslationalTilings.Stepanov
axiom zeroBlockNorm_eq_zero_implies_exists_zero_factor
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    (hnorm : zeroBlockNormPolynomial f u P = 0) :
    ∀ {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L] (z : L),
      Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0 →
      ∃ beta : ZMod p,
        zeroBlockEval P
          (z + algebraMap (RatFunc (ZMod p)) L
            (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1688; TranslationalTilings.Stepanov.zeroBlock_minpoly_add_primeField -/
namespace TranslationalTilings.Stepanov
axiom zeroBlock_minpoly_add_primeField
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (beta : ZMod p) :
    minpoly (RatFunc (ZMod p))
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) =
      zeroBlockArtinSchreierPolynomial f u
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1701; TranslationalTilings.Stepanov.eq_zero_of_zeroBlockEval_eq_zero -/
namespace TranslationalTilings.Stepanov
axiom eq_zero_of_zeroBlockEval_eq_zero
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (z : L)
    (hz : Polynomial.aeval z (zeroBlockArtinSchreierPolynomial f u) = 0)
    (beta : ZMod p)
    (hzero : zeroBlockEval P
      (z + algebraMap (RatFunc (ZMod p)) L
        (algebraMap (ZMod p) (RatFunc (ZMod p)) beta)) = 0) :
    P = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1730; TranslationalTilings.Stepanov.auxiliaryBlock -/
namespace TranslationalTilings.Stepanov
noncomputable def auxiliaryBlock
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : Polynomial (Polynomial (ZMod p)) :=
  ∑ i : Fin p, Polynomial.monomial i.1 (e.coeff i j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1737; TranslationalTilings.Stepanov.auxiliaryBlock_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom auxiliaryBlock_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : (auxiliaryBlock e j).natDegree < p
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1743; TranslationalTilings.Stepanov.auxiliaryBlock_coeff_natDegree_lt -/
namespace TranslationalTilings.Stepanov
axiom auxiliaryBlock_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) (i : ℕ) :
    ((auxiliaryBlock e j).coeff i).natDegree < par.S
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1750; TranslationalTilings.Stepanov.X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero -/
namespace TranslationalTilings.Stepanov
axiom X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0)
    (j : Fin (par.K + 1))
    (hprev : ∀ q : Fin (par.K + 1), q.1 < j.1 →
      auxiliaryBlock e q = 0) :
    Polynomial.X ^ (p ^ n) ∣
      (auxiliaryBlock e j).eval (upperTracePolynomial f n par.u)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1762; TranslationalTilings.Stepanov.auxiliaryBlock_eq_zero_of_previous_eq_zero -/
namespace TranslationalTilings.Stepanov
axiom auxiliaryBlock_eq_zero_of_previous_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0)
    (j : Fin (par.K + 1))
    (hprev : ∀ q : Fin (par.K + 1), q.1 < j.1 →
      auxiliaryBlock e q = 0) :
    auxiliaryBlock e j = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1774; TranslationalTilings.Stepanov.all_auxiliaryBlocks_eq_zero -/
namespace TranslationalTilings.Stepanov
axiom all_auxiliaryBlocks_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0) :
    ∀ j : Fin (par.K + 1), auxiliaryBlock e j = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1783; TranslationalTilings.Stepanov.additiveAuxiliaryPolynomial_ne_zero_of_blocks -/
namespace TranslationalTilings.Stepanov
axiom additiveAuxiliaryPolynomial_ne_zero_of_blocks
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:1791; TranslationalTilings.Stepanov.additiveAuxiliaryPolynomial_ne_zero -/
namespace TranslationalTilings.Stepanov
axiom additiveAuxiliaryPolynomial_ne_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0
end TranslationalTilings.Stepanov
