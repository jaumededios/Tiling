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

/- blueprint/05a-weil-stepanov.md:185; TranslationalTilings.Stepanov.eraseConstant -/
namespace TranslationalTilings.Stepanov
noncomputable def eraseConstant {k : Type*} [CommRing k] (f : Polynomial k) :
    Polynomial k :=
  f - Polynomial.C (f.coeff 0)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:189; TranslationalTilings.Stepanov.constantTwist -/
namespace TranslationalTilings.Stepanov
def constantTwist {k : Type*} [CommRing k]
    (psi : AddChar k ℂ) (f : Polynomial k) : ℂ :=
  psi (f.coeff 0)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:193; TranslationalTilings.Stepanov.eraseConstant_coeff_zero -/
namespace TranslationalTilings.Stepanov
axiom eraseConstant_coeff_zero {k : Type*} [CommRing k]
    (f : Polynomial k) :
    (eraseConstant f).coeff 0 = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:197; TranslationalTilings.Stepanov.eraseConstant_natDegree -/
namespace TranslationalTilings.Stepanov
axiom eraseConstant_natDegree {k : Type*} [CommRing k]
    (f : Polynomial k) (hpos : 0 < f.natDegree) :
    (eraseConstant f).natDegree = f.natDegree
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:201; TranslationalTilings.Stepanov.norm_constantTwist_of_finite -/
namespace TranslationalTilings.Stepanov
axiom norm_constantTwist_of_finite
    {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    ‖constantTwist psi f‖ = 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:233; TranslationalTilings.Stepanov.MonicDegreePolynomial -/
namespace TranslationalTilings.Stepanov
structure MonicDegreePolynomial (k : Type*) [CommRing k] (n : ℕ) where
  coeff : Fin n → k
deriving Fintype
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:239; TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
noncomputable def toPolynomial {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : Polynomial k :=
  Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.monomial (n - 1 - i.1) (A.coeff i)
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:244; TranslationalTilings.Stepanov.MonicDegreePolynomial.waringCoeff -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
def waringCoeff {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (j : ℕ) : k :=
  if h : 1 ≤ j ∧ j ≤ n then A.coeff ⟨j - 1, by omega⟩ else 0
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:248; TranslationalTilings.Stepanov.MonicDegreePolynomial.mul -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
noncomputable def mul {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    MonicDegreePolynomial k (n + m) :=
  ⟨fun i ↦ (A.toPolynomial * B.toPolynomial).coeff (n + m - 1 - i.1)⟩
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:253; TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial_monic -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
axiom toPolynomial_monic {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : A.toPolynomial.Monic
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:256; TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial_natDegree -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
axiom toPolynomial_natDegree {k : Type*} [CommRing k] [Nontrivial k]
    {n : ℕ} (A : MonicDegreePolynomial k n) :
    A.toPolynomial.natDegree = n
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:260; TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial_mul -/
namespace TranslationalTilings.Stepanov.MonicDegreePolynomial
axiom toPolynomial_mul {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    (A.mul B).toPolynomial = A.toPolynomial * B.toPolynomial
end TranslationalTilings.Stepanov.MonicDegreePolynomial

/- blueprint/05a-weil-stepanov.md:273; TranslationalTilings.Stepanov.reverseCoordinatesEquiv -/
namespace TranslationalTilings.Stepanov
def reverseCoordinatesEquiv (k : Type*) (n : ℕ) :
    (Fin n → k) ≃ (Fin n → k) where
  toFun a i := a i.rev
  invFun a i := a i.rev
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:280; TranslationalTilings.Stepanov.MonicDegreePolynomial.coeffEquiv -/
namespace TranslationalTilings.Stepanov
def MonicDegreePolynomial.coeffEquiv
    (k : Type*) [CommRing k] (n : ℕ) :
    MonicDegreePolynomial k n ≃ (Fin n → k) where
  toFun := MonicDegreePolynomial.coeff
  invFun := MonicDegreePolynomial.mk
  left_inv _ := rfl
  right_inv _ := rfl
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:288; TranslationalTilings.Stepanov.monicEncodingEquiv -/
namespace TranslationalTilings.Stepanov
noncomputable def monicEncodingEquiv
    (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    MonicDegreePolynomial k n ≃
      {P : Polynomial k // P.Monic ∧ P.natDegree = n} :=
  (MonicDegreePolynomial.coeffEquiv k n).trans <|
    (reverseCoordinatesEquiv k n).trans <|
      (Polynomial.degreeLTEquiv k n).symm.toEquiv.trans
        (Polynomial.monicEquivDegreeLT (R := k) n).symm
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:297; TranslationalTilings.Stepanov.monicEncodingEquiv_apply -/
namespace TranslationalTilings.Stepanov
axiom monicEncodingEquiv_apply
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    (monicEncodingEquiv k n A).1 = A.toPolynomial
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:302; TranslationalTilings.Stepanov.MonicDegreePolynomial.ofPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def MonicDegreePolynomial.ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) : MonicDegreePolynomial k n :=
  (monicEncodingEquiv k n).symm ⟨P, hPmonic, hPdegree⟩
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:308; TranslationalTilings.Stepanov.MonicDegreePolynomial.toPolynomial_ofPolynomial -/
namespace TranslationalTilings.Stepanov
axiom MonicDegreePolynomial.toPolynomial_ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) :
    (MonicDegreePolynomial.ofPolynomial P hPmonic hPdegree).toPolynomial = P
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:314; TranslationalTilings.Stepanov.MonicDegreePolynomial.ofPolynomial_toPolynomial -/
namespace TranslationalTilings.Stepanov
axiom MonicDegreePolynomial.ofPolynomial_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    MonicDegreePolynomial.ofPolynomial A.toPolynomial
      A.toPolynomial_monic A.toPolynomial_natDegree = A
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:338; <private:waringVariable@blueprint/05a-weil-stepanov.md:338> -/
namespace TranslationalTilings.Stepanov
private noncomputable def waringVariable
    (k : Type*) [CommRing k] (n j : ℕ) : MvPolynomial (Fin n) k :=
  if h : 1 ≤ j ∧ j ≤ n then MvPolynomial.X ⟨j - 1, by omega⟩ else 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:342; TranslationalTilings.Stepanov.waringPowerSum -/
namespace TranslationalTilings.Stepanov
noncomputable def waringPowerSum (k : Type*) [CommRing k] (n m : ℕ) :
    MvPolynomial (Fin n) k :=
  if _hm : m = 0 then MvPolynomial.C (n : k)
  else -((m : MvPolynomial (Fin n) k) * waringVariable k n m +
    ∑ j : Fin (m - 1),
      waringVariable k n (j.1 + 1) *
        waringPowerSum k n (m - (j.1 + 1)))
termination_by m
decreasing_by omega
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:352; TranslationalTilings.Stepanov.monicPowerSum -/
namespace TranslationalTilings.Stepanov
noncomputable def monicPowerSum {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (m : ℕ) : k :=
  MvPolynomial.eval A.coeff (waringPowerSum k n m)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:356; TranslationalTilings.Stepanov.monicPhase -/
namespace TranslationalTilings.Stepanov
noncomputable def monicPhase {k : Type*} [CommRing k] {n : ℕ}
    (f : Polynomial k) (A : MonicDegreePolynomial k n) : k :=
  ∑ j ∈ f.support, f.coeff j * monicPowerSum A j
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:360; TranslationalTilings.Stepanov.monicWeight -/
namespace TranslationalTilings.Stepanov
noncomputable def monicWeight {k : Type*} [CommRing k] {n : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) : ℂ :=
  psi (monicPhase f A)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:365; TranslationalTilings.Stepanov.artinCoefficient -/
namespace TranslationalTilings.Stepanov
noncomputable def artinCoefficient {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (n : ℕ) : ℂ :=
  ∑ A : MonicDegreePolynomial k n, monicWeight psi f A
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:394; TranslationalTilings.Stepanov.monicPowerSum_eq_sum_roots -/
namespace TranslationalTilings.Stepanov
axiom monicPowerSum_eq_sum_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (A : MonicDegreePolynomial k n)
    (hA : (A.toPolynomial.map (algebraMap k K)).Splits) (m : ℕ) :
    algebraMap k K (monicPowerSum A m) =
      ((A.toPolynomial.map (algebraMap k K)).roots.map fun x ↦ x ^ m).sum
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:401; TranslationalTilings.Stepanov.monicWeight_mul -/
namespace TranslationalTilings.Stepanov
axiom monicWeight_mul
    {k : Type*} [Field k] {n m : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    monicWeight psi f (A.mul B) = monicWeight psi f A * monicWeight psi f B
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:413; TranslationalTilings.Stepanov.MonicPolynomial -/
namespace TranslationalTilings.Stepanov
def MonicPolynomial (k : Type*) [CommRing k] :=
  {P : Polynomial k // P.Monic}
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:418; TranslationalTilings.Stepanov.MonicPolynomial.encoding -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
noncomputable def encoding
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) :
    MonicDegreePolynomial k P.1.natDegree :=
  (monicEncodingEquiv k P.1.natDegree).symm ⟨P.1, P.2, rfl⟩
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:424; TranslationalTilings.Stepanov.MonicPolynomial.encoding_toPolynomial -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
axiom encoding_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) : P.encoding.toPolynomial = P.1
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:428; TranslationalTilings.Stepanov.MonicPolynomial.normalizedIrreducibleFactors -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
noncomputable def normalizedIrreducibleFactors
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    Multiset (MonicPolynomial k) := by
  letI := Classical.decEq k
  exact (UniqueFactorizationMonoid.normalizedFactors P.1).attach.map
    fun G ↦
      ⟨G.1,
        ((Polynomial.mem_normalizedFactors_iff P.2.ne_zero).mp G.2).2.1⟩
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:437; TranslationalTilings.Stepanov.MonicPolynomial.normalizedIrreducibleFactors_irreducible -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
axiom normalizedIrreducibleFactors_irreducible
    {k : Type*} [Field k] (P : MonicPolynomial k)
    {G : MonicPolynomial k}
    (hG : G ∈ P.normalizedIrreducibleFactors) : Irreducible G.1
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:442; TranslationalTilings.Stepanov.MonicPolynomial.normalizedIrreducibleFactors_prod -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
axiom normalizedIrreducibleFactors_prod
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1).prod = P.1
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:446; TranslationalTilings.Stepanov.MonicPolynomial.normalizedIrreducibleFactors_degree_sum -/
namespace TranslationalTilings.Stepanov.MonicPolynomial
axiom normalizedIrreducibleFactors_degree_sum
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1.natDegree).sum =
      P.1.natDegree
end TranslationalTilings.Stepanov.MonicPolynomial

/- blueprint/05a-weil-stepanov.md:453; TranslationalTilings.Stepanov.monicPolynomialWeight -/
namespace TranslationalTilings.Stepanov
noncomputable def monicPolynomialWeight
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) : ℂ :=
  monicWeight psi f P.encoding
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:459; TranslationalTilings.Stepanov.monicWeight_eq_prod_normalizedIrreducibleFactors -/
namespace TranslationalTilings.Stepanov
axiom monicWeight_eq_prod_normalizedIrreducibleFactors
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) :
    monicPolynomialWeight psi f P =
      (P.normalizedIrreducibleFactors.map
        (monicPolynomialWeight psi f)).prod
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:502; TranslationalTilings.Stepanov.monicPhase_affine_last -/
namespace TranslationalTilings.Stepanov
axiom monicPhase_affine_last
    {k : Type*} [CommRing k] {d : ℕ}
    (f : Polynomial k) (hd : f.natDegree = d) (hdpos : 0 < d)
    (n : ℕ) (hdn : d ≤ n) :
    ∀ A : MonicDegreePolynomial k n, ∀ u : k,
      monicPhase f ⟨Function.update A.coeff ⟨d - 1, by omega⟩ u⟩ =
        -(d : k) * f.leadingCoeff * u +
          monicPhase f
            ⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:512; TranslationalTilings.Stepanov.artinCoefficient_eq_zero_of_degree_le -/
namespace TranslationalTilings.Stepanov
axiom artinCoefficient_eq_zero_of_degree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : f.natDegree ≤ n) :
    artinCoefficient psi f n = 0
end TranslationalTilings.Stepanov
