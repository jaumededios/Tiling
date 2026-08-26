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
import TranslationalTilings.NumberTheory.Stepanov.NewtonWaring

/-!
Validator-only module generated from the blueprint.
It contains exact-type theorem axioms and is outside production trust.

source-sha256 23f3373f2f8c6f1bc5d7ac91e541a7cbb875f039c26b478fa70608a0d99c27d5  blueprint/05a-weil-stepanov.md
-/


set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

open scoped BigOperators Real

/- blueprint/05a-weil-stepanov.md:538; TranslationalTilings.Stepanov.artinLPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def artinLPolynomial {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (max 1 f.natDegree),
    Polynomial.monomial n (artinCoefficient psi f n)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:543; TranslationalTilings.Stepanov.reciprocalRoots -/
namespace TranslationalTilings.Stepanov
noncomputable def reciprocalRoots
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) : Multiset ℂ :=
  (artinLPolynomial psi f).reverse.roots
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:548; TranslationalTilings.Stepanov.artinLPolynomial_coeff_zero -/
namespace TranslationalTilings.Stepanov
axiom artinLPolynomial_coeff_zero
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).coeff 0 = 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:553; TranslationalTilings.Stepanov.artinLPolynomial_constant_regression -/
namespace TranslationalTilings.Stepanov
axiom artinLPolynomial_constant_regression
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (c : ZMod p) :
    artinLPolynomial psi (Polynomial.C c) = 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:558; TranslationalTilings.Stepanov.artinLPolynomial_natDegree_le -/
namespace TranslationalTilings.Stepanov
axiom artinLPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).natDegree ≤ f.natDegree - 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:563; TranslationalTilings.Stepanov.reciprocalRoots_card_le -/
namespace TranslationalTilings.Stepanov
axiom reciprocalRoots_card_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (reciprocalRoots psi f).card ≤ f.natDegree - 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:575; TranslationalTilings.Stepanov.markedFactorSum -/
namespace TranslationalTilings.Stepanov
noncomputable def markedFactorSum
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (m : ℕ) : ℂ := by
  classical
  exact ∑ r ∈ Finset.Icc 1 m with r ∣ m,
    ∑ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        (r : ℂ) * monicWeight psi f G ^ (m / r)
      else 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:585; TranslationalTilings.Stepanov.truncatedEulerFactor -/
namespace TranslationalTilings.Stepanov
noncomputable def truncatedEulerFactor
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff r : ℕ) (G : MonicDegreePolynomial k r) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (cutoff / r + 1),
    Polynomial.monomial (a * r) (monicWeight psi f G ^ a)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:592; TranslationalTilings.Stepanov.truncatedEulerProduct -/
namespace TranslationalTilings.Stepanov
noncomputable def truncatedEulerProduct
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ := by
  classical
  exact ∏ r ∈ Finset.Icc 1 cutoff,
    ∏ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        truncatedEulerFactor psi f cutoff r G
      else 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:603; TranslationalTilings.Stepanov.markedFactorPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def markedFactorPolynomial
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 cutoff,
    Polynomial.monomial j (markedFactorSum psi f j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:610; TranslationalTilings.Stepanov.truncatedEulerProduct_coeff -/
namespace TranslationalTilings.Stepanov
axiom truncatedEulerProduct_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (truncatedEulerProduct psi f cutoff).coeff n =
      artinCoefficient psi f n
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:617; TranslationalTilings.Stepanov.truncatedEulerProduct_logDerivative_coeff -/
namespace TranslationalTilings.Stepanov
axiom truncatedEulerProduct_logDerivative_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (Polynomial.X *
      (truncatedEulerProduct psi f cutoff).derivative).coeff n =
    (truncatedEulerProduct psi f cutoff *
      markedFactorPolynomial psi f cutoff).coeff n
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:626; TranslationalTilings.Stepanov.artinCoefficient_zero -/
namespace TranslationalTilings.Stepanov
axiom artinCoefficient_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    artinCoefficient psi f 0 = 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:631; TranslationalTilings.Stepanov.truncatedEulerProduct_zero -/
namespace TranslationalTilings.Stepanov
axiom truncatedEulerProduct_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    truncatedEulerProduct psi f 0 = 1
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:636; TranslationalTilings.Stepanov.artinCoefficient_markedFactor_recurrence -/
namespace TranslationalTilings.Stepanov
axiom artinCoefficient_markedFactor_recurrence
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        markedFactorSum psi f j * artinCoefficient psi f (m - j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:669; TranslationalTilings.Stepanov.traceLiftAddChar -/
namespace TranslationalTilings.Stepanov
noncomputable def traceLiftAddChar
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (n : ℕ) :
    AddChar (GaloisField p n) ℂ :=
  psi.compAddMonoidHom
    (Algebra.trace (ZMod p) (GaloisField p n)).toAddMonoidHom
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:676; TranslationalTilings.Stepanov.extensionExponentialSum -/
namespace TranslationalTilings.Stepanov
noncomputable def extensionExponentialSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ x : GaloisField p n,
    traceLiftAddChar psi n
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:685; TranslationalTilings.Stepanov.extensionExponentialSum_one_eq_primeSum -/
namespace TranslationalTilings.Stepanov
theorem extensionExponentialSum_one_eq_primeSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    extensionExponentialSum psi f 1 =
      ∑ x : ZMod p, psi (f.eval x) := by
  classical
  let _ := Fintype.ofFinite (GaloisField p 1)
  let e := GaloisField.equivZmodP p
  rw [extensionExponentialSum]
  refine Fintype.sum_equiv e.toEquiv _ _ fun x ↦ ?_
  change psi (Algebra.trace (ZMod p) (GaloisField p 1)
    (f.eval₂ (algebraMap (ZMod p) (GaloisField p 1)) x)) =
      psi (f.eval (e x))
  congr 1
  rw [← Algebra.trace_eq_of_algEquiv e]
  rw [Algebra.trace_self_apply]
  simpa [Polynomial.aeval_def] using
    (Polynomial.aeval_algHom_apply e x f).symm
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:722; TranslationalTilings.Stepanov.minpolyFiber -/
namespace TranslationalTilings.Stepanov
noncomputable def minpolyFiber
    {p : ℕ} [Fact p.Prime] (m : ℕ)
    (G : Polynomial (ZMod p)) : Finset (GaloisField p m) := by
  letI := Fintype.ofFinite (GaloisField p m)
  classical
  exact Finset.univ.filter fun x ↦ minpoly (ZMod p) x = G
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:729; TranslationalTilings.Stepanov.minpolyEncoding -/
namespace TranslationalTilings.Stepanov
noncomputable def minpolyEncoding
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    MonicDegreePolynomial (ZMod p)
      (minpoly (ZMod p) x).natDegree :=
  (monicEncodingEquiv (ZMod p) (minpoly (ZMod p) x).natDegree).symm
    ⟨minpoly (ZMod p) x,
      minpoly.monic (Algebra.IsIntegral.isIntegral x), rfl⟩
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:737; TranslationalTilings.Stepanov.minpolyFiber_nonempty_iff_natDegree_dvd -/
namespace TranslationalTilings.Stepanov
axiom minpolyFiber_nonempty_iff_natDegree_dvd
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).Nonempty ↔ G.natDegree ∣ m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:743; TranslationalTilings.Stepanov.card_minpolyFiber -/
namespace TranslationalTilings.Stepanov
axiom card_minpolyFiber
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).card =
      if G.natDegree ∣ m then G.natDegree else 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:750; TranslationalTilings.Stepanov.minpolyFiber_eq_galoisOrbit -/
namespace TranslationalTilings.Stepanov
axiom minpolyFiber_eq_galoisOrbit
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (x : GaloisField p m) :
    ↑(minpolyFiber m (minpoly (ZMod p) x)) =
      MulAction.orbit
        (GaloisField p m ≃ₐ[ZMod p] GaloisField p m) x
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:757; TranslationalTilings.Stepanov.minpolyPhase_eq_sum_frobenius -/
namespace TranslationalTilings.Stepanov
axiom minpolyPhase_eq_sum_frobenius
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    algebraMap (ZMod p) (GaloisField p m)
        (monicPhase f (minpolyEncoding x)) =
      ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree,
        f.eval₂ (algebraMap (ZMod p) (GaloisField p m))
          (x ^ (p ^ i))
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:766; TranslationalTilings.Stepanov.traceLiftAddChar_eq_minpolyWeight_pow -/
namespace TranslationalTilings.Stepanov
axiom traceLiftAddChar_eq_minpolyWeight_pow
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    traceLiftAddChar psi m
        (f.eval₂ (algebraMap (ZMod p) (GaloisField p m)) x) =
      monicWeight psi f (minpolyEncoding x) ^
        (m / (minpoly (ZMod p) x).natDegree)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:775; TranslationalTilings.Stepanov.markedFactorSum_eq_extensionExponentialSum -/
namespace TranslationalTilings.Stepanov
axiom markedFactorSum_eq_extensionExponentialSum
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    markedFactorSum psi f m = extensionExponentialSum psi f m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:780; TranslationalTilings.Stepanov.artinCoefficient_extension_recurrence -/
namespace TranslationalTilings.Stepanov
axiom artinCoefficient_extension_recurrence
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        extensionExponentialSum psi f j *
          artinCoefficient psi f (m - j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:814; TranslationalTilings.Stepanov.rootFactorPolynomial -/
namespace TranslationalTilings.Stepanov
noncomputable def rootFactorPolynomial
    (roots : Multiset ℂ) : Polynomial ℂ :=
  (roots.map fun omega ↦
    1 - Polynomial.C omega * Polynomial.X).prod
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:819; TranslationalTilings.Stepanov.rootPowerSum -/
namespace TranslationalTilings.Stepanov
def rootPowerSum (roots : Multiset ℂ) (m : ℕ) : ℂ :=
  (roots.map fun omega ↦ omega ^ m).sum
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:822; TranslationalTilings.Stepanov.reverseRootPowerSum -/
namespace TranslationalTilings.Stepanov
noncomputable def reverseRootPowerSum
    (L : Polynomial ℂ) (m : ℕ) : ℂ :=
  rootPowerSum L.reverse.roots m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:826; TranslationalTilings.Stepanov.rootFactorPolynomial_newton_recurrence -/
namespace TranslationalTilings.Stepanov
axiom rootFactorPolynomial_newton_recurrence
    (roots : Multiset ℂ) {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * (rootFactorPolynomial roots).coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        rootPowerSum roots j *
          (rootFactorPolynomial roots).coeff (m - j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:833; TranslationalTilings.Stepanov.eq_rootFactorPolynomial_reverse_roots -/
namespace TranslationalTilings.Stepanov
axiom eq_rootFactorPolynomial_reverse_roots
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1) :
    L = rootFactorPolynomial L.reverse.roots
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:837; TranslationalTilings.Stepanov.reverseRoot_newton_recurrence -/
namespace TranslationalTilings.Stepanov
axiom reverseRoot_newton_recurrence
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * L.coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        reverseRootPowerSum L j * L.coeff (m - j)
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:844; TranslationalTilings.Stepanov.artinLPolynomial_coeff_eq_artinCoefficient -/
namespace TranslationalTilings.Stepanov
axiom artinLPolynomial_coeff_eq_artinCoefficient
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (m : ℕ) :
    (artinLPolynomial psi f).coeff m = artinCoefficient psi f m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:852; TranslationalTilings.Stepanov.neg_eq_of_convolution_recurrences -/
namespace TranslationalTilings.Stepanov
axiom neg_eq_of_convolution_recurrences
    (T S P : ℕ → ℂ) (hT0 : T 0 = 1)
    (hS : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        ∑ j ∈ Finset.Icc 1 m, S j * T (m - j))
    (hP : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        -∑ j ∈ Finset.Icc 1 m, P j * T (m - j)) :
    ∀ {m : ℕ}, 0 < m → S m = -P m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:862; TranslationalTilings.Stepanov.extensionExponentialSum_eq_neg_reverseRootPowerSum -/
namespace TranslationalTilings.Stepanov
axiom extensionExponentialSum_eq_neg_reverseRootPowerSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m =
      -reverseRootPowerSum (artinLPolynomial psi f) m
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:871; TranslationalTilings.Stepanov.extensionExponentialSum_eq_zero_of_natDegree_eq_one -/
namespace TranslationalTilings.Stepanov
axiom extensionExponentialSum_eq_zero_of_natDegree_eq_one
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hdegree : f.natDegree = 1) {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m = 0
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:878; TranslationalTilings.Stepanov.artinLPolynomial_trace_identity -/
namespace TranslationalTilings.Stepanov
axiom artinLPolynomial_trace_identity
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      -((reciprocalRoots psi f).map fun omega ↦ omega ^ n).sum
end TranslationalTilings.Stepanov

/- blueprint/05a-weil-stepanov.md:887; TranslationalTilings.Stepanov.extensionExponentialSum_eraseConstant -/
namespace TranslationalTilings.Stepanov
axiom extensionExponentialSum_eraseConstant
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      constantTwist psi f ^ n *
        extensionExponentialSum psi (eraseConstant f) n
end TranslationalTilings.Stepanov
