# The prime polynomial Weil bound by the Stepanov--Schmidt method

This chapter is the recursive prerequisite for the large-prime branch of
Chapter 05b, which is used by Chapter 5.  Its terminal result is the
fixed-character estimate

\[
  \left|\sum_{x\in\mathbf F_p}\psi(f(x))\right|
     \le (\deg f-1)\sqrt p,
  \qquad 0<\deg f<p,
\]

for every nontrivial additive character `psi`.  The standard-character
specialization is exported under the exact name consumed by Chapter 5:
`polynomial_addChar_sum_prime`.

This is not a wrapper around the Weil conjectures.  The accepted proof is the
elementary Artin-L-series/Stepanov proof, specialized all the way to a
polynomial over the prime field.  The specialization removes multiplicative
characters, rational-function poles, Kummer extensions, curves, class field
theory, Riemann--Roch, and the function-field Riemann hypothesis.  It retains
and proves the pieces which actually do work in the elementary argument:

```text
Newton--Waring identities for a monic polynomial
  -> cancellation of all L-series coefficients in degree >= deg f
  -> bounded Euler/log-derivative recurrence over every GaloisField p n
  -> Artin--Schreier irreducibility for Y^p-Y+f(X)
  -> Hasse-derivative multiplicity and Frobenius freezing
  -> a nonzero Stepanov auxiliary polynomial for each trace fiber
  -> trace-fiber equidistribution with O_{p,d}(p^(n/2)) error
  -> simultaneous-phase control of reciprocal roots
  -> the degree-minus-one bound at n=1.
```

## Source audit and proof-route decision

The primary implementation source is Todd Cochrane and Christopher Pinner,
*Using Stepanov's Method for Exponential Sums Involving Rational Functions*,
especially (1.3), Section 2, Lemma 3.1, Lemma 3.2, and Theorem 3.1.  A local
copy is `tmp/pdfs/cochrane-pinner-stepmix.pdf`; all fifteen pages were checked.
Their polynomial, pure-additive specialization has `M=deg f`, `L=0`, and
therefore gives the constant `M-1` in (1.3).

The four local images `tmp/pdfs/weil-204.png` through
`tmp/pdfs/weil-207.png` were also checked.  Weil's 1948 proof gives the same
constant through a fixed ray-class character and a degree-`d-1` L-factor.
Appendix Lemma A.5 of
`tmp/pdfs/arkhipov-chubarikov-karatsuba.pdf` prints the weaker constant
`d*sqrt p`, even though the book's Chapter 2, Theorem 2.1 uses
`(d-1)*sqrt p`.  The formal statement below follows the sharper Weil and
Cochrane--Pinner statements; the Appendix A.5 display is not silently treated
as though it contained that sharper constant.

Kevin Broughan's Appendix E, *The Weil Exponential Sum Bound*, independently
advertises the same Waring/hyperderivative proof and the same sharp constant.
Only the official metadata and lawful preview were available; the chapter PDF
was access-controlled.  No mathematical step below relies on inaccessible
text from that source.

### Why the function-field route is rejected

The earlier candidate route through Weil's fixed ray-class L-series is
mathematically sound, but its recursive closure in pinned Mathlib would need
new theories of complete-curve divisors, residues and weak approximation,
Riemann--Roch and duality, ray groups, Artin--Schreier reciprocity, curve zeta
functions, product-surface intersection theory, Hodge-index positivity, and
the curve Riemann hypothesis.  None of those layers is present in the pinned
checkout.  That route would be a separate major formalization, not an honest
prerequisite file.  It is retained here only as a scope audit; there is no
Lean declaration for it and it is outside the accepted import graph.

### Clean-room Stepanov evidence

The read-only repository `tmp/RiemannHypothesisCurves` (math-inc, commit
`c99880d`) shows that Mathlib's Hasse derivatives, a homogeneous auxiliary
linear system, nonzero-polynomial arguments, and root multiplicity estimates
support a roughly four-thousand-line Bombieri--Stepanov development for a
hyperelliptic family.  It contains no license file and treats `y^2=f(x)`, not
the Artin--Schreier trace fibers needed here.  Therefore no code, declaration,
proof text, or file structure is copied from it.  It is architecture evidence
only.  The construction below is independently derived from
Cochrane--Pinner's printed formulas and is specialized to
`Y^p-Y+f(X)`.

## Feasibility, module homes, and dependency direction

The recursive closure is finite, but it is still a substantial new milestone.
A realistic implementation is several thousand Lean lines, concentrated in
the nonzero auxiliary-polynomial proof and the linear-system degree audit.
The dependency-ordered module split is:

```text
TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean
TranslationalTilings/NumberTheory/Stepanov/ArtinLSeries.lean
TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean
TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean
TranslationalTilings/NumberTheory/Stepanov/TranslationProduct.lean
TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean
TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean
TranslationalTilings/NumberTheory/PolynomialWeilBound.lean
```

Only the last module is imported by the complete-exponential-sum development.
The first seven modules form reusable algebraic seams, but their construction
details remain private except for the displayed audit theorems.  There is no
dependency on Chapter 5 or on the later Chen prime-power recursion.

The signatures in this chapter were checked in the dedicated pinned-version
validator `tmp/BlueprintWeilStepanov.lean`.  Its import union is:

```lean
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Tactic.Order
```

The pinned Mathlib commit is
`db584cd6d46c92f209a44c0f1c829460d327499d`.

Exact reuse from Mathlib is:

- `AddChar`, `AddChar.mulShift`, character values on sums, and
  `AddChar.sum_eq_zero_iff_ne_zero`;
- `ZMod`, its field structure under `Fact p.Prime`,
  `ZMod.stdAddChar`, and `ZMod.isPrimitive_stdAddChar`;
- `MvPolynomial.psum`, elementary symmetric polynomials, and
  `MvPolynomial.psum_eq_mul_esymm_sub_sum`;
- `Polynomial.hasseDeriv`, its product formula, Taylor coefficients,
  `Polynomial.rootMultiplicity`, roots, splitting, reverse, and degree
  estimates;
- `RatFunc`, numerator/denominator normalization and the infinity valuation;
- `GaloisField p n`, `GaloisField.card`, finite-field trace, and
  `FiniteField.algebraMap_trace_eq_sum_pow`;
- finite-dimensional linear algebra for a nonzero kernel when the number of
  unknowns exceeds the number of equations;
- factorization of complex polynomials, complex norm, `Real.sqrt`, compactness
  of finite products, and finite-sum norm inequalities.

Not present in Mathlib, and proved below, are the coefficient form of the
Newton--Waring phase, the monic-polynomial Artin L-polynomial, its extension
trace identity, the special Artin--Schreier irreducibility theorem, the
Frobenius-freezing Hasse lemma, the direct-trace Stepanov auxiliary polynomial,
the trace-fiber point count, and the reciprocal-root bound.

## 1. Degree one and the constant term

The nontrivial Stepanov branch begins at degree two.  This is important for
both the arithmetic parameters and the characteristic-two edge case.  If
`deg f=1`, write `f=aX+c` with `a!=0`.  Multiplication by `a`, followed by
translation by `c`, permutes `ZMod p`; hence the sum is the sum of a
nontrivial additive character over the field and is zero.  In particular,
when `p=2`, the hypotheses `0<deg f<p` force `deg f=1`, so the Stepanov
parameter construction is never invoked in characteristic two.

For higher degree the L-polynomial is built from the zero-constant-term
polynomial.  The missing constant is restored by a unit twist, not discarded.

```lean
namespace TranslationalTilings
namespace Stepanov

noncomputable def eraseConstant {k : Type*} [CommRing k] (f : Polynomial k) :
    Polynomial k :=
  f - Polynomial.C (f.coeff 0)

def constantTwist {k : Type*} [CommRing k]
    (psi : AddChar k ℂ) (f : Polynomial k) : ℂ :=
  psi (f.coeff 0)

theorem eraseConstant_coeff_zero {k : Type*} [CommRing k]
    (f : Polynomial k) :
    (eraseConstant f).coeff 0 = 0

theorem eraseConstant_natDegree {k : Type*} [CommRing k]
    (f : Polynomial k) (hpos : 0 < f.natDegree) :
    (eraseConstant f).natDegree = f.natDegree

theorem norm_constantTwist_of_finite
    {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    ‖constantTwist psi f‖ = 1
```

For the norm assertion, additivity gives
`psi(c)*psi(-c)=psi(0)=1`, so a character value is nonzero.  Because the
additive order of `c` is finite, the value is a complex root of unity, hence
has norm one.  If `g=eraseConstant f`, then over an extension of degree `n`,

\[
 \operatorname{Tr}(f(x))=\operatorname{Tr}(g(x))+n f(0),
 \qquad
 S_n(\psi,f)=\psi(f(0))^n S_n(\psi,g).
\]

This identity is formalized after the extension sum is defined in Section 3.

## 2. Newton--Waring phases and the polynomial L-series

Module home:
`TranslationalTilings/NumberTheory/Stepanov/NewtonWaring.lean`.

### 2.1 Monic polynomials and power sums

A monic degree-`n` polynomial is encoded by exactly its `n` lower
coefficients.  Coordinate `i` is the coefficient `u_(i+1)` of
`X^(n-1-i)`.  This representation has a canonical finite type when the base
ring is finite and avoids a proof-bearing subtype in every finite sum.

```lean
structure MonicDegreePolynomial (k : Type*) [CommRing k] (n : ℕ) where
  coeff : Fin n → k
deriving Fintype

namespace MonicDegreePolynomial

noncomputable def toPolynomial {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : Polynomial k :=
  Polynomial.X ^ n +
    ∑ i : Fin n, Polynomial.monomial (n - 1 - i.1) (A.coeff i)

def waringCoeff {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (j : ℕ) : k :=
  if h : 1 ≤ j ∧ j ≤ n then A.coeff ⟨j - 1, by omega⟩ else 0

noncomputable def mul {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    MonicDegreePolynomial k (n + m) :=
  ⟨fun i ↦ (A.toPolynomial * B.toPolynomial).coeff (n + m - 1 - i.1)⟩

theorem toPolynomial_monic {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) : A.toPolynomial.Monic

theorem toPolynomial_natDegree {k : Type*} [CommRing k] [Nontrivial k]
    {n : ℕ} (A : MonicDegreePolynomial k n) :
    A.toPolynomial.natDegree = n

theorem toPolynomial_mul {k : Type*} [CommRing k] {n m : ℕ}
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    (A.mul B).toPolynomial = A.toPolynomial * B.toPolynomial

end MonicDegreePolynomial
```

The descending-coordinate convention is connected literally to Mathlib's
ascending `degreeLTEquiv` by `Fin.rev`.  This adapter is needed before using
Mathlib's normalized factorization; no prose coercion between the coefficient
record and `Polynomial` is allowed.

```lean
def reverseCoordinatesEquiv (k : Type*) (n : ℕ) :
    (Fin n → k) ≃ (Fin n → k) where
  toFun a i := a i.rev
  invFun a i := a i.rev
  left_inv a := by ext i; simp
  right_inv a := by ext i; simp

def MonicDegreePolynomial.coeffEquiv
    (k : Type*) [CommRing k] (n : ℕ) :
    MonicDegreePolynomial k n ≃ (Fin n → k) where
  toFun := MonicDegreePolynomial.coeff
  invFun := MonicDegreePolynomial.mk
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def monicEncodingEquiv
    (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    MonicDegreePolynomial k n ≃
      {P : Polynomial k // P.Monic ∧ P.natDegree = n} :=
  (MonicDegreePolynomial.coeffEquiv k n).trans <|
    (reverseCoordinatesEquiv k n).trans <|
      (Polynomial.degreeLTEquiv k n).symm.toEquiv.trans
        (Polynomial.monicEquivDegreeLT (R := k) n).symm

theorem monicEncodingEquiv_apply
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    (monicEncodingEquiv k n A).1 = A.toPolynomial

noncomputable def MonicDegreePolynomial.ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) : MonicDegreePolynomial k n :=
  (monicEncodingEquiv k n).symm ⟨P, hPmonic, hPdegree⟩

theorem MonicDegreePolynomial.toPolynomial_ofPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (P : Polynomial k) (hPmonic : P.Monic)
    (hPdegree : P.natDegree = n) :
    (MonicDegreePolynomial.ofPolynomial P hPmonic hPdegree).toPolynomial = P

theorem MonicDegreePolynomial.ofPolynomial_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k] {n : ℕ}
    (A : MonicDegreePolynomial k n) :
    MonicDegreePolynomial.ofPolynomial A.toPolynomial
      A.toPolynomial_monic A.toPolynomial_natDegree = A
```

The proof of `monicEncodingEquiv_apply` is the finite reindexing by
`Fin.revPerm`; the two reconstruction theorems are the inverse laws.  At
`n=0`, this identifies the unique coefficient record with the polynomial
`1`, so the coefficient-zero recurrence below has a genuine base case.

For formal variables `u_1,...,u_n`, define the Newton power sum recursively:

\[
 s_0=n,
 \qquad
 s_m=-\left(m u_m+\sum_{1\le j<m}u_j s_{m-j}\right).
\]

The `waringVariable` helper is implementation-internal.  It is zero outside
`1<=j<=n`.

```lean
private noncomputable def waringVariable
    (k : Type*) [CommRing k] (n j : ℕ) : MvPolynomial (Fin n) k :=
  if h : 1 ≤ j ∧ j ≤ n then MvPolynomial.X ⟨j - 1, by omega⟩ else 0

noncomputable def waringPowerSum (k : Type*) [CommRing k] (n m : ℕ) :
    MvPolynomial (Fin n) k :=
  if _hm : m = 0 then MvPolynomial.C (n : k)
  else -((m : MvPolynomial (Fin n) k) * waringVariable k n m +
    ∑ j : Fin (m - 1),
      waringVariable k n (j.1 + 1) *
        waringPowerSum k n (m - (j.1 + 1)))
termination_by m
decreasing_by omega

noncomputable def monicPowerSum {k : Type*} [CommRing k] {n : ℕ}
    (A : MonicDegreePolynomial k n) (m : ℕ) : k :=
  MvPolynomial.eval A.coeff (waringPowerSum k n m)

noncomputable def monicPhase {k : Type*} [CommRing k] {n : ℕ}
    (f : Polynomial k) (A : MonicDegreePolynomial k n) : k :=
  ∑ j ∈ f.support, f.coeff j * monicPowerSum A j

noncomputable def monicWeight {k : Type*} [CommRing k] {n : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) : ℂ :=
  psi (monicPhase f A)

noncomputable def artinCoefficient {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (n : ℕ) : ℂ :=
  ∑ A : MonicDegreePolynomial k n, monicWeight psi f A
```

If the roots of `A` in a splitting field are
`lambda_1,...,lambda_n`, Mathlib's Newton identity is evaluated at that root
tuple.  Induction on `m` identifies `monicPowerSum A m` with
`sum lambda_i^m`.  Summing over the support of `f` then gives

\[
  \operatorname{monicPhase}(f,A)=\sum_i f(\lambda_i).
\]

For multiplicativity, the base is now explicitly a field.  Transport both
monic polynomials along `algebraMap k (AlgebraicClosure k)`;
`IsAlgClosed.splits` makes both mapped polynomials split, and
`(algebraMap k (AlgebraicClosure k)).injective` is the descent map.  Apply
`monicPowerSum_eq_sum_roots` there.  The mapped identity
`MonicDegreePolynomial.toPolynomial_mul`, together with `Polynomial.map_mul`
and `Polynomial.roots_mul` (the mapped monic factors are nonzero), identifies
the root multiset of `A.mul B` with the sum of the root multisets of `A` and
`B`, including multiplicities.  Hence the transported phase of the product
is the sum of the two transported phases.  Injectivity of the algebraic-
closure map descends this phase equality to `k`, and `AddChar.map_add` turns
it into multiplication of weights.  This also proves that the phase
calculation is independent of the chosen splitting field and root ordering.

```lean
theorem monicPowerSum_eq_sum_roots
    {k K : Type*} [Field k] [Field K] [Algebra k K] {n : ℕ}
    (A : MonicDegreePolynomial k n)
    (hA : (A.toPolynomial.map (algebraMap k K)).Splits) (m : ℕ) :
    algebraMap k K (monicPowerSum A m) =
      ((A.toPolynomial.map (algebraMap k K)).roots.map fun x ↦ x ^ m).sum

theorem monicWeight_mul
    {k : Type*} [Field k] {n m : ℕ}
    (psi : AddChar k ℂ) (f : Polynomial k)
    (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
    monicWeight psi f (A.mul B) = monicWeight psi f A * monicWeight psi f B
```

For factorization, forget the degree but retain the proof of monicity.
Normalized factors remain a `Multiset`: repeated irreducible factors are
mathematically essential to the marked-factor recurrence.

```lean
def MonicPolynomial (k : Type*) [CommRing k] :=
  {P : Polynomial k // P.Monic}

namespace MonicPolynomial

noncomputable def encoding
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) :
    MonicDegreePolynomial k P.1.natDegree :=
  (monicEncodingEquiv k P.1.natDegree).symm ⟨P.1, P.2, rfl⟩

theorem encoding_toPolynomial
    {k : Type*} [CommRing k] [Nontrivial k]
    (P : MonicPolynomial k) : P.encoding.toPolynomial = P.1

noncomputable def normalizedIrreducibleFactors
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    Multiset (MonicPolynomial k) := by
  letI := Classical.decEq k
  exact (UniqueFactorizationMonoid.normalizedFactors P.1).attach.map
    fun G ↦
      ⟨G.1,
        ((Polynomial.mem_normalizedFactors_iff P.2.ne_zero).mp G.2).2.1⟩

theorem normalizedIrreducibleFactors_irreducible
    {k : Type*} [Field k] (P : MonicPolynomial k)
    {G : MonicPolynomial k}
    (hG : G ∈ P.normalizedIrreducibleFactors) : Irreducible G.1

theorem normalizedIrreducibleFactors_prod
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1).prod = P.1

theorem normalizedIrreducibleFactors_degree_sum
    {k : Type*} [Field k] (P : MonicPolynomial k) :
    (P.normalizedIrreducibleFactors.map fun G ↦ G.1.natDegree).sum =
      P.1.natDegree

end MonicPolynomial

noncomputable def monicPolynomialWeight
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) : ℂ :=
  monicWeight psi f P.encoding

theorem monicWeight_eq_prod_normalizedIrreducibleFactors
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (P : MonicPolynomial k) :
    monicPolynomialWeight psi f P =
      (P.normalizedIrreducibleFactors.map
        (monicPolynomialWeight psi f)).prod
```

`normalizedIrreducibleFactors_prod` is
`UniqueFactorizationMonoid.prod_normalizedFactors_eq` specialized to a monic
polynomial; the leading unit disappears by
`Polynomial.Monic.normalize_eq_self`.  The degree sum uses
`Polynomial.natDegree_multiset_prod`.  The weight formula is multiset
induction using `monicWeight_mul`; its ambient `k` is already a field here, as
it is in every later Euler-product and finite-field consumer.  For `P=1`,
both products are empty and have value one.

### 2.2 Waring cancellation

Let `d=deg f`, assume `f(0)=0`, and take a monic polynomial of degree
`n>=d`.  Newton's recurrence shows that `s_j` for `j<d` is independent of
`u_d`, whereas

\[
  s_d=-d u_d+Q(u_1,\ldots,u_{d-1}).
\]

No coefficient of `f` above `d` occurs.  Hence the full phase has the affine
form

\[
 \sum_i f(\lambda_i)
   =-d\,\operatorname{lc}(f)\,u_d+Q_f(u_1,\ldots,u_{d-1}).
\]

Because `0<d<p`, both `d` and `leadingCoeff f` are nonzero in `ZMod p`.
Multiplication by their product preserves nontriviality of `psi`.  Summation
over `u_d` is therefore zero by Mathlib's additive-character orthogonality.
All other coordinates are spectators, so the entire degree-`n` coefficient
vanishes.

```lean
theorem monicPhase_affine_last
    {k : Type*} [CommRing k] {d : ℕ}
    (f : Polynomial k) (hd : f.natDegree = d) (hdpos : 0 < d)
    (n : ℕ) (hdn : d ≤ n) :
    ∀ A : MonicDegreePolynomial k n, ∀ u : k,
      monicPhase f ⟨Function.update A.coeff ⟨d - 1, by omega⟩ u⟩ =
        -(d : k) * f.leadingCoeff * u +
          monicPhase f
            ⟨Function.update A.coeff ⟨d - 1, by omega⟩ 0⟩

theorem artinCoefficient_eq_zero_of_degree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : f.natDegree ≤ n) :
    artinCoefficient psi f n = 0
```

### 2.3 The L-polynomial and extension trace identity

Define

\[
  T_n=\sum_{A\ \text{ monic},\ \deg A=n}\lambda_f(A),
  \qquad
  L_{\psi,f}(z)=\sum_{0\le n<d}T_nz^n.
\]

For `d>0`, the preceding cancellation proves that this truncation equals the
full formal series.  The Lean definition uses `range (max 1 d)` so that the
unused constant-polynomial case is definitionally the polynomial `1`; this
makes the unconditional constant-coefficient and degree lemmas true.  In all
cases its constant coefficient is one and its degree is at most `d-1`.

```lean
noncomputable def artinLPolynomial {k : Type*} [CommRing k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (max 1 f.natDegree),
    Polynomial.monomial n (artinCoefficient psi f n)

noncomputable def reciprocalRoots
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) : Multiset ℂ :=
  (artinLPolynomial psi f).reverse.roots

theorem artinLPolynomial_coeff_zero
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).coeff 0 = 1

theorem artinLPolynomial_constant_regression
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (c : ZMod p) :
    artinLPolynomial psi (Polynomial.C c) = 1

theorem artinLPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (artinLPolynomial psi f).natDegree ≤ f.natDegree - 1

theorem reciprocalRoots_card_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    (reciprocalRoots psi f).card ≤ f.natDegree - 1
```

The Euler-product calculation is made finite at every cutoff.  The marked
factor sum keeps the degree and multiplicity of the marked irreducible; the
geometric factor is truncated only after the largest exponent which can
affect a coefficient at or below the cutoff.

```lean
noncomputable def markedFactorSum
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (m : ℕ) : ℂ := by
  classical
  exact ∑ r ∈ Finset.Icc 1 m with r ∣ m,
    ∑ G : MonicDegreePolynomial k r,
      if Irreducible G.toPolynomial then
        (r : ℂ) * monicWeight psi f G ^ (m / r)
      else 0

noncomputable def truncatedEulerFactor
    {k : Type*} [Field k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff r : ℕ) (G : MonicDegreePolynomial k r) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (cutoff / r + 1),
    Polynomial.monomial (a * r) (monicWeight psi f G ^ a)

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

noncomputable def markedFactorPolynomial
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    (cutoff : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.Icc 1 cutoff,
    Polynomial.monomial j (markedFactorSum psi f j)

theorem truncatedEulerProduct_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (truncatedEulerProduct psi f cutoff).coeff n =
      artinCoefficient psi f n

theorem truncatedEulerProduct_logDerivative_coeff
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) (cutoff : ℕ)
    {n : ℕ} (hn : n ≤ cutoff) :
    (Polynomial.X *
      (truncatedEulerProduct psi f cutoff).derivative).coeff n =
    (truncatedEulerProduct psi f cutoff *
      markedFactorPolynomial psi f cutoff).coeff n

theorem artinCoefficient_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    artinCoefficient psi f 0 = 1

theorem truncatedEulerProduct_zero
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k) :
    truncatedEulerProduct psi f 0 = 1

theorem artinCoefficient_markedFactor_recurrence
    {k : Type*} [Field k] [Fintype k]
    (psi : AddChar k ℂ) (f : Polynomial k)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        markedFactorSum psi f j * artinCoefficient psi f (m - j)
```

For `truncatedEulerProduct_coeff`, expanding the finite product selects a
multiplicity `a_G` for each normalized monic irreducible `G`.  The exact
product and degree-sum theorems give a bijection between selections of total
degree `n` and monic degree-`n` polynomials; the weight-product theorem matches
their coefficients.  When `n≤cutoff`, no omitted degree or multiplicity can
contribute.  The logarithmic derivative theorem is proved factor by factor:

\[
 X\frac d{dX}\sum_{a=0}^{M/r}w^aX^{ar}
 =\left(\sum_{a=0}^{M/r}w^aX^{ar}\right)
   \left(\sum_{b=1}^{M/r}r w^bX^{br}\right)
 \pmod {X^{M+1}}.
\]

Use `Polynomial.derivative_prod_finset`, `coeff_derivative`, `coeff_X_mul`,
and `coeff_mul`, then group `j=b*r`.  At cutoff `m` this yields the displayed
marked-factor recurrence with its positive sign.  The cutoff-zero theorem and
`artinCoefficient_zero` are explicit regressions: the empty product and the
unique degree-zero monic both have weight one.

For `n!=0`, Mathlib supplies the finite field `GaloisField p n`, its
cardinality `p^n`, and its trace to `ZMod p`.

```lean
noncomputable def traceLiftAddChar
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (n : ℕ) :
    AddChar (GaloisField p n) ℂ :=
  psi.compAddMonoidHom
    (Algebra.trace (ZMod p) (GaloisField p n)).toAddMonoidHom

noncomputable def extensionExponentialSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact ∑ x : GaloisField p n,
    traceLiftAddChar psi n
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x)

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
```

The degree-one bridge is literal, not a type-level identification.  Put
`e=GaloisField.equivZmodP p`.  The equivalence `e.toEquiv` reindexes the
finite sum without changing its multiplicities.  For an extension element
`y`, `Algebra.trace_eq_of_algEquiv e y` identifies its trace with the trace of
`e y` in the algebra `ZMod p` over itself; `Algebra.trace_self_apply` reduces
the latter to `e y`.  Finally, `Polynomial.aeval_algHom_apply` says that `e`
transports evaluation of `f` at `x` to evaluation of `f` at `e x` (and
`Polynomial.aeval_def` identifies this with the displayed `eval₂`).  Thus the
summands agree pointwise under the reindexing, proving
`extensionExponentialSum_one_eq_primeSum`.

The remaining identification is finite-field orbit accounting.  A minpoly
fiber is a finite set of extension elements; it is empty unless the
irreducible degree divides the extension degree, and otherwise it is exactly
one Galois orbit with the irreducible degree as cardinality.

```lean
noncomputable def minpolyFiber
    {p : ℕ} [Fact p.Prime] (m : ℕ)
    (G : Polynomial (ZMod p)) : Finset (GaloisField p m) := by
  letI := Fintype.ofFinite (GaloisField p m)
  classical
  exact Finset.univ.filter fun x ↦ minpoly (ZMod p) x = G

noncomputable def minpolyEncoding
    {p m : ℕ} [Fact p.Prime] (x : GaloisField p m) :
    MonicDegreePolynomial (ZMod p)
      (minpoly (ZMod p) x).natDegree :=
  (monicEncodingEquiv (ZMod p) (minpoly (ZMod p) x).natDegree).symm
    ⟨minpoly (ZMod p) x,
      minpoly.monic (Algebra.IsIntegral.isIntegral x), rfl⟩

theorem minpolyFiber_nonempty_iff_natDegree_dvd
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).Nonempty ↔ G.natDegree ∣ m

theorem card_minpolyFiber
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (G : Polynomial (ZMod p))
    (hGmonic : G.Monic) (hGirr : Irreducible G) :
    (minpolyFiber m G).card =
      if G.natDegree ∣ m then G.natDegree else 0

theorem minpolyFiber_eq_galoisOrbit
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (x : GaloisField p m) :
    ↑(minpolyFiber m (minpoly (ZMod p) x)) =
      MulAction.orbit
        (GaloisField p m ≃ₐ[ZMod p] GaloisField p m) x

theorem minpolyPhase_eq_sum_frobenius
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    algebraMap (ZMod p) (GaloisField p m)
        (monicPhase f (minpolyEncoding x)) =
      ∑ i ∈ Finset.range (minpoly (ZMod p) x).natDegree,
        f.eval₂ (algebraMap (ZMod p) (GaloisField p m))
          (x ^ (p ^ i))

theorem traceLiftAddChar_eq_minpolyWeight_pow
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ)
    (f : Polynomial (ZMod p)) (x : GaloisField p m) :
    traceLiftAddChar psi m
        (f.eval₂ (algebraMap (ZMod p) (GaloisField p m)) x) =
      monicWeight psi f (minpolyEncoding x) ^
        (m / (minpoly (ZMod p) x).natDegree)

theorem markedFactorSum_eq_extensionExponentialSum
    {p m : ℕ} [Fact p.Prime] (hm : m ≠ 0)
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p)) :
    markedFactorSum psi f m = extensionExponentialSum psi f m

theorem artinCoefficient_extension_recurrence
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * artinCoefficient psi f m =
      ∑ j ∈ Finset.Icc 1 m,
        extensionExponentialSum psi f j *
          artinCoefficient psi f (m - j)
```

For the fiber criterion, rewrite `Nat.card (ZMod p)=p` and apply
`Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`.  The polynomial
`X^(p^m)-X` splits in `GaloisField p m`; a divisor therefore has a root there,
whose minpoly is `G` by irreducibility and monicity.  Conversely,
`minpoly.degree_dvd` and `GaloisField.finrank p hm` force the degree divisor.
Finite fields are perfect, so an irreducible is separable; its root set has
exactly `natDegree G` elements.  `Normal.minpoly_eq_iff_mem_orbit` gives the
literal orbit equality.

For the phase theorem, the minpoly roots are the Frobenius orbit
`x,x^p,...,x^(p^(r-1))`; combine that fact with
`monicPowerSum_eq_sum_roots`.  The trace formula
`FiniteField.algebraMap_trace_eq_sum_pow` and `r∣m` split the `m` Frobenius
terms into `m/r` identical orbit blocks.  Applying the character turns this
repeated addition into a power by `AddChar.map_nsmul_eq_pow`.  Finally,
partition extension elements by `minpoly` and use the exact fiber cardinality:
this proves `markedFactorSum_eq_extensionExponentialSum`, including every
factor multiplicity, and hence the extension recurrence.

Independently, factor a polynomial with constant coefficient one using the
roots of its reverse.  This gives the second recurrence with an explicit
negative sign.

```lean
noncomputable def rootFactorPolynomial
    (roots : Multiset ℂ) : Polynomial ℂ :=
  (roots.map fun omega ↦
    1 - Polynomial.C omega * Polynomial.X).prod

def rootPowerSum (roots : Multiset ℂ) (m : ℕ) : ℂ :=
  (roots.map fun omega ↦ omega ^ m).sum

noncomputable def reverseRootPowerSum
    (L : Polynomial ℂ) (m : ℕ) : ℂ :=
  rootPowerSum L.reverse.roots m

theorem rootFactorPolynomial_newton_recurrence
    (roots : Multiset ℂ) {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * (rootFactorPolynomial roots).coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        rootPowerSum roots j *
          (rootFactorPolynomial roots).coeff (m - j)

theorem eq_rootFactorPolynomial_reverse_roots
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1) :
    L = rootFactorPolynomial L.reverse.roots

theorem reverseRoot_newton_recurrence
    (L : Polynomial ℂ) (hL0 : L.coeff 0 = 1)
    {m : ℕ} (hm : 0 < m) :
    (m : ℂ) * L.coeff m =
      -∑ j ∈ Finset.Icc 1 m,
        reverseRootPowerSum L j * L.coeff (m - j)

theorem artinLPolynomial_coeff_eq_artinCoefficient
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    (m : ℕ) :
    (artinLPolynomial psi f).coeff m = artinCoefficient psi f m

theorem neg_eq_of_convolution_recurrences
    (T S P : ℕ → ℂ) (hT0 : T 0 = 1)
    (hS : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        ∑ j ∈ Finset.Icc 1 m, S j * T (m - j))
    (hP : ∀ {m : ℕ}, 0 < m →
      (m : ℂ) * T m =
        -∑ j ∈ Finset.Icc 1 m, P j * T (m - j)) :
    ∀ {m : ℕ}, 0 < m → S m = -P m

theorem extensionExponentialSum_eq_neg_reverseRootPowerSum
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m =
      -reverseRootPowerSum (artinLPolynomial psi f) m

theorem extensionExponentialSum_eq_zero_of_natDegree_eq_one
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hdegree : f.natDegree = 1) {m : ℕ} (hm : m ≠ 0) :
    extensionExponentialSum psi f m = 0

theorem artinLPolynomial_trace_identity
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p)
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      -((reciprocalRoots psi f).map fun omega ↦ omega ^ n).sum

theorem extensionExponentialSum_eraseConstant
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (f : Polynomial (ZMod p))
    {n : ℕ} (hn : n ≠ 0) :
    extensionExponentialSum psi f n =
      constantTwist psi f ^ n *
        extensionExponentialSum psi (eraseConstant f) n
```

The root recurrence is a multiset induction: adjoining `a` changes
`T_m` to `T_m-a*T_(m-1)` and `P_j` to `P_j+a^j`; the new terms telescope.
For the factorization, `L.coeff 0=1` makes `L.reverse` monic.  Over `ℂ`, its
root multiset has full degree, so
`Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq`, followed by
reversal, gives `L=prod (1-C omega*X)`.

The coefficient bridge uses Waring cancellation above the truncation and the
definition below it, so both recurrences use the same `T_m`.  In
`neg_eq_of_convolution_recurrences`, strong induction kills every `j<m` term;
the remaining `j=m` term is `(S_m+P_m)*T_0`, and `T_0=1`.  This proves the
power-sum identity without division.  The explicit degree-one regression has
`L=1`, empty reverse roots, and zero positive extension sums.  No orbit theorem
is stated at `m=0`, where the pinned `GaloisField.finrank` theorem does not
apply.  No convergence, infinite product, or analytic interchange is used.

## 3. The Artin--Schreier irreducibility prerequisite

Module home:
`TranslationalTilings/NumberTheory/Stepanov/ArtinSchreier.lean`.

```lean
noncomputable def artinSchreierPolynomial
    {K : Type*} [Field K] (p : ℕ) (c : K) : Polynomial K :=
  Polynomial.X ^ p - Polynomial.X - Polynomial.C c

theorem artinSchreierPolynomial_monic
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Monic

theorem artinSchreierPolynomial_natDegree
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).natDegree = p

theorem artinSchreierPolynomial_derivative
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).derivative = -1

theorem artinSchreierPolynomial_separable
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).Separable

noncomputable def artinSchreierSplittingRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : (artinSchreierPolynomial p c).SplittingField :=
  Polynomial.rootOfSplits
    (Polynomial.SplittingField.splits (artinSchreierPolynomial p c))
    (Polynomial.degree_ne_of_natDegree_ne (by
      rw [Polynomial.natDegree_map, artinSchreierPolynomial_natDegree c]
      exact (Fact.out : p.Prime).ne_zero))

theorem artinSchreierSplittingRoot_isRoot
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ((artinSchreierPolynomial p c).map
      (algebraMap K (artinSchreierPolynomial p c).SplittingField)).IsRoot
        (artinSchreierSplittingRoot c)

theorem artinSchreier_root_sub_root_mem_bot
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]
    {c : K} {x y : L}
    (hx : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) x = 0)
    (hy : (artinSchreierPolynomial p c).eval₂ (algebraMap K L) y = 0) :
    x - y ∈ (⊥ : Subfield L)

theorem artinSchreier_splittingField_adjoin_root_eq_top
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    IntermediateField.adjoin K {artinSchreierSplittingRoot c} =
      (⊤ : IntermediateField K
        (artinSchreierPolynomial p c).SplittingField)

theorem exists_artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ∃ phi : Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
        (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField),
      (∀ sigma,
        (phi sigma : (artinSchreierPolynomial p c).SplittingField) =
          sigma (artinSchreierSplittingRoot c) -
            artinSchreierSplittingRoot c) ∧
      Function.Injective phi

noncomputable def artinSchreierAutShift
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Additive (Polynomial.Gal (artinSchreierPolynomial p c)) →+
      (⊥ : Subfield (artinSchreierPolynomial p c).SplittingField) :=
  Classical.choose (exists_artinSchreierAutShift c)

theorem artinSchreierAutShift_apply
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K)
    (sigma : Additive (Polynomial.Gal (artinSchreierPolynomial p c))) :
    (artinSchreierAutShift c sigma :
      (artinSchreierPolynomial p c).SplittingField) =
        sigma (artinSchreierSplittingRoot c) -
          artinSchreierSplittingRoot c

theorem artinSchreierAutShift_injective
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) : Function.Injective (artinSchreierAutShift c)

theorem artinSchreier_minpoly_natDegree_dvd_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree ∣ p

theorem artinSchreier_minpoly_natDegree_eq_one_or_prime
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    (minpoly K (artinSchreierSplittingRoot c)).natDegree = 1 ∨
      (minpoly K (artinSchreierSplittingRoot c)).natDegree = p

theorem artinSchreierPolynomial_irreducible_iff_no_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    Irreducible (artinSchreierPolynomial p c) ↔
      ¬ ∃ x : K, x ^ p - x = c

theorem not_artinSchreierPolynomial_irreducible_iff_root
    {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (c : K) :
    ¬ Irreducible (artinSchreierPolynomial p c) ↔
      ∃ x : K, x ^ p - x = c

noncomputable def artinSchreierRatFuncPolynomial
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p)) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f)

theorem ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap
    {p : ℕ} [Fact p.Prime]
    (h : RatFunc (ZMod p)) (g : Polynomial (ZMod p))
    (heq : h ^ p - h =
      algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) g) :
    ∃ A : Polynomial (ZMod p),
      h = algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) A

theorem polynomial_pow_sub_self_natDegree
    {p : ℕ} [Fact p.Prime]
    (A : Polynomial (ZMod p)) (hA : 0 < A.natDegree) :
    (A ^ p - A).natDegree = p * A.natDegree

theorem no_ratFunc_artinSchreier_root
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ¬ ∃ h : RatFunc (ZMod p),
      h ^ p - h =
        -algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) f

theorem artinSchreierRatFuncPolynomial_irreducible
    {p : ℕ} [Fact p.Prime] (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (artinSchreierRatFuncPolynomial f)
```

Here is the complete algebraic proof boundary.

The derivative is `-1`, so the polynomial is separable.  If `alpha` is the
chosen splitting-field root, subtracting the equations for any two roots
shows their difference satisfies `a^p=a`; `Subfield.mem_bot_iff_pow_eq_self`
places it in the prime subfield.  Hence every root is `alpha+a` and the one
root generates the full splitting field.

For an automorphism `sigma`, the difference `sigma(alpha)-alpha` lies in that
prime subfield.  It is fixed by every other automorphism, so expanding
`(sigma*tau)(alpha)-alpha` proves additivity of the shift map; zero shift fixes
the generator and is therefore the identity.  Separability makes the
splitting field Galois.  The injective shift identifies its automorphism group
with an additive subgroup of the prime subfield, whose cardinal divides `p`.
Use `IsGalois.card_aut_eq_finrank`, the adjoin theorem, and
`IntermediateField.adjoin.finrank` to identify this cardinal with the
minpoly degree.  Primality gives degree `1` or `p`.  Degree one puts the root
in the base field; degree `p`, plus `minpoly.dvd` and monicity, identifies the
minpoly with the Artin--Schreier polynomial.  This proves the two root
criteria.  It never multiplies the translations of a proper factor: over
`F_5`, the translates of `T(T-1)` multiply to `(T^5-T)^2`, not `T^5-T`.

For the rational-function specialization write `h=A/B` with Mathlib's
normalized coprime numerator and monic denominator.  Clearing denominators in
`h^p-h=g` gives

\[
 A^p-A B^{p-1}=gB^p.
\]

If a monic irreducible `q` divides a nonunit `B`, reduction modulo `q` gives
`q∣A^p`, hence `q∣A`, contradicting `RatFunc.isCoprime_num_denom`.  Thus `B`
is the monic unit `1`, proving
`ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap`.  A nonconstant
polynomial `A` has `deg(A^p-A)=p*deg A`; a constant gives a constant result.
Neither can equal `-f` with `0<deg f<p`.  The generic root criterion now gives
`artinSchreierRatFuncPolynomial_irreducible`.  The infinity valuation is only
a degree cross-check; no curve or absolute-irreducibility theorem is used.

## 4. Hasse derivatives, multiplicity, and Frobenius freezing

Module home:
`TranslationalTilings/NumberTheory/Stepanov/HasseMultiplicity.lean`.

```lean
def VanishesToOrderAtLeast {K : Type*} [CommRing K]
    (P : Polynomial K) (a : K) (R : ℕ) : Prop :=
  ∀ r < R, (P.hasseDeriv r).eval a = 0

theorem vanishesToOrderAtLeast_iff_rootMultiplicity
    {K : Type*} [Field K] {P : Polynomial K}
    (hP : P ≠ 0) (a : K) (R : ℕ) :
    VanishesToOrderAtLeast P a R ↔ R ≤ P.rootMultiplicity a

theorem card_mul_le_natDegree_of_vanishes
    {K : Type*} [Field K] {P : Polynomial K} (hP : P ≠ 0)
    (A : Finset K) {R : ℕ}
    (hvanish : ∀ a ∈ A, VanishesToOrderAtLeast P a R) :
    A.card * R ≤ P.natDegree

theorem hasseDeriv_eval_frobenius
    {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (Q : Polynomial (Polynomial K)) {m r : ℕ} (hr : r < p ^ m) :
    (Q.eval (Polynomial.X ^ (p ^ m))).hasseDeriv r =
      (Q.sum fun i a ↦
        Polynomial.C (a.hasseDeriv r) * Polynomial.X ^ i).eval
          (Polynomial.X ^ (p ^ m))
```

The first equivalence is Taylor's theorem: the coefficient of `X^r` in the
Taylor expansion at `a` is `(hasseDeriv r P).eval a`.  Vanishing of the first
`R` coefficients is divisibility by `(X-C a)^R`, which is precisely the
root-multiplicity inequality.  Multiplying these pairwise coprime powers for
distinct `a` proves the cardinality-degree bound.

For Frobenius freezing, expand the Hasse derivative of every monomial.  In
characteristic `p`, `choose (j*p^m) r` is zero for `0<r<p^m`; equivalently
`D^r(Q(X,X^(p^m)))` differentiates only the coefficient-polynomial variable.
The `r=0` case is immediate.  This is the precise replacement for the
informal instruction to treat a Frobenius power as a constant.

## 5. The direct trace-fiber Stepanov construction

Module home:
`TranslationalTilings/NumberTheory/Stepanov/AdditivePointCount.lean`.

For `n` large, put

\[
 u=\lfloor n/2\rfloor,\quad
 S=p^{n-2},\quad
 K=\left\lfloor\frac{p^{u-2}}{2d}\right\rfloor,\quad
 R=pK.
\]

The factor `2` is deliberate.  It creates strict slack in the direct
trace-only linear system after the norm/Kummer variable from
Cochrane--Pinner is removed.

```lean
structure AdditiveStepanovParameters (p d n : ℕ) where
  u : ℕ
  S : ℕ
  K : ℕ
  R : ℕ
  u_eq : u = n / 2
  S_eq : S = p ^ (n - 2)
  K_eq : K = p ^ (u - 2) / (2 * d)
  K_pos : 0 < K
  two_mul_d_le_K : 2 * d ≤ K
  R_eq : R = p * K
  R_lt_frobenius : R < p ^ u
  dimension_ok :
    R * (S + d * (p - 1) * p ^ (u - 1) + K) <
      p * S * (K + 1)
  norm_degree_ok :
    p * S + d * p ^ u * (p - 1) < p ^ n

theorem exists_additive_stepanov_parameters
    (p d : ℕ) (hp : p.Prime) (hd : 2 ≤ d) (hdp : d < p) :
    ∃ N, ∀ n ≥ N, Nonempty (AdditiveStepanovParameters p d n)

theorem AdditiveStepanovParameters.S_pos
    {p d n : ℕ} (par : AdditiveStepanovParameters p d n) :
    0 < par.S

theorem AdditiveStepanovParameters.n_pos
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : 0 < n
```

This theorem is a displayed prerequisite because the direct specialization's
variable count is tight enough that it must not be hidden in prose.  Its proof
chooses `N` so that `u>=3`, `p^(u-2)>=4*d^2`, and `p^u` dominates
`d*(p-1)`.  Then `K>=2d`, so `R>0`.  The case `p=2` cannot enter because
`2<=d<p`; it was already discharged by the degree-one argument.  Both
`n=2u` and `n=2u+1` are checked.

After substituting `R=pK`, the common term `p*K*S` cancels from the two sides
of `dimension_ok`.  It remains to prove

\[
 Kd(p-1)p^{u-1}+K^2<S=p^{n-2}.
\]

Using `K<=p^(u-2)/(2d)`, for even `n=2u` the first term is at most
`((p-1)/(2p))*S`, strictly less than `S/2`, and the square term is at most
`S/(4d^2p^2)`.  For odd `n=2u+1` there is one extra factor of `p` of slack.
The same parity split proves `R<p^u` and `norm_degree_ok`.  Thus the
`p*S*(K+1)` coefficient variables strictly outnumber all equations.
The theorem `S_pos` also follows directly from `dimension_ok`, whose right
side must be positive.  For `n_pos`, primality and `K_pos` make `R=p*K≥2`;
if `n=0`, then `u=0` and `R_lt_frobenius` would say `R<p^0=1`.

### 5.1 The auxiliary polynomial

Define the upper half of the trace polynomial

\[
 \Phi_{f,n,u}(X)=\sum_{t=u}^{n-1}f(X)^{p^t}.
\]

```lean
noncomputable def upperTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.Ico u n, f ^ (p ^ t)

structure AdditiveAuxiliaryCoefficients {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (k : Type*) [Field k] where
  coeff : Fin p → Fin (par.K + 1) → Polynomial k
  degree_lt : ∀ i j, (coeff i j).natDegree < par.S

def AdditiveAuxiliaryCoefficients.Nonzero
    {p d n : ℕ} {par : AdditiveStepanovParameters p d n}
    {k : Type*} [Field k]
    (e : AdditiveAuxiliaryCoefficients par k) : Prop :=
  ∃ i j, e.coeff i j ≠ 0

noncomputable def additiveAuxiliaryPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p))
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    e.coeff i j * upperTracePolynomial f n par.u ^ i.1 *
      Polynomial.X ^ (p ^ n * j.1)
```

Rank--nullity is not applied to the proof-bearing coefficient package.  The
literal source and target vector spaces, coefficient decoder, reduced Hasse
polynomial, and constraint map are as follows.

```lean
abbrev AdditiveCoeffVector {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin p → Fin (par.K + 1) → Fin par.S → ZMod p

def additiveConstraintDegree {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) : ℕ :=
  par.S + d * (p - 1) * p ^ (par.u - 1) + par.K

abbrev AdditiveConstraintTarget {p d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :=
  Fin par.R → Fin (additiveConstraintDegree par) → ZMod p

noncomputable def coeffPolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) : Polynomial (ZMod p) :=
  ∑ s : Fin par.S,
    Polynomial.C (v i j s) * Polynomial.X ^ s.1

theorem coeffPolynomial_coeff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) (s : Fin par.S) :
    (coeffPolynomial v i j).coeff s.1 = v i j s

theorem coeffPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) (i : Fin p)
    (j : Fin (par.K + 1)) :
    (coeffPolynomial v i j).natDegree < par.S

noncomputable def coeffVectorToCoefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    AdditiveAuxiliaryCoefficients par (ZMod p) where
  coeff := coeffPolynomial v
  degree_lt := coeffPolynomial_natDegree_lt v

noncomputable def coeffVectorToAuxiliaryFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v : AdditiveCoeffVector par) :
    Polynomial (ZMod p) :=
  additiveAuxiliaryPolynomial par f (coeffVectorToCoefficients v)

theorem coeffVectorToAuxiliaryFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (v w : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (v + w) =
      coeffVectorToAuxiliaryFun par f v +
        coeffVectorToAuxiliaryFun par f w

theorem coeffVectorToAuxiliaryFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (c : ZMod p)
    (v : AdditiveCoeffVector par) :
    coeffVectorToAuxiliaryFun par f (c • v) =
      c • coeffVectorToAuxiliaryFun par f v

noncomputable def coeffVectorToAuxiliary
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := coeffVectorToAuxiliaryFun par f
  map_add' := coeffVectorToAuxiliaryFun_add par f
  map_smul' := coeffVectorToAuxiliaryFun_smul par f

noncomputable def lowerTracePolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) : Polynomial (ZMod p) :=
  ∑ t ∈ Finset.range u, f ^ (p ^ t)

noncomputable def reducedHassePolynomial
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v : AdditiveCoeffVector par) : Polynomial (ZMod p) :=
  ∑ i : Fin p, ∑ j : Fin (par.K + 1),
    (coeffPolynomial v i j).hasseDeriv r *
      (Polynomial.C b - lowerTracePolynomial f par.u) ^ i.1 *
        Polynomial.X ^ j.1

theorem reducedHassePolynomial_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (v w : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (v + w) =
      reducedHassePolynomial par f b r v +
        reducedHassePolynomial par f b r w

theorem reducedHassePolynomial_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    reducedHassePolynomial par f b r (c • v) =
      c • reducedHassePolynomial par f b r v

noncomputable def reducedHasseLinearMap
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) (r : ℕ) :
    AdditiveCoeffVector par →ₗ[ZMod p] Polynomial (ZMod p) where
  toFun := reducedHassePolynomial par f b r
  map_add' := reducedHassePolynomial_add par f b r
  map_smul' := reducedHassePolynomial_smul par f b r

noncomputable def additiveConstraintFun
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) : AdditiveConstraintTarget par :=
  fun r q ↦ (reducedHassePolynomial par f b r.1 v).coeff q.1

theorem additiveConstraintFun_add
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v w : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (v + w) =
      additiveConstraintFun par f b v +
        additiveConstraintFun par f b w

theorem additiveConstraintFun_smul
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (c : ZMod p) (v : AdditiveCoeffVector par) :
    additiveConstraintFun par f b (c • v) =
      c • additiveConstraintFun par f b v

noncomputable def additiveConstraint
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    AdditiveCoeffVector par →ₗ[ZMod p] AdditiveConstraintTarget par where
  toFun := additiveConstraintFun par f b
  map_add' := additiveConstraintFun_add par f b
  map_smul' := additiveConstraintFun_smul par f b
```

The displayed additivity and scalar lemmas are direct finite-sum
distributivity facts; they are the proof fields of the three literal linear
maps.  The substantive evaluation and rank interfaces are:

```lean
theorem lowerTracePolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d : ℕ}
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (u : ℕ) :
    (lowerTracePolynomial f u).natDegree ≤ d * p ^ (u - 1)

theorem reducedHassePolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (r : ℕ) (v : AdditiveCoeffVector par) :
    (reducedHassePolynomial par f b r v).natDegree <
      additiveConstraintDegree par

theorem upperTracePolynomial_eval_eq_of_trace_eq
    {p : ℕ} [Fact p.Prime] {n u : ℕ}
    (f : Polynomial (ZMod p)) (hn : n ≠ 0) (hu : u ≤ n)
    (b : ZMod p) (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (upperTracePolynomial f n u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      (Polynomial.C b - lowerTracePolynomial f u).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x

theorem reducedHassePolynomial_eval₂_eq_hasseDeriv_eval
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p)
    (v : AdditiveCoeffVector par) (r : ℕ) (hr : r < par.R)
    (x : GaloisField p n)
    (hx : Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b) :
    (reducedHassePolynomial par f b r v).eval₂
        (algebraMap (ZMod p) (GaloisField p n)) x =
      Polynomial.eval x
        ((((coeffVectorToAuxiliary par f) v).map
          (algebraMap (ZMod p) (GaloisField p n))).hasseDeriv r)

theorem additiveCoeffVector_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveCoeffVector par) =
      p * par.S * (par.K + 1)

theorem additiveConstraintTarget_finrank
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n) :
    Module.finrank (ZMod p) (AdditiveConstraintTarget par) =
      par.R * additiveConstraintDegree par

theorem exists_nonzero_mem_additiveConstraint_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (b : ZMod p) :
    ∃ v : AdditiveCoeffVector par,
      v ≠ 0 ∧ v ∈ LinearMap.ker (additiveConstraint par f b)

theorem reducedHassePolynomial_eq_zero_of_mem_ker
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) (v : AdditiveCoeffVector par)
    (hv : v ∈ LinearMap.ker (additiveConstraint par f b))
    (r : Fin par.R) :
    reducedHassePolynomial par f b r.1 v = 0

theorem coeffVectorToCoefficients_nonzero_iff
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (v : AdditiveCoeffVector par) :
    (coeffVectorToCoefficients v).Nonzero ↔ v ≠ 0

theorem exists_additive_stepanov_coefficients
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (b : ZMod p) :
    ∃ e : AdditiveAuxiliaryCoefficients par (ZMod p), e.Nonzero ∧
      ∀ x : GaloisField p n,
        Algebra.trace (ZMod p) (GaloisField p n)
            (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b →
          VanishesToOrderAtLeast
            ((additiveAuxiliaryPolynomial par f e).map
              (algebraMap (ZMod p) (GaloisField p n))) x par.R
```

This source has exactly `p*S*(K+1)` scalar coordinates.  On a point `x` in
`GaloisField p n`, `x^(p^n)=x`.  If `Tr(f(x))=b`, then

\[
 \Phi(x)=b-\sum_{t=0}^{u-1}f(x)^{p^t},
\]

whose right-hand side is the value of a polynomial of degree at most
`d*p^(u-1)`.  For `r<R<p^u`, Frobenius freezing shows that the `r`th Hasse
derivative of the auxiliary reduces on the fiber to a polynomial of degree
strictly below

\[
 S+d(p-1)p^{u-1}+K.
\]

The upper/lower trace theorem deliberately requires `hn : n≠0` and
`hu:u≤n`.  The pinned trace-as-Frobenius-sum theorem is unavailable at `n=0`,
and the assertion would in fact be false there: for `f=1,b=1`, the trace
hypothesis can hold while both polynomial sums are empty.  The caller passes
`par.n_pos.ne'`; `par.u_eq` gives `u≤n`.  In the reduced-Hasse proof,
`r<R<p^u` freezes every upper-trace Frobenius factor, and `u≤n` also freezes
`X^(p^n*j)`.  This is the exact use of `R_lt_frobenius`.

Setting every coefficient below `D=additiveConstraintDegree par` to zero
gives exactly the displayed target Pi space.  Rewrite the two finranks using
`Module.finrank_fintype_fun_eq_card`; `dimension_ok` and
`LinearMap.ker_ne_bot_of_finrank_lt` give a nonzero kernel, and
`Submodule.exists_mem_ne_zero_of_ne_bot` selects its vector.  The strict
degree bound turns its first `D` zero coefficients into the zero reduced
polynomial.  The evaluation theorem then supplies every Hasse vanishing, and
the decoder coefficient theorem makes the packaged family nonzero.

### 5.2 Nonzero auxiliary: the exact norm descent

It is invalid to call the first translated product a field norm:
`Phi=sum_(t=u)^(n-1)f^(p^t)` already lies in `F_p(X)`.  The proof first needs
the fixed ring of literal translations in an outer variable `T`.

```lean
noncomputable def polynomialTranslate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (beta : ZMod p) :
    Polynomial (Polynomial (ZMod p)) :=
  P.comp (Polynomial.X + Polynomial.C (Polynomial.C beta))

noncomputable def translationProduct
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  ∏ beta : ZMod p, polynomialTranslate P beta

theorem translationProduct_translate
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (gamma : ZMod p) :
    polynomialTranslate (translationProduct P) gamma = translationProduct P

theorem exists_translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    ∃ Q : Polynomial (Polynomial (ZMod p)),
      translationProduct P =
          Q.comp (Polynomial.X ^ p - Polynomial.X) ∧
        Q.natDegree ≤ p - 1

noncomputable def translationProductQuotient
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) :
    Polynomial (Polynomial (ZMod p)) :=
  if hP : P.natDegree < p then
    Classical.choose (exists_translationProductQuotient P hP)
  else 0

theorem translationProductQuotient_spec
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p) :
    translationProduct P =
        (translationProductQuotient P).comp
          (Polynomial.X ^ p - Polynomial.X) ∧
      (translationProductQuotient P).natDegree ≤ p - 1

theorem translationProductQuotient_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (P : Polynomial (Polynomial (ZMod p))) (hP : P.natDegree < p)
    {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) (a : ℕ) :
    ((translationProductQuotient P).coeff a).natDegree < p * S
```

Translation invariance is the finite reindexing `beta↦beta+gamma`.  The
fixed-ring theorem is proved by outer-degree induction.  An invariant's
leading outer exponent is divisible by `p`; subtract its leading coefficient
times `(T^p-T)^a`, strictly lower the outer degree, and recurse.  The product
has outer degree at most `p*(p-1)`, so the quotient degree is at most `p-1`.
Each product coefficient uses `p` inner coefficient polynomials of degree
`<S`; the same induction never increases that filtration and gives the
strict `<p*S` bound.  This theorem is new project algebra, not a hidden
Mathlib invariant-ring result.

Substitute the zero-block Artin--Schreier value into the invariant quotient.

```lean
noncomputable def zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p))) : Polynomial (ZMod p) :=
  (translationProductQuotient P).eval
    (Polynomial.C (f.coeff 0) - f ^ (p ^ u))

theorem zeroBlockNormPolynomial_natDegree_lt
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) {S : ℕ} (hS : 0 < S)
    (hcoeff : ∀ i, (P.coeff i).natDegree < S) :
    (zeroBlockNormPolynomial f u P).natDegree <
      p * S + f.natDegree * p ^ u * (p - 1)

theorem X_pow_dvd_zeroBlockNormPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n u : ℕ)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p) (hu : u ≤ n)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n u)) :
    Polynomial.X ^ (p ^ n) ∣ zeroBlockNormPolynomial f u P

theorem zeroBlockNormPolynomial_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (P : Polynomial (Polynomial (ZMod p)))
    (hP : P.natDegree < p)
    (hcoeff : ∀ i, (P.coeff i).natDegree < par.S)
    (hdiv : Polynomial.X ^ (p ^ n) ∣
      P.eval (upperTracePolynomial f n par.u)) :
    zeroBlockNormPolynomial f par.u P = 0
```

Evaluate the translation-product identity at `Phi`.  Its `beta=0` factor is
divisible by `X^(p^n)`.  Since `Phi^p-Phi=f^(p^n)-f^(p^u)` and
`X^(p^n)∣f^(p^n)-C(f.coeff 0)`, use exactly
`Polynomial.sub_dvd_eval_sub` to replace the invariant argument modulo
`X^(p^n)` by `C(f.coeff 0)-f^(p^u)`.  The displayed degree bound and
`par.norm_degree_ok` make the norm degree strictly below `p^n`; combine
`Polynomial.eq_zero_of_dvd_of_natDegree_lt` with
`Polynomial.natDegree_X_pow` to get the zero polynomial.

The later root is genuinely algebraic.  Its polynomial and evaluation map
are literal definitions.

```lean
noncomputable def zeroBlockArtinSchreierPolynomial
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    Polynomial (RatFunc (ZMod p)) :=
  Polynomial.X ^ p - Polynomial.X +
    Polynomial.C
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
        (f ^ (p ^ u) - Polynomial.C (f.coeff 0)))

theorem zeroBlockArtinSchreierPolynomial_translate
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ) :
    zeroBlockArtinSchreierPolynomial f u =
      (artinSchreierRatFuncPolynomial (eraseConstant f)).comp
        (Polynomial.X + Polynomial.C
          (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))
            (lowerTracePolynomial f u)))

theorem zeroBlockArtinSchreierPolynomial_irreducible
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (u : ℕ)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    Irreducible (zeroBlockArtinSchreierPolynomial f u)

noncomputable def zeroBlockEval
    {p : ℕ} [Fact p.Prime]
    {L : Type*} [Field L] [Algebra (RatFunc (ZMod p)) L]
    (P : Polynomial (Polynomial (ZMod p))) (z : L) : L :=
  P.eval₂
    ((algebraMap (RatFunc (ZMod p)) L).comp
      (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)))) z

theorem zeroBlockNorm_eq_zero_implies_exists_zero_factor
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

theorem zeroBlock_minpoly_add_primeField
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

theorem eq_zero_of_zeroBlockEval_eq_zero
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
```

For `s=lowerTracePolynomial f u`, freshman's dream gives
`s^p-s=f^(p^u)-f`.  Translating `T^p-T+(f-f(0))` by `T↦T+s` therefore gives
the zero-block polynomial; transport irreducibility through
`Polynomial.algEquivAevalXAddC` and `MulEquiv.irreducible_iff`.  After the
zero norm is evaluated at a root `z`, `Finset.prod_eq_zero_iff` selects
**one** `beta` with `P(z+beta)=0`.  The translated element has the displayed
irreducible degree-`p` polynomial as minpoly.  Thus `minpoly.dvd` makes a
degree-`p` polynomial divide the mapped `P` of degree `<p`; degree forcing
gives mapped `P=0`, and injectivity of the polynomial-to-rational-function
map gives `P=0`.  No step concludes that every translation factor vanishes.

Finally package and eliminate every `j`-block by finite strong induction.

```lean
noncomputable def auxiliaryBlock
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : Polynomial (Polynomial (ZMod p)) :=
  ∑ i : Fin p, Polynomial.monomial i.1 (e.coeff i j)

theorem auxiliaryBlock_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) : (auxiliaryBlock e j).natDegree < p

theorem auxiliaryBlock_coeff_natDegree_lt
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    {par : AdditiveStepanovParameters p d n}
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (j : Fin (par.K + 1)) (i : ℕ) :
    ((auxiliaryBlock e j).coeff i).natDegree < par.S

theorem X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero
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

theorem auxiliaryBlock_eq_zero_of_previous_eq_zero
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

theorem all_auxiliaryBlocks_eq_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p))
    (haux : additiveAuxiliaryPolynomial par f e = 0) :
    ∀ j : Fin (par.K + 1), auxiliaryBlock e j = 0

theorem additiveAuxiliaryPolynomial_ne_zero_of_blocks
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0

theorem additiveAuxiliaryPolynomial_ne_zero
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) (he : e.Nonzero) :
    additiveAuxiliaryPolynomial par f e ≠ 0
```

Assuming blocks below `j` are zero, factor the auxiliary as
`X^(p^n*j)*(P_j(Phi)+X^(p^n)*laterTail)=0`.  Cancel the nonzero monomial in the
domain and obtain `X^(p^n)∣P_j(Phi)`.  The zero-block norm and one-factor
theorems give `P_j=0`.  Strong induction on `j.1` proves every block zero;
coefficient extraction contradicts `e.Nonzero`.  This handles a zero initial
block without choosing a least nonzero index and remains valid when `K=0`.
The original `additiveAuxiliaryPolynomial_ne_zero` is now a short alias of the
block theorem, not the hiding place for the descent.

### 5.3 Degree divided by multiplicity and the point count

Every auxiliary term has degree at most

\[
 S+d(p-1)p^{n-1}+p^nK.
\]

```lean
theorem additiveAuxiliaryPolynomial_natDegree_le
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (e : AdditiveAuxiliaryCoefficients par (ZMod p)) :
    (additiveAuxiliaryPolynomial par f e).natDegree ≤
      par.S + d * (p - 1) * p ^ (n - 1) + p ^ n * par.K
```

Let `N_n(b)` be the trace-fiber cardinality.

```lean
noncomputable def tracePhaseFiberCard
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p)) (n : ℕ) (b : ZMod p) : ℕ := by
  letI := Fintype.ofFinite (GaloisField p n)
  exact (Finset.univ.filter fun x : GaloisField p n ↦
    Algebra.trace (ZMod p) (GaloisField p n)
      (f.eval₂ (algebraMap (ZMod p) (GaloisField p n)) x) = b).card
```

The auxiliary has multiplicity at least `R=pK` at every point in the fiber,
so the Hasse root-count theorem and the exact degree bound give

\[
 N_n(b)\le p^{n-1}+
 \frac{S+d(p-1)p^{n-1}}{R}.
\]

The quotient and its error term are displayed in Lean; no floor-division
estimate is hidden.

```lean
theorem stepanov_traceFiberCard_upper
    {p : ℕ} [Fact p.Prime] {d n : ℕ}
    (par : AdditiveStepanovParameters p d n)
    (f : Polynomial (ZMod p)) (hdegree : f.natDegree = d)
    (hpos : 0 < d) (hsmall : d < p) (b : ZMod p) :
    (tracePhaseFiberCard f n b : ℝ) ≤ (p : ℝ) ^ (n - 1) +
      ((par.S + d * (p - 1) * p ^ (n - 1) : ℕ) : ℝ) / par.R
```

For large `n`, `K>=p^(u-2)/(4d)`.  Substitution into the displayed error
shows it is at most `C_(p,d)*(sqrt p)^n`, with parity handled by
`n=2u` or `n=2u+1`.  The fibers partition all `p^n` extension-field
elements.  Applying the upper estimate to the other `p-1` fibers gives the
matching lower estimate for the selected fiber.  Therefore:

```lean
theorem additive_stepanov_point_count
    {p : ℕ} [Fact p.Prime]
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ b : ZMod p,
      |(tracePhaseFiberCard f n b : ℝ) - (p : ℝ) ^ (n - 1)| ≤
        C * (Real.sqrt p) ^ n
```

When `deg f=1`, the theorem follows directly from the nonzero linear trace
functional and does not construct Stepanov parameters.  Thus its stated
`0<deg f` API is honest.

## 6. Fourier inversion and reciprocal-root control

Module home:
`TranslationalTilings/NumberTheory/Stepanov/ReciprocalRoots.lean`.

Group the extension sum by trace value:

\[
 S_n(\psi,f)=\sum_{b\in F_p}\psi(b)N_n(b).
\]

The main terms cancel because `psi` is nontrivial.  The point-count error and
the triangle inequality give a uniform power bound.

```lean
theorem extensionExponentialSum_bound
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p))
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖extensionExponentialSum psi f n‖ ≤
        C * (Real.sqrt p) ^ n
```

The remaining analytic argument is split at its two actual proof seams.  The
first is simultaneous phase recurrence for a finite product of unit circles.
The implementation uses a finite-box pigeonhole proof: for each accuracy
`q`, partition every circle coordinate into `q` arcs, and fix a desired gap
`B`.  Among `(B+1)*q^s+1` consecutive powers, one of the `q^s` boxes contains
two exponent indices separated by more than `B`; their positive difference
has the requested gap while all coordinate phases are close to one.  At
diagonal stage `m`, take `B` to be the previous chosen exponent.  This gives a
strictly increasing sequence without multiplying an already-close exponent
(which could amplify its phase error).  Thus no one-dimensional
`AddCircle.exists_norm_nsmul_le` result, and no new
`Mathlib.NumberTheory.WellApproximable` import, is being treated as a
simultaneous approximation theorem.

```lean
theorem exists_unbounded_aligned_powers
    {s : ℕ} (u : Fin s → Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ i, Filter.Tendsto (fun m ↦ u i ^ n m)
        Filter.atTop (nhds 1)

noncomputable def maximalRootMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) : ℕ := by
  classical
  exact (roots.filter fun z ↦ ‖z‖ = rho).card

theorem exists_normalized_powerSum_tendsto_maximalMultiplicity
    (roots : Multiset ℂ) (rho : ℝ) (hrho : 0 < rho)
    (hle : ∀ z ∈ roots, ‖z‖ ≤ rho)
    (hmax : ∃ z ∈ roots, ‖z‖ = rho) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Filter.Tendsto
        (fun m ↦
          (roots.map fun z ↦ z ^ n m / (rho : ℂ) ^ n m).sum)
        Filter.atTop
        (nhds (maximalRootMultiplicity roots rho : ℂ))

theorem norm_le_of_power_sum_bound
    (roots : Multiset ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hpow : ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ n ≥ N,
      ‖(roots.map fun z ↦ z ^ n).sum‖ ≤ C * R ^ n) :
    ∀ z ∈ roots, ‖z‖ ≤ R
```

For the second seam, choose `rho` as the maximum modulus (the empty multiset
is immediate), enumerate the maximal roots with their multiplicities, and
apply `exists_unbounded_aligned_powers` to `z/rho`.  Along the returned
strictly increasing exponents, every normalized maximal root tends to one.
Every smaller root has modulus ratio strictly below one, so its normalized
powers tend to zero.  The finite sum therefore tends to the positive natural
number `maximalRootMultiplicity roots rho`, exactly as stated by
`exists_normalized_powerSum_tendsto_maximalMultiplicity`.  If `rho>R`, the
assumed bound divided by `rho^n` tends to zero because `R/rho<1`, a
contradiction.  Multiplicities cause no cancellation because all maximal
phases are aligned simultaneously.  Thus `norm_le_of_power_sum_bound` is a
short corollary of the two named seams.

Combining this lemma with the trace identity proves the last internal API:

```lean
theorem reciprocalRoots_norm_le
    {p : ℕ} [Fact p.Prime]
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hf0 : f.coeff 0 = 0)
    (hpos : 0 < f.natDegree) (hsmall : f.natDegree < p) :
    ∀ omega ∈ reciprocalRoots psi f, ‖omega‖ ≤ Real.sqrt p
```

Only an upper root bound is needed.  Cochrane--Pinner also compute the leading
L-coefficient, via paired Waring variables and a quadratic Gauss sum, in order
to prove equality `norm omega=sqrt p`.  That calculation is deliberately not
in the minimal closure: at most `d-1` roots, each of norm at most `sqrt p`,
already gives the exact exponential-sum bound required by Chapter 5.

## 7. Public terminal API and proof

Module home:
`TranslationalTilings/NumberTheory/PolynomialWeilBound.lean`.

The implementation closes `namespace Stepanov` before these declarations, so
the names live directly in `TranslationalTilings`, matching the Chapter 5
consumer.

```lean
end Stepanov

open Stepanov

theorem exists_prime_addChar_reciprocalRoots_le
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ∃ r ≤ f.natDegree - 1, ∃ alpha : Fin r → ℂ,
      (∑ x : ZMod p, psi (f.eval x)) = -∑ i, alpha i ∧
      ∀ i, ‖alpha i‖ ≤ Real.sqrt p

theorem polynomial_addChar_sum_prime_of_ne_one
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (psi : AddChar (ZMod p) ℂ) (hpsi : psi ≠ 1)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, psi (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p

theorem polynomial_addChar_sum_prime
    {p : ℕ} [NeZero p] (hp : p.Prime)
    (f : Polynomial (ZMod p)) (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
    ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
      (f.natDegree - 1 : ℝ) * Real.sqrt p

end TranslationalTilings
```

To prove the first theorem, install `Fact p.Prime`, put
`g=eraseConstant f`, and let `t=constantTwist psi f`.  Sections 2 and 6 give
a reciprocal-root multiset `omega` of cardinality `r<=d-1`, the `n=1`
extension identity for `g`, and `norm omega_i<=sqrt p`.
`extensionExponentialSum_one_eq_primeSum` converts its left side from the
sum over `GaloisField p 1` to the literal sum over `ZMod p`.  The
constant-twist identity gives the sum for `f` after replacing every root by
`t*omega_i`; Section 1 gives `norm t=1`, so the norm bound is unchanged.
Choose an equivalence between the multiset's finite index type and `Fin r` to
obtain `alpha`.

The second theorem is the finite-sum triangle inequality followed by
`r<=d-1`.  The third uses Mathlib's primitivity of `ZMod.stdAddChar`; because
`p` is prime and hence `1<p`, the standard character is not the trivial
character.  No equality of reciprocal-root norms is used.

## 8. Source-to-Lean comparator

| Mathematical source step | Lean boundary | Exact specialization/change |
|---|---|---|
| Cochrane--Pinner (2.1)--(2.2), monic encoding | `monicEncodingEquiv`, `normalizedIrreducibleFactors_prod`, `monicWeight_eq_prod_normalizedIrreducibleFactors` | Makes the coefficient-record/polynomial bridge and repeated normalized factors literal. |
| Cochrane--Pinner Waring formulas | `waringPowerSum`, `monicPhase_affine_last`, `artinCoefficient_eq_zero_of_degree_le` | Polynomial `f`, `g=1`; cancellation in coordinate `u_d`; the affine identity is characteristic-independent. |
| Cochrane--Pinner formal Euler step | `truncatedEulerProduct_coeff`, `truncatedEulerProduct_logDerivative_coeff`, `artinCoefficient_markedFactor_recurrence` | Replaces the infinite Euler product by a cutoff-finite recurrence with the same coefficients and multiplicities. |
| Cochrane--Pinner extension-field identification | `minpolyFiber_nonempty_iff_natDegree_dvd`, `card_minpolyFiber`, `traceLiftAddChar_eq_minpolyWeight_pow`, `markedFactorSum_eq_extensionExponentialSum` | Uses finite-field divisor/splitting/perfectness/trace APIs; no appeal to unnamed “Galois conjugacy.” |
| Degree-one extension/base-field identification | `extensionExponentialSum_one_eq_primeSum` | Reindexes by `GaloisField.equivZmodP`, transports trace with `Algebra.trace_eq_of_algEquiv`, and reduces the self-trace before the terminal specialization. |
| Cochrane--Pinner (2.3), root comparison | `rootFactorPolynomial_newton_recurrence`, `artinLPolynomial_coeff_eq_artinCoefficient`, `neg_eq_of_convolution_recurrences`, `artinLPolynomial_trace_identity` | Reverse-polynomial roots; negative sign and the `T 0=1` induction are explicit. |
| Cochrane--Pinner Lemma 3.1, reducibility criterion | `artinSchreierAutShift`, `artinSchreier_minpoly_natDegree_eq_one_or_prime`, `artinSchreierPolynomial_irreducible_iff_no_root` | Correct splitting-field/Galois-subgroup proof; does not multiply translations of an arbitrary factor. |
| Cochrane--Pinner Lemma 3.1, rational-function exclusion | `ratFunc_eq_algebraMap_of_pow_sub_self_eq_algebraMap`, `polynomial_pow_sub_self_natDegree`, `artinSchreierRatFuncPolynomial_irreducible` | Coprime numerator/denominator clearing and `0<d<p`; no general plane-curve criterion. |
| Direct trace-only parameter specialization | `AdditiveStepanovParameters`, `exists_additive_stepanov_parameters` | `S=p^(n-2)`, `K=floor(p^(u-2)/(2d))`, `R=pK`; proves `K>0`, `2d≤K`, both parities, and strict dimension slack. |
| Cochrane--Pinner Theorem 3.1, linear system | `AdditiveCoeffVector`, `reducedHassePolynomial`, `additiveConstraint`, `exists_nonzero_mem_additiveConstraint_ker`, `exists_additive_stepanov_coefficients` | Literal `p*S*(K+1)`-dimensional source and `R*D`-dimensional target; corrected `n≠0` trace seam and exact freezing use. |
| Cochrane--Pinner Lemma 3.2, fixed ring/modulus | `exists_translationProductQuotient`, `translationProductQuotient_coeff_natDegree_lt`, `X_pow_dvd_zeroBlockNormPolynomial`, `zeroBlockNormPolynomial_eq_zero` | Translation product, not field norm; fixed-ring filtration and `sub_dvd_eval_sub` modulo `X^(p^n)` are project theorems. |
| Cochrane--Pinner Lemma 3.2, algebraic root | `zeroBlockArtinSchreierPolynomial_irreducible`, `zeroBlockNorm_eq_zero_implies_exists_zero_factor`, `zeroBlock_minpoly_add_primeField`, `eq_zero_of_zeroBlockEval_eq_zero` | Selects one zero factor, then uses the degree-`p` minpoly against outer degree `<p`. |
| Cochrane--Pinner Lemma 3.2, iteration | `X_pow_dvd_auxiliaryBlock_eval_of_previous_eq_zero`, `all_auxiliaryBlocks_eq_zero`, `additiveAuxiliaryPolynomial_ne_zero` | Strong induction over all `Fin (K+1)` blocks; no least-index or “repeat” gap. |
| Hasse multiplicity and degree quotient | `vanishesToOrderAtLeast_iff_rootMultiplicity`, `card_mul_le_natDegree_of_vanishes`, `stepanov_traceFiberCard_upper` | Gives the exact displayed `/R` error before asymptotic simplification. |
| Their box-principle paragraph after (3.1) | `exists_unbounded_aligned_powers`, `exists_normalized_powerSum_tendsto_maximalMultiplicity`, `norm_le_of_power_sum_bound` | Finite-box simultaneous recurrence, strict-mono exponents, and maximal/smaller-root limit are separate seams. |
| Their (1.3), pure additive case | `polynomial_addChar_sum_prime_of_ne_one` | Fixed nontrivial character over `ZMod p`, with constant term restored by a norm-one twist. |
| Chapter 5 consumer | `polynomial_addChar_sum_prime` | `psi=ZMod.stdAddChar`; exact RHS `(natDegree f-1)*sqrt p`. |

## 9. Sorry-free acceptance checklist

This chapter is complete only when all of the following hold in the pinned
checkout:

1. every displayed definition and theorem signature elaborates with the
   listed imports;
2. every theorem above has a proof term containing no `sorry`, `admit`, axiom,
   opaque certificate field, or imported theorem which merely restates the
   desired estimate;
3. the direct trace-only dimension inequality is proved for both parities,
   `K>0` and `R>0` are explicit, and the degree-divided-by-`R` error is the
   displayed quotient;
4. the nonzero auxiliary proof contains the literal translation product,
   reduction
   modulo `X^(p^n)`, strict degree comparison, transported Artin--Schreier
   irreducibility, and iteration over every `j` block;
5. the bounded Euler coefficient and log-derivative recurrences, together with
   their irreducible-orbit accounting, are formalized over `GaloisField p n`,
   and `extensionExponentialSum_one_eq_primeSum` explicitly transports the
   `n=1` sum to `ZMod p` before the terminal theorem;
6. the phase-alignment lemma treats multisets and produces unbounded powers;
7. `lake env lean` succeeds for every new module and for the Chapter 5
   consumer, and repository-wide `rg` finds no forbidden proof holes;
8. independent mathematical and Lean-library referees recheck the completed
   modules against this dependency graph before the prime theorem is marked
   closed.

Under the Tau Ceti standard, passing compilation alone is not the final gate:
the independent review must also confirm source fidelity, dependency
direction, minimal public API, and absence of a hidden theorem-strength
assumption.
