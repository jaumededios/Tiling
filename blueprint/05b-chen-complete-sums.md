# Chen--Nechaev complete rational sums

Paper prerequisite: the exact power-saving complete-sum estimate used in
Greenfeld--Tao, Lemma 4.2.  Primary source: Arkhipov--Chubarikov--Karatsuba,
*Trigonometric Sums in Number Theory and Analysis*, Chapter 2, Section 2.1,
especially printed pp. 49--56 (PDF pp. 60--67), Lemmas 2.1--2.4 and
Theorems 2.1--2.2.

This chapter replaces every closest-root, root-separation, or
polynomial-dependent `delta` argument.  The proof is exactly the source's
stationary residue-class descent.  In particular, the constant is uniform in
the coefficients and the modulus, and the exponent is exactly `1 - 1 / d`.

## Ownership and module boundary

This chapter owns the following production modules:

```text
TranslationalTilings/NumberTheory/FiniteCyclicPhase.lean
TranslationalTilings/NumberTheory/PolynomialCongruence.lean
TranslationalTilings/NumberTheory/ChenCompleteSum.lean
TranslationalTilings/NumberTheory/QuadraticCompleteSum.lean
TranslationalTilings/NumberTheory/CompleteExponentialSum.lean
```

It owns `IntegralPolynomialPhase`, `integralCompleteSum`, the integer and
`ZMod` polynomial representations, coefficient content and normalization,
the exact Chen local factors, the global finite product, the low-degree
branches, and the terminal theorems
`polynomialCompleteSum_effective` and
`integral_complete_exponential_sum_effective`.  Chapter 5 retains
`CirclePolynomial`, constructs its `IntegralPolynomialPhase`, and consumes the
terminal theorem to prove the Greenfeld--Tao-facing declarations.  No Chen API
is duplicated in Chapter 5.

The scratch declaration file
`tmp/BlueprintChenCompleteSums.lean` checks every definition and public
signature below against the pinned Mathlib checkout.

## Source audit and corrected typography

The rendered source pages, not OCR alone, fix four points which are part of
the formal specification.

1. In Theorem 2.1 the factor-one range is
   `(d - 1)^(2*d/(d-2)) < p`, strictly.  Equality belongs to the second
   branch.  This corrects the earlier blueprint's non-strict test.
2. In the proof of Lemma 2.2, printed p. 50 says `m >= n`, although `n` is not
   in the lemma.  The displayed identity proves and needs `m >= u`.
3. On printed p. 55, the normalization of the `j`th translated polynomial is
   printed once with `p^(-sigma_1)`; the surrounding definition and (2.14)
   require `p^(-sigma_j)`.
4. Printed p. 54 defines one convex function and labels its displayed
   derivatives with the next subscript.  The proof uses a single function
   `r |-> r * p^(M/(r*d))`; no mathematical index changes.

These are source errata, not changes to the argument.

## Exact imports and recursive gap audit

```lean
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Polynomial.Content
```

Pinned Mathlib supplies `Polynomial.eval`, `comp`, `derivative`, `content`,
monic division, `rootMultiplicity`, roots over a field, `ZMod`,
`ZMod.chineseRemainder`, `ZMod.stdAddChar`, character orthogonality, finite
sums, `Nat.factorization`, p-adic valuations, quadratic characters, and the
general Gauss-sum identities.  It does not supply any of the following, all
of which are proved here:

- coefficientwise p-adic normalization of an integer polynomial;
- A--C--K Lemmas 2.2--2.4 in the exact forms needed by the descent;
- the residue-class identities (2.3)--(2.5);
- the large-, middle-, and small-prime inductions (2.6)--(2.14);
- general polynomial complete-sum CRT with preservation of nonconstant
  content-primitivity;
- the quadratic prime-power estimate, especially the `2^a` parity branch;
- degree padding and the uniform finite-product estimate.

The prime-modulus base case used below is the project theorem
`TranslationalTilings.polynomial_addChar_sum_prime`, owned solely by Chapter
05a.  Its exact type has `[NeZero p]`, `hp : p.Prime`,
`f : Polynomial (ZMod p)`, `0 < f.natDegree`, and `f.natDegree < p`, and its
conclusion is
`‖∑ x, ZMod.stdAddChar (f.eval x)‖ ≤
 (f.natDegree - 1 : ℝ) * Real.sqrt p`.
It is proved by the fixed-character Weil development in `05a-weil-stepanov.md`;
05b neither redeclares nor axiomatizes it.  Thus this chapter's only deep
incoming edge is explicit.
To keep the q-adic development independently buildable, the first four
number-theory modules consume the following proposition as a parameter:

```lean
def PolynomialPrimeSumBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (f : Polynomial (ZMod p)),
    0 < f.natDegree → f.natDegree < p →
      ‖∑ x : ZMod p, ZMod.stdAddChar (f.eval x)‖ ≤
        (f.natDegree - 1 : ℝ) * Real.sqrt p

theorem polynomialPrimeSumBound : PolynomialPrimeSumBound := by
  intro p _ f hpos hsmall
  let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact polynomial_addChar_sum_prime
    (Fact.out : p.Prime) f hpos hsmall
```

`ChenCompleteSum.lean` exports every main result first with suffix
`_of_primeBound` and hypothesis `hWeil : PolynomialPrimeSumBound`.
`CompleteExponentialSum.lean` imports the fixed-character module, constructs
`PolynomialPrimeSumBound` from `polynomial_addChar_sum_prime`, and exports the
unsuffixed specializations.  In particular, the unsuffixed
`chen_prime_base`, `primePower_completeSum_bound`, and
`ack_theorem_2_2_finiteProduct` declarations displayed below are owned by
`CompleteExponentialSum`, not by the conditional `ChenCompleteSum` module.
The displayed checked body introduces
`let _ : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩` and applies the 05a
theorem, so the change from `[Fact p.Prime]` to `[NeZero p]` is elaborated,
not merely asserted in prose.  Therefore the
exact stationary recursion and its
scratch integration do not wait for the terminal proof of the incoming Weil
module, while the final trusted declarations have no hypothesis standing in
for Weil.

## 1. Integral phases, polynomial content, and exact enumeration

Only positive-degree coefficients enter primitivity.  Constant coefficients
multiply a complete sum by a unit complex number and do not enter the gcd.

```lean
namespace TranslationalTilings

open scoped BigOperators Real

abbrev Torus := AddCircle (1 : ℝ)

noncomputable def circlePhase (x : Torus) : ℂ := fourier 1 x

structure IntegralPolynomialPhase (d : ℕ) where
  modulus : ℕ
  modulus_pos : 0 < modulus
  coeff : Fin d → ℤ

def IntegralPolynomialPhase.evalNumerator
    (A : IntegralPolynomialPhase d) (n : ℤ) : ℤ :=
  ∑ i : Fin d, A.coeff i * n ^ ((i : ℕ) + 1)

def IntegralPolynomialPhase.Primitive
    (A : IntegralPolynomialPhase d) : Prop :=
  Nat.Coprime A.modulus
    (Finset.univ.gcd fun i : Fin d ↦ Int.natAbs (A.coeff i))

noncomputable def integralCompleteSum
    (A : IntegralPolynomialPhase d) : ℂ :=
  ∑ n ∈ Finset.Icc 1 A.modulus,
    circlePhase
      (((A.evalNumerator n : ℝ) / A.modulus : ℝ) : Torus)

noncomputable def _root_.Polynomial.nonconstantPart
    (f : Polynomial ℤ) : Polynomial ℤ :=
  f - Polynomial.C (f.coeff 0)

def _root_.Polynomial.contentNat (f : Polynomial ℤ) : ℕ :=
  Int.natAbs (Polynomial.content f)

noncomputable def _root_.Polynomial.nonconstantContentNat
    (f : Polynomial ℤ) : ℕ :=
  Polynomial.contentNat (Polynomial.nonconstantPart f)

noncomputable def IntegralPolynomialPhase.toPolynomial
    (A : IntegralPolynomialPhase d) : Polynomial ℤ :=
  ∑ i : Fin d,
    Polynomial.monomial ((i : ℕ) + 1) (A.coeff i)

noncomputable def polynomialCompleteSum
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) : ℂ :=
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  ∑ x : ZMod q,
    ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
```

The cross-representation interface is public:

```lean
theorem IntegralPolynomialPhase.eval_toPolynomial
    (A : IntegralPolynomialPhase d) (n : ℤ) :
  A.toPolynomial.eval n = A.evalNumerator n

theorem IntegralPolynomialPhase.eval_toPolynomial_zmod
    (A : IntegralPolynomialPhase d) (q : ℕ) (hq : 0 < q) (n : ℤ) :
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  Polynomial.eval (n : ZMod q)
      (A.toPolynomial.map (Int.castRingHom (ZMod q))) =
    (A.evalNumerator n : ZMod q)

theorem IntegralPolynomialPhase.natDegree_toPolynomial_le
    (A : IntegralPolynomialPhase d) :
  A.toPolynomial.natDegree ≤ d

theorem IntegralPolynomialPhase.primitive_toPolynomial
    (A : IntegralPolynomialPhase d) (hA : A.Primitive) :
  Nat.Coprime A.modulus
    (Polynomial.nonconstantContentNat A.toPolynomial)

theorem integralCompleteSum_eq_polynomialCompleteSum
    (A : IntegralPolynomialPhase d) :
  integralCompleteSum A =
    polynomialCompleteSum A.modulus A.modulus_pos A.toPolynomial
```

For evaluation, expand the finite polynomial sum and commute `Polynomial.eval`
with the cast.  For content, the coefficient of `X^(i+1)` is exactly
`A.coeff i`; coefficient zero is zero.  The gcd of this finitely supported
coefficient family is the `Finset.univ.gcd` in `Primitive`, including `d=0`.

For the enumeration theorem, reindex `Finset.Icc 1 q` by reduction modulo
`q`.  The representatives `1,...,q-1,q` map bijectively to the standard
residues `1,...,q-1,0`.  Use `ZMod.stdAddChar_coe` and
`AddCircle.fourier_coe_apply`; both use the positive exponential
`exp(2*pi*I*x/q)`.  This proves equality of complex sums, not merely equality
of their norms.

## 2. Coefficient valuation and stationary data

The following definitions are total.  Division is integer coefficientwise
division; every theorem that rewrites a polynomial first proves divisibility
of all coefficients.

```lean
noncomputable def _root_.Polynomial.modPrime (p : ℕ)
    (f : Polynomial ℤ) : Polynomial (ZMod p) :=
  f.map (Int.castRingHom (ZMod p))

noncomputable def _root_.Polynomial.rootsModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : Finset (ZMod p) :=
  Finset.univ.filter (Polynomial.modPrime p f).IsRoot

noncomputable def _root_.Polynomial.rootMassModPrime (p : ℕ) [Fact p.Prime]
    (f : Polynomial ℤ) : ℕ :=
  ∑ x ∈ Polynomial.rootsModPrime p f,
    (Polynomial.modPrime p f).rootMultiplicity x

noncomputable def _root_.Polynomial.coeffDiv
    (f : Polynomial ℤ) (m : ℕ) : Polynomial ℤ :=
  f.sum fun n a ↦ Polynomial.monomial n (a / (m : ℤ))

def _root_.Polynomial.coefficientPadicOrder
    (p : ℕ) (f : Polynomial ℤ) : ℕ :=
  padicValNat p (Polynomial.contentNat f)

noncomputable def _root_.Polynomial.normalizeAtPrime
    (p : ℕ) (f : Polynomial ℤ) : Polynomial ℤ :=
  Polynomial.coeffDiv f (p ^ Polynomial.coefficientPadicOrder p f)

noncomputable def _root_.Polynomial.primeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  f.comp (Polynomial.C (p : ℤ) * Polynomial.X + Polynomial.C mu)

noncomputable def _root_.Polynomial.normalizedPrimeScaleTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.primeScaleTranslate f p mu)

noncomputable def _root_.Polynomial.stationaryTranslate
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.primeScaleTranslate f p mu - Polynomial.C (f.eval mu)

noncomputable def _root_.Polynomial.stationaryOrder
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : ℕ :=
  Polynomial.coefficientPadicOrder p (Polynomial.stationaryTranslate f p mu)

noncomputable def _root_.Polynomial.stationaryNormalize
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p (Polynomial.stationaryTranslate f p mu)

noncomputable def _root_.Polynomial.derivativeContentOrder
    (f : Polynomial ℤ) (p : ℕ) : ℕ :=
  Polynomial.coefficientPadicOrder p f.derivative

noncomputable def _root_.Polynomial.normalizedDerivative
    (f : Polynomial ℤ) (p : ℕ) : Polynomial ℤ :=
  Polynomial.normalizeAtPrime p f.derivative

noncomputable def _root_.Polynomial.derivativeRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p f.derivative

noncomputable def _root_.Polynomial.derivativeRootMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p f.derivative

noncomputable def _root_.Polynomial.earlyDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    Polynomial.stationaryOrder f p mu.val < L

noncomputable def _root_.Polynomial.lateDerivativeRoots
    (f : Polynomial ℤ) (p L : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  (Polynomial.derivativeRoots f p).filter fun mu ↦
    L ≤ Polynomial.stationaryOrder f p mu.val

noncomputable def _root_.Polynomial.derivativeRootMassOn
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime]
    (s : Finset (ZMod p)) : ℕ :=
  ∑ mu ∈ s, (Polynomial.modPrime p f.derivative).rootMultiplicity mu

noncomputable def _root_.Polynomial.smallPrimeStationaryRoots
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : Finset (ZMod p) :=
  Polynomial.rootsModPrime p (Polynomial.normalizedDerivative f p)

noncomputable def _root_.Polynomial.smallPrimeStationaryMass
    (f : Polynomial ℤ) (p : ℕ) [Fact p.Prime] : ℕ :=
  Polynomial.rootMassModPrime p (Polynomial.normalizedDerivative f p)

structure _root_.Polynomial.StationaryChildInvariant
    (f : Polynomial ℤ) (p : ℕ) (mu : ℤ) (d : ℕ) : Prop where
  translate_ne_zero : Polynomial.stationaryTranslate f p mu ≠ 0
  natDegree_eq : (Polynomial.stationaryNormalize f p mu).natDegree = d
  coeff_zero : (Polynomial.stationaryNormalize f p mu).coeff 0 = 0
  primitive :
    ¬ p ∣ Polynomial.nonconstantContentNat
      (Polynomial.stationaryNormalize f p mu)
```

The normalization and scalar-content API is:

```lean
theorem _root_.Polynomial.nonconstantContentNat_C_mul
    (u : ℤ) (f : Polynomial ℤ) :
  Polynomial.nonconstantContentNat (Polynomial.C u * f) =
    Int.natAbs u * Polynomial.nonconstantContentNat f

theorem _root_.Polynomial.normalizeAtPrime_spec
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0) :
  f = Polynomial.C
      ((p ^ Polynomial.coefficientPadicOrder p f : ℕ) : ℤ) *
    Polynomial.normalizeAtPrime p f

theorem _root_.Polynomial.normalizeAtPrime_primitive
    (hp : p.Prime) (f : Polynomial ℤ) (hf : f ≠ 0) :
  ¬ p ∣ Polynomial.contentNat (Polynomial.normalizeAtPrime p f)
```

`Polynomial.content` is a gcd up to the normalized associate in `ℤ`.  Taking
`Int.natAbs` removes the associate.  The standard characterization of
`padicValNat` proves that `p^u` divides every coefficient, so `coeffDiv`
reconstructs the original polynomial.  Maximality of the valuation gives a
coefficient of the quotient not divisible by `p`.

## 3. A--C--K Lemmas 2.2--2.4

### 3.1 Lemma 2.2: multiplicity does not grow under descent

```lean
theorem _root_.Polynomial.ack_lemma_2_2_degree
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p g).IsRoot mu) :
  (Polynomial.modPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val)).natDegree ≤
    (Polynomial.modPrime p g).rootMultiplicity mu

theorem _root_.Polynomial.ack_lemma_2_2_rootMass
    [Fact p.Prime] (hp : p.Prime) (g : Polynomial ℤ)
    (hg : Polynomial.modPrime p g ≠ 0) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p g).IsRoot mu) :
  Polynomial.rootMassModPrime p
      (Polynomial.normalizedPrimeScaleTranslate g p mu.val) ≤
    (Polynomial.modPrime p g).rootMultiplicity mu
```

Let `m` be the root multiplicity.  Divide `g` over `ℤ[X]` by the monic
polynomial `(X-mu)^m`.  Reduction modulo `p` shows that the remainder is
`p*l` with `degree l < m`, while the quotient `k` satisfies `k(mu) != 0`
modulo `p`.  Thus

`g(pX+mu) = p^m X^m k(pX+mu) + p*l(pX+mu)`.

If `u` is its coefficient-content valuation, the `X^m` coefficient shows
`u <= m` (the correction to the source typo).  After division by `p^u`, the
reduction modulo `p` has degree at most `m`: when `u<m` the first term
vanishes, and when `u=m` it contributes precisely `X^m*k(mu)`; the second
term always has degree below `m`.  Over the field `ZMod p`, the sum of root
multiplicities is the cardinality of the roots multiset and is at most the
degree.  This proves the second theorem without a splitting field.

### 3.2 Lemma 2.3: translated content is between one and the degree

```lean
theorem _root_.Polynomial.ack_lemma_2_3
    (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  1 ≤ Polynomial.stationaryOrder f p mu ∧
    Polynomial.stationaryOrder f p mu ≤ d

theorem _root_.Polynomial.stationaryChildInvariant
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 0 < d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ℤ) :
  Polynomial.StationaryChildInvariant f p mu d

theorem _root_.Polynomial.stationaryOrder_two_le_of_isRoot
    (hp : p.Prime) (f : Polynomial ℤ) (mu : ZMod p)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val
```

The constant term of `f(mu+pX)-f(mu)` is zero and every other coefficient
contains `p`, proving the lower bound.  Choose the largest `tau` for which
the coefficient of `X^tau` in `f` is not divisible by `p`.  In the translated
polynomial the coefficient of `X^tau` has p-adic valuation exactly `tau`:
the leading contribution is `a_tau*p^tau`, and every contribution from a
higher index has one extra `p` because of maximality of `tau`.  Hence
`sigma <= tau <= d`.

The combined child invariant is the state carried by both strong inductions.
If `a_d` is the nonzero leading coefficient, then the leading coefficient of
`f(mu+p*X)-f(mu)` is `a_d*p^d`, hence the translate is nonzero and still has
degree `d`.  Dividing every coefficient by the exact common power `p^sigma`
does not kill that leading coefficient, so the normalized child also has
degree exactly `d`.  Its constant coefficient is zero.  Finally
`normalizeAtPrime_primitive` makes its full content a p-unit; because the
constant coefficient is zero, full content and nonconstant content agree.
Thus the child again satisfies every induction hypothesis, not only the
descendant root-mass estimate.

For the last theorem, the coefficient of `X` in the stationary translate is
`p*f'(mu)`.  Root membership contributes a second factor of `p`, while all
higher coefficients already contain `p^2`.  Nonzero translation excludes the
totalized `padicValNat p 0 = 0` case, so the common order is at least two.

### 3.3 Lemma 2.4: the convexity estimate

```lean
theorem chen_convexity_bound
    {I : Type*} (s : Finset I) (a : ℝ) (m : I → ℕ)
    (ha : 1 < a) (hm : ∀ i ∈ s, 0 < m i) :
  ∑ i ∈ s, a ^ m i ≤
    max (((∑ i ∈ s, m i : ℕ) : ℝ) * a)
      (a ^ (∑ i ∈ s, m i))
```

For positive `r,s`,

`a^r + a^s <= a^(r+s-1) + a`

because the difference factors as `(a^r-a)*(a^(s-1)-1)`.  Repeatedly merge
two parts to obtain

`sum a^(m_i) <= (card s-1)*a + a^(k-card s+1)`,

where `k=sum m_i`.  Since `1 <= card s <= k` in the nonempty case, the last
expression is bounded by the larger endpoint `max(k*a,a^k)`.  The empty case
is immediate.  This finite induction is preferable in Lean to differentiating
the real interpolation used in the source.

## 4. Residue-class enumeration: equations (2.3)--(2.5)

```lean
noncomputable def primePowerResidueClassSum
    (p a : ℕ) (hp : p.Prime) (f : Polynomial ℤ)
    (v : ZMod p) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ∑ x : ZMod (p ^ a),
    if (x.val : ZMod p) = v then
      ZMod.stdAddChar (Polynomial.eval x (f.map (Int.castRingHom _)))
    else 0

noncomputable def primePowerStationaryShortSum
    (p a : ℕ) (hp : p.Prime) (f : Polynomial ℤ)
    (v : ZMod p) : ℂ :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  letI : NeZero (p ^ (a - 2)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  ∑ y : ZMod (p ^ (a - 2)),
    ZMod.stdAddChar
      (Polynomial.eval ((v.val + p * y.val : ℕ) : ZMod (p ^ a))
        (f.map (Int.castRingHom _)))

theorem ack_completeSum_eq_sum_residueClasses
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f =
    ∑ v : ZMod p, primePowerResidueClassSum p a hp f v

theorem ack_eq_2_3_vanish
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (v : ZMod p)
    (hv : ¬ (Polynomial.modPrime p f.derivative).IsRoot v) :
  primePowerResidueClassSum p a hp f v = 0

theorem ack_eq_2_4
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  primePowerResidueClassSum p a hp f mu =
    (p : ℂ) * primePowerStationaryShortSum p a hp f mu

theorem ack_eq_2_5
    (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ) (mu : ZMod p)
    (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu)
    (htranslate : Polynomial.stationaryTranslate f p mu.val ≠ 0)
    (hsigma : Polynomial.stationaryOrder f p mu.val < a) :
  ‖primePowerResidueClassSum p a hp f mu‖ =
    (p : ℝ) ^ (Polynomial.stationaryOrder f p mu.val - 1) *
      ‖polynomialCompleteSum
        (p ^ (a - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _) (Polynomial.stationaryNormalize f p mu.val)‖

theorem ack_residueClass_trivial
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ) (v : ZMod p) :
  ‖primePowerResidueClassSum p a hp f v‖ ≤ (p : ℝ) ^ (a - 1)
```

For (2.3), each class is written uniquely as
`x=y+p^(a-1)z`, with `y` modulo `p^(a-1)` and `z` modulo `p`.  The binomial
theorem gives

`f(y+p^(a-1)z) = f(y)+p^(a-1)z*f'(y) (mod p^a)`.

The inner character sum is `p` if `f'(y)=0 mod p` and zero otherwise.
Because `y=v mod p`, it vanishes exactly on nonstationary classes.  At a
stationary root, the remaining summand has period `p^(a-2)`, giving the
factor `p` in (2.4).  Write

`f(mu+pY)-f(mu)=p^sigma*g_mu(Y)`.

The repaired nonzero premise and
`Polynomial.stationaryOrder_two_le_of_isRoot` first give `2<=sigma`; hence no
natural subtraction in the repetition count truncates.  If `sigma<a`, the
short sum contains `p^(sigma-2)` repetitions of the complete
sum modulo `p^(a-sigma)`; the outer `p` gives `p^(sigma-1)`.  The factor from
`f(mu)` has norm one, proving (2.5).  If `a<=sigma`, the class contains
`p^(a-1)` unit summands and the trivial bound applies.

The unrestricted totalized identity is deliberately retained as a negative
regression test: for `p=2`, `a=2`, `f=0`, and `mu=0`, the translation is zero,
`sigma=padicValNat 2 0=0`, the residue-class norm is `2`, while the naively
stated right side is the norm of the zero-polynomial complete sum modulo four,
namely `4`.  Every call to (2.5) therefore obtains `htranslate` from
`stationaryChildInvariant.translate_ne_zero`; the false `2=4` signature can
never be reintroduced unnoticed.

## 5. Large primes and exact branch endpoints

For `p>d`, reduction of the derivative is nonzero.  Let `m_mu` be each root
multiplicity and `m=sum m_mu`.  The following Taylor lemmas provide the exact
stationary data.

The two thresholds are defined here, before any range lemma consumes them:

```lean
noncomputable def chenLargePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((2 * d : ℝ) / (d - 2 : ℝ))

noncomputable def chenMiddlePrimeThreshold (d : ℕ) : ℝ :=
  Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2 : ℝ))
```

```lean
theorem _root_.Polynomial.stationaryOrder_two_le
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  2 ≤ Polynomial.stationaryOrder f p mu.val

theorem _root_.Polynomial.stationaryOrder_le_rootMultiplicity_succ
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.stationaryOrder f p mu.val ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1

theorem _root_.Polynomial.derivativeRootMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.derivativeRootMass f p ≤ d - 1

theorem _root_.Polynomial.stationaryNormalize_derivativeRootMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : (Polynomial.modPrime p f.derivative).IsRoot mu) :
  Polynomial.derivativeRootMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p f.derivative).rootMultiplicity mu
```

Taylor expansion is legitimate integrally.  Since `p>d`, every factorial up
to `d` is a unit modulo `p`.  A root of `f'` gives `sigma>=2`; if its
multiplicity is `m_mu`, then the first Taylor term not forced to gain an
extra `p` occurs at order `m_mu+1`, proving `sigma<=m_mu+1`.  The root-mass
bound is the standard roots-cardinality bound for the nonzero derivative.
Differentiating
`f(mu+pX)-f(mu)=p^sigma*g_mu(X)` identifies `g_mu'` with the
coefficient-normalized polynomial `f'(mu+pX)` modulo `p`.  Lemma 2.2 applied
to `f'` therefore gives the displayed descendant-root-mass theorem.  This is
the exact bridge used in (2.7); no unproved identification of two contents is
left implicit.

### 5.1 Prime denominator

```lean
theorem chen_prime_base
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d)

theorem chen_prime_base_of
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum p hp.pos f‖ ≤
    min (Real.rpow p ((1 : ℝ) / d))
        ((d - 1 : ℝ) *
          Real.rpow p (-(1 : ℝ) / 2 + (1 : ℝ) / d)) *
      Real.rpow p (1 - (1 : ℝ) / d)
```

The first term is the trivial bound `p`; the second is the imported Weil
bound `(d-1)*sqrt p`, padded from the actual degree modulo `p` to `d`.

### 5.2 The range `d < p <= B_d`: (2.6)--(2.12)

Set

`A_d=(d-1)^(2*d/(d-2))`, `B_d=(d-1)^(d/(d-2))`.

The elementary real inequalities are public because they are the delicate
part of the source induction:

```lean
theorem ack_ineq_2_9
    (d m p : ℕ) (hd : 3 ≤ d) (hm : 1 ≤ m) (hmd : m ≤ d - 1)
    (hp : d < p) (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  Real.rpow p ((m : ℝ) / d) ≤
    (m : ℝ) * Real.rpow p ((1 : ℝ) / d)

theorem ack_ineq_2_11
    (d L r₁ M₁ : ℕ) (hd : 3 ≤ d) (hr : 0 < r₁)
    (hL : r₁ * L ≤ M₁ + r₁) :
  (L : ℝ) ≤
    (L + 1 : ℝ) * (1 - (1 : ℝ) / d) - 1 + (2 : ℝ) / d +
      (M₁ : ℝ) / ((r₁ : ℝ) * d)

theorem ack_ineq_2_12
    (d r₁ M₁ p : ℕ) (hd : 3 ≤ d) (hr : 1 ≤ r₁)
    (hrM : r₁ ≤ M₁) (hMd : M₁ ≤ d - 1) (hp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d) :
  (r₁ : ℝ) *
      Real.rpow p ((M₁ : ℝ) / ((r₁ : ℝ) * d)) ≤
    (M₁ : ℝ) * Real.rpow p ((1 : ℝ) / d)
```

For (2.9), study the concave function
`y*p^(1/d)-p^(y/d)` on `[1,d-1]`; its endpoint inequalities are equivalent to
`d<p<=B_d`.  Inequality (2.11) is rational rearrangement of
`r1*L<=M1+r1`.  For (2.12), convexity of
`r |-> r*p^(M1/(r*d))` bounds it by its two endpoints, and (2.9) bounds both
by `M1*p^(1/d)`.

The source's individual and aggregate induction steps are exported:

```lean
theorem ack_ineq_2_7_of_inductionBound
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (L : ℕ) (hL : 2 ≤ L) (mu : ZMod p)
    (hmu : mu ∈ Polynomial.earlyDerivativeRoots f p L)
    (hrec :
      ‖polynomialCompleteSum
        (p ^ (L + 1 - Polynomial.stationaryOrder f p mu.val))
        (pow_pos hp.pos _) (Polynomial.stationaryNormalize f p mu.val)‖ ≤
      ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
        Real.rpow p
          (-1 + (3 : ℝ) / d +
            (L + 1 - Polynomial.stationaryOrder f p mu.val : ℝ) *
              (1 - (1 : ℝ) / d))) :
  ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤
    ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
      Real.rpow p
        (-2 +
          ((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d +
          (3 : ℝ) / d + (L + 1 : ℝ) * (1 - (1 : ℝ) / d))

theorem ack_ineq_2_8
    (hp : p.Prime) (f : Polynomial ℤ) (L : ℕ) (mu : ZMod p) :
  ‖primePowerResidueClassSum p (L + 1) hp f mu‖ ≤ (p : ℝ) ^ L

theorem ack_ineq_2_10
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (L : ℕ) (hL : 2 ≤ L) :
  ‖polynomialCompleteSum (p ^ (L + 1)) (pow_pos hp.pos _) f‖ ≤
    ((Polynomial.lateDerivativeRoots f p L).card : ℝ) * (p : ℝ) ^ L +
      ∑ mu ∈ Polynomial.earlyDerivativeRoots f p L,
        ((Polynomial.modPrime p f.derivative).rootMultiplicity mu : ℝ) *
          Real.rpow p
            (((Polynomial.modPrime p f.derivative).rootMultiplicity mu + 1 : ℝ) / d -
              2 + (3 : ℝ) / d +
              (L + 1 : ℝ) * (1 - (1 : ℝ) / d))

theorem ack_eq_2_6
    [Fact p.Prime] (hp : p.Prime) (ha : 2 ≤ a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hdp : d < p)
    (hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    (Polynomial.derivativeRootMass f p : ℝ) *
      Real.rpow p
        (-1 + (3 : ℝ) / d + (a : ℝ) * (1 - (1 : ℝ) / d))
```

The strong induction is on the modulus exponent.  For an early root
`sigma<L`, first obtain `stationaryChildInvariant f p mu d`; its
`translate_ne_zero` field licenses the repaired (2.5), and its
`natDegree_eq` and `primitive` fields license the induction hypothesis for the
normalized polynomial.  Then apply (2.5), the induction hypothesis,
Lemma 2.2 to bound its next root mass by `m_mu`, and
`sigma<=m_mu+1`; this is (2.7).  A late root uses the trivial class estimate
`p^L`, which is (2.8).  Split the roots into the finite `late` and `early`
sets under the displayed middle-prime hypothesis `hpB` to get (2.10).  Put

`r1=card late`, `M1=sum_(late) m_mu`, `M2=sum_(early) m_mu`.

If `late` is empty, (2.9) and the root-mass bound close the estimate.  If not,
`sigma>=L` and `sigma<=m_mu+1` give `r1*L<=M1+r1`; (2.11), (2.12), and (2.9)
turn both pieces of (2.10) into `(M1+M2)` times the desired common power.
This proves (2.6), including the endpoint `p=B_d`.

For `B_d<=p`, the simpler (2.5) induction uses
`sigma<=m_mu+1`, Lemma 2.4, and `sum m_mu<=d-1` to prove that the total
stationary weight is at most one.  Combining it with the prime base gives
factor `1` when `A_d<p` and `d^(2/d)` when `B_d<=p<=A_d`.  Combining (2.6)
with `m<=d-1` gives `d^(3/d)` when `d<p<B_d`.

## 6. Small primes: the `t` block and (2.13)--(2.14)

Put `t=v_p(content(f'))`.  Primitivity gives a coefficient `a_k` not divisible
by `p`; the derivative coefficient `k*a_k` shows `p^t | k`, hence `p^t<=k<=d`.
The normalized derivative is nonzero modulo `p`.

```lean
theorem _root_.Polynomial.derivativeContent_pow_le_degree
    (hp : p.Prime) (f : Polynomial ℤ) (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  p ^ Polynomial.derivativeContentOrder f p ≤ d

theorem _root_.Polynomial.mem_smallPrimeStationaryRoots_iff
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (v : ZMod p) :
  v ∈ Polynomial.smallPrimeStationaryRoots f p ↔
    (p ^ (Polynomial.derivativeContentOrder f p + 1) : ℤ) ∣
      f.derivative.eval v.val

theorem _root_.Polynomial.smallPrimeStationaryMass_le_degree
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  Polynomial.smallPrimeStationaryMass f p ≤ d - 1

theorem _root_.Polynomial.stationaryNormalize_smallPrimeStationaryMass_le
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  Polynomial.smallPrimeStationaryMass
      (Polynomial.stationaryNormalize f p mu.val) p ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu

theorem ack_smallPrime_block_vanish
    [Fact p.Prime] (hp : p.Prime) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (ha : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (v : ZMod p) (hv : v ∉ Polynomial.smallPrimeStationaryRoots f p) :
  primePowerResidueClassSum p a hp f v = 0
```

When `a>=2(t+1)`, write
`x=y+p^(a-t-1)z`, where `z` runs modulo `p^(t+1)`.  The quadratic and higher
Taylor terms are divisible by `p^a`; the inner sum is

`sum_z exp(2*pi*i*z*f'(y)/p^(t+1))`.

It vanishes unless `p^(t+1)|f'(y)`.  Since every derivative coefficient is
divisible by `p^t`, this condition depends only on `y mod p` and is exactly
membership in `smallPrimeStationaryRoots`.  The normalized derivative is
nonzero and has degree at most `d-1`, proving the first root-mass bound.
For a stationary root, differentiate the stationary normalization and remove
the remaining derivative content.  The result is exactly the normalized
prime-scale translate of `p^(-t)f'` up to a nonzero scalar modulo `p`.
Lemma 2.2 then proves the descendant-mass bound required by (2.14).

The inductive and per-class conclusions are:

```lean
theorem ack_eq_2_13
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    Real.rpow d ((3 : ℝ) / d) *
      max 1 (Polynomial.smallPrimeStationaryMass f p : ℝ) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))

theorem ack_eq_2_14
    [Fact p.Prime] (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) (hpd : p ≤ d)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hblock : 2 * (Polynomial.derivativeContentOrder f p + 1) ≤ a)
    (mu : ZMod p) (hmu : mu ∈ Polynomial.smallPrimeStationaryRoots f p) :
  ‖primePowerResidueClassSum p a hp f mu‖ ≤
    (Polynomial.modPrime p
      (Polynomial.normalizedDerivative f p)).rootMultiplicity mu *
      Real.rpow d ((3 : ℝ) / d) *
      Real.rpow p ((a : ℝ) * (1 - (1 : ℝ) / d))
```

Equation (2.14) is stated only in its source-faithful block
`2*(t+1)<=a`.  The low block is a base branch of (2.13), not an undocumented
branch of the per-class theorem.  If `a<2(t+1)`, the complete-sum trivial bound
gives

`p^a <= p^(a*(1-1/d))*p^((2*t+1)/d)
     <= d^(3/d)*p^(a*(1-1/d))`,

using `p^t<=d` and `p<=d`.  In the source block, nonstationary classes vanish.
At a stationary root, Lemma 2.3 gives `1<=sigma<=d`; the stronger lower bound
needed by (2.5) comes from `stationaryOrder_two_le_of_isRoot`.  The child
invariant supplies nonzero translation, exact degree `d`, zero constant, and
local primitivity before the induction hypothesis is invoked.  If `sigma<a`,
(2.5), strong induction, and Lemma 2.2 prove (2.14); if `a<=sigma`, the trivial
class bound does.  Summing and using total multiplicity at most `d-1` proves (2.13) and
the fourth local factor `(d-1)*d^(3/d)`.  This includes `p=d`.

## 7. Exact A--C--K Theorem 2.1

The thresholds and local factor encode the four source ranges with the exact
strict/non-strict endpoints.

```lean
noncomputable def chenLocalFactor (d p : ℕ) : ℝ :=
  if chenLargePrimeThreshold d < (p : ℝ) then 1
  else if chenMiddlePrimeThreshold d ≤ (p : ℝ) then
    Real.rpow d ((2 : ℝ) / d)
  else if d < p then Real.rpow d ((3 : ℝ) / d)
  else (d - 1 : ℝ) * Real.rpow d ((3 : ℝ) / d)

theorem primePower_completeSum_bound
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d)

theorem primePower_completeSum_bound_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hprimitive : ¬ p ∣ Polynomial.nonconstantContentNat f)
    (hdegree : f.natDegree = d) (hd : 3 ≤ d) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ ≤
    chenLocalFactor d p *
      Real.rpow (p ^ a : ℝ) (1 - (1 : ℝ) / d)
```

The proof branches in this order:

| Exact condition | Source factor |
|---|---:|
| `A_d < p` | `1` |
| `B_d <= p <= A_d` | `d^(2/d)` |
| `d < p < B_d` | `d^(3/d)` |
| `p <= d` | `(d-1)*d^(3/d)` |

Exponent `a=1` uses the prime base.  Exponents `a>=2` use the corresponding
stationary induction.  No endpoint is discharged by an unjustified
strict-to-nonstrict conversion.

## 8. CRT and the global finite product

The two-factor CRT theorem uses exact Bezout coefficients.  This is equivalent
to A--C--K Lemma 2.1 but does not require first deleting the constant term.

```lean
theorem polynomialCompleteSum_crt
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : Nat.Coprime q₁ q₂)
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1)
    (f : Polynomial ℤ) :
  polynomialCompleteSum (q₁ * q₂) (Nat.mul_pos hq₁ hq₂) f =
    polynomialCompleteSum q₁ hq₁ (Polynomial.C u₁ * f) *
      polynomialCompleteSum q₂ hq₂ (Polynomial.C u₂ * f)

theorem nonconstantContent_coprime_of_crt_unit
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hcop : Nat.Coprime q₁ q₂)
    (hprim : Nat.Coprime (q₁ * q₂)
      (Polynomial.nonconstantContentNat f))
    {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  Nat.Coprime q₁
      (Polynomial.nonconstantContentNat (Polynomial.C u₁ * f)) ∧
    Nat.Coprime q₂
      (Polynomial.nonconstantContentNat (Polynomial.C u₂ * f))
```

Reindex by `ZMod.chineseRemainder hcop`.  The Bezout identity gives

`e_(q1*q2)(f(x)) = e_q1(u1*f(x1))*e_q2(u2*f(x2))`,

and the sum over the product factors.  Reducing the identity modulo `q1`
shows that `u1` is a unit there; similarly `u2` is a unit modulo `q2`.
Together with `nonconstantContentNat_C_mul`, this proves local primitivity.

The support induction is exposed rather than hidden inside Theorem 2.2.  Its
scalar is the exact Bezout coefficient attached to each prime-power component.
The scalar family is indexed by the finite factorization support itself, not
by all natural numbers: there is no off-support proof data to choose.

```lean
/-- The prime-power components which actually occur in `q`. -/
abbrev FactorizationPrimeSupport (q : ℕ) :=
  {p : ℕ // p ∈ q.factorization.support}

/-- One Bezout scalar for each actual prime-power component of `q`. -/
abbrev FactorizationScalar (q : ℕ) :=
  FactorizationPrimeSupport q → ℤ

theorem factorizationPrimeSupport_prime {q : ℕ}
    (p : FactorizationPrimeSupport q) : p.1.Prime :=
  Nat.prime_of_mem_primeFactors p.property

/-- Canonical total lookup for interoperability with natural-prime-indexed
APIs.  It is definitionally fixed to zero away from the support. -/
def factorizationScalarLookup {q : ℕ}
    (u : FactorizationScalar q) (p : ℕ) : ℤ :=
  if hp : p ∈ q.factorization.support then u ⟨p, hp⟩ else 0

@[simp] theorem factorizationScalarLookup_of_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∈ q.factorization.support) :
  factorizationScalarLookup u p = u ⟨p, hp⟩ := by
  unfold factorizationScalarLookup
  rw [dif_pos hp]

@[simp] theorem factorizationScalarLookup_of_not_mem
    {q p : ℕ} (u : FactorizationScalar q)
    (hp : p ∉ q.factorization.support) :
  factorizationScalarLookup u p = 0 := by
  unfold factorizationScalarLookup
  rw [dif_neg hp]

theorem factorizationScalar_ext {q : ℕ}
    {u v : FactorizationScalar q}
    (h : ∀ p, u p = v p) : u = v := by
  funext p
  exact h p

theorem factorizationScalar_ext_iff_lookup_eq {q : ℕ}
    {u v : FactorizationScalar q} :
  u = v ↔ ∀ p, factorizationScalarLookup u p =
    factorizationScalarLookup v p := by
  constructor
  · rintro rfl p
    rfl
  · intro h
    apply factorizationScalar_ext
    intro p
    have hp := h p.1
    rw [factorizationScalarLookup_of_mem u p.property,
      factorizationScalarLookup_of_mem v p.property] at hp
    exact hp

/-- Bridge from the support subtype product to the source's double Finset
product notation. -/
theorem factorizationPrimeSupport_prod_eq
    {q : ℕ} {M : Type*} [CommMonoid M] (g : ℕ → M) :
  (∏ p : FactorizationPrimeSupport q, g p.1) =
    ∏ p ∈ q.factorization.support, g p := by
  classical
  exact Finset.prod_coe_sort q.factorization.support g

/-- At modulus one the support-indexed scalar family is uniquely empty. -/
theorem factorizationScalar_one_unique
    (u v : FactorizationScalar 1) : u = v := by
  apply factorizationScalar_ext
  intro p
  have hp : False := by simpa using p.property
  exact hp.elim

noncomputable def factorizationLocalCompleteSum
    (q : ℕ) (f : Polynomial ℤ) (u : FactorizationScalar q)
    (p : FactorizationPrimeSupport q) : ℂ :=
  polynomialCompleteSum (p.1 ^ q.factorization p.1)
    (pow_pos (factorizationPrimeSupport_prime p).pos _)
    (Polynomial.C (u p) * f)

structure CompleteSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ) where
  scalar : FactorizationScalar q
  scalar_ne_zero : ∀ p, scalar p ≠ 0
  local_primitive : ∀ p,
    Nat.Coprime (p.1 ^ q.factorization p.1)
      (Polynomial.nonconstantContentNat (Polynomial.C (scalar p) * f))
  norm_eq_product :
    ‖polynomialCompleteSum q hq f‖ =
      ∏ p : FactorizationPrimeSupport q,
        ‖factorizationLocalCompleteSum q f scalar p‖

theorem CompleteSumFactorizationData.ext_scalar
    {q : ℕ} {hq : 0 < q} {f : Polynomial ℤ}
    (D₁ D₂ : CompleteSumFactorizationData q hq f)
    (hscalar : ∀ p, D₁.scalar p = D₂.scalar p) : D₁ = D₂ := by
  cases D₁ with
  | mk scalar₁ scalar_ne_zero₁ local_primitive₁ norm_eq_product₁ =>
    cases D₂ with
    | mk scalar₂ scalar_ne_zero₂ local_primitive₂ norm_eq_product₂ =>
      have h : scalar₁ = scalar₂ := factorizationScalar_ext hscalar
      subst scalar₂
      rfl

theorem CompleteSumFactorizationData.one_unique
    {hq : 0 < 1} {f : Polynomial ℤ}
    (D₁ D₂ : CompleteSumFactorizationData 1 hq f) : D₁ = D₂ := by
  apply CompleteSumFactorizationData.ext_scalar
  intro p
  exact congrFun (factorizationScalar_one_unique D₁.scalar D₂.scalar) p

theorem _root_.Polynomial.natDegree_C_mul_eq
    (f : Polynomial ℤ) {u : ℤ} (hu : u ≠ 0) :
  (Polynomial.C u * f).natDegree = f.natDegree

theorem bezout_left_ne_zero_of_one_lt
    (hq₁ : 1 < q₁) {q₂ : ℕ} {u₁ u₂ : ℤ}
    (hbezout : u₁ * (q₂ : ℤ) + u₂ * (q₁ : ℤ) = 1) :
  u₁ ≠ 0

theorem polynomialCompleteSum_one_norm (f : Polynomial ℤ) :
  ‖polynomialCompleteSum 1 (by omega) f‖ = 1

theorem exists_completeSumFactorizationData
    (q : ℕ) (hq : 0 < q) (f : Polynomial ℤ)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  Nonempty (CompleteSumFactorizationData q hq f)

theorem factorization_rpow_product
    (q : ℕ) (hq : 0 < q) (x : ℝ) :
  ∏ p ∈ q.factorization.support,
      Real.rpow (p ^ q.factorization p : ℝ) x =
    Real.rpow q x
```

Membership in `FactorizationPrimeSupport q` implies primality by
`Nat.prime_of_mem_primeFactors`; this is the checked
`factorizationPrimeSupport_prime` bridge used to make each local modulus
positive.  `factorizationScalarLookup` is the only conversion back to a total
natural-indexed function, and its two simp theorems fix every off-support value
to zero.  Conversely, `factorizationScalar_ext_iff_lookup_eq` says those
canonical total lookups determine the support family.  The product bridge
`factorizationPrimeSupport_prod_eq` identifies the subtype product with the
source's `prod p in factorization.support` notation, so the pre-existing rpow
and local-factor product theorems below retain their statements.

For `q=1`, `Nat.factorization 1` has empty support.  Hence
`FactorizationPrimeSupport 1` is empty and
`factorizationScalar_one_unique` proves that any two scalar families are
equal: the constructor uses the unique empty function, both local laws have no
arguments, and the subtype product is one.
`polynomialCompleteSum_one_norm` supplies the remaining norm equality.  Thus
the modulus-one certificate has no arbitrary payload at all;
`CompleteSumFactorizationData.one_unique` makes this uniqueness explicit at
the level of the entire public structure.

For `q>1`, induction on `q.factorization.support` extracts `p^a` and its
positive coprime complement.  At each insertion step assign the exact Bezout
coefficient to that element of `FactorizationPrimeSupport q`; extensionality
of the finite support function proves independence from proof witnesses and
closes reconstruction.  The Bezout identity and `p^a>1` imply the
corresponding scalar is nonzero;
`Polynomial.natDegree_C_mul_eq` therefore transports the exact degree, while
`nonconstantContent_coprime_of_crt_unit` transports primitivity.  Repeated CRT
gives the subtype-indexed `norm_eq_product`, with neither a zero support scalar
nor any off-support choice.  `CompleteSumFactorizationData.ext_scalar` shows
that two public certificates are equal as soon as their meaningful scalar
families agree; all remaining fields are propositions.

Finally, the rpow theorem first rewrites `q` as the product of its positive
prime powers using `Nat.factorization_prod_pow_eq_self`, then applies
`Real.mul_rpow` inductively; positivity of each prime power supplies every side
condition.  Its use after `norm_eq_product` is preceded by
`factorizationPrimeSupport_prod_eq`.

For a transparent uniform constant, retain the finite product which appears
in the proof of source Theorem 2.2 rather than importing the source's separate
decimal prime-counting simplification.

```lean
def chenExceptionalPrimes (d : ℕ) : Finset ℕ :=
  (Finset.range ((d + 1) ^ 6 + 1)).filter Nat.Prime

noncomputable def chenGlobalFactor (d : ℕ) : ℝ :=
  ∏ p ∈ chenExceptionalPrimes d, chenLocalFactor d p

theorem chenLargePrimeExponent_le_six (d : ℕ) (hd : 3 ≤ d) :
  (2 * d : ℝ) / (d - 2 : ℝ) ≤ 6

theorem chenLargePrimeThreshold_le (d : ℕ) (hd : 3 ≤ d) :
  chenLargePrimeThreshold d ≤ (d + 1 : ℝ) ^ 6

theorem one_le_chenLocalFactor (d p : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenLocalFactor d p

theorem chenLocalFactor_eq_one_of_prime_not_mem
    (d p : ℕ) (hd : 3 ≤ d) (hp : p.Prime)
    (hmem : p ∉ chenExceptionalPrimes d) :
  chenLocalFactor d p = 1

theorem factorization_localFactor_product_le_global
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) :
  ∏ p ∈ q.factorization.support, chenLocalFactor d p ≤
    chenGlobalFactor d

theorem one_le_chenGlobalFactor (d : ℕ) (hd : 3 ≤ d) :
  1 ≤ chenGlobalFactor d

theorem ack_theorem_2_2_finiteProduct
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d)

theorem ack_theorem_2_2_finiteProduct_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 3 ≤ d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree = d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    chenGlobalFactor d * Real.rpow q (1 - (1 : ℝ) / d)
```

Take `CompleteSumFactorizationData` and apply the prime-power bound to every
`p : FactorizationPrimeSupport q`, using `p.1` as the natural prime.  Exact
scalar degree and local primitivity are fields of the data.  Rewrite its
subtype product with `factorizationPrimeSupport_prod_eq`; then
`factorization_rpow_product` combines all p-power terms into `q^(1-1/d)`.  If
a support prime is not exceptional, the threshold estimate and
`chenLocalFactor_eq_one_of_prime_not_mem` make its factor exactly one; all
exceptional factors are at least one, so finite-product monotonicity enlarges
the remaining support product to `chenGlobalFactor`.  When `q=1`, the unique
empty scalar family contributes no local factor, the left norm and the rpow
term are one, and `one_le_chenGlobalFactor` closes the bound.  This is the
exact finite product `D` in the first display
of the proof of source Theorem 2.2.  The subsequent printed bounds
`exp(4*d)` and the tabulated decimals only replace `D` by a larger elementary
number using a prime-counting estimate; Greenfeld--Tao never uses those
decimals.  They are therefore not added as a second public API or as an
unneeded recursive analytic-number-theory dependency.

## 9. Degrees one and two, including the full 2-adic branch

The Chen induction assumes `d>=3`.  The low degrees are independent and must
not be hidden inside degree padding.

```lean
noncomputable def quadraticPolynomial (A B C : ℤ) : Polynomial ℤ :=
  Polynomial.monomial 2 A + Polynomial.monomial 1 B + Polynomial.C C

noncomputable def quadraticGaussSum
    (q : ℕ) (hq : 0 < q) (A : ℤ) : ℂ :=
  polynomialCompleteSum q hq (quadraticPolynomial A 0 0)

theorem quadraticGaussSum_one (A : ℤ) :
  quadraticGaussSum 1 (by omega) A = 1

theorem quadraticGaussSum_oddPrime_base
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) :
  ‖quadraticGaussSum p hp.pos A‖ = Real.sqrt p

theorem quadraticGaussSum_oddPrime_recurrence
    (hp : p.Prime) (hpodd : p ≠ 2) (A : ℤ)
    (hA : ¬ p ∣ Int.natAbs A) (a : ℕ) :
  quadraticGaussSum (p ^ (a + 2)) (pow_pos hp.pos _) A =
    (p : ℂ) * quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A

theorem quadraticCompleteSum_oddPrime_completeSquare
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a)
    (A B C : ℤ) (hA : ¬ p ∣ Int.natAbs A) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (p ^ a) (pow_pos hp.pos _) A‖

theorem quadraticGaussSum_two_base_two
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 4 (by omega) A‖ = Real.sqrt 8

theorem quadraticGaussSum_two_base_three
    (A : ℤ) (hA : Odd A) :
  ‖quadraticGaussSum 8 (by omega) A‖ = 4

theorem quadraticGaussSum_two_recurrence
    (A : ℤ) (hA : Odd A) (a : ℕ) (ha : 2 ≤ a) :
  quadraticGaussSum (2 ^ (a + 2)) (pow_pos (by omega) _) A =
    2 * quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A

theorem quadraticCompleteSum_two_completeSquare
    (A B C : ℤ) (hA : Odd A) (hB : Even B)
    (a : ℕ) (ha : 2 ≤ a) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) _)
      (quadraticPolynomial A B C)‖ =
    ‖quadraticGaussSum (2 ^ a) (pow_pos (by omega) _) A‖

theorem quadraticCompleteSum_mod_two_norm
    (A B C : ℤ) :
  ‖polynomialCompleteSum 2 (by omega) (quadraticPolynomial A B C)‖ =
    if Even (A + B) then 2 else 0

theorem _root_.Polynomial.eq_quadraticPolynomial_of_natDegree_le
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2) :
  f = quadraticPolynomial (f.coeff 2) (f.coeff 1) (f.coeff 0)

theorem linear_polynomialCompleteSum_eq_zero
    (hq : 1 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  polynomialCompleteSum q (Nat.zero_lt_of_lt hq) f = 0

theorem linear_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 1)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ 1

theorem quadratic_primePower_linear_unit_eq_zero
    (hp : p.Prime) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hlinear : ¬ p ∣ Int.natAbs (f.coeff 1))
    (hquadratic : p ∣ Int.natAbs (f.coeff 2)) :
  polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f = 0

theorem quadratic_oddPrimePower_norm
    (hp : p.Prime) (hpodd : p ≠ 2) (ha : 0 < a) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ 2)
    (hquadratic : ¬ p ∣ Int.natAbs (f.coeff 2)) :
  ‖polynomialCompleteSum (p ^ a) (pow_pos hp.pos a) f‖ =
    Real.sqrt (p ^ a)

theorem quadratic_twoPower_linear_odd_eq_zero
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Odd (f.coeff 1)) :
  polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f = 0

theorem quadratic_twoPower_quadratic_odd_norm
    (ha : 2 ≤ a) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hlinear : Even (f.coeff 1)) (hquadratic : Odd (f.coeff 2)) :
  ‖polynomialCompleteSum (2 ^ a) (pow_pos (by omega) a) f‖ =
    Real.sqrt (2 * 2 ^ a)

theorem quadratic_mod_two_bound
    (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime 2 (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum 2 (by omega) f‖ ≤ 2

theorem quadratic_polynomialCompleteSum_parity_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    if Even q then Real.sqrt (2 * q) else Real.sqrt q

theorem quadratic_polynomialCompleteSum_bound
    (hq : 0 < q) (f : Polynomial ℤ) (hdegree : f.natDegree ≤ 2)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤ Real.sqrt (2 * q)
```

For degree one and `q>1`, the linear coefficient is a unit modulo every prime
factor, so additive-character orthogonality makes the sum zero.  If the phase
is constant, primitivity forces `q=1`, whose sum has norm one.

First use `Polynomial.ext` and `coeff_eq_zero_of_natDegree_lt` to prove
`eq_quadraticPolynomial_of_natDegree_le`; thus no higher coefficient remains
implicit.  For an odd prime, the pinned Mathlib field Gauss theorem is used
only for the base `G_1(A)` over `ZMod p`, where it gives norm `sqrt p`.
Prime powers are proved internally.  For `n=a+2`, write each residue uniquely
as `x=y+p^(n-1)z`.  Character orthogonality in `z` forces `p|y` because `2A`
is a p-unit.  Reindex `y=p*y'`; the resulting phase has modulus `p^(n-2)` and
`y'` runs exactly modulo `p^(n-2)`, while the surviving inner `z` sum contributes
the scalar `p`.  This gives exactly `G_(a+2)(A)=p*G_a(A)`.  Together with
`G_0(A)=1`, the even and odd exponent
recurrences give norm `sqrt(p^a)`.  To remove the linear term, choose `h`
with `2*A*h=B mod p^a`; translation by `h` changes only the constant phase,
whose norm is one.

At the 2-primary factor, an odd linear coefficient cancels under the
fixed-point-free shift `x |-> x+2^(a-1)` for every `a>=2`.  If `B` is even and
`A` odd, solve `A*h=B/2 mod 2^(a-1)` and complete the square modulo `2^a`.
For the pure sum, put `n=a+2>=4` and split residues into even and odd blocks.
The even block, after `x=2y`, is two copies of `G_(n-2)(A)`.  On the odd block,
pair `x` with `x+2^(n-2)`: the square difference is congruent to `2^(n-1)`
modulo `2^n`, so odd `A` changes the character by `-1` and the block cancels.
This proves `G_(a+2)(A)=2*G_a(A)`.  Direct enumeration gives
`G_2(A)=2*(1+i^A)`, of norm `sqrt 8`, and
`G_3(A)=4*exp(2*pi*i*A/8)`, of norm `4`.

At modulus two, direct enumeration gives norm `2` exactly when `A+B` is even
and zero otherwise; this includes the case in which both coefficients are
odd.  Finally apply `CompleteSumFactorizationData` to the quadratic polynomial.
Its factors are enumerated by `p : FactorizationPrimeSupport q`; rewrite that
subtype product with `factorizationPrimeSupport_prod_eq`.  Every odd-primary
norm is `sqrt(p^a)`, while the unique possible 2-primary factor contributes
either zero or at most `sqrt(2*2^a)`.  The named parity bound records the
resulting CRT product: it is `sqrt q` for odd `q` and `sqrt(2*q)` for even
`q`.  At `q=1` the support-indexed family and product are uniquely empty.  The
terminal quadratic theorem follows by monotonicity of `Real.sqrt`, so the
extra `sqrt 2` cannot accidentally be multiplied once per prime factor.
The two composite-modulus declarations
`quadratic_polynomialCompleteSum_parity_bound` and
`quadratic_polynomialCompleteSum_bound` are consequently owned by
`CompleteExponentialSum`, the first module importing both the local quadratic
branch and Chen's support-indexed factorization certificate.  All preceding
prime-power and local quadratic declarations remain in
`QuadraticCompleteSum`.

## 10. Effective global constant and actual-degree padding

```lean
def stechkinNatConstant (d : ℕ) : ℕ :=
  2 ^ (10 * (d + 1) ^ 8)

theorem chenLocalFactor_le (d p : ℕ) (hd : 3 ≤ d) :
  chenLocalFactor d p ≤ d ^ 2

theorem chenExceptionalPrimes_card_le (d : ℕ) :
  (chenExceptionalPrimes d).card ≤ (d + 1) ^ 6

theorem chenGlobalFactor_le_degreePow (d : ℕ) (hd : 3 ≤ d) :
  chenGlobalFactor d ≤
    ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6)

theorem nat_le_two_pow (d : ℕ) : d ≤ 2 ^ d

theorem chenMajorant_exponent_le (d : ℕ) :
  2 * d * (d + 1) ^ 6 ≤ 10 * (d + 1) ^ 8

theorem chenDegreePow_le_natConstant (d : ℕ) :
  (d ^ 2) ^ ((d + 1) ^ 6) ≤ stechkinNatConstant d

theorem chenDegreePow_cast (d : ℕ) :
  ((((d ^ 2) ^ ((d + 1) ^ 6) : ℕ) : ℝ)) =
    ((d : ℝ) ^ 2) ^ ((d + 1) ^ 6)

theorem chenGlobalFactor_le_stechkinNatConstant
    (d : ℕ) (hd : 3 ≤ d) :
  chenGlobalFactor d ≤ stechkinNatConstant d

theorem stechkinNatConstant_mono {e d : ℕ} (hed : e ≤ d) :
  stechkinNatConstant e ≤ stechkinNatConstant d

theorem polynomialCompleteSum_effective
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d)

theorem polynomialCompleteSum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d q : ℕ) (hd : 0 < d) (hq : 0 < q) (f : Polynomial ℤ)
    (hdegree : f.natDegree ≤ d)
    (hprimitive : Nat.Coprime q (Polynomial.nonconstantContentNat f)) :
  ‖polynomialCompleteSum q hq f‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow q (1 - (1 : ℝ) / d)

theorem integral_complete_exponential_sum_effective
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d)

theorem integral_complete_exponential_sum_effective_of_primeBound
    (hWeil : PolynomialPrimeSumBound)
    (d : ℕ) (hd : 0 < d) (A : IntegralPolynomialPhase d)
    (hprimitive : A.Primitive) :
  ‖integralCompleteSum A‖ ≤
    (stechkinNatConstant d : ℝ) *
      Real.rpow A.modulus (1 - (1 : ℝ) / d)
```

Here is the executable domination chain.  For `d>=3`, positivity of `d-2`
and field normalization reduce
`(2*d)/(d-2)<=6` to `12<=4*d`.  Monotonicity of `Real.rpow` then gives
`A_d<=(d-1)^6<=(d+1)^6`, proving the threshold theorem used already in
Section 8.  Filtering the range and deleting the nonprimes `0,1` gives
`card (chenExceptionalPrimes d)<=(d+1)^6`.  Each of the four branches of
`chenLocalFactor` is between one and `d^2`: use `d>=3`, the nonnegative rpow
exponents `2/d` and `3/d`, and `d^(3/d)<=d`.

Finite-product monotonicity now yields
`chenGlobalFactor d <= (d^2)^N`, where `N=(d+1)^6`; missing factors are padded
by one.  The elementary induction `d<=2^d` gives

`(d^2)^N <= ((2^d)^2)^N = 2^(2*d*N)`.

Finally `2*d*(d+1)^6 <= 10*(d+1)^8` follows after factoring the positive
`(d+1)^6` from `2*d <= 10*(d+1)^2`.  Monotonicity of `Nat.pow` therefore gives
`(d^2)^N <= 2^(10*(d+1)^8)=stechkinNatConstant d`.
`chenDegreePow_cast` is proved by repeated `Nat.cast_pow` and is used before
transitivity with the real product estimate.  Thus no informal coercion from
natural powers to `Real.rpow` is left in the final constant theorem; all rpow
appears earlier only in the local-factor inequalities.

For padding, let `e=f.natDegree`.

- If `e=0`, `nonconstantContentNat f=0`, so `Nat.Coprime q 0` forces `q=1`.
- If `e=1`, use the linear theorem.
- If `e=2`, use the quadratic theorem, including even `q`.
- If `3<=e`, use `ack_theorem_2_2_finiteProduct` at the actual degree.

Since `e<=d`, monotonicity of the natural constant and, for `q>=1`,

`q^(1-1/e) <= q^(1-1/d)`

give the padded exponent.  Finally apply the exact `IntegralPolynomialPhase`
evaluation, content, and enumeration bridges.  The final constant is chosen
from `d` before the phase or modulus, so it is a genuine uniform
Greenfeld--Tao `O_d` estimate.

## 11. Proof order and audit obligations

The implementation order is forced by the recurrence:

1. finite cyclic enumeration and `IntegralPolynomialPhase.toPolynomial`;
2. content, coefficient division, and scalar-content lemmas;
3. roots/multiplicities and Lemmas 2.2--2.4;
4. (2.3)--(2.5) with exact finite reindexings;
5. prime base from the fixed-character Weil theorem;
6. the `p>d` strong induction and (2.6)--(2.12);
7. the `p<=d` `t`-block induction and (2.13)--(2.14);
8. Theorem 2.1, CRT, and the finite-product Theorem 2.2;
9. linear, odd-prime quadratic, and all 2-adic quadratic branches;
10. actual-degree padding and the integral-phase transfer.

Required regression examples include:

- `d=3`, where `A_d=64`, to verify the strict first endpoint;
- a phase whose top integer coefficient is divisible by `p` but another
  coefficient is a p-unit;
- `q=1` and a constant phase;
- linear phases at composite `q`;
- quadratic phases modulo `2`, `4`, `8`, an odd prime power, and a mixed even
  modulus;
- a zero-padded degree-two polynomial consumed at an advertised degree
  `d>2`;
- direct comparison of the integer range sum and the `ZMod` sum.

The terminal audit runs `lake env lean` on all five modules, rejects every
`sorry`, `axiom`, `admit`, or declaration with unexpected axioms, and prints
the axioms of `primePower_completeSum_bound`,
`ack_theorem_2_2_finiteProduct`, `quadratic_polynomialCompleteSum_bound`,
`polynomialCompleteSum_effective`, and
`integral_complete_exponential_sum_effective`.  The only allowed axioms are
Lean's standard logical foundations and the explicitly audited fixed-character
Weil theorem's already formalized dependency chain.

## 12. Primary-source anchors and remaining assumptions

| Formal block | Exact A--C--K anchor | Formalization note |
|---|---|---|
| CRT splitting | Lemma 2.1, printed p. 49 | Bezout-unit form, valid with a constant term |
| multiplicity descent | Lemma 2.2, pp. 49--50 | fixes `m>=u`; root multiplicity is counted |
| translated content | Lemma 2.3, p. 50 | gives `1<=sigma<=d` |
| convexity | Lemma 2.4, pp. 50--51 | finite merge proof of the same maximum |
| prime base and class split | Theorem 2.1, pp. 51--52, (2.3)--(2.5) | Weil base plus exact residue enumeration |
| third large-prime range | pp. 53--54, (2.6)--(2.12) | early/late root split with all endpoints |
| small-prime block | pp. 54--55, (2.13)--(2.14) | `t=v_p(content(f'))`, Lemma 2.2 controls child mass |
| global product | Theorem 2.2, pp. 55--56, its first displayed `D` bound | retains the exact finite product; omits only the unused decimal relaxation |

The source assumes `d>=3`; hence the `d=1` and `d=2` sections are necessary
formal prerequisites rather than claims attributed to A--C--K Theorem 2.1.
In particular, the 2-adic statements are proved by parity shifts and the
two-step quadratic Gauss recursion.  No odd-modulus Gauss formula is silently
applied at `2`, and modulus `2` is a separate theorem.

The only provisional hypothesis is `PolynomialPrimeSumBound` on the
`_of_primeBound` declarations.  Chapter 05a discharges it with its
fixed-character Weil theorem before the unsuffixed declarations are exported.
The small-prime root-mass inequalities, the full quadratic `2^a` analysis,
the inequality `1<=chenLocalFactor`, and domination of the global finite
product by `stechkinNatConstant` are project theorems in this chapter, not
remaining assumptions.  The printed prime-counting estimate
`pi(x)<=1.25*x/log x` is deliberately absent because it is used only to
replace the exact finite product by decimal constants that have no consumer.
Thus there is no hidden analytic-number-theory assumption in the final
Greenfeld--Tao bound.

```lean
end TranslationalTilings
```
