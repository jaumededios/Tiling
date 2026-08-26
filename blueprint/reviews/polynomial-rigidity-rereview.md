# Polynomial rigidity and weak-periodicity re-review

## Snapshot and verdict

This is an independent, snapshot-specific re-review of the specification pinned
by `blueprint/SNAPSHOT.sha256`.  Running
`sha256sum -c blueprint/SNAPSHOT.sha256` succeeds for all fourteen listed
files.  The SHA-256 digest of the manifest itself is

```text
e428270de372f935f6f101fe873ecc40ee1463b45f2c113d112060ba2facd1fb
```

**Verdict: REJECT.**  The corrected snapshot fixes the earlier exponent,
quantifier, denominator-transport, higher-torsion, Fejer, and half-circle
errors.  Conditional on the claimed complete-sum theorem, the proof of Lemma
4.3 and its use in Proposition 4.4 are now mathematically sound.  However, the
two deepest inputs to Lemma 4.2 are still not recursively blueprinted:

1. the six-line Artin--Schreier outline moves the full Weil theorem for curves
   into unstated prerequisites, and does not even specify the character
   `L`-factor needed to isolate the displayed one-character sum;
2. the proposed stationary-phase route retains an unbounded
   polynomial-dependent valuation `delta`, but never proves the uniform Chen
   recurrence that removes it and yields the four displayed degree-only
   factors.

There is also no specified bridge from `IntegralPolynomialPhase` to the
`Polynomial Z` complete sum on which CRT and the local theorems operate, and
the Chapter 6 version of Proposition 4.4 uses `Q_|F|` rather than the paper's
`Q_m`.  These are unresolved P1 findings, so this snapshot cannot pass the
pre-implementation gate.

The verdict concerns this identified snapshot only.  It does not assert that
the Weil or Chen--Stechkin estimates are false; it asserts that the blueprint
does not yet contain the mathematics needed to prove them without a new axiom,
`sorry`, or a theorem-sized opaque certificate.

## Scope and source comparison

I compared Chapter 5, all of Chapter 6, the paper-facing aliases in Chapter 9,
the recursive dependency audit, the comparator, the resolution log, and the
signature validators.  I also checked the paper directly at pages 15--17:

- Lemma 4.2 has the exact gain `Q^(1-1/d)` and a constant depending only on
  `d`;
- Lemma 4.3 only needs a degree/interval-dependent period;
- Proposition 4.4 states a period `Q_m M^2 N q h_j`, with `Q_m` depending only
  on the number `m` of directions.

For the local four-case constant I compared the statement to
Arkhipov--Chubarikov--Karatsuba, Chapter 2, Theorem 2.1.  Its four factors and
two thresholds agree with `chenLocalFactor` for degree at least three.  This
agreement of theorem statements does not supply the missing proof recursion.

The audit followed the adversarial clean-room rule: a true theorem cited in
prose is not a completed recursive blueprint when Mathlib does not contain it;
the hard argument may not be hidden in a curve-zeta theorem, a splitting-field
choice, a valuation `delta`, or a proof-only branch certificate.

## Blocking findings

### RP1 - P1: the Weil prime bound is replaced by an unstated curve-RH development

**Risk.**  `polynomial_addChar_sum_prime` is the large-prime base case of the
prime-power recursion.  Mathlib does not currently supply this polynomial
additive-character Weil bound or the algebraic-curve machinery described in
the proof plan.  As written, implementation must either introduce the desired
result as a black box or invent a major prerequisite development after the
blueprint gate.  Either outcome violates the requested recursive,
sorry-free specification.

**Location and evidence.**  Chapter 5, lines 533--564, states

```lean
theorem polynomial_addChar_sum_prime
    [NeZero p] (hp : p.Prime) (f : Polynomial (ZMod p))
    (hnonconst : 0 < f.natDegree)
    (hsmall : f.natDegree < p) :
  norm (sum x : ZMod p, ZMod.stdAddChar (f.eval x)) <=
    (f.natDegree - 1 : Real) * Real.sqrt p
```

and then gives only six prose bullets: construct an Artin--Schreier curve,
count points over extensions, formalize its zeta numerator and functional
equation, prove the root bound from intersection-pairing positivity, and
deduce the estimate.  None of the following required objects or results is
defined or stated in Lean:

- the smooth projective model and its points over every finite extension;
- Frobenius and the curve zeta function;
- divisors, the required pairing, and the positivity theorem;
- the Artin--Schreier `L`-function for a fixed nontrivial additive character;
- the trace identity for that `L`-function;
- its degree `deg f - 1` and the absolute-value bound for every reciprocal
  root.

There is also a concrete logical gap in the six bullets.  The zeta numerator
of `Y^p-Y=f(X)` contains the factors for all `p-1` nontrivial additive
characters.  A point count for the whole curve controls their aggregate.  To
obtain `(deg f-1)*sqrt p` for the single character `ZMod.stdAddChar`, one must
factor the zeta numerator into the character `L`-factors and identify the
roots of the selected factor.  That decomposition is not mentioned.  Merely
proving the curve zeta numerator has degree `2g=(p-1)(deg f-1)` would otherwise
give the wrong factor.

A direct search of the pinned Mathlib tree finds only an Artin--Schreier
reference in Kummer-extension prose, not a theorem that subsumes this result.
This agrees with Chapter 5's own reuse audit at lines 54--62.

**Concrete repair.**  Either use an actually existing pinned-Mathlib theorem
with its exact declaration and adapter, or expand
`PolynomialCongruence.lean` into a genuine prerequisite blueprint.  A minimal
usable API for the proposed route includes statements of the following shape
(names may change):

```lean
def artinSchreierLPolynomial
    (psi : AddChar (ZMod p) Circle) (f : Polynomial (ZMod p)) :
    Polynomial Complex

theorem artinSchreierLPolynomial_degree
    (hpsi : psi.Nontrivial) (hf : 0 < f.natDegree)
    (hprimeToP : f.natDegree < p) :
  (artinSchreierLPolynomial psi f).natDegree = f.natDegree - 1

theorem artinSchreierLPolynomial_trace
    (hpsi : psi.Nontrivial) (hf : 0 < f.natDegree)
    (hprimeToP : f.natDegree < p) :
  -((artinSchreierLPolynomial psi f).coeff 1) =
    sum x : ZMod p, psi (f.eval x)

theorem artinSchreierLPolynomial_reciprocalRoot_norm
    (hpsi : psi.Nontrivial) (hf : 0 < f.natDegree)
    (hprimeToP : f.natDegree < p) :
  forall alpha, IsReciprocalRoot (artinSchreierLPolynomial psi f) alpha ->
    norm alpha = Real.sqrt p
```

The blueprint must then recursively state the finite-extension point-count,
zeta-factorization, functional-equation, and pairing-positivity theorems used
to prove these declarations, with module homes and the needed definitions.
Alternatively, choose a fully specified elementary proof of the exact prime
bound.  The current instruction to formalize Weil's RH for this family after
approval is not a bounded Lean proof plan.

**Disposition.**  Unresolved in the inspected snapshot.

### RP2 - P1: the stationary-phase outline does not imply the uniform Chen factor

**Risk.**  The final local theorem has a constant depending only on `d` and
`p`, but the displayed branch invariant contains an additional quantity
`delta` depending on arbitrarily close roots of `f'`.  No lemma removes that
dependence.  Consequently the stated recursion does not prove
`primePower_completeSum_bound`, and hence does not prove the exact uniform
Lemma 4.2.

**Location and evidence.**  Chapter 5, lines 568--588, introduces the branch
bound

```text
2*scale + derivativeValuation <= step*(e+1)+delta,
```

where `delta` is a maximum valuation of nonzero derivative values at complex
roots.  Lines 590--616 then jump directly to the four values of
`chenLocalFactor`, none of which contains `delta`.  No summation lemma,
separation lemma, or induction invariant relating this polynomial-dependent
quantity to a degree-only constant is stated.

The dependence cannot be dismissed by a uniform bound on `delta`.  Fix a
prime `p>3` and let

```text
f_M(X) = 2 X^3 - 3 p^M X^2.
```

Its nonconstant content is `gcd(2,3p^M)=1`, so it satisfies the proposed local
primitivity hypothesis.  But

```text
f'_M(X) = 6 X (X-p^M).
```

The two complex roots are simple, while
`f''_M(0)=-6p^M` and `f''_M(p^M)=6p^M`; their `p`-adic valuations are `M`.
Thus the `delta` described at lines 584--585 is unbounded even in fixed degree
three among primitive polynomials.  A Loxton--Vaughan-style closest-root
estimate with this invariant does not by itself yield Chen's degree-only
factor.  The uniform theorem remains true, but it requires the separate Chen
induction that sums derivative-root residue classes without retaining this
root-separation constant.

The four-case formula itself is correctly transcribed: for `d>=3` the factors
are `1`, `d^(2/d)`, `d^(3/d)`, and `(d-1)d^(3/d)` at the two displayed
thresholds and the split `p>d`.  The blocker is the absent argument connecting
the proof-local recursion to that formula.

**Concrete repair.**  Replace the hybrid `delta` outline by the actual Chen
recurrence from Arkhipov--Chubarikov--Karatsuba, and state every invariant used
by the induction.  At minimum the blueprint must include:

- the normalized derivative/root residue classes at modulus `p` and the exact
  Taylor decomposition of the complete sum over those classes;
- the vanishing lemma for nonstationary first digits;
- the root-multiplicity/cardinality inequality used when stationary branches
  are summed;
- the induction parameter and a recurrence whose right side contains only
  `a,d,p` and the preceding normalized sums, not an unbounded invariant of
  `f`;
- a proved solution of that recurrence in each of the four prime ranges,
  including all endpoint inequalities;
- the small-prime block expansion and its exact terminal estimate.

A satisfactory theorem boundary would be a branch-sum recurrence immediately
followed by four lemmas, one for each definition branch, whose conclusions are
exactly the corresponding `chenLocalFactor` bounds.  The counterexample above
should be retained as a regression ensuring that no alleged degree-only bound
on the closest-root `delta` enters the proof.  If the chosen route instead
uses a theorem with a discriminant or root-separation factor, then that theorem
is insufficient for the paper and must not be exported as Lemma 4.2.

**Disposition.**  Unresolved in the inspected snapshot.

### RP3 - P1: the local-to-global proof and low-degree cases are only asserted

**Risk.**  Even granting RP1 and RP2, the explicit global natural constant does
not yet follow from any stated recursion.  The blueprint omits the theorems for
degrees one and two, the CRT factorization over all prime powers, preservation
of local primitivity under CRT units, the exceptional-prime product estimate,
and padded-degree transport.  These omissions sit directly on the only route
to `integral_complete_exponential_sum_effective`.

**Location and evidence.**  Chapter 5, lines 617--632, handles degree one,
degree two, arbitrary prime factorization, the product of local constants, and
actual degree `e<d` in two prose paragraphs.  The next displayed declaration,
at lines 635--640, is already the final integral estimate.  There are no
intermediate Lean statements.

The numerical majorant is plausible once all local estimates exist: for
`d>=3`, factors are one above the large threshold; that threshold is at most
`(d+1)^6`; each exceptional factor is at most `d^2`; and the deliberately huge
`2^(10(d+1)^8)` can dominate the product.  This numerical observation is not a
replacement for the missing finite-product theorem.  In degree two, the
phrase "complete the square; split even moduli into parity classes" also hides
the exact 2-adic recurrence needed to prove the claimed `sqrt(2q)` bound from
Mathlib's prime Gauss-sum results.

**Concrete repair.**  State and prove at least the following internal API:

```lean
theorem linear_completeSum_bound ...
theorem quadratic_primePower_completeSum_bound ...
theorem quadratic_completeSum_bound ...
theorem primitive_of_crt_unit_mul ...
theorem polynomialCompleteSum_primeFactorization ...
theorem chenLocalFactor_le_degreeSquare ...
theorem exceptionalPrime_product_le_stechkinNatConstant ...
theorem stechkinNatConstant_mono ...
theorem completeSum_bound_of_actualDegree_le ...
```

The prime-factorization theorem must specify the exact polynomials produced by
the repeated Bezout scalings, so that every local use of RP2 receives a proof
of content-primitivity.  The degree-padding lemma must explicitly cover the
zero polynomial/modulus-one case before applying the monotonicity
`q^(1-1/e) <= q^(1-1/d)`.

**Disposition.**  Unresolved in the inspected snapshot.

### RP4 - P1: no bridge connects `IntegralPolynomialPhase` to `polynomialCompleteSum`

**Risk.**  Normalization produces an `IntegralPolynomialPhase`, whereas CRT
and both local estimates consume `Polynomial Z`.  Without a conversion and a
sum-equivalence theorem, the global number-theory result cannot be transferred
to `integralCompleteSum`.  This is exactly the kind of representation gap that
usually becomes a late Lean blocker (coefficient indexing, residue
enumeration, character convention, content, and degree all have to agree).

**Location and evidence.**  Chapter 5 defines `IntegralPolynomialPhase` and
`evalNumerator` at lines 159--185.  It proves circle normalization at lines
449--489.  Section 5.1 separately defines `polynomialCompleteSum` at lines
505--524.  No definition maps the coefficient vector to `Polynomial Z`, and a
search of the chapter finds no theorem relating `integralCompleteSum` to
`polynomialCompleteSum`.  Nevertheless, Section 5.4 jumps to the final
integral estimate at lines 635--640.

The missing bridge has four non-definitional obligations:

1. `Fin d` index `i` must become the coefficient of `X^(i+1)`;
2. the representatives `1,...,q` must be shown to enumerate `ZMod q` exactly
   once;
3. `circlePhase (evalNumerator n/q)` must be reconciled with
   `ZMod.stdAddChar`, including the chosen sign convention;
4. `IntegralPolynomialPhase.Primitive` must imply coprimality of the modulus
   with the nonconstant polynomial content used by every local factor.

**Concrete repair.**  Add an explicit conversion and its characteristic
lemmas before Section 5.1, for example:

```lean
def IntegralPolynomialPhase.toPolynomial
    (A : IntegralPolynomialPhase d) : Polynomial Z :=
  sum i, Polynomial.monomial ((i : Nat) + 1) (A.coeff i)

theorem IntegralPolynomialPhase.eval_toPolynomial ...
theorem IntegralPolynomialPhase.content_toPolynomial ...
theorem IntegralPolynomialPhase.primitive_toPolynomial ...
theorem IntegralPolynomialPhase.natDegree_toPolynomial_le ...

theorem norm_integralCompleteSum_eq_polynomialCompleteSum
    (A : IntegralPolynomialPhase d) :
  norm (integralCompleteSum A) =
    norm (polynomialCompleteSum A.modulus A.modulus_pos A.toPolynomial)
```

If the two character conventions agree definitionally after coercions, an
equality rather than norm equality is preferable.  Either way, separately
state the `Finset.Icc 1 q`/`ZMod q` bijection and the character-evaluation
lemma.  The global proof should then visibly compose RP3 with these bridges.

**Disposition.**  Unresolved in the inspected snapshot.

### RP5 - P1: Proposition 4.4 has the wrong uniform dependence (`Q_|F|` instead of `Q_m`)

**Risk.**  The current theorem is sufficient for Theorem 1.4, whose hidden
constants may depend on `|F|`, but it is not the exact paper Proposition 4.4
exported by Chapter 9 and claimed exact in the comparator.  Two tiles with the
same number `m` of directions but different cardinalities can receive
different advertised rigidity factors.  Thus the theorem statement does not
express that `Q_m` depends only on `m`.

**Location and evidence.**  The paper states on page 16 that the coset period
is `Q_m M^2 N q h_j`, "where `Q_m` depends only on `m`."  In the blueprint:

- Chapter 6, lines 105--107, sets `Q = weakRigidityPeriod c` for `c=|F|`;
- lines 116--117 define the parameter as `tileCard`;
- lines 164--167 bake `weakRigidityPeriod F.card` into `weakMultiplier`;
- lines 391--396 use that multiplier in `coset_one_dimensional_periodicity`;
- Chapter 9 line 147 aliases this theorem as `proposition_4_4`;
- the comparator, lines 52 and 68--70, calls the result exact.

The proof itself only requires degrees at most `m-2`, so dependence on
`F.card` is unnecessary at this stage.

**Concrete repair.**  Separate the exact proposition factor from its
cardinality-only majorant.  For example:

```lean
def propositionRigidityPeriod (m : Nat) : Nat :=
  (Finset.range (m + 1)).lcm universalRigidityPeriod

def weakRigidityPeriodCap (tileCard : Nat) : Nat :=
  (Finset.range (tileCard + 1)).lcm propositionRigidityPeriod
```

Use `propositionRigidityPeriod m` in `weakMultiplier`,
`WeakArithmeticData`, and `coset_one_dimensional_periodicity`, where `m` is the
domain size of `h`.  Prove its positivity and that it is a common multiple of
all degree-`<=m-2` rigidity periods.  Then use `m<=F.card-1` to prove the actual
multiplier is bounded by a closed constant containing
`weakRigidityPeriodCap F.card`.  This preserves all Chapter 6--8 quantitative
bounds while restoring the exact Proposition 4.4 dependence.

**Disposition.**  Unresolved in the inspected snapshot.

## Nonblocking findings requiring cleanup

### RP6 - P2: the signature validator is stale and does not validate the corrected composition

**Risk.**  The comparator presents the compiled validator as evidence that the
corrected displayed declarations elaborate.  The current file instead mixes
old theorem interfaces with independent stubs, so that evidence cannot be used
for this snapshot's acceptance gate.

**Location and evidence.**  `blueprint/COMPARATOR.md:129-149` says
`tmp/BlueprintPolynomial.lean` tests the definitions and theorem types.  But
that validator still defines `localStechkinConstant` and
`paperStechkinConstant` (`tmp/BlueprintPolynomial.lean:78-100`) and validates
old `*_paper_explicit_statement` declarations using that constant
(`:220-239`).  The corrected chapter instead exports only the natural
effective constant at `blueprint/05-polynomial-rigidity.md:635-657`.  There is
no validator for the current integral effective theorem or for the missing
RP4 bridge.

Similarly, `tmp/BlueprintWeak.lean:60` replaces
`universalRigidityPeriod` by the stub constant `1`, and its Chapter 6
definitions are re-declared in a separate namespace rather than checked
against Chapter 5.  It therefore cannot expose the `Q_m`/`Q_|F|` composition
problem in RP5.  The `tmp` files are not included in `SNAPSHOT.sha256`.

**Concrete repair.**  Regenerate the validators from the corrected
declarations, validate the actual cross-module composition rather than
shadowing analytic definitions with stubs, compile them against the pinned
toolchain, and include their hashes (or generated outputs) in the reviewed
snapshot.  The comparator should list exactly which declarations each
validator covers.

**Disposition.**  Unresolved in the inspected snapshot.

### RP7 - P2: the paper's function-nonconstant hypothesis lacks an explicit bridge

**Risk.**  This does not make the complete-sum theorem weaker: a
function-nonconstant circle polynomial is necessarily
coefficient-nonconstant, so the blueprint theorem applies.  But the comparator
calls the statement exact while Chapter 5 asserts without a bridge that
`CoefficientConstant` is literally the paper's hypothesis.  Circle polynomial
representations are not unique, as the chapter itself notes with
`(n^2+n)/2 mod 1`.

**Location and evidence.**  The paper defines a polynomial as a map
`P : Z -> R/Z` and Lemma 4.2 assumes that `P` is nonconstant.  Chapter 5,
lines 85--90, deliberately distinguishes `CoefficientConstant` and
`FunctionConstant`, but line 146 calls `CoefficientConstant` the paper's
hypothesis.  Lines 147--151 then acknowledge that a nonzero coefficient vector
can induce a constant function.

**Concrete repair.**  State the bridge

```lean
theorem CirclePolynomial.functionConstant_of_coefficientConstant
    (h : P.CoefficientConstant) : P.FunctionConstant

theorem CirclePolynomial.not_coefficientConstant_of_not_functionConstant
    (h : not P.FunctionConstant) : not P.CoefficientConstant
```

and expose a literal paper-facing corollary whose hypothesis is
`not P.FunctionConstant`, while retaining the stronger coefficient-facing
theorem for the rigidity proof.  Update the comparator to say "strengthened
via the displayed bridge" rather than "exact" unless the representation is
made part of the paper-facing input.

**Disposition.**  Unresolved in the inspected snapshot.

## Components that now pass mathematical review

The following items from the prior polynomial-rigidity review are repaired in
this snapshot.  Their approval is conditional only where explicitly noted on
RP1--RP4.

### Exact exponent and uniform quantifiers

`complete_exponential_sum_paper` has exponent exactly `1-1/d`, and
`complete_exponential_sum_paper_bigO` chooses `C` before `P`.  The constant is
therefore genuinely uniform in the coefficients and denominator.  No
per-polynomial witness or certificate makes the theorem vacuous.

### Primitive normalization and denominator transport

Only positive-degree coefficients enter torsion and the common denominator.
The lcm is positive, including the empty family.  The normalization argument
is correct: if a prime divided `Q` and all chosen numerators, every coefficient
order would divide `Q/p`, contradicting minimality of the lcm.  Thus the
integer coefficient vector is primitive relative to `Q`.

The two divisibilities

```text
Q_k | Q,              Q | |k| Q_k
```

follow coefficientwise from the orders of `k*a_i`, and lcm monotonicity gives
the displayed global statements.  `normalized_completeSum_repeat` has the
right hypotheses and orientation: a `Q_k`-periodic phase averaged over a
multiple `Q` has the same normalized average.  This closes the denominator
change used in the Fejer argument.  RP4 concerns only the subsequent change of
representation to `Polynomial Z`.

### CRT

The two-factor CRT formula is normalized correctly.  A Bezout relation

```text
u1*q2 + u2*q1 = 1 mod q1*q2
```

rewrites `f/(q1*q2)` as `u1*f/q1 + u2*f/q2` modulo one.  Each `u_i` is a unit
modulo its corresponding factor, so multiplication by it preserves local
content-primitivity.  RP3 requests the stated iteration and preservation
lemmas, not a correction to this formula.

### Weyl/van der Corput/residue splitting

The higher-torsion defect from the previous snapshot is fixed.  After choosing
the largest nontorsion positive coefficient, splitting into residue classes
modulo the lcm of all higher torsion orders kills every positive-degree
contribution from those higher coefficients.  The coefficient at the selected
degree becomes a nonzero integer multiple of a nontorsion element and remains
nontorsion.  The residue averages all tend to zero and recombine correctly.

The stated van der Corput inequality is a harmlessly loose form of the usual
Cesaro estimate, and its constants suffice for the induction.  The explicit
positive bump turns avoidance into failure of equidistribution.  Hence
avoidance forces torsion of every nonconstant coefficient without placing any
condition on the constant coefficient.

### Finite-difference/Newton bridge

The falling-factorial plan now supplies the necessary circle polynomial.  A
`(d+1)`st backward difference equal to zero yields a Newton expansion; division
by factorials is available in the divisible group `AddCircle 1`; and signed
Stirling identities convert falling factorials to monomials.  The `m=1` case
in Chapter 6 is handled separately by the mod-one sum, so natural subtraction
in degree `m-2` does not create a false edge case.

### Fejer separator and rigidity algebra

The separator is `2*(1-F_N)` with its zero coefficient removed.  Its frequency
support, real-valuedness, lower bound outside the ball, and coefficient
`l1` bound are correct.  Averaging it over `Q` gives a nonzero frequency
`0<|k|<=K` with normalized sum at least `1/L`.

Conditional on the exact complete-sum theorem, the algebra is exact:

```text
1/L <= C * Q_k^(-1/d)
Q_k <= (C*L)^d
Q <= |k|*Q_k <= K*(C*L)^d.
```

If `kP` becomes coefficient-constant, `Q<=|k|` is the correct separate branch
and avoids an invalid application of Lemma 4.2.

### Real-lift half-circle API

`HasHalfCircleLifts` is well typed and exactly what Proposition 4.4 supplies
for the small-supremum line functions.  Every lift in `[0,1/2]` has circle
distance at least `1/4` from `3/4`, so the radius-`1/8` avoided ball is valid.
Values and their translates in `[0,1)` that agree modulo one agree in `Real`,
which correctly transfers circle periodicity back to the real `phi` values.

### Proposition 4.4 branch logic

Apart from RP5's parameter dependence, both branches match the paper.

- If one supremum is one, the pairwise inequality and nonnegativity make every
  other function zero; the remaining function is `{0,1}`-valued, and the
  stronger `M^2 N q h_j` period lies in the lattice.
- If every supremum is below one, all but at most one line function has lifts
  in `[0,1/2]`.  Lemma 4.3 supplies their bounded periods.  The mod-one sum
  transfers a common period to the possible exception, and strict upper bounds
  by one lift circle equality to real equality.  The `Q M N q h_0` period may
  be multiplied by `M` to reach the advertised direction list.

The source's `b_i`/`b_j` typo is corrected consistently.

## Downstream sensitivity to a weaker power saving

The snapshot correctly distinguishes theorem identity from downstream
sufficiency.  If one had only

```text
norm S(P,Q) <= C_d * Q^(1-delta_d),    delta_d > 0,
```

the Fejer argument would give

```text
Q_k <= (C_d*L)^(1/delta_d)
```

instead of `(C_d*L)^d`.  This remains a function only of degree and the
avoided interval.  In Chapters 6--8 the resulting universal period occurs only
inside constants depending on `|F|`; the printed powers of the diameter and
`ell` would not change.  Therefore a weaker uniform power saving would still
close Theorems 1.3--1.5 and the finite-search cap after redefining the hidden
cardinality functions.

It would **not** prove the paper's labelled Lemma 4.2 and must not be aliased as
such.  The corrected snapshot no longer makes that substitution: its public
statement keeps the exact exponent.  RP1--RP4 explain why the planned proof of
that exact statement is still incomplete.

## Cross-chapter statement audit

| Consumer | Result of audit |
|---|---|
| Chapter 6, Proposition 4.1(ii) | Degree `m-2`, including `m=1`, agrees with the finite-difference bridge. |
| Chapter 6, Proposition 4.4 proof | Correctly consumes half-circle rigidity and universal-period divisibility. |
| Chapter 6, quantitative weak periodicity | The `q/ell` quotient is exact; the `Q*M^2*N*(q/ell)` multiplier identity is correct.  Its diameter and `ell` exponents are insensitive to the analytic constant. |
| Chapter 9, `lemma_4_2` and `lemma_4_2_bigO` | Signatures retain exact exponent and uniformity, but proofs remain blocked by RP1--RP4. |
| Chapter 9, `lemma_4_3` | Correct metric-ball formulation and effective bound, conditional on Lemma 4.2. |
| Chapter 9, `proposition_4_4` | Mismatched dependence: alias points to a `Q_|F|` theorem rather than the paper's `Q_m`; see RP5. |
| Chapters 7--8 | They need only an explicit `|F|`-dependent cap, so RP5's stronger exactness repair can be bounded by the existing cap without changing their exponents or algorithms. |
| Comparator | Analytic theorem claims are accurate at the statement level; its "exact Proposition 4.4" and validator claims require RP5 and RP6 repairs. |

## Minimum acceptance gate for the next snapshot

1. Replace the six-bullet Weil outline by a recursively complete fixed-character
   `L`-function/curve development, or by another fully specified proof of the
   exact prime bound.
2. Replace the unclosed `delta` route by the actual uniform Chen recurrence and
   prove all four local cases with their endpoints.
3. State the degree-one, degree-two, prime-factorization, exceptional-factor,
   constant-majorization, and padded-degree lemmas used by the global theorem.
4. Add and validate the `IntegralPolynomialPhase.toPolynomial` conversion,
   character/enumeration equality, content-primitivity, and degree bridges.
5. Restore `Q_m` dependence in Proposition 4.4 and use a separate
   `|F|`-dependent cap only for later quantitative bounds.
6. Regenerate integrated signature validators for the corrected API and record
   the coefficient-/function-nonconstant bridge in the paper-facing crosswalk.

Until items 1--5 are completed, the blueprint does not meet the requested
mathematical completeness or sorry-free Lean-formalization standard.
