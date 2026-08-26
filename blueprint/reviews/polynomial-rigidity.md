# Independent audit: polynomial rigidity and its weak-periodicity consumers

## Scope and snapshot

This review covers all of `blueprint/05-polynomial-rigidity.md` and every use of
that chapter in `blueprint/06-weak-periodicity.md`.  It compares the proposed
API and proof graph with Lemmas 4.2 and 4.3 and Propositions 4.1 and 4.4 of
Greenfeld--Tao, arXiv:2010.03254v3.

The directory is not a Git repository and contains no Lean source or Lake
project, so the review snapshot is the unversioned Markdown tree present on
2026-08-24.  The inventory script consequently found no Lean declarations.
Exact Mathlib checks below were made against the available v4.33.0 checkout in
the neighboring `2026-08-14/Tiling` workspace.

Priority meanings are those of the library-review rubric: P0 is a logical or
specification-integrity failure, P1 blocks the planned proof, P2 is a bounded
API/maintenance correction, and P3 is low-impact.

The audit also uses an adversarial clean-room standard: prose claims receive no
credit unless their quantifiers and uniform dependencies can be reconstructed
from the displayed API; existential structures do not count as algorithms;
and every plausible edge case is tested against a concrete polynomial (degree
zero, padded degree, torsion above an irrational coefficient, collapsed
denominator after multiplying by a character, and coefficient-wise
nonconstant data representing a constant function).

## Executive verdict

**Verdict: reject the two chapters as an implementation blueprint in their
current form.**  The central mathematical implication needed downstream is
sound: *any explicit complete-sum power saving depending only on the degree
gives a uniform period bound, and the weaker exponent leaves every printed
diameter exponent in the tiling theorems unchanged*.  However, the current
blueprint cannot yet support a sorry-free implementation, for four independent
reasons:

1. its `IsRational` conclusion is false because it includes the constant
   coefficient;
2. the proposed complete-sum recursion does not establish its displayed bound;
3. several indispensable denominator and repeated-period bridges are absent;
4. the half-circle statement and several displayed definitions do not elaborate
   as Lean.

In addition, the README promises every labelled result of the paper, whereas
the proposed `lemma_4_2` alias has a strictly weaker exponent.  That weaker
lemma is sufficient for Lemma 4.3 and all subsequent tiling results, but it is
not a formalization of the paper's Lemma 4.2.

## Dependency map reconstructed by the review

```text
Proposition 4.1(ii)
  -> iterated-difference-to-circle-polynomial representation
  -> polynomial sequence avoids a fixed open arc
      -> Weyl criterion on AddCircle
      -> polynomial equidistribution with a non-torsion coefficient
      -> all nonconstant coefficients have finite additive order
      -> their lcm Q is a period
      -> explicit mean-zero trigonometric separator
      -> a large nonzero Fourier coefficient k
      -> denominator comparison Q versus denominator of kP
      -> complete rational exponential-sum power saving
      -> uniform bound Q <= B(d, arc)
  -> universal lcm of all periods up to B
  -> Proposition 4.4, second branch
  -> Q_m is absorbed in card-dependent constants in Theorems 1.4 and 1.5
```

Every arrow above needs an exported theorem or a named private helper.  The
present text fully identifies the intended ends of the chain but omits several
middle arrows.

## Findings

For exact-location reference, the inspected evidence is:

| Finding | Exact blueprint evidence | Principal risk | Repair location below |
|---|---|---|---|
| A1 | 05:55-68, 168-196, 214-219 | false avoidance conclusion and over-strong complete-sum hypotheses | corrected nonconstant torsion/rational predicates |
| A2 | 05:145-177 | induction silently assumes the irrational coefficient is leading | residue-class reduction before van der Corput |
| A3 | 05:205-236 | asserted recursion does not yield asserted power saving | full Stechkin or quantitative Weyl route |
| A4 | 05:285-303; 09's `lemma_4_2` alias | labelled paper theorem replaced by a weaker theorem | fix scope or prove paper exponent |
| A5 | 05:99-106, 241-260 | undefined/non-justified separator bounds | direct explicit Fejer kernel |
| A6 | 05:193-196, 277-283 | large sum is over `Q`, estimate is at `den(kP)` | divisibility, repeat-average, and constant branches |
| A7 | 05:271-274 | ordered interval used on unordered `AddCircle` | real-lift half-circle predicate |
| A8 | 06:47-51, 161-165 | cross-module representation theorem absent | public Newton/monomial conversion theorem |
| A9 | 06:80-95, 173-178 | upper-bounded periods are not yet made into one genuine real period | lcm, exception, and lift lemmas |
| A10 | 05:298-303; 06:28-30, 214-227 | possible loss of printed exponents | verified: only card-dependent constant changes |
| A11 | 05:1-18, 77-87, 121-140 | nonexistent import and duplicated Fourier work | existing AddCircle Fourier/Haar API |
| A12 | 05:62-65, 103-106, 145-148, 288-295; 06:97-112, 157-196 | complexity hidden in ellipses/certificates | close every executable definition and signature |
| A13 | 05:173-177 | “hits an open ball” is stronger than the stated continuous-test definition until proved | explicit bump and full-support Haar lemma |
| A14 | 06:80 | range/avoidance relation is verbally reversed | say “contained in one half and avoids a ball in the other” |

### A1 (P0): `IsRational` is false as the conclusion of avoidance

`CirclePolynomial.IsRational` currently quantifies over *all* coefficients.
The paper and the mathematical argument only force the **nonconstant**
coefficients to be rational.  Take a constant polynomial with an irrational
value `a : Torus` and a positive ball not containing `a`.  It avoids the ball,
but its constant coefficient is not a rational point.  Thus
`rational_coefficients_of_avoidsBall` is false as displayed.

The proposed expression

```lean
P.coeff i = (q : ℝ) • (1 : Torus)
```

is also not the rational-point embedding of `R/Z`: real scalar multiplication
does not descend through the integer lattice.  The available Mathlib API uses
the quotient coercion `((q : ℝ) : AddCircle 1)`.  In v4.33.0,
`AddCircle.addOrderOf_coe_rat` and
`AddCircle.exists_gcd_eq_one_of_isOfFinAddOrder` already give the two required
directions.

Use a predicate whose name and binders say exactly what is meant:

```lean
def CirclePolynomial.HasTorsionNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i, 0 < (i : ℕ) -> IsOfFinAddOrder (P.coeff i)

def CirclePolynomial.HasRationalNonconstantCoeffs
    (P : CirclePolynomial d) : Prop :=
  ∀ i, 0 < (i : ℕ) ->
    ∃ q : ℚ, P.coeff i = ((q : ℝ) : Torus)

theorem rational_nonconstant_coefficients_of_avoidsBall
    (P : CirclePolynomial d) (heps : 0 < eps)
    (havoid : P.AvoidsBall c eps) :
    P.HasRationalNonconstantCoeffs
```

The torsion version should be the working predicate; the rational version is a
paper-facing corollary.  The constant coefficient must never enter
`commonDenominator`.  For `d = 0` that denominator must definitionally be `1`.

### A2 (P1): the stated polynomial equidistribution theorem is true, but the proposed induction is incomplete

The theorem “a circle polynomial with at least one non-torsion nonconstant
coefficient is equidistributed” is correct in one dimension.  The explanation
“select the highest nontorsion coefficient; a nonzero shift lowers its degree”
does not prove it when higher coefficients are nonzero torsion points.  For
example, a quadratic rational coefficient survives a general difference even
when the highest irrational coefficient is linear.  The usual van der Corput
induction only applies directly when the *leading* coefficient is non-torsion.

A correct proof route is:

1. fix a nonzero character `k` and let `r` be the largest index for which
   `k • P.coeff r` is non-torsion;
2. let `H` be the lcm of the finite additive orders of all coefficients above
   `r`;
3. split the Cesaro average into the `H` residue classes `n = H*t + a`;
4. on each residue class, all positive-degree contributions from coefficients
   above `r` vanish, while the coefficient of `t^r` is `H^r • k • P.coeff r`
   and remains non-torsion;
5. apply the leading-coefficient van der Corput induction on each class and
   recombine the finitely many averages.

The missing reusable statements should be explicit:

```lean
theorem nontorsion_zsmul {a : Torus} (ha : addOrderOf a = 0)
    {k : ℤ} (hk : k != 0) : addOrderOf (k • a) = 0

theorem cesaroAverage_residue_classes ...

theorem polynomial_phase_tendsto_zero_of_leading_nontorsion ...

theorem polynomial_equidistributed_iff_exists_nontorsion
    (P : CirclePolynomial d) :
  Equidistributed (fun n : ℕ => P n) <->
    ∃ i, 0 < (i : ℕ) ∧ addOrderOf (P.coeff i) = 0
```

Only the forward implication of the displayed iff needs an extra argument:
if every nonconstant coefficient is torsion, the sequence is periodic with
finite range and hence cannot have Haar distribution.  The reverse implication
is the part needed by avoidance.

The degree-zero case must be split before invoking any positive-degree Weyl
theorem: every degree-zero sequence has period `1`, whether or not its constant
value is rational.

### A3 (P1): the complete-sum bound is plausible, but the five-step recursion given does not prove it

The displayed power saving

```text
|S(P;Q)|^(2^d) <= C_d Q^(2^d-1)
```

is weaker than Stechkin's estimate and is mathematically plausible with a
sufficiently large degree-only constant.  The proposed proof is nevertheless
not a valid derivation of it:

- after expanding `|S|^2`, a difference polynomial can be constant; for a
  nontrivial linear phase every correlation has norm `Q`, and cancellation
  between the shifts is essential;
- replacing each correlation by its norm loses precisely that cancellation;
- the exact denominator of a difference can collapse by a large gcd;
- the estimate `number of divisors <= Q`, inserted into the standard
  differencing count, consumes a full power of `Q` and does not leave the
  claimed power saving;
- no recurrence has been proved that justifies the displayed definition of
  `completeWeylConstant`.

This is a proof-architecture blocker, not a claim that no weaker power saving
exists.  One of the following complete routes must replace the current prose.

**Route 1 (faithful to the paper).**  Normalize the coefficients as

```text
P(n) = a_0 + A(n)/Q mod 1,
gcd(Q, A_1, ..., A_d) = 1,
```

prove CRT factorization of complete sums, prove the primitive prime-power
estimate, and combine the local estimates.  This is the recursive content of a
formal Stechkin proof and yields the paper's `Q^(1-1/d)` exponent.

**Route 2 (sufficient downstream).**  Prove a standard quantitative Weyl
inequality with every divisor-counting loss stated explicitly, then choose and
prove recursive functions `weylPower d` and `completeWeylConstant d` from that
inequality.  The theorem should not commit to `2^d` until the recurrence has
actually been checked.  A suitable stable API is:

```lean
def weylPower : ℕ -> ℕ
def completeWeylConstant : ℕ -> ℕ

theorem weylPower_pos (d) : 0 < weylPower d

theorem complete_exponential_sum_pow_bound
    (hd : 0 < d) (P : CirclePolynomial d)
    (htor : P.HasTorsionNonconstantCoeffs)
    (hnonconst : ∃ i, 0 < (i : ℕ) ∧ P.coeff i != 0)
    (hQ : Q = P.commonDenominator) :
  ‖completeSum P Q‖ ^ weylPower d <=
    (completeWeylConstant d : ℝ) *
      (Q : ℝ) ^ (weylPower d - 1)
```

The proof also needs a bounded “fixed divisor” branch: over a torsion target,
nonzero monomial coefficients can represent a constant function (for example
`n(n+1)/2 mod 1`).  A coefficient-based `IsConstant` is therefore not the same
as `Function.IsConstant P`.  Either state the estimate for primitive integral
phase data, or prove that this degeneracy bounds `Q` by a degree-only factorial
and absorb it into the constant.

### A4 (P0): the blueprint does not formalize the paper's labelled Lemma 4.2

The paper states a `Q^(1-1/d)` bound.  The blueprint explicitly substitutes a
weaker exponentially decaying gain, and `09-main-results.md` nevertheless
aliases that result as `lemma_4_2`.  This conflicts with the README's promise to
formalize every labelled result.

The sketched “paper form” does not fix the problem: its existential `C` occurs
after `P` and therefore may depend on the polynomial and on `Q`, making the
claim essentially vacuous.  The correct quantifier order is degree first,
constant second, then all phases:

```lean
theorem complete_exponential_sum_paper
    (d : ℕ) (hd : 0 < d) :
  ∃ C : ℝ, 0 <= C ∧
    ∀ (P : CirclePolynomial d) (Q : ℕ),
      P.HasTorsionNonconstantCoeffs ->
      (∃ i, 0 < (i : ℕ) ∧ P.coeff i != 0) ->
      Q = P.commonDenominator ->
      ‖completeSum P Q‖ <=
        C * Real.rpow Q (1 - (1 : ℝ) / d)
```

There are two acceptable scope resolutions:

- formalize Stechkin and export the theorem above; or
- explicitly narrow the project to the paper's main tiling theorems, retain the
  weaker lemma under a different name, and do not export it as `lemma_4_2`.

The second resolution is sufficient for the tiling results but not for the
user's stated “formalization of the paper” or the blueprint's own completion
standard.

### A5 (P1): the Fejer separator has no executable definition or justified bound

`separatorCoefficientBound` is used but never defined, and
`separatorDegree = ceil (32/eps)` is not derived from the tent-function Fejer
argument.  A crude Lipschitz/Fejer approximation estimate usually has a
logarithmic loss or requires an order quadratic in `eps^-1`; the stated linear
order cannot simply be asserted.

There is a shorter, completely explicit construction which avoids uniform
approximation.  For `0 < eps < 1/2`, choose the rationally computable

```text
N = max 1 ceil(1 / (2 eps^2)).
```

Let `F_N` be the Fejer kernel centered at zero and set

```text
f(x) = 2 * (1 - F_N(x-c)).
```

Then:

- the constant Fourier coefficient of `f` is zero;
- `f` is real-valued;
- its degree is `N-1`;
- the l1 norm of its nonzero Fourier coefficients is at most `2*(N-1)`;
- if `dist(x,c) >= eps`, then
  `F_N(x-c) <= 1/(4*N*eps^2) <= 1/2`, using
  `sin(pi*t) >= 2*t` on `[0,1/2]`, so `f(x) >= 1`.

This route requires finite geometric sums and elementary real sine bounds, but
not a general Fejer convergence theorem.  It also makes both
`separatorDegree` and `separatorCoefficientBound` executable rational
functions.  Mathlib v4.33.0 contains no ready-made Fejer kernel API, so these
lemmas are genuine recursive project prerequisites.

### A6 (P1): the rigidity proof omits the crucial `kP` denominator and period-average cases

After the separator pigeonhole step one obtains a nonzero integer frequency
`k`, but the current proof jumps directly to the complete-sum theorem for
`kP`.  The following facts are all necessary:

```lean
def CirclePolynomial.zsmul (k : ℤ) (P : CirclePolynomial d) :
    CirclePolynomial d := ...

theorem commonDenominator_zsmul_dvd
    (htor : P.HasTorsionNonconstantCoeffs) :
  (P.zsmul k).commonDenominator ∣ P.commonDenominator

theorem commonDenominator_dvd_natAbs_mul_zsmul
    (htor : P.HasTorsionNonconstantCoeffs) :
  P.commonDenominator ∣
    k.natAbs * (P.zsmul k).commonDenominator

theorem normalized_completeSum_eq_of_period_dvd
    (hQ' : Q' ∣ Q) (hper : (P.zsmul k).PeriodicWith Q') :
  (Q : ℂ)⁻¹ * completeSum (P.zsmul k) Q =
    (Q' : ℂ)⁻¹ * completeSum (P.zsmul k) Q'
```

In fact, under torsion hypotheses one can prove the sharper formula

```text
den(kP) = den(P) / gcd(den(P), |k|),
```

by applying `IsOfFinAddOrder.addOrderOf_nsmul` coefficientwise and then proving
the corresponding lcm identity.  The divisibility formulation above is enough
and is more robust.

There must also be a branch for `kP` having no nonzero nonconstant coefficient.
In that branch the complete-sum estimate is inapplicable, but denominator loss
immediately gives `Q <= |k|`.  In the other branch, put
`Qk = den(kP)`, replace the average over `Q` by the repeated average over `Qk`,
and apply the power saving at its **exact** denominator.

If the separator has degree at most `K`, coefficient l1 norm at most the
positive integer `L`, and the complete bound uses power `r` and constant `C`,
the final arithmetic is simply

```text
|average exp(kP)| >= 1/L
=> Qk <= C * L^r
=> Q <= |k| * Qk <= K * C * L^r.
```

Thus an honest executable definition can have the form

```lean
def rigidityPeriodBound (d : ℕ) (eps : ℚ) : ℕ :=
  if d = 0 then 1 else
    max 1 (separatorDegree eps * completeWeylConstant d *
      separatorL1NatBound eps ^ weylPower d)
```

with harmless extra factors if the proved real-to-natural rearrangement needs
them.  Until all named factors and the exact formula are present, the
blueprint's `...` is a proof-relevant gap, not merely a comparator detail.

### A7 (P1): the half-circle theorem does not elaborate and the downstream bridge is unstated

`AddCircle 1` has no canonical order, so

```lean
P n ∈ Set.Icc (0 : Torus) (1 / 2 : Torus)
```

is not a meaningful intrinsic statement.  The downstream data already provide
a real lift `linePhi` in `[0,1]`, so state the theorem using a lift:

```lean
theorem periodic_of_range_in_halfCircle
    (P : CirclePolynomial d)
    (hrange : ∀ n : ℤ, ∃ t : ℝ,
      t ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) ∧ P n = (t : Torus)) :
  ∃ Q, 0 < Q ∧ Q <= halfCirclePeriodBound d ∧ P.PeriodicWith Q
```

Alternatively define the predicate using `AddCircle.equivIco 1 0`.  The
existential-lift version is easier at the `linePhi` call site.

The bridge lemma should be named and proved once:

```lean
theorem avoidsBall_threeQuarter_of_halfCircle
    (hrange : ...) :
  P.AvoidsBall (((3 / 4 : ℝ) : Torus)) (1 / 8 : ℝ)
```

Radius `1/8` is smaller than necessary (the open ball of radius `1/4` also
works) but is mathematically valid.  The choice only changes a degree-dependent
constant downstream.

### A8 (P1): the finite-difference representation used by Proposition 4.1 is an unformalized recursive prerequisite

Chapter 06 says a “separate finite-difference representation theorem” converts
`Delta^(m-1) f = 0` into a `CirclePolynomial`, but neither chapter states this
theorem or explains its coefficient and denominator behavior.  It is a real
prerequisite because `Torus` is only an additive group and monomial
coefficients require division by factorials.

Export at least:

```lean
theorem exists_circlePolynomial_of_iteratedDifference_eq_zero
    (f : ℤ -> Torus)
    (h : ∀ n, iteratedForwardDifference (d + 1) f n = 0) :
  ∃ P : CirclePolynomial d, ∀ n, P n = f n
```

A robust proof first obtains the Newton expansion in the integer-valued
falling-factorial basis, then converts it to the monomial basis using the
divisibility of `AddCircle`.  The conversion must cover negative integers as
well as naturals.  Nonuniqueness of division introduces only factorial-torsion;
prove the bound explicitly if later denominator bounds use a selected
representation.  An alternative is to store Newton coefficients as the
primary representation and prove a separate monomial normalization theorem,
but then both the period and complete-sum statements must include the resulting
factorial loss.

This lemma is used across the module boundary and therefore is public,
contrary to the current “private helper” treatment.

### A9 (P1): `universalRigidityPeriod` is correct only after three missing uniformity lemmas

The definition

```lean
finsetLCM (Finset.Icc 1 (halfCirclePeriodBound d))
```

is the right way to turn an upper bound into one common period.  It must be
accompanied by:

```lean
theorem halfCirclePeriodBound_pos (d) : 0 < halfCirclePeriodBound d

theorem dvd_universalRigidityPeriod
    (hq0 : 0 < q) (hqB : q <= halfCirclePeriodBound d) :
  q ∣ universalRigidityPeriod d

theorem periodic_universalRigidityPeriod
    (hper : P.PeriodicWith q) (hq0 : 0 < q) (hqB : q <= ...) :
  P.PeriodicWith (universalRigidityPeriod d)
```

The positivity lemma is essential: if the upper bound were zero, `Icc 1 B` is
empty and the lcm is `1`, while no positive `q <= B` exists.

The “at most one exception” step in Proposition 4.4 also needs correction.  One
does not apply Lemma 4.3 to the exception.  First make the nonexceptional circle
polynomials periodic with the universal lcm; then

```text
sum_j P_j(n) = 0 in Torus
```

forces the exceptional summand to have the same period.  Finally use
`0 <= linePhi` and `sSup(range linePhi) < 1` to lift equality in `R/Z` to
equality in `[0,1)`.  These should be separate helpers; otherwise the coset
proof silently changes between circle-valued and real-valued periodicity.

The edge cases must be frozen in the API:

- `m = 1` is handled before invoking polynomial rigidity;
- `m = 2` gives degree `0`, hence universal period `1`;
- constant polynomials in any padded degree also use period `1`.

### A10 (P2): the weaker exponent really is sufficient for every downstream quantitative tiling bound

This part of the blueprint is correct and should be retained.  Suppose the
complete-sum theorem gives any bound

```text
|S| <= C_d Q^(1-delta_d),  delta_d > 0,
```

with effective `C_d` and `delta_d` depending only on `d`.  The separator makes
`Q <= B(d)` for the fixed half-circle, hence

```text
Q_m = lcm {1, ..., B(m-2)}
```

depends only on `m`.  In Chapter 06 it occurs only in

```text
L = Q_m M^2 N q / ell.
```

Since `m <= |F|-1`, `Q_m` is absorbed into `C_L(|F|)`.  It introduces no
factor of the diameter and no factor of `ell`.  Consequently the exponents

```text
relative index:  2(|F|-1)^2
multiplier:       |F|(|F|-1)
```

and all later polynomial/exponential complexity exponents are unchanged.
This remains true even if `B(d)` is extremely large.

The comparator should therefore say:

```text
Paper Lemma 4.2 exponent: not obtained by the weaker lemma.
Lemma 4.3 and all tiling consequences: same statements and same printed
diameter exponents; only the hidden |F|-dependent constant changes.
```

It must not say “statement equivalence of Lemma 4.2.”

### A11 (P2): use the existing AddCircle Fourier infrastructure and correct the imports

The proposed `Mathlib.NumberTheory.WeylCriterion` module does not exist in the
checked v4.33.0 Mathlib.  This is correctly described as a search target, but a
nonexistent import cannot remain in the target module block.

Mathlib already supplies more of part A than the prose acknowledges:

- `AddCircle.fourier` and `AddCircle.fourier_apply`;
- `AddCircle.span_fourier_closure_eq_top`, so the project need not rebuild
  Stone--Weierstrass;
- `AddCircle.haarAddCircle` and its probability-measure instance;
- `AddCircle.orthonormal_fourier`, including nonzero-character integral
  orthogonality;
- finite-order/rational-point lemmas in
  `Topology.Instances.AddCircle.Defs`.

Define the phase by the existing complex-valued Fourier character, for example

```lean
def circlePhase (x : Torus) : ℂ := AddCircle.fourier 1 x
```

or import `Analysis.SpecialFunctions.Complex.CircleAddChar` explicitly before
using `AddCircle.toCircle_addChar`.  `Complex.Circle` alone does not expose that
additive-character definition.

`Equidistributed` should integrate against
`AddCircle.haarAddCircle` explicitly:

```lean
def Equidistributed (u : ℕ -> Torus) : Prop :=
  ∀ f : C(Torus, ℂ),
    Filter.Tendsto
      (fun N => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (u n))
      Filter.atTop
      (nhds (∫ x, f x ∂AddCircle.haarAddCircle))
```

For period multiplication, Mathlib already has `Function.Periodic.nsmul` and
`.zsmul` in `Algebra.Ring.Periodic`.

### A12 (P1): the blueprint is not definition-complete enough to start Lean

The user's completion criterion requires every definition and public theorem
signature in Lean before implementation.  The reviewed chapters still contain
or depend on all of the following unresolved items:

- the body of `rigidityPeriodBound`;
- `separatorCoefficientBound` and a natural ceiling of it;
- `CirclePolynomial.smul`/`zsmul`;
- the full statement of `vanDerCorput_cesaro`;
- the full statement of `exponential_sum_estimate_paper_form`;
- the finite-difference representation theorem;
- the half-circle predicate;
- all `...` hypotheses in the Chapter 06 public theorems;
- executable bodies of `groupedTileDirections`, `weakPeriodIndexBound`, and
  `weakPeriodMultiplierBound`.

The placeholders in Chapter 06 are broader than the analytic audit, but the
three bound functions consume `universalRigidityPeriod`, so their exact
dependency on the corrected degree-zero and half-circle bounds must be fixed
after A5--A9 and before Lean implementation.

The clean-room risk is that the current proof-relevant structures can conceal
the hard work in certificates.  In particular, an arbitrary inhabitant of
`TrigSeparator` or an existential `CirclePolynomial` is not an executable
construction.  Acceptance requires closed constructors with proved bounds;
neither `Classical.choose` from qualitative Stone--Weierstrass nor an omitted
proof field may be used to justify the numeric period cap consumed by Chapter
06 and the algorithmic chapters.

### A13 (P1): avoidance contradicting the chosen definition of equidistribution still needs a positivity lemma

Lines 173-177 say that an equidistributed sequence hits every nonempty open
ball with positive limiting frequency.  The displayed `Equidistributed`
predicate quantifies over continuous functions, not indicators of open balls,
so this statement is not immediate.  Boundary measure is avoidable, but the
bridge must be formalized.

Use the continuous nonnegative bump

```text
g(x) = max(0, eps - dist(x,c)).
```

It vanishes outside `Metric.ball c eps` and satisfies `g(c)=eps>0`.  Prove that
normalized Haar measure on `AddCircle 1` has full support, hence the integral of
this nonzero nonnegative continuous function is positive.  If `P` avoids the
ball, every Cesaro average of `g(P(n))` is zero, contradicting
equidistribution.  A suitable reusable interface is:

```lean
theorem equidistributed_hits_open
    (hu : Equidistributed u) (hU : IsOpen U) (hne : U.Nonempty) :
  ∃ n : ℕ, u n ∈ U

theorem not_equidistributed_of_avoidsBall
    (heps : 0 < eps) (havoid : ∀ n, u n ∉ Metric.ball c eps) :
  ¬ Equidistributed u
```

Only the second theorem is needed, and proving it directly with the bump is
smaller than developing limiting frequencies of Borel sets.

### A14 (P2): Chapter 06 reverses “contained in a half-circle” and “avoids an interval”

Line 80 says that the `P_j mod 1` “avoid the fixed half-circle.”  The preceding
supremum argument shows instead that their real lifts lie in `[0,1/2]`; they
are **contained** in that half-circle and avoid an open ball in the
complementary half.  The later intended call to
`periodic_of_range_in_halfCircle` has the correct direction, so this is prose
rather than a false downstream theorem, but it is exactly the kind of reversal
that can produce a wrong Lean hypothesis when the ellipses are filled.

Replace the sentence by:

```text
all but at most one circle-valued P_j have real lifts in [0,1/2], hence avoid
the ball centered at 3/4 of radius 1/8.
```

## Corrected rigidity proof, end to end

After resolving the findings, the shortest sound proof of the result consumed
by Proposition 4.4 is the following.

1. If `d = 0` or all nonconstant coefficients vanish, use period `1`.
2. Otherwise, avoidance contradicts equidistribution, so every nonconstant
   coefficient has finite additive order.
3. Let `Q` be their lcm.  Prove `0 < Q` and expand `(n+Q)^i-n^i` to show that
   `Q` is a period.
4. Average the explicit mean-zero separator over `1,...,Q`.
5. Since its value is at least `1` on the range of `P`, find
   `k != 0`, `|k| <= K`, with normalized character sum at least `1/L`.
6. Put `Qk = den(kP)`.  Prove `Qk | Q` and `Q | |k| Qk`; replace the average
   over `Q` by the average over `Qk`.
7. If `kP` has no nonzero nonconstant coefficient, conclude `Q <= |k| <= K`.
8. Otherwise apply the proved complete-sum power saving to `kP` at `Qk` and
   conclude `Q <= K C_d L^r`.
9. Package the maximum of the constant and nonconstant branches as the explicit
   positive `rigidityPeriodBound`.
10. For the Chapter 06 half-circle application, use center `3/4`, radius `1/8`,
    and take the lcm of every positive integer up to that bound.

No asymptotic statement is needed after step 2; all later arguments are finite
and executable.

## Rubric closure notes

- **Mathematical intent:** blocked by A1, A3, A4, and A13.
- **Reusable seams:** the finite-difference representation and denominator
  transport are genuine public seams (A6, A8); the q-N-M tiling data remain
  application-specific.
- **Public API:** blocked by A1, A4, A7, and A12.
- **Module direction:** the intended direction `PolynomialRigidity ->
  WeakPeriodicity` is good and no reverse dependency is needed.
- **Mathlib integration:** bounded correction A11; no Mathlib Weyl, van der
  Corput, or Fejer theorem was found in the pinned checkout.
- **Proof architecture:** blocked chiefly by A3 and A6.
- **Cost and durability:** the direct Fejer-kernel separator is smaller and
  more durable than formalizing a general uniform approximation theorem for
  this one use.  No elaboration-performance claim is possible before Lean code
  exists.
- **Refactor risk:** there are no Lean call sites yet.  Freeze the corrected
  coefficient predicate and period API before implementation; changing them
  later would affect every analytic theorem and Proposition 4.4.

## Acceptance conditions for a revised blueprint

The revised chapters are ready for independent re-review only when:

1. A1's constant-coefficient counterexample is impossible by definition;
2. one complete and quantitatively checked exponential-sum route replaces the
   current five bullets;
3. the paper's Lemma 4.2 is either actually proved or explicitly removed from
   the claimed formalization scope and comparator aliases;
4. `rigidityPeriodBound` is a closed executable term with a positivity theorem;
5. all denominator divisibility and repeated-average lemmas are stated;
6. the half-circle theorem has a real-lift or `equivIco` formulation;
7. the iterated-difference representation theorem is public and covers all
   integers;
8. `universalRigidityPeriod` is proved to be a common period, including the
   exception and real-lift steps in Proposition 4.4;
9. every ellipsis and undefined bound in the public surface is gone; and
10. the comparator explicitly separates “weaker Lemma 4.2 substitute” from
    “unchanged downstream tiling theorems”; and
11. avoidance is connected to continuous-test equidistribution by an explicit
    positive-integral bump lemma.

## Sources checked

- Greenfeld--Tao, [The Structure of Translational Tilings in
  `Z^d`](https://arxiv.org/pdf/2010.03254), especially Section 4.
- Tao, [Higher Order Fourier Analysis](https://terrytao.wordpress.com/wp-content/uploads/2011/03/higher-book.pdf),
  Section 1.1 for the Weyl criterion, van der Corput lemma, and polynomial
  equidistribution statements cited by the paper.
