# PM3 independent mathematical and dependency review

Date: 2026-08-24 UTC.

## Verdict

**APPROVE.** There are no P0, P1, P2, or P3 findings. The repaired premise

```lean
(hpB : (p : ℝ) ≤ chenMiddlePrimeThreshold d)
```

on `ack_ineq_2_10` is mathematically sufficient for the implemented proof and
is necessary for its chosen middle-prime recurrence route. It is also the
source-faithful domain of ACK equation (2.10). This is a route-necessity
claim, not a claim that the displayed inequality is false for every prime
above the threshold: ACK has a different large-prime argument there.

The repaired API is synchronized across the chapter and both generated
signature validators. Its terminal paper-facing consumers retain their prior
types.

Generated validator axioms were used only to check exact signatures and
elaboration. They were not used as mathematical proof evidence.

## Reviewed identity

| Artifact | SHA-256 |
|---|---|
| `blueprint/05b-chen-complete-sums.md` | `81b1799e2e08cdaa6639df75a16e15fb3c415793ee04f52cc3cdd2def5dd15a3` |
| integrated validator | `318a8e40e829627be34c28574abf56710eb62f18bd9bbaf4bf888bb473e2b809` |
| generated module validator | `cd03788aa0b765957c87dcfeb797decdc966ffdfb74ba7c6f90b70f5eb5e03dc` |
| module ownership ledger | `1ced9cce08d0db519eb8ec699b5db9e9d19f76f623a6437253dd451f481aaf57` |
| resolution log | `c21906aa12ef8737f7a3af32785d4d86b37fcb9781622981d445b80692dfdd92` |
| frozen production `ChenCompleteSum.lean` | `a1671beb23762d7a57d2e1856bf9eb330587b5725da6d0af1b241580a659d311` |
| ACK source PDF | `12710e296d23aff5ddaee2e7233911491d35aa8e192486cd2c2b16f17a2a01ab` |
| ACK rendered printed p. 52 | `6cb94be8a2f4d18b4c67e38c7a7a7952afa9e630968a386232bdef979a6d3de8` |
| ACK rendered printed p. 53 | `fdec125e745abbbc2ea445858e2c8ea934efbce2b421cf4bdbeb2c1cb3675ccf` |
| ACK rendered printed p. 54 | `01adb151d774edd65a61c2e881fb8c46bfa08b654466d07f26d2e98a0aeb971b` |

The primary mathematical comparison was made against
Arkhipov--Chubarikov--Karatsuba, *Trigonometric Sums in Number Theory and
Analysis*, Chapter 2, Section 2.1, especially printed pp. 52--54.

I did not edit any reviewed chapter, validator, ledger, resolution log, or
production source. This report is the sole file written by this review.

## Printed-source audit

ACK printed p. 53 introduces (2.6) specifically in the range

```text
n < p ≤ (n - 1)^(n/(n-2)),  l ≥ 2.
```

The proof then assumes (2.6) in that same prime range for exponents
`2 ≤ l ≤ L`. For a derivative root with `sigma_j < L`, it invokes that
induction hypothesis on the normalized child to obtain (2.7). For
`sigma_j ≥ L`, it uses the trivial estimate (2.8). The displayed equation
(2.10) is exactly the sum of those early and late contributions. Printed
p. 54 continues from (2.10) through (2.11) and (2.12) to close (2.6), still
within the same middle-prime case.

The Lean definition

```lean
chenMiddlePrimeThreshold d =
  Real.rpow (d - 1 : ℝ) ((d : ℝ) / (d - 2 : ℝ))
```

therefore represents the printed endpoint exactly. The non-strict upper
bound is deliberate: ACK treats primes at or above the threshold by its
large-prime argument and primes at or below it by this middle-prime argument,
so equality is a valid overlap rather than a gap. The Lean inequalities used
in the middle-prime closure are likewise non-strict at that endpoint.

## Sufficiency of `hpB`

For each `mu` in `earlyDerivativeRoots f p L`, the production proof sets

```text
sigma = stationaryOrder f p mu.val
b     = L + 1 - sigma.
```

Early-root membership gives `sigma < L`. Root membership together with the
nonzero normalized translation gives `2 ≤ sigma`. Consequently `2 ≤ b`, so
the child exponent satisfies the lower bound required by `ack_eq_2_6` (and
is strictly smaller than `L + 1`, as in the underlying strong induction).

`stationaryChildInvariant` supplies the other child obligations: the
normalized polynomial still has natural degree `d`, is primitive modulo
`p`, and has the nonzero translation needed by the stationary identities.
The ambient hypotheses already supply `3 ≤ d` and `d < p`. Passing `hpB`
then supplies the one remaining premise of

```lean
ack_eq_2_6 hp hb2 (stationaryNormalize ...) ... hpB ...
```

The child root-mass comparison bounds its coefficient by the parent root
multiplicity. Exponent normalization and `ack_ineq_2_7_of_inductionBound`
give the stated early-root summand. The private early/late assembly uses
`ack_ineq_2_8` for every late root and combines both finite sums. No further
prime-range assumption is required. Thus `hpB` is sufficient at exactly the
point advertised by the repaired statement.

## Necessity for the chosen proof route

The former hypotheses do not imply `hpB`. For example, with `d = 3` the
middle threshold is `2^3 = 8`, whereas the prime `p = 101` still satisfies
`3 ≤ d` and `d < p`. Primitivity is independent of this numerical upper
bound. There is therefore no way to synthesize `hpB` from the old public
context.

This matters concretely, rather than merely as a current elaboration detail.
The early-root proof calls the conditional middle-prime theorem
`ack_eq_2_6`; that theorem's inductive estimate is proved only on the range
`p ≤ chenMiddlePrimeThreshold d`. Removing `hpB` from `ack_ineq_2_10` while
retaining this route would leave the child bound unjustified. Neither the
late-root estimate nor the stationary child invariant supplies a replacement
upper bound on `p`.

The qualifier "for the chosen route" is essential. ACK printed pp. 52--53
first proves the relevant complete-sum bound for primes at or above the
threshold by a separate large-prime estimate. An alternative, stronger API
could combine that route with the middle-prime route and assume its extra
analytic input. That is not the conditional theorem implemented here.
Scoping public (2.10) to the middle-prime induction is the smaller,
source-aligned repair.

## Dependency and paper-facing stability

A repository-wide Lean-source search found no caller of public
`ack_ineq_2_10` outside its defining module. Inside production
`ChenCompleteSum.lean`, the theorem calls `ack_eq_2_6` and then the generic
early/late assembly; the strong-induction engine itself uses that private
assembly directly. Hence adding `hpB` does not force any external API change.

The substantive downstream route is through public `ack_eq_2_6`. In
`primePower_completeSum_bound_of_primeBound`, the branch

```text
¬ chenMiddlePrimeThreshold d ≤ (p : ℝ)
```

passes `le_of_not_ge hpMid` to `ack_eq_2_6`. Thus the terminal conditional
bound obtains exactly the repaired middle-prime premise from its existing
case split. The adjacent threshold-or-larger branches use the independent
large-prime induction. The types of `chenLocalFactor`,
`primePower_completeSum_bound_of_primeBound`, and the unconditional wrapper
are unchanged. No comparator, README, or main-result declaration mentions
either `ack_ineq_2_10` or `ack_eq_2_6` as a paper-facing endpoint.

The chapter, integrated validator, and module validator all place `hpB`
after `hdp` and before `hprimitive`, with the same type. The ownership ledger
continues to assign the declaration uniquely to
`TranslationalTilings.NumberTheory.ChenCompleteSum`.

## Independent replay

After the production owner explicitly froze the source, the following fresh
commands succeeded with exit code zero and no output:

```text
lake env lean TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  -DwarningAsError=true
lake env lean blueprint/validation/BlueprintIntegrated.lean \
  -DwarningAsError=true
lake env lean \
  blueprint/validation/modules/BlueprintModuleValidation/\
TranslationalTilings/NumberTheory/ChenCompleteSum.lean \
  -DwarningAsError=true
```

The production source rehashed immediately after the strict replay to
`a1671beb23762d7a57d2e1856bf9eb330587b5725da6d0af1b241580a659d311`.

One earlier whole-file command overlapped an atomic edit during the owner's
final audit: it began on pre-fix bytes and later reported a failure in a
terminal product rewrite around line 3978 while hashing the newly written
bytes. The owner then declared the file frozen, and the exact frozen hash
passed the strict replay above. That concurrency artifact was downstream of
PM3 and is not a mathematical or API finding.
