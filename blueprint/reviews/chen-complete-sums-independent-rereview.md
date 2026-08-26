# Independent re-review: Chen complete sums

## Snapshot, scope, and verdict

**Verdict: APPROVE.**  This verdict applies only to
`blueprint/05b-chen-complete-sums.md` at SHA-256

```text
61558a3d321548c1b02b5524e8152be58502990b88e8570265a6061639be990b
```

The reviewed file is 59,725 bytes and had filesystem timestamp
`2026-08-24 06:54:56.096866684 +0000` when the final hash was taken.  The
primary-source extract `tmp/pdfs/ack-ch2-pages49-58.txt` has SHA-256

```text
3a41dfa06f25894fce0dda1686fb35d2455f1f6dc29bbcbef26524d97857cb80
```

I reread the entire current chapter, not only its changes, and compared it
against the complete extract and the rendered ACK printed pp. 49--56.  In
particular, the rendered theorem table on printed p. 51 was used to resolve the
OCR error at extract line 119: the first range is strictly `A_d < p`.

This is a clean-room mathematical referee pass.  I checked the truth of every
displayed public definition and theorem signature and whether the supplied
proof route recursively exposes enough mathematics for a sorry-free Lean
implementation.  Lean proof style and elaboration quality remain the Lean
referee's remit.  This report cannot self-approve the authored repairs or any
implementation derived from them.

No P0 or P1 finding remains, and this rereview found no new P0, P1, or P2
finding.

## Disposition of C1--C7

| ID | Previous severity | Current anchors | Independent verification | Disposition |
|---|---:|---|---|---|
| C1 | P0 | Chapter lines 395--406 and 499--542; ACK extract lines 168--193 (printed p. 52) | `ack_eq_2_5` now requires `stationaryTranslate f p mu.val != 0`.  The separate lemma derives `2 <= sigma` from derivative-root membership: the linear coefficient has two factors of `p`, and every higher coefficient already has two.  Thus `sigma-1` and the `p^(sigma-2)` repetition count do not truncate.  The old counterexample `p=2, a=2, f=0, mu=0` no longer inhabits the signature because its translation is zero, and it is retained explicitly as a regression. | **Resolved** |
| C2 | P1 | Chapter lines 90--120; `05a-weil-stepanov.md` lines 910--962 | The incoming theorem now really is owned by 05a: `polynomial_addChar_sum_prime` occurs at lines 941--946 with exactly the nonconstant-degree, degree-`<p`, standard-additive-character bound consumed here.  The 05b adapter explicitly obtains `[NeZero p]` from `[Fact p.Prime]`, while conditional `_of_primeBound` declarations remain available below the module boundary.  There is no longer an undeclared or 05b-owned Weil axiom in the intended dependency graph. | **Resolved** |
| C3 | P1 | Chapter lines 312--319, 395--431, 725--731, and 841--847 | `StationaryChildInvariant` now carries nonzero translation, exact child degree `d`, zero constant coefficient, and local nonconstant-content primitivity.  These fields follow from the nonzero leading coefficient `a_d p^d`, exact coefficient division, and `normalizeAtPrime_primitive`; zero constant identifies full and nonconstant content.  Both the large-prime and small-prime inductions explicitly invoke the invariant before applying their induction hypotheses. | **Resolved** |
| C4 | P1 | Chapter lines 900--987 and 994--1046; ACK Lemma 2.1 at extract lines 9--47 and Theorem 2.2 at lines 385--396 | The chapter now exposes a finite-support certificate with nonzero Bezout scalars, local primitivity, and an exact norm product.  `natDegree_C_mul_eq` transports the degree, `bezout_left_ne_zero_of_one_lt` rules out a zero scalar on every nontrivial prime-power factor, and `factorization_rpow_product` combines the powers.  Factors outside the exceptional set are exactly one, remaining factors are at least one, and support enlargement is a named theorem.  The empty support `q=1` case is closed by norm one and `1 <= chenGlobalFactor`.  The resulting product is the source's exact `D`, with only its unused decimal relaxation omitted. | **Resolved** |
| C5 | P1 | Chapter lines 1059--1205 | The formerly implicit Gauss-sum work is now a usable recurrence API.  For odd `p`, the chapter states `G_(a+2)=p G_a`, its `G_0` and finite-field `G_1` bases, and completion of the square.  For `2^a`, it states the `a=2,3` bases, `G_(a+2)=2 G_a` for `a>=2`, cancellation for odd linear coefficient, completion of the square for even linear coefficient, and a separate modulus-two enumeration.  These recurrences give exactly `sqrt(p^a)` at odd primes and `sqrt(2*2^a)` in the nonzero 2-primary branch.  CRT therefore introduces the extra `sqrt 2` at most once.  All displayed low-degree signatures, including `q=1`, are true. | **Resolved** |
| C6 | P2 | Chapter lines 820--848; ACK extract lines 326--384 (printed pp. 54--55) | `ack_eq_2_14` is now source-faithful: it assumes `2*(t+1) <= a`.  The complementary low block occurs only in `ack_eq_2_13`, where the chapter gives the exact chain `p^a <= p^(a(1-1/d)) p^((2t+1)/d) <= d^(3/d) p^(a(1-1/d))`, using `p^t <= d` and `p <= d`.  No undocumented branch remains. | **Resolved** |
| C7 | P2 | Chapter lines 1210--1296 | The global constant is now reduced to named finite-product, cardinality, exponent, natural-power, and cast lemmas.  The chain `chenGlobalFactor d <= (d^2)^((d+1)^6) <= 2^(2d(d+1)^6) <= 2^(10(d+1)^8)` is valid, and the prose specifies where real casts and `Real.rpow` monotonicity are discharged. | **Resolved** |

## Whole-chapter mathematical audit

### ACK transcription and recurrence

- Lemmas 2.1--2.4 agree with ACK printed pp. 49--51.  The correction of the
  printed/OCR typo in Lemma 2.2 is right: the content order is bounded by the
  root multiplicity.
- The local-factor endpoints at chapter lines 856--892 agree with the rendered
  source: `A_d < p`, `B_d <= p <= A_d`, `d < p < B_d`, and `p <= d`.
- The exponents and factors in (2.5), (2.6), (2.7), and (2.10)--(2.14) agree
  with ACK printed pp. 52--55.  Algebraically, the (2.7) exponent is precisely
  what results after multiplying the child estimate by `p^(sigma-1)` and then
  using `sigma <= m_mu+1`.  The early/late split and inequalities (2.9),
  (2.11), and (2.12) close the `d < p <= B_d` induction at the stated endpoint.
- The raw derivative root mass for `p>d`, normalized derivative root mass for
  `p<=d`, and both descendant-mass bounds use multiplicity, not merely root
  cardinality.  The hypotheses needed to keep each reduced polynomial nonzero
  are present.
- In the small-prime branch, `t=v_p(content(f'))`, `p^t<=d`, the
  `2*(t+1)` block, nonstationary cancellation, and the per-child multiplicity
  bound are all explicit and mutually consistent.

### CRT, global support, and constants

- The Bezout CRT character identity is correct even when the polynomial has a
  constant term.  Scalar multiplication changes the nonconstant content by
  `abs(u)` and preserves exact degree when `u != 0`; the support construction
  supplies exactly those conditions.
- The finite product handles all factorization degeneracies.  A support prime
  has positive exponent and a nontrivial prime-power modulus; `q=1` has empty
  support.  Positivity of prime powers supplies every `Real.mul_rpow`
  side-condition.
- `chenExceptionalPrimes d` contains every prime at most `(d+1)^6`, and
  `A_d <= (d+1)^6` for `d>=3`.  Hence every omitted support factor is exactly
  one.  The cardinality and local `d^2` estimates yield the stated global
  majorant without a prime-counting assumption.

### Low degrees, padding, and edge cases

- The linear complete sum is zero for `q>1` under the stated primitivity
  condition.  A constant primitive phase forces `q=1`.
- The odd-prime and 2-adic quadratic formulas cover all coefficient-unit
  cases.  Modulus two is separated, including the case in which both the
  quadratic and linear coefficients are odd.  The parity-sensitive global
  bound is `sqrt(q)` for odd `q` and `sqrt(2q)` for even `q`.
- Actual-degree padding is valid for `e=0`, `e=1`, `e=2`, and `3<=e<=d`.
  The natural constant is monotone, and for `q>=1` the exponent
  `1-1/e` is monotone in positive `e`.  The public terminal theorem excludes
  the meaningless advertised degree `d=0` with `0<d`.
- All public mathematical signatures in the chapter are true on their stated
  domains.  No hidden `q=0`, `q=1`, zero-polynomial, totalized-valuation, or
  even-modulus counterexample remains.

## Validation evidence

Immediately before writing this report I ran

```text
python3 blueprint/validation/generate_integrated.py --check
```

and it exited successfully with no output.  The generated header records the
reviewed 05b hash and reports `Generator integration gaps: none`.  I then ran

```text
cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
```

which exited successfully with no diagnostics.  As its own header notes, this
validator checks exact names, types, namespaces, typeclasses, and dependency
integration by replacing bodyless blueprint theorems with exact-type axioms;
it is not used here as evidence that the mathematical proofs already exist.
The approval rests on the independent source comparison and proof-closure
audit above.

## Final verdict

**APPROVE for SHA-256
`61558a3d321548c1b02b5524e8152be58502990b88e8570265a6061639be990b`.**
All C1--C7 findings are resolved, the repairs do not introduce a downstream
P0/P1 defect, and the current prose exposes a mathematically complete route to
the displayed APIs under the requested recursive, sorry-free standard.  Any
change to the chapter hash requires a fresh independent review.
