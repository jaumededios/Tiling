# Independent mathematical referee report: Chen complete sums

## Reviewed snapshot and scope

- Reviewed file: `blueprint/05b-chen-complete-sums.md`
- SHA-256: `0aa095a0a03bfd6f29102e14e62d47eceb6cfdc5bfebdbfa4946218e6564666c`
- Primary-source extract: `tmp/pdfs/ack-ch2-pages49-58.txt`, SHA-256
  `3a41dfa06f25894fce0dda1686fb35d2455f1f6dc29bbcbef26524d97857cb80`
- Visual source check: rendered ACK printed pp. 49--56,
  `tmp/pdfs/ack-book-page-49.png` through
  `tmp/pdfs/ack-book-page-56.png`.

The workspace root is not a Git worktree, so the chapter hash, rather than a
commit, fixes this review snapshot. The chapter changed once while the review
was in progress; all findings below refer only to the final hash above. This is
a clean-room referee pass and cannot approve any authored or resolution work.
Lean elaboration is left to the Lean referee; I checked whether every public
mathematical signature is true and whether the prose closes the mathematics
needed by a sorry-free implementation.

## Findings

1. **[P0] `ack_eq_2_5` is false on the totalized zero/constant-polynomial case.**

   **Anchor.** Chapter lines 244--270 define
   `coefficientPadicOrder`, `stationaryOrder`, and
   `stationaryNormalize`; lines 460--468 state `ack_eq_2_5` without a
   nonconstancy or positive-order hypothesis. Mathlib's convention is
   `padicValNat p 0 = 0`. ACK printed p. 52 defines
   `f(pY+mu)-f(mu)=p^sigma g_mu(Y)` only inside Theorem 2.1's positive-degree,
   primitive setting and obtains `2 <= sigma` before (2.5); see source-extract
   lines 168--193.

   **Counterexample.** Take `p=2`, `a=2`, `f=0`, and `mu=0 : ZMod 2`.
   Then `hmu` holds, `stationaryTranslate f p mu = 0`, hence
   `stationaryOrder f p mu = 0`, and `hsigma : 0 < 2` holds. The left side is
   the norm of the sum over the two even residues modulo four, so it is `2`.
   On the right, natural subtraction makes `0 - 1 = 0`, while the complete sum
   of the zero polynomial modulo `2^(2-0)=4` has norm `4`. The asserted
   equality is therefore `2 = 4`.

   **Exact repair.** Add either
   `htranslate : Polynomial.stationaryTranslate f p mu.val != 0`, the more
   natural `hnonconstant : 0 < f.natDegree`, or explicitly
   `hsigma_pos : 1 <= Polynomial.stationaryOrder f p mu.val`. Before using
   natural subtraction or the repetition count, prove from `hmu` and
   nonzero translation that `2 <= sigma`. All actual Chen callers have
   `natDegree f = d` and `3 <= d`, so this does not weaken the terminal theorem.
   Add the counterexample above as a negative regression test for the
   unrestricted signature.

2. **[P1] The claimed incoming Weil edge is not owned or discharged by Chapter 05a in this snapshot.**

   **Anchor.** Chapter lines 88--120 say that
   `polynomial_addChar_sum_prime` is already proved in Chapter 05a and that the
   unsuffixed theorems construct `PolynomialPrimeSumBound` from it. However,
   `blueprint/05a-weil-function-fields.md` (SHA-256
   `2bfde22a43dd1b64bd60b00de454356c4e82daa5792bf075f62e7678999ff2b6`)
   contains no declaration named `polynomial_addChar_sum_prime`. The generated
   validator consequently attributes its exact-type axiom stub to Chapter 05b,
   not 05a. ACK printed p. 51 explicitly invokes the prime-denominator Weil
   estimate before the stationary induction (source-extract lines 123--130),
   so this is a genuine recursive prerequisite, not optional exposition.

   **Risk.** The `_of_primeBound` results are conditional and mathematically
   meaningful, but the unsuffixed local, global, and terminal results do not
   yet have the asserted axiom-free incoming proof chain.

   **Exact repair.** Add the displayed theorem, with proof, to Chapter 05a's
   terminal `PolynomialWeilBound` module. In Chapter 05b, consume it rather
   than redeclaring it, and add the explicit bridge
   `polynomialPrimeSumBound : PolynomialPrimeSumBound`. Verify that the bridge
   derives `[NeZero p]` from `[Fact p.Prime]`. Only then specialize every
   `_of_primeBound` theorem to its unsuffixed form in
   `CompleteExponentialSum.lean`.

3. **[P1] Both strong inductions omit the state-invariant that lets the induction hypothesis apply to a stationary child.**

   **Anchor.** `ack_eq_2_6` and `ack_eq_2_13` require the exact hypotheses
   `f.natDegree = d` and
   `not p | nonconstantContentNat f` (chapter lines 663--671 and 757--764).
   Their proofs then apply the induction hypothesis to
   `stationaryNormalize f p mu` (lines 674--677 and 783--786), but the chapter
   contains no declaration or proof that this child still has exact integer
   degree `d` and is nonconstant-content primitive. The newly stated
   descendant-root-mass lemmas at lines 531--538 and 720--728 correctly cover
   root mass, but not these two other induction hypotheses. ACK uses the same
   degree `n` for every child in (2.5), (2.7), and (2.14); see printed pp.
   52--55, source-extract lines 185--194, 232--235, and 360--376.

   **Risk.** The displayed induction hypotheses cannot simply be invoked on
   the child from the currently documented API. This blocks both the
   `d<p<=B_d` recurrence and the small-prime `t` recurrence.

   **Exact repair.** Before either induction, add and prove a combined child
   invariant (or three focused lemmas) saying, for `0 < d`, prime `p`,
   `f.natDegree=d`, and local primitivity, that for every `mu`:

   - `(stationaryNormalize f p mu).natDegree = d`;
   - its constant coefficient is zero;
   - `not p | nonconstantContentNat (stationaryNormalize f p mu)`.

   For the degree, the leading coefficient of `f(mu+pX)-f(mu)` is
   `a_d p^d != 0`; division by the exact common power of `p` preserves it.
   For primitivity, use `normalizeAtPrime_primitive` and the zero constant term
   to identify full content with nonconstant content. State explicitly that
   the same lemma supplies the nonzero-translation premise needed by repaired
   (2.5).

4. **[P1] The CRT-to-global-product proof does not yet close finite support, exact degree transport, or the `q=1` base.**

   **Anchor.** Chapter lines 879--904 reduce Theorem 2.2 to one paragraph:
   extract prime powers, apply CRT to `C u * f`, and say every factor outside
   `chenExceptionalPrimes` is one. The two lemmas actually needed to justify
   that enlargement, `chenLargePrimeThreshold_le` and
   `one_le_chenLocalFactor`, occur only later at lines 985--992; there is no
   support lemma `p notin chenExceptionalPrimes d -> chenLocalFactor d p = 1`.
   Nor is there a proof that the Bezout scalar used on a nontrivial prime-power
   factor is nonzero, hence preserves `natDegree = d`, which is required by
   `primePower_completeSum_bound`. Finally, for `q=1` the factorization is
   empty and the proof needs `1 <= chenGlobalFactor d`; this degeneracy is not
   handled in Section 8. ACK's exact product is the displayed `D` on printed
   p. 55 (source-extract lines 385--396).

   **Risk.** The CRT identity and content-primitivity theorem themselves are
   correct, but the advertised exact finite-product theorem is not presently
   supported by a dependency-complete proof plan.

   **Exact repair.** Move the threshold and lower-bound lemmas before the
   global theorem, then add:

   - `chenLocalFactor_eq_one_of_prime_not_mem` using
     `A_d <= (d+1)^6`;
   - a scalar-degree lemma for `Polynomial.C u * f`, and a Bezout lemma proving
     `u != 0` when its modulus factor is greater than one;
   - an explicit factorization theorem over `q.factorization.support`, with
     local primitivity transported at every CRT step;
   - a product-monotonicity lemma using `1 <= chenLocalFactor` to enlarge the
     support product to `chenExceptionalPrimes`;
   - the `q=1` base (`norm S(1,f)=1` and `1 <= chenGlobalFactor d`).

   The `Real.rpow` product identity should also be stated for the positive
   prime powers, rather than being hidden in the phrase “multiplying the
   p-power terms.”

5. **[P1] The low-degree prime-power Gauss-sum proof is not detailed enough to implement from the cited Mathlib API.**

   **Anchor.** The true public statements are at chapter lines 922--955, but
   the odd-prime proof is only “complete the square and use the quadratic
   Gauss-sum identity” (lines 962--966), and the 2-adic proof only names a
   “standard two-step Gauss recursion” (lines 967--974). The imported pinned
   `Mathlib/NumberTheory/GaussSum.lean` defines Gauss sums for finite rings, but
   its norm-producing product and square theorems are in the section with
   `[Field R]` (lines 163--224 of that file). Thus they apply at `ZMod p`, not
   at `ZMod (p^a)` for `a>1`. ACK Theorems 2.1--2.2 assume degree at least
   three, so ACK supplies none of these missing low-degree recurrences.

   **Risk.** The formulas checked numerically and mathematically are correct,
   including the `sqrt(2*2^a)` factor, but the blueprint currently jumps over
   the principal proof obligation in a chapter that explicitly claims to own
   it.

   **Exact repair.** Introduce the pure quadratic sum `G_a(A)` and state the
   recurrences and bases explicitly:

   - for odd `p` and `p not | A`, complete the linear term using `(2A)^-1`,
     prove `G_a(A)=p*G_(a-2)(A)` for `a>=2` by the last-digit class split, use
     `G_0=1`, and obtain `norm G_1=sqrt p` from the finite-field Mathlib Gauss
     theorem;
   - for `2^a`, cancel immediately when the linear coefficient is odd; when it
     is even and `A` is odd, remove the linear term, compute the `a=2` and
     `a=3` bases, and prove `G_a(A)=2*G_(a-2)(A)` for `a>=4` by pairing the odd
     residue block;
   - enumerate all modulus-two parity cases, then perform CRT with the already
     proved scalar/content transport and show that only the 2-primary factor
     contributes the extra `sqrt 2`.

   These should be named intermediate declarations, not left as a tactic-level
   derivation inside the terminal quadratic theorem.

6. **[P2] The all-exponents signature of `ack_eq_2_14` has an undocumented low-block branch.**

   **Anchor.** `ack_eq_2_14` is stated for every `0<a` at lines 766--775. Lines
   778--783 prove only the global trivial bound when `a<2(t+1)` and then say
   “Otherwise” before deriving the per-class estimate. In ACK, (2.14) occurs
   after the assumption `l>=2(t+1)` (source-extract lines 332--375).

   **Risk.** The stronger all-`a` theorem is true, but its proof plan does not
   cover its full public domain.

   **Exact repair.** Either add the source-faithful block hypothesis
   `2*(t+1) <= a`, or give the missing branch: by
   `ack_residueClass_trivial`,
   `norm S_mu <= p^(a-1) <= p^a`; the already displayed low-block inequality
   bounds `p^a` by `d^(3/d)*p^(a(1-1/d))`, and root membership gives
   `1 <= rootMultiplicity mu`, allowing insertion of the multiplicity factor.

7. **[P2] Domination by `stechkinNatConstant` is asserted rather than reduced to explicit elementary inequalities.**

   **Anchor.** Chapter lines 985--996 state the threshold, local-factor, and
   global-majorant theorems, but lines 1034--1037 only say that the chosen power
   of two “deliberately dominates” the product. This is not an ACK result; it
   is a new executable constant owned by this chapter.

   **Risk.** The bound is mathematically ample, but a sorry-free Lean proof
   needs the integer/real comparison chain and exponent arithmetic. The current
   prose gives no such chain.

   **Exact repair.** Record the following proof route. For `d>=3`,
   `2d/(d-2)<=6`, hence
   `A_d<=(d-1)^6<=(d+1)^6`. The exceptional set has at most
   `N=(d+1)^6` elements and every factor is at most `d^2`, so
   `chenGlobalFactor d <= (d^2)^N`. Use `d<=2^d` to get
   `(d^2)^N <= 2^(2*d*N)`, then prove
   `2*d*(d+1)^6 <= 10*(d+1)^8`. Include the coercion lemmas that transfer this
   natural-power inequality to `Real.rpow`/real products.

## Verified points with no finding

- The rendered theorem table on ACK printed p. 51 really has the strict first
  branch `A_d < p`; the OCR extract's `>=` at line 119 is wrong. The chapter's
  four branch endpoints are correct, including `B_d` in the second branch and
  `p=d` in the small-prime branch.
- The powers in (2.5), (2.6), (2.7), and (2.10)--(2.14) agree with rendered
  ACK pp. 52--55 after algebraic simplification. The `sigma_j` and convexity
  typographical repairs are correct.
- The raw derivative root mass for `p>d`, the normalized derivative root mass
  for `p<=d`, and the two descendant-root-mass theorem statements use the
  correct multiplicities. The `t`-block cutoff `a>=2(t+1)` and the inequality
  `p^t<=d` are correct.
- The Bezout-form CRT identity is mathematically correct even with a constant
  term, and `nonconstantContentNat_C_mul` gives the right local content
  transport. The missing items in Finding 4 concern closure of the global
  induction, not the CRT formula itself.
- The low-degree theorem statements, including the modulus-two exception and
  the `sqrt(2q)` global quadratic bound, are true. The actual-degree padding
  inequalities are also correct for `d=1`, `d=2`, and `d>2`.
- At the terminal API, `d=0` is excluded by `0<d`; constant phases force
  `q=1` under primitivity, and the advertised effective bound handles that
  case. The separate `q=1` omission identified above is in the proof plan for
  the exact degree-`d>=3` finite-product theorem.

## Verdict

**Block.** The snapshot contains one false public theorem (`ack_eq_2_5`) and
four independent P1 proof/dependency gaps: the absent incoming Weil theorem,
missing stationary-child induction invariants, incomplete finite-product
closure, and the unstated prime-power Gauss recurrences. The ACK transcription,
range endpoints, recurrence exponents, and terminal estimate are otherwise
mathematically sound. A corrected snapshot needs a fresh independent review;
this report does not self-approve any repair.
