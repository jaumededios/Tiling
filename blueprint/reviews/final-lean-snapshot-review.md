# Independent Lean/mathlib/library/algorithm review of snapshot `f0fade`

## Reviewed snapshot and verdict

I reviewed the exact manifest whose `blueprint/SNAPSHOT.sha256` has SHA-256

```text
f0fadecea264bedff038c5af40a1a6880c7512c74ae5fa50b72048398434f10d
```

I began and ended the review by running `sha256sum -c blueprint/SNAPSHOT.sha256`; all 20 manifest entries passed. I did not rely on earlier reviews or author summaries, and I did not modify any manifest-listed file.

**Verdict: BLOCK. Production Lean may not begin from this snapshot.** There is one unresolved P1: the exact Chapter 07 completion certificate and its general public theorem are false at tile cardinality one. I found no P0 and no separate P2 finding. The main Theorem 1.5 plan already has a singleton branch, so this does not itself falsify that main theorem; it does block the advertised Theorem 5.3 API and the proposed proof implementation.

## Executable and coverage evidence

- `python3 blueprint/validation/generate_integrated.py --check` succeeded.
- The generated artifact elaborated without output under Lean 4.33.0 and pinned Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d` using the command prescribed in `blueprint/validation/README.md`.
- I independently parsed the chapter fences and coverage ledger. There are exactly 848 declarations in both: 837 public, one private, and ten anonymous. The kinds are 487 theorems, 323 definitions, 19 structures, nine abbreviations, seven instances, and three examples. There are 453 validator-only exact-type theorem stubs, 44 copied checked bodies, and 351 copied definitions. There are no duplicate public names, visibility mismatches, namespace mismatches, or ledger/source omissions. `waringVariable` is the sole private declaration and is not exported.
- I read all manifest-listed chapters, the comparator, recursive dependency audit, validation source and generator, and every generated Lean fence/API. The generated theorem axioms were treated only as elaborated type evidence, never as proof evidence.
- I compared all labelled paper results in the local arXiv v3 source with the paper-facing aliases. I also searched the pinned project and Mathlib checkout for the proposed foundational, finite-difference, lattice-index, polynomial-sum, HNF, Weyl/van-der-Corput, and algorithm APIs. The documented reuse of `fwdDiff`, `AddSubgroup.index_range_nsmul`, `AddSubgroup.index_eq_natAbs_det`, `primorial`, polynomial/content/character APIs, and finite folds is appropriate; I found no blocking duplicate of the project-owned mathematics.

## FM1 — P1 — `CompletionCertificate` is uninhabited for a valid singleton-tile decomposition

### Risk

The public theorem `improve_weaklyPeriodic` in `07-periodic-completion.md` and its paper-facing alias `theorem_5_3_general` in `09-main-results.md` assert `Nonempty (CompletionCertificate D)` for every nonempty tile and every decomposition with at least two parts. That assertion is false. The failure is not a tactic gap: two numerical fields of the certificate contradict its required exact multiplier on a concrete valid input.

The paper proof itself uses

```text
k_j * ||h'_j||_1^r = ||h_j||_1 * ||h'_j||_1^(r-1)
```

only for `r>0`. Chapter 07 sets `r = completionSliceExponent c = c(c-1)/2` but assumes only `F.Nonempty`, so `c=1` and `r=0` are admitted.

### Exact counterexample

Use `ell = 1`, `F = {0}`, and `A = E = Set.univ`. For any even natural number `k > 2304`, form a two-part `DirectionalTilingDecomposition` with

```text
part 0      = empty
part 1      = univ
direction 0 = (k, 0)
direction 1 = (0, 1).
```

This satisfies every structure field: both directions are nonzero and incommensurable, the empty and universal sets have the required directional periods, they are disjoint with union `A`, `E` is scalar-periodic, and `{0}` tiles `univ` by `univ`.

The closed Chapter 02/07 definitions then evaluate as follows.

- `completionSliceExponent F.card = 0` and `l1Diameter F = 0`.
- `avoidanceVector` tests `(1,t)` in increasing order. `t=0` is parallel to `(k,0)` and `t=1` is the first successful slope, so `completionAvoidance D = (1,1)`.
- `completionPairLCM D = |(k,0) wedge (0,1)| = k`.
- The two `completionWedgeFactor`s are `k` and `1`, hence the two `completionConvolutionMultiplier`s are `k^2` and `k`.
- The primitive directions are `(1,0)` and `(0,1)`, with contents `k` and `1`.
- `slicingLCM {0} h = 1`: every tile difference is zero, the nonzero-wedge filter is empty, and the empty lcm is one.
- Since `k` is even, both convolution multipliers are divisible by `primorial 2`; therefore both `completionDilationRatio`s are one.
- Consequently the two `completionPartMultiplier`s are `k^2` and `1`, and

```text
completionMultiplier D = k * (k^2 * 1) = k^3.
```

But the certificate requires, at direction zero,

```text
k^2 <= completionPartMultiplierBound 1 0 2 k = 48*k,
```

which already fails for `k>48`. It also requires both

```text
completed.scalarMultiplier = completionMultiplier D = k^3
```

and

```text
completed.scalarMultiplier
  <= weakCompletionPeriodBound 1 0 2 k
   = ((2+1)*4^2)^2 * k^(2+0) * 1
   = 2304*k^2,
```

which fails for the chosen `k>2304`. Thus `CompletionCertificate D` is empty, contradicting `improve_weaklyPeriodic` and `theorem_5_3_general`.

The directly affected declarations and proof text are:

- `completionSliceExponent`, `completionPartMultiplierBound`, and `weakCompletionPeriodBound` in `07-periodic-completion.md`, lines 201–224;
- `completionPartMultiplier`, `completionMultiplier`, and `CompletionCertificate`, lines 301–406;
- `improve_weaklyPeriodic`, lines 486–490, and the `r>0` estimate in its proof plan, lines 529–539;
- `theorem_5_3_general` in `09-main-results.md`, lines 300–305.

The structural theorem is not directly contradicted by this example, because `2 <= F.card-1` is impossible at `F.card=1`. The main Theorem 1.5 plan is likewise salvageable because its prose already handles singleton tiles before invoking multi-part completion.

### Required repair

1. Add `hcard : 1 < F.card` to the exact multi-part construction theorem and to every alias that returns the current exact `CompletionCertificate`. State and use a positivity lemma for `completionSliceExponent`; do not leave the `r>0` step implicit.
2. Add a genuine singleton completion branch. For a singleton tile `{f}`, translate the periodic target by `-f` (for the normalized `{0}` case, use the target itself), producing a periodic tiling with scalar multiplier one. This branch must not claim that its multiplier is the Chapter 07 product `completionMultiplier D`.
3. Separate the construction-specific exact certificate from the paper-level existence interface if necessary. The component convolution-periodicity clause can remain a theorem about the original decomposition, while the singleton completion certificate uses the direct tiling.
4. The current declaration named `theorem_5_3` also adds `D.numberOfParts <= F.card-1`, a hypothesis absent from printed Theorem 5.3. Retain that useful result under an explicitly structural name, but do not count it as the complete paper theorem. Export an all-cases paper-facing result by combining the singleton branch with the positive-slice-exponent construction, and either prove the printed `O_|F|` dependence under the printed hypotheses or explicitly formalize and document the source's missing structural restriction. The comparator and faithfulness ledger must describe the final choice exactly.
5. Add a regression example for this family, or at minimum checked evaluation lemmas for the singleton slice exponent and the `k^3` exact multiplier, before requesting rereview. Then regenerate the manifest, strict integrated file, and 848-row ledger and obtain fresh clean-room approvals.

Disposition for this snapshot: **unresolved; blocking**.

## Remaining rubric results

### Mathematical intent and recursive prerequisites

Clear apart from FM1. I rechecked the direct Stepanov/Artin–Schreier/fixed-ring route in 05a, the stationary Chen prime-power recurrences and CRT/low-degree branches in 05b, the Weyl residue splitting and Fejer separation in Chapter 05, and the `q–N–M–Q_m–L` dependency direction in Chapter 06. The plans expose the non-Mathlib inputs rather than hiding them in hypotheses or certificates. No additional false boundary case was found.

### Public API, assumptions, and trust

Clear apart from the missing `1 < F.card` assumption and the overly strong exact certificate in FM1. `F.Nonempty` is genuinely used for level-one disjointness. Definitions are substantive; I found no `:= True` stand-in, vacuous decision predicate, theorem-shaped opaque declaration, source `axiom`, `sorry`, or `admit`. The validator's 453 generated axiom stubs remain outside the proposed production trust boundary.

### Module design and Mathlib integration

Clear. Dependencies run from foundations and number theory toward tiling applications, with the fixed-character Weil theorem as the explicit deep incoming edge of the terminal complete-sum module. The counterexample stays independent of the structure theorem. Proposed application-specific APIs are not forced into unsuitable neighboring measurable-tiling abstractions. Actual production modules must still be compiled individually after implementation; concatenated validation does not replace that later import audit.

### Algorithms, finite coverage, and computability

Clear. `PeriodicSetCode`, the filtered `Fintype` tuple search, and every decision procedure have proof-free finite payloads and `Bool = true iff` specifications. The mathematical `LineSelection` correctly represents infinitely many line choices and is not advertised as an enumeration. The HNF wire format `(a,0),(b,c)` has checked `a,c>0`, `0<=b<a`; its membership normal form, scalar-lattice inclusion, and `a*c` coset table agree. Coverage of arbitrary finite-index planar lattices is explicitly proof-side and may be noncomputable; no raw-generator normalization or conversion cost is claimed. The periodic finite-box checker, factorial period lift, longitudinal chameleon test, and slice-type box coverage are sufficient at the stated interfaces. I found no hidden classical choice in an executable payload and no soundness/completeness gap.

### Cost and durability

Clear. The exact periodic-candidate trace is consistent with the stated unit-cost model: a tile summand costs `2*d+3`, the target and comparison contribute `d+4`, the outer fold contributes one per point plus its initial unit, yielding `q^d * (tileCard*(2*d+3)+d+5)+1`. The recursive Boolean-table and positive-period traces have explicit recurrences and closed bounds. No bit-complexity claim is made. The strict integrated file elaborates on the pinned toolchain without a global classical-instance shim.

## Final counts

- P0: 0
- P1: 1 unresolved (`FM1`)
- P2: 0

This exact snapshot is not approved, and production Lean may not begin until FM1 is repaired and the corrected manifest receives fresh independent approvals.
