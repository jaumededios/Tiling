# Third independent mathematical review of the final blueprint snapshot

## Verdict

**BLOCK.**  The mathematical statements and proof architecture survive the
adversarial review, including the repaired singleton-completion and prime-sum
interfaces, but one public proof-data structure still has unconstrained data
outside its mathematical index set.  Under the project's stated gate, this P2
API defect must be repaired and the common snapshot regenerated before Lean
implementation begins.

## Reviewed candidate

- Manifest: `blueprint/SNAPSHOT.sha256`
- Manifest SHA-256, before review:
  `de3b3f3d3625cfc6b17ea3965392e1e2aa2776b4beeb9d12ddf6ad0bddbc96c9`
- Manifest entries: 62
- `sha256sum -c blueprint/SNAPSHOT.sha256`: all 62 entries verified before the
  review and again immediately before this report.
- Paper: Greenfeld--Tao, *The structure of translational tilings in Z^d*,
  [arXiv:2010.03254v3](https://arxiv.org/abs/2010.03254), last revised
  23 September 2021.  I read the complete local v3 TeX source and compared the
  labelled statements and their proofs, not an author summary.
- Pinned formal environment: project commit
  `b6744348ec0c2ab44788000b031721b861424c2f`; Mathlib commit
  `db584cd6d46c92f209a44c0f1c829460d327499d`.

I read every manifest payload: all chapters, the recursive dependency audit,
the comparator, module contract, resolution ledger, both generator sources,
the integrated declaration ledger/artifact, all module metadata, and all 31
manifested generated Lean sources.  The generated sources were additionally
checked byte-for-byte against their chapter owners.  The payload totals were
1,377,794 bytes and 26,016 lines; the declaration ledger has 857 entries
(9 abbreviations, 324 definitions, 3 examples, 7 instances, 20 structures,
and 494 theorems).

I also inspected the relevant pinned project and Mathlib sources, including
the existing `Tiling.Basic`, Mathlib's discrete tiling API, `fwdDiff` and its
Newton identities, `index_range_nsmul`, `primorial`, polynomial content,
`ZMod.stdAddChar`, AddCircle Fourier theory, and Gauss-sum files.  Searches did
not locate an existing Mathlib or project theorem replacing the proposed
Stepanov/Chen complete-sum developments or the exact finite-convolution API.
The existing measurable/a.e. `Tiling` library is a different abstraction and
has no dependency edge to the proposed `TranslationalTilings` library.

## Reproduced validation evidence

I independently ran every command required by
`blueprint/11-refereeing-standard.md`:

```text
sha256sum -c blueprint/SNAPSHOT.sha256                         PASS (62/62)
python3 blueprint/validation/generate_integrated.py --check   PASS
lake env lean -DrelaxedAutoImplicit=false
  -DmaxSynthPendingDepth=3 -DmaxErrors=1000
  blueprint/validation/BlueprintIntegrated.lean               PASS
python3 blueprint/validation/modules/generate_modules.py
  --check                                                      PASS
sha256sum -c blueprint/validation/modules/generated-hashes.sha256
                                                               PASS (38/38)
python3 blueprint/validation/modules/generate_modules.py
  --build                                                      PASS
```

The last command built the complete generated umbrella successfully (3446
jobs) and independently reported 29 modules, 857 declarations, and an acyclic
direct-import DAG.  I also ran the integrated file without command-line option
overrides; its frozen in-file strict options elaborated successfully.  The
module build emitted long-line/header linter warnings in validation-only
generated sources, but no error.  These tests establish syntax, instances,
imports, ownership, and exact signatures only.  The validator `axiom` stubs
were not treated as evidence that any proposed proof exists.

## Mathematical audit

### Paper correspondence and edge cases

- Theorem 1.3(i) explicitly assumes `F.Nonempty`, exactly exposing the paper's
  convention that a tile is nonempty; the empty-target consequence is still
  valid.  The level-four eight-point counterexample has the correct carry/sign
  calculation and the bit-injectivity argument recovers all three bits.
- Theorem 1.7 and Lemma 3.1 retain the correct dimension, positivity,
  boundedness, and `Nat.ModEq` quantifiers.  The source's `1 mod q` phrase in
  Lemma 3.1(ii), its stray `Z^2` in the dimension-generic discussion, and the
  `b_i`/`b_j` slip in Proposition 4.4 are corrected without changing the
  mathematics.
- The grouping construction uses actual integer multiples of nonzero tile
  vectors.  The coefficient-one product and individual direction bounds follow
  from the dimension-generic common-multiple construction; the Euclidean norm
  is the `WithLp 2` norm, not the Pi supremum norm.
- Zero periods, zero moduli, dimension zero, empty directions, and zero wedge
  factors are either excluded at the theorem requiring positivity or covered
  by total definitions with separate boundary lemmas.  In particular,
  `commonDenominator_pos` and normalized repeated sums carry the necessary
  torsion and positive-denominator hypotheses.

### Analytic and number-theoretic closure

- Chapter 05a supplies a genuine recursive proof plan for the fixed-character
  prime bound: finite Euler products and orbit accounting, the trace identity,
  the literal Stepanov coefficient space and dimension inequality, fixed-ring
  translation-product descent, the Artin--Schreier irreducibility criterion,
  Hasse multiplicities, and reciprocal-root phase alignment.  The sign and
  the degree-one `GaloisField p 1` to `ZMod p` bridge are explicit.
- The repaired `Stepanov.monicWeight_mul` has `[Field k]`.  That is precisely
  the domain justified by the algebraic-closure, splitting, root-multiset, and
  injective-descent argument, and every direct or transitive consumer is over
  a field.  The former unsupported `CommRing` generality is gone.
- Chapter 05b closes the integral-phase bridge, all stationary residue-class
  recurrences and endpoint ranges, CRT/content transport, the odd and 2-primary
  quadratic cases, low degrees, and degree padding.  Its internal
  `PolynomialPrimeSumBound` parameter does not leak into a terminal theorem:
  the unsuffixed exported results construct it from Chapter 05a's
  `polynomial_addChar_sum_prime`.  Thus no hard analytic result is smuggled into
  the hypotheses of Lemma 4.2 or the main tiling theorems.
- The Fejer separator and averaging argument give the exact exponent
  `1-1/d`; torsion denominators, positivity, and the coefficient-constant versus
  function-constant bridge cover the exceptional cases used in Lemma 4.3.

### Weak periodicity and completion

- The `q-N-M-Q_m-L` identities use the actual direction count in the exact
  period and enlarge to the cardinality cap only in the final bound.  Cramer
  inclusion, avoidance, determinant-lcm positivity, and exponent arithmetic
  match the paper.
- The FM1 repair is mathematically sound.  `CompletionCertificate` and
  `improve_weaklyPeriodic_exact` require `1 < F.card`; the proof plan consumes
  `completionSliceExponent_pos` before using the `r-1` identity.
  `PaperCompletionResult` remains valid for every nonempty tile.  Its singleton
  branch translates the periodic target and takes multiplier one, while its
  component-convolution field is separately supplied.  The checked
  `k=4096` regression correctly demonstrates why the former singleton exact
  bounds were false.  The structural route derives `1 < F.card` from
  `2 <= m <= F.card - 1`, so the hypothesis is not hidden in a certificate.
- The one-part completion has a separate construction.  The multi-part
  multiplier calculation `N * product L_j`, disjointness argument using a
  chosen `f_0 in F`, and rebasing from `ell*L` to `ell` are consistent.

### Algorithms and main exports

- Periodic inputs and candidate tables are proof-free finite payloads.  The HNF
  wire format has checked positivity/shear invariants and proof-side coverage
  of every finite-index planar period lattice; no raw-generator conversion cost
  is claimed.
- The Boolean-table and positive-period searches are the actual recursive
  programs.  Independently expanding their recurrences gives the advertised
  per-point cost `9*F.card+5`, the Boolean-tree and period-search formulas, and
  the empty-tile value `(false,17)`.  The result is explicitly a unit-cost
  arithmetic bound, not bit complexity.
- The finite chameleon test covers one full common longitudinal period and all
  scalar-period line types.  The line-selection object represents the genuinely
  infinite choices without pretending to enumerate them.  Two nonparallel
  nontrivial line-supported changes destroy every nonzero period; with at most
  one chameleon a common nonzero period remains.
- All paper-numbered declarations in Chapter 09 expand to the corresponding
  lower-level types.  The Theorems 1.4 and 1.5 quantifier order, constants, and
  exact/paper-facing branches agree with the comparator; Corollary 1.6 and
  Theorem 6.2 refer to actual Boolean programs.

## Findings

### P0

None.

### P1

None.

### P2

#### FMS3-1 — `CompleteSumFactorizationData` exposes unconstrained off-support data

Location: `blueprint/05b-chen-complete-sums.md`, lines 940--952,
`CompleteSumFactorizationData.scalar`.

The public field is

```lean
scalar : ℕ → ℤ
```

but `scalar_ne_zero`, `local_primitive`, and `norm_eq_product` inspect it only
for `p in q.factorization.support`.  Hence values away from that support are
completely unconstrained and mathematically unobservable.  The edge case
`q = 1` makes this decisive: the support is empty, both quantified laws are
vacuous, the product is empty, and every function `ℕ → ℤ` is an equally valid
payload once the independent norm equality is supplied.  Consequently the
public bundle has no extensionality principle based on the data it denotes and
two certificates can differ solely on meaningless coordinates.  The complete
declaration ledger confirms that the structure and
`exists_completeSumFactorizationData` are exported public API in
`TranslationalTilings.NumberTheory.ChenCompleteSum`.

Repair: either make this proof-only structure and its constructor theorem
private (the public `_of_primeBound` theorem is the actual downstream seam), or
index the scalar by the finite support,
`q.factorization.support → ℤ`, and adapt the local product accordingly.  A less
clean alternative is a law canonically fixing every off-support value.  After
the repair, add/verify the natural extensionality theorem and regenerate both
validators, ledgers, module hashes, and `SNAPSHOT.sha256`.

### P3

None.

## Final disposition

The core mathematics, including every previously identified blocker named in
the review request, is ready for implementation.  The candidate snapshot as a
whole is nevertheless **BLOCKED** by FMS3-1 because the user required repair
of every substantive issue before implementation.  Any repair changes a
manifest-listed payload and therefore requires a new common-snapshot hash and
fresh approvals; this report must not be carried forward to that new snapshot.
