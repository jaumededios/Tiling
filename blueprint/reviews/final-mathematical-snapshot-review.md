# Final mathematical snapshot review

## Verdict

**BLOCK — one P1 mathematical/API defect.**

The reviewed manifest is exactly SHA-256
`f0fadecea264bedff038c5af40a1a6880c7512c74ae5fa50b72048398434f10d`.
Every entry in that manifest has the recorded hash.  I found no P0 and no
additional P2, but the P1 below makes a public theorem false and therefore
prevents this snapshot from authorizing production Lean.

This was a clean-room whole-snapshot review.  I re-read the local v3 paper
source, all frozen blueprint chapters 01--11, README, COMPARATOR, the recursive
dependency audit, the validation documentation, and the resolution log.  I did
not use an earlier approval as evidence for the verdict.

## Finding

### FM1 — P1: the general completion certificate is false for a singleton tile

**Locations.**

- `07-periodic-completion.md:201--224` defines the slice exponent and the local
  and total bounds.
- `07-periodic-completion.md:267--311` defines the exact factors
  `N`, `N_j`, `C_j`, `s_j`, `L_j`, and `M`.
- `07-periodic-completion.md:366--407` requires both the local and total bounds
  as fields of every `CompletionCertificate`.
- `07-periodic-completion.md:486--489` asserts existence of that certificate
  from only `F.Nonempty`, `0 < ell`, and `2 <= D.numberOfParts`.
- `07-periodic-completion.md:531--535` explicitly derives the asserted local
  estimate only "for `r>0`".
- `09-main-results.md:298--304` republishes the false constructor as
  `theorem_5_3_general`.
- `COMPARATOR.md:55,79` advertises it as the general Theorem 5.3 bound without
  the missing non-singleton condition.

**Concrete counterexample.**

Let `k = 4096`, `ell = 1`, `F = {0}`, and `A = E = Set.univ`.  There is a
valid `DirectionalTilingDecomposition F A E ell` with two parts

```text
part 0 = empty,       direction 0 = (k,0),
part 1 = Set.univ,    direction 1 = (0,1).
```

Both directions are nonzero and their wedge is `k`, so they are
incommensurable.  The two constant indicator functions have their declared
periods, the parts are disjoint and cover `A`, `E` is scalar-periodic, and
`{0}` tiles `Set.univ` by `Set.univ`.  Thus all fields of
`DirectionalTilingDecomposition` and all four hypotheses of
`improve_weaklyPeriodic` hold.  Empty parts are permitted by the public
structure; this is not an appeal to malformed input.

For these ordered directions the executable avoidance search tries slopes
`(1,0)`, `(1,1)`, `(1,2)` and chooses `(1,1)`.  Consequently the frozen
definitions give

```text
completionPairLCM D                         = k,
completionWedgeFactor D 0                  = k,
completionConvolutionMultiplier D 0        = k^2,
completionDirectionContent D 0             = k,
completionPrimitiveDirection D 0           = (1,0),
completionSliceLCM D 0                     = 1.
```

The last equality holds because a singleton tile has no surviving nonzero
wedge pair.  Since `primorial 2 = 2` and `k` is even,

```text
indicatorDilationModulus (k^2) 1 = lcm (k^2) 2 = k^2,
completionDilationRatio D 0 = 1.
```

It follows that `completionPartMultiplier D 0 = k^2`.  On the other hand,
`F.card = 1`, `l1Diameter F = 0`, and
`completionSliceExponent 1 = 0`, so the asserted local bound is only

```text
completionPartMultiplierBound 1 0 2 k = 3 * 4^2 * k = 48k.
```

For `k = 4096`, this would require `16777216 <= 196608`, which is false.
Therefore no `CompletionCertificate D` can exist.

The certificate's total bound fails independently as well.  The second part
has multiplier one, hence the exact stored multiplier would be
`M = k * k^2 = k^3`.  With direction product `H = k`, the frozen total bound is
`48^2 k^2 = 2304 k^2`; it is smaller than `k^3` because `k > 2304`.

**Cause.**  Write `r = |F|(|F|-1)/2`.  The proof plan absorbs direction
content using

```text
k_j * ||h'_j||^r = ||h_j|| * ||h'_j||^(r-1),
```

and correctly labels this step as requiring `r > 0`.  The public theorem does
not require `1 < F.card`; for a singleton tile `r = 0`, and the two occurrences
of the scale `k` (avoidance wedge and direction content) cannot be bounded by a
single first power of `||h_j||`.

**Required repair.**  The paper-faithful repair is to separate the nontrivial
construction certificate from the paper-facing existential theorem:

1. Require `1 < F.card` on the constructor returning the exact
   `CompletionCertificate` (and on the current exact-certificate version of
   `theorem_5_3_general`).  Under this hypothesis `r > 0`, so the displayed
   estimate applies.  The existing structural theorem needs no extra public
   hypothesis: `2 <= m <= F.card - 1` already implies the nontrivial-cardinality
   fact internally.
2. Export a paper-facing Theorem 5.3 wrapper that handles `F.card = 1`
   separately and returns the theorem's actual existential conclusion: take
   the translated periodic target (equivalently, a multiplier-one periodic
   tiling).  Keep `convolution_part_scalarPeriodic` as the separate
   component-convolution clause.  Do not promise the exact `N * product L_j`
   construction or its per-part bounds in the singleton branch.
3. Update COMPARATOR so the domain of the exact construction certificate and
   the singleton branch are explicit.  Add this counterexample as a negative
   regression before freezing a replacement manifest.

An alternative is a piecewise bound with an extra direction-product power
when `r=0`, propagated through every local, total, structural, and comparator
formula.  That is more invasive and is not needed for the paper's main
argument, which already treats `|F|=1` separately.

## Remaining mathematical audit

Subject to FM1, the rest of the blueprint is suitable in mathematical shape
for Lean formalization:

- The paper's labelled main results and intermediate results have public Lean
  statements and proof routes; the comparator distinguishes literal paper
  claims, strengthened statements, and implementation certificates.
- The M19--M30 and RP/RQ repairs were checked from their owning definitions and
  proof plans rather than accepted from the resolution-log summaries.  In
  particular, the finite-difference sign, torsion-denominator positivity,
  positive repeat moduli, `0 in F` direction count, Chen endpoints, generic
  primitive decomposition, exact weak `Q_m` arithmetic, HNF wire format,
  counted recursive searches, and empty/singleton/zero target branches are
  mathematically coherent.
- Chapters 05a and 05b expose the hard Weil--Stepanov and Chen ingredients as
  public theorem families with their hypotheses and recurrences.  Chapter 05
  consumes their unsuffixed proved endpoints.  No class-field/RH-style result
  is hidden inside a structure field, an unexplained hypothesis, or prose.
- Empty products, empty lcms, zero moduli, degree-zero phases, singleton tiles,
  empty targets, one-part completion, and the structural multi-part branch are
  explicitly routed.  FM1 is the sole missed interaction: a singleton tile
  paired with an arbitrary scaled direction in a permitted empty part.
- The recursive prerequisite audit is credible: the non-Mathlib algebraic,
  finite-field, analytic, CRT/prime-power, lattice, and executable-search
  prerequisites needed for a sorry-free implementation are assigned to owning
  chapters with dependency direction stated.

I found no P0 and no separate P2 in this frozen snapshot.

## Signature and integrity evidence

The following checks passed on the reviewed snapshot:

```text
sha256sum blueprint/SNAPSHOT.sha256
  f0fadecea264bedff038c5af40a1a6880c7512c74ae5fa50b72048398434f10d

sha256sum -c blueprint/SNAPSHOT.sha256
  all 19 manifest entries: OK

python3 blueprint/validation/generate_integrated.py --check
  exit 0

cd /home/codex/Documents/Codex/2026-08-14/Tiling
lake env lean /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
  exit 0
```

The generator check and integrated Lean elaboration establish signature,
namespace, definition-body, import, and declaration-ledger consistency only.
The generated theorem bodies are exact-type validator axioms, so those checks
cannot detect FM1 and are not proof evidence.

## Authorization decision

**This whole mathematical blueprint is not suitable to authorize production
Lean at the reviewed manifest.**  Repair FM1, freeze a new manifest, rerun the
strict generator and pinned integrated elaboration, and obtain fresh
independent mathematical and Lean-suitability approvals on that common
snapshot before starting production proofs.
