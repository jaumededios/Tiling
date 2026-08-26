# Final mathematical snapshot rereview

## Gate result

**Verdict: BLOCK production Lean.**

This is a clean-room, whole-snapshot mathematical rereview.  It does not use
an earlier approval as evidence.  The snapshot is overwhelmingly complete and
the repaired Chapter 7 completion API is mathematically sound, including the
singleton counterexample and its domain-total paper wrapper.  Nevertheless,
one P2 proof-plan/API mismatch remains in Chapter 05a.  The requested gate is
unconditional, so a frozen blueprint with even this bounded unresolved repair
is not approved for production implementation.

The manifest file itself has SHA-256

```text
247da8b51bf5dceb79d1d87a013e3ae973b5a758093f613d824db207f9ff8dd6
```

which is exactly the hash required for this review.  Every one of its twenty
listed payload hashes verified before the mathematical audit began and again
at the end.

## Findings

### P0

None.

### P1

None.

### P2: `monicWeight_mul` has a proof only over fields but is exported over arbitrary commutative rings

- **Location:** `blueprint/05a-weil-stepanov.md:379-394`, especially the
  signature at lines 390-394.  The exact validator copy is at
  `blueprint/validation/BlueprintIntegrated.lean:964-968`; its coverage entry
  is `blueprint/validation/declaration-coverage.tsv:195`.
- **Claimed API:**

  ```lean
  theorem monicWeight_mul
      {k : Type*} [CommRing k] {n m : ℕ}
      (psi : AddChar k ℂ) (f : Polynomial k)
      (A : MonicDegreePolynomial k n) (B : MonicDegreePolynomial k m) :
      monicWeight psi f (A.mul B) = monicWeight psi f A * monicWeight psi f B
  ```

- **Documented proof:** the immediately preceding paragraph says to identify
  the Newton power sums with sums over roots in a splitting field and then use
  the union of root multisets under multiplication.  But the sole root theorem
  supplied just above it, `monicPowerSum_eq_sum_roots`, assumes `[Field k]`.
  Thus that proof does not establish the exported `[CommRing k]` theorem.
- **Exact witness to the proof-domain failure:** take
  `k = ZMod 6`.  This satisfies `CommRing k` and is admitted by the public
  signature, but it is not a field and it cannot inject into a field: the
  nonzero classes of `2` and `3` have product zero.  Consequently the stated
  splitting-field argument and `monicPowerSum_eq_sum_roots` cannot be
  instantiated for this legal API input.  This is a counterexample to the
  documented proof route, not to the multiplicativity identity itself.
- **Truth and impact:** the identity is mathematically true over commutative
  rings as a universal Newton-polynomial identity.  All located downstream
  consumers in the Euler-factorization route already work over fields.  The
  issue therefore does not invalidate the paper results, but it is a missing
  recursive prerequisite for the public theorem as frozen.  Validator axioms
  only confirm that this stronger type elaborates; they provide no proof.
- **Exact acceptable repairs:** either

  1. change `monicWeight_mul` to `[Field k]`, which is sufficient for every
     present consumer, and regenerate the integrated validator, ledger, and
     manifest; or
  2. retain `[CommRing k]` and add the missing theorem that Newton power sums
     are additive under `MonicDegreePolynomial.mul`, proved directly from the
     universal Newton recurrence/coefficient convolution (or an explicitly
     identified Mathlib symmetric-polynomial identity), then derive phase
     additivity and apply `AddChar.map_add`.

  Merely citing roots again is not a repair for the current generality.

## Source-faithfulness and mathematical audit

I read the complete local arXiv v3 source
`tmp/arxiv/structure_tilings.tex` (1,072 lines; SHA-256
`0d918fa19f66b28831a22ec1227ceae827de612476a89b059f254a55a4e444fd`)
and compared its definitions, theorem hypotheses, constructions, and displayed
bounds against the blueprint.  The local archive is
`tmp/arxiv/2010.03254v3.tar`.  The following conclusions are independent of
the finding above.

### Quantifiers and edge cases

- Theorem 1.4 correctly retains `0 ∈ F` and `1 < F.card`.  Its uniform form
  chooses the lattice, directions, and multiplier before `E` and `A`; this is
  stronger than, and implies, the source's stated independence from the
  tiling set `A`.
- Translation/normalization uses the correct sign in finite convolution.
  The empty tile in Theorem 1.5 forces an empty target; the singleton tile is
  handled by translation of the target/tiling set with scalar multiplier one.
- Directional decompositions make the positive number of parts explicit.
  One part is handled by `improve_onePart`; differentiation requiring at
  least two parts is never silently applied to it.
- The multi-part structural route has `2 <= m <= F.card - 1`, from which
  `1 < F.card` is derived before constructing an exact completion
  certificate.  There is no circular or hidden cardinality assumption.
- All divisions used in the `q,N,M,Q,L` and slicing constructions are paired
  with divisibility/positivity lemmas.  Natural-number subtraction at
  `r-1`, where `r=c(c-1)/2`, occurs only after proving `r>0` from `1<c`.
- The algorithmic witnesses are finite Boolean payloads.  Their correctness
  statements cover both directions, including the empty input and target,
  rather than relying on proof-bearing enumeration or arbitrary-set choice.

### Exact quantitative formulas

- The dilation modulus is the lcm of `ell` and the required small-prime
  product; the coprimality formulation fixes the source proof typo and gives
  the explicit `ell * 4^(2*oscillation*card)` bound.
- The canonical grouped directions satisfy both individual bounds and the
  stronger coefficient-one product bound
  `prod_j ||h_j|| <= diameter^(card-1)`.  This product bound is essential in
  the final exponent computation.
- Chapter 6's relative lattice-index exponent is
  `2*(c-1)^2`, and the weak multiplier exponent is `c*(c-1)`, as in the
  paper after converting the exact `q-N-M-Q-L` construction.
- In Chapter 7, with `H=prod_j ||h_j||` and `r=c(c-1)/2`, the general honest
  completion estimate is

  ```text
  ((m+1)*4^(2c))^m * H^(m+r) * D^(m*r).
  ```

  Under `m<=c-1`, its first factor is bounded by the closed cardinality-only
  constant `(c*4^(2c))^c`.  Combining this with the weak-period data gives
  the explicit final diameter exponent
  `(c-1)*(c^2+c-1)`, hence the paper's `O(c^4)` exponent.
- Polynomial rigidity retains the source exponent `1-1/d`.  The prime-field
  input is recursively discharged by the Artin--Schreier/Stepanov route in
  05a and the prime-power/CRT Chen route in 05b; constants depend only on the
  degree.  Torsion denominators use the product bound `Q <= |k|*Q_k`, not an
  invalid lcm substitution.
- The Fejer separator uses coefficient l1 mass `2(N-1)` and the chosen
  `N >= 1/(2*epsilon^2)` gives the required one-half separation outside the
  small arc.
- The counted planar algorithm's per-candidate accounting is explicit
  (`9*F.card+5`, with the empty-input regression evaluating to `17`), and the
  exponential search cap is connected to the periodic-completion witness.

### Chapter 7 singleton regression and repair

The repaired API genuinely closes the earlier `k=4096` failure and creates no
new gap.

For the legal two-part decomposition with

```text
F={0}, ell=1, A=E=univ,
part 0=empty, direction 0=(4096,0),
part 1=univ,  direction 1=(0,1),
```

the exact frozen construction has

```text
completionPairLCM               = 4096
completionWedgeFactor (part 0)  = 4096
completionConvolutionMultiplier = 4096^2
completionDirectionContent      = 4096
completionSliceLCM              = 1
completionDilationRatio         = 1
completionPartMultiplier        = 4096^2
completionMultiplier            = 4096^3.
```

At `c=1`, however, `r=0`; the former advertised local and total bounds are
respectively

```text
48*4096       = 196608       < 4096^2 = 16777216
48^2*4096^2  = 38654705664   < 4096^3 = 68719476736.
```

`completion_singleton_bound_regression` has a checked `norm_num` body for
these inequalities.  The new design makes the exact constructor
`improve_weaklyPeriodic_exact` require `1<F.card`, precisely the hypothesis
needed for `r>0`.  The paper-facing `PaperCompletionResult` does not expose
the false exact construction fields.  Its singleton branch constructs a
multiplier-one periodic completion directly, while its component-convolution
field is supplied independently by `convolution_part_scalarPeriodic` and
remains valid.  The one-part and structural multi-part branches are separate,
and Theorem 1.5 rebases their certificates correctly.  Therefore this repair
does not weaken or leave uncovered the source theorem.

### Recursive prerequisite audit

Apart from the P2 above, the recursive mathematical prerequisites are present
at theorem-level granularity:

- finite convolution, translations, exact representation counts, periodicity,
  and reusable finite differences;
- lattice content, primitive decomposition, Cramer/index calculations,
  avoidance, and pairwise-wedge lcm bounds;
- Frobenius dilation, Folner boundary estimates, compact-product ray limits,
  and grouped structure data;
- the explicit level-four counterexample and non-weak-periodicity argument;
- Newton/Waring encoding, finite Euler products, extension-field orbit/trace
  accounting, Artin--Schreier irreducibility, direct Stepanov auxiliary
  construction, Hasse multiplicity, root counting, and power alignment;
- stationary prime-power recurrences, the separate 2-adic quadratic cases,
  primitive normalization, correctly oriented CRT coefficients, and the
  finite exceptional-prime product;
- circle-polynomial representation, Weyl/van der Corput, torsion residue
  splitting, Fejer separation, and bounded period extraction;
- directional decomposition, slicing, exact/one-part/singleton completion,
  rebasing, and disjointness from level-one nonnegativity;
- finite-torus/HNF encodings, classifier and chameleon tests, finite support
  geometry, and counted decision procedures.

The four recorded source errata are corrections rather than mathematical
changes: Lemma 3.1(ii) needs coprimality rather than congruence, Theorem 3.2
has one accidental `Z^2`, Proposition 4.4 has `b_j` rather than fixed `b_i`,
and the Section 6 bracket slips are repaired by the typed recurrence.

## Architecture and Mathlib reuse

The dependency direction and public boundaries are suitable for a library
development.  The blueprint reuses finite sums/additive monoid algebras,
forward differences, lcms/primorials, Euclidean `WithLp`, subgroup-index and
matrix APIs, compact products, `AddCircle` Fourier theory, finite-field traces,
polynomial content, Hasse derivatives, normalized factors, additive
characters, and finite Pi types.  Project-owned adapters are justified where
the exact paper statement is not already in Mathlib.

I independently inspected the neighboring project API at
`/home/codex/Documents/Codex/2026-08-14/Tiling/Tiling/Basic.lean` and its plane
geometry.  Chapter 10's decision **not** to reuse `Tiling.Prototile` is sound:
that structure has measurable nonempty supports in a normed additive group,
placements with labels, almost-everywhere disjointness under `volume`, an
almost-everywhere cover, and countability.  This paper instead needs finite
subsets of `Z^d`, exact integer-valued convolution equalities, periodic target
sets, and arbitrary positive tiling levels.  An adapter would neither preserve
the intended equality notion nor share a substantive theorem, and would add
measure-theory dependencies to the discrete core.  This is a confirmed
do-not-refactor decision.

The pinned checkout was at commit
`b6744348ec0c2ab44788000b031721b861424c2f` and already contained unrelated
working-tree changes.  The successful validator elaboration is evidence only
about the frozen signatures against that Mathlib toolchain; it is not a build
or trust audit of unfinished production modules.

## Full-scope manifest evidence

Every manifest-listed file was included.  Mathematical source chapters were
read in full; the generated file was checked against every source fence and
reviewed in dependency order; the coverage ledger was checked as a complete
row-level inventory.

| Manifest payload | Lines | Independent audit focus | Result |
|---|---:|---|---|
| `blueprint/README.md` | 110 | scope, conventions, source errata, gate | consistent |
| `blueprint/01-foundations.md` | 366 | convolution signs, periodicity, finite differences | sound |
| `blueprint/02-lattice-geometry.md` | 357 | norms, primitive content, Cramer, lcms, avoidance | sound |
| `blueprint/03-dilation-structure.md` | 297 | Frobenius dilation, limits, grouping, one-dimensional period | sound |
| `blueprint/04-counterexample.md` | 194 | eight-element injectivity, cancellation, non-weak-periodicity | sound |
| `blueprint/05a-weil-stepanov.md` | 2,077 | full recursive prime-field estimate | one P2 above |
| `blueprint/05b-chen-complete-sums.md` | 1,384 | full stationary recursion, 2-adic and CRT branches | sound |
| `blueprint/05-polynomial-rigidity.md` | 679 | polynomial/function distinction, torsion, Fejer, exact exponent | sound |
| `blueprint/06-weak-periodicity.md` | 525 | FM1 use, quantifier order, q-N-M-Q-L arithmetic | sound |
| `blueprint/07-periodic-completion.md` | 782 | full corrected FM1 API and all edge branches | sound |
| `blueprint/08-algorithms.md` | 1,047 | actual finite algorithms, costs, HNF/classifier/chameleon iff | sound |
| `blueprint/09-main-results.md` | 382 | paper wrappers, normalization, exact final bounds | sound |
| `blueprint/10-recursive-dependency-audit.md` | 224 | prerequisite closure and reuse decisions | P2 omission above |
| `blueprint/11-refereeing-standard.md` | 137 | independent adversarial gate/trust protocol | suitable |
| `blueprint/COMPARATOR.md` | 160 | source/blueprint/Lean theorem-by-theorem comparison | faithful |
| `blueprint/validation/README.md` | 62 | validator semantics and limitations | accurate |
| `blueprint/validation/generate_integrated.py` | 610 | strict extraction, rejection checks, ledger generation | passes |
| `blueprint/validation/BlueprintIntegrated.lean` | 5,150 | all extracted definitions and exact theorem signatures | elaborates; axioms are signature evidence only |
| `blueprint/validation/declaration-coverage.tsv` | 858 | complete source-line/name/visibility/coverage inventory | internally consistent |
| `blueprint/reviews/resolution-log.md` | 80 | dispositions and Chapter 7 repair history | consistent with frozen files |

The ledger contains 857 declarations: 324 definitions, 20 structures, 7
instances, 9 abbreviations, 494 theorems, and 3 examples.  Coverage is 353
definition bodies, 46 checked bodies, and 458 exact-type validator stubs;
visibility is 846 public, 1 private, and 10 anonymous.  These figures reconcile
with the eleven extracted mathematical chapters.

## Commands and observed results

Run from `/home/codex/Documents/Codex/2026-08-24/usi` unless noted:

```bash
sha256sum blueprint/SNAPSHOT.sha256
# 247da8b51bf5dceb79d1d87a013e3ae973b5a758093f613d824db207f9ff8dd6

sha256sum -c blueprint/SNAPSHOT.sha256
# all 20 payloads: OK

wc -l $(awk '{print $2}' blueprint/SNAPSHOT.sha256)
# 15,481 total lines; per-file counts reproduced in the table above

sha256sum tmp/arxiv/structure_tilings.tex
# 0d918fa19f66b28831a22ec1227ceae827de612476a89b059f254a55a4e444fd

wc -l tmp/arxiv/structure_tilings.tex
# 1072

python3 blueprint/validation/generate_integrated.py --check
# exit 0, no drift or integration gap

awk -F '\t' 'NR>1 {total++; kind[$4]++; vis[$6]++; cov[$7]++; src[$1]++}
  END {print total; for(k in kind) print k,kind[k];
  for(k in vis) print k,vis[k]; for(k in cov) print k,cov[k]}' \
  blueprint/validation/declaration-coverage.tsv
# 857 total; declaration and coverage figures reported above

rg -n -C 6 'monicWeight_mul|root multisets of a product' \
  blueprint/05a-weil-stepanov.md \
  blueprint/validation/BlueprintIntegrated.lean \
  blueprint/validation/declaration-coverage.tsv
# isolated the P2 at 05a:379-394 / Integrated:964-968
```

Run from `/home/codex/Documents/Codex/2026-08-14/Tiling`:

```bash
lake env lean \
  /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
# exit 0, no output

git rev-parse HEAD
# b6744348ec0c2ab44788000b031721b861424c2f

rg -n 'Prototile|IsTiling|AEDisjoint|MeasureSpace|NormedAddCommGroup' \
  Tiling/Basic.lean Tiling/Geometry/Plane.lean
# confirmed the measurable/a.e. API mismatch described above
```

The source files and generated validator were read with line-bounded `sed`
chunks after `wc -l`; targeted `rg -n` checks were then used to re-open every
quantitative and edge-case interface cited in this report.  No
manifest-listed file was edited.

## Required disposition

Repair the Chapter 05a `monicWeight_mul` generality/proof mismatch by one of
the two exact routes above, regenerate and freeze a new manifest, and subject
that new snapshot to mathematical and Lean rereview.  Until then this exact
`247da8...` snapshot is **BLOCKED** for beginning production Lean.
