# Fourth independent mathematical snapshot review

**Verdict: APPROVE.**

There are no unresolved findings at any severity in the reviewed snapshot.
This approval is bound only to the 62-entry manifest
`blueprint/SNAPSHOT.sha256` whose SHA-256 is
`be5e45b06e55cb83ee5e70fc5186b881ee29305880a05b6a44d9b8d2600a6e36`.
Any change to a manifest-listed payload invalidates this report.

Date: 2026-08-24 UTC.

## Referee standard and independence

I reviewed the snapshot read-only as a fresh mathematical referee.  Before
review actions I read the complete `referee-lean-library` skill and its complete
global rubric, then applied that library-scale rubric together with the
Tau-Ceti-style clean-room, adversarial standard frozen in Chapter 11.  I did
not rely on earlier approval reports or on the author-side resolution ledger as
proof that a repair was correct.  I independently checked the repaired
statements and their downstream consumers.

I did not edit any of the 62 manifest-listed files.  This report is outside the
manifest.

## Snapshot identity and material read

At the start of the review I obtained:

```text
$ sha256sum blueprint/SNAPSHOT.sha256
be5e45b06e55cb83ee5e70fc5186b881ee29305880a05b6a44d9b8d2600a6e36  blueprint/SNAPSHOT.sha256
$ wc -l blueprint/SNAPSHOT.sha256
62 blueprint/SNAPSHOT.sha256
$ sha256sum -c blueprint/SNAPSHOT.sha256
[all 62 entries: OK]
```

I read the complete arXiv v3 paper (all 28 pages), using the local PDF
`tmp/pdfs/greenfeld-tao-2010.03254v3.pdf`, SHA-256
`2a3f035bb13718e47087a27233f5339ed8feb9fe8dabccb9dec93a95fae2a0a9`,
and its full text extraction.  I checked the source arguments, formulas,
quantifiers, constants, edge cases, source errata, and v3 numbering throughout
Sections 1--6 rather than consulting only the abstract or theorem statements.

I also read every manifest-listed payload in full: Chapters 01--11, README,
comparator, module layout, resolution log, both validation READMEs, both
generator programs, the integrated validator, both declaration ledgers, the
module map and source ledger, build report, future and validation Lake files,
offline manifest and toolchain, generated hash list, the umbrella, and all 29
generated module files.  For the generated payloads I additionally reconstructed
and compared their complete text through both generators' byte-for-byte
`--check` modes and checked every generated hash.  The resulting interface has
867 unique declaration rows: 856 public, one private, and ten anonymous; 356
definitions, 53 checked bodies, and 458 exact-type theorem stubs.

The exact environment was independently confirmed:

```text
pinned project commit  b6744348ec0c2ab44788000b031721b861424c2f
Mathlib commit         db584cd6d46c92f209a44c0f1c829460d327499d
Lean                   4.33.0 (d8b18978322de05a8f3dba51ef03cf5461676c17)
```

The pinned Tiling worktree was already dirty with unrelated user work.  I made
no changes there and treated the blueprint solely as the manifest-bound
candidate under review.

## Mathematical audit

### Paper coverage and recursive closure

The comparator and Chapter 9 cover the v3 results with the correct labels,
assumptions, and conclusions: Theorems 1.3--1.5 and 1.7, Corollary 1.6,
Lemma 2.1, Lemma 3.1(i)--(iii), Theorem 3.4, Corollary 3.5,
Proposition 4.1(i)--(iii), Lemmas 4.2--4.3, Proposition 4.4,
Lemma 5.1, Corollary 5.3, Theorem 5.4, and Theorem 6.2.  The names
`theorem_3_4`, `corollary_3_5`, `corollary_5_3`, `theorem_5_4`,
`theorem_5_4_exact`, and `theorem_5_4_structural` match arXiv v3; no obsolete
pre-v3 public alias remains.  Proposition 4.4's equation (29) uses the indexed
`b_j`, correctly documenting the source typo.

The recursive dependency audit closes every non-Mathlib prerequisite.  In
particular, the difficult analytic input is not assumed wholesale: Chapter 05a
decomposes the prime-field Weil/Stepanov theorem through Newton--Waring,
Artin L-series, Artin--Schreier descent, Hasse multiplicity, additive point
counting, and reciprocal roots; Chapter 05b supplies the integral-phase,
stationary recurrence, CRT, quadratic, low-degree, and degree-padding layers;
Chapter 05 is a terminal circle-polynomial consumer.  I found no duplicated
ownership, cyclic mathematical dependency, hidden oracle, or theorem moved
into a certificate field merely to make a consumer immediate.

### Independent proof-chain checks

I independently rederived or regression-checked the following parts.

- Foundations use exact finite convolution and explicitly separate empty and
  singleton tiles, level-zero cases, scalar periods, and backward/forward
  difference conventions.  The nonempty-tile hypotheses occur precisely where
  level-one disjointness needs them.
- Lattice geometry is dimension-generic where required; primitive content,
  common integer multiples, determinant inclusions, and coefficient-one
  individual/product Euclidean estimates use the intended `WithLp.toLp 2`
  norm rather than the Pi supremum norm.
- Dilation uses `Nat.ModEq` even at modulus one, the coprime clause rather than
  the source's erroneous congruence prose, and the product `q*n` in Corollary
  3.5.  The `F={0,2}` period-four regression distinguishes this from an
  incorrect lcm.
- The eight-point construction's parity/carry decoding is injective, its
  cancellation gives the claimed level-four tiling, and its finite-difference
  obstruction rules out weak periodicity.
- Circle-polynomial rigidity keeps function constancy separate from
  coefficient constancy, excludes the constant coefficient from torsion and
  denominator claims, and transports a normalized primitive integral phase
  through the exact complete-sum estimate.
- In the Stepanov chain, the direct parameters
  `S=p^(n-2)`, `u=n/2`, `K=p^(u-2)/(2d)`, and `R=p*K` satisfy the stated
  dimension slack and degree bounds.  Translation products, fixed-ring
  descent, the Artin--Schreier minimum-polynomial alternative, nonzero
  auxiliary construction, trace weights, reciprocal-root recurrence, and
  maximal-root phase alignment have the required hypotheses.  The repaired
  `monicWeight_mul` correctly requires a field, matching its root/splitting
  proof and every consumer.
- Chen's stationary recurrences retain their source ranges, nonzero child
  invariant, content-primitivity transport, four endpoint ranges, and
  small/large-prime split.  CRT combines only positive prime-power factors;
  the exponent-six padding and low degrees really yield the advertised
  degree-only `1-1/d` bound.  The odd and 2-primary quadratic branches, parity
  cases, and global square-root bound are consistent.
- Weak periodicity's q--N--M--Q--L chain has the correct direction count,
  divisibility enlargement, lattice membership, and exponent bounds.
  Proposition 4.4's two supremum branches transfer the common period to the
  possible exceptional circle polynomial.
- Completion filters zero wedges, treats one-part and singleton cases
  separately, and requires `1<F.card` only for the exact constructor that needs
  it.  The structural route derives this from its part-count hypotheses.  The
  component multiplier and hidden-constant bounds follow from the stored exact
  quantities; the `k=4096` regression correctly rejects the former singleton
  over-strengthening.
- The Boolean-table and positive-period searches are genuine finite recursive
  enumerators with exact counted recurrences.  The HNF input is a checked wire
  format with proof-side coverage, and no raw normalization cost is falsely
  charged to the public algorithm.  The classifier's infinite line selections
  are specifications, not falsely claimed finite data; the chameleon argument
  yields at most one exceptional choice and the terminal decisions split all
  empty/singleton cases.

### FMS3-1 focused repair

I gave the latest repair a separate adversarial audit.

`FactorizationPrimeSupport q` is exactly the subtype of primes occurring in
`q.factorization.support`, and
`FactorizationScalar q := FactorizationPrimeSupport q -> Z` contains no
off-support coordinate.  `factorizationScalarLookup` is definitionally zero
off support; its two simplification lemmas and the lookup extensionality theorem
make that normal form public.  All scalar nonzeroness, local primitivity, local
complete sums, and products in `CompleteSumFactorizationData` quantify the
support subtype.

For `q=1`, the support is empty, so the scalar family is the unique empty
function.  `factorizationScalar_one_unique` proves this, the local fields are
vacuous propositions, the product is one, and
`CompleteSumFactorizationData.one_unique` eliminates all remaining arbitrary
payload.  For `q>1`, the support-indexed Bezout scalars provide exactly the
degree and primitivity facts needed by the local factors.  The subtype/product
bridge recovers the source factorization product, and the CRT, effective Chen,
degree-padding, and quadratic consumers use only support entries.  No
natural-prime-indexed free data, off-support choice, or modulus-one ambiguity
survives.

## Lean, module, and trust evidence

I ran every command required by Chapter 11 and both validation READMEs.  From
the blueprint root unless a `cd` is shown:

```text
$ sha256sum -c blueprint/SNAPSHOT.sha256
all 62 entries OK

$ python3 blueprint/validation/generate_integrated.py --check
exit 0; generated integrated file and 867-row ledger current

$ cd /home/codex/Documents/Codex/2026-08-14/Tiling
$ lake env lean \
    /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
exit 0; no output

$ lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 \
    -DmaxErrors=1000 \
    /home/codex/Documents/Codex/2026-08-24/usi/blueprint/validation/BlueprintIntegrated.lean
exit 0; no output

$ cd /home/codex/Documents/Codex/2026-08-24/usi
$ python3 blueprint/validation/modules/generate_modules.py --check
module validation current: 29 modules; 867 declarations; DAG acyclic

$ sha256sum -c blueprint/validation/modules/generated-hashes.sha256
all generated sources, package files, generators, maps, and ledgers OK

$ python3 blueprint/validation/modules/generate_modules.py --build
module validation current: 29 modules; 867 declarations; DAG acyclic
Build completed successfully (3446 jobs).

$ cd blueprint/validation/modules/BlueprintModuleValidation
$ lake query TranslationalTilings
exit 0; complete umbrella replayed successfully
```

The module build/query emitted only the documented generated-source style
warnings for long copied signatures and the generated Main header.  There was
no module-resolution, cycle, elaboration, or trust-boundary error.  A separate
scan of all 30 generated Lean files found zero `sorry`, zero `admit`, zero
`native_decide`, and no option enabling relaxed auto-implicit declarations.
The 867 coverage rows and 867 ownership rows agree exactly in their common
columns, all names are unique, all assigned production paths exist, and the
direct-import graph has one owner per declaration.

These results are signature, namespace, import-boundary, and package evidence
only.  The 458 generated exact-type axioms are **not proof evidence** and are
outside the proposed production trust boundary.  Approval here is approval of
the complete pre-proof blueprint/API snapshot, not a claim that those theorems
have already been proved in Lean.

## Findings ledger

| Severity | Unresolved findings | Disposition |
|---|---:|---|
| P0 | 0 | none |
| P1 | 0 | none |
| P2 | 0 | none |
| P3 | 0 | none |

The generated-code style warnings are not findings against the blueprint's
mathematics, API, or production-module contract: they arise from copied
signatures/source-location comments in explicitly non-production validation
artifacts and do not weaken any acceptance check.

## Post-review integrity

After completing the substantive review and writing this report, I re-ran the
manifest verification rather than relying on the initial check:

```text
$ sha256sum blueprint/SNAPSHOT.sha256
be5e45b06e55cb83ee5e70fc5186b881ee29305880a05b6a44d9b8d2600a6e36  blueprint/SNAPSHOT.sha256
$ wc -l blueprint/SNAPSHOT.sha256
62 blueprint/SNAPSHOT.sha256
$ sha256sum -c blueprint/SNAPSHOT.sha256
[all 62 entries: OK]
```

A separate structural parse confirmed 62 well-formed SHA-256 rows, unique
existing paths, and that this review report itself is not a manifest entry.
Thus the reviewed payload is byte-for-byte the candidate identified at the
start of the review.

## Final disposition

The blueprint faithfully and completely decomposes arXiv:2010.03254v3, closes
the recursively necessary mathematics, states the planned public Lean API with
the necessary boundary cases and bridges, and gives a suitable acyclic module
plan for a sorry-free implementation.  The FMS3-1 support-indexing repair and
all earlier repaired areas survive independent regression review.

**APPROVE** the exact 62-entry snapshot with manifest SHA-256
`be5e45b06e55cb83ee5e70fc5186b881ee29305880a05b6a44d9b8d2600a6e36`.
