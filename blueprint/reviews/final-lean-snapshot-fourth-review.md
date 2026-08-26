# Fourth independent Lean/Mathlib snapshot review

## Verdict

**APPROVE.**  This frozen blueprint is suitable to begin the production Lean
formalization.  I found zero unresolved findings at every severity:

| Severity | Unresolved findings |
|---|---:|
| P0 | 0 |
| P1 | 0 |
| P2 | 0 |
| P3 | 0 |

This verdict is bound only to the 62-entry candidate manifest
`blueprint/SNAPSHOT.sha256`, whose SHA-256 is exactly

```text
be5e45b06e55cb83ee5e70fc5186b881ee29305880a05b6a44d9b8d2600a6e36
```

I verified the manifest file and all 62 listed payloads before review actions,
after all validator/build actions, and after writing this report.  This report
is not a manifest entry and does not alter the reviewed candidate.

The successful elaborations below are signature, namespace, ownership, and
module-boundary evidence only.  In particular, the 458 generated exact-type
theorem axioms are **not proof evidence**, were never treated as proof
evidence, and must not enter production.  Approval means that the blueprint is
mathematically and architecturally ready for the promised sorry-free proof
work; it does not claim that those proofs have already been implemented.

## Review identity, method, and fixed environment

This is a fresh, read-only, library-scale referee pass using the complete
`referee-lean-library` skill and its global rubric in the Tau-Ceti style: freeze
the candidate, inventory the full dependency/API surface, read the proof plan
as mathematics, independently search for reuse, replay strict validation and
the actual module build, assign every observation a severity, and approve only
when the ledger is empty.

I read the complete 28-page arXiv:2010.03254v3 paper from the local 1,275-line,
12,372-word text extraction.  I then read every manifest-listed Markdown
chapter, comparator, layout, resolution record, validation README/report,
generator, TSV/JSON/TOML input, integrated validator, umbrella, and all 29
generated module sources.  Finally, I byte-read every one of the 62 manifest
payloads.  Generated modules were compared with their Markdown provenance and
ownership ledgers, not accepted merely because they compiled.

The pinned checkout and toolchain are:

```text
Tiling commit:  b6744348ec0c2ab44788000b031721b861424c2f
Mathlib commit: db584cd6d46c92f209a44c0f1c829460d327499d
Lean:           4.33.0, commit d8b18978322de05a8f3dba51ef03cf5461676c17
```

The production checkout was already dirty:

```text
 M Tiling.lean
 M Tiling/Basic.lean
?? Tiling/Geometry/
?? Tiling/Topology/
?? blueprint/
```

I did not edit that checkout or any manifest-listed file.  Its unrelated,
pre-existing `sorry` in `Tiling/Geometry/Plate.lean:125` is outside the new
`TranslationalTilings` library and its import closure.  It is therefore not a
finding against this candidate, although a later claim about the entire dirty
checkout rather than this new library would have to account for it.

## Frozen-artifact and command evidence

I independently ran every command required by Chapter 11 and both validation
READMEs, including both forms of the production-option elaboration, the real
offline module build, and the registered-library query.

| Check | Independent result |
|---|---|
| `sha256sum blueprint/SNAPSHOT.sha256` | exact expected digest above |
| `wc -l blueprint/SNAPSHOT.sha256` | 62 |
| `sha256sum -c blueprint/SNAPSHOT.sha256` | all 62 entries `OK` |
| `python3 blueprint/validation/generate_integrated.py --check` | success; integrated source and coverage ledger current |
| pinned direct `lake env lean .../BlueprintIntegrated.lean` | success |
| pinned `lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxErrors=1000 .../BlueprintIntegrated.lean` | success, no diagnostics |
| `python3 blueprint/validation/modules/generate_modules.py --check` | success: `29 modules; 867 declarations; DAG acyclic` |
| `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | every generated acceptance input `OK` |
| `python3 blueprint/validation/modules/generate_modules.py --build` | exit 0; actual offline `lake --no-cache build TranslationalTilings` completed |
| nested-package `lake query TranslationalTilings` | exit 0; second library target registered and resolves through its umbrella |

The module build emitted only generated-validator style warnings about copied
source-location comments, long exact signatures, and the deliberately short
generated `Main` header.  There was no elaboration, import, cycle, target, or
trust-boundary error.  These files are not proposed production source, so the
warnings are not a blueprint finding; ordinary production lints remain part of
the later implementation audit.

## Exact arXiv v3 coverage and public aliases

I compared the labelled results in the v3 paper directly with Chapter 09 and
the comparator.  The blueprint covers Theorems 1.3--1.5 and 1.7, Corollary
1.6, Lemma 2.1, all three clauses of Lemma 3.1, Theorem 3.4, Corollary 3.5,
all three clauses of Proposition 4.1, Lemmas 4.2--4.3, Proposition 4.4, Lemma
5.1, Corollary 5.3, Theorem 5.4, and Theorem 6.2.  Strengthened or
machine-oriented forms are named separately and their relationship to the
paper statement is explicit.

The latest FLSR3-1 repair is complete:

- v3 PDF line 477 is `Theorem 3.4`, exported as `theorem_3_4`;
- v3 PDF line 533 is `Corollary 3.5`, exported as `corollary_3_5`;
- v3 PDF line 804 is `Corollary 5.3`, exported as `corollary_5_3`;
- v3 PDF line 838 is `Theorem 5.4`, exported as `theorem_5_4`, with honest
  strengthenings `theorem_5_4_exact` and `theorem_5_4_structural`; and
- the Proposition 4.4 source erratum is identified as equation (29), with
  indexed `b_j` replacing the paper's fixed `b_i`.

I searched every manifest payload for the obsolete names and labels
`theorem_3_2`, `corollary_3_3`, `corollary_5_2`, `theorem_5_3*`, and their old
paper-number prose.  There are no hits.  The repaired names occur consistently
in the chapters, comparator, recursive audit, resolution log, both ledgers,
integrated artifact, and generated `TranslationalTilings.Main`.  There is no
compatibility alias silently creating a second purported occurrence of a v3
result.

The statement-level audit also confirms the important source corrections:
Lemma 3.1(ii) uses coprimality rather than the paper proof's erroneous
congruence phrase; Theorem 3.4 remains dimension-generic; Corollary 3.5 uses
the period product `q*n`, not an lcm; and Proposition 4.4 contains both
supremum branches, the exceptional-summand transfer, and the stated lattice
membership.

## FLSR3-1 Theorem 5.4 and singleton audit

The public Section 5 API now has three honest layers.

1. `theorem_5_4` is valid on the paper's full nonempty-tile domain and returns
   `PaperCompletionResult`, containing the periodic completion with the
   correct `m`-dependent bound and the separate component-convolution clause.
2. `theorem_5_4_exact` exposes the exact `N * product L_j` construction only
   under the necessary hypothesis `1 < F.card`.
3. `theorem_5_4_structural` derives `1 < F.card` from
   `2 <= m <= F.card - 1` before invoking the exact constructor, and then
   derives the cardinality-only hidden constant used downstream.

For `F.card = 1`, the canonical theorem uses the direct multiplier-one target
translate.  The checked `completion_singleton_bound_regression` at `k=4096`
retains the counterexample to the former over-strong exact bound, so the false
API cannot be reintroduced unnoticed.  Equation (29), the canonical
component-periodicity clause, the exact certificate, and the structural
wrapper all elaborate under the frozen strict options.  No old Section 5 API
name remains.

## FMS3-1 support-indexed factorization audit

The latest mathematical repair also closes cleanly.  Chapter 05b now defines

```lean
FactorizationPrimeSupport q := {p : Nat // p ∈ q.factorization.support}
FactorizationScalar q := FactorizationPrimeSupport q → Int
```

and `CompleteSumFactorizationData.scalar` has exactly this support-indexed
type.  Its nonzero and local-primitivity laws and its norm product quantify
only actual support primes.  `factorizationScalarLookup` is definitionally
zero off support; the two lookup simp theorems, support-family extensionality,
lookup extensionality, and the subtype-product bridge make conversion precise.

At `q=1`, the support subtype is empty.  Both
`factorizationScalar_one_unique` and
`CompleteSumFactorizationData.one_unique` prove that no arbitrary payload
survives.  The existence proof assigns the Bezout coefficient only to its
actual support element, and the Chen/global-product and quadratic consumers
iterate the same support subtype.  Thus no proposition-irrelevant proof choice
or mathematically meaningless off-support integer leaks into the public data.

## Declaration ownership, visibility, and API surface

I parsed `declaration-modules.tsv` independently of the generator and checked
its owners against `module-map.json` and every generated file.

| Property | Independent result |
|---|---:|
| declaration rows | 867 |
| public declarations | 856 |
| private declarations | 1 |
| anonymous instances/examples | 10 |
| definitions copied as definitions | 356 |
| checked theorem/instance/example bodies | 53 |
| exact-type theorem stubs | 458 |
| duplicate public qualified names | 0 |
| unowned or multiply owned rows | 0 |
| production owner modules | 29 |

The kind inventory is 501 theorems, 325 definitions, 20 structures, 11
abbreviations, seven instances, and three examples.  Every generated module's
direct project imports equal its frozen map entry exactly.

The sole private declaration is the source-local `waringVariable` owned by
`TranslationalTilings.NumberTheory.Stepanov.NewtonWaring`.  It is literally
`private`, receives a source-coordinate identity rather than a fictitious
public name, and is used only in its owner module.  No downstream signature or
ledger row leaks it.  Every other non-proof-irrelevant object consumed across
files is discussed and assigned a public owner.

The public seams are coherent: finite-tile convolution, finite differences,
lattice content/primitive geometry, grouped structure, fixed-character and
complete-sum number theory, circle-polynomial rigidity, slicing/completion,
and executable decision data are reusable modules; the concrete
Greenfeld--Tao counterexample and paper-specific quantitative packages remain
application modules.  Main-result aliases are short checked bodies pointing
to the substantive owner declarations rather than duplicated proof plans.

## Module DAG and latest section-boundary repair

An independent topological check confirms 29 distinct modules, no unknown or
self imports, no back edge, and reachability through
`TranslationalTilings.Main`.  Number theory lies below analysis; structure,
slicing, and completion consume those layers in the expected direction; the
counterexample stays independent of the completion chain.

The repaired Chapter 05b cut points in `generate_modules.py` are exactly:

| Source interval | Owner |
|---|---|
| before line 221 | `FiniteCyclicPhase` |
| lines 221--457 | `PolynomialCongruence` |
| lines 458--1173 | `ChenCompleteSum` |
| lines 1174--1329 | `QuadraticCompleteSum` |
| line 1330 onward | `CompleteExponentialSum` |

The one documented non-contiguous exception,
`polynomialPrimeSumBound`, is terminal proof packaging in
`CompleteExponentialSum`.  The full support-indexed CRT/factorization/global
finite-product bridge ends in the Chen interval; the quadratic definitions and
2-adic proof are wholly in the quadratic interval; and the effective global
constant and degree padding start in `CompleteExponentialSum`.

The direct imports match that ownership:

```text
ChenCompleteSum       -> PolynomialCongruence
QuadraticCompleteSum  -> FiniteCyclicPhase
CompleteExponentialSum
  -> ChenCompleteSum, QuadraticCompleteSum, PolynomialWeilBound
```

This is not inferred only from the generator: the complete offline 29-module
build succeeded, including replay of all owner/import boundaries.  The earlier
hidden `Dilation.Periodic -> LatticeGeometry` dependency is also retained.

## Lake target and strict production options

`future-lakefile.toml` is the pinned Tiling package file with precisely the
intended additions: `TranslationalTilings` is a second `[[lean_lib]]` and is
added to `defaultTargets`; the existing `Tiling` library and Mathlib v4.33.0
requirement are preserved.  The production option block is unchanged:

```text
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3
```

The generated validation package repeats these options, every generated
source has the strict local option header, the explicit command-line check
passes with `maxErrors=1000`, and `lake query TranslationalTilings` resolves the
registered target.  The nested manifest uses only the existing pinned local
package directories, and `--build` disables cache downloads.  No production
module imports `BlueprintIntegrated`, `BlueprintModuleValidation`, or a
validation namespace.

## Mathlib and local-project reuse

I searched the pinned Mathlib and existing local project by mathematical role,
not only by proposed name.  The blueprint correctly reuses the existing
finite-difference, primorial, finite-lcm/gcd, subgroup-index, matrix-adjugate,
Euclidean-space, compactness, AddCircle/Fourier, polynomial-content, ZMod
character, Hasse-derivative, and finite-Pi-enumeration APIs identified in its
reuse map.  In particular,
`Nat.Prime.dvd_primorial_iff` has the required `p <= n` direction in this exact
Mathlib revision.

Two nearby APIs do not justify a refactor:

- Mathlib's `Finset.addConvolution` counts representations between two finite
  finsets into `Nat`; the paper requires a finite tile convolved with an
  arbitrary, potentially infinite, function/set indicator into a general
  additive codomain.  `tileConv` is therefore the correct total finite-sum
  adapter.
- Mathlib's `IsCoprime.exists_SL2_row`/`exists_SL2_col` supplies matrix-level
  raw material for the planar normalization, but the project theorem packages
  primitive lattice content, a determinant-one linear equivalence, and the
  exact image `![1,0]`.  That adapter has genuine downstream value and is not
  an avoidable duplicate.

The decision not to reuse the neighboring measurable `Tiling.Prototile` API
is also correct: it models almost-everywhere measure-theoretic packing and
covering, while this paper needs exact pointwise integer representation counts,
higher tiling levels, and discrete periodicity.  I found no Mathlib or local
declaration replacing the paper-specific grouped quantitative structure,
circle rigidity, counterexample, completion certificate, or chameleon
classifier, and no public-name conflict.

## Algorithms, Boolean specifications, and costs

The algorithms chapter exposes finite, proof-free payloads and actual Boolean
programs rather than classical existence disguised as computation.  Periodic
sets are finite Boolean tables; bounded multiplier tuples have genuine
`Fintype` enumerations; convolution, slice, chameleon, and period predicates
have named `= true iff` specifications.  The general finite-index lattice
input is a checked triangular/Hermite wire format with a proof-side coverage
theorem; raw HNF normalization and its cost are explicitly outside the
executable claim.

The counted searches are real recursive evaluators:
`searchBoolTablesCounted` and `searchPositivePeriodsCounted` accumulate the
same callbacks their specifications analyze.  Empty/singleton tile and empty
target branches are explicit.  The regression computes the empty-tile result
and exact cost as `(false, 17)` and `17`; there is no detached fold surcharge
and no `native_decide` trust seam.  The global theorem uses the paper's
unit-cost arithmetic model, states candidate-generation and verification
costs separately, and derives the advertised exponential bound from the
closed period exponent.  I found no Bool/Prop mismatch, hidden proof field in
an enumerated type, or uncosted normalization step inside the claimed model.

## Mathematical closure and proof architecture

The recursive proof plan closes every non-Mathlib prerequisite rather than
promoting a hard theorem to an input certificate.  The largest chain is
explicitly split into Newton--Waring identities, Artin L-polynomials,
Artin--Schreier irreducibility, Hasse multiplicity, translation products,
additive point counts, reciprocal-root bounds, the fixed-character prime
estimate, prime-power recurrences, CRT factorization, quadratic sums, effective
global padding, equidistribution, Fejer separation, and rigidity.

I rechecked the substantive prior high-risk seams:

- the Artin L-series trace identity has finite Euler products, coefficient
  recurrences, exact minpoly fibers, and orbit multiplicities;
- the Stepanov auxiliary construction exposes its literal finite-dimensional
  source/target, reduced-Hasse linear map, finranks, nonzero kernel, evaluation,
  degree bound, and multiplicity/root count;
- the Artin--Schreier and zero-block descents use the repaired minpoly and
  fixed-ring arguments, not the rejected arbitrary-factor translation-product
  claim;
- the terminal degree-one bridge is a checked body and transports the trace
  and polynomial sum to literal `ZMod p`;
- Chen's stationary child invariant, exponent ranges, 2-adic low-degree
  branch, support product, and exponent-six global comparison are all present;
- polynomial rigidity distinguishes constant functions from constant
  coefficient data, requires positive repeat moduli, and handles torsion and
  denominator positivity honestly;
- the weak-period arithmetic uses the actual direction count before the final
  cardinality enlargement; and
- directional decomposition, exact one-part completion, singleton completion,
  and structural multi-part completion form a complete route to Theorem 1.5.

The proof burden remains substantial, particularly in the 05a/05b number
theory, but it is decomposed into named well-typed obligations with a plausible
dependency order and explicit edge-case lemmas.  I found no false theorem, no
vacuous definition, no missing recursive prerequisite, and no hard step hidden
inside a non-proof-irrelevant structure field.

## Regression disposition of all prior blockers

I treated every historical finding in `reviews/resolution-log.md` as live and
regression-audited it against this exact manifest.  The original M1--M30,
L1--L32, A1--A14, Q/RQ/RP findings remain repaired in their owning APIs; the
Chen C1--C7 and Stepanov W1--W8 chains remain present; FM1, FMSR1, FLSR1, and
FLSR2 remain fixed; and the two latest repairs FMS3-1 and FLSR3-1 are confirmed
above.  The generated coverage, strict elaboration, ownership build, and
paper comparison give independent common-snapshot evidence rather than merely
repeating the resolution log's author claims.

No blocker regressed, and no new P0/P1/P2/P3 issue emerged.

## Final decision

The frozen blueprint is mathematically faithful to arXiv:2010.03254v3,
recursively closed, explicit enough to guide a sorry-free implementation,
appropriately reuses pinned Mathlib, and presents a coherent public API,
module DAG, package target, executable layer, and trust boundary.

**Final verdict: APPROVE, with zero unresolved findings.**
