# Final production Lean/library snapshot review v2

**Date:** 2026-08-26  
**Review role:** fresh independent final Lean 4 / Mathlib library referee  
**Verdict:** **APPROVE**

## 1. Scope, independence, and sealed identity

I reviewed the restored production snapshot independently. Prior report verdicts were not used as evidence. The blueprint, canonical declaration ledger, module contract, generated validators, and all production `TranslationalTilings` sources were treated as immutable. The only file written by this review is this report, which is outside the sealed manifest.

The reviewed seal was checked before substantive work and again immediately before this report was written:

- `sha256sum blueprint/SNAPSHOT.sha256`:
  `482c18adc1fcdb3865454bd50471cb075d662ceac4ee84f35b607a38cbfa7ae3`
- `wc -l blueprint/SNAPSHOT.sha256`: `95`
- `sha256sum -c blueprint/SNAPSHOT.sha256`: `95 OK`, `0 FAILED`

This is the requested production digest. The rejected older digest was not used.

The production trust boundary was derived from the actual import graph, not from directory proximity. `TranslationalTilings.Main` reaches all 29 contracted `TranslationalTilings` modules and no `Tiling` module. In particular, the disclosed legacy `Tiling/Geometry/Plate.lean` `sorry` is outside the production formalization's import closure. The generated validators contain exact-type axiom stubs by design and are outside the production trust boundary.

## 2. Executive assessment

The snapshot is internally consistent at four independent levels:

1. **Seal:** all 95 payloads match the target manifest.
2. **Architecture:** the 29-module source graph and umbrella agree exactly with the committed module contract, form an acyclic DAG, and have the intended dependency direction.
3. **API:** every one of the canonical 869 rows is accounted for; all 858 public declaration types agree at kernel-expression level, all 355 public definition bodies agree, and all 20 public structure interfaces agree down to constructor and projection types.
4. **Trust and execution:** production compiles strictly, uses no project axioms or proof placeholders, has no unexpected axiom dependencies, and passes executable boundary regressions.

I found no unresolved P0, P1, P2, or P3 issue.

## 3. Commands and observed results

The following gates were run from the restored paths, against the sealed sources.

| Area | Command or audit | Result |
|---|---|---|
| Seal | `sha256sum blueprint/SNAPSHOT.sha256`; `wc -l`; `sha256sum -c` | Exact target digest; 95 rows; 95/95 payloads OK |
| Integrated validator freshness | `python3 blueprint/validation/generate_integrated.py --check` | Current |
| Integrated strict compile | `lake env lean -DrelaxedAutoImplicit=false -DmaxSynthPendingDepth=3 -DmaxErrors=1000 .../BlueprintIntegrated.lean` | Pass |
| Module validator freshness | `python3 blueprint/validation/modules/generate_modules.py --check` | `29 modules; 869 declarations; DAG acyclic` |
| Generated artifact hashes | `sha256sum -c blueprint/validation/modules/generated-hashes.sha256` | 38/38 OK |
| Module validators | `python3 blueprint/validation/modules/generate_modules.py --build` | Pass; 3446 jobs |
| Production query | `lake query TranslationalTilings` | Pass |
| Production build | `lake build TranslationalTilings` | Pass; 3463 jobs |
| Combined package build | `lake build Tiling TranslationalTilings` | Pass; 3479 jobs |
| Strict entry points | `lake env lean -DwarningAsError=true TranslationalTilings/Main.lean` and `TranslationalTilings.lean` | Both pass without warnings |
| Strict source sweep | `lake env lean -DwarningAsError=true` over all 29 production source files plus the umbrella | 30/30 pass without warnings |
| Public type dump | fresh Lean environment audit of canonical public names in production and validators | 858 found, 0 missing on each side; byte-identical dumps, SHA-256 `8f750a5e9e356680f0c46007bfda649f34f1c95916e45e315ed93bf684136290` |
| Public definition dump | fresh Lean environment audit of public rows represented as definitions | 355 found, 0 missing on each side; byte-identical dumps, SHA-256 `db7c950b0b644d86e089470695aec07724ecd6027fb75b77d49ca38edc3125be` |
| Structure metadata dump | constructor, field-order, projection-name, and projection-type audit | 20 structures, 0 missing; byte-identical dumps, SHA-256 `b3cdc4e562cb523d096eedb44355fafa56117e2e62ea29b87a82d11538aea95f` |
| Explicit API enumeration | source namespace/declaration parser versus ledger | 858 expected public, 858 explicit public, 858 intersection, 0 missing, 0 extra |
| Axiom closure | fresh `Lean.collectAxioms` audit of all 858 public declarations | 858 found, 0 missing, 2357 aggregate occurrences, 0 outside `{propext, Classical.choice, Quot.sound}` |
| Public documentation | fresh `Lean.findDocString?` audit | 858 found, 0 missing names, 0 missing docstrings |
| Static trust scan | production scan for `axiom`, `opaque`, `unsafe`, `sorry`, `admit`, `native_decide`, validator imports, and local resource overrides | 0 forbidden occurrences; no validator import; no heartbeat/recursion-depth override |
| Executable regressions | finite decision/cost evaluation and named completion/normalization examples | Expected values and proofs pass |

The initially restored shared `.lake` cache was incomplete. An early validator attempt exposed missing Mathlib object files and four transient dependency-output misses. Those dependencies were rebuilt serially, without changing any sealed source, and every affected validator and production gate above was rerun successfully. This was an environment recovery event, not a snapshot finding.

## 4. Architecture and dependency direction

The checked source graph has two disciplined lower branches which converge only where mathematically intended:

- the tiling branch: `Basic` / `FiniteDifference` / `Arithmetic` -> lattice and dilation structure -> grouped structure and slicing;
- the number-theory branch: Stepanov and finite-cyclic-phase developments -> polynomial and complete exponential-sum bounds;
- the analytic bridge: circle polynomials -> equidistribution -> Fejer separation -> polynomial rigidity;
- the theorem pipeline: weak periodicity + slicing -> periodic completion -> executable algorithms -> `Main`.

Fresh comparison of actual direct imports against `module-map.json` was exact for all 29 modules and the umbrella (`30/30`). The graph is acyclic. `Main` reaches `29/29` contracted modules, with none missing. There is no dependency on generated validation modules or on legacy `Tiling` sources.

The abstraction seams are appropriate for library use:

- foundational types and convolution/difference operations live below geometry and periodicity;
- the Stepanov subdevelopment is split by mathematical role rather than placed in one dependency-heavy file;
- unconditional complete-sum wrappers live at the convergence layer rather than creating a reverse import into their prerequisite proofs;
- certificate/data structures are separated from the final decision procedures;
- the umbrella imports only `Main`, and `Main` exposes the algorithms/counterexample endpoints without bypassing intermediate layers.

The largest production files are `Algorithms.lean` (5045 lines), `ChenCompleteSum.lean` (4071), `WeakPeriodicity.lean` (2616), and `ArtinLSeries.lean` (2253). I inspected these as possible maintainability hotspots. Their declaration order follows their local proof/certificate pipelines, their imports remain narrow, and strict compilation requires no exceptional resource settings. Their size alone does not justify a destabilizing split at this sealed milestone.

## 5. Exact 869-row API and implementation coverage

The canonical ledger contains:

- 869 total rows;
- 858 public, 10 anonymous, and 1 private;
- 503 theorems, 325 definitions, 20 structures, 11 abbreviations, 7 instances, and 3 examples;
- 356 definition representations, 56 checked-body representations, and 457 exact-type axiom-stub representations.

### Public declarations

A fresh Lean metaprogram loaded each of the 858 public qualified names in both environments and emitted `repr` of the kernel type expression. The two complete streams were byte-identical. This avoids dependence on human-formatted pretty-printing and establishes exact public type agreement.

A second metaprogram emitted declaration kind, type, and value expression for every public row represented as a definition. All 355 were found on both sides and the streams were byte-identical. A third audit covered the 20 structure rows and found exact equality of constructor types, field order, projection names, and projection types.

An independent source enumeration found exactly the same 858 explicit public declaration names as the ledger: no missing declaration and no unledgered explicit public helper.

### Non-public and anonymous rows

The remaining 11 rows were checked directly at their source locations and by strict compilation:

- one private `waringVariable` definition, whose production and validator declaration/body agree;
- one anonymous `CoeFun CirclePolynomial` instance;
- six anonymous counted Boolean-algebra instances (`Commutative` / `Associative` for the counted operations);
- three anonymous algorithm regression examples.

Thus all 869 canonical rows are accounted for. Validator theorem axioms do not substitute for production proofs: the production modules themselves were compiled and axiom-audited, and the validator namespace is absent from their closure.

## 6. Trust, proof architecture, warnings, and durability

The production source scan contains no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, or `native_decide`. The only uses of kernel `decide` are finite executable checks in `Algorithms`; there are 15 such sites, and the strict build validates them. There is no production import of `BlueprintIntegrated` or `BlueprintModuleValidation`.

For all 858 public declarations, `Lean.collectAxioms` found no dependency other than the standard accepted set `propext`, `Classical.choice`, and `Quot.sound`. In particular, no project-specific axiom or `sorryAx` enters the API.

Production has no `maxHeartbeats` or `maxRecDepth` override. Its package options agree structurally with the frozen future package configuration: strict auto-implicit behavior and the package-wide `maxSynthPendingDepth = 3`, with no declaration-level escape hatch. All production files pass `-DwarningAsError=true`. Generated-validator comment/header style warnings are confined to generated, non-production artifacts and do not affect the production warning gate.

All 858 public declarations have docstrings, and all 29 modules have meaningful module documentation. Important theorem families retain descriptive names and qualified namespaces, so users can discover the library through the intended mathematical layers.

The proofs make deliberate use of Mathlib primitives including finite sums and finsets, `MvPolynomial`, `Polynomial.Content`, forward finite differences, `Nat.ModEq`, `WithLp`, additive-circle Fourier infrastructure, and finite-field/characteristic typeclasses. A fresh name-level search found no existing project/Mathlib declaration replacing the distinctive core abstractions (`tileConv`, backward differences, completion certificates, periodic-set codes, normalized complete sums, or the Artin-L-series bridge). I found no local duplicate suitable for deletion or upstream replacement at this milestone.

## 7. Repaired-boundary audit

I rechecked the high-risk seams called out by the blueprint and resolution history, using source inspection, exact `#check` queries, strict compilation, and executable examples.

| Boundary zone | Independent result |
|---|---|
| Empty/nonempty tile interfaces | `dilate_zero` carries `F.Nonempty`; grouped direction counting carries the correct zero-membership condition; exact and structural completion wrappers use their distinct cardinality hypotheses rather than silently assuming nonemptiness. |
| Backward/forward difference convention | `backwardDiff_eq_fwdDiff` has the intended shift and no spurious negation; iterated uses compile against that convention. |
| Slicing and directional decomposition | Wedge/slice exponents and the directional-periodicity target are wired through the declared decomposition interface; the singleton completion regression proves exponent zero. |
| Period bounds and arithmetic edge cases | Universal periods use the specified product construction; modulus-one `Nat.ModEq`, torsion/constancy, direction witnesses, and exact `1 - 1/d` bounds remain explicit. |
| Norm and polynomial boundaries | `WithLp` norm interfaces, primitive/content/common-denominator boundaries, and normalized complete-sum types match the ledger exactly. |
| Stepanov/Hasse boundary | `hasseDeriv_eval_frobenius` has the corrected implicit-field/characteristic binder order; the Newton/Waring, translation-product, reciprocal-root, and Artin-L-series dependencies remain one-way. |
| Chen and factorization boundary | The middle-prime upper range is present in `ack_ineq_2_10`; factorization scalar lookup has separated simplification lemmas; C1-C7 interfaces compile at their intended layer. |
| Periodic completion results | `proposition_4_4` explicitly carries the `SetScalarPeriodic` target; `theorem_5_4` has its required nonempty hypothesis; exact, structural, and HNF/lattice results expose their distinct hypotheses and bounds. |
| Normalization regression | The repeated-prime normalized complete-sum theorem handles the nominal `Q = 0` boundary; the dedicated negative regression compiles. |
| Executable algorithm boundary | `theorem_6_2` and its lattice-input form carry the existence/nonemptiness contract and the Boolean iff specification; empty-input evaluation returns `(false, 17)` and search cost `17`; all anonymous finite `decide` examples compile. |

Additional executable checks returned:

- `periodicTilingPeriodBound 0 0 = 1`;
- `planarTileDecisionCounted (empty Finset Plane) = (false, 17)`;
- `planarTileSearchCost (empty Finset Plane) = 17`.

The named singleton-completion and normalized-repeat-zero regressions also compiled under the production umbrella.

## 8. Global rubric disposition

1. **Library intent and structure:** clear mathematical pipeline; module responsibilities and naming align with the blueprint.
2. **Abstraction seams:** reusable foundations, number-theory components, analytic bridge, completion certificates, and algorithms are separated at stable interfaces.
3. **Public API:** exactly reconciled to the 869-row contract; public types, definition bodies, and structure metadata independently matched.
4. **Dependency direction:** exact contract match, acyclic, complete `Main` closure, no validator/legacy leakage.
5. **Mathlib integration:** appropriate reuse of established types and theories; no convincing exact replacement or redundant local layer found.
6. **Proof architecture:** real production bodies are trusted; validator axioms are isolated; high-risk seams have named local interfaces and regressions.
7. **Cost and durability:** strict builds are clean; no resource escape hatches; large modules remain cohesive and have narrow imports.
8. **Refactor risk:** no refactor is warranted before acceptance. In particular, splitting the dense Chen/Algorithms pipelines or moving unconditional wrappers downward would add dependency and theorem-statement risk without a demonstrated library benefit. No local proof-polish handoff is required for acceptance.

## 9. Finding ledger

| ID | Severity | Area | Finding | Disposition |
|---|---|---|---|---|
| L-01 | None | Seal | Target manifest has the exact requested digest and all 95 payloads validate. | Closed |
| L-02 | None | Architecture | Actual imports match the 29-module contract plus umbrella; DAG and `Main` closure are complete. | Closed |
| L-03 | None | API | All 869 rows are accounted for; public types, definition bodies, and structure metadata match independently. | Closed |
| L-04 | None | Trust | No placeholder/project axiom/unsafe escape; no unexpected axiom dependency; legacy `Plate.lean` is outside closure. | Closed |
| L-05 | None | Build | Query, production build, combined build, validators, strict entry points, and strict source sweep pass. | Closed |
| L-06 | None | Boundaries | Repaired empty-set, finite-difference, Stepanov/Chen, completion, normalization, HNF, and executable-decision seams pass. | Closed |
| L-07 | None | Maintainability | Docs are complete, imports narrow, package options controlled, and no acceptance-blocking duplication/refactor need was found. | Closed |

**Unresolved P0:** 0  
**Unresolved P1:** 0  
**Unresolved P2:** 0  
**Unresolved P3:** 0

## 10. Final verdict

**APPROVE.** The restored sealed snapshot is acceptable as the final production Lean/library snapshot. This conclusion is conditional only on the post-write seal recheck remaining at the same exact digest with all 95 payloads valid; that closing check is performed after this report is written because this report itself is outside the manifest.
