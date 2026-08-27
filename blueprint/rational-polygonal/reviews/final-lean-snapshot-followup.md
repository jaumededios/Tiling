# Independent final Lean-library/API/trust follow-up review

## Verdict

**ACCEPT.** The frozen commit passes the complete Lean-library, public-API, dependency, build,
documentation, executable-frontend, and trust audit. I found no P0, P1, P2, or P3 issue. Under the
review rule that every finding at those priorities blocks acceptance, this snapshot is therefore
accepted.

Finding totals: **P0: 0, P1: 0, P2: 0, P3: 0.**

The earlier reports in this directory remain accurate historical reviews of commit `5dff73d`; they
were not edited. Their effective-input, ownership-parser, dependency, orphan-module, and root-export
findings are closed in the present snapshot.

## Fixed snapshot and immutable gate

- Repository: `/workspace/tiling-rational-polygonal`
- Branch: `formalize/rational-polygonal-tilings`
- Frozen commit: `9062a580fa82620422472105002395a115e1d354`
- Initial Git state: clean and equal to
  `origin/formalize/rational-polygonal-tilings`
- Manifest: `blueprint/rational-polygonal/SNAPSHOT.sha256`
- Manifest rows: **78**
- Manifest SHA-256:
  `3074903f416d96d5af213aba2c47810835b5b86db1802cb604f9a9f6b4ea1ada`
- Initial `sha256sum -c`: **PASS for every one of the 78 payloads**
- Initial `freeze.py --check`: **PASS**

Every manifest-listed file and every production source remained read-only. This report is the only
file created. The `reviews/` subdirectory is outside the payload enumeration performed by
`freeze.py`, so writing this report does not alter the sealed snapshot.

## Findings

None.

## Public API, ownership, and generated-artifact evidence

The audited surface is the actual 26-module ownership list in `validate.py`, from
`Tiling.Geometry.Plane` through `Tiling.RationalPolygonal.Main`, not merely the generated validator
file.

- Fresh regeneration-and-comparison reported **26 modules, 874 public declarations or explicit
  structure fields, and 518 theorem/lemma trust closures**.
- The ledger has 874 `proved` rows, no duplicate declaration names, and these kind counts:
  5 abbreviations, 238 definitions, 23 structures, 90 explicit fields, and 518 theorems.
- The source parser's same-line attribute/modifier regression passed. Its independently implemented
  compiled-environment cross-check found no omitted public source line, parser extra, moved owner,
  or source-range mismatch.
- I additionally ran a separate row-wise Lean environment query over all 874 ledger entries. Every
  name was public, owned by the recorded compiled module, and had exactly the recorded source line:
  `OWNERSHIP_PASS 874`.
- Live elaborated public types and all public definition/structure/instance bodies matched
  `api-signatures.txt` and `definition-bodies.txt` byte for byte. The four committed generated
  artifacts also passed `generated-hashes.sha256` directly.
- `BlueprintValidation.lean` contains genuine production imports followed by `#check`s; no
  production module imports it or any other validation artifact.

The terminal types, checked after only `import Tiling`, are the intended interfaces:

```text
RationalPolygonalRegion.theorem_1_1 :
  ∀ K, (∃ T, K.Tiles T) ↔ ∃ T, K.Tiles T ∧ DoublyPeriodic T

RationalPolygonalRegion.corollary_1_1 :
  ∃ algorithm, Raw.Decision.DecidesRawTileability algorithm

RationalPolygonalRegion.corollary_1_1_spec :
  ∀ P : Raw.Code.Input,
    Raw.Decision.rawTileDecision P = true ↔
      ∃ T, P.rationalPolygonalRegion.Tiles T

RationalPolygonalRegion.theorem_1_2 :
  ∀ {K T}, K.Tiles T → WeaklyPeriodic T
```

Thus the root umbrella now exposes all three paper endpoints. Theorem 1.2 concerns the supplied
translation set, and Corollary 1.1 is unconditional for every inhabitant of the valid raw-input
type.

## Executable raw-input and compiler audit

The new frontend closes the former post-raster input gap without smuggling a semantic answer into
runtime data.

- `Raw.QPoint` contains two `ℚ` coordinates; `Raw.QTriangle` contains three such points; and
  `Raw.Code` contains only a finite `List Raw.QTriangle`.
- `Raw.Code.Valid : Prop` contains nonemptiness, triangle nondegeneracy, pairwise a.e.
  disjointness, and the intrinsic-anchor condition. `Raw.Code.Input` contains the code plus this
  proof-only field. There is no tiling answer, raster, `RasterPresentation.Represents` witness, or
  other semantic decision certificate in the input.
- Common-denominator normalization is executable. Its proofs identify denominator clearing,
  normalized integer vertices, triangle carriers, and the full finite union with the semantic
  normalized support.
- `LinearFeasibility.solve` is an executable rational Fourier--Motzkin solver. `solve_sound`,
  `solve_complete`, and `solve_isSome_iff` prove exact equivalence with finite strict rational
  feasibility.
- The computational definitions in `SignatureCompiler` are ordinary computable definitions: they
  use lists, arrays, finsets, rationals, integers, the verified solver, exact rational orientation
  tests, and executable marker constructors. Their definition bodies contain no `noncomputable`,
  choice-based, semantic-signature, or raster-representation certificate dependency. The exact
  triangle-membership bridge is proved separately.
- The noncomputable declarations in `SignatureCorrectness` are proof-side real/rational-density
  helpers, not dependencies of the executable compiler. The endpoint
  `signatureFamily_toFinset_eq_relevantSignatures` proves unordered equality of the computed
  family and the semantic positive-measure family for every valid raw input.
- `ComputableMarker` proves exact extensional equality between each executable constructor and the
  semantic marker geometry. `rawTileDecision` then directly composes the computed signature
  family, executable nonempty-first packaging, executable marker raster, and
  `planarTileDecision`; its printed body contains no semantic compiler choice or `Represents`
  premise.
- `Raw.Decision.DecidesRawTileability` is literally a universal quantifier over
  `Raw.Code.Input`. `rawTileDecision_decidesRawTileability` discharges the compiler-correctness
  bridge internally, leaving no extra hypothesis for callers.

Executable regressions passed under warnings-as-errors and unused-decidable checking:

```text
fractional common denominator                         6
clear 2/3 with denominator 6                         4
clear 1/3 with denominator 6                         2
feasible open unit box solver witness                some (1/2, 1/2)
inconsistent strict x-system                         none
unit right-triangle signature-family length          2
unit right-triangle signature cardinalities          [1, 0]
compiled marker raster cardinality                   some 92
```

The intentionally enormous final bounded tiling search is not used as a smoke test; its executable
implementation and correctness theorem are covered by the build and trust closures.

## Imports, architecture, and dependency direction

The complete production project has **60 modules and 92 project-import edges**; `tsort` found no
cycle. The owned 26-module graph has **40 direct project-import edges** and also has no cycle.

The documented layer direction matches source:

- general geometry precedes rational specialization;
- `DiscreteCarrier` is the lower shared discrete interface;
- `Raster` no longer imports the earthquake or Greenfeld--Tao weak-periodicity layer;
- `ComputableMarker`, `LinearFeasibility`, and `RawInput` feed `SignatureCompiler` without
  importing periodic completion or the decision backend;
- `SignatureCorrectness` is the semantic proof layer above the executable compiler;
- `RawDecision` is the sole compiler-correctness/bounded-decision join;
- `Main` is the terminal paper-facing join; and
- root `Tiling.lean` imports `Tiling.RationalPolygonal.Main`.

The former special `RigidFrame` orphan is absent. The generalized rigidity proof used by the
actual raster decoder is the sole production route. I found no dependency inversion, duplicate
foundational layer, or public compatibility surface with a concrete removal benefit.

## Build, diagnostics, documentation, resources, and trust

- Full `lake build`: **PASS, 3531 jobs**. It replayed only Mathlib's optional short-copyright
  header-style warning for `Main.lean`; this is not a source, API, trust, or strict-compilation
  defect. Direct strict compilation of that file emits no diagnostic.
- `validate.py --check`: **PASS: 26 modules, 874 declarations, 518 theorem trust closures,
  documentation clean, executable frontend regression passed**.
- Every owned production source and the committed validator compiled with
  `-DwarningAsError=true -Dlinter.unusedDecidableInType=true`.
- `docBlame` passed on all 26 modules. Module comments document mathematical responsibility and
  dependency role; every public declaration is documented.
- Production scans found no `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, `partial`,
  `native_decide`, generated-validator import, `maxHeartbeats`, or `maxRecDepth` marker. The only
  relevant resource option in the inherited project is bounded `maxSynthPendingDepth = 3`; it is
  not an unbounded proof-resource waiver.
- All 518 public theorem/lemma closures use only `propext`, `Classical.choice`, and `Quot.sound`.
  Separate targeted checks confirmed the same for the linear solver, raw normalization,
  computable-marker bridge, signature correctness, raw decision correctness, all three terminal
  paper endpoints, periodic completion, and the planar bounded-decision theorem.

## Global Lean-library rubric disposition

1. **Mathematical intent:** clear. The declaration graph implements the written five-stage proof
   plan, including the complete raw-input corollary.
2. **Reusable seams:** clear. Linear feasibility, raw normalization, discrete carriers,
   executable markers, compiler correctness, raster rigidity, earthquakes, and period transport
   are coherent boundaries with genuine consumers. No further extraction has a demonstrated
   reuse or dependency benefit.
3. **Public API and theorem shape:** clear. The paper endpoints are thin and canonical; the raw
   correctness contract quantifies over precisely the valid input domain, and the compiled-raster
   backend remains a useful separate API.
4. **Module and dependency design:** clear. The source graph matches the documented DAG and has no
   cycle or reversed high-level dependency.
5. **Mathlib/project integration:** clear. Existing `TranslationalTilings` periodicity,
   completion, and bounded-decision results are consumed through proved production APIs; no exact
   replacement or adapter-saving upstream refactor was identified.
6. **Proof architecture:** clear. Hard geometric, feasibility, cell-completeness, marker,
   earthquake, and transport arguments are isolated behind named interfaces; terminal results do
   not mix those proofs monolithically.
7. **Cost and durability:** clear on measured evidence. Full strict validation completes without
   resource overrides; computation and semantic correctness are separated so classical real-set
   reasoning is outside the runtime compiler.
8. **Refactor risk:** no migration is recommended for this seal. Historical compatibility and
   compiled-backend declarations have active conceptual value, and no deletion or API change has
   an evidence-backed benefit large enough to justify snapshot churn.

## Explicit do-not-refactor decisions and proof handoff

- Keep the regular-closed polygonal support and explicit a.e. open-carrier bridge.
- Keep raw coordinate data separate from proof-only validity instead of attempting to decide all
  geometric well-formedness inside the tileability Boolean.
- Keep `RasterPresentation` as the reusable compiled backend even though it is no longer the
  paper-facing input boundary.
- Keep the executable compiler and its semantic correctness layer in separate modules; this makes
  runtime dependencies auditable.
- Keep the stronger finite-family geometry and the real/discrete periodicity APIs distinct.
- No local proof-polish handoff is warranted by this review.

## Final seal recheck

After creating only this report:

- `python3 blueprint/rational-polygonal/freeze.py --check`: **PASS: 78 payloads, manifest SHA-256
  `3074903f416d96d5af213aba2c47810835b5b86db1802cb604f9a9f6b4ea1ada`**.
- `sha256sum -c blueprint/rational-polygonal/SNAPSHOT.sha256`: **all 78 payloads OK**.
- Git scope check: the only path changed by this review is
  `blueprint/rational-polygonal/reviews/final-lean-snapshot-followup.md`.

**Final disposition: ACCEPTED for the frozen Lean-library/API/trust snapshot at `9062a58`.**
