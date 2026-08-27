# Independent final Lean-library/API/trust review

## Verdict

**REQUEST CHANGES.**  The reviewed snapshot is logically clean under Lean's kernel and the proved
Theorem 1.1/Theorem 1.2 endpoints have the advertised semantic types.  I found no project axiom,
`sorry`, unsafe declaration, validator import, or unbounded proof-resource waiver in the production
closure.  However, this snapshot cannot be accepted as the complete paper formalization because it
has one unresolved P1 effective-input gap and four unresolved P2 library/validation findings.  The
review instruction makes every P0--P3 finding blocking.

Finding totals: **P0: 0, P1: 1, P2: 4, P3: 0.**

## Fixed review snapshot

- Repository: `/workspace/tiling-rational-polygonal`
- Branch: `formalize/rational-polygonal-tilings`
- Commit: `5dff73dbf3bf16ee759a6c43ea669918f5259fea`
- Initial Git state: clean and equal to `origin/formalize/rational-polygonal-tilings`
- Manifest: `blueprint/rational-polygonal/SNAPSHOT.sha256`
- Payload count: 72
- Manifest SHA-256:
  `732f65cac2059b03222b61c0a48219bab26f3f788f62d016010aa1cc6009eb77`
- Initial `freeze.py --check`: PASS

Every manifest-listed file remained read-only during this review.  This report is the only file I
created, and the `reviews/` directory is deliberately outside the payload enumeration performed by
`freeze.py`.

## Blocking findings

### G1 (P1) — The terminal Corollary 1.1 API starts after the noncomputable compilation step

**Files/declarations.**

- `Tiling/RationalPolygonal/Decision.lean:21-128`
- `Tiling/RationalPolygonal/Main.lean:137-153`
- `RasterPresentation`, `RasterPresentation.Represents`,
  `RasterPresentation.DecidesTileability`, `tileDecision_decidesTileability`,
  `exists_tileabilityAlgorithm`, `exists_representation`, and
  `RationalPolygonalRegion.corollary_1_1`

**Evidence.**  The elaborated terminal type is

```text
RationalPolygonalRegion.corollary_1_1 :
  ∃ algorithm : RasterPresentation → Bool,
    RasterPresentation.DecidesTileability algorithm
```

where

```text
structure RasterPresentation where
  rasterTile : Finset IntegerPlane

Represents P K :=
  P.rasterTile = K.normalizedRegion.relevantPlanarRasterTile
```

The Boolean is genuinely executable on `rasterTile`, but `RasterPresentation.canonical` is
explicitly `noncomputable`; `exists_representation` only proves that a code exists.  There is no
finite raw rational-polygon input type, no executable normalization/signature/marker compiler, and
no theorem that such a compiler produces `Represents`.  Thus a caller given the paper's rational
vertex/edge data cannot compute the input expected by `tileDecision`.  The comparator and blueprint
honestly acknowledge this remaining obligation, which confirms that it is not merely a naming
question.

This is a real proof-plan/API boundary: an executable decision after a noncomputable many-one
reduction is not yet the paper's decision procedure on rational polygonal input.  The current
conditional theorem `tileDecision_eq_true_iff P K hP` is correct and worth retaining, but it is the
post-compilation specification, not the complete effective corollary.

**Required change.**  Introduce an effective finite input representation (for example rational
vertices plus a verified polygon/region interpretation), an executable total compiler to
`RasterPresentation`, and a compiler-correctness theorem giving `Represents`.  State the terminal
algorithm and correctness theorem on that input.  Alternatively, do not label the existing
post-raster theorem as the completed paper corollary; that alternative would leave the paper
formalization intentionally incomplete and therefore would not satisfy the present milestone.

**Blast radius and order.**  Add the finite input/normalization layer below `Decision`, prove raster
correctness using the existing semantic APIs, then replace or strengthen `corollary_1_1`; retain the
compiled-raster API as a reusable backend.  Re-run executable tests, exact signatures, the full
trust audit, and the mathematical comparator after migration.  Confidence: high.

### G2 (P2) — The generated declaration/trust gate omits 11 public theorems

**Files/declarations.**

- `blueprint/rational-polygonal/validate.py:38-41,100-137`
- `Tiling/Geometry/LocalLine.lean:53-77,226,266,276,326-331`

**Evidence.**  `DECL_RE` is anchored at the declaration keyword and does not accept a same-line
attribute.  Consequently it misses every declaration written as `@[simp] theorem ...` in
`LocalLine.lean`:

```text
Tiling.mem_positiveSide
Tiling.mem_negativeSide
Tiling.mem_positiveHalfPlane
Tiling.mem_negativeHalfPlane
Tiling.mem_affineLine
Tiling.signedSide_self
Tiling.planarCrossCLM_apply
Tiling.signedSide_add_mul_I
Tiling.signedSide_sub_mul_I
Tiling.compl_positiveHalfPlane
Tiling.compl_negativeHalfPlane
```

An independent source-to-ledger comparison found 490 public declaration commands:
344 theorems, 130 definitions, 11 structures, and 5 abbreviations.  The ledger contains only 479 of
those commands, plus all 60 explicit structure fields.  Therefore the actual accounting target is
**550 declarations/explicit fields and 344 theorem trust closures**, not 539/333.  There were no
ledger extras and no field-line mismatches.  Direct `#print axioms` checks on all 344 actual public
theorems passed with only the three allowed standard axioms, so this is a validation-integrity bug,
not evidence of an untrusted theorem.

**Required change.**  Replace the line regex with a syntax-aware enumeration or, at minimum, parse
command modifiers and attributes robustly.  Add a regression containing same-line attributes and
cross-check parsed source commands against declarations owned by each compiled module.  Regenerate
the ledger, validator, type/body dumps, and hashes; the new gate must report 550/344 unless the
source API itself is deliberately changed.

**Blast radius.**  Generated artifacts and the seal change; production theorem bodies need not.
Verification must demonstrate no source-command omissions or ledger extras, rather than merely
showing that every already-selected ledger name elaborates.  Confidence: certain.

### G3 (P2) — `Raster` contains an unused high-level weak-period endpoint and inverts the documented dependency boundary

**Files/declarations.**

- `Tiling/RationalPolygonal/Raster.lean:1,903-997`
- `Tiling/RationalPolygonal/Earthquake.lean:24-38`
- `blueprint/rational-polygonal/MODULE_LAYOUT.md`
- `integerPointWeakPeriodicDecomposition`, `weaklyPeriodic_integerPoint_image`,
  `Tiles.weaklyPeriodic_of_integerPoint_image`, and
  `RationalPolygonalRegion.exists_weaklyPeriodic_tiling`

**Evidence.**  The written dependency plan says the raster layer precedes `Earthquake`, but the
source has `Raster` importing `Earthquake`.  That import is forced only by the weak-period bridge at
the bottom of `Raster`; the core signature/carrier development does not use the earthquake API.
The last endpoint, `exists_weaklyPeriodic_tiling`, has no production consumer and proves only the
older replacement-tiling result that the final Theorem 1.2 development was specifically designed
to strengthen to weak periodicity of the original translation set.

This gives a foundational encoding module an unnecessary dependency on the Greenfeld--Tao weak
periodicity stack, contradicts the frozen module diagram, and retains an obsolete endpoint beside
the stronger final chain.

**Required change.**  Move the discrete-to-real weak-period transport helpers to a later bridge or
`WeakPeriodicity` module, decide explicitly whether the unused existence theorem is a named
corollary worth retaining, and remove it otherwise.  Then make `Raster` depend only on the integer
reduction and the genuinely lower discrete carrier API.  Update the module diagram to the actual
DAG.

**Blast radius.**  Mostly imports and declaration ownership; preserve theorem statements during
the move if downstream compatibility is desired.  Re-run import, ledger, strict compilation, and
trust gates.  Confidence: high.

### G4 (P2) — `RigidFrame` is a 533-line orphan parallel to the rigidity proof actually used

**Files/declarations.**

- `Tiling/RationalPolygonal/RigidFrame.lean`
- `Tiling/RationalPolygonal/RasterRigidity.lean`
- `blueprint/rational-polygonal/MODULE_LAYOUT.md`

**Evidence.**  `RigidFrame.lean` proves the special `modifiedMarkerSquare 0` / `4ℤ²` theorem
`rigidFrame_translation_differences_mem_lattice`.  No production module imports
`Tiling.RationalPolygonal.RigidFrame`, neither `rigidFrame` nor its theorem has a production call
site, and even `import Tiling.RationalPolygonal.Main` does not expose it.  The actual raster decoder
instead proves and consumes the general-`M`
`planarRasterTile_translation_differences_mem_markerLattice` independently in
`RasterRigidity.lean`.  The module-layout prose nevertheless says `RigidFrame` supplies the frame
rigidity used by `RasterRigidity`.

This is not a small compatibility alias: it is 533 lines of isolated proof machinery and two
public declarations duplicating the architecture of the generalized proof without serving it.

**Required change.**  Either generalize/refactor the frame proof so `RasterRigidity` genuinely
consumes it, or delete the orphan module and correct the blueprint.  Do not retain the current
parallel proof solely because it is already sealed.

**Blast radius.**  No current production consumer; validator, blueprint, umbrella choice, and seal
must be updated.  If extracting a reusable generalized frame theorem, establish it first and
migrate the raster proof before removing the special case.  Confidence: certain.

### G5 (P2) — The root `Tiling` umbrella does not expose the paper-facing terminal API

**Files/declarations.**

- `Tiling.lean`
- `Tiling/RationalPolygonal/Main.lean`

**Evidence.**  `Tiling.lean` imports the rational-polygonal support chain through `Decision`, but
does not import `Tiling.RationalPolygonal.Main`.  The concrete query

```lean
import Tiling
#check Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1
```

fails with `Unknown constant`.  In contrast, the sibling `TranslationalTilings.lean` umbrella
imports `TranslationalTilings.Main` and documents that it exports its paper endpoints.  Users of the
root library therefore receive most implementation details but not `theorem_1_1`,
`corollary_1_1`, or `theorem_1_2`.

**Required change.**  Make the umbrella import the terminal `Main` module (and simplify redundant
lower imports if appropriate), or document a deliberate non-umbrella policy consistently.  For
this paper-facing library, importing `Main` is the natural public API.

**Blast radius.**  One import-surface change, with a possible increase in root import closure that
is already present in the built library.  Verify the three endpoint `#check`s after only
`import Tiling`.  Confidence: high.

## Independent validation evidence

The following checks passed on the fixed commit:

- `python3 blueprint/rational-polygonal/freeze.py --check`:
  72 payloads and the expected manifest digest.
- `python3 blueprint/rational-polygonal/validate.py --check`:
  reported 20 modules, 539 ledger entries, 333 theorem closures, and clean documentation.  G2
  explains why its accounting is incomplete.
- `lake build Tiling TranslationalTilings`:
  PASS, 3523 jobs.
- Strict direct compilation of every one of the 20 owned source files with
  `-DwarningAsError=true -Dlinter.unusedDecidableInType=true`:
  PASS.
- Standalone strict compilation of committed `BlueprintValidation.lean`:
  PASS for the names it contains.
- Independent exact source audit:
  490 public commands plus 60 explicit fields; zero ledger extras, eleven omissions.
- Independent `#print axioms` for all 344 actual public source theorems:
  PASS; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- Production scan:
  no `axiom`, `opaque`, `sorry`, `admit`, `unsafe`, `native_decide`, validator import,
  `maxHeartbeats`, or `maxRecDepth`.  The pinned project uses a bounded
  `maxSynthPendingDepth = 3`; this is not an unbounded proof-resource waiver.
- Project import graph:
  54 modules, 92 project edges, zero cycles.
- `lake exe lint-style Tiling.RationalPolygonal.Main`:
  no style finding; only the repository's missing `scripts/nolints-style.txt` notice.
- Executable regressions on the empty raster:
  `tileDecision = false`, `tileDecisionCost = 17`, and
  `planarTileDecisionCounted = (false, 17)`.
- Generated artifact hashes matched `generated-hashes.sha256` exactly.

The exact public endpoint checks confirm:

- Theorem 1.1 is the semantic tileability iff doubly-periodic-tileability statement.
- Theorem 1.2 takes an arbitrary supplied tiling and concludes weak periodicity of that same
  translation set.
- `tileDecision` is a concrete `RasterPresentation → Bool`, and its counted theorem/correctness
  contract elaborate exactly as documented.
- The unresolved issue is specifically the effective raw-input-to-raster reduction, not the
  Boolean backend or the two semantic headline theorems.

## Global rubric disposition

1. **Mathematical intent:** Theorem 1.1 and Theorem 1.2 declaration graphs match the written plan;
   G1 blocks complete Corollary 1.1 coverage.
2. **Reusable seams:** The marker-frame duplication is actionable as G4.  I do **not** recommend
   replacing the paper-facing real-period structures with `Function.Periodic`: the current
   set-membership API avoids adapter noise and communicates the intended domain boundary.
3. **Public API and theorem shape:** Terminal semantic theorem shapes are good.  G1, G2, and G5
   block the effective/API acceptance story.
4. **Module/dependency design:** The graph is acyclic.  G3 and G4 identify the concrete direction
   and orphan-module problems; G5 identifies the root exposure problem.
5. **Mathlib integration:** No verified exact Mathlib replacement would improve the central raster,
   quake, or weak-decomposition structures.  Existing project `TranslationalTilings` results are
   consumed through proved production declarations.
6. **Proof architecture:** The semantic headline theorems are thin compositions of named lower
   APIs.  G3 removes a superseded endpoint from the foundational raster layer; no tactic-level
   golfing is requested.
7. **Cost and durability:** No measured elaboration failure or resource bypass was found.  G4 is a
   concrete 533-line maintenance cost with zero consumers.
8. **Refactor risk:** G2 and G5 are bounded.  For G3/G4, move or establish replacement declarations
   before removing old surface, regenerate validators after declaration ownership stabilizes, and
   reseal only after the full source/trust/comparator checks pass.

## Explicit do-not-refactor decisions and local-proof handoff

- Keep the semantic regular-closed polygon model and its explicit a.e. open-carrier bridge; it is
  an intentional abstraction for the repository's measure-theoretic tiling relation.
- Keep the compiled `RasterPresentation` decision backend after adding the missing effective front
  end; it is a clean, executable boundary with an exact cost theorem.
- Keep the real and discrete weak-period structures distinct unless a future refactor demonstrates
  reduced adapter cost at existing consumers.
- No individual proof requires a tactic-polish handoff from this library review.

## Acceptance conditions for a follow-up review

1. Implement and validate the effective rational-polygon input/compiler required by G1.
2. Make declaration enumeration complete and regenerate a 550/344-equivalent ledger/trust gate,
   adjusted only for intentional API changes.
3. Repair the Raster/Earthquake ownership boundary and decide the obsolete existence endpoint.
4. Integrate or remove the orphan `RigidFrame` proof.
5. Expose the final endpoints from the chosen root public import.
6. Re-run a clean seal check, full builds, strict unused-decidable compilation, independent
   source/environment API comparison, all-theorem trust closure, executable regressions, and both
   independent referee reviews on the new seal.

