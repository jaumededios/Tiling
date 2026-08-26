# Final independent mathematical snapshot review

## Verdict

**BLOCKED (one P1 finding).** The sealed snapshot contains genuine, trusted, mathematically
faithful proofs of paper Theorems 1.1 and 1.2 and of the continuous/discrete reduction used by
them. It does **not** yet contain a complete formalization of paper Corollary 1.1 from the paper's
stated input, a given rational polygonal set. The executable code starts only after an unverified,
noncomputable polygon-to-raster boundary.

Under the review instruction that every P0--P3 finding is blocking, this snapshot is not acceptable
as a complete formalization of all results in arXiv:2408.02151v2. I found no second mathematical,
specification, or trust defect in the sealed production development.

## Reviewed snapshot and method

- Repository: `/workspace/tiling-rational-polygonal`
- Branch: `formalize/rational-polygonal-tilings`
- Commit: `5dff73dbf3bf16ee759a6c43ea669918f5259fea`
- Review state before this report: clean and equal to
  `origin/formalize/rational-polygonal-tilings`
- Sealed manifest: `blueprint/rational-polygonal/SNAPSHOT.sha256`
- Required and observed manifest digest:
  `732f65cac2059b03222b61c0a48219bab26f3f788f62d016010aa1cc6009eb77`
- Payload count: 72
- Paper: exact local TeX source for arXiv:2408.02151v2,
  `/tmp/dmgm-paper.qSrqmZ/Rational_Vertex_PTC.tex`, read end-to-end.

I read the complete blueprint, comparator, module layout, all five proof-plan documents, the
production theorem bodies on every numbered result and essential intermediate step, the imported
Greenfeld--Tao endpoint bodies used here, and the validator/freeze scripts. I also applied every
section of the global Lean-library review rubric. Manifest-listed files and all production sources
remained read-only.

## Blocking finding

### G1 — P1 — Corollary 1.1 begins after, rather than implements, the effective input compilation

**Files and declarations**

- `Tiling/RationalPolygonal/Decision.lean:21`, `RasterPresentation`
- `Tiling/RationalPolygonal/Decision.lean:30`, `RasterPresentation.Represents`
- `Tiling/RationalPolygonal/Decision.lean:34`, `RasterPresentation.tileDecision`
- `Tiling/RationalPolygonal/Decision.lean:87`, `RasterPresentation.DecidesTileability`
- `Tiling/RationalPolygonal/Decision.lean:116`, `RasterPresentation.canonical`
- `Tiling/RationalPolygonal/Main.lean:139`, `RationalPolygonalRegion.corollary_1_1_spec`
- `Tiling/RationalPolygonal/Main.lean:148`, `RationalPolygonalRegion.corollary_1_1`
- `Tiling/RationalPolygonal/Raster.lean:222`, `PolygonalRegion.signature`
- `Tiling/RationalPolygonal/Raster.lean:493`, `PolygonalRegion.relevantSignatures`
- `Tiling/RationalPolygonal/RasterMarker.lean:1473`,
  `PolygonalRegion.relevantPlanarRasterTile`

**Paper requirement.** Corollary 1.1 states that there is an algorithm which, “upon any given
rational polygonal set,” decides tileability (paper lines 220--222). Its proof makes the first
algorithmic step explicit: from the given polygon `Ω`, the algorithm computes the normalizing
number `N` and the finite raster `F` (paper line 547), then runs the finite tiling decision.

**What production proves.** `RasterPresentation` contains only an already supplied
`Finset IntegerPlane`. `tileDecision` is a genuinely executable and verified bounded search on that
finite set. `Represents P K` is the proposition

```lean
P.rasterTile = K.normalizedRegion.relevantPlanarRasterTile
```

and the pointwise correctness theorem requires a proof of that proposition. The only constructor
from a semantic rational region is `canonical`, which is explicitly `noncomputable`. Its target
uses `relevantPlanarRasterTile`, whose signature selection and enumeration are also noncomputable
semantic constructions. Consequently neither `canonical_represents` nor
`exists_representation` supplies code which a caller can execute on raw rational vertices and
edges. The terminal `corollary_1_1` has domain `RasterPresentation`, not an effective encoding of a
rational polygonal set.

This is a strict input-domain weakening, not merely a representation rename. A finite lattice tile
can be accepted as the post-raster input only if it is accompanied by the non-executable semantic
claim that it is the correct raster. The proved Boolean cannot itself validate or construct that
claim from the paper's input. The blueprint candidly records this boundary, which prevents a P0
trust or false-proof diagnosis, but recording the missing stage does not formalize it.

**Severity.** P1. The theorem stated in Lean is logically sound, and the downstream lattice
decision procedure is verified; there is no inconsistency or forbidden axiom. However, an entire
major layer of the advertised paper corollary—the executable map from the paper's input to the
proved finite decision problem—is absent. This blocks the proof plan for Corollary 1.1 and blocks a
claim that all results in the paper have been formalized.

**Required repair.** Add a finite executable input representation and a verified compiler. At a
minimum, acceptance requires:

1. a runtime rational-polygon code supporting the paper's allowed disconnected components and
   holes, with a precise validity predicate or a validity-by-construction encoding;
2. a semantic decoding theorem connecting every valid code to the regular-closed
   `PolygonalRegion` model and its intrinsic vertices;
3. executable common-denominator normalization and executable construction of the finite
   cell/signature family and rigid marker raster;
4. a compiler correctness theorem showing that the computed `RasterPresentation` represents the
   decoded region, without asking the caller to supply `Represents` as an oracle-like proof;
5. one total executable Boolean on the raw code, for example
   `rawTileDecision input := tileDecision (compile input)`, and a paper-facing correctness theorem
   quantifying over every valid raw rational-polygon input; and
6. fresh strict build, trust, documentation, generated-ledger, and seal checks covering the new
   compiler and endpoint.

An alternative representation is acceptable if the formal input itself contains enough finite
rational polygonal data to compute and verify the raster. Merely bundling an arbitrary raster with
a propositional `Represents` witness, or retaining a noncomputable canonical constructor, does not
repair the gap.

**Blast radius and migration order.** This can be additive: retain the current
`RasterPresentation.tileDecision` as the verified backend, add the raw input/decoder/compiler below
`Decision`, prove compiler correctness using the existing raster equivalence, then strengthen the
paper-facing `corollary_1_1` endpoint. The semantic Theorems 1.1 and 1.2 and their proof bodies need
not change. Confidence: high.

## Numbered paper comparator audit

| Paper item | Production trace and independent assessment |
| --- | --- |
| Definition 1.2(i), singly periodic | `Basic.SinglyPeriodic` supplies a nonzero real period and exact translation invariance. Accepted. |
| Definition 1.2(ii), weakly periodic | `Basic.WeakPeriodicDecomposition` is a finite pairwise-disjoint exact union with a nonzero period for each part; `WeaklyPeriodic` packages it. Accepted. |
| Definition 1.2(iii), doubly periodic | `Basic.DoublyPeriodic` supplies two linearly independent real periods. Accepted; this generates a full-rank lattice in the real plane. |
| Theorem 1.1 | `Main.RationalPolygonalRegion.theorem_1_1` is a thin endpoint over `exists_doublyPeriodic_tiling`; the forward proof normalizes, obtains an integer tiling, encodes it as a finite raster, applies `TranslationalTilings.theorem_1_5`, decodes a scalar-periodic raster tiling, embeds two independent coordinate periods, and denormalizes. Accepted. |
| Corollary 1.1 | The finite-raster backend and its correctness are genuine, but the raw rational polygon-to-raster compiler required by the paper is absent. Blocked by G1. |
| Theorem 1.2 | `WeakPeriodicity.RationalPolygonalRegion.Tiles.weaklyPeriodic` and the thin `Main.theorem_1_2` retain and decompose the originally supplied `T`; they do not merely produce a replacement tiling. Accepted. |
| Definition 2.1, integer tiling | `IntegerReduction.PolygonalRegion.IsIntegerTiling` requires a tiling and integrality of every placed intrinsic vertex. Accepted. |
| Lemma 2.2, existence of integer tiling | `IntegerReduction.exists_integer_tiling` invokes the genuine connected-component-shift construction, rebases one placement at zero, and obtains integral differences by graph reachability. Accepted. |
| Definition 2.3, vertex sharing and components | `Geometry.Plate` defines placed intrinsic vertices, vertex adjacency, the vertex graph, reachability (`SamePlate`), and the component quotient. Accepted. |
| Lemma 2.4, one component implies integral translations | `samePlate_translation_sub_mem_integerLattice` accumulates integral differences along actual graph walks; `translations_integer_of_connected` specializes from a zero placement. Accepted. |
| Lemma 2.5, components slide | `Geometry.Sliding.exists_isSlidingDirection` proves a common nonzero stabilizer direction for every plate carrier using the local-boundary/regular-closed geometry; arbitrary independent component shifts preserve the tiling. This is a genuine stronger finite-prototile theorem. Accepted. |
| Remark 2.6 | The paper asserts no mathematical result here. The stronger finite-family organization is documented. Accepted. |
| Lemma 2.7, merge components | `Geometry.Connected.IsSlidingDirection.exists_connected_component_shift` constructs a realized potential whose shifted graph is connected; `exists_connected_tiling` and the monotile wrapper use that proof, not an assumption. Accepted. |
| Lemma 3.1(i), tileability equivalence | `RasterRigidity.PolygonalRegion.exists_integer_tiling_iff_relevantPlanarRasterTile` proves both directions. The reverse direction first proves marker-lattice rigidity for an arbitrary raster tiling, decodes one common translation set for every signature, then reconstructs the continuous integer tiling. Accepted. |
| Lemma 3.1(ii), same translation set | `RasterMarker.tiles_integerPoint_image_iff_relevantPlanarRasterTile`, together with the exact family equivalences, identifies continuous integer tiling with the coarse-scaled image of the same lattice translation set. The formal theorem is stronger than the paper's based (`0 ∈ T`) formulation. Accepted. |
| Lemma 3.1(iii), carrier equality | `RasterMarker.relevantPlanarRasterTile_carrier_eq_iff` proves literal equality in both directions. Its forward direction first gets a.e. continuous equality and then invokes locally finite regular-closed carrier uniqueness. Accepted. |
| Theorem 4.1 used by the paper | `TranslationalTilings.exists_quantitativeWeakPeriodData` constructs data depending only on the finite tile and target period and proves `ValidFor` every relevant target/tiling. `EarthquakeUniform` consumes that theorem directly. Accepted as a genuine proved imported result. |
| Definition 4.1, earthquakes | `Earthquake.quakeTransfer`, `quakeGraph`, `QuakePlate`, and `quakePlateTranslations` construct the canonical components. `quakePlateCarrier_periodic` proves carrier periodicity, while `quakePlate_minimal` proves the exact nonempty-minimality clause. Independent shifts are proved to tile by `tilesUniverse_quakeShiftedTranslations`. Accepted. |
| Lemma 4.2, uniform quake periods | `EarthquakeUniform.exists_uniformQuakePeriodicDecomposition` obtains one Greenfeld--Tao data package before quantifying over plates, uses the auxiliary quake tilings and repeated-coset pigeonhole argument, and returns one finite pairwise-incommensurable period list for every plate. The no-parallel and parallel branches are separate genuine constructions; the latter merges the residual direction with the unique parallel complete direction. The singleton tile is proved directly, and arbitrary nonempty tiles are normalized by a shift with a proved graph transport. Accepted. |

## Essential non-numbered chain and representation checks

### Open-set versus regular-closed semantics

The paper's bounded open carrier is modeled by `PolygonalRegion.openCarrier = interior support`; the
stored support is a nonempty finite union of closed nondegenerate triangles. Production proves
compactness, boundedness, closedness, `closure (interior support) = support`, null frontier, and
`interior support =ᵐ support`. Therefore the a.e. packing/covering definition is invariant under the
open/regular-closed replacement. Exact carrier equality in Lemma 3.1(iii) is not inferred directly
from an a.e. statement: the lattice carrier is proved locally finite and regular closed before the
upgrade. This representation choice is faithful.

### Rational normalization

`RationalPolygonalRegion` is a data-with-certificate presentation: it stores an intrinsic anchor,
a positive common natural denominator, and integrality of every normalized intrinsic vertex.
`normalizedRegion` translates by the anchor and clears the denominator. The forward/inverse maps
are proved mutually inverse and transport placed tiles, tilings, weak periods, and double periods;
all inverse uses discharge denominator nonzeroness. `normalized_vertex_integral` and
`normalizedRegion_hasIntegerVertices` connect the data to the integer reduction, and
`isRelativelyRational` proves the presentation satisfies the paper predicate.

I accept the common-denominator certificate as the Lean input representation rather than demanding
that every endpoint take a bare `PolygonalRegion` plus a separate predicate proof: the intrinsic
vertex set is finite, and the structure states exactly the finite common-denominator data needed by
the paper's normalization. A reverse convenience constructor from `IsRelativelyRational` could
improve ergonomics, but it is not needed to validate the statements as quantified over this
explicit rational-region presentation and has no current proof-plan consumer.

### Raster reduction and marker rigidity

The formal raster uses finitely many positive-measure lattice signatures rather than literally
implementing the paper's polygonal cell partition. The finite candidate window, measurable fibers,
almost-everywhere relevance, and continuous/exact-discrete equivalences are all proved. The marker
construction reserves a nonempty zero layer; `RasterRigidity` proves that every pair of translations
in an arbitrary exact raster tiling differs by a coarse marker-lattice element and then decodes one
common signature tiling. This validates all three mathematical properties needed from paper Lemma
3.1. The alternative representation is acceptable for Theorems 1.1 and 1.2; its noncomputability is
acceptable for those semantic existence/structure results but is exactly the problem identified in
G1 for the algorithmic corollary.

### Retaining and unshifting the original tiling

`ContinuousEarthquake` keeps the old continuous plate translation sets. It proves a nonzero
integer direction parallel to their common sliding line, including the single-plate branch, and
proves exact carrier-period transfer to every signature. `IntegerSlidingReduction` stores exact
images, disjointness, union, and the old plate carriers after connecting and basing the shifted
tiling. `quakePlateTranslations_subset_owner` uses earthquake minimality to prove each canonical
discrete plate refines one old continuous plate. Finally, `unshiftedQuakePart`,
`assembledQuakePart`, and `iUnion_assembledQuakePart` apply the owner-specific inverse shift and
prove the resulting finite disjoint union equals the original `T`. Denormalization then cancels the
initial normalization exactly. This closes the delicate gap between weak periodicity of a
replacement integer tiling and weak periodicity of every original tiling.

### Periodic completion

`exists_doublyPeriodic_integer_tiling_of_tileable_raster` applies the proved upstream
`TranslationalTilings.theorem_1_5` to the raster with target `univ`, preserves the scalar period
through arbitrary raster decoding, reconstructs a continuous integer tiling, and turns the two
coordinate scalar periods into linearly independent real periods. The inverse affine map preserves
linear independence because the scaling factor is nonzero. This is a complete semantic proof of
Theorem 1.1.

## Trust and build evidence

- `python3 blueprint/rational-polygonal/validate.py --check` passed:
  `PASS: 20 modules, 539 declarations, 333 theorem trust closures, documentation clean`.
- The validator performs a fresh Lake build, regenerates and compares the declaration ledger,
  elaborated signatures, public definition bodies, and artifact hashes, strictly compiles all 20
  sources with warnings as errors, runs documentation lint, compiles the committed validator, and
  audits every public theorem/lemma with `#print axioms`.
- A separate targeted `#print axioms` pass covered `theorem_1_1`, `theorem_1_2`, `corollary_1_1`,
  `exists_integer_tiling`, `exists_integer_tiling_iff_relevantPlanarRasterTile`,
  `exists_uniformQuakePeriodicDecomposition`, `exists_quantitativeWeakPeriodData`,
  `TranslationalTilings.theorem_1_5`, and `planarTileDecision_eq_true_iff`. Every closure contained
  only `propext`, `Classical.choice`, and `Quot.sound`.
- A production-source search found no `sorry`, `admit`, project `axiom`, unsafe theorem endpoint,
  or generated-validator import.
- The generated `BlueprintValidation.lean` consists of imports and `#check` commands and is never
  imported by production.

## Global-rubric disposition

1. **Mathematical intent:** G1 blocks only the algorithmic corollary; the semantic proof graph is
   faithful and complete for Theorems 1.1 and 1.2.
2. **Reusable seams:** clear. The geometry, sliding, raster, earthquake, and period-transport seams
   are real concepts with multiple consumers; no further extraction is required for correctness.
3. **Public API and theorem shape:** G1. Other paper-facing endpoints are thin and canonical.
4. **Module and dependency design:** clear. General geometry precedes rational specialization;
   discrete weak periodicity, completion, and algorithms enter only at their consumers.
5. **Mathlib/project integration:** clear. Existing `TranslationalTilings` production endpoints are
   imported and used rather than duplicated or assumed.
6. **Proof architecture:** clear. Hard geometric, marker-rigidity, earthquake, and transport
   boundaries are named and consumed through proved APIs.
7. **Cost and durability:** clear on available evidence. The strict validation/build completes;
   no unmeasured performance claim or resource-limit workaround is part of this finding.
8. **Refactor risk:** the required repair should be additive through the existing verified raster
   backend. Semantic theorem statements and frozen proof bodies should remain stable.

## Explicit do-not-refactor decisions and local-proof handoff

- Do not replace the regular-closed support model merely to imitate open-set notation; the proved
  a.e. and exact-equality bridges are the correct abstraction boundary.
- Do not weaken the common-denominator rational presentation or remove explicit denominator
  positivity; it makes normalization dependencies visible.
- Do not rewrite the stronger finite-family sliding/connected results into paper-specific monotile
  proofs; their generality is genuine and already reused.
- Do not replace the signature raster solely to copy the paper's cell notation; the current
  semantic equivalences and marker rigidity suffice for the two theorem proofs.
- Do not treat classical choice or other semantic noncomputability as a defect in Theorems 1.1 and
  1.2. The executable Corollary boundary is the only place where it is blocking.
- No local tactic-golfing, warning-cleanup, or proof-only handoff is required by this mathematical
  review.

## Acceptance condition

After G1 is repaired, a fresh independent review should execute the raw compiler on representative
valid inputs (including disconnected regions and holes), inspect the compiler-correctness proof,
confirm that the strengthened `corollary_1_1` quantifies over the raw effective input rather than an
already compiled raster, and rerun every seal/build/trust gate. Until then the correct release
description is: **Theorems 1.1 and 1.2 are formalized; Corollary 1.1 is verified only from the
post-raster finite input boundary.**
