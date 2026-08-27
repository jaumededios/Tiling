# Paper-to-Lean comparator

This comparator targets de Dios Pont--Grebík--Greenfeld--Madrid,
*Periodicity and decidability of translational tilings by rational polygonal sets*,
arXiv:2408.02151v2.  Declaration-level coverage is generated from production by
`validate.py`; this file records the mathematical correspondence, including the complete
effective pipeline from finite rational triangulations to the bounded lattice decision.

## Representation contract

| Paper object | Lean object | Bridge implemented in production |
| --- | --- | --- |
| Bounded open polygonal set `Ω` | `PolygonalRegion.support`, a nonempty regular-closed finite union of nondegenerate triangles | `PolygonalRegion.openCarrier` and `openCarrier_ae_eq` identify the paper's open carrier with the support for the a.e. tiling relation. |
| Intrinsic vertices `V(Ω)` | `vertexSet support` | The polygonal topology API proves finiteness and independence from a chosen triangulation. |
| Relative rationality | `RationalPolygonalRegion` | The structure records an anchor and one positive common denominator; `normalizedRegion` has integral vertices and the forward/inverse affine translation maps transport tilings and periods. |
| Finite rational polygon input | `Raw.Code.Input`, whose runtime `Raw.Code` is a list of rational triangles and whose `Valid` field is proof-only geometry | `Raw.Code.Input.rationalPolygonalRegion` interprets the code semantically; executable common-denominator normalization is identified with `normalizedRegion` by the `RawInput` support and carrier theorems. |
| `Ω ⊕ T = ℝ²` a.e. | `PolygonalRegion.Tiles T` | A unit-labelled `Tiling.IsTiling`; `Tiles.countable` and `Tiles.ae_existsUnique_translation` expose the countable unique-representation form. |
| `F ⊕ A = ℤ²` exactly | `TranslationalTilings.TilesUniverse F A` | The existing exact finite convolution/unique representation API is used by rasterization and earthquakes. |
| singly/weakly/doubly periodic real set | `SinglyPeriodic`, `WeakPeriodicDecomposition`/`WeaklyPeriodic`, `DoublyPeriodic` | These use genuine real periods; integer-period embeddings and inverse affine transport are proved, not definitional identifications. |
| periodic structure in `ℤ²` | `SetScalarPeriodic`, `QuantitativeWeakPeriodData`, and related Greenfeld--Tao declarations | The imported project results are genuine production theorems; no generated validator is imported. |

The raster argument first obtains an almost-everywhere continuous carrier comparison, matching
the repository's `IsTiling` semantics.  `integerTranslationCarrier_closure_interior` proves that
arbitrary lattice-translation carriers are locally finite regular-closed unions, so
`relevantPlanarRasterTile_carrier_eq_iff` upgrades this to the literal equality stated in paper
Lemma 3.1(iii).

## Numbered results

| Paper item | Lean owner / declaration | Status |
| --- | --- | --- |
| Definition 1.2(i) | `Basic`: `SinglyPeriodic` | proved |
| Definition 1.2(ii) | `Basic`: `WeakPeriodicDecomposition`, `WeaklyPeriodic` | proved |
| Definition 1.2(iii) | `Basic`: `DoublyPeriodic` | proved |
| Theorem 1.1 | `Main`: `RationalPolygonalRegion.theorem_1_1` | proved |
| Corollary 1.1 | `RawDecision`/`Main`: `Raw.Decision.rawTileDecision_decidesRawTileability`, `RationalPolygonalRegion.corollary_1_1` | proved by one total Boolean on every valid finite rational triangulation; normalization, signature enumeration, marker compilation, and semantic correctness are all in production |
| Theorem 1.2 | `WeakPeriodicity`/`Main`: `RationalPolygonalRegion.Tiles.weaklyPeriodic`, `RationalPolygonalRegion.theorem_1_2` | proved for every given tiling |
| Definition 2.1 | `IntegerReduction`: `PolygonalRegion.IsIntegerTiling` | proved definition |
| Lemma 2.2 | `IntegerReduction`: `PolygonalRegion.exists_integer_tiling` | proved |
| Definition 2.3 | `Geometry.Plate`: vertex adjacency, `vertexGraph`, `SamePlate`, and plate quotient | proved |
| Lemma 2.4 | `IntegerReduction`: `samePlate_translation_sub_mem_integerLattice` | proved |
| Lemma 2.5 | `Geometry.Sliding`: `exists_isSlidingDirection` | proved in the finite-prototile setting |
| Remark 2.6 | comparator/prose | represented by the rational/integer plate compatibility discussion; no theorem is asserted in the paper |
| Lemma 2.7 | `Geometry.Connected` and `IntegerReduction`: `exists_connected_component_shift`, `exists_connected_tiling` | proved in a stronger finite-family form and specialized to monotiles |
| Section 3 discrete tiling | `TranslationalTilings.TilesUniverse` | proved upstream |
| Lemma 3.1(i) | `RasterRigidity`: `PolygonalRegion.exists_integer_tiling_iff_relevantPlanarRasterTile` | proved |
| Lemma 3.1(ii) | `RasterMarker`: `tiles_integerPoint_image_iff_relevantPlanarRasterTile` plus exact family decoding | proved |
| Lemma 3.1(iii) | `RasterMarker`: `relevantPlanarRasterTile_carrier_eq_iff` | proved with literal equality on both raster and continuous carriers |
| Theorem 4.1 used by the paper | `TranslationalTilings.exists_quantitativeWeakPeriodData` and its validity API | proved upstream and consumed in `EarthquakeUniform` |
| Definition 4.1 | `DiscreteCarrier`/`Earthquake`: `quakeTransfer`, `quakeGraph`, `QuakePlate`, carrier periodicity and minimality | proved |
| Lemma 4.2 | `EarthquakeUniform`: `exists_uniformQuakePeriodicDecomposition` | proved, including singleton and normalization cases |

## Essential non-numbered proof chain

The headline results additionally use the following genuine declarations.

1. `normalizedRegion_hasIntegerVertices`, `normalizedRegion_tiles`, and
   `tiles_of_normalizedRegion_tiles` implement affine normalization and inverse transport.
2. `signature`, `relevantSignatures`, and the a.e. signature lemmas reduce a continuous integer
   tiling to one common exact tiling problem for finitely many lattice tiles.
3. `RasterMarker` and `RasterRigidity` construct the marker tile, prove its frame rigidity, and
   decode arbitrary raster tilings back to one common signature translation set.
4. `quakePlateCarrier_periodic`, `quakePlate_minimal`, and
   `tilesUniverse_quakeShiftedTranslations` establish the canonical earthquake decomposition and
   the validity of independent plate shifts.
5. `exists_uniformQuakePeriodicDecomposition` proves one finite period list works for every quake
   plate of a fixed tiling and quake direction.
6. `ContinuousEarthquake` preserves the original continuous plates while connecting the shifted
   tiling; `IntegerSlidingReduction` retains their exact lattice images and raster-carrier period.
7. `quakePlateTranslations_subset_owner` proves canonical discrete quake plates refine those old
   continuous plates.
8. `IntegerSlidingReduction.weakPeriodicDecomposition` unshifts and regroups the uniform quake
   parts, producing a finite disjoint periodic decomposition of the *original* translation set.
9. `Raw.Code.Input.normalizedSupport_eq_normalizedCodeSupport`, the verified rational
   Fourier--Motzkin solver, and `signatureFamily_toFinset_eq_relevantSignatures` prove that the
   executable normalized triangle compiler enumerates exactly the semantic signature family.
10. `planarRasterTileExec_eq_planarRasterTile` and
    `rawTileDecision_decidesRawTileability` connect that family to the rigid marker and bounded
    lattice decision, proving Corollary 1.1 on raw rational input.
11. `exists_doublyPeriodic_integer_tiling_of_tileable_raster` applies periodic completion to the
    semantic raster tile and decodes the result, proving Theorem 1.1.

## Imported paper-scale results

The development imports the already proved Greenfeld--Tao production API in this repository:

- `TranslationalTilings.exists_quantitativeWeakPeriodData` for the uniform weak-period data used
  in Lemma 4.2;
- `TranslationalTilings.theorem_1_5` for periodic completion; and
- `TranslationalTilings.planarTileDecision` together with
  `planarTileDecision_eq_true_iff` for the bounded finite raster search.

The generated file `BlueprintValidation.lean` contains only `#check` commands.  No production file
imports it, and the trust pass accepts only `propext`, `Classical.choice`, and `Quot.sound`.

## Executable raw-input closure

The semantic `RationalPolygonalRegion` still intentionally contains a real set and proof witnesses;
it is not treated as runtime data.  Corollary 1.1 instead uses:

```lean
Raw.Code.Input
Raw.Decision.rawTileDecision : Raw.Code.Input → Bool
Raw.Decision.DecidesRawTileability rawTileDecision
```

The runtime code is a finite list of rational triangles.  Its `Valid` field certifies the
paper-domain geometric assumptions and is proof-only; it contains neither a raster nor an answer.
`RawInput` computes the anchor, common denominator, and integer triangles.  `SignatureCompiler`
uses the verified `LinearFeasibility` solver to enumerate rational samples for all strict
arrangement cells.  `SignatureCorrectness` proves that the resulting unordered signature family
is exactly `relevantSignatures`; `ComputableMarker` constructs the rigid finite tile; and
`RawDecision` runs `planarTileDecision` and proves the real-plane tileability equivalence.

The older `RasterPresentation` declarations remain as a reusable compiled-backend API and exact
cost interface.  They no longer carry the paper-facing Corollary 1.1 claim.  Thus the effective
input obligation recorded by the initial independent reviews is closed in production, while those
historical BLOCK reports remain unchanged as reviews of their original sealed snapshot.
