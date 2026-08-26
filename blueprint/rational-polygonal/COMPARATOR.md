# Paper-to-Lean comparator

This comparator targets de Dios Pont--Grebík--Greenfeld--Madrid,
*Periodicity and decidability of translational tilings by rational polygonal sets*,
arXiv:2408.02151v2.  Declaration-level coverage is generated from production by
`validate.py`; this file records the mathematical correspondence and, in particular, the one
remaining effective-input boundary.

## Representation contract

| Paper object | Lean object | Bridge implemented in production |
| --- | --- | --- |
| Bounded open polygonal set `Ω` | `PolygonalRegion.support`, a nonempty regular-closed finite union of nondegenerate triangles | `PolygonalRegion.openCarrier` and `openCarrier_ae_eq` identify the paper's open carrier with the support for the a.e. tiling relation. |
| Intrinsic vertices `V(Ω)` | `vertexSet support` | The polygonal topology API proves finiteness and independence from a chosen triangulation. |
| Relative rationality | `RationalPolygonalRegion` | The structure records an anchor and one positive common denominator; `normalizedRegion` has integral vertices and the forward/inverse affine translation maps transport tilings and periods. |
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
| Corollary 1.1 | `Decision`/`Main`: `RasterPresentation.tileDecision_decidesTileability`, `RationalPolygonalRegion.corollary_1_1` | one executable Boolean algorithm is proved correct for every valid finite compiled raster presentation; the raw finite rational-vertex-to-raster compiler described below remains outside the executable API |
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
| Definition 4.1 | `Earthquake`: `quakeTransfer`, `quakeGraph`, `QuakePlate`, carrier periodicity and minimality | proved |
| Lemma 4.2 | `EarthquakeUniform`: `exists_uniformQuakePeriodicDecomposition` | proved, including singleton and normalization cases |

## Essential non-numbered proof chain

The headline results additionally use the following genuine declarations.

1. `normalizedRegion_hasIntegerVertices`, `normalizedRegion_tiles`, and
   `tiles_of_normalizedRegion_tiles` implement affine normalization and inverse transport.
2. `signature`, `relevantSignatures`, and the a.e. signature lemmas reduce a continuous integer
   tiling to one common exact tiling problem for finitely many lattice tiles.
3. `RasterMarker`, `RigidFrame`, and `RasterRigidity` construct the marker tile, prove its frame
   rigidity, and decode arbitrary raster tilings back to one common signature translation set.
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
9. `exists_doublyPeriodic_integer_tiling_of_tileable_raster` applies periodic completion to the
   raster tile and decodes the result, proving Theorem 1.1.

## Imported paper-scale results

The development imports the already proved Greenfeld--Tao production API in this repository:

- `TranslationalTilings.exists_quantitativeWeakPeriodData` for the uniform weak-period data used
  in Lemma 4.2;
- `TranslationalTilings.theorem_1_5` for periodic completion; and
- `TranslationalTilings.planarTileDecision` together with
  `planarTileDecision_eq_true_iff` for the bounded finite raster search.

The generated file `BlueprintValidation.lean` contains only `#check` commands.  No production file
imports it, and the trust pass accepts only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining effective-input obligation

The semantic `RationalPolygonalRegion` contains a real set and proof witnesses and therefore is
not executable data.  Production currently makes the next boundary explicit:

```lean
structure RasterPresentation where
  rasterTile : Finset IntegerPlane

RasterPresentation.Represents P K
RasterPresentation.tileDecision P : Bool
```

`DecidesTileability` is the universal correctness contract,
`tileDecision_decidesTileability` supplies its executable witness, and paper-facing
`corollary_1_1` states the literal existence of that algorithm.  Every semantic region has a valid
code by `exists_representation`; the search and its counted cost are executable on the code.  The
paper, however, starts from a
finite rational polygon description and says to compute the normalization, cell signatures, and
raster.  A fully literal computational formalization of that sentence still requires an
executable finite rational-polygon input type and a verified compiler from its vertices/edges to
`RasterPresentation`.  Until that compiler is implemented or an independent review accepts the
compiled raster as the formal input representation, Corollary 1.1 is recorded as complete from
the post-raster finite boundary, not as a bit-level decision procedure on raw vertex lists.
