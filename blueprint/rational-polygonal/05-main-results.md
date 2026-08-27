# 5. Main results

## Theorem 1.1

The reverse implication is immediate.  For the forward implication, production performs the
paper's chain:

1. `normalizedRegion_tiles` sends the assumed rational tiling to an integer-vertex region.
2. `exists_integer_signature_tiling` replaces it by an integer translation tiling.
3. `exists_integer_tiling_iff_relevantPlanarRasterTile` obtains a tiling by the finite raster.
4. `TranslationalTilings.theorem_1_5` replaces that raster tiling by a scalar-periodic one.
5. Marker rigidity decodes one scalar-periodic translation set tiling every relevant signature.
6. `tiles_integerPoint_image_iff_relevantSignatures` decodes a continuous integer tiling.
7. Two coordinate periods embed as linearly independent real periods, and inverse normalization
   transports them to the original rational region.

`RationalPolygonalRegion.theorem_1_1` states exactly that a rational polygonal region tiles the
plane iff it admits a doubly periodic translation tiling.

## Corollary 1.1

The paper-facing executable layer is:

```lean
Raw.Decision.rawTileDecision : Raw.Code.Input → Bool
```

Its input contains a finite list of rational triangles together with proof-only geometric validity.
Execution computes the common-denominator integer normalization, enumerates the exact semantic
signature family using the verified rational feasibility solver, moves a nonempty signature to
marker color zero, constructs the executable planar raster, and invokes the bounded exhaustive
`planarTileDecision`.

`Raw.Decision.DecidesRawTileability` is the universal correctness contract, and
`rawTileDecision_decidesRawTileability` proves it for the total Boolean.  Consequently
`RationalPolygonalRegion.corollary_1_1` has the literal raw-input existential type, while
`corollary_1_1_spec` is its pointwise specialization on `Raw.Code.Input`.

`RasterPresentation.tileDecision` and `tileDecisionCost` remain public compiled-backend support,
with `tileDecision_eq_true_iff` relating a certified compiled raster to its semantic region.  They
are no longer presented as the paper's input representation.  Validation exercises fractional
denominator clearing and a complete small signature-family computation, but does not run the
enormous final tiling search.

## Theorem 1.2

For an arbitrary given tiling `T`:

1. normalize the rational tile to integral vertices;
2. retain the common integer sliding direction and old continuous plate partition while shifting
   the tiling to a connected integer realization;
3. prove every signature-carrier quake plate refines one old continuous plate;
4. apply Lemma 4.2 to obtain a common finite period list for all quake plates;
5. undo each old plate shift inside each periodic part;
6. regroup equal-period parts, retaining pairwise disjointness and exact union; and
7. undo rational normalization.

The resulting `WeakPeriodicDecomposition` has union exactly the original translation set.
`RationalPolygonalRegion.theorem_1_2` is therefore the paper theorem for every supplied tiling,
not an existence theorem about a replacement tiling.

## Terminal API

`Tiling.RationalPolygonal.Main` exposes the three exact paper names:

- `RationalPolygonalRegion.theorem_1_1`;
- `RationalPolygonalRegion.corollary_1_1`; and
- `RationalPolygonalRegion.theorem_1_2`.

All geometric, raster, earthquake, and executable proof bodies live in their owning lower modules.
