# 3. Raster encoding

## Fundamental-cell signatures

For a bounded polygonal region `K` and `u : Plane`, production defines

```lean
K.signature u : Finset IntegerPlane
```

whose members are exactly the lattice points `z` for which `u + integerPoint z ∈ K.support`.
Compactness bounds every signature by the finite `signatureWindow`.  `candidateSignatures` is the
finite powerset of that window, `signatureFiber K F` is the corresponding measurable unit-cell
fiber, and `relevantSignatures` retains precisely the fibers of nonzero volume.

The key measure-theoretic chain proves:

```text
K tiles by integerPoint '' T
  ↔ almost every signature tiles ℤ² by T
  ↔ every relevant signature tiles ℤ² by T.
```

The last equivalence is `tiles_integerPoint_image_iff_relevantSignatures`.  The family is
nonempty, and one member is explicitly chosen nonempty for marker rigidity.

## Marker family and single raster tile

`RasterMarker` enumerates the relevant signatures and constructs a planar marker block for each
color.  Its square has side `3M + 4`; nonzero colors use separated eight-point rings, while the
zero color is the square remainder with two protrusions and two matching holes.  The module proves
block disjointness, the exact modified-square union, marker-lattice tiling, and the forward
simultaneous-family encoding.

`RasterRigidity` proves directly that the modified-square frame and asymmetric fillers leave no
relative placement freedom modulo the marker lattice.  It shows that every exact tiling by the
raster tile lies in one marker-lattice coset, then decodes that coset to one common translation set
for all source signatures.  There is no parallel special-case frame module.

The canonical finite tile is

```lean
K.relevantPlanarRasterTile : Finset IntegerPlane.
```

It is a genuine definition, not a structure field whose specification is assumed.

## Paper Lemma 3.1

- Part (i), existence: `exists_integer_tiling_iff_relevantPlanarRasterTile` proves that `K` has an
  integer-translation tiling iff its single raster tile has an arbitrary exact lattice tiling.
- Part (ii), same translation data: `tiles_integerPoint_image_iff_relevantPlanarRasterTile` proves
  the equivalence for the explicitly scaled marker translation set; rigidity supplies the converse
  for an arbitrary raster tiling.
- Part (iii), carriers: `relevantPlanarRasterTile_discreteCarrier_eq_iff` gives exact equality for
  every relevant discrete carrier.  The initial continuous comparison is a.e.;
  `locallyFinite_integerTranslates` and `integerTranslationCarrier_closure_interior` prove that
  both carriers are regular closed, and `relevantPlanarRasterTile_carrier_eq_iff` concludes the
  literal continuous-carrier equivalence stated by the paper.

The construction has no empty-color escape hatch: `relevantSignatures_nonempty` and
`distinguishedRelevantSignature_nonempty` provide a genuine nonempty zero marker layer.

## Executable raw compiler

The effective path begins with the computed integer triangles from `RawInput`:

1. `LinearFeasibility` supplies a verified rational Fourier--Motzkin solver for finite strict
   systems in two variables.
2. `SignatureCompiler` computes a finite offset window, all translated triangle-edge lines,
   feasible strict sign cells in the open unit square, one exact rational sample per cell, and the
   deduplicated `signatureFamily` of finite lattice signatures.
3. `SignatureCorrectness` proves
   `signatureFamily_toFinset_eq_relevantSignatures`: the executable unordered family is exactly
   the semantic positive-measure family.  The proof includes offset-window completeness, rational
   density in nonempty open cells, null exceptional boundaries, and exact triangle membership.
4. `ComputableMarker` proves the executable array-indexed marker constructors extensionally equal
   the semantic marker geometry.  `nonemptyRasterFamily?` moves a known nonempty signature to color
   zero, and `planarRasterTileExec` produces the actual finite lattice tile.

The live frontend regression computes the signature family of the normalized unit right triangle:
the deduplicated family has length `2` and signature cardinalities `[1, 0]`.  It deliberately stops
before the potentially enormous final exhaustive tiling search.

`Decision.RasterPresentation` remains a useful compiled-backend abstraction.  `Represents P K`
states that its finite tile is the canonical semantic raster, while `tileDecision` and its exact
counted cost expose the bounded planar search.  The paper-facing raw algorithm instead lives in
`RawDecision` and obtains its finite raster by the verified executable pipeline above.
