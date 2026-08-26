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

`RigidFrame` proves that the modified-square frame has no relative placement freedom modulo the
marker lattice.  `RasterRigidity` combines the frame and fillers to show that every exact tiling by
the raster tile lies in one marker-lattice coset, then decodes that coset to one common translation
set for all source signatures.

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
  every relevant discrete carrier, and
  `integerTranslationCarrier_ae_eq_of_relevantPlanarRasterTile` transports this to the continuous
  carrier at the a.e. strength of `PolygonalRegion.Tiles`.

The construction has no empty-color escape hatch: `relevantSignatures_nonempty` and
`distinguishedRelevantSignature_nonempty` provide a genuine nonempty zero marker layer.

## Executable boundary

`Decision.RasterPresentation` stores the resulting `Finset IntegerPlane`; `Represents P K` states
that it is definitionally the canonical normalized raster.  `tileDecision` and its exact counted
cost are executable on this finite data.  Constructing the raster from the semantic real-set
structure is noncomputable, so a raw rational-coordinate compiler is tracked separately in the
comparator rather than being silently identified with this stage.

