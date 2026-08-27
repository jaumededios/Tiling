# 1. Model and rational normalization

## Polygonal regions

The production model stores the regular-closed representative `K = closure Ω` of the paper's
bounded open polygonal set.  It requires:

- `IsPolygonal K`;
- `K.Nonempty`; and
- the inherited measurable, compact, bounded, regular-closed, and null-frontier facts.

The paper-facing carrier is `interior K`.  Since `volume (frontier K) = 0`, replacing `interior K`
by `K` preserves the a.e. packing and covering relation.  Exact set equality is used only after a
regular-closed/local-finite bridge.

## Monotile placement sets

For `T : Set Plane`, `PolygonalRegion.placements T` is the corresponding
`ProtoTiling Plane Unit`:

```lean
{p | p.1 ∈ T}
```

with the sole unit label.  `PolygonalRegion.Tiles K T` abbreviates `Tiling.IsTiling` for this
family.  `Tiles.countable` proves countability, while `Tiles.ae_existsUnique_translation` supplies
the unique-representation-a.e. form used by rasterization.

## Relative rationality

The source notion is not “all vertices are absolutely rational”.  The predicate
`IsRelativelyRational` is

```text
there is v in vertexSet K such that every w in vertexSet K has w - v in ℚ².
```

The paper-facing structure `RationalPolygonalRegion` stores the selected anchor, one positive
common denominator, and the proof that every normalized intrinsic vertex is integral.  Translation
by the anchor and dilation by that denominator produce `normalizedRegion`.  The API defines the
forward and inverse translation maps and proves transport of:

- the tiling relation in both directions;
- weak periodicity under inverse normalization; and
- double periodicity under inverse normalization.

The normalizing linear factor is nonzero and positive.  Every use of the inverse map cites that
fact explicitly.

## Raw rational input and executable normalization

`Raw.Code` is finite runtime data: a list of `Raw.QTriangle` values whose vertices are pairs of
executable rationals.  `Raw.Code.Valid` contains only proof certificates that the list is nonempty,
its triangles are nondegenerate and pairwise almost-everywhere disjoint, and the selected anchor is
an intrinsic vertex.  The paper-facing domain is `Raw.Code.Input`, which packages that proof-only
validity with the rational code; it contains no raster or decision certificate.

The executable normalization selects the first encoded vertex as anchor, computes the least common
multiple of every coordinate denominator, and maps each rational triangle to a `Raw.ZTriangle`.
The exact bridges are:

- `scaledCoordinate_cast`, identifying denominator clearing with real scalar multiplication;
- `normalizedPoint_toPlane` and `normalizedTriangle_carrier`, identifying computed vertices and
  triangle carriers with affine normalization;
- `rationalPolygonalRegion`, interpreting a valid code in the semantic model; and
- `normalizedSupport_eq_normalizedCodeSupport`, identifying the semantic normalized support with
  the finite union represented by the computed integer triangles.

The live frontend regression uses coordinates with denominators two and three: it computes common
denominator `6`, and clears `2/3` and `1/3` to the integers `4` and `2`.  This specifically guards
the fractional normalization path rather than testing only integral examples.

## Integer lattice bridge

The discrete plane is `TranslationalTilings.Plane = Fin 2 → ℤ`.  The continuous embedding is the
additive map

```text
z ↦ (z 0 : ℝ) + (z 1 : ℝ) I.
```

The image is packaged as `integerLattice : AddSubgroup Plane`; `mem_integerLattice_iff` and
`integerPoint_injective` provide the exact bridge used in the arithmetic and period proofs.
Inverse normalization always cites `denominator_pos` before dividing.
