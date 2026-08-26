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

## Integer lattice bridge

The discrete plane is `TranslationalTilings.Plane = Fin 2 → ℤ`.  The continuous embedding is the
additive map

```text
z ↦ (z 0 : ℝ) + (z 1 : ℝ) I.
```

The image is packaged as `integerLattice : AddSubgroup Plane`; `mem_integerLattice_iff` and
`integerPoint_injective` provide the exact bridge used in the arithmetic and period proofs.
Inverse normalization always cites `denominator_pos` before dividing.
