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

For `T : Set Plane`, the corresponding `ProtoTiling Plane Unit` is

```lean
{p | p.1 ∈ T}
```

with the sole unit label.  The API exposes both directions between membership in `T` and membership
of `(t, ())` in this placement set.  `IsMonotileTiling K T` abbreviates `Tiling.IsTiling` for this
family, while a separate theorem gives its countable, unique-representation-a.e. characterization.

## Relative rationality

The source definition is not “all vertices are absolutely rational”.  The correct predicate is

```text
there is v in vertexSet K such that every w in vertexSet K has w - v in ℚ².
```

Finiteness of `vertexSet K` supplies a common positive denominator `n`.  Translation by `-v` and
dilation by `n` produce an integer-vertex polygonal region.  The normalization certificate records
the forward and inverse affine maps and proves transport of:

- the tiling relation;
- emptiness/nonemptiness of the tiling space;
- single, weak, and double periodicity; and
- the finite input presentation used by the decision procedure.

The normalizing linear factor is nonzero and positive.  Every use of the inverse map cites that
fact explicitly.

## Integer lattice bridge

The discrete plane is `TranslationalTilings.Plane = Fin 2 → ℤ`.  The continuous embedding is the
additive map

```text
z ↦ (z 0 : ℝ) + (z 1 : ℝ) I.
```

The image is packaged as an additive subgroup of `ℂ`, with an additive equivalence from the
discrete plane.  Scaled lattices use a positive natural denominator and never divide by an
unproved nonzero scalar.

