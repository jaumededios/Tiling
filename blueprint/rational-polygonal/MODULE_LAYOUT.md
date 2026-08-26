# Module layout and dependency direction

```text
Tiling.Basic
  └─ Tiling.Geometry.Plane
      ├─ Tiling.Geometry.LocalLine
      ├─ Tiling.Geometry.PolygonalTopology
      └─ Tiling.Geometry.Plate
          └─ Tiling.Geometry.PackingTopology
              └─ Tiling.Geometry.Sliding
                  └─ Tiling.Geometry.Connected

TranslationalTilings.Main

Tiling.RationalPolygonal.Basic
  ├─ Tiling.RationalPolygonal.IntegerReduction
  ├─ Tiling.RationalPolygonal.RasterMarkers
  │    └─ Tiling.RationalPolygonal.Raster
  └─ Tiling.RationalPolygonal.Earthquake
         └─ Tiling.RationalPolygonal.Main
```

The actual project edge into `TranslationalTilings.Main` should be as low as possible:

- `RasterMarkers` and the geometric/signature half of `Raster` are independent of Greenfeld--Tao;
- `Earthquake` imports the qualitative weak-periodicity API;
- the final raster existence/decision wrappers import periodic completion and the decision API; and
- `Main` is the terminal join.

If keeping those edges separate requires splitting `Raster` into `RasterGeometry` and
`RasterConsequences`, do so rather than introducing a cycle.

## Planned production ownership

| Module | Responsibility |
| --- | --- |
| `Tiling.RationalPolygonal.Basic` | Regular-closed polygonal region, monotile placement/tiling wrappers, relative rationality, integer lattice embedding, real periodicity notions, affine transport. |
| `Tiling.RationalPolygonal.IntegerReduction` | Paper Definitions 2.1/2.3 and Lemmas 2.2/2.4; specializations of the existing sliding and connected-component theorems. |
| `Tiling.RationalPolygonal.RasterMarkers` | Explicit `Sᵢ` construction, partition identities, frame rigidity, and the generic simultaneous-family-to-single-tile theorem. |
| `Tiling.RationalPolygonal.Raster` | Fundamental-cell signatures, positive-measure pattern family, canonical raster data, and all three parts of Lemma 3.1. |
| `Tiling.RationalPolygonal.Earthquake` | Canonical quake graph/components, minimality/uniqueness, quake shifts, and Lemma 4.2 using the existing Greenfeld--Tao structure theorem. |
| `Tiling.RationalPolygonal.Main` | Thin paper-facing statements of Theorem 1.1, Corollary 1.1, and Theorem 1.2. |

## API policy

- Every public declaration must have one canonical ledger row and one informative docstring.
- Helpers stay private unless two production modules consume them.
- Definitions are validated by value/structure metadata as well as type.
- The generated validator mirrors declarations only; production never imports it.
- Imports are checked after the proof chain is stable, and no artificial edge to the full
  `TranslationalTilings.Main` umbrella is retained in lower modules.

