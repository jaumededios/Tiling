# 3. Raster encoding

## Fundamental-cell signatures

For a bounded measurable region `K` and a fundamental-cell point `u`, define the finite signature

```text
signature K u = {z ∈ ℤ² | u + z ∈ K}.
```

Boundedness supplies one finite box containing every possible signature.  Hence the set of
signatures is finite without constructing the planar line arrangement from the exposition.

The relevant colors are precisely the signatures whose fibers inside the half-open unit cell have
positive volume.  Every other fiber is null, and there are only finitely many of them.  This gives:

```text
K tiles by an integer translation set T
  ↔ every positive-measure signature tiles ℤ² by the same T.
```

This is the measure-theoretic form of the paper's partition into `P₀, …, Pₘ₋₁`.  For a polygonal
region the positive-measure fibers are unions of the paper's open cells, so it has the same tiling
content.

## Marker family

For `M` colors choose the least `k > 0` with `M ≤ k²` and put `N = 3k + 4`.  Production implements
the paper's sets exactly:

- for `1 ≤ i < M`, `Sᵢ` is the eight-point ring around `(3aᵢ,3bᵢ)`;
- `S₀` is the remaining `N × N` square, with protrusions `(N,1),(1,N)` and holes
  `(0,1),(1,0)`.

The marker proof is split into:

1. disjointness and the exact modified-square union;
2. rigidity: every tiling by a raster tile containing a nonempty `S₀` layer has all translation
   vectors in one coset of `Nℤ²`;
3. residue decoding: after normalization to that coset, residue `Sᵢ` reads exactly the tiling
   equation for color `i`; and
4. carrier decoding for arbitrary subsets, used by Lemma 3.1(iii).

## Canonical raster data

`RasterEncoding K` records only constructed data and proved specifications:

- positive `N`;
- a finite integer tile `F`;
- the finite positive-measure signature family; and
- exact proofs of Lemma 3.1(i)--(iii).

The structure itself is not an assumption to the paper-facing theorems.  Production proves
`exists_rasterEncoding` from bounded polygonality and integer normalization, then the three public
lemmas project its fields.

The empty-signature case is explicit: it certifies that no integer translation tiling exists and
the raster tile is chosen to be nontiling.  No proof relies on an unspoken nonempty color.

