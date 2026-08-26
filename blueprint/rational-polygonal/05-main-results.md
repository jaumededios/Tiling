# 5. Main results

## Theorem 1.1

The reverse implication is immediate: a periodic tiling is a tiling.

For the forward implication:

1. normalize the rational polygonal region to integral vertices;
2. apply Lemma 2.2 to obtain an integer translation tiling;
3. construct the raster tile and use Lemma 3.1(ii);
4. scale it to a finite tile in `TranslationalTilings.Plane`;
5. apply `TranslationalTilings.Main.theorem_1_5` to obtain a scalar-periodic discrete tiling;
6. decode it through Lemma 3.1(ii); and
7. undo the affine normalization, transporting two independent periods.

## Corollary 1.1

The executable input is a finite rational presentation of the polygonal region.  The program:

1. computes an integral normalization;
2. computes the finite signature family and marker raster tile;
3. calls `TranslationalTilings.planarTileDecision` on the scaled integer tile; and
4. returns the resulting Boolean.

Correctness is Lemma 3.1(i) plus
`TranslationalTilings.Main.corollary_1_6`.  The public theorem states the Boolean specification; the
program is not represented merely by an existential proposition.

## Theorem 1.2

For an arbitrary tiling `T`:

1. normalize the rational tile;
2. obtain the common rational sliding direction and continuous plate decomposition;
3. choose shifts merging the plates into the integer tiling `T'`;
4. rasterize `T'`;
5. refine every shifted continuous plate by the canonical discrete earthquake decomposition;
6. apply Lemma 4.2 to every quake plate using one finite list of directions;
7. regroup the resulting periodic pieces inside each original plate; and
8. undo the plate shifts and affine normalization.

The result is a finite disjoint decomposition of the original translation set into subsets with
nonzero real periods, exactly Definition 1.2(ii).

## Terminal API rule

`Tiling.RationalPolygonal.Main` contains only the three paper-facing endpoints and explicitly
named quantitative/executable refinements.  Every geometric, raster, and earthquake proof is
owned below it.

