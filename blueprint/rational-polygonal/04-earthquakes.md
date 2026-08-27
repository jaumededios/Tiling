# 4. Discrete earthquakes and continuous compatibility

## Canonical decomposition

Let `F` tile `ℤ²` with translation set `T`, and let `v ≠ 0`.  `quakeTransfer F T v t t'` records
one transfer forced by moving a represented lattice point by `v`; `quakeGraph` is its symmetric
simple graph on the subtype `T`.  A `QuakePlate` is a connected component of this graph and
`quakePlateTranslations` forgets the subtype witness.

`Earthquake.lean` proves the clauses needed for paper Definition 4.1:

- the plate translation sets partition `T` and are pairwise disjoint;
- `discreteCarrier F (quakePlateTranslations C)` is invariant under `v`;
- a periodic carrier subset containing one point of `C` contains the whole component
  (`quakePlateTranslations_subset_of_mem_periodic`); and
- independent integer multiples of `v` assigned to the components preserve exact tiling
  (`tilesUniverse_quakeShiftedTranslations`).

Thus the tectonic plates are constructed canonically; their defining properties are not assumed.

## Uniform decomposition (Lemma 4.2)

`EarthquakeUniform` applies `exists_quantitativeWeakPeriodData` to the first `m + 1` indexed quake
shifts.  On every lattice coset two indices select the same one of `m` directions.  Complete
orbits inherit that selected period; the residual incomplete orbits receive the nonzero factorial
multiple of the quake direction.

`UniformQuakePeriodicDecomposition` records one finite family of nonzero, pairwise
incommensurable periods, and for every quake plate a pairwise-disjoint partition by subsets with
those periods.  The proof handles:

- the case where no Greenfeld--Tao direction is parallel to the quake direction;
- the parallel case, where the two commensurable parts are merged and the unique parallel period
  is replaced by a common multiple;
- singleton finite tiles directly; and
- arbitrary nonempty tiles by translating a chosen tile point to the origin.

The terminal declaration is `exists_uniformQuakePeriodicDecomposition`.

## Compatibility with the original continuous tiling

Theorem 1.2 requires periodicity of the *given* translation set, not merely existence of a nicer
tiling.  Three modules retain this information:

1. `ContinuousEarthquake` defines the original continuous plate translation sets, proves their
   exact partition and pairwise disjointness, chooses a nonzero integer vector parallel to their
   common sliding direction, and proves component shifts preserve the tiling and the plate
   partition.
2. `IntegerSlidingReduction` packages a connected based integer realization while retaining, for
   every old continuous plate, its exact lattice image and the common period of all signature
   carriers.  `quakePlateTranslations_subset_owner` then proves each canonical quake plate lies
   in one old plate.
3. `WeakPeriodicity` applies the uniform decomposition on every relevant signature, unshifts each
   periodic part by its old plate's displacement, and unions all pieces carrying the same period.
   `assembledQuakePart_periodic`, `assembledQuakePart_pairwiseDisjoint`, and
   `iUnion_assembledQuakePart` prove that the result is a finite disjoint decomposition of the
   original translation set.

Finally `Tiles.weaklyPeriodic_of_integerVertices` proves the integer-vertex theorem and
`RationalPolygonalRegion.Tiles.weaklyPeriodic` transports it through inverse rational
normalization.

