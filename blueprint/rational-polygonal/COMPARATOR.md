# Paper-to-Lean comparator

## Representation contract

| Paper object | Lean object | Exact bridge obligation |
| --- | --- | --- |
| Bounded open polygonal set `Ω` | `PolygonalRegion.support`, a nonempty regular-closed polygonal subset of `ℂ`; the paper's open set is `interior support` | Prove `interior support =ᵐ[volume] support`, and transport packing, covering, carrier equality, and periodicity across this a.e. equality. |
| `V(Ω)` | `vertexSet support` | Use the triangulation-independent vertex API; prove the rational-presentation and integer-normalization lemmas rather than assuming a chosen triangulation is intrinsic. |
| Rationality `V(Ω) - v ⊂ ℚ²` | `IsRelativelyRational support` | Prove equivalence with a common positive denominator and an integral translated/dilated vertex set, using finiteness of `vertexSet`. |
| `Ω ⊕ T = ℝ²` | `IsMonotileTiling Ω T`, implemented through `Tiling.IsTiling` | Prove the countable unique-representation-a.e. characterization used by rasterization. |
| `F ⊕ A = ℤ²` | `TranslationalTilings.TilesUniverse F A` | Use the existing exact finite-convolution definition and representation-count theorem. |
| Singly/weakly/doubly periodic subset of `ℝ²` | real-vector periodicity structures in `Tiling.RationalPolygonal` | Prove translation and nonzero-dilation transport.  Do not identify real and integer periods definitionally. |
| Periodic/weakly periodic subset of `ℤ²` | `TranslationalTilings.IsPeriodic` / `WeaklyPeriodic` | Reuse the fully proved Greenfeld--Tao API. |

The regular-closed model does not change any a.e. tiling assertion.  Exact carrier equalities in
Lemma 3.1(iii) and the earthquake argument are recovered from a.e. equality using local finiteness
and regular closedness; they are not weakened in the paper-facing API.

## Numbered results

| Paper item | Mathematical content | Lean owner | Status at initial recovery |
| --- | --- | --- | --- |
| Definition 1.2(i) | singly periodic set | `RationalPolygonal.Basic` | planned wrapper |
| Definition 1.2(ii) | finite disjoint weak-periodic decomposition | `RationalPolygonal.Basic` | planned wrapper and bridge |
| Definition 1.2(iii) | two independent periods | `RationalPolygonal.Basic` | planned wrapper |
| Theorem 1.1 | rational polygonal tile iff it has a periodic tiling | `RationalPolygonal.Main` | pending raster and normalization |
| Corollary 1.1 | executable decision procedure | `RationalPolygonal.Main` | pending raster and encoding algorithm |
| Theorem 1.2 | every tiling by a rational polygonal tile is weakly periodic | `RationalPolygonal.Main` | pending earthquake compatibility |
| Definition 2.1 | integer tiling | `RationalPolygonal.IntegerReduction` | pending monotile wrapper |
| Lemma 2.2 | existence of an integer tiling | `RationalPolygonal.IntegerReduction` | geometric core proved; integer-coordinate wrapper pending |
| Definition 2.3 | vertex sharing and its transitive closure | `Tiling.Geometry.Plate` plus monotile wrappers | core definitions proved |
| Lemma 2.4 | one vertex-sharing class implies integral translations | `RationalPolygonal.IntegerReduction` | pending arithmetic wrapper |
| Lemma 2.5 | all tiling components slide in one direction | `Tiling.Geometry.Sliding` | proved in stronger finite-family form |
| Remark 2.6 | comparison with rational components | documentation only | recorded, no declaration |
| Lemma 2.7 | component shifts can merge all classes | `Tiling.Geometry.Connected` | proved in stronger finite-family form |
| Section 3 discrete tiling definition | finite exact translational tiling | `TranslationalTilings.Basic` | proved |
| Lemma 3.1(i) | continuous tileability iff raster tileability | `RationalPolygonal.Raster` | pending |
| Lemma 3.1(ii) | normalized raster tilings exactly equal integer continuous tilings | `RationalPolygonal.Raster` | pending |
| Lemma 3.1(iii) | continuous carrier equality iff raster carrier equality | `RationalPolygonal.Raster` | pending |
| Theorem 4.1 | uniform weak-periodic/cosetwise structure in `ℤ²` | `TranslationalTilings.Main.theorem_1_4` | proved upstream; wrapper pending |
| Definition 4.1 | earthquake decomposition and tectonic plates | `RationalPolygonal.Earthquake` | pending canonical graph construction |
| Lemma 4.2 | every earthquake plate has a uniform finite periodic decomposition | `RationalPolygonal.Earthquake` | pending |

## Non-numbered proof obligations that receive declarations

The comparator also owns the following steps because the headline proofs depend on them:

1. affine normalization of a relatively rational polygonal region to an integer-vertex region;
2. transport of tilings and all three periodicity notions through that affine equivalence;
3. finiteness and positive-measure completeness of lattice membership signatures on a fundamental
   cell;
4. rigidity of the paper's `S₀, …, Sₘ₋₁` marker family;
5. equivalence between a common tiling of all positive-measure signatures and a tiling by the
   single raster tile;
6. the canonical earthquake graph, its component partition, carrier periodicity, and minimality;
7. earthquake shifts preserve exact discrete tilings;
8. refinement of continuous sliding plates by discrete earthquake plates; and
9. transport of the resulting finite period list back through sliding and rational normalization.

## Imported results

The only paper-scale imported mathematical results are proved production declarations in this
repository:

- `TranslationalTilings.Main.theorem_1_4` for the uniform cosetwise weak-periodic structure;
- `TranslationalTilings.Main.theorem_1_5` for periodic completion; and
- `TranslationalTilings.Main.corollary_1_6` for the counted decision procedure.

No generated validator axiom, prose assertion, or paper citation may be imported into production.

## Known recovered gap

`PolygonalProtoTiling.edgeConnected_iff_sharesNonvertex_of_isPacking` still contains the only
recovered `sorry`.  It is not used by the connected-sliding theorem, but the final project audit
will not accept it: the local edge-contact equivalence must be proved or removed from the public
surface before the final snapshot is sealed.

