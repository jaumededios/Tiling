# Module layout and dependency direction

The implemented dependency chain is:

```text
Tiling.Geometry.Plane
  ├─ LocalLine
  ├─ PolygonalTopology
  └─ Plate → PackingTopology → Sliding → Connected

Tiling.RationalPolygonal.Basic
  ├─ IntegerReduction
  ├─ RawInput
  └─ DiscreteCarrier
       ├─ Raster + IntegerReduction
       │    └─ RasterMarker
       │         ├─ RasterRigidity
       │         └─ ComputableMarker
       └─ Earthquake + TranslationalTilings quantitative weak-period API
            └─ EarthquakeUniform

Raster + EarthquakeUniform
  └─ ContinuousEarthquake
       └─ SlidingReduction
            └─ WeakPeriodicity

RasterRigidity + TranslationalTilings.Algorithms
  └─ Decision

LinearFeasibility + RawInput + ComputableMarker
  └─ SignatureCompiler
       └─ SignatureCorrectness + Raster

Decision + SignatureCorrectness
  └─ RawDecision

RasterRigidity + WeakPeriodicity + RawDecision + TranslationalTilings.Main
  └─ Main
```

## Production ownership

| Module | Responsibility |
| --- | --- |
| `Tiling.Geometry.Plane` | Polygonal and rational geometric primitives. |
| `LocalLine`, `PolygonalTopology`, `Plate`, `PackingTopology` | Local boundary geometry, intrinsic vertices, vertex-sharing graph, and contact topology. |
| `Sliding`, `Connected` | Common sliding direction and component shifts merging the vertex graph. |
| `RationalPolygonal.Basic` | Region/tiling model, rational presentation, normalization, real periodicity, inverse transport. |
| `RawInput` | Finite rational-triangle runtime data, proof-only validity, executable common-denominator normalization, and semantic interpretation. |
| `IntegerReduction` | Monotile wrappers, Lemmas 2.2 and 2.4, integer connected tilings. |
| `DiscreteCarrier` | Exact finite-tile carriers, unique representations, tile shifts, and elementary transfer/period APIs shared by rasterization and earthquakes. |
| `Raster` | Lattice signatures, relevant positive-measure fibers, continuous/discrete tiling equivalence. |
| `RasterMarker` | Marker construction, simultaneous-family encoding, exact carrier decoding. |
| `ComputableMarker` | Executable finite marker constructors and exact extensional bridges to the semantic marker API. |
| `RasterRigidity` | Marker-frame rigidity, removal of the coarse-lattice restriction, and arbitrary-tiling decoding. |
| `Earthquake` | Canonical graph/components, carrier periodicity/minimality, independent shifts. |
| `EarthquakeUniform` | Uniform finite periodic decomposition of every quake plate (Lemma 4.2). |
| `ContinuousEarthquake` | Continuous plate partition and shifts retaining the original tiling. |
| `SlidingReduction` | Integer realization retaining each old continuous plate and its common carrier period. |
| `WeakPeriodicity` | Refinement by quake plates, inverse shifts, regrouping, and Theorem 1.2. |
| `LinearFeasibility` | Verified executable rational Fourier--Motzkin feasibility in one and two variables. |
| `SignatureCompiler` | Executable normalized offset window, line arrangement, feasible sign cells, samples, signatures, and marker input. |
| `SignatureCorrectness` | Exact equality of executable and semantic relevant-signature families. |
| `Decision` | Reusable compiled-raster search, exact cost, and semantic correctness certificate. |
| `RawDecision` | Total Boolean and universal correctness contract on valid finite rational triangulations. |
| `Main` | Thin endpoints for Theorem 1.1, Corollary 1.1, and Theorem 1.2. |

Lower geometric/raster modules do not import the Greenfeld--Tao weak-periodicity development.
`DiscreteCarrier` is the shared lower interface; the earthquake module adds exactly the
quantitative weak-period declarations it needs.  The raw compiler depends on the marker geometry
and semantic raster API without importing periodic completion.  `RawDecision` is the sole join
between compiler correctness and the bounded decision backend.  `Main` is the terminal
paper-facing join and is exported by the root `Tiling` umbrella.

## API and validation policy

- `validate.py --update` derives one canonical row for every public declaration and explicit
  public structure field in the 26 owned modules.  A same-line attribute/modifier regression and
  an independent compiled-module ownership/source-range cross-check prevent silent omissions.
- `validate.py --check` regenerates and compares the ledger, exact elaborated signature dump,
  public-definition body dump, and generated hashes; rebuilds and strict-compiles every production
  source and the `#check` validator with warnings and unused decidable instances treated as errors;
  runs `docBlame`; and runs `#print axioms` on every public theorem/lemma.
- `BlueprintValidation.lean` imports genuine production only and contains no declaration stubs.
- Production never imports generated validation artifacts.
- Helpers remain private unless another production module consumes them.
- Every public declaration has a mathematical docstring; module-level comments explain the proof
  boundary and dependency role.
