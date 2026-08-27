# Independent final mathematical/paper-comparator follow-up review

## Verdict

**ACCEPT.** The frozen snapshot proves the mathematical content attributed to
de Dios Pont--Grebík--Greenfeld--Madrid, including the previously missing effective boundary of
Corollary 1.1. I found no P0, P1, P2, or P3 issue. Under the review rule that every finding at any
of those priorities blocks release, this snapshot is accepted.

Finding totals: **P0: 0, P1: 0, P2: 0, P3: 0.**

## Exact snapshot binding and immutable gate

- Repository: `/workspace/tiling-rational-polygonal`
- Branch: `formalize/rational-polygonal-tilings`
- Frozen commit: `9062a580fa82620422472105002395a115e1d354`
- Initial Git state: clean and equal to
  `origin/formalize/rational-polygonal-tilings`
- Manifest: `blueprint/rational-polygonal/SNAPSHOT.sha256`
- Manifest rows: **78**
- Manifest SHA-256:
  `3074903f416d96d5af213aba2c47810835b5b86db1802cb604f9a9f6b4ea1ada`
- Initial `sha256sum -c`: **78/78 payloads OK**
- Independent `freeze.py --check`: **PASS: 78 payloads and the exact required manifest hash**

All sealed production, blueprint, generator, validator, and toolchain payloads were reviewed
read-only. This review wrote only this report. In particular, it did not edit production, blueprint
prose, generated validation artifacts, the manifest, or either historical report.

The historical mathematical BLOCK report remains byte-for-byte unchanged at SHA-256
`0cd1f13a8d40bda2de8934b1cfb7b4addc83fa1f88e8b57446fe363cbae54f9b`. It is a correct review of
commit `5dff73dbf3bf16ee759a6c43ea669918f5259fea`; it is not silently superseded or rewritten.

## Paper and review scope

I read the official source of
[arXiv:2408.02151v2](https://arxiv.org/abs/2408.02151v2) end to end: all 747 lines of
`Rational_Vertex_PTC.tex`, SHA-256
`c0d41850d73caf356e992e36338c64a5c1ed55a53379fbe4c6af53c806ff9ac5` (official v2 source archive
SHA-256 `1183ab0d6be3082731ff1196735c506c930a6ecef45e955a51d9471d73090aff`). I compared the definitions,
every numbered result, all proof dependencies used by Theorems 1.1 and 1.2, and the algorithmic
content of Corollary 1.1 against the sealed production sources. I also inspected the full
rational-polygonal blueprint and comparator, the manifest-listed generated artifacts and their
generators, the public ownership ledger, the imported Greenfeld--Tao endpoints, and the complete
sealed source/import/trust surface.

The paper uses a bounded open polygonal set, while Lean uses its nonempty regular-closed finite
triangle union. `PolygonalRegion.openCarrier` is the interior, and `openCarrier_ae_eq` proves that
the two representatives agree for the a.e. tiling relation. This is a sound representation bridge,
not a strengthening hidden in notation. Arbitrary finite a.e.-disjoint triangle unions permit
disconnected sets and sets with holes; neither `PolygonalRegion` nor `Raw.Code.Valid` assumes
connectedness or simple connectedness.

## Closure of the historical Corollary 1.1 block

The old G1 finding is genuinely closed in production rather than relabelled. The effective chain
now begins with rational coordinates and ends in one total Boolean:

| Obligation | Production implementation and checked mathematical content |
| --- | --- |
| Runtime input, with no raster or answer certificate | `Raw.QPoint` is a pair of rationals, `Raw.QTriangle` has three such points, and `Raw.Code` is a finite list of triangles. `Raw.Code.Valid : Prop` supplies only nonemptiness, nondegeneracy, pairwise a.e. disjointness, and an intrinsic anchor. `Raw.Code.Input` contains the runtime code and that proof-only validity field. There is no raster, tiling witness, Boolean answer, or `RasterPresentation.Represents` certificate. |
| Semantic decoding | `Code.support` is the exact finite union of the closed triangle carriers. The validity proof constructs a genuine `Triangulation`, `polygonalRegion`, and `rationalPolygonalRegion`; the anchor and common denominator satisfy the existing relative-rational semantic API. |
| Executable normalization | `Code.commonDenominator` takes the LCM of all rational coordinate denominators. `normalizedPoint`, `normalizedTriangle`, and `normalizedTriangles` are executable integer data. The cast and carrier lemmas culminate in `normalizedSupport_eq_normalizedCodeSupport`, so this code is exactly the semantic affine normalization, not a nearby raster approximation. |
| Exact strict feasibility | `LinearFeasibility.solve` is a terminating rational Fourier--Motzkin solver for finite strict affine systems. `solve_sound`, `solve_complete`, `solve_isSome_iff`, and the Boolean correctness theorem establish exact rational feasibility, including genuinely strict boundaries. |
| Complete positive-measure signatures | `SignatureCompiler` forms a finite padded offset window, all translated triangle-edge lines, and every feasible strict sign cell in the open unit square. Exact rational orientation tests compute the sample signature and deduplicate the result. `SignatureCorrectness` proves soundness by openness/positive measure and completeness by removing the finite null line arrangement and unit-square boundary, using rational density to obtain a solver sample in the same cell. The endpoint `signatureFamily_toFinset_eq_relevantSignatures` is equality with the entire semantic positive-measure family, independent of list order. |
| Executable marker | `ComputableMarker` implements the integer boxes, rings, zero block, scale, array marker, and finite planar tile. Its extensional theorems identify these ordinary executable definitions with the marker used in `RasterMarker` and `RasterRigidity`. A computed nonempty signature is moved to color zero; marker rigidity decodes an arbitrary exact raster tiling back to one common translation set for every signature. |
| Total Boolean | `Raw.Decision.rawTileDecision : Raw.Code.Input → Bool` has an executable `false` fallback and otherwise invokes the bounded exhaustive `TranslationalTilings.planarTileDecision` on the computed marker tile. Semantic family nonemptiness proves that valid input never uses the fallback. The runtime body has no semantic choice, raster certificate, or oracle. |
| Real-plane iff | `rawTileDecision_eq_true_iff` connects the bounded lattice Boolean, executable marker, unordered computed family, semantic relevant signatures, integer reduction, and inverse normalization. `rawTileDecision_decidesRawTileability` discharges signature correctness internally. `RationalPolygonalRegion.corollary_1_1` therefore quantifies over a single algorithm on every valid raw rational triangulation, while `corollary_1_1_spec` exposes the pointwise real-plane iff. |

The proof-only geometric validity predicate is the domain certificate for a finite triangulation;
it is not an answer certificate and is erased from execution. This is exactly the admissible raw
input boundary called for by the old review. The theorem does not pretend that malformed lists are
paper inputs, and it does not use the older post-raster `RasterPresentation` as Corollary 1.1's
input.

The executable tests independently exercised the relevant corner cases:

```text
fractional denominator LCM                                  6
clear 2/3 at denominator 6                                 4
inconsistent strict system x < 0 and x > 0                none
strict box 0 < x,y < 1/1000                               some (1/2000, 1/2000)
two separated integral triangles: family/cardinalities    (2, [2, 0])
eight-triangle square ring: material point / hole point    true / false
```

Thus disconnected input is accepted by the complete signature-family computation, and the same
raw triangle-union membership code correctly represents a genuine open hole. I also launched a
complete signature-family enumeration for a six-triangle annulus; it remained computationally
expensive after a bounded four-minute smoke window and was stopped without a diagnostic. This is
not contrary to the paper's decidability claim: the production compiler and final search are
finite but make no practical complexity promise, and the universal cell-completeness and
signature-correctness theorems above cover the annulus without relying on that test. As documented
by the validator, the enormous final bounded tiling search is intentionally not a smoke test.

## Independent numbered-result comparator

| Paper item | Independent disposition |
| --- | --- |
| Definition 1.2(i)--(iii) | `SinglyPeriodic`, `WeakPeriodicDecomposition`/`WeaklyPeriodic`, and `DoublyPeriodic` use genuine nonzero real periods; the double-period definition requires linear independence. |
| Theorem 1.1 | `RationalPolygonalRegion.theorem_1_1` has the exact iff between tileability and existence of a doubly periodic tiling. Its forward proof normalizes, obtains an integer signature tiling, applies raster rigidity and `TranslationalTilings.theorem_1_5`, decodes a scalar-periodic lattice tiling, embeds two independent coordinate periods, and inverse-normalizes. The reverse implication retains the exhibited tiling. |
| Corollary 1.1 | Proved on `Raw.Code.Input` by the total Boolean and real-plane iff audited above. The result no longer starts at an already compiled raster. |
| Theorem 1.2 | `RationalPolygonalRegion.theorem_1_2` takes the supplied `hT : K.Tiles T` and concludes `WeaklyPeriodic T` for that same `T`, not for a replacement tiling. |
| Definition 2.1 | `PolygonalRegion.IsIntegerTiling` records a tiling whose placed intrinsic vertices are integral. |
| Lemma 2.2 | `PolygonalRegion.exists_integer_tiling` first obtains a connected component shift, bases it at one placement, and uses vertex-graph paths to prove every translation integral. |
| Definition 2.3 | `PolygonalProtoTiling.VertexConnected`, `vertexGraph`, `SamePlate`, and `Plate` implement vertex-connected components and their carriers. |
| Lemma 2.4 | `samePlate_translation_sub_mem_integerLattice` sums integral translation differences along a vertex-contact walk. |
| Lemma 2.5 | The locally straight frontier analysis and a.e.-disjoint regular-closed plate carriers yield one nonzero common `IsSlidingDirection`; invariance is for every real multiple on every plate. |
| Remark 2.6 | Correctly retained as explanatory compatibility rather than invented as a theorem. |
| Lemma 2.7 | `exists_connected_component_shift` realizes a connected potential graph and proves arbitrary plate shifts preserve tiling; the monotile specialization supplies the connected tiling used in Lemma 2.2. |
| Section 3 discrete tiling | Uses the exact `TranslationalTilings.TilesUniverse` unique-representation semantics on `ℤ²`. |
| Lemma 3.1(i) | `exists_integer_tiling_iff_relevantPlanarRasterTile` is an iff for arbitrary raster translations; the hard direction first proves all raster translations lie in one coarse-marker-lattice coset and then decodes the common signature tiling. |
| Lemma 3.1(ii) | `tiles_integerPoint_image_iff_relevantPlanarRasterTile` and the family decoder give the exact continuous/integer/raster tileability bridge. |
| Lemma 3.1(iii) | `relevantPlanarRasterTile_carrier_eq_iff` proves literal equality on both sides. The forward path passes through a.e. signature equality and then upgrades by local finiteness and regular closedness of integer-translation carriers. |
| Theorem 4.1 used in the paper | The imported `TranslationalTilings.exists_quantitativeWeakPeriodData` chooses directions, lattice, and multiplier uniformly from the finite tile and target period, and its `ValidFor` theorem applies to every auxiliary earthquake tiling. Its trust closure was independently rechecked. |
| Definition 4.1 | `quakeTransfer`, `quakeGraph`, `QuakePlate`, carrier periodicity/minimality, and independent `quakeShiftedTranslations` implement the earthquake relation and preserve exact tiling. |
| Lemma 4.2 | `exists_uniformQuakePeriodicDecomposition` applies one uniform quantitative datum, uses the quotient-coset pigeonhole and factorial quake period, partitions complete and incomplete orbits, treats parallel/no-parallel branches, handles the singleton tile directly, and transports an arbitrary nonempty tile to the zero-containing case. |

No comparator row overstates an existence result as a result about the original tiling, confuses
a.e. with literal carrier equality, assumes a one-plate tiling, or imports a generated theorem.

## Theorem 1.2 compatibility chain

I separately followed the subtle part of Theorem 1.2 through its proof bodies. For an arbitrary
given tiling, `ContinuousEarthquake` obtains a nonzero integer sliding direction and constructs a
connected component shift while retaining the old continuous-plate translation partition.
`IntegerSlidingReduction` bases that shifted tiling in `ℤ²` and records, for every old plate
and every raster signature, the same discrete sliding period. Consequently
`quakePlateTranslations_subset_owner` proves each canonical discrete quake plate refines one old
continuous plate. Lemma 4.2 supplies uniform labelled periodic parts. `unshiftedQuakePart` reverses
the owner-dependent component shift; equal labels retain one common period across all owners.
Pairwise disjointness follows first from distinct old owners and then from the per-quake
decomposition, while `iUnion_assembledQuakePart` proves the union is exactly the original `T`.
Finally inverse rational normalization transports that finite decomposition and its nonzero
periods. This closes the compatibility point on which a merely existential weak-periodic
replacement would have been insufficient.

## Build, generation, regression, and trust evidence

- Full `lake build`: **PASS, 3531 jobs**. The only message was the known optional short copyright
  header linter warning for `Main.lean`; strict direct compilation is clean.
- Full `python3 blueprint/rational-polygonal/validate.py --check`: **PASS: 26 modules, 874
  declarations, 518 theorem trust closures, documentation clean, executable frontend regression
  passed**.
- The generated ledger contains exactly 874 proved rows: 5 abbreviations, 238 definitions, 23
  structures, 90 explicit fields, and 518 theorems. Live signatures, definition bodies, compiled
  ownership/source ranges, parser regression, strict module compiles, documentation, validator
  compile, and all four generated hashes were current.
- An independent targeted file compiled 15 mathematical endpoints with `#print axioms`: the three
  paper endpoints, raw decision iff/contract, exact signature equality, strict feasibility,
  executable marker equality, raster equivalences, uniform earthquake decomposition, uniform
  Greenfeld--Tao data, periodic completion, and bounded planar decision. Every closure used only
  `propext`, `Classical.choice`, and `Quot.sound`.
- A scan of every manifest-listed Lean source found no `sorry`, `admit`, project `axiom`, `unsafe`,
  `native_decide`, validator import, `maxHeartbeats`, or `maxRecDepth`. The two lexical matches were
  only the English word "admit" in documentation. Production imports no blueprint or validation
  artifact.
- `Tiling.lean` imports `Tiling.RationalPolygonal.Main`, and the imported
  `TranslationalTilings.lean` umbrella exports its genuine production `Main`; the terminal results
  are reachable without a validation import.

## Global library-review rubric and do-not-refactor decisions

1. **Mathematical intent:** clear and paper-faithful, including the raw algorithmic boundary.
2. **Reusable seams:** raw normalization, exact strict feasibility, semantic compiler correctness,
   executable markers, raster rigidity, earthquakes, and continuous/discrete compatibility have
   coherent responsibilities and real consumers.
3. **Public API/theorem shape:** the terminal theorems are thin, exact, and quantify over the
   intended objects. The older compiled-raster backend remains accurately named support API.
4. **Dependency design:** geometry and discrete-carrier foundations sit below raster and
   earthquake consumers; compiler computation is below semantic correctness; `Main` is the final
   join. No proof depends on generated validation.
5. **Mathlib/project integration:** the development reuses the proved Greenfeld--Tao periodicity,
   completion, and bounded-decision APIs rather than duplicating them.
6. **Proof architecture:** the hard local geometry, null-set cell argument, marker rigidity,
   uniform earthquake construction, and unshifting argument are exposed through named lemmas and
   checked endpoints.
7. **Cost/durability:** strict builds and trust checks are green without heartbeat or recursion
   waivers. The executable decision is a finitary decidability result; no unsupported efficiency
   claim is made.
8. **Refactor risk:** no snapshot migration has a demonstrated mathematical or dependency benefit.

Keep the regular-closed support with its explicit a.e. open-carrier bridge. Keep geometric
validity proof-only rather than folding it into the tileability Boolean. Keep the compiled-raster
backend as a separate reusable API. Keep the executable compiler separate from classical semantic
correctness. Keep the stronger finite-family sliding lemmas and the explicit continuous/discrete
period APIs. No proof-polish or upstream-refactor handoff is warranted by this review.

## Final seal recheck

After creating this report, the immutable gate was rerun:

- `python3 blueprint/rational-polygonal/freeze.py --check`: **PASS: 78 payloads**, exact manifest
  SHA-256 `3074903f416d96d5af213aba2c47810835b5b86db1802cb604f9a9f6b4ea1ada`.
- `sha256sum -c blueprint/rational-polygonal/SNAPSHOT.sha256`: **78/78 payloads OK**.
- Commit binding remained `9062a580fa82620422472105002395a115e1d354`; no manifest-listed path
  changed.

**Final disposition: ACCEPTED for the frozen mathematical/paper-comparator snapshot at
`9062a58`.**
