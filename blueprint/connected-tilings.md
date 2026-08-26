# Blueprint: connected polygonal tilings

## Scope

We fix a finite labelled family of nondegenerate polygonal subsets of the real plane and a
countable translational tiling by that family.  Placements are joined when the translated supports
share a point which is a triangulation-independent vertex of both supports.  The goal is to replace
the placement set, without changing the prototile family, by a tiling whose vertex-contact graph is
connected.

This is a finite-family extension of the sliding argument in Lemmas 2.5 and 2.7 of J. de Dios Pont,
J. Grebík, R. Greenfeld, and J. Madrid, *Periodicity and decidability of translational tilings by
rational polygonal sets* (arXiv:2408.02151).  The paper states the result for one bounded open
polygonal tile.  Here supports are finite unions of closed nondegenerate triangles and packing and
covering hold almost everywhere.  The proof must therefore include the open/closed and a.e./exact
bridges; it must not silently import them from the paper.

Rationality is not used in this development.

## Canonical representatives

For a plate `C`, use the union of the closed placed supports in `C`:

```lean
def plateCarrier (C : A.Plate) : Set Plane :=
  ⋃ i : C, placedTile A.prototiles (i : A.placements).1
```

The open representative used for local topology is `interior (A.plateCarrier C)`.  We do **not**
use the union of the interiors of the individual tiles.  That union omits every seam in the square
grid, even when the grid has only one plate, so it is not literally invariant under the expected
translations.

Directional invariance is expressed through Mathlib's additive-action stabilizer rather than a
project-specific wrapper:

```lean
structure IsSlidingDirection (v : Plane) : Prop where
  ne_zero : v ≠ 0
  invariant : ∀ (C : A.Plate) (r : ℝ),
    r • v ∈ AddAction.stabilizer Plane (A.plateCarrier C)
```

`AddAction.mem_stabilizer_iff` exposes this as the equality
`r • v +ᵥ A.plateCarrier C = A.plateCarrier C`.

This certificate is the reusable conclusion of the hard geometric argument.  It retains the
component carriers needed by the merging proof.  The user-facing assertion that every map from
plates to real shifts preserves the tiling is a corollary, not the primary geometric theorem.

## Theorem dependency graph

```text
finite triangulations
  ├── compact / bounded / regular closed / null frontier
  ├── nonempty interior / positive volume
  └── finite intrinsic vertex set + local straightness away from it
                 │
local straight-line topology
  └── affine-line coordinates + local half-plane classification
                 │
packing + finite family
  ├── uniformly separated physical anchors across the finite label family
  └── locally finite family of placed supports
                 │
AE cover + closed locally finite union
  └── exact closed cover of the plane
                 │
plate contact graph + proper-boundary-vertex argument
  └── exists a common IsSlidingDirection
          │                         │
          ├── generic shift bookkeeping ──└── carrier-contact graph → alignment graph
          │                                      └── connected parent tree
          └── every component shift tiles                 └── integrate edge offsets
                                                        └── connected shifted tiling
```

## Layer 1: polygonal regularity

The following facts should be exposed from `IsPolygonal`, with implementations assembled from the
finite triangulation and existing Mathlib results about convex hulls:

1. The support is compact, hence closed and bounded.
2. It is regular closed: `closure (interior s) = s`.
3. Its frontier has zero planar volume, so `interior s =ᵐ[volume] s`.
4. If `s.Nonempty`, it has nonempty interior and positive volume.  `IsPolygonal ∅` holds via the
   empty triangulation, so this hypothesis must be explicit.  It is supplied by
   `Prototile.nonempty_support` at every tiling use.
5. `vertexSet s` is finite and commutes with translations.
6. At a frontier point outside `vertexSet s`, the frontier is locally an affine line.

The last item is the interface between the triangulation-based definition of `vertexSet` and the
paper's intrinsic proper boundary vertices.  It is a genuine computational-geometry theorem, not
routine finite-union bookkeeping.  A full equality of the two notions, including
`vertexSet s ⊆ frontier s`, is desirable, but the one-way local-straightness implication is enough
for sliding.

## Layer 2: packing topology

For every label choose the center of an interior ball in its support.  Translate that center along
with a placement; these are **physical anchors**.  Packing separates these anchors across all
labels, and finiteness of the label type supplies a uniform positive inradius.  Boundedness of the
finitely many supports then gives:

```lean
LocallyFinite fun i : A.placements ↦ placedTile A.prototiles i.1
```

Do not assert uniform discreteness of the raw translation coordinates across labels.  It is false
when two labels use differently anchored copies of the same shape: a valid tiling can have
cross-label translation vectors approach each other while all physical supports remain locally
finite.

Consequences to prove once:

- every plate carrier is a locally finite union of closed, regular-closed supports;
- the total union of placed supports is closed;
- an a.e. cover by that closed union is an exact cover, since a nonempty open complement has
  positive volume;
- a.e. packing gives disjoint interiors of distinct placed supports;
- carriers of distinct plates are a.e. disjoint, by countable unions of the original packing
  relations.
- for a placement subfamily and its complement, both regular-closed carriers have the same
  frontier.  This is the closed/open form of the boundary identity used in the paper's
  proper-vertex argument.

Local finiteness is derived from the existing hypotheses, not added as data to a tiling.

## Layer 3: the sliding direction

The geometric proof has two reusable seams.

First, if a proper vertex occurs on the boundary of the carrier of a set of placements, local
finiteness and the exact cover produce incident tiles on both sides of that placement subset.  The
local polygonal alternatives imply that either the boundary is straight there or some tile from
each side has that point as a vertex.  Applied to a plate, the latter alternative would create a
vertex-graph edge crossing the component, a contradiction.  Hence a plate carrier has no proper
boundary vertices.

Second, a nonempty regular-closed planar set whose nonempty boundary is locally a line everywhere
has a boundary consisting of parallel lines and is invariant along their common direction.  The
empty-boundary case is separate: such a carrier is all of the connected plane, hence is the sole
plate and every nonzero direction works.  Distinct plate interiors cannot have nonparallel
invariant directions, so all plates admit one common line direction.

The hard theorem is therefore:

```lean
theorem exists_isSlidingDirection [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ v : Plane, A.IsSlidingDirection v
```

The documentation must call this a finite-family extension of the paper, not an exact restatement
of its monotile lemma.

## Layer 4: shifting bookkeeping

For `shift : A.Plate → ℝ`, send a placement `i` to the same label translated by
`shift (componentMk i) • v`, and take the range as the new placement set.

The preservation theorem should be fully measure-theoretic and independent of planar boundary
geometry:

```lean
theorem IsSlidingDirection.isTiling_shiftComponents
    (hv : A.IsSlidingDirection v)
    (hA : IsTiling A.prototiles A.placements)
    (shift : A.Plate → ℝ) :
    IsTiling (A.shiftComponents v shift).prototiles
      (A.shiftComponents v shift).placements
```

Proof obligations:

1. A range of a countable placement subtype is countable.
2. Within one plate both tiles receive the same translation, so translation invariance of volume
   preserves their a.e. disjointness.
3. Across plates, shifted tiles remain subsets of their unchanged carriers; distinct carriers are
   a.e. disjoint.
4. The union of all shifted supports equals the original union because every carrier is unchanged;
   hence the original a.e. cover transfers.

Expose the canonical surjective map from old to shifted placement vertices and the elementary
support/label formulas.  The map is injective on each old plate because that plate receives one
common translation.  No global injectivity claim is needed: if images from two old plates happen
to coincide, the range representation identifies them and thereby already connects those two
fibers.  The merging proof handles that equality case explicitly.  The map is therefore used as a
`SimpleGraph.Hom`, not a `SimpleGraph.Embedding`: the chosen shift is supposed to add edges between
old plates, whereas a graph embedding would incorrectly reflect those new edges.

The consumer-facing API should include membership and coercion lemmas rather than requiring later
proofs to unfold ranges and nested subtypes:

```lean
theorem mem_plateCarrier_iff ...
theorem placedTile_subset_plateCarrier ...
theorem mem_shiftComponents_placements_iff ...
@[simp] theorem shiftedVertex_val ...
theorem shiftedVertex_surjective ...
theorem shiftedVertex_injective_of_component_eq ...
theorem placedTile_shiftedVertex ...
theorem placedVertexSet_shiftedVertex ...
```

The requested intermediate statement then follows immediately:

```lean
theorem exists_sliding_direction [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ v : Plane, v ≠ 0 ∧ ∀ shift : A.Plate → ℝ,
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements
```

## Layer 5: merging plates

First define the carrier-contact graph on plates: distinct `C` and `D` are adjacent when
`A.plateCarrier C ∩ A.plateCarrier D` is nonempty.  The plate carriers form a locally finite
family of nonempty closed sets covering the connected plane.  Their contact graph is connected by
a generic clopen-separation argument: the union over one graph connected component and the union
over all remaining components would be disjoint, closed, complementary nonempty subsets of the
plane.  This route deliberately avoids projection; projection does not preserve local finiteness.

Next define the alignment graph on plates: `C` and `D` are adjacent when some relative real
displacement along `v` makes a vertex from a placement in `C` coincide with a vertex from a
placement in `D`.  The geometric realization lemma says that every carrier-contact edge is an
alignment edge when `v` is a sliding direction.  Thus the alignment graph is connected.

Choose a root of the alignment graph.  For every nonroot vertex, choose a shortest walk from the
root and use its penultimate vertex as a parent; the parent has strictly smaller graph distance.
Well-founded recursion on distance integrates one witnessed relative displacement per parent edge
to a potential `shift : A.Plate → ℝ`.  Package this as a generic theorem for a symmetric
additive-commutative-group-valued edge-offset relation.  This avoids orientation machinery for
unordered edges and works without a countability assumption.

The shifted vertex map preserves every old vertex edge because a shift is constant on each old
plate.  The spanning-tree edges add contacts between the shifted images of adjacent plates.
Connected old fibers plus those tree edges make the entire shifted vertex graph connected.

The replacement for the provisional merging statement is explicit about its structural premise:

```lean
theorem IsSlidingDirection.exists_connected_component_shift [Finite P]
    (hv : A.IsSlidingDirection v)
    (hA : IsTiling A.prototiles A.placements) :
    ∃ shift : A.Plate → ℝ,
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements ∧
      (A.shiftComponents v shift).vertexGraph.Connected
```

The strong result should retain the actual construction:

```lean
theorem exists_connected_shift [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ (v : Plane) (hv : A.IsSlidingDirection v) (shift : A.Plate → ℝ),
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements ∧
      (A.shiftComponents v shift).vertexGraph.Connected
```

The family-level API quantifies only a replacement placement set for the fixed prototile family:

```lean
def withPlacements (S : ProtoTiling Plane P) : PolygonalProtoTiling P :=
  { A with placements := S }

theorem exists_connected_tiling [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ S : ProtoTiling Plane P,
      IsTiling A.prototiles S ∧ (A.withPlacements S).vertexGraph.Connected
```

`withPlacements` is also used to define `shiftComponents`, so it is a constructor with two real
consumers rather than an equality-transport convenience.

## Module boundaries

- `Plane.lean` retains the elementary shapes and decompositions.
- `LocalLine.lean` contains affine-line coordinates, signed half-planes, and the reusable local
  classification of regular-closed sets with straight boundary.
- `PolygonalTopology.lean` contains finite-union regularity, translation covariance, intrinsic
  vertex finiteness, and the local-straightness bridge.
- `PackingTopology.lean` contains physical-anchor separation, local finiteness, regular-closed
  carriers, the exact-cover bridge, complementary-carrier frontiers, and plate-boundary geometry.
- `Topology/IntersectionGraph.lean` contains the generic locally-finite union and connected
  intersection-graph lemmas.
- `Plate.lean` contains contact relations, graph APIs, plates, and `plateCarrier`.
- `Sliding.lean` contains the sliding certificate, shifted-placement API, generic preservation, and
  existence of a sliding direction.
- `Connected.lean` contains the private carrier-contact/alignment scaffolding, offset-potential
  construction, merging theorem, and final wrappers.

The generic offset-potential proof stays local to `Connected.lean` until it has a second consumer;
it is stated at its natural additive-commutative-group generality but is not prematurely made a
separate public module.

## Honest proof boundaries

The four geometric seams specific to the connected-tiling argument are all proved:

1. the triangulation-independent-vertex/local-straight-boundary bridge;
2. the local proper-vertex/common-tile-vertex lemma;
3. classification of a regular-closed planar region with locally straight boundary as
   line-invariant, including the common-direction argument across regions;
4. realization of carrier contact by an alignable pair of tile vertices along the sliding
   direction, including the supporting-line fact that each of two incident invariant carriers
   supplies a placed support with an intrinsic vertex on the common line.

Countability, a.e.-disjoint unions, translation transport, graph adjacency simplification, shifted
vertex maps, graph-distance potentials, and final wrappers are bookkeeping and should not be hidden
inside those seams.

`PolygonalProtoTiling.edgeConnected_iff_sharesNonvertex_of_isPacking` is a pre-existing, separate
geometric gap.
It is not used by the connected-tiling proof, but it must still be listed in any project-wide trust
audit.

The proved declaration-level seam inventory is:

| Declaration | Proved seam |
| --- | --- |
| `IsPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet` | (1) |
| `exists_vertices_across_of_local_tile_geometry` | (2) |
| `exists_common_stabilizer_direction` | (3) |
| `alignsAlong_of_carrierContact` | (4) |

The complete remaining trust inventory is therefore the single legacy declaration:

| Declaration | Status |
| --- | --- |
| `PolygonalProtoTiling.edgeConnected_iff_sharesNonvertex_of_isPacking` | `sorry`; pre-existing and unused here |

In particular, `exists_isSlidingDirection`, `alignmentGraph_connected`, arbitrary-shift tiling
preservation, the offset-potential construction, and the final connected-tiling wrappers are all
proved without any connected-tiling-specific trust boundary.

## Acceptance criteria

- The theorem statements survive an independent counterexample/quantifier audit.
- The project builds from a clean state; the sole remaining `sorry` is the enumerated legacy edge-
  contact lemma, which is not used by the connected-tiling development.
- Each touched Lean file receives independent correctness, reuse/API, and proof-quality review.
- Findings are repaired and the revised snapshot is re-reviewed until no reviewer identifies a
  correctness or architecture blocker.
- No theorem is described as proved while it depends on an unproved declaration.
