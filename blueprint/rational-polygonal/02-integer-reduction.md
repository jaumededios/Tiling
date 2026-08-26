# 2. From an integer polygonal tiling to integer translations

This chapter specializes the already proved finite-family sliding development to the paper's one
tile setting.

## Vertex sharing

For the unit-labelled polygonal prototiling associated to `K` and `T`, paper adjacency is exactly
`PolygonalProtoTiling.VertexConnected`.  Its transitive closure is
`PolygonalProtoTiling.SamePlate`, equivalently equality in the connected-component quotient of
`vertexGraph`.

## Lemma 2.4

If the vertices of `K` lie in the integer lattice and two translates share a placed vertex, their
translation-vector difference is integral.  A reachable path therefore has integral total
difference.  If `0 ∈ T` and the vertex graph is connected, every element of `T` is integral.

The proof must use the actual vertex equality witness at each graph edge.  It may not assume that
all translation coordinates are uniformly discrete.

## Lemmas 2.5 and 2.7

The following stronger results are already proved:

```lean
PolygonalProtoTiling.exists_isSlidingDirection
PolygonalProtoTiling.IsSlidingDirection.exists_connected_component_shift
PolygonalProtoTiling.exists_connected_shift
PolygonalProtoTiling.exists_connected_tiling
```

The new monotile wrappers retain the constructed direction and shift, then project the shifted
unit-labelled placement set back to a set of translation vectors.

## Lemma 2.2

Starting from any tiling by an integer polygonal region:

1. use `exists_connected_shift` to obtain a connected replacement tiling;
2. translate the replacement so that one placement is at the origin;
3. apply Lemma 2.4 to put every translation in `ℤ²`; and
4. transport the set through the integer-plane additive equivalence.

The output includes both the continuous integer translation set and the corresponding discrete
set, because rasterization and the earthquake argument consume different views.

