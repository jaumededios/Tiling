import ChallengeDeps
import Tiling.RationalPolygonal.Main

/-!
# Solution bridge for the rational-polygon comparator

The theorem statement below is exactly the one in `Challenge.lean`, expressed solely through the
Mathlib-only vocabulary of `ChallengeDeps.lean`.  This file is allowed to import the project.

Most of the code is intentionally pedestrian conversion work.  Keeping it explicit demonstrates
that the production theorem proves the challenge as stated, rather than a nearby theorem hidden
behind project-specific definitions.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace DeDiosGreenfeldComparator

namespace ProductionBridge

/-! ## Polygonal geometry -/

/-- Turn a comparator triangulation into the production library's triangulation structure. -/
def toProductionTriangulation {Ω : Set Plane} (τ : Triangulation Ω) :
    Tiling.Triangulation Ω where
  pieces := τ.pieces
  isTriangle := by
    intro t ht
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      τ.isTriangle t ht
  pairwiseAEDisjoint := τ.pairwiseAEDisjoint
  sUnion_eq := τ.sUnion_eq

/-- Read a production triangulation using the comparator's independent structure. -/
def ofProductionTriangulation {Ω : Set Plane} (τ : Tiling.Triangulation Ω) :
    Triangulation Ω where
  pieces := τ.pieces
  isTriangle := by
    intro t ht
    simpa [IsTriangle, twiceSignedArea, Tiling.IsTriangle, Tiling.twiceSignedArea] using
      τ.isTriangle t ht
  pairwiseAEDisjoint := τ.pairwiseAEDisjoint
  sUnion_eq := τ.sUnion_eq

/-- The independently defined intrinsic vertices are exactly the production vertex set.

The proof simply converts a triangulation in either direction.  This is the key check that the
challenge did not smuggle in a preferred triangulation or a different notion of polygon vertex. -/
theorem intrinsicVertices_eq_vertexSet (Ω : Set Plane) :
    intrinsicVertices Ω = Tiling.vertexSet Ω := by
  ext x
  constructor
  · intro hx τ
    obtain ⟨t, ht, hxt⟩ := hx (ofProductionTriangulation τ)
    exact ⟨t, ht, hxt⟩
  · intro hx τ
    obtain ⟨t, ht, hxt⟩ := hx (toProductionTriangulation τ)
    exact ⟨t, ht, hxt⟩

/-! ## Integer points -/

/-- The elementary coordinate definition of an integer point implies membership in the
production integer lattice. -/
theorem production_isIntegerPoint_of_isIntegerPoint {z : Plane}
    (hz : IsIntegerPoint z) :
    Tiling.RationalPolygonal.IsIntegerPoint z := by
  obtain ⟨m, n, rfl⟩ := hz
  apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
  refine ⟨![m, n], ?_⟩
  simp [Tiling.RationalPolygonal.integerPoint]

/-! ## Monotile tilings -/

/-- Convert the comparator's direct monotile tiling relation to the unit-labelled production
relation. -/
theorem toProductionTiling (K : Tiling.RationalPolygonal.PolygonalRegion)
    {T : Set Plane} (hT : TranslationTiling volume K.support T) :
    K.Tiles T := by
  refine
    { countable := K.placements_countable hT.countable
      isPacking := ?_
      isCover := ?_ }
  · intro p hp q hq hpq
    apply hT.isPacking hp hq
    intro hpqfst
    apply hpq
    apply Prod.ext
    · exact hpqfst
    · exact Subsingleton.elim _ _
  · filter_upwards [hT.isCover] with x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨((t : Plane), ()), t.property⟩, ?_⟩
    exact hxt

/-- Convert a production monotile tiling back to the direct comparator relation. -/
theorem ofProductionTiling (K : Tiling.RationalPolygonal.PolygonalRegion)
    {T : Set Plane} (hT : K.Tiles T) :
    TranslationTiling volume K.support T := by
  refine
    { countable := hT.countable
      isPacking := ?_
      isCover := ?_ }
  · intro s hs t ht hst
    have hplacements :
        AEDisjoint volume
          (Tiling.placedTile K.prototileFamily (s, ()))
          (Tiling.placedTile K.prototileFamily (t, ())) := by
      apply hT.isPacking hs ht
      intro hpair
      exact hst (congrArg Prod.fst hpair)
    exact hplacements
  · filter_upwards [hT.isCover] with x hx
    obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨p.1.1, p.property⟩, ?_⟩
    exact hxp

/-! ## The theorem bridge -/

/-- The Mathlib-only rationality predicate supplies a production region with the same support.

This is existential rather than a data-valued definition because `RationalPolygon Ω` is a
proposition: the theorem must not pretend that its geometric witnesses are executable input. -/
theorem exists_productionRegion {Ω : Set Plane} (hΩ : RationalPolygon Ω) :
    ∃ K : Tiling.RationalPolygonal.RationalPolygonalRegion, K.support = Ω := by
  rcases hΩ with ⟨⟨τ⟩, hnonempty, anchor, hanchor, denominator, hdenominator, hvertices⟩
  refine ⟨
    { support := Ω
      isPolygonal := ⟨toProductionTriangulation τ⟩
      nonempty := hnonempty
      anchor := anchor
      anchor_mem_vertex := by
        rw [← intrinsicVertices_eq_vertexSet]
        exact hanchor
      denominator := denominator
      denominator_pos := hdenominator
      vertex_integral := by
        intro w hw
        apply production_isIntegerPoint_of_isIntegerPoint
        apply hvertices w
        rwa [intrinsicVertices_eq_vertexSet] }, rfl⟩

end ProductionBridge

open ProductionBridge

/-- Every translationally tileable rational polygon admits a doubly periodic tiling.

This repeats the exact challenge theorem name and type.  The proof constructs the production
region, applies paper Theorem 1.1, and converts the returned tiling back to the independent
Mathlib-only vocabulary. -/
theorem periodic_tiling_of_rational_polygon : PeriodicTilingTheorem := by
  intro Ω hΩ htileable
  obtain ⟨K, hK⟩ := exists_productionRegion hΩ
  obtain ⟨T, hT⟩ := htileable
  have hT' : TranslationTiling volume K.support T := by
    simpa only [hK] using hT
  have hproductionTileable :
      ∃ T : Set Plane, K.toPolygonalRegion.Tiles T :=
    ⟨T, toProductionTiling K.toPolygonalRegion hT'⟩
  obtain ⟨S, hStiles, hSperiodic⟩ :=
    (Tiling.RationalPolygonal.RationalPolygonalRegion.theorem_1_1 K).mp
      hproductionTileable
  refine ⟨S, hSperiodic, ?_⟩
  simpa only [hK] using ofProductionTiling K.toPolygonalRegion hStiles

end DeDiosGreenfeldComparator
