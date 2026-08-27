import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Tiling.RationalPolygonal.Main

/-!
# Solution for the rational-polygon comparator

The complete definition block below is repeated from the trusted `Challenge.lean`. Repetition is
intentional: the challenge remains one Mathlib-only file which a mathematician can read from top
to bottom, while `leanprover/comparator` independently verifies that these declarations elaborate
to exactly the same constants in the solution environment.

After that repeated block, the `ProductionBridge` namespace performs explicit conversion to the
project's geometry and invokes the formalized de Dios Pont--Grebík--Greenfeld--Madrid theorem.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace DeDiosGreenfeldComparator

universe u v

/-! ## 1. Prototiles, packing, covering, and tiling -/

/-- A translational prototile is a nonempty measurable subset of the ambient group.

The label of a tile is deliberately *not* stored here.  Labels live in `PrototileFamily`, so two
geometrically equal supports may still represent differently decorated prototiles. -/
structure Prototile (G : Type u) [MeasurableSpace G] where
  /-- The region occupied before translation. -/
  support : Set G
  /-- Measurability makes the almost-disjointness and covering conditions meaningful. -/
  measurableSet_support : MeasurableSet support
  /-- Empty sets are excluded from the mathematical notion of a tile. -/
  nonempty_support : support.Nonempty

/-- A family of prototiles indexed by a label type `ι`. -/
abbrev PrototileFamily (G : Type u) (ι : Type v) [MeasurableSpace G] :=
  ι → Prototile G

/-- A placement records a translation vector and the label of the prototile being translated. -/
abbrev Placement (G : Type u) (ι : Type v) := G × ι

/-- The region occupied by a placed prototile. -/
def placedTile {G : Type u} {ι : Type v} [NormedAddCommGroup G] [MeasurableSpace G]
    (F : PrototileFamily G ι) (p : Placement G ι) : Set G :=
  p.1 +ᵥ (F p.2).support

/-- Distinct placements form a packing when their occupied regions overlap only on null sets. -/
def IsPacking {G : Type u} {ι : Type v} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (F : PrototileFamily G ι) (A : Set (Placement G ι)) : Prop :=
  A.Pairwise (AEDisjoint μ on placedTile F)

/-- The placements cover when almost every ambient point lies in some placed prototile. -/
def IsCover {G : Type u} {ι : Type v} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (F : PrototileFamily G ι) (A : Set (Placement G ι)) : Prop :=
  ∀ᵐ x ∂μ, x ∈ ⋃ p : A, placedTile F p

/-- A measurable translational tiling is a countable packing which covers almost everywhere.

Countability is part of the definition because it is the standard locally countable measurable
tiling model and makes countable-union measure arguments available. -/
structure IsTiling {G : Type u} {ι : Type v} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (F : PrototileFamily G ι) (A : Set (Placement G ι)) : Prop where
  /-- Only countably many translated copies are used. -/
  countable : A.Countable
  /-- Distinct copies have null overlap. -/
  isPacking : IsPacking μ F A
  /-- Their union has full measure. -/
  isCover : IsCover μ F A

/-! ### The monotile specialization used in the theorem -/

/-- Packing by translates of one set `Ω`. -/
def IsTranslationPacking {G : Type u} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (Ω T : Set G) : Prop :=
  T.Pairwise (AEDisjoint μ on fun t ↦ t +ᵥ Ω)

/-- Almost-everywhere covering by translates of one set `Ω`. -/
def IsTranslationCover {G : Type u} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (Ω T : Set G) : Prop :=
  ∀ᵐ x ∂μ, x ∈ ⋃ t : T, (t : G) +ᵥ Ω

/-- A translation set `T` tiles the ambient measured group by copies of the monotile `Ω`. -/
structure TranslationTiling {G : Type u} [NormedAddCommGroup G] [MeasurableSpace G]
    (μ : Measure G) (Ω T : Set G) : Prop where
  /-- The translation set is countable. -/
  countable : T.Countable
  /-- Distinct translates overlap only on a null set. -/
  isPacking : IsTranslationPacking μ Ω T
  /-- The translates cover almost every point. -/
  isCover : IsTranslationCover μ Ω T

/-! ## 1.1. Periodic translation sets -/

/-- The real plane, represented by `ℂ` with its usual real two-dimensional geometry. -/
abbrev Plane := ℂ

/-- Membership in `A` is unchanged after translation by `h`. -/
def PeriodicBy (A : Set Plane) (h : Plane) : Prop :=
  ∀ x, x + h ∈ A ↔ x ∈ A

/-- A planar translation set is doubly periodic when it has two linearly independent real
periods.  Linear independence rules out both a zero period and two collinear periods. -/
def Periodic (A : Set Plane) : Prop :=
  ∃ h₁ h₂ : Plane,
    LinearIndependent ℝ ![h₁, h₂] ∧ PeriodicBy A h₁ ∧ PeriodicBy A h₂

/-! ## 2. Polygonal tiles -/

/-- Twice the oriented area of the triangle with vertices `a`, `b`, and `c`. -/
def twiceSignedArea (a b c : Plane) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

/-- A nondegenerate closed triangle. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, twiceSignedArea a b c ≠ 0 ∧ s = convexHull ℝ {a, b, c}

/-- A finite decomposition of `Ω` into triangles whose distinct interiors overlap only on a
null set.  Exact union is used for the closed representatives. -/
structure Triangulation (Ω : Set Plane) where
  /-- The finitely many triangular pieces. -/
  pieces : Finset (Set Plane)
  /-- Every piece is a nondegenerate triangle. -/
  isTriangle : ∀ t ∈ pieces, IsTriangle t
  /-- Distinct triangles intersect only on a null set. -/
  pairwiseAEDisjoint : (pieces : Set (Set Plane)).Pairwise (AEDisjoint volume)
  /-- The pieces have union exactly `Ω`. -/
  sUnion_eq : ⋃₀ (pieces : Set (Set Plane)) = Ω

/-- A planar set is polygonal when it can be written as a finite union of nondegenerate
triangles, with overlaps allowed only along null boundaries. -/
def Polygonal (Ω : Set Plane) : Prop :=
  Nonempty (Triangulation Ω)

/-- The intrinsic vertices of a polygonal set.

A point is intrinsic when every triangulation sees it as an extreme point of one of its triangle
pieces.  Quantifying over every triangulation makes this independent of arbitrary added diagonals
or subdivisions. -/
def intrinsicVertices (Ω : Set Plane) : Set Plane :=
  {x | ∀ triangulation : Triangulation Ω,
    ∃ t ∈ triangulation.pieces, x ∈ t.extremePoints ℝ}

/-! ## 3. Rational polygonal tiles -/

/-- A planar point with integer real and imaginary coordinates. -/
def IsIntegerPoint (z : Plane) : Prop :=
  ∃ m n : ℤ, z = (m : ℝ) + (n : ℝ) * Complex.I

/-- A translation-invariant common-denominator presentation of a rational polygon.

The chosen `anchor` is an intrinsic vertex.  After moving it to the origin, multiplication by one
positive natural number sends every intrinsic vertex into `ℤ²`.  This is equivalent to saying
that every difference of two polygon vertices has rational coordinates, but records the common
denominator needed by the normalization argument. -/
def RationalPolygon (Ω : Set Plane) : Prop :=
  Polygonal Ω ∧ Ω.Nonempty ∧
    ∃ anchor : Plane, anchor ∈ intrinsicVertices Ω ∧
      ∃ denominator : ℕ, 0 < denominator ∧
        ∀ w ∈ intrinsicVertices Ω,
          IsIntegerPoint ((denominator : ℝ) • (w - anchor))

end DeDiosGreenfeldComparator

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
theorem periodic_tiling_of_rational_polygon
    (Ω : Set Plane) (hΩ : RationalPolygon Ω) :
    (∃ T : Set Plane, TranslationTiling volume Ω T) →
      ∃ T : Set Plane, Periodic T ∧ TranslationTiling volume Ω T := by
  intro htileable
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
