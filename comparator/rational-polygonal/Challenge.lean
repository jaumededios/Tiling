import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# A Mathlib-only statement of periodicity for rational polygonal tilings

This is the *trusted vocabulary* for a `leanprover/comparator` challenge.  In particular, this
file imports only Mathlib: none of the definitions below is inherited from the formalization that
will eventually prove the theorem.

The presentation proceeds in the same order in which a mathematician might introduce the
objects.

1. A labelled prototile family is placed by translations in a measured additive group.
2. A tiling is a countable packing which covers almost every point.
3. For a single tile in the real plane, double periodicity means invariance under two linearly
   independent translation vectors.
4. A polygonal region is a finite almost-disjoint union of nondegenerate closed triangles.
5. Rationality is expressed intrinsically, after translating one vertex to the origin and
   clearing all vertex denominators at once.

Closed triangles are convenient Lean objects.  The paper uses bounded open polygonal sets, but a
polygonal set and its interior differ only on finitely many line segments, hence on a null set.
Because packing and covering below are measure-theoretic, this choice does not change tileability.
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

/-! ## 4. The periodic tiling theorem -/

namespace DeDiosGreenfeldComparator

open MeasureTheory

/-- **Periodic tiling theorem for rational polygonal sets.**

If the rational polygonal set `Ω` tiles the real plane by translations at all, then it also tiles
using a translation set invariant under two linearly independent periods.  The ambient measure is
Mathlib's Lebesgue measure `volume` on `ℂ ≃ ℝ²`. -/
theorem periodic_tiling_of_rational_polygon
    (Ω : Set Plane) (hΩ : RationalPolygon Ω) :
    (∃ T : Set Plane, TranslationTiling volume Ω T) →
      ∃ T : Set Plane, Periodic T ∧ TranslationTiling volume Ω T := by
  sorry

end DeDiosGreenfeldComparator
