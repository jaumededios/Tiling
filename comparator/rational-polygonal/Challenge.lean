import Mathlib

/-!
# A Mathlib-only statement of periodicity for rational polygonal tilings

This is a self-contained statement for `leanprover/comparator`. It imports only Mathlib: none of
the definitions below is inherited from the formalization that will eventually prove the theorem.
The definitions are specialized to one tile in the real plane so that the file reads like the
mathematical theorem, rather than like a reusable software interface.

The presentation proceeds in the same order in which a mathematician might introduce the
objects.

1. A set `Ω` tiles the plane along a translation set `T` when its translates pack and cover almost
   everywhere.
2. Double periodicity means invariance under two linearly
   independent translation vectors.
3. A polygonal region is a finite almost-disjoint union of nondegenerate closed triangles.
4. Rationality is expressed intrinsically, after translating one vertex to the origin and
   clearing all vertex denominators at once.

Closed triangles are convenient Lean objects.  The paper uses bounded open polygonal sets, but a
polygonal set and its interior differ only on finitely many line segments, hence on a null set.
Because packing and covering below are measure-theoretic, this choice does not change tileability.
-/

open Function MeasureTheory Set
open scoped Pointwise

namespace DeDiosGreenfeldComparator

/-! ## 1. Translational tilings of the plane -/

/-- The real plane, represented by `ℂ` with its usual real two-dimensional geometry. -/
abbrev Plane := ℂ

/-- The translates `t + Ω`, for `t ∈ T`, form a packing: two distinct copies of the tile `Ω`
overlap only on a set of Lebesgue measure zero. -/
def Packing (Ω T : Set Plane) : Prop :=
  ∀ ⦃s⦄, s ∈ T → ∀ ⦃t⦄, t ∈ T → s ≠ t →
    volume ((s +ᵥ Ω) ∩ (t +ᵥ Ω)) = 0

/-- The translates of `Ω` by `T` cover almost every point of the plane. -/
def Covering (Ω T : Set Plane) : Prop :=
  ∀ᵐ x ∂volume, ∃ t ∈ T, x ∈ t +ᵥ Ω

/-- The set `T` is a translational tiling of the plane by the single tile `Ω`: `T` is countable,
its translates of `Ω` form a packing, and those translates cover almost every point. -/
def Tiling (Ω T : Set Plane) : Prop :=
  T.Countable ∧ Packing Ω T ∧ Covering Ω T

/-! ## 1.1. Periodic translation sets -/

/-- Membership in `A` is unchanged after translation by `h`. -/
def PeriodicBy (A : Set Plane) (h : Plane) : Prop :=
  ∀ x, x + h ∈ A ↔ x ∈ A

/-- A planar translation set is doubly periodic when it has two nonparallel periods.

The displayed determinant is nonzero exactly when the two vectors are linearly independent. -/
def Periodic (A : Set Plane) : Prop :=
  ∃ h₁ h₂ : Plane,
    h₁.re * h₂.im - h₁.im * h₂.re ≠ 0 ∧ PeriodicBy A h₁ ∧ PeriodicBy A h₂

/-! ## 2. Polygonal tiles -/

/-- Twice the oriented area of the triangle with vertices `a`, `b`, and `c`. -/
def twiceSignedArea (a b c : Plane) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

/-- A nondegenerate closed triangle. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, twiceSignedArea a b c ≠ 0 ∧ s = convexHull ℝ {a, b, c}

/-- A finite decomposition of `Ω` into triangles whose distinct interiors overlap only on a
null set. Exact union is used for the closed representatives. -/
structure Triangulation (Ω : Set Plane) where
  /-- The finitely many triangular pieces. -/
  pieces : Finset (Set Plane)
  /-- Every piece is a nondegenerate triangle. -/
  isTriangle : ∀ t ∈ pieces, IsTriangle t
  /-- Distinct triangles intersect only on a null set. -/
  nullOverlap : ∀ ⦃s⦄, s ∈ pieces → ∀ ⦃t⦄, t ∈ pieces → s ≠ t →
    volume (s ∩ t) = 0
  /-- The pieces have union exactly `Ω`. -/
  sUnion_eq : ⋃₀ (pieces : Set (Set Plane)) = Ω

/-- A planar set is polygonal when it can be written as a finite union of nondegenerate
triangles, with overlaps allowed only along null boundaries. -/
def Polygonal (Ω : Set Plane) : Prop :=
  Nonempty (Triangulation Ω)

/-- The intrinsic vertices of a polygonal set.

A point is intrinsic when every triangulation sees it as an extreme point of one of its triangle
pieces. Quantifying over every triangulation makes this independent of arbitrary added diagonals
or subdivisions. -/
def intrinsicVertices (Ω : Set Plane) : Set Plane :=
  {x | ∀ triangulation : Triangulation Ω,
    ∃ t ∈ triangulation.pieces, x ∈ t.extremePoints ℝ}

/-! ## 3. Rational polygonal tiles -/

/-- A planar point with integer real and imaginary coordinates. -/
def IsIntegerPoint (z : Plane) : Prop :=
  ∃ m n : ℤ, z = (m : ℝ) + (n : ℝ) * Complex.I

/-- A translation-invariant common-denominator presentation of a rational polygon.

The chosen `anchor` is an intrinsic vertex. After moving it to the origin, multiplication by one
positive natural number sends every intrinsic vertex into `ℤ²`. This is equivalent to saying
that every difference of two polygon vertices has rational coordinates, but records the common
denominator needed by the normalization argument. -/
def RationalPolygon (Ω : Set Plane) : Prop :=
  Polygonal Ω ∧ Ω.Nonempty ∧
    ∃ anchor : Plane, anchor ∈ intrinsicVertices Ω ∧
      ∃ denominator : ℕ, 0 < denominator ∧
        ∀ w ∈ intrinsicVertices Ω,
          IsIntegerPoint ((denominator : ℝ) • (w - anchor))

/-! ## 4. The periodic tiling theorem -/

/-- **Periodic tiling theorem for rational polygonal sets.**

If the rational polygonal set `Ω` tiles the real plane by translations at all, then it also tiles
using a translation set invariant under two linearly independent periods.  The ambient measure is
Mathlib's Lebesgue measure `volume` on `ℂ ≃ ℝ²`. -/
theorem periodic_tiling_of_rational_polygon
    (Ω : Set Plane) (hΩ : RationalPolygon Ω) :
    (∃ T : Set Plane, Tiling Ω T) →
      ∃ T : Set Plane, Periodic T ∧ Tiling Ω T := by
  sorry

end DeDiosGreenfeldComparator
