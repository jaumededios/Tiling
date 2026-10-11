import Tiling.AxisParallel.Continuous.PlateCore

set_option linter.style.header false

/-!
# Horizontal-complexity definitions

This module owns the projected-centre, translated-vertex, bounded-difference, and ordered-gap
vocabulary used by the continuous finite-horizontal-complexity development.
-/

open Set

namespace Tiling.AxisParallel.Continuous

/-- The first-coordinate projection of a set of planar translation centres. -/
def horizontalCentreProjection
    (T : Set Tiling.Plane) : Set ℝ :=
  Complex.re '' T

/-- First coordinates of all translated vertices of `K` at centres in `T`. -/
def horizontalTranslatedVertices
    (K : Region) (T : Set Tiling.Plane) : Set ℝ :=
  {x : ℝ | ∃ v ∈ K.vertices, ∃ t ∈ T, x = (v + t).re}

/-- A planar centre set has finite horizontal complexity when its first-coordinate projection has
finite local complexity. -/
def HasFiniteHorizontalComplexity
    (T : Set Tiling.Plane) : Prop :=
  HasFLC (horizontalCentreProjection T)

/-- Differences of pairs of points of `A` whose absolute value is at most `R`. -/
def horizontalBoundedDifferences
    (A : Set ℝ) (R : ℝ) : Set ℝ :=
  {d : ℝ | ∃ a ∈ A, ∃ b ∈ A, d = b - a ∧ |d| ≤ R}

/-- A strict integer ordering of a set together with its exact finite alphabet of adjacent gaps. -/
structure HorizontalOrderData (A : Set ℝ) where
  point : ℤ → ℝ
  point_strictMono : StrictMono point
  point_range : Set.range point = A
  gapAlphabet : Finset ℝ
  gap_mem : ∀ i : ℤ, point (i + 1) - point i ∈ gapAlphabet
  gap_pos : ∀ g ∈ gapAlphabet, 0 < g
  gap_complete : ∀ g ∈ gapAlphabet,
    ∃ i : ℤ, g = point (i + 1) - point i

/-- The set of adjacent gaps displayed by an integer ordering. -/
def horizontalGapSet
    {A : Set ℝ} (order : HorizontalOrderData A) : Set ℝ :=
  {g : ℝ | ∃ i : ℤ, g = order.point (i + 1) - order.point i}

end Tiling.AxisParallel.Continuous
