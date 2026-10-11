import Tiling.RationalPolygonal.Earthquake
import TranslationalTilings.Slicing

/-!
# Core definitions for axis-parallel discrete tilings

This file contains the transparent coordinate, fibre, plate, and column definitions used by the
axis-parallel discrete development.  It deliberately reuses the canonical earthquake components
and exact discrete carrier from `Tiling.RationalPolygonal`.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Discrete

/-- The positive horizontal coordinate vector in `ℤ²`. -/
abbrev horizontalDiscreteUnit : TranslationalTilings.Plane := ![1, 0]

/-- The positive vertical coordinate vector in `ℤ²`. -/
abbrev verticalDiscreteUnit : TranslationalTilings.Plane := ![0, 1]

/-- First coordinate on the integer lattice plane. -/
def firstDiscreteCoordinate (z : TranslationalTilings.Plane) : ℤ := z 0

/-- The vertical affine lattice fibre with first coordinate `x`. -/
def verticalDiscreteFibre (x : ℤ) : Set TranslationalTilings.Plane :=
  TranslationalTilings.addCoset
    (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
    (x • horizontalDiscreteUnit)

/-- The union of vertical fibres whose first coordinates are congruent to `x` modulo `L`. -/
def verticalDiscreteCongruenceClass (x : ℤ) (L : ℕ) :
    Set TranslationalTilings.Plane :=
  ⋃ n : ℤ, verticalDiscreteFibre (x + n * (L : ℤ))

/-- The vertical cylinder over a set of first coordinates. -/
def verticalDiscreteCylinder (B : Set ℤ) : Set TranslationalTilings.Plane :=
  ⋃ x : B, verticalDiscreteFibre x

/-- Pointwise sum of two integer subsets. -/
def integerSumset (B C : Set ℤ) : Set ℤ := B + C

/-- A canonical vertical earthquake plate whose centres have one first coordinate. -/
def IsDiscreteVerticalColumn
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) : Prop :=
  ∃ c : ℤ,
    firstDiscreteCoordinate '' Tiling.RationalPolygonal.quakePlateTranslations P = {c}

/-- Union of the centre sets of all canonical vertical-column plates. -/
def discreteColumnUnion
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) : Set TranslationalTilings.Plane :=
  ⋃ (P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit),
    ⋃ (_ : IsDiscreteVerticalColumn P),
      Tiling.RationalPolygonal.quakePlateTranslations P

/-- The canonical vertical earthquake plates which are not columns. -/
def noncolumnDiscretePlates
    (F : Finset TranslationalTilings.Plane)
    (A : Set TranslationalTilings.Plane) :
    Set (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit) :=
  {P | ¬ IsDiscreteVerticalColumn P}

end Tiling.AxisParallel.Discrete
