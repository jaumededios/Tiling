import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.MeasureTheory.Group.Pointwise
import Mathlib.MeasureTheory.Measure.AEDisjoint
import Mathlib.Topology.LocallyFinite

set_option linter.style.header false

/-!
# Translational tilings

This file models tilings of a normed additive group, including `ℤ`, `ℝ`, and finite-dimensional
Euclidean spaces.  A prototile is a nonempty measurable set; in particular, its support need not
be bounded.  Its label is kept separate from its support, so differently oriented or decorated
copies may have the same underlying set.

A placement is a translation vector together with a prototile label.  Geometric tilings are
locally finite, pairwise almost-everywhere disjoint, and cover almost every point.  Compatibility
conditions are encoded in the geometry of the prototile supports themselves.
-/

open scoped Pointwise
open Function MeasureTheory

namespace Tiling

universe u v

/-- A nonempty measurable set used as a translational prototile. -/
structure Prototile (E : Type u) [MeasurableSpace E] where
  support : Set E
  measurableSet_support : MeasurableSet support
  nonempty_support : support.Nonempty

/-- A labelled family of prototiles.  The type `P` carries identity, orientation, or decoration;
the function supplies the geometric prototile attached to each label. -/
abbrev PrototileFamily (E : Type u) (P : Type v) [MeasurableSpace E] :=
  P → Prototile E

/-- A placement consists of a translation vector and a prototile label. -/
abbrev Placement (E : Type u) (P : Type v) := E × P

section Geometry

variable {E : Type u} {P : Type v}
variable [NormedAddCommGroup E] [MeasureSpace E]

/-- The set occupied by the translate `(x, p)`. -/
def placedTile (T : PrototileFamily E P) (i : Placement E P) : Set E :=
  i.1 +ᵥ (T i.2).support

/-- The set covered by a collection of translated prototiles. -/
def coveredSet (T : PrototileFamily E P) (A : Set (Placement E P)) : Set E :=
  ⋃ i : A, placedTile T i

/-- Only finitely many placed supports meet a sufficiently small neighborhood of each point. -/
def IsLocallyFinite (T : PrototileFamily E P) (A : Set (Placement E P)) : Prop :=
  LocallyFinite fun i : A ↦ placedTile T i

/-- Distinct placements have almost-everywhere disjoint supports. -/
def IsPacking (T : PrototileFamily E P) (A : Set (Placement E P)) : Prop :=
  A.Pairwise (AEDisjoint volume on placedTile T)

/-- Almost every point belongs to the union of the placed supports. -/
def IsCover (T : PrototileFamily E P) (A : Set (Placement E P)) : Prop :=
  ∀ᵐ x, x ∈ coveredSet T A

/-- A locally finite measurable translational tiling. -/
structure IsTiling (T : PrototileFamily E P) (A : Set (Placement E P)) : Prop where
  locallyFinite : IsLocallyFinite T A
  isPacking : IsPacking T A
  isCover : IsCover T A

end Geometry

end Tiling
