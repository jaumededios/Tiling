import Tiling.AxisParallel.SetFormulation.Definitions

/-!
# Finite geometric inputs and coordinate comparison queries

These lists and indices are the internal input language of the verified decision
algorithm. Planar geometry comes from the set formulation.
-/

set_option autoImplicit false

open Set Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability

def cornerList (R : List (Plane × Plane)) : List Plane :=
  R.flatMap fun (a, b) ↦ [a, b]

def coordinate (i : Fin 2) (z : Plane) : ℝ := if i = 0 then p₁ z else p₂ z

abbrev Query := Fin 2 × List ℕ × List ℕ

def coordinateSum (V : List Plane) (i : Fin 2) (indices : List ℕ) : ℝ :=
  (indices.map fun j ↦ coordinate i (V.getD j 0)).sum

def Comparison (V : List Plane) : Query → Prop :=
  fun (i, left, right) ↦ coordinateSum V i left ≤ coordinateSum V i right

def CorrectOracle (V : List Plane) (answer : Query → Bool) : Prop :=
  ∀ i left right,
    answer (i, left, right) = true ↔ coordinateSum V i left ≤ coordinateSum V i right

end Tiling.AxisParallel.Decidability
