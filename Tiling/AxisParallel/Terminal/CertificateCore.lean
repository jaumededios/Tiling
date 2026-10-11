import Mathlib.Data.Finsupp.Basic
import Mathlib.Logic.Function.Basic
import Tiling.AxisParallel.Terminal.NormalFormCore
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Tiling.AxisParallel.Terminal.PeriodicReplacementCore

/-!
# Oracle-relative tiling certificates

This definition-only module contains the legacy finite input presentation and coordinate-order
oracle interface, together with the relative semidecision and decision records. The executable
formula language and certificate codes live in their dedicated lower modules.
-/

open scoped BigOperators Pointwise
open Set

noncomputable section

namespace Tiling.AxisParallel.Terminal

/-- An open axis-parallel rectangle in the complex model of the plane. -/
def openRectangle (left right bottom top : ℝ) : Set Tiling.Plane :=
  {z | left < z.re ∧ z.re < right ∧ bottom < z.im ∧ z.im < top}

/-- A finite decomposition of a polygonal region into disjoint open rectangles. -/
structure RectangleCellPresentation (K : Tiling.AxisParallel.Region) where
  numberOfCells : ℕ
  numberOfCells_pos : 0 < numberOfCells
  leftVertex : Fin numberOfCells → ↥K.vertices
  rightVertex : Fin numberOfCells → ↥K.vertices
  bottomVertex : Fin numberOfCells → ↥K.vertices
  topVertex : Fin numberOfCells → ↥K.vertices
  left_lt_right : ∀ i, (leftVertex i).1.re < (rightVertex i).1.re
  bottom_lt_top : ∀ i, (bottomVertex i).1.im < (topVertex i).1.im
  cells_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ
    (fun i ↦ openRectangle
      (leftVertex i).1.re (rightVertex i).1.re
      (bottomVertex i).1.im (topVertex i).1.im)

/-- The union of the open rectangular cells in a presentation. -/
def RectangleCellPresentation.carrier
    {K : Tiling.AxisParallel.Region} (P : RectangleCellPresentation K) : Set Tiling.Plane :=
  ⋃ i, openRectangle
    (P.leftVertex i).1.re (P.rightVertex i).1.re
    (P.bottomVertex i).1.im (P.topVertex i).1.im

/-- An axis-parallel tile together with the finite cell data presented to an oracle verifier. -/
structure EncodedAxisParallelRegion where
  region : Tiling.AxisParallel.Region
  presentation : RectangleCellPresentation region
  originVertex : ↥region.vertices
  originVertex_eq_zero : originVertex.1 = 0
  presentation_correct : presentation.carrier =ᵐ[MeasureTheory.volume] region.openCarrier

/-- Evaluate an integer linear combination of input vertex coordinates. -/
def evalCoordExpr (E : EncodedAxisParallelRegion) (axis : Tiling.AxisParallel.Axis)
    (a : ↥E.region.vertexFinset →₀ ℤ) : ℝ :=
  a.sum fun v n ↦ (n : ℝ) * axis.coord (v : Tiling.Plane)

/-- An oracle deciding weak order between input-coordinate expressions in one coordinate sort. -/
structure CoordinateOrderOracle
    (E : EncodedAxisParallelRegion) (axis : Tiling.AxisParallel.Axis) where
  answer : (↥E.region.vertexFinset →₀ ℤ) →
    (↥E.region.vertexFinset →₀ ℤ) → Bool
  correct : ∀ a b, answer a b = true ↔
    evalCoordExpr E axis a ≤ evalCoordExpr E axis b

/-- The independent horizontal and vertical coordinate-order oracles. -/
structure SelectedCoordinateOracles (E : EncodedAxisParallelRegion) where
  horizontal : CoordinateOrderOracle E Tiling.AxisParallel.Axis.horizontal
  vertical : CoordinateOrderOracle E Tiling.AxisParallel.Axis.vertical

/-- A same-coordinate comparison query. -/
inductive CoordQuery (E : EncodedAxisParallelRegion)
  | horizontalLe :
      (↥E.region.vertexFinset →₀ ℤ) →
      (↥E.region.vertexFinset →₀ ℤ) → CoordQuery E
  | verticalLe :
      (↥E.region.vertexFinset →₀ ℤ) →
      (↥E.region.vertexFinset →₀ ℤ) → CoordQuery E

/-- Dispatch a selected-coordinate query to the corresponding original oracle. -/
def SelectedCoordinateOracles.answer
    {E : EncodedAxisParallelRegion} (O : SelectedCoordinateOracles E) :
    CoordQuery E → Bool
  | .horizontalLe a b => O.horizontal.answer a b
  | .verticalLe a b => O.vertical.answer a b

/-- A semidecision procedure relative to a fixed Boolean oracle. -/
structure RelativeSemidecision (Q : Type) (answer : Q → Bool) (P : Prop) where
  program : ℕ → OracleProgram Q Bool
  sound : ∀ n, OracleProgram.evaluate answer (program n) = true → P
  complete : P → ∃ n, OracleProgram.evaluate answer (program n) = true

/-- Two complementary semidecisions packaged with one dovetailed decision program. -/
structure RelativeDecision (Q : Type) (answer : Q → Bool) (P : Prop) where
  positive : RelativeSemidecision Q answer P
  negative : RelativeSemidecision Q answer (¬ P)
  decisionProgram : ℕ → OracleProgram Q (Option Bool)
  true_sound : ∀ n,
    OracleProgram.evaluate answer (decisionProgram n) = some true → P
  false_sound : ∀ n,
    OracleProgram.evaluate answer (decisionProgram n) = some false → ¬ P
  halts : ∃ n b, OracleProgram.evaluate answer (decisionProgram n) = some b

/-- The semantic proposition decided by the terminal oracle procedure. -/
def isPlaneTileable (E : EncodedAxisParallelRegion) : Prop :=
  ∃ S : Set Tiling.Plane, Tiling.AxisParallel.TilesOn E.region S Set.univ

end Tiling.AxisParallel.Terminal
