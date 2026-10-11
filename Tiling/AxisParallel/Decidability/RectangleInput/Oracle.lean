import Tiling.AxisParallel.Decidability.RectangleInput.Realization
import Tiling.AxisParallel.Decidability.ComparisonTransport

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Decidability.QueryTransport

def sortBool : CoordSort → Bool
  | .horizontal => false
  | .vertical => true

@[simp] theorem packedAxis_sortBool (s : CoordSort) :
    packedAxis (sortBool s) = axis (sortBool s) := by
  cases s <;> rfl

@[simp] theorem coordinate_sortBool (s : CoordSort) (z : Plane) :
    coordinate (axis (sortBool s)) z = s.axis.coord z := by
  cases s <;> rfl

theorem linearCoordinateSum_ofFn {n : ℕ} (V : List Plane) (a : Fin 2) (f : Fin n → ℤ) :
    linearCoordinateSum V a (List.ofFn f) =
      ∑ i : Fin n, (f i : ℝ) * coordinate a (V.getD i 0) := by
  unfold linearCoordinateSum indexedCoefficients
  simp only [List.length_ofFn, List.map_map]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [Function.comp_apply]
  rw [List.getD_eq_getElem (List.ofFn f) 0
      (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem_ofFn]

theorem normalizedVertices_getD {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (i : Fin (vertexLabels (R.length, history)).length) :
    (normalizedVertices (cornerList R) (vertexLabels (R.length, history)) 0).getD i 0 =
      (realization hR h hinput).vertex i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [normalizedVertices, List.length_map] using i.isLt)]
  simp only [normalizedVertices, List.getElem_map, realization_vertex,
    originalVertex, anchor, List.getD_eq_getElem _ _ i.isLt]
  rfl

theorem linearCoordinateSum_eq_evalCoeff {R : List (Plane × Plane)} {Ω : Set Plane}
    {history : List Bool} (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (s : CoordSort) (a : Coeff (inputCode (R.length, history) hinput)) :
    linearCoordinateSum
      (normalizedVertices (cornerList R) (vertexLabels (R.length, history)) 0)
      (packedAxis (sortBool s)) (List.ofFn a) = evalCoeff (realization hR h hinput) s a := by
  rw [linearCoordinateSum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [normalizedVertices_getD hR h hinput i, packedAxis_sortBool, coordinate_sortBool]

def nativeQueryToCorner {input : TableInput}
    {hinput : 0 < (vertexLabels input).length}
    (q : Tiling.AxisParallel.Terminal.Executable.Query (inputCode input hinput)) :
    Tiling.AxisParallel.Decidability.Query :=
  compilePackedComparison (vertexLabels input) 0
    (sortBool q.sort, List.ofFn q.lhs, List.ofFn q.rhs)

/-- A correct corner oracle induces a correct oracle on the computed translated
production region; integer signs and the anchor correction are handled by the
finite query compiler. -/
def oracle {R : List (Plane × Plane)} {Ω : Set Plane} {history : List Bool}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (h : TableCorrect (cornerList R) history)
    (hinput : 0 < (vertexLabels (R.length, history)).length)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer) :
    Tiling.AxisParallel.Terminal.Executable.CorrectOracle
      (inputCode (R.length, history) hinput) (realization hR h hinput) where
  answer q := answer (nativeQueryToCorner q)
  correct q := by
    rw [nativeQueryToCorner, compilePackedComparison_correct hanswer,
      linearCoordinateSum_eq_evalCoeff hR h hinput q.sort q.lhs,
      linearCoordinateSum_eq_evalCoeff hR h hinput q.sort q.rhs, sub_nonpos]

end Tiling.AxisParallel.Decidability.RectangleInput
