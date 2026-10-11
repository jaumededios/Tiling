import Tiling.AxisParallel.Decidability.Oracle.Coefficients
import Tiling.AxisParallel.Decidability.RectangleInput.Geometry
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace Tiling.AxisParallel.Decidability.OracleCoefficients

open Tiling.AxisParallel.SetFormulation

theorem sum_range_pairs (n : ℕ) (f : ℕ → ℝ) :
    (∑ j ∈ Finset.range (2 * n), f j) =
      ∑ i ∈ Finset.range n, (f (2 * i) + f (2 * i + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [add_assoc]

theorem corner_sum_eq (n : ℕ) (data : (Fin n → Plane) × (Fin n → Plane))
    (coeffs : List ℤ) (axis : Fin 2) :
    (∑ j ∈ Finset.range (2 * n), (coeffs.getD j 0 : ℝ) *
      coordinate axis ((cornerList (List.ofFn fun i => (data.1 i, data.2 i))).getD j 0)) =
    ∑ i : Fin n, ((coeffs.getD (2 * i.val) 0 : ℤ) • coordinate axis (data.1 i) +
      (coeffs.getD (2 * i.val + 1) 0 : ℤ) • coordinate axis (data.2 i)) := by
  rw [sum_range_pairs]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hin : i.val < n := i.isLt
  rw [RectangleInput.cornerList_getD_left _ (by simpa only [List.length_ofFn] using hin),
    RectangleInput.cornerList_getD_right _ (by simpa only [List.length_ofFn] using hin)]
  rw [List.getD_eq_getElem (List.ofFn fun i => (data.1 i, data.2 i)) (0, 0)
    (by simpa only [List.length_ofFn] using hin)]
  simp only [List.getElem_ofFn, zsmul_eq_mul]

end Tiling.AxisParallel.Decidability.OracleCoefficients
