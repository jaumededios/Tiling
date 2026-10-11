import Tiling.AxisParallel.Decidability.Input
import Tiling.Computability.FunProp
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

namespace Tiling.AxisParallel.Decidability.OracleCoefficients

open Tiling.AxisParallel.SetFormulation
open Tiling.Computability.Rational Tiling.Computability.List

def coefficients (n : ℕ) (q : Query) : List ℤ :=
  (List.range (2 * n)).map fun j => (q.2.2.count j : ℤ) - (q.2.1.count j : ℤ)

def encodeQuery (n : ℕ) (q : Query) : ℕ :=
  Encodable.encode (decide (q.1 ≠ 0), coefficients n q)

theorem count_computable : Computable₂ (fun (xs : List ℕ) (j : ℕ) => xs.count j) := by
  have hf := (PrimrecRel.listFilter (Primrec.eq : PrimrecRel (fun a b : ℕ => a = b))).to_comp
  refine (Computable.list_length.comp hf).to₂.of_eq ?_
  intro xs
  simp only [List.count, List.countP_eq_length_filter]
  congr 2

theorem coefficients_computable (n : ℕ) : Computable (coefficients n) := by
  unfold coefficients
  apply map_computable 0 (Computable.const (List.range (2 * n)))
  exact (int_sub_computable.comp
    (int_ofNat_computable.comp (count_computable.comp
      (Computable.snd.comp (Computable.snd.comp Computable.fst)) Computable.snd))
    (int_ofNat_computable.comp (count_computable.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd))).to₂

theorem encodeQuery_computable (n : ℕ) : Computable (encodeQuery n) := by
  unfold encodeQuery
  exact Primrec.encode.to_comp.comp
    (((Primrec.eq.comp Primrec.fst (Primrec.const (0 : Fin 2))).not.decide.to_comp).pair
      (coefficients_computable n))

theorem coefficients_getD (n : ℕ) (q : Query) (j : ℕ) (hj : j < 2 * n) :
    (coefficients n q).getD j 0 = (q.2.2.count j : ℤ) - (q.2.1.count j : ℤ) := by
  rw [List.getD_eq_getElem _ _
    (by simpa only [coefficients, List.length_map, List.length_range] using hj)]
  simp [coefficients]

theorem coefficients_computable₂ : Computable₂ coefficients := by
  unfold coefficients
  apply map_computable 0
    (Primrec.list_range.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (Computable.const 2) Computable.fst))
  exact (int_sub_computable.comp
    (int_ofNat_computable.comp (count_computable.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      Computable.snd))
    (int_ofNat_computable.comp (count_computable.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
      Computable.snd))).to₂

theorem encodeQuery_computable₂ : Computable₂ encodeQuery := by
  unfold encodeQuery
  exact Primrec.encode.to_comp.comp
    (((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.const (0 : Fin 2))).not.decide.to_comp).pair coefficients_computable₂)

theorem sum_count_coordinates (V : List Plane) (axis : Fin 2) (indices : List ℕ)
    (m : ℕ) (hm : V.length = m) :
    (∑ j ∈ Finset.range m, (indices.count j : ℝ) * coordinate axis (V.getD j 0)) =
      coordinateSum V axis indices := by
  induction indices with
  | nil => simp [coordinateSum]
  | cons a xs ih =>
    simp only [List.count_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      add_mul, Finset.sum_add_distrib]
    rw [ih]
    have hsingle : (∑ j ∈ Finset.range m,
        (if a == j then (1 : ℝ) else 0) * coordinate axis (V.getD j 0)) =
        coordinate axis (V.getD a 0) := by
      by_cases ha : a < m
      · simp [beq_iff_eq, ha]
      · have hout : V.getD a 0 = 0 := List.getD_eq_default _ _ (by omega)
        rw [hout]
        simp [beq_iff_eq, ha, coordinate, p₁, p₂]
    rw [hsingle]
    simp [coordinateSum, add_comm]

theorem coefficient_sum_eq (V : List Plane) (n : ℕ) (q : Query)
    (hV : V.length = 2 * n) :
    (∑ j ∈ Finset.range (2 * n),
      (((q.2.2.count j : ℤ) - (q.2.1.count j : ℤ) : ℤ) : ℝ) *
        coordinate q.1 (V.getD j 0)) =
      coordinateSum V q.1 q.2.2 - coordinateSum V q.1 q.2.1 := by
  simp only [Int.cast_sub, Int.cast_natCast, sub_mul, Finset.sum_sub_distrib]
  rw [sum_count_coordinates V q.1 q.2.2 _ hV,
    sum_count_coordinates V q.1 q.2.1 _ hV]

theorem coefficients_sum_eq (V : List Plane) (n : ℕ) (q : Query)
    (hV : V.length = 2 * n) :
    (∑ j ∈ Finset.range (2 * n), ((coefficients n q).getD j 0 : ℝ) *
        coordinate q.1 (V.getD j 0)) =
      coordinateSum V q.1 q.2.2 - coordinateSum V q.1 q.2.1 := by
  convert coefficient_sum_eq V n q hV using 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficients_getD n q j (Finset.mem_range.mp hj)]

end Tiling.AxisParallel.Decidability.OracleCoefficients
