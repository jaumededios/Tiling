import Tiling.AxisParallel.Decidability.Input
import Mathlib.Computability.Partrec

/-!
# A finite coordinate comparison table

The boundary frontend asks exactly two comparisons for each ordered pair of
vertex labels. Its remaining operations use a Boolean list, so no real number
comparison or choice enters the executable frontend. Out-of-range reads have a
fixed default, making the operations total on malformed input and histories.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

/-- `false` denotes the first coordinate and `true` the second. -/
def axis (vertical : Bool) : Fin 2 := if vertical then 1 else 0

def comparisonIndex (n : ℕ) (vertical : Bool) (i j : ℕ) : ℕ :=
  2 * (i * n + j) + bif vertical then 1 else 0

/-- The query at a given position of the fixed comparison schedule. -/
def comparisonQuery (n k : ℕ) : Query :=
  (axis (k % 2 == 1), [k / 2 / n], [k / 2 % n])

def comparisonQueries (n : ℕ) : List Query :=
  (List.range (2 * (n * n))).map (comparisonQuery n)

def compare (n : ℕ) (history : List Bool) (vertical : Bool) (i j : ℕ) : Bool :=
  history.getD (comparisonIndex n vertical i j) false

/-- The table obtained by answering the fixed finite schedule. -/
def comparisonHistory (n : ℕ) (answer : Query → Bool) : List Bool :=
  (comparisonQueries n).map answer

theorem comparisonQuery_index {n i j : ℕ} (hi : i < n) (hj : j < n)
    (vertical : Bool) :
    comparisonQuery n (comparisonIndex n vertical i j) =
      (axis vertical, [i], [j]) := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have hdiv : (i * n + j) / n = i := by
    rw [Nat.mul_comm i n, Nat.mul_add_div hn, Nat.div_eq_of_lt hj, Nat.add_zero]
  have hmod : (i * n + j) % n = j := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hj]
  cases vertical <;> simp [comparisonQuery, comparisonIndex, axis,
    Nat.add_div, hdiv, hmod]

theorem comparisonIndex_lt {n i j : ℕ} (hi : i < n) (hj : j < n)
    (vertical : Bool) : comparisonIndex n vertical i j < 2 * (n * n) := by
  have hrow : i * n + j < n * n := by
    calc
      i * n + j < i * n + n := Nat.add_lt_add_left hj _
      _ = (i + 1) * n := by simp [Nat.add_mul]
      _ ≤ n * n := Nat.mul_le_mul_right n hi
  cases vertical <;> simp only [comparisonIndex, Bool.cond_false, Bool.cond_true] <;> omega

theorem comparisonQueries_length (n : ℕ) :
    (comparisonQueries n).length = 2 * (n * n) := by
  simp [comparisonQueries]

theorem comparisonHistory_length (n : ℕ) (answer : Query → Bool) :
    (comparisonHistory n answer).length = 2 * (n * n) := by
  simp [comparisonHistory, comparisonQueries]

theorem compare_history {n i j : ℕ} (hi : i < n) (hj : j < n)
    (vertical : Bool) (answer : Query → Bool) :
    compare n (comparisonHistory n answer) vertical i j =
      answer (axis vertical, [i], [j]) := by
  have hlt := comparisonIndex_lt hi hj vertical
  simp only [compare, comparisonHistory, comparisonQueries, List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa using hlt)]
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
  rw [comparisonQuery_index hi hj]

theorem compare_history_correct {n i j : ℕ} {V : List Plane}
    {answer : Query → Bool} (hanswer : CorrectOracle V answer)
    (hi : i < n) (hj : j < n) (vertical : Bool) :
    compare n (comparisonHistory n answer) vertical i j = true ↔
      coordinate (axis vertical) (V.getD i 0) ≤
        coordinate (axis vertical) (V.getD j 0) := by
  rw [compare_history hi hj]
  simpa only [coordinateSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero] using hanswer (axis vertical) [i] [j]

private theorem axis_primrec : Primrec axis := by
  exact Primrec.dom_bool _

theorem comparisonIndex_primrec :
    Primrec (fun x : ℕ × Bool × ℕ × ℕ =>
      comparisonIndex x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Primrec.cond (Primrec.fst.comp Primrec.snd) (Primrec.const 1) (Primrec.const 0))

theorem comparisonQuery_primrec : Primrec₂ comparisonQuery := by
  have hhalf : Primrec (fun x : ℕ × ℕ => x.2 / 2) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  exact Primrec.pair
    (axis_primrec.comp (Primrec.beq.comp
      (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)))
    (Primrec.pair
      (Primrec.list_cons.comp (Primrec.nat_div.comp hhalf Primrec.fst)
        (Primrec.const []))
      (Primrec.list_cons.comp (Primrec.nat_mod.comp hhalf Primrec.fst)
        (Primrec.const [])))

theorem comparisonQueries_primrec : Primrec comparisonQueries :=
  Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_mul.comp Primrec.id Primrec.id))) comparisonQuery_primrec

theorem compare_primrec :
    Primrec (fun x : (ℕ × List Bool) × Bool × ℕ × ℕ =>
      compare x.1.1 x.1.2 x.2.1 x.2.2.1 x.2.2.2) := by
  exact (Primrec.list_getD false).comp (Primrec.snd.comp Primrec.fst)
    (comparisonIndex_primrec.comp
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))

end Tiling.AxisParallel.Decidability.RectangleInput
