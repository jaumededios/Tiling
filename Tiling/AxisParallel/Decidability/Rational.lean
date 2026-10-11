import Tiling.AxisParallel.Decidability.Uniform
import Tiling.AxisParallel.Decidability.RectangleInput.Validity
import Tiling.AxisParallel.Decidability.Oracle.Run
import Tiling.Computability.TotalSearch
import Tiling.Computability.Rational

/-! Exact rational coordinate oracles and a total decision for arbitrary finite
rectangle lists. Empty interiors are rejected before certificate search. -/

set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped Pointwise
open Tiling.AxisParallel.SetFormulation Tiling.Computability

namespace Tiling.AxisParallel.Decidability.RationalDecision

abbrev Point := ℚ × ℚ
abbrev Input := List (Point × Point)

def realPoint (p : Point) : Plane := ⟨p.1, p.2⟩
def rectangles (R : Input) : List (Plane × Plane) :=
  R.map fun r => (realPoint r.1, realPoint r.2)
def region (R : Input) : Set Plane :=
  interior (⋃ r ∈ R, rectangle (realPoint r.1) (realPoint r.2))
def corners (R : Input) : List Point := R.flatMap fun r => [r.1, r.2]
def coord (axis : Fin 2) (p : Point) : ℚ := if axis = 0 then p.1 else p.2
def sum (R : Input) (axis : Fin 2) (indices : List ℕ) : ℚ :=
  (indices.map fun i => coord axis ((corners R).getD i (0, 0))).sum
def answer (R : Input) (q : Query) : Bool := decide (sum R q.1 q.2.1 ≤ sum R q.1 q.2.2)
def valid (R : Input) : Bool :=
  R.foldr (fun r found => (decide (r.1.1 < r.2.1) && decide (r.1.2 < r.2.2)) || found) false

theorem region_eq (R : Input) :
    region R = interior (⋃ r ∈ rectangles R, rectangle r.1 r.2) := by
  unfold region
  congr 1
  ext z
  simp only [Set.mem_iUnion, rectangles, List.mem_map]
  constructor
  · rintro ⟨r, hr, hz⟩
    exact ⟨_, ⟨r, hr, rfl⟩, hz⟩
  · rintro ⟨r, ⟨s, hs, rfl⟩, hz⟩
    exact ⟨s, hs, hz⟩

theorem corners_real (R : Input) :
    cornerList (rectangles R) = (corners R).map realPoint := by
  induction R with
  | nil => simp [cornerList, rectangles, corners]
  | cons r R ih => simpa [cornerList, rectangles, corners] using ih

theorem coord_real (axis : Fin 2) (p : Point) :
    coordinate axis (realPoint p) = (coord axis p : ℝ) := by
  by_cases h : axis = 0 <;> simp [coordinate, coord, realPoint, p₁, p₂, h]

theorem sum_real (R : Input) (axis : Fin 2) (indices : List ℕ) :
    coordinateSum (cornerList (rectangles R)) axis indices = (sum R axis indices : ℝ) := by
  rw [coordinateSum, corners_real]
  simp only [sum, Rat.cast_list_sum, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  have hget : ((corners R).map realPoint).getD i 0 =
      realPoint ((corners R).getD i (0, 0)) := by
    have hz : realPoint (0, 0) = (0 : Plane) := by
      apply Complex.ext <;> simp [realPoint]
    rw [← hz, List.getD_map]
  rw [hget, coord_real]
  rfl

theorem answer_correct (R : Input) : CorrectOracle (cornerList (rectangles R)) (answer R) := by
  intro axis left right
  simp [answer, sum_real]

theorem valid_correct (R : Input) : valid R = true ↔ (region R).Nonempty := by
  rw [region_eq, RectangleInput.Validity.interior_rectangles_nonempty]
  have hf : valid R = true ↔ ∃ r ∈ R, r.1.1 < r.2.1 ∧ r.1.2 < r.2.2 := by
    induction R with
    | nil => simp [valid]
    | cons r R ih =>
        change ((decide (r.1.1 < r.2.1) && decide (r.1.2 < r.2.2)) || valid R) = true ↔ _
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih,
          List.mem_cons, exists_eq_or_imp]
  rw [hf]
  simp [rectangles, realPoint, p₁, p₂]

private theorem corners_computable : Computable corners := by
  have hf : Primrec₂ (fun _xs : Input => fun r : Point × Point => [r.1, r.2]) :=
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))).to₂
  exact (Primrec.list_flatMap Primrec.id hf).to_comp

private theorem coord_computable : Computable₂ coord := by
  exact (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const (0 : Fin 2)))
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp.to₂

private theorem queryList_computable :
    Computable (fun x : Input × (Fin 2 × List ℕ) =>
      x.2.2.map fun i => coord x.2.1 ((corners x.1).getD i (0, 0))) := by
  exact Tiling.Computability.List.map_computable 0
    (Computable.snd.comp Computable.snd)
    (coord_computable.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))
      ((Primrec.list_getD (0, 0)).to_comp.comp
        (corners_computable.comp (Computable.fst.comp Computable.fst)) Computable.snd)).to₂

private theorem sum_computable :
    Computable (fun x : Input × (Fin 2 × List ℕ) => sum x.1 x.2.1 x.2.2) := by
  have hs : Computable (fun xs : List ℚ => xs.sum) :=
    (Tiling.Computability.List.computable_list_foldr
      Tiling.Computability.Rational.rat_add_computable).comp Computable.id (Computable.const 0)
  exact hs.comp queryList_computable

theorem answer_computable : Computable₂ answer := by
  exact (Tiling.Computability.Rational.rat_le_computable.comp
    (sum_computable.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.fst.comp (Computable.snd.comp Computable.snd)))))
    (sum_computable.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair
        (Computable.snd.comp (Computable.snd.comp Computable.snd)))))).to₂

theorem valid_computable : Computable valid := by
  have hproper : Computable (fun r : Point × Point =>
      decide (r.1.1 < r.2.1) && decide (r.1.2 < r.2.2)) :=
    (Primrec.dom_bool₂ Bool.and).to_comp.comp
      (Tiling.Computability.Rational.rat_lt_computable.comp
        (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Tiling.Computability.Rational.rat_lt_computable.comp
        (Computable.snd.comp Computable.fst) (Computable.snd.comp Computable.snd))
  exact (Tiling.Computability.List.computable_list_foldr
    ((Primrec.dom_bool₂ Bool.or).to_comp.comp
      (hproper.comp Computable.fst) Computable.snd).to₂).comp
    Computable.id (Computable.const false)

def bounded (R : Input) (fuel : ℕ) : Option Bool :=
  run (uniformDecisionProgram R.length) (answer R) fuel []

theorem bounded_computable : Computable₂ bounded :=
  OracleRun.run_from_empty_computable
    (uniformDecisionProgram_computable.comp
      (Computable.list_length.comp Computable.fst) Computable.snd) answer_computable

theorem halts : BoundedSearchHalts valid bounded := by
  intro R hR
  have hp : RectanglePresentation (rectangles R) (region R) :=
    ⟨(valid_correct R).mp hR, region_eq R⟩
  obtain ⟨fuel, b, hb⟩ := (uniformDecisionProgram_correct hp (answer_correct R)).1
  refine ⟨fuel, b, ?_⟩
  simpa [bounded, rectangles] using hb

/-- The first successful bounded verdict, with `false` for empty interiors.
Its computability is certified by `decideTiling_computable`. -/
noncomputable def decideTiling : Input → Bool := totalSearch valid bounded halts

theorem decideTiling_computable : Computable decideTiling :=
  computable_totalSearch valid bounded valid_computable bounded_computable halts

theorem not_tiles_empty (T : Set Plane) : ¬ Tiles ∅ T := by
  intro h
  have hc := h.2.2
  have he : (univ : Set Plane) =ᵐ[volume] (∅ : Set Plane) := by
    simpa only [CoversExactly, Set.vadd_empty] using hc
  have hz : volume (univ : Set Plane) = 0 := by
    simpa using MeasureTheory.measure_congr he
  simp at hz

theorem decideTiling_correct (R : Input) :
    decideTiling R = true ↔ ∃ T, Tiles (region R) T := by
  by_cases hv : valid R = true
  · have hp : RectanglePresentation (rectangles R) (region R) :=
      ⟨(valid_correct R).mp hv, region_eq R⟩
    obtain ⟨fuel, hfuel⟩ := totalSearch_sound valid bounded halts R hv
    have hr : run (uniformDecisionProgram (rectangles R).length) (answer R) fuel [] =
        some (decideTiling R) := by
      simpa [bounded, rectangles, Option.mem_def, decideTiling] using hfuel
    exact (uniformDecisionProgram_correct hp (answer_correct R)).2 _ _ hr
  · have he : region R = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (mt (valid_correct R).mpr hv)
    simp [decideTiling, totalSearch, hv, he, not_tiles_empty]

/-- Tileability is a computable predicate on every rational rectangle list.
No orientation, nondegeneracy, or nonemptiness restriction is imposed. -/
theorem rational_tiling_computable :
    ComputablePred (fun R : List ((ℚ × ℚ) × (ℚ × ℚ)) =>
      ∃ T, Tiles (interior (⋃ r ∈ R,
        rectangle ⟨r.1.1, r.1.2⟩ ⟨r.2.1, r.2.2⟩)) T) := by
  have hc : ComputablePred (fun R : Input => decideTiling R = true) :=
    ((Primrec.eq.decide).to_comp.comp
      decideTiling_computable (Computable.const true)).computablePred
  exact hc.of_eq (fun R => by simpa [region, realPoint] using decideTiling_correct R)

end Tiling.AxisParallel.Decidability.RationalDecision
