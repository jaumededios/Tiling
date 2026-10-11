import Tiling.AxisParallel.Decidability.RectangleInput.LocalBound

set_option autoImplicit false

open scoped BigOperators

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput.LocalBound

open Tiling.AxisParallel.Terminal.Executable

def pairCoeff (C : RegionCode) (p : ℕ × ℕ) : Coeff C := fun i =>
  (bif i.val == p.1 then (1 : ℤ) else 0) - (bif i.val == p.2 then (1 : ℤ) else 0)

theorem pairCoeff_zero (C : RegionCode) : pairCoeff C (0, 0) = Coeff.zero C := by
  funext i
  simp [pairCoeff, Coeff.zero]

theorem pairCoeff_eq_sub_single (C : RegionCode) {p : ℕ × ℕ}
    (hp : p.1 < C.vertexCount ∧ p.2 < C.vertexCount) :
    pairCoeff C p = Coeff.sub (Coeff.single ⟨p.1, hp.1⟩ 1) (Coeff.single ⟨p.2, hp.2⟩ 1) := by
  funext i
  by_cases h₁ : i.val = p.1 <;> by_cases h₂ : i.val = p.2 <;>
    simp [pairCoeff, Coeff.sub, Coeff.single, Fin.ext_iff, h₁, h₂, beq_iff_eq, Bool.cond_eq_ite]

theorem evalCoeff_pair {C : RegionCode} (R : Realization C) (s : CoordSort)
    {p : ℕ × ℕ} (hp : p.1 < C.vertexCount ∧ p.2 < C.vertexCount) :
    evalCoeff R s (pairCoeff C p) =
      s.axis.coord (R.vertex ⟨p.1, hp.1⟩) - s.axis.coord (R.vertex ⟨p.2, hp.2⟩) := by
  rw [pairCoeff_eq_sub_single C hp]
  simp only [evalCoeff, Coeff.sub, Int.cast_sub, sub_mul, Finset.sum_sub_distrib,
    Coeff.single, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
  simp

theorem table_correct {corners : List Plane}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle corners answer) {P : PackedRegion}
    {vertical : Bool} {a b : ℕ × ℕ}
    (ha : a.1 < P.1.length ∧ a.2 < P.1.length)
    (hb : b.1 < P.1.length ∧ b.2 < P.1.length) :
    table P.1.length (history P answer) vertical a b = true ↔
      coordinate (axis vertical) (pointValue corners (P.1.getD a.1 (0, 0))) -
          coordinate (axis vertical) (pointValue corners (P.1.getD a.2 (0, 0))) ≤
        coordinate (axis vertical) (pointValue corners (P.1.getD b.1 (0, 0))) -
          coordinate (axis vertical) (pointValue corners (P.1.getD b.2 (0, 0))) := by
  rw [table_history ha hb]
  change answer (axis vertical, _, _) = true ↔ _
  rw [hanswer]
  simp only [coordinateSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero]
  cases vertical <;> simp only [cornerLabel, coordinate, axis, pointValue,
    Bool.cond_false, Bool.cond_true, Bool.false_eq_true, ↓reduceIte,
    show (1 : Fin 2) ≠ 0 by decide]
  all_goals constructor <;> intro h <;> linarith

theorem table_matches_oracle {R : List (Plane × Plane)} {Ω : Set Plane}
    {gridHistory : List Bool} {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (hgrid : TableCorrect (cornerList R) gridHistory)
    (hinput : 0 < (vertexLabels (R.length, gridHistory)).length)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer)
    (s : CoordSort) {a b : ℕ × ℕ}
    (ha : a.1 < (vertexLabels (R.length, gridHistory)).length ∧
      a.2 < (vertexLabels (R.length, gridHistory)).length)
    (hb : b.1 < (vertexLabels (R.length, gridHistory)).length ∧
      b.2 < (vertexLabels (R.length, gridHistory)).length) :
    table (vertexLabels (R.length, gridHistory)).length
      (history (packedRegion (R.length, gridHistory)) answer) (sortBool s) a b =
      (oracle hR hgrid hinput hanswer).answer
        ⟨s, pairCoeff (inputCode (R.length, gridHistory) hinput) a,
          pairCoeff (inputCode (R.length, gridHistory) hinput) b⟩ := by
  apply Bool.eq_iff_iff.mpr
  change table (packedRegion (R.length, gridHistory)).1.length
    (history (packedRegion (R.length, gridHistory)) answer) (sortBool s) a b = true ↔ _
  rw [table_correct hanswer ha hb, (oracle hR hgrid hinput hanswer).correct,
    evalCoeff_pair _ s ha, evalCoeff_pair _ s hb]
  simp only [coordinate_sortBool, realization, normalizedVertex, originalVertex, packedRegion]
  cases s <;> simp only [CoordSort.axis, Tiling.AxisParallel.Axis.coord,
    Complex.sub_re, Complex.sub_im]
  all_goals constructor <;> intro h <;> linarith

theorem mem_differenceCandidates {n : ℕ} {p : ℕ × ℕ} :
    p ∈ differenceCandidates n ↔ p.1 < n ∧ p.2 < n := by
  rcases p with ⟨i, j⟩
  simp [differenceCandidates, mem_pairs, and_comm]
  aesop

theorem map_range_eq_ofFn {α : Type*} (f : ℕ → α) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem differenceCoeff_eq_ofFn_pairCoeff (C : RegionCode) (p : ℕ × ℕ) :
    differenceCoeff C.vertexCount p = List.ofFn (pairCoeff C p) :=
  map_range_eq_ofFn _ _

theorem diameterCandidates_eq_map (C : RegionCode) :
    LocalCoverSearch.diameterCandidates C =
      (differenceCandidates C.vertexCount).map (pairCoeff C) := by
  have hrange : List.range C.vertexCount = List.ofFn (fun i : Fin C.vertexCount => i.val) :=
    by simpa using map_range_eq_ofFn id C.vertexCount
  simp only [LocalCoverSearch.diameterCandidates, differenceCandidates, pairs, hrange,
    List.flatMap, List.map_flatten, List.map_ofFn]
  congr 1
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply, List.map_cons, List.map_nil]
  rw [pairCoeff_eq_sub_single C ⟨i.isLt, j.isLt⟩,
    pairCoeff_eq_sub_single C ⟨j.isLt, i.isLt⟩]

theorem fold_pairCoeff {R : List (Plane × Plane)} {Ω : Set Plane}
    {gridHistory : List Bool} {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (hgrid : TableCorrect (cornerList R) gridHistory)
    (hinput : 0 < (vertexLabels (R.length, gridHistory)).length)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer)
    (s : CoordSort) (xs : List (ℕ × ℕ))
    (hxs : ∀ p ∈ xs, p.1 < (vertexLabels (R.length, gridHistory)).length ∧
      p.2 < (vertexLabels (R.length, gridHistory)).length)
    (a : ℕ × ℕ)
    (ha : a.1 < (vertexLabels (R.length, gridHistory)).length ∧
      a.2 < (vertexLabels (R.length, gridHistory)).length) :
    pairCoeff (inputCode (R.length, gridHistory) hinput)
      (xs.foldl (fun a b => bif table (vertexLabels (R.length, gridHistory)).length
        (history (packedRegion (R.length, gridHistory)) answer) (sortBool s) a b
        then b else a) a) =
    (xs.map (pairCoeff (inputCode (R.length, gridHistory) hinput))).foldl
      (LocalCoverSearch.chooseLargerCoeff (oracle hR hgrid hinput hanswer).toOracle s)
      (pairCoeff (inputCode (R.length, gridHistory) hinput) a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b xs ih =>
    have hb := hxs b (by simp)
    have htail : ∀ p ∈ xs, p.1 < (vertexLabels (R.length, gridHistory)).length ∧
        p.2 < (vertexLabels (R.length, gridHistory)).length :=
      fun p hp => hxs p (by simp [hp])
    simp only [List.foldl_cons, List.map_cons, LocalCoverSearch.chooseLargerCoeff]
    rw [table_matches_oracle hR hgrid hinput hanswer s ha hb]
    cases hresp : (oracle hR hgrid hinput hanswer).answer
        ⟨s, pairCoeff (inputCode (R.length, gridHistory) hinput) a,
          pairCoeff (inputCode (R.length, gridHistory) hinput) b⟩
    · simpa only [hresp, Bool.cond_false, Bool.false_eq_true, ↓reduceIte] using ih htail a ha
    · simpa only [hresp, Bool.cond_true, ↓reduceIte] using ih htail b hb

theorem maximumPair_eq_native {R : List (Plane × Plane)} {Ω : Set Plane}
    {gridHistory : List Bool} {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (hgrid : TableCorrect (cornerList R) gridHistory)
    (hinput : 0 < (vertexLabels (R.length, gridHistory)).length)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer)
    (s : CoordSort) :
    pairCoeff (inputCode (R.length, gridHistory) hinput)
      (maximumPair (vertexLabels (R.length, gridHistory)).length
        (history (packedRegion (R.length, gridHistory)) answer) (sortBool s)) =
      LocalCoverSearch.maxCoeffList (oracle hR hgrid hinput hanswer).toOracle s
        (LocalCoverSearch.diameterCandidates (inputCode (R.length, gridHistory) hinput)) := by
  rw [maximumPair, LocalCoverSearch.maxCoeffList, diameterCandidates_eq_map]
  rw [← pairCoeff_zero]
  exact fold_pairCoeff hR hgrid hinput hanswer s _
    (fun p hp => mem_differenceCandidates.mp hp) (0, 0) ⟨hinput, hinput⟩

def encodeNativeBound {C : RegionCode} (B : LocalCoverSearch.LocalBoundCode C) : Bounds :=
  (List.ofFn B.horizontalDiameter, List.ofFn B.verticalDiameter,
    List.ofFn B.horizontalWidth, List.ofFn B.verticalWidth)

theorem horizontalWidth_eq {P : PackedRegion} (hP : 0 < P.1.length)
    (hc : 0 < P.2.length) :
    differenceCoeff P.1.length
      ((P.2.getD 0 (0, 0)).1.2 % P.1.length,
        (P.2.getD 0 (0, 0)).1.1 % P.1.length) =
    List.ofFn (Coeff.sub (Coeff.cellRight (C := regionCode P hP) ⟨0, hc⟩)
      (Coeff.cellLeft ⟨0, hc⟩)) := by
  exact (differenceCoeff_eq_ofFn_pairCoeff (regionCode P hP) _).trans
    (congrArg List.ofFn (pairCoeff_eq_sub_single (regionCode P hP)
      ⟨Nat.mod_lt _ hP, Nat.mod_lt _ hP⟩))

theorem verticalWidth_eq {P : PackedRegion} (hP : 0 < P.1.length)
    (hc : 0 < P.2.length) :
    differenceCoeff P.1.length
      ((P.2.getD 0 (0, 0)).2.2 % P.1.length,
        (P.2.getD 0 (0, 0)).2.1 % P.1.length) =
    List.ofFn (Coeff.sub (Coeff.cellTop (C := regionCode P hP) ⟨0, hc⟩)
      (Coeff.cellBottom ⟨0, hc⟩)) := by
  exact (differenceCoeff_eq_ofFn_pairCoeff (regionCode P hP) _).trans
    (congrArg List.ofFn (pairCoeff_eq_sub_single (regionCode P hP)
      ⟨Nat.mod_lt _ hP, Nat.mod_lt _ hP⟩))

theorem build_eq_native {R : List (Plane × Plane)} {Ω : Set Plane}
    {gridHistory : List Bool} {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : Tiling.AxisParallel.SetFormulation.RectanglePresentation R Ω)
    (hgrid : TableCorrect (cornerList R) gridHistory)
    (hinput : 0 < (vertexLabels (R.length, gridHistory)).length)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer) :
    build (packedRegion (R.length, gridHistory))
        (history (packedRegion (R.length, gridHistory)) answer) =
      (LocalCoverSearch.buildLocalBound (inputCode (R.length, gridHistory) hinput)
        (oracle hR hgrid hinput hanswer).toOracle).map encodeNativeBound := by
  have hc : 0 < (packedRegion (R.length, gridHistory)).2.length := by
    simpa only [packedRegion, List.length_map] using coarseCells_nonempty hR hgrid
  have hn : 0 < (inputCode (R.length, gridHistory) hinput).cellCount := hc
  simp only [build, if_pos hc, LocalCoverSearch.buildLocalBound, dif_pos hn,
    Option.map_some, encodeNativeBound]
  apply congrArg some
  apply Prod.ext
  · exact (differenceCoeff_eq_ofFn_pairCoeff (inputCode (R.length, gridHistory) hinput)
      _).trans (congrArg List.ofFn (maximumPair_eq_native hR hgrid hinput hanswer .horizontal))
  · apply Prod.ext
    · exact (differenceCoeff_eq_ofFn_pairCoeff (inputCode (R.length, gridHistory) hinput)
        _).trans (congrArg List.ofFn (maximumPair_eq_native hR hgrid hinput hanswer .vertical))
    · exact Prod.ext (horizontalWidth_eq hinput hc) (verticalWidth_eq hinput hc)

end Tiling.AxisParallel.Decidability.RectangleInput.LocalBound
