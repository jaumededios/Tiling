import Tiling.AxisParallel.Decidability.RectangleInput.Geometry

/-!
# Nonemptiness of finite rectangle inputs

A finite union has nonempty interior exactly when one rectangle has two positive
side lengths. A coordinate comparison oracle checks those strict inequalities.
-/

set_option autoImplicit false
set_option warningAsError true

open Set Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput.Validity

private def rectangleUnion (R : List (Plane × Plane)) : Set Plane :=
  ⋃ r ∈ R, rectangle r.1 r.2

private theorem rectangleUnion_cons (r : Plane × Plane) (R : List (Plane × Plane)) :
    rectangleUnion (r :: R) = rectangle r.1 r.2 ∪ rectangleUnion R := by
  simp [rectangleUnion]

private theorem rectangle_isClosed (a b : Plane) : IsClosed (rectangle a b) :=
  (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

private theorem rectangleUnion_isClosed (R : List (Plane × Plane)) :
    IsClosed (rectangleUnion R) := by
  induction R with
  | nil => simp [rectangleUnion]
  | cons r R ih => rw [rectangleUnion_cons]; exact (rectangle_isClosed r.1 r.2).union ih

theorem interior_rectangle_nonempty (a b : Plane) :
    (interior (rectangle a b)).Nonempty ↔ p₁ a < p₁ b ∧ p₂ a < p₂ b := by
  change (interior (Tiling.AxisParallel.FiniteRectangles.box
    (a.re, b.re) (a.im, b.im))).Nonempty ↔ _
  rw [Tiling.AxisParallel.FiniteRectangles.interior_box]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨hz.1.1.trans hz.1.2, hz.2.1.trans hz.2.2⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨x, hax, hxb⟩ := exists_between hx
    obtain ⟨y, hay, hyb⟩ := exists_between hy
    exact ⟨⟨x, y⟩, ⟨hax, hxb⟩, hay, hyb⟩

theorem interior_rectangles_nonempty (R : List (Plane × Plane)) :
    (interior (⋃ r ∈ R, rectangle r.1 r.2)).Nonempty ↔
      ∃ r ∈ R, p₁ r.1 < p₁ r.2 ∧ p₂ r.1 < p₂ r.2 := by
  change (interior (rectangleUnion R)).Nonempty ↔ _
  induction R with
  | nil => simp [rectangleUnion]
  | cons r R ih =>
      rw [rectangleUnion_cons]
      by_cases hr : (interior (rectangle r.1 r.2)).Nonempty
      · have hleft : (interior (rectangle r.1 r.2 ∪ rectangleUnion R)).Nonempty :=
          hr.mono (interior_mono subset_union_left)
        have hright : ∃ s ∈ r :: R, p₁ s.1 < p₁ s.2 ∧ p₂ s.1 < p₂ s.2 :=
          ⟨r, List.mem_cons_self, (interior_rectangle_nonempty r.1 r.2).mp hr⟩
        exact iff_of_true hleft hright
      · have he : interior (rectangle r.1 r.2) = ∅ := Set.not_nonempty_iff_eq_empty.mp hr
        rw [union_comm, interior_union_isClosed_of_interior_empty
          (rectangleUnion_isClosed R) he, ih]
        have hn : ¬(p₁ r.1 < p₁ r.2 ∧ p₂ r.1 < p₂ r.2) :=
          mt (interior_rectangle_nonempty r.1 r.2).mpr hr
        simp only [List.mem_cons, exists_eq_or_imp, hn, false_or]

/-- The finite input contains a genuinely two-dimensional rectangle. -/
def properRectangle (answer : Query → Bool) (k : ℕ) : Bool :=
  !(answer (0, [2 * k + 1], [2 * k])) &&
    !(answer (1, [2 * k + 1], [2 * k]))

theorem properRectangle_correct {answer : Query → Bool} {R : List (Plane × Plane)}
    (hanswer : CorrectOracle (cornerList R) answer)
    {k : ℕ} (hk : k < R.length) :
    properRectangle answer k = true ↔
      p₁ (R.getD k (0, 0)).1 < p₁ (R.getD k (0, 0)).2 ∧
      p₂ (R.getD k (0, 0)).1 < p₂ (R.getD k (0, 0)).2 := by
  dsimp only [CorrectOracle] at hanswer
  simp only [properRectangle, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false,
    Bool.eq_false_iff, ne_eq, hanswer]
  simp only [coordinateSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, RectangleInput.cornerList_getD_left R hk,
    RectangleInput.cornerList_getD_right R hk, coordinate]
  simp


end Tiling.AxisParallel.Decidability.RectangleInput.Validity
