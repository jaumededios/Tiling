import Tiling.AxisParallel.Terminal.BoundaryCore
import Tiling.AxisParallel.Terminal.RationalSliceCore

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false

open Set

namespace Tiling.AxisParallel.Terminal

universe u

private theorem reflTransGen_symm_of_symmetric
    {α : Type u} {R : α → α → Prop}
    (hsymm : ∀ {x y}, R x y → R y x) {x y : α}
    (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact (Relation.ReflTransGen.single (hsymm hbc)).trans ih

private theorem eqvGen_iff_reflTransGen_of_symmetric
    {α : Type u} {R : α → α → Prop}
    (hsymm : ∀ {x y}, R x y → R y x) {x y : α} :
    Relation.EqvGen R x y ↔ Relation.ReflTransGen R x y := by
  constructor
  · intro h
    induction h with
    | rel x y hxy => exact Relation.ReflTransGen.single hxy
    | refl x => exact Relation.ReflTransGen.refl
    | symm _ _ _ ih => exact reflTransGen_symm_of_symmetric hsymm ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    induction h with
    | refl => exact Relation.EqvGen.refl _
    | tail hab hbc ih =>
        exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ hbc)

/-- A nonempty slice is non-gapped exactly when its strict-distance graph is linked.
No positivity assumption on `r` is needed: for `r ≤ 0`, both sides hold exactly for singletons. -/
theorem linked_iff_not_isGappedSlice {r : ℝ} {S : Set Tiling.Plane}
    (hS : S.Nonempty) : Linked r S ↔ ¬ IsGappedSlice r S := by
  let R : Tiling.Plane → Tiling.Plane → Prop :=
    fun a b ↦ a ∈ S ∧ b ∈ S ∧ dist a b < r
  have hsymm : ∀ {x y}, R x y → R y x := by
    rintro x y ⟨hx, hy, hxy⟩
    exact ⟨hy, hx, by simpa only [dist_comm] using hxy⟩
  rw [Linked, IsGappedSlice]
  constructor
  · rintro ⟨_, hlinked⟩ ⟨x, hx, y, hy, hnot⟩
    apply hnot
    exact (eqvGen_iff_reflTransGen_of_symmetric hsymm).2
      (hlinked x hx y hy)
  · intro hnot
    refine ⟨hS, fun x hx y hy ↦ ?_⟩
    apply (eqvGen_iff_reflTransGen_of_symmetric hsymm).1
    by_contra hxy
    exact hnot ⟨x, hx, y, hy, hxy⟩

/-- Membership in the no-gap phase family, together with the actual slice
nonemptiness supplied by the construction, yields literal graph linkedness. -/
theorem RationalSliceOrbit.linked_originalSlice_of_mem_noGapPhases
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {within transverse : RationalDirection}
    (O : RationalSliceOrbit K T within transverse)
    (originalSlice : RationalSlice within → Set Tiling.Plane)
    (hPreimageNonempty : ∀ Q, Q ∈ O.phases → (originalSlice Q).Nonempty)
    {r : ℝ} {Q : RationalSlice within}
    (hQ : Q ∈ O.noGapPhases originalSlice r) : Linked r (originalSlice Q) := by
  have hphase : Q ∈ O.phases := hQ.1
  have hnotGap : ¬IsGappedSlice r (originalSlice Q) := by
    intro hgap
    exact hQ.2 ⟨hphase, hgap⟩
  exact (linked_iff_not_isGappedSlice (hPreimageNonempty Q hphase)).2 hnotGap

end Tiling.AxisParallel.Terminal
