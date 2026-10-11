import Tiling.AxisParallel.SetFormulation.RegionBridge
import Tiling.AxisParallel.Foundations.IntrinsicBoundaryEdges
import Tiling.AxisParallel.Foundations.QuadrantGermGeometry

/-!
# Intrinsic rectangle vertices from local quadrant occupancy

For a finite rectangle presentation, each open quadrant next to a point is
occupied exactly when one presented rectangle reaches that quadrant. The
resulting Boolean pattern is an intrinsic vertex precisely when it changes
across both coordinate axes.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.SetFormulation

open Tiling.AxisParallel.Foundations

/-- The open quadrant described by its west/east and south/north sides. -/
def rectangleQuadrant (west south : Bool) : Quadrant :=
  match west, south with
  | true, true => .southwest
  | true, false => .northwest
  | false, true => .southeast
  | false, false => .northeast

/-- A rectangle reaches a specified local quadrant at `v`. -/
def rectangleReachesQuadrant (r : Plane × Plane) (v : Plane)
    (west south : Bool) : Prop :=
  (if west then r.1.re < v.re ∧ v.re ≤ r.2.re else r.1.re ≤ v.re ∧ v.re < r.2.re) ∧
  (if south then r.1.im < v.im ∧ v.im ≤ r.2.im else r.1.im ≤ v.im ∧ v.im < r.2.im)

/-- The finite rectangle union occupies a local quadrant iff one rectangle reaches it. -/
def quadrantOccupied (R : List (Plane × Plane)) (v : Plane)
    (west south : Bool) : Prop :=
  ∃ r ∈ R, rectangleReachesQuadrant r v west south

def quadrantDifferent (P Q : Prop) : Prop := (P ∧ ¬ Q) ∨ (¬ P ∧ Q)

def hasBothAxisQuadrantChanges (R : List (Plane × Plane)) (v : Plane) : Prop :=
  (quadrantDifferent (quadrantOccupied R v true false)
      (quadrantOccupied R v true true) ∨
    quadrantDifferent (quadrantOccupied R v false false)
      (quadrantOccupied R v false true)) ∧
  (quadrantDifferent (quadrantOccupied R v true false)
      (quadrantOccupied R v false false) ∨
    quadrantDifferent (quadrantOccupied R v true true)
      (quadrantOccupied R v false true))

def rectangleRealLevels (R : List (Plane × Plane)) : Finset ℝ := by
  classical
  exact (R.toFinset.image fun r => r.1.re) ∪ (R.toFinset.image fun r => r.2.re)

private def rectangleImagLevels (R : List (Plane × Plane)) : Finset ℝ := by
  classical
  exact (R.toFinset.image fun r => r.1.im) ∪ (R.toFinset.image fun r => r.2.im)

private theorem exists_radius_avoiding_levels (s : Finset ℝ) (x : ℝ) :
    ∃ ε > 0, ∀ y ∈ s, dist y x < ε → y = x := by
  classical
  let t := s.erase x
  have hx : x ∈ ((t : Finset ℝ) : Set ℝ)ᶜ := by simp [t]
  have hopen : IsOpen (((t : Finset ℝ) : Set ℝ)ᶜ) :=
    t.finite_toSet.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
  refine ⟨ε, hε, ?_⟩
  intro y hy hdist
  by_contra hyx
  have hyt : y ∈ t := Finset.mem_erase.mpr ⟨hyx, hy⟩
  exact hball hdist hyt

private theorem dist_re_le_norm_sub (z v : Plane) :
    dist z.re v.re ≤ ‖z - v‖ := by
  rw [Real.dist_eq]
  calc
    |z.re - v.re| = |(z - v).re| := by simp
    _ ≤ ‖z - v‖ := Complex.abs_re_le_norm _

private theorem dist_im_le_norm_sub (z v : Plane) :
    dist z.im v.im ≤ ‖z - v‖ := by
  rw [Real.dist_eq]
  calc
    |z.im - v.im| = |(z - v).im| := by simp
    _ ≤ ‖z - v‖ := Complex.abs_im_le_norm _

private theorem no_level_strictly_between
    {s : Finset ℝ} {v z : ℝ} {ε : ℝ}
    (havoid : ∀ y ∈ s, dist y v < ε → y = v)
    (hz : dist z v < ε) (hneq : z ≠ v) :
    ∀ y ∈ s, ¬ (min z v < y ∧ y < max z v) := by
  intro y hy hybetween
  have hyDist : dist y v < ε := by
    rcases lt_or_gt_of_ne hneq with h | h
    · have hybetween' : z < y ∧ y < v := by
        simpa [min_eq_left h.le, max_eq_right h.le] using hybetween
      have hsmall : dist y v < dist z v := by
        rw [Real.dist_eq, Real.dist_eq,
          abs_of_nonpos (by linarith : y - v ≤ 0),
          abs_of_nonpos (by linarith : z - v ≤ 0)]
        linarith
      exact hsmall.trans hz
    · have hybetween' : v < y ∧ y < z := by
        simpa [min_eq_right h.le, max_eq_left h.le] using hybetween
      have hsmall : dist y v < dist z v := by
        rw [Real.dist_eq, Real.dist_eq,
          abs_of_nonneg (by linarith : 0 ≤ y - v),
          abs_of_nonneg (by linarith : 0 ≤ z - v)]
        linarith
      exact hsmall.trans hz
  have hEq := havoid y hy hyDist
  rcases lt_or_gt_of_ne hneq with h | h
  · have hybetween' : z < y ∧ y < v := by
      simpa [min_eq_left h.le, max_eq_right h.le] using hybetween
    linarith
  · have hybetween' : v < y ∧ y < z := by
      simpa [min_eq_right h.le, max_eq_left h.le] using hybetween
    linarith

private theorem closedInterval_reachesWest {x v lo hi : ℝ}
    (hxv : x < v) (hxhi : x ≠ hi)
    (hnoLo : ¬ (x < lo ∧ lo < v)) (hnoHi : ¬ (x < hi ∧ hi < v)) :
    (lo ≤ x ∧ x ≤ hi) ↔ (lo < v ∧ v ≤ hi) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨lt_of_le_of_lt hlo hxv, ?_⟩
    by_contra hnot
    have hvhi : hi < v := lt_of_not_ge hnot
    exact hnoHi ⟨lt_of_le_of_ne hhi hxhi, hvhi⟩
  · rintro ⟨hlov, hvhi⟩
    refine ⟨?_, le_trans hxv.le hvhi⟩
    by_contra hnot
    have hxlo' : x < lo := lt_of_not_ge hnot
    exact hnoLo ⟨hxlo', hlov⟩

private theorem closedInterval_reachesEast {x v lo hi : ℝ}
    (hvx : v < x) (hxlo : x ≠ lo)
    (hnoLo : ¬ (v < lo ∧ lo < x)) (hnoHi : ¬ (v < hi ∧ hi < x)) :
    (lo ≤ x ∧ x ≤ hi) ↔ (lo ≤ v ∧ v < hi) := by
  constructor
  · rintro ⟨hlo, hhi⟩
    refine ⟨?_, lt_of_lt_of_le hvx hhi⟩
    by_contra hnot
    have hvlo : v < lo := lt_of_not_ge hnot
    exact hnoLo ⟨hvlo, lt_of_le_of_ne hlo (Ne.symm hxlo)⟩
  · rintro ⟨hlov, hvhi⟩
    refine ⟨le_trans hlov hvx.le, ?_⟩
    by_contra hnot
    have hxhi' : hi < x := lt_of_not_ge hnot
    exact hnoHi ⟨hvhi, hxhi'⟩
private theorem rectangle_mem_iff_quadrantOccupied_local
    {R : List (Plane × Plane)} {Ω : Set Plane} (hR : RectanglePresentation R Ω)
    (v z : Plane) (west south : Bool) {ε : ℝ}
    (havoidRe : ∀ y ∈ rectangleRealLevels R, dist y v.re < ε → y = v.re)
    (havoidIm : ∀ y ∈ rectangleImagLevels R, dist y v.im < ε → y = v.im)
    (hzball : z ∈ Metric.ball v ε)
    (hzquad : z ∈ quadrantAt (rectangleQuadrant west south) v) :
    z ∈ Ω ↔ quadrantOccupied R v west south := by
  classical
  have hnorm : ‖z - v‖ < ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hdistRe : dist z.re v.re < ε := (dist_re_le_norm_sub z v).trans_lt hnorm
  have hdistIm : dist z.im v.im < ε := (dist_im_le_norm_sub z v).trans_lt hnorm
  have hzReNe : z.re ≠ v.re := by
    intro h
    have hz := hzquad
    cases west <;> cases south <;>
      simp [rectangleQuadrant, quadrantAt, h] at hz
  have hzImNe : z.im ≠ v.im := by
    intro h
    have hz := hzquad
    cases west <;> cases south <;>
      simp [rectangleQuadrant, quadrantAt, h] at hz
  have hNoRe := no_level_strictly_between havoidRe hdistRe hzReNe
  have hNoIm := no_level_strictly_between havoidIm hdistIm hzImNe
  have hzSides :
      (if west then z.re < v.re else v.re < z.re) ∧
      (if south then z.im < v.im else v.im < z.im) := by
    cases west <;> cases south <;>
      simpa [rectangleQuadrant, quadrantAt] using hzquad
  have hcoordinate : ∀ r : Plane × Plane, r ∈ R →
      (z ∈ rectangle r.1 r.2 ↔ rectangleReachesQuadrant r v west south) := by
    intro r hr
    have hlevelsA : r.1.re ∈ rectangleRealLevels R := by
      change r.1.re ∈ (R.toFinset.image (fun q => q.1.re)) ∪ _
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsB : r.2.re ∈ rectangleRealLevels R := by
      change r.2.re ∈ _ ∪ (R.toFinset.image (fun q => q.2.re))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsC : r.1.im ∈ rectangleImagLevels R := by
      change r.1.im ∈ (R.toFinset.image (fun q => q.1.im)) ∪ _
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsD : r.2.im ∈ rectangleImagLevels R := by
      change r.2.im ∈ _ ∪ (R.toFinset.image (fun q => q.2.im))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hneqA : z.re ≠ r.1.re := by
      intro heq
      have hclose := havoidRe r.1.re hlevelsA (by simpa [heq] using hdistRe)
      exact hzReNe (heq.trans hclose)
    have hneqB : z.re ≠ r.2.re := by
      intro heq
      have hclose := havoidRe r.2.re hlevelsB (by simpa [heq] using hdistRe)
      exact hzReNe (heq.trans hclose)
    have hneqC : z.im ≠ r.1.im := by
      intro heq
      have hclose := havoidIm r.1.im hlevelsC (by simpa [heq] using hdistIm)
      exact hzImNe (heq.trans hclose)
    have hneqD : z.im ≠ r.2.im := by
      intro heq
      have hclose := havoidIm r.2.im hlevelsD (by simpa [heq] using hdistIm)
      exact hzImNe (heq.trans hclose)
    have hnoA : ¬ (if west then z.re < r.1.re ∧ r.1.re < v.re
        else v.re < r.1.re ∧ r.1.re < z.re) := by
      cases west
      · simpa [min_eq_right hzSides.1.le, max_eq_left hzSides.1.le] using
          hNoRe r.1.re hlevelsA
      · simpa [min_eq_left hzSides.1.le, max_eq_right hzSides.1.le] using
          hNoRe r.1.re hlevelsA
    have hnoB : ¬ (if west then z.re < r.2.re ∧ r.2.re < v.re
        else v.re < r.2.re ∧ r.2.re < z.re) := by
      cases west
      · simpa [min_eq_right hzSides.1.le, max_eq_left hzSides.1.le] using
          hNoRe r.2.re hlevelsB
      · simpa [min_eq_left hzSides.1.le, max_eq_right hzSides.1.le] using
          hNoRe r.2.re hlevelsB
    have hnoC : ¬ (if south then z.im < r.1.im ∧ r.1.im < v.im
        else v.im < r.1.im ∧ r.1.im < z.im) := by
      cases south
      · simpa [min_eq_right hzSides.2.le, max_eq_left hzSides.2.le] using
          hNoIm r.1.im hlevelsC
      · simpa [min_eq_left hzSides.2.le, max_eq_right hzSides.2.le] using
          hNoIm r.1.im hlevelsC
    have hnoD : ¬ (if south then z.im < r.2.im ∧ r.2.im < v.im
        else v.im < r.2.im ∧ r.2.im < z.im) := by
      cases south
      · simpa [min_eq_right hzSides.2.le, max_eq_left hzSides.2.le] using
          hNoIm r.2.im hlevelsD
      · simpa [min_eq_left hzSides.2.le, max_eq_right hzSides.2.le] using
          hNoIm r.2.im hlevelsD
    have hRe : z.re ∈ Set.Icc r.1.re r.2.re ↔
        (if west then r.1.re < v.re ∧ v.re ≤ r.2.re
          else r.1.re ≤ v.re ∧ v.re < r.2.re) := by
      cases west
      · simpa using closedInterval_reachesEast hzSides.1 hneqA hnoA hnoB
      · simpa using closedInterval_reachesWest hzSides.1 hneqB hnoA hnoB
    have hIm : z.im ∈ Set.Icc r.1.im r.2.im ↔
        (if south then r.1.im < v.im ∧ v.im ≤ r.2.im
          else r.1.im ≤ v.im ∧ v.im < r.2.im) := by
      cases south
      · simpa using closedInterval_reachesEast hzSides.2 hneqC hnoC hnoD
      · simpa using closedInterval_reachesWest hzSides.2 hneqD hnoC hnoD
    have hcoordRect : z ∈ rectangle r.1 r.2 ↔
        z.re ∈ Set.Icc r.1.re r.2.re ∧ z.im ∈ Set.Icc r.1.im r.2.im := by
      simp [rectangle, p₁, p₂]
    rw [hcoordRect, hRe, hIm]
    rfl
  constructor
  · intro hzΩ
    rw [hR.2] at hzΩ
    have hzu : z ∈ ⋃ r ∈ R, rectangle r.1 r.2 := interior_subset hzΩ
    obtain ⟨r, hr⟩ := mem_iUnion.mp hzu
    obtain ⟨hr, hzrect⟩ := mem_iUnion.mp hr
    exact ⟨r, hr, (hcoordinate r hr).mp hzrect⟩
  · rintro ⟨r, hr, hreach⟩
    rw [hR.2]
    have hzrect : z ∈ rectangle r.1 r.2 := (hcoordinate r hr).mpr hreach
    have hcoordRect : z ∈ rectangle r.1 r.2 ↔
        z.re ∈ Set.Icc r.1.re r.2.re ∧ z.im ∈ Set.Icc r.1.im r.2.im := by
      simp [rectangle, p₁, p₂]
    have hlevelsA : r.1.re ∈ rectangleRealLevels R := by
      change r.1.re ∈ (R.toFinset.image (fun q => q.1.re)) ∪ _
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsB : r.2.re ∈ rectangleRealLevels R := by
      change r.2.re ∈ _ ∪ (R.toFinset.image (fun q => q.2.re))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsC : r.1.im ∈ rectangleImagLevels R := by
      change r.1.im ∈ (R.toFinset.image (fun q => q.1.im)) ∪ _
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hlevelsD : r.2.im ∈ rectangleImagLevels R := by
      change r.2.im ∈ _ ∪ (R.toFinset.image (fun q => q.2.im))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    have hneqA : z.re ≠ r.1.re := by
      intro heq
      have hclose := havoidRe r.1.re hlevelsA (by simpa [heq] using hdistRe)
      exact hzReNe (heq.trans hclose)
    have hneqB : z.re ≠ r.2.re := by
      intro heq
      have hclose := havoidRe r.2.re hlevelsB (by simpa [heq] using hdistRe)
      exact hzReNe (heq.trans hclose)
    have hneqC : z.im ≠ r.1.im := by
      intro heq
      have hclose := havoidIm r.1.im hlevelsC (by simpa [heq] using hdistIm)
      exact hzImNe (heq.trans hclose)
    have hneqD : z.im ≠ r.2.im := by
      intro heq
      have hclose := havoidIm r.2.im hlevelsD (by simpa [heq] using hdistIm)
      exact hzImNe (heq.trans hclose)
    have hinterior : z ∈ interior (rectangle r.1 r.2) := by
      have hstrict : z.re ∈ Set.Ioo r.1.re r.2.re ∧ z.im ∈ Set.Ioo r.1.im r.2.im := by
        have hclosed' : z.re ∈ Set.Icc r.1.re r.2.re ∧
            z.im ∈ Set.Icc r.1.im r.2.im := hcoordRect.mp hzrect
        rcases hclosed' with ⟨⟨hxl, hxu⟩, ⟨hyl, hyu⟩⟩
        refine ⟨?_, ?_⟩ <;> simp only [Set.mem_Ioo]
        · exact ⟨lt_of_le_of_ne hxl (Ne.symm hneqA), lt_of_le_of_ne hxu hneqB⟩
        · exact ⟨lt_of_le_of_ne hyl (Ne.symm hneqC), lt_of_le_of_ne hyu hneqD⟩
      change z ∈ interior
        (Tiling.AxisParallel.FiniteRectangles.box (r.1.re, r.2.re) (r.1.im, r.2.im))
      rw [Tiling.AxisParallel.FiniteRectangles.interior_box]
      change z.re ∈ Set.Ioo r.1.re r.2.re ∧ z.im ∈ Set.Ioo r.1.im r.2.im
      exact hstrict
    have hsub : rectangle r.1 r.2 ⊆ ⋃ q ∈ R, rectangle q.1 q.2 := by
      intro x hx
      exact mem_iUnion.mpr ⟨r, mem_iUnion.mpr ⟨hr, hx⟩⟩
    exact interior_mono hsub hinterior

/-- The endpoint inequalities for one rectangle are exactly its quadrant germ. -/
theorem quadrantOccupied_iff_setOccupiesQuadrant
    {R : List (Plane × Plane)} {Ω : Set Plane} (hR : RectanglePresentation R Ω)
    (v : Plane) (west south : Bool) :
    quadrantOccupied R v west south ↔
      SetOccupiesQuadrant Ω v (rectangleQuadrant west south) := by
  classical
  obtain ⟨εre, hεre, havoidRe⟩ :=
    exists_radius_avoiding_levels (rectangleRealLevels R) v.re
  obtain ⟨εim, hεim, havoidIm⟩ :=
    exists_radius_avoiding_levels (rectangleImagLevels R) v.im
  let ε := min εre εim
  have hε : 0 < ε := lt_min hεre hεim
  have havoidRe' : ∀ y ∈ rectangleRealLevels R, dist y v.re < ε → y = v.re := by
    intro y hy hyε
    exact havoidRe y hy (hyε.trans_le (min_le_left _ _))
  have havoidIm' : ∀ y ∈ rectangleImagLevels R, dist y v.im < ε → y = v.im := by
    intro y hy hyε
    exact havoidIm y hy (hyε.trans_le (min_le_right _ _))
  constructor
  · rintro ⟨r, hr, hreach⟩
    refine ⟨ε, hε, ?_⟩
    rintro z ⟨hzball, hzquad⟩
    exact (rectangle_mem_iff_quadrantOccupied_local hR v z west south
      havoidRe' havoidIm' hzball hzquad).2 ⟨r, hr, hreach⟩
  · intro hocc
    by_contra hnot
    have hnot' : ¬ quadrantOccupied R v west south := hnot
    obtain ⟨ρ, hρ, hlocal⟩ := hocc
    let ρ' := min ρ ε
    have hρ' : 0 < ρ' := lt_min hρ hε
    obtain ⟨z, hzρ⟩ := quadrant_ball_nonempty hρ' (rectangleQuadrant west south)
    have hzball : z ∈ Metric.ball v ε :=
      Metric.ball_subset_ball (min_le_right ρ ε) hzρ.1
    have hzquad : z ∈ quadrantAt (rectangleQuadrant west south) v := hzρ.2
    have hzΩ : z ∈ Ω := hlocal ⟨Metric.ball_subset_ball (min_le_left ρ ε) hzρ.1,
      hzquad⟩
    exact hnot' ((rectangle_mem_iff_quadrantOccupied_local hR v z west south
      havoidRe' havoidIm' hzball hzquad).mp hzΩ)

private theorem different_iff_bool_ne {P Q : Prop} {a b : Bool}
    (hP : P ↔ a = true) (hQ : Q ↔ b = true) :
    quadrantDifferent P Q ↔ a ≠ b := by
  cases a <;> cases b <;> simp [quadrantDifferent, hP, hQ]

private theorem nonstraightPattern_iff_both_axis_changes (p : QuadrantPattern) :
    nonstraightPattern p ↔
      (p .northwest ≠ p .southwest ∨ p .northeast ≠ p .southeast) ∧
        (p .northwest ≠ p .northeast ∨ p .southwest ≠ p .southeast) := by
  constructor
  · exact nonstraightPattern_has_both_axis_changes p
  · intro h
    by_contra hnon
    have hstraight : straightPattern p := by
      simpa [nonstraightPattern] using hnon
    rcases hstraight with ⟨hSWSE, hNWNE⟩ | ⟨hSWNW, hSENE⟩
    · rcases h.2 with hNWNE' | hSWSE'
      · exact hNWNE' hNWNE
      · exact hSWSE' hSWSE
    · rcases h.1 with hNWSW | hNES
      · exact hNWSW hSWNW.symm
      · exact hNES hSENE.symm

private theorem realizesRectangles_isAxisParallelTile
    {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) : IsRectangleTile Ω := by
  classical
  refine ⟨hR.1, R.toFinset, ?_⟩
  rw [hR.2]
  congr 1
  ext z
  simp [List.mem_toFinset]

private theorem finite_segments_locallyAxisParallelPolygonal
    {D : Set Plane}
    (E : Set (Plane × Plane)) (hE : E.Finite)
    (hshape : ∀ e ∈ E, e.1 ≠ e.2 ∧ (e.1.re = e.2.re ∨ e.1.im = e.2.im))
    (hfront : frontier D = ⋃ e ∈ E, segment ℝ e.1 e.2)
    (hopen : IsOpen D) (hregular : interior (closure D) = D) :
    Tiling.AxisParallel.IsLocallyAxisParallelPolygonal D := by
  classical
  let G : Set (Set Plane) := (fun e : Plane × Plane => segment ℝ e.1 e.2) '' E
  have hGfinite : G.Finite := hE.image _
  have hsegments : ∀ g ∈ G, ∃ a b : Plane,
      a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧ g = segment ℝ a b := by
    intro g hg
    obtain ⟨e, he, rfl⟩ := (Set.mem_image _ _ _).mp hg
    exact ⟨e.1, e.2, (hshape e he).1, (hshape e he).2, rfl⟩
  have hcover : frontier D = ⋃₀ G := by
    rw [hfront]
    ext z
    constructor
    · intro hz
      obtain ⟨e, hz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨he, hz⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_sUnion.mpr ⟨segment ℝ e.1 e.2,
        (Set.mem_image _ _ _).mpr ⟨e, he, rfl⟩, hz⟩
    · intro hz
      obtain ⟨g, hg, hzg⟩ := Set.mem_sUnion.mp hz
      obtain ⟨e, he, rfl⟩ := (Set.mem_image _ _ _).mp hg
      exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨he, hzg⟩⟩
  refine ⟨hopen, hregular, G, hsegments, hcover, ?_⟩
  intro Q _
  apply hGfinite.subset
  intro g hg
  exact hg.1

/-- A point is an intrinsic vertex exactly when the rectangle occupancy pattern changes
across both coordinate axes. -/
theorem mem_vertices_iff_quadrantChanges
    {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (v : Plane) :
    v ∈ vertices Ω ↔ hasBothAxisQuadrantChanges R v := by
  classical
  let hΩtile := realizesRectangles_isAxisParallelTile hR
  let K := regionOfTile Ω hΩtile
  let E := K.intrinsicBoundaryEdges
  have hE : E.Finite := K.intrinsicBoundaryEdges_finite
  have hshape : ∀ e ∈ E,
      e.1 ≠ e.2 ∧ (e.1.re = e.2.re ∨ e.1.im = e.2.im) :=
    fun e he => ⟨he.2.2.1, he.2.2.2.1⟩
  have hfront : frontier Ω = ⋃ e ∈ E, segment ℝ e.1 e.2 := by
    calc
      frontier Ω = frontier K.openCarrier := by simp [K, regionOfTile_openCarrier]
      _ = frontier K.support := K.frontier_openCarrier_eq_frontier_support
      _ = ⋃ e ∈ E, segment ℝ e.1 e.2 := K.frontier_eq_intrinsicBoundaryEdges
  have hpolygonal : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal Ω :=
    finite_segments_locallyAxisParallelPolygonal E hE hshape hfront
      hΩtile.isOpen hΩtile.isRegularOpen
  have hvertices : v ∈ vertices Ω ↔ Tiling.AxisParallel.IsProperVertex Ω v := by
    rw [vertices_eq_native Ω hΩtile]
    rw [Tiling.AxisParallel.IntrinsicVertices.region_vertices_eq_nonStraightBoundary K]
    simp [K, regionOfTile_openCarrier, Tiling.AxisParallel.IsProperVertex,
      Tiling.Polygonal.IsProperVertex]
  obtain ⟨ρ, hρ, p, hgerm, hoccupies⟩ :=
    exists_quadrantPattern_germ hΩtile.isOpen hΩtile.isRegularOpen hpolygonal v
  have hproper := properVertex_iff_nonstraightPattern
    hΩtile.isOpen hΩtile.isRegularOpen hρ p hgerm
  have hOcc (west south : Bool) :
      p (rectangleQuadrant west south) = true ↔ quadrantOccupied R v west south := by
    rw [hoccupies]
    exact (quadrantOccupied_iff_setOccupiesQuadrant hR v west south).symm
  have hchanges : hasBothAxisQuadrantChanges R v ↔
      (p .northwest ≠ p .southwest ∨ p .northeast ≠ p .southeast) ∧
        (p .northwest ≠ p .northeast ∨ p .southwest ≠ p .southeast) := by
    unfold hasBothAxisQuadrantChanges
    exact and_congr
      (or_congr
        (by simpa [rectangleQuadrant] using
          different_iff_bool_ne (hOcc true false).symm (hOcc true true).symm)
        (by simpa [rectangleQuadrant] using
          different_iff_bool_ne (hOcc false false).symm (hOcc false true).symm))
      (or_congr
        (by simpa [rectangleQuadrant] using
          different_iff_bool_ne (hOcc true false).symm (hOcc false false).symm)
        (by simpa [rectangleQuadrant] using
          different_iff_bool_ne (hOcc true true).symm (hOcc false true).symm))
  calc
    v ∈ vertices Ω ↔ Tiling.AxisParallel.IsProperVertex Ω v := hvertices
    _ ↔ nonstraightPattern p := hproper
    _ ↔ (p .northwest ≠ p .southwest ∨ p .northeast ≠ p .southeast) ∧
        (p .northwest ≠ p .northeast ∨ p .southwest ≠ p .southeast) :=
      nonstraightPattern_iff_both_axis_changes p
    _ ↔ hasBothAxisQuadrantChanges R v := hchanges.symm

/-- Every intrinsic vertex coordinate is a rectangle endpoint level. -/
theorem vertex_real_coordinate_mem_rectangleLevels
    {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) {v : Plane} (hv : v ∈ vertices Ω) :
    v.re ∈ rectangleRealLevels R := by
  classical
  rw [mem_vertices_iff_quadrantChanges hR] at hv
  by_contra hnot
  have hneqLo (r : Plane × Plane) (hr : r ∈ R) : r.1.re ≠ v.re := by
    intro heq
    have hmem : r.1.re ∈ rectangleRealLevels R := by
      change r.1.re ∈ (R.toFinset.image (fun q => q.1.re)) ∪ _
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    apply hnot
    rw [← heq]
    exact hmem
  have hneqHi (r : Plane × Plane) (hr : r ∈ R) : r.2.re ≠ v.re := by
    intro heq
    have hmem : r.2.re ∈ rectangleRealLevels R := by
      change r.2.re ∈ _ ∪ (R.toFinset.image (fun q => q.2.re))
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨r,
        List.mem_toFinset.mpr hr, rfl⟩)
    apply hnot
    rw [← heq]
    exact hmem
  have hsame (south : Bool) :
      quadrantOccupied R v true south = quadrantOccupied R v false south := by
    apply propext
    constructor
    · rintro ⟨r, hr, hreach⟩
      cases south <;> simp only [rectangleReachesQuadrant, Bool.false_eq_true,
        ↓reduceIte] at hreach ⊢
      · rcases hreach with ⟨⟨hlo, hhi⟩, hy⟩
        exact ⟨r, hr, ⟨⟨hlo.le, lt_of_le_of_ne hhi (hneqHi r hr).symm⟩, hy⟩⟩
      · rcases hreach with ⟨⟨hlo, hhi⟩, hy⟩
        exact ⟨r, hr, ⟨⟨hlo.le, lt_of_le_of_ne hhi (hneqHi r hr).symm⟩, hy⟩⟩
    · rintro ⟨r, hr, hreach⟩
      cases south <;> simp only [rectangleReachesQuadrant, Bool.false_eq_true,
        ↓reduceIte] at hreach ⊢
      · rcases hreach with ⟨⟨hlo, hhi⟩, hy⟩
        exact ⟨r, hr, ⟨⟨lt_of_le_of_ne hlo (hneqLo r hr), hhi.le⟩, hy⟩⟩
      · rcases hreach with ⟨⟨hlo, hhi⟩, hy⟩
        exact ⟨r, hr, ⟨⟨lt_of_le_of_ne hlo (hneqLo r hr), hhi.le⟩, hy⟩⟩
  have hNWNE : quadrantOccupied R v true false =
      quadrantOccupied R v false false := hsame false
  have hSWSE : quadrantOccupied R v true true =
      quadrantOccupied R v false true := hsame true
  rcases hv.2 with hNW | hSW
  · simp [quadrantDifferent, hNWNE] at hNW
  · simp [quadrantDifferent, hSWSE] at hSW

end Tiling.AxisParallel.SetFormulation
