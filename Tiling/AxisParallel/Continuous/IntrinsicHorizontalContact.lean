import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

/-!
# Intrinsic horizontal proper contact

This module characterizes horizontal proper contact using intrinsic horizontal
edges and the overlap of their translated coordinate intervals.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Pointwise Topology

namespace Tiling.AxisParallel.Continuous
open Tiling AxisParallel

private def IsIntrinsicHorizontalSide (K : Region) (v w : K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices

private def translatedHorizontalInterval (v w : Tiling.Plane)
    (s : Tiling.Plane) : Set ℝ :=
  Set.Ioo (min v.re w.re + s.re) (max v.re w.re + s.re)

private theorem mem_openSegment_sub_iff
    {a b t z : Tiling.Plane} :
    z ∈ openSegment ℝ (a - t) (b - t) ↔ z + t ∈ openSegment ℝ a b := by
  rw [show a = t +ᵥ (a - t) by simp [vadd_eq_add, sub_eq_add_neg],
    show b = t +ᵥ (b - t) by simp [vadd_eq_add, sub_eq_add_neg],
    ← vadd_openSegment ℝ]
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro h
  · simpa [add_assoc] using h
  · simpa [add_assoc] using h

theorem labelledSides_giveHorizontalProperContact
    {K : Region} {t s : Tiling.Plane}
    {a b a' b' : K.vertices}
    (_hab : a.1 ≠ b.1) (_habIm : a.1.im = b.1.im)
    (habEdge : openSegment ℝ a.1 b.1 ⊆ frontier K.support \ K.vertices)
    (_ha'b' : a'.1 ≠ b'.1) (_ha'b'Im : a'.1.im = b'.1.im)
    (ha'b'Edge : openSegment ℝ a'.1 b'.1 ⊆ frontier K.support \ K.vertices)
    (u v : Tiling.Plane) (huv : u ≠ v) (huvIm : u.im = v.im)
    (hoverlap : openSegment ℝ u v ⊆
      openSegment ℝ (a.1 + t) (b.1 + t) ∩
        openSegment ℝ (a'.1 + s) (b'.1 + s)) :
    HorizontalProperContact K t s := by
  refine ⟨u, v, huv, huvIm, fun z hz ↦ ?_⟩
  have hzBoth := hoverlap hz
  have hzFirst : z - t ∈ openSegment ℝ a.1 b.1 := by
    rw [show a.1 + t = t +ᵥ a.1 by simp [add_comm],
      show b.1 + t = t +ᵥ b.1 by simp [add_comm], ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.1
  have hzSecond : z - s ∈ openSegment ℝ a'.1 b'.1 := by
    rw [show a'.1 + s = s +ᵥ a'.1 by simp [add_comm],
      show b'.1 + s = s +ᵥ b'.1 by simp [add_comm], ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.2
  have hzFirstEdge := habEdge hzFirst
  have hzSecondEdge := ha'b'Edge hzSecond
  refine ⟨⟨by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hzFirstEdge.1,
    by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hzSecondEdge.1⟩, ?_⟩
  intro hzVertices
  rcases hzVertices with hzVertices | hzVertices
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
    exact hzFirstEdge.2 (by simpa [sub_eq_add_neg, add_comm] using hzVertices)
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
    exact hzSecondEdge.2 (by simpa [sub_eq_add_neg, add_comm] using hzVertices)

private theorem im_eq_of_mem_openSegment_horizontal
    {a b p : Tiling.Plane} (hab : a.im = b.im)
    (hp : p ∈ openSegment ℝ a b) : p.im = a.im := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem horizontal_point_mem_openSegment_iff
    {a b : Tiling.Plane} (_hab : a ≠ b) (hh : a.im = b.im) (x : ℝ) :
    ((x : ℂ) + a.im * Complex.I) ∈ openSegment ℝ a b ↔
      x ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor <;> rintro ⟨r, hr, h⟩
  · refine ⟨r, hr, ?_⟩
    simpa using congrArg Complex.re h
  · refine ⟨r, hr, ?_⟩
    apply Complex.ext
    · simpa using congrArg id h
    · simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        Complex.smul_im, smul_eq_mul]
      rw [hh]
      ring

private theorem re_mem_openSegment_of_mem
    {a b p : Tiling.Plane} (hp : p ∈ openSegment ℝ a b) :
    p.re ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image] at hp ⊢
  obtain ⟨r, hr, h⟩ := hp
  refine ⟨r, hr, ?_⟩
  simpa using congrArg Complex.re h




private theorem properContact_lower
    (K : Region) (s t : Tiling.Plane) :
    HorizontalProperContact K s t ↔
      ∃ v v' w w' : K.vertices,
        IsIntrinsicHorizontalSide K v v' ∧
        IsIntrinsicHorizontalSide K w w' ∧
        (v.1 + s).im = (w.1 + t).im ∧
        (Set.Ioo (min v.1.re v'.1.re + s.re)
            (max v.1.re v'.1.re + s.re) ∩
          Set.Ioo (min w.1.re w'.1.re + t.re)
            (max w.1.re w'.1.re + t.re)).Nonempty := by
  constructor
  · rintro ⟨c, d, hcd, hcdIm, hcontact⟩
    let p : Tiling.Plane := midpoint ℝ c d
    have hpCD : p ∈ openSegment ℝ c d := midpoint_mem_openSegment c d
    have hpContact := hcontact hpCD
    have hpSFrontier : p - s ∈ frontier K.support :=
      by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hpContact.1.1
    have hpSNotVertex : p - s ∉ K.vertices := by
      intro hpVertex
      apply hpContact.2
      left
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
    have hpTFrontier : p - t ∈ frontier K.support :=
      by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hpContact.1.2
    have hpTNotVertex : p - t ∉ K.vertices := by
      intro hpVertex
      apply hpContact.2
      right
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
    obtain ⟨axisS, v, v', hvv, hvvCoord, hpVV, hvvEdge⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
        K (p - s) hpSFrontier hpSNotVertex
    have hvvIm : v.1.im = v'.1.im := by
      cases axisS with
      | horizontal => exact hvvCoord
      | vertical =>
          exfalso
          apply hpSNotVertex
          exact K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
            (c := c - s) (d := d - s) (p := p - s)
            (v := v.1) (w := v'.1) (by intro h; exact hcd (sub_left_inj.mp h))
            (by simp only [Complex.sub_im]; linarith)
            (by
              intro z hz
              have hzPlaced := mem_openSegment_sub_iff.mp hz
              simpa [Tiling.AxisParallel.frontier_vadd_eq,
                Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
                neg_add_eq_sub] using (hcontact hzPlaced).1.1)
            (by apply mem_openSegment_sub_iff.mpr; simpa using hpCD)
            hvv hvvCoord hpVV (by intro z hz; exact (hvvEdge hz).1)
    obtain ⟨axisT, w, w', hww, hwwCoord, hpWW, hwwEdge⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
        K (p - t) hpTFrontier hpTNotVertex
    have hwwIm : w.1.im = w'.1.im := by
      cases axisT with
      | horizontal => exact hwwCoord
      | vertical =>
          exfalso
          apply hpTNotVertex
          exact K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
            (c := c - t) (d := d - t) (p := p - t)
            (v := w.1) (w := w'.1) (by intro h; exact hcd (sub_left_inj.mp h))
            (by simp only [Complex.sub_im]; linarith)
            (by
              intro z hz
              have hzPlaced := mem_openSegment_sub_iff.mp hz
              simpa [Tiling.AxisParallel.frontier_vadd_eq,
                Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
                neg_add_eq_sub] using (hcontact hzPlaced).1.2)
            (by apply mem_openSegment_sub_iff.mpr; simpa using hpCD)
            hww hwwCoord hpWW (by intro z hz; exact (hwwEdge hz).1)
    have hpVVPlaced : p ∈ openSegment ℝ (v.1 + s) (v'.1 + s) := by
      rw [show v.1 + s = s +ᵥ v.1 by simp [add_comm],
        show v'.1 + s = s +ᵥ v'.1 by simp [add_comm], ← vadd_openSegment ℝ]
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hpVV
    have hpWWPlaced : p ∈ openSegment ℝ (w.1 + t) (w'.1 + t) := by
      rw [show w.1 + t = t +ᵥ w.1 by simp [add_comm],
        show w'.1 + t = t +ᵥ w'.1 by simp [add_comm], ← vadd_openSegment ℝ]
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hpWW
    refine ⟨v, v', w, w', ⟨hvv, hvvIm, hvvEdge⟩,
      ⟨hww, hwwIm, hwwEdge⟩, ?_, ⟨p.re, ?_, ?_⟩⟩
    · have hpSIm := im_eq_of_mem_openSegment_horizontal hvvIm hpVV
      have hpTIm := im_eq_of_mem_openSegment_horizontal hwwIm hpWW
      simp only [Complex.sub_im, Complex.add_im] at hpSIm hpTIm ⊢
      linarith
    · have hreal := re_mem_openSegment_of_mem hpVVPlaced
      have hvvPlacedRe : (v.1 + s).re ≠ (v'.1 + s).re := by
        intro h
        apply hvv
        exact Complex.ext (add_right_cancel h) hvvIm
      rw [openSegment_eq_Ioo' hvvPlacedRe] at hreal
      simpa only [translatedHorizontalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_re] using hreal
    · have hreal := re_mem_openSegment_of_mem hpWWPlaced
      have hwwPlacedRe : (w.1 + t).re ≠ (w'.1 + t).re := by
        intro h
        apply hww
        exact Complex.ext (add_right_cancel h) hwwIm
      rw [openSegment_eq_Ioo' hwwPlacedRe] at hreal
      simpa only [translatedHorizontalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_re] using hreal
  · rintro ⟨v, v', w, w', ⟨hvv, hvvIm, hvvEdge⟩,
      ⟨hww, hwwIm, hwwEdge⟩, hheight, hoverlap⟩
    rw [Set.Ioo_inter_Ioo, Set.nonempty_Ioo] at hoverlap
    let lo := max (min v.1.re v'.1.re + s.re)
      (min w.1.re w'.1.re + t.re)
    let hi := min (max v.1.re v'.1.re + s.re)
      (max w.1.re w'.1.re + t.re)
    have hlohiLt : lo < hi := hoverlap
    let u : Tiling.Plane := (lo : ℂ) + (v.1 + s).im * Complex.I
    let z : Tiling.Plane := (hi : ℂ) + (v.1 + s).im * Complex.I
    have huz : u ≠ z := by
      intro h
      have hre := congrArg Complex.re h
      simp only [u, z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one,
        zero_sub, neg_zero, add_zero] at hre
      exact hlohiLt.ne hre
    have huzIm : u.im = z.im := by simp [u, z]
    apply labelledSides_giveHorizontalProperContact hvv hvvIm hvvEdge
      hww hwwIm hwwEdge u z huz huzIm
    intro q hq
    have hqIm := im_eq_of_mem_openSegment_horizontal huzIm hq
    have hqRe : q.re ∈ openSegment ℝ lo hi := by
      simpa [u, z] using re_mem_openSegment_of_mem hq
    rw [openSegment_eq_Ioo' hlohiLt.ne] at hqRe
    simp only [min_eq_left hlohiLt.le, max_eq_right hlohiLt.le] at hqRe
    have hqFirstInterval : q.re ∈
        Set.Ioo (min v.1.re v'.1.re + s.re)
          (max v.1.re v'.1.re + s.re) := by
      exact ⟨(le_max_left _ _).trans_lt hqRe.1,
        hqRe.2.trans_le (min_le_left _ _)⟩
    have hqSecondInterval : q.re ∈
        Set.Ioo (min w.1.re w'.1.re + t.re)
          (max w.1.re w'.1.re + t.re) := by
      exact ⟨(le_max_right _ _).trans_lt hqRe.1,
        hqRe.2.trans_le (min_le_right _ _)⟩
    have hvvPlaced : v.1 + s ≠ v'.1 + s := by
      intro h
      exact hvv (add_right_cancel h)
    have hvvPlacedIm : (v.1 + s).im = (v'.1 + s).im := by
      simp only [Complex.add_im, hvvIm]
    have hqAsFirst : (q.re : ℂ) + (v.1 + s).im * Complex.I = q := by
      have huIm : u.im = (v.1 + s).im := by simp [u]
      have hqIm' : q.im = (v.1 + s).im := hqIm.trans huIm
      apply Complex.ext
      · simp
      · simpa only [Complex.add_im, Complex.ofReal_im, zero_add,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.I_re, mul_zero, add_zero] using hqIm'.symm
    have hqFirst : q ∈ openSegment ℝ (v.1 + s) (v'.1 + s) := by
      rw [← hqAsFirst, horizontal_point_mem_openSegment_iff hvvPlaced hvvPlacedIm]
      have hvvPlacedRe : (v.1 + s).re ≠ (v'.1 + s).re := by
        intro h
        apply hvv
        exact Complex.ext (add_right_cancel h) hvvIm
      rw [openSegment_eq_Ioo' hvvPlacedRe]
      simpa only [translatedHorizontalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_re] using hqFirstInterval
    have hwwPlaced : w.1 + t ≠ w'.1 + t := by
      intro h
      exact hww (add_right_cancel h)
    have hwwPlacedIm : (w.1 + t).im = (w'.1 + t).im := by
      simp only [Complex.add_im, hwwIm]
    have hqSecond : q ∈ openSegment ℝ (w.1 + t) (w'.1 + t) := by
      have hqAsSecond : (q.re : ℂ) + (w.1 + t).im * Complex.I = q := by
        rw [← hheight]
        exact hqAsFirst
      rw [← hqAsSecond, horizontal_point_mem_openSegment_iff hwwPlaced hwwPlacedIm]
      have hwwPlacedRe : (w.1 + t).re ≠ (w'.1 + t).re := by
        intro h
        apply hww
        exact Complex.ext (add_right_cancel h) hwwIm
      rw [openSegment_eq_Ioo' hwwPlacedRe]
      simpa only [translatedHorizontalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_re] using hqSecondInterval
    exact ⟨hqFirst, hqSecond⟩

public theorem horizontalProperContact_iff_exists_intrinsicSides
    (K : Region) (s t : Tiling.Plane) :
    HorizontalProperContact K s t ↔
      ∃ v v' w w' : K.vertices,
        (v.1 ≠ v'.1 ∧ v.1.im = v'.1.im ∧
          openSegment ℝ v.1 v'.1 ⊆ frontier K.support \ K.vertices) ∧
        (w.1 ≠ w'.1 ∧ w.1.im = w'.1.im ∧
          openSegment ℝ w.1 w'.1 ⊆ frontier K.support \ K.vertices) ∧
        (v.1 + s).im = (w.1 + t).im ∧
        (Set.Ioo (min v.1.re v'.1.re + s.re)
            (max v.1.re v'.1.re + s.re) ∩
          Set.Ioo (min w.1.re w'.1.re + t.re)
            (max w.1.re w'.1.re + t.re)).Nonempty := by
  simpa only [IsIntrinsicHorizontalSide] using properContact_lower K s t

end Tiling.AxisParallel.Continuous
