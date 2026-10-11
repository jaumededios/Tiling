import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Continuous.IntrinsicHorizontalContact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option linter.unusedVariables false

open Bornology Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- Horizontal displacements realized by a proper overlap of the indicated edge types. -/
def horizontalContactDisplacements
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (a b a' b' : ↥K.vertices) : Set ℝ :=
  {delta | a.1 ≠ b.1 ∧ a.1.im = b.1.im ∧
      openSegment ℝ a.1 b.1 ⊆ frontier K.support \ K.vertices ∧
      a'.1 ≠ b'.1 ∧ a'.1.im = b'.1.im ∧
      openSegment ℝ a'.1 b'.1 ⊆ frontier K.support \ K.vertices ∧
      ∃ t : ↥T, ∃ s : ↥T,
        delta = ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∧
        ∃ u v : Tiling.Plane,
          u ≠ v ∧ u.im = v.im ∧
          openSegment ℝ u v ⊆
            openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
                (b.1 + (t.1 : Tiling.Plane)) ∩
              openSegment ℝ (a'.1 + (s.1 : Tiling.Plane))
                (b'.1 + (s.1 : Tiling.Plane))}

theorem horizontalContactDisplacements_iff
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (a b a' b' : ↥K.vertices) (delta : ℝ) :
    delta ∈ horizontalContactDisplacements K T a b a' b' ↔
      a.1 ≠ b.1 ∧ a.1.im = b.1.im ∧
      openSegment ℝ a.1 b.1 ⊆ frontier K.support \ K.vertices ∧
      a'.1 ≠ b'.1 ∧ a'.1.im = b'.1.im ∧
      openSegment ℝ a'.1 b'.1 ⊆ frontier K.support \ K.vertices ∧
      ∃ t : ↥T, ∃ s : ↥T,
        delta = ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∧
        ∃ u v : Tiling.Plane,
          u ≠ v ∧ u.im = v.im ∧
          openSegment ℝ u v ⊆
            openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
                (b.1 + (t.1 : Tiling.Plane)) ∩
              openSegment ℝ (a'.1 + (s.1 : Tiling.Plane))
                (b'.1 + (s.1 : Tiling.Plane)) :=
  Iff.rfl

private theorem abs_re_sub_translation_le_of_mem_segment
    {a b t p : Tiling.Plane}
    (hp : p ∈ segment ℝ (a + t) (b + t)) :
    |p.re - t.re| ≤ |a.re| + |b.re| := by
  rcases hp with ⟨c, d, hc, hd, hcd, hp⟩
  have hc1 : c ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  have heq : p.re - t.re = c * a.re + d * b.re := by
    rw [← hp]
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    calc
      c * (a.re + t.re) + d * (b.re + t.re) - t.re =
          c * a.re + d * b.re + (c + d - 1) * t.re := by ring
      _ = c * a.re + d * b.re := by rw [hcd]; ring
  rw [heq]
  calc
    |c * a.re + d * b.re| ≤ |c * a.re| + |d * b.re| := abs_add_le _ _
    _ = c * |a.re| + d * |b.re| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg hd]
    _ ≤ |a.re| + |b.re| := by
      exact add_le_add
        (mul_le_of_le_one_left (abs_nonneg _) hc1)
        (mul_le_of_le_one_left (abs_nonneg _) hd1)

theorem horizontalContactDisplacements_bounded
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (a b a' b' : ↥K.vertices) :
    Bornology.IsBounded (horizontalContactDisplacements K T a b a' b') := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  let R : ℝ := |a.1.re| + |b.1.re| + (|a'.1.re| + |b'.1.re|)
  refine ⟨R, ?_⟩
  intro delta hdelta
  rw [horizontalContactDisplacements_iff] at hdelta
  rcases hdelta with
    ⟨_, _, _, _, _, _, t, s, hdelta, u, v, _, _, huv⟩
  let p : Tiling.Plane := midpoint ℝ u v
  have hpOpen : p ∈ openSegment ℝ u v := midpoint_mem_openSegment u v
  have hpBoth := huv hpOpen
  have hpFirst : p ∈ segment ℝ (a.1 + (t.1 : Tiling.Plane))
      (b.1 + (t.1 : Tiling.Plane)) :=
    openSegment_subset_segment ℝ _ _ hpBoth.1
  have hpSecond : p ∈ segment ℝ (a'.1 + (s.1 : Tiling.Plane))
      (b'.1 + (s.1 : Tiling.Plane)) :=
    openSegment_subset_segment ℝ _ _ hpBoth.2
  have hFirst : |p.re - (t.1 : Tiling.Plane).re| ≤ |a.1.re| + |b.1.re| :=
    abs_re_sub_translation_le_of_mem_segment hpFirst
  have hSecond : |p.re - (s.1 : Tiling.Plane).re| ≤ |a'.1.re| + |b'.1.re| :=
    abs_re_sub_translation_le_of_mem_segment hpSecond
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, hdelta, Complex.sub_re]
  have hre : (s.1 : Tiling.Plane).re - (t.1 : Tiling.Plane).re =
      (p.re - (t.1 : Tiling.Plane).re) - (p.re - (s.1 : Tiling.Plane).re) := by
    ring
  rw [hre]
  calc
    |(p.re - (t.1 : Tiling.Plane).re) - (p.re - (s.1 : Tiling.Plane).re)| ≤
        |p.re - (t.1 : Tiling.Plane).re| + |p.re - (s.1 : Tiling.Plane).re| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (p.re - (t.1 : Tiling.Plane).re) 0
          (p.re - (s.1 : Tiling.Plane).re))
    _ ≤ R := add_le_add hFirst hSecond


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




private theorem exists_common_horizontal_subsegment
    {c d e f g h p : Tiling.Plane}
    (hcd : c ≠ d) (hcdIm : c.im = d.im)
    (hef : e ≠ f) (hefIm : e.im = f.im)
    (hgh : g ≠ h) (hghIm : g.im = h.im)
    (hpCD : p ∈ openSegment ℝ c d)
    (hpEF : p ∈ openSegment ℝ e f)
    (hpGH : p ∈ openSegment ℝ g h) :
    ∃ u v : Tiling.Plane, u ≠ v ∧ u.im = v.im ∧
      openSegment ℝ u v ⊆
        openSegment ℝ c d ∩ (openSegment ℝ e f ∩ openSegment ℝ g h) := by
  have hcdRe : c.re ≠ d.re := fun hre ↦ hcd (Complex.ext hre hcdIm)
  have hefRe : e.re ≠ f.re := fun hre ↦ hef (Complex.ext hre hefIm)
  have hghRe : g.re ≠ h.re := fun hre ↦ hgh (Complex.ext hre hghIm)
  have hpImCD := im_eq_of_mem_openSegment_horizontal hcdIm hpCD
  have hpImEF := im_eq_of_mem_openSegment_horizontal hefIm hpEF
  have hpImGH := im_eq_of_mem_openSegment_horizontal hghIm hpGH
  let A : Set ℝ := openSegment ℝ c.re d.re ∩
    (openSegment ℝ e.re f.re ∩ openSegment ℝ g.re h.re)
  have hAOpen : IsOpen A := by
    have hcdOpen : IsOpen (openSegment ℝ c.re d.re) := by
      rw [openSegment_eq_Ioo' hcdRe]
      exact isOpen_Ioo
    have hefOpen : IsOpen (openSegment ℝ e.re f.re) := by
      rw [openSegment_eq_Ioo' hefRe]
      exact isOpen_Ioo
    have hghOpen : IsOpen (openSegment ℝ g.re h.re) := by
      rw [openSegment_eq_Ioo' hghRe]
      exact isOpen_Ioo
    exact hcdOpen.inter (hefOpen.inter hghOpen)
  have hpA : p.re ∈ A := ⟨
    re_mem_openSegment_of_mem hpCD,
    re_mem_openSegment_of_mem hpEF,
    re_mem_openSegment_of_mem hpGH⟩
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.1 (hAOpen.mem_nhds hpA)
  let δ := r / 2
  have hδ : 0 < δ := half_pos hr
  let u : Tiling.Plane := p - (δ : ℂ)
  let v : Tiling.Plane := p + (δ : ℂ)
  have huA : u.re ∈ A := by
    apply hrA
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [u, Complex.sub_re, Complex.ofReal_re, sub_sub_cancel_left,
      abs_neg, abs_of_pos hδ]
    exact half_lt_self hr
  have hvA : v.re ∈ A := by
    apply hrA
    rw [Metric.mem_ball, Real.dist_eq]
    simp only [v, Complex.add_re, Complex.ofReal_re, add_sub_cancel_left,
      abs_of_pos hδ]
    exact half_lt_self hr
  have huAsCD : (u.re : ℂ) + c.im * Complex.I = u := by
    apply Complex.ext <;> simp [u, hpImCD]
  have hvAsCD : (v.re : ℂ) + c.im * Complex.I = v := by
    apply Complex.ext <;> simp [v, hpImCD]
  have huAsEF : (u.re : ℂ) + e.im * Complex.I = u := by
    rw [hpImEF.symm.trans hpImCD]
    exact huAsCD
  have hvAsEF : (v.re : ℂ) + e.im * Complex.I = v := by
    rw [hpImEF.symm.trans hpImCD]
    exact hvAsCD
  have huAsGH : (u.re : ℂ) + g.im * Complex.I = u := by
    rw [hpImGH.symm.trans hpImCD]
    exact huAsCD
  have hvAsGH : (v.re : ℂ) + g.im * Complex.I = v := by
    rw [hpImGH.symm.trans hpImCD]
    exact hvAsCD
  have huCD : u ∈ openSegment ℝ c d :=
    huAsCD.symm ▸ (horizontal_point_mem_openSegment_iff hcd hcdIm u.re).mpr huA.1
  have hvCD : v ∈ openSegment ℝ c d :=
    hvAsCD.symm ▸ (horizontal_point_mem_openSegment_iff hcd hcdIm v.re).mpr hvA.1
  have huEF : u ∈ openSegment ℝ e f := by
    exact huAsEF.symm ▸ (horizontal_point_mem_openSegment_iff hef hefIm u.re).mpr huA.2.1
  have hvEF : v ∈ openSegment ℝ e f := by
    exact hvAsEF.symm ▸ (horizontal_point_mem_openSegment_iff hef hefIm v.re).mpr hvA.2.1
  have huGH : u ∈ openSegment ℝ g h := by
    exact huAsGH.symm ▸ (horizontal_point_mem_openSegment_iff hgh hghIm u.re).mpr huA.2.2
  have hvGH : v ∈ openSegment ℝ g h := by
    exact hvAsGH.symm ▸ (horizontal_point_mem_openSegment_iff hgh hghIm v.re).mpr hvA.2.2
  refine ⟨u, v, ?_, by simp [u, v], fun z hz ↦ ⟨?_, ?_, ?_⟩⟩
  · intro huv
    have hre := congrArg Complex.re huv
    simp [u, v] at hre
    linarith
  · exact (convex_openSegment c d).openSegment_subset huCD hvCD hz
  · exact (convex_openSegment e f).openSegment_subset huEF hvEF hz
  · exact (convex_openSegment g h).openSegment_subset huGH hvGH hz

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

private theorem properHorizontalContact_hasIntrinsicSideLabels :
  ∀ {K : Region} {T : Set Tiling.Plane},
    ∀ t s : ↥T, t ≠ s →
      Continuous.HorizontalProperContact K t.1 s.1 →
      ∃ a b a' b' : ↥K.vertices,
        ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im =
            a.1.im - a'.1.im ∧
        ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∈
          Tiling.AxisParallel.Structure.horizontalContactDisplacements K T a b a' b' := by
  intro K T t s hts hcontact
  obtain ⟨c, d, hcd, hcdIm, hcontact⟩ := hcontact
  let p : Tiling.Plane := midpoint ℝ c d
  have hpCD : p ∈ openSegment ℝ c d := midpoint_mem_openSegment c d
  have hpContact := hcontact hpCD
  have hpTFrontier : p - t.1 ∈ frontier K.support :=
    by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hpContact.1.1
  have hpTNotVertex : p - t.1 ∉ K.vertices := by
    intro hpVertex
    apply hpContact.2
    left
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
  have hpSFrontier : p - s.1 ∈ frontier K.support :=
    by simpa only [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hpContact.1.2
  have hpSNotVertex : p - s.1 ∉ K.vertices := by
    intro hpVertex
    apply hpContact.2
    right
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
  obtain ⟨axisT, a, b, hab, habCoord, hpAB, habEdge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K (p - t.1)
      hpTFrontier hpTNotVertex
  have habIm : a.1.im = b.1.im := by
    cases axisT with
    | horizontal => exact habCoord
    | vertical =>
        exfalso
        apply hpTNotVertex
        apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
          (c := c - t.1) (d := d - t.1) (p := p - t.1)
          (v := a.1) (w := b.1)
        · exact fun h ↦ hcd (sub_left_inj.mp h)
        · simp only [Complex.sub_im]; linarith
        · intro z hz
          have hzPlaced := mem_openSegment_sub_iff.mp hz
          simpa [Tiling.AxisParallel.frontier_vadd_eq,
                Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
                neg_add_eq_sub] using (hcontact hzPlaced).1.1
        · apply mem_openSegment_sub_iff.mpr
          simpa using hpCD
        · exact hab
        · exact habCoord
        · exact hpAB
        · exact fun z hz ↦ (habEdge hz).1
  obtain ⟨axisS, a', b', ha'b', ha'b'Coord, hpA'B', ha'b'Edge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K (p - s.1)
      hpSFrontier hpSNotVertex
  have ha'b'Im : a'.1.im = b'.1.im := by
    cases axisS with
    | horizontal => exact ha'b'Coord
    | vertical =>
        exfalso
        apply hpSNotVertex
        apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
          (c := c - s.1) (d := d - s.1) (p := p - s.1)
          (v := a'.1) (w := b'.1)
        · exact fun h ↦ hcd (sub_left_inj.mp h)
        · simp only [Complex.sub_im]; linarith
        · intro z hz
          have hzPlaced := mem_openSegment_sub_iff.mp hz
          simpa [Tiling.AxisParallel.frontier_vadd_eq,
                Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
                neg_add_eq_sub] using (hcontact hzPlaced).1.2
        · apply mem_openSegment_sub_iff.mpr
          simpa using hpCD
        · exact ha'b'
        · exact ha'b'Coord
        · exact hpA'B'
        · exact fun z hz ↦ (ha'b'Edge hz).1
  have hpABPlaced : p ∈ openSegment ℝ (a.1 + t.1) (b.1 + t.1) := by
    rw [show a.1 + t.1 = t.1 +ᵥ a.1 by simp [add_comm],
      show b.1 + t.1 = t.1 +ᵥ b.1 by simp [add_comm], ← vadd_openSegment ℝ]
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hpAB
  have hpA'B'Placed : p ∈ openSegment ℝ (a'.1 + s.1) (b'.1 + s.1) := by
    rw [show a'.1 + s.1 = s.1 +ᵥ a'.1 by simp [add_comm],
      show b'.1 + s.1 = s.1 +ᵥ b'.1 by simp [add_comm], ← vadd_openSegment ℝ]
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hpA'B'
  have habPlaced : a.1 + t.1 ≠ b.1 + t.1 := fun h ↦ hab (add_right_cancel h)
  have ha'b'Placed : a'.1 + s.1 ≠ b'.1 + s.1 := fun h ↦ ha'b' (add_right_cancel h)
  have habPlacedIm : (a.1 + t.1).im = (b.1 + t.1).im := by
    simp only [Complex.add_im]
    linarith
  have ha'b'PlacedIm : (a'.1 + s.1).im = (b'.1 + s.1).im := by
    simp only [Complex.add_im]
    linarith
  obtain ⟨u, v, huv, huvIm, huvSub⟩ := exists_common_horizontal_subsegment
    hcd hcdIm habPlaced habPlacedIm ha'b'Placed ha'b'PlacedIm
    hpCD hpABPlaced hpA'B'Placed
  refine ⟨a, b, a', b', ?_, ?_⟩
  · have hpIm := im_eq_of_mem_openSegment_horizontal hcdIm hpCD
    have hpTIm := im_eq_of_mem_openSegment_horizontal habIm hpAB
    have hpSIm := im_eq_of_mem_openSegment_horizontal ha'b'Im hpA'B'
    simp only [Complex.sub_im] at hpTIm hpSIm ⊢
    linarith
  · rw [Tiling.AxisParallel.Structure.horizontalContactDisplacements_iff]
    refine ⟨hab, habIm, habEdge, ha'b', ha'b'Im, ha'b'Edge,
      t, s, rfl, u, v, huv, huvIm, ?_⟩
    exact fun z hz ↦ ⟨(huvSub hz).2.1, (huvSub hz).2.2⟩

private theorem labelledDisplacement_givesHorizontalProperContact :
  ∀ {K : Region} {T : Set Tiling.Plane},
    ∀ t s : ↥T, t ≠ s →
    (∃ a b a' b' : ↥K.vertices,
      ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im =
          a.1.im - a'.1.im ∧
      ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∈
        Tiling.AxisParallel.Structure.horizontalContactDisplacements K T a b a' b') →
      Continuous.HorizontalProperContact K t.1 s.1 := by
  intro K T t s _hts hlabels
  obtain ⟨a, b, a', b', him, hdelta⟩ := hlabels
  rw [Tiling.AxisParallel.Structure.horizontalContactDisplacements_iff] at hdelta
  obtain ⟨hab, habIm, habEdge, ha'b', ha'b'Im, ha'b'Edge,
    t₀, s₀, hre, u, v, huv, huvIm, hoverlap⟩ := hdelta
  have hpBoth := hoverlap (midpoint_mem_openSegment (𝕜 := ℝ) u v)
  have hpFirstIm := im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [habIm]) hpBoth.1
  have hpSecondIm := im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [ha'b'Im]) hpBoth.2
  have him₀ : (s₀.1 - t₀.1).im = a.1.im - a'.1.im := by
    rw [Complex.sub_im]
    simp only [Complex.add_im] at hpFirstIm hpSecondIm
    linarith
  have hdiff : (s.1 : Tiling.Plane) - t.1 = s₀.1 - t₀.1 := by
    apply Complex.ext
    · simpa only [Complex.sub_re] using hre
    · simpa only [Complex.sub_im] using him.trans him₀.symm
  let d : Tiling.Plane := t.1 - t₀.1
  have hsShift : s₀.1 + d = s.1 := by
    dsimp only [d]
    linear_combination -hdiff
  have htShift : t₀.1 + d = t.1 := by simp [d]
  refine Tiling.AxisParallel.Continuous.labelledSides_giveHorizontalProperContact hab habIm habEdge
    ha'b' ha'b'Im ha'b'Edge (u + d) (v + d) ?_ ?_ ?_
  · exact fun h ↦ huv (add_right_cancel h)
  · simp only [Complex.add_im]
    linarith
  · rw [openSegment_eq_image]
    rintro z ⟨r, hr, rfl⟩
    have hline : (1 - r) • (u + d) + r • (v + d) =
        (1 - r) • u + r • v + d := by module
    dsimp only
    rw [hline]
    have hw : AffineMap.lineMap u v r ∈ openSegment ℝ u v :=
      lineMap_mem_openSegment (𝕜 := ℝ) u v hr
    have hwBoth := hoverlap hw
    constructor
    · rw [openSegment_eq_image_lineMap]
      rw [openSegment_eq_image_lineMap] at hwBoth
      obtain ⟨q, hq, hqEq⟩ := hwBoth.1
      refine ⟨q, hq, ?_⟩
      calc
        AffineMap.lineMap (a.1 + t.1) (b.1 + t.1) q =
            AffineMap.lineMap ((a.1 + t₀.1) + d) ((b.1 + t₀.1) + d) q := by
          congr 2 <;> rw [add_assoc, htShift]
        _ = AffineMap.lineMap (a.1 + t₀.1) (b.1 + t₀.1) q + d := by
          exact (AffineMap.lineMap_vadd _ _ d q).symm
        _ = AffineMap.lineMap u v r + d := congrArg (fun z ↦ z + d) hqEq
        _ = (1 - r) • u + r • v + d := by
          rw [AffineMap.lineMap_apply_module]
    · rw [openSegment_eq_image_lineMap]
      have hwSecond := hwBoth.2
      rw [openSegment_eq_image_lineMap] at hwSecond
      obtain ⟨q, hq, hqEq⟩ := hwSecond
      refine ⟨q, hq, ?_⟩
      calc
        AffineMap.lineMap (a'.1 + s.1) (b'.1 + s.1) q =
            AffineMap.lineMap ((a'.1 + s₀.1) + d) ((b'.1 + s₀.1) + d) q := by
          congr 2 <;> rw [add_assoc, hsShift]
        _ = AffineMap.lineMap (a'.1 + s₀.1) (b'.1 + s₀.1) q + d := by
          exact (AffineMap.lineMap_vadd _ _ d q).symm
        _ = AffineMap.lineMap u v r + d := congrArg (fun z ↦ z + d) hqEq
        _ = (1 - r) • u + r • v + d := by
          rw [AffineMap.lineMap_apply_module]

private theorem horizontalProperContact_self :
  ∀ (K : Region) (t : Tiling.Plane),
    Continuous.HorizontalProperContact K t t := by
  intro K t
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  let vK : ↥K.vertices := ⟨v, hv⟩
  obtain ⟨wK, hwv, hwIm, hedge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge
      K Axis.horizontal vK
  have hwIm' : vK.1.im = wK.1.im := by
    simpa [Axis.transverseCoord] using hwIm.symm
  refine Tiling.AxisParallel.Continuous.labelledSides_giveHorizontalProperContact
    hwv.symm hwIm' hedge
    hwv.symm hwIm' hedge (vK.1 + t) (wK.1 + t) ?_ ?_ ?_
  · exact fun h ↦ hwv (add_right_cancel h).symm
  · simp only [Complex.add_im]
    linarith
  · intro z hz
    exact ⟨hz, hz⟩

private theorem horizontalProperContact_comm
    {K : Region} {s t : Tiling.Plane} :
    Continuous.HorizontalProperContact K s t ↔
      Continuous.HorizontalProperContact K t s := by
  constructor <;> rintro ⟨a, b, hab, him, hseg⟩
  · refine ⟨a, b, hab, him, fun z hz ↦ ?_⟩
    have h := hseg hz
    exact ⟨⟨h.1.2, h.1.1⟩, by simpa [union_comm] using h.2⟩
  · refine ⟨a, b, hab, him, fun z hz ↦ ?_⟩
    have h := hseg hz
    exact ⟨⟨h.1.2, h.1.1⟩, by simpa [union_comm] using h.2⟩

theorem verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement :
  ∀ (K : Region) (T : Set Tiling.Plane) (t s : ↥T),
    (Continuous.verticalPlateGraph K T).Adj t s ↔
      t ≠ s ∧
        ∃ a b a' b' : ↥K.vertices,
          ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).im =
              a.1.im - a'.1.im ∧
          ((s.1 : Tiling.Plane) - (t.1 : Tiling.Plane)).re ∈
            Tiling.AxisParallel.Structure.horizontalContactDisplacements K T a b a' b' := by
  intro K T t s
  rw [Continuous.verticalPlateGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hts, hcontact⟩
    have hcontact' : Continuous.HorizontalProperContact K t.1 s.1 :=
      hcontact.elim id (fun h ↦ horizontalProperContact_comm.mpr h)
    exact ⟨hts, properHorizontalContact_hasIntrinsicSideLabels t s hts hcontact'⟩
  · rintro ⟨hts, hlabels⟩
    exact ⟨hts, Or.inl (labelledDisplacement_givesHorizontalProperContact t s hts hlabels)⟩

end Tiling.AxisParallel.Structure
