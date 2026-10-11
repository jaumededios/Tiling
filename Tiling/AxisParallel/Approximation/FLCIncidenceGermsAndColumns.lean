import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Continuous.IntrinsicHorizontalContact
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.QuadrantGermGeometry

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Approximation

/-!
The incidence, local-germ, and column transport declarations are intentionally kept in this
module.  Their proofs use the metric-control package and neutral quadrant-germ geometry;
no alternative incidence or plate representation is introduced here.
-/

/-- A labelled centre deformation preserves the one-coordinate condition for a vertical plate. -/
theorem deformation_preserves_verticalPlateColumn
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (Psource : Tiling.AxisParallel.Continuous.VerticalPlate C.region C.centres)
    (Ptarget : Tiling.AxisParallel.Continuous.VerticalPlate
      D.deformedRegion (deformedCenterCarrier Tphi))
    (hsource : Psource.centres = Set.image Subtype.val S)
    (htarget : Ptarget.centres = deformedCenterCarrierOn Tphi S)
    (hColumn : Tiling.AxisParallel.Continuous.IsVerticalColumn Psource) :
    Tiling.AxisParallel.Continuous.IsVerticalColumn Ptarget := by
  have _hScale := hScale
  have _hphi := hphi
  rw [Tiling.AxisParallel.Continuous.IsVerticalColumn] at hColumn ⊢
  obtain ⟨x, hx⟩ := hColumn
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    refine ⟨(Tphi s₀).re, ?_⟩
    intro z hz
    rw [htarget] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    have hsSource : (s : Tiling.Plane) ∈ Psource.centres := by
      rw [hsource]
      exact ⟨s, hs, rfl⟩
    have hs₀Source : (s₀ : Tiling.Plane) ∈ Psource.centres := by
      rw [hsource]
      exact ⟨s₀, hs₀, rfl⟩
    have hre : (s : Tiling.Plane).re = (s₀ : Tiling.Plane).re :=
      (hx hsSource).trans (hx hs₀Source).symm
    change (Tphi s).re = (Tphi s₀).re
    rw [hTphi s, hTphi s₀]
    simp only [mapPoint, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, mapScalar]
    congr 2
    apply Subtype.ext
    exact hre
  · refine ⟨0, ?_⟩
    intro z hz
    rw [htarget, deformedCenterCarrierOn] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact (hS ⟨s, hs⟩).elim

open Function Set
open scoped Pointwise

noncomputable section

open Tiling AxisParallel Approximation
open Tiling.AxisParallel.IntrinsicVertices
open Tiling.AxisParallel.Foundations

universe u

private def OccupiesQuadrant (K : Region) (S : Set Tiling.Plane)
    (a : Tiling.Plane) (q : Quadrant) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.ball a r ∩ quadrantAt q a ⊆ regularSupport K S

private def supportGerm (K : Region) (S : Set Tiling.Plane)
    (a : Tiling.Plane) : Set Quadrant :=
  {q | OccupiesQuadrant K S a q}

private structure ControlledGermLabels (C : ApproximationContext.{u})
    (S : Set ↥C.centres) (a : ↥C.translatedVertices) where
  labels : Finset ↥C.centres
  labels_spec : ∀ t, t ∈ labels ↔
    t ∈ S ∧ (a : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support
  quadrant_spec : ∀ q,
    q ∈ supportGerm C.region (Set.image Subtype.val S) a ↔
      ∃ t, t ∈ labels ∧
        ∃ r : ℝ, 0 < r ∧
          Metric.ball (a : Tiling.Plane) r ∩ quadrantAt q a ⊆
            (t : Tiling.Plane) +ᵥ C.region.openCarrier

private structure ImageAnchorCandidateSet
    (C : ApproximationContext.{u})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (a : ↥C.translatedVertices) where
  sourceRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  candidates : Finset ↥C.centres
  candidates_spec : ∀ t, t ∈ candidates ↔
    dist (t : Tiling.Plane) (a : Tiling.Plane) ≤ sourceRadius
  captures_unitBall : ∀ t,
    (Metric.ball (mapTranslatedVertex phi a) 1 ∩
      (Tphi t +ᵥ D.deformedRegion.openCarrier)).Nonempty →
        t ∈ candidates

private theorem finite_closed_supports_separation
    {α β : Type*} [PseudoMetricSpace α]
    (p : α) (B : Finset β) (F : β → Set α)
    (hclosed : ∀ t ∈ B, IsClosed (F t))
    (hnot : ∀ t ∈ B, p ∉ F t) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ t ∈ B, Disjoint (Metric.ball p r) (F t) := by
  classical
  induction B using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pos, le_rfl, ?_⟩
      simp
  | @insert t B hnotmem ih =>
      have htclosed := hclosed t (Finset.mem_insert_self t B)
      have htp : p ∈ (F t)ᶜ := hnot t (Finset.mem_insert_self t B)
      obtain ⟨rt, hrt, hrtball⟩ := Metric.mem_nhds_iff.mp
        (htclosed.isOpen_compl.mem_nhds htp)
      have hclosedB : ∀ s ∈ B, IsClosed (F s) := by
        intro s hs
        exact hclosed s (Finset.mem_insert_of_mem hs)
      have hnotB : ∀ s ∈ B, p ∉ F s := by
        intro s hs
        exact hnot s (Finset.mem_insert_of_mem hs)
      obtain ⟨rB, hrB, hrB1, hB⟩ := ih hclosedB hnotB
      refine ⟨min rt (min rB 1), lt_min hrt (lt_min hrB one_pos),
        min_le_right _ _ |>.trans (min_le_right _ _), ?_⟩
      intro s hs
      simp only [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · apply Set.disjoint_left.2
        intro z hz hzF
        exact (hrtball (Metric.ball_subset_ball (min_le_left _ _) hz)) hzF
      · have hmin : min rt (min rB 1) ≤ rB :=
          (min_le_right rt (min rB 1)).trans (min_le_left rB 1)
        exact (hB s hs).mono_left (Metric.ball_subset_ball hmin)

private theorem openSegment_axisAligned_local
    {K : Region} {a b : Tiling.Plane} (hab : a ≠ b)
    (hfront : openSegment ℝ a b ⊆ frontier K.support) :
    a.re = b.re ∨ a.im = b.im := by
  by_contra hnot
  have hneRe : a.re ≠ b.re := by
    intro h
    exact hnot (Or.inl h)
  have hneIm : a.im ≠ b.im := by
    intro h
    exact hnot (Or.inr h)
  let p : Tiling.Plane := AffineMap.lineMap a b (1 / 2 : ℝ)
  have hpseg : p ∈ openSegment ℝ a b := by
    exact lineMap_mem_openSegment ℝ a b (by norm_num)
  obtain ⟨r, hr, hcross⟩ := K.isAxisParallel.localBoundaryCross p
  let delta : ℝ := min ((1 - (1 / 2 : ℝ)) / 2) (r / (2 * dist a b))
  have habDist : 0 < dist a b := dist_pos.mpr hab
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min (by norm_num) (div_pos hr (mul_pos zero_lt_two habDist))
  have hthetaDelta : (1 / 2 : ℝ) + delta ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨by linarith, ?_⟩
    have hdeltaLe : delta ≤ (1 - (1 / 2 : ℝ)) / 2 := min_le_left _ _
    linarith
  let q : Tiling.Plane := AffineMap.lineMap a b ((1 / 2 : ℝ) + delta)
  have hqseg : q ∈ openSegment ℝ a b :=
    lineMap_mem_openSegment ℝ a b hthetaDelta
  have hqne : q ≠ p := by
    intro heq
    have hparam := AffineMap.lineMap_injective ℝ hab (by simpa [q, p] using heq)
    linarith
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : AffineMap.lineMap a b ((1 / 2 : ℝ) + delta) -
        AffineMap.lineMap a b (1 / 2 : ℝ) = delta • (b - a) := by
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      module
    rw [show q = AffineMap.lineMap a b ((1 / 2 : ℝ) + delta) by rfl,
      show p = AffineMap.lineMap a b (1 / 2 : ℝ) by rfl, hdiff,
      norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
    have hnorm : ‖b - a‖ = dist a b := by
      rw [dist_eq_norm]
      simpa only [norm_neg] using congrArg norm (by abel : b - a = -(a - b))
    rw [hnorm]
    have hdeltaLe : delta ≤ r / (2 * dist a b) := min_le_right _ _
    calc
      delta * dist a b ≤ (r / (2 * dist a b)) * dist a b :=
        mul_le_mul_of_nonneg_right hdeltaLe habDist.le
      _ = r / 2 := by field_simp
      _ < r := half_lt_self hr
  have hqfront : q ∈ frontier K.support := hfront hqseg
  have hcrossq := hcross q hqball hqfront
  rcases hcrossq with hqre | hqim
  · exfalso
    have hcoord : delta * (b.re - a.re) = 0 := by
      have hi := hqre
      dsimp [q, p] at hi
      simp only [AffineMap.lineMap_apply_module, Complex.add_re,
        Complex.smul_re, smul_eq_mul] at hi
      linarith
    exact hneRe (sub_eq_zero.mp ((mul_eq_zero.mp hcoord).resolve_left hdelta.ne')).symm
  · exfalso
    have hcoord : delta * (b.im - a.im) = 0 := by
      have hr' := hqim
      dsimp [q, p] at hr'
      simp only [AffineMap.lineMap_apply_module, Complex.add_im,
        Complex.smul_im, smul_eq_mul] at hr'
      linarith
    exact hneIm (sub_eq_zero.mp ((mul_eq_zero.mp hcoord).resolve_left hdelta.ne')).symm

private theorem mem_segment_horizontal_local
    {a b p : Tiling.Plane} (hab : a ≠ b) (him : a.im = b.im) :
    p ∈ segment ℝ a b ↔ p.im = a.im ∧ p.re ∈ uIcc a.re b.re := by
  constructor
  · rw [segment_eq_image_lineMap] at *
    rintro ⟨θ, hθ, rfl⟩
    constructor
    · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
        Complex.smul_im, smul_eq_mul]
      rw [him]
      ring
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
        Complex.smul_re, smul_eq_mul]
      rcases le_total a.re b.re with hle | hge
      · rw [Set.uIcc_of_le hle]
        have h₁ : 0 ≤ θ * (b.re - a.re) :=
          mul_nonneg hθ.1 (sub_nonneg.mpr hle)
        have h₂ : θ * (b.re - a.re) ≤ b.re - a.re := by
          rw [← one_mul (b.re - a.re)]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hθ.2 (sub_nonneg.mpr hle))
        rw [show (1 - θ) * a.re + θ * b.re =
          a.re + θ * (b.re - a.re) by ring]
        exact ⟨by linarith, by linarith⟩
      · rw [Set.uIcc_of_ge hge]
        have h₁ : 0 ≤ (1 - θ) * (a.re - b.re) :=
          mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hge)
        have h₂ : (1 - θ) * (a.re - b.re) ≤ a.re - b.re := by
          rw [← one_mul (a.re - b.re)]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (sub_le_self 1 hθ.1)
              (sub_nonneg.mpr hge))
        rw [show (1 - θ) * a.re + θ * b.re =
          b.re + (1 - θ) * (a.re - b.re) by ring]
        exact ⟨by linarith, by linarith⟩
  · rintro ⟨hpim, hpre⟩
    rw [segment_eq_image_lineMap]
    rcases le_total a.re b.re with hle | hge
    · have hne : a.re ≠ b.re := by
        intro h
        apply hab
        exact Complex.ext h him
      have hθ : (p.re - a.re) / (b.re - a.re) ∈ Icc (0 : ℝ) 1 := by
        rw [Set.mem_Icc]
        rw [Set.uIcc_of_le hle] at hpre
        have hlt : a.re < b.re := lt_of_le_of_ne hle hne
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpre.1) (le_of_lt (sub_pos.mpr hlt))
        · exact (div_le_one (sub_pos.mpr hlt)).2 (sub_le_sub_right hpre.2 a.re)
      refine ⟨(p.re - a.re) / (b.re - a.re), hθ, ?_⟩
      apply Complex.ext
      · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
          Complex.smul_re, smul_eq_mul]
        field_simp
        ring
      · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
          Complex.smul_im, smul_eq_mul]
        rw [show (1 - (p.re - a.re) / (b.re - a.re)) * a.im +
            (p.re - a.re) / (b.re - a.re) * b.im = a.im by
              rw [him]
              ring]
        simpa using hpim.symm
    · have hne : b.re ≠ a.re := by
        intro h
        apply hab
        exact Complex.ext h.symm him
      have hθ : (p.re - b.re) / (a.re - b.re) ∈ Icc (0 : ℝ) 1 := by
        rw [Set.mem_Icc]
        rw [Set.uIcc_of_ge hge] at hpre
        have hlt : b.re < a.re := lt_of_le_of_ne hge hne
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpre.1) (le_of_lt (sub_pos.mpr hlt))
        · exact (div_le_one (sub_pos.mpr hlt)).2 (sub_le_sub_right hpre.2 b.re)
      refine ⟨1 - (p.re - b.re) / (a.re - b.re), ?_, ?_⟩
      · constructor <;> linarith [hθ.1, hθ.2]
      · apply Complex.ext
        · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
            Complex.smul_re, smul_eq_mul]
          field_simp
          ring
        · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
            Complex.smul_im, smul_eq_mul]
          rw [← him, ← hpim]
          ring

private theorem mem_segment_vertical_local
    {a b p : Tiling.Plane} (hab : a ≠ b) (hre : a.re = b.re) :
    p ∈ segment ℝ a b ↔ p.re = a.re ∧ p.im ∈ uIcc a.im b.im := by
  constructor
  · rw [segment_eq_image_lineMap] at *
    rintro ⟨θ, hθ, rfl⟩
    constructor
    · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
        Complex.smul_re, smul_eq_mul]
      rw [hre]
      ring
    · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
        Complex.smul_im, smul_eq_mul]
      rcases le_total a.im b.im with hle | hge
      · rw [Set.uIcc_of_le hle]
        have h₁ : 0 ≤ θ * (b.im - a.im) :=
          mul_nonneg hθ.1 (sub_nonneg.mpr hle)
        have h₂ : θ * (b.im - a.im) ≤ b.im - a.im := by
          rw [← one_mul (b.im - a.im)]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right hθ.2 (sub_nonneg.mpr hle))
        rw [show (1 - θ) * a.im + θ * b.im =
          a.im + θ * (b.im - a.im) by ring]
        exact ⟨by linarith, by linarith⟩
      · rw [Set.uIcc_of_ge hge]
        have h₁ : 0 ≤ (1 - θ) * (a.im - b.im) :=
          mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hge)
        have h₂ : (1 - θ) * (a.im - b.im) ≤ a.im - b.im := by
          rw [← one_mul (a.im - b.im)]
          simpa only [one_mul] using
            (mul_le_mul_of_nonneg_right (sub_le_self 1 hθ.1)
              (sub_nonneg.mpr hge))
        rw [show (1 - θ) * a.im + θ * b.im =
          b.im + (1 - θ) * (a.im - b.im) by ring]
        exact ⟨by linarith, by linarith⟩
  · rintro ⟨hpre, hpim⟩
    rw [segment_eq_image_lineMap]
    rcases le_total a.im b.im with hle | hge
    · have hne : a.im ≠ b.im := by
        intro h
        apply hab
        exact Complex.ext hre h
      have hθ : (p.im - a.im) / (b.im - a.im) ∈ Icc (0 : ℝ) 1 := by
        rw [Set.mem_Icc]
        rw [Set.uIcc_of_le hle] at hpim
        have hlt : a.im < b.im := lt_of_le_of_ne hle hne
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpim.1) (le_of_lt (sub_pos.mpr hlt))
        · exact (div_le_one (sub_pos.mpr hlt)).2 (sub_le_sub_right hpim.2 a.im)
      refine ⟨(p.im - a.im) / (b.im - a.im), hθ, ?_⟩
      apply Complex.ext
      · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
          Complex.smul_re, smul_eq_mul]
        rw [show (1 - (p.im - a.im) / (b.im - a.im)) * a.re +
            (p.im - a.im) / (b.im - a.im) * b.re = a.re by
              rw [hre]
              ring]
        simpa using hpre.symm
      · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
          Complex.smul_im, smul_eq_mul]
        field_simp
        ring
    · have hne : b.im ≠ a.im := by
        intro h
        apply hab
        exact Complex.ext hre h.symm
      have hθ : (p.im - b.im) / (a.im - b.im) ∈ Icc (0 : ℝ) 1 := by
        rw [Set.mem_Icc]
        rw [Set.uIcc_of_ge hge] at hpim
        have hlt : b.im < a.im := lt_of_le_of_ne hge hne
        constructor
        · exact div_nonneg (sub_nonneg.mpr hpim.1) (le_of_lt (sub_pos.mpr hlt))
        · exact (div_le_one (sub_pos.mpr hlt)).2 (sub_le_sub_right hpim.2 b.im)
      refine ⟨1 - (p.im - b.im) / (a.im - b.im), ?_, ?_⟩
      · constructor <;> linarith [hθ.1, hθ.2]
      · apply Complex.ext
        · simp only [AffineMap.lineMap_apply_module, Complex.add_re,
            Complex.smul_re, smul_eq_mul]
          rw [← hre, ← hpre]
          ring
        · simp only [AffineMap.lineMap_apply_module, Complex.add_im,
            Complex.smul_im, smul_eq_mul]
          field_simp
          ring

private theorem dist_le_dist_of_mem_segment_local
    {a b p : Tiling.Plane} (hp : p ∈ segment ℝ a b) :
    dist p a ≤ dist b a ∧ dist p b ≤ dist b a := by
  rw [segment_eq_image_lineMap] at hp
  obtain ⟨θ, hθ, rfl⟩ := hp
  have hpa : AffineMap.lineMap a b θ - a = θ • (b - a) := by
    rw [AffineMap.lineMap_apply_module]
    module
  have hpb : AffineMap.lineMap a b θ - b = (1 - θ) • (a - b) := by
    rw [AffineMap.lineMap_apply_module]
    module
  constructor
  · rw [dist_eq_norm, hpa, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hθ.1]
    have hnorm : ‖b - a‖ = dist b a := by
      rw [dist_eq_norm]
    rw [hnorm]
    simpa [mul_comm] using
      (mul_le_of_le_one_right (dist_nonneg) hθ.2 :
        dist b a * θ ≤ dist b a)
  · rw [dist_eq_norm, hpb, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hθ.2)]
    have hnorm : ‖a - b‖ = dist b a := by
      rw [dist_eq_norm]
      simpa only [norm_neg] using congrArg norm (by abel : a - b = -(b - a))
    rw [hnorm]
    simpa [mul_comm] using
      (mul_le_of_le_one_right (dist_nonneg) (sub_le_self 1 hθ.1) :
        dist b a * (1 - θ) ≤ dist b a)

private theorem mapPoint_add_indexed_local
    {C : ApproximationContext}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    mapPoint phi
      ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
        C.coordinateSpace.add_mem x.2.2 y.2.2⟩ =
      mapPoint phi x + mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    have hxy : (⟨(x.1).re + (y.1).re,
        C.coordinateSpace.add_mem x.2.1 y.2.1⟩ : C.coordinateSpace) =
        ⟨(x.1).re, x.2.1⟩ + ⟨(y.1).re, y.2.1⟩ := by
      apply Subtype.ext
      rfl
    rw [hxy, map_add]
    norm_num
  · simp only [mapPoint, mapScalar, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_add, add_zero]
    have hxy : (⟨(x.1).im + (y.1).im,
        C.coordinateSpace.add_mem x.2.2 y.2.2⟩ : C.coordinateSpace) =
        ⟨(x.1).im, x.2.2⟩ + ⟨(y.1).im, y.2.2⟩ := by
      apply Subtype.ext
      rfl
    rw [hxy, map_add]
    norm_num

private theorem mapTranslatedVertex_add_local
    {C : ApproximationContext}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (v : C.region.vertices) (s : C.centres) :
    ∃ x : ↥C.translatedVertices,
      (x : Tiling.Plane) = (v : Tiling.Plane) + (s : Tiling.Plane) ∧
      mapTranslatedVertex phi x =
        mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint s.1 s.2) := by
  let x : ↥C.translatedVertices := ⟨(v : Tiling.Plane) + (s : Tiling.Plane),
    ⟨v, v.2, s, s.2, rfl⟩⟩
  refine ⟨x, rfl, ?_⟩
  change mapPoint phi (C.translatedVertexPoint x) = _
  have hx : C.translatedVertexPoint x =
      ⟨(v : Tiling.Plane) + (s : Tiling.Plane),
        C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem s.1 s.2),
        C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2)
          (C.centre_im_mem s.1 s.2)⟩ := by
    apply Subtype.ext
    rfl
  rw [hx]
  convert (mapPoint_add_indexed_local phi
    (C.vertexPoint v.1 v.2) (C.centrePoint s.1 s.2)) using 1
  apply congrArg (mapPoint phi)
  apply Subtype.ext
  rfl

private theorem diam_support_eq_openCarrier_local (K : Region) :
    Metric.diam K.support = Metric.diam K.openCarrier := by
  change Metric.diam K.support = Metric.diam (interior K.support)
  nth_rewrite 1 [← K.isPolygonal.closure_interior]
  exact Metric.diam_closure _

private theorem vertex_mem_support_local {K : Region}
    {v : Tiling.Plane} (hv : v ∈ K.vertices) : v ∈ K.support := by
  rw [← K.isPolygonal.closure_interior]
  exact frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier K hv)

private def IsIntrinsicEdge (K : Region) (a b : Tiling.Plane) : Prop :=
  a ∈ K.vertices ∧ b ∈ K.vertices ∧ a ≠ b ∧
    openSegment ℝ a b ⊆ frontier K.openCarrier ∧
    ∀ v ∈ K.vertices, v ∉ openSegment ℝ a b

private theorem translated_endpoint_mem_support_local
    {K : Region} {a b t : Tiling.Plane}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) :
    a + t ∈ t +ᵥ K.support ∧ b + t ∈ t +ᵥ K.support := by
  constructor
  · rw [show a + t = t +ᵥ a by simp [vadd_eq_add, add_comm]]
    exact ⟨a, vertex_mem_support_local ha, rfl⟩
  · rw [show b + t = t +ᵥ b by simp [vadd_eq_add, add_comm]]
    exact ⟨b, vertex_mem_support_local hb, rfl⟩

private theorem translated_edge_endpoint_dist_le_diam_local
    {K : Region} {a b t : Tiling.Plane}
    (ha : a ∈ K.vertices) (hb : b ∈ K.vertices) :
    dist (a + t) (b + t) ≤ Metric.diam K.openCarrier := by
  have haSupport := vertex_mem_support_local ha
  have hbSupport := vertex_mem_support_local hb
  have hdiam := Metric.dist_le_diam_of_mem K.isPolygonal.isBounded haSupport hbSupport
  rw [diam_support_eq_openCarrier_local K] at hdiam
  simpa [dist_eq_norm] using hdiam

private theorem segment_translated_pair_lt_control_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    {a b v : C.region.vertices} {s t : C.centres}
    (hp : (v : Tiling.Plane) + (s : Tiling.Plane) ∈
      segment ℝ ((a : Tiling.Plane) + (t : Tiling.Plane))
        ((b : Tiling.Plane) + (t : Tiling.Plane))) :
    dist ((v : Tiling.Plane) + (s : Tiling.Plane))
        ((a : Tiling.Plane) + (t : Tiling.Plane)) < P.controlRadius ∧
      dist ((v : Tiling.Plane) + (s : Tiling.Plane))
        ((b : Tiling.Plane) + (t : Tiling.Plane)) < P.controlRadius := by
  have hdist := dist_le_dist_of_mem_segment_local hp
  have hedge := translated_edge_endpoint_dist_le_diam_local
    (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
  have hdiam : Metric.diam C.region.openCarrier < P.controlRadius := by
    exact (by nlinarith [hScale, P.scale_pos] :
      Metric.diam C.region.openCarrier < P.scale).trans
      P.scale_lt_controlRadius
  have hedge' : dist ((b : Tiling.Plane) + (t : Tiling.Plane))
      ((a : Tiling.Plane) + (t : Tiling.Plane)) ≤
      Metric.diam C.region.openCarrier := by
    simpa [dist_comm] using hedge
  constructor
  · exact lt_of_le_of_lt (hdist.1.trans hedge') hdiam
  · exact lt_of_le_of_lt (hdist.2.trans hedge') hdiam

private theorem le_zero_of_sign_eq_local
    {x y : ℝ} (hs : Real.sign x = Real.sign y) (hx : x ≤ 0) : y ≤ 0 := by
  by_contra hy
  have hypos : 0 < y := lt_of_not_ge hy
  have hsy : Real.sign y = 1 := Real.sign_of_pos hypos
  have hsx : Real.sign x = -1 ∨ Real.sign x = 0 := by
    rcases eq_or_lt_of_le hx with hzero | hneg
    · exact Or.inr (Real.sign_eq_zero_iff.mpr hzero)
    · exact Or.inl (Real.sign_of_neg hneg)
  rcases hsx with hsx | hsx
  · linarith [hs, hsx, hsy]
  · linarith [hs, hsx, hsy]

private theorem nonneg_of_sign_eq_local
    {x y : ℝ} (hs : Real.sign x = Real.sign y) (hx : 0 ≤ x) : 0 ≤ y := by
  by_contra hy
  have hyneg : y < 0 := lt_of_not_ge hy
  have hsy : Real.sign y = -1 := Real.sign_of_neg hyneg
  have hsx : Real.sign x = 1 ∨ Real.sign x = 0 := by
    rcases eq_or_lt_of_le hx with hzero | hpos
    · exact Or.inr (Real.sign_eq_zero_iff.mpr hzero.symm)
    · exact Or.inl (Real.sign_of_pos hpos)
  rcases hsx with hsx | hsx <;> linarith [hs, hsx, hsy]

private theorem translated_edge_image_dist_lt_half_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {a b : ↥C.region.vertices} {t : ↥C.centres}
    (y z : ↥C.translatedVertices)
    (hyval : (y : Tiling.Plane) = (a : Tiling.Plane) + (t : Tiling.Plane))
    (hzval : (z : Tiling.Plane) = (b : Tiling.Plane) + (t : Tiling.Plane)) :
    dist (mapTranslatedVertex phi y) (mapTranslatedVertex phi z) < P.scale / 2 := by
  have hsource : dist (y : Tiling.Plane) (z : Tiling.Plane) < P.scale := by
    rw [hyval, hzval]
    have hedge := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
    exact lt_of_le_of_lt hedge (by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)])
  have hlocal := deformation_localAccuracy P phi hphi y z hsource
  rw [dist_eq_norm]
  calc
    ‖mapTranslatedVertex phi y - mapTranslatedVertex phi z‖ =
        ‖(mapTranslatedVertex phi y - mapTranslatedVertex phi z) -
            ((y : Tiling.Plane) - (z : Tiling.Plane)) +
            ((y : Tiling.Plane) - (z : Tiling.Plane))‖ := by
      congr 1
      abel
    _ ≤ ‖(mapTranslatedVertex phi y - mapTranslatedVertex phi z) -
          ((y : Tiling.Plane) - (z : Tiling.Plane))‖ +
          ‖(y : Tiling.Plane) - (z : Tiling.Plane)‖ := norm_add_le _ _
    _ < P.localError + Metric.diam C.region.openCarrier := by
      have hdiam := translated_edge_endpoint_dist_le_diam_local
        (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
      have hnorm : ‖(y : Tiling.Plane) - (z : Tiling.Plane)‖ ≤
          Metric.diam C.region.openCarrier := by
        simpa [dist_eq_norm, hyval, hzval] using hdiam
      have hlocal' : ‖mapTranslatedVertex phi y - mapTranslatedVertex phi z -
          ((y : Tiling.Plane) - (z : Tiling.Plane))‖ < P.localError := by
        simpa [dist_eq_norm] using hlocal
      exact add_lt_add_of_lt_of_le hlocal' hnorm
    _ < P.scale / 2 := by
      rw [P.localError_eq]
      have hscale10 : 10 < P.scale := by
        nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
      have hinv : P.scale⁻¹ < (10 : ℝ)⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num) hscale10
      have hdiamnonneg : 0 ≤ Metric.diam C.region.openCarrier :=
        Metric.diam_nonneg
      nlinarith [hinv, hScale]

private theorem translated_edge_image_dist_lt_quarter_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {a b : ↥C.region.vertices} {t : ↥C.centres}
    (y z : ↥C.translatedVertices)
    (hyval : (y : Tiling.Plane) = (a : Tiling.Plane) + (t : Tiling.Plane))
    (hzval : (z : Tiling.Plane) = (b : Tiling.Plane) + (t : Tiling.Plane)) :
    dist (mapTranslatedVertex phi y) (mapTranslatedVertex phi z) < P.scale / 4 := by
  have hsource : dist (y : Tiling.Plane) (z : Tiling.Plane) < P.scale := by
    rw [hyval, hzval]
    have hedge := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
    exact lt_of_le_of_lt hedge (by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)])
  have hlocal := deformation_localAccuracy P phi hphi y z hsource
  rw [dist_eq_norm]
  calc
    ‖mapTranslatedVertex phi y - mapTranslatedVertex phi z‖ =
        ‖(mapTranslatedVertex phi y - mapTranslatedVertex phi z) -
            ((y : Tiling.Plane) - (z : Tiling.Plane)) +
            ((y : Tiling.Plane) - (z : Tiling.Plane))‖ := by
      congr 1; abel
    _ ≤ ‖(mapTranslatedVertex phi y - mapTranslatedVertex phi z) -
          ((y : Tiling.Plane) - (z : Tiling.Plane))‖ +
          ‖(y : Tiling.Plane) - (z : Tiling.Plane)‖ := norm_add_le _ _
    _ < P.localError + Metric.diam C.region.openCarrier := by
      have hdiam := translated_edge_endpoint_dist_le_diam_local
        (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
      have hnorm : ‖(y : Tiling.Plane) - (z : Tiling.Plane)‖ ≤
          Metric.diam C.region.openCarrier := by
        simpa [dist_eq_norm, hyval, hzval] using hdiam
      have hlocal' : ‖mapTranslatedVertex phi y - mapTranslatedVertex phi z -
          ((y : Tiling.Plane) - (z : Tiling.Plane))‖ < P.localError := by
        simpa [dist_eq_norm] using hlocal
      exact add_lt_add_of_lt_of_le hlocal' hnorm
    _ < P.scale / 4 := by
      rw [P.localError_eq]
      have hscale10 : 10 < P.scale := by
        nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
      have hinv : P.scale⁻¹ < (10 : ℝ)⁻¹ := by
        simpa [one_div] using one_div_lt_one_div_of_lt (by norm_num) hscale10
      have hdiamnonneg : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
      nlinarith [hinv, hScale]

private theorem vertexOnEdgeTransport
    : ∀ {C : ApproximationContext} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (_D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (a b v : ↥C.region.vertices) (s t : ↥C.centres),
      IsIntrinsicEdge C.region a b →
      ((v : Tiling.Plane) + (s : Tiling.Plane) ∈
          segment ℝ ((a : Tiling.Plane) + (t : Tiling.Plane))
            ((b : Tiling.Plane) + (t : Tiling.Plane)) ↔
        mapPoint phi (C.vertexPoint v.1 v.2) + Tphi s ∈
          segment ℝ (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi t)
            (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi t)) := by
  intro C P hScale phi hphi D Tphi hTphi a b v s t hEdge
  rcases hEdge with ⟨ha, hb, hab, hfront, hnov⟩
  have hfront' : openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane) ⊆
      frontier C.region.support := by
    intro q hq
    rw [← C.region.frontier_openCarrier_eq_frontier_support]
    exact hfront hq
  have haxis0 := openSegment_axisAligned_local hab hfront'
  have haxis : (a : Tiling.Plane).im = (b : Tiling.Plane).im ∨
      (a : Tiling.Plane).re = (b : Tiling.Plane).re := by
    rcases haxis0 with hre | him
    · exact Or.inr hre
    · exact Or.inl him
  obtain ⟨x, hxval, hxmap⟩ := mapTranslatedVertex_add_local phi v s
  obtain ⟨y, hyval, hymap⟩ := mapTranslatedVertex_add_local phi a t
  obtain ⟨z, hzval, hzmap⟩ := mapTranslatedVertex_add_local phi b t
  have htargetX : mapTranslatedVertex phi x =
      mapPoint phi (C.vertexPoint v.1 v.2) + Tphi s := by
    simpa [hTphi s] using hxmap
  have htargetY : mapTranslatedVertex phi y =
      mapPoint phi (C.vertexPoint a.1 a.2) + Tphi t := by
    simpa [hTphi t] using hymap
  have htargetZ : mapTranslatedVertex phi z =
      mapPoint phi (C.vertexPoint b.1 b.2) + Tphi t := by
    simpa [hTphi t] using hzmap
  have hyz : y ≠ z := by
    intro h
    apply hab
    simpa [hyval, hzval] using congrArg Subtype.val h
  have htargetYZ : mapTranslatedVertex phi y ≠ mapTranslatedVertex phi z := by
    intro h
    apply hyz
    exact (deformation_injectiveOnTranslatedVertices P phi hphi) h
  have hforwardBounds (hp : (v : Tiling.Plane) + (s : Tiling.Plane) ∈
      segment ℝ ((a : Tiling.Plane) + (t : Tiling.Plane))
        ((b : Tiling.Plane) + (t : Tiling.Plane))) :
      dist (x : Tiling.Plane) (y : Tiling.Plane) < P.controlRadius ∧
        dist (x : Tiling.Plane) (z : Tiling.Plane) < P.controlRadius := by
    simpa [hxval, hyval, hzval] using
      segment_translated_pair_lt_control_local P hScale hp
  have htargetEdge : dist (mapTranslatedVertex phi y)
      (mapTranslatedVertex phi z) < P.scale / 2 :=
    translated_edge_image_dist_lt_half_local P hScale phi hphi y z hyval hzval
  have hedgeControl : dist (y : Tiling.Plane) (z : Tiling.Plane) < P.controlRadius := by
    have hedge := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (t : Tiling.Plane)) a.2 b.2
    have hdiam : Metric.diam C.region.openCarrier < P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
    rw [hyval, hzval]
    exact lt_trans (lt_of_le_of_lt hedge hdiam) P.scale_lt_controlRadius
  have hcoordSign (axis : Axis) {w : ↥C.translatedVertices}
      (hw : dist (x : Tiling.Plane) (w : Tiling.Plane) < P.controlRadius) :
      Real.sign (Axis.coord axis ((x : Tiling.Plane) - (w : Tiling.Plane))) =
        Real.sign (Axis.coord axis (mapTranslatedVertex phi x -
          mapTranslatedVertex phi w)) :=
    (deformation_reflectsFiniteValues P phi hphi axis x w x w hw hw).1.symm
  have habt : (a : Tiling.Plane) + (t : Tiling.Plane) ≠
      (b : Tiling.Plane) + (t : Tiling.Plane) := by
    intro h
    apply hab
    exact add_right_cancel h
  constructor
  · intro hp
    have hbounds := hforwardBounds hp
    rw [← htargetX, ← htargetY, ← htargetZ]
    rcases haxis with him | hre
    · have himt : ((a : Tiling.Plane) + (t : Tiling.Plane)).im =
          ((b : Tiling.Plane) + (t : Tiling.Plane)).im := by
        simpa only [Complex.add_im] using
          congrArg (fun q : ℝ => q + (t : Tiling.Plane).im) him
      have hs := (mem_segment_horizontal_local habt himt).mp hp
      have hzeroY := (deformation_reflectsFiniteValues P phi hphi Axis.vertical
          x y x y hbounds.1 hbounds.1).2.1.mpr
          (by simpa [hxval, hyval, Axis.coord] using sub_eq_zero.mpr hs.1)
      have hzeroZ := (deformation_reflectsFiniteValues P phi hphi Axis.vertical
          x z x z hbounds.2 hbounds.2).2.1.mpr
          (by
            have hsZ : (x : Tiling.Plane).im = (z : Tiling.Plane).im := by
              simpa [hxval, hzval, him] using hs.1
            simpa [Axis.coord, Complex.sub_im] using sub_eq_zero.mpr hsZ)
      have him' : (mapTranslatedVertex phi x).im =
            (mapTranslatedVertex phi y).im := by
          simpa [Axis.coord] using sub_eq_zero.mp hzeroY
      have himz' : (mapTranslatedVertex phi x).im =
            (mapTranslatedVertex phi z).im := by
          simpa [Axis.coord] using sub_eq_zero.mp hzeroZ
      have hs' := (mem_segment_horizontal_local (p := mapTranslatedVertex phi x) htargetYZ
          (by simpa [Axis.coord] using him'.symm.trans himz')).mpr
      refine hs' ⟨him', ?_⟩
      rw [Set.mem_uIcc]
      rcases Set.mem_uIcc.mp hs.2 with hslo | hshi
      · left
        constructor
        · have hsource : 0 ≤ Axis.coord Axis.horizontal
              ((x : Tiling.Plane) - (y : Tiling.Plane)) := by
            simpa [Axis.coord, hxval, hyval] using sub_nonneg.mpr hslo.1
          have htarget := nonneg_of_sign_eq_local
            (hcoordSign Axis.horizontal hbounds.1) hsource
          simpa [Axis.coord] using htarget
        · have hsource : Axis.coord Axis.horizontal
              ((x : Tiling.Plane) - (z : Tiling.Plane)) ≤ 0 := by
            simpa [Axis.coord, hxval, hzval] using sub_nonpos.mpr hslo.2
          have htarget := le_zero_of_sign_eq_local
            (hcoordSign Axis.horizontal hbounds.2) hsource
          simpa [Axis.coord] using htarget
      · right
        constructor
        · have hsource : 0 ≤ Axis.coord Axis.horizontal
              ((x : Tiling.Plane) - (z : Tiling.Plane)) := by
            simpa [Axis.coord, hxval, hzval] using sub_nonneg.mpr hshi.1
          have htarget := nonneg_of_sign_eq_local
            (hcoordSign Axis.horizontal hbounds.2) hsource
          simpa [Axis.coord] using htarget
        · have hsource : Axis.coord Axis.horizontal
              ((x : Tiling.Plane) - (y : Tiling.Plane)) ≤ 0 := by
            simpa [Axis.coord, hxval, hyval] using sub_nonpos.mpr hshi.2
          have htarget := le_zero_of_sign_eq_local
            (hcoordSign Axis.horizontal hbounds.1) hsource
          simpa [Axis.coord] using htarget
    · have hret : ((a : Tiling.Plane) + (t : Tiling.Plane)).re =
          ((b : Tiling.Plane) + (t : Tiling.Plane)).re := by
        simpa only [Complex.add_re] using
          congrArg (fun q : ℝ => q + (t : Tiling.Plane).re) hre
      have hs := (mem_segment_vertical_local habt hret).mp hp
      have hzeroY := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
          x y x y hbounds.1 hbounds.1).2.1.mpr
          (by simpa [hxval, hyval, Axis.coord] using sub_eq_zero.mpr hs.1)
      have hzeroZ := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
          x z x z hbounds.2 hbounds.2).2.1.mpr
          (by
            have hsZ : (x : Tiling.Plane).re = (z : Tiling.Plane).re := by
              simpa [hxval, hzval, hre] using hs.1
            simpa [Axis.coord, Complex.sub_re] using sub_eq_zero.mpr hsZ)
      have hre' : (mapTranslatedVertex phi x).re =
            (mapTranslatedVertex phi y).re := by
          simpa [Axis.coord] using sub_eq_zero.mp hzeroY
      have hrez' : (mapTranslatedVertex phi x).re =
            (mapTranslatedVertex phi z).re := by
          simpa [Axis.coord] using sub_eq_zero.mp hzeroZ
      have hs' := (mem_segment_vertical_local (p := mapTranslatedVertex phi x) htargetYZ
          (by simpa [Axis.coord] using hre'.symm.trans hrez')).mpr
      refine hs' ⟨hre', ?_⟩
      rw [Set.mem_uIcc]
      rcases Set.mem_uIcc.mp hs.2 with hslo | hshi
      · left
        constructor
        · have hsource : 0 ≤ Axis.coord Axis.vertical
              ((x : Tiling.Plane) - (y : Tiling.Plane)) := by
            simpa [Axis.coord, hxval, hyval] using sub_nonneg.mpr hslo.1
          have htarget := nonneg_of_sign_eq_local
            (hcoordSign Axis.vertical hbounds.1) hsource
          simpa [Axis.coord] using htarget
        · have hsource : Axis.coord Axis.vertical
              ((x : Tiling.Plane) - (z : Tiling.Plane)) ≤ 0 := by
            simpa [Axis.coord, hxval, hzval] using sub_nonpos.mpr hslo.2
          have htarget := le_zero_of_sign_eq_local
            (hcoordSign Axis.vertical hbounds.2) hsource
          simpa [Axis.coord] using htarget
      · right
        constructor
        · have hsource : 0 ≤ Axis.coord Axis.vertical
              ((x : Tiling.Plane) - (z : Tiling.Plane)) := by
            simpa [Axis.coord, hxval, hzval] using sub_nonneg.mpr hshi.1
          have htarget := nonneg_of_sign_eq_local
            (hcoordSign Axis.vertical hbounds.2) hsource
          simpa [Axis.coord] using htarget
        · have hsource : Axis.coord Axis.vertical
              ((x : Tiling.Plane) - (y : Tiling.Plane)) ≤ 0 := by
            simpa [Axis.coord, hxval, hyval] using sub_nonpos.mpr hshi.2
          have htarget := le_zero_of_sign_eq_local
            (hcoordSign Axis.vertical hbounds.1) hsource
          simpa [Axis.coord] using htarget
  · intro hp
    have hp' : mapTranslatedVertex phi x ∈ segment ℝ
        (mapTranslatedVertex phi y) (mapTranslatedVertex phi z) := by
      simpa [htargetX, htargetY, htargetZ] using hp
    have htBounds := dist_le_dist_of_mem_segment_local hp'
    have hxy : dist (x : Tiling.Plane) (y : Tiling.Plane) < P.controlRadius := by
      exact (deformation_coarselyProper P phi hphi x y
        (lt_of_le_of_lt htBounds.1 (by simpa [dist_comm] using htargetEdge))).trans
        P.scale_lt_controlRadius
    have hxz : dist (x : Tiling.Plane) (z : Tiling.Plane) < P.controlRadius := by
      exact (deformation_coarselyProper P phi hphi x z
        (lt_of_le_of_lt htBounds.2 (by simpa [dist_comm] using htargetEdge))).trans
        P.scale_lt_controlRadius
    rcases haxis with him | hre
    · have htIm : (mapTranslatedVertex phi y).im =
          (mapTranslatedVertex phi z).im := by
        have hzero : Axis.coord Axis.vertical
            ((y : Tiling.Plane) - (z : Tiling.Plane)) = 0 := by
          simp [hyval, hzval, Axis.coord, him]
        have hzero' := (deformation_reflectsFiniteValues P phi hphi Axis.vertical
          y z y z hedgeControl hedgeControl).2.1.mpr hzero
        simpa [Axis.coord] using sub_eq_zero.mp hzero'
      have ht := (mem_segment_horizontal_local htargetYZ htIm).mp hp'
      have hsY := (deformation_reflectsFiniteValues P phi hphi Axis.vertical x y
        x y hxy hxy).2.1.mp (by
          simpa [Axis.coord] using sub_eq_zero.mpr ht.1)
      have hsZ := (deformation_reflectsFiniteValues P phi hphi Axis.vertical x z
        x z hxz hxz).2.1.mp (by
          simpa [Axis.coord] using sub_eq_zero.mpr (ht.1.trans htIm))
      have himx : (x : Tiling.Plane).im = (y : Tiling.Plane).im := by
        simpa [Axis.coord] using sub_eq_zero.mp hsY
      have hs' := (mem_segment_horizontal_local (p := (x : Tiling.Plane)) habt
        (by simpa only [Complex.add_im] using
          (congrArg (fun q : ℝ => q + (t : Tiling.Plane).im) him))).mpr
      rw [← hxval]
      refine hs' ?_
      refine ⟨(by simpa [hyval] using himx), ?_⟩
      rw [Set.mem_uIcc]
      rcases Set.mem_uIcc.mp ht.2 with htlo | hthi
      · left
        constructor
        · have htarget : 0 ≤ Axis.coord Axis.horizontal
              (mapTranslatedVertex phi x - mapTranslatedVertex phi y) := by
            simpa [Axis.coord] using sub_nonneg.mpr htlo.1
          have hsource := nonneg_of_sign_eq_local
            (hcoordSign Axis.horizontal hxy).symm htarget
          simpa [Axis.coord, hxval, hyval] using hsource
        · have htarget : Axis.coord Axis.horizontal
              (mapTranslatedVertex phi x - mapTranslatedVertex phi z) ≤ 0 := by
            simpa [Axis.coord] using sub_nonpos.mpr htlo.2
          have hsource := le_zero_of_sign_eq_local
            (hcoordSign Axis.horizontal hxz).symm htarget
          simpa [Axis.coord, hxval, hzval] using hsource
      · right
        constructor
        · have htarget : 0 ≤ Axis.coord Axis.horizontal
              (mapTranslatedVertex phi x - mapTranslatedVertex phi z) := by
            simpa [Axis.coord] using sub_nonneg.mpr hthi.1
          have hsource := nonneg_of_sign_eq_local
            (hcoordSign Axis.horizontal hxz).symm htarget
          simpa [Axis.coord, hxval, hzval] using hsource
        · have htarget : Axis.coord Axis.horizontal
              (mapTranslatedVertex phi x - mapTranslatedVertex phi y) ≤ 0 := by
            simpa [Axis.coord] using sub_nonpos.mpr hthi.2
          have hsource := le_zero_of_sign_eq_local
            (hcoordSign Axis.horizontal hxy).symm htarget
          simpa [Axis.coord, hxval, hyval] using hsource
    · have htRe : (mapTranslatedVertex phi y).re =
          (mapTranslatedVertex phi z).re := by
        have hzero : Axis.coord Axis.horizontal
            ((y : Tiling.Plane) - (z : Tiling.Plane)) = 0 := by
          simp [hyval, hzval, Axis.coord, hre]
        have hzero' := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
          y z y z hedgeControl hedgeControl).2.1.mpr hzero
        simpa [Axis.coord] using sub_eq_zero.mp hzero'
      have ht := (mem_segment_vertical_local htargetYZ htRe).mp hp'
      have hsY := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal x y
        x y hxy hxy).2.1.mp (by
          simpa [Axis.coord] using sub_eq_zero.mpr ht.1)
      have hsZ := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal x z
        x z hxz hxz).2.1.mp (by
          simpa [Axis.coord] using sub_eq_zero.mpr (ht.1.trans htRe))
      have hrex : (x : Tiling.Plane).re = (y : Tiling.Plane).re := by
        simpa [Axis.coord] using sub_eq_zero.mp hsY
      have hs' := (mem_segment_vertical_local (p := (x : Tiling.Plane)) habt
        (by simpa only [Complex.add_re] using
          (congrArg (fun q : ℝ => q + (t : Tiling.Plane).re) hre))).mpr
      rw [← hxval]
      refine hs' ?_
      refine ⟨(by simpa [hyval] using hrex), ?_⟩
      rw [Set.mem_uIcc]
      rcases Set.mem_uIcc.mp ht.2 with htlo | hthi
      · left
        constructor
        · have htarget : 0 ≤ Axis.coord Axis.vertical
              (mapTranslatedVertex phi x - mapTranslatedVertex phi y) := by
            simpa [Axis.coord] using sub_nonneg.mpr htlo.1
          have hsource := nonneg_of_sign_eq_local
            (hcoordSign Axis.vertical hxy).symm htarget
          simpa [Axis.coord, hxval, hyval] using hsource
        · have htarget : Axis.coord Axis.vertical
              (mapTranslatedVertex phi x - mapTranslatedVertex phi z) ≤ 0 := by
            simpa [Axis.coord] using sub_nonpos.mpr htlo.2
          have hsource := le_zero_of_sign_eq_local
            (hcoordSign Axis.vertical hxz).symm htarget
          simpa [Axis.coord, hxval, hzval] using hsource
      · right
        constructor
        · have htarget : 0 ≤ Axis.coord Axis.vertical
              (mapTranslatedVertex phi x - mapTranslatedVertex phi z) := by
            simpa [Axis.coord] using sub_nonneg.mpr hthi.1
          have hsource := nonneg_of_sign_eq_local
            (hcoordSign Axis.vertical hxz).symm htarget
          simpa [Axis.coord, hxval, hzval] using hsource
        · have htarget : Axis.coord Axis.vertical
              (mapTranslatedVertex phi x - mapTranslatedVertex phi y) ≤ 0 := by
            simpa [Axis.coord] using sub_nonpos.mpr hthi.2
          have hsource := le_zero_of_sign_eq_local
            (hcoordSign Axis.vertical hxy).symm htarget
          simpa [Axis.coord, hxval, hyval] using hsource


private theorem finiteNonincidentImageSupports_separated_of_anchor_notmem
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (a : ↥C.translatedVertices) (B : Finset ↥C.centres)
    (hnot : ∀ t ∈ B, mapTranslatedVertex phi a ∉
      Tphi t +ᵥ D.deformedRegion.support) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ t ∈ B,
      Disjoint (Metric.ball (mapTranslatedVertex phi a) r)
        (Tphi t +ᵥ D.deformedRegion.support) := by
  apply finite_closed_supports_separation (mapTranslatedVertex phi a) B
    (fun t => Tphi t +ᵥ D.deformedRegion.support)
  · intro t ht
    exact D.deformedRegion.isPolygonal.isClosed.vadd (Tphi t)
  · exact hnot

private theorem finiteNonincidentImageSupports_separated_of_candidate_nonincident
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (a : ↥C.translatedVertices) (S : Set ↥C.centres)
    (G : ControlledGermLabels C S a)
    (Q : ImageAnchorCandidateSet C phi D Tphi a)
    (hanchor : ∀ t ∈ Q.candidates, t ∈ S → t ∉ G.labels →
      mapTranslatedVertex phi a ∉ Tphi t +ᵥ D.deformedRegion.support) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ t ∈ Q.candidates, t ∈ S → t ∉ G.labels →
        Disjoint (Metric.ball (mapTranslatedVertex phi a) r)
          (Tphi t +ᵥ D.deformedRegion.support) := by
  classical
  let B : Finset ↥C.centres :=
    Q.candidates.filter (fun t => t ∈ S ∧ t ∉ G.labels)
  have hnot : ∀ t ∈ B, mapTranslatedVertex phi a ∉
      Tphi t +ᵥ D.deformedRegion.support := by
    intro t ht
    exact hanchor t (Finset.mem_filter.mp ht).1 (Finset.mem_filter.mp ht).2.1
      (Finset.mem_filter.mp ht).2.2
  obtain ⟨r, hr, hr1, hsep⟩ :=
    finiteNonincidentImageSupports_separated_of_anchor_notmem D Tphi a B hnot
  refine ⟨r, hr, hr1, ?_⟩
  intro t htQ htS htG
  apply hsep t
  exact Finset.mem_filter.mpr ⟨htQ, htS, htG⟩

private theorem finite_tiles_quadrant_constancy
    (K : Region) (Q : Finset Tiling.Plane) (a : Tiling.Plane) (q : Quadrant) :
    ∃ r > 0, ∀ t ∈ Q,
      (Metric.ball a r ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier ∨
        Disjoint (Metric.ball a r ∩ quadrantAt q a) (t +ᵥ K.openCarrier)) := by
  classical
  induction Q using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pos, ?_⟩
      simp
  | @insert t Q ht ih =>
      have hopenTile : IsOpen (t +ᵥ K.openCarrier) := by
        exact (Region.openCarrier_regularOpen K).1.vadd t
      have hregularTile : interior (closure (t +ᵥ K.openCarrier)) =
          t +ᵥ K.openCarrier := by
        rw [closure_vadd, interior_vadd, (Region.openCarrier_regularOpen K).2]
      obtain ⟨rt, hrt, p, hg, _hp⟩ :=
        exists_quadrantPattern_germ_of_localBoundaryCross hopenTile hregularTile a
          (Tiling.AxisParallel.translated_openCarrier_frontier_cross K t a)
      have hrtcase :
          Metric.ball a rt ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier ∨
          Disjoint (Metric.ball a rt ∩ quadrantAt q a) (t +ᵥ K.openCarrier) := by
        by_cases hp : p q = true
        · exact Or.inl (fun z hz => (hg q z hz.1 hz.2).mpr hp)
        · exact Or.inr (Set.disjoint_left.mpr (fun z hz hzD =>
            hp ((hg q z hz.1 hz.2).mp hzD)))
      obtain ⟨rQ, hrQ, hQcase⟩ := ih
      let r := min rt rQ
      refine ⟨r, lt_min hrt hrQ, ?_⟩
      intro s hs
      simp only [Finset.mem_insert] at hs
      rcases hs with rfl | hs
      · rcases hrtcase with h | h
        · exact Or.inl (fun z hz => h
            (inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _)) Set.Subset.rfl hz))
        · exact Or.inr (h.mono_left
            (inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _)) Set.Subset.rfl))
      · rcases hQcase s hs with h | h
        · exact Or.inl (fun z hz => h
            (inter_subset_inter (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl hz))
        · exact Or.inr (h.mono_left
            (inter_subset_inter (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl))

private theorem quadrant_pair_of_displacement
    (a b u : Tiling.Plane) (hre : u.re ≠ 0) (him : u.im ≠ 0) :
    ∃ q : Quadrant, a + u ∈ quadrantAt q a ∧ b + u ∈ quadrantAt q b := by
  have hre' : u.re < 0 ∨ 0 < u.re := lt_or_gt_of_ne hre
  have him' : u.im < 0 ∨ 0 < u.im := lt_or_gt_of_ne him
  rcases hre' with hre' | hre' <;> rcases him' with him' | him'
  · refine ⟨.southwest, ?_, ?_⟩ <;>
      dsimp [quadrantAt] <;>
      constructor <;> linarith
  · refine ⟨.northwest, ?_, ?_⟩ <;>
      dsimp [quadrantAt] <;>
      constructor <;> linarith
  · refine ⟨.southeast, ?_, ?_⟩ <;>
      dsimp [quadrantAt] <;>
      constructor <;> linarith
  · refine ⟨.northeast, ?_, ?_⟩ <;>
      dsimp [quadrantAt] <;>
      constructor <;> linarith

private theorem quadrantGerm_membership_of_cross
    {D E : Set Tiling.Plane} {a b : Tiling.Plane} (hDopen : IsOpen D)
    (hEopen : IsOpen E) (hDreg : interior (closure D) = D)
    (hEreg : interior (closure E) = E)
    (hDcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier D →
      z.re = a.re ∨ z.im = a.im)
    (hEcross : ∃ r > 0, ∀ z ∈ Metric.ball b r, z ∈ frontier E →
      z.re = b.re ∨ z.im = b.im)
    (hocc : ∀ q, SetOccupiesQuadrant D a q ↔ SetOccupiesQuadrant E b q) :
    ∃ r : ℝ, 0 < r ∧ ∀ u, dist u 0 < r → (a + u ∈ D ↔ b + u ∈ E) := by
  obtain ⟨rD, hrD, pD, hgD, hpD⟩ :=
    exists_quadrantPattern_germ_of_localBoundaryCross hDopen hDreg a hDcross
  obtain ⟨rE, hrE, pE, hgE, hpE⟩ :=
    exists_quadrantPattern_germ_of_localBoundaryCross hEopen hEreg b hEcross
  let Ds : Set Tiling.Plane := (-a) +ᵥ D
  let Es : Set Tiling.Plane := (-b) +ᵥ E
  have hDs (u : Tiling.Plane) : u ∈ Ds ↔ a + u ∈ D := by
    simp only [Ds, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
  have hEs (u : Tiling.Plane) : u ∈ Es ↔ b + u ∈ E := by
    simp only [Es, Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, vadd_eq_add]
  have hDsOpen : IsOpen Ds := hDopen.vadd (-a)
  have hEsOpen : IsOpen Es := hEopen.vadd (-b)
  have hDsReg : interior (closure Ds) = Ds := by
    dsimp only [Ds]
    rw [closure_vadd, interior_vadd, hDreg]
  have hEsReg : interior (closure Es) = Es := by
    dsimp only [Es]
    rw [closure_vadd, interior_vadd, hEreg]
  have hoff : ∀ᶠ u in nhds (0 : Tiling.Plane),
      u.re ≠ 0 ∧ u.im ≠ 0 → (u ∈ Ds ↔ u ∈ Es) := by
    filter_upwards [Metric.ball_mem_nhds (0 : Tiling.Plane) (lt_min hrD hrE)]
      with u hu hcoords
    obtain ⟨q, hDq, hEq⟩ := quadrant_pair_of_displacement a b u hcoords.1 hcoords.2
    have hDa : a + u ∈ Metric.ball a rD := by
      rw [Metric.mem_ball]
      have hdist : dist (a + u) a = dist u 0 := by
        simpa only [vadd_eq_add, add_zero] using dist_vadd_cancel_left a u 0
      rw [hdist]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hu) (min_le_left _ _)
    have hEb : b + u ∈ Metric.ball b rE := by
      rw [Metric.mem_ball]
      have hdist : dist (b + u) b = dist u 0 := by
        simpa only [vadd_eq_add, add_zero] using dist_vadd_cancel_left b u 0
      rw [hdist]
      exact lt_of_lt_of_le (Metric.mem_ball.mp hu) (min_le_right _ _)
    exact (hDs u).trans ((hgD q (a + u) hDa hDq).trans
      ((hpD q).trans ((hocc q).trans ((hpE q).symm.trans
        ((hgE q (b + u) hEb hEq).symm)))) |>.trans (hEs u).symm)
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (eventually_mem_iff_of_regularOpen_of_off_cross
      hDsOpen hEsOpen hDsReg hEsReg hoff)
  refine ⟨r, hr, ?_⟩
  intro u hu
  exact (hDs u).symm.trans ((hlocal hu).trans (hEs u))

private theorem quadrantGerm_membership :
    ∀ {D E : Set Tiling.Plane} {a b : Tiling.Plane}, IsOpen D → IsOpen E →
      interior (closure D) = D → interior (closure E) = E →
      IsLocallyAxisParallelPolygonal D → IsLocallyAxisParallelPolygonal E →
      (∀ q, SetOccupiesQuadrant D a q ↔ SetOccupiesQuadrant E b q) →
      ∃ r : ℝ, 0 < r ∧ ∀ u, dist u 0 < r → (a + u ∈ D ↔ b + u ∈ E) := by
  intro D E a b hDopen hEopen hDreg hEreg hDlocal hElocal hocc
  exact quadrantGerm_membership_of_cross hDopen hEopen hDreg hEreg
    (Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hDlocal a)
    (Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hElocal b) hocc

private theorem finiteLabels_regularSupportGerm_noPacking :
    ∀ (K : Region) (Q : Finset Tiling.Plane) (a : Tiling.Plane),
      supportGerm K Q a = {q | ∃ t ∈ Q, ∃ r : ℝ, 0 < r ∧
        Metric.ball a r ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier} := by
  intro K Q a
  have hopenUnion : IsOpen (openUnion K (Q : Set Tiling.Plane)) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
    exact isOpen_iUnion fun s => (Region.openCarrier_regularOpen K).1.vadd s.1
  have htileSub : ∀ t ∈ Q, t +ᵥ K.openCarrier ⊆
      regularSupport K (Q : Set Tiling.Plane) := by
    intro t ht z hz
    have hto : t +ᵥ K.openCarrier ⊆ openUnion K (Q : Set Tiling.Plane) := by
      intro w hw
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨t, ht⟩, hw⟩
    have hregular := interior_maximal (s := closure (openUnion K (Q : Set Tiling.Plane)))
      (t := t +ᵥ K.openCarrier) (hto.trans subset_closure)
      ((Region.openCarrier_regularOpen K).1.vadd t)
    exact hregular hz
  ext q
  constructor
  · intro hq
    change OccupiesQuadrant K (Q : Set Tiling.Plane) a q at hq
    obtain ⟨r₀, hr₀, hocc⟩ := hq
    obtain ⟨r₁, hr₁, hconst⟩ := finite_tiles_quadrant_constancy K Q a q
    let r := min r₀ r₁
    have hr : 0 < r := lt_min hr₀ hr₁
    let A : Set Tiling.Plane := Metric.ball a r ∩ quadrantAt q a
    have hAreg : A ⊆ regularSupport K (Q : Set Tiling.Plane) := by
      intro z hz
      exact hocc (inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
        Set.Subset.rfl hz)
    by_cases hex : ∃ t ∈ Q, A ⊆ t +ᵥ K.openCarrier
    · obtain ⟨t, ht, htA⟩ := hex
      exact ⟨t, ht, r, hr, htA⟩
    · have hdisj : ∀ t ∈ Q, Disjoint A (t +ᵥ K.openCarrier) := by
        intro t ht
        rcases hconst t ht with h | h
        · exfalso
          apply hex
          exact ⟨t, ht, fun z hz => h
            (inter_subset_inter (Metric.ball_subset_ball (min_le_right _ _))
              Set.Subset.rfl hz)⟩
        · exact h.mono_left (inter_subset_inter
            (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl)
      have hAopen : IsOpen A := by
        apply Metric.isOpen_ball.inter
        cases q
        · exact (isOpen_lt Complex.continuous_re continuous_const).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        · exact (isOpen_lt continuous_const Complex.continuous_re).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        · exact (isOpen_lt Complex.continuous_re continuous_const).inter
            (isOpen_lt continuous_const Complex.continuous_im)
        · exact (isOpen_lt continuous_const Complex.continuous_re).inter
            (isOpen_lt continuous_const Complex.continuous_im)
      have hAunion : Disjoint A (openUnion K (Q : Set Tiling.Plane)) := by
        apply Set.disjoint_left.2
        intro z hzA hzU
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzU
        obtain ⟨s, hzs⟩ := hzU
        exact Set.disjoint_left.mp (hdisj s s.2) hzA hzs
      have hAnotreg : Disjoint A (regularSupport K (Q : Set Tiling.Plane)) := by
        apply Set.disjoint_left.2
        intro z hzA hzreg
        change z ∈ interior (closure (openUnion K (Q : Set Tiling.Plane))) at hzreg
        have hzcl : z ∈ closure (openUnion K (Q : Set Tiling.Plane)) :=
          interior_subset hzreg
        obtain ⟨w, hwA, hwU⟩ := mem_closure_iff.mp hzcl A hAopen hzA
        exact Set.disjoint_left.mp hAunion hwA hwU
      obtain ⟨z, hz⟩ := quadrant_ball_nonempty hr q
      exact False.elim (Set.disjoint_left.mp hAnotreg hz (hAreg hz))
  · intro hq
    change (∃ t ∈ Q, ∃ r : ℝ, 0 < r ∧
      Metric.ball a r ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier) at hq
    change OccupiesQuadrant K (Q : Set Tiling.Plane) a q
    rcases hq with ⟨t, ht, r, hr, hsub⟩
    exact ⟨r, hr, hsub.trans (htileSub t ht)⟩

private theorem finiteLabels_regularSupportGerm :
    ∀ (K : Region) (Q : Finset Tiling.Plane) (a : Tiling.Plane),
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements Q) →
      supportGerm K Q a = {q | ∃ t ∈ Q, ∃ r : ℝ, 0 < r ∧
        Metric.ball a r ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier} := by
  intro K Q a _hpacking
  exact finiteLabels_regularSupportGerm_noPacking K Q a

private theorem finiteIncidentLabels_exists
    (C : ApproximationContext.{u}) (S : Set ↥C.centres)
    (a : ↥C.translatedVertices) (hFLC : HasFLC C.centres) :
    ∃ labels : Finset ↥C.centres, ∀ t, t ∈ labels ↔
      t ∈ S ∧ (a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support := by
  classical
  obtain ⟨R, hR⟩ := C.region.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let R' := max R 1
  have hRpos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let Q : Set Tiling.Plane := Metric.closedBall (a : Tiling.Plane) R'
  have hQbounded : Bornology.IsBounded Q := Metric.isBounded_closedBall
  have hfinite : (C.centres ∩ Q).Finite := by
    exact hFLC.1 Q hQbounded
  have hpre : ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹' (C.centres ∩ Q)).Finite := by
    apply hfinite.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  let B : Finset ↥C.centres := hpre.toFinset
  have hB : ∀ t, t ∈ B ↔ (t : Tiling.Plane) ∈ Q := by
    intro t
    rw [show t ∈ B ↔ t ∈ ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹'
      (C.centres ∩ Q)) from hpre.mem_toFinset]
    simp [Q]
  let labels : Finset ↥C.centres := B.filter
    (fun t => t ∈ S ∧ (a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support)
  refine ⟨labels, ?_⟩
  intro t
  constructor
  · intro ht
    exact (Finset.mem_filter.mp ht).2
  · intro ht
    apply Finset.mem_filter.mpr
    refine ⟨?_, ht⟩
    apply (hB t).2
    rcases ht.2 with ⟨w, hw, hwa⟩
    change (t : Tiling.Plane) + w = (a : Tiling.Plane) at hwa
    rw [Metric.mem_closedBall]
    have hdist : dist (t : Tiling.Plane) (a : Tiling.Plane) = dist w 0 := by
      rw [← hwa]
      simp [dist_eq_norm]
    rw [hdist]
    have hwR := hR hw
    rw [Metric.mem_closedBall, dist_comm] at hwR
    exact le_trans (by simpa [dist_comm] using hwR) (le_max_left _ _)

private theorem imageAnchorCandidateSet_exists :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (a : ↥C.translatedVertices),
      Nonempty (ImageAnchorCandidateSet C phi D Tphi a) := by
  intro C P hScale phi hphi D Tphi hTphi a
  classical
  let d : ℝ := Metric.diam C.region.openCarrier
  have hd : Metric.diam C.region.support = d := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    calc
      Metric.diam C.region.support =
          Metric.diam (closure (interior C.region.support)) := by
            rw [C.region.isPolygonal.closure_interior]
      _ = Metric.diam (interior C.region.support) := Metric.diam_closure _
  have hdscale : Metric.diam C.region.support < P.scale := by
    rw [hd]
    change 10 * (d + 1) < P.scale at hScale
    have hdnonneg : 0 ≤ d := Metric.diam_nonneg
    linarith
  have hdiam := deformedRegion_diam_le_add_localError P hphi D hdscale
  have hscale10 : 10 < P.scale := by
    have hdp : 0 ≤ d := Metric.diam_nonneg
    linarith
  have hlocal_lt_one : P.localError < 1 := by
    rw [P.localError_eq]
    have hspos : 0 < P.scale := P.scale_pos
    apply (inv_lt_one₀ hspos).2
    linarith
  have hdiam_lt_half : Metric.diam D.deformedRegion.support + 1 < P.scale / 2 := by
    have hdnonneg : 0 ≤ d := Metric.diam_nonneg
    have hdiam' : Metric.diam D.deformedRegion.support ≤ d + P.localError := by
      rw [← hd]
      exact hdiam
    linarith
  let b : ↥C.translatedVertices :=
    ⟨(a : Tiling.Plane), a.2⟩
  have hbmap : mapTranslatedVertex phi b = mapTranslatedVertex phi a := by rfl
  let ball : Set ↥C.centres := {t | dist (t : Tiling.Plane) (a : Tiling.Plane) ≤ P.scale}
  have hball_finite : ball.Finite := by
    let Q : Set Tiling.Plane := Metric.closedBall (a : Tiling.Plane) P.scale
    have hQ : Bornology.IsBounded Q := Metric.isBounded_closedBall
    have hfinite : (C.centres ∩ Q).Finite := P.source_hasFLC.1 Q hQ
    have himage : ((fun t : ↥C.centres => (t : Tiling.Plane)) '' ball) = C.centres ∩ Q := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨t.2, by simpa [ball, Q, Metric.mem_closedBall] using ht⟩
      · rintro ⟨hzC, hzQ⟩
        let t : ↥C.centres := ⟨z, hzC⟩
        refine ⟨t, ?_, rfl⟩
        simpa [ball, Q, Metric.mem_closedBall] using hzQ
    have hpre : (fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹' (C.centres ∩ Q) = ball := by
      ext t
      simp [ball, Q, Metric.mem_closedBall, dist_comm]
    rw [← hpre]
    apply hfinite.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  let candidates : Finset ↥C.centres := hball_finite.toFinset
  have hcandidates : ∀ t, t ∈ candidates ↔ t ∈ ball := by
    intro t
    exact hball_finite.mem_toFinset
  refine ⟨⟨P.scale, P.scale_pos, candidates, ?_, ?_⟩⟩
  · intro t
    rw [hcandidates]
    rfl
  · intro t ht
    obtain ⟨z, hzball, hztile⟩ := ht
    rcases hztile with ⟨w, hwopen, hzw⟩
    have hwsupport : w ∈ D.deformedRegion.support := interior_subset hwopen
    have hzsupport : z ∈ Tphi t +ᵥ D.deformedRegion.support := by
      exact ⟨w, hwsupport, hzw⟩
    have hzero : (0 : Tiling.Plane) ∈ D.deformedRegion.support := by
      have hv : (0 : Tiling.Plane) ∈ D.deformedRegion.vertices := by
        rw [D.vertices_image]
        have hvsrc : (0 : Tiling.Plane) ∈ C.region.vertices := C.zero_mem_vertices
        refine ⟨(0 : Tiling.Plane), hvsrc, ?_⟩
        rw [D.vertex_agreement 0 hvsrc]
        have hp : C.vertexPoint 0 hvsrc =
            ⟨(0 : Tiling.Plane), C.coordinateSpace.zero_mem,
              C.coordinateSpace.zero_mem⟩ := by rfl
        rw [hp]
        simp only [mapPoint, mapScalar]
        change ((phi ⟨(0 : ℝ), _⟩ : ℚ) : ℝ) +
          ((phi ⟨(0 : ℝ), _⟩ : ℚ) : ℝ) * Complex.I = 0
        have hφzero : ∀ (h : (0 : ℝ) ∈ C.coordinateSpace),
            phi ⟨0, h⟩ = 0 := by
          intro h
          have hz : (⟨0, h⟩ : C.coordinateSpace) = 0 := by
            apply Subtype.ext
            simp
          rw [hz, map_zero]
        rw [hφzero C.coordinateSpace.zero_mem]
        simp
      rw [← D.deformedRegion.isPolygonal.closure_interior]
      exact frontier_subset_closure
        (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion hv)
    have hztileDist : dist (Tphi t) z ≤ Metric.diam D.deformedRegion.support := by
      calc
        dist (Tphi t) z = dist (0 : Tiling.Plane) w := by
          change Tphi t + w = z at hzw
          rw [← hzw]
          simp [dist_eq_norm]
        _ ≤ Metric.diam D.deformedRegion.support :=
          Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded hzero hwsupport
    have himage : dist (mapTranslatedVertex phi a) (Tphi t) < P.scale / 2 := by
      have hzdist : dist (mapTranslatedVertex phi a) z < 1 := by
        simpa only [Metric.mem_ball, dist_comm] using hzball
      have htri := dist_triangle (mapTranslatedVertex phi a) z (Tphi t)
      rw [dist_comm z (Tphi t)] at htri
      linarith
    let b : ↥C.translatedVertices :=
      ⟨(t : Tiling.Plane), by
        exact ⟨0, C.zero_mem_vertices, t, t.2, zero_add (t : Tiling.Plane)⟩⟩
    have hbmap : mapTranslatedVertex phi b = Tphi t := by
      change mapPoint phi (C.translatedVertexPoint b) = _
      rw [hTphi t]
      congr 1
    have hsource := P.coarse_inverse phi hphi a b (by simpa [hbmap] using himage)
    have hsource' : dist (a : Tiling.Plane) (t : Tiling.Plane) < P.scale := by
      simpa [b] using hsource
    have : t ∈ ball := by
      simpa [ball, dist_comm] using (le_of_lt hsource')
    exact (hcandidates t).2 this

private theorem controlledGermLabels_exists :
    ∀ (C : ApproximationContext.{u}) (S : Set ↥C.centres)
      (a : ↥C.translatedVertices),
      (a : Tiling.Plane) ∈ C.region.vertices + Set.image Subtype.val S →
      HasFLC C.centres → Nonempty (ControlledGermLabels C S a) := by
  intro C S a ha hFLC
  classical
  obtain ⟨R, hR⟩ := C.region.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let R' : ℝ := max R 1 + 1
  let Q : Set Tiling.Plane := Metric.closedBall (a : Tiling.Plane) R'
  have hQbounded : Bornology.IsBounded Q := Metric.isBounded_closedBall
  have hfinite : (C.centres ∩ Q).Finite := hFLC.1 Q hQbounded
  have hpre : ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹'
      (C.centres ∩ Q)).Finite := by
    apply hfinite.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  let B : Finset ↥C.centres := hpre.toFinset
  have hB : ∀ t, t ∈ B ↔ (t : Tiling.Plane) ∈ Q := by
    intro t
    rw [show t ∈ B ↔ t ∈ ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹'
      (C.centres ∩ Q)) from hpre.mem_toFinset]
    simp [Q]
  let labels : Finset ↥C.centres := B.filter
    (fun t => t ∈ S ∧ (a : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support)
  have hlabels : ∀ t, t ∈ labels ↔ t ∈ S ∧ (a : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support := by
    intro t
    constructor
    · intro ht
      exact (Finset.mem_filter.mp ht).2
    · intro ht
      apply Finset.mem_filter.mpr
      refine ⟨?_, ht⟩
      apply (hB t).2
      rcases ht.2 with ⟨w, hw, hwa⟩
      change (t : Tiling.Plane) + w = (a : Tiling.Plane) at hwa
      rw [Metric.mem_closedBall]
      have hdist : dist (t : Tiling.Plane) (a : Tiling.Plane) = dist w 0 := by
        rw [← hwa]
        simp [dist_eq_norm]
      rw [hdist]
      have hwR := hR hw
      rw [Metric.mem_closedBall, dist_comm] at hwR
      exact le_trans (by simpa [dist_comm] using hwR)
        (by linarith [le_max_left R 1])
  let L : Finset Tiling.Plane := labels.image (fun t : ↥C.centres =>
    (t : Tiling.Plane))
  let U : Set Tiling.Plane := openUnion C.region (Set.image Subtype.val S)
  let V : Set Tiling.Plane := openUnion C.region (L : Set Tiling.Plane)
  let N : Finset ↥C.centres := B.filter
    (fun t => t ∈ S ∧ t ∉ labels)
  have hNnot : ∀ t ∈ N, (a : Tiling.Plane) ∉
      (t : Tiling.Plane) +ᵥ C.region.support := by
    intro t ht hta
    have hts : t ∈ S := (Finset.mem_filter.mp ht).2.1
    have htl : t ∈ labels := (hlabels t).2 ⟨hts, hta⟩
    exact (Finset.mem_filter.mp ht).2.2 htl
  obtain ⟨rs, hrs, hrsle, hsep⟩ := finite_closed_supports_separation
    (a : Tiling.Plane) N (fun t => (t : Tiling.Plane) +ᵥ C.region.support)
    (by
      intro t ht
      exact (C.region.isPolygonal.isClosed.vadd (t : Tiling.Plane)))
    (by
      intro t ht
      exact hNnot t ht)
  let r0 : ℝ := min 1 rs
  have hr0 : 0 < r0 := lt_min one_pos hrs
  have hUV : ∀ z ∈ Metric.ball (a : Tiling.Plane) r0, z ∈ U ↔ z ∈ V := by
    intro z hz
    constructor
    · intro hzU
      change z ∈ openUnion C.region (Set.image Subtype.val S) at hzU
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzU
      obtain ⟨t, hzt⟩ := hzU
      rcases Set.mem_vadd_set.mp hzt with ⟨w, hwopen, hzw⟩
      obtain ⟨s, hsS, hst⟩ := t.property
      have hzt' : (s : Tiling.Plane) + w = z := by
        simpa [hst] using hzw
      have hsB : s ∈ B := by
        apply (hB s).2
        rw [Metric.mem_closedBall]
        have hwsupport : w ∈ C.region.support := interior_subset hwopen
        have hwR := hR hwsupport
        rw [Metric.mem_closedBall, dist_comm] at hwR
        have hsub : (s : Tiling.Plane) = z - w := by
          calc
            (s : Tiling.Plane) = ((s : Tiling.Plane) + w) - w := by
              simp [sub_eq_add_neg, add_assoc]
            _ = z - w := by rw [hzt']
        have hdist : dist (s : Tiling.Plane) (a : Tiling.Plane) ≤
            dist w 0 + dist z (a : Tiling.Plane) := by
          calc
            dist (s : Tiling.Plane) (a : Tiling.Plane) =
                dist (z - w) (a : Tiling.Plane) := by rw [hsub]
            _ ≤ dist (z - w) z + dist z (a : Tiling.Plane) :=
              dist_triangle _ _ _
            _ = dist w 0 + dist z (a : Tiling.Plane) := by
              congr 1
              simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm]
        have hz' : dist z (a : Tiling.Plane) < r0 := by
          simpa [Metric.mem_ball, dist_comm] using hz
        have hwR' : dist w 0 ≤ R := by simpa [dist_comm] using hwR
        have hr0le : r0 ≤ 1 := min_le_left _ _
        have hR' : R + 1 ≤ R' := by
          dsimp [R']
          linarith [le_max_left R 1]
        linarith [hwR', hdist]
      by_cases hslabels : s ∈ labels
      · change z ∈ openUnion C.region (L : Set Tiling.Plane)
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨(s : Tiling.Plane), Finset.mem_coe.mpr
          (Finset.mem_image.mpr ⟨s, hslabels, rfl⟩)⟩,
          Set.mem_vadd_set.mpr ⟨w, hwopen, by simp [vadd_eq_add, hzt']⟩⟩
      · have hsN : s ∈ N := by
          apply Finset.mem_filter.mpr
          exact ⟨hsB, hsS, hslabels⟩
        have hzrs : z ∈ Metric.ball (a : Tiling.Plane) rs :=
          Metric.ball_subset_ball (min_le_right _ _) hz
        have hzsupport : z ∈ (s : Tiling.Plane) +ᵥ C.region.support :=
          Set.mem_vadd_set.mpr ⟨w, interior_subset hwopen,
            by simp [vadd_eq_add, hzt']⟩
        exact False.elim (Set.disjoint_left.mp (hsep s hsN) hzrs hzsupport)
    · intro hzV
      change z ∈ openUnion C.region (L : Set Tiling.Plane) at hzV
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzV
      obtain ⟨t, hzt⟩ := hzV
      rcases Set.mem_vadd_set.mp hzt with ⟨w, hwopen, hzw⟩
      obtain ⟨s, hslabels, hst⟩ := Finset.mem_image.mp t.property
      have hsS : s ∈ S := (hlabels s).1 hslabels |>.1
      have hzt' : (s : Tiling.Plane) + w = z := by
        simpa [hst] using hzw
      change z ∈ openUnion C.region (Set.image Subtype.val S)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨(s : Tiling.Plane), ⟨s, hsS, rfl⟩⟩,
        Set.mem_vadd_set.mpr ⟨w, hwopen, hzt'⟩⟩
  obtain ⟨rlocal, hrlocal, hreg⟩ :=
    regularSupport_local_eq_of_openUnion_eq_on_ball hr0 hUV
  have hlocalGerm : supportGerm C.region (Set.image Subtype.val S) a =
      supportGerm C.region (L : Set Tiling.Plane) a := by
    ext q
    constructor
    · intro hq
      rcases hq with ⟨r, hr, hsub⟩
      refine ⟨min r rlocal, lt_min hr hrlocal, ?_⟩
      intro y hy
      have hylocal : y ∈ Metric.ball (a : Tiling.Plane) rlocal :=
        Metric.ball_subset_ball (min_le_right _ _) hy.1
      apply (hreg y hylocal).mp
      exact hsub ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
    · intro hq
      rcases hq with ⟨r, hr, hsub⟩
      refine ⟨min r rlocal, lt_min hr hrlocal, ?_⟩
      intro y hy
      have hylocal : y ∈ Metric.ball (a : Tiling.Plane) rlocal :=
        Metric.ball_subset_ball (min_le_right _ _) hy.1
      apply (hreg y hylocal).mpr
      exact hsub ⟨Metric.ball_subset_ball (min_le_left _ _) hy.1, hy.2⟩
  refine ⟨⟨labels, hlabels, ?_⟩⟩
  intro q
  rw [hlocalGerm]
  rw [finiteLabels_regularSupportGerm_noPacking]
  constructor
  · rintro ⟨t, ht, r, hr, hsub⟩
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp ht
    refine ⟨s, hs, r, hr, ?_⟩
    simpa [hst] using hsub
  · rintro ⟨s, hs, r, hr, hsub⟩
    refine ⟨(s : Tiling.Plane), Finset.mem_image.mpr ⟨s, hs, rfl⟩,
      r, hr, hsub⟩

private theorem sourceCandidateSet_exists
    (C : ApproximationContext.{u}) (hFLC : HasFLC C.centres)
    (a : ↥C.translatedVertices) :
    ∃ B : Finset ↥C.centres, ∀ t : ↥C.centres,
      (Metric.ball (a : Tiling.Plane) 1 ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty → t ∈ B := by
  classical
  obtain ⟨R, hR⟩ := C.region.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let R' : ℝ := max R 1 + 1
  let Q : Set Tiling.Plane := Metric.closedBall (a : Tiling.Plane) R'
  have hQbounded : Bornology.IsBounded Q := Metric.isBounded_closedBall
  have hfinite : (C.centres ∩ Q).Finite := hFLC.1 Q hQbounded
  have hpre : ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹'
      (C.centres ∩ Q)).Finite := by
    apply hfinite.preimage
    intro x hx y hy hxy
    exact Subtype.ext hxy
  let B : Finset ↥C.centres := hpre.toFinset
  have hB : ∀ t, t ∈ B ↔ (t : Tiling.Plane) ∈ Q := by
    intro t
    rw [show t ∈ B ↔ t ∈ ((fun t : ↥C.centres => (t : Tiling.Plane)) ⁻¹'
      (C.centres ∩ Q)) from hpre.mem_toFinset]
    simp [Q]
  refine ⟨B, ?_⟩
  intro t hmeet
  apply (hB t).2
  obtain ⟨z, hzball, hztile⟩ := hmeet
  obtain ⟨w, hwopen, hzw⟩ := Set.mem_vadd_set.mp hztile
  have hwsupport : w ∈ C.region.support := interior_subset hwopen
  have hwR := hR hwsupport
  rw [Metric.mem_closedBall, dist_comm] at hwR
  have hdist : dist (t : Tiling.Plane) (a : Tiling.Plane) ≤
      dist w 0 + dist z (a : Tiling.Plane) := by
    have hsub : (t : Tiling.Plane) = z - w := by
      calc
        (t : Tiling.Plane) = ((t : Tiling.Plane) + w) - w := by
          simp [sub_eq_add_neg, add_assoc]
        _ = z - w := by
          have hzw' : (t : Tiling.Plane) + w = z := by
            simpa [vadd_eq_add] using hzw
          rw [hzw']
    calc
      dist (t : Tiling.Plane) (a : Tiling.Plane) =
          dist (z - w) (a : Tiling.Plane) := by rw [hsub]
      _ ≤ dist (z - w) z + dist z (a : Tiling.Plane) := dist_triangle _ _ _
      _ = dist w 0 + dist z (a : Tiling.Plane) := by
        congr 1
        simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm]
  have hz' : dist z (a : Tiling.Plane) < 1 := by
    simpa [Metric.mem_ball, dist_comm] using hzball
  have hwR' : dist w 0 ≤ R := by simpa [dist_comm] using hwR
  have hR' : R + 1 ≤ R' := by
    dsimp [R']
    linarith [le_max_left R 1]
  rw [Metric.mem_closedBall]
  linarith

private theorem translatedVertex_coordinateSigns_transport
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (v : ↥C.region.vertices)
    (t : ↥C.centres)
    (hnear : dist (a : Tiling.Plane)
      ((v : Tiling.Plane) + (t : Tiling.Plane)) < P.controlRadius)
    (axis : Axis) :
    Real.sign (Axis.coord axis
      (mapTranslatedVertex phi a -
        (mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t))) =
      Real.sign (Axis.coord axis
        ((a : Tiling.Plane) - ((v : Tiling.Plane) + (t : Tiling.Plane)))) ∧
    (Axis.coord axis
      (mapTranslatedVertex phi a -
        (mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t)) = 0 ↔
      Axis.coord axis
        ((a : Tiling.Plane) - ((v : Tiling.Plane) + (t : Tiling.Plane))) = 0) := by
  obtain ⟨b, hbval, hbmap⟩ := mapTranslatedVertex_add_local phi v t
  have hnear' : dist (a : Tiling.Plane) (b : Tiling.Plane) < P.controlRadius := by
    simpa [hbval] using hnear
  have hsign := deformation_reflectsFiniteValues P phi hphi axis a b a b hnear' hnear'
  have hbmap' : mapTranslatedVertex phi b =
      mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t := by
    simpa [hTphi t] using hbmap
  have hbval' : (b : Tiling.Plane) =
      (v : Tiling.Plane) + (t : Tiling.Plane) := hbval
  constructor
  · rw [← hbmap', ← hbval']
    exact hsign.1
  · rw [← hbmap', ← hbval']
    exact hsign.2.1

private theorem tileVertex_near_translatedAnchor
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (a : ↥C.translatedVertices) (t : ↥C.centres) (_q : Quadrant)
    (ha : (a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support)
    (v : ↥C.region.vertices) :
    dist (a : Tiling.Plane)
        ((v : Tiling.Plane) + (t : Tiling.Plane)) < P.controlRadius := by
  have hv : (v : Tiling.Plane) + (t : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support := by
    exact Set.mem_vadd_set.mpr ⟨v, vertex_mem_support_local v.2, by
      simp [vadd_eq_add, add_comm]⟩
  have hdiam : Metric.diam C.region.support =
      Metric.diam C.region.openCarrier := diam_support_eq_openCarrier_local C.region
  obtain ⟨w, hw, hwa⟩ := Set.mem_vadd_set.mp ha
  have hdist0 := Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hw
    (vertex_mem_support_local v.2)
  have hdist : dist (a : Tiling.Plane)
      ((v : Tiling.Plane) + (t : Tiling.Plane)) ≤
      Metric.diam C.region.support := by
    calc
      dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) =
          dist w (v : Tiling.Plane) := by
            rw [← hwa]
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            simp only [vadd_eq_add]
            abel
      _ ≤ Metric.diam C.region.support := hdist0
  rw [hdiam] at hdist
  have hscale : Metric.diam C.region.openCarrier < P.scale := by
    nlinarith [hScale, (Metric.diam_nonneg :
      0 ≤ Metric.diam C.region.openCarrier)]
  exact lt_of_le_of_lt hdist (lt_trans hscale P.scale_lt_controlRadius)

private theorem finite_add_sign_stability (F : Finset ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ F, x ≠ 0 →
      ∀ y : ℝ, |y| < δ → Real.sign (x + y) = Real.sign x := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      refine ⟨1, one_pos, ?_⟩
      simp
  | @insert x F hxF ih =>
      obtain ⟨δF, hδF, hF⟩ := ih
      by_cases hx0 : x = 0
      · refine ⟨min δF 1, lt_min hδF one_pos, ?_⟩
        intro z hz hz0 y hy
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact False.elim (hz0 hx0)
        · exact hF z hz hz0 y (lt_of_lt_of_le hy (min_le_left _ _))
      · let δx : ℝ := |x| / 2
        have hδx : 0 < δx := by
          dsimp [δx]
          exact div_pos (abs_pos.mpr hx0) (by norm_num)
        refine ⟨min δF δx, lt_min hδF hδx, ?_⟩
        intro z hz hz0 y hy
        simp only [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · have hyx : |y| < δx := lt_of_lt_of_le hy (min_le_right _ _)
          have hy' : -δx < y ∧ y < δx := abs_lt.mp hyx
          rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
          · have hsum : z + y < 0 := by
              dsimp [δx] at hy' ⊢
              rw [abs_of_neg hxneg] at hy'
              linarith
            rw [Real.sign_of_neg hsum, Real.sign_of_neg hxneg]
          · have hsum : 0 < z + y := by
              dsimp [δx] at hy' ⊢
              rw [abs_of_pos hxpos] at hy'
              linarith
            rw [Real.sign_of_pos hsum, Real.sign_of_pos hxpos]
        · exact hF z hz hz0 y (lt_of_lt_of_le hy (min_le_left _ _))

private theorem finite_vertex_coordinate_stability
    (K : Region) (x : Tiling.Plane) (axis : Axis) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ K.vertices,
      Axis.coord axis (x - v) ≠ 0 → ∀ u : Tiling.Plane,
        |Axis.coord axis u| < δ →
          Real.sign (Axis.coord axis ((x + u) - v)) =
            Real.sign (Axis.coord axis (x - v)) := by
  classical
  let F : Finset ℝ := K.vertexFinset.image (fun v : Tiling.Plane =>
    Axis.coord axis (x - v))
  obtain ⟨δ, hδ, hF⟩ := finite_add_sign_stability F
  refine ⟨δ, hδ, ?_⟩
  intro v hv hzero u hu
  have hvfin : (v : Tiling.Plane) ∈ K.vertexFinset := by
    change (v : Tiling.Plane) ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset]
    exact hv
  have hmem : Axis.coord axis (x - (v : Tiling.Plane)) ∈ F := by
    exact Finset.mem_image.mpr ⟨(v : Tiling.Plane), hvfin, rfl⟩
  have hsign := hF _ hmem hzero (Axis.coord axis u) hu
  have hadd : Axis.coord axis ((x + u) - (v : Tiling.Plane)) =
      Axis.coord axis (x - (v : Tiling.Plane)) + Axis.coord axis u := by
    cases axis <;> simp [Axis.coord, sub_eq_add_neg, add_assoc,
      add_comm, add_left_comm]
  rw [hadd]
  exact hsign

private theorem sameVertexGridCell_of_coordinate_sign
    {K : Region} {x y : Tiling.Plane}
    (hx : OffVertexCoordinateGrid K x) (hy : OffVertexCoordinateGrid K y)
    (hsign : ∀ v ∈ K.vertices,
      Real.sign (Axis.coord Axis.horizontal (x - v)) =
          Real.sign (Axis.coord Axis.horizontal (y - v)) ∧
        Real.sign (Axis.coord Axis.vertical (x - v)) =
          Real.sign (Axis.coord Axis.vertical (y - v))) :
    SameVertexGridCell K x y := by
  have hneg (p q : ℝ) (hp : p < 0) (hq : q ≠ 0)
      (heq : Real.sign p = Real.sign q) : q < 0 := by
    rcases lt_or_gt_of_ne hq with hq | hq
    · exact hq
    · rw [Real.sign_of_neg hp, Real.sign_of_pos hq] at heq
      norm_num at heq
  have hpos (p q : ℝ) (hp : 0 < p) (hq : q ≠ 0)
      (heq : Real.sign p = Real.sign q) : 0 < q := by
    rcases lt_or_gt_of_ne hq with hq | hq
    · rw [Real.sign_of_pos hp, Real.sign_of_neg hq] at heq
      norm_num at heq
    · exact hq
  constructor
  · intro v hv
    have hsgn := hsign v hv
    constructor
    · intro hxy
      have hq : (y - v).re ≠ 0 := by
        exact sub_ne_zero.mpr (hy v hv).1
      have hqneg := hneg ((x - v).re) ((y - v).re) (by simpa using sub_neg.mpr hxy)
        hq (by simpa [Axis.coord] using hsgn.1)
      simpa only [Complex.sub_re] using (sub_neg.mp hqneg)
    · intro hyx
      have hp : (x - v).re ≠ 0 := by
        exact sub_ne_zero.mpr (hx v hv).1
      have hqneg := hneg ((y - v).re) ((x - v).re) (by simpa using sub_neg.mpr hyx)
        hp (by simpa [Axis.coord] using hsgn.1.symm)
      simpa only [Complex.sub_re] using (sub_neg.mp hqneg)
  · intro v hv
    have hsgn := hsign v hv
    constructor
    · intro hxy
      have hq : (y - v).im ≠ 0 := by
        exact sub_ne_zero.mpr (hy v hv).2
      have hqneg := hneg ((x - v).im) ((y - v).im) (by simpa using sub_neg.mpr hxy)
        hq (by simpa [Axis.coord] using hsgn.2)
      simpa only [Complex.sub_im] using (sub_neg.mp hqneg)
    · intro hyx
      have hp : (x - v).im ≠ 0 := by
        exact sub_ne_zero.mpr (hx v hv).2
      have hqneg := hneg ((y - v).im) ((x - v).im) (by simpa using sub_neg.mpr hyx)
        hp (by simpa [Axis.coord] using hsgn.2.symm)
      simpa only [Complex.sub_im] using (sub_neg.mp hqneg)

private theorem quadrantDisplacement
    (q : Quadrant) {a b z : Tiling.Plane}
    (hz : z ∈ quadrantAt q b) :
    b + (z - b) = z ∧ a + (z - b) ∈ quadrantAt q a := by
  constructor
  · abel
  · cases q <;> dsimp [quadrantAt] at hz ⊢ <;>
      constructor <;> linarith

private theorem sourceIncidentLabels_isolated
    {C : ApproximationContext.{u}} (S : Set ↥C.centres)
    (a : ↥C.translatedVertices) (G : ControlledGermLabels C S a)
    (B : Finset ↥C.centres)
    (hcover : ∀ t, t ∈ S →
      (Metric.ball (a : Tiling.Plane) 1 ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty → t ∈ B) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ t ∈ S,
        (Metric.ball (a : Tiling.Plane) r ∩
          ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty → t ∈ G.labels := by
  classical
  let N : Finset ↥C.centres := B.filter
    (fun t => t ∈ S ∧ t ∉ G.labels)
  have hNnot : ∀ t ∈ N, (a : Tiling.Plane) ∉
      (t : Tiling.Plane) +ᵥ C.region.support := by
    intro t ht hta
    have htS : t ∈ S := (Finset.mem_filter.mp ht).2.1
    have htlabels : t ∈ G.labels := (G.labels_spec t).2 ⟨htS, hta⟩
    exact (Finset.mem_filter.mp ht).2.2 htlabels
  obtain ⟨r, hr, hr1, hsep⟩ := finite_closed_supports_separation
    (a : Tiling.Plane) N (fun t => (t : Tiling.Plane) +ᵥ C.region.support)
    (by
      intro t ht
      exact C.region.isPolygonal.isClosed.vadd (t : Tiling.Plane))
    (by
      intro t ht
      exact hNnot t ht)
  refine ⟨r, hr, hr1, ?_⟩
  intro t htS hmeet
  by_contra htlabels
  have htB : t ∈ B := by
    apply hcover t htS
    obtain ⟨z, hzball, hzopen⟩ := hmeet
    refine ⟨z, Metric.ball_subset_ball hr1 hzball, hzopen⟩
  have htN : t ∈ N := Finset.mem_filter.mpr ⟨htB, htS, htlabels⟩
  obtain ⟨z, hzball, hzopen⟩ := hmeet
  have hzsupport : z ∈ (t : Tiling.Plane) +ᵥ C.region.support := by
    obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzopen
    exact Set.mem_vadd_set.mpr ⟨w, interior_subset hw, hzw⟩
  exact Set.disjoint_left.mp (hsep t htN) hzball hzsupport

private theorem imageIncidentLabels_isolated
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (a : ↥C.translatedVertices) (S : Set ↥C.centres)
    (G : ControlledGermLabels C S a)
    (Q : ImageAnchorCandidateSet C phi D Tphi a)
    (hnot : ∀ t ∈ Q.candidates, t ∈ S → t ∉ G.labels →
      mapTranslatedVertex phi a ∉ Tphi t +ᵥ D.deformedRegion.support) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ t ∈ S,
        (Metric.ball (mapTranslatedVertex phi a) r ∩
          (Tphi t +ᵥ D.deformedRegion.openCarrier)).Nonempty → t ∈ G.labels := by
  classical
  obtain ⟨r, hr, hr1, hsep⟩ :=
    finiteNonincidentImageSupports_separated_of_candidate_nonincident
      D Tphi a S G Q hnot
  refine ⟨r, hr, hr1, ?_⟩
  intro t htS hmeet
  by_contra htlabels
  have htQ : t ∈ Q.candidates := by
    apply Q.captures_unitBall t
    obtain ⟨z, hzball, hztile⟩ := hmeet
    refine ⟨z, Metric.ball_subset_ball hr1 hzball, hztile⟩
  obtain ⟨z, hzball, hzopen⟩ := hmeet
  have hzsupport : z ∈ Tphi t +ᵥ D.deformedRegion.support := by
    obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzopen
    exact Set.mem_vadd_set.mpr ⟨w, interior_subset hw, hzw⟩
  exact Set.disjoint_left.mp (hsep t htQ htS htlabels) hzball hzsupport

private theorem cross_region_grid_cell_membership
    {K L : Region} {x x' y y' : Tiling.Plane}
    (hx : OffVertexCoordinateGrid K x) (hx' : OffVertexCoordinateGrid K x')
    (hy : OffVertexCoordinateGrid L y) (hy' : OffVertexCoordinateGrid L y')
    (hK : SameVertexGridCell K x x')
    (hL : SameVertexGridCell L y y')
    (hbase : (x ∈ K.openCarrier ↔ y ∈ L.openCarrier)) :
    (x' ∈ K.openCarrier ↔ y' ∈ L.openCarrier) := by
  have hK' := sameVertexGridCell_openCarrier_iff K x x' hx hx' hK
  have hL' := sameVertexGridCell_openCarrier_iff L y y' hy hy' hL
  exact hK'.symm.trans (hbase.trans hL')

private theorem strictMono_sub_sign
    {f : ℝ → ℝ} (hf : StrictMono f) (x y : ℝ) :
    Real.sign (f x - f y) = Real.sign (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp
  · rcases lt_or_gt_of_ne hxy with hxy | hxy
    · rw [Real.sign_of_neg (sub_neg.mpr hxy),
        Real.sign_of_neg (sub_neg.mpr (hf hxy))]
    · rw [Real.sign_of_pos (sub_pos.mpr hxy),
        Real.sign_of_pos (sub_pos.mpr (hf hxy))]

private theorem planarHomeomorph_coordinate_sign
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (x v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (axis : Axis) :
    Real.sign (Axis.coord axis
      (D.planarHomeomorph x - mapPoint phi (C.vertexPoint v hv))) =
      Real.sign (Axis.coord axis (x - v)) := by
  rw [← D.vertex_agreement v hv]
  cases axis
  · simpa [Axis.coord, D.planarHomeomorph_apply] using
      strictMono_sub_sign D.firstHomeomorph_strictMono x.re v.re
  · simpa [Axis.coord, D.planarHomeomorph_apply] using
      strictMono_sub_sign D.secondHomeomorph_strictMono x.im v.im


private theorem anchor_mem_translatedSupport_of_quadrant_wip
    {K : Region} (a t : Tiling.Plane) (q : Quadrant)
    {r : ℝ} (hr : 0 < r)
    (hsub : Metric.ball a r ∩ quadrantAt q a ⊆ t +ᵥ K.openCarrier) :
    a ∈ t +ᵥ K.support := by
  have hacl : a ∈ closure (t +ᵥ K.openCarrier) := by
    apply mem_closure_iff.2
    intro V hV haV
    obtain ⟨ε, hε, hVε⟩ := Metric.isOpen_iff.1 hV a haV
    obtain ⟨z, hzball, hzq⟩ := quadrant_ball_nonempty (lt_min hr hε) q
    refine ⟨z, hVε ?_, hsub ⟨Metric.ball_subset_ball (min_le_left _ _) hzball, hzq⟩⟩
    exact lt_of_lt_of_le (Metric.mem_ball.1 hzball) (min_le_right _ _)
  have hsubset : t +ᵥ K.openCarrier ⊆ t +ᵥ K.support := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hz
    exact Set.mem_vadd_set.mpr ⟨w, interior_subset hw, hzw⟩
  exact closure_minimal hsubset (K.isPolygonal.isClosed.vadd t) hacl

private theorem strictMono_sub_sign_wip
    {f : ℝ → ℝ} (hf : StrictMono f) (x y : ℝ) :
    Real.sign (f x - f y) = Real.sign (x - y) := by
  by_cases hxy : x = y
  · subst y
    simp
  · rcases lt_or_gt_of_ne hxy with hxy | hxy
    · rw [Real.sign_of_neg (sub_neg.mpr hxy),
        Real.sign_of_neg (sub_neg.mpr (hf hxy))]
    · rw [Real.sign_of_pos (sub_pos.mpr hxy),
        Real.sign_of_pos (sub_pos.mpr (hf hxy))]

private theorem planarHomeomorph_coordinate_sign_wip
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (x v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (axis : Axis) :
    Real.sign (Axis.coord axis
      (D.planarHomeomorph x - mapPoint phi (C.vertexPoint v hv))) =
      Real.sign (Axis.coord axis (x - v)) := by
  rw [← D.vertex_agreement v hv]
  cases axis
  · simpa [Axis.coord, D.planarHomeomorph_apply] using
      strictMono_sub_sign_wip D.firstHomeomorph_strictMono x.re v.re
  · simpa [Axis.coord, D.planarHomeomorph_apply] using
      strictMono_sub_sign_wip D.secondHomeomorph_strictMono x.im v.im

private theorem mapped_vertex_subtype_wip
    {C : ApproximationContext.{u}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) :
    ∃ w : ↥D.deformedRegion.vertices,
      (w : Tiling.Plane) = mapPoint phi (C.vertexPoint v hv) := by
  refine ⟨⟨mapPoint phi (C.vertexPoint v hv), ?_⟩, rfl⟩
  rw [D.vertices_image]
  exact ⟨v, hv, D.vertex_agreement v hv⟩

private theorem diam_support_eq_openCarrier_wip (K : Region) :
    Metric.diam K.support = Metric.diam K.openCarrier := by
  change Metric.diam K.support = Metric.diam (interior K.support)
  nth_rewrite 1 [← K.isPolygonal.closure_interior]
  exact Metric.diam_closure _

private theorem vertex_mem_support_wip {K : Region}
    {v : Tiling.Plane} (hv : v ∈ K.vertices) : v ∈ K.support := by
  rw [← K.isPolygonal.closure_interior]
  exact frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier K hv)

private theorem tileVertex_near_translatedAnchor_wip
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (a : ↥C.translatedVertices) (t : ↥C.centres) (_q : Quadrant)
    (ha : (a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support)
    (v : ↥C.region.vertices) :
    dist (a : Tiling.Plane)
        ((v : Tiling.Plane) + (t : Tiling.Plane)) < P.controlRadius := by
  have hv : (v : Tiling.Plane) + (t : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support := by
    exact Set.mem_vadd_set.mpr ⟨v, vertex_mem_support_wip v.2, by
      simp [vadd_eq_add, add_comm]⟩
  have hdiam : Metric.diam C.region.support =
      Metric.diam C.region.openCarrier := diam_support_eq_openCarrier_wip C.region
  obtain ⟨w, hw, hwa⟩ := Set.mem_vadd_set.mp ha
  have hdist0 := Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hw
    (vertex_mem_support_wip v.2)
  have hdist : dist (a : Tiling.Plane)
      ((v : Tiling.Plane) + (t : Tiling.Plane)) ≤
      Metric.diam C.region.support := by
    calc
      dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) =
          dist w (v : Tiling.Plane) := by
            rw [← hwa]
            rw [dist_eq_norm, dist_eq_norm]
            congr 1
            simp only [vadd_eq_add]
            abel
      _ ≤ Metric.diam C.region.support := hdist0
  rw [hdiam] at hdist
  have hscale : Metric.diam C.region.openCarrier < P.scale := by
    nlinarith [hScale, (Metric.diam_nonneg :
      0 ≤ Metric.diam C.region.openCarrier)]
  exact lt_of_le_of_lt hdist (lt_trans hscale P.scale_lt_controlRadius)

private theorem support_transport_of_local_grid_wip
    {K L : Region} {x y : Tiling.Plane} {r : ℝ}
    (hr : 0 < r)
    (hlocal : ∀ z, dist z x < r →
      ((OffVertexCoordinateGrid L (y + (z - x)) ↔
          OffVertexCoordinateGrid K z) ∧
        (OffVertexCoordinateGrid K z →
          (z ∈ K.openCarrier ↔ y + (z - x) ∈ L.openCarrier)))) :
    (x ∈ K.support ↔ y ∈ L.support) := by
  constructor
  · intro hx
    rw [support_eq_closure_openCarrier_offVertexGrid K] at hx
    rw [support_eq_closure_openCarrier_offVertexGrid L]
    apply mem_closure_iff.2
    intro V hV hyV
    obtain ⟨ε, hε, hVε⟩ := Metric.isOpen_iff.1 hV y hyV
    let δ := min r ε
    have hδ : 0 < δ := lt_min hr hε
    have hxδ : x ∈ Metric.ball x δ := Metric.mem_ball_self hδ
    obtain ⟨z, hzball, hzopen, hzoff⟩ := mem_closure_iff.1 hx
      (Metric.ball x δ) Metric.isOpen_ball hxδ
    have hzsmall : dist z x < r :=
      lt_of_lt_of_le (Metric.mem_ball.1 hzball) (min_le_left _ _)
    obtain ⟨hzoff', hzmem⟩ := hlocal z hzsmall
    have hzy : dist (y + (z - x)) y < ε := by
      have hzd := Metric.mem_ball.1 hzball
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm] using
        (lt_of_lt_of_le hzd (min_le_right _ _))
    refine ⟨y + (z - x), ⟨hVε hzy, ?_⟩⟩
    exact ⟨(hzmem hzoff).mp hzopen, hzoff'.mpr hzoff⟩
  · intro hy
    rw [support_eq_closure_openCarrier_offVertexGrid L] at hy
    rw [support_eq_closure_openCarrier_offVertexGrid K]
    apply mem_closure_iff.2
    intro V hV hxV
    obtain ⟨ε, hε, hVε⟩ := Metric.isOpen_iff.1 hV x hxV
    let δ := min r ε
    have hδ : 0 < δ := lt_min hr hε
    have hyδ : y ∈ Metric.ball y δ := Metric.mem_ball_self hδ
    obtain ⟨w, hwball, hwopen, hwoff⟩ := mem_closure_iff.1 hy
      (Metric.ball y δ) Metric.isOpen_ball hyδ
    have hwsmall : dist w y < r :=
      lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_left _ _)
    let z := x + (w - y)
    have hzx : dist z x < r := by
      have hwd := lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_left _ _)
      have heq : dist z x = dist w y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        dsimp [z]
        ring
      apply Metric.mem_ball.mpr
      apply Metric.mem_ball.mpr
      rw [heq]
      exact hwd
    have hzy : y + (z - x) = w := by
      dsimp [z]
      abel
    have hzoff : OffVertexCoordinateGrid K z := by
      have hlocal' := hlocal z hzx
      have htarget : OffVertexCoordinateGrid L (y + (z - x)) := by
        simpa [hzy] using hwoff
      exact hlocal'.1.mp htarget
    obtain ⟨_, hzmem⟩ := hlocal z hzx
    refine ⟨z, ⟨hVε ?_, ?_⟩⟩
    · have hwd := lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_right _ _)
      have heq : dist z x = dist w y := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        dsimp [z]
        ring
      apply Metric.mem_ball.mpr
      rw [heq]
      exact hwd
    · have hzopen : y + (z - x) ∈ L.openCarrier := by
        rw [hzy]
        exact hwopen
      exact ⟨(hzmem hzoff).mpr hzopen, hzoff⟩

private theorem offVertexGrid_of_ball_quadrant_wip
    (K : Region) (x : Tiling.Plane) (q : Quadrant) (r : ℝ)
    (_hr : 0 < r)
    (hstable : ∀ (axis : Axis) (v : Tiling.Plane), v ∈ K.vertices →
      Axis.coord axis (x - v) ≠ 0 → ∀ u : Tiling.Plane,
        |Axis.coord axis u| < r →
          Real.sign (Axis.coord axis ((x + u) - v)) =
            Real.sign (Axis.coord axis (x - v))) :
    ∀ z, z ∈ Metric.ball x r → z ∈ quadrantAt q x →
      OffVertexCoordinateGrid K z := by
  intro z hzball hzq
  have hdisp (axis : Axis) : |Axis.coord axis (z - x)| < r := by
    cases axis
    · exact lt_of_le_of_lt (Complex.abs_re_le_norm (z - x)) (by
        simpa [Metric.mem_ball, dist_eq_norm] using hzball)
    · exact lt_of_le_of_lt (Complex.abs_im_le_norm (z - x)) (by
        simpa [Metric.mem_ball, dist_eq_norm] using hzball)
  have hadd (axis : Axis) (v : Tiling.Plane) :
      Axis.coord axis (z - v) =
        Axis.coord axis (x - v) + Axis.coord axis (z - x) := by
    cases axis <;> simp [Axis.coord, sub_eq_add_neg] <;> ring
  unfold OffVertexCoordinateGrid
  intro v hv
  constructor
  · intro hzero
    by_cases hbase : Axis.coord Axis.horizontal (x - v) = 0
    · have hqcoord : Axis.coord Axis.horizontal (z - x) ≠ 0 := by
        cases q <;> dsimp [quadrantAt] at hzq ⊢ <;>
          intro h <;> simp [Axis.coord] at h <;> linarith
      apply hqcoord
      have hzero' : Axis.coord Axis.horizontal (z - v) = 0 := by
        simpa [Axis.coord] using sub_eq_zero.mpr hzero
      rw [hadd Axis.horizontal v, hbase, zero_add] at hzero'
      exact hzero'
    · have hs := hstable Axis.horizontal v hv hbase (z - x)
        (hdisp Axis.horizontal)
      have hzsign : Real.sign (Axis.coord Axis.horizontal (z - v)) =
          Real.sign (Axis.coord Axis.horizontal (x - v)) := by
        simpa [show x + (z - x) = z by ring] using hs
      apply (Real.sign_eq_zero_iff.not.mpr hbase)
      rw [← hzsign]
      exact Real.sign_eq_zero_iff.mpr (by
        simpa [Axis.coord] using (sub_eq_zero.mpr hzero))
  · intro hzero
    by_cases hbase : Axis.coord Axis.vertical (x - v) = 0
    · have hqcoord : Axis.coord Axis.vertical (z - x) ≠ 0 := by
        cases q <;> dsimp [quadrantAt] at hzq ⊢ <;>
          intro h <;> simp [Axis.coord] at h <;> linarith
      apply hqcoord
      have hzero' : Axis.coord Axis.vertical (z - v) = 0 := by
        simpa [Axis.coord] using sub_eq_zero.mpr hzero
      rw [hadd Axis.vertical v, hbase, zero_add] at hzero'
      exact hzero'
    · have hs := hstable Axis.vertical v hv hbase (z - x)
        (hdisp Axis.vertical)
      have hzsign : Real.sign (Axis.coord Axis.vertical (z - v)) =
          Real.sign (Axis.coord Axis.vertical (x - v)) := by
        simpa [show x + (z - x) = z by ring] using hs
      apply (Real.sign_eq_zero_iff.not.mpr hbase)
      rw [← hzsign]
      exact Real.sign_eq_zero_iff.mpr (by
        simpa [Axis.coord] using (sub_eq_zero.mpr hzero))

private theorem local_grid_transport_of_near_wip
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (t : ↥C.centres)
    (x : Tiling.Plane) (y : Tiling.Plane)
    (hx : x = (a : Tiling.Plane) - (t : Tiling.Plane))
    (hy : y = mapTranslatedVertex phi a - Tphi t)
    (hnear : ∀ v : ↥C.region.vertices,
      dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) <
        P.controlRadius) :
    ∃ r : ℝ, 0 < r ∧ ∀ z, dist z x < r →
      ((OffVertexCoordinateGrid D.deformedRegion (y + (z - x)) ↔
          OffVertexCoordinateGrid C.region z) ∧
        (OffVertexCoordinateGrid C.region z →
          (z ∈ C.region.openCarrier ↔
            y + (z - x) ∈ D.deformedRegion.openCarrier))) := by
  obtain ⟨δsh, hδsh, hsh⟩ :=
    finite_vertex_coordinate_stability C.region x Axis.horizontal
  obtain ⟨δsv, hδsv, hsv⟩ :=
    finite_vertex_coordinate_stability C.region x Axis.vertical
  obtain ⟨δth, hδth, hth⟩ :=
    finite_vertex_coordinate_stability D.deformedRegion y Axis.horizontal
  obtain ⟨δtv, hδtv, htv⟩ :=
    finite_vertex_coordinate_stability D.deformedRegion y Axis.vertical
  have hcontAt : ContinuousAt D.planarHomeomorph x :=
    D.planarHomeomorph.continuous.continuousAt
  obtain ⟨δc, hδc, hcont⟩ :=
    (Metric.continuousAt_iff.1 hcontAt)
      (min δth δtv) (lt_min hδth hδtv)
  let r := min δsh (min δsv (min δc (min δth δtv)))
  refine ⟨r, ?_, ?_⟩
  · dsimp [r]
    exact lt_min hδsh (lt_min hδsv (lt_min hδc (lt_min hδth hδtv)))
  · intro z hz
    let u := z - x
    let w := y + u
    have hzu (axis : Axis) : |Axis.coord axis u| < r := by
      cases axis
      · exact lt_of_le_of_lt (Complex.abs_re_le_norm u) (by
          simpa [u, dist_eq_norm] using hz)
      · exact lt_of_le_of_lt (Complex.abs_im_le_norm u) (by
          simpa [u, dist_eq_norm] using hz)
    have hsml (axis : Axis) : |Axis.coord axis u| < δsh :=
      lt_of_lt_of_le (hzu axis) (min_le_left _ _)
    have hsvl (axis : Axis) : |Axis.coord axis u| < δsv :=
      lt_of_lt_of_le (hzu axis)
        (le_trans (min_le_right _ _) (min_le_left _ _))
    have hthl (axis : Axis) : |Axis.coord axis u| < δth :=
      lt_of_lt_of_le (hzu axis)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _))))
    have htl (axis : Axis) : |Axis.coord axis u| < δtv :=
      lt_of_lt_of_le (hzu axis)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_right _ _))))
    have hsignzero : ∀ (v : ↥C.region.vertices) (axis : Axis),
        Real.sign (Axis.coord axis (z - (v : Tiling.Plane))) =
          Real.sign (Axis.coord axis (w - mapPoint phi (C.vertexPoint v.1 v.2))) ∧
        (Axis.coord axis (z - (v : Tiling.Plane)) = 0 ↔
          Axis.coord axis (w - mapPoint phi (C.vertexPoint v.1 v.2)) = 0) := by
      intro v axis
      have hb := translatedVertex_coordinateSigns_transport P phi hphi
        Tphi hTphi a v t (hnear v) axis
      have hsource_eq : (a : Tiling.Plane) -
          ((v : Tiling.Plane) + (t : Tiling.Plane)) =
          x - (v : Tiling.Plane) := by
        rw [hx]
        abel
      have htarget_eq : y - mapPoint phi (C.vertexPoint v.1 v.2) =
          mapTranslatedVertex phi a -
            (mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t) := by
        rw [hy]
        abel
      have hbsource : Real.sign (Axis.coord axis
          ((a : Tiling.Plane) - ((v : Tiling.Plane) + (t : Tiling.Plane)))) =
          Real.sign (Axis.coord axis (x - (v : Tiling.Plane))) := by
        rw [hsource_eq]
      have hbtarget : Real.sign (Axis.coord axis
          (y - mapPoint phi (C.vertexPoint v.1 v.2))) =
          Real.sign (Axis.coord axis
            (mapTranslatedVertex phi a -
              (mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t))) := by
        rw [htarget_eq]
      by_cases hzero : Axis.coord axis (x - (v : Tiling.Plane)) = 0
      · have hzero' : Axis.coord axis
            ((a : Tiling.Plane) - ((v : Tiling.Plane) + (t : Tiling.Plane))) = 0 := by
          rw [hsource_eq]
          exact hzero
        have hb0 := hb.2.mpr hzero'
        have hzu' : Axis.coord axis (z - (v : Tiling.Plane)) =
            Axis.coord axis u := by
          have hzexpr : z - (v : Tiling.Plane) =
              (x - (v : Tiling.Plane)) + u := by
            dsimp [u]
            ring
          rw [hzexpr]
          cases axis <;>
            simp [Axis.coord, Complex.sub_re, Complex.sub_im,
              Complex.add_re, Complex.add_im] at hzero ⊢ <;> linarith
        have hwu' : Axis.coord axis (w - mapPoint phi
            (C.vertexPoint v.1 v.2)) = Axis.coord axis u := by
          have : Axis.coord axis (y - mapPoint phi
              (C.vertexPoint v.1 v.2)) = 0 := by
            rw [htarget_eq]
            exact hb0
          have hwexpr : w - mapPoint phi (C.vertexPoint v.1 v.2) =
              (y - mapPoint phi (C.vertexPoint v.1 v.2)) + u := by
            dsimp [w]
            ring
          rw [hwexpr]
          cases axis <;>
            simp [Axis.coord, Complex.sub_re, Complex.sub_im,
              Complex.add_re, Complex.add_im] at this ⊢ <;> linarith
        rw [hzu', hwu']
        exact ⟨rfl, Iff.rfl⟩
      · have hs : Real.sign (Axis.coord axis (z - (v : Tiling.Plane))) =
            Real.sign (Axis.coord axis (x - (v : Tiling.Plane))) := by
          cases axis
          · simpa [Axis.coord, u, show x + (z - x) = z by ring] using
              hsh v.1 v.2 (by simpa [Axis.coord] using hzero) u
                (by simpa [Axis.coord] using hsml Axis.horizontal)
          · simpa [Axis.coord, u, show x + (z - x) = z by ring] using
              hsv v.1 v.2 (by simpa [Axis.coord] using hzero) u
                (by simpa [Axis.coord] using hsvl Axis.vertical)
        have htzero : Axis.coord axis (y - mapPoint phi
            (C.vertexPoint v.1 v.2)) ≠ 0 := by
          intro h
          have h' : Axis.coord axis
              (mapTranslatedVertex phi a -
                (mapPoint phi (C.vertexPoint v.1 v.2) + Tphi t)) = 0 := by
            rw [← htarget_eq]
            exact h
          exact hzero (by
            rw [← hsource_eq]
            exact hb.2.mp h')
        obtain ⟨mv, hmv⟩ := mapped_vertex_subtype_wip D v.1 v.2
        have htzero' : Axis.coord axis (y - mv.1) ≠ 0 := by
          simpa [hmv] using htzero
        have ht : Real.sign (Axis.coord axis (w - mv.1)) =
            Real.sign (Axis.coord axis (y - mv.1)) := by
          cases axis
          · simpa [Axis.coord, w, hmv, u] using
              hth mv.1 mv.2 (by simpa [Axis.coord] using htzero') u
                (by simpa [Axis.coord] using hthl Axis.horizontal)
          · simpa [Axis.coord, w, hmv, u] using
              htv mv.1 mv.2 (by simpa [Axis.coord] using htzero') u
                (by simpa [Axis.coord] using htl Axis.vertical)
        have hs' := hs
        have ht' : Real.sign (Axis.coord axis (w - mapPoint phi
            (C.vertexPoint v.1 v.2))) =
            Real.sign (Axis.coord axis (y - mapPoint phi
              (C.vertexPoint v.1 v.2))) := by
          simpa [hmv] using ht
        have hsn : Real.sign (Axis.coord axis (z - (v : Tiling.Plane))) ≠ 0 := by
          rw [hs']
          exact (Real.sign_eq_zero_iff.not.mpr hzero)
        have hsig : Real.sign (Axis.coord axis (z - (v : Tiling.Plane))) =
            Real.sign (Axis.coord axis (w - mapPoint phi
              (C.vertexPoint v.1 v.2))) :=
          hs'.trans (hbsource.symm.trans
            (hb.1.symm.trans (hbtarget.symm.trans ht'.symm)))
        constructor
        · exact hsig
        · constructor
          · intro hz0
            apply Real.sign_eq_zero_iff.mp
            rw [← hsig, Real.sign_eq_zero_iff.mpr hz0]
          · intro hw0
            apply Real.sign_eq_zero_iff.mp
            rw [hsig, Real.sign_eq_zero_iff.mpr hw0]
    have hoff : OffVertexCoordinateGrid C.region z ↔
        OffVertexCoordinateGrid D.deformedRegion w := by
      constructor
      · intro hzoff
        unfold OffVertexCoordinateGrid at hzoff ⊢
        rw [D.vertices_image]
        rintro _ ⟨v, hv, hmv⟩
        rw [← hmv, D.vertex_agreement v hv]
        constructor
        · intro hzero
          apply (hzoff v hv).1
          have hzero' : Axis.coord Axis.horizontal
              (w - mapPoint phi (C.vertexPoint v hv)) = 0 := by
            simpa [Axis.coord] using sub_eq_zero.mpr hzero
          exact sub_eq_zero.mp (by simpa [Axis.coord] using
            (hsignzero ⟨v, hv⟩ Axis.horizontal).2.mpr hzero')
        · intro hzero
          apply (hzoff v hv).2
          have hzero' : Axis.coord Axis.vertical
              (w - mapPoint phi (C.vertexPoint v hv)) = 0 := by
            simpa [Axis.coord] using sub_eq_zero.mpr hzero
          exact sub_eq_zero.mp (by simpa [Axis.coord] using
            (hsignzero ⟨v, hv⟩ Axis.vertical).2.mpr hzero')
      · intro hwoff
        unfold OffVertexCoordinateGrid at hwoff ⊢
        intro v hv
        obtain ⟨mv, hmv⟩ := mapped_vertex_subtype_wip D v hv
        have hw := hwoff mv mv.property
        constructor
        · intro h
          apply hw.1
          have hzero : Axis.coord Axis.horizontal
              (z - (v : Tiling.Plane)) = 0 := by
            simpa [Axis.coord] using sub_eq_zero.mpr h
          have hzero' := (hsignzero ⟨v, hv⟩ Axis.horizontal).2.mp hzero
          simpa [hmv, Axis.coord] using sub_eq_zero.mp hzero'
        · intro h
          apply hw.2
          have hzero : Axis.coord Axis.vertical
              (z - (v : Tiling.Plane)) = 0 := by
            simpa [Axis.coord] using sub_eq_zero.mpr h
          have hzero' := (hsignzero ⟨v, hv⟩ Axis.vertical).2.mp hzero
          simpa [hmv, Axis.coord] using sub_eq_zero.mp hzero'
    have hopen : z ∈ C.region.openCarrier ↔
        D.planarHomeomorph z ∈ D.deformedRegion.openCarrier := by
      rw [D.deformedRegion_openCarrier]
      constructor
      · intro hzopen
        exact ⟨z, hzopen, rfl⟩
      · rintro ⟨z', hzopen, heq⟩
        exact D.planarHomeomorph.injective heq ▸ hzopen
    have hoffH_of : OffVertexCoordinateGrid C.region z →
        OffVertexCoordinateGrid D.deformedRegion (D.planarHomeomorph z) := by
      intro hzoff
      unfold OffVertexCoordinateGrid
      rw [D.vertices_image]
      rintro _ ⟨v, hv, hmv⟩
      rw [← hmv, D.vertex_agreement v hv]
      constructor
      · intro hzero
        have hzero' : Axis.coord Axis.horizontal (D.planarHomeomorph z -
            mapPoint phi (C.vertexPoint v hv)) = 0 := by
          simpa [Axis.coord] using sub_eq_zero.mpr hzero
        have hs := planarHomeomorph_coordinate_sign_wip D z v hv Axis.horizontal
        have hs0 : Real.sign (Axis.coord Axis.horizontal (z - v)) = 0 := by
          rw [← hs, Real.sign_eq_zero_iff.mpr hzero']
        exact (hzoff v hv).1 (sub_eq_zero.mp (by
          simpa [Axis.coord] using Real.sign_eq_zero_iff.mp hs0))
      · intro hzero
        have hzero' : Axis.coord Axis.vertical (D.planarHomeomorph z -
            mapPoint phi (C.vertexPoint v hv)) = 0 := by
          simpa [Axis.coord] using sub_eq_zero.mpr hzero
        have hs := planarHomeomorph_coordinate_sign_wip D z v hv Axis.vertical
        have hs0 : Real.sign (Axis.coord Axis.vertical (z - v)) = 0 := by
          rw [← hs, Real.sign_eq_zero_iff.mpr hzero']
        exact (hzoff v hv).2 (sub_eq_zero.mp (by
          simpa [Axis.coord] using Real.sign_eq_zero_iff.mp hs0))
    constructor
    · exact hoff.symm
    · intro hzoff
      have hoffH := hoffH_of hzoff
      have hsame : SameVertexGridCell D.deformedRegion
          (D.planarHomeomorph z) w := by
        apply sameVertexGridCell_of_coordinate_sign hoffH (hoff.mp hzoff)
        intro mv hmv
        rw [D.vertices_image] at hmv
        obtain ⟨v, hv, hmv⟩ := hmv
        rw [← hmv, D.vertex_agreement v hv]
        exact ⟨(planarHomeomorph_coordinate_sign_wip D z v hv Axis.horizontal).trans
            (hsignzero ⟨v, hv⟩ Axis.horizontal).1,
          (planarHomeomorph_coordinate_sign_wip D z v hv Axis.vertical).trans
            (hsignzero ⟨v, hv⟩ Axis.vertical).1⟩
      have hmem : z ∈ C.region.openCarrier ↔
          w ∈ D.deformedRegion.openCarrier :=
        hopen.trans (sameVertexGridCell_openCarrier_iff _ _ _ hoffH
          (hoff.mp hzoff) hsame)
      exact hmem

private theorem placed_support_conj_wip
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (t : ↥C.centres) :
    ((a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support ↔
      mapTranslatedVertex phi a ∈ Tphi t +ᵥ D.deformedRegion.support) := by
  let x : Tiling.Plane := (a : Tiling.Plane) - (t : Tiling.Plane)
  let y : Tiling.Plane := mapTranslatedVertex phi a - Tphi t
  have hsource_near : ∀ ha : (a : Tiling.Plane) ∈
      (t : Tiling.Plane) +ᵥ C.region.support,
      ∀ v : ↥C.region.vertices,
        dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) <
          P.controlRadius := by
    intro ha v
    exact tileVertex_near_translatedAnchor_wip P hScale a t
      Quadrant.southwest ha v
  have hdiamSource : Metric.diam C.region.support < P.scale := by
    rw [diam_support_eq_openCarrier_wip C.region]
    nlinarith [hScale, (Metric.diam_nonneg :
      0 ≤ Metric.diam C.region.openCarrier)]
  have hdiamTarget : Metric.diam D.deformedRegion.support < P.scale / 2 := by
    have hle := deformedRegion_diam_le_add_localError P hphi D hdiamSource
    have hscale1 : 1 < P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg :
        0 ≤ Metric.diam C.region.openCarrier)]
    have herr : P.localError < 1 := by
      rw [P.localError_eq]
      exact inv_lt_one_of_one_lt₀ hscale1
    have hhalf : Metric.diam C.region.support + P.localError < P.scale / 2 := by
      rw [diam_support_eq_openCarrier_wip C.region]
      nlinarith [hScale, herr, (Metric.diam_nonneg :
        0 ≤ Metric.diam C.region.openCarrier)]
    exact lt_of_le_of_lt hle hhalf
  have htarget_near : ∀ hb : mapTranslatedVertex phi a ∈
      Tphi t +ᵥ D.deformedRegion.support,
      ∀ v : ↥C.region.vertices,
        dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) <
          P.controlRadius := by
    intro hb v
    obtain ⟨b, hbval, hbmap⟩ := mapTranslatedVertex_add_local phi v t
    have hp : mapPoint phi (C.vertexPoint v.1 v.2) ∈
        D.deformedRegion.support := by
      apply vertex_mem_support_wip
      rw [D.vertices_image]
      exact ⟨(v : Tiling.Plane), v.2, D.vertex_agreement v.1 v.2⟩
    have hv : mapTranslatedVertex phi b ∈
        Tphi t +ᵥ D.deformedRegion.support := by
      apply Set.mem_vadd_set.mpr
      refine ⟨mapPoint phi (C.vertexPoint v.1 v.2), hp, ?_⟩
      simpa [vadd_eq_add, hTphi t, add_comm] using hbmap.symm
    have hba : dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) <
        P.scale / 2 := by
      obtain ⟨w, hw, hwa⟩ := Set.mem_vadd_set.mp hb
      obtain ⟨p, hp', hpb⟩ := Set.mem_vadd_set.mp hv
      have hda := Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded
        hw hp'
      have hdist : dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) ≤
          Metric.diam D.deformedRegion.support := by
        calc
          dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) =
              dist w p := by
            rw [← hwa, ← hpb]
            simp [vadd_eq_add, dist_eq_norm, sub_eq_add_neg, add_comm,
              add_left_comm, add_assoc]
          _ ≤ Metric.diam D.deformedRegion.support := hda
      exact lt_of_le_of_lt hdist hdiamTarget
    have hsource := deformation_coarselyProper P phi hphi a b hba
    simpa [hbval] using lt_trans hsource P.scale_lt_controlRadius
  constructor
  · intro ha
    obtain ⟨w, hw, hwa⟩ := Set.mem_vadd_set.mp ha
    have hxmem : x ∈ C.region.support := by
      have hxeq : x = w := by
        dsimp [x]
        rw [← hwa]
        simp [vadd_eq_add, sub_eq_add_neg, add_assoc]
      rw [hxeq]
      exact hw
    obtain ⟨r, hr, hgrid⟩ := local_grid_transport_of_near_wip P phi hphi D Tphi
      hTphi a t x y rfl rfl (hsource_near ha)
    have hsupp := support_transport_of_local_grid_wip (K := C.region)
      (L := D.deformedRegion) (x := x) (y := y) hr hgrid
    have hymem : y ∈ D.deformedRegion.support := hsupp.mp hxmem
    apply Set.mem_vadd_set.mpr
    refine ⟨y, hymem, ?_⟩
    dsimp [y]
    abel
  · intro hb
    obtain ⟨w, hw, hwa⟩ := Set.mem_vadd_set.mp hb
    have hymem : y ∈ D.deformedRegion.support := by
      have hyeq : y = w := by
        dsimp [y]
        rw [← hwa]
        simp [vadd_eq_add, sub_eq_add_neg, add_assoc]
      rw [hyeq]
      exact hw
    obtain ⟨r, hr, hgrid⟩ := local_grid_transport_of_near_wip P phi hphi D Tphi
      hTphi a t x y rfl rfl (htarget_near hb)
    have hsupp := support_transport_of_local_grid_wip (K := C.region)
      (L := D.deformedRegion) (x := x) (y := y) hr hgrid
    have hxmem : x ∈ C.region.support := hsupp.mpr hymem
    apply Set.mem_vadd_set.mpr
    refine ⟨x, hxmem, ?_⟩
    dsimp [x]
    abel

private theorem placed_quadrant_conj_wip
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (t : ↥C.centres) (q : Quadrant)
    (ha : (a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support) :
    ((∃ r : ℝ, 0 < r ∧ Metric.ball (a : Tiling.Plane) r ∩
        quadrantAt q a ⊆ (t : Tiling.Plane) +ᵥ C.region.openCarrier) ↔
      ∃ r : ℝ, 0 < r ∧ Metric.ball (mapTranslatedVertex phi a) r ∩
        quadrantAt q (mapTranslatedVertex phi a) ⊆
          Tphi t +ᵥ D.deformedRegion.openCarrier) := by
  let x : Tiling.Plane := (a : Tiling.Plane) - (t : Tiling.Plane)
  let y : Tiling.Plane := mapTranslatedVertex phi a - Tphi t
  have hnear : ∀ v : ↥C.region.vertices,
      dist (a : Tiling.Plane) ((v : Tiling.Plane) + (t : Tiling.Plane)) <
        P.controlRadius := by
    intro v
    exact tileVertex_near_translatedAnchor_wip P hScale a t
      Quadrant.southwest ha v
  obtain ⟨ρ, hρ, hgrid⟩ := local_grid_transport_of_near_wip P phi hphi D Tphi
    hTphi a t x y rfl rfl hnear
  obtain ⟨δsh, hδsh, hsh⟩ :=
    finite_vertex_coordinate_stability C.region x Axis.horizontal
  obtain ⟨δsv, hδsv, hsv⟩ :=
    finite_vertex_coordinate_stability C.region x Axis.vertical
  obtain ⟨δth, hδth, hth⟩ :=
    finite_vertex_coordinate_stability D.deformedRegion y Axis.horizontal
  obtain ⟨δtv, hδtv, htv⟩ :=
    finite_vertex_coordinate_stability D.deformedRegion y Axis.vertical
  let r := min ρ (min δsh (min δsv (min δth δtv)))
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hρ (lt_min hδsh (lt_min hδsv (lt_min hδth hδtv)))
  have hstableS (axis : Axis) (v : Tiling.Plane) (hv : v ∈ C.region.vertices)
      (hzero : Axis.coord axis (x - v) ≠ 0) (u : Tiling.Plane)
      (hu : |Axis.coord axis u| < r) :
      Real.sign (Axis.coord axis ((x + u) - v)) =
        Real.sign (Axis.coord axis (x - v)) := by
    cases axis
    · exact hsh v hv hzero u (lt_of_lt_of_le hu
        (le_trans (min_le_right ρ _) (min_le_left _ _)))
    · exact hsv v hv hzero u (lt_of_lt_of_le hu
        (le_trans (min_le_right ρ _) (le_trans (min_le_right δsh _)
          (min_le_left _ _))))
  have hstableT (axis : Axis) (v : Tiling.Plane)
      (hv : v ∈ D.deformedRegion.vertices)
      (hzero : Axis.coord axis (y - v) ≠ 0) (u : Tiling.Plane)
      (hu : |Axis.coord axis u| < r) :
      Real.sign (Axis.coord axis ((y + u) - v)) =
        Real.sign (Axis.coord axis (y - v)) := by
    cases axis
    · exact hth v hv hzero u (lt_of_lt_of_le hu
        (le_trans (min_le_right ρ _) (le_trans (min_le_right δsh _)
          (le_trans (min_le_right δsv _) (min_le_left _ _)))))
    · exact htv v hv hzero u (lt_of_lt_of_le hu
        (le_trans (min_le_right ρ _) (le_trans (min_le_right δsh _)
          (le_trans (min_le_right δsv _) (min_le_right _ _)))) )
  have hqsub (z : Tiling.Plane) :
      (z ∈ quadrantAt q (a : Tiling.Plane)) ↔
        (z - (t : Tiling.Plane) ∈ quadrantAt q x) := by
    cases q <;> dsimp [quadrantAt, x] <;>
      constructor <;> intro hz <;> constructor <;> linarith
  have hballsub (z : Tiling.Plane) :
      dist z (a : Tiling.Plane) < r ↔
        dist (z - (t : Tiling.Plane)) x < r := by
    dsimp [x]
    simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hqtarget (z : Tiling.Plane) :
      z ∈ quadrantAt q (mapTranslatedVertex phi a) ↔
        z - Tphi t ∈ quadrantAt q y := by
    cases q <;> dsimp [quadrantAt, y] <;>
      constructor <;> intro hz <;> constructor <;> linarith
  have hballtarget (z : Tiling.Plane) :
      dist z (mapTranslatedVertex phi a) < r ↔
        dist (z - Tphi t) y < r := by
    dsimp [y]
    simp [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  constructor
  · rintro ⟨s, hs, hsub⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    intro w hw
    obtain ⟨hwball, hwq⟩ := hw
    have hwrelq : w - Tphi t ∈ quadrantAt q y := (hqtarget w).1 hwq
    have hwballr : dist w (mapTranslatedVertex phi a) < r :=
      lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_left _ _)
    have hwrelball : dist (w - Tphi t) y < r := (hballtarget w).1 hwballr
    have hwoffs := offVertexGrid_of_ball_quadrant_wip D.deformedRegion y q r hr
      hstableT (w - Tphi t) hwrelball hwrelq
    let z : Tiling.Plane := x + (w - mapTranslatedVertex phi a)
    have hzball : dist z x < r := by
      dsimp [z]
      simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        hwballr
    have hzsmall : dist z x < ρ := lt_of_lt_of_le hzball (min_le_left _ _)
    obtain ⟨hwoffS, hmem⟩ := hgrid z hzsmall
    have hzq : z ∈ quadrantAt q x := by
      have hzq' := (quadrantDisplacement (a := (a : Tiling.Plane) -
        (t : Tiling.Plane)) (b := (mapTranslatedVertex phi a) - Tphi t)
        q (show w - Tphi t ∈ quadrantAt q y from hwrelq)).2
      have heq : z = x + (w - Tphi t - y) := by
        dsimp [z, y]
        ring
      rw [heq]
      exact hzq'
    have hzactual : (t : Tiling.Plane) + z ∈
        (t : Tiling.Plane) +ᵥ C.region.openCarrier := by
      have hzqactual := (quadrantDisplacement
        (a := (a : Tiling.Plane)) (b := mapTranslatedVertex phi a) q hwq).2
      have hzballactual : dist ((t : Tiling.Plane) + z) (a : Tiling.Plane) < s := by
        dsimp [z, x]
        simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_right _ _))
      apply hsub
      refine ⟨hzballactual, ?_⟩
      dsimp [z, x]
      simpa [z, x, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hzqactual
    have htargetoff : OffVertexCoordinateGrid D.deformedRegion
        (y + (z - x)) := by
      simpa [z, y, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hwoffs
    have hsourceoff : OffVertexCoordinateGrid C.region z := hwoffS.mp htargetoff
    have hzsource : z ∈ C.region.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzactual
      simpa [z] using hzactual
    have hztarget : y + (z - x) ∈ D.deformedRegion.openCarrier :=
      (hmem hsourceoff).mp hzsource
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [y, z, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hztarget
  · rintro ⟨s, hs, hsub⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    intro w hw
    obtain ⟨hwball, hwq⟩ := hw
    have hwrelq : w - (t : Tiling.Plane) ∈ quadrantAt q x := (hqsub w).1 hwq
    have hwballr : dist w (a : Tiling.Plane) < r :=
      lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_left _ _)
    have hwrelball : dist (w - (t : Tiling.Plane)) x < r := (hballsub w).1 hwballr
    have hwoffs := offVertexGrid_of_ball_quadrant_wip C.region x q r hr
      hstableS (w - (t : Tiling.Plane)) hwrelball hwrelq
    have hwsmall : dist (w - (t : Tiling.Plane)) x < ρ :=
      lt_of_lt_of_le hwrelball (min_le_left _ _)
    obtain ⟨hwoffT, hmem⟩ := hgrid (w - (t : Tiling.Plane)) hwsmall
    have hwtarg : y + ((w - (t : Tiling.Plane)) - x) ∈
        D.deformedRegion.openCarrier := by
      have hactualq := (quadrantDisplacement
        (a := mapTranslatedVertex phi a) (b := (a : Tiling.Plane)) q hwq).2
      have hactualball : mapTranslatedVertex phi a +
          ((w - (t : Tiling.Plane)) - x) ∈ Metric.ball (mapTranslatedVertex phi a) s := by
        rw [Metric.mem_ball]
        dsimp [x]
        simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          (lt_of_lt_of_le (Metric.mem_ball.1 hwball) (min_le_right _ _))
      have hactualmem := hsub ⟨hactualball, by
        convert hactualq using 1
        dsimp [x]
        ring⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hactualmem
      simpa [y, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hactualmem
    have hwsource : w - (t : Tiling.Plane) ∈ C.region.openCarrier :=
      (hmem hwoffs).mpr hwtarg
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hwsource

private theorem placedTileQuadrantTransport :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (a : ↥C.translatedVertices) (t : ↥C.centres) (q : Quadrant),
      ((a : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support ↔
        mapTranslatedVertex phi a ∈ Tphi t +ᵥ D.deformedRegion.support) ∧
      ((∃ r : ℝ, 0 < r ∧ Metric.ball (a : Tiling.Plane) r ∩ quadrantAt q a ⊆
          (t : Tiling.Plane) +ᵥ C.region.openCarrier) ↔
        ∃ r : ℝ, 0 < r ∧ Metric.ball (mapTranslatedVertex phi a) r ∩
          quadrantAt q (mapTranslatedVertex phi a) ⊆
            Tphi t +ᵥ D.deformedRegion.openCarrier) := by
  classical
  intro C P hScale phi hphi D Tphi hTphi a t q
  constructor
  · exact placed_support_conj_wip P hScale phi hphi D Tphi hTphi a t
  · constructor
    · intro hs
      obtain ⟨r, hr, hsub⟩ := hs
      have ha := anchor_mem_translatedSupport_of_quadrant_wip
        (a : Tiling.Plane) (t : Tiling.Plane) q hr hsub
      exact (placed_quadrant_conj_wip P hScale phi hphi D Tphi hTphi a t q ha).mp
        ⟨r, hr, hsub⟩
    · intro ht
      obtain ⟨r, hr, hsub⟩ := ht
      have hb := anchor_mem_translatedSupport_of_quadrant_wip
        (mapTranslatedVertex phi a) (Tphi t) q hr hsub
      have ha := (placed_support_conj_wip P hScale phi hphi D Tphi hTphi a t).mpr hb
      exact (placed_quadrant_conj_wip P hScale phi hphi D Tphi hTphi a t q ha).mpr
        ⟨r, hr, hsub⟩

private theorem finiteNonincidentImageSupports_separated :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (S : Set ↥C.centres) (a : ↥C.translatedVertices)
      (G : ControlledGermLabels C S a)
      (Q : ImageAnchorCandidateSet C phi D Tphi a),
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
        ∀ t ∈ Q.candidates, t ∈ S → t ∉ G.labels →
          Disjoint (Metric.ball (mapTranslatedVertex phi a) r)
            (Tphi t +ᵥ D.deformedRegion.support) := by
  intro C P hScale phi hphi D Tphi hTphi S a G Q
  apply finiteNonincidentImageSupports_separated_of_candidate_nonincident
    D Tphi a S G Q
  intro t htQ htS htG htarget
  apply htG
  apply (G.labels_spec t).2
  refine ⟨htS, ?_⟩
  exact (placedTileQuadrantTransport P hScale phi hphi D Tphi hTphi a t
    .southwest).1.mpr htarget

private theorem incidentLabels_complete_bothWays :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (S : Set ↥C.centres) (a : ↥C.translatedVertices)
      (G : ControlledGermLabels C S a),
      ∃ r : ℝ, 0 < r ∧
        (∀ t ∈ S, (Metric.ball (a : Tiling.Plane) r ∩
            ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty → t ∈ G.labels) ∧
        ∀ t ∈ S, (Metric.ball (mapTranslatedVertex phi a) r ∩
          (Tphi t +ᵥ D.deformedRegion.openCarrier)).Nonempty → t ∈ G.labels := by
  intro C P hScale phi hphi D Tphi hTphi S a G
  classical
  obtain ⟨B, hB⟩ := sourceCandidateSet_exists C P.source_hasFLC a
  obtain ⟨rs, hrs, hrs1, hsrc⟩ := sourceIncidentLabels_isolated S a G B (by
    intro t htS hmeet
    exact hB t hmeet)
  obtain ⟨Q⟩ := imageAnchorCandidateSet_exists P hScale phi hphi D Tphi hTphi a
  have hnot : ∀ t ∈ Q.candidates, t ∈ S → t ∉ G.labels →
      mapTranslatedVertex phi a ∉ Tphi t +ᵥ D.deformedRegion.support := by
    intro t htQ htS htG htarget
    apply htG
    apply (G.labels_spec t).2
    refine ⟨htS, ?_⟩
    exact (placedTileQuadrantTransport P hScale phi hphi D Tphi hTphi a t
      .southwest).1.mpr htarget
  obtain ⟨ri, hri, hri1, himage⟩ := imageIncidentLabels_isolated
    D Tphi a S G Q hnot
  refine ⟨min rs ri, lt_min hrs hri, ?_⟩
  constructor
  · intro t htS hmeet
    apply hsrc t htS
    obtain ⟨z, hz⟩ := hmeet
    exact ⟨z, Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  · intro t htS hmeet
    apply himage t htS
    obtain ⟨z, hz⟩ := hmeet
    exact ⟨z, Metric.ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩

private theorem controlledGermLabels_transport :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (S : Set ↥C.centres) (a : ↥C.translatedVertices)
      (_G : ControlledGermLabels C S a),
      supportGerm C.region (Set.image Subtype.val S) a =
        supportGerm D.deformedRegion (deformedCenterCarrierOn Tphi S)
          (mapTranslatedVertex phi a) := by
  intro C P hScale phi hphi D Tphi hTphi S a G
  classical
  obtain ⟨ri, hri, hsourceIso, himageIso⟩ :=
    incidentLabels_complete_bothWays P hScale phi hphi D Tphi hTphi S a G
  let L : Finset Tiling.Plane := G.labels.image (fun t : ↥C.centres => Tphi t)
  let U : Set Tiling.Plane :=
    openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S)
  let V : Set Tiling.Plane := openUnion D.deformedRegion (L : Set Tiling.Plane)
  have hUV : ∀ z ∈ Metric.ball (mapTranslatedVertex phi a) ri,
      z ∈ U ↔ z ∈ V := by
    intro z hz
    constructor
    · intro hzU
      change z ∈ openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) at hzU
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzU
      obtain ⟨c, hzc⟩ := hzU
      obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzc
      obtain ⟨t, htS, htc⟩ := c.property
      have hct : Tphi t = (c : Tiling.Plane) := htc
      have htG : t ∈ G.labels := himageIso t htS ⟨z, hz, by
        simpa [hct] using hzc⟩
      change z ∈ openUnion D.deformedRegion (L : Set Tiling.Plane)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨Tphi t, ?_⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, htG, rfl⟩)
      · exact Set.mem_vadd_set.mpr ⟨w, hw, by simpa [hct] using hzw⟩
    · intro hzV
      change z ∈ openUnion D.deformedRegion (L : Set Tiling.Plane) at hzV
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzV
      obtain ⟨c, hzc⟩ := hzV
      obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzc
      obtain ⟨t, htG, htc⟩ := Finset.mem_image.mp c.property
      have htS : t ∈ S := (G.labels_spec t).1 htG |>.1
      change z ∈ openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨Tphi t, ⟨t, htS, rfl⟩⟩, ?_⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by simpa [htc] using hzw⟩
  obtain ⟨rlocal, hrlocal, hreg⟩ :=
    regularSupport_local_eq_of_openUnion_eq_on_ball hri hUV
  have hfiniteGerm :
      supportGerm D.deformedRegion (deformedCenterCarrierOn Tphi S)
        (mapTranslatedVertex phi a) =
      supportGerm D.deformedRegion (L : Set Tiling.Plane)
        (mapTranslatedVertex phi a) := by
    ext q
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨min r rlocal, lt_min hr hrlocal, ?_⟩
      intro z hz
      apply (hreg z (Metric.ball_subset_ball (min_le_right _ _) hz.1)).mp
      exact hsub ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
    · rintro ⟨r, hr, hsub⟩
      refine ⟨min r rlocal, lt_min hr hrlocal, ?_⟩
      intro z hz
      apply (hreg z (Metric.ball_subset_ball (min_le_right _ _) hz.1)).mpr
      exact hsub ⟨Metric.ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
  have htargetSpec : ∀ q : Quadrant,
      q ∈ supportGerm D.deformedRegion (deformedCenterCarrierOn Tphi S)
          (mapTranslatedVertex phi a) ↔
        ∃ t, t ∈ G.labels ∧ ∃ r : ℝ, 0 < r ∧
          Metric.ball (mapTranslatedVertex phi a) r ∩
            quadrantAt q (mapTranslatedVertex phi a) ⊆
              Tphi t +ᵥ D.deformedRegion.openCarrier := by
    intro q
    rw [hfiniteGerm, finiteLabels_regularSupportGerm_noPacking]
    constructor
    · rintro ⟨p, hpL, r, hr, hsub⟩
      obtain ⟨t, htG, htp⟩ := Finset.mem_image.mp hpL
      refine ⟨t, htG, r, hr, ?_⟩
      simpa [htp] using hsub
    · rintro ⟨t, htG, r, hr, hsub⟩
      refine ⟨Tphi t, Finset.mem_image.mpr ⟨t, htG, rfl⟩, r, hr, hsub⟩
  ext q
  rw [G.quadrant_spec, htargetSpec]
  constructor
  · rintro ⟨t, htG, r, hr, hsub⟩
    exact ⟨t, htG, (placedTileQuadrantTransport P hScale phi hphi D Tphi
      hTphi a t q).2.mp ⟨r, hr, hsub⟩⟩
  · rintro ⟨t, htG, hq⟩
    exact ⟨t, htG, (placedTileQuadrantTransport P hScale phi hphi D Tphi
      hTphi a t q).2.mpr hq⟩

private theorem finite_iUnion_localBoundaryCross
    {ι : Type*} [Finite ι] (F : ι → Set Tiling.Plane)
    (hclosed : ∀ i, IsClosed (F i))
    (hcross : ∀ i x, ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (F i) →
      z.re = x.re ∨ z.im = x.im) (x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (⋃ i, F i) →
      z.re = x.re ∨ z.im = x.im := by
  let hfinite : LocallyFinite F := locallyFinite_of_finite F
  let J : Set ι := {i | x ∈ F i}
  have hJfinite : J.Finite := hfinite.point_finite x
  have hincident : ∀ᶠ z in nhds x, ∀ i, z ∈ F i → i ∈ J :=
    hfinite.eventually_subset hclosed x
  have hcrossEventually (i : ι) (hi : i ∈ J) :
      ∀ᶠ z in nhds x, z ∈ frontier (F i) →
        z.re = x.re ∨ z.im = x.im := by
    obtain ⟨r, hr, hball⟩ := hcross i x
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x hr) hball
  have hallCross : ∀ᶠ z in nhds x, ∀ i ∈ J, z ∈ frontier (F i) →
      z.re = x.re ∨ z.im = x.im := by
    exact hJfinite.eventually_all.mpr fun i hi ↦ hcrossEventually i hi
  have hevent : ∀ᶠ z in nhds x, ∀ i, z ∈ F i →
      z ∈ frontier (⋃ i, F i) → z.re = x.re ∨ z.im = x.im := by
    filter_upwards [hincident, hallCross] with z hzIncident hzCross i hzi hzfront
    have hzNotInterior : z ∉ interior (F i) := by
      intro hzint
      exact Set.disjoint_left.1 disjoint_interior_frontier
        (interior_mono (subset_iUnion F i) hzint) hzfront
    have hzFiFrontier : z ∈ frontier (F i) := by
      rw [(hclosed i).frontier_eq]
      exact ⟨hzi, hzNotInterior⟩
    exact hzCross i (hzIncident i hzi) hzFiFrontier
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨r, hr, fun z hzBall hzFrontier ↦ ?_⟩
  have hzUnion : z ∈ ⋃ i, F i :=
    (hfinite.isClosed_iUnion hclosed).frontier_subset hzFrontier
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hzUnion
  exact hball hzBall i hzi hzFrontier

private theorem finite_openUnion_closure_support
    (K : Region) (Q : Finset Tiling.Plane) :
    closure (openUnion K (Q : Set Tiling.Plane)) =
      ⋃ t : Q, (t : Tiling.Plane) +ᵥ K.support := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def]
  | @insert t Q ht ih =>
      have hU : openUnion K ((insert t Q : Finset Tiling.Plane) : Set Tiling.Plane) =
          ((t : Tiling.Plane) +ᵥ K.openCarrier) ∪ openUnion K (Q : Set Tiling.Plane) := by
        ext z
        simp [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Finset.mem_insert]
      rw [hU]
      rw [closure_union]
      rw [closure_vadd]
      change ((t : Tiling.Plane) +ᵥ closure (interior K.support)) ∪
        closure (openUnion K (Q : Set Tiling.Plane)) = _
      rw [K.isPolygonal.closure_interior, ih]
      rw [show (⋃ x : (insert t Q : Finset Tiling.Plane),
          (x : Tiling.Plane) +ᵥ K.support) =
          ((t : Tiling.Plane) +ᵥ K.support) ∪
            ⋃ x : Q, (x : Tiling.Plane) +ᵥ K.support by
        ext z
        simp]

private theorem finite_regularSupport_localBoundaryCross
    (K : Region) (Q : Finset Tiling.Plane) (x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r,
      z ∈ frontier (regularSupport K (Q : Set Tiling.Plane)) →
        z.re = x.re ∨ z.im = x.im := by
  classical
  let F : Q → Set Tiling.Plane := fun t ↦ (t : Tiling.Plane) +ᵥ K.support
  have hcross : ∀ t : Q, ∀ y : Tiling.Plane, ∃ r > 0,
      ∀ z ∈ Metric.ball y r, z ∈ frontier (F t) →
      z.re = y.re ∨ z.im = y.im := by
    intro t y
    obtain ⟨r, hr, hball⟩ := K.isAxisParallel.localBoundaryCross (y - t.1)
    refine ⟨r, hr, fun z hz hzfront ↦ ?_⟩
    have hzdist : z - t.1 ∈ Metric.ball (y - t.1) r := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have heq : z - t.1 - (y - t.1) = z - y := by abel
      rw [heq]
      exact hz
    have hzsource : z - t.1 ∈ frontier K.support := by
      rw [Tiling.AxisParallel.frontier_vadd_eq] at hzfront
      simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hzfront
    rcases hball (z - t.1) hzdist hzsource with h | h
    · left
      simpa only [Complex.sub_re] using sub_left_inj.mp h
    · right
      simpa only [Complex.sub_im] using sub_left_inj.mp h
  have hboundary := finite_iUnion_localBoundaryCross F
    (fun t ↦ K.isPolygonal.isClosed.vadd t.1) hcross x
  obtain ⟨r, hr, hball⟩ := hboundary
  refine ⟨r, hr, fun z hz hzfront ↦ ?_⟩
  have hzfront' : z ∈ frontier (closure (openUnion K (Q : Set Tiling.Plane))) :=
    frontier_interior_subset hzfront
  rw [finite_openUnion_closure_support K Q] at hzfront'
  exact hball z hz (by simpa [F] using hzfront')

private theorem frontier_local_eq_of_eqOn_ball
    {A B : Set Tiling.Plane} {x : Tiling.Plane} {R : ℝ} (hR : 0 < R)
    (hEq : ∀ z ∈ Metric.ball x R, z ∈ A ↔ z ∈ B) :
    ∀ z ∈ Metric.ball x (R / 2), z ∈ frontier A ↔ z ∈ frontier B := by
  intro z hz
  have hcl_of : ∀ (S T : Set Tiling.Plane),
      (∀ y ∈ Metric.ball x R, y ∈ S ↔ y ∈ T) →
        (z ∈ closure S ↔ z ∈ closure T) := by
    intro S T hST
    constructor
    · intro hzA
      rw [mem_closure_iff]
      intro o ho hzo
      obtain ⟨ε, hε, hεo⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hzo)
      let δ := min ε ((R - dist z x) / 2)
      have hmargin : dist z x < R := by
        have hz' := Metric.mem_ball.mp hz
        linarith
      have hδ : 0 < δ := lt_min hε (by linarith)
      obtain ⟨y, hy, hyA⟩ := (mem_closure_iff.mp hzA)
        (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
      have hyR : y ∈ Metric.ball x R := by
        rw [Metric.mem_ball]
        calc
          dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ < δ + dist z x := by linarith [Metric.mem_ball.mp hy]
          _ < R := by
            have hδ' : δ ≤ (R - dist z x) / 2 := min_le_right _ _
            linarith
      have hyB := (hST y hyR).mp hyA
      exact ⟨y, hεo (Metric.ball_subset_ball (min_le_left _ _) hy), hyB⟩
    · intro hzB
      rw [mem_closure_iff]
      intro o ho hzo
      obtain ⟨ε, hε, hεo⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds hzo)
      let δ := min ε ((R - dist z x) / 2)
      have hmargin : dist z x < R := by
        have hz' := Metric.mem_ball.mp hz
        linarith
      have hδ : 0 < δ := lt_min hε (by linarith)
      obtain ⟨y, hy, hyB⟩ := (mem_closure_iff.mp hzB)
        (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
      have hyR : y ∈ Metric.ball x R := by
        rw [Metric.mem_ball]
        calc
          dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
          _ < δ + dist z x := by linarith [Metric.mem_ball.mp hy]
          _ < R := by
            have hδ' : δ ≤ (R - dist z x) / 2 := min_le_right _ _
            linarith
      have hyA := (hST y hyR).mpr hyB
      exact ⟨y, hεo (Metric.ball_subset_ball (min_le_left _ _) hy), hyA⟩
  have hcl : z ∈ closure A ↔ z ∈ closure B := (hcl_of A B) hEq
  have hclc : z ∈ closure Aᶜ ↔ z ∈ closure Bᶜ :=
    (hcl_of Aᶜ Bᶜ) (fun y hy ↦ not_congr (hEq y hy))
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure]
  exact and_congr hcl hclc

private theorem localConeTransport :
    ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (S : Set ↥C.centres) (a : ↥C.translatedVertices),
      (a : Tiling.Plane) ∈ C.region.vertices + Set.image Subtype.val S →
      ∃ r : ℝ, 0 < r ∧ ∀ u, dist u 0 < r →
        ((a : Tiling.Plane) + u ∈ regularSupport C.region (Set.image Subtype.val S) ↔
          mapTranslatedVertex phi a + u ∈
            regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
  intro C P hScale phi hphi D Tphi hTphi S a ha
  classical
  obtain ⟨G⟩ := controlledGermLabels_exists C S a ha P.source_hasFLC
  obtain ⟨ri, hri, hsourceIso, himageIso⟩ :=
    incidentLabels_complete_bothWays P hScale phi hphi D Tphi hTphi S a G
  have hpackS : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Set.image Subtype.val S)) := by
    apply (isPacking_iff_openCarrier_disjoint C.region
      (Set.image Subtype.val S)).2
    intro s hs t ht hst
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨t', ht', rfl⟩ := ht
    apply ((isPacking_iff_openCarrier_disjoint C.region C.centres).1
      P.source_tilesOn.2.1) s'.property t'.property
    exact hst
  obtain ⟨rS, hrS, hsourceCross⟩ :=
    regularSupport_localBoundaryCross hpackS (a : Tiling.Plane)
  let L : Finset Tiling.Plane := G.labels.image (fun t : ↥C.centres => Tphi t)
  let U : Set Tiling.Plane :=
    openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S)
  let V : Set Tiling.Plane := openUnion D.deformedRegion (L : Set Tiling.Plane)
  have hUV : ∀ z ∈ Metric.ball (mapTranslatedVertex phi a) ri,
      z ∈ U ↔ z ∈ V := by
    intro z hz
    constructor
    · intro hzU
      change z ∈ openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) at hzU
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzU
      obtain ⟨c, hzc⟩ := hzU
      obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzc
      obtain ⟨t, htS, htc⟩ := c.property
      have hct : Tphi t = (c : Tiling.Plane) := htc
      have htG : t ∈ G.labels := himageIso t htS ⟨z, hz, by
        simpa [hct] using hzc⟩
      change z ∈ openUnion D.deformedRegion (L : Set Tiling.Plane)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨Tphi t, ?_⟩, ?_⟩
      · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨t, htG, rfl⟩)
      · exact Set.mem_vadd_set.mpr ⟨w, hw, by simpa [hct] using hzw⟩
    · intro hzV
      change z ∈ openUnion D.deformedRegion (L : Set Tiling.Plane) at hzV
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzV
      obtain ⟨c, hzc⟩ := hzV
      obtain ⟨w, hw, hzw⟩ := Set.mem_vadd_set.mp hzc
      obtain ⟨t, htG, htc⟩ := Finset.mem_image.mp c.property
      have htS : t ∈ S := (G.labels_spec t).1 htG |>.1
      change z ∈ openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨Tphi t, ⟨t, htS, rfl⟩⟩, ?_⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by simpa [htc] using hzw⟩
  obtain ⟨rlocal, hrlocal, hreg⟩ :=
    regularSupport_local_eq_of_openUnion_eq_on_ball hri hUV
  obtain ⟨rL, hrL, hLcross⟩ :=
    finite_regularSupport_localBoundaryCross D.deformedRegion L
      (mapTranslatedVertex phi a)
  let rE := min rL (rlocal / 2)
  have hrE : 0 < rE := lt_min hrL (by linarith)
  have htargetCross : ∀ z ∈ Metric.ball (mapTranslatedVertex phi a) rE,
      z ∈ frontier (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S)) →
        z.re = (mapTranslatedVertex phi a).re ∨
          z.im = (mapTranslatedVertex phi a).im := by
    intro z hz hzfront
    have hzhalf : z ∈ Metric.ball (mapTranslatedVertex phi a) (rlocal / 2) :=
      Metric.ball_subset_ball (by dsimp [rE]; exact min_le_right _ _) hz
    have hzL : z ∈ frontier (regularSupport D.deformedRegion (L : Set Tiling.Plane)) :=
      (frontier_local_eq_of_eqOn_ball hrlocal hreg z hzhalf).mp hzfront
    exact hLcross z (Metric.ball_subset_ball (by dsimp [rE]; exact min_le_left _ _) hz) hzL
  have htransport := controlledGermLabels_transport P hScale phi hphi D Tphi hTphi S a G
  have hocc : ∀ q, SetOccupiesQuadrant
      (regularSupport C.region (Set.image Subtype.val S)) (a : Tiling.Plane) q ↔
      SetOccupiesQuadrant
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))
          (mapTranslatedVertex phi a) q := by
    intro q
    exact Set.ext_iff.mp htransport q
  obtain ⟨r, hr, hlocal⟩ := quadrantGerm_membership_of_cross
    (regularSupport_isRegularOpen C.region (Set.image Subtype.val S)).1
    (regularSupport_isRegularOpen D.deformedRegion
      (deformedCenterCarrierOn Tphi S)).1
    (regularSupport_isRegularOpen C.region (Set.image Subtype.val S)).2
    (regularSupport_isRegularOpen D.deformedRegion
      (deformedCenterCarrierOn Tphi S)).2
    ⟨rS, hrS, hsourceCross⟩ ⟨rE, hrE, htargetCross⟩ hocc
  refine ⟨min r ri, lt_min hr hri, ?_⟩
  intro u hu
  have hsmall : dist u 0 < r := lt_of_lt_of_le hu (min_le_left _ _)
  have hmem := hlocal u hsmall
  exact hmem


end



end Tiling.AxisParallel.Approximation



namespace Tiling.AxisParallel.Approximation
open Tiling AxisParallel

private theorem uIcc_transport_local
    {a b x A B X : ℝ}
    (hxa : Real.sign (x - a) = Real.sign (X - A))
    (hxb : Real.sign (x - b) = Real.sign (X - B)) :
    x ∈ uIcc a b ↔ X ∈ uIcc A B := by
  rw [Set.mem_uIcc, Set.mem_uIcc]
  constructor
  · rintro (⟨hax, hxb'⟩ | ⟨hbx, hxa'⟩)
    · left
      constructor
      · exact sub_nonneg.mp (nonneg_of_sign_eq_local hxa (sub_nonneg.mpr hax))
      · exact sub_nonpos.mp (le_zero_of_sign_eq_local hxb (sub_nonpos.mpr hxb'))
    · right
      constructor
      · exact sub_nonneg.mp (nonneg_of_sign_eq_local hxb (sub_nonneg.mpr hbx))
      · exact sub_nonpos.mp (le_zero_of_sign_eq_local hxa (sub_nonpos.mpr hxa'))
  · rintro (⟨hAX, hXB⟩ | ⟨hBX, hXA⟩)
    · left
      constructor
      · exact sub_nonneg.mp (nonneg_of_sign_eq_local hxa.symm (sub_nonneg.mpr hAX))
      · exact sub_nonpos.mp (le_zero_of_sign_eq_local hxb.symm (sub_nonpos.mpr hXB))
    · right
      constructor
      · exact sub_nonneg.mp (nonneg_of_sign_eq_local hxb.symm (sub_nonneg.mpr hBX))
      · exact sub_nonpos.mp (le_zero_of_sign_eq_local hxa.symm (sub_nonpos.mpr hXA))

private theorem horizontal_intersection_iff_local
    {a b c d : Tiling.Plane} (hab : a ≠ b) (hcd : c ≠ d)
    (habIm : a.im = b.im) (hcdIm : c.im = d.im) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty ↔
      a.im = c.im ∧ (uIcc a.re b.re ∩ uIcc c.re d.re).Nonempty := by
  constructor
  · rintro ⟨p, hpab, hpcd⟩
    have hpab' := (mem_segment_horizontal_local hab habIm).mp hpab
    have hpcd' := (mem_segment_horizontal_local hcd hcdIm).mp hpcd
    exact ⟨hpab'.1.symm.trans hpcd'.1,
      ⟨p.re, (mem_segment_horizontal_local hab habIm).mp hpab |>.2,
        (mem_segment_horizontal_local hcd hcdIm).mp hpcd |>.2⟩⟩
  · rintro ⟨him, ⟨r, hra, hrc⟩⟩
    let p : Tiling.Plane := (r : ℂ) + (a.im : ℂ) * Complex.I
    refine ⟨p, ?_, ?_⟩
    · apply (mem_segment_horizontal_local hab habIm).mpr
      exact ⟨by simp [p, him], by simpa [p] using hra⟩
    · apply (mem_segment_horizontal_local hcd hcdIm).mpr
      exact ⟨by simp [p, him, hcdIm], by simpa [p] using hrc⟩

private theorem vertical_intersection_iff_local
    {a b c d : Tiling.Plane} (hab : a ≠ b) (hcd : c ≠ d)
    (habRe : a.re = b.re) (hcdRe : c.re = d.re) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty ↔
      a.re = c.re ∧ (uIcc a.im b.im ∩ uIcc c.im d.im).Nonempty := by
  constructor
  · rintro ⟨p, hpab, hpcd⟩
    have hpab' := (mem_segment_vertical_local hab habRe).mp hpab
    have hpcd' := (mem_segment_vertical_local hcd hcdRe).mp hpcd
    exact ⟨hpab'.1.symm.trans hpcd'.1,
      ⟨p.im, (mem_segment_vertical_local hab habRe).mp hpab |>.2,
        (mem_segment_vertical_local hcd hcdRe).mp hpcd |>.2⟩⟩
  · rintro ⟨hre, ⟨r, hra, hrc⟩⟩
    let p : Tiling.Plane := (a.re : ℂ) + (r : ℂ) * Complex.I
    refine ⟨p, ?_, ?_⟩
    · apply (mem_segment_vertical_local hab habRe).mpr
      exact ⟨by simp [p, hre], by simpa [p] using hra⟩
    · apply (mem_segment_vertical_local hcd hcdRe).mpr
      exact ⟨by simp [p, hre, hcdRe], by simpa [p] using hrc⟩

private theorem horizontal_vertical_intersection_iff_local
    {a b c d : Tiling.Plane} (hab : a ≠ b) (hcd : c ≠ d)
    (habIm : a.im = b.im) (hcdRe : c.re = d.re) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty ↔
      c.re ∈ uIcc a.re b.re ∧ a.im ∈ uIcc c.im d.im := by
  constructor
  · rintro ⟨p, hpab, hpcd⟩
    have hpab' := (mem_segment_horizontal_local hab habIm).mp hpab
    have hpcd' := (mem_segment_vertical_local hcd hcdRe).mp hpcd
    exact ⟨by simpa [hpcd'.1] using hpab'.2, by simpa [hpab'.1] using hpcd'.2⟩
  · rintro ⟨hcx, hay⟩
    let p : Tiling.Plane := (c.re : ℂ) + (a.im : ℂ) * Complex.I
    refine ⟨p, ?_, ?_⟩
    · apply (mem_segment_horizontal_local hab habIm).mpr
      exact ⟨by simp [p], by simpa [p] using hcx⟩
    · apply (mem_segment_vertical_local hcd hcdRe).mpr
      exact ⟨by simp [p], by simpa [p] using hay⟩

private theorem vertical_horizontal_intersection_iff_local
    {a b c d : Tiling.Plane} (hab : a ≠ b) (hcd : c ≠ d)
    (habRe : a.re = b.re) (hcdIm : c.im = d.im) :
    (segment ℝ a b ∩ segment ℝ c d).Nonempty ↔
      a.re ∈ uIcc c.re d.re ∧ c.im ∈ uIcc a.im b.im := by
  rw [inter_comm]
  exact horizontal_vertical_intersection_iff_local hcd hab hcdIm habRe

private theorem source_cross_endpoint_control_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    {a b c d p : Tiling.Plane}
    (hpab : p ∈ segment ℝ a b) (hpcd : p ∈ segment ℝ c d)
    (hab : dist a b ≤ Metric.diam C.region.openCarrier)
    (hcd : dist c d ≤ Metric.diam C.region.openCarrier) :
    dist a c < P.controlRadius ∧ dist a d < P.controlRadius ∧
      dist b c < P.controlRadius ∧ dist b d < P.controlRadius := by
  have hpa := dist_le_dist_of_mem_segment_local hpab
  have hpc := dist_le_dist_of_mem_segment_local hpcd
  have hdiam : Metric.diam C.region.openCarrier < P.scale := by
    nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
  have hsum : Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier <
      P.controlRadius := by
    have hsum' : Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier <
        P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
    exact hsum'.trans P.scale_lt_controlRadius
  have hpaA : dist a p ≤ Metric.diam C.region.openCarrier := by
    calc dist a p = dist p a := dist_comm _ _
      _ ≤ dist b a := hpa.1
      _ = dist a b := dist_comm _ _
      _ ≤ _ := hab
  have hpaB : dist b p ≤ Metric.diam C.region.openCarrier := by
    calc dist b p = dist p b := dist_comm _ _
      _ ≤ dist b a := hpa.2
      _ = dist a b := dist_comm _ _
      _ ≤ _ := hab
  have hpcC : dist p c ≤ Metric.diam C.region.openCarrier := by
    calc dist p c ≤ dist d c := hpc.1
      _ = dist c d := dist_comm _ _
      _ ≤ _ := hcd
  have hpcD : dist p d ≤ Metric.diam C.region.openCarrier := by
    calc dist p d ≤ dist d c := hpc.2
      _ = dist c d := dist_comm _ _
      _ ≤ _ := hcd
  have hac : dist a c ≤ Metric.diam C.region.openCarrier +
      Metric.diam C.region.openCarrier := by
    calc
      dist a c ≤ dist a p + dist p c := dist_triangle _ _ _
      _ ≤ Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier := by
        exact add_le_add hpaA hpcC
  have had : dist a d ≤ Metric.diam C.region.openCarrier +
      Metric.diam C.region.openCarrier := by
    calc
      dist a d ≤ dist a p + dist p d := dist_triangle _ _ _
      _ ≤ Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier := by
        exact add_le_add hpaA hpcD
  have hbc : dist b c ≤ Metric.diam C.region.openCarrier +
      Metric.diam C.region.openCarrier := by
    calc
      dist b c ≤ dist b p + dist p c := dist_triangle _ _ _
      _ ≤ Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier := by
        exact add_le_add hpaB hpcC
  have hbd : dist b d ≤ Metric.diam C.region.openCarrier +
      Metric.diam C.region.openCarrier := by
    calc
      dist b d ≤ dist b p + dist p d := dist_triangle _ _ _
      _ ≤ Metric.diam C.region.openCarrier + Metric.diam C.region.openCarrier := by
        exact add_le_add hpaB hpcD
  exact ⟨lt_of_le_of_lt hac hsum, lt_of_le_of_lt had hsum,
    lt_of_le_of_lt hbc hsum, lt_of_le_of_lt hbd hsum⟩

private theorem target_cross_source_control_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {a b c d : ↥C.translatedVertices} {A B C' D' p : Tiling.Plane}
    (ha : mapTranslatedVertex phi a = A)
    (hb : mapTranslatedVertex phi b = B)
    (hc : mapTranslatedVertex phi c = C')
    (hd : mapTranslatedVertex phi d = D')
    (hpab : p ∈ segment ℝ A B) (hpcd : p ∈ segment ℝ C' D')
    (hAB : dist A B < P.scale / 4) (hCD : dist C' D' < P.scale / 4) :
    dist (a : Tiling.Plane) c < P.controlRadius ∧
      dist (a : Tiling.Plane) d < P.controlRadius ∧
      dist (b : Tiling.Plane) c < P.controlRadius ∧
      dist (b : Tiling.Plane) d < P.controlRadius := by
  have hpa := dist_le_dist_of_mem_segment_local hpab
  have hpc := dist_le_dist_of_mem_segment_local hpcd
  have hAC : dist A C' < P.scale / 2 := by
    calc
      dist A C' ≤ dist A p + dist p C' := dist_triangle _ _ _
      _ ≤ dist B A + dist D' C' := by
        rw [dist_comm A p]
        exact add_le_add hpa.1 hpc.1
      _ < P.scale / 2 := by
        calc
          _ < P.scale / 4 + P.scale / 4 := by
            simpa [dist_comm] using add_lt_add hAB hCD
          _ = P.scale / 2 := by ring
  have hAD : dist A D' < P.scale / 2 := by
    calc
      dist A D' ≤ dist A p + dist p D' := dist_triangle _ _ _
      _ ≤ dist B A + dist D' C' := by
        rw [dist_comm A p]
        exact add_le_add hpa.1 hpc.2
      _ < P.scale / 2 := by
        calc
          _ < P.scale / 4 + P.scale / 4 := by
            simpa [dist_comm] using add_lt_add hAB hCD
          _ = P.scale / 2 := by ring
  have hBC : dist B C' < P.scale / 2 := by
    calc
      dist B C' ≤ dist B p + dist p C' := dist_triangle _ _ _
      _ ≤ dist B A + dist D' C' := by
        exact add_le_add (by simpa [dist_comm] using hpa.2) hpc.1
      _ < P.scale / 2 := by
        calc
          _ < P.scale / 4 + P.scale / 4 := by
            simpa [dist_comm] using add_lt_add hAB hCD
          _ = P.scale / 2 := by ring
  have hBD : dist B D' < P.scale / 2 := by
    calc
      dist B D' ≤ dist B p + dist p D' := dist_triangle _ _ _
      _ ≤ dist B A + dist D' C' := by
        exact add_le_add (by simpa [dist_comm] using hpa.2) hpc.2
      _ < P.scale / 2 := by
        calc
          _ < P.scale / 4 + P.scale / 4 := by
            simpa [dist_comm] using add_lt_add hAB hCD
          _ = P.scale / 2 := by ring
  constructor
  · exact (deformation_coarselyProper P phi hphi a c (ha ▸ hc ▸ hAC)).trans
      P.scale_lt_controlRadius
  constructor
  · exact (deformation_coarselyProper P phi hphi a d (ha ▸ hd ▸ hAD)).trans
      P.scale_lt_controlRadius
  constructor
  · exact (deformation_coarselyProper P phi hphi b c (hb ▸ hc ▸ hBC)).trans
      P.scale_lt_controlRadius
  · exact (deformation_coarselyProper P phi hphi b d (hb ▸ hd ▸ hBD)).trans
      P.scale_lt_controlRadius

private theorem uIcc_inter_nonempty_iff_endpoint_local
    {a b c d : ℝ} :
    (uIcc a b ∩ uIcc c d).Nonempty ↔
      a ∈ uIcc c d ∨ b ∈ uIcc c d ∨ c ∈ uIcc a b ∨ d ∈ uIcc a b := by
  rcases le_total a b with hab | hba
  · rcases le_total c d with hcd | hdc
    · rw [uIcc_of_le hab, uIcc_of_le hcd]
      constructor
      · rintro ⟨x, ⟨hx1l, hx1u⟩, ⟨hx2l, hx2u⟩⟩
        by_cases hac : a ≤ c
        · by_cases hcb : c ≤ b
          · exact Or.inr (Or.inr (Or.inl ⟨hac, hcb⟩))
          · exfalso; linarith
        · exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (h | h | h | h)
        · exact ⟨a, ⟨le_rfl, hab⟩, h⟩
        · exact ⟨b, ⟨hab, le_rfl⟩, h⟩
        · exact ⟨c, h, ⟨le_rfl, hcd⟩⟩
        · exact ⟨d, h, ⟨hcd, le_rfl⟩⟩
    · rw [uIcc_of_le hab, uIcc_of_ge hdc]
      constructor
      · rintro ⟨x, ⟨hx1l, hx1u⟩, ⟨hx2l, hx2u⟩⟩
        by_cases had : a ≤ d
        · exact Or.inr (Or.inr (Or.inr ⟨had, by linarith⟩))
        · exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (h | h | h | h)
        · exact ⟨a, ⟨le_rfl, hab⟩, h⟩
        · exact ⟨b, ⟨hab, le_rfl⟩, h⟩
        · exact ⟨c, h, ⟨hdc, le_rfl⟩⟩
        · exact ⟨d, h, ⟨le_rfl, hdc⟩⟩
  · rcases le_total c d with hcd | hdc
    · rw [uIcc_of_ge hba, uIcc_of_le hcd]
      constructor
      · rintro ⟨x, ⟨hx1l, hx1u⟩, ⟨hx2l, hx2u⟩⟩
        by_cases hbc : b ≤ c
        · exact Or.inr (Or.inr (Or.inl ⟨hbc, by linarith⟩))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · rintro (h | h | h | h)
        · exact ⟨a, ⟨hba, le_rfl⟩, h⟩
        · exact ⟨b, ⟨le_rfl, hba⟩, h⟩
        · exact ⟨c, h, ⟨le_rfl, hcd⟩⟩
        · exact ⟨d, h, ⟨hcd, le_rfl⟩⟩
    · rw [uIcc_of_ge hba, uIcc_of_ge hdc]
      constructor
      · rintro ⟨x, ⟨hx1l, hx1u⟩, ⟨hx2l, hx2u⟩⟩
        by_cases hbd : b ≤ d
        · exact Or.inr (Or.inr (Or.inr ⟨hbd, by linarith⟩))
        · exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      · rintro (h | h | h | h)
        · exact ⟨a, ⟨hba, le_rfl⟩, h⟩
        · exact ⟨b, ⟨le_rfl, hba⟩, h⟩
        · exact ⟨c, h, ⟨hdc, le_rfl⟩⟩
        · exact ⟨d, h, ⟨le_rfl, hdc⟩⟩


private theorem edgeIntersectionTransport
    : ∀ {C : ApproximationContext} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (_D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (a b c d : ↥C.region.vertices) (s t : ↥C.centres),
      IsIntrinsicEdge C.region a b → IsIntrinsicEdge C.region c d →
      (segment ℝ ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ∩
          segment ℝ ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t) = ∅ ↔
        segment ℝ (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s)
            (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s) ∩
          segment ℝ (mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t)
            (mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t) = ∅) := by
  intro C P hScale phi hphi D Tphi hTphi a b c d s t hEdge₁ hEdge₂
  rcases hEdge₁ with ⟨ha, hb, hab, hfront₁, hnov₁⟩
  rcases hEdge₂ with ⟨hc, hd, hcd, hfront₂, hnov₂⟩
  have haxis₁ : (a : Tiling.Plane).im = (b : Tiling.Plane).im ∨
      (a : Tiling.Plane).re = (b : Tiling.Plane).re := by
    have hfront : openSegment ℝ (a : Tiling.Plane) b ⊆ frontier C.region.support := by
      intro z hz
      rw [← C.region.frontier_openCarrier_eq_frontier_support]
      exact hfront₁ hz
    rcases openSegment_axisAligned_local hab hfront with hre | him
    · exact Or.inr hre
    · exact Or.inl him
  have haxis₂ : (c : Tiling.Plane).im = (d : Tiling.Plane).im ∨
      (c : Tiling.Plane).re = (d : Tiling.Plane).re := by
    have hfront : openSegment ℝ (c : Tiling.Plane) d ⊆ frontier C.region.support := by
      intro z hz
      rw [← C.region.frontier_openCarrier_eq_frontier_support]
      exact hfront₂ hz
    rcases openSegment_axisAligned_local hcd hfront with hre | him
    · exact Or.inr hre
    · exact Or.inl him
  obtain ⟨x₁, hx₁, hm₁⟩ := mapTranslatedVertex_add_local phi a s
  obtain ⟨x₂, hx₂, hm₂⟩ := mapTranslatedVertex_add_local phi b s
  obtain ⟨x₃, hx₃, hm₃⟩ := mapTranslatedVertex_add_local phi c t
  obtain ⟨x₄, hx₄, hm₄⟩ := mapTranslatedVertex_add_local phi d t
  have htarget₁ : mapTranslatedVertex phi x₁ =
      mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s := by
    simpa [hTphi s] using hm₁
  have htarget₂ : mapTranslatedVertex phi x₂ =
      mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s := by
    simpa [hTphi s] using hm₂
  have htarget₃ : mapTranslatedVertex phi x₃ =
      mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t := by
    simpa [hTphi t] using hm₃
  have htarget₄ : mapTranslatedVertex phi x₄ =
      mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t := by
    simpa [hTphi t] using hm₄
  have hne₁ : x₁ ≠ x₂ := by
    intro h
    apply hab
    simpa [hx₁, hx₂] using congrArg Subtype.val h
  have hne₂ : x₃ ≠ x₄ := by
    intro h
    apply hcd
    simpa [hx₃, hx₄] using congrArg Subtype.val h
  have hPlaneNe₁ : (x₁ : Tiling.Plane) ≠ (x₂ : Tiling.Plane) := by
    simpa [hx₁, hx₂] using hab
  have hPlaneNe₂ : (x₃ : Tiling.Plane) ≠ (x₄ : Tiling.Plane) := by
    simpa [hx₃, hx₄] using hcd
  have hTne₁ : mapTranslatedVertex phi x₁ ≠ mapTranslatedVertex phi x₂ := by
    intro h
    exact hne₁ ((deformation_injectiveOnTranslatedVertices P phi hphi) h)
  have hTne₂ : mapTranslatedVertex phi x₃ ≠ mapTranslatedVertex phi x₄ := by
    intro h
    exact hne₂ ((deformation_injectiveOnTranslatedVertices P phi hphi) h)
  have hEdgeDist₁ : dist (x₁ : Tiling.Plane) (x₂ : Tiling.Plane) ≤
      Metric.diam C.region.openCarrier := by
    simpa [hx₁, hx₂] using
      (translated_edge_endpoint_dist_le_diam_local (K := C.region)
        (t := (s : Tiling.Plane)) a.2 b.2)
  have hEdgeDist₂ : dist (x₃ : Tiling.Plane) (x₄ : Tiling.Plane) ≤
      Metric.diam C.region.openCarrier := by
    simpa [hx₃, hx₄] using
      (translated_edge_endpoint_dist_le_diam_local (K := C.region)
        (t := (t : Tiling.Plane)) c.2 d.2)
  have hTargetDist₁ : dist (mapTranslatedVertex phi x₁)
      (mapTranslatedVertex phi x₂) < P.scale / 4 :=
    translated_edge_image_dist_lt_quarter_local P hScale phi hphi x₁ x₂ hx₁ hx₂
  have hTargetDist₂ : dist (mapTranslatedVertex phi x₃)
      (mapTranslatedVertex phi x₄) < P.scale / 4 :=
    translated_edge_image_dist_lt_quarter_local P hScale phi hphi x₃ x₄ hx₃ hx₄
  have hdiamControl : Metric.diam C.region.openCarrier < P.controlRadius := by
    have hdiamScale : Metric.diam C.region.openCarrier < P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
    exact hdiamScale.trans P.scale_lt_controlRadius
  have hedgeControl₁ : dist (x₁ : Tiling.Plane) (x₂ : Tiling.Plane) < P.controlRadius :=
    lt_of_le_of_lt hEdgeDist₁ hdiamControl
  have hedgeControl₂ : dist (x₃ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius :=
    lt_of_le_of_lt hEdgeDist₂ hdiamControl
  have hcoordSign (axis : Axis) {i j : ↥C.translatedVertices}
      (hij : dist (i : Tiling.Plane) (j : Tiling.Plane) < P.controlRadius) :
      Real.sign (Axis.coord axis ((i : Tiling.Plane) - (j : Tiling.Plane))) =
        Real.sign (Axis.coord axis (mapTranslatedVertex phi i -
          mapTranslatedVertex phi j)) :=
    (deformation_reflectsFiniteValues P phi hphi axis i j i j hij hij).1.symm
  have hcoordZero (axis : Axis) {i j : ↥C.translatedVertices}
      (hij : dist (i : Tiling.Plane) (j : Tiling.Plane) < P.controlRadius) :
      Axis.coord axis ((i : Tiling.Plane) - (j : Tiling.Plane)) = 0 ↔
        Axis.coord axis (mapTranslatedVertex phi i - mapTranslatedVertex phi j) = 0 :=
    (deformation_reflectsFiniteValues P phi hphi axis i j i j hij hij).2.1.symm
  have hmemRe {q i j : ↥C.translatedVertices}
      (hqi : dist (q : Tiling.Plane) (i : Tiling.Plane) < P.controlRadius)
      (hqj : dist (q : Tiling.Plane) (j : Tiling.Plane) < P.controlRadius) :
      (q : Tiling.Plane).re ∈ uIcc (i : Tiling.Plane).re (j : Tiling.Plane).re ↔
        (mapTranslatedVertex phi q).re ∈ uIcc
          (mapTranslatedVertex phi i).re (mapTranslatedVertex phi j).re := by
    apply uIcc_transport_local
    · simpa [Axis.coord] using hcoordSign Axis.horizontal hqi
    · simpa [Axis.coord] using hcoordSign Axis.horizontal hqj
  have hmemIm {q i j : ↥C.translatedVertices}
      (hqi : dist (q : Tiling.Plane) (i : Tiling.Plane) < P.controlRadius)
      (hqj : dist (q : Tiling.Plane) (j : Tiling.Plane) < P.controlRadius) :
      (q : Tiling.Plane).im ∈ uIcc (i : Tiling.Plane).im (j : Tiling.Plane).im ↔
        (mapTranslatedVertex phi q).im ∈ uIcc
          (mapTranslatedVertex phi i).im (mapTranslatedVertex phi j).im := by
    apply uIcc_transport_local
    · simpa [Axis.coord] using hcoordSign Axis.vertical hqi
    · simpa [Axis.coord] using hcoordSign Axis.vertical hqj
  have hforward :
      (segment ℝ ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ∩
        segment ℝ ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t)).Nonempty →
      (segment ℝ (mapTranslatedVertex phi x₁) (mapTranslatedVertex phi x₂) ∩
        segment ℝ (mapTranslatedVertex phi x₃) (mapTranslatedVertex phi x₄)).Nonempty := by
    intro hp
    have hEdgeDist₁' : dist ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ≤
        Metric.diam C.region.openCarrier := by
      simpa [hx₁, hx₂] using hEdgeDist₁
    have hEdgeDist₂' : dist ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t) ≤
        Metric.diam C.region.openCarrier := by
      simpa [hx₃, hx₄] using hEdgeDist₂
    have hcross := source_cross_endpoint_control_local P hScale
      (p := Classical.choose (Set.inter_nonempty.mp hp))
      (Classical.choose_spec (Set.inter_nonempty.mp hp)).1
      (Classical.choose_spec (Set.inter_nonempty.mp hp)).2
      hEdgeDist₁' hEdgeDist₂'
    have hcrossX :
        dist (x₁ : Tiling.Plane) (x₃ : Tiling.Plane) < P.controlRadius ∧
        dist (x₁ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius ∧
        dist (x₂ : Tiling.Plane) (x₃ : Tiling.Plane) < P.controlRadius ∧
        dist (x₂ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius := by
      simpa [hx₁, hx₂, hx₃, hx₄] using hcross
    have hPlaneNe₁ : (x₁ : Tiling.Plane) ≠ (x₂ : Tiling.Plane) := by
      simpa [hx₁, hx₂] using hab
    have hPlaneNe₂ : (x₃ : Tiling.Plane) ≠ (x₄ : Tiling.Plane) := by
      simpa [hx₃, hx₄] using hcd
    have haxis₁' : (x₁ : Tiling.Plane).im = (x₂ : Tiling.Plane).im ∨
        (x₁ : Tiling.Plane).re = (x₂ : Tiling.Plane).re := by
      simpa [hx₁, hx₂, Complex.add_re, Complex.add_im] using haxis₁
    have haxis₂' : (x₃ : Tiling.Plane).im = (x₄ : Tiling.Plane).im ∨
        (x₃ : Tiling.Plane).re = (x₄ : Tiling.Plane).re := by
      simpa [hx₃, hx₄, Complex.add_re, Complex.add_im] using haxis₂
    rcases haxis₁' with h₁ | h₁ <;> rcases haxis₂' with h₂ | h₂
    · have ht₁ : (mapTranslatedVertex phi x₁).im =
          (mapTranslatedVertex phi x₂).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).im =
          (mapTranslatedVertex phi x₄).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have hs := (horizontal_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mp
        (by simpa [hx₁, hx₂, hx₃, hx₄] using hp)
      apply (horizontal_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mpr
      refine ⟨?_, ?_⟩
      · have hz := (hcoordZero Axis.vertical hcrossX.1).mp
          (by simpa [Axis.coord, hx₁, hx₃] using sub_eq_zero.mpr hs.1)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      · apply (uIcc_inter_nonempty_iff_endpoint_local).mpr
        rcases (uIcc_inter_nonempty_iff_endpoint_local).mp hs.2 with h | h | h | h
        · exact Or.inl ((hmemRe hcrossX.1 hcrossX.2.1).mp h)
        · exact Or.inr (Or.inl ((hmemRe hcrossX.2.2.1 hcrossX.2.2.2).mp h))
        · exact Or.inr (Or.inr (Or.inl ((hmemRe (by simpa [dist_comm] using hcrossX.1)
              (by simpa [dist_comm] using hcrossX.2.2.1)).mp h)))
        · exact Or.inr (Or.inr (Or.inr ((hmemRe (by simpa [dist_comm] using hcrossX.2.1)
              (by simpa [dist_comm] using hcrossX.2.2.2)).mp h)))
    · have ht₁ : (mapTranslatedVertex phi x₁).im =
          (mapTranslatedVertex phi x₂).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).re =
          (mapTranslatedVertex phi x₄).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have hs := (horizontal_vertical_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mp
        (by simpa [hx₁, hx₂, hx₃, hx₄] using hp)
      apply (horizontal_vertical_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mpr
      refine ⟨?_, ?_⟩
      · exact (by simpa [Axis.coord] using
          (hmemRe (by simpa [dist_comm] using hcrossX.1)
            (by simpa [dist_comm] using hcrossX.2.2.1)).mp hs.1)
      · exact (by simpa [Axis.coord] using
          (hmemIm hcrossX.1 hcrossX.2.1).mp hs.2)
    · have ht₁ : (mapTranslatedVertex phi x₁).re =
          (mapTranslatedVertex phi x₂).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).im =
          (mapTranslatedVertex phi x₄).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have hs := (vertical_horizontal_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mp
        (by simpa [hx₁, hx₂, hx₃, hx₄] using hp)
      apply (vertical_horizontal_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mpr
      refine ⟨?_, ?_⟩
      · exact (by simpa [Axis.coord] using
          (hmemRe hcrossX.1 hcrossX.2.1).mp hs.1)
      · exact (by simpa [Axis.coord] using
          (hmemIm (by simpa [dist_comm] using hcrossX.1)
            (by simpa [dist_comm] using hcrossX.2.2.1)).mp hs.2)
    · have ht₁ : (mapTranslatedVertex phi x₁).re =
          (mapTranslatedVertex phi x₂).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).re =
          (mapTranslatedVertex phi x₄).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have hs := (vertical_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mp
        (by simpa [hx₁, hx₂, hx₃, hx₄] using hp)
      apply (vertical_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mpr
      refine ⟨?_, ?_⟩
      · have hz := (hcoordZero Axis.horizontal hcrossX.1).mp
          (by simpa [Axis.coord, hx₁, hx₃] using sub_eq_zero.mpr hs.1)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      · apply (uIcc_inter_nonempty_iff_endpoint_local).mpr
        rcases (uIcc_inter_nonempty_iff_endpoint_local).mp hs.2 with h | h | h | h
        · exact Or.inl ((hmemIm hcrossX.1 hcrossX.2.1).mp h)
        · exact Or.inr (Or.inl ((hmemIm hcrossX.2.2.1 hcrossX.2.2.2).mp h))
        · exact Or.inr (Or.inr (Or.inl ((hmemIm (by simpa [dist_comm] using hcrossX.1)
              (by simpa [dist_comm] using hcrossX.2.2.1)).mp h)))
        · exact Or.inr (Or.inr (Or.inr ((hmemIm (by simpa [dist_comm] using hcrossX.2.1)
              (by simpa [dist_comm] using hcrossX.2.2.2)).mp h)))
  have hback :
      (segment ℝ (mapTranslatedVertex phi x₁) (mapTranslatedVertex phi x₂) ∩
        segment ℝ (mapTranslatedVertex phi x₃) (mapTranslatedVertex phi x₄)).Nonempty →
      (segment ℝ ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ∩
        segment ℝ ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t)).Nonempty := by
    rw [← hx₁, ← hx₂, ← hx₃, ← hx₄]
    intro hp
    obtain ⟨p, hp1, hp2⟩ := Set.inter_nonempty.mp hp
    have hp1' : p ∈ segment ℝ
        (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s)
        (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s) := by
      simpa [← htarget₁, ← htarget₂] using hp1
    have hp2' : p ∈ segment ℝ
        (mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t)
        (mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t) := by
      simpa [← htarget₃, ← htarget₄] using hp2
    have hTargetDist₁' : dist
        (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s)
        (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s) < P.scale / 4 := by
      simpa [← htarget₁, ← htarget₂] using hTargetDist₁
    have hTargetDist₂' : dist
        (mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t)
        (mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t) < P.scale / 4 := by
      simpa [← htarget₃, ← htarget₄] using hTargetDist₂
    have hcross := target_cross_source_control_local P phi hphi
      (ha := htarget₁) (hb := htarget₂) (hc := htarget₃) (hd := htarget₄)
      hp1' hp2' hTargetDist₁' hTargetDist₂'
    have hcrossX :
        dist (x₁ : Tiling.Plane) (x₃ : Tiling.Plane) < P.controlRadius ∧
        dist (x₁ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius ∧
        dist (x₂ : Tiling.Plane) (x₃ : Tiling.Plane) < P.controlRadius ∧
        dist (x₂ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius := hcross
    have haxis₁' : (x₁ : Tiling.Plane).im = (x₂ : Tiling.Plane).im ∨
        (x₁ : Tiling.Plane).re = (x₂ : Tiling.Plane).re := by
      simpa [hx₁, hx₂, Complex.add_re, Complex.add_im] using haxis₁
    have haxis₂' : (x₃ : Tiling.Plane).im = (x₄ : Tiling.Plane).im ∨
        (x₃ : Tiling.Plane).re = (x₄ : Tiling.Plane).re := by
      simpa [hx₃, hx₄, Complex.add_re, Complex.add_im] using haxis₂
    rcases haxis₁' with h₁ | h₁ <;> rcases haxis₂' with h₂ | h₂
    · have ht₁ : (mapTranslatedVertex phi x₁).im = (mapTranslatedVertex phi x₂).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).im = (mapTranslatedVertex phi x₄).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht := (horizontal_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mp hp
      have hsCross : (x₁ : Tiling.Plane).im = (x₃ : Tiling.Plane).im := by
        have hz := (hcoordZero Axis.vertical (by simpa [dist_comm] using hcrossX.1)).mpr
          (by simpa [Axis.coord] using sub_eq_zero.mpr ht.1)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      apply (horizontal_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mpr
      refine ⟨hsCross, ?_⟩
      apply uIcc_inter_nonempty_iff_endpoint_local.mpr
      rcases uIcc_inter_nonempty_iff_endpoint_local.mp ht.2 with h | h | h | h
      · exact Or.inl ((hmemRe hcrossX.1 hcrossX.2.1).mpr h)
      · exact Or.inr (Or.inl ((hmemRe hcrossX.2.2.1 hcrossX.2.2.2).mpr h))
      · exact Or.inr (Or.inr (Or.inl ((hmemRe (by simpa [dist_comm] using hcrossX.1)
          (by simpa [dist_comm] using hcrossX.2.2.1)).mpr h)))
      · exact Or.inr (Or.inr (Or.inr ((hmemRe (by simpa [dist_comm] using hcrossX.2.1)
          (by simpa [dist_comm] using hcrossX.2.2.2)).mpr h)))
    · have ht₁ : (mapTranslatedVertex phi x₁).im = (mapTranslatedVertex phi x₂).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).re = (mapTranslatedVertex phi x₄).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht := (horizontal_vertical_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mp hp
      have hs1 := (hmemRe (by simpa [dist_comm] using hcrossX.1)
        (by simpa [dist_comm] using hcrossX.2.2.1)).mpr ht.1
      have hs2 := (hmemIm hcrossX.1 hcrossX.2.1).mpr ht.2
      apply (horizontal_vertical_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mpr
      exact ⟨by simpa [Axis.coord] using hs1, by simpa [Axis.coord] using hs2⟩
    · have ht₁ : (mapTranslatedVertex phi x₁).re = (mapTranslatedVertex phi x₂).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).im = (mapTranslatedVertex phi x₄).im := by
        have hz := (hcoordZero Axis.vertical hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht := (vertical_horizontal_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mp hp
      have hs1 := (hmemRe hcrossX.1 hcrossX.2.1).mpr ht.1
      have hs2 := (hmemIm (by simpa [dist_comm] using hcrossX.1)
        (by simpa [dist_comm] using hcrossX.2.2.1)).mpr ht.2
      apply (vertical_horizontal_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mpr
      exact ⟨by simpa [Axis.coord] using hs1, by simpa [Axis.coord] using hs2⟩
    · have ht₁ : (mapTranslatedVertex phi x₁).re = (mapTranslatedVertex phi x₂).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₁).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₁)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht₂ : (mapTranslatedVertex phi x₃).re = (mapTranslatedVertex phi x₄).re := by
        have hz := (hcoordZero Axis.horizontal hedgeControl₂).mp
          (by simpa [Axis.coord] using sub_eq_zero.mpr h₂)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      have ht := (vertical_intersection_iff_local hTne₁ hTne₂ ht₁ ht₂).mp hp
      have hsCross : (x₁ : Tiling.Plane).re = (x₃ : Tiling.Plane).re := by
        have hz := (hcoordZero Axis.horizontal (by simpa [dist_comm] using hcrossX.1)).mpr
          (by simpa [Axis.coord] using sub_eq_zero.mpr ht.1)
        simpa [Axis.coord] using sub_eq_zero.mp hz
      apply (vertical_intersection_iff_local hPlaneNe₁ hPlaneNe₂ h₁ h₂).mpr
      refine ⟨hsCross, ?_⟩
      apply uIcc_inter_nonempty_iff_endpoint_local.mpr
      rcases uIcc_inter_nonempty_iff_endpoint_local.mp ht.2 with h | h | h | h
      · exact Or.inl ((hmemIm hcrossX.1 hcrossX.2.1).mpr h)
      · exact Or.inr (Or.inl ((hmemIm hcrossX.2.2.1 hcrossX.2.2.2).mpr h))
      · exact Or.inr (Or.inr (Or.inl ((hmemIm (by simpa [dist_comm] using hcrossX.1)
          (by simpa [dist_comm] using hcrossX.2.2.1)).mpr h)))
      · exact Or.inr (Or.inr (Or.inr ((hmemIm (by simpa [dist_comm] using hcrossX.2.1)
          (by simpa [dist_comm] using hcrossX.2.2.2)).mpr h)))
  have hnonempty :
      (segment ℝ ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ∩
        segment ℝ ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t)).Nonempty ↔
      (segment ℝ (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s)
          (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s) ∩
        segment ℝ (mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t)
          (mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t)).Nonempty := by
    have hiff :
        (segment ℝ ((a : Tiling.Plane) + s) ((b : Tiling.Plane) + s) ∩
          segment ℝ ((c : Tiling.Plane) + t) ((d : Tiling.Plane) + t)).Nonempty ↔
        (segment ℝ (mapTranslatedVertex phi x₁) (mapTranslatedVertex phi x₂) ∩
          segment ℝ (mapTranslatedVertex phi x₃) (mapTranslatedVertex phi x₄)).Nonempty :=
      ⟨hforward, hback⟩
    simpa [htarget₁, htarget₂, htarget₃, htarget₄] using hiff
  simpa only [Set.not_nonempty_iff_eq_empty] using hnonempty.not

private theorem zero_of_sign_eq_zero_local
    {x y : ℝ} (hs : Real.sign x = Real.sign y) (hx : x = 0) : y = 0 := by
  apply Real.sign_eq_zero_iff.mp
  rw [← hs]
  exact Real.sign_eq_zero_iff.mpr hx



open Tiling AxisParallel

private def IsHorizontalSideLocal (K : Region) (v w : K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support ∩ (K.vertices : Set Tiling.Plane)ᶜ





private theorem lt_iff_of_sign_sub_eq_local {a b A B : ℝ}
    (h : Real.sign (b - a) = Real.sign (B - A)) :
    a < b ↔ A < B := by
  have forward {x y X Y : ℝ}
      (hsign : Real.sign (y - x) = Real.sign (Y - X))
      (hxy : x < y) : X < Y := by
    have hsource : Real.sign (y - x) = 1 :=
      Real.sign_of_pos (sub_pos.mpr hxy)
    have htarget : Real.sign (Y - X) = 1 := hsign.symm.trans hsource
    by_contra hnot
    have hle : Y - X ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    rcases hle.eq_or_lt with hzero | hneg
    · rw [hzero, Real.sign_zero] at htarget
      norm_num at htarget
    · rw [Real.sign_of_neg hneg] at htarget
      norm_num at htarget
  exact ⟨forward h, forward h.symm⟩

private theorem intervalOverlap_transport_local
    {a b c d A B C' D' : ℝ}
    (hab : Real.sign (b - a) = Real.sign (B - A))
    (hac : Real.sign (c - a) = Real.sign (C' - A))
    (had : Real.sign (d - a) = Real.sign (D' - A))
    (hbc : Real.sign (c - b) = Real.sign (C' - B))
    (hbd : Real.sign (d - b) = Real.sign (D' - B))
    (hcd : Real.sign (d - c) = Real.sign (D' - C')) :
    (Set.Ioo (min a b) (max a b) ∩ Set.Ioo (min c d) (max c d)).Nonempty ↔
      (Set.Ioo (min A B) (max A B) ∩ Set.Ioo (min C' D') (max C' D')).Nonempty := by
  have hAB : a < b ↔ A < B := lt_iff_of_sign_sub_eq_local hab
  have hAC : a < c ↔ A < C' := lt_iff_of_sign_sub_eq_local hac
  have hAD : a < d ↔ A < D' := lt_iff_of_sign_sub_eq_local had
  have hBC : b < c ↔ B < C' := lt_iff_of_sign_sub_eq_local hbc
  have hBD : b < d ↔ B < D' := lt_iff_of_sign_sub_eq_local hbd
  have hCD : c < d ↔ C' < D' := lt_iff_of_sign_sub_eq_local hcd
  have negSign {x y X Y : ℝ} (h : Real.sign (y - x) = Real.sign (Y - X)) :
      Real.sign (x - y) = Real.sign (X - Y) := by
    rw [← neg_sub y x, ← neg_sub Y X, Real.sign_neg, Real.sign_neg]
    exact congrArg Neg.neg h
  have hBA : b < a ↔ B < A := lt_iff_of_sign_sub_eq_local (negSign hab)
  have hCA : c < a ↔ C' < A := lt_iff_of_sign_sub_eq_local (negSign hac)
  have hDA : d < a ↔ D' < A := lt_iff_of_sign_sub_eq_local (negSign had)
  have hCB : c < b ↔ C' < B := lt_iff_of_sign_sub_eq_local (negSign hbc)
  have hDB : d < b ↔ D' < B := lt_iff_of_sign_sub_eq_local (negSign hbd)
  have hDC : d < c ↔ D' < C' := lt_iff_of_sign_sub_eq_local (negSign hcd)
  simp [Set.Ioo_inter_Ioo, Set.nonempty_Ioo, hAB, hAC, hAD, hBC, hBD, hCD,
    hBA, hCA, hDA, hCB, hDB, hDC]


private theorem mem_uIcc_of_strict_bounds_local {x y r : ℝ}
    (hlo : min x y < r) (hhi : r < max x y) : r ∈ Set.uIcc x y := by
  rw [Set.mem_uIcc]
  rcases le_total x y with hxy | hyx
  · left
    rw [min_eq_left hxy] at hlo
    rw [max_eq_right hxy] at hhi
    exact ⟨le_of_lt hlo, le_of_lt hhi⟩
  · right
    rw [min_eq_right hyx] at hlo
    rw [max_eq_left hyx] at hhi
    exact ⟨le_of_lt hlo, le_of_lt hhi⟩

private theorem translated_order_transport_local
    {C : ApproximationContext} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hphi : IsEpsilonApproximation C P.threshold phi)
    {x y : C.translatedVertices}
    (hxy : dist (x : Tiling.Plane) (y : Tiling.Plane) < P.controlRadius) :
    (x : Tiling.Plane).re < (y : Tiling.Plane).re ↔
      (mapTranslatedVertex phi x).re < (mapTranslatedVertex phi y).re := by
  apply lt_iff_of_sign_sub_eq_local
  have hs := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
    y x y x (by simpa [dist_comm] using hxy) (by simpa [dist_comm] using hxy)).1.symm
  simpa [Axis.coord] using hs

private theorem properContactTransport
    : ∀ {C : ApproximationContext} (P : FLCControlPackage C)
      (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hphi : IsEpsilonApproximation C P.threshold phi)
      (D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane)
      (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
      (s t : ↥C.centres),
      Continuous.HorizontalProperContact C.region s t ↔
        Continuous.HorizontalProperContact D.deformedRegion (Tphi s) (Tphi t) := by
  intro C P hScale phi hphi D Tphi hTphi s t
  rw [Continuous.horizontalProperContact_iff_exists_intrinsicSides,
    Continuous.horizontalProperContact_iff_exists_intrinsicSides]
  constructor
  · rintro ⟨v, v', w, w', hvv, hww, hheight, hoverlap⟩
    have hvsrc : IsHorizontalSideLocal C.region v v' := by
      simpa [IsHorizontalSideLocal, Set.sdiff_eq] using hvv
    have hwsrc : IsHorizontalSideLocal C.region w w' := by
      simpa [IsHorizontalSideLocal, Set.sdiff_eq] using hww
    obtain ⟨hvMem, hv'Mem, hvTarget⟩ :=
      (intrinsicHorizontalSide_transport C phi D v v').mp
        (by simpa only [IsHorizontalSideLocal, Set.sdiff_eq] using hvsrc)
    obtain ⟨hwMem, hw'Mem, hwTarget⟩ :=
      (intrinsicHorizontalSide_transport C phi D w w').mp
        (by simpa only [IsHorizontalSideLocal, Set.sdiff_eq] using hwsrc)
    let V : D.deformedRegion.vertices :=
      ⟨mapPoint phi (C.vertexPoint v.1 v.2), hvMem⟩
    let V' : D.deformedRegion.vertices :=
      ⟨mapPoint phi (C.vertexPoint v'.1 v'.2), hv'Mem⟩
    let W : D.deformedRegion.vertices :=
      ⟨mapPoint phi (C.vertexPoint w.1 w.2), hwMem⟩
    let W' : D.deformedRegion.vertices :=
      ⟨mapPoint phi (C.vertexPoint w'.1 w'.2), hw'Mem⟩
    obtain ⟨x₁, hx₁, hm₁⟩ := mapTranslatedVertex_add_local phi v s
    obtain ⟨x₂, hx₂, hm₂⟩ := mapTranslatedVertex_add_local phi v' s
    obtain ⟨x₃, hx₃, hm₃⟩ := mapTranslatedVertex_add_local phi w t
    obtain ⟨x₄, hx₄, hm₄⟩ := mapTranslatedVertex_add_local phi w' t
    have hdiamV := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (s : Tiling.Plane)) v.2 v'.2
    have hdiamW := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (t : Tiling.Plane)) w.2 w'.2
    have hdiam : Metric.diam C.region.openCarrier < P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
    have hVctrl : dist (x₁ : Tiling.Plane) (x₂ : Tiling.Plane) < P.controlRadius :=
      lt_of_le_of_lt (by simpa [hx₁, hx₂] using hdiamV) (hdiam.trans P.scale_lt_controlRadius)
    have hWctrl : dist (x₃ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius :=
      lt_of_le_of_lt (by simpa [hx₃, hx₄] using hdiamW) (hdiam.trans P.scale_lt_controlRadius)
    have hVne : (v : Tiling.Plane) + s ≠ (v' : Tiling.Plane) + s := by
      intro h; apply hvv.1; exact add_right_cancel h
    have hWne : (w : Tiling.Plane) + t ≠ (w' : Tiling.Plane) + t := by
      intro h; apply hww.1; exact add_right_cancel h
    have hoverlap' :
        max (min (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
            (min (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re) <
          min (max (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
            (max (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re) := by
      simpa [Set.Ioo_inter_Ioo, Set.nonempty_Ioo] using hoverlap
    let r : ℝ :=
      (max (min (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
          (min (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re) +
        min (max (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
          (max (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re)) / 2
    have hrlo : max (min (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
          (min (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re) < r := by
      dsimp [r]; linarith
    have hrhi : r < min (max (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
          (max (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re) := by
      dsimp [r]; linarith
    let p : Tiling.Plane := (r : ℂ) + ((v : Tiling.Plane) + s).im * Complex.I
    have himV : ((v : Tiling.Plane) + s).im =
        ((v' : Tiling.Plane) + s).im := by simpa [Complex.add_im] using hvv.2.1
    have himW : ((w : Tiling.Plane) + t).im =
        ((w' : Tiling.Plane) + t).im := by simpa [Complex.add_im] using hww.2.1
    have hpV : p ∈ segment ℝ ((v : Tiling.Plane) + s) ((v' : Tiling.Plane) + s) := by
      apply (mem_segment_horizontal_local hVne himV).mpr
      refine ⟨by simp [p], mem_uIcc_of_strict_bounds_local ?_ ?_⟩
      · have hminV : min ((v : Tiling.Plane).re + (s : Tiling.Plane).re)
            ((v' : Tiling.Plane).re + (s : Tiling.Plane).re) < r := by
          simpa only [Complex.add_re, ← min_add_add_right] using
            (lt_of_le_of_lt (le_max_left _ _) hrlo)
        simpa [p, Complex.add_re] using hminV
      · have hmaxV : r < max ((v : Tiling.Plane).re + (s : Tiling.Plane).re)
            ((v' : Tiling.Plane).re + (s : Tiling.Plane).re) := by
          simpa only [Complex.add_re, ← max_add_add_right] using
            (lt_of_lt_of_le hrhi (min_le_left _ _))
        simpa [p, Complex.add_re] using hmaxV
    have hpW : p ∈ segment ℝ ((w : Tiling.Plane) + t) ((w' : Tiling.Plane) + t) := by
      apply (mem_segment_horizontal_local hWne himW).mpr
      refine ⟨?_, mem_uIcc_of_strict_bounds_local ?_ ?_⟩
      · simp [p, hheight]
      · have hminW : min ((w : Tiling.Plane).re + (t : Tiling.Plane).re)
            ((w' : Tiling.Plane).re + (t : Tiling.Plane).re) < r := by
          simpa only [Complex.add_re, ← min_add_add_right] using
            (lt_of_le_of_lt (le_max_right _ _) hrlo)
        simpa [p, Complex.add_re] using hminW
      · have hmaxW : r < max ((w : Tiling.Plane).re + (t : Tiling.Plane).re)
            ((w' : Tiling.Plane).re + (t : Tiling.Plane).re) := by
          simpa only [Complex.add_re, ← max_add_add_right] using
            (lt_of_lt_of_le hrhi (min_le_right _ _))
        simpa [p, Complex.add_re] using hmaxW
    have hcross := source_cross_endpoint_control_local P hScale hpV hpW hdiamV hdiamW
    have hsig12 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₂ x₁ x₂ x₁ (by simpa [dist_comm] using hVctrl)
        (by simpa [dist_comm] using hVctrl)).1.symm
    have hsig13 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₃ x₁ x₃ x₁ (by simpa [dist_comm, hx₁, hx₃] using hcross.1)
        (by simpa [dist_comm, hx₁, hx₃] using hcross.1)).1.symm
    have hsig14 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₁ x₄ x₁ (by simpa [dist_comm, hx₁, hx₄] using hcross.2.1)
        (by simpa [dist_comm, hx₁, hx₄] using hcross.2.1)).1.symm
    have hsig23 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₃ x₂ x₃ x₂ (by simpa [dist_comm, hx₂, hx₃] using hcross.2.2.1)
        (by simpa [dist_comm, hx₂, hx₃] using hcross.2.2.1)).1.symm
    have hsig24 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₂ x₄ x₂ (by simpa [dist_comm, hx₂, hx₄] using hcross.2.2.2)
        (by simpa [dist_comm, hx₂, hx₄] using hcross.2.2.2)).1.symm
    have hsig34 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₃ x₄ x₃ (by simpa [dist_comm] using hWctrl)
        (by simpa [dist_comm] using hWctrl)).1.symm
    have hheightTarget :
        ((V : Tiling.Plane) + Tphi s).im =
          ((W : Tiling.Plane) + Tphi t).im := by
      have hz := (deformation_reflectsFiniteValues P phi hphi Axis.vertical
        x₁ x₃ x₁ x₃ (by simpa [hx₁, hx₃] using hcross.1)
          (by simpa [hx₁, hx₃] using hcross.1)).2.1.mpr
        (by
          simpa [hx₁, hx₃, Axis.coord] using
            sub_eq_zero.mpr (by simpa [hx₁, hx₃] using hheight))
      have himTarget : (mapTranslatedVertex phi x₁).im =
          (mapTranslatedVertex phi x₃).im := by
        simpa [Axis.coord] using sub_eq_zero.mp hz
      simpa [V, W, hm₁, hm₃, hTphi, Complex.add_im] using himTarget
    have hoverlapTarget :
        (Set.Ioo (min (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
          (max (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re) ∩
        Set.Ioo (min (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re)
          (max (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re)).Nonempty := by
      have hInt := (intervalOverlap_transport_local
        (a := (x₁ : Tiling.Plane).re) (b := (x₂ : Tiling.Plane).re)
        (c := (x₃ : Tiling.Plane).re) (d := (x₄ : Tiling.Plane).re)
        (A := (mapTranslatedVertex phi x₁).re) (B := (mapTranslatedVertex phi x₂).re)
        (C' := (mapTranslatedVertex phi x₃).re) (D' := (mapTranslatedVertex phi x₄).re)
        (by simpa [Axis.coord] using hsig12)
        (by simpa [Axis.coord] using hsig13)
        (by simpa [Axis.coord] using hsig14)
        (by simpa [Axis.coord] using hsig23)
        (by simpa [Axis.coord] using hsig24)
        (by simpa [Axis.coord] using hsig34)).mp
        (by simpa only [hx₁, hx₂, hx₃, hx₄, Complex.add_re,
          ← min_add_add_right, ← max_add_add_right] using hoverlap)
      simpa only [V, V', hm₁, hm₂, hm₃, hm₄, hTphi,
        ← min_add_add_right, ← max_add_add_right, Complex.add_re] using hInt
    refine ⟨V, V', W, W', ?_, ?_, hheightTarget, hoverlapTarget⟩
    · simpa [V, V', IsHorizontalSideLocal, Set.sdiff_eq] using hvTarget
    · simpa [W, W', IsHorizontalSideLocal, Set.sdiff_eq] using hwTarget
  · rintro ⟨V, V', W, W', hVV, hWW, hheight, hoverlap⟩
    let v := D.vertexEquiv.symm V
    let v' := D.vertexEquiv.symm V'
    let w := D.vertexEquiv.symm W
    let w' := D.vertexEquiv.symm W'
    have hvMap : mapPoint phi (C.vertexPoint v.1 v.2) = (V : Tiling.Plane) := by
      calc
        mapPoint phi (C.vertexPoint v.1 v.2) = D.planarHomeomorph v :=
          (D.vertex_agreement v.1 v.2).symm
        _ = (D.vertexEquiv v : Tiling.Plane) := rfl
        _ = (V : Tiling.Plane) := congrArg Subtype.val (D.vertexEquiv.apply_symm_apply V)
    have hv'Map : mapPoint phi (C.vertexPoint v'.1 v'.2) = (V' : Tiling.Plane) := by
      calc
        mapPoint phi (C.vertexPoint v'.1 v'.2) = D.planarHomeomorph v' :=
          (D.vertex_agreement v'.1 v'.2).symm
        _ = (D.vertexEquiv v' : Tiling.Plane) := rfl
        _ = (V' : Tiling.Plane) := congrArg Subtype.val (D.vertexEquiv.apply_symm_apply V')
    have hwMap : mapPoint phi (C.vertexPoint w.1 w.2) = (W : Tiling.Plane) := by
      calc
        mapPoint phi (C.vertexPoint w.1 w.2) = D.planarHomeomorph w :=
          (D.vertex_agreement w.1 w.2).symm
        _ = (D.vertexEquiv w : Tiling.Plane) := rfl
        _ = (W : Tiling.Plane) := congrArg Subtype.val (D.vertexEquiv.apply_symm_apply W)
    have hw'Map : mapPoint phi (C.vertexPoint w'.1 w'.2) = (W' : Tiling.Plane) := by
      calc
        mapPoint phi (C.vertexPoint w'.1 w'.2) = D.planarHomeomorph w' :=
          (D.vertex_agreement w'.1 w'.2).symm
        _ = (D.vertexEquiv w' : Tiling.Plane) := rfl
        _ = (W' : Tiling.Plane) := congrArg Subtype.val (D.vertexEquiv.apply_symm_apply W')
    have hvsrc : IsHorizontalSideLocal C.region v v' := by
      simp only [IsHorizontalSideLocal, ← Set.sdiff_eq]
      apply (intrinsicHorizontalSide_transport C phi D v v').mpr
      refine ⟨?_, ?_, ?_⟩
      · rw [hvMap]; exact V.2
      · rw [hv'Map]; exact V'.2
      · simpa [IsHorizontalSideLocal, Set.sdiff_eq, hvMap, hv'Map] using hVV
    have hwsrc : IsHorizontalSideLocal C.region w w' := by
      simp only [IsHorizontalSideLocal, ← Set.sdiff_eq]
      apply (intrinsicHorizontalSide_transport C phi D w w').mpr
      refine ⟨?_, ?_, ?_⟩
      · rw [hwMap]; exact W.2
      · rw [hw'Map]; exact W'.2
      · simpa [IsHorizontalSideLocal, Set.sdiff_eq, hwMap, hw'Map] using hWW
    have hvv : (v.1 ≠ v'.1 ∧ v.1.im = v'.1.im ∧
        openSegment ℝ v.1 v'.1 ⊆
          frontier C.region.support ∩ (C.region.vertices : Set Tiling.Plane)ᶜ) := by
      simpa [IsHorizontalSideLocal, Set.sdiff_eq] using hvsrc
    have hww : (w.1 ≠ w'.1 ∧ w.1.im = w'.1.im ∧
        openSegment ℝ w.1 w'.1 ⊆
          frontier C.region.support ∩ (C.region.vertices : Set Tiling.Plane)ᶜ) := by
      simpa [IsHorizontalSideLocal, Set.sdiff_eq] using hwsrc
    obtain ⟨x₁, hx₁, hm₁⟩ := mapTranslatedVertex_add_local phi v s
    obtain ⟨x₂, hx₂, hm₂⟩ := mapTranslatedVertex_add_local phi v' s
    obtain ⟨x₃, hx₃, hm₃⟩ := mapTranslatedVertex_add_local phi w t
    obtain ⟨x₄, hx₄, hm₄⟩ := mapTranslatedVertex_add_local phi w' t
    have hA1 : mapTranslatedVertex phi x₁ = (V : Tiling.Plane) + Tphi s := by
      simp [hm₁, hvMap, hTphi]
    have hA2 : mapTranslatedVertex phi x₂ = (V' : Tiling.Plane) + Tphi s := by
      simp [hm₂, hv'Map, hTphi]
    have hA3 : mapTranslatedVertex phi x₃ = (W : Tiling.Plane) + Tphi t := by
      simp [hm₃, hwMap, hTphi]
    have hA4 : mapTranslatedVertex phi x₄ = (W' : Tiling.Plane) + Tphi t := by
      simp [hm₄, hw'Map, hTphi]
    have hdiamV := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (s : Tiling.Plane)) v.2 v'.2
    have hdiamW := translated_edge_endpoint_dist_le_diam_local
      (K := C.region) (t := (t : Tiling.Plane)) w.2 w'.2
    have hdiam : Metric.diam C.region.openCarrier < P.scale := by
      nlinarith [hScale, (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
    have hVctrl : dist (x₁ : Tiling.Plane) (x₂ : Tiling.Plane) < P.controlRadius :=
      lt_of_le_of_lt (by simpa [hx₁, hx₂] using hdiamV) (hdiam.trans P.scale_lt_controlRadius)
    have hWctrl : dist (x₃ : Tiling.Plane) (x₄ : Tiling.Plane) < P.controlRadius :=
      lt_of_le_of_lt (by simpa [hx₃, hx₄] using hdiamW) (hdiam.trans P.scale_lt_controlRadius)
    have hVimage := translated_edge_image_dist_lt_quarter_local
      P hScale phi hphi x₁ x₂ hx₁ hx₂
    have hWimage := translated_edge_image_dist_lt_quarter_local
      P hScale phi hphi x₃ x₄ hx₃ hx₄
    have hoverlap' :
        max (min (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
            (min (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re) <
          min (max (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
            (max (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re) := by
      simpa [Set.Ioo_inter_Ioo, Set.nonempty_Ioo] using hoverlap
    let r : ℝ :=
      (max (min (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
          (min (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re) +
        min (max (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
          (max (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re)) / 2
    have hrlo : max (min (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
          (min (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re) < r := by
      dsimp [r]; linarith
    have hrhi : r < min (max (V : Tiling.Plane).re (V' : Tiling.Plane).re + (Tphi s).re)
          (max (W : Tiling.Plane).re (W' : Tiling.Plane).re + (Tphi t).re) := by
      dsimp [r]; linarith
    let q : Tiling.Plane := (r : ℂ) + ((V : Tiling.Plane) + Tphi s).im * Complex.I
    have himV : ((V : Tiling.Plane) + Tphi s).im =
        ((V' : Tiling.Plane) + Tphi s).im := by simpa [Complex.add_im] using hVV.2.1
    have himW : ((W : Tiling.Plane) + Tphi t).im =
        ((W' : Tiling.Plane) + Tphi t).im := by simpa [Complex.add_im] using hWW.2.1
    have hqV : q ∈ segment ℝ ((V : Tiling.Plane) + Tphi s)
        ((V' : Tiling.Plane) + Tphi s) := by
      have hne : (V : Tiling.Plane) + Tphi s ≠ (V' : Tiling.Plane) + Tphi s := by
        intro h; apply hVV.1; exact add_right_cancel h
      apply (mem_segment_horizontal_local hne himV).mpr
      refine ⟨by simp [q], ?_⟩
      apply mem_uIcc_of_strict_bounds_local
      · simpa [q, Complex.add_re, ← min_add_add_right] using
          lt_of_le_of_lt (le_max_left _ _) hrlo
      · simpa [q, Complex.add_re, ← max_add_add_right] using
          lt_of_lt_of_le hrhi (min_le_left _ _)
    have hqW : q ∈ segment ℝ ((W : Tiling.Plane) + Tphi t)
        ((W' : Tiling.Plane) + Tphi t) := by
      have hne : (W : Tiling.Plane) + Tphi t ≠ (W' : Tiling.Plane) + Tphi t := by
        intro h; apply hWW.1; exact add_right_cancel h
      apply (mem_segment_horizontal_local hne himW).mpr
      refine ⟨by simp [q, hheight], ?_⟩
      apply mem_uIcc_of_strict_bounds_local
      · simpa [q, Complex.add_re, ← min_add_add_right] using
          lt_of_le_of_lt (le_max_right _ _) hrlo
      · simpa [q, Complex.add_re, ← max_add_add_right] using
          lt_of_lt_of_le hrhi (min_le_right _ _)
    have hVimage' : dist ((V : Tiling.Plane) + Tphi s)
        ((V' : Tiling.Plane) + Tphi s) < P.scale / 4 := by
      simpa [hA1, hA2] using hVimage
    have hWimage' : dist ((W : Tiling.Plane) + Tphi t)
        ((W' : Tiling.Plane) + Tphi t) < P.scale / 4 := by
      simpa [hA3, hA4] using hWimage
    have hcross := target_cross_source_control_local P phi hphi
      hA1 hA2 hA3 hA4 (p := q) hqV hqW hVimage' hWimage'
    have hsig12 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₂ x₁ x₂ x₁ (by simpa [dist_comm] using hVctrl)
        (by simpa [dist_comm] using hVctrl)).1.symm
    have hsig13 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₃ x₁ x₃ x₁ (by simpa [dist_comm] using hcross.1)
        (by simpa [dist_comm] using hcross.1)).1.symm
    have hsig14 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₁ x₄ x₁ (by simpa [dist_comm] using hcross.2.1)
        (by simpa [dist_comm] using hcross.2.1)).1.symm
    have hsig23 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₃ x₂ x₃ x₂ (by simpa [dist_comm] using hcross.2.2.1)
        (by simpa [dist_comm] using hcross.2.2.1)).1.symm
    have hsig24 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₂ x₄ x₂ (by simpa [dist_comm] using hcross.2.2.2)
        (by simpa [dist_comm] using hcross.2.2.2)).1.symm
    have hsig34 := (deformation_reflectsFiniteValues P phi hphi Axis.horizontal
      x₄ x₃ x₄ x₃ (by simpa [dist_comm] using hWctrl)
        (by simpa [dist_comm] using hWctrl)).1.symm
    have hheightSource : ((v : Tiling.Plane) + s).im =
        ((w : Tiling.Plane) + t).im := by
      have hz := (deformation_reflectsFiniteValues P phi hphi Axis.vertical
        x₁ x₃ x₁ x₃ (by simpa [hx₁, hx₃] using hcross.1)
          (by simpa [hx₁, hx₃] using hcross.1)).2.1.mp
        (by
          have : (mapTranslatedVertex phi x₁).im =
              (mapTranslatedVertex phi x₃).im := by
            simpa [hA1, hA3] using hheight
          simpa [Axis.coord] using sub_eq_zero.mpr this)
      have hz' : (x₁ : Tiling.Plane).im = (x₃ : Tiling.Plane).im := by
        simpa [Axis.coord] using sub_eq_zero.mp hz
      simpa [hx₁, hx₃] using hz'
    have hoverlapSource :
        (Set.Ioo (min (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re)
          (max (v : Tiling.Plane).re (v' : Tiling.Plane).re + (s : Tiling.Plane).re) ∩
        Set.Ioo (min (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re)
          (max (w : Tiling.Plane).re (w' : Tiling.Plane).re + (t : Tiling.Plane).re)).Nonempty := by
      have hInt := (intervalOverlap_transport_local
        (a := (x₁ : Tiling.Plane).re) (b := (x₂ : Tiling.Plane).re)
        (c := (x₃ : Tiling.Plane).re) (d := (x₄ : Tiling.Plane).re)
        (A := (mapTranslatedVertex phi x₁).re) (B := (mapTranslatedVertex phi x₂).re)
        (C' := (mapTranslatedVertex phi x₃).re) (D' := (mapTranslatedVertex phi x₄).re)
        (by simpa [Axis.coord] using hsig12)
        (by simpa [Axis.coord] using hsig13)
        (by simpa [Axis.coord] using hsig14)
        (by simpa [Axis.coord] using hsig23)
        (by simpa [Axis.coord] using hsig24)
        (by simpa [Axis.coord] using hsig34)).mpr
        (by simpa [hA1, hA2, hA3, hA4, Complex.add_re,
          ← min_add_add_right, ← max_add_add_right] using hoverlap)
      simpa [hx₁, hx₂, hx₃, hx₄, Complex.add_re,
        ← min_add_add_right, ← max_add_add_right] using hInt
    refine ⟨v, v', w, w', hvv, hww, hheightSource, hoverlapSource⟩





private structure TargetPlateContactPath
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Ptarget : Continuous.VerticalPlate D.deformedRegion
      (deformedCenterCarrier Tphi))
    (s t : ↥C.centres) where
  length : ℕ
  point : Fin (length + 1) → ↥C.centres
  point_zero : point 0 = s
  point_last : point (Fin.last length) = t
  point_mem : ∀ i, Tphi (point i) ∈ Ptarget.centres
  contact : ∀ i : Fin length,
    Continuous.HorizontalProperContact D.deformedRegion
      (Tphi (point i.castSucc)) (Tphi (point i.succ))

private noncomputable def centre_vertex
    {C : ApproximationContext} (s : ↥C.centres) : ↥C.translatedVertices :=
  ⟨s, ⟨0, C.zero_mem_vertices, s, s.2, zero_add (s : Tiling.Plane)⟩⟩

private theorem centre_vertex_map
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s : ↥C.centres) :
    mapTranslatedVertex phi (centre_vertex s) = Tphi s := by
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint (centre_vertex s) = C.centrePoint s.1 s.2 := by
    apply Subtype.ext
    rfl
  rw [hpoint, ← hTphi s]

private theorem horizontalProperContact_comm_local
    (K : Region) (s t : Tiling.Plane) :
    Continuous.HorizontalProperContact K s t ↔
      Continuous.HorizontalProperContact K t s := by
  constructor <;> rintro ⟨a, b, hab, him, hseg⟩
  · refine ⟨a, b, hab, him, ?_⟩
    simpa only [inter_comm, union_comm] using hseg
  · refine ⟨a, b, hab, him, ?_⟩
    simpa only [inter_comm, union_comm] using hseg

private theorem targetPlateContactPath_exists :
    ∀ {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Ptarget : Continuous.VerticalPlate D.deformedRegion
      (deformedCenterCarrier Tphi)) (s t : ↥C.centres),
    Tphi s ∈ Ptarget.centres → Tphi t ∈ Ptarget.centres →
      Nonempty (TargetPlateContactPath D Tphi Ptarget s t) := by
  intro C phi D Tphi Ptarget s t hs ht
  let E := deformedCenterEquivCarrier Tphi
  obtain ⟨qs, hqs, hqse⟩ := hs
  obtain ⟨qt, hqt, hqte⟩ := ht
  have hqs' : qs = E s := by
    apply Subtype.ext
    change (qs : Tiling.Plane) = Tphi s
    exact hqse
  have hqt' : qt = E t := by
    apply Subtype.ext
    change (qt : Tiling.Plane) = Tphi t
    exact hqte
  obtain ⟨w⟩ := Ptarget.reachable_of_mem_supp hqs hqt
  have hqs_component :
      (Continuous.verticalPlateGraph D.deformedRegion
        (deformedCenterCarrier Tphi)).connectedComponentMk qs =
        Ptarget := (SimpleGraph.ConnectedComponent.mem_supp_iff Ptarget qs).mp hqs
  let point : Fin (w.length + 1) → ↥C.centres :=
    fun i => E.symm (w.getVert i.1)
  have hpoint_zero : point 0 = s := by
    dsimp [point]
    rw [w.getVert_zero, hqs']
    exact E.symm_apply_apply s
  have hpoint_last : point (Fin.last w.length) = t := by
    dsimp [point]
    rw [w.getVert_length, hqt']
    exact E.symm_apply_apply t
  have hpoint_mem : ∀ i, Tphi (point i) ∈ Ptarget.centres := by
    intro i
    have hreach := (w.take i.1).reachable
    have hcomp := SimpleGraph.ConnectedComponent.sound hreach
    have hmem : w.getVert i.1 ∈ Ptarget.supp := by
      apply (SimpleGraph.ConnectedComponent.mem_supp_iff Ptarget _).mpr
      exact hcomp.symm.trans hqs_component
    refine ⟨w.getVert i.1, hmem, ?_⟩
    change (w.getVert i.1 : Tiling.Plane) = Tphi (E.symm (w.getVert i.1))
    have he := congrArg Subtype.val (E.apply_symm_apply (w.getVert i.1))
    change Tphi (E.symm (w.getVert i.1)) = (w.getVert i.1 : Tiling.Plane) at he
    exact he.symm
  have hcontact : ∀ i : Fin w.length,
      Continuous.HorizontalProperContact D.deformedRegion
        (Tphi (point i.castSucc)) (Tphi (point i.succ)) := by
    intro i
    have hmap (j : Fin (w.length + 1)) :
        Tphi (point j) = (w.getVert j.1 : Tiling.Plane) := by
      dsimp [point]
      have he := congrArg Subtype.val (E.apply_symm_apply (w.getVert j.1))
      change Tphi (E.symm (w.getVert j.1)) = (w.getVert j.1 : Tiling.Plane) at he
      exact he
    have hadj := w.adj_getVert_succ i.isLt
    have hadj' : (Continuous.verticalPlateGraph D.deformedRegion
        (deformedCenterCarrier Tphi)).Adj
        (w.getVert i.1) (w.getVert (i.1 + 1)) := hadj
    change (w.getVert i.1 ≠ w.getVert (i.1 + 1)) ∧
      (Continuous.HorizontalProperContact D.deformedRegion
          (w.getVert i.1 : Tiling.Plane) (w.getVert (i.1 + 1) : Tiling.Plane) ∨
        Continuous.HorizontalProperContact D.deformedRegion
          (w.getVert (i.1 + 1) : Tiling.Plane) (w.getVert i.1 : Tiling.Plane)) at hadj'
    rcases hadj' with ⟨_, hrel | hrel⟩
    · change Continuous.HorizontalProperContact D.deformedRegion
        (w.getVert i.1 : Tiling.Plane) (w.getVert (i.1 + 1) : Tiling.Plane) at hrel
      rw [hmap i.castSucc, hmap i.succ]
      exact hrel
    · change Continuous.HorizontalProperContact D.deformedRegion
        (w.getVert (i.1 + 1) : Tiling.Plane) (w.getVert i.1 : Tiling.Plane) at hrel
      rw [hmap i.castSucc, hmap i.succ]
      exact (horizontalProperContact_comm_local D.deformedRegion _ _).mp hrel
  exact ⟨⟨w.length, point, hpoint_zero, hpoint_last, hpoint_mem, hcontact⟩⟩

private theorem targetContactZero_reflectsSourceRealEquality :
    ∀ {C : ApproximationContext} (P : FLCControlPackage C)
    (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s t : ↥C.centres),
    Continuous.HorizontalProperContact D.deformedRegion (Tphi s) (Tphi t) →
    (Tphi s).re = (Tphi t).re →
      (s : Tiling.Plane).re = (t : Tiling.Plane).re := by
  intro C P hScale phi hphi D Tphi hTphi s t hcontact htarget
  have hsource_support : C.region.support = closure C.region.openCarrier := by
    change C.region.support = closure (interior C.region.support)
    exact C.region.isPolygonal.closure_interior.symm
  have hsource_diam_eq : Metric.diam C.region.support =
      Metric.diam C.region.openCarrier := by
    rw [hsource_support]
    exact Metric.diam_closure C.region.openCarrier
  have hsource_diam : Metric.diam C.region.support < P.scale := by
    rw [hsource_diam_eq]
    have hd : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
    nlinarith
  have htarget_diam_le := deformedRegion_diam_le_add_localError P hphi D hsource_diam
  have hlocal : P.localError < 1 := by
    rw [P.localError_eq]
    apply inv_lt_one_of_one_lt₀
    have hd : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
    nlinarith
  have htarget_diam : Metric.diam D.deformedRegion.support <
      2 * (Metric.diam C.region.openCarrier + 1) := by
    calc
      Metric.diam D.deformedRegion.support ≤
          Metric.diam C.region.support + P.localError := htarget_diam_le
      _ = Metric.diam C.region.openCarrier + P.localError := by rw [hsource_diam_eq]
      _ < Metric.diam C.region.openCarrier + 1 := by linarith
      _ < 2 * (Metric.diam C.region.openCarrier + 1) := by
        have hd : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
        nlinarith
  rcases hcontact with ⟨a, b, hab, him, hseg⟩
  let p : Tiling.Plane := midpoint ℝ a b
  have hpopen : p ∈ openSegment ℝ a b := by
    exact midpoint_mem_openSegment (𝕜 := ℝ) a b
  have hps := hseg hpopen
  have hzeroV : (0 : Tiling.Plane) ∈ D.deformedRegion.vertices := by
    rw [D.vertices_image]
    refine ⟨0, C.zero_mem_vertices, ?_⟩
    have hz := D.vertex_agreement 0 C.zero_mem_vertices
    have hr : (⟨((C.vertexPoint 0 C.zero_mem_vertices) : Tiling.Plane).re,
        C.vertex_re_mem 0 C.zero_mem_vertices⟩ : C.coordinateSpace) = 0 := by
      apply Subtype.ext
      change (0 : Tiling.Plane).re = 0
      rfl
    have hi : (⟨((C.vertexPoint 0 C.zero_mem_vertices) : Tiling.Plane).im,
        C.vertex_im_mem 0 C.zero_mem_vertices⟩ : C.coordinateSpace) = 0 := by
      apply Subtype.ext
      change (0 : Tiling.Plane).im = 0
      rfl
    have hm : mapPoint phi (C.vertexPoint 0 C.zero_mem_vertices) = 0 := by
      change (mapScalar phi (0 : C.coordinateSpace) : ℂ) +
        (mapScalar phi (0 : C.coordinateSpace) : ℂ) * Complex.I = 0
      simp [mapScalar]
    exact hz.trans hm
  have hzeroSupport : (0 : Tiling.Plane) ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion hzeroV)
  have hpsupport : p ∈ Tphi s +ᵥ D.deformedRegion.support := by
    have hcl := frontier_subset_closure hps.1.1
    rw [(D.deformedRegion.isPolygonal.vadd (Tphi s)).isClosed.closure_eq] at hcl
    exact hcl
  have htsupport : p ∈ Tphi t +ᵥ D.deformedRegion.support := by
    have hcl := frontier_subset_closure hps.1.2
    rw [(D.deformedRegion.isPolygonal.vadd (Tphi t)).isClosed.closure_eq] at hcl
    exact hcl
  have hsDist : dist (Tphi s) p ≤ Metric.diam D.deformedRegion.support := by
    rcases hpsupport with ⟨y, hy, hpy⟩
    change Tphi s +ᵥ y = p at hpy
    calc
      dist (Tphi s) p = dist (Tphi s) (Tphi s +ᵥ y) := by rw [hpy]
      _ = dist (Tphi s +ᵥ (0 : Tiling.Plane)) (Tphi s +ᵥ y) := by
        change dist (Tphi s) (Tphi s + y) = dist (Tphi s + 0) (Tphi s + y)
        simp only [add_zero]
      _ = dist 0 y := dist_vadd_cancel_left _ _ _
      _ ≤ Metric.diam D.deformedRegion.support :=
        Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded hzeroSupport hy
  have htDist : dist (Tphi t) p ≤ Metric.diam D.deformedRegion.support := by
    rcases htsupport with ⟨y, hy, hpy⟩
    change Tphi t +ᵥ y = p at hpy
    calc
      dist (Tphi t) p = dist (Tphi t) (Tphi t +ᵥ y) := by rw [hpy]
      _ = dist (Tphi t +ᵥ (0 : Tiling.Plane)) (Tphi t +ᵥ y) := by
        change dist (Tphi t) (Tphi t + y) = dist (Tphi t + 0) (Tphi t + y)
        simp only [add_zero]
      _ = dist 0 y := dist_vadd_cancel_left _ _ _
      _ ≤ Metric.diam D.deformedRegion.support :=
        Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded hzeroSupport hy
  have htarget_dist : dist (Tphi s) (Tphi t) < P.scale / 2 := by
    have htp' : dist p (Tphi t) ≤ Metric.diam D.deformedRegion.support := by
      simpa [dist_comm] using htDist
    calc
      dist (Tphi s) (Tphi t) ≤ dist (Tphi s) p + dist p (Tphi t) := by
        exact dist_triangle _ _ _
      _ ≤ 2 * Metric.diam D.deformedRegion.support := by
        linarith [hsDist, htp']
      _ < P.scale / 2 := by
        have hd : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
        nlinarith [htarget_diam]
  have hsource_dist : dist (centre_vertex s : Tiling.Plane)
      (centre_vertex t : Tiling.Plane) < P.scale := by
    have hcoarse := P.coarse_inverse phi hphi (centre_vertex s) (centre_vertex t)
      (by simpa [centre_vertex_map phi Tphi hTphi s,
        centre_vertex_map phi Tphi hTphi t] using htarget_dist)
    exact hcoarse
  let zs : C.coordinateSpace :=
    ⟨(s : Tiling.Plane).re, C.centre_re_mem s.1 s.2⟩
  let zt : C.coordinateSpace :=
    ⟨(t : Tiling.Plane).re, C.centre_re_mem t.1 t.2⟩
  let z : C.coordinateSpace := zs - zt
  have hzalpha : z ∈ P.scalarAlphabet := by
    change z ∈ (P.scalarAlphabet : Set C.coordinateSpace)
    rw [P.scalarAlphabet_exact]
    refine ⟨Axis.horizontal, centre_vertex s, centre_vertex t,
      lt_trans hsource_dist P.scale_lt_controlRadius, ?_⟩
    rfl
  have hmapzero : mapScalar phi z = 0 := by
    have hreal : mapScalar phi zs = mapScalar phi zt := by
      rw [hTphi s, hTphi t] at htarget
      simpa [zs, zt, mapPoint, mapScalar, ApproximationContext.centrePoint] using htarget
    have hlin : mapScalar phi z =
        mapScalar phi zs - mapScalar phi zt := by
      change ((phi z : ℚ) : ℝ) =
        ((phi zs : ℚ) : ℝ) - ((phi zt : ℚ) : ℝ)
      have hlinq : phi z = phi zs - phi zt := by
        exact map_sub phi zs zt
      exact_mod_cast hlinq
    rw [hlin, sub_eq_zero.mpr hreal]
  have hzcontrol : z ∈ P.scalarAlphabet ∪ P.edgeSumAlphabet :=
    Finset.mem_union_left _ hzalpha
  have hzreal := (P.scalar_zero_iff phi hphi z hzcontrol).mp hmapzero
  exact sub_eq_zero.mp hzreal

private theorem targetVerticalPlateCollinearity_reflects :
    ∀ {C : ApproximationContext} (P : FLCControlPackage C)
    (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (Ptarget : Continuous.VerticalPlate D.deformedRegion
      (deformedCenterCarrier Tphi)),
    Ptarget.centres = deformedCenterCarrierOn Tphi S →
      Continuous.IsVerticalColumn Ptarget →
      ∃ c : ℝ, ∀ t ∈ S, (t : Tiling.Plane).re = c := by
  intro C P hScale phi hphi D Tphi hTphi S Ptarget hcentres hColumn
  rw [Continuous.IsVerticalColumn] at hColumn
  obtain ⟨c, hc⟩ := hColumn
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    refine ⟨(s₀ : Tiling.Plane).re, ?_⟩
    intro t ht
    have hs₀mem : Tphi s₀ ∈ Ptarget.centres := by
      rw [hcentres, deformedCenterCarrierOn]
      exact ⟨s₀, hs₀, rfl⟩
    have htmem : Tphi t ∈ Ptarget.centres := by
      rw [hcentres, deformedCenterCarrierOn]
      exact ⟨t, ht, rfl⟩
    obtain ⟨path⟩ := targetPlateContactPath_exists D Tphi Ptarget s₀ t
      hs₀mem htmem
    have hpath : ∀ i : Fin (path.length + 1),
        (path.point i : Tiling.Plane).re = (s₀ : Tiling.Plane).re := by
      intro i
      induction i using Fin.induction with
      | zero =>
          exact congrArg (fun q : ↥C.centres => (q : Tiling.Plane).re)
            path.point_zero
      | succ i ih =>
          have hleft := hc (path.point_mem i.castSucc)
          have hright := hc (path.point_mem i.succ)
          have htarget :
              (Tphi (path.point i.castSucc)).re =
                (Tphi (path.point i.succ)).re := hleft.trans hright.symm
          have hsource := targetContactZero_reflectsSourceRealEquality
            P hScale phi hphi D Tphi hTphi
            (path.point i.castSucc) (path.point i.succ)
            (path.contact ⟨i.1, i.isLt⟩) htarget
          exact hsource.symm.trans ih
    simpa [path.point_last] using hpath (Fin.last path.length)
  · refine ⟨0, ?_⟩
    intro t ht
    exact (hS ⟨t, ht⟩).elim

private theorem verticalPlateColumnTransport :
    ∀ {C : ApproximationContext} (P : FLCControlPackage C)
    (_hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (Psource : Continuous.VerticalPlate C.region C.centres)
    (Ptarget : Continuous.VerticalPlate D.deformedRegion (deformedCenterCarrier Tphi)),
    Psource.centres = Set.image Subtype.val S →
    Ptarget.centres = deformedCenterCarrierOn Tphi S →
    (Continuous.IsVerticalColumn Psource ↔ Continuous.IsVerticalColumn Ptarget) := by
  intro C P hScale phi hphi D Tphi hTphi S Psource Ptarget hsource htarget
  constructor
  · intro hColumn
    have _hScale := hScale
    have _hphi := hphi
    rw [Continuous.IsVerticalColumn] at hColumn ⊢
    obtain ⟨x, hx⟩ := hColumn
    by_cases hS : S.Nonempty
    · obtain ⟨s₀, hs₀⟩ := hS
      refine ⟨(Tphi s₀).re, ?_⟩
      intro z hz
      rw [htarget] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      have hsSource : (s : Tiling.Plane) ∈ Psource.centres := by
        rw [hsource]
        exact ⟨s, hs, rfl⟩
      have hs₀Source : (s₀ : Tiling.Plane) ∈ Psource.centres := by
        rw [hsource]
        exact ⟨s₀, hs₀, rfl⟩
      have hre : (s : Tiling.Plane).re = (s₀ : Tiling.Plane).re :=
        (hx hsSource).trans (hx hs₀Source).symm
      change (Tphi s).re = (Tphi s₀).re
      rw [hTphi s, hTphi s₀]
      simp only [mapPoint, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
        add_zero, mapScalar]
      congr 2
      apply Subtype.ext
      exact hre
    · refine ⟨0, ?_⟩
      intro z hz
      rw [htarget, deformedCenterCarrierOn] at hz
      obtain ⟨s, hs, rfl⟩ := hz
      exact (hS ⟨s, hs⟩).elim
  · intro hColumn
    obtain ⟨c, hc⟩ := targetVerticalPlateCollinearity_reflects P hScale phi hphi D Tphi hTphi S
      Ptarget htarget hColumn
    rw [Continuous.IsVerticalColumn]
    refine ⟨c, ?_⟩
    rw [hsource]
    rintro z ⟨s, hs, rfl⟩
    exact hc s hs

end Tiling.AxisParallel.Approximation

namespace Tiling.AxisParallel.Approximation

set_option linter.unusedVariables false

open Function MeasureTheory Filter Set _root_.Topology
open scoped Pointwise _root_.Topology
open Tiling AxisParallel Approximation
open Tiling.AxisParallel.IntrinsicVertices

universe u

private def FullAxisSections (axis : Axis) (K : Region) (S : Set Tiling.Plane) : Prop :=
  ∀ c : ℝ,
    axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = Set.univ ∨
    axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = ∅

private def axisPoint (axis : Axis) (x c : ℝ) : Tiling.Plane :=
  match axis with
  | .horizontal => (x : ℂ) + (c : ℂ) * Complex.I
  | .vertical => (c : ℂ) + (x : ℂ) * Complex.I

private theorem axisPoint_coord (axis : Axis) (x c : ℝ) :
    axis.coord (axisPoint axis x c) = x := by
  cases axis <;> simp [axisPoint, Axis.coord]

private theorem axisPoint_transverseCoord (axis : Axis) (x c : ℝ) :
    axis.transverseCoord (axisPoint axis x c) = c := by
  cases axis <;> simp [axisPoint, Axis.transverseCoord]

private theorem axisPoint_eq (axis : Axis) (z : Tiling.Plane) (c : ℝ)
    (hc : axis.transverseCoord z = c) :
    axisPoint axis (axis.coord z) c = z := by
  cases axis
  · change z.im = c at hc
    change (z.re : ℂ) + (c : ℂ) * Complex.I = z
    apply Complex.ext
    · simp
    · simpa using hc.symm
  · change z.re = c at hc
    change (c : ℂ) + (z.im : ℂ) * Complex.I = z
    apply Complex.ext
    · simpa using hc.symm
    · simp

private theorem axisPoint_dist_sameCoord (axis : Axis) (x c d : ℝ) :
    dist (axisPoint axis x c) (axisPoint axis x d) = |c - d| := by
  cases axis
  · rw [Complex.dist_eq]
    norm_num [axisPoint, Complex.norm_def, Complex.normSq_apply]
    convert Real.sqrt_sq_eq_abs (c - d) using 1
    ring_nf
  · rw [Complex.dist_eq]
    norm_num [axisPoint, Complex.norm_def, Complex.normSq_apply]
    convert Real.sqrt_sq_eq_abs (c - d) using 1
    ring_nf

private theorem finiteLevel_isolated
    {L : Set ℝ} (hL : L.Finite) (c : ℝ) (hc : c ∈ L) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball c δ ⊆ (L \ {c})ᶜ := by
  have hclosed : IsClosed (L \ {c}) := hL.sdiff.isClosed
  have hmem : c ∈ (L \ {c})ᶜ := by simp [hc]
  exact Metric.mem_nhds_iff.mp (hclosed.isOpen_compl.mem_nhds hmem)

private theorem axis_transverse_le_dist (axis : Axis) (p q : Tiling.Plane) :
    |axis.transverseCoord p - axis.transverseCoord q| ≤ dist p q := by
  cases axis
  · simpa [Axis.transverseCoord, Complex.dist_eq] using
      Complex.abs_im_le_norm (p - q)
  · simpa [Axis.transverseCoord, Complex.dist_eq] using
      Complex.abs_re_le_norm (p - q)

private theorem axis_eq_of_coords (axis : Axis) {p q : Tiling.Plane}
    (hc : axis.coord p = axis.coord q)
    (ht : axis.transverseCoord p = axis.transverseCoord q) : p = q := by
  cases axis
  · apply Complex.ext <;> assumption
  · apply Complex.ext <;> assumption

private theorem interior_closedAxisBox_inter_iff
    {a b c d e f g h : ℝ} (_hab : a < b) (_hcd : c < d)
    (_hef : e < f) (_hgh : g < h) :
    (interior (closedAxisBox a b c d) ∩
      interior (closedAxisBox e f g h)).Nonempty ↔
      (max a e < min b f ∧ max c g < min d h) := by
  rw [show interior (closedAxisBox a b c d) =
      {z : Tiling.Plane | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d} by
    change interior (Icc a b ×ℂ Icc c d) = _
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
    ext z
    exact Complex.mem_reProdIm,
    show interior (closedAxisBox e f g h) =
      {z : Tiling.Plane | z.re ∈ Ioo e f ∧ z.im ∈ Ioo g h} by
    change interior (Icc e f ×ℂ Icc g h) = _
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
    ext z
    exact Complex.mem_reProdIm]
  constructor
  · rintro ⟨z, hz₁, hz₂⟩
    rcases hz₁ with ⟨⟨hza, hzb⟩, hzc, hzd⟩
    rcases hz₂ with ⟨⟨hze, hzf⟩, hzg, hzh⟩
    constructor
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hza, hze⟩).trans hzb,
        (max_lt_iff.mpr ⟨hza, hze⟩).trans hzf⟩
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hzc, hzg⟩).trans hzd,
        (max_lt_iff.mpr ⟨hzc, hzg⟩).trans hzh⟩
  · rintro ⟨hre, him⟩
    refine ⟨Complex.mk ((max a e + min b f) / 2)
      ((max c g + min d h) / 2), ?_, ?_⟩
    · change ((max a e + min b f) / 2 ∈ Ioo a b ∧
        (max c g + min d h) / 2 ∈ Ioo c d)
      have hlo : max a e < (max a e + min b f) / 2 := by linarith
      have hhi : (max a e + min b f) / 2 < min b f := by linarith
      have hlo' : max c g < (max c g + min d h) / 2 := by linarith
      have hhi' : (max c g + min d h) / 2 < min d h := by linarith
      exact ⟨⟨(le_max_left _ _).trans_lt hlo, hhi.trans_le (min_le_left _ _)⟩,
        ⟨(le_max_left _ _).trans_lt hlo', hhi'.trans_le (min_le_left _ _)⟩⟩
    · change ((max a e + min b f) / 2 ∈ Ioo e f ∧
        (max c g + min d h) / 2 ∈ Ioo g h)
      have hlo : max a e < (max a e + min b f) / 2 := by linarith
      have hhi : (max a e + min b f) / 2 < min b f := by linarith
      have hlo' : max c g < (max c g + min d h) / 2 := by linarith
      have hhi' : (max c g + min d h) / 2 < min d h := by linarith
      exact ⟨⟨(le_max_right _ _).trans_lt hlo, hhi.trans_le (min_le_right _ _)⟩,
        ⟨(le_max_right _ _).trans_lt hlo', hhi'.trans_le (min_le_right _ _)⟩⟩

private theorem coordinateBoxOverlap_transport
    (f g : ℝ ≃ₜ ℝ) (hf : StrictMono f) (hg : StrictMono g)
    {a b c d e f₀ g₀ h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f₀) (hgh : g₀ < h) :
    (interior (closedAxisBox a b c d) ∩
      interior (closedAxisBox e f₀ g₀ h)).Nonempty ↔
    (interior (closedAxisBox (f a) (f b) (g c) (g d)) ∩
      interior (closedAxisBox (f e) (f f₀) (g g₀) (g h))).Nonempty := by
  have hab' : f a < f b := hf hab
  have hcd' : g c < g d := hg hcd
  have hef' : f e < f f₀ := hf hef
  have hgh' : g g₀ < g h := hg hgh
  have hmaxf : max (f a) (f e) = f (max a e) := by
    rcases le_total a e with hae | hea
    · rw [max_eq_right (hf.monotone hae), max_eq_right hae]
    · rw [max_eq_left (hf.monotone hea), max_eq_left hea]
  have hminf : min (f b) (f f₀) = f (min b f₀) := by
    rcases le_total b f₀ with hbf | hfb
    · rw [min_eq_left (hf.monotone hbf), min_eq_left hbf]
    · rw [min_eq_right (hf.monotone hfb), min_eq_right hfb]
  have hmaxg : max (g c) (g g₀) = g (max c g₀) := by
    rcases le_total c g₀ with hcg | hgc
    · rw [max_eq_right (hg.monotone hcg), max_eq_right hcg]
    · rw [max_eq_left (hg.monotone hgc), max_eq_left hgc]
  have hming : min (g d) (g h) = g (min d h) := by
    rcases le_total d h with hdh | hhd
    · rw [min_eq_left (hg.monotone hdh), min_eq_left hdh]
    · rw [min_eq_right (hg.monotone hhd), min_eq_right hhd]
  rw [interior_closedAxisBox_inter_iff hab hcd hef hgh,
    interior_closedAxisBox_inter_iff hab' hcd' hef' hgh']
  constructor
  · rintro ⟨hre, him⟩
    constructor
    · rw [hmaxf, hminf]
      exact hf hre
    · rw [hmaxg, hming]
      exact hg him
  · rintro ⟨hre, him⟩
    constructor
    · rw [hmaxf, hminf] at hre
      exact hf.lt_iff_lt.mp hre
    · rw [hmaxg, hming] at him
      exact hg.lt_iff_lt.mp him

private theorem regularize_finite_transverse
    (axis : Axis) (D : Set Tiling.Plane)
    (hopen : IsOpen D) (hreg : interior (closure D) = D)
    (L : Set ℝ) (hL : L.Finite)
    (hgeneric : ∀ c, c ∉ L →
      axis.coord '' (D ∩ {z | axis.transverseCoord z = c}) = Set.univ ∨
      axis.coord '' (D ∩ {z | axis.transverseCoord z = c}) = ∅) :
    (∀ c, axis.coord '' (D ∩ {z | axis.transverseCoord z = c}) = Set.univ ∨
      axis.coord '' (D ∩ {z | axis.transverseCoord z = c}) = ∅) := by
  intro c
  by_cases hcL : c ∉ L
  · exact hgeneric c hcL
  · by_cases hempty :
      axis.coord '' (D ∩ {z | axis.transverseCoord z = c}) = ∅
    · exact Or.inr hempty
    · left
      obtain ⟨x, hx⟩ :
          (axis.coord '' (D ∩ {z | axis.transverseCoord z = c})).Nonempty :=
        Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨z, hz, hzx⟩ := hx
      have hzD : z ∈ D := hz.1
      have hzc : axis.transverseCoord z = c := hz.2
      obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hopen z hzD
      have hcL' : c ∈ L := not_not.mp hcL
      obtain ⟨δ, hδ, hδavoid⟩ := finiteLevel_isolated hL c hcL'
      let η : ℝ := min (r₀ / 2) (δ / 2)
      have hη : 0 < η := lt_min (by linarith) (by linarith)
      have hfull_near : ∀ r : ℝ, |r - c| < η → r ≠ c →
          axis.coord '' (D ∩ {z | axis.transverseCoord z = r}) = Set.univ := by
        intro r hrc hrcne
        have hrL : r ∉ L := by
          intro hr
          have hrball : r ∈ Metric.ball c δ := by
            rw [Metric.mem_ball, Real.dist_eq]
            exact hrc.trans (lt_of_le_of_lt (min_le_right _ _) (by linarith))
          apply hδavoid hrball
          exact ⟨hr, by simp [hrcne]⟩
        have hrD : axisPoint axis (axis.coord z) r ∈ D := by
          apply hball
          have hzpoint : axisPoint axis (axis.coord z) c = z :=
            axisPoint_eq axis z c hzc
          calc
            dist (axisPoint axis (axis.coord z) r) z =
                dist (axisPoint axis (axis.coord z) r)
                  (axisPoint axis (axis.coord z) c) := by rw [hzpoint]
            _ = |r - c| := axisPoint_dist_sameCoord axis _ _ _
            _ < r₀ := hrc.trans (lt_of_le_of_lt (min_le_left _ _) (by linarith))
        have himage : (axis.coord '' (D ∩
            {z | axis.transverseCoord z = r})).Nonempty := by
          refine ⟨axis.coord z, ?_⟩
          refine ⟨axisPoint axis (axis.coord z) r, ⟨hrD,
            axisPoint_transverseCoord axis (axis.coord z) r⟩,
            axisPoint_coord axis (axis.coord z) r⟩
        rcases hgeneric r hrL with hfull | hempty
        · exact hfull
        · exact False.elim (Set.not_nonempty_empty (hempty ▸ himage))
      ext y
      constructor
      · intro _
        trivial
      · intro _
        let w := axisPoint axis y c
        have hwD : w ∈ D := by
          have hwinterior : w ∈ interior (closure D) := by
            apply mem_interior_iff_mem_nhds.mpr
            have hballnh : Metric.ball w (η / 4) ∈ 𝓝 w :=
              Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
            apply Filter.mem_of_superset hballnh
            intro q hq
            rw [Metric.mem_closure_iff]
            intro ε hε
            by_cases hqc : axis.transverseCoord q = c
            · have hρ : 0 < min (η / 2) (ε / 2) :=
                lt_min (by linarith) (by linarith)
              let r := c + min (η / 2) (ε / 2)
              have hrc : |r - c| < η := by
                dsimp [r]
                rw [abs_of_pos (by linarith [hρ])]
                have hmin := min_le_left (η / 2) (ε / 2)
                linarith
              have hrcne : r ≠ c := by dsimp [r]; linarith
              have hmem : axis.coord q ∈ axis.coord ''
                  (D ∩ {z | axis.transverseCoord z = r}) := by
                rw [hfull_near r hrc hrcne]
                exact Set.mem_univ _
              obtain ⟨p, hp, hpcoord⟩ := hmem
              have hptrans : axis.transverseCoord p = r := hp.2
              have hpeq : p = axisPoint axis (axis.coord q) r := by
                calc
                  p = axisPoint axis (axis.coord p) r :=
                    (axisPoint_eq axis p r hptrans).symm
                  _ = axisPoint axis (axis.coord q) r := by rw [hpcoord]
              refine ⟨p, hp.1, ?_⟩
              calc
                dist q p = dist (axisPoint axis (axis.coord q) c)
                    (axisPoint axis (axis.coord q) r) := by
                  rw [axisPoint_eq axis q c hqc, hpeq]
                _ = |c - r| := axisPoint_dist_sameCoord axis _ _ _
                _ < ε := by
                  dsimp [r]
                  rw [abs_of_nonpos (by linarith [hρ])]
                  linarith [min_le_right (η / 2) (ε / 2)]
            · have hqclose : |axis.transverseCoord q - c| < η := by
                have hcoordle := axis_transverse_le_dist axis q w
                have hwtrans : axis.transverseCoord w = c :=
                  axisPoint_transverseCoord axis _ _
                rw [hwtrans] at hcoordle
                exact lt_of_le_of_lt hcoordle (lt_of_lt_of_le
                  (by simpa [Metric.mem_ball] using hq) (by linarith))
              have hmem : axis.coord q ∈ axis.coord ''
                  (D ∩ {z | axis.transverseCoord z =
                    axis.transverseCoord q}) := by
                rw [hfull_near (axis.transverseCoord q) hqclose hqc]
                exact Set.mem_univ _
              obtain ⟨p, hp, hpcoord⟩ := hmem
              have hptrans := hp.2
              have hpeq : p = q := axis_eq_of_coords axis hpcoord
                (hptrans)
              have hqD : q ∈ D := hpeq ▸ hp.1
              exact ⟨q, hqD, dist_self q |>.trans_lt hε⟩
          simpa [hreg] using hwinterior
        change y ∈ axis.coord ''
          (D ∩ {z | axis.transverseCoord z = c})
        exact ⟨w, ⟨hwD, axisPoint_transverseCoord axis y c⟩,
          axisPoint_coord axis y c⟩

private theorem genericFibres_regularizeGrid :
  ∀ (axis : Axis) (K : Region) (S : Set Tiling.Plane) (c₀ : ℝ),
    (∀ t ∈ S, axis.transverseCoord t = c₀) →
    (∀ c, c ∉ c₀ +ᵥ (axis.transverseCoord '' K.vertices) →
      axis.coord '' (regularSupport K S ∩ {z | axis.transverseCoord z = c}) = Set.univ ∨
      axis.coord '' (regularSupport K S ∩ {z | axis.transverseCoord z = c}) = ∅) →
    FullAxisSections axis K S := by
  intro axis K S c₀ _hcol hgeneric
  let L : Set ℝ := c₀ +ᵥ (axis.transverseCoord '' K.vertices)
  have hL : L.Finite := by
    dsimp [L]
    rw [K.vertices_eq_vertexSet]
    simpa only [Set.singleton_vadd] using
      (Set.finite_singleton c₀).vadd
        (K.isPolygonal.vertexSet_finite.image axis.transverseCoord)
  have hgeneric' : ∀ c, c ∉ L →
      axis.coord '' (regularSupport K S ∩
        {z | axis.transverseCoord z = c}) = Set.univ ∨
      axis.coord '' (regularSupport K S ∩
        {z | axis.transverseCoord z = c}) = ∅ := by
    intro c hc
    exact hgeneric c (by simpa [L] using hc)
  exact regularize_finite_transverse axis (regularSupport K S)
    (regularSupport_isRegularOpen K S).1
    (regularSupport_isRegularOpen K S).2 L hL hgeneric'

private structure LabelledFibreChain (axis : Axis) (K : Region)
    (S : Set Tiling.Plane) (c : ℝ) where
  endpoint : ℤ → ℝ
  owner : ℤ → Tiling.Plane
  owner_mem : ∀ j, owner j ∈ S
  strictMono : StrictMono endpoint
  tendsto_atTop : Filter.Tendsto endpoint Filter.atTop Filter.atTop
  tendsto_atBot : Filter.Tendsto endpoint Filter.atBot Filter.atBot
  gap_in_tile : ∀ j,
    {z : Tiling.Plane | axis.transverseCoord z = c ∧
      axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
      owner j +ᵥ K.openCarrier
  fibre_eq : axis.coord '' (regularSupport K S ∩
    {z | axis.transverseCoord z = c}) = Set.univ

private def IsTransverseGridCell (levels J : Set ℝ) : Prop :=
  IsOpen J ∧ IsPreconnected J ∧ J.Nonempty ∧ Disjoint J levels ∧
    ∀ U : Set ℝ, IsOpen U → IsPreconnected U → U.Nonempty →
      Disjoint U levels → J ⊆ U → U ⊆ J

private def mappedTransverseVertexLevels {C : ApproximationContext.{u}}
    (axis : Axis) (phi : C.coordinateSpace →ₗ[ℚ] ℚ) : Set ℝ :=
  axis.transverseCoord ''
    (mapPoint phi '' Set.range (fun v : ↥C.region.vertices => C.vertexPoint v.1 v.2))

private structure TransverseGridCellTransportData
    (C : ApproximationContext.{u}) (axis : Axis)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (S : Set ↥C.centres) where
  sourceCentreCoordinate : ℝ
  targetCentreCoordinate : ℝ
  source_collinear : ∀ t ∈ S,
    axis.transverseCoord (t : Tiling.Plane) = sourceCentreCoordinate
  target_collinear : ∀ t ∈ S,
    axis.transverseCoord (Tphi t) = targetCentreCoordinate
  sourceLevels : Set ℝ
  targetLevels : Set ℝ
  sourceLevels_eq : sourceLevels = sourceCentreCoordinate +ᵥ
    (axis.transverseCoord '' C.region.vertices)
  targetLevels_eq : targetLevels = targetCentreCoordinate +ᵥ
    mappedTransverseVertexLevels axis phi
  sourceLevels_finite : sourceLevels.Finite
  targetLevels_finite : targetLevels.Finite
  levelEquiv : ↥sourceLevels ≃ ↥targetLevels
  levelEquiv_vertex : ∀ (x : ↥sourceLevels) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices),
    x.1 = sourceCentreCoordinate + axis.transverseCoord v →
    (levelEquiv x).1 = targetCentreCoordinate +
      axis.transverseCoord (mapPoint phi (C.vertexPoint v hv))
  sourceCells : Set (Set ℝ)
  targetCells : Set (Set ℝ)
  sourceCells_eq : sourceCells = {J | IsTransverseGridCell sourceLevels J}
  targetCells_eq : targetCells = {J | IsTransverseGridCell targetLevels J}
  sourceCells_finite : sourceCells.Finite
  targetCells_finite : targetCells.Finite
  transverseHomeomorph : ℝ ≃ₜ ℝ
  transverseHomeomorph_strictMono : StrictMono transverseHomeomorph
  transverseHomeomorph_vertex : ∀ (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices),
    transverseHomeomorph
        (sourceCentreCoordinate + axis.transverseCoord v) =
      targetCentreCoordinate +
        axis.transverseCoord (mapPoint phi (C.vertexPoint v hv))
  cellEquiv : ↥sourceCells ≃ ↥targetCells
  cell_image : ∀ A : ↥sourceCells,
    (cellEquiv A).1 = transverseHomeomorph '' A.1
  order_preserving : ∀ A B : ↥sourceCells, A ≠ B → ∀ a ∈ A.1, ∀ b ∈ B.1,
    a < b → ∀ a' ∈ (cellEquiv A).1, ∀ b' ∈ (cellEquiv B).1, a' < b'
  occupied_iff : ∀ A : ↥sourceCells,
    (∀ c ∈ A.1, axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c}) = Set.univ) ↔
    ∀ c ∈ (cellEquiv A).1, axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩ {z | axis.transverseCoord z = c}) = Set.univ
  empty_iff : ∀ A : ↥sourceCells,
    (∀ c ∈ A.1, axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c}) = ∅) ↔
    ∀ c ∈ (cellEquiv A).1, axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩ {z | axis.transverseCoord z = c}) = ∅

private theorem gridCell_eq_connectedComponentIn
    {L J : Set ℝ} (hL : L.Finite) (hJ : IsTransverseGridCell L J) :
    J = connectedComponentIn Lᶜ (Classical.choose hJ.2.2.1) := by
  classical
  let x : ℝ := Classical.choose hJ.2.2.1
  have hxJ : x ∈ J := Classical.choose_spec hJ.2.2.1
  have hJL : J ⊆ Lᶜ := by
    intro y hyJ hyL
    exact Set.disjoint_left.1 hJ.2.2.2.1 hyJ hyL
  apply Set.Subset.antisymm
  · exact hJ.2.1.subset_connectedComponentIn hxJ hJL
  · apply hJ.2.2.2.2 (connectedComponentIn Lᶜ x)
    · exact hL.isClosed.isOpen_compl.connectedComponentIn
    · exact isPreconnected_connectedComponentIn
    · exact ⟨x, mem_connectedComponentIn (hJL hxJ)⟩
    · exact Set.disjoint_left.2 fun y hy hyl =>
        (connectedComponentIn_subset Lᶜ x hy) hyl
    · exact hJ.2.1.subset_connectedComponentIn hxJ hJL

private theorem gridCells_finite {L : Set ℝ} (hL : L.Finite) :
    {J : Set ℝ | IsTransverseGridCell L J}.Finite := by
  classical
  let Cells := {J : Set ℝ // IsTransverseGridCell L J}
  let point : Cells → ℝ := fun A => Classical.choose A.2.2.2.1
  let signature : Cells → Set ↥L := fun A =>
    {l | (l : ℝ) < point A}
  have hpoint_mem (A : Cells) : point A ∈ (A : Set ℝ) :=
    Classical.choose_spec A.2.2.2.1
  have hpoint_off (A : Cells) : point A ∉ L := by
    intro hp
    exact Set.disjoint_left.1 A.2.2.2.2.1 (hpoint_mem A) hp
  have hreach (A B : Cells) (hsig : signature A = signature B)
      (hle : point A ≤ point B) :
      point B ∈ connectedComponentIn Lᶜ (point A) := by
    have hI : Icc (point A) (point B) ⊆ Lᶜ := by
      intro z hz hzL
      by_cases hzB : z = point B
      · exact hpoint_off B (hzB ▸ hzL)
      · have hzlt : z < point B := lt_of_le_of_ne hz.2 hzB
        have hzsigB : (⟨z, hzL⟩ : ↥L) ∈ signature B := hzlt
        have hzsigA : (⟨z, hzL⟩ : ↥L) ∈ signature A := by
          rw [hsig]
          exact hzsigB
        exact (not_lt_of_ge hz.1) hzsigA
    exact (isPreconnected_Icc.subset_connectedComponentIn
      (left_mem_Icc.mpr hle) hI) (right_mem_Icc.mpr hle)
  have hsignature : Function.Injective signature := by
    intro A B hsig
    apply Subtype.ext
    have hA := gridCell_eq_connectedComponentIn hL A.2
    have hB := gridCell_eq_connectedComponentIn hL B.2
    rcases le_total (point A) (point B) with hle | hle
    · have hm := hreach A B hsig hle
      rw [hA, hB, connectedComponentIn_eq hm]
    · have hm := hreach B A hsig.symm hle
      rw [hA, hB, connectedComponentIn_eq hm]
  let _ : Fintype ↥L := hL.fintype
  have hfinite : Finite Cells := Finite.of_injective signature hsignature
  exact Set.finite_coe_iff.mp hfinite

private theorem gridCell_image_iff
    (H : ℝ ≃ₜ ℝ) {L M J : Set ℝ} (hLM : H '' L = M) :
    IsTransverseGridCell L J ↔ IsTransverseGridCell M (H '' J) := by
  have hforward : ∀ (G : ℝ ≃ₜ ℝ) (A B Q : Set ℝ),
      G '' A = B → IsTransverseGridCell A Q →
        IsTransverseGridCell B (G '' Q) := by
    intro G A B Q hAB hQ
    refine ⟨G.isOpenMap _ hQ.1,
      hQ.2.1.image G G.continuous.continuousOn,
      hQ.2.2.1.image G, ?_, ?_⟩
    · rw [← hAB]
      exact Set.disjoint_image_of_injective G.injective hQ.2.2.2.1
    · intro U hUopen hUpre hUne hUdis hsub
      let V : Set ℝ := G.symm '' U
      have hVopen : IsOpen V := G.symm.isOpenMap U hUopen
      have hVpre : IsPreconnected V :=
        hUpre.image G.symm G.symm.continuous.continuousOn
      have hVne : V.Nonempty := hUne.image G.symm
      have hVL : Disjoint V A := by
        have himg : Disjoint (G.symm '' U) (G.symm '' B) :=
          Set.disjoint_image_of_injective G.symm.injective hUdis
        rw [← hAB] at himg
        have hcancel : G.symm '' (G '' A) = A := by
          ext x
          constructor
          · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
            rw [← hy]
            simpa using hz
          · intro hx
            exact ⟨G x, ⟨x, hx, rfl⟩, G.symm_apply_apply x⟩
        rw [hcancel] at himg
        exact himg
      have hQV : Q ⊆ V := by
        intro x hx
        exact ⟨G x, hsub ⟨x, hx, rfl⟩, G.symm_apply_apply x⟩
      have hVQ := hQ.2.2.2.2 V hVopen hVpre hVne hVL hQV
      intro y hy
      refine ⟨G.symm y, hVQ ?_, G.apply_symm_apply y⟩
      exact ⟨y, hy, rfl⟩
  constructor
  · exact hforward H L M J hLM
  · intro hHJ
    have hback := hforward H.symm M L (H '' J) (by
      rw [← hLM]
      exact H.symm_image_image L) hHJ
    have hcancel : H.symm '' (H '' J) = J := by
      ext x
      constructor
      · rintro ⟨y, ⟨z, hz, rfl⟩, hy⟩
        rw [← hy]
        simpa using hz
      · intro hx
        exact ⟨H x, ⟨x, hx, rfl⟩, H.symm_apply_apply x⟩
    rw [hcancel] at hback
    exact hback

private theorem distinct_gridCells_disjoint
    {L A B : Set ℝ} (hL : L.Finite)
    (hA : IsTransverseGridCell L A) (hB : IsTransverseGridCell L B)
    (hne : A ≠ B) : Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hxA hxB
  apply hne
  have hAc := gridCell_eq_connectedComponentIn hL hA
  have hBc := gridCell_eq_connectedComponentIn hL hB
  rw [hAc] at hxA ⊢
  rw [hBc] at hxB ⊢
  exact (connectedComponentIn_eq hxA).trans (connectedComponentIn_eq hxB).symm

private theorem distinct_gridCells_order
    {L A B : Set ℝ} (hL : L.Finite)
    (hA : IsTransverseGridCell L A) (hB : IsTransverseGridCell L B)
    (hne : A ≠ B) {a b : ℝ} (ha : a ∈ A) (hb : b ∈ B) (hab : a < b) :
    ∀ a' ∈ A, ∀ b' ∈ B, a' < b' := by
  have hdis := distinct_gridCells_disjoint hL hA hB hne
  intro a' ha' b' hb'
  by_contra hnlt
  have hle : b' ≤ a' := le_of_not_gt hnlt
  by_cases hba : b' ≤ a
  · have haB : a ∈ B := hB.2.1.ordConnected.out hb' hb ⟨hba, hab.le⟩
    exact Set.disjoint_left.1 hdis ha haB
  · have hab' : a ≤ b' := le_of_not_ge hba
    have hbA : b' ∈ A := hA.2.1.ordConnected.out ha ha' ⟨hab', hle⟩
    exact Set.disjoint_left.1 hdis hbA hb'

private noncomputable def gridCellEquiv (H : ℝ ≃ₜ ℝ) {L M : Set ℝ}
    (hLM : H '' L = M) :
    ↥{J : Set ℝ | IsTransverseGridCell L J} ≃
      ↥{J : Set ℝ | IsTransverseGridCell M J} where
  toFun A := ⟨H '' A.1, (gridCell_image_iff H hLM).mp A.2⟩
  invFun B := ⟨H.symm '' B.1, by
    have hML : H.symm '' M = L := by
      rw [← hLM]
      exact H.symm_image_image L
    exact (gridCell_image_iff H.symm hML).mp B.2⟩
  left_inv A := by
    apply Subtype.ext
    exact H.symm_image_image A.1
  right_inv B := by
    apply Subtype.ext
    exact H.image_symm_image B.1

private theorem gridCellEquiv_image (H : ℝ ≃ₜ ℝ) {L M : Set ℝ}
    (hLM : H '' L = M) (A : ↥{J : Set ℝ | IsTransverseGridCell L J}) :
    (gridCellEquiv H hLM A).1 = H '' A.1 := rfl

private def transverseTransportHomeomorph {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (axis : Axis)
    (D : CoordinateDeformation C phi) (c₀ c₁ : ℝ) : ℝ ≃ₜ ℝ :=
  match axis with
  | .horizontal =>
      (Homeomorph.addRight (-c₀)).trans
        (D.secondHomeomorph.trans (Homeomorph.addLeft c₁))
  | .vertical =>
      (Homeomorph.addRight (-c₀)).trans
        (D.firstHomeomorph.trans (Homeomorph.addLeft c₁))

private theorem transverseTransportHomeomorph_apply {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (axis : Axis)
    (D : CoordinateDeformation C phi) (c₀ c₁ x : ℝ) :
    transverseTransportHomeomorph axis D c₀ c₁ x =
      c₁ + match axis with
        | .horizontal => D.secondHomeomorph (x - c₀)
        | .vertical => D.firstHomeomorph (x - c₀) := by
  cases axis <;> simp [transverseTransportHomeomorph, sub_eq_add_neg]

private theorem planarHomeomorph_re {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C phi)
    (z : Tiling.Plane) :
    (D.planarHomeomorph z).re = D.firstHomeomorph z.re := by
  simp [D.planarHomeomorph_apply]

private theorem planarHomeomorph_im {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C phi)
    (z : Tiling.Plane) :
    (D.planarHomeomorph z).im = D.secondHomeomorph z.im := by
  simp [D.planarHomeomorph_apply]

private theorem transverseTransportHomeomorph_strictMono {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (axis : Axis)
    (D : CoordinateDeformation C phi) (c₀ c₁ : ℝ) :
    StrictMono (transverseTransportHomeomorph axis D c₀ c₁) := by
  cases axis with
  | horizontal =>
      intro x y hxy
      rw [transverseTransportHomeomorph_apply,
        transverseTransportHomeomorph_apply]
      simpa [add_comm] using add_lt_add_left
        (D.secondHomeomorph_strictMono (sub_lt_sub_right hxy c₀)) c₁
  | vertical =>
      intro x y hxy
      rw [transverseTransportHomeomorph_apply,
        transverseTransportHomeomorph_apply]
      simpa [add_comm] using add_lt_add_left
        (D.firstHomeomorph_strictMono (sub_lt_sub_right hxy c₀)) c₁

private theorem transverseTransportHomeomorph_vertex
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (axis : Axis) (c₀ c₁ : ℝ)
    (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
    transverseTransportHomeomorph axis D c₀ c₁
        (c₀ + axis.transverseCoord v) =
      c₁ + axis.transverseCoord (mapPoint phi (C.vertexPoint v hv)) := by
  rw [transverseTransportHomeomorph_apply]
  have hvmap := D.vertex_agreement v hv
  cases axis with
  | horizontal =>
      simpa [Axis.transverseCoord, D.planarHomeomorph_apply] using
        congrArg Complex.im hvmap
  | vertical =>
      simpa [Axis.transverseCoord, D.planarHomeomorph_apply] using
        congrArg Complex.re hvmap

private theorem transverseTransport_levels
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (axis : Axis) (c₀ c₁ : ℝ) :
    transverseTransportHomeomorph axis D c₀ c₁ ''
        (c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)) =
      c₁ +ᵥ mappedTransverseVertexLevels axis phi := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx ⊢
    obtain ⟨v, hv, hvx⟩ := hx
    rw [mappedTransverseVertexLevels]
    refine ⟨mapPoint phi (C.vertexPoint v hv), ?_, ?_⟩
    · exact ⟨C.vertexPoint v hv, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
    · have hxeq : x = c₀ + axis.transverseCoord v := by
        change axis.transverseCoord v = -c₀ + x at hvx
        linarith
      rw [hxeq, transverseTransportHomeomorph_vertex phi D axis c₀ c₁ v hv]
      simp [vadd_eq_add]
  · intro hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨w, hw, hwz⟩ := hz
    obtain ⟨v, rfl⟩ := hw
    subst z
    let x := c₀ + axis.transverseCoord v.1
    refine ⟨x, ?_, ?_⟩
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      refine ⟨v.1, v.2, ?_⟩
      dsimp [x]
      ring
    · dsimp [x]
      rw [transverseTransportHomeomorph_vertex phi D axis c₀ c₁ v.1 v.2]
      rw [hzy]
      change c₁ + (-c₁ + y) = y
      ring

private theorem deformed_transverse_vertices_eq_mapped
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (axis : Axis) :
    axis.transverseCoord '' D.deformedRegion.vertices =
      mappedTransverseVertexLevels axis phi := by
  rw [mappedTransverseVertexLevels, D.vertices_image]
  ext x
  constructor
  · rintro ⟨z, ⟨v, hv, rfl⟩, rfl⟩
    rw [D.vertex_agreement v hv]
    exact ⟨mapPoint phi (C.vertexPoint v hv),
      ⟨C.vertexPoint v hv, ⟨⟨v, hv⟩, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨p, ⟨v, rfl⟩, rfl⟩, rfl⟩
    refine ⟨D.planarHomeomorph v.1, ⟨v.1, v.2, rfl⟩, ?_⟩
    rw [D.vertex_agreement v.1 v.2]

private theorem translatedTile_image
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (s : ↥C.centres) :
    (fun z : Tiling.Plane => Tphi s + D.planarHomeomorph
        (z - (s : Tiling.Plane))) ''
        ((s : Tiling.Plane) +ᵥ C.region.openCarrier) =
      Tphi s +ᵥ D.deformedRegion.openCarrier := by
  rw [show ((s : Tiling.Plane) +ᵥ C.region.openCarrier) =
      (fun z : Tiling.Plane => (s : Tiling.Plane) + z) '' C.region.openCarrier by
    rw [← Set.image_vadd]
    rfl]
  rw [Set.image_image]
  rw [show (fun z : Tiling.Plane =>
      Tphi s + D.planarHomeomorph
        ((s : Tiling.Plane) + z - (s : Tiling.Plane))) =
      (fun z : Tiling.Plane => Tphi s + D.planarHomeomorph z) by
    funext z
    rw [add_sub_cancel_left]]
  rw [D.deformedRegion_openCarrier]
  rw [← Set.image_vadd]
  rw [Set.image_image]
  rfl

private theorem mappedTranslatedVertex_coord_lt_iff
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (a b : ↥C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < P.controlRadius) :
    Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) < 0 ↔
      Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) < 0 := by
  have hs := (deformation_reflectsFiniteValues P phi hphi axis a b a b hab hab).1
  constructor
  · intro hm
    by_contra hn
    have hz : Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) ≠ 0 := by
      intro hz
      have : Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 :=
        (deformation_reflectsFiniteValues P phi hphi axis a b a b hab hab).2.1.mpr hz
      linarith
    have hpos : 0 < Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
    have hsign : Real.sign
        (Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane))) = 1 :=
      Real.sign_of_pos hpos
    rw [hsign] at hs
    have : Real.sign
        (Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b)) = -1 :=
      Real.sign_of_neg hm
    linarith
  · intro hsour
    have hsign : Real.sign
        (Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane))) = -1 :=
      Real.sign_of_neg hsour
    rw [← hs] at hsign
    by_contra hn
    have hz : Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) ≠ 0 := by
      intro hz
      rw [Real.sign_eq_zero_iff.mpr hz] at hsign
      norm_num at hsign
    have hpos : 0 < Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) :=
      lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
    linarith [Real.sign_of_pos hpos]

private theorem volume_re_eq_zero (a : ℝ) :
    volume {z : Tiling.Plane | z.re = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.re = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_re continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : (z + (ε / 2 : ℝ)) ∈ H := interior_subset hw
    have hzH : z.re = a := hzmem
    have hwH : (z + (ε / 2 : ℝ)).re = a := hwmem
    simp only [Complex.add_re, Complex.ofReal_re] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.reLm.isLinear a).addHaar_frontier volume

private theorem volume_im_eq_zero (a : ℝ) :
    volume {z : Tiling.Plane | z.im = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.im = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_im continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) * Complex.I ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : z + (ε / 2 : ℝ) * Complex.I ∈ H := interior_subset hw
    have hzH : z.im = a := hzmem
    have hwH : (z + (ε / 2 : ℝ) * Complex.I).im = a := hwmem
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.imLm.isLinear a).addHaar_frontier volume

private theorem exists_offFiniteCoordinateGrid_mem_open (V : Finset Tiling.Plane)
    {U : Set Tiling.Plane} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, ∀ v ∈ V, z.re ≠ v.re ∧ z.im ≠ v.im := by
  classical
  let bad : Set Tiling.Plane := ⋃ v : ↥V,
    ({z : Tiling.Plane | z.re = v.1.re} ∪ {z : Tiling.Plane | z.im = v.1.im})
  have hbadzero : volume bad = 0 := by
    dsimp only [bad]
    apply measure_iUnion_null
    intro v
    exact measure_union_null (volume_re_eq_zero v.1.re) (volume_im_eq_zero v.1.im)
  by_contra hn
  push Not at hn
  have hsub : U ⊆ bad := by
    intro z hz
    obtain ⟨v, hv, hvbad⟩ := hn z hz
    apply mem_iUnion.mpr ⟨⟨v, hv⟩, ?_⟩
    by_cases hzre : z.re = v.re
    · exact Or.inl hzre
    · right
      by_contra hzim
      exact hzim (hvbad hzre)
  have hUzero : volume U = 0 := measure_mono_null hsub hbadzero
  exact hUopen.measure_ne_zero volume hUne hUzero

private theorem exists_common_offGrid_mem_open
    {C : ApproximationContext} (s t : ↥C.centres)
    {U : Set Tiling.Plane} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U,
      OffVertexCoordinateGrid C.region (-(s : Tiling.Plane) + z) ∧
        OffVertexCoordinateGrid C.region (-(t : Tiling.Plane) + z) := by
  classical
  let Vs : Finset Tiling.Plane :=
    C.region.vertexFinset.image (fun v => (s : Tiling.Plane) + v)
  let Vt : Finset Tiling.Plane :=
    C.region.vertexFinset.image (fun v => (t : Tiling.Plane) + v)
  let V : Finset Tiling.Plane := Vs ∪ Vt
  obtain ⟨z, hzU, hzV⟩ := exists_offFiniteCoordinateGrid_mem_open V hUopen hUne
  refine ⟨z, hzU, ?_, ?_⟩
  · intro v hv
    have hvf : v ∈ C.region.vertexFinset := by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv
    have hV : (s : Tiling.Plane) + v ∈ V := by
      exact Finset.mem_union_left Vt (Finset.mem_image.mpr ⟨v, hvf, rfl⟩)
    have hcoord := hzV ((s : Tiling.Plane) + v) hV
    constructor
    · intro heq
      apply hcoord.1
      change -(s : Tiling.Plane).re + z.re = v.re at heq
      change z.re = (s : Tiling.Plane).re + v.re
      linarith
    · intro heq
      apply hcoord.2
      change -(s : Tiling.Plane).im + z.im = v.im at heq
      change z.im = (s : Tiling.Plane).im + v.im
      linarith
  · intro v hv
    have hvf : v ∈ C.region.vertexFinset := by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv
    have hV : (t : Tiling.Plane) + v ∈ V := by
      exact Finset.mem_union_right Vs (Finset.mem_image.mpr ⟨v, hvf, rfl⟩)
    have hcoord := hzV ((t : Tiling.Plane) + v) hV
    constructor
    · intro heq
      apply hcoord.1
      change -(t : Tiling.Plane).re + z.re = v.re at heq
      change z.re = (t : Tiling.Plane).re + v.re
      linarith
    · intro heq
      apply hcoord.2
      change -(t : Tiling.Plane).im + z.im = v.im at heq
      change z.im = (t : Tiling.Plane).im + v.im
      linarith

private theorem pairedIntrinsicCells_exists
    {C : ApproximationContext} (s t : ↥C.centres)
    {x : Tiling.Plane}
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier) :
    ∃ z xp yp xq yq,
      z ∈ ((s : Tiling.Plane) +ᵥ C.region.openCarrier) ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier) ∧
      xp ∈ consecutiveLevelPairs
        (intrinsicCoordinateLevels C.region Axis.horizontal) ∧
      yp ∈ consecutiveLevelPairs
        (intrinsicCoordinateLevels C.region Axis.vertical) ∧
      xq ∈ consecutiveLevelPairs
        (intrinsicCoordinateLevels C.region Axis.horizontal) ∧
      yq ∈ consecutiveLevelPairs
        (intrinsicCoordinateLevels C.region Axis.vertical) ∧
      (-((s : Tiling.Plane)) + z).re ∈ Ioo xp.1 xp.2 ∧
      (-((s : Tiling.Plane)) + z).im ∈ Ioo yp.1 yp.2 ∧
      (-((t : Tiling.Plane)) + z).re ∈ Ioo xq.1 xq.2 ∧
      (-((t : Tiling.Plane)) + z).im ∈ Ioo yq.1 yq.2 := by
  have hopen : IsOpen (
      ((s : Tiling.Plane) +ᵥ C.region.openCarrier) ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier)) := by
    exact (C.region.openCarrier_regularOpen.1.vadd (s : Tiling.Plane)).inter
      (C.region.openCarrier_regularOpen.1.vadd (t : Tiling.Plane))
  have hne : (
      ((s : Tiling.Plane) +ᵥ C.region.openCarrier) ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty :=
    ⟨x, ⟨hs, ht⟩⟩
  obtain ⟨z, hz, hzsoff, hztoff⟩ :=
    exists_common_offGrid_mem_open s t hopen hne
  have hzs : -(s : Tiling.Plane) + z ∈ C.region.openCarrier := by
    obtain ⟨y, hy, hyz⟩ := Set.mem_vadd_set.mp hz.1
    rw [← hyz]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hy
  have hzt : -(t : Tiling.Plane) + z ∈ C.region.openCarrier := by
    obtain ⟨y, hy, hyz⟩ := Set.mem_vadd_set.mp hz.2
    rw [← hyz]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hy
  obtain ⟨xp, yp, hxp, hyp, hxr, hxi⟩ :=
    IntrinsicVertices.exists_intrinsicCell_around_offGrid C.region hzs hzsoff
  obtain ⟨xq, yq, hxq, hyq, hxr', hxi'⟩ :=
    IntrinsicVertices.exists_intrinsicCell_around_offGrid C.region hzt hztoff
  refine ⟨z, xp, yp, xq, yq, hz, hxp, hyp, hxq, hyq, hxr, hxi, hxr', hxi'⟩

private theorem consecutivePair_endpoint_vertices
    (K : Region) (axis : Axis) {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K axis)) :
    ∃ v w, v ∈ K.vertices ∧ w ∈ K.vertices ∧
      Axis.coord axis v = p.1 ∧ Axis.coord axis w = p.2 := by
  have hp' := (Finset.mem_filter.mp hp).1
  have hpa := (Finset.mem_product.mp hp').1
  have hpb := (Finset.mem_product.mp hp').2
  have hlevels : intrinsicCoordinateLevels K axis =
      (K.vertexFinset.image (fun v => Axis.coord axis v)) := rfl
  have hpa' : p.1 ∈ K.vertexFinset.image (fun v => Axis.coord axis v) := by
    simpa [hlevels] using hpa
  have hpb' : p.2 ∈ K.vertexFinset.image (fun v => Axis.coord axis v) := by
    simpa [hlevels] using hpb
  rcases Finset.mem_image.mp hpa' with ⟨v, hv, hvcoord⟩
  rcases Finset.mem_image.mp hpb' with ⟨w, hw, hwcoord⟩
  have hv' : v ∈ K.vertices := by
    rw [← K.coe_vertexFinset]
    exact hv
  have hw' : w ∈ K.vertices := by
    rw [← K.coe_vertexFinset]
    exact hw
  exact ⟨v, w, hv', hw', hvcoord, hwcoord⟩

private theorem translatedCellVertexPair_control
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (s t : ↥C.centres) (x : Tiling.Plane)
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices) :
    ∃ a b : ↥C.translatedVertices,
      (a : Tiling.Plane) = v + (s : Tiling.Plane) ∧
      (b : Tiling.Plane) = w + (t : Tiling.Plane) ∧
      dist (a : Tiling.Plane) b < P.controlRadius := by
  have hs' : -(s : Tiling.Plane) + x ∈ C.region.openCarrier := by
    obtain ⟨y, hy, hys⟩ := Set.mem_vadd_set.mp hs
    rw [← hys]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hy
  have ht' : -(t : Tiling.Plane) + x ∈ C.region.openCarrier := by
    obtain ⟨y, hy, hyt⟩ := Set.mem_vadd_set.mp ht
    rw [← hyt]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hy
  have hvs : v ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hv)
  have hws : w ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hw)
  have hxs : -(s : Tiling.Plane) + x ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact subset_closure (show -(s : Tiling.Plane) + x ∈ interior C.region.support from hs')
  have hxt : -(t : Tiling.Plane) + x ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact subset_closure (show -(t : Tiling.Plane) + x ∈ interior C.region.support from ht')
  have hd : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure (interior C.region.support)
  have h₁ : dist (v + (s : Tiling.Plane)) x ≤ Metric.diam C.region.support := by
    have h := Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hxs hvs
    rw [show dist (v + (s : Tiling.Plane)) x =
      dist (-(s : Tiling.Plane) + x) v by
        rw [dist_eq_norm, dist_eq_norm]
        rw [show v + (s : Tiling.Plane) - x =
          - (-(s : Tiling.Plane) + x - v) by abel, norm_neg]]
    exact h
  have h₂ : dist x (w + (t : Tiling.Plane)) ≤ Metric.diam C.region.support := by
    have h := Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hxt hws
    calc
      dist x (w + (t : Tiling.Plane)) =
          dist (-(t : Tiling.Plane) + x) w := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        simp [sub_eq_add_neg, add_comm, add_left_comm]
      _ ≤ Metric.diam C.region.support := h
  have hdiam : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
  have hlt : dist (v + (s : Tiling.Plane)) (w + (t : Tiling.Plane)) < P.scale := by
    calc
      dist (v + (s : Tiling.Plane)) (w + (t : Tiling.Plane)) ≤
          dist (v + (s : Tiling.Plane)) x + dist x (w + (t : Tiling.Plane)) :=
        dist_triangle _ _ _
      _ ≤ 2 * Metric.diam C.region.support := by linarith
      _ = 2 * Metric.diam C.region.openCarrier := by rw [hd]
      _ < P.scale := by linarith
  let a : ↥C.translatedVertices :=
    ⟨v + (s : Tiling.Plane), by
      rw [ApproximationContext.translatedVertices]
      exact Set.mem_add.mpr ⟨v, hv, s, s.property, rfl⟩⟩
  let b : ↥C.translatedVertices :=
    ⟨w + (t : Tiling.Plane), by
      rw [ApproximationContext.translatedVertices]
      exact Set.mem_add.mpr ⟨w, hw, t, t.property, rfl⟩⟩
  refine ⟨a, b, rfl, rfl, ?_⟩
  exact lt_trans hlt P.scale_lt_controlRadius

private theorem translatedCellVertexPair_coord_lt_transport
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (s t : ↥C.centres) (x : Tiling.Plane)
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices) :
    ∃ a b : ↥C.translatedVertices,
      (a : Tiling.Plane) = v + (s : Tiling.Plane) ∧
      (b : Tiling.Plane) = w + (t : Tiling.Plane) ∧
      (Axis.coord axis (mapTranslatedVertex phi a -
        mapTranslatedVertex phi b) < 0 ↔
        Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) < 0) := by
  obtain ⟨a, b, ha, hb, hab⟩ := translatedCellVertexPair_control P hScale s t x hs ht v w hv hw
  refine ⟨a, b, ha, hb, ?_⟩
  exact mappedTranslatedVertex_coord_lt_iff P phi hphi axis a b hab

private theorem translatedEndpoint_orderTransport
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (s t : ↥C.centres) (x : Tiling.Plane)
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (horder : Axis.coord axis (v + (s : Tiling.Plane)) <
      Axis.coord axis (w + (t : Tiling.Plane))) :
    ∃ a b : ↥C.translatedVertices,
      (a : Tiling.Plane) = v + (s : Tiling.Plane) ∧
      (b : Tiling.Plane) = w + (t : Tiling.Plane) ∧
      Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) < 0 ∧
      Axis.coord axis (mapTranslatedVertex phi a -
        mapTranslatedVertex phi b) < 0 := by
  obtain ⟨a, b, ha, hb, hiff⟩ :=
    translatedCellVertexPair_coord_lt_transport P hScale phi hphi axis s t x hs ht v w hv hw
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · rw [show (a : Tiling.Plane) = v + (s : Tiling.Plane) from ha,
      show (b : Tiling.Plane) = w + (t : Tiling.Plane) from hb]
    cases axis with
    | horizontal => simpa [Axis.coord, Complex.sub_re] using sub_neg.mpr horder
    | vertical => simpa [Axis.coord, Complex.sub_im] using sub_neg.mpr horder
  · exact hiff.mpr (by
      rw [ha, hb]
      cases axis with
      | horizontal => simpa [Axis.coord, Complex.sub_re] using sub_neg.mpr horder
      | vertical => simpa [Axis.coord, Complex.sub_im] using sub_neg.mpr horder)

private theorem translatedEndpoint_orderTransport_iff
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (s t : ↥C.centres) (x : Tiling.Plane)
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices) :
    ∃ a b : ↥C.translatedVertices,
      (a : Tiling.Plane) = v + (s : Tiling.Plane) ∧
      (b : Tiling.Plane) = w + (t : Tiling.Plane) ∧
      (Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) < 0 ↔
        Axis.coord axis (mapTranslatedVertex phi a -
          mapTranslatedVertex phi b) < 0) := by
  obtain ⟨a, b, ha, hb, hiff⟩ := translatedCellVertexPair_coord_lt_transport
    P hScale phi hphi axis s t x hs ht v w hv hw
  exact ⟨a, b, ha, hb, hiff.symm⟩

private theorem pairedCell_crossOrders_transport
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (s t : ↥C.centres) (x : Tiling.Plane)
    (hs : x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (ht : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier) :
    ∃ a₁ b₂ a₂ b₁ c₁ d₂ c₂ d₁ : ↥C.translatedVertices,
      Axis.coord Axis.horizontal (mapTranslatedVertex phi a₁ -
        mapTranslatedVertex phi b₂) < 0 ∧
      Axis.coord Axis.horizontal (mapTranslatedVertex phi a₂ -
        mapTranslatedVertex phi b₁) < 0 ∧
      Axis.coord Axis.vertical (mapTranslatedVertex phi c₁ -
        mapTranslatedVertex phi d₂) < 0 ∧
      Axis.coord Axis.vertical (mapTranslatedVertex phi c₂ -
        mapTranslatedVertex phi d₁) < 0 := by
  obtain ⟨z, xp, yp, xq, yq, hz, hxp, hyp, hxq, hyq,
      hxr, hxi, hxr', hxi'⟩ := pairedIntrinsicCells_exists s t hs ht
  obtain ⟨v₁, v₂, hv₁, hv₂, hv₁coord, hv₂coord⟩ :=
    consecutivePair_endpoint_vertices C.region Axis.horizontal hxp
  obtain ⟨w₁, w₂, hw₁, hw₂, hw₁coord, hw₂coord⟩ :=
    consecutivePair_endpoint_vertices C.region Axis.horizontal hxq
  obtain ⟨u₁, u₂, hu₁, hu₂, hu₁coord, hu₂coord⟩ :=
    consecutivePair_endpoint_vertices C.region Axis.vertical hyp
  obtain ⟨r₁, r₂, hr₁, hr₂, hr₁coord, hr₂coord⟩ :=
    consecutivePair_endpoint_vertices C.region Axis.vertical hyq
  simp only [Complex.add_re, Complex.neg_re] at hxr hxr'
  simp only [Complex.add_im, Complex.neg_im] at hxi hxi'
  have hv₁r : v₁.re = xp.1 := by simpa [Axis.coord] using hv₁coord
  have hv₂r : v₂.re = xp.2 := by simpa [Axis.coord] using hv₂coord
  have hw₁r : w₁.re = xq.1 := by simpa [Axis.coord] using hw₁coord
  have hw₂r : w₂.re = xq.2 := by simpa [Axis.coord] using hw₂coord
  have hu₁i : u₁.im = yp.1 := by simpa [Axis.coord] using hu₁coord
  have hu₂i : u₂.im = yp.2 := by simpa [Axis.coord] using hu₂coord
  have hr₁i : r₁.im = yq.1 := by simpa [Axis.coord] using hr₁coord
  have hr₂i : r₂.im = yq.2 := by simpa [Axis.coord] using hr₂coord
  have hleft : Axis.coord Axis.horizontal (v₁ + (s : Tiling.Plane)) <
      Axis.coord Axis.horizontal (w₂ + (t : Tiling.Plane)) := by
    simp only [Axis.coord, Complex.add_re]
    linarith [hxr.1, hxr'.2, hv₁r, hw₂r]
  have hright : Axis.coord Axis.horizontal (w₁ + (t : Tiling.Plane)) <
    Axis.coord Axis.horizontal (v₂ + (s : Tiling.Plane)) := by
    simp only [Axis.coord, Complex.add_re]
    linarith [hxr'.1, hxr.2, hw₁r, hv₂r]
  have hbottom : Axis.coord Axis.vertical (u₁ + (s : Tiling.Plane)) <
    Axis.coord Axis.vertical (r₂ + (t : Tiling.Plane)) := by
    simp only [Axis.coord, Complex.add_im]
    linarith [hxi.1, hxi'.2, hu₁i, hr₂i]
  have htop : Axis.coord Axis.vertical (r₁ + (t : Tiling.Plane)) <
    Axis.coord Axis.vertical (u₂ + (s : Tiling.Plane)) := by
    simp only [Axis.coord, Complex.add_im]
    linarith [hxi'.1, hxi.2, hr₁i, hu₂i]
  obtain ⟨a₁, b₂, ha₁, hb₂, _ha₁s, hab₂⟩ := translatedEndpoint_orderTransport
    P hScale phi hphi Axis.horizontal s t z hz.1 hz.2 v₁ w₂ hv₁ hw₂ hleft
  obtain ⟨a₂, b₁, ha₂, hb₁, _ha₂s, hab₁⟩ := translatedEndpoint_orderTransport
    P hScale phi hphi Axis.horizontal t s z hz.2 hz.1 w₁ v₂ hw₁ hv₂ hright
  obtain ⟨c₁, d₂, hc₁, hd₂, _hc₁s, hcd₂⟩ := translatedEndpoint_orderTransport
    P hScale phi hphi Axis.vertical s t z hz.1 hz.2 u₁ r₂ hu₁ hr₂ hbottom
  obtain ⟨c₂, d₁, hc₂, hd₁, _hc₂s, hcd₁⟩ := translatedEndpoint_orderTransport
    P hScale phi hphi Axis.vertical t s z hz.2 hz.1 r₁ u₂ hr₁ hu₂ htop
  exact ⟨a₁, b₂, a₂, b₁, c₁, d₂, c₂, d₁,
    hab₂, hab₁, hcd₂, hcd₁⟩

private theorem rectangleOverlap_of_orderTransport
    {a b c d e f g h a' b' c' d' e' f' g' h' : ℝ}
    (hab : a < b) (hcd : c < d) (hef : e < f) (hgh : g < h)
    (hab' : a' < b') (hcd' : c' < d') (hef' : e' < f') (hgh' : g' < h')
    (haf : a < f ↔ a' < f') (heb : e < b ↔ e' < b')
    (ch : c < h ↔ c' < h') (gd : g < d ↔ g' < d') :
    (interior (closedAxisBox a b c d) ∩
      interior (closedAxisBox e f g h)).Nonempty ↔
    (interior (closedAxisBox a' b' c' d') ∩
      interior (closedAxisBox e' f' g' h')).Nonempty := by
  rw [interior_closedAxisBox_inter_iff hab hcd hef hgh,
    interior_closedAxisBox_inter_iff hab' hcd' hef' hgh']
  constructor
  · rintro ⟨hre, him⟩
    have haf' : a' < f' := haf.mp (lt_of_le_of_lt
      (le_max_left _ _) (lt_of_lt_of_le hre (min_le_right _ _)))
    have heb' : e' < b' := heb.mp (lt_of_le_of_lt
      (le_max_right _ _) (lt_of_lt_of_le hre (min_le_left _ _)))
    have ch' : c' < h' := ch.mp (lt_of_le_of_lt
      (le_max_left _ _) (lt_of_lt_of_le him (min_le_right _ _)))
    have gd' : g' < d' := gd.mp (lt_of_le_of_lt
      (le_max_right _ _) (lt_of_lt_of_le him (min_le_left _ _)))
    constructor
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hab', heb'⟩),
        (max_lt_iff.mpr ⟨haf', hef'⟩)⟩
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hcd', gd'⟩),
        (max_lt_iff.mpr ⟨ch', hgh'⟩)⟩
  · rintro ⟨hre, him⟩
    have haf₀ : a < f := haf.mpr (lt_of_le_of_lt
      (le_max_left _ _) (lt_of_lt_of_le hre (min_le_right _ _)))
    have heb₀ : e < b := heb.mpr (lt_of_le_of_lt
      (le_max_right _ _) (lt_of_lt_of_le hre (min_le_left _ _)))
    have ch₀ : c < h := ch.mpr (lt_of_le_of_lt
      (le_max_left _ _) (lt_of_lt_of_le him (min_le_right _ _)))
    have gd₀ : g < d := gd.mpr (lt_of_le_of_lt
      (le_max_right _ _) (lt_of_lt_of_le him (min_le_left _ _)))
    constructor
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hab, heb₀⟩),
        (max_lt_iff.mpr ⟨haf₀, hef⟩)⟩
    · rw [lt_min_iff]
      exact ⟨(max_lt_iff.mpr ⟨hcd, gd₀⟩),
        (max_lt_iff.mpr ⟨ch₀, hgh⟩)⟩

private theorem mapPoint_add_local
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
      z.im ∈ C.coordinateSpace}) :
    mapPoint phi ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩ = mapPoint phi x + mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one]
    norm_num
    norm_cast
    exact_mod_cast (map_add phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact_mod_cast (map_add phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem translatedVertex_targetImage
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s : ↥C.centres) (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
    ∃ a : ↥C.translatedVertices,
      (a : Tiling.Plane) = v + (s : Tiling.Plane) ∧
      mapTranslatedVertex phi a = Tphi s + D.planarHomeomorph v := by
  let a : ↥C.translatedVertices :=
    ⟨v + (s : Tiling.Plane), by
      rw [ApproximationContext.translatedVertices]
      exact Set.mem_add.mpr ⟨v, hv, s, s.property, rfl⟩⟩
  refine ⟨a, rfl, ?_⟩
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint a =
      ⟨v + (s : Tiling.Plane),
        C.coordinateSpace.add_mem (C.vertex_re_mem v hv) (C.centre_re_mem s s.property),
        C.coordinateSpace.add_mem (C.vertex_im_mem v hv) (C.centre_im_mem s s.property)⟩ := by
    apply Subtype.ext
    rfl
  rw [hpoint]
  have hadd := mapPoint_add_local phi (C.vertexPoint v hv)
    (C.centrePoint s s.property)
  calc
    mapPoint phi ⟨v + (s : Tiling.Plane),
        C.coordinateSpace.add_mem (C.vertex_re_mem v hv)
          (C.centre_re_mem s s.property),
        C.coordinateSpace.add_mem (C.vertex_im_mem v hv)
          (C.centre_im_mem s s.property)⟩ =
        mapPoint phi (C.vertexPoint v hv) +
          mapPoint phi (C.centrePoint s s.property) := by
            simpa [ApproximationContext.vertexPoint,
              ApproximationContext.centrePoint] using hadd
    _ = D.planarHomeomorph v + Tphi s := by
      rw [D.vertex_agreement v hv, hTphi s]
    _ = Tphi s + D.planarHomeomorph v := add_comm _ _

private theorem interior_closedAxisBox_local
    {a b c d : ℝ} :
    interior (closedAxisBox a b c d) =
      {z : Tiling.Plane | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d} := by
  change interior (Icc a b ×ℂ Icc c d) = _
  rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
  ext z
  exact Complex.mem_reProdIm

private theorem targetCell_mem_of_allVertexSides
    {C : ApproximationContext}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (s : ↥C.centres)
    {u y : Tiling.Plane}
    (hu : u ∈ C.region.openCarrier)
    (huoff : OffVertexCoordinateGrid C.region u)
    (hyoff : OffVertexCoordinateGrid D.deformedRegion
      (-(Tphi s) + y))
    (hsource : ∀ v ∈ C.region.vertices,
      (u.re < v.re ↔ (D.planarHomeomorph u).re <
        (D.planarHomeomorph v).re) ∧
      (v.re < u.re ↔ (D.planarHomeomorph v).re <
        (D.planarHomeomorph u).re) ∧
      (u.im < v.im ↔ (D.planarHomeomorph u).im <
        (D.planarHomeomorph v).im) ∧
      (v.im < u.im ↔ (D.planarHomeomorph v).im <
        (D.planarHomeomorph u).im))
    (htarget : ∀ v ∈ C.region.vertices,
      ((D.planarHomeomorph u).re < (D.planarHomeomorph v).re ↔
        (-(Tphi s) + y).re < (D.planarHomeomorph v).re) ∧
      ((D.planarHomeomorph u).im < (D.planarHomeomorph v).im ↔
        (-(Tphi s) + y).im < (D.planarHomeomorph v).im)) :
    y ∈ Tphi s +ᵥ D.deformedRegion.openCarrier := by
  have hHuoff : OffVertexCoordinateGrid D.deformedRegion
      (D.planarHomeomorph u) := by
    intro w hw
    rw [D.vertices_image] at hw
    rcases hw with ⟨v, hv, rfl⟩
    constructor
    · intro heq
      rcases lt_or_gt_of_ne (huoff v hv).1 with hlt | hgt
      · exact (hsource v hv).1.mp hlt |>.ne heq
      · exact (hsource v hv).2.1.mp hgt |>.ne heq.symm
    · intro heq
      rcases lt_or_gt_of_ne (huoff v hv).2 with hlt | hgt
      · exact (hsource v hv).2.2.1.mp hlt |>.ne heq
      · exact (hsource v hv).2.2.2.mp hgt |>.ne heq.symm
  have hsame : SameVertexGridCell D.deformedRegion
      (D.planarHomeomorph u) (-(Tphi s) + y) := by
    constructor
    · intro v hv
      rw [D.vertices_image] at hv
      rcases hv with ⟨w, hw, rfl⟩
      exact (htarget w hw).1
    · intro v hv
      rw [D.vertices_image] at hv
      rcases hv with ⟨w, hw, rfl⟩
      exact (htarget w hw).2
  have hyrel : -(Tphi s) + y ∈ D.deformedRegion.openCarrier :=
    (sameVertexGridCell_openCarrier_iff D.deformedRegion
      (D.planarHomeomorph u) (-(Tphi s) + y) hHuoff hyoff hsame).mp
      (D.deformedRegion_openCarrier ▸ ⟨u, hu, rfl⟩)
  exact (Set.mem_vadd_set_iff_neg_vadd_mem).mpr hyrel

private theorem intrinsicCell_targetSides
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (s : ↥C.centres)
    {u y : Tiling.Plane} {xp yp : ℝ × ℝ}
    (hxp : xp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.horizontal))
    (hyp : yp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.vertical))
    (hu : u ∈ C.region.openCarrier)
    (hxr : u.re ∈ Ioo xp.1 xp.2)
    (hxi : u.im ∈ Ioo yp.1 yp.2)
    (v₁ v₂ u₁ u₂ : Tiling.Plane)
    (hv₁ : v₁ ∈ C.region.vertices) (hv₂ : v₂ ∈ C.region.vertices)
    (hu₁ : u₁ ∈ C.region.vertices) (hu₂ : u₂ ∈ C.region.vertices)
    (hv₁r : v₁.re = xp.1) (hv₂r : v₂.re = xp.2)
    (hu₁i : u₁.im = yp.1) (hu₂i : u₂.im = yp.2)
    (hybounds :
      (D.planarHomeomorph v₁).re < (-(Tphi s) + y).re ∧
      (-(Tphi s) + y).re < (D.planarHomeomorph v₂).re ∧
      (D.planarHomeomorph u₁).im < (-(Tphi s) + y).im ∧
      (-(Tphi s) + y).im < (D.planarHomeomorph u₂).im) :
    y ∈ Tphi s +ᵥ D.deformedRegion.openCarrier := by
  have hxp' := hxp
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hxp'
  have hyp' := hyp
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hyp'
  have hlevel_re : ∀ v ∈ C.region.vertices,
      v.re ∈ intrinsicCoordinateLevels C.region Axis.horizontal := by
    intro v hv
    rw [intrinsicCoordinateLevels]
    exact Finset.mem_image.mpr ⟨v, by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv, by simp [Axis.coord]⟩
  have hlevel_im : ∀ v ∈ C.region.vertices,
      v.im ∈ intrinsicCoordinateLevels C.region Axis.vertical := by
    intro v hv
    rw [intrinsicCoordinateLevels]
    exact Finset.mem_image.mpr ⟨v, by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv, by simp [Axis.coord]⟩
  have hside_re : ∀ v ∈ C.region.vertices,
      v.re ≤ xp.1 ∨ xp.2 ≤ v.re := by
    intro v hv
    by_contra h
    push Not at h
    exact hxp'.2.2 (v.re) (hlevel_re v hv) ⟨h.1, h.2⟩
  have hside_im : ∀ v ∈ C.region.vertices,
      v.im ≤ yp.1 ∨ yp.2 ≤ v.im := by
    intro v hv
    by_contra h
    push Not at h
    exact hyp'.2.2 (v.im) (hlevel_im v hv) ⟨h.1, h.2⟩
  have hmono_re : ∀ {v w : Tiling.Plane}, v.re ≤ w.re →
      (D.planarHomeomorph v).re ≤ (D.planarHomeomorph w).re := by
    intro v w hvw
    simpa [D.planarHomeomorph_apply, Complex.add_re] using
      D.firstHomeomorph_strictMono.monotone hvw
  have hmono_im : ∀ {v w : Tiling.Plane}, v.im ≤ w.im →
      (D.planarHomeomorph v).im ≤ (D.planarHomeomorph w).im := by
    intro v w hvw
    simpa [D.planarHomeomorph_apply, Complex.add_im] using
      D.secondHomeomorph_strictMono.monotone hvw
  have huoff : OffVertexCoordinateGrid C.region u := by
    intro v hv
    constructor
    · intro heq
      exact (hxp'.2.2 (v.re) (hlevel_re v hv)) ⟨by linarith [hxr.1, heq],
        by linarith [hxr.2, heq]⟩
    · intro heq
      exact (hyp'.2.2 (v.im) (hlevel_im v hv)) ⟨by linarith [hxi.1, heq],
        by linarith [hxi.2, heq]⟩
  have hsource : ∀ v ∈ C.region.vertices,
      (u.re < v.re ↔ (D.planarHomeomorph u).re <
        (D.planarHomeomorph v).re) ∧
      (v.re < u.re ↔ (D.planarHomeomorph v).re <
        (D.planarHomeomorph u).re) ∧
      (u.im < v.im ↔ (D.planarHomeomorph u).im <
        (D.planarHomeomorph v).im) ∧
      (v.im < u.im ↔ (D.planarHomeomorph v).im <
        (D.planarHomeomorph u).im) := by
    intro v hv
    constructor
    · simpa [D.planarHomeomorph_apply, Complex.add_re] using
        D.firstHomeomorph_strictMono.lt_iff_lt.symm
    constructor
    · simpa [D.planarHomeomorph_apply, Complex.add_re] using
        D.firstHomeomorph_strictMono.lt_iff_lt.symm
    constructor
    · simpa [D.planarHomeomorph_apply, Complex.add_im] using
        D.secondHomeomorph_strictMono.lt_iff_lt.symm
    · simpa [D.planarHomeomorph_apply, Complex.add_im] using
        D.secondHomeomorph_strictMono.lt_iff_lt.symm
  have hyoff : OffVertexCoordinateGrid D.deformedRegion
      (-(Tphi s) + y) := by
    intro w hw
    rw [D.vertices_image] at hw
    rcases hw with ⟨v, hv, rfl⟩
    constructor
    · rcases hside_re v hv with hleft | hright
      · have hle := hmono_re (v := v) (w := v₁) (by linarith [hleft, hv₁r])
        intro heq
        linarith [hybounds.1, hle]
      · have hge := hmono_re (v := v₂) (w := v) (by linarith [hright, hv₂r])
        intro heq
        linarith [hybounds.2.1, hge]
    · rcases hside_im v hv with hbottom | htop
      · have hle := hmono_im (v := v) (w := u₁) (by linarith [hbottom, hu₁i])
        intro heq
        linarith [hybounds.2.1, hle]
      · have hge := hmono_im (v := u₂) (w := v) (by linarith [htop, hu₂i])
        intro heq
        linarith [hybounds.2.2.2, hge]
  have htarget : ∀ v ∈ C.region.vertices,
      ((D.planarHomeomorph u).re < (D.planarHomeomorph v).re ↔
        (-(Tphi s) + y).re < (D.planarHomeomorph v).re) ∧
      ((D.planarHomeomorph u).im < (D.planarHomeomorph v).im ↔
        (-(Tphi s) + y).im < (D.planarHomeomorph v).im) := by
    intro v hv
    have hre : (D.planarHomeomorph u).re <
        (D.planarHomeomorph v).re ↔
        (-(Tphi s) + y).re < (D.planarHomeomorph v).re := by
      rcases hside_re v hv with hleft | hright
      · have hle := hmono_re (v := v) (w := v₁) (by linarith [hleft, hv₁r])
        have hfalse₁ : ¬ (D.planarHomeomorph u).re <
            (D.planarHomeomorph v).re := by
          apply not_lt_of_ge
          exact hmono_re (v := v) (w := u)
            (by linarith [hleft, hxr.1])
        have hfalse₂ : ¬ (-(Tphi s) + y).re <
            (D.planarHomeomorph v).re := by linarith [hybounds.1, hle]
        exact iff_of_false hfalse₁ hfalse₂
      · have hge := hmono_re (v := v₂) (w := v) (by linarith [hright, hv₂r])
        have htrue₁ : (D.planarHomeomorph u).re <
            (D.planarHomeomorph v).re := by
          exact (hsource v hv).1.mp <| by linarith [hright, hxr.2]
        have htrue₂ : (-(Tphi s) + y).re <
            (D.planarHomeomorph v).re := by linarith [hybounds.2.1, hge]
        exact iff_of_true htrue₁ htrue₂
    have him : (D.planarHomeomorph u).im <
        (D.planarHomeomorph v).im ↔
        (-(Tphi s) + y).im < (D.planarHomeomorph v).im := by
      rcases hside_im v hv with hbottom | htop
      · have hle := hmono_im (v := v) (w := u₁) (by linarith [hbottom, hu₁i])
        have hfalse₁ : ¬ (D.planarHomeomorph u).im <
            (D.planarHomeomorph v).im := by
          apply not_lt_of_ge
          exact hmono_im (v := v) (w := u)
            (by linarith [hbottom, hxi.1])
        have hfalse₂ : ¬ (-(Tphi s) + y).im <
            (D.planarHomeomorph v).im := by linarith [hybounds.2.2.1, hle]
        exact iff_of_false hfalse₁ hfalse₂
      · have hge := hmono_im (v := u₂) (w := v) (by linarith [htop, hu₂i])
        have htrue₁ : (D.planarHomeomorph u).im <
            (D.planarHomeomorph v).im := by
          exact (hsource v hv).2.2.1.mp <| by linarith [htop, hxi.2]
        have htrue₂ : (-(Tphi s) + y).im <
            (D.planarHomeomorph v).im := by linarith [hybounds.2.2.2, hge]
        exact iff_of_true htrue₁ htrue₂
    exact ⟨hre, him⟩
  exact targetCell_mem_of_allVertexSides phi D Tphi s hu huoff hyoff hsource htarget

private theorem transportedCellPair_mem_of_targetRectangles
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    {s t : ↥C.centres} {z₀ y : Tiling.Plane}
    (hzs : z₀ ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier)
    (hzt : z₀ ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier)
    {xp yp xq yq : ℝ × ℝ}
    (hxp : xp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.horizontal))
    (hyp : yp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.vertical))
    (hxq : xq ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.horizontal))
    (hyq : yq ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.vertical))
    (hxr : (-(s : Tiling.Plane) + z₀).re ∈ Ioo xp.1 xp.2)
    (hxi : (-(s : Tiling.Plane) + z₀).im ∈ Ioo yp.1 yp.2)
    (hxr' : (-(t : Tiling.Plane) + z₀).re ∈ Ioo xq.1 xq.2)
    (hxi' : (-(t : Tiling.Plane) + z₀).im ∈ Ioo yq.1 yq.2)
    (v₁ v₂ w₁ w₂ u₁ u₂ r₁ r₂ : Tiling.Plane)
    (hv₁ : v₁ ∈ C.region.vertices) (hv₂ : v₂ ∈ C.region.vertices)
    (hw₁ : w₁ ∈ C.region.vertices) (hw₂ : w₂ ∈ C.region.vertices)
    (hu₁ : u₁ ∈ C.region.vertices) (hu₂ : u₂ ∈ C.region.vertices)
    (hr₁ : r₁ ∈ C.region.vertices) (hr₂ : r₂ ∈ C.region.vertices)
    (hv₁r : v₁.re = xp.1) (hv₂r : v₂.re = xp.2)
    (hw₁r : w₁.re = xq.1) (hw₂r : w₂.re = xq.2)
    (hu₁i : u₁.im = yp.1) (hu₂i : u₂.im = yp.2)
    (hr₁i : r₁.im = yq.1) (hr₂i : r₂.im = yq.2)
    (hyS : y ∈ interior (closedAxisBox
      (Tphi s + D.planarHomeomorph v₁).re
      (Tphi s + D.planarHomeomorph v₂).re
      (Tphi s + D.planarHomeomorph u₁).im
      (Tphi s + D.planarHomeomorph u₂).im))
    (hyT : y ∈ interior (closedAxisBox
      (Tphi t + D.planarHomeomorph w₁).re
      (Tphi t + D.planarHomeomorph w₂).re
      (Tphi t + D.planarHomeomorph r₁).im
      (Tphi t + D.planarHomeomorph r₂).im)) :
    y ∈ Tphi s +ᵥ D.deformedRegion.openCarrier ∧
      y ∈ Tphi t +ᵥ D.deformedRegion.openCarrier := by
  rw [interior_closedAxisBox_local] at hyS hyT
  have hus : -(s : Tiling.Plane) + z₀ ∈ C.region.openCarrier := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hzs
  have hut : -(t : Tiling.Plane) + z₀ ∈ C.region.openCarrier := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hzt
  have hs_bounds :
      (D.planarHomeomorph v₁).re < (-(Tphi s) + y).re ∧
      (-(Tphi s) + y).re < (D.planarHomeomorph v₂).re ∧
      (D.planarHomeomorph u₁).im < (-(Tphi s) + y).im ∧
      (-(Tphi s) + y).im < (D.planarHomeomorph u₂).im := by
    constructor
    · simpa [Complex.add_re, Complex.neg_re] using hyS.1.1
    constructor
    · simpa [Complex.add_re, Complex.neg_re] using hyS.1.2
    constructor
    · simpa [Complex.add_im, Complex.neg_im] using hyS.2.1
    · simpa [Complex.add_im, Complex.neg_im] using hyS.2.2
  have ht_bounds :
      (D.planarHomeomorph w₁).re < (-(Tphi t) + y).re ∧
      (-(Tphi t) + y).re < (D.planarHomeomorph w₂).re ∧
      (D.planarHomeomorph r₁).im < (-(Tphi t) + y).im ∧
      (-(Tphi t) + y).im < (D.planarHomeomorph r₂).im := by
    constructor
    · simpa [Complex.add_re, Complex.neg_re] using hyT.1.1
    constructor
    · simpa [Complex.add_re, Complex.neg_re] using hyT.1.2
    constructor
    · simpa [Complex.add_im, Complex.neg_im] using hyT.2.1
    · simpa [Complex.add_im, Complex.neg_im] using hyT.2.2
  constructor
  · apply intrinsicCell_targetSides phi D Tphi s hxp hyp hus
      (by simpa [Complex.add_re, Complex.neg_re] using hxr)
      (by simpa [Complex.add_im, Complex.neg_im] using hxi)
      v₁ v₂ u₁ u₂ hv₁ hv₂ hu₁ hu₂ hv₁r hv₂r hu₁i hu₂i hs_bounds
  · apply intrinsicCell_targetSides phi D Tphi t hxq hyq hut
      (by simpa [Complex.add_re, Complex.neg_re] using hxr')
      (by simpa [Complex.add_im, Complex.neg_im] using hxi')
      w₁ w₂ r₁ r₂ hw₁ hw₂ hr₁ hr₂ hw₁r hw₂r hr₁i hr₂i ht_bounds

private theorem consecutiveLevelPair_reflect_planarHomeomorph
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (axis : Axis) {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels D.deformedRegion axis)) :
    ∃ v w, v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
      Axis.coord axis (D.planarHomeomorph v) = p.1 ∧
      Axis.coord axis (D.planarHomeomorph w) = p.2 ∧
      (Axis.coord axis v, Axis.coord axis w) ∈
        consecutiveLevelPairs (intrinsicCoordinateLevels C.region axis) := by
  obtain ⟨av, aw, hav, haw, havcoord, hawcoord⟩ :=
    consecutivePair_endpoint_vertices D.deformedRegion axis hp
  rw [D.vertices_image] at hav haw
  rcases hav with ⟨v, hv, hvimage⟩
  rcases haw with ⟨w, hw, hwimage⟩
  have hp' := hp
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp'
  have hvlevel : Axis.coord axis v ∈
      intrinsicCoordinateLevels C.region axis := by
    rw [intrinsicCoordinateLevels]
    exact Finset.mem_image.mpr ⟨v, by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv, rfl⟩
  have hwlevel : Axis.coord axis w ∈
      intrinsicCoordinateLevels C.region axis := by
    rw [intrinsicCoordinateLevels]
    exact Finset.mem_image.mpr ⟨w, by
      change w ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hw, rfl⟩
  have hvcoord' : Axis.coord axis (D.planarHomeomorph v) = p.1 := by
    rw [hvimage]
    exact havcoord
  have hwcoord' : Axis.coord axis (D.planarHomeomorph w) = p.2 := by
    rw [hwimage]
    exact hawcoord
  have horder : Axis.coord axis v < Axis.coord axis w := by
    cases axis with
    | horizontal =>
        change v.re < w.re
        have hvfirst : D.firstHomeomorph v.re = p.1 := by
          simpa [D.planarHomeomorph_apply, Axis.coord] using hvcoord'
        have hwfirst : D.firstHomeomorph w.re = p.2 := by
          simpa [D.planarHomeomorph_apply, Axis.coord] using hwcoord'
        apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
        rw [hvfirst, hwfirst]
        exact hp'.2.1
    | vertical =>
        change v.im < w.im
        have hvsecond : D.secondHomeomorph v.im = p.1 := by
          simpa [D.planarHomeomorph_apply, Axis.coord] using hvcoord'
        have hwsecond : D.secondHomeomorph w.im = p.2 := by
          simpa [D.planarHomeomorph_apply, Axis.coord] using hwcoord'
        apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
        rw [hvsecond, hwsecond]
        exact hp'.2.1
  have hno : ∀ q ∈ intrinsicCoordinateLevels C.region axis,
      ¬(Axis.coord axis v < q ∧ q < Axis.coord axis w) := by
    intro q hq hbetween
    obtain ⟨z, hz, hzcoord⟩ := Finset.mem_image.mp hq
    have hzset : z ∈ (↑C.region.vertexFinset : Set Tiling.Plane) := by
      exact hz
    have hzV : z ∈ C.region.vertices := by
      simpa only [C.region.coe_vertexFinset] using hzset
    have hzlevel : Axis.coord axis (D.planarHomeomorph z) ∈
        intrinsicCoordinateLevels D.deformedRegion axis := by
      rw [intrinsicCoordinateLevels]
      have hzimage : D.planarHomeomorph z ∈ D.deformedRegion.vertices := by
        rw [D.vertices_image]
        exact ⟨z, hzV, rfl⟩
      have hzfin : D.planarHomeomorph z ∈ D.deformedRegion.vertexFinset := by
        change D.planarHomeomorph z ∈ (↑D.deformedRegion.vertexFinset : Set Tiling.Plane)
        simpa only [D.deformedRegion.coe_vertexFinset] using hzimage
      exact Finset.mem_image.mpr ⟨D.planarHomeomorph z, hzfin, rfl⟩
    have hleft : p.1 < Axis.coord axis (D.planarHomeomorph z) := by
      cases axis with
      | horizontal =>
          have hD := D.firstHomeomorph_strictMono
            (by simpa [Axis.coord] using hbetween.1)
          have hvfirst : D.firstHomeomorph v.re = p.1 := by
            simpa [D.planarHomeomorph_apply, Axis.coord] using hvcoord'
          have hzfirst : (D.planarHomeomorph z).re = D.firstHomeomorph q := by
            simpa [D.planarHomeomorph_apply, Complex.add_re] using
              congrArg D.firstHomeomorph (show z.re = q from hzcoord)
          have hleft' : p.1 < (D.planarHomeomorph z).re := by
            linarith [hvfirst, hzfirst, hD]
          simpa [Axis.coord] using hleft'
      | vertical =>
          have hD := D.secondHomeomorph_strictMono
            (by simpa [Axis.coord] using hbetween.1)
          have hvsecond : D.secondHomeomorph v.im = p.1 := by
            simpa [D.planarHomeomorph_apply, Axis.coord] using hvcoord'
          have hzsecond : (D.planarHomeomorph z).im = D.secondHomeomorph q := by
            simpa [D.planarHomeomorph_apply, Complex.add_im] using
              congrArg D.secondHomeomorph (show z.im = q from hzcoord)
          have hleft' : p.1 < (D.planarHomeomorph z).im := by
            linarith [hvsecond, hzsecond, hD]
          simpa [Axis.coord] using hleft'
    have hright : Axis.coord axis (D.planarHomeomorph z) < p.2 := by
      cases axis with
      | horizontal =>
          have hD := D.firstHomeomorph_strictMono
            (by simpa [Axis.coord] using hbetween.2)
          have hwfirst : D.firstHomeomorph w.re = p.2 := by
            simpa [D.planarHomeomorph_apply, Axis.coord] using hwcoord'
          have hzfirst : (D.planarHomeomorph z).re = D.firstHomeomorph q := by
            simpa [D.planarHomeomorph_apply, Complex.add_re] using
              congrArg D.firstHomeomorph (show z.re = q from hzcoord)
          have hright' : (D.planarHomeomorph z).re < p.2 := by
            linarith [hwfirst, hzfirst, hD]
          simpa [Axis.coord] using hright'
      | vertical =>
          have hD := D.secondHomeomorph_strictMono
            (by simpa [Axis.coord] using hbetween.2)
          have hwsecond : D.secondHomeomorph w.im = p.2 := by
            simpa [D.planarHomeomorph_apply, Axis.coord] using hwcoord'
          have hzsecond : (D.planarHomeomorph z).im = D.secondHomeomorph q := by
            simpa [D.planarHomeomorph_apply, Complex.add_im] using
              congrArg D.secondHomeomorph (show z.im = q from hzcoord)
          have hright' : (D.planarHomeomorph z).im < p.2 := by
            linarith [hwsecond, hzsecond, hD]
          simpa [Axis.coord] using hright'
    exact hp'.2.2 _ hzlevel ⟨hleft, hright⟩
  refine ⟨v, w, hv, hw, hvcoord', hwcoord', ?_⟩
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product]
  exact ⟨⟨hvlevel, hwlevel⟩, horder, hno⟩

private theorem consecutivePair_sameSide_local {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) {x y : ℝ}
    (hx : x ∈ Ioo p.1 p.2) (hy : y ∈ Ioo p.1 p.2) {c : ℝ} (hc : c ∈ s) :
    x ≠ c ∧ (x < c ↔ y < c) := by
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp
  have hnot : ¬(p.1 < c ∧ c < p.2) := hp.2.2 c hc
  have hout : c ≤ p.1 ∨ p.2 ≤ c := by
    by_contra h
    push Not at h
    exact hnot ⟨h.1, h.2⟩
  rcases hout with hcL | hcR
  · refine ⟨by linarith [hx.1], ?_⟩
    constructor <;> intro h <;> linarith [hx.1, hy.1]
  · refine ⟨by linarith [hx.2], ?_⟩
    constructor <;> intro h <;> linarith [hx.2, hy.2]

private theorem sourceCell_mem_of_rectangle
    {C : ApproximationContext} {s z x : Tiling.Plane}
    {xp yp : ℝ × ℝ}
    (hxp : xp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.horizontal))
    (hyp : yp ∈ consecutiveLevelPairs
      (intrinsicCoordinateLevels C.region Axis.vertical))
    (hz : -(s : Tiling.Plane) + z ∈ C.region.openCarrier)
    (hzr : (-(s : Tiling.Plane) + z).re ∈ Ioo xp.1 xp.2)
    (hzi : (-(s : Tiling.Plane) + z).im ∈ Ioo yp.1 yp.2)
    (hxr : (-(s : Tiling.Plane) + x).re ∈ Ioo xp.1 xp.2)
    (hxi : (-(s : Tiling.Plane) + x).im ∈ Ioo yp.1 yp.2) :
    x ∈ (s : Tiling.Plane) +ᵥ C.region.openCarrier := by
  let zr := -(s : Tiling.Plane) + z
  let xr := -(s : Tiling.Plane) + x
  have hzoff : OffVertexCoordinateGrid C.region zr := by
    intro v hv
    have hvf : v ∈ C.region.vertexFinset := by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv
    constructor
    · exact (consecutivePair_sameSide_local hxp hzr hxr
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
    · exact (consecutivePair_sameSide_local hyp hzi hxi
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
  have hxoff : OffVertexCoordinateGrid C.region xr := by
    intro v hv
    have hvf : v ∈ C.region.vertexFinset := by
      change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
      simpa only [C.region.coe_vertexFinset] using hv
    constructor
    · exact (consecutivePair_sameSide_local hxp hxr hzr
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
    · exact (consecutivePair_sameSide_local hyp hxi hzi
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
  have hsame : SameVertexGridCell C.region zr xr := by
    constructor
    · intro v hv
      have hvf : v ∈ C.region.vertexFinset := by
        change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
        simpa only [C.region.coe_vertexFinset] using hv
      exact (consecutivePair_sameSide_local hxp hzr hxr
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).2
    · intro v hv
      have hvf : v ∈ C.region.vertexFinset := by
        change v ∈ (↑C.region.vertexFinset : Set Tiling.Plane)
        simpa only [C.region.coe_vertexFinset] using hv
      exact (consecutivePair_sameSide_local hyp hzi hxi
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).2
  have hxopen : xr ∈ C.region.openCarrier :=
    (sameVertexGridCell_openCarrier_iff C.region zr xr hzoff hxoff hsame).mp hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [xr] using hxopen

private theorem targetEndpoint_orderReflect
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres) (y : Tiling.Plane)
    (hys : y ∈ Tphi s +ᵥ D.deformedRegion.openCarrier)
    (hyt : y ∈ Tphi t +ᵥ D.deformedRegion.openCarrier)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (horder : Axis.coord axis
      ((Tphi s + D.planarHomeomorph v) -
        (Tphi t + D.planarHomeomorph w)) < 0) :
    Axis.coord axis ((v + (s : Tiling.Plane)) -
      (w + (t : Tiling.Plane))) < 0 := by
  let d : ℝ := Metric.diam C.region.openCarrier
  have hd : Metric.diam C.region.support = d := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  have hdscale : Metric.diam C.region.support < P.scale := by
    rw [hd]
    dsimp [d]
    have hdnonneg : 0 ≤ Metric.diam (C.region.openCarrier : Set Tiling.Plane) :=
      Metric.diam_nonneg
    linarith
  have hDle := deformedRegion_diam_le_add_localError P hphi D hdscale
  have hlocal : P.localError < 1 := by
    rw [P.localError_eq]
    apply (inv_lt_one₀ P.scale_pos).2
    have hdnonneg : 0 ≤ Metric.diam (C.region.openCarrier : Set Tiling.Plane) :=
      Metric.diam_nonneg
    linarith
  have hDlt : Metric.diam D.deformedRegion.support < P.scale / 10 := by
    rw [hd] at hDle
    dsimp [d] at hDle ⊢
    linarith [hScale, hlocal]
  obtain ⟨a, ha, hA⟩ := translatedVertex_targetImage phi D Tphi hTphi s v hv
  obtain ⟨b, hb, hB⟩ := translatedVertex_targetImage phi D Tphi hTphi t w hw
  have hvrel : D.planarHomeomorph v ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion
        (by rw [D.vertices_image]; exact ⟨v, hv, rfl⟩))
  have hwrel : D.planarHomeomorph w ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion
        (by rw [D.vertices_image]; exact ⟨w, hw, rfl⟩))
  have hvsup : Tphi s + D.planarHomeomorph v ∈
      Tphi s +ᵥ D.deformedRegion.support := ⟨_, hvrel, rfl⟩
  have hwsup : Tphi t + D.planarHomeomorph w ∈
      Tphi t +ᵥ D.deformedRegion.support := ⟨_, hwrel, rfl⟩
  obtain ⟨ys, hysopen, hyseq⟩ := Set.mem_vadd_set.mp hys
  obtain ⟨yt, hytopen, hyteq⟩ := Set.mem_vadd_set.mp hyt
  have hysrel : ys ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact subset_closure hysopen
  have hytrel : yt ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact subset_closure hytopen
  have hdistA0 : dist (D.planarHomeomorph v) ys ≤
      Metric.diam D.deformedRegion.support :=
    Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded
      hvrel hysrel
  have hdistB0 : dist yt (D.planarHomeomorph w) ≤
      Metric.diam D.deformedRegion.support :=
    Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded
      hytrel hwrel
  have hdistA : dist (Tphi s + D.planarHomeomorph v) y ≤
      Metric.diam D.deformedRegion.support := by
    rw [← hyseq]
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdistA0
  have hdistB : dist y (Tphi t + D.planarHomeomorph w) ≤
      Metric.diam D.deformedRegion.support := by
    rw [← hyteq]
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdistB0
  have habmap : dist (mapTranslatedVertex phi a)
      (mapTranslatedVertex phi b) < P.scale / 2 := by
    rw [hA, hB]
    have htri := dist_triangle (Tphi s + D.planarHomeomorph v) y
      (Tphi t + D.planarHomeomorph w)
    have hsum : dist (Tphi s + D.planarHomeomorph v) y +
        dist y (Tphi t + D.planarHomeomorph w) < P.scale / 5 := by
      nlinarith [hDlt, hdistA, hdistB]
    have htargetdist : dist (Tphi s + D.planarHomeomorph v)
        (Tphi t + D.planarHomeomorph w) < P.scale / 5 :=
      lt_of_le_of_lt htri hsum
    nlinarith [P.scale_pos]
  have habsource := P.coarse_inverse phi hphi a b habmap
  have habcontrol : dist (a : Tiling.Plane) b < P.controlRadius :=
    lt_trans habsource P.scale_lt_controlRadius
  have href := deformation_reflectsFiniteValues P phi hphi axis a b a b
    habcontrol habcontrol
  have hmap : Axis.coord axis
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b) < 0 := by
    rw [hA, hB]
    exact horder
  have hsrc : Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) < 0 :=
    (mappedTranslatedVertex_coord_lt_iff P phi hphi axis a b habcontrol).mp hmap
  simpa [ha, hb] using hsrc

private theorem openTileOverlapTransport :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s t : ↥C.centres),
    (((s : Tiling.Plane) +ᵥ C.region.openCarrier) ∩
        ((t : Tiling.Plane) +ᵥ C.region.openCarrier)).Nonempty ↔
      ((Tphi s +ᵥ D.deformedRegion.openCarrier) ∩
        (Tphi t +ᵥ D.deformedRegion.openCarrier)).Nonempty := by
  intro C P hScale phi hphi D Tphi hTphi s t
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z₀, xp, yp, xq, yq, hz₀, hxp, hyp, hxq, hyq,
        hxr, hxi, hxr', hxi'⟩ := pairedIntrinsicCells_exists s t hz.1 hz.2
    have hxp_order : xp.1 < xp.2 := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hxp
      exact hxp.2.1
    have hyp_order : yp.1 < yp.2 := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hyp
      exact hyp.2.1
    have hxq_order : xq.1 < xq.2 := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hxq
      exact hxq.2.1
    have hyq_order : yq.1 < yq.2 := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hyq
      exact hyq.2.1
    obtain ⟨v₁, v₂, hv₁, hv₂, hv₁coord, hv₂coord⟩ :=
      consecutivePair_endpoint_vertices C.region Axis.horizontal hxp
    obtain ⟨w₁, w₂, hw₁, hw₂, hw₁coord, hw₂coord⟩ :=
      consecutivePair_endpoint_vertices C.region Axis.horizontal hxq
    obtain ⟨u₁, u₂, hu₁, hu₂, hu₁coord, hu₂coord⟩ :=
      consecutivePair_endpoint_vertices C.region Axis.vertical hyp
    obtain ⟨r₁, r₂, hr₁, hr₂, hr₁coord, hr₂coord⟩ :=
      consecutivePair_endpoint_vertices C.region Axis.vertical hyq
    have hv₁r : v₁.re = xp.1 := by simpa [Axis.coord] using hv₁coord
    have hv₂r : v₂.re = xp.2 := by simpa [Axis.coord] using hv₂coord
    have hw₁r : w₁.re = xq.1 := by simpa [Axis.coord] using hw₁coord
    have hw₂r : w₂.re = xq.2 := by simpa [Axis.coord] using hw₂coord
    have hu₁i : u₁.im = yp.1 := by simpa [Axis.coord] using hu₁coord
    have hu₂i : u₂.im = yp.2 := by simpa [Axis.coord] using hu₂coord
    have hr₁i : r₁.im = yq.1 := by simpa [Axis.coord] using hr₁coord
    have hr₂i : r₂.im = yq.2 := by simpa [Axis.coord] using hr₂coord
    have hxr0 := hxr
    have hxi0 := hxi
    have hxr1 := hxr'
    have hxi1 := hxi'
    simp only [Complex.add_re, Complex.neg_re] at hxr hxr'
    simp only [Complex.add_im, Complex.neg_im] at hxi hxi'
    have hleft : Axis.coord Axis.horizontal (v₁ + (s : Tiling.Plane)) <
        Axis.coord Axis.horizontal (w₂ + (t : Tiling.Plane)) := by
      simp only [Axis.coord, Complex.add_re]
      linarith [hxr.1, hxr'.2, hv₁r, hw₂r]
    have hright : Axis.coord Axis.horizontal (w₁ + (t : Tiling.Plane)) <
        Axis.coord Axis.horizontal (v₂ + (s : Tiling.Plane)) := by
      simp only [Axis.coord, Complex.add_re]
      linarith [hxr'.1, hxr.2, hw₁r, hv₂r]
    have hbottom : Axis.coord Axis.vertical (u₁ + (s : Tiling.Plane)) <
        Axis.coord Axis.vertical (r₂ + (t : Tiling.Plane)) := by
      simp only [Axis.coord, Complex.add_im]
      linarith [hxi.1, hxi'.2, hu₁i, hr₂i]
    have htop : Axis.coord Axis.vertical (r₁ + (t : Tiling.Plane)) <
        Axis.coord Axis.vertical (u₂ + (s : Tiling.Plane)) := by
      simp only [Axis.coord, Complex.add_im]
      linarith [hxi'.1, hxi.2, hr₁i, hu₂i]
    obtain ⟨a₁, b₂, ha₁, hb₂, hab₂iff⟩ := translatedEndpoint_orderTransport_iff
      P hScale phi hphi Axis.horizontal s t z₀ hz₀.1 hz₀.2 v₁ w₂ hv₁ hw₂
    obtain ⟨a₂, b₁, ha₂, hb₁, hab₁iff⟩ := translatedEndpoint_orderTransport_iff
      P hScale phi hphi Axis.horizontal t s z₀ hz₀.2 hz₀.1 w₁ v₂ hw₁ hv₂
    obtain ⟨c₁, d₂, hc₁, hd₂, hcd₂iff⟩ := translatedEndpoint_orderTransport_iff
      P hScale phi hphi Axis.vertical s t z₀ hz₀.1 hz₀.2 u₁ r₂ hu₁ hr₂
    obtain ⟨c₂, d₁, hc₂, hd₁, hcd₁iff⟩ := translatedEndpoint_orderTransport_iff
      P hScale phi hphi Axis.vertical t s z₀ hz₀.2 hz₀.1 r₁ u₂ hr₁ hu₂
    obtain ⟨av₁, hav₁, hav₁map⟩ := translatedVertex_targetImage phi D Tphi hTphi s v₁ hv₁
    obtain ⟨av₂, hav₂, hav₂map⟩ := translatedVertex_targetImage phi D Tphi hTphi s v₂ hv₂
    obtain ⟨aw₁, haw₁, haw₁map⟩ := translatedVertex_targetImage phi D Tphi hTphi t w₁ hw₁
    obtain ⟨aw₂, haw₂, haw₂map⟩ := translatedVertex_targetImage phi D Tphi hTphi t w₂ hw₂
    obtain ⟨au₁, hau₁, hau₁map⟩ := translatedVertex_targetImage phi D Tphi hTphi s u₁ hu₁
    obtain ⟨au₂, hau₂, hau₂map⟩ := translatedVertex_targetImage phi D Tphi hTphi s u₂ hu₂
    obtain ⟨ar₁, har₁, har₁map⟩ := translatedVertex_targetImage phi D Tphi hTphi t r₁ hr₁
    obtain ⟨ar₂, har₂, har₂map⟩ := translatedVertex_targetImage phi D Tphi hTphi t r₂ hr₂
    have ha₁eq : a₁ = av₁ := Subtype.ext (ha₁.trans hav₁.symm)
    have hb₂eq : b₂ = aw₂ := Subtype.ext (hb₂.trans haw₂.symm)
    have ha₂eq : a₂ = aw₁ := Subtype.ext (ha₂.trans haw₁.symm)
    have hb₁eq : b₁ = av₂ := Subtype.ext (hb₁.trans hav₂.symm)
    have hc₁eq : c₁ = au₁ := Subtype.ext (hc₁.trans hau₁.symm)
    have hd₂eq : d₂ = ar₂ := Subtype.ext (hd₂.trans har₂.symm)
    have hc₂eq : c₂ = ar₁ := Subtype.ext (hc₂.trans har₁.symm)
    have hd₁eq : d₁ = au₂ := Subtype.ext (hd₁.trans hau₂.symm)
    have hab₂' : (s : Tiling.Plane).re + xp.1 <
          (t : Tiling.Plane).re + xq.2 ↔
        (Tphi s + D.planarHomeomorph v₁).re <
          (Tphi t + D.planarHomeomorph w₂).re := by
      have h := hab₂iff
      rw [ha₁eq, hb₂eq, hav₁map, haw₂map] at h
      simpa [Axis.coord, Complex.sub_re, Complex.add_re, add_comm, hv₁r, hw₂r,
        hav₁, haw₂] using h
    have hab₁' : (t : Tiling.Plane).re + xq.1 <
          (s : Tiling.Plane).re + xp.2 ↔
        (Tphi t + D.planarHomeomorph w₁).re <
          (Tphi s + D.planarHomeomorph v₂).re := by
      have h := hab₁iff
      rw [ha₂eq, hb₁eq, haw₁map, hav₂map] at h
      simpa [Axis.coord, Complex.sub_re, Complex.add_re, add_comm, hw₁r, hv₂r,
        haw₁, hav₂] using h
    have hcd₂' : (s : Tiling.Plane).im + yp.1 <
          (t : Tiling.Plane).im + yq.2 ↔
        (Tphi s + D.planarHomeomorph u₁).im <
          (Tphi t + D.planarHomeomorph r₂).im := by
      have h := hcd₂iff
      rw [hc₁eq, hd₂eq, hau₁map, har₂map] at h
      simpa [Axis.coord, Complex.sub_im, Complex.add_im, add_comm, hu₁i, hr₂i,
        hau₁, har₂] using h
    have hcd₁' : (t : Tiling.Plane).im + yq.1 <
          (s : Tiling.Plane).im + yp.2 ↔
        (Tphi t + D.planarHomeomorph r₁).im <
          (Tphi s + D.planarHomeomorph u₂).im := by
      have h := hcd₁iff
      rw [hc₂eq, hd₁eq, har₁map, hau₂map] at h
      simpa [Axis.coord, Complex.sub_im, Complex.add_im, add_comm, hr₁i, hu₂i,
        har₁, hau₂] using h
    have hsbox : z₀ ∈ interior (closedAxisBox
        ((s : Tiling.Plane).re + xp.1) ((s : Tiling.Plane).re + xp.2)
        ((s : Tiling.Plane).im + yp.1) ((s : Tiling.Plane).im + yp.2)) := by
      rw [interior_closedAxisBox_local]
      exact ⟨⟨by linarith [hxr.1], by linarith [hxr.2]⟩,
        ⟨by linarith [hxi.1], by linarith [hxi.2]⟩⟩
    have htbox : z₀ ∈ interior (closedAxisBox
        ((t : Tiling.Plane).re + xq.1) ((t : Tiling.Plane).re + xq.2)
        ((t : Tiling.Plane).im + yq.1) ((t : Tiling.Plane).im + yq.2)) := by
      rw [interior_closedAxisBox_local]
      exact ⟨⟨by linarith [hxr'.1], by linarith [hxr'.2]⟩,
        ⟨by linarith [hxi'.1], by linarith [hxi'.2]⟩⟩
    have hrect := rectangleOverlap_of_orderTransport
      (a := (s : Tiling.Plane).re + xp.1) (b := (s : Tiling.Plane).re + xp.2)
      (c := (s : Tiling.Plane).im + yp.1) (d := (s : Tiling.Plane).im + yp.2)
      (e := (t : Tiling.Plane).re + xq.1) (f := (t : Tiling.Plane).re + xq.2)
      (g := (t : Tiling.Plane).im + yq.1) (h := (t : Tiling.Plane).im + yq.2)
      (a' := (Tphi s + D.planarHomeomorph v₁).re)
      (b' := (Tphi s + D.planarHomeomorph v₂).re)
      (c' := (Tphi s + D.planarHomeomorph u₁).im)
      (d' := (Tphi s + D.planarHomeomorph u₂).im)
      (e' := (Tphi t + D.planarHomeomorph w₁).re)
      (f' := (Tphi t + D.planarHomeomorph w₂).re)
      (g' := (Tphi t + D.planarHomeomorph r₁).im)
      (h' := (Tphi t + D.planarHomeomorph r₂).im)
      (by linarith [hxp_order]) (by linarith [hyp_order])
      (by linarith [hxq_order]) (by linarith [hyq_order])
      (by simpa [D.planarHomeomorph_apply, Complex.add_re] using
        add_lt_add_left (D.firstHomeomorph_strictMono (by linarith [hv₁r, hv₂r])) (Tphi s).re)
      (by simpa [D.planarHomeomorph_apply, Complex.add_im] using
        add_lt_add_left (D.secondHomeomorph_strictMono (by linarith [hu₁i, hu₂i])) (Tphi s).im)
      (by simpa [D.planarHomeomorph_apply, Complex.add_re] using
        add_lt_add_left (D.firstHomeomorph_strictMono (by linarith [hw₁r, hw₂r])) (Tphi t).re)
      (by simpa [D.planarHomeomorph_apply, Complex.add_im] using
        add_lt_add_left (D.secondHomeomorph_strictMono (by linarith [hr₁i, hr₂i])) (Tphi t).im)
      hab₂' hab₁' hcd₂' hcd₁'
    obtain ⟨y, hyS, hyT⟩ := hrect.mp ⟨z₀, hsbox, htbox⟩
    exact ⟨y, (transportedCellPair_mem_of_targetRectangles phi D Tphi hz₀.1 hz₀.2
      hxp hyp hxq hyq hxr0 hxi0 hxr1 hxi1 v₁ v₂ w₁ w₂ u₁ u₂ r₁ r₂
      hv₁ hv₂ hw₁ hw₂ hu₁ hu₂ hr₁ hr₂ hv₁r hv₂r hw₁r hw₂r hu₁i hu₂i hr₁i hr₂i
      hyS hyT).1, (transportedCellPair_mem_of_targetRectangles phi D Tphi hz₀.1 hz₀.2
      hxp hyp hxq hyq hxr0 hxi0 hxr1 hxi1 v₁ v₂ w₁ w₂ u₁ u₂ r₁ r₂
      hv₁ hv₂ hw₁ hw₂ hu₁ hu₂ hr₁ hr₂ hv₁r hv₂r hw₁r hw₂r hu₁i hu₂i hr₁i hr₂i
      hyS hyT).2⟩
  · intro htarget
    let Vs : Finset Tiling.Plane :=
      D.deformedRegion.vertexFinset.image (fun v => (Tphi s) + v)
    let Vt : Finset Tiling.Plane :=
      D.deformedRegion.vertexFinset.image (fun v => (Tphi t) + v)
    let V : Finset Tiling.Plane := Vs ∪ Vt
    have hopen : IsOpen ((Tphi s +ᵥ D.deformedRegion.openCarrier) ∩
        (Tphi t +ᵥ D.deformedRegion.openCarrier)) := by
      exact (D.deformedRegion.openCarrier_regularOpen.1.vadd (Tphi s)).inter
        (D.deformedRegion.openCarrier_regularOpen.1.vadd (Tphi t))
    obtain ⟨y, hy, hyoff⟩ := exists_offFiniteCoordinateGrid_mem_open V hopen htarget
    have hyoffS : OffVertexCoordinateGrid D.deformedRegion
        (-(Tphi s) + y) := by
      intro v hv
      have hvf : v ∈ D.deformedRegion.vertexFinset := by
        change v ∈ (↑D.deformedRegion.vertexFinset : Set Tiling.Plane)
        simpa only [D.deformedRegion.coe_vertexFinset] using hv
      have hV : (Tphi s) + v ∈ V := by
        exact Finset.mem_union_left Vt (Finset.mem_image.mpr ⟨v, hvf, rfl⟩)
      have hne := hyoff ((Tphi s) + v) hV
      constructor
      · intro heq
        apply hne.1
        change -(Tphi s).re + y.re = v.re at heq
        change y.re = (Tphi s).re + v.re
        linarith
      · intro heq
        apply hne.2
        change -(Tphi s).im + y.im = v.im at heq
        change y.im = (Tphi s).im + v.im
        linarith
    have hyoffT : OffVertexCoordinateGrid D.deformedRegion
        (-(Tphi t) + y) := by
      intro v hv
      have hvf : v ∈ D.deformedRegion.vertexFinset := by
        change v ∈ (↑D.deformedRegion.vertexFinset : Set Tiling.Plane)
        simpa only [D.deformedRegion.coe_vertexFinset] using hv
      have hV : (Tphi t) + v ∈ V := by
        exact Finset.mem_union_right Vs (Finset.mem_image.mpr ⟨v, hvf, rfl⟩)
      have hne := hyoff ((Tphi t) + v) hV
      constructor
      · intro heq
        apply hne.1
        change -(Tphi t).re + y.re = v.re at heq
        change y.re = (Tphi t).re + v.re
        linarith
      · intro heq
        apply hne.2
        change -(Tphi t).im + y.im = v.im at heq
        change y.im = (Tphi t).im + v.im
        linarith
    have hys : -(Tphi s) + y ∈ D.deformedRegion.openCarrier := by
      obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy.1
      rw [← hqy]
      simpa only [vadd_eq_add, neg_add_cancel_left] using hq
    have hyt : -(Tphi t) + y ∈ D.deformedRegion.openCarrier := by
      obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy.2
      rw [← hqy]
      simpa only [vadd_eq_add, neg_add_cancel_left] using hq
    obtain ⟨xp, yp, hxp, hyp, hxpbox, hypbox⟩ :=
      IntrinsicVertices.exists_intrinsicCell_around_offGrid
        D.deformedRegion hys hyoffS
    obtain ⟨xq, yq, hxq, hyq, hxqbox, hyqbox⟩ :=
      IntrinsicVertices.exists_intrinsicCell_around_offGrid
        D.deformedRegion hyt hyoffT
    obtain ⟨av₁, av₂, hav₁, hav₂, hav₁coord, hav₂coord⟩ :=
      consecutivePair_endpoint_vertices D.deformedRegion Axis.horizontal hxp
    obtain ⟨aw₁, aw₂, haw₁, haw₂, haw₁coord, haw₂coord⟩ :=
      consecutivePair_endpoint_vertices D.deformedRegion Axis.horizontal hxq
    obtain ⟨au₁, au₂, hau₁, hau₂, hau₁coord, hau₂coord⟩ :=
      consecutivePair_endpoint_vertices D.deformedRegion Axis.vertical hyp
    obtain ⟨ar₁, ar₂, har₁, har₂, har₁coord, har₂coord⟩ :=
      consecutivePair_endpoint_vertices D.deformedRegion Axis.vertical hyq
    rw [D.vertices_image] at hav₁ hav₂ haw₁ haw₂ hau₁ hau₂ har₁ har₂
    rcases hav₁ with ⟨v₁, hv₁, hav₁eq⟩
    rcases hav₂ with ⟨v₂, hv₂, hav₂eq⟩
    rcases haw₁ with ⟨w₁, hw₁, haw₁eq⟩
    rcases haw₂ with ⟨w₂, hw₂, haw₂eq⟩
    rcases hau₁ with ⟨u₁, hu₁, hau₁eq⟩
    rcases hau₂ with ⟨u₂, hu₂, hau₂eq⟩
    rcases har₁ with ⟨r₁, hr₁, har₁eq⟩
    rcases har₂ with ⟨r₂, hr₂, har₂eq⟩
    obtain ⟨sv₁, sv₂, hsv₁, hsv₂, hsv₁D, hsv₂D, hxpS⟩ :=
      consecutiveLevelPair_reflect_planarHomeomorph D Axis.horizontal hxp
    obtain ⟨sw₁, sw₂, hsw₁, hsw₂, hsw₁D, hsw₂D, hxqS⟩ :=
      consecutiveLevelPair_reflect_planarHomeomorph D Axis.horizontal hxq
    obtain ⟨su₁, su₂, hsu₁, hsu₂, hsu₁D, hsu₂D, hypS⟩ :=
      consecutiveLevelPair_reflect_planarHomeomorph D Axis.vertical hyp
    obtain ⟨sr₁, sr₂, hsr₁, hsr₂, hsr₁D, hsr₂D, hyqS⟩ :=
      consecutiveLevelPair_reflect_planarHomeomorph D Axis.vertical hyq
    have hxpbox1 : (Tphi s).re + xp.1 < y.re := by
      simpa [Complex.add_re, Complex.neg_re] using hxpbox.1
    have hxpbox2 : y.re < (Tphi s).re + xp.2 := by
      simpa [Complex.add_re, Complex.neg_re] using hxpbox.2
    have hxqbox1 : (Tphi t).re + xq.1 < y.re := by
      simpa [Complex.add_re, Complex.neg_re] using hxqbox.1
    have hxqbox2 : y.re < (Tphi t).re + xq.2 := by
      simpa [Complex.add_re, Complex.neg_re] using hxqbox.2
    have hypbox1 : (Tphi s).im + yp.1 < y.im := by
      simpa [Complex.add_im, Complex.neg_im] using hypbox.1
    have hypbox2 : y.im < (Tphi s).im + yp.2 := by
      simpa [Complex.add_im, Complex.neg_im] using hypbox.2
    have hyqbox1 : (Tphi t).im + yq.1 < y.im := by
      simpa [Complex.add_im, Complex.neg_im] using hyqbox.1
    have hyqbox2 : y.im < (Tphi t).im + yq.2 := by
      simpa [Complex.add_im, Complex.neg_im] using hyqbox.2
    have htarget_hleft : Axis.coord Axis.horizontal
        ((Tphi s + D.planarHomeomorph sv₁) -
          (Tphi t + D.planarHomeomorph sw₂)) < 0 := by
      have hsv₁r : (D.planarHomeomorph sv₁).re = xp.1 := by
        simpa [Axis.coord] using hsv₁D
      have hsw₂r : (D.planarHomeomorph sw₂).re = xq.2 := by
        simpa [Axis.coord] using hsw₂D
      simp only [Axis.coord, Complex.sub_re, Complex.add_re]
      linarith [hxpbox1, hxqbox2, hsv₁r, hsw₂r]
    have htarget_hright : Axis.coord Axis.horizontal
        ((Tphi t + D.planarHomeomorph sw₁) -
          (Tphi s + D.planarHomeomorph sv₂)) < 0 := by
      have hsv₂r : (D.planarHomeomorph sv₂).re = xp.2 := by
        simpa [Axis.coord] using hsv₂D
      have hsw₁r : (D.planarHomeomorph sw₁).re = xq.1 := by
        simpa [Axis.coord] using hsw₁D
      simp only [Axis.coord, Complex.sub_re, Complex.add_re]
      linarith [hxpbox2, hxqbox1, hsv₂r, hsw₁r]
    have htarget_hbottom : Axis.coord Axis.vertical
        ((Tphi s + D.planarHomeomorph su₁) -
          (Tphi t + D.planarHomeomorph sr₂)) < 0 := by
      have hsu₁i : (D.planarHomeomorph su₁).im = yp.1 := by
        simpa [Axis.coord] using hsu₁D
      have hsr₂i : (D.planarHomeomorph sr₂).im = yq.2 := by
        simpa [Axis.coord] using hsr₂D
      simp only [Axis.coord, Complex.sub_im, Complex.add_im]
      linarith [hypbox1, hyqbox2, hsu₁i, hsr₂i]
    have htarget_htop : Axis.coord Axis.vertical
        ((Tphi t + D.planarHomeomorph sr₁) -
          (Tphi s + D.planarHomeomorph su₂)) < 0 := by
      have hsu₂i : (D.planarHomeomorph su₂).im = yp.2 := by
        simpa [Axis.coord] using hsu₂D
      have hsr₁i : (D.planarHomeomorph sr₁).im = yq.1 := by
        simpa [Axis.coord] using hsr₁D
      simp only [Axis.coord, Complex.sub_im, Complex.add_im]
      linarith [hypbox2, hyqbox1, hsu₂i, hsr₁i]
    have hsource_hleft := targetEndpoint_orderReflect P hScale phi hphi D Tphi
      hTphi Axis.horizontal s t y hy.1 hy.2 sv₁ sw₂ hsv₁ hsw₂ htarget_hleft
    have hsource_hright := targetEndpoint_orderReflect P hScale phi hphi D Tphi
      hTphi Axis.horizontal t s y hy.2 hy.1 sw₁ sv₂ hsw₁ hsv₂ htarget_hright
    have hsource_hbottom := targetEndpoint_orderReflect P hScale phi hphi D Tphi
      hTphi Axis.vertical s t y hy.1 hy.2 su₁ sr₂ hsu₁ hsr₂ htarget_hbottom
    have hsource_htop := targetEndpoint_orderReflect P hScale phi hphi D Tphi
      hTphi Axis.vertical t s y hy.2 hy.1 sr₁ su₂ hsr₁ hsu₂ htarget_htop
    let us : Tiling.Plane := (D.planarHomeomorph).symm (-(Tphi s) + y)
    let ut : Tiling.Plane := (D.planarHomeomorph).symm (-(Tphi t) + y)
    have hDus : D.planarHomeomorph us = -(Tphi s) + y := by
      simp [us]
    have hDut : D.planarHomeomorph ut = -(Tphi t) + y := by
      simp [ut]
    have hus : us ∈ C.region.openCarrier := by
      rw [D.deformedRegion_openCarrier] at hys
      rcases hys with ⟨q, hq, hqeq⟩
      have heq : us = q := D.planarHomeomorph.injective (by
        rw [hDus]
        exact hqeq.symm)
      simpa [heq] using hq
    have hut : ut ∈ C.region.openCarrier := by
      rw [D.deformedRegion_openCarrier] at hyt
      rcases hyt with ⟨q, hq, hqeq⟩
      have heq : ut = q := D.planarHomeomorph.injective (by
        rw [hDut]
        exact hqeq.symm)
      simpa [heq] using hq
    have husfirst : D.firstHomeomorph us.re = y.re - (Tphi s).re := by
      have h := congrArg Complex.re hDus
      simpa [D.planarHomeomorph_apply, Complex.add_re, Complex.neg_re,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have hussecond : D.secondHomeomorph us.im = y.im - (Tphi s).im := by
      have h := congrArg Complex.im hDus
      simpa [D.planarHomeomorph_apply, Complex.add_im, Complex.neg_im,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have hutfirst : D.firstHomeomorph ut.re = y.re - (Tphi t).re := by
      have h := congrArg Complex.re hDut
      simpa [D.planarHomeomorph_apply, Complex.add_re, Complex.neg_re,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have hutsecond : D.secondHomeomorph ut.im = y.im - (Tphi t).im := by
      have h := congrArg Complex.im hDut
      simpa [D.planarHomeomorph_apply, Complex.add_im, Complex.neg_im,
        sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    have husr : us.re ∈ Ioo (Axis.coord Axis.horizontal sv₁)
        (Axis.coord Axis.horizontal sv₂) := by
      constructor
      · apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
        change D.firstHomeomorph sv₁.re < D.firstHomeomorph us.re
        have hsv₁r : (D.planarHomeomorph sv₁).re = xp.1 := by
          simpa [Axis.coord] using hsv₁D
        have hsv₁f : D.firstHomeomorph sv₁.re = xp.1 := by
          simpa [D.planarHomeomorph_apply, Complex.add_re] using hsv₁r
        have h₁ : D.firstHomeomorph sv₁.re <
            y.re - (Tphi s).re := by linarith [hxpbox1, hsv₁f]
        exact h₁.trans_eq husfirst.symm
      · apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
        change D.firstHomeomorph us.re < D.firstHomeomorph sv₂.re
        have hsv₂r : (D.planarHomeomorph sv₂).re = xp.2 := by
          simpa [Axis.coord] using hsv₂D
        have hsv₂f : D.firstHomeomorph sv₂.re = xp.2 := by
          simpa [D.planarHomeomorph_apply, Complex.add_re] using hsv₂r
        have h₂ : y.re - (Tphi s).re < D.firstHomeomorph sv₂.re := by
          linarith [hxpbox2, hsv₂f]
        exact husfirst ▸ h₂
    have husi : us.im ∈ Ioo (Axis.coord Axis.vertical su₁)
        (Axis.coord Axis.vertical su₂) := by
      constructor
      · apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
        change D.secondHomeomorph su₁.im < D.secondHomeomorph us.im
        have hsu₁i : (D.planarHomeomorph su₁).im = yp.1 := by
          simpa [Axis.coord] using hsu₁D
        have hsu₁f : D.secondHomeomorph su₁.im = yp.1 := by
          simpa [D.planarHomeomorph_apply, Complex.add_im] using hsu₁i
        have h₁ : D.secondHomeomorph su₁.im <
            y.im - (Tphi s).im := by linarith [hypbox1, hsu₁f]
        exact h₁.trans_eq hussecond.symm
      · apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
        change D.secondHomeomorph us.im < D.secondHomeomorph su₂.im
        have hsu₂i : (D.planarHomeomorph su₂).im = yp.2 := by
          simpa [Axis.coord] using hsu₂D
        have hsu₂f : D.secondHomeomorph su₂.im = yp.2 := by
          simpa [D.planarHomeomorph_apply, Complex.add_im] using hsu₂i
        have h₂ : y.im - (Tphi s).im < D.secondHomeomorph su₂.im := by
          linarith [hypbox2, hsu₂f]
        exact hussecond ▸ h₂
    have hutr : ut.re ∈ Ioo (Axis.coord Axis.horizontal sw₁)
        (Axis.coord Axis.horizontal sw₂) := by
      constructor
      · apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
        change D.firstHomeomorph sw₁.re < D.firstHomeomorph ut.re
        have hsw₁r : (D.planarHomeomorph sw₁).re = xq.1 := by
          simpa [Axis.coord] using hsw₁D
        have hsw₁f : D.firstHomeomorph sw₁.re = xq.1 := by
          simpa [D.planarHomeomorph_apply, Complex.add_re] using hsw₁r
        have h₁ : D.firstHomeomorph sw₁.re <
            y.re - (Tphi t).re := by linarith [hxqbox1, hsw₁f]
        exact h₁.trans_eq hutfirst.symm
      · apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
        change D.firstHomeomorph ut.re < D.firstHomeomorph sw₂.re
        have hsw₂r : (D.planarHomeomorph sw₂).re = xq.2 := by
          simpa [Axis.coord] using hsw₂D
        have hsw₂f : D.firstHomeomorph sw₂.re = xq.2 := by
          simpa [D.planarHomeomorph_apply, Complex.add_re] using hsw₂r
        have h₂ : y.re - (Tphi t).re < D.firstHomeomorph sw₂.re := by
          linarith [hxqbox2, hsw₂f]
        exact hutfirst ▸ h₂
    have huti : ut.im ∈ Ioo (Axis.coord Axis.vertical sr₁)
        (Axis.coord Axis.vertical sr₂) := by
      constructor
      · apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
        change D.secondHomeomorph sr₁.im < D.secondHomeomorph ut.im
        have hsr₁i : (D.planarHomeomorph sr₁).im = yq.1 := by
          simpa [Axis.coord] using hsr₁D
        have hsr₁f : D.secondHomeomorph sr₁.im = yq.1 := by
          simpa [D.planarHomeomorph_apply, Complex.add_im] using hsr₁i
        have h₁ : D.secondHomeomorph sr₁.im <
            y.im - (Tphi t).im := by linarith [hyqbox1, hsr₁f]
        exact h₁.trans_eq hutsecond.symm
      · apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
        change D.secondHomeomorph ut.im < D.secondHomeomorph sr₂.im
        have hsr₂i : (D.planarHomeomorph sr₂).im = yq.2 := by
          simpa [Axis.coord] using hsr₂D
        have hsr₂f : D.secondHomeomorph sr₂.im = yq.2 := by
          simpa [D.planarHomeomorph_apply, Complex.add_im] using hsr₂i
        have h₂ : y.im - (Tphi t).im < D.secondHomeomorph sr₂.im := by
          linarith [hyqbox2, hsr₂f]
        exact hutsecond ▸ h₂
    have hxpSorder : Axis.coord Axis.horizontal sv₁ <
        Axis.coord Axis.horizontal sv₂ := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hxpS
      exact hxpS.2.1
    have hxqSorder : Axis.coord Axis.horizontal sw₁ <
        Axis.coord Axis.horizontal sw₂ := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hxqS
      exact hxqS.2.1
    have hypSorder : Axis.coord Axis.vertical su₁ <
        Axis.coord Axis.vertical su₂ := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hypS
      exact hypS.2.1
    have hyqSorder : Axis.coord Axis.vertical sr₁ <
        Axis.coord Axis.vertical sr₂ := by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hyqS
      exact hyqS.2.1
    have hsxorder : (s + sv₁).re < (s + sv₂).re := by
      simp only [Complex.add_re]
      simpa [Axis.coord] using hxpSorder
    have htxorder : (t + sw₁).re < (t + sw₂).re := by
      simp only [Complex.add_re]
      simpa [Axis.coord] using hxqSorder
    have hsyorder : (s + su₁).im < (s + su₂).im := by
      simp only [Complex.add_im]
      simpa [Axis.coord] using hypSorder
    have htyorder : (t + sr₁).im < (t + sr₂).im := by
      simp only [Complex.add_im]
      simpa [Axis.coord] using hyqSorder
    have hsleft : (s + sv₁).re < (t + sw₂).re := by
      simp only [Complex.add_re]
      have h := hsource_hleft
      simp only [Axis.coord, Complex.sub_re, Complex.add_re] at h
      linarith
    have hsright : (t + sw₁).re < (s + sv₂).re := by
      simp only [Complex.add_re]
      have h := hsource_hright
      simp only [Axis.coord, Complex.sub_re, Complex.add_re] at h
      linarith
    have hsbottom : (s + su₁).im < (t + sr₂).im := by
      simp only [Complex.add_im]
      have h := hsource_hbottom
      simp only [Axis.coord, Complex.sub_im, Complex.add_im] at h
      linarith
    have hstop : (t + sr₁).im < (s + su₂).im := by
      simp only [Complex.add_im]
      have h := hsource_htop
      simp only [Axis.coord, Complex.sub_im, Complex.add_im] at h
      linarith
    have hsourceRect : (interior (closedAxisBox
        (s + sv₁).re (s + sv₂).re (s + su₁).im (s + su₂).im) ∩
        interior (closedAxisBox
        (t + sw₁).re (t + sw₂).re (t + sr₁).im (t + sr₂).im)).Nonempty := by
      rw [interior_closedAxisBox_inter_iff hsxorder hsyorder
        htxorder htyorder]
      constructor
      · rw [lt_min_iff]
        exact ⟨(max_lt_iff.mpr ⟨hsxorder, hsright⟩),
          (max_lt_iff.mpr ⟨hsleft, htxorder⟩)⟩
      · rw [lt_min_iff]
        exact ⟨(max_lt_iff.mpr ⟨hsyorder, hstop⟩),
          (max_lt_iff.mpr ⟨hsbottom, htyorder⟩)⟩
    obtain ⟨x, hxs, hxt⟩ := hsourceRect
    rw [interior_closedAxisBox_local] at hxs hxt
    have hxsr : (-(s : Tiling.Plane) + x).re ∈
        Ioo (Axis.coord Axis.horizontal sv₁) (Axis.coord Axis.horizontal sv₂) := by
      constructor
      · simp only [Axis.coord, Complex.add_re, Complex.neg_re]
        have h := hxs.1.1
        simp only [Complex.add_re] at h
        linarith
      · simp only [Axis.coord, Complex.add_re, Complex.neg_re]
        have h := hxs.1.2
        simp only [Complex.add_re] at h
        linarith
    have hxsi : (-(s : Tiling.Plane) + x).im ∈
        Ioo (Axis.coord Axis.vertical su₁) (Axis.coord Axis.vertical su₂) := by
      constructor
      · simp only [Axis.coord, Complex.add_im, Complex.neg_im]
        have h := hxs.2.1
        simp only [Complex.add_im] at h
        linarith
      · simp only [Axis.coord, Complex.add_im, Complex.neg_im]
        have h := hxs.2.2
        simp only [Complex.add_im] at h
        linarith
    have hxtr : (-(t : Tiling.Plane) + x).re ∈
        Ioo (Axis.coord Axis.horizontal sw₁) (Axis.coord Axis.horizontal sw₂) := by
      constructor
      · simp only [Axis.coord, Complex.add_re, Complex.neg_re]
        have h := hxt.1.1
        simp only [Complex.add_re] at h
        linarith
      · simp only [Axis.coord, Complex.add_re, Complex.neg_re]
        have h := hxt.1.2
        simp only [Complex.add_re] at h
        linarith
    have hxti : (-(t : Tiling.Plane) + x).im ∈
        Ioo (Axis.coord Axis.vertical sr₁) (Axis.coord Axis.vertical sr₂) := by
      constructor
      · simp only [Axis.coord, Complex.add_im, Complex.neg_im]
        have h := hxt.2.1
        simp only [Complex.add_im] at h
        linarith
      · simp only [Axis.coord, Complex.add_im, Complex.neg_im]
        have h := hxt.2.2
        simp only [Complex.add_im] at h
        linarith
    have hus' : -(s : Tiling.Plane) + ((s : Tiling.Plane) + us) ∈
        C.region.openCarrier := by simpa using hus
    have hut' : -(t : Tiling.Plane) + ((t : Tiling.Plane) + ut) ∈
        C.region.openCarrier := by simpa using hut
    have husr' : (-(s : Tiling.Plane) + ((s : Tiling.Plane) + us)).re ∈
        Ioo (Axis.coord Axis.horizontal sv₁) (Axis.coord Axis.horizontal sv₂) := by
      simpa using husr
    have husi' : (-(s : Tiling.Plane) + ((s : Tiling.Plane) + us)).im ∈
        Ioo (Axis.coord Axis.vertical su₁) (Axis.coord Axis.vertical su₂) := by
      simpa using husi
    have hutr' : (-(t : Tiling.Plane) + ((t : Tiling.Plane) + ut)).re ∈
        Ioo (Axis.coord Axis.horizontal sw₁) (Axis.coord Axis.horizontal sw₂) := by
      simpa using hutr
    have huti' : (-(t : Tiling.Plane) + ((t : Tiling.Plane) + ut)).im ∈
        Ioo (Axis.coord Axis.vertical sr₁) (Axis.coord Axis.vertical sr₂) := by
      simpa using huti
    have hxsopen := sourceCell_mem_of_rectangle (z := (s : Tiling.Plane) + us)
      (x := x) hxpS hypS hus' husr' husi' hxsr hxsi
    have hxtopen := sourceCell_mem_of_rectangle (z := (t : Tiling.Plane) + ut)
      (x := x) hxqS hyqS hut' hutr' huti' hxtr hxti
    exact ⟨x, hxsopen, hxtopen⟩

private theorem selectedSubfamily_packingTransport :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres),
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Set.image Subtype.val S)) →
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S)) := by
  intro C P hScale phi hphi D Tphi hTphi S hpacking
  apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
    D.deformedRegion (deformedCenterCarrierOn Tphi S)).2
  intro a ha b hb hab
  rw [deformedCenterCarrierOn] at ha hb
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  have hst : (s : Tiling.Plane) ≠ (t : Tiling.Plane) := by
    intro hst
    apply hab
    exact congrArg Tphi (Subtype.ext hst)
  have hsource :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint C.region
      (Set.image Subtype.val S)).mp hpacking
      ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ hst
  apply Set.disjoint_left.2
  intro z hzA hzB
  obtain ⟨w, hwA, hwB⟩ :=
    (openTileOverlapTransport P hScale phi hphi D Tphi hTphi s t).mpr
      ⟨z, hzA, hzB⟩
  exact (Set.disjoint_left.1 hsource) hwA hwB

private theorem selectedSubfamily_sourcePacking
    {C : ApproximationContext} (P : FLCControlPackage C)
    (S : Set ↥C.centres) :
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Set.image Subtype.val S)) := by
  apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint C.region
    (Set.image Subtype.val S)).2
  intro a ha b hb hab
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint C.region
    C.centres).mp P.source_tilesOn.2.1 s.2 t.2 hab

private theorem centerColumn_fullSections :
  ∀ (axis : Axis) (K : Region) (S : Set Tiling.Plane),
    IsCenterColumn axis K S → FullAxisSections axis K S := by
  intro axis K S hC c
  obtain ⟨c₀, _hS, _hcoord, hsupp⟩ :=
    Tiling.AxisParallel.centerColumn_regularSupport hC
  rw [hsupp]
  cases axis with
  | horizontal =>
      by_cases hc : c ∈ interior (closure (c₀ +ᵥ (Complex.im '' K.openCarrier)))
      · left
        ext x
        constructor
        · intro _
          trivial
        · intro _
          refine ⟨(x : ℂ) + (c : ℂ) * Complex.I, ?_, ?_⟩
          · exact ⟨by simpa [Axis.transverseCoord] using hc, by
              simp [Axis.transverseCoord]⟩
          · simp [Axis.coord]
      · right
        ext x
        constructor
        · intro hx
          obtain ⟨z, hz, _hzx⟩ := hx
          exact (hc (by
            rw [← hz.2]
            simpa [Axis.transverseCoord] using hz.1)).elim
        · simp
  | vertical =>
      by_cases hc : c ∈ interior (closure (c₀ +ᵥ (Complex.re '' K.openCarrier)))
      · left
        ext y
        constructor
        · intro _
          trivial
        · intro _
          refine ⟨(c : ℂ) + (y : ℂ) * Complex.I, ?_, ?_⟩
          · exact ⟨by simpa [Axis.transverseCoord] using hc, by
              simp [Axis.transverseCoord]⟩
          · simp [Axis.coord]
      · right
        ext y
        constructor
        · intro hy
          obtain ⟨z, hz, _hzy⟩ := hy
          exact (hc (by
            rw [← hz.2]
            simpa [Axis.transverseCoord] using hz.1)).elim
        · intro hy
          have hfalse : False := by simp at hy
          exact hfalse.elim


open Tiling AxisParallel Approximation
open Tiling.AxisParallel.IntrinsicVertices
open Tiling.AxisParallel.Foundations.GenericSlices

open Tiling.AxisParallel
open Tiling.AxisParallel.Foundations.GenericSlices

open Tiling.AxisParallel.Foundations.FilledSliceChains

private theorem generic_slice_raw_ae_of_full
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {c : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hgeneric : ∀ t ∈ S, c ∉ axis.transverseCoord t +ᵥ
      (axis.transverseCoord '' K.vertices))
    (hfull : axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = Set.univ) :
    {x : ℝ | slicePoint axis c x ∈ openUnion K S} =ᵐ[volume]
      Set.univ := by
  let P := K.polygonalProtoTiling S
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hst)
  have hloc : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.support) := by
    exact (P.locallyFinite_placedTile hpacking).comp_injective htoPlacement
  have hlocOpen : LocallyFinite (fun s : S ↦
      (s : Tiling.Plane) +ᵥ K.openCarrier) := by
    exact hloc.subset fun s ↦ vadd_set_mono interior_subset
  have hS : S.Countable := (IsPacking.locallyFinite_centres hpacking).2
  have hV : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable S := hS.to_subtype
  let _ : Countable ↥K.vertices := hV.to_subtype
  let A : Set ℝ := Set.range (fun p : S × ↥K.vertices ↦
    axis.coord ((p.1 : Tiling.Plane) + p.2.1))
  have hAcount : A.Countable := Set.countable_range _
  have hbad : {x : ℝ | slicePoint axis c x ∉
      openUnion K S} ⊆ A := by
    intro x hx
    have hmem : axis.coord (slicePoint axis c x) ∈
        axis.coord '' (regularSupport K S ∩
          {z | axis.transverseCoord z = c}) := by
      rw [hfull]
      exact Set.mem_univ _
    obtain ⟨z, hz, hzx⟩ := hmem
    have hzc : axis.transverseCoord z = c := hz.2
    have hzeq : z = slicePoint axis c x := by
      have hsliceCoord : axis.coord
          (slicePoint axis c x) = x := by
        cases axis <;> simp [slicePoint, Axis.coord]
      have hsliceTrans : axis.transverseCoord
          (slicePoint axis c x) = c := by
        cases axis <;> simp [slicePoint,
          Axis.transverseCoord]
      apply axis_eq_of_coords axis
      · exact hzx
      · exact hzc.trans hsliceTrans.symm
    have hzreg : slicePoint axis c x ∈ regularSupport K S :=
      hzeq ▸ hz.1
    have hzcl : slicePoint axis c x ∈ closure (openUnion K S) :=
      interior_subset hzreg
    have hzfront : slicePoint axis c x ∈ frontier (openUnion K S) := by
      have hopen : IsOpen (openUnion K S) := isOpen_iUnion fun s : S ↦
        (Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
      rw [frontier, hopen.interior_eq]
      exact ⟨hzcl, hx⟩
    have hfrontUnion : frontier (openUnion K S) ⊆
        ⋃ s : S, frontier ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
      rw [openUnion]
      exact frontier_iUnion_subset_iUnion_frontier hlocOpen
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp (hfrontUnion hzfront)
    have hfrontEq : frontier ((s : Tiling.Plane) +ᵥ K.openCarrier) =
        (s : Tiling.Plane) +ᵥ frontier K.openCarrier := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [mem_vadd_set_iff_neg_vadd_mem, Set.mem_sdiff]
      rfl
    have hfrontOpen : slicePoint axis c x ∈
        (s : Tiling.Plane) +ᵥ frontier K.openCarrier :=
      hfrontEq ▸ hzs
    have hfrontSupport : slicePoint axis c x - (s : Tiling.Plane) ∈
        frontier K.support := by
      rw [mem_vadd_set_iff_neg_vadd_mem] at hfrontOpen
      simpa [Region.frontier_openCarrier_eq_frontier_support K,
        sub_eq_add_neg, add_comm] using hfrontOpen
    cases axis with
    | horizontal =>
        rcases IntrinsicVertices.frontier_subset_vertexCoordinateGrid K
          hfrontSupport with hcoord | htrans
        · obtain ⟨v, hv, hcoord⟩ := hcoord
          refine ⟨⟨s, ⟨v, hv⟩⟩, ?_⟩
          change (s : Tiling.Plane).re + v.re = x
          simp [slicePoint] at hcoord
          linarith
        · exfalso
          rcases htrans with ⟨v, hv, htrans⟩
          apply hgeneric s s.2
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          refine ⟨v, hv, ?_⟩
          simp [slicePoint] at htrans
          simpa [Axis.transverseCoord, sub_eq_add_neg, add_comm] using htrans.symm
    | vertical =>
        rcases IntrinsicVertices.frontier_subset_vertexCoordinateGrid K
          hfrontSupport with hcoord | htrans
        · exfalso
          rcases hcoord with ⟨v, hv, hcoord⟩
          apply hgeneric s s.2
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          refine ⟨v, hv, ?_⟩
          simp [slicePoint] at hcoord
          simpa [Axis.transverseCoord, sub_eq_add_neg, add_comm] using hcoord.symm
        · obtain ⟨v, hv, htrans⟩ := htrans
          refine ⟨⟨s, ⟨v, hv⟩⟩, ?_⟩
          change (s : Tiling.Plane).im + v.im = x
          simp [slicePoint] at htrans
          linarith
  filter_upwards [hAcount.ae_notMem (μ := volume)] with x hxA
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    by_contra hnot
    exact False.elim (hxA (hbad hnot))

private theorem endpoint_min_above
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hunbdd : ¬ BddAbove E) (a : E) :
    ∃ z : E, (a : ℝ) < z ∧ ∀ w : E, (a : ℝ) < w → (z : ℝ) ≤ w := by
  classical
  obtain ⟨b, hbE, hab⟩ := not_bddAbove_iff.mp hunbdd (a : ℝ)
  let F : Set ℝ := E ∩ Icc (a : ℝ) b ∩ Ioi (a : ℝ)
  have hF : F.Finite :=
    (hlocal (Icc (a : ℝ) b) (Metric.isBounded_Icc _ _)).inter_of_left _
  let fs : Finset ℝ := hF.toFinset
  have hbfs : b ∈ fs := by
    simp only [fs, Finite.mem_toFinset, F, mem_inter_iff, mem_Icc, mem_Ioi]
    exact ⟨⟨hbE, ⟨hab.le, le_rfl⟩⟩, hab⟩
  let z : ℝ := fs.min' ⟨b, hbfs⟩
  have hzfs : z ∈ fs := Finset.min'_mem fs ⟨b, hbfs⟩
  have hzF : z ∈ F := by simpa only [fs, Finite.mem_toFinset] using hzfs
  have hzE : z ∈ E := hzF.1.1
  have haz : (a : ℝ) < z := hzF.2
  refine ⟨⟨z, hzE⟩, haz, ?_⟩
  intro w hw
  change z ≤ (w : ℝ)
  by_cases hwb : (w : ℝ) ≤ b
  · have hwfs : (w : ℝ) ∈ fs := by
      simp only [fs, Finite.mem_toFinset, F, mem_inter_iff, mem_Icc, mem_Ioi]
      exact ⟨⟨w.2, ⟨hw.le, hwb⟩⟩, hw⟩
    simpa [z] using (Finset.min'_le fs (w : ℝ) hwfs)
  · exact le_trans (by simpa [z] using (Finset.min'_le fs b hbfs)
      ) (le_of_not_ge hwb)

private theorem endpoint_max_below
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hunbdd : ¬ BddBelow E) (a : E) :
    ∃ z : E, (z : ℝ) < a ∧ ∀ w : E, w < (a : ℝ) → w ≤ z := by
  classical
  obtain ⟨b, hbE, hba⟩ := not_bddBelow_iff.mp hunbdd (a : ℝ)
  let F : Set ℝ := E ∩ Icc b (a : ℝ) ∩ Iio (a : ℝ)
  have hF : F.Finite :=
    (hlocal (Icc b (a : ℝ)) (Metric.isBounded_Icc _ _)).inter_of_left _
  let fs : Finset ℝ := hF.toFinset
  have hbf : b ∈ fs := by
    simp only [fs, Finite.mem_toFinset, F, mem_inter_iff, mem_Icc, mem_Iio]
    exact ⟨⟨hbE, ⟨le_rfl, hba.le⟩⟩, hba⟩
  let z : ℝ := fs.max' ⟨b, hbf⟩
  have hzfs : z ∈ fs := Finset.max'_mem fs ⟨b, hbf⟩
  have hzF : z ∈ F := by simpa only [fs, Finite.mem_toFinset] using hzfs
  have hzE : z ∈ E := hzF.1.1
  have hza : z < (a : ℝ) := hzF.2
  refine ⟨⟨z, hzE⟩, hza, ?_⟩
  intro w hw
  change (w : ℝ) ≤ z
  by_cases hbw : b ≤ (w : ℝ)
  · have hwfs : (w : ℝ) ∈ fs := by
      simp only [fs, Finite.mem_toFinset, F, mem_inter_iff, mem_Icc, mem_Iio]
      exact ⟨⟨w.2, ⟨hbw, hw.le⟩⟩, hw⟩
    simpa [z] using (Finset.le_max' fs (w : ℝ) hwfs)
  · exact le_trans (le_of_not_ge hbw)
      (by simpa [z] using (Finset.le_max' fs b hbf))

private theorem endpoint_subtype_Icc_finite
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (a b : E) : (Set.Icc a b).Finite := by
  refine Set.Finite.of_injOn (s := Set.Icc a b)
    (t := E ∩ Set.Icc (a : ℝ) b) (f := fun x : E => (x : ℝ)) ?_ ?_ ?_
  · intro x hx
    exact ⟨x.2, hx.1, hx.2⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · exact hlocal (Icc (a : ℝ) b) (Metric.isBounded_Icc _ _)

set_option linter.style.haveILetI false in
private theorem endpoint_orderIso_int
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hunbddAbove : ¬ BddAbove E) (hunbddBelow : ¬ BddBelow E) :
    Nonempty (E ≃o ℤ) := by
  classical
  let locfin : LocallyFiniteOrder E := LocallyFiniteOrder.ofFiniteIcc
    (fun a b => endpoint_subtype_Icc_finite hlocal a b)
  let succ : SuccOrder E := @LinearLocallyFiniteOrder.succOrder E _ locfin
  let pred : PredOrder E := @LinearLocallyFiniteOrder.predOrder E _ locfin
  let arch : @IsSuccArchimedean E _ succ := by
    letI := locfin
    letI := succ
    infer_instance
  let nmax : NoMaxOrder E :=
    ⟨fun a => ⟨(endpoint_min_above hlocal hunbddAbove a).choose,
      (endpoint_min_above hlocal hunbddAbove a).choose_spec.1⟩⟩
  let nmin : NoMinOrder E :=
    ⟨fun a => ⟨(endpoint_max_below hlocal hunbddBelow a).choose,
      (endpoint_max_below hlocal hunbddBelow a).choose_spec.1⟩⟩
  obtain ⟨w, hwE, hw⟩ := not_bddAbove_iff.mp hunbddAbove (0 : ℝ)
  exact ⟨@orderIsoIntOfLinearSuccPredArch E _ succ pred arch nmax nmin
    ⟨⟨w, hwE⟩⟩⟩

private theorem labelledFibreChain_fixed
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ)
    (hsupport : axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = q}) = Set.univ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (sliceEndpointSet K S axis q ∩ Q).Finite)
    (hunbddAbove : ¬ BddAbove (sliceEndpointSet K S axis q))
    (hunbddBelow : ¬ BddBelow (sliceEndpointSet K S axis q)) :
    Nonempty (LabelledFibreChain axis K S q) := by
  classical
  let E : Set ℝ := sliceEndpointSet K S axis q
  obtain ⟨e⟩ := endpoint_orderIso_int hlocal hunbddAbove hunbddBelow
  let endpoint : ℤ → ℝ := fun j => ((e.symm j : E) : ℝ)
  have hendpoint_mem (j : ℤ) : endpoint j ∈ E := (e.symm j : E).property
  have hendpoint_strict (j : ℤ) : endpoint j < endpoint (j + 1) := by
    exact_mod_cast e.symm.strictMono (by omega : j < j + 1)
  have hnone (j : ℤ) : Disjoint E (Ioo (endpoint j) (endpoint (j + 1))) := by
    rw [Set.disjoint_left]
    intro z hzE hzI
    have hzI' : (e.symm j : E) < (⟨z, hzE⟩ : E) ∧
        (⟨z, hzE⟩ : E) < e.symm (j + 1) := by
      exact ⟨by exact_mod_cast hzI.1, by exact_mod_cast hzI.2⟩
    have hjk : j < e ⟨z, hzE⟩ :=
      (e.symm.lt_iff_lt).mp (by simpa using hzI'.1)
    have hkj : e ⟨z, hzE⟩ < j + 1 :=
      (e.symm.lt_iff_lt).mp (by simpa using hzI'.2)
    omega
  have hgapData (j : ℤ) : ∃ t : S,
      axisInterval axis q (endpoint j) (endpoint (j + 1)) ⊆
        (t : Tiling.Plane) +ᵥ K.openCarrier := by
    obtain ⟨t, v, w, hv, hw, hvl, hwr, hpositive, hinc⟩ :=
      filledGap_of_local_ae hpacking hq
        (by
          filter_upwards [hfull] with y hy
          intro hyI
          change ({x : ℝ | slicePoint axis q x ∈ openUnion K S} : Set ℝ) y
          exact hy ▸ trivial)
        (hendpoint_mem j) (hendpoint_mem (j + 1))
        (hendpoint_strict j) (hnone j)
    exact ⟨t, hinc⟩
  let owner : ℤ → S := fun j => (hgapData j).choose
  have howner_mem (j : ℤ) : (owner j : Tiling.Plane) ∈ S := (owner j).property
  have hgap (j : ℤ) :
      {z : Tiling.Plane | axis.transverseCoord z = q ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        (owner j : Tiling.Plane) +ᵥ K.openCarrier := by
    cases axis <;> simpa [axisInterval, Axis.coord, Axis.transverseCoord, owner]
      using (hgapData j).choose_spec
  have htendstoTop : Filter.Tendsto endpoint Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    obtain ⟨w, hwE, hbw⟩ := not_bddAbove_iff.mp hunbddAbove b
    let k : ℤ := e ⟨w, hwE⟩
    refine ⟨k, ?_⟩
    intro j hj
    have hkj : e ⟨w, hwE⟩ ≤ j := by simpa [k] using hj
    have hle : (⟨w, hwE⟩ : E) ≤ e.symm j :=
      (e.le_iff_le).mp (by simpa using hkj)
    exact hbw.le.trans (by exact_mod_cast hle)
  have htendstoBot : Filter.Tendsto endpoint Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    obtain ⟨w, hwE, hwb⟩ := not_bddBelow_iff.mp hunbddBelow b
    let k : ℤ := e ⟨w, hwE⟩
    refine ⟨k, ?_⟩
    intro j hj
    have hkj : j ≤ e ⟨w, hwE⟩ := by simpa [k] using hj
    have hle : e.symm j ≤ (⟨w, hwE⟩ : E) :=
      (e.le_iff_le).mp (by simpa using hkj)
    have hle' : endpoint j ≤ (w : ℝ) := by exact_mod_cast hle
    exact hle'.trans hwb.le
  refine ⟨⟨endpoint, fun j => (owner j : Tiling.Plane), howner_mem,
    ?_, htendstoTop, htendstoBot, hgap, ?_⟩⟩
  · intro a b hab
    exact_mod_cast e.symm.strictMono hab
  · simpa [E] using hsupport

private structure WitnessedLabelledFibreChain (axis : Axis) (K : Region)
    (S : Set Tiling.Plane) (c : ℝ) where
  chain : LabelledFibreChain axis K S c
  endpoint_mem : ∀ j, chain.endpoint j ∈ sliceEndpointSet K S axis c
  gap_witness : ∀ j, ∃ t : S, ∃ v w : Tiling.Plane,
    v ∈ K.vertices ∧ w ∈ K.vertices ∧
      chain.endpoint j = axis.coord (v + (t : Tiling.Plane)) ∧
      chain.endpoint (j + 1) = axis.coord (w + (t : Tiling.Plane)) ∧
      0 < axis.coord (w - v) ∧
      axisInterval axis c (chain.endpoint j) (chain.endpoint (j + 1)) ⊆
        (t : Tiling.Plane) +ᵥ K.openCarrier

private theorem labelledFibreChain_fixed_witnessed
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ)
    (hsupport : axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = q}) = Set.univ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (sliceEndpointSet K S axis q ∩ Q).Finite)
    (hunbddAbove : ¬ BddAbove (sliceEndpointSet K S axis q))
    (hunbddBelow : ¬ BddBelow (sliceEndpointSet K S axis q)) :
    Nonempty (WitnessedLabelledFibreChain axis K S q) := by
  classical
  let E : Set ℝ := sliceEndpointSet K S axis q
  obtain ⟨e⟩ := endpoint_orderIso_int hlocal hunbddAbove hunbddBelow
  let endpoint : ℤ → ℝ := fun j => ((e.symm j : E) : ℝ)
  have hendpoint_mem (j : ℤ) : endpoint j ∈ E := (e.symm j : E).property
  have hendpoint_strict (j : ℤ) : endpoint j < endpoint (j + 1) := by
    exact_mod_cast e.symm.strictMono (by omega : j < j + 1)
  have hnone (j : ℤ) : Disjoint E (Ioo (endpoint j) (endpoint (j + 1))) := by
    rw [Set.disjoint_left]
    intro z hzE hzI
    have hzI' : (e.symm j : E) < (⟨z, hzE⟩ : E) ∧
        (⟨z, hzE⟩ : E) < e.symm (j + 1) := by
      exact ⟨by exact_mod_cast hzI.1, by exact_mod_cast hzI.2⟩
    have hjk : j < e ⟨z, hzE⟩ :=
      (e.symm.lt_iff_lt).mp (by simpa using hzI'.1)
    have hkj : e ⟨z, hzE⟩ < j + 1 :=
      (e.symm.lt_iff_lt).mp (by simpa using hzI'.2)
    omega
  have hgapData (j : ℤ) : ∃ t : S, ∃ v w : Tiling.Plane,
      v ∈ K.vertices ∧ w ∈ K.vertices ∧
      endpoint j = axis.coord (v + (t : Tiling.Plane)) ∧
      endpoint (j + 1) = axis.coord (w + (t : Tiling.Plane)) ∧
      0 < axis.coord (w - v) ∧
      axisInterval axis q (endpoint j) (endpoint (j + 1)) ⊆
        (t : Tiling.Plane) +ᵥ K.openCarrier := by
    obtain ⟨t, v, w, hv, hw, hvl, hwr, hpositive, hinc⟩ :=
      filledGap_of_local_ae hpacking hq
        (by
          filter_upwards [hfull] with y hy
          intro hyI
          change ({x : ℝ | slicePoint axis q x ∈ openUnion K S} : Set ℝ) y
          exact hy ▸ trivial)
        (hendpoint_mem j) (hendpoint_mem (j + 1))
        (hendpoint_strict j) (hnone j)
    exact ⟨t, v, w, hv, hw, hvl, hwr, hpositive, hinc⟩
  let owner : ℤ → S := fun j => (hgapData j).choose
  have howner_mem (j : ℤ) : (owner j : Tiling.Plane) ∈ S := (owner j).property
  have hgap (j : ℤ) :
      {z : Tiling.Plane | axis.transverseCoord z = q ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        (owner j : Tiling.Plane) +ᵥ K.openCarrier := by
    obtain ⟨v, w, hv, hw, hvl, hwr, hpositive, hinc⟩ :=
      (hgapData j).choose_spec
    cases axis <;> simpa [axisInterval, Axis.coord, Axis.transverseCoord, owner]
      using hinc
  have htendstoTop : Filter.Tendsto endpoint Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    obtain ⟨w, hwE, hbw⟩ := not_bddAbove_iff.mp hunbddAbove b
    let k : ℤ := e ⟨w, hwE⟩
    refine ⟨k, ?_⟩
    intro j hj
    have hkj : e ⟨w, hwE⟩ ≤ j := by simpa [k] using hj
    have hle : (⟨w, hwE⟩ : E) ≤ e.symm j :=
      (e.le_iff_le).mp (by simpa using hkj)
    exact hbw.le.trans (by exact_mod_cast hle)
  have htendstoBot : Filter.Tendsto endpoint Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    obtain ⟨w, hwE, hwb⟩ := not_bddBelow_iff.mp hunbddBelow b
    let k : ℤ := e ⟨w, hwE⟩
    refine ⟨k, ?_⟩
    intro j hj
    have hkj : j ≤ e ⟨w, hwE⟩ := by simpa [k] using hj
    have hle : e.symm j ≤ (⟨w, hwE⟩ : E) :=
      (e.le_iff_le).mp (by simpa using hkj)
    have hle' : endpoint j ≤ (w : ℝ) := by exact_mod_cast hle
    exact hle'.trans hwb.le
  refine ⟨⟨⟨endpoint, fun j => (owner j : Tiling.Plane), howner_mem,
    ?_, htendstoTop, htendstoBot, hgap, ?_⟩, ?_, ?_⟩⟩
  · intro a b hab
    exact_mod_cast e.symm.strictMono hab
  · simpa [E] using hsupport
  · intro j
    exact hendpoint_mem j
  · intro j
    simpa [endpoint] using hgapData j

private theorem endpoint_witness_of_mem
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hq : q ∉ translatedVertexLevels K S axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈ openUnion K S} =ᵐ[volume] univ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (sliceEndpointSet K S axis q ∩ Q).Finite)
    (hunbddAbove : ¬ BddAbove (sliceEndpointSet K S axis q))
    {x : ℝ} (hx : x ∈ sliceEndpointSet K S axis q) :
    ∃ t : S, ∃ v : K.vertices,
      x = axis.coord (v.1 + (t : Tiling.Plane)) := by
  obtain ⟨r, hr, hxr⟩ := not_bddAbove_iff.mp hunbddAbove x
  obtain ⟨n, hn, xs, owner, hxs, hxe, hchain, hnodes⟩ :=
    genericSliceChain_betweenEndpoints_fixed_of_local_ae hpacking hq hx hr hxr (by
      filter_upwards [hfull] with y hy
      intro _hyI
      exact hy.mpr (Set.mem_univ y))
  let i : Fin n := ⟨0, hn⟩
  have hfilled := hchain.2 i
  rcases hfilled with ⟨v, w, hv, hw, hxv, hxw, hpositive, hinc⟩
  refine ⟨owner i, ⟨v, hv⟩, ?_⟩
  calc
    x = xs 0 := hxs.symm
    _ = xs i.castSucc := by simp [i]
    _ = axis.coord ((⟨v, hv⟩ : K.vertices).1 + (owner i).1) := hxv

private theorem endpointWitness_dist_le_vertex
    {axis : Axis} {s t v w : Tiling.Plane}
    (htrans : axis.transverseCoord s = axis.transverseCoord t)
    (hcoord : axis.coord (v + s) = axis.coord (w + t)) :
    dist (v + s) (w + t) ≤ dist v w := by
  cases axis with
  | horizontal =>
      have htrans' : s.im = t.im := by
        simpa [Axis.transverseCoord] using htrans
      have hre : (v + s - (w + t)).re = 0 := by
        simpa [Axis.coord, Complex.sub_re] using sub_eq_zero.mpr hcoord
      have him : (v + s - (w + t)).im = (v - w).im := by
        simp only [Complex.sub_im, Complex.add_im]
        linarith
      rw [dist_eq_norm, dist_eq_norm]
      rw [Complex.norm_def, Complex.norm_def]
      simp only [Complex.normSq_apply]
      apply Real.sqrt_le_sqrt
      rw [hre, him]
      nlinarith [sq_nonneg (v - w).re]
  | vertical =>
      have htrans' : s.re = t.re := by
        simpa [Axis.transverseCoord] using htrans
      have him : (v + s - (w + t)).im = 0 := by
        simpa [Axis.coord, Complex.sub_im] using sub_eq_zero.mpr hcoord
      have hre : (v + s - (w + t)).re = (v - w).re := by
        simp only [Complex.sub_re, Complex.add_re]
        linarith
      rw [dist_eq_norm, dist_eq_norm]
      rw [Complex.norm_def, Complex.norm_def]
      simp only [Complex.normSq_apply]
      apply Real.sqrt_le_sqrt
      rw [him, hre]
      nlinarith [sq_nonneg (v - w).im]

private theorem endpointWitness_target_coord_eq
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres) (v w : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices)
    (htrans : axis.transverseCoord (s : Tiling.Plane) =
      axis.transverseCoord (t : Tiling.Plane))
    (hcoord : axis.coord (v + (s : Tiling.Plane)) =
      axis.coord (w + (t : Tiling.Plane))) :
    axis.coord (Tphi s + D.planarHomeomorph v) =
      axis.coord (Tphi t + D.planarHomeomorph w) := by
  have hd : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  have hvSupport : v ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hv)
  have hwSupport : w ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hw)
  have hdvw : dist v w ≤ Metric.diam C.region.support :=
    Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hvSupport hwSupport
  have hdist : dist (v + (s : Tiling.Plane)) (w + (t : Tiling.Plane)) <
      P.controlRadius := by
    have hle := endpointWitness_dist_le_vertex htrans hcoord
    have hsmall : Metric.diam C.region.support < P.scale := by
      rw [hd]
      have hnonneg : 0 ≤ Metric.diam C.region.openCarrier := Metric.diam_nonneg
      linarith
    exact lt_trans (lt_of_le_of_lt hle
      (lt_of_le_of_lt hdvw hsmall)) P.scale_lt_controlRadius
  obtain ⟨a, ha, hA⟩ := translatedVertex_targetImage phi D Tphi hTphi s v hv
  obtain ⟨b, hb, hB⟩ := translatedVertex_targetImage phi D Tphi hTphi t w hw
  have hsource : Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) = 0 := by
    rw [ha, hb]
    cases axis <;> simpa [Axis.coord, Complex.sub_re, Complex.sub_im] using
      sub_eq_zero.mpr hcoord
  have hdist' : dist (a : Tiling.Plane) b < P.controlRadius := by
    simpa [ha, hb] using hdist
  have htarget := (deformation_reflectsFiniteValues P phi hphi axis a b a b
    hdist' hdist').2.1.mpr hsource
  rw [hA, hB] at htarget
  cases axis
  · apply sub_eq_zero.mp
    simpa [Axis.coord, Complex.sub_re] using htarget
  · apply sub_eq_zero.mp
    simpa [Axis.coord, Complex.sub_im] using htarget

private theorem endpointWitness_source_coord_eq
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres) (v w : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices)
    (htrans : axis.transverseCoord (Tphi s) =
      axis.transverseCoord (Tphi t))
    (hcoord : axis.coord (Tphi s + D.planarHomeomorph v) =
      axis.coord (Tphi t + D.planarHomeomorph w)) :
    axis.coord (v + (s : Tiling.Plane)) =
      axis.coord (w + (t : Tiling.Plane)) := by
  obtain ⟨a, ha, hA⟩ := translatedVertex_targetImage phi D Tphi hTphi s v hv
  obtain ⟨b, hb, hB⟩ := translatedVertex_targetImage phi D Tphi hTphi t w hw
  have hd : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  have hdscale : Metric.diam C.region.support < P.scale := by
    rw [hd]
    nlinarith [hScale,
      (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
  have hDle := deformedRegion_diam_le_add_localError P hphi D hdscale
  have hlocal : P.localError < 1 := by
    rw [P.localError_eq]
    apply (inv_lt_one₀ P.scale_pos).2
    nlinarith [hScale,
      (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
  have hDlt : Metric.diam D.deformedRegion.support < P.scale / 10 := by
    rw [hd] at hDle
    nlinarith [hScale, hlocal]
  have hvSupport : D.planarHomeomorph v ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion (by
        rw [D.vertices_image]
        exact ⟨v, hv, rfl⟩))
  have hwSupport : D.planarHomeomorph w ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion (by
        rw [D.vertices_image]
        exact ⟨w, hw, rfl⟩))
  have hvw : dist (D.planarHomeomorph v) (D.planarHomeomorph w) ≤
      Metric.diam D.deformedRegion.support :=
    Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded
      hvSupport hwSupport
  have hplaced : dist (Tphi s + D.planarHomeomorph v)
      (Tphi t + D.planarHomeomorph w) ≤
      dist (D.planarHomeomorph v) (D.planarHomeomorph w) := by
    simpa [add_comm] using (endpointWitness_dist_le_vertex
      (s := Tphi s) (t := Tphi t)
      (v := D.planarHomeomorph v) (w := D.planarHomeomorph w)
      htrans (by simpa [add_comm] using hcoord))
  have hmapdist : dist (mapTranslatedVertex phi a)
      (mapTranslatedVertex phi b) < P.scale / 2 := by
    rw [hA, hB]
    exact hplaced.trans_lt (hvw.trans_lt (by linarith [hDlt, P.scale_pos]))
  have hdist : dist (a : Tiling.Plane) b < P.controlRadius :=
    (P.coarse_inverse phi hphi a b hmapdist).trans P.scale_lt_controlRadius
  have htarget : Axis.coord axis
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 := by
    rw [hA, hB]
    cases axis <;> simpa [Axis.coord, Complex.sub_re, Complex.sub_im] using
      sub_eq_zero.mpr hcoord
  have hsource := (deformation_reflectsFiniteValues P phi hphi axis a b a b
    hdist hdist).2.1.mp htarget
  rw [ha, hb] at hsource
  cases axis
  · apply sub_eq_zero.mp
    simpa [Axis.coord, Complex.sub_re] using hsource
  · apply sub_eq_zero.mp
    simpa [Axis.coord, Complex.sub_im] using hsource

private theorem target_transverse_line
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres) (x y : Tiling.Plane)
    (hcent : axis.transverseCoord (s : Tiling.Plane) =
      axis.transverseCoord (t : Tiling.Plane))
    (hxy : axis.transverseCoord x = axis.transverseCoord y) :
    axis.transverseCoord (Tphi s + D.planarHomeomorph (x - (s : Tiling.Plane))) =
      axis.transverseCoord (Tphi t + D.planarHomeomorph (y - (t : Tiling.Plane))) := by
  cases axis with
  | horizontal =>
      have hcent' : (s : Tiling.Plane).im = (t : Tiling.Plane).im := hcent
      have hxy' : x.im = y.im := hxy
      have hsmap : (Tphi s).im = (Tphi t).im := by
        rw [hTphi s, hTphi t]
        simp only [mapPoint, mapScalar, Complex.add_im, Complex.mul_im,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, zero_add]
        congr 1
        exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
          (show
            (⟨(C.centrePoint s s.property).1.im,
              (C.centrePoint s s.property).2.2⟩ : C.coordinateSpace) =
              ⟨(C.centrePoint t t.property).1.im,
                (C.centrePoint t t.property).2.2⟩ from
            Subtype.ext hcent')
      simp only [Axis.transverseCoord, D.planarHomeomorph_apply,
        Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, zero_add]
      rw [hsmap]
      congr 1
      have hdiff : x.im - (s : Tiling.Plane).im =
          y.im - (t : Tiling.Plane).im := by rw [hxy', hcent']
      simp [hdiff]
  | vertical =>
      have hcent' : (s : Tiling.Plane).re = (t : Tiling.Plane).re := hcent
      have hxy' : x.re = y.re := hxy
      have hsmap : (Tphi s).re = (Tphi t).re := by
        rw [hTphi s, hTphi t]
        simp only [mapPoint, mapScalar, Complex.add_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero]
        congr 1
        exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
          (show
            (⟨(C.centrePoint s s.property).1.re,
              (C.centrePoint s s.property).2.1⟩ : C.coordinateSpace) =
              ⟨(C.centrePoint t t.property).1.re,
                (C.centrePoint t t.property).2.1⟩ from
            Subtype.ext hcent')
      simp only [Axis.transverseCoord, D.planarHomeomorph_apply,
        Complex.add_re, Complex.sub_re]
      rw [hsmap]
      congr 1
      have hdiff : x.re - (s : Tiling.Plane).re =
          y.re - (t : Tiling.Plane).re := by rw [hxy', hcent']
      simp [hdiff]

private theorem endpoint_witness_center_of_mem
    {C : ApproximationContext} {S : Set ↥C.centres}
    {K : Region} {axis : Axis} {q : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Set.image Subtype.val S)))
    (hq : q ∉ translatedVertexLevels K (Set.image Subtype.val S) axis)
    (hfull : {x : ℝ | slicePoint axis q x ∈
      openUnion K (Set.image Subtype.val S)} =ᵐ[volume] univ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (sliceEndpointSet K (Set.image Subtype.val S) axis q ∩ Q).Finite)
    (hunbddAbove : ¬ BddAbove
      (sliceEndpointSet K (Set.image Subtype.val S) axis q))
    {x : ℝ} (hx : x ∈ sliceEndpointSet K (Set.image Subtype.val S) axis q) :
    ∃ z : ↥C.centres × K.vertices,
      z.1 ∈ S ∧ x = axis.coord (z.2.1 + (z.1 : Tiling.Plane)) := by
  obtain ⟨t, v, hxv⟩ := endpoint_witness_of_mem
    hpacking hq hfull hlocal hunbddAbove hx
  rcases t.property with ⟨s, hs, hst⟩
  refine ⟨(s, v), hs, ?_⟩
  simpa [hst] using hxv

private theorem targetEndpoint_strict_of_source_gap
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t u : ↥C.centres) (v w v₀ w₀ : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices)
    (hv₀ : v₀ ∈ C.region.vertices) (hw₀ : w₀ ∈ C.region.vertices)
    (hsv : axis.transverseCoord (s : Tiling.Plane) =
      axis.transverseCoord (u : Tiling.Plane))
    (htu : axis.transverseCoord (t : Tiling.Plane) =
      axis.transverseCoord (u : Tiling.Plane))
    (hx : axis.coord (v + (s : Tiling.Plane)) =
      axis.coord (v₀ + (u : Tiling.Plane)))
    (hy : axis.coord (w + (t : Tiling.Plane)) =
      axis.coord (w₀ + (u : Tiling.Plane)))
    (hpositive : 0 < axis.coord (w₀ - v₀)) :
    axis.coord (Tphi s + D.planarHomeomorph v) <
      axis.coord (Tphi t + D.planarHomeomorph w) := by
  have hleft := endpointWitness_target_coord_eq P hScale phi hphi D Tphi hTphi
    axis s u v v₀ hv hv₀ hsv hx
  have hright := endpointWitness_target_coord_eq P hScale phi hphi D Tphi hTphi
    axis t u w w₀ hw hw₀ htu hy
  have horder : axis.coord (D.planarHomeomorph v₀) <
      axis.coord (D.planarHomeomorph w₀) := by
    cases axis with
    | horizontal =>
        simpa [Axis.coord, D.planarHomeomorph_apply] using
          D.firstHomeomorph_strictMono (by
            simpa [Axis.coord, Complex.sub_re] using sub_pos.mp hpositive)
    | vertical =>
        simpa [Axis.coord, D.planarHomeomorph_apply] using
          D.secondHomeomorph_strictMono (by
            simpa [Axis.coord, Complex.sub_im] using sub_pos.mp hpositive)
  rw [hleft, hright]
  cases axis with
  | horizontal =>
      simpa [Axis.coord, Complex.add_re, add_comm] using
        add_lt_add_left horder (Tphi u).re
  | vertical =>
      simpa [Axis.coord, Complex.add_im, add_comm] using
        add_lt_add_left horder (Tphi u).im

private theorem source_witnessed_chain_for_centerColumn
    {C : ApproximationContext} (axis : Axis) (S : Set ↥C.centres)
    (c : ℝ) (hColumn : IsCenterColumn axis C.region (Set.image Subtype.val S))
    (hgeneric : ∀ t ∈ S, c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
      (axis.transverseCoord '' C.region.vertices))
    (hnonempty : (axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c})).Nonempty) :
    Nonempty (WitnessedLabelledFibreChain axis C.region
      (Set.image Subtype.val S) c) := by
  obtain ⟨c₀, _hS, _hcoord, hsupp⟩ :=
    Tiling.AxisParallel.centerColumn_regularSupport hColumn
  have hsections := centerColumn_fullSections axis C.region
    (Set.image Subtype.val S) hColumn
  have hcase := hsections c
  have hq : c ∉ translatedVertexLevels C.region
      (Set.image Subtype.val S) axis := by
    rintro ⟨⟨t, v⟩, rfl⟩
    rcases t.property with ⟨s, hs, hst⟩
    apply hgeneric s hs
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    refine ⟨v.1, v.2, ?_⟩
    let t' : ↥(Set.image Subtype.val S) := ⟨s, ⟨s, hs, rfl⟩⟩
    have htt : t = t' := Subtype.ext hst.symm
    rw [htt]
    cases axis <;> simp [Axis.transverseCoord, add_comm, t', hst]
  have hpacking := hColumn.1
  have hgeneric' : ∀ t ∈ Set.image Subtype.val S, c ∉
      axis.transverseCoord t +ᵥ (axis.transverseCoord '' C.region.vertices) := by
    intro t ht
    rcases ht with ⟨s, hs, rfl⟩
    exact hgeneric s hs
  have hfull : {x : ℝ | slicePoint axis c x ∈
      openUnion C.region (Set.image Subtype.val S)} =ᵐ[volume] univ := by
    rcases hcase with hfull | hempty
    · exact generic_slice_raw_ae_of_full
        hpacking hgeneric' hfull
    · rcases hnonempty with ⟨x, hx⟩
      exact (hempty ▸ hx).elim
  have hsupport : axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c}) = Set.univ := by
    rcases hcase with hfull | hempty
    · exact hfull
    · rcases hnonempty with ⟨x, hx⟩
      exact (hempty ▸ hx).elim
  have hlocal := genericSliceEndpointSet_locallyFinite_fixed
    hpacking hq
  obtain ⟨habove, hbelow⟩ := frontier_unbounded_of_ae_univ
    hpacking hq hfull
  exact labelledFibreChain_fixed_witnessed
    hpacking hq hfull hsupport
    hlocal habove hbelow

private theorem witnessed_chain_of_packing_full
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {c : ℝ}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hgeneric : ∀ t ∈ S, c ∉ axis.transverseCoord t +ᵥ
      (axis.transverseCoord '' K.vertices))
    (hfull : axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = Set.univ) :
    Nonempty (WitnessedLabelledFibreChain axis K S c) := by
  have hq : c ∉ translatedVertexLevels K S axis := by
    rintro ⟨⟨t, v⟩, rfl⟩
    apply hgeneric t t.2
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    refine ⟨v.1, v.2, ?_⟩
    cases axis <;> simp [Axis.transverseCoord, add_comm]
  have hraw : {x : ℝ | slicePoint axis c x ∈ openUnion K S} =ᵐ[volume] univ :=
    generic_slice_raw_ae_of_full hpacking hgeneric hfull
  have hlocal := genericSliceEndpointSet_locallyFinite_fixed hpacking hq
  obtain ⟨habove, hbelow⟩ := frontier_unbounded_of_ae_univ
    hpacking hq hraw
  exact labelledFibreChain_fixed_witnessed
    hpacking hq hraw hfull hlocal habove hbelow

private theorem target_gap_transport
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (q cphi : ℝ) (u : ↥C.centres)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hcphi : cphi = axis.transverseCoord
      (Tphi u + D.planarHomeomorph (slicePoint axis q 0 - (u : Tiling.Plane))))
    (hsource : {z : Tiling.Plane | axis.transverseCoord z = q ∧
      axis.coord z ∈ Ioo (axis.coord (v + (u : Tiling.Plane)))
        (axis.coord (w + (u : Tiling.Plane)))} ⊆
      (u : Tiling.Plane) +ᵥ C.region.openCarrier) :
    {z : Tiling.Plane | axis.transverseCoord z = cphi ∧
      axis.coord z ∈ Ioo
        (axis.coord (Tphi u + D.planarHomeomorph v))
        (axis.coord (Tphi u + D.planarHomeomorph w))} ⊆
      Tphi u +ᵥ D.deformedRegion.openCarrier := by
  intro z hz
  cases axis with
  | horizontal =>
      let r : ℝ := (u : Tiling.Plane).re +
        D.firstHomeomorph.symm (z.re - (Tphi u).re)
      let x : Tiling.Plane := (r : ℂ) + (q : ℂ) * Complex.I
      have hzleft : (Tphi u).re + D.firstHomeomorph v.re < z.re := by
        simpa [Axis.coord, D.planarHomeomorph_apply] using hz.2.1
      have hzright : z.re < (Tphi u).re + D.firstHomeomorph w.re := by
        simpa [Axis.coord, D.planarHomeomorph_apply] using hz.2.2
      have hleft : Axis.coord Axis.horizontal (v + (u : Tiling.Plane)) < r := by
        dsimp [r]
        have h : v.re < D.firstHomeomorph.symm (z.re - (Tphi u).re) := by
          apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
          rw [D.firstHomeomorph.apply_symm_apply]
          linarith
        simpa [Axis.coord, add_comm] using add_lt_add_right h (u : Tiling.Plane).re
      have hright : r < Axis.coord Axis.horizontal (w + (u : Tiling.Plane)) := by
        dsimp [r]
        have h : D.firstHomeomorph.symm (z.re - (Tphi u).re) < w.re := by
          apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
          rw [D.firstHomeomorph.apply_symm_apply]
          linarith
        simpa [Axis.coord, add_comm] using add_lt_add_right h (u : Tiling.Plane).re
      have hxsource : x ∈ (u : Tiling.Plane) +ᵥ C.region.openCarrier := by
        apply hsource
        constructor
        · change x.im = q
          simp [x]
        · simpa [x, Axis.coord] using And.intro hleft hright
      have hc' : (Tphi u).im + D.secondHomeomorph
          (q - (u : Tiling.Plane).im) = z.im := by
        have hztrans := hz.1
        change z.im = cphi at hztrans
        rw [hcphi] at hztrans
        simpa [Axis.transverseCoord, D.planarHomeomorph_apply, slicePoint] using hztrans.symm
      have hmap : Tphi u + D.planarHomeomorph (x - (u : Tiling.Plane)) = z := by
        have hxsubre : (x - (u : Tiling.Plane)).re =
            r - (u : Tiling.Plane).re := by simp [x]
        have hxsubim : (x - (u : Tiling.Plane)).im =
            q - (u : Tiling.Plane).im := by simp [x]
        apply Complex.ext
        · simp only [D.planarHomeomorph_apply, Complex.add_re,
            Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, hxsubre]
          dsimp [r]
          rw [add_sub_cancel_left, D.firstHomeomorph.apply_symm_apply]
          ring
        · simp only [D.planarHomeomorph_apply, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            mul_one, hxsubim]
          simpa [Complex.ofReal_re, Complex.mul_re] using hc'
      rw [← translatedTile_image phi D Tphi u]
      exact ⟨x, hxsource, hmap⟩
  | vertical =>
      let r : ℝ := (u : Tiling.Plane).im +
        D.secondHomeomorph.symm (z.im - (Tphi u).im)
      let x : Tiling.Plane := (q : ℂ) + (r : ℂ) * Complex.I
      have hzleft : (Tphi u).im + D.secondHomeomorph v.im < z.im := by
        simpa [Axis.coord, D.planarHomeomorph_apply] using hz.2.1
      have hzright : z.im < (Tphi u).im + D.secondHomeomorph w.im := by
        simpa [Axis.coord, D.planarHomeomorph_apply] using hz.2.2
      have hleft : Axis.coord Axis.vertical (v + (u : Tiling.Plane)) < r := by
        dsimp [r]
        have h : v.im < D.secondHomeomorph.symm (z.im - (Tphi u).im) := by
          apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
          rw [D.secondHomeomorph.apply_symm_apply]
          linarith
        simpa [Axis.coord, add_comm] using add_lt_add_right h (u : Tiling.Plane).im
      have hright : r < Axis.coord Axis.vertical (w + (u : Tiling.Plane)) := by
        dsimp [r]
        have h : D.secondHomeomorph.symm (z.im - (Tphi u).im) < w.im := by
          apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
          rw [D.secondHomeomorph.apply_symm_apply]
          linarith
        simpa [Axis.coord, add_comm] using add_lt_add_right h (u : Tiling.Plane).im
      have hxsource : x ∈ (u : Tiling.Plane) +ᵥ C.region.openCarrier := by
        apply hsource
        constructor
        · change x.re = q
          simp [x]
        · simpa [x, Axis.coord] using And.intro hleft hright
      have hc' : (Tphi u).re + D.firstHomeomorph
          (q - (u : Tiling.Plane).re) = z.re := by
        have hztrans := hz.1
        change z.re = cphi at hztrans
        rw [hcphi] at hztrans
        simpa [Axis.transverseCoord, D.planarHomeomorph_apply, slicePoint] using hztrans.symm
      have hmap : Tphi u + D.planarHomeomorph (x - (u : Tiling.Plane)) = z := by
        have hxsubre : (x - (u : Tiling.Plane)).re =
            q - (u : Tiling.Plane).re := by simp [x]
        have hxsubim : (x - (u : Tiling.Plane)).im =
            r - (u : Tiling.Plane).im := by simp [x]
        apply Complex.ext
        · simp only [D.planarHomeomorph_apply, Complex.add_re,
            Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
            Complex.I_im, mul_zero, hxsubre]
          simpa [Complex.ofReal_re, Complex.mul_re] using hc'
        · simp only [D.planarHomeomorph_apply, Complex.add_im,
            Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
            mul_one, hxsubim]
          dsimp [r]
          rw [add_sub_cancel_left, D.secondHomeomorph.apply_symm_apply]
          ring
      rw [← translatedTile_image phi D Tphi u]
      exact ⟨x, hxsource, hmap⟩

private theorem source_gap_reflect
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (q qphi : ℝ) (u : ↥C.centres)
    (v w : Tiling.Plane)
    (hqphi : qphi = axis.transverseCoord
      (Tphi u + D.planarHomeomorph
        (slicePoint axis q 0 - (u : Tiling.Plane))))
    (htarget : {z : Tiling.Plane | axis.transverseCoord z = qphi ∧
      axis.coord z ∈ Ioo
        (axis.coord (Tphi u + D.planarHomeomorph v))
        (axis.coord (Tphi u + D.planarHomeomorph w))} ⊆
      Tphi u +ᵥ D.deformedRegion.openCarrier) :
    {z : Tiling.Plane | axis.transverseCoord z = q ∧
      axis.coord z ∈ Ioo
        (axis.coord (v + (u : Tiling.Plane)))
        (axis.coord (w + (u : Tiling.Plane)))} ⊆
      (u : Tiling.Plane) +ᵥ C.region.openCarrier := by
  intro z hz
  let r : Tiling.Plane := z - (u : Tiling.Plane)
  let y : Tiling.Plane := Tphi u + D.planarHomeomorph r
  have hytrans : axis.transverseCoord y = qphi := by
    have hzline := hz.1
    rw [hqphi]
    cases axis <;>
      simp [y, r, Axis.transverseCoord, slicePoint,
        D.planarHomeomorph_apply] at hzline ⊢ <;> linarith
  have hycoord : axis.coord y ∈ Ioo
      (axis.coord (Tphi u + D.planarHomeomorph v))
      (axis.coord (Tphi u + D.planarHomeomorph w)) := by
    cases axis with
    | horizontal =>
        have hl : v.re < z.re - (u : Tiling.Plane).re := by
          have h := hz.2.1
          simp [Axis.coord] at h
          linarith
        have hr : z.re - (u : Tiling.Plane).re < w.re := by
          have h := hz.2.2
          simp [Axis.coord] at h
          linarith
        constructor
        · simpa [y, r, Axis.coord, D.planarHomeomorph_apply] using
            add_lt_add_left
              (D.firstHomeomorph_strictMono hl) (Tphi u).re
        · simpa [y, r, Axis.coord, D.planarHomeomorph_apply] using
            add_lt_add_left
              (D.firstHomeomorph_strictMono hr) (Tphi u).re
    | vertical =>
        have hl : v.im < z.im - (u : Tiling.Plane).im := by
          have h := hz.2.1
          simp [Axis.coord] at h
          linarith
        have hr : z.im - (u : Tiling.Plane).im < w.im := by
          have h := hz.2.2
          simp [Axis.coord] at h
          linarith
        constructor
        · simpa [y, r, Axis.coord, D.planarHomeomorph_apply] using
            add_lt_add_left
              (D.secondHomeomorph_strictMono hl) (Tphi u).im
        · simpa [y, r, Axis.coord, D.planarHomeomorph_apply] using
            add_lt_add_left
              (D.secondHomeomorph_strictMono hr) (Tphi u).im
  have hy := htarget ⟨hytrans, hycoord⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
  rw [D.deformedRegion_openCarrier] at hy
  obtain ⟨k, hk, hkmap⟩ := hy
  have hkr : k = r := by
    apply D.planarHomeomorph.injective
    simpa [y] using hkmap
  have hrmem : r ∈ C.region.openCarrier := hkr ▸ hk
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [r, sub_eq_add_neg, add_comm] using hrmem

private theorem tendsto_int_of_uniform_step
    {f : ℤ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hstep : ∀ j, f j + δ ≤ f (j + 1)) :
    Filter.Tendsto f Filter.atTop Filter.atTop ∧
      Filter.Tendsto f Filter.atBot Filter.atBot := by
  have hnat : ∀ n : ℕ, f 0 + (n : ℝ) * δ ≤ f n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep (n : ℤ)
        have hs' : f n + δ ≤ f (n + 1) := by
          simpa only [Int.ofNat_eq_natCast, Int.reduceAdd] using hs
        calc
          f 0 + ((n + 1 : ℕ) : ℝ) * δ =
              (f 0 + (n : ℝ) * δ) + δ := by push_cast; ring
          _ ≤ f n + δ := by linarith
          _ ≤ f (n + 1) := hs'
  have hat : Filter.Tendsto f Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_atTop.mpr ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - f 0) / δ)
    refine ⟨N, ?_⟩
    intro j hj
    have hj0 : 0 ≤ j := le_trans (by omega) hj
    let n : ℕ := Int.toNat j
    have hjn : (n : ℤ) = j := by
      dsimp [n]
      exact Int.toNat_of_nonneg hj0
    have hn := hnat n
    rw [← hjn] at hj
    have hNj : (N : ℝ) ≤ n := by exact_mod_cast hj
    rw [hjn] at hn
    have hN' : b - f 0 < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
    have hlin : b < f 0 + (N : ℝ) * δ := by linarith
    have hmon : (N : ℝ) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hNj (le_of_lt hδ)
    linarith
  have hnat_neg : ∀ n : ℕ, f (-n) + (n : ℝ) * δ ≤ f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hs := hstep (-(n : ℤ) - 1)
        have hs' : f (-(n : ℤ) - 1) + δ ≤ f (-(n : ℤ)) := by simpa using hs
        have hidx : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by omega
        rw [hidx]
        calc
          f (-(n : ℤ) - 1) + ((n + 1 : ℕ) : ℝ) * δ =
              (f (-(n : ℤ) - 1) + δ) + (n : ℝ) * δ := by push_cast; ring
          _ ≤ f (-(n : ℤ)) + (n : ℝ) * δ := by linarith [hs']
          _ ≤ f 0 := ih
  have hbot : Filter.Tendsto f Filter.atBot Filter.atBot := by
    refine Filter.tendsto_atBot_atBot.mpr ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt ((f 0 - b) / δ)
    refine ⟨-(N : ℤ), ?_⟩
    intro j hj
    have hj0 : j ≤ 0 := le_trans hj (by omega)
    let n : ℕ := Int.toNat (-j)
    have hjn : (n : ℤ) = -j := by
      dsimp [n]
      rw [Int.toNat_of_nonneg]
      omega
    have hNj : (N : ℝ) ≤ n := by
      have hj' : (N : ℤ) ≤ -j := by omega
      have hjn' : (N : ℤ) ≤ (n : ℤ) := by rw [hjn]; exact hj'
      exact_mod_cast hjn'
    have hn := hnat_neg n
    have hnj : -(n : ℤ) = j := by omega
    rw [hnj] at hn
    have hN' : f 0 - b < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
    have hlin : f 0 - (N : ℝ) * δ < b := by linarith
    have hmon : (N : ℝ) * δ ≤ (n : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hNj (le_of_lt hδ)
    linarith
  exact ⟨hat, hbot⟩

private theorem mapScalar_translatedDifferenceScalar_local
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Axis) (a b : ↥C.translatedVertices) :
    mapScalar phi (C.translatedDifferenceScalar axis a b) =
      Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) := by
  cases axis <;>
    simp only [ApproximationContext.translatedDifferenceScalar, mapTranslatedVertex,
      mapPoint, mapScalar, Axis.coord, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add]
  all_goals
    norm_cast
    rw [← map_sub]
    rfl

private theorem mappedTranslatedVertex_positive_mem_scalarAlphabet
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (a b : ↥C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < P.controlRadius)
    (hsource : 0 < Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane))) :
    C.translatedDifferenceScalar axis a b ∈ P.scalarAlphabet ∧
      0 < Axis.coord axis (mapTranslatedVertex phi a - mapTranslatedVertex phi b) := by
  have hz : C.translatedDifferenceScalar axis a b ∈ P.scalarAlphabet := by
    have hzset : C.translatedDifferenceScalar axis a b ∈
        (P.scalarAlphabet : Set C.coordinateSpace) := by
      rw [P.scalarAlphabet_exact]
      exact ⟨axis, a, b, hab, by cases axis <;> rfl⟩
    exact hzset
  have hz' : C.translatedDifferenceScalar axis a b ∈
      P.scalarAlphabet ∪ P.edgeSumAlphabet :=
    Finset.mem_union_left _ hz
  have hsign := P.scalar_sign phi hphi
    (C.translatedDifferenceScalar axis a b) hz'
  rw [mapScalar_translatedDifferenceScalar_local] at hsign
  have hsource' : Real.sign
      ((C.translatedDifferenceScalar axis a b : C.coordinateSpace) : ℝ) = 1 := by
    have hcoord : ((C.translatedDifferenceScalar axis a b : C.coordinateSpace) : ℝ) =
        Axis.coord axis ((a : Tiling.Plane) - (b : Tiling.Plane)) := by
      cases axis <;> rfl
    rw [hcoord]
    exact Real.sign_of_pos hsource
  rw [hsource'] at hsign
  have hnonneg : 0 ≤ Axis.coord axis
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b) := by
    by_contra hn
    have hneg : Axis.coord axis
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) < 0 :=
      lt_of_not_ge hn
    rw [Real.sign_of_neg hneg] at hsign
    norm_num at hsign
  have hne : Axis.coord axis
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b) ≠ 0 := by
    intro hz0
    rw [Real.sign_eq_zero_iff.mpr hz0] at hsign
    norm_num at hsign
  exact ⟨hz, lt_of_le_of_ne hnonneg (Ne.symm hne)⟩

private theorem exists_uniform_mapped_step
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (f : ℤ → ℝ)
    (hgap : ∀ j, ∃ a b : ↥C.translatedVertices,
      dist (a : Tiling.Plane) b < P.controlRadius ∧
      0 < Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) ∧
      f j = Axis.coord axis (mapTranslatedVertex phi a) ∧
      f (j + 1) = Axis.coord axis (mapTranslatedVertex phi b)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, f j + δ ≤ f (j + 1) := by
  let positive : Finset ℝ :=
    (P.scalarAlphabet.image (mapScalar phi)).filter (fun x => 0 < x)
  have hpositive : positive.Nonempty := by
    obtain ⟨a, b, hab, hsrc, hfa, hfb⟩ := hgap 0
    obtain ⟨hz, hpos⟩ := mappedTranslatedVertex_positive_mem_scalarAlphabet
      P phi hphi axis b a (by simpa [dist_comm] using hab) hsrc
    refine ⟨mapScalar phi (C.translatedDifferenceScalar axis b a), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hz, rfl⟩, by
      have hmap := mapScalar_translatedDifferenceScalar_local phi axis b a
      rw [hmap]
      exact hpos⟩
  let δ : ℝ := positive.min' hpositive
  have hδ : 0 < δ := by
    have hm := (Finset.mem_filter.mp (Finset.min'_mem positive hpositive)).2
    simpa [δ] using hm
  refine ⟨δ, hδ, ?_⟩
  intro j
  obtain ⟨a, b, hab, hsrc, hfa, hfb⟩ := hgap j
  obtain ⟨hz, hpos⟩ := mappedTranslatedVertex_positive_mem_scalarAlphabet
    P phi hphi axis b a (by simpa [dist_comm] using hab) hsrc
  have hm : mapScalar phi (C.translatedDifferenceScalar axis b a) ∈ positive := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨_, hz, rfl⟩, by
      have hmap := mapScalar_translatedDifferenceScalar_local phi axis b a
      rw [hmap]
      exact hpos⟩
  have hmin := Finset.min'_le positive _ hm
  have hmin' : δ ≤ mapScalar phi
      (C.translatedDifferenceScalar axis b a) := by simpa [δ] using hmin
  rw [mapScalar_translatedDifferenceScalar_local] at hmin'
  have hdiff : Axis.coord axis
      (mapTranslatedVertex phi b - mapTranslatedVertex phi a) =
      f (j + 1) - f j := by
    have hcoord : Axis.coord axis
        (mapTranslatedVertex phi b - mapTranslatedVertex phi a) =
        Axis.coord axis (mapTranslatedVertex phi b) -
          Axis.coord axis (mapTranslatedVertex phi a) := by
      cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im]
    calc
      _ = Axis.coord axis (mapTranslatedVertex phi b) -
          Axis.coord axis (mapTranslatedVertex phi a) := hcoord
      _ = f (j + 1) - f j := by linarith [hfa, hfb]
  rw [hdiff] at hmin'
  linarith

private theorem exists_uniform_source_step
    {C : ApproximationContext} (P : FLCControlPackage C)
    (axis : Axis) (f : ℤ → ℝ)
    (hgap : ∀ j, ∃ a b : ↥C.translatedVertices,
      dist (a : Tiling.Plane) b < P.controlRadius ∧
      0 < Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) ∧
      f j = Axis.coord axis (a : Tiling.Plane) ∧
      f (j + 1) = Axis.coord axis (b : Tiling.Plane)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j, f j + δ ≤ f (j + 1) := by
  let positive : Finset ℝ :=
    (P.scalarAlphabet.image fun x : C.coordinateSpace => (x.1 : ℝ)).filter
      (fun x => 0 < x)
  have hpositive : positive.Nonempty := by
    obtain ⟨a, b, hab, hpos, _hfa, _hfb⟩ := hgap 0
    have hz : C.translatedDifferenceScalar axis b a ∈ P.scalarAlphabet := by
      have hzset : C.translatedDifferenceScalar axis b a ∈
          (P.scalarAlphabet : Set C.coordinateSpace) := by
        rw [P.scalarAlphabet_exact]
        refine ⟨axis, b, a, by simpa [dist_comm] using hab, ?_⟩
        cases axis <;> rfl
      exact hzset
    refine ⟨(C.translatedDifferenceScalar axis b a : ℝ), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨_, hz, rfl⟩, ?_⟩
    have hval : (C.translatedDifferenceScalar axis b a : ℝ) =
        Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) := by
      cases axis <;> rfl
    rw [hval]
    exact hpos
  let δ : ℝ := positive.min' hpositive
  have hδ : 0 < δ := by
    have hm := (Finset.mem_filter.mp (Finset.min'_mem positive hpositive)).2
    simpa [δ] using hm
  refine ⟨δ, hδ, ?_⟩
  intro j
  obtain ⟨a, b, hab, hpos, hfa, hfb⟩ := hgap j
  have hz : C.translatedDifferenceScalar axis b a ∈ P.scalarAlphabet := by
    have hzset : C.translatedDifferenceScalar axis b a ∈
        (P.scalarAlphabet : Set C.coordinateSpace) := by
      rw [P.scalarAlphabet_exact]
      refine ⟨axis, b, a, by simpa [dist_comm] using hab, ?_⟩
      cases axis <;> rfl
    exact hzset
  have hm : (C.translatedDifferenceScalar axis b a : ℝ) ∈ positive := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_image.mpr ⟨_, hz, rfl⟩, ?_⟩
    have hval : (C.translatedDifferenceScalar axis b a : ℝ) =
        Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) := by
      cases axis <;> rfl
    rw [hval]
    exact hpos
  have hmin := Finset.min'_le positive _ hm
  have hdiff : (C.translatedDifferenceScalar axis b a : ℝ) =
      f (j + 1) - f j := by
    rw [hfb, hfa]
    cases axis <;> simp [ApproximationContext.translatedDifferenceScalar,
      Axis.coord, Complex.sub_re, Complex.sub_im]
  have hmin' : δ ≤ (C.translatedDifferenceScalar axis b a : ℝ) := by
    simpa [δ] using hmin
  rw [hdiff] at hmin'
  linarith

private theorem exists_consecutiveLevelPair_around_local {s : Finset ℝ} {x : ℝ}
    (hx : x ∉ s) (hl : ∃ a ∈ s, a < x) (hu : ∃ b ∈ s, x < b) :
    ∃ a b, (a, b) ∈ consecutiveLevelPairs s ∧ x ∈ Ioo a b := by
  classical
  let L : Set ℝ := {a | a ∈ s ∧ a < x}
  let U : Set ℝ := {b | b ∈ s ∧ x < b}
  have hLfin : L.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  have hUfin : U.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  have hLne : L.Nonempty := by
    obtain ⟨a, ha, hax⟩ := hl
    exact ⟨a, ha, hax⟩
  have hUne : U.Nonempty := by
    obtain ⟨b, hb, hxb⟩ := hu
    exact ⟨b, hb, hxb⟩
  obtain ⟨a, haL, hamax⟩ := Set.exists_max_image L id hLfin hLne
  obtain ⟨b, hbU, hbmin⟩ := Set.exists_min_image U id hUfin hUne
  refine ⟨a, b, ?_, haL.2, hbU.2⟩
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨haL.1, hbU.1⟩, haL.2.trans hbU.2, ?_⟩
  intro z hzs hzbetween
  by_cases hzx : z < x
  · exact (not_lt_of_ge (hamax z ⟨hzs, hzx⟩)) hzbetween.1
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) (Ne.symm (by
        intro h; apply hx; simpa [h] using hzs))
    exact (not_lt_of_ge (hbmin z ⟨hzs, hxz⟩)) hzbetween.2

private theorem labelledFibreChain_of_centerColumn
    {K : Region} {S : Set Tiling.Plane} {axis : Axis} {q : ℝ}
    (hpackingColumn : IsCenterColumn axis K S)
    (hqgeneric : ∀ t ∈ S, q ∉ axis.transverseCoord t +ᵥ
      (axis.transverseCoord '' K.vertices))
    (hsectionNonempty : (axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = q})).Nonempty) :
    Nonempty (LabelledFibreChain axis K S q) := by
  have hsections := centerColumn_fullSections axis K S hpackingColumn
  have hcase := hsections q
  rcases hcase with hfull | hempty
  · rcases hpackingColumn with ⟨hpacking, _hnonempty, _hcollinear, _hinvariant⟩
    have hq : q ∉ translatedVertexLevels K S axis := by
      rintro ⟨⟨t, v⟩, rfl⟩
      apply hqgeneric t t.2
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      refine ⟨v.1, v.2, ?_⟩
      cases axis <;> simp [Axis.transverseCoord, add_comm]
    have hraw := generic_slice_raw_ae_of_full hpacking hqgeneric hfull
    have hlocal := genericSliceEndpointSet_locallyFinite_fixed hpacking hq
    obtain ⟨habove, hbelow⟩ :=
      frontier_unbounded_of_ae_univ hpacking hq hraw
    exact labelledFibreChain_fixed hpacking hq hraw hfull hlocal
      habove hbelow
  · rcases hsectionNonempty with ⟨x, hx⟩
    have hxempty : x ∈ (∅ : Set ℝ) := hempty ▸ hx
    exact hxempty.elim

private theorem fibre_eq_of_uniform_generic_chain
    (axis : Axis) (K : Region) (S : Set Tiling.Plane) (c : ℝ)
    (endpoint : ℤ → ℝ) (owner : ℤ → Tiling.Plane)
    (howner : ∀ j, owner j ∈ S)
    (hstrict : StrictMono endpoint)
    (htop : Filter.Tendsto endpoint Filter.atTop Filter.atTop)
    (hbot : Filter.Tendsto endpoint Filter.atBot Filter.atBot)
    (hgap : ∀ j,
      {z : Tiling.Plane | axis.transverseCoord z = c ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        owner j +ᵥ K.openCarrier)
    (d : ℝ) (hrelative : ∀ j, c - axis.transverseCoord (owner j) = d)
    (hd : d ∉ axis.transverseCoord '' K.vertices) :
    axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = Set.univ := by
  classical
  have hbracket : ∀ y : ℝ, ∃ j : ℤ,
      endpoint j < y ∧ y ≤ endpoint (j + 1) := by
    intro y
    obtain ⟨J, hJ⟩ := Filter.tendsto_atBot_atBot.mp hbot (y - 1)
    have hJy : endpoint J < y := lt_of_le_of_lt (hJ J le_rfl) (by linarith)
    let t : ℕ → ℝ := fun n => endpoint (J + (n : ℤ))
    have htmono : StrictMono t := by
      intro m n hmn
      apply hstrict
      have hmn' : (m : ℤ) < n := by exact_mod_cast hmn
      omega
    have httop : Filter.Tendsto t Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro b
      obtain ⟨k, hk⟩ := Filter.tendsto_atTop_atTop.mp htop b
      obtain ⟨N, hN⟩ := exists_nat_gt (((k - J : ℤ) : ℝ))
      refine ⟨N, ?_⟩
      intro n hn
      apply hk
      have hN' : k - J < (N : ℤ) := by exact_mod_cast hN
      have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
      omega
    have hex : ∃ n, y ≤ t n := by
      obtain ⟨n, hn⟩ := Filter.tendsto_atTop_atTop.mp httop y
      exact ⟨n, hn n le_rfl⟩
    have hmin m := Nat.find_min hex (m := m)
    simp only [not_le] at hmin
    have hfindne : Nat.find hex ≠ 0 := by
      intro heq
      have hspec := Nat.find_spec hex
      rw [heq] at hspec
      exact (not_le_of_gt (by simpa [t] using hJy)) hspec
    have hfindpos : 0 < Nat.find hex := Nat.pos_of_ne_zero hfindne
    have hpred : Nat.find hex - 1 < Nat.find hex :=
      Nat.sub_lt hfindpos zero_lt_one
    have hpredsucc : Nat.find hex - 1 + 1 = Nat.find hex :=
      Nat.sub_add_cancel hfindpos
    obtain ⟨n, hnlo, hnhi⟩ : ∃ n, t n < y ∧ y ≤ t (n + 1) :=
      ⟨Nat.find hex - 1, hmin _ hpred, by
        rw [hpredsucc]
        exact Nat.find_spec hex⟩
    refine ⟨J + (n : ℤ), hnlo, ?_⟩
    dsimp [t] at hnhi
    have hidx : J + ((n : ℤ) + 1) = J + (n : ℤ) + 1 := by omega
    rw [← hidx]
    exact hnhi
  have hslicePoint_coord (q x : ℝ) :
      axis.coord (slicePoint axis q x) = x := by
    cases axis <;> simp [slicePoint, Axis.coord]
  have hslicePoint_transverse (q x : ℝ) :
      axis.transverseCoord (slicePoint axis q x) = q := by
    cases axis <;> simp [slicePoint, Axis.transverseCoord]
  have hslicePoint_eq (z : Tiling.Plane) :
      slicePoint axis (axis.transverseCoord z) (axis.coord z) = z := by
    cases axis <;> apply Complex.ext <;>
      simp [slicePoint, Axis.coord, Axis.transverseCoord]
  have hslicePoint_dist (q x y : ℝ) :
      dist (slicePoint axis q x) (slicePoint axis q y) = |x - y| := by
    cases axis
    · rw [Complex.dist_eq]
      norm_num [slicePoint, Complex.norm_def, Complex.normSq_apply]
      convert Real.sqrt_sq_eq_abs (x - y) using 1
      ring_nf
    · rw [Complex.dist_eq]
      norm_num [slicePoint, Complex.norm_def, Complex.normSq_apply]
      convert Real.sqrt_sq_eq_abs (x - y) using 1
      ring_nf
  obtain ⟨ε, hε, hslice⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ,
      |r - d| < ε → match axis with
        | .horizontal => horizontalSlice K r = horizontalSlice K d
        | .vertical => verticalSlice K r = verticalSlice K d := by
    cases axis with
    | horizontal =>
        have hdFin : d ∉ K.vertexFinset.image Complex.im := by
          intro h
          obtain ⟨v, hv, hvd⟩ := Finset.mem_image.mp h
          apply hd
          refine ⟨v, ?_, hvd⟩
          rw [← K.coe_vertexFinset]
          exact hv
        exact horizontalSlice_locallyConstant K hdFin
    | vertical =>
        have hdFin : d ∉ K.vertexFinset.image Complex.re := by
          intro h
          obtain ⟨v, hv, hvd⟩ := Finset.mem_image.mp h
          apply hd
          refine ⟨v, ?_, hvd⟩
          rw [← K.coe_vertexFinset]
          exact hv
        exact verticalSlice_locallyConstant K hdFin
  have hgap_near : ∀ (j : ℤ) (r : ℝ), |r - c| < ε →
      {z : Tiling.Plane | axis.transverseCoord z = r ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        owner j +ᵥ K.openCarrier := by
    intro j r hrc z hz
    have hz0 : slicePoint axis c (axis.coord z) ∈
        owner j +ᵥ K.openCarrier := by
      apply hgap j
      exact ⟨hslicePoint_transverse c (axis.coord z), by
        simpa [hslicePoint_coord] using hz.2⟩
    cases axis with
    | horizontal =>
        have hrel := hrelative j
        have hrel' : c - (owner j).im = d := by
          simpa [Axis.transverseCoord] using hrel
        have hnear : |(r - (owner j).im) - d| < ε := by
          rw [← hrel']
          have heq : (r - (owner j).im) - (c - (owner j).im) = r - c := by
            ring
          rw [heq]
          exact hrc
        have hs := hslice (r - (owner j).im) hnear
        have hs' : horizontalSlice K (r - (owner j).im) =
            horizontalSlice K d := by simpa using hs
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        have hvadd : -owner j +ᵥ z = Complex.mk
            (z.re - (owner j).re) (z.im - (owner j).im) := by
          apply Complex.ext <;> simp <;> ring
        rw [hvadd]
        have hztrans : z.im = r := hz.1
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz0
        have hz0eq : -owner j +ᵥ
            slicePoint Axis.horizontal c (Axis.horizontal.coord z) =
            Complex.mk (z.re - (owner j).re)
              (c - (owner j).im) := by
          apply Complex.ext <;> simp [slicePoint, Axis.coord] <;> ring
        rw [hz0eq] at hz0
        change z.re - (owner j).re ∈
          horizontalSlice K (c - (owner j).im) at hz0
        rw [hrel', ← hs'] at hz0
        change Complex.mk (z.re - (owner j).re)
          (r - (owner j).im) ∈ K.openCarrier at hz0
        simpa [hztrans] using hz0
    | vertical =>
        have hrel := hrelative j
        have hrel' : c - (owner j).re = d := by
          simpa [Axis.transverseCoord] using hrel
        have hnear : |(r - (owner j).re) - d| < ε := by
          rw [← hrel']
          have heq : (r - (owner j).re) - (c - (owner j).re) = r - c := by
            ring
          rw [heq]
          exact hrc
        have hs := hslice (r - (owner j).re) hnear
        have hs' : verticalSlice K (r - (owner j).re) =
            verticalSlice K d := by simpa using hs
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        have hvadd : -owner j +ᵥ z = Complex.mk
            (z.re - (owner j).re) (z.im - (owner j).im) := by
          apply Complex.ext <;> simp <;> ring
        rw [hvadd]
        have hztrans : z.re = r := hz.1
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz0
        have hz0eq : -owner j +ᵥ
            slicePoint Axis.vertical c (Axis.vertical.coord z) =
            Complex.mk (c - (owner j).re)
              (z.im - (owner j).im) := by
          apply Complex.ext <;> simp [slicePoint, Axis.coord] <;> ring
        rw [hz0eq] at hz0
        change z.im - (owner j).im ∈
          verticalSlice K (c - (owner j).re) at hz0
        rw [hrel', ← hs'] at hz0
        change Complex.mk (r - (owner j).re)
          (z.im - (owner j).im) ∈ K.openCarrier at hz0
        simpa [hztrans] using hz0
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let w := slicePoint axis c x
  have hwreg : w ∈ regularSupport K S := by
    change w ∈ interior (closure (openUnion K S))
    apply mem_interior_iff_mem_nhds.mpr
    have hballnh : Metric.ball w (ε / 2) ∈ nhds w :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith))
    apply Filter.mem_of_superset hballnh
    intro z hzball
    rw [Metric.mem_closure_iff]
    intro η hη
    have hzclose : |axis.transverseCoord z - c| < ε := by
      have hle := axis_transverse_le_dist axis z w
      have hwtrans : axis.transverseCoord w = c :=
        hslicePoint_transverse c x
      rw [hwtrans] at hle
      exact lt_of_le_of_lt hle (lt_trans
        (by simpa [Metric.mem_ball] using hzball) (by linarith))
    obtain ⟨j, hjlo, hjhi⟩ := hbracket (axis.coord z)
    by_cases hjend : axis.coord z < endpoint (j + 1)
    · refine ⟨z, ?_, dist_self z |>.trans_lt hη⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨owner j, howner j⟩, ?_⟩
      exact hgap_near j (axis.transverseCoord z) hzclose
        ⟨rfl, hjlo, hjend⟩
    · have hjEq : axis.coord z = endpoint (j + 1) :=
        le_antisymm hjhi (le_of_not_gt hjend)
      have hwidth : 0 < axis.coord z - endpoint j := by linarith
      let ρ : ℝ := min ((axis.coord z - endpoint j) / 2) (η / 2)
      have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
      let p := slicePoint axis (axis.transverseCoord z) (axis.coord z - ρ)
      have hpcoord : axis.coord p = axis.coord z - ρ :=
        hslicePoint_coord _ _
      have hptrans : axis.transverseCoord p = axis.transverseCoord z :=
        hslicePoint_transverse _ _
      have hpGap : axis.coord p ∈ Ioo (endpoint j) (endpoint (j + 1)) := by
        rw [hpcoord, ← hjEq]
        constructor
        · have hρle := min_le_left ((axis.coord z - endpoint j) / 2) (η / 2)
          linarith
        · linarith
      refine ⟨p, ?_, ?_⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        refine ⟨⟨owner j, howner j⟩, ?_⟩
        exact hgap_near j (axis.transverseCoord z) hzclose
          ⟨hptrans, hpGap⟩
      · calc
          dist z p = dist
              (slicePoint axis (axis.transverseCoord z) (axis.coord z))
              (slicePoint axis (axis.transverseCoord z) (axis.coord z - ρ)) := by
                rw [hslicePoint_eq z]
          _ = |axis.coord z - (axis.coord z - ρ)| :=
            hslicePoint_dist _ _ _
          _ < η := by
            rw [show axis.coord z - (axis.coord z - ρ) = ρ by ring,
              abs_of_pos hρ]
            have hρle := min_le_right
              ((axis.coord z - endpoint j) / 2) (η / 2)
            linarith
  refine ⟨w, ⟨hwreg, hslicePoint_transverse c x⟩, ?_⟩
  exact hslicePoint_coord c x

private theorem allGenericFibreChainsTransport_of_witnessed
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (c c₀ : ℝ)
    (hc₀ : ∀ z ∈ Set.image Subtype.val S,
      axis.transverseCoord z = c₀)
    (hgeneric : ∀ t ∈ S, c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
      (axis.transverseCoord '' C.region.vertices))
    (Gsrc : WitnessedLabelledFibreChain axis C.region
      (Set.image Subtype.val S) c)
    (s₀ : ↥C.centres) (hs₀ : s₀ ∈ S) :
    ∃ cphi : ℝ,
      cphi = axis.transverseCoord
        (Tphi s₀ + D.planarHomeomorph
          (slicePoint axis c 0 - (s₀ : Tiling.Plane))) ∧
      Nonempty (LabelledFibreChain axis D.deformedRegion
        (deformedCenterCarrierOn Tphi S) cphi) := by
  classical
  let cphi : ℝ := axis.transverseCoord
    (Tphi s₀ +
      D.planarHomeomorph (slicePoint axis c 0 -
        (s₀ : Tiling.Plane)))
  let sourceOwner : ℤ → ↥C.centres := fun j =>
    (Gsrc.gap_witness j).choose.property.choose
  let sourceVertex : ℤ → Tiling.Plane := fun j =>
    (Gsrc.gap_witness j).choose_spec.choose
  have hsourceOwner_eq (j : ℤ) :
      ((Gsrc.gap_witness j).choose : Tiling.Plane) =
        (sourceOwner j : Tiling.Plane) := by
    exact (Gsrc.gap_witness j).choose.property.choose_spec.2.symm
  have hsourceEndpoint (j : ℤ) :
      Gsrc.chain.endpoint j =
        axis.coord (sourceVertex j + (sourceOwner j : Tiling.Plane)) := by
    let p := (Gsrc.gap_witness j).choose_spec
    have hj := p.choose_spec.choose_spec.2.2.1
    change Gsrc.chain.endpoint j =
      axis.coord (p.choose + ((Gsrc.gap_witness j).choose : Tiling.Plane)) at hj
    calc
      Gsrc.chain.endpoint j =
          axis.coord (p.choose + ((Gsrc.gap_witness j).choose : Tiling.Plane)) := hj
      _ = axis.coord (sourceVertex j + (sourceOwner j : Tiling.Plane)) := by
        congr 1
        change p.choose + ((Gsrc.gap_witness j).choose : Tiling.Plane) =
          p.choose + (sourceOwner j : Tiling.Plane)
        exact congrArg (fun z : Tiling.Plane => p.choose + z)
          (hsourceOwner_eq j)
  let endpoint : ℤ → ℝ := fun j =>
    axis.coord (Tphi (sourceOwner j) + D.planarHomeomorph (sourceVertex j))
  have hmappedGap : ∀ j : ℤ, ∃ a b : ↥C.translatedVertices,
      dist (a : Tiling.Plane) b < P.controlRadius ∧
      0 < Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) ∧
      endpoint j = Axis.coord axis (mapTranslatedVertex phi a) ∧
      endpoint (j + 1) = Axis.coord axis (mapTranslatedVertex phi b) := by
    intro j
    rcases (Gsrc.gap_witness j) with ⟨t, v, w, hv, hw, hleft, hright, hpos, hinc⟩
    rcases t.property with ⟨s, hs, hst⟩
    have hsOwner : sourceOwner j ∈ S :=
      (Gsrc.gap_witness j).choose.property.choose_spec.1
    have htrans_left : axis.transverseCoord (sourceOwner j : Tiling.Plane) =
        axis.transverseCoord (s : Tiling.Plane) := by
      rw [hc₀ _ ⟨sourceOwner j, hsOwner, rfl⟩,
        hc₀ _ ⟨s, hs, rfl⟩]
    have htrans_right : axis.transverseCoord
        (sourceOwner (j + 1) : Tiling.Plane) =
        axis.transverseCoord (s : Tiling.Plane) := by
      have hsOwner' : sourceOwner (j + 1) ∈ S :=
        (Gsrc.gap_witness (j + 1)).choose.property.choose_spec.1
      rw [hc₀ _ ⟨sourceOwner (j + 1), hsOwner', rfl⟩,
        hc₀ _ ⟨s, hs, rfl⟩]
    let x : Tiling.Plane := slicePoint axis c
      ((Gsrc.chain.endpoint j + Gsrc.chain.endpoint (j + 1)) / 2)
    have hlt : Gsrc.chain.endpoint j < Gsrc.chain.endpoint (j + 1) :=
      Gsrc.chain.strictMono (by omega)
    have hxI : axis.coord x ∈ Ioo (Gsrc.chain.endpoint j)
        (Gsrc.chain.endpoint (j + 1)) := by
      cases axis with
      | horizontal =>
          constructor <;> dsimp [x, slicePoint] <;> simp [Axis.coord] <;> linarith
      | vertical =>
          constructor <;> dsimp [x, slicePoint] <;> simp [Axis.coord] <;> linarith
    have hxaxis : x ∈ axisInterval axis c (Gsrc.chain.endpoint j)
        (Gsrc.chain.endpoint (j + 1)) := by
      cases axis <;> simpa [axisInterval, x, slicePoint, Axis.coord,
        Axis.transverseCoord] using hxI
    have hxin : x ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier := hinc hxaxis
    obtain ⟨a, b, ha, hb, hab⟩ := translatedCellVertexPair_control P hScale s s x
      (by simpa [hst] using hxin) (by simpa [hst] using hxin) v w hv hw
    have hdist : dist (a : Tiling.Plane) b < P.controlRadius := hab
    have hsource_coord : axis.coord (sourceVertex j +
        (sourceOwner j : Tiling.Plane)) = axis.coord (v + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint j := (hsourceEndpoint j).symm
        _ = axis.coord (v + (t : Tiling.Plane)) := hleft
        _ = axis.coord (v + (s : Tiling.Plane)) := by rw [hst]
    have hsource_coord' : axis.coord (sourceVertex (j + 1) +
        (sourceOwner (j + 1) : Tiling.Plane)) = axis.coord (w + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint (j + 1) := (hsourceEndpoint (j + 1)).symm
        _ = axis.coord (w + (t : Tiling.Plane)) := hright
        _ = axis.coord (w + (s : Tiling.Plane)) := by rw [hst]
    obtain ⟨aa, haa, haa_map⟩ := translatedVertex_targetImage phi D Tphi hTphi s v hv
    obtain ⟨bb, hbb, hbb_map⟩ := translatedVertex_targetImage phi D Tphi hTphi s w hw
    have haa_eq : a = aa := Subtype.ext (ha.trans haa.symm)
    have hbb_eq : b = bb := Subtype.ext (hb.trans hbb.symm)
    have hsource_pos : 0 < Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) := by
      rw [ha, hb]
      simpa [Axis.coord, Complex.sub_re, Complex.sub_im] using hpos
    have hfa : endpoint j = Axis.coord axis (mapTranslatedVertex phi a) := by
      dsimp [endpoint]
      have h := endpointWitness_target_coord_eq P hScale phi hphi D Tphi hTphi
        axis (sourceOwner j) s (sourceVertex j) v
        (by exact (by
          let p := (Gsrc.gap_witness j).choose_spec
          change p.choose ∈ C.region.vertices
          exact p.choose_spec.choose_spec.1)) hv htrans_left hsource_coord
      rw [h, ← haa_map, haa_eq]
    have hfb : endpoint (j + 1) = Axis.coord axis (mapTranslatedVertex phi b) := by
      dsimp [endpoint]
      have h := endpointWitness_target_coord_eq P hScale phi hphi D Tphi hTphi
        axis (sourceOwner (j + 1)) s (sourceVertex (j + 1)) w
        (by
          let p := (Gsrc.gap_witness (j + 1)).choose_spec
          change p.choose ∈ C.region.vertices
          exact p.choose_spec.choose_spec.1) hw htrans_right hsource_coord'
      rw [h, ← hbb_map, hbb_eq]
    exact ⟨a, b, hdist, hsource_pos, hfa, hfb⟩
  obtain ⟨δ, hδ, hstep⟩ := exists_uniform_mapped_step P phi hphi axis endpoint
    (by
      intro j
      obtain ⟨a, b, hab, hpos, hfa, hfb⟩ := hmappedGap j
      exact ⟨a, b, hab, hpos, hfa, hfb⟩)
  obtain ⟨htop, hbot⟩ := tendsto_int_of_uniform_step hδ hstep
  have hendpointStrict : StrictMono endpoint :=
    strictMono_int_of_lt_succ fun j => by linarith [hδ, hstep j]
  have htargetGap : ∀ j,
      {z : Tiling.Plane | axis.transverseCoord z = cphi ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        Tphi (sourceOwner j) +ᵥ D.deformedRegion.openCarrier := by
    intro j z hz
    let p := (Gsrc.gap_witness j).choose_spec
    let t := (Gsrc.gap_witness j).choose
    let v := p.choose
    let w := p.choose_spec.choose
    have hv : v ∈ C.region.vertices := p.choose_spec.choose_spec.1
    have hw : w ∈ C.region.vertices := p.choose_spec.choose_spec.2.1
    have hleft : Gsrc.chain.endpoint j = axis.coord (v + (t : Tiling.Plane)) :=
      p.choose_spec.choose_spec.2.2.1
    have hright : Gsrc.chain.endpoint (j + 1) =
        axis.coord (w + (t : Tiling.Plane)) :=
      p.choose_spec.choose_spec.2.2.2.1
    have hinc : axisInterval axis c (Gsrc.chain.endpoint j)
        (Gsrc.chain.endpoint (j + 1)) ⊆
        (t : Tiling.Plane) +ᵥ C.region.openCarrier :=
      p.choose_spec.choose_spec.2.2.2.2.2
    rcases t.property with ⟨s, hs, hst⟩
    have hsOwner : sourceOwner j ∈ S :=
      (Gsrc.gap_witness j).choose.property.choose_spec.1
    have htrans : axis.transverseCoord (sourceOwner j : Tiling.Plane) =
        axis.transverseCoord (s : Tiling.Plane) := by
      rw [hc₀ _ ⟨sourceOwner j, hsOwner, rfl⟩,
        hc₀ _ ⟨s, hs, rfl⟩]
    have hcphi : cphi = axis.transverseCoord
        (Tphi s + D.planarHomeomorph (slicePoint axis c 0 -
          (s : Tiling.Plane))) := by
      have hline := target_transverse_line phi D Tphi hTphi axis s₀ s
        (slicePoint axis c 0) (slicePoint axis c 0) (by
          rw [hc₀ _ ⟨s₀, hs₀, rfl⟩, hc₀ _ ⟨s, hs, rfl⟩]) (by rfl)
      simpa [cphi] using hline
    have hsource_coord : axis.coord (sourceVertex j +
        (sourceOwner j : Tiling.Plane)) = axis.coord (v + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint j := (hsourceEndpoint j).symm
        _ = axis.coord (v + (t : Tiling.Plane)) := hleft
        _ = axis.coord (v + (s : Tiling.Plane)) := by rw [hst]
    have hsource_coord' : axis.coord (sourceVertex (j + 1) +
        (sourceOwner (j + 1) : Tiling.Plane)) =
        axis.coord (w + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint (j + 1) := (hsourceEndpoint (j + 1)).symm
        _ = axis.coord (w + (t : Tiling.Plane)) := hright
        _ = axis.coord (w + (s : Tiling.Plane)) := by rw [hst]
    have hvsrc : sourceVertex j ∈ C.region.vertices := by
      let p := (Gsrc.gap_witness j).choose_spec
      change p.choose ∈ C.region.vertices
      exact p.choose_spec.choose_spec.1
    have hwsrc : sourceVertex (j + 1) ∈ C.region.vertices := by
      let p := (Gsrc.gap_witness (j + 1)).choose_spec
      change p.choose ∈ C.region.vertices
      exact p.choose_spec.choose_spec.1
    have hleftTarget := endpointWitness_target_coord_eq P hScale phi hphi D
      Tphi hTphi axis (sourceOwner j) s (sourceVertex j) v hvsrc hv htrans
      hsource_coord
    have hrightTarget := endpointWitness_target_coord_eq P hScale phi hphi D
      Tphi hTphi axis (sourceOwner (j + 1)) s (sourceVertex (j + 1)) w
      hwsrc hw (by
        have hsOwner' : sourceOwner (j + 1) ∈ S :=
          (Gsrc.gap_witness (j + 1)).choose.property.choose_spec.1
        rw [hc₀ _ ⟨sourceOwner (j + 1), hsOwner', rfl⟩,
          hc₀ _ ⟨s, hs, rfl⟩]) hsource_coord'
    have hsource : {y : Tiling.Plane | axis.transverseCoord y = c ∧
        axis.coord y ∈ Ioo (axis.coord (v + (s : Tiling.Plane)))
          (axis.coord (w + (s : Tiling.Plane)))} ⊆
        (s : Tiling.Plane) +ᵥ C.region.openCarrier := by
      intro y hy
      have hy0 := hy
      rw [hst] at hy0
      have hy' : y ∈ axisInterval axis c (Gsrc.chain.endpoint j)
          (Gsrc.chain.endpoint (j + 1)) := by
        cases axis <;> simpa [axisInterval, Axis.coord, Axis.transverseCoord,
          hleft, hright] using hy0
      have hyTile := hinc hy'
      simpa [hst] using hyTile
    have hsourceSet := target_gap_transport P hScale phi hphi D Tphi hTphi axis
      c cphi s v w hv hw hcphi hsource
    have hz' : axis.transverseCoord z = cphi ∧
        axis.coord z ∈ Ioo
          (axis.coord (Tphi s + D.planarHomeomorph v))
          (axis.coord (Tphi s + D.planarHomeomorph w)) := by
      refine ⟨hz.1, ?_⟩
      rw [← hleftTarget, ← hrightTarget]
      exact hz.2
    have hs_eq : sourceOwner j = s := by
      apply Subtype.ext
      exact (hst.trans (hsourceOwner_eq j)).symm
    rw [hs_eq]
    exact hsourceSet hz'
  refine ⟨cphi, rfl, ?_⟩
  refine ⟨endpoint, (fun j => Tphi (sourceOwner j)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [deformedCenterCarrierOn]
    exact ⟨sourceOwner j, (Gsrc.gap_witness j).choose.property.choose_spec.1, rfl⟩
  · have hsucc : ∀ j : ℤ, endpoint j < endpoint (j + 1) := by
      intro j
      rcases (Gsrc.gap_witness j).choose_spec with
        ⟨v, w, hv, hw, hleft, hright, hpos, hinc⟩
      let t := (Gsrc.gap_witness j).choose
      have hvs' : sourceVertex (j + 1) ∈ C.region.vertices := by
        let p' := (Gsrc.gap_witness (j + 1)).choose_spec
        change p'.choose ∈ C.region.vertices
        exact p'.choose_spec.choose_spec.1
      rcases t.property with ⟨s, hs, hst⟩
      have hsOwner : sourceOwner j ∈ S :=
        (Gsrc.gap_witness j).choose.property.choose_spec.1
      have hsOwner' : sourceOwner (j + 1) ∈ S :=
        (Gsrc.gap_witness (j + 1)).choose.property.choose_spec.1
      have htrans_left : axis.transverseCoord (sourceOwner j : Tiling.Plane) =
          axis.transverseCoord (s : Tiling.Plane) := by
        rw [hc₀ _ ⟨sourceOwner j, hsOwner, rfl⟩,
          hc₀ _ ⟨s, hs, rfl⟩]
      have htrans_right : axis.transverseCoord
          (sourceOwner (j + 1) : Tiling.Plane) =
          axis.transverseCoord (s : Tiling.Plane) := by
        rw [hc₀ _ ⟨sourceOwner (j + 1), hsOwner', rfl⟩,
          hc₀ _ ⟨s, hs, rfl⟩]
      have hx : axis.coord (sourceVertex j +
          (sourceOwner j : Tiling.Plane)) =
          axis.coord (v + (s : Tiling.Plane)) := by
        calc
          _ = Gsrc.chain.endpoint j := (hsourceEndpoint j).symm
          _ = axis.coord (v + (t : Tiling.Plane)) := hleft
          _ = axis.coord (v + (s : Tiling.Plane)) := by rw [hst]
      have hy : axis.coord (sourceVertex (j + 1) +
          (sourceOwner (j + 1) : Tiling.Plane)) =
          axis.coord (w + (s : Tiling.Plane)) := by
        calc
          _ = Gsrc.chain.endpoint (j + 1) := (hsourceEndpoint (j + 1)).symm
          _ = axis.coord (w + (t : Tiling.Plane)) := hright
          _ = axis.coord (w + (s : Tiling.Plane)) := by rw [hst]
      have hvs : sourceVertex j ∈ C.region.vertices := by
        let p := (Gsrc.gap_witness j).choose_spec
        change p.choose ∈ C.region.vertices
        exact p.choose_spec.choose_spec.1
      have hstrict := targetEndpoint_strict_of_source_gap P hScale phi hphi D
        Tphi hTphi axis (sourceOwner j) (sourceOwner (j + 1)) s
        (sourceVertex j) (sourceVertex (j + 1)) v w
        hvs hvs' hv hw htrans_left htrans_right
        hx hy hpos
      exact hstrict
    exact strictMono_int_of_lt_succ hsucc
  · exact htop
  · exact hbot
  · intro j z hz
    let p := (Gsrc.gap_witness j).choose_spec
    let t := (Gsrc.gap_witness j).choose
    let v := p.choose
    let w := p.choose_spec.choose
    have hv : v ∈ C.region.vertices := p.choose_spec.choose_spec.1
    have hw : w ∈ C.region.vertices := p.choose_spec.choose_spec.2.1
    have hleft : Gsrc.chain.endpoint j = axis.coord (v + (t : Tiling.Plane)) :=
      p.choose_spec.choose_spec.2.2.1
    have hright : Gsrc.chain.endpoint (j + 1) =
        axis.coord (w + (t : Tiling.Plane)) :=
      p.choose_spec.choose_spec.2.2.2.1
    have hpos : 0 < axis.coord (w - v) :=
      p.choose_spec.choose_spec.2.2.2.2.1
    have hinc : axisInterval axis c (Gsrc.chain.endpoint j)
        (Gsrc.chain.endpoint (j + 1)) ⊆
        (t : Tiling.Plane) +ᵥ C.region.openCarrier :=
      p.choose_spec.choose_spec.2.2.2.2.2
    rcases t.property with ⟨s, hs, hst⟩
    have hsOwner : sourceOwner j ∈ S :=
      (Gsrc.gap_witness j).choose.property.choose_spec.1
    have htrans : axis.transverseCoord (sourceOwner j : Tiling.Plane) =
        axis.transverseCoord (s : Tiling.Plane) := by
      rw [hc₀ _ ⟨sourceOwner j, hsOwner, rfl⟩,
        hc₀ _ ⟨s, hs, rfl⟩]
    have hcphi : cphi = axis.transverseCoord
        (Tphi s + D.planarHomeomorph (slicePoint axis c 0 -
          (s : Tiling.Plane))) := by
      have hline := target_transverse_line phi D Tphi hTphi axis s₀ s
        (slicePoint axis c 0) (slicePoint axis c 0) (by
          rw [hc₀ _ ⟨s₀, hs₀, rfl⟩, hc₀ _ ⟨s, hs, rfl⟩]) (by rfl)
      simpa [cphi] using hline
    have hsource_coord : axis.coord (sourceVertex j +
        (sourceOwner j : Tiling.Plane)) = axis.coord (v + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint j := (hsourceEndpoint j).symm
        _ = axis.coord (v + (t : Tiling.Plane)) := hleft
        _ = axis.coord (v + (s : Tiling.Plane)) := by rw [hst]
    have hsource_coord' : axis.coord (sourceVertex (j + 1) +
        (sourceOwner (j + 1) : Tiling.Plane)) = axis.coord (w + (s : Tiling.Plane)) := by
      calc
        _ = Gsrc.chain.endpoint (j + 1) := (hsourceEndpoint (j + 1)).symm
        _ = axis.coord (w + (t : Tiling.Plane)) := hright
        _ = axis.coord (w + (s : Tiling.Plane)) := by rw [hst]
    have hvsrc : sourceVertex j ∈ C.region.vertices := by
      let p := (Gsrc.gap_witness j).choose_spec
      change p.choose ∈ C.region.vertices
      exact p.choose_spec.choose_spec.1
    have hwsrc : sourceVertex (j + 1) ∈ C.region.vertices := by
      let p := (Gsrc.gap_witness (j + 1)).choose_spec
      change p.choose ∈ C.region.vertices
      exact p.choose_spec.choose_spec.1
    have hleftTarget := endpointWitness_target_coord_eq P hScale phi hphi D
      Tphi hTphi axis (sourceOwner j) s (sourceVertex j) v hvsrc hv htrans
      hsource_coord
    have hrightTarget := endpointWitness_target_coord_eq P hScale phi hphi D
      Tphi hTphi axis (sourceOwner (j + 1)) s (sourceVertex (j + 1)) w
      hwsrc hw (by
        have hsOwner' : sourceOwner (j + 1) ∈ S :=
          (Gsrc.gap_witness (j + 1)).choose.property.choose_spec.1
        rw [hc₀ _ ⟨sourceOwner (j + 1), hsOwner', rfl⟩,
          hc₀ _ ⟨s, hs, rfl⟩]) hsource_coord'
    have hsource : {z : Tiling.Plane | axis.transverseCoord z = c ∧
        axis.coord z ∈ Ioo (axis.coord (v + (s : Tiling.Plane)))
          (axis.coord (w + (s : Tiling.Plane)))} ⊆
        (s : Tiling.Plane) +ᵥ C.region.openCarrier := by
      intro y hy
      have hy0 := hy
      rw [hst] at hy0
      have hy' : y ∈ axisInterval axis c (Gsrc.chain.endpoint j)
          (Gsrc.chain.endpoint (j + 1)) := by
        cases axis <;> simpa [axisInterval, Axis.coord, Axis.transverseCoord,
          hleft, hright] using hy0
      have := hinc hy'
      simpa [hst] using this
    have hsourceSet := target_gap_transport P hScale phi hphi D Tphi hTphi axis
      c cphi s v w hv hw hcphi (by
        exact hsource)
    have hz' : axis.transverseCoord z = cphi ∧
        axis.coord z ∈ Ioo
          (axis.coord (Tphi s + D.planarHomeomorph v))
          (axis.coord (Tphi s + D.planarHomeomorph w)) := by
      refine ⟨hz.1, ?_⟩
      rw [← hleftTarget, ← hrightTarget]
      exact hz.2
    have hs_eq : sourceOwner j = s := by
      apply Subtype.ext
      exact (hst.trans (hsourceOwner_eq j)).symm
    rw [hs_eq]
    exact hsourceSet hz'
  · apply Set.eq_univ_iff_forall.mpr
    intro x
    let dphi : ℝ := cphi - axis.transverseCoord (Tphi s₀)
    have htargetTrans (s : ↥C.centres) (hs : s ∈ S) :
        axis.transverseCoord (Tphi s) =
          axis.transverseCoord (Tphi s₀) := by
      cases axis with
      | horizontal =>
          have hsource : (s : Tiling.Plane).im = (s₀ : Tiling.Plane).im := by
            simpa [Axis.transverseCoord] using
              (hc₀ _ ⟨s, hs, rfl⟩).trans (hc₀ _ ⟨s₀, hs₀, rfl⟩).symm
          rw [hTphi s, hTphi s₀]
          simp only [Axis.transverseCoord, mapPoint, mapScalar, Complex.add_im,
            Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
            mul_one, zero_add]
          congr 1
          exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
            (show
              (⟨(C.centrePoint s s.property).1.im,
                (C.centrePoint s s.property).2.2⟩ : C.coordinateSpace) =
                ⟨(C.centrePoint s₀ s₀.property).1.im,
                  (C.centrePoint s₀ s₀.property).2.2⟩ from
              Subtype.ext hsource)
      | vertical =>
          have hsource : (s : Tiling.Plane).re = (s₀ : Tiling.Plane).re := by
            simpa [Axis.transverseCoord] using
              (hc₀ _ ⟨s, hs, rfl⟩).trans (hc₀ _ ⟨s₀, hs₀, rfl⟩).symm
          rw [hTphi s, hTphi s₀]
          simp only [Axis.transverseCoord, mapPoint, mapScalar, Complex.add_re,
            Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
            Complex.I_re, Complex.I_im, mul_zero]
          congr 1
          exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
            (show
              (⟨(C.centrePoint s s.property).1.re,
                (C.centrePoint s s.property).2.1⟩ : C.coordinateSpace) =
                ⟨(C.centrePoint s₀ s₀.property).1.re,
                  (C.centrePoint s₀ s₀.property).2.1⟩ from
              Subtype.ext hsource)
    have hdphi : dphi ∉ axis.transverseCoord '' D.deformedRegion.vertices := by
      rintro ⟨y, hy, hdy⟩
      rw [D.vertices_image] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      apply hgeneric s₀ hs₀
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      refine ⟨v, hv, ?_⟩
      cases axis with
      | horizontal =>
          have heq : D.secondHomeomorph v.im =
              D.secondHomeomorph (c - (s₀ : Tiling.Plane).im) := by
            simpa [dphi, cphi, Axis.transverseCoord,
              D.planarHomeomorph_apply, slicePoint] using hdy
          have heq' := D.secondHomeomorph.injective heq
          simpa [Axis.transverseCoord, vadd_eq_add, sub_eq_add_neg,
            add_comm] using heq'
      | vertical =>
          have heq : D.firstHomeomorph v.re =
              D.firstHomeomorph (c - (s₀ : Tiling.Plane).re) := by
            simpa [dphi, cphi, Axis.transverseCoord,
              D.planarHomeomorph_apply, slicePoint] using hdy
          have heq' := D.firstHomeomorph.injective heq
          simpa [Axis.transverseCoord, vadd_eq_add, sub_eq_add_neg,
            add_comm] using heq'
    have hrelative : ∀ j,
        cphi - axis.transverseCoord (Tphi (sourceOwner j)) = dphi := by
      intro j
      dsimp [dphi]
      rw [htargetTrans (sourceOwner j)
        (Gsrc.gap_witness j).choose.property.choose_spec.1]
    have hfibre := fibre_eq_of_uniform_generic_chain axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) cphi endpoint
      (fun j => Tphi (sourceOwner j)) (by
        intro j
        rw [deformedCenterCarrierOn]
        exact ⟨sourceOwner j,
          (Gsrc.gap_witness j).choose.property.choose_spec.1, rfl⟩)
      hendpointStrict htop hbot htargetGap dphi hrelative hdphi
    rw [hfibre]
    exact Set.mem_univ x

private theorem allGenericFibreChainsReflect_of_witnessed
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (c cphi c₀ c₁ : ℝ)
    (hsource : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀)
    (htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁)
    (hcphi : cphi = transverseTransportHomeomorph axis D c₀ c₁ c)
    (hgeneric : c ∉ c₀ +ᵥ (axis.transverseCoord '' C.region.vertices))
    (Gtgt : WitnessedLabelledFibreChain axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) cphi) :
    Nonempty (LabelledFibreChain axis C.region
      (Set.image Subtype.val S) c) := by
  classical
  let targetOwner : ℤ → ↥(deformedCenterCarrierOn Tphi S) := fun j =>
    (Gtgt.gap_witness j).choose
  let sourceOwner : ℤ → ↥C.centres := fun j =>
    Classical.choose (targetOwner j).property
  have hsourceOwner_mem (j : ℤ) : sourceOwner j ∈ S :=
    (Classical.choose_spec (targetOwner j).property).1
  have htargetOwner_eq (j : ℤ) :
      Tphi (sourceOwner j) = (targetOwner j : Tiling.Plane) :=
    (Classical.choose_spec (targetOwner j).property).2
  let targetVertex : ℤ → Tiling.Plane := fun j =>
    (Gtgt.gap_witness j).choose_spec.choose
  have htargetVertex_mem (j : ℤ) :
      targetVertex j ∈ D.deformedRegion.vertices :=
    (Gtgt.gap_witness j).choose_spec.choose_spec.choose_spec.1
  have htargetVertex_image (j : ℤ) :
      targetVertex j ∈ D.planarHomeomorph '' C.region.vertices := by
    rw [← D.vertices_image]
    exact htargetVertex_mem j
  let sourceVertex : ℤ → Tiling.Plane := fun j =>
    Classical.choose (htargetVertex_image j)
  have hsourceVertex_mem (j : ℤ) : sourceVertex j ∈ C.region.vertices :=
    (Classical.choose_spec (htargetVertex_image j)).1
  have htargetVertex_eq (j : ℤ) :
      D.planarHomeomorph (sourceVertex j) = targetVertex j :=
    (Classical.choose_spec (htargetVertex_image j)).2
  let endpoint : ℤ → ℝ := fun j =>
    axis.coord (sourceVertex j + (sourceOwner j : Tiling.Plane))
  have htargetEndpoint (j : ℤ) : Gtgt.chain.endpoint j =
      axis.coord (Tphi (sourceOwner j) +
        D.planarHomeomorph (sourceVertex j)) := by
    let p := (Gtgt.gap_witness j).choose_spec
    have hj := p.choose_spec.choose_spec.2.2.1
    change Gtgt.chain.endpoint j =
      axis.coord (targetVertex j + (targetOwner j : Tiling.Plane)) at hj
    rw [← htargetOwner_eq j, ← htargetVertex_eq j] at hj
    calc
      Gtgt.chain.endpoint j = axis.coord
          (D.planarHomeomorph (sourceVertex j) +
            Tphi (sourceOwner j)) := hj
      _ = axis.coord (Tphi (sourceOwner j) +
          D.planarHomeomorph (sourceVertex j)) := by rw [add_comm]
  have hcphi_owner (j : ℤ) : cphi = axis.transverseCoord
      (Tphi (sourceOwner j) + D.planarHomeomorph
        (slicePoint axis c 0 - (sourceOwner j : Tiling.Plane))) := by
    rw [hcphi, transverseTransportHomeomorph_apply]
    have hs := hsource (sourceOwner j) (hsourceOwner_mem j)
    have ht := htarget (sourceOwner j) (hsourceOwner_mem j)
    cases axis with
    | horizontal =>
        simp only [Axis.transverseCoord, Complex.add_im,
          planarHomeomorph_im, slicePoint, Complex.sub_im,
          Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, mul_one, zero_add]
        rw [show (Tphi (sourceOwner j)).im = c₁ by
          simpa only [Axis.transverseCoord] using ht]
        rw [show (sourceOwner j : Tiling.Plane).im = c₀ by
          simpa only [Axis.transverseCoord] using hs]
        congr 2
        simp only [Complex.ofReal_re]
        ring
    | vertical =>
        simp only [Axis.transverseCoord, Complex.add_re,
          planarHomeomorph_re, slicePoint, Complex.sub_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, mul_zero]
        rw [show (Tphi (sourceOwner j)).re = c₁ by
          simpa only [Axis.transverseCoord] using ht]
        rw [show (sourceOwner j : Tiling.Plane).re = c₀ by
          simpa only [Axis.transverseCoord] using hs]
        congr 2
        simp only [Complex.ofReal_im]
        ring
  have hgapData (j : ℤ) : ∃ v w : Tiling.Plane,
      sourceOwner j ∈ S ∧ v ∈ C.region.vertices ∧
      w ∈ C.region.vertices ∧
      endpoint j = axis.coord (v + (sourceOwner j : Tiling.Plane)) ∧
      endpoint (j + 1) = axis.coord (w + (sourceOwner j : Tiling.Plane)) ∧
      0 < axis.coord (w - v) ∧
      {z : Tiling.Plane | axis.transverseCoord z = c ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
        (sourceOwner j : Tiling.Plane) +ᵥ C.region.openCarrier := by
    let p := (Gtgt.gap_witness j).choose_spec
    let wphi : Tiling.Plane := p.choose_spec.choose
    have hwphi : wphi ∈ D.deformedRegion.vertices :=
      p.choose_spec.choose_spec.2.1
    have hwimage : wphi ∈ D.planarHomeomorph '' C.region.vertices := by
      rw [← D.vertices_image]
      exact hwphi
    let w : Tiling.Plane := Classical.choose hwimage
    have hw : w ∈ C.region.vertices := (Classical.choose_spec hwimage).1
    have hwmap : D.planarHomeomorph w = wphi :=
      (Classical.choose_spec hwimage).2
    let u := sourceOwner j
    have hu : u ∈ S := hsourceOwner_mem j
    have hrightTarget : Gtgt.chain.endpoint (j + 1) =
        axis.coord (Tphi u + D.planarHomeomorph w) := by
      have h := p.choose_spec.choose_spec.2.2.2.1
      change Gtgt.chain.endpoint (j + 1) =
        axis.coord (wphi + (targetOwner j : Tiling.Plane)) at h
      rw [← htargetOwner_eq j, ← hwmap] at h
      calc
        Gtgt.chain.endpoint (j + 1) = axis.coord
            (D.planarHomeomorph w + Tphi (sourceOwner j)) := h
        _ = axis.coord (Tphi u + D.planarHomeomorph w) := by
          rw [show u = sourceOwner j from rfl, add_comm]
    have hsourceRight : endpoint (j + 1) =
        axis.coord (w + (u : Tiling.Plane)) := by
      apply endpointWitness_source_coord_eq P hScale phi hphi D Tphi hTphi axis
        (sourceOwner (j + 1)) u (sourceVertex (j + 1)) w
        (hsourceVertex_mem (j + 1)) hw
      · rw [htarget _ (hsourceOwner_mem (j + 1)), htarget u hu]
      · rw [← htargetEndpoint (j + 1), ← hrightTarget]
    have hpositive : 0 < axis.coord (w - sourceVertex j) := by
      have htpos := p.choose_spec.choose_spec.2.2.2.2.1
      change 0 < axis.coord (wphi - targetVertex j) at htpos
      rw [← htargetVertex_eq j, ← hwmap] at htpos
      cases axis with
      | horizontal =>
          have htpos' : 0 < D.firstHomeomorph w.re -
              D.firstHomeomorph (sourceVertex j).re := by
            rw [← planarHomeomorph_re D w,
              ← planarHomeomorph_re D (sourceVertex j)]
            simpa only [Axis.coord, Complex.sub_re] using htpos
          have hlt : (sourceVertex j).re < w.re := by
            apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
            exact sub_pos.mp htpos'
          change 0 < w.re - (sourceVertex j).re
          exact sub_pos.mpr hlt
      | vertical =>
          have htpos' : 0 < D.secondHomeomorph w.im -
              D.secondHomeomorph (sourceVertex j).im := by
            rw [← planarHomeomorph_im D w,
              ← planarHomeomorph_im D (sourceVertex j)]
            simpa only [Axis.coord, Complex.sub_im] using htpos
          have hlt : (sourceVertex j).im < w.im := by
            apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
            exact sub_pos.mp htpos'
          change 0 < w.im - (sourceVertex j).im
          exact sub_pos.mpr hlt
    have htargetGap : {z : Tiling.Plane |
        axis.transverseCoord z = cphi ∧
        axis.coord z ∈ Ioo
          (axis.coord (Tphi u + D.planarHomeomorph (sourceVertex j)))
          (axis.coord (Tphi u + D.planarHomeomorph w))} ⊆
        Tphi u +ᵥ D.deformedRegion.openCarrier := by
      have hinc := p.choose_spec.choose_spec.2.2.2.2.2
      change axisInterval axis cphi (Gtgt.chain.endpoint j)
          (Gtgt.chain.endpoint (j + 1)) ⊆
        (targetOwner j : Tiling.Plane) +ᵥ D.deformedRegion.openCarrier at hinc
      rw [← htargetOwner_eq j] at hinc
      intro z hz
      apply hinc
      cases axis <;> simpa [axisInterval, Axis.coord, Axis.transverseCoord,
        htargetEndpoint j, hrightTarget] using hz
    have hsourceGap := source_gap_reflect phi D Tphi axis c cphi u
      (sourceVertex j) w (hcphi_owner j) htargetGap
    refine ⟨sourceVertex j, w, hsourceOwner_mem j, hsourceVertex_mem j, hw, rfl,
      hsourceRight, hpositive, ?_⟩
    intro z hz
    apply hsourceGap
    simpa [hsourceRight] using hz
  have hstrictSucc : ∀ j, endpoint j < endpoint (j + 1) := by
    intro j
    obtain ⟨v, w, hu, hv, hw, hleft, hright, hpos, hinc⟩ := hgapData j
    rw [hleft, hright]
    cases axis <;> simpa [Axis.coord, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im] using hpos
  have hstrict : StrictMono endpoint := strictMono_int_of_lt_succ hstrictSucc
  have hboundedGap (j : ℤ) : ∃ a b : ↥C.translatedVertices,
      dist (a : Tiling.Plane) b < P.controlRadius ∧
      0 < Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) ∧
      endpoint j = Axis.coord axis (a : Tiling.Plane) ∧
      endpoint (j + 1) = Axis.coord axis (b : Tiling.Plane) := by
    obtain ⟨v, w, hu, hv, hw, hleft, hright, hpos, hinc⟩ := hgapData j
    let a : ↥C.translatedVertices := ⟨v + (sourceOwner j : Tiling.Plane),
      ⟨v, hv, (sourceOwner j : Tiling.Plane), (sourceOwner j).2, rfl⟩⟩
    let b : ↥C.translatedVertices := ⟨w + (sourceOwner j : Tiling.Plane),
      ⟨w, hw, (sourceOwner j : Tiling.Plane), (sourceOwner j).2, rfl⟩⟩
    have hvSupport : v ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure
        (IntrinsicVertices.region_vertices_subset_frontier C.region hv)
    have hwSupport : w ∈ C.region.support := by
      rw [← C.region.isPolygonal.closure_interior]
      exact frontier_subset_closure
        (IntrinsicVertices.region_vertices_subset_frontier C.region hw)
    have hdvw : dist v w ≤ Metric.diam C.region.support :=
      Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hvSupport hwSupport
    have hd : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
      change Metric.diam C.region.support = Metric.diam (interior C.region.support)
      nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
      exact Metric.diam_closure _
    have hsmall : Metric.diam C.region.support < P.scale := by
      rw [hd]
      nlinarith [hScale, (Metric.diam_nonneg :
        0 ≤ Metric.diam C.region.openCarrier)]
    refine ⟨a, b, ?_, ?_, ?_, ?_⟩
    · simpa [a, b] using hdvw.trans_lt (hsmall.trans P.scale_lt_controlRadius)
    · simpa [a, b] using hpos
    · simpa [a] using hleft
    · simpa [b] using hright
  obtain ⟨δ, hδ, hstep⟩ := exists_uniform_source_step P axis endpoint hboundedGap
  obtain ⟨htop, hbot⟩ := tendsto_int_of_uniform_step hδ hstep
  have hgap : ∀ j,
      {z : Tiling.Plane | axis.transverseCoord z = c ∧
        axis.coord z ∈ Ioo (endpoint j) (endpoint (j + 1))} ⊆
      (sourceOwner j : Tiling.Plane) +ᵥ C.region.openCarrier := by
    intro j
    obtain ⟨v, w, hu, hv, hw, hleft, hright, hpos, hinc⟩ := hgapData j
    exact hinc
  let d : ℝ := c - c₀
  have hrelative : ∀ j,
      c - axis.transverseCoord (sourceOwner j : Tiling.Plane) = d := by
    intro j
    rw [hsource _ (hsourceOwner_mem j)]
  have hd : d ∉ axis.transverseCoord '' C.region.vertices := by
    rintro ⟨v, hv, hvd⟩
    apply hgeneric
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    refine ⟨v, hv, ?_⟩
    dsimp [d] at hvd
    change axis.transverseCoord v = -c₀ + c
    linarith
  have hfibre := fibre_eq_of_uniform_generic_chain axis C.region
    (Set.image Subtype.val S) c endpoint
    (fun j => (sourceOwner j : Tiling.Plane)) (by
      intro j
      exact ⟨sourceOwner j, hsourceOwner_mem j, rfl⟩)
    hstrict htop hbot hgap d hrelative hd
  exact ⟨⟨endpoint, (fun j => (sourceOwner j : Tiling.Plane)),
    (by intro j; exact ⟨sourceOwner j, hsourceOwner_mem j, rfl⟩),
    hstrict, htop, hbot, hgap, hfibre⟩⟩

private theorem allGenericFibreChainsTransport :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres),
    IsCenterColumn axis C.region (Set.image Subtype.val S) →
    ∀ c : ℝ,
      (∀ t ∈ S, c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
        (axis.transverseCoord '' C.region.vertices)) →
      (axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = c})).Nonempty →
      ∃ cphi : ℝ, Nonempty (LabelledFibreChain axis D.deformedRegion
        (deformedCenterCarrierOn Tphi S) cphi) := by
  intro C P hScale phi hphi D Tphi hTphi axis S hColumn c hgeneric hnonempty
  obtain ⟨Gsrc⟩ := source_witnessed_chain_for_centerColumn axis S c
    hColumn hgeneric hnonempty
  let c₀ : ℝ := Classical.choose hColumn.2.2.1
  have hc₀ : ∀ z ∈ Set.image Subtype.val S,
      axis.transverseCoord z = c₀ := Classical.choose_spec hColumn.2.2.1
  obtain ⟨u, hu⟩ := hColumn.2.1
  rcases hu with ⟨s₀, hs₀, rfl⟩
  obtain ⟨cphi, _hcphi, G⟩ := allGenericFibreChainsTransport_of_witnessed
    P hScale phi hphi D Tphi hTphi axis S c c₀ hc₀ hgeneric Gsrc s₀ hs₀
  exact ⟨cphi, G⟩

private theorem full_source_fibre_transport
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (c₀ c₁ c : ℝ)
    (hsource : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀)
    (htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁)
    (hc : c ∉ c₀ +ᵥ (axis.transverseCoord '' C.region.vertices))
    (hfull : axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c}) = Set.univ) :
    axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z =
          transverseTransportHomeomorph axis D c₀ c₁ c}) = Set.univ := by
  classical
  have hSne : S.Nonempty := by
    by_contra hSne
    have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hSne
    subst S
    have hfull' : (∅ : Set ℝ) = Set.univ := by
      simpa [regularSupport, Tiling.Polygonal.regularSupport, openUnion,
        Tiling.Polygonal.openUnion] using hfull
    exact Set.empty_ne_univ hfull'
  obtain ⟨s₀, hs₀⟩ := hSne
  have hgeneric : ∀ t ∈ S,
      c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
        (axis.transverseCoord '' C.region.vertices) := by
    intro t ht hmem
    apply hc
    simpa [hsource t ht] using hmem
  have hgeneric' : ∀ t ∈ Set.image Subtype.val S,
      c ∉ axis.transverseCoord t +ᵥ
        (axis.transverseCoord '' C.region.vertices) := by
    rintro t ⟨s, hs, rfl⟩
    exact hgeneric s hs
  obtain ⟨Gsrc⟩ := witnessed_chain_of_packing_full
    (selectedSubfamily_sourcePacking P S) hgeneric' hfull
  have hc₀ : ∀ z ∈ Set.image Subtype.val S,
      axis.transverseCoord z = c₀ := by
    rintro z ⟨s, hs, rfl⟩
    exact hsource s hs
  obtain ⟨cphi, hcphi, G⟩ := allGenericFibreChainsTransport_of_witnessed
    P hScale phi hphi D Tphi hTphi axis S c c₀ hc₀ hgeneric Gsrc s₀ hs₀
  have hcphiH : cphi = transverseTransportHomeomorph axis D c₀ c₁ c := by
    rw [hcphi, transverseTransportHomeomorph_apply]
    have hs := hsource s₀ hs₀
    have ht := htarget s₀ hs₀
    cases axis with
    | horizontal =>
        have hs' : (s₀ : Tiling.Plane).im = c₀ := by
          simpa only [Axis.transverseCoord] using hs
        have ht' : (Tphi s₀).im = c₁ := by
          simpa only [Axis.transverseCoord] using ht
        change (Tphi s₀).im + (D.planarHomeomorph
            (slicePoint Axis.horizontal c 0 - (s₀ : Tiling.Plane))).im =
          c₁ + D.secondHomeomorph (c - c₀)
        rw [planarHomeomorph_im, ht']
        congr 2
        rw [Complex.sub_im, hs']
        simp only [slicePoint, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im,
          Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, zero_add]
        ring
    | vertical =>
        have hs' : (s₀ : Tiling.Plane).re = c₀ := by
          simpa only [Axis.transverseCoord] using hs
        have ht' : (Tphi s₀).re = c₁ := by
          simpa only [Axis.transverseCoord] using ht
        change (Tphi s₀).re + (D.planarHomeomorph
            (slicePoint Axis.vertical c 0 - (s₀ : Tiling.Plane))).re =
          c₁ + D.firstHomeomorph (c - c₀)
        rw [planarHomeomorph_re, ht']
        congr 2
        rw [Complex.sub_re, hs']
        simp only [slicePoint, Complex.add_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.I_re,
          Complex.I_im, mul_zero]
        ring
  rw [← hcphiH]
  exact G.some.fibre_eq

private theorem regularSupport_fibre_empty_iff_openUnion_fibre_empty
    (axis : Axis) (K : Region) (S : Set Tiling.Plane) (c c₀ : ℝ)
    (hcol : ∀ t ∈ S, axis.transverseCoord t = c₀)
    (hc : c ∉ c₀ +ᵥ (axis.transverseCoord '' K.vertices)) :
    axis.coord '' (regularSupport K S ∩
      {z | axis.transverseCoord z = c}) = ∅ ↔
    openUnion K S ∩ {z | axis.transverseCoord z = c} = ∅ := by
  let d : ℝ := c - c₀
  have hd : d ∉ axis.transverseCoord '' K.vertices := by
    rintro ⟨v, hv, hvd⟩
    apply hc
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    refine ⟨v, hv, ?_⟩
    change axis.transverseCoord v = -c₀ + c
    dsimp [d] at hvd
    linarith
  have hlocal : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - d| < ε →
      (match axis with
        | .horizontal => horizontalSlice K s
        | .vertical => verticalSlice K s) =
      (match axis with
        | .horizontal => horizontalSlice K d
        | .vertical => verticalSlice K d) := by
    cases axis with
    | horizontal =>
        have hd' : d ∉ Finset.image Complex.im K.vertexFinset := by
          intro hd'
          obtain ⟨v, hv, hvd⟩ := Finset.mem_image.mp hd'
          apply hd
          refine ⟨v, ?_, hvd⟩
          change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
          rw [K.coe_vertexFinset] at hv
          exact hv
        simpa using horizontalSlice_locallyConstant K hd'
    | vertical =>
        have hd' : d ∉ Finset.image Complex.re K.vertexFinset := by
          intro hd'
          obtain ⟨v, hv, hvd⟩ := Finset.mem_image.mp hd'
          apply hd
          refine ⟨v, ?_, hvd⟩
          change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
          rw [K.coe_vertexFinset] at hv
          exact hv
        simpa using verticalSlice_locallyConstant K hd'
  obtain ⟨ε, hε, hslice⟩ := hlocal
  have hopen : IsOpen (openUnion K S) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
    exact isOpen_iUnion fun t => isOpen_interior.vadd (t : Tiling.Plane)
  constructor
  · intro hreg
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hzreg : z ∈ regularSupport K S :=
      hopen.subset_interior_closure hz.1
    have hzimage : axis.coord z ∈ axis.coord ''
        (regularSupport K S ∩ {w | axis.transverseCoord w = c}) :=
      ⟨z, ⟨hzreg, hz.2⟩, rfl⟩
    rw [hreg] at hzimage
    exact hzimage
  · intro hraw
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hztrans : axis.transverseCoord z = c := hz.2
    have hstrip : ∀ r : ℝ, |r - c| < ε →
        openUnion K S ∩ {w | axis.transverseCoord w = r} = ∅ := by
      intro r hrc
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hwopen := hw.1
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hwopen
      obtain ⟨t, hwt⟩ := hwopen
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hwt
      have hrel : |(r - axis.transverseCoord (t : Tiling.Plane)) - d| < ε := by
        rw [hcol t t.2]
        dsimp [d]
        convert hrc using 1
        ring
      have hs := hslice (r - axis.transverseCoord (t : Tiling.Plane)) hrel
      let w₀ := axisPoint axis (axis.coord w) c
      have hw₀tile : w₀ ∈ (t : Tiling.Plane) +ᵥ K.openCarrier := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        cases axis with
        | horizontal =>
            have hwmem : (-(t : Tiling.Plane) + w).re ∈
                horizontalSlice K (r - (t : Tiling.Plane).im) := by
              have hwline : w.im = r := by
                have hwline := hw.2
                change w.im = r at hwline
                exact hwline
              change Complex.mk ((-(t : Tiling.Plane) + w).re)
                (r - (t : Tiling.Plane).im) ∈ K.openCarrier
              convert hwt using 1
              apply Complex.ext
              · rfl
              · change r - (t : Tiling.Plane).im =
                  -(t : Tiling.Plane).im + w.im
                rw [hwline]
                ring
            have hs' : horizontalSlice K
                (r - (t : Tiling.Plane).im) = horizontalSlice K d := by
              simpa only [Axis.transverseCoord] using hs
            have hwmemd : (-(t : Tiling.Plane) + w).re ∈
                horizontalSlice K d := by
              rw [← hs']
              exact hwmem
            have htcol : (t : Tiling.Plane).im = c₀ := by
              simpa [Axis.transverseCoord] using hcol t t.2
            have hwmemc : (-(t : Tiling.Plane) + w).re ∈
                horizontalSlice K (c - (t : Tiling.Plane).im) := by
              simpa [d, htcol]
                using hwmemd
            have hpoint : -(t : Tiling.Plane) +ᵥ w₀ =
                Complex.mk ((-(t : Tiling.Plane) + w).re)
                  (c - (t : Tiling.Plane).im) := by
              apply Complex.ext
              · simp [w₀, axisPoint, Axis.coord, vadd_eq_add]
              · simp [w₀, axisPoint, Axis.coord, vadd_eq_add]
                ring
            rw [hpoint]
            exact hwmemc
        | vertical =>
            have hwmem : (-(t : Tiling.Plane) + w).im ∈
                verticalSlice K (r - (t : Tiling.Plane).re) := by
              have hwline : w.re = r := by
                have hwline := hw.2
                change w.re = r at hwline
                exact hwline
              change Complex.mk (r - (t : Tiling.Plane).re)
                ((-(t : Tiling.Plane) + w).im) ∈ K.openCarrier
              convert hwt using 1
              apply Complex.ext
              · change r - (t : Tiling.Plane).re =
                  -(t : Tiling.Plane).re + w.re
                rw [hwline]
                ring
              · rfl
            have hs' : verticalSlice K
                (r - (t : Tiling.Plane).re) = verticalSlice K d := by
              simpa only [Axis.transverseCoord] using hs
            have hwmemd : (-(t : Tiling.Plane) + w).im ∈
                verticalSlice K d := by
              rw [← hs']
              exact hwmem
            have htcol : (t : Tiling.Plane).re = c₀ := by
              simpa [Axis.transverseCoord] using hcol t t.2
            have hwmemc : (-(t : Tiling.Plane) + w).im ∈
                verticalSlice K (c - (t : Tiling.Plane).re) := by
              simpa [d, htcol]
                using hwmemd
            have hpoint : -(t : Tiling.Plane) +ᵥ w₀ =
                Complex.mk (c - (t : Tiling.Plane).re)
                  ((-(t : Tiling.Plane) + w).im) := by
              apply Complex.ext
              · simp [w₀, axisPoint, Axis.coord, vadd_eq_add]
                ring
              · simp [w₀, axisPoint, Axis.coord, vadd_eq_add]
            rw [hpoint]
            exact hwmemc
      have hw₀open : w₀ ∈ openUnion K S := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
        exact ⟨t, hw₀tile⟩
      have hw₀line : axis.transverseCoord w₀ = c :=
        axisPoint_transverseCoord axis _ _
      have hempty : w₀ ∈ openUnion K S ∩
          {q | axis.transverseCoord q = c} := ⟨hw₀open, hw₀line⟩
      rw [hraw] at hempty
      exact hempty
    have hball : Metric.ball z (ε / 2) ∩ openUnion K S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hcoordle := axis_transverse_le_dist axis w z
      rw [hztrans] at hcoordle
      have hclose : |axis.transverseCoord w - c| < ε :=
        hcoordle.trans_lt (lt_trans (by
          simpa [Metric.mem_ball, dist_comm] using hw.1) (by linarith))
      have hwstrip : w ∈ openUnion K S ∩
          {q | axis.transverseCoord q = axis.transverseCoord w} := ⟨hw.2, rfl⟩
      rw [hstrip _ hclose] at hwstrip
      exact hwstrip
    have hznotcl : z ∉ closure (openUnion K S) := by
      intro hzcl
      rw [Metric.mem_closure_iff] at hzcl
      obtain ⟨w, hwopen, hwdist⟩ := hzcl (ε / 2) (by linarith)
      have hwball : w ∈ Metric.ball z (ε / 2) := by
        simpa only [Metric.mem_ball, dist_comm] using hwdist
      have hempty : w ∈ Metric.ball z (ε / 2) ∩ openUnion K S :=
        ⟨hwball, hwopen⟩
      rw [hball] at hempty
      exact hempty
    exact hznotcl (interior_subset hz.1)

private theorem openUnion_fibre_empty_transport
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (S : Set ↥C.centres) (c₀ c₁ c : ℝ)
    (hsource : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀)
    (htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁) :
    openUnion C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = c} = ∅ ↔
      openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z =
          transverseTransportHomeomorph axis D c₀ c₁ c} = ∅ := by
  let H := transverseTransportHomeomorph axis D c₀ c₁
  have hforward : (openUnion C.region (Set.image Subtype.val S) ∩
      {z | axis.transverseCoord z = c}).Nonempty →
      (openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z = H c}).Nonempty := by
    rintro ⟨z, hzopen, hzline⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzopen
    obtain ⟨t, hzt⟩ := hzopen
    rcases t.property with ⟨s, hs, hst⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
    let k := -(t : Tiling.Plane) + z
    let y := Tphi s + D.planarHomeomorph k
    refine ⟨y, ?_, ?_⟩
    · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      let ts : ↥(deformedCenterCarrierOn Tphi S) :=
        ⟨Tphi s, ⟨s, hs, rfl⟩⟩
      refine ⟨ts, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier]
      refine ⟨k, ?_, ?_⟩
      · simpa [k, hst] using hzt
      · simp [ts, y]
    · rw [transverseTransportHomeomorph_apply]
      have hscoord := hsource s hs
      have htcoord := htarget s hs
      have hstcoord := congrArg (axis.transverseCoord) hst
      change axis.transverseCoord y = _
      cases axis with
      | horizontal =>
          dsimp only [y]
          change (Tphi s).im + (D.planarHomeomorph k).im =
            c₁ + D.secondHomeomorph (c - c₀)
          rw [planarHomeomorph_im]
          rw [show (Tphi s).im = c₁ by simpa [Axis.transverseCoord] using htcoord]
          congr 1
          apply congrArg D.secondHomeomorph
          dsimp [k]
          have hzcoord : z.im = c := by
            simpa [Axis.transverseCoord] using hzline
          have hscoord' : (s : Tiling.Plane).im = c₀ := by
            simpa [Axis.transverseCoord] using hscoord
          have hstcoord' : (s : Tiling.Plane).im = (t : Tiling.Plane).im :=
            congrArg Complex.im hst
          linarith
      | vertical =>
          dsimp only [y]
          change (Tphi s).re + (D.planarHomeomorph k).re =
            c₁ + D.firstHomeomorph (c - c₀)
          rw [planarHomeomorph_re]
          rw [show (Tphi s).re = c₁ by simpa [Axis.transverseCoord] using htcoord]
          congr 1
          apply congrArg D.firstHomeomorph
          dsimp [k]
          have hzcoord : z.re = c := by
            simpa [Axis.transverseCoord] using hzline
          have hscoord' : (s : Tiling.Plane).re = c₀ := by
            simpa [Axis.transverseCoord] using hscoord
          have hstcoord' : (s : Tiling.Plane).re = (t : Tiling.Plane).re :=
            congrArg Complex.re hst
          linarith
  have hback : (openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) ∩
      {z | axis.transverseCoord z = H c}).Nonempty →
      (openUnion C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = c}).Nonempty := by
    rintro ⟨y, hyopen, hyline⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hyopen
    obtain ⟨t, hyt⟩ := hyopen
    rcases t.property with ⟨s, hs, hst⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier] at hyt
    obtain ⟨k, hk, hkmap⟩ := hyt
    let z := (s : Tiling.Plane) + k
    refine ⟨z, ?_, ?_⟩
    · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      let ts : ↥(Set.image Subtype.val S) :=
        ⟨(s : Tiling.Plane), ⟨s, hs, rfl⟩⟩
      refine ⟨ts, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [ts, z] using hk
    · have hscoord := hsource s hs
      have htcoord := htarget s hs
      have hkmap' : D.planarHomeomorph k =
          -(t : Tiling.Plane) + y := by
        simpa only [vadd_eq_add] using hkmap
      have hyEq : y = Tphi s + D.planarHomeomorph k := by
        calc
          y = (t : Tiling.Plane) + (-(t : Tiling.Plane) + y) := by abel
          _ = (t : Tiling.Plane) + D.planarHomeomorph k := by rw [← hkmap']
          _ = Tphi s + D.planarHomeomorph k := by rw [hst]
      rw [hyEq, transverseTransportHomeomorph_apply] at hyline
      change axis.transverseCoord z = c
      cases axis with
      | horizontal =>
          change (Tphi s + D.planarHomeomorph k).im =
            c₁ + D.secondHomeomorph (c - c₀) at hyline
          rw [Complex.add_im, planarHomeomorph_im] at hyline
          have hkcoord : k.im = c - c₀ := by
            apply D.secondHomeomorph.injective
            have ht' : (Tphi s).im = c₁ := by
              simpa only [Axis.transverseCoord] using htcoord
            rw [ht'] at hyline
            exact add_left_cancel hyline
          have hs' : (s : Tiling.Plane).im = c₀ := by
            simpa only [Axis.transverseCoord] using hscoord
          change (s : Tiling.Plane).im + k.im = c
          rw [hs', hkcoord]
          ring
      | vertical =>
          change (Tphi s + D.planarHomeomorph k).re =
            c₁ + D.firstHomeomorph (c - c₀) at hyline
          rw [Complex.add_re, planarHomeomorph_re] at hyline
          have hkcoord : k.re = c - c₀ := by
            apply D.firstHomeomorph.injective
            have ht' : (Tphi s).re = c₁ := by
              simpa only [Axis.transverseCoord] using htcoord
            rw [ht'] at hyline
            exact add_left_cancel hyline
          have hs' : (s : Tiling.Plane).re = c₀ := by
            simpa only [Axis.transverseCoord] using hscoord
          change (s : Tiling.Plane).re + k.re = c
          rw [hs', hkcoord]
          ring
  change openUnion C.region (Set.image Subtype.val S) ∩
      {z | axis.transverseCoord z = c} = ∅ ↔
    openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) ∩
      {z | axis.transverseCoord z = H c} = ∅
  constructor
  · intro hsEmpty
    apply Set.not_nonempty_iff_eq_empty.mp
    intro htne
    exact Set.not_nonempty_iff_eq_empty.mpr hsEmpty (hback htne)
  · intro htEmpty
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hsne
    exact Set.not_nonempty_iff_eq_empty.mpr htEmpty (hforward hsne)

private theorem empty_fibre_transport
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (S : Set ↥C.centres) (c₀ c₁ c : ℝ)
    (hsource : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀)
    (htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁)
    (hc : c ∉ c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)) :
    axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = c}) = ∅ ↔
      axis.coord '' (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z =
          transverseTransportHomeomorph axis D c₀ c₁ c}) = ∅ := by
  let H := transverseTransportHomeomorph axis D c₀ c₁
  have hsourceCol : ∀ t ∈ Set.image Subtype.val S,
      axis.transverseCoord t = c₀ := by
    rintro t ⟨s, hs, rfl⟩
    exact hsource s hs
  have htargetCol : ∀ t ∈ deformedCenterCarrierOn Tphi S,
      axis.transverseCoord t = c₁ := by
    rintro t ⟨s, hs, rfl⟩
    exact htarget s hs
  have htgeneric : H c ∉
      c₁ +ᵥ (axis.transverseCoord '' D.deformedRegion.vertices) := by
    rw [deformed_transverse_vertices_eq_mapped phi D axis]
    intro hm
    have hm' : H c ∈ H ''
        (c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)) := by
      rw [transverseTransport_levels phi D axis c₀ c₁]
      exact hm
    obtain ⟨x, hx, hxc⟩ := hm'
    exact hc (H.injective hxc ▸ hx)
  rw [regularSupport_fibre_empty_iff_openUnion_fibre_empty
      axis C.region (Set.image Subtype.val S) c c₀ hsourceCol hc,
    regularSupport_fibre_empty_iff_openUnion_fibre_empty
      axis D.deformedRegion (deformedCenterCarrierOn Tphi S)
      (H c) c₁ htargetCol htgeneric]
  exact openUnion_fibre_empty_transport phi D Tphi axis S c₀ c₁ c
    hsource htarget

private theorem full_target_fibre_reflect
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (c₀ c₁ c : ℝ)
    (hsource : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀)
    (htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁)
    (hc : c ∉ c₀ +ᵥ (axis.transverseCoord '' C.region.vertices))
    (hfull : axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z =
          transverseTransportHomeomorph axis D c₀ c₁ c}) = Set.univ) :
    axis.coord '' (regularSupport C.region
      (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c}) =
        Set.univ := by
  let H := transverseTransportHomeomorph axis D c₀ c₁
  have htargetGeneric : H c ∉
      c₁ +ᵥ mappedTransverseVertexLevels axis phi := by
    intro hm
    have hm' : H c ∈ H ''
        (c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)) := by
      rw [transverseTransport_levels phi D axis c₀ c₁]
      exact hm
    obtain ⟨x, hx, hxc⟩ := hm'
    have : x = c := H.injective hxc
    exact hc (this ▸ hx)
  have hgeneric' : ∀ t ∈ deformedCenterCarrierOn Tphi S,
      H c ∉ axis.transverseCoord t +ᵥ
        (axis.transverseCoord '' D.deformedRegion.vertices) := by
    rintro t ⟨s, hs, rfl⟩ hm
    apply htargetGeneric
    rw [← deformed_transverse_vertices_eq_mapped phi D axis]
    simpa [htarget s hs] using hm
  have hsourcePacking := selectedSubfamily_sourcePacking P S
  have htargetPacking := selectedSubfamily_packingTransport
    P hScale phi hphi D Tphi hTphi S hsourcePacking
  obtain ⟨Gtgt⟩ := witnessed_chain_of_packing_full
    htargetPacking hgeneric' hfull
  obtain ⟨Gsrc⟩ := allGenericFibreChainsReflect_of_witnessed
    P hScale phi hphi D Tphi hTphi axis S c (H c) c₀ c₁
    hsource htarget rfl hc Gtgt
  exact Gsrc.fibre_eq

private theorem transverseGridCellTransportData_exists :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hsource : ∃ c, ∀ t ∈ S, axis.transverseCoord (t : Tiling.Plane) = c)
    (htarget : ∃ c, ∀ t ∈ S, axis.transverseCoord (Tphi t) = c),
    Nonempty (TransverseGridCellTransportData C axis phi D Tphi S) := by
  intro C P hScale phi hphi D Tphi hTphi axis S hsource htarget
  classical
  let c₀ : ℝ := Classical.choose hsource
  let c₁ : ℝ := Classical.choose htarget
  have hscol : ∀ t ∈ S,
      axis.transverseCoord (t : Tiling.Plane) = c₀ :=
    Classical.choose_spec hsource
  have htcol : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁ :=
    Classical.choose_spec htarget
  let L : Set ℝ := c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)
  let M : Set ℝ := c₁ +ᵥ mappedTransverseVertexLevels axis phi
  let H : ℝ ≃ₜ ℝ := transverseTransportHomeomorph axis D c₀ c₁
  have hVfinite : C.region.vertices.Finite := by
    rw [C.region.vertices_eq_vertexSet]
    exact C.region.isPolygonal.vertexSet_finite
  have hLfinite : L.Finite := by
    dsimp [L]
    simpa only [Set.singleton_vadd] using
      (Set.finite_singleton c₀).vadd (hVfinite.image axis.transverseCoord)
  have hLM : H '' L = M :=
    transverseTransport_levels phi D axis c₀ c₁
  have hMfinite : M.Finite := by
    rw [← hLM]
    exact hLfinite.image H
  let levelEquiv : ↥L ≃ ↥M := {
    toFun x := ⟨H x.1, hLM ▸ ⟨x.1, x.2, rfl⟩⟩
    invFun y := ⟨H.symm y.1, by
      have hy : y.1 ∈ H '' L := hLM.symm ▸ y.2
      obtain ⟨x, hx, hxy⟩ := hy
      have : H.symm y.1 = x := by rw [← hxy, H.symm_apply_apply]
      exact this ▸ hx⟩
    left_inv x := by apply Subtype.ext; exact H.symm_apply_apply x.1
    right_inv y := by apply Subtype.ext; exact H.apply_symm_apply y.1 }
  let sourceCells : Set (Set ℝ) := {J | IsTransverseGridCell L J}
  let targetCells : Set (Set ℝ) := {J | IsTransverseGridCell M J}
  let cellEquiv : ↥sourceCells ≃ ↥targetCells := gridCellEquiv H hLM
  refine ⟨⟨c₀, c₁, hscol, htcol, L, M, rfl, rfl,
    hLfinite, hMfinite, levelEquiv, ?_, sourceCells, targetCells,
    rfl, rfl, gridCells_finite hLfinite, gridCells_finite hMfinite,
    H, transverseTransportHomeomorph_strictMono axis D c₀ c₁,
    ?_, cellEquiv, ?_, ?_, ?_, ?_⟩⟩
  · intro x v hv hx
    change H x.1 = _
    rw [hx]
    exact transverseTransportHomeomorph_vertex phi D axis c₀ c₁ v hv
  · exact transverseTransportHomeomorph_vertex phi D axis c₀ c₁
  · intro A
    rfl
  · intro A B hAB a ha b hb hab a' ha' b' hb'
    obtain ⟨x, hxA, rfl⟩ := ha'
    obtain ⟨y, hyB, rfl⟩ := hb'
    apply transverseTransportHomeomorph_strictMono axis D c₀ c₁
    exact distinct_gridCells_order hLfinite A.2 B.2
      (fun h => hAB (Subtype.ext h)) ha hb hab x hxA y hyB
  · intro A
    constructor
    · intro hfull c' hc'
      obtain ⟨c, hcA, rfl⟩ := hc'
      have hAcell : IsTransverseGridCell L A.1 := A.2
      have hcgeneric : c ∉ L := by
        intro hcL
        exact Set.disjoint_left.1 hAcell.2.2.2.1 hcA hcL
      exact full_source_fibre_transport P hScale phi hphi D Tphi hTphi
        axis S c₀ c₁ c hscol htcol hcgeneric (hfull c hcA)
    · intro hfull c hcA
      have hAcell : IsTransverseGridCell L A.1 := A.2
      have hcgeneric : c ∉ L := by
        intro hcL
        exact Set.disjoint_left.1 hAcell.2.2.2.1 hcA hcL
      apply full_target_fibre_reflect P hScale phi hphi D Tphi hTphi
        axis S c₀ c₁ c hscol htcol hcgeneric
      exact hfull (H c) ⟨c, hcA, rfl⟩
  · intro A
    constructor
    · intro hempty c' hc'
      obtain ⟨c, hcA, rfl⟩ := hc'
      have hAcell : IsTransverseGridCell L A.1 := A.2
      have hcgeneric : c ∉ L := by
        intro hcL
        exact Set.disjoint_left.1 hAcell.2.2.2.1 hcA hcL
      exact (empty_fibre_transport phi D Tphi axis S c₀ c₁ c
        hscol htcol hcgeneric).mp (hempty c hcA)
    · intro hempty c hcA
      have hAcell : IsTransverseGridCell L A.1 := A.2
      have hcgeneric : c ∉ L := by
        intro hcL
        exact Set.disjoint_left.1 hAcell.2.2.2.1 hcA hcL
      exact (empty_fibre_transport phi D Tphi axis S c₀ c₁ c
        hscol htcol hcgeneric).mpr (hempty (H c) ⟨c, hcA, rfl⟩)

private theorem slice_eq_of_mem_gridCell
    (axis : Axis) (K : Region) (c₀ : ℝ) {J : Set ℝ}
    (hJ : IsTransverseGridCell
      (c₀ +ᵥ (axis.transverseCoord '' K.vertices)) J)
    {c r : ℝ} (hc : c ∈ J) (hr : r ∈ J) :
    (match axis with
      | .horizontal => horizontalSlice K (c - c₀)
      | .vertical => verticalSlice K (c - c₀)) =
    (match axis with
      | .horizontal => horizontalSlice K (r - c₀)
      | .vertical => verticalSlice K (r - c₀)) := by
  let F : ↥J → Set ℝ := fun q => match axis with
    | .horizontal => horizontalSlice K (q.1 - c₀)
    | .vertical => verticalSlice K (q.1 - c₀)
  let E : Set ↥J := {q | F q = F ⟨c, hc⟩}
  have hgeneric (q : ↥J) : q.1 - c₀ ∉
      axis.transverseCoord '' K.vertices := by
    intro hq
    have hlevel : q.1 ∈
        c₀ +ᵥ (axis.transverseCoord '' K.vertices) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [sub_eq_add_neg, add_comm] using hq
    exact Set.disjoint_left.1 hJ.2.2.2.1 q.2 hlevel
  have hloc (q : ↥J) : ∃ ε : ℝ, 0 < ε ∧
      ∀ s : ↥J, dist s q < ε → F s = F q := by
    cases axis with
    | horizontal =>
        have hq' : q.1 - c₀ ∉ Finset.image Complex.im K.vertexFinset := by
          intro hq'
          obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq'
          apply hgeneric q
          refine ⟨v, ?_, hvq⟩
          change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
          rw [K.coe_vertexFinset] at hv
          exact hv
        obtain ⟨ε, hε, hs⟩ := horizontalSlice_locallyConstant K hq'
        refine ⟨ε, hε, ?_⟩
        intro s hsq
        change dist (s.1 : ℝ) q.1 < ε at hsq
        have habs : |(s.1 - c₀) - (q.1 - c₀)| < ε := by
          rw [show (s.1 - c₀) - (q.1 - c₀) = s.1 - q.1 by ring]
          simpa only [Real.dist_eq] using hsq
        simpa only [F] using hs (s.1 - c₀) habs
    | vertical =>
        have hq' : q.1 - c₀ ∉ Finset.image Complex.re K.vertexFinset := by
          intro hq'
          obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq'
          apply hgeneric q
          refine ⟨v, ?_, hvq⟩
          change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
          rw [K.coe_vertexFinset] at hv
          exact hv
        obtain ⟨ε, hε, hs⟩ := verticalSlice_locallyConstant K hq'
        refine ⟨ε, hε, ?_⟩
        intro s hsq
        change dist (s.1 : ℝ) q.1 < ε at hsq
        have habs : |(s.1 - c₀) - (q.1 - c₀)| < ε := by
          rw [show (s.1 - c₀) - (q.1 - c₀) = s.1 - q.1 by ring]
          simpa only [Real.dist_eq] using hsq
        simpa only [F] using hs (s.1 - c₀) habs
  have hopenE : IsOpen E := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨ε, hε, hqε⟩ := hloc q
    apply Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    intro s hs
    change F s = F ⟨c, hc⟩
    exact (hqε s (by simpa only [Metric.mem_ball] using hs)).trans hq
  have hopenEc : IsOpen Eᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    obtain ⟨ε, hε, hqε⟩ := hloc q
    apply Filter.mem_of_superset
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε))
    intro s hs hse
    apply hq
    change F q ≠ F ⟨c, hc⟩ at hq
    change F s = F ⟨c, hc⟩ at hse
    exact (hqε s (by simpa only [Metric.mem_ball] using hs)).symm.trans hse
  have hclopen : IsClopen E := ⟨by
    simpa using hopenEc.isClosed_compl, hopenE⟩
  let _ : PreconnectedSpace ↥J := Subtype.preconnectedSpace hJ.2.1
  have hEuniv : E = Set.univ := hclopen.eq_univ ⟨⟨c, hc⟩, rfl⟩
  have hrE : (⟨r, hr⟩ : ↥J) ∈ E := by rw [hEuniv]; trivial
  cases axis <;> simpa only [E, F] using hrE.symm

private theorem openUnion_fibre_nonempty_iff_slice_nonempty
    (axis : Axis) (K : Region) (S : Set Tiling.Plane) (c c₀ : ℝ)
    (hSne : S.Nonempty)
    (hcol : ∀ t ∈ S, axis.transverseCoord t = c₀) :
    (openUnion K S ∩ {z | axis.transverseCoord z = c}).Nonempty ↔
      (match axis with
        | .horizontal => horizontalSlice K (c - c₀)
        | .vertical => verticalSlice K (c - c₀)).Nonempty := by
  obtain ⟨t₀, ht₀⟩ := hSne
  cases axis with
  | horizontal =>
      constructor
      · rintro ⟨z, hzopen, hzline⟩
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzopen
        obtain ⟨t, hzt⟩ := hzopen
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
        refine ⟨(-(t : Tiling.Plane) + z).re, ?_⟩
        change Complex.mk ((-(t : Tiling.Plane) + z).re) (c - c₀) ∈
          K.openCarrier
        convert hzt using 1
        apply Complex.ext
        · rfl
        · have hz' : z.im = c := by
            change z.im = c at hzline
            exact hzline
          have ht' : (t : Tiling.Plane).im = c₀ := by
            simpa only [Axis.transverseCoord] using hcol t t.2
          change c - c₀ = -(t : Tiling.Plane).im + z.im
          rw [hz', ht']
          ring
      · rintro ⟨x, hx⟩
        change Complex.mk x (c - c₀) ∈ K.openCarrier at hx
        let p : Tiling.Plane := Complex.mk x (c - c₀)
        let z : Tiling.Plane := (t₀ : Tiling.Plane) + p
        refine ⟨z, ?_, ?_⟩
        · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
          refine ⟨⟨t₀, ht₀⟩, ?_⟩
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [z, p, vadd_eq_add] using hx
        · change z.im = c
          have ht' : (t₀ : Tiling.Plane).im = c₀ := by
            simpa only [Axis.transverseCoord] using hcol t₀ ht₀
          simp only [z, p, Complex.add_im]
          rw [ht']
          ring
  | vertical =>
      constructor
      · rintro ⟨z, hzopen, hzline⟩
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzopen
        obtain ⟨t, hzt⟩ := hzopen
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
        refine ⟨(-(t : Tiling.Plane) + z).im, ?_⟩
        change Complex.mk (c - c₀) ((-(t : Tiling.Plane) + z).im) ∈
          K.openCarrier
        convert hzt using 1
        apply Complex.ext
        · have hz' : z.re = c := by
            change z.re = c at hzline
            exact hzline
          have ht' : (t : Tiling.Plane).re = c₀ := by
            simpa only [Axis.transverseCoord] using hcol t t.2
          change c - c₀ = -(t : Tiling.Plane).re + z.re
          rw [hz', ht']
          ring
        · rfl
      · rintro ⟨x, hx⟩
        change Complex.mk (c - c₀) x ∈ K.openCarrier at hx
        let p : Tiling.Plane := Complex.mk (c - c₀) x
        let z : Tiling.Plane := (t₀ : Tiling.Plane) + p
        refine ⟨z, ?_, ?_⟩
        · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
          refine ⟨⟨t₀, ht₀⟩, ?_⟩
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [z, p, vadd_eq_add] using hx
        · change z.re = c
          have ht' : (t₀ : Tiling.Plane).re = c₀ := by
            simpa only [Axis.transverseCoord] using hcol t₀ ht₀
          simp only [z, p, Complex.add_re]
          rw [ht']
          ring

private theorem regularSupport_fibre_empty_iff_of_mem_gridCell
    (axis : Axis) (K : Region) (S : Set Tiling.Plane) (c₀ : ℝ) {J : Set ℝ}
    (hSne : S.Nonempty) (hcol : ∀ t ∈ S, axis.transverseCoord t = c₀)
    (hJ : IsTransverseGridCell
      (c₀ +ᵥ (axis.transverseCoord '' K.vertices)) J)
    {c r : ℝ} (hc : c ∈ J) (hr : r ∈ J) :
    axis.coord '' (regularSupport K S ∩
        {z | axis.transverseCoord z = c}) = ∅ ↔
      axis.coord '' (regularSupport K S ∩
        {z | axis.transverseCoord z = r}) = ∅ := by
  cases axis with
  | horizontal =>
      have hcgen : c ∉ c₀ +ᵥ (Complex.im '' K.vertices) := by
        intro hcL
        exact Set.disjoint_left.1 hJ.2.2.2.1 hc hcL
      have hrgen : r ∉ c₀ +ᵥ (Complex.im '' K.vertices) := by
        intro hrL
        exact Set.disjoint_left.1 hJ.2.2.2.1 hr hrL
      rw [regularSupport_fibre_empty_iff_openUnion_fibre_empty
          Axis.horizontal K S c c₀ hcol hcgen,
        regularSupport_fibre_empty_iff_openUnion_fibre_empty
          Axis.horizontal K S r c₀ hcol hrgen]
      have hslice : horizontalSlice K (c - c₀) =
          horizontalSlice K (r - c₀) := by
        simpa only using slice_eq_of_mem_gridCell
          Axis.horizontal K c₀ hJ hc hr
      have hcne := openUnion_fibre_nonempty_iff_slice_nonempty
        Axis.horizontal K S c c₀ hSne hcol
      have hrne := openUnion_fibre_nonempty_iff_slice_nonempty
        Axis.horizontal K S r c₀ hSne hcol
      constructor
      · intro hcempty
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hrnonempty
        have hrslice := hrne.mp hrnonempty
        have hcslice : (horizontalSlice K (c - c₀)).Nonempty := by
          rw [hslice]
          exact hrslice
        exact Set.not_nonempty_iff_eq_empty.mpr hcempty (hcne.mpr hcslice)
      · intro hrempty
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hcnonempty
        have hcslice := hcne.mp hcnonempty
        have hrslice : (horizontalSlice K (r - c₀)).Nonempty := by
          rw [← hslice]
          exact hcslice
        exact Set.not_nonempty_iff_eq_empty.mpr hrempty (hrne.mpr hrslice)
  | vertical =>
      have hcgen : c ∉ c₀ +ᵥ (Complex.re '' K.vertices) := by
        intro hcL
        exact Set.disjoint_left.1 hJ.2.2.2.1 hc hcL
      have hrgen : r ∉ c₀ +ᵥ (Complex.re '' K.vertices) := by
        intro hrL
        exact Set.disjoint_left.1 hJ.2.2.2.1 hr hrL
      rw [regularSupport_fibre_empty_iff_openUnion_fibre_empty
          Axis.vertical K S c c₀ hcol hcgen,
        regularSupport_fibre_empty_iff_openUnion_fibre_empty
          Axis.vertical K S r c₀ hcol hrgen]
      have hslice : verticalSlice K (c - c₀) =
          verticalSlice K (r - c₀) := by
        simpa only using slice_eq_of_mem_gridCell
          Axis.vertical K c₀ hJ hc hr
      have hcne := openUnion_fibre_nonempty_iff_slice_nonempty
        Axis.vertical K S c c₀ hSne hcol
      have hrne := openUnion_fibre_nonempty_iff_slice_nonempty
        Axis.vertical K S r c₀ hSne hcol
      constructor
      · intro hcempty
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hrnonempty
        have hrslice := hrne.mp hrnonempty
        have hcslice : (verticalSlice K (c - c₀)).Nonempty := by
          rw [hslice]
          exact hrslice
        exact Set.not_nonempty_iff_eq_empty.mpr hcempty (hcne.mpr hcslice)
      · intro hrempty
        apply Set.not_nonempty_iff_eq_empty.mp
        intro hcnonempty
        have hcslice := hcne.mp hcnonempty
        have hrslice : (verticalSlice K (r - c₀)).Nonempty := by
          rw [← hslice]
          exact hcslice
        exact Set.not_nonempty_iff_eq_empty.mpr hrempty (hrne.mpr hrslice)

private theorem everyTargetGenericFibre_chain :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (G : TransverseGridCellTransportData C axis phi D Tphi S),
    IsCenterColumn axis C.region (Set.image Subtype.val S) →
    ∀ A : ↥G.targetCells, ∀ c ∈ A.1,
      (axis.coord '' (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S) ∩
          {z | axis.transverseCoord z = c})).Nonempty →
      Nonempty (LabelledFibreChain axis D.deformedRegion
        (deformedCenterCarrierOn Tphi S) c) := by
  intro C P hScale phi hphi D Tphi hTphi axis S G hC A c hcA hcnonempty
  classical
  let B : ↥G.sourceCells := G.cellEquiv.symm A
  have hBA : G.cellEquiv B = A := G.cellEquiv.apply_symm_apply A
  have hcImage : c ∈ (G.cellEquiv B).1 := by
    rw [hBA]
    exact hcA
  have hBcell : IsTransverseGridCell G.sourceLevels B.1 := by
    exact (Set.ext_iff.mp G.sourceCells_eq B.1).mp B.2
  have hBcell' : IsTransverseGridCell
      (G.sourceCentreCoordinate +ᵥ
        (axis.transverseCoord '' C.region.vertices)) B.1 := by
    rw [← G.sourceLevels_eq]
    exact hBcell
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := hC.2.1
    obtain ⟨s, hs, _⟩ := hz
    exact ⟨s, hs⟩
  have hnotAllEmpty : ¬ ∀ q ∈ B.1,
      axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = q}) = ∅ := by
    intro hsourceEmpty
    have htargetEmpty := (G.empty_iff B).mp hsourceEmpty
    have hcempty := htargetEmpty c hcImage
    rw [hcempty] at hcnonempty
    exact Set.not_nonempty_empty hcnonempty
  have hexistsSource : ∃ q ∈ B.1,
      axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = q}) ≠ ∅ := by
    by_contra hexists
    apply hnotAllEmpty
    intro q hq
    by_contra hqempty
    exact (not_exists.mp hexists q) ⟨hq, hqempty⟩
  obtain ⟨q, hqB, hqnonempty⟩ := hexistsSource
  have hsourceFull : ∀ r ∈ B.1,
      axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = r}) = Set.univ := by
    intro r hrB
    have hemptyIff := regularSupport_fibre_empty_iff_of_mem_gridCell
      axis C.region (Set.image Subtype.val S) G.sourceCentreCoordinate
      hC.2.1
      (by
        rintro z ⟨s, hs, rfl⟩
        exact G.source_collinear s hs)
      hBcell' hqB hrB
    have hrnonempty : axis.coord ''
        (regularSupport C.region (Set.image Subtype.val S) ∩
          {z | axis.transverseCoord z = r}) ≠ ∅ := by
      intro hrempty
      exact hqnonempty (hemptyIff.mpr hrempty)
    rcases centerColumn_fullSections axis C.region
      (Set.image Subtype.val S) hC r with hfull | hempty
    · exact hfull
    · exact False.elim (hrnonempty hempty)
  have htargetFull := (G.occupied_iff B).mp hsourceFull
  have hcfull := htargetFull c hcImage
  have hAcell : IsTransverseGridCell G.targetLevels A.1 := by
    exact (Set.ext_iff.mp G.targetCells_eq A.1).mp A.2
  have hcTargetLevel : c ∉ G.targetLevels := by
    intro hcL
    exact Set.disjoint_left.1 hAcell.2.2.2.1 hcA hcL
  have hgeneric : ∀ t ∈ deformedCenterCarrierOn Tphi S,
      c ∉ axis.transverseCoord t +ᵥ
        (axis.transverseCoord '' D.deformedRegion.vertices) := by
    rintro t ⟨s, hs, rfl⟩ hm
    apply hcTargetLevel
    rw [G.targetLevels_eq,
      ← deformed_transverse_vertices_eq_mapped phi D axis]
    simpa [G.target_collinear s hs] using hm
  have hsourcePacking := selectedSubfamily_sourcePacking P S
  have htargetPacking := selectedSubfamily_packingTransport
    P hScale phi hphi D Tphi hTphi S hsourcePacking
  obtain ⟨Gtgt⟩ := witnessed_chain_of_packing_full
    htargetPacking hgeneric hcfull
  exact ⟨Gtgt.chain⟩

private theorem dist_eq_abs_axisCoord_of_transverse_eq
    (axis : Axis) (p q : Tiling.Plane)
    (htrans : axis.transverseCoord p = axis.transverseCoord q) :
    dist p q = |axis.coord (p - q)| := by
  cases axis with
  | horizontal =>
      have him : p.im - q.im = 0 := by
        simpa [Axis.transverseCoord] using sub_eq_zero.mpr htrans
      rw [Complex.dist_eq]
      rw [Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      rw [him]
      rw [show (p.re - q.re) * (p.re - q.re) = (p.re - q.re) ^ 2 by ring]
      simp only [zero_mul, add_zero, Axis.coord, Complex.sub_re]
      exact Real.sqrt_sq_eq_abs _
  | vertical =>
      have hre : p.re - q.re = 0 := by
        simpa [Axis.transverseCoord] using sub_eq_zero.mpr htrans
      rw [Complex.dist_eq]
      rw [Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      rw [hre]
      rw [show (p.im - q.im) * (p.im - q.im) = (p.im - q.im) ^ 2 by ring]
      simp only [zero_mul, zero_add, Axis.coord, Complex.sub_im]
      exact Real.sqrt_sq_eq_abs _

private theorem axisCoord_abs_le_dist
    (axis : Axis) (p q : Tiling.Plane) :
    |axis.coord (p - q)| ≤ dist p q := by
  cases axis with
  | horizontal =>
      simpa [Axis.coord, Complex.dist_eq] using Complex.abs_re_le_norm (p - q)
  | vertical =>
      simpa [Axis.coord, Complex.dist_eq] using Complex.abs_im_le_norm (p - q)

private theorem targetCentre_dist_lt_scale_half_of_adjacentVertices
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (s t : ↥C.centres)
    (htrans : axis.transverseCoord (Tphi s) =
      axis.transverseCoord (Tphi t))
    (v w : Tiling.Plane)
    (hv : v ∈ D.deformedRegion.vertices)
    (hw : w ∈ D.deformedRegion.vertices)
    (hendpoint : axis.coord (w + Tphi s) = axis.coord (v + Tphi t)) :
    dist (Tphi s) (Tphi t) < P.scale / 2 := by
  have hd : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  have hdscale : Metric.diam C.region.support < P.scale := by
    rw [hd]
    nlinarith [hScale,
      (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
  have hDle := deformedRegion_diam_le_add_localError P hphi D hdscale
  have hlocal : P.localError < 1 := by
    rw [P.localError_eq]
    apply (inv_lt_one₀ P.scale_pos).2
    nlinarith [hScale,
      (Metric.diam_nonneg : 0 ≤ Metric.diam C.region.openCarrier)]
  have hDlt : Metric.diam D.deformedRegion.support < P.scale / 10 := by
    rw [hd] at hDle
    nlinarith [hScale, hlocal]
  have hvSupport : v ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion hv)
  have hwSupport : w ∈ D.deformedRegion.support := by
    rw [← D.deformedRegion.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion hw)
  have hvertexDist : dist v w ≤ Metric.diam D.deformedRegion.support :=
    Metric.dist_le_diam_of_mem D.deformedRegion.isPolygonal.isBounded
      hvSupport hwSupport
  have hgapCoord : axis.coord (Tphi s - Tphi t) = axis.coord (v - w) := by
    cases axis <;>
      simp only [Axis.coord, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im] at hendpoint ⊢ <;>
      linarith
  rw [dist_eq_abs_axisCoord_of_transverse_eq axis (Tphi s) (Tphi t) htrans,
    hgapCoord]
  have hsmall : |axis.coord (v - w)| < P.scale / 10 :=
    lt_of_le_of_lt (axisCoord_abs_le_dist axis v w)
      (lt_of_le_of_lt hvertexDist hDlt)
  nlinarith [hsmall, P.scale_pos]

private theorem reverse_transverse_of_targetAdjacentOwners
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres)
    (htrans : axis.transverseCoord (Tphi s) =
      axis.transverseCoord (Tphi t))
    (v w : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices)
    (hendpoint : axis.coord (D.planarHomeomorph w + Tphi s) =
      axis.coord (D.planarHomeomorph v + Tphi t)) :
    axis.transverseCoord (s : Tiling.Plane) =
      axis.transverseCoord (t : Tiling.Plane) := by
  have hdist := targetCentre_dist_lt_scale_half_of_adjacentVertices
    P hScale phi hphi D Tphi axis s t htrans
    (D.planarHomeomorph v) (D.planarHomeomorph w)
    (by rw [D.vertices_image]; exact ⟨v, hv, rfl⟩)
    (by rw [D.vertices_image]; exact ⟨w, hw, rfl⟩)
    hendpoint
  have ha0 : 0 ∈ C.region.vertices := C.zero_mem_vertices
  obtain ⟨a, ha, hA⟩ := translatedVertex_targetImage
    phi D Tphi hTphi s 0 ha0
  obtain ⟨b, hb, hB⟩ := translatedVertex_targetImage
    phi D Tphi hTphi t 0 ha0
  have hD0 : D.planarHomeomorph 0 = 0 := by
    have hz := D.vertex_agreement 0 ha0
    have hm : mapPoint phi (C.vertexPoint 0 ha0) = 0 := by
      change (mapScalar phi (0 : C.coordinateSpace) : ℂ) +
        (mapScalar phi (0 : C.coordinateSpace) : ℂ) * Complex.I = 0
      simp [mapScalar]
    exact hz.trans hm
  have hA' : mapTranslatedVertex phi a = Tphi s := by
    rw [hA, hD0, add_zero]
  have hB' : mapTranslatedVertex phi b = Tphi t := by
    rw [hB, hD0, add_zero]
  have hsourceDist : dist (a : Tiling.Plane) b < P.scale := by
    have hdistMap : dist (mapTranslatedVertex phi a)
        (mapTranslatedVertex phi b) < P.scale / 2 := by
      simpa [hA', hB'] using hdist
    exact P.coarse_inverse phi hphi a b hdistMap
  have hab : dist (a : Tiling.Plane) b < P.controlRadius :=
    hsourceDist.trans P.scale_lt_controlRadius
  have hmapzero : Axis.coord axis.swap
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 := by
    rw [hA', hB']
    cases axis <;> simpa [Axis.swap, Axis.coord, Axis.transverseCoord] using
      sub_eq_zero.mpr htrans
  have hreflect := (deformation_reflectsFiniteValues P phi hphi axis.swap
    a b a b hab hab).2.1.mp hmapzero
  cases axis <;>
    apply sub_eq_zero.mp <;>
    simpa [ha, hb, Axis.swap, Axis.coord, Axis.transverseCoord] using hreflect

private theorem witnessedGap_owner_eq_chainOwner
    {axis : Axis} {K : Region} {S : Set Tiling.Plane} {c : ℝ}
    (G : WitnessedLabelledFibreChain axis K S c)
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (j : ℤ) :
    ((G.gap_witness j).choose : Tiling.Plane) = G.chain.owner j := by
  classical
  let u := (G.gap_witness j).choose
  change (u : Tiling.Plane) = G.chain.owner j
  rcases (G.gap_witness j).choose_spec with
    ⟨v, w, hv, hw, hleft, hright, hpos, hinc⟩
  let x := (G.chain.endpoint j + G.chain.endpoint (j + 1)) / 2
  have hstrict : G.chain.endpoint j < G.chain.endpoint (j + 1) :=
    G.chain.strictMono (by omega)
  have hxl : G.chain.endpoint j < x := by dsimp [x]; linarith
  have hxr : x < G.chain.endpoint (j + 1) := by dsimp [x]; linarith
  let z := slicePoint axis c x
  have hzcoord : axis.coord z = x := by cases axis <;> simp [z, slicePoint, Axis.coord]
  have hztrans : axis.transverseCoord z = c := by
    cases axis <;> simp [z, slicePoint, Axis.transverseCoord]
  have hzwit : z ∈ (u : Tiling.Plane) +ᵥ K.openCarrier := by
    apply hinc
    cases axis <;> simpa [axisInterval, z, slicePoint, Axis.coord,
      Axis.transverseCoord] using And.intro hztrans ⟨hxl, hxr⟩
  have hzchain : z ∈ G.chain.owner j +ᵥ K.openCarrier :=
    G.chain.gap_in_tile j ⟨hztrans, by rw [hzcoord]; exact ⟨hxl, hxr⟩⟩
  have hpair := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mp
    hpacking
  by_contra hneq
  have hdis := hpair u.property (G.chain.owner_mem j) hneq
  exact Set.disjoint_left.1 hdis hzwit hzchain

private theorem fibreChain_owner_surjective
    {axis : Axis} {K : Region} {S : Set Tiling.Plane} {c : ℝ}
    (G : LabelledFibreChain axis K S c)
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (htileFibre : ∀ t ∈ S,
      ((t +ᵥ K.openCarrier) ∩ {z | axis.transverseCoord z = c}).Nonempty) :
    ∀ t ∈ S, ∃ j, G.owner j = t := by
  classical
  have hbracket : ∀ y : ℝ, ∃ j : ℤ,
      G.endpoint j < y ∧ y ≤ G.endpoint (j + 1) := by
    intro y
    obtain ⟨J, hJ⟩ := Filter.tendsto_atBot_atBot.mp G.tendsto_atBot (y - 1)
    have hJy : G.endpoint J < y := lt_of_le_of_lt (hJ J le_rfl) (by linarith)
    let t : ℕ → ℝ := fun n => G.endpoint (J + (n : ℤ))
    have httop : Filter.Tendsto t Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop_atTop.mpr ?_
      intro b
      obtain ⟨k, hk⟩ := Filter.tendsto_atTop_atTop.mp G.tendsto_atTop b
      obtain ⟨N, hN⟩ := exists_nat_gt (((k - J : ℤ) : ℝ))
      refine ⟨N, ?_⟩
      intro n hn
      apply hk
      have hN' : k - J < (N : ℤ) := by exact_mod_cast hN
      have hn' : (N : ℤ) ≤ n := by exact_mod_cast hn
      omega
    have hex : ∃ n, y ≤ t n := by
      obtain ⟨n, hn⟩ := Filter.tendsto_atTop_atTop.mp httop y
      exact ⟨n, hn n le_rfl⟩
    have hmin m := Nat.find_min hex (m := m)
    simp only [not_le] at hmin
    have hfindne : Nat.find hex ≠ 0 := by
      intro heq
      have hspec := Nat.find_spec hex
      rw [heq] at hspec
      exact (not_le_of_gt (by simpa [t] using hJy)) hspec
    have hfindpos : 0 < Nat.find hex := Nat.pos_of_ne_zero hfindne
    have hpred : Nat.find hex - 1 < Nat.find hex :=
      Nat.sub_lt hfindpos zero_lt_one
    have hpredsucc : Nat.find hex - 1 + 1 = Nat.find hex :=
      Nat.sub_add_cancel hfindpos
    obtain ⟨n, hnlo, hnhi⟩ : ∃ n, t n < y ∧ y ≤ t (n + 1) :=
      ⟨Nat.find hex - 1, hmin _ hpred, by
        rw [hpredsucc]
        exact Nat.find_spec hex⟩
    refine ⟨J + (n : ℤ), hnlo, ?_⟩
    dsimp [t] at hnhi
    have hidx : J + ((n : ℤ) + 1) = J + (n : ℤ) + 1 := by omega
    rw [← hidx]
    exact hnhi
  intro t ht
  obtain ⟨z, hzTile, hzc⟩ := htileFibre t ht
  have hopen : IsOpen (t +ᵥ K.openCarrier) :=
    (Region.openCarrier_regularOpen K).1.vadd t
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen z hzTile
  obtain ⟨j, hjlo, hjhi⟩ := hbracket (axis.coord z)
  let ρ := min ((axis.coord z - G.endpoint j) / 2) (ε / 2)
  have hρ : 0 < ρ := lt_min (by linarith) (by linarith)
  let p := slicePoint axis c (axis.coord z - ρ)
  have hpc : axis.coord p = axis.coord z - ρ := by
    cases axis <;> simp [p, slicePoint, Axis.coord]
  have hpt : axis.transverseCoord p = c := by
    cases axis <;> simp [p, slicePoint, Axis.transverseCoord]
  have hpGap : axis.coord p ∈ Ioo (G.endpoint j) (G.endpoint (j + 1)) := by
    rw [hpc]
    constructor
    · have hρle := min_le_left ((axis.coord z - G.endpoint j) / 2) (ε / 2)
      linarith
    · linarith
  have hdist : dist p z = |ρ| := by
    have hzEq : z = slicePoint axis c (axis.coord z) := by
      cases axis <;> apply Complex.ext <;>
        simp_all [slicePoint, Axis.coord, Axis.transverseCoord]
    rw [hzEq]
    dsimp [p]
    cases axis
    · rw [Complex.dist_eq]
      norm_num [slicePoint, Complex.norm_def, Complex.normSq_apply]
    · rw [Complex.dist_eq]
      norm_num [slicePoint, Complex.norm_def, Complex.normSq_apply]
      convert Real.sqrt_sq_eq_abs ρ using 1
      ring_nf
  have hpTile : p ∈ t +ᵥ K.openCarrier := by
    apply hball
    rw [Metric.mem_ball, hdist, abs_of_pos hρ]
    exact lt_of_le_of_lt (min_le_right
      ((axis.coord z - G.endpoint j) / 2) (ε / 2)) (by linarith)
  have hpOwner : p ∈ G.owner j +ᵥ K.openCarrier := G.gap_in_tile j ⟨hpt, hpGap⟩
  refine ⟨j, ?_⟩
  by_contra hne
  have hdis := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mp
    hpacking (G.owner_mem j) ht hne
  exact Set.disjoint_left.1 hdis hpOwner hpTile

private theorem witnessedChain_reflects_transverse
    {C : ApproximationContext} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (cphi c₁ : ℝ)
    (G : WitnessedLabelledFibreChain axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) cphi)
    (hpacking : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)))
    (htargetCollinear : ∀ z ∈ deformedCenterCarrierOn Tphi S,
      axis.transverseCoord z = c₁)
    (htileFibre : ∀ z ∈ deformedCenterCarrierOn Tphi S,
      ((z +ᵥ D.deformedRegion.openCarrier) ∩
        {x | axis.transverseCoord x = cphi}).Nonempty) :
    ∀ s ∈ S, ∀ t ∈ S,
      axis.transverseCoord (s : Tiling.Plane) =
        axis.transverseCoord (t : Tiling.Plane) := by
  classical
  have himage (j : ℤ) : G.chain.owner j ∈ Tphi '' S := by
    simpa [deformedCenterCarrierOn] using G.chain.owner_mem j
  let sourceOwner : ℤ → ↥C.centres := fun j => Classical.choose (himage j)
  have hsourceMap (j : ℤ) : Tphi (sourceOwner j) = G.chain.owner j :=
    (Classical.choose_spec (himage j)).2
  have hstep (j : ℤ) :
      axis.transverseCoord (sourceOwner j : Tiling.Plane) =
        axis.transverseCoord (sourceOwner (j + 1) : Tiling.Plane) := by
    let u := (G.gap_witness j).choose
    let u' := (G.gap_witness (j + 1)).choose
    obtain ⟨_v, w, _hv, hw, _hleft, hright, _hpositive, _hinc⟩ :=
      (G.gap_witness j).choose_spec
    obtain ⟨v', _w', hv', _hw', hleft', _hright', _hpositive', _hinc'⟩ :=
      (G.gap_witness (j + 1)).choose_spec
    have huOwner : (u : Tiling.Plane) = G.chain.owner j := by
      change ((G.gap_witness j).choose : Tiling.Plane) = G.chain.owner j
      exact witnessedGap_owner_eq_chainOwner G hpacking j
    have hu'Owner : (u' : Tiling.Plane) = G.chain.owner (j + 1) := by
      change ((G.gap_witness (j + 1)).choose : Tiling.Plane) =
        G.chain.owner (j + 1)
      exact witnessedGap_owner_eq_chainOwner G hpacking (j + 1)
    have himageU : (u : Tiling.Plane) ∈ Tphi '' S := by
      rw [huOwner]
      exact himage j
    have himageU' : (u' : Tiling.Plane) ∈ Tphi '' S := by
      rw [hu'Owner]
      exact himage (j + 1)
    let su : ↥C.centres := Classical.choose himageU
    let su' : ↥C.centres := Classical.choose himageU'
    have hsuMap : Tphi su = (u : Tiling.Plane) :=
      (Classical.choose_spec himageU).2
    have hsu'Map : Tphi su' = (u' : Tiling.Plane) :=
      (Classical.choose_spec himageU').2
    have hsuEq : su = sourceOwner j := by
      apply Tphi.injective
      rw [hsuMap, hsourceMap j, huOwner]
    have hsu'Eq : su' = sourceOwner (j + 1) := by
      apply Tphi.injective
      rw [hsu'Map, hsourceMap (j + 1), hu'Owner]
    have hVimg : v' ∈ D.planarHomeomorph '' C.region.vertices := by
      rw [← D.vertices_image]
      exact hv'
    have hWimg : w ∈ D.planarHomeomorph '' C.region.vertices := by
      rw [← D.vertices_image]
      exact hw
    let sv : Tiling.Plane := Classical.choose hVimg
    let sw : Tiling.Plane := Classical.choose hWimg
    have hsv : sv ∈ C.region.vertices := (Classical.choose_spec hVimg).1
    have hsw : sw ∈ C.region.vertices := (Classical.choose_spec hWimg).1
    have hsvMap : D.planarHomeomorph sv = v' := (Classical.choose_spec hVimg).2
    have hswMap : D.planarHomeomorph sw = w := (Classical.choose_spec hWimg).2
    have hshared : axis.coord (w + (u : Tiling.Plane)) =
        axis.coord (v' + (u' : Tiling.Plane)) := hright.symm.trans hleft'
    have htargetEndpoint : axis.coord
        (D.planarHomeomorph sw + Tphi su) = axis.coord
          (D.planarHomeomorph sv + Tphi su') := by
      simpa [hswMap, hsvMap, hsuMap, hsu'Map] using hshared
    have htargetTrans : axis.transverseCoord (Tphi su) =
        axis.transverseCoord (Tphi su') := by
      rw [hsuMap, hsu'Map]
      exact (htargetCollinear _ u.property).trans
        (htargetCollinear _ u'.property).symm
    have hreflect := reverse_transverse_of_targetAdjacentOwners
      P hScale phi hphi D Tphi hTphi axis su su' htargetTrans
      sv sw hsv hsw htargetEndpoint
    simpa [hsuEq, hsu'Eq] using hreflect
  have hconst (j : ℤ) :
      axis.transverseCoord (sourceOwner j : Tiling.Plane) =
        axis.transverseCoord (sourceOwner 0 : Tiling.Plane) := by
    induction j using Int.induction_on with
    | zero => rfl
    | succ j ih =>
        exact (hstep j).symm.trans ih
    | pred j ih =>
        have hp := hstep (-(j : ℤ) - 1)
        have hidx : (-(j : ℤ) - 1) + 1 = -(j : ℤ) := by omega
        rw [hidx] at hp
        exact hp.trans ih
  intro s hs t ht
  obtain ⟨j, hj⟩ := fibreChain_owner_surjective G.chain hpacking htileFibre
    (Tphi s) ⟨s, hs, rfl⟩
  obtain ⟨k, hk⟩ := fibreChain_owner_surjective G.chain hpacking htileFibre
    (Tphi t) ⟨t, ht, rfl⟩
  have hsj : sourceOwner j = s := by
    apply Tphi.injective
    rw [hsourceMap j, hj]
  have htk : sourceOwner k = t := by
    apply Tphi.injective
    rw [hsourceMap k, hk]
  rw [← hsj, ← htk]
  exact (hconst j).trans (hconst k).symm


private theorem exists_generic_fibre_meeting_all_collinear_tiles
    (axis : Axis) (K : Region) (S : Set Tiling.Plane)
    (hcol : ∃ c₀, ∀ t ∈ S, axis.transverseCoord t = c₀) :
    ∃ c, (∀ t ∈ S, c ∉ axis.transverseCoord t +ᵥ
      (axis.transverseCoord '' K.vertices)) ∧
      ∀ t ∈ S,
        ((t +ᵥ K.openCarrier) ∩ {z | axis.transverseCoord z = c}).Nonempty := by
  obtain ⟨c₀, hc₀⟩ := hcol
  obtain ⟨z₀, hz₀, hzoff⟩ := exists_offVertexCoordinateGrid_mem_open K
    (Region.openCarrier_regularOpen K).1
    (K.isPolygonal.interior_nonempty K.nonempty)
  let c := c₀ + axis.transverseCoord z₀
  refine ⟨c, ?_, ?_⟩
  · intro t ht hm
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hm
    obtain ⟨v, hv, hvcoord⟩ := hm
    have hcoord := hc₀ t ht
    cases axis with
    | horizontal =>
        have hneq := (hzoff v hv).2
        have hsame : z₀.im = v.im := by
          change v.im = -t.im + (c₀ + z₀.im) at hvcoord
          change t.im = c₀ at hcoord
          linarith
        exact hneq hsame
    | vertical =>
        have hneq := (hzoff v hv).1
        have hsame : z₀.re = v.re := by
          change v.re = -t.re + (c₀ + z₀.re) at hvcoord
          change t.re = c₀ at hcoord
          linarith
        exact hneq hsame
  · intro t ht
    refine ⟨t + z₀, ?_, ?_⟩
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa using hz₀
    · have hcoord := hc₀ t ht
      cases axis <;>
        simpa [c, Axis.transverseCoord, hcoord, Complex.add_re,
          Complex.add_im] using hcoord

private theorem reverseCollinearity_boundedSteps :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres),
    (deformedCenterCarrierOn Tphi S).Nonempty →
    (∃ c, ∀ z ∈ deformedCenterCarrierOn Tphi S, axis.transverseCoord z = c) →
    FullAxisSections axis D.deformedRegion (deformedCenterCarrierOn Tphi S) →
    ∃ c, ∀ z ∈ Set.image Subtype.val S, axis.transverseCoord z = c := by
  intro C P hScale phi hphi D Tphi hTphi axis S hnonempty hcol hsections
  obtain ⟨c₁, hc₁⟩ := hcol
  obtain ⟨c, hgeneric, htileFibre⟩ :=
    exists_generic_fibre_meeting_all_collinear_tiles axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ⟨c₁, hc₁⟩
  have hsourcePacking := selectedSubfamily_sourcePacking P S
  have htargetPacking := selectedSubfamily_packingTransport
    P hScale phi hphi D Tphi hTphi S hsourcePacking
  obtain ⟨t₀, ht₀⟩ := hnonempty
  obtain ⟨z, hzTile, hzc⟩ := htileFibre t₀ ht₀
  have hzUnion : z ∈ openUnion D.deformedRegion
      (deformedCenterCarrierOn Tphi S) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨t₀, ht₀⟩, hzTile⟩
  have hopenUnion : IsOpen (openUnion D.deformedRegion
      (deformedCenterCarrierOn Tphi S)) := by
    unfold openUnion
    exact isOpen_iUnion fun t =>
      (Region.openCarrier_regularOpen D.deformedRegion).1.vadd t.1
  have hzRegular : z ∈ regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) := hopenUnion.subset_interior_closure hzUnion
  have hoccupied : (axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩ {x | axis.transverseCoord x = c})).Nonempty :=
    ⟨axis.coord z, z, ⟨hzRegular, hzc⟩, rfl⟩
  have hfull : axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩ {x | axis.transverseCoord x = c}) =
      Set.univ := by
    rcases hsections c with hfull | hempty
    · exact hfull
    · rw [hempty] at hoccupied
      exact False.elim (Set.not_nonempty_empty hoccupied)
  obtain ⟨G⟩ := witnessed_chain_of_packing_full htargetPacking hgeneric hfull
  have hpairs := witnessedChain_reflects_transverse
    P hScale phi hphi D Tphi hTphi axis S c c₁ G htargetPacking hc₁ htileFibre
  obtain ⟨s₀, hs₀, _hs₀map⟩ := ht₀
  refine ⟨axis.transverseCoord (s₀ : Tiling.Plane), ?_⟩
  rintro z ⟨s, hs, rfl⟩
  exact hpairs s hs s₀ hs₀


private theorem allGenericFibreChainsReflect :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres),
    IsCenterColumn axis D.deformedRegion (deformedCenterCarrierOn Tphi S) →
    ∀ c : ℝ,
      (∀ t ∈ S, c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
        (axis.transverseCoord '' C.region.vertices)) →
      (axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
        {z | axis.transverseCoord z = c})).Nonempty →
      Nonempty (LabelledFibreChain axis C.region
        (Set.image Subtype.val S) c) := by
  intro C P hScale phi hphi D Tphi hTphi axis S hColumn c hgeneric hnonempty
  obtain ⟨c₀, hc₀⟩ := reverseCollinearity_boundedSteps
    P hScale phi hphi D Tphi hTphi axis S hColumn.2.1 hColumn.2.2.1
    (centerColumn_fullSections axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) hColumn)
  obtain ⟨c₁, hc₁⟩ := hColumn.2.2.1
  have hsource : ∀ t ∈ S, axis.transverseCoord (t : Tiling.Plane) = c₀ := by
    intro t ht
    exact hc₀ t ⟨t, ht, rfl⟩
  have htarget : ∀ t ∈ S, axis.transverseCoord (Tphi t) = c₁ := by
    intro t ht
    exact hc₁ _ ⟨t, ht, rfl⟩
  obtain ⟨_z₀, s₀, hs₀, _hmap₀⟩ := hColumn.2.1
  have hc : c ∉ c₀ +ᵥ (axis.transverseCoord '' C.region.vertices) := by
    simpa [hsource s₀ hs₀] using hgeneric s₀ hs₀
  let H := transverseTransportHomeomorph axis D c₀ c₁
  have htargetNonempty : (axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z = H c})).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro hempty
    have hsourceEmpty := (empty_fibre_transport phi D Tphi axis S c₀ c₁ c
      hsource htarget hc).mpr hempty
    rw [hsourceEmpty] at hnonempty
    exact Set.not_nonempty_empty hnonempty
  have htargetFull : axis.coord '' (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S) ∩
        {z | axis.transverseCoord z = H c}) = Set.univ := by
    rcases centerColumn_fullSections axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) hColumn (H c) with hfull | hempty
    · exact hfull
    · rw [hempty] at htargetNonempty
      exact False.elim (Set.not_nonempty_empty htargetNonempty)
  have htargetLevel : H c ∉ c₁ +ᵥ mappedTransverseVertexLevels axis phi := by
    intro hm
    have hm' : H c ∈ H '' (c₀ +ᵥ (axis.transverseCoord '' C.region.vertices)) := by
      rw [transverseTransport_levels phi D axis c₀ c₁]
      exact hm
    obtain ⟨x, hx, hxc⟩ := hm'
    exact hc (H.injective hxc ▸ hx)
  have htargetGeneric : ∀ t ∈ deformedCenterCarrierOn Tphi S,
      H c ∉ axis.transverseCoord t +ᵥ
        (axis.transverseCoord '' D.deformedRegion.vertices) := by
    rintro t ⟨s, hs, rfl⟩ hm
    apply htargetLevel
    rw [← deformed_transverse_vertices_eq_mapped phi D axis]
    simpa [htarget s hs] using hm
  obtain ⟨Gtgt⟩ := witnessed_chain_of_packing_full hColumn.1
    htargetGeneric htargetFull
  exact allGenericFibreChainsReflect_of_witnessed
    P hScale phi hphi D Tphi hTphi axis S c (H c) c₀ c₁
    hsource htarget rfl hc Gtgt

private theorem fullAxisSections_translationInvariant
    (axis : Axis) (K : Region) (S : Set Tiling.Plane)
    (hfull : FullAxisSections axis K S) :
    ∀ a : ℝ,
      (match axis with
        | .horizontal => (a : ℂ)
        | .vertical => (a : ℂ) * Complex.I) +ᵥ regularSupport K S =
      regularSupport K S := by
  have hmem {z w : Tiling.Plane}
      (htrans : axis.transverseCoord z = axis.transverseCoord w)
      (hz : z ∈ regularSupport K S) : w ∈ regularSupport K S := by
    rcases hfull (axis.transverseCoord z) with hall | hempty
    · have hwcoord : axis.coord w ∈ axis.coord ''
          (regularSupport K S ∩ {p | axis.transverseCoord p = axis.transverseCoord z}) := by
        rw [hall]
        trivial
      obtain ⟨p, hp, hpc⟩ := hwcoord
      have hpw : p = w := axis_eq_of_coords axis hpc (hp.2.trans htrans)
      exact hpw ▸ hp.1
    · have hzcoord : axis.coord z ∈ axis.coord ''
          (regularSupport K S ∩ {p | axis.transverseCoord p = axis.transverseCoord z}) :=
        ⟨z, ⟨hz, rfl⟩, rfl⟩
      rw [hempty] at hzcoord
      exact hzcoord.elim
  intro a
  ext z
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · intro hz
    apply hmem _ hz
    cases axis <;> simp [Axis.transverseCoord]
  · intro hz
    apply hmem _ hz
    cases axis <;> simp [Axis.transverseCoord]

private theorem image_centres_collinear
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hsource : ∃ c, ∀ t ∈ S, axis.transverseCoord (t : Tiling.Plane) = c) :
    ∃ c, ∀ t ∈ S, axis.transverseCoord (Tphi t) = c := by
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, hs₀⟩ := hS
    obtain ⟨c₀, hc₀⟩ := hsource
    refine ⟨axis.transverseCoord (Tphi s₀), ?_⟩
    intro s hs
    have hsourceEq := (hc₀ s hs).trans (hc₀ s₀ hs₀).symm
    rw [hTphi s, hTphi s₀]
    cases axis with
    | horizontal =>
        have him : (s : Tiling.Plane).im = (s₀ : Tiling.Plane).im := hsourceEq
        simp only [Axis.transverseCoord, mapPoint, mapScalar, Complex.add_im,
          Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_one, zero_add]
        congr 1
        exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
          (Subtype.ext him)
    | vertical =>
        have hre : (s : Tiling.Plane).re = (s₀ : Tiling.Plane).re := hsourceEq
        simp only [Axis.transverseCoord, mapPoint, mapScalar, Complex.add_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero]
        congr 1
        exact congrArg (fun z : C.coordinateSpace => (phi z : ℝ))
          (Subtype.ext hre)
  · exact ⟨0, fun t ht => False.elim (hS ⟨t, ht⟩)⟩

private theorem exists_transverseGridCell_mem
    {L : Set ℝ} (hL : L.Finite) {c : ℝ} (hc : c ∉ L) :
    ∃ J, IsTransverseGridCell L J ∧ c ∈ J := by
  let J := connectedComponentIn Lᶜ c
  have hcJ : c ∈ J := mem_connectedComponentIn hc
  refine ⟨J, ⟨hL.isClosed.isOpen_compl.connectedComponentIn,
    isPreconnected_connectedComponentIn, ⟨c, hcJ⟩, ?_, ?_⟩, hcJ⟩
  · exact Set.disjoint_left.2 fun y hy hyL =>
      connectedComponentIn_subset Lᶜ c hy hyL
  · intro U _hUopen hUpre _hUne hUdis hJU
    exact hUpre.subset_connectedComponentIn (hJU hcJ)
      (fun y hy hyL => Set.disjoint_left.1 hUdis hy hyL)


private theorem centerColumnTransport :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres),
    IsCenterColumn axis C.region (Set.image Subtype.val S) ↔
      IsCenterColumn axis D.deformedRegion (deformedCenterCarrierOn Tphi S) := by
  intro C P hScale phi hphi D Tphi hTphi axis S
  constructor
  · intro hColumn
    have hsource : ∃ c, ∀ t ∈ S, axis.transverseCoord (t : Tiling.Plane) = c := by
      obtain ⟨c, hc⟩ := hColumn.2.2.1
      exact ⟨c, fun t ht => hc t ⟨t, ht, rfl⟩⟩
    have htarget := image_centres_collinear phi Tphi hTphi axis S hsource
    obtain ⟨G⟩ := transverseGridCellTransportData_exists
      P hScale phi hphi D Tphi hTphi axis S hsource htarget
    have htargetCol : ∀ z ∈ deformedCenterCarrierOn Tphi S,
        axis.transverseCoord z = G.targetCentreCoordinate := by
      rintro z ⟨t, ht, rfl⟩
      exact G.target_collinear t ht
    have hgeneric : ∀ c, c ∉ G.targetCentreCoordinate +ᵥ
        (axis.transverseCoord '' D.deformedRegion.vertices) →
        axis.coord '' (regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S) ∩ {z | axis.transverseCoord z = c}) =
          Set.univ ∨
        axis.coord '' (regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S) ∩ {z | axis.transverseCoord z = c}) = ∅ := by
      intro c hc
      by_cases hne : (axis.coord '' (regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S) ∩ {z | axis.transverseCoord z = c})).Nonempty
      · left
        have hcL : c ∉ G.targetLevels := by
          rw [G.targetLevels_eq, ← deformed_transverse_vertices_eq_mapped phi D axis]
          exact hc
        obtain ⟨J, hJ, hcJ⟩ := exists_transverseGridCell_mem G.targetLevels_finite hcL
        have hJmem : J ∈ G.targetCells := by
          rw [G.targetCells_eq]
          exact hJ
        obtain ⟨chain⟩ := everyTargetGenericFibre_chain
          P hScale phi hphi D Tphi hTphi axis S G hColumn ⟨J, hJmem⟩ c hcJ hne
        exact chain.fibre_eq
      · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hne)
    have hsections := genericFibres_regularizeGrid axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) G.targetCentreCoordinate htargetCol hgeneric
    refine ⟨selectedSubfamily_packingTransport P hScale phi hphi D Tphi hTphi S
      hColumn.1, ?_, ⟨G.targetCentreCoordinate, htargetCol⟩,
      fullAxisSections_translationInvariant axis D.deformedRegion
        (deformedCenterCarrierOn Tphi S) hsections⟩
    obtain ⟨z, t, ht, rfl⟩ := hColumn.2.1
    exact ⟨Tphi t, t, ht, rfl⟩
  · intro hColumn
    have hsectionsTarget := centerColumn_fullSections axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S) hColumn
    obtain ⟨c₀, hc₀⟩ := reverseCollinearity_boundedSteps
      P hScale phi hphi D Tphi hTphi axis S hColumn.2.1 hColumn.2.2.1
      hsectionsTarget
    have hsourceGeneric : ∀ c, c ∉ c₀ +ᵥ
        (axis.transverseCoord '' C.region.vertices) →
        axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
          {z | axis.transverseCoord z = c}) = Set.univ ∨
        axis.coord '' (regularSupport C.region (Set.image Subtype.val S) ∩
          {z | axis.transverseCoord z = c}) = ∅ := by
      intro c hc
      by_cases hne : (axis.coord '' (regularSupport C.region
          (Set.image Subtype.val S) ∩ {z | axis.transverseCoord z = c})).Nonempty
      · left
        have hgeneric : ∀ t ∈ S,
            c ∉ axis.transverseCoord (t : Tiling.Plane) +ᵥ
              (axis.transverseCoord '' C.region.vertices) := by
          intro t ht hm
          apply hc
          simpa [hc₀ t ⟨t, ht, rfl⟩] using hm
        obtain ⟨chain⟩ := allGenericFibreChainsReflect
          P hScale phi hphi D Tphi hTphi axis S hColumn c hgeneric hne
        exact chain.fibre_eq
      · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp hne)
    have hsectionsSource := genericFibres_regularizeGrid axis C.region
      (Set.image Subtype.val S) c₀ hc₀ hsourceGeneric
    refine ⟨selectedSubfamily_sourcePacking P S, ?_, ⟨c₀, hc₀⟩,
      fullAxisSections_translationInvariant axis C.region
        (Set.image Subtype.val S) hsectionsSource⟩
    obtain ⟨z, t, ht, _hmap⟩ := hColumn.2.1
    exact ⟨t, t, ht, rfl⟩

end Tiling.AxisParallel.Approximation

namespace Tiling.AxisParallel.Approximation

set_option linter.unusedVariables false

open Function Set
open Tiling AxisParallel Approximation
universe u

theorem deformation_preserves_vertexOnEdge :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a b v : ↥C.region.vertices) (s t : ↥C.centres)
    (hEdge : a ≠ b ∧
      openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane) ⊆
        frontier C.region.openCarrier ∧
      ∀ w : ↥C.region.vertices,
        (w : Tiling.Plane) ∉
          openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane))
    (hIncidence : (v : Tiling.Plane) + (s : Tiling.Plane) ∈
        segment ℝ ((a : Tiling.Plane) + (t : Tiling.Plane))
          ((b : Tiling.Plane) + (t : Tiling.Plane))),
    mapPoint phi (C.vertexPoint v.1 v.2) + Tphi s ∈
      segment ℝ
        (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi t)
        (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi t) := by
  intro C P hScale phi hphi D Tphi hTphi a b v s t hEdge hIncidence
  apply (Tiling.AxisParallel.Approximation.vertexOnEdgeTransport
    P hScale phi hphi D Tphi hTphi a b v s t ?_).mp hIncidence
  have hab : (a : Tiling.Plane) ≠ (b : Tiling.Plane) := by
    intro h
    apply hEdge.1
    exact Subtype.ext h
  refine ⟨a.2, b.2, hab, hEdge.2.1, ?_⟩
  intro w hw
  exact hEdge.2.2 ⟨w, hw⟩

theorem deformation_reflects_vertexOnEdge :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a b v : ↥C.region.vertices) (s t : ↥C.centres)
    (hEdge : a ≠ b ∧
      openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane) ⊆
        frontier C.region.openCarrier ∧
      ∀ w : ↥C.region.vertices,
        (w : Tiling.Plane) ∉
          openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane))
    (hIncidence : mapPoint phi (C.vertexPoint v.1 v.2) + Tphi s ∈
        segment ℝ
          (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi t)
          (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi t)),
    (v : Tiling.Plane) + (s : Tiling.Plane) ∈
      segment ℝ ((a : Tiling.Plane) + (t : Tiling.Plane))
        ((b : Tiling.Plane) + (t : Tiling.Plane)) := by
  intro C P hScale phi hphi D Tphi hTphi a b v s t hEdge hIncidence
  apply (Tiling.AxisParallel.Approximation.vertexOnEdgeTransport
    P hScale phi hphi D Tphi hTphi a b v s t ?_).mpr hIncidence
  have hab : (a : Tiling.Plane) ≠ (b : Tiling.Plane) := by
    intro h
    apply hEdge.1
    exact Subtype.ext h
  refine ⟨a.2, b.2, hab, hEdge.2.1, ?_⟩
  intro w hw
  exact hEdge.2.2 ⟨w, hw⟩

theorem deformation_preserves_edgeIntersection :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a b c d : ↥C.region.vertices) (s t : ↥C.centres)
    (hEdgeAB : a ≠ b ∧
      openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane) ⊆
        frontier C.region.openCarrier ∧
      ∀ w : ↥C.region.vertices,
        (w : Tiling.Plane) ∉
          openSegment ℝ (a : Tiling.Plane) (b : Tiling.Plane))
    (hEdgeCD : c ≠ d ∧
      openSegment ℝ (c : Tiling.Plane) (d : Tiling.Plane) ⊆
        frontier C.region.openCarrier ∧
      ∀ w : ↥C.region.vertices,
        (w : Tiling.Plane) ∉
          openSegment ℝ (c : Tiling.Plane) (d : Tiling.Plane)),
    segment ℝ ((a : Tiling.Plane) + (s : Tiling.Plane))
          ((b : Tiling.Plane) + (s : Tiling.Plane)) ∩
        segment ℝ ((c : Tiling.Plane) + (t : Tiling.Plane))
          ((d : Tiling.Plane) + (t : Tiling.Plane)) = ∅ ↔
      segment ℝ
            (mapPoint phi (C.vertexPoint a.1 a.2) + Tphi s)
            (mapPoint phi (C.vertexPoint b.1 b.2) + Tphi s) ∩
          segment ℝ
            (mapPoint phi (C.vertexPoint c.1 c.2) + Tphi t)
            (mapPoint phi (C.vertexPoint d.1 d.2) + Tphi t) = ∅ := by
  intro C P hScale phi hphi D Tphi hTphi a b c d s t hEdgeAB hEdgeCD
  have hAB : Tiling.AxisParallel.Approximation.IsIntrinsicEdge C.region
      (a : Tiling.Plane) (b : Tiling.Plane) := by
    have hab : (a : Tiling.Plane) ≠ (b : Tiling.Plane) := by
      intro h
      apply hEdgeAB.1
      exact Subtype.ext h
    refine ⟨a.2, b.2, hab, hEdgeAB.2.1, ?_⟩
    intro w hw
    exact hEdgeAB.2.2 ⟨w, hw⟩
  have hCD : Tiling.AxisParallel.Approximation.IsIntrinsicEdge C.region
      (c : Tiling.Plane) (d : Tiling.Plane) := by
    have hcd : (c : Tiling.Plane) ≠ (d : Tiling.Plane) := by
      intro h
      apply hEdgeCD.1
      exact Subtype.ext h
    refine ⟨c.2, d.2, hcd, hEdgeCD.2.1, ?_⟩
    intro w hw
    exact hEdgeCD.2.2 ⟨w, hw⟩
  exact Tiling.AxisParallel.Approximation.edgeIntersectionTransport
    P hScale phi hphi D Tphi hTphi a b c d s t hAB hCD

theorem deformation_preserves_horizontalProperContact :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s t : ↥C.centres),
    Continuous.HorizontalProperContact C.region
        (s : Tiling.Plane) (t : Tiling.Plane) ↔
      Continuous.HorizontalProperContact D.deformedRegion (Tphi s) (Tphi t) := by
  intro C P hScale phi hphi D Tphi hTphi s t
  exact Tiling.AxisParallel.Approximation.properContactTransport
    P hScale phi hphi D Tphi hTphi s t

theorem deformation_preserves_localCone :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres) (a : ↥C.translatedVertices)
    (ha : (a : Tiling.Plane) ∈
      C.region.vertices + Set.image Subtype.val S),
    ∃ r : ℝ, 0 < r ∧ ∀ u : Tiling.Plane, dist u 0 < r →
      ((a : Tiling.Plane) + u ∈
          regularSupport C.region (Set.image Subtype.val S) →
        mapTranslatedVertex phi a + u ∈
          regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
  intro C P hScale phi hphi D Tphi hTphi S a ha
  obtain ⟨r, hr, htransport⟩ :=
    Tiling.AxisParallel.Approximation.localConeTransport
      P hScale phi hphi D Tphi hTphi S a ha
  refine ⟨r, hr, ?_⟩
  intro u hu hsource
  exact (htransport u hu).mp hsource

theorem deformation_reflects_localCone :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres) (a : ↥C.translatedVertices)
    (ha : (a : Tiling.Plane) ∈
      C.region.vertices + Set.image Subtype.val S),
    ∃ r : ℝ, 0 < r ∧ ∀ u : Tiling.Plane, dist u 0 < r →
      (mapTranslatedVertex phi a + u ∈
          regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S) →
        (a : Tiling.Plane) + u ∈
          regularSupport C.region (Set.image Subtype.val S)) := by
  intro C P hScale phi hphi D Tphi hTphi S a ha
  obtain ⟨r, hr, htransport⟩ :=
    Tiling.AxisParallel.Approximation.localConeTransport
      P hScale phi hphi D Tphi hTphi S a ha
  refine ⟨r, hr, ?_⟩
  intro u hu htarget
  exact (htransport u hu).mpr htarget

theorem deformation_preserves_centerColumns :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hColumn : IsCenterColumn axis C.region (Set.image Subtype.val S)),
    IsCenterColumn axis D.deformedRegion (deformedCenterCarrierOn Tphi S) := by
  intro C P hScale phi hphi D Tphi hTphi axis S hColumn
  exact (centerColumnTransport P hScale phi hphi D Tphi hTphi axis S).mp hColumn

theorem deformation_reflects_centerColumns :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hColumn : IsCenterColumn axis D.deformedRegion
      (deformedCenterCarrierOn Tphi S)),
    IsCenterColumn axis C.region (Set.image Subtype.val S) := by
  intro C P hScale phi hphi D Tphi hTphi axis S hColumn
  exact (centerColumnTransport P hScale phi hphi D Tphi hTphi axis S).mpr hColumn

theorem deformation_reflects_verticalPlateColumn :
  ∀ {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (Psource : Continuous.VerticalPlate C.region C.centres)
    (Ptarget : Continuous.VerticalPlate
      D.deformedRegion (deformedCenterCarrier Tphi))
    (hsource : Psource.centres = Set.image Subtype.val S)
    (htarget : Ptarget.centres = deformedCenterCarrierOn Tphi S)
    (hColumn : Continuous.IsVerticalColumn Ptarget),
    Continuous.IsVerticalColumn Psource := by
  intro C P hScale phi hphi D Tphi hTphi S Psource Ptarget hsource htarget hColumn
  exact (Tiling.AxisParallel.Approximation.verticalPlateColumnTransport
    P hScale phi hphi D Tphi hTphi S Psource Ptarget hsource htarget).mpr hColumn

end Tiling.AxisParallel.Approximation
