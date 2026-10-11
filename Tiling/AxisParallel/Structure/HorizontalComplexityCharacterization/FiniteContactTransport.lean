import Mathlib.Data.Finset.Powerset
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.ApproximationPreservesEarthquakes
import Tiling.AxisParallel.Structure.HorizontalBoundaryChains
import Tiling.AxisParallel.Structure.PlateThickness
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.EdgeOffsets
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.BoundaryDensity
import Tiling.Geometry.LocalLine

/-!
# Finite contact transport

This module develops the finite horizontal-line code used to transport
axis-parallel contacts through the rational approximation.  It includes contact codes, order fibres, plates, and component boundaries.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Bornology Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

private def linePoint (y x : ℝ) : Tiling.Plane :=
  (x : ℂ) + (y : ℂ) * Complex.I

private def IsIntrinsicSide (K : Region) (v w : ↥K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ (v.1.re = w.1.re ∨ v.1.im = w.1.im) ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices

private def IsIntrinsicHorizontalSide
    (K : Region) (v w : ↥K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices

/-- A controlled cut of an arbitrary horizontal line.  For a vertical side
the two endpoint real coordinates coincide; for a horizontal side the cut is
one of its endpoints.  Thus every cut is a translated intrinsic-vertex
coordinate even when `y` itself is an exceptional slice level. -/
private structure HorizontalLineCutWitness
    (K : Region) (T : Set Tiling.Plane) (y x : ℝ) where
  center : ↥T
  v : ↥K.vertices
  w : ↥K.vertices
  side : IsIntrinsicSide K v w
  x_coordinate :
    x = (v.1 + (center.1 : Tiling.Plane)).re ∨
      x = (w.1 + (center.1 : Tiling.Plane)).re
  line_meets_side : linePoint y x ∈
    segment ℝ (v.1 + (center.1 : Tiling.Plane))
      (w.1 + (center.1 : Tiling.Plane))

private def horizontalLineCutSet
    (K : Region) (T : Set Tiling.Plane) (y : ℝ) : Set ℝ :=
  {x | Nonempty (HorizontalLineCutWitness K T y x)}

private structure HorizontalCrossingCell
    (K : Region) (T : Set Tiling.Plane) (y l r : ℝ) where
  center : ↥T
  leftBottom : ↥K.vertices
  leftTop : ↥K.vertices
  rightBottom : ↥K.vertices
  rightTop : ↥K.vertices
  left_lt_right : l < r
  left_coordinate : l =
    (leftBottom.1 + (center.1 : Tiling.Plane)).re
  right_coordinate : r =
    (rightBottom.1 + (center.1 : Tiling.Plane)).re
  left_vertical : IsIntrinsicSide K leftBottom leftTop ∧
    leftBottom.1.re = leftTop.1.re
  right_vertical : IsIntrinsicSide K rightBottom rightTop ∧
    rightBottom.1.re = rightTop.1.re
  left_endpoint_at_level : linePoint y l ∈
    segment ℝ (leftBottom.1 + (center.1 : Tiling.Plane))
      (leftTop.1 + (center.1 : Tiling.Plane))
  right_endpoint_at_level : linePoint y r ∈
    segment ℝ (rightBottom.1 + (center.1 : Tiling.Plane))
      (rightTop.1 + (center.1 : Tiling.Plane))
  crossing : ∀ x ∈ Ioo l r,
    linePoint y x ∈ (center.1 : Tiling.Plane) +ᵥ K.openCarrier

private structure HorizontalSeamCell
    (K : Region) (T : Set Tiling.Plane) (y l r : ℝ) where
  upperCenter : ↥T
  lowerCenter : ↥T
  centers_ne : upperCenter ≠ lowerCenter
  a : ↥K.vertices
  b : ↥K.vertices
  a' : ↥K.vertices
  b' : ↥K.vertices
  left_lt_right : l < r
  first_horizontal : IsIntrinsicHorizontalSide K a b
  second_horizontal : IsIntrinsicHorizontalSide K a' b'
  first_side : ∀ x ∈ Ioo l r, linePoint y x ∈
    openSegment ℝ (a.1 + (upperCenter.1 : Tiling.Plane))
      (b.1 + (upperCenter.1 : Tiling.Plane))
  second_side : ∀ x ∈ Ioo l r, linePoint y x ∈
    openSegment ℝ (a'.1 + (lowerCenter.1 : Tiling.Plane))
      (b'.1 + (lowerCenter.1 : Tiling.Plane))
  opposite_germs : ∀ x ∈ Ioo l r,
    ∃ epsilon : ℝ, 0 < epsilon ∧
      (∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y + h) x ∈
          (upperCenter.1 : Tiling.Plane) +ᵥ K.openCarrier) ∧
      ∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y - h) x ∈
          (lowerCenter.1 : Tiling.Plane) +ᵥ K.openCarrier

/-- Finite endpoint-aligned code around `[A,B]`.  The outer coordinates are
actual controlled cuts, never the arbitrary exhaustion endpoints. -/
private structure EndpointAlignedLineCode
    (K : Region) (T : Set Tiling.Plane) (y A B : ℝ) where
  qLeft : ℝ
  qRight : ℝ
  cuts : Finset ℝ
  left_of : qLeft < A
  right_of : B < qRight
  left_mem : qLeft ∈ cuts
  right_mem : qRight ∈ cuts
  cuts_bounded : ∀ q ∈ cuts, qLeft ≤ q ∧ q ≤ qRight
  cuts_complete :
    horizontalLineCutSet K T y ∩ Icc qLeft qRight ⊆ (cuts : Set ℝ)
  cut_controlled : ∀ q ∈ cuts,
    Nonempty (HorizontalLineCutWitness K T y q)
  cell_classification : ∀ l r : ℝ,
    l ∈ cuts → r ∈ cuts → l < r → Ioo l r ∩ (cuts : Set ℝ) = ∅ →
      Nonempty (HorizontalCrossingCell K T y l r) ∨
        Nonempty (HorizontalSeamCell K T y l r)

/-! ## Finite scalar alphabet -/

private def contactCriticalScalars
    (C : ApproximationContext.{0}) : Set ℝ :=
  {x | ∃ a b a' b' : ↥C.region.vertices,
    ∃ delta ∈ Tiling.AxisParallel.Structure.horizontalContactDisplacements
      C.region C.centres a b a' b',
    x ≠ 0 ∧
      (x = delta ∨
       ∃ r ∈ ({a.1.re, b.1.re, a'.1.re + delta,
          b'.1.re + delta} : Set ℝ),
       ∃ s ∈ ({a.1.re, b.1.re, a'.1.re + delta,
          b'.1.re + delta} : Set ℝ), x = r - s)}

/-- The step alphabet is included explicitly because it controls global
component-boundary order, not merely local contact overlap. -/
private def transportCriticalScalars
    (C : ApproximationContext.{0}) : Set ℝ :=
  contactCriticalScalars C ∪ C.region.horizontalStepAlphabet

private structure FiniteTransportCriticalAlphabet
    (C : ApproximationContext.{0}) where
  values : Finset C.coordinateSpace
  lift : ↥(transportCriticalScalars C) → C.coordinateSpace
  lift_coe : ∀ x, (lift x : ℝ) = x.1
  lift_mem : ∀ x, lift x ∈ values

/-- Exact finite first-stage image code.  It retains the original centre and
side labels.  `mapped_cells_cover` is the finite-order fact used to choose a
source cell below a target open overlap. -/
private structure FirstStageEndpointAlignedLineCodeTransport
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    {y A B : ℝ} (source : EndpointAlignedLineCode C.region C.centres y A B) where
  cutLift : ↥source.cuts → C.coordinateSpace
  cutLift_coe : ∀ q, (cutLift q : ℝ) = q.1
  mappedCut : ↥source.cuts → ℝ
  mappedCut_formula : ∀ q, mappedCut q = mapScalar phi (cutLift q)
  mapped_strictMono : StrictMono mappedCut
  crossing_preserved : ∀ (l r : ↥source.cuts), l.1 < r.1 →
    Ioo l.1 r.1 ∩ (source.cuts : Set ℝ) = ∅ →
    ∀ X : HorizontalCrossingCell C.region C.centres y l.1 r.1,
      ∀ x ∈ Ioo (mappedCut l) (mappedCut r),
        linePoint y x ∈ P.firstCenters X.center +ᵥ D.firstRegion.openCarrier
  seam_preserved : ∀ (l r : ↥source.cuts), l.1 < r.1 →
    Ioo l.1 r.1 ∩ (source.cuts : Set ℝ) = ∅ →
    ∀ S : HorizontalSeamCell C.region C.centres y l.1 r.1,
      (∀ x ∈ Ioo (mappedCut l) (mappedCut r),
        linePoint y x ∈
          openSegment ℝ
            (D.firstPlanarHomeomorph S.a.1 + P.firstCenters S.upperCenter)
            (D.firstPlanarHomeomorph S.b.1 + P.firstCenters S.upperCenter)) ∧
      ∀ x ∈ Ioo (mappedCut l) (mappedCut r),
        linePoint y x ∈
          openSegment ℝ
            (D.firstPlanarHomeomorph S.a'.1 + P.firstCenters S.lowerCenter)
            (D.firstPlanarHomeomorph S.b'.1 + P.firstCenters S.lowerCenter)
  mapped_cells_cover : ∀ x ∈
      Ioo (mappedCut ⟨source.qLeft, source.left_mem⟩)
        (mappedCut ⟨source.qRight, source.right_mem⟩),
    x ∉ Set.range mappedCut →
    ∃ l r : ↥source.cuts,
      l.1 < r.1 ∧ Ioo l.1 r.1 ∩ (source.cuts : Set ℝ) = ∅ ∧
        x ∈ Ioo (mappedCut l) (mappedCut r)

/-! ## Exact first/second-axis contact adapters -/

private def translatedHorizontalInterval (v w : Tiling.Plane)
    (s : Tiling.Plane) : Set ℝ :=
  Ioo (min v.re w.re + s.re) (max v.re w.re + s.re)

private def ProperOpenSideOverlap
    (a b a' b' s t : Tiling.Plane) : Prop :=
  ∃ u v : Tiling.Plane,
    u ≠ v ∧ u.im = v.im ∧
      openSegment ℝ u v ⊆
        openSegment ℝ (a + s) (b + s) ∩
          openSegment ℝ (a' + t) (b' + t)

/-! ## Every-height line cells -/

private theorem horizontalLineCutSet_locallyFinite :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ y : ℝ, ∀ Q : Set ℝ,
      Bornology.IsBounded Q →
      (horizontalLineCutSet K T y ∩ Q).Finite) := by
  intro K T hTile y Q hQ
  obtain ⟨R_Q, hQball⟩ := hQ.subset_closedBall (0 : ℝ)
  obtain ⟨D, hD⟩ := K.isPolygonal.isBounded.subset_closedBall
    (0 : Tiling.Plane)
  obtain ⟨k, hk⟩ := K.nonempty
  have hDnonneg : 0 ≤ D := by
    have hkD := hD hk
    have hkD' : ‖k‖ ≤ D := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hkD
    exact (norm_nonneg k).trans hkD'
  have hVnorm (v : ↥K.vertices) : ‖(v.1 : Tiling.Plane)‖ ≤ D := by
    have hvfront := IntrinsicVertices.region_vertices_subset_frontier K v.2
    rw [Region.frontier_openCarrier_eq_frontier_support] at hvfront
    have hvSupport : (v.1 : Tiling.Plane) ∈ K.support := by
      rw [← K.isPolygonal.isClosed.closure_eq]
      exact frontier_subset_closure hvfront
    have hvBall := hD hvSupport
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hvBall
  let R : ℝ := max R_Q 0 + |y| + 4 * D + 1
  let S : Set Tiling.Plane := T ∩ Metric.closedBall 0 R
  have hSfinite : S.Finite := by
    exact (IsPacking.locallyFinite_centres hTile.2.1).1 _
      (Metric.isBounded_closedBall)
  have hVfinite : (K.vertices : Set Tiling.Plane).Finite := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet
  have hPairs : (S ×ˢ (K.vertices : Set Tiling.Plane)).Finite :=
    hSfinite.prod hVfinite
  let value : Tiling.Plane × Tiling.Plane → ℝ :=
    fun p ↦ (p.2 + p.1).re
  apply (hPairs.image value).subset
  rintro x ⟨hxCut, hxQ⟩
  obtain ⟨witness⟩ := hxCut
  rcases witness with ⟨t, v, w, hside, hcoord, hline⟩
  have hxBall : x ∈ Metric.closedBall (0 : ℝ) R_Q := hQball hxQ
  have hxNorm : ‖linePoint y x‖ ≤ max R_Q 0 + |y| := by
    rw [Complex.norm_def]
    have hxabsQ : |x| ≤ R_Q := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hxBall
    have hxabs : |x| ≤ max R_Q 0 := hxabsQ.trans (le_max_left R_Q 0)
    have hsqrt : Real.sqrt (x ^ 2 + y ^ 2) ≤ |x| + |y| := by
      have hnonneg : 0 ≤ x ^ 2 + y ^ 2 := by positivity
      have hsquare : (Real.sqrt (x ^ 2 + y ^ 2)) ^ 2 = x ^ 2 + y ^ 2 :=
        Real.sq_sqrt hnonneg
      have hsum : 0 ≤ |x| + |y| := by positivity
      have hx_sq : |x| ^ 2 = x ^ 2 := sq_abs x
      have hy_sq : |y| ^ 2 = y ^ 2 := sq_abs y
      have hxy : x ^ 2 + y ^ 2 ≤ (|x| + |y|) ^ 2 := by
        rw [← hx_sq, ← hy_sq]
        nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg y)]
      nlinarith [Real.sqrt_nonneg (x ^ 2 + y ^ 2)]
    calc
      ‖linePoint y x‖ = Real.sqrt (x ^ 2 + y ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]
        simp [linePoint]
        ring_nf
      _ ≤ |x| + |y| := hsqrt
      _ ≤ max R_Q 0 + |y| := by linarith
  have hpSegment : ‖linePoint y x - (v.1 + (t.1 : Tiling.Plane))‖ ≤
      ‖(w.1 + (t.1 : Tiling.Plane)) - (v.1 + (t.1 : Tiling.Plane))‖ := by
    exact norm_sub_le_of_mem_segment hline
  have htNorm : ‖(t.1 : Tiling.Plane)‖ ≤ R := by
    have hv := hVnorm v
    have hw := hVnorm w
    have hvw : ‖(w.1 + (t.1 : Tiling.Plane)) -
        (v.1 + (t.1 : Tiling.Plane))‖ ≤ 2 * D := by
      calc
        ‖(w.1 + (t.1 : Tiling.Plane)) - (v.1 + (t.1 : Tiling.Plane))‖ =
            ‖(w.1 : Tiling.Plane) - v.1‖ := by congr 1; ring
        _ ≤ ‖(w.1 : Tiling.Plane)‖ + ‖(v.1 : Tiling.Plane)‖ := norm_sub_le _ _
        _ ≤ 2 * D := by linarith
    have htri : ‖(t.1 : Tiling.Plane)‖ ≤
        ‖linePoint y x‖ +
          ‖linePoint y x - (v.1 + (t.1 : Tiling.Plane))‖ +
          ‖(v.1 : Tiling.Plane)‖ := by
      calc
        ‖(t.1 : Tiling.Plane)‖ =
            ‖linePoint y x -
              (linePoint y x - (v.1 + (t.1 : Tiling.Plane))) - v.1‖ := by
                congr 1; ring
        _ ≤ ‖linePoint y x -
              (linePoint y x - (v.1 + (t.1 : Tiling.Plane)))‖ +
              ‖(v.1 : Tiling.Plane)‖ := norm_sub_le _ _
        _ ≤ (‖linePoint y x‖ +
              ‖linePoint y x - (v.1 + (t.1 : Tiling.Plane))‖) +
              ‖(v.1 : Tiling.Plane)‖ := by
                gcongr
                exact norm_sub_le _ _
        _ = ‖linePoint y x‖ +
              ‖linePoint y x - (v.1 + (t.1 : Tiling.Plane))‖ +
              ‖(v.1 : Tiling.Plane)‖ := by ring
    dsimp [R]
    linarith [hxNorm, hpSegment, hVnorm v, hVnorm w, hVnorm v, hvw, hDnonneg]
  have htS : (t.1 : Tiling.Plane) ∈ S := by
    exact ⟨t.2, by simpa [S, Metric.mem_closedBall, dist_eq_norm, sub_zero] using htNorm⟩
  rcases hcoord with hcoord | hcoord
  · refine ⟨((t.1 : Tiling.Plane), (v.1 : Tiling.Plane)), ?_, ?_⟩
    · exact ⟨htS, v.2⟩
    · simp [value, hcoord, add_comm]
  · refine ⟨((t.1 : Tiling.Plane), (w.1 : Tiling.Plane)), ?_, ?_⟩
    · exact ⟨htS, w.2⟩
    · simp [value, hcoord, add_comm]

private def closedSupportUnion (K : Region) (T : Set Tiling.Plane) :
    Set Tiling.Plane :=
  ⋃ t : ↥T, (t.1 : Tiling.Plane) +ᵥ K.support

private theorem closedTranslatedSupports_cover :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T univ → closedSupportUnion K T = univ := by
  intro K T hTile
  have hSupport : regularSupport K T = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
  have hClosure : closure (openUnion K T) = closedSupportUnion K T :=
    closure_openUnion_eq_iUnion_support hTile.2.1
  apply Set.Subset.antisymm (fun _ _ ↦ Set.mem_univ _)
  intro z _
  rw [← hClosure]
  apply interior_subset
  change z ∈ regularSupport K T
  rw [hSupport]
  exact Set.mem_univ z

private theorem horizontalLineCutSet_unbounded :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ y : ℝ,
      ¬ BddAbove (horizontalLineCutSet K T y) ∧
        ¬ BddBelow (horizontalLineCutSet K T y)) := by
  intro K T hTile y
  obtain ⟨D, hD⟩ := K.isPolygonal.isBounded.subset_closedBall
    (0 : Tiling.Plane)
  obtain ⟨k₀, hk₀⟩ := K.nonempty
  have hDnonneg : 0 ≤ D := by
    have hkD := hD hk₀
    have hkD' : ‖k₀‖ ≤ D := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hkD
    exact (norm_nonneg k₀).trans hkD'
  have hcoord_re {v w q : Tiling.Plane} (hvw : v.re = w.re)
      (hq : q ∈ segment ℝ v w) : q.re = v.re := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    rw [hvw]
    ring
  have hcoord_im {v w q : Tiling.Plane} (hvw : v.im = w.im)
      (hq : q ∈ segment ℝ v w) : q.im = v.im := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im,
      smul_eq_mul]
    rw [hvw]
    ring
  have hcut_from_frontier : ∀ (t : ↥T) (p : Tiling.Plane),
      p ∈ frontier ((t.1 : Tiling.Plane) +ᵥ K.support) → p.im = y →
      ∃ c : ℝ, c ∈ horizontalLineCutSet K T y ∧
        ∃ W : HorizontalLineCutWitness K T y c, W.center = t := by
    intro t p hpfront hpim
    have hqfront : p - t.1 ∈ frontier K.support := by
      rw [Tiling.AxisParallel.frontier_vadd_eq] at hpfront
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, sub_eq_add_neg,
        add_comm, vadd_eq_add] using hpfront
    by_cases hpvertex : p - t.1 ∈ K.vertices
    · obtain ⟨w, hwne, hwtrans, hside⟩ :=
        IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical
          ⟨p - t.1, hpvertex⟩
      let v : ↥K.vertices := ⟨p - t.1, hpvertex⟩
      have hside' : IsIntrinsicSide K v w := by
        refine ⟨hwne.symm, ?_, hside⟩
        exact Or.inl hwtrans.symm
      have hpEq : p = v.1 + (t.1 : Tiling.Plane) := by
        simp [v]
      have hy : v.1.im + (t.1 : Tiling.Plane).im = y := by
        simpa [hpEq] using hpim
      have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
          segment ℝ (v.1 + (t.1 : Tiling.Plane))
            (w.1 + (t.1 : Tiling.Plane)) := by
        have hline : linePoint y (v.1 + (t.1 : Tiling.Plane)).re = p := by
          apply Complex.ext
          · simp [linePoint, hpEq]
          · simp [linePoint, hpim]
        rw [hline]
        have hvadd := vadd_segment (𝕜 := ℝ) (t.1 : Tiling.Plane) v.1 w.1
        have hseg : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
            ((t.1 : Tiling.Plane) +ᵥ w.1) := by
          have hvseg : (t.1 : Tiling.Plane) +ᵥ v.1 ∈
              segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                ((t.1 : Tiling.Plane) +ᵥ w.1) := by
            rw [← hvadd]
            exact vadd_mem_vadd_set (left_mem_segment ℝ v.1 w.1)
          have hpt : p = (t.1 : Tiling.Plane) +ᵥ v.1 := by
            simpa only [vadd_eq_add, add_comm] using hpEq
          rw [hpt]
          simpa only [vadd_eq_add, add_comm] using hvseg
        simpa [vadd_eq_add, add_comm] using hseg
      refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
      · exact ⟨⟨t, v, w, hside', Or.inl rfl, hmeet⟩⟩
      · exact ⟨⟨t, v, w, hside', Or.inl rfl, hmeet⟩, rfl⟩
    · obtain ⟨axis, v, w, hvw, htrans, hpseg, hside⟩ :=
        IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K (p - t.1)
          hqfront hpvertex
      cases axis with
      | vertical =>
          have hvwRe : v.1.re = w.1.re := htrans
          have hpseg' : p - t.1 ∈ segment ℝ v.1 w.1 :=
            openSegment_subset_segment ℝ v.1 w.1 hpseg
          have hpre : (p - t.1).re = v.1.re := hcoord_re hvwRe hpseg'
          have hpre' : p.re = (v.1 + (t.1 : Tiling.Plane)).re := by
            dsimp only [Complex.sub_re] at hpre
            dsimp only [Complex.add_re]
            linarith
          have hpEq : p = linePoint y (v.1 + (t.1 : Tiling.Plane)).re := by
            apply Complex.ext
            · simp [linePoint, hpre']
            · simp [linePoint, hpim]
          have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
              segment ℝ (v.1 + (t.1 : Tiling.Plane))
                (w.1 + (t.1 : Tiling.Plane)) := by
            have hline : linePoint y (v.1 + (t.1 : Tiling.Plane)).re = p := hpEq.symm
            rw [hline]
            have hvadd := vadd_segment (𝕜 := ℝ) (t.1 : Tiling.Plane) v.1 w.1
            have hseg : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                ((t.1 : Tiling.Plane) +ᵥ w.1) := by
              rw [← hvadd]
              have hpseg'' : (t.1 : Tiling.Plane) +ᵥ (p - t.1) ∈
                  (t.1 : Tiling.Plane) +ᵥ segment ℝ v.1 w.1 :=
                vadd_mem_vadd_set hpseg'
              have hpseg''' : (t.1 : Tiling.Plane) +ᵥ (p - t.1) ∈
                  segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                    ((t.1 : Tiling.Plane) +ᵥ w.1) := by
                simpa only [hvadd] using hpseg''
              have hpt : (t.1 : Tiling.Plane) +ᵥ (p - t.1) = p := by
                rw [vadd_eq_add]
                abel
              have hpseg'''' : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                  ((t.1 : Tiling.Plane) +ᵥ w.1) := by
                rw [← hpt]
                exact hpseg'''
              simpa only [hvadd] using hpseg''''
            simpa [vadd_eq_add, add_comm] using hseg
          refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
          · exact ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩, Or.inl rfl, hmeet⟩⟩
          · exact ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩, Or.inl rfl, hmeet⟩, rfl⟩
      | horizontal =>
          have hvwIm : v.1.im = w.1.im := htrans
          have hpseg' : p - t.1 ∈ segment ℝ v.1 w.1 :=
            openSegment_subset_segment ℝ v.1 w.1 hpseg
          have hpim' : (p - t.1).im = v.1.im := hcoord_im hvwIm hpseg'
          have hvEq : linePoint y (v.1 + (t.1 : Tiling.Plane)).re =
              v.1 + (t.1 : Tiling.Plane) := by
            apply Complex.ext
            · simp [linePoint]
            · have hy : v.1.im + t.1.im = y := by
                dsimp only [Complex.sub_im] at hpim'
                linarith [hpim, hpim']
              simp [linePoint, hy]
          have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
              segment ℝ (v.1 + (t.1 : Tiling.Plane))
                (w.1 + (t.1 : Tiling.Plane)) := by
            rw [hvEq]
            exact left_mem_segment ℝ _ _
          refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
          · exact ⟨⟨t, v, w, ⟨hvw, Or.inr hvwIm, hside⟩, Or.inl rfl, hmeet⟩⟩
          · exact ⟨⟨t, v, w, ⟨hvw, Or.inr hvwIm, hside⟩, Or.inl rfl, hmeet⟩, rfl⟩
  have hvertexSupport : ∀ v : ↥K.vertices, (v.1 : Tiling.Plane) ∈ K.support := by
    intro v
    have hvfront := IntrinsicVertices.region_vertices_subset_frontier K v.2
    rw [Region.frontier_openCarrier_eq_frontier_support] at hvfront
    rw [← K.isPolygonal.isClosed.closure_eq]
    exact frontier_subset_closure hvfront
  have hcut_near : ∀ X : ℝ, ∃ c ∈ horizontalLineCutSet K T y,
      |c - X| ≤ 2 * D := by
    intro X
    have hzcover : linePoint y X ∈ closedSupportUnion K T := by
      rw [closedTranslatedSupports_cover hTile]
      exact Set.mem_univ _
    rw [closedSupportUnion, Set.mem_iUnion] at hzcover
    obtain ⟨t, hzt⟩ := hzcover
    rw [mem_vadd_set] at hzt
    obtain ⟨kX, hkX, hlineX⟩ := hzt
    let S : Set Tiling.Plane :=
      ((t.1 : Tiling.Plane) +ᵥ K.support) ∩ {z | z.im = y}
    have hScompact : IsCompact S := by
      exact (K.isPolygonal.isCompact.vadd (t.1 : Tiling.Plane)).inter_right
        (isClosed_eq Complex.continuous_im continuous_const)
    have hSne : S.Nonempty := by
      refine ⟨linePoint y X, ⟨⟨kX, hkX, hlineX⟩, ?_⟩⟩
      simp [linePoint]
    let R : Set ℝ := Complex.re '' S
    have hRcompact : IsCompact R := hScompact.image Complex.continuous_re
    have hRne : R.Nonempty := hSne.image _
    obtain ⟨r, hrR, hrmax⟩ :=
      hRcompact.exists_isMaxOn hRne continuous_id.continuousOn
    obtain ⟨p, hpS, hpr⟩ := hrR
    have hpim : p.im = y := hpS.2
    have hpSupport : p ∈ (t.1 : Tiling.Plane) +ᵥ K.support := hpS.1
    have hpNotInterior : p ∉ interior ((t.1 : Tiling.Plane) +ᵥ K.support) := by
      intro hpint
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hpint
      let q := linePoint y (p.re + ε / 2)
      have hpLine : p = linePoint y p.re := by
        apply Complex.ext <;> simp [linePoint, hpim]
      have hqp : dist q p < ε := by
        rw [hpLine, dist_eq_norm]
        simp [q, linePoint, abs_of_pos hε]
        linarith
      have hqS : q ∈ S := by
        refine ⟨interior_subset (hball (Metric.mem_ball.mpr hqp)), ?_⟩
        simp [q, linePoint]
      have hqR : q.re ∈ R := ⟨q, hqS, rfl⟩
      have hmax := hrmax hqR
      dsimp only [id] at hmax
      rw [← hpr] at hmax
      dsimp [q] at hmax
      simp [linePoint] at hmax
      linarith
    have hpfront : p ∈ frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
      rw [frontier]
      exact ⟨subset_closure hpSupport, hpNotInterior⟩
    obtain ⟨c, hc, hW⟩ := hcut_from_frontier t p hpfront hpim
    refine ⟨c, hc, ?_⟩
    obtain ⟨W, hWcenter⟩ := hW
    rcases W with ⟨center, v, w, hside, hcoord, hline⟩
    have hcenter : center = t := hWcenter
    subst center
    have hplaced (u : ↥K.vertices) :
        (u.1 + (t.1 : Tiling.Plane)) ∈
          (t.1 : Tiling.Plane) +ᵥ K.support := by
      refine ⟨u.1, hvertexSupport u, ?_⟩
      simp [vadd_eq_add, add_comm]
    have hbase : linePoint y X ∈
        (t.1 : Tiling.Plane) +ᵥ K.support := by
      exact ⟨kX, hkX, hlineX⟩
    have hreal (u : ↥K.vertices) :
        |(u.1 + (t.1 : Tiling.Plane)).re - X| ≤ 2 * D := by
      obtain ⟨ke, hke, he⟩ := (mem_vadd_set.mp (hplaced u))
      obtain ⟨kb, hkb, hb⟩ := (mem_vadd_set.mp hbase)
      have hnorm : ‖(u.1 + (t.1 : Tiling.Plane)) - linePoint y X‖ ≤
          2 * D := by
        calc
          ‖(u.1 + (t.1 : Tiling.Plane)) - linePoint y X‖ = ‖ke - kb‖ := by
            rw [← he, ← hb]
            congr 1
            simp [vadd_eq_add, add_comm]
          _ ≤ ‖ke‖ + ‖kb‖ := norm_sub_le _ _
          _ ≤ 2 * D := by
            have hke' : ‖ke‖ ≤ D := by
              simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hD hke
            have hkb' : ‖kb‖ ≤ D := by
              simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hD hkb
            linarith
      calc
        |(u.1 + (t.1 : Tiling.Plane)).re - X| =
            |((u.1 + (t.1 : Tiling.Plane)) - linePoint y X).re| := by
              simp [linePoint]
        _ ≤ ‖(u.1 + (t.1 : Tiling.Plane)) - linePoint y X‖ :=
          Complex.abs_re_le_norm _
        _ ≤ 2 * D := hnorm
    rcases hcoord with hcoord | hcoord
    · simpa [hcoord] using hreal v
    · simpa [hcoord] using hreal w
  constructor
  · intro hBound
    rcases hBound with ⟨B, hB⟩
    obtain ⟨c, hc, hcNear⟩ := hcut_near (B + 2 * D + 1)
    have hcB : c ≤ B := hB hc
    have hcLower : B + 1 ≤ c := by
      have h := (abs_le.mp hcNear).1
      linarith
    linarith
  · intro hBound
    rcases hBound with ⟨B, hB⟩
    obtain ⟨c, hc, hcNear⟩ := hcut_near (B - 2 * D - 1)
    have hcB : B ≤ c := hB hc
    have hcUpper : c ≤ B - 1 := by
      have h := (abs_le.mp hcNear).2
      linarith
    linarith

private theorem frontierPoint_horizontalLineCutWitness
    {K : Region} {T : Set Tiling.Plane} {y : ℝ}
    : ∀ (t : ↥T) (p : Tiling.Plane),
      p ∈ frontier ((t.1 : Tiling.Plane) +ᵥ K.support) → p.im = y →
      ∃ c : ℝ, c ∈ horizontalLineCutSet K T y ∧
        ∃ W : HorizontalLineCutWitness K T y c, W.center = t ∧
          (c = p.re ∨
            ∃ v w : ↥K.vertices,
              IsIntrinsicHorizontalSide K v w ∧
                p ∈ openSegment ℝ
                  (v.1 + (t.1 : Tiling.Plane))
                  (w.1 + (t.1 : Tiling.Plane))) := by
  intro t p hpfront hpim
  have hcoord_re {v w q : Tiling.Plane} (hvw : v.re = w.re)
      (hq : q ∈ segment ℝ v w) : q.re = v.re := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    rw [hvw]
    ring
  have hcoord_im {v w q : Tiling.Plane} (hvw : v.im = w.im)
      (hq : q ∈ segment ℝ v w) : q.im = v.im := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im,
      smul_eq_mul]
    rw [hvw]
    ring
  have hqfront : p - t.1 ∈ frontier K.support := by
    rw [Tiling.AxisParallel.frontier_vadd_eq] at hpfront
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_sub, sub_eq_add_neg,
      add_comm, vadd_eq_add] using hpfront
  by_cases hpvertex : p - t.1 ∈ K.vertices
  · obtain ⟨w, hwne, hwtrans, hside⟩ :=
      IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical
        ⟨p - t.1, hpvertex⟩
    let v : ↥K.vertices := ⟨p - t.1, hpvertex⟩
    have hside' : IsIntrinsicSide K v w := by
      refine ⟨hwne.symm, ?_, hside⟩
      exact Or.inl hwtrans.symm
    have hpEq : p = v.1 + (t.1 : Tiling.Plane) := by
      simp [v]
    have hy : v.1.im + (t.1 : Tiling.Plane).im = y := by
      simpa [hpEq] using hpim
    have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
        segment ℝ (v.1 + (t.1 : Tiling.Plane))
          (w.1 + (t.1 : Tiling.Plane)) := by
      have hline : linePoint y (v.1 + (t.1 : Tiling.Plane)).re = p := by
        apply Complex.ext
        · simp [linePoint, hpEq]
        · simp [linePoint, hpim]
      rw [hline]
      have hvadd := vadd_segment (𝕜 := ℝ) (t.1 : Tiling.Plane) v.1 w.1
      have hseg : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
          ((t.1 : Tiling.Plane) +ᵥ w.1) := by
        have hvseg : (t.1 : Tiling.Plane) +ᵥ v.1 ∈
            segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
              ((t.1 : Tiling.Plane) +ᵥ w.1) := by
          rw [← hvadd]
          exact vadd_mem_vadd_set (left_mem_segment ℝ v.1 w.1)
        have hpt : p = (t.1 : Tiling.Plane) +ᵥ v.1 := by
          simpa only [vadd_eq_add, add_comm] using hpEq
        rw [hpt]
        simpa only [vadd_eq_add, add_comm] using hvseg
      simpa [vadd_eq_add, add_comm] using hseg
    refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
    · exact ⟨⟨t, v, w, hside', Or.inl rfl, hmeet⟩⟩
    · refine ⟨⟨t, v, w, hside', Or.inl rfl, hmeet⟩, rfl, Or.inl ?_⟩
      rw [hpEq]
  · obtain ⟨axis, v, w, hvw, htrans, hpseg, hside⟩ :=
      IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K (p - t.1)
        hqfront hpvertex
    cases axis with
    | vertical =>
        have hvwRe : v.1.re = w.1.re := htrans
        have hpseg' : p - t.1 ∈ segment ℝ v.1 w.1 :=
          openSegment_subset_segment ℝ v.1 w.1 hpseg
        have hpre : (p - t.1).re = v.1.re := hcoord_re hvwRe hpseg'
        have hpre' : p.re = (v.1 + (t.1 : Tiling.Plane)).re := by
          dsimp only [Complex.sub_re] at hpre
          dsimp only [Complex.add_re]
          linarith
        have hpEq : p = linePoint y (v.1 + (t.1 : Tiling.Plane)).re := by
          apply Complex.ext
          · simp [linePoint, hpre']
          · simp [linePoint, hpim]
        have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
            segment ℝ (v.1 + (t.1 : Tiling.Plane))
              (w.1 + (t.1 : Tiling.Plane)) := by
          have hline : linePoint y (v.1 + (t.1 : Tiling.Plane)).re = p := hpEq.symm
          rw [hline]
          have hvadd := vadd_segment (𝕜 := ℝ) (t.1 : Tiling.Plane) v.1 w.1
          have hseg : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
              ((t.1 : Tiling.Plane) +ᵥ w.1) := by
            rw [← hvadd]
            have hpseg'' : (t.1 : Tiling.Plane) +ᵥ (p - t.1) ∈
                (t.1 : Tiling.Plane) +ᵥ segment ℝ v.1 w.1 :=
              vadd_mem_vadd_set hpseg'
            have hpseg''' : (t.1 : Tiling.Plane) +ᵥ (p - t.1) ∈
                segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                  ((t.1 : Tiling.Plane) +ᵥ w.1) := by
              simpa only [hvadd] using hpseg''
            have hpt : (t.1 : Tiling.Plane) +ᵥ (p - t.1) = p := by
              rw [vadd_eq_add]
              abel
            have hpseg'''' : p ∈ segment ℝ ((t.1 : Tiling.Plane) +ᵥ v.1)
                ((t.1 : Tiling.Plane) +ᵥ w.1) := by
              rw [← hpt]
              exact hpseg'''
            simpa only [hvadd] using hpseg''''
          simpa [vadd_eq_add, add_comm] using hseg
        refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
        · exact ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩, Or.inl rfl, hmeet⟩⟩
        · exact ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩, Or.inl rfl, hmeet⟩,
            rfl, Or.inl hpre'.symm⟩
    | horizontal =>
        have hvwIm : v.1.im = w.1.im := htrans
        have hpseg' : p - t.1 ∈ segment ℝ v.1 w.1 :=
          openSegment_subset_segment ℝ v.1 w.1 hpseg
        have hpim' : (p - t.1).im = v.1.im := hcoord_im hvwIm hpseg'
        have hvEq : linePoint y (v.1 + (t.1 : Tiling.Plane)).re =
            v.1 + (t.1 : Tiling.Plane) := by
          apply Complex.ext
          · simp [linePoint]
          · have hy : v.1.im + t.1.im = y := by
              dsimp only [Complex.sub_im] at hpim'
              linarith [hpim, hpim']
            simp [linePoint, hy]
        have hmeet : linePoint y (v.1 + (t.1 : Tiling.Plane)).re ∈
            segment ℝ (v.1 + (t.1 : Tiling.Plane))
              (w.1 + (t.1 : Tiling.Plane)) := by
          rw [hvEq]
          exact left_mem_segment ℝ _ _
        refine ⟨(v.1 + (t.1 : Tiling.Plane)).re, ?_, ?_⟩
        · exact ⟨⟨t, v, w, ⟨hvw, Or.inr hvwIm, hside⟩, Or.inl rfl, hmeet⟩⟩
        · refine ⟨⟨t, v, w, ⟨hvw, Or.inr hvwIm, hside⟩, Or.inl rfl, hmeet⟩,
            rfl, Or.inr ⟨v, w, ⟨hvw, hvwIm, hside⟩, ?_⟩⟩
          rw [show v.1 + (t.1 : Tiling.Plane) =
                (t.1 : Tiling.Plane) +ᵥ v.1 by simp [add_comm],
            show w.1 + (t.1 : Tiling.Plane) =
                (t.1 : Tiling.Plane) +ᵥ w.1 by simp [add_comm],
            ← vadd_openSegment ℝ]
          exact ⟨p - t.1, hpseg, by simp [vadd_eq_add]⟩

private theorem fct_horizontal_point_mem_openSegment_iff
    {a b : Tiling.Plane} (_hab : a ≠ b) (hh : a.im = b.im) (x : ℝ) :
    ((x : ℂ) + a.im * Complex.I) ∈ openSegment ℝ a b ↔
      x ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor <;> rintro ⟨s, hs, h⟩
  · exact ⟨s, hs, by simpa using congrArg Complex.re h⟩
  · refine ⟨s, hs, ?_⟩
    apply Complex.ext
    · simpa using congrArg id h
    · simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        Complex.smul_im, smul_eq_mul]
      rw [hh]
      ring

private theorem fct_im_eq_of_mem_openSegment_horizontal
    {a b p : Tiling.Plane} (hab : a.im = b.im)
    (hp : p ∈ openSegment ℝ a b) : p.im = a.im := by
  rw [openSegment_eq_image] at hp
  obtain ⟨s, _hs, rfl⟩ := hp
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem fct_re_mem_openSegment_of_mem
    {a b p : Tiling.Plane} (hp : p ∈ openSegment ℝ a b) :
    p.re ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image] at hp ⊢
  obtain ⟨s, hs, h⟩ := hp
  exact ⟨s, hs, by simpa using congrArg Complex.re h⟩


private theorem horizontalLineCell_constantMembership :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ (y l r : ℝ), l < r →
      Ioo l r ∩ horizontalLineCutSet K T y = ∅ →
      ∀ t : ↥T,
        (∀ x ∈ Ioo l r,
          linePoint y x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) ∨
        (∀ x ∈ Ioo l r,
          linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)) := by
  intro K T _hTile y l r hlr hnocuts t
  have hlineCont : Continuous (linePoint y) := by
    change Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I)
    fun_prop
  let U : Set ℝ :=
    Ioo l r ∩ linePoint y ⁻¹' ((t.1 : Tiling.Plane) +ᵥ K.openCarrier)
  let V : Set ℝ := Ioo l r \ U
  have hUopen : IsOpen U := by
    exact isOpen_Ioo.inter
      ((isOpen_interior.vadd (t.1 : Tiling.Plane)).preimage hlineCont)
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro x hxV
    have hxI : x ∈ Ioo l r := hxV.1
    have hxNotOpen : linePoint y x ∉
        (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
      intro hxOpen
      exact hxV.2 ⟨hxI, hxOpen⟩
    by_cases hxSupport : linePoint y x ∈
        (t.1 : Tiling.Plane) +ᵥ K.support
    · have hxFrontier : linePoint y x ∈
          frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
        rw [frontier]
        refine ⟨subset_closure hxSupport, ?_⟩
        rw [interior_vadd]
        exact hxNotOpen
      obtain ⟨c, hcCut, W, hWcenter, hcEq | ⟨v, w, hside, hpSide⟩⟩ :=
        frontierPoint_horizontalLineCutWitness (K := K) (T := T) (y := y)
          t (linePoint y x)
          hxFrontier (by simp [linePoint])
      · have hcx : c = x := by simpa [linePoint] using hcEq
        have hxCut : x ∈ horizontalLineCutSet K T y := hcx ▸ hcCut
        have hxInter : x ∈ Ioo l r ∩ horizontalLineCutSet K T y :=
          ⟨hxI, hxCut⟩
        rw [hnocuts] at hxInter
        exact hxInter.elim
      · let a : Tiling.Plane := v.1 + (t.1 : Tiling.Plane)
        let b : Tiling.Plane := w.1 + (t.1 : Tiling.Plane)
        have hab : a ≠ b := by
          intro habEq
          apply hside.1
          apply add_right_cancel (b := (t.1 : Tiling.Plane))
          simpa [a, b] using habEq
        have habIm : a.im = b.im := by simp [a, b, hside.2.1]
        have hxJ : x ∈ openSegment ℝ a.re b.re := by
          have hpRe := fct_re_mem_openSegment_of_mem hpSide
          simpa [a, b, linePoint] using hpRe
        have hJopen : IsOpen (openSegment ℝ a.re b.re) := by
          have habRe : a.re ≠ b.re := by
            intro hre
            exact hab (Complex.ext hre habIm)
          rcases lt_or_gt_of_ne habRe with habLt | hbaLt
          · rw [openSegment_eq_Ioo habLt]
            exact isOpen_Ioo
          · rw [openSegment_symm, openSegment_eq_Ioo hbaLt]
            exact isOpen_Ioo
        have hy : y = a.im := by
          have hpIm : (linePoint y x).im = a.im := by
            rw [show a = v.1 + (t.1 : Tiling.Plane) by rfl]
            exact fct_im_eq_of_mem_openSegment_horizontal habIm hpSide
          simpa [linePoint] using hpIm
        have hedgePlaced : openSegment ℝ a b ⊆
            frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
          rw [show a = (t.1 : Tiling.Plane) +ᵥ v.1 by simp [a, add_comm],
            show b = (t.1 : Tiling.Plane) +ᵥ w.1 by simp [b, add_comm],
            ← vadd_openSegment ℝ, Tiling.AxisParallel.frontier_vadd_eq]
          rintro z ⟨q, hq, rfl⟩
          exact ⟨q, (hside.2.2 hq).1, rfl⟩
        filter_upwards [hJopen.mem_nhds hxJ, isOpen_Ioo.mem_nhds hxI] with z hzJ hzI
        refine ⟨hzI, ?_⟩
        intro hzU
        have hzSide : linePoint y z ∈ openSegment ℝ a b := by
          rw [show linePoint y z = (z : ℂ) + a.im * Complex.I by
            simp [linePoint, hy]]
          exact (fct_horizontal_point_mem_openSegment_iff hab habIm z).2 hzJ
        have hzFrontier := hedgePlaced hzSide
        have hzOpen : linePoint y z ∈
            interior ((t.1 : Tiling.Plane) +ᵥ K.support) := by
          rw [interior_vadd]
          exact hzU.2
        exact hzFrontier.2 hzOpen
    · have hOutsideOpen : IsOpen
          (((t.1 : Tiling.Plane) +ᵥ K.support)ᶜ) :=
        (K.isPolygonal.isClosed.vadd (t.1 : Tiling.Plane)).isOpen_compl
      have hxOutside : linePoint y x ∈
          ((t.1 : Tiling.Plane) +ᵥ K.support)ᶜ := hxSupport
      filter_upwards [isOpen_Ioo.mem_nhds hxI,
        hlineCont.continuousAt (hOutsideOpen.mem_nhds hxOutside)] with z hzI hzOutside
      refine ⟨hzI, ?_⟩
      intro hzU
      apply hzOutside
      have hzOpen := hzU.2
      change linePoint y z ∈
        (t.1 : Tiling.Plane) +ᵥ K.openCarrier at hzOpen
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzOpen ⊢
      exact interior_subset hzOpen
  have hUVdis : Disjoint U V := by
    rw [Set.disjoint_left]
    exact fun _ hxU hxV ↦ hxV.2 hxU
  have hUVcover : Ioo l r ⊆ U ∪ V := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl hxU
    · exact Or.inr ⟨hx, hxU⟩
  rcases isPreconnected_Ioo.subset_or_subset hUopen hVopen hUVdis hUVcover with hU | hV
  · left
    exact fun x hx ↦ (hU hx).2
  · right
    intro x hx hxOpen
    exact (hV hx).2 ⟨hx, hxOpen⟩

private theorem endpointAlignedLineCode_exists_of_classification
    (hclassify : (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ (y l r : ℝ), l < r →
      l ∈ horizontalLineCutSet K T y →
      r ∈ horizontalLineCutSet K T y →
      Ioo l r ∩ horizontalLineCutSet K T y = ∅ →
      Nonempty (HorizontalCrossingCell K T y l r) ∨
        Nonempty (HorizontalSeamCell K T y l r))) :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ y A B : ℝ, A ≤ B →
      Nonempty (EndpointAlignedLineCode K T y A B)) := by
  intro K T hTile y A B _hAB
  have hunbounded := horizontalLineCutSet_unbounded hTile y
  obtain ⟨qLeft, hqLeftCut, hqLeft⟩ :=
    not_bddBelow_iff.mp hunbounded.2 A
  obtain ⟨qRight, hqRightCut, hqRight⟩ :=
    not_bddAbove_iff.mp hunbounded.1 B
  let S : Set ℝ := horizontalLineCutSet K T y ∩ Icc qLeft qRight
  have hSfinite : S.Finite := by
    exact horizontalLineCutSet_locallyFinite hTile y (Icc qLeft qRight)
      (Metric.isBounded_Icc qLeft qRight)
  let cuts : Finset ℝ := hSfinite.toFinset
  have hmem (q : ℝ) : q ∈ cuts ↔
      q ∈ horizontalLineCutSet K T y ∧ q ∈ Icc qLeft qRight := by
    rw [show q ∈ cuts ↔ q ∈ S by exact hSfinite.mem_toFinset]
    rfl
  have hLeftRight : qLeft ≤ qRight :=
    ((hqLeft.trans_le _hAB).trans hqRight).le
  have hqLeftMem : qLeft ∈ cuts := by
    exact (hmem qLeft).2
      ⟨hqLeftCut, le_rfl, hLeftRight⟩
  have hqRightMem : qRight ∈ cuts := by
    exact (hmem qRight).2
      ⟨hqRightCut, hLeftRight, le_rfl⟩
  refine ⟨{
    qLeft := qLeft
    qRight := qRight
    cuts := cuts
    left_of := hqLeft
    right_of := hqRight
    left_mem := hqLeftMem
    right_mem := hqRightMem
    cuts_bounded := ?_
    cuts_complete := ?_
    cut_controlled := ?_
    cell_classification := ?_ }⟩
  · intro q hq
    exact (hmem q).1 hq |>.2
  · intro q hq
    exact (hmem q).2 hq
  · intro q hq
    exact (hmem q).1 hq |>.1
  · intro l r hlmem hrmem hlr hnocuts
    apply hclassify hTile y l r hlr ((hmem l).1 hlmem).1
      ((hmem r).1 hrmem).1
    apply Set.Subset.antisymm
    · intro x hx
      have hlBound := ((hmem l).1 hlmem).2
      have hrBound := ((hmem r).1 hrmem).2
      have hxCuts : x ∈ cuts := by
        apply (hmem x).2
        exact ⟨hx.2,
          le_trans hlBound.1 hx.1.1.le,
          le_trans hx.1.2.le hrBound.2⟩
      have hxEmpty : x ∈ Ioo l r ∩ (cuts : Set ℝ) := ⟨hx.1, hxCuts⟩
      rw [hnocuts] at hxEmpty
      exact hxEmpty
    · exact Set.empty_subset _

private theorem finite_iUnion_univ
    {ι α : Type*} [Finite ι] (s : ι → Set α)
    (hs : ∀ i, (s i).Finite) : (⋃ i, s i).Finite := by
  apply Set.Finite.iUnion Set.finite_univ
  · intro i _
    exact hs i
  · intro i hi
    exact (hi (Set.mem_univ i)).elim

private theorem finite_contact_scalar_skeleton
    (C : ApproximationContext.{0})
    (hfinite : ∀ a b a' b' : ↥C.region.vertices,
      (Tiling.AxisParallel.Structure.horizontalContactDisplacements
        C.region C.centres a b a' b').Finite) :
    (⋃ a : ↥C.region.vertices, ⋃ b : ↥C.region.vertices,
      ⋃ a' : ↥C.region.vertices, ⋃ b' : ↥C.region.vertices,
        {x : ℝ | ∃ delta ∈ Tiling.AxisParallel.Structure.horizontalContactDisplacements
            C.region C.centres a b a' b',
          x ≠ 0 ∧
            (x = delta ∨
              ∃ r ∈ ({a.1.re, b.1.re, a'.1.re + delta,
                b'.1.re + delta} : Set ℝ),
                ∃ s ∈ ({a.1.re, b.1.re, a'.1.re + delta,
                  b'.1.re + delta} : Set ℝ), x = r - s)}).Finite := by
  classical
  let hV : C.region.vertices.Finite := by
    rw [← C.region.coe_vertexFinset]
    exact C.region.vertexFinset.finite_toSet
  let _ : Fintype (↥C.region.vertices) := hV.fintype
  apply finite_iUnion_univ
  intro a
  apply finite_iUnion_univ
  intro b
  apply finite_iUnion_univ
  intro a'
  apply finite_iUnion_univ
  intro b'
  let fiber : ℝ → Set ℝ := fun delta ↦
    {x | x ≠ 0 ∧
      (x = delta ∨ ∃ r ∈ ({a.1.re, b.1.re, a'.1.re + delta,
        b'.1.re + delta} : Set ℝ),
        ∃ s ∈ ({a.1.re, b.1.re, a'.1.re + delta,
          b'.1.re + delta} : Set ℝ), x = r - s)}
  have hfiber (delta : ℝ) : (fiber delta).Finite := by
    let hends :
        ({a.1.re, b.1.re, a'.1.re + delta,
          b'.1.re + delta} : Set ℝ).Finite := Set.toFinite _
    have hdiff :
        (Set.image2 (· - ·)
          ({a.1.re, b.1.re, a'.1.re + delta,
            b'.1.re + delta} : Set ℝ)
          {a.1.re, b.1.re, a'.1.re + delta,
            b'.1.re + delta}).Finite :=
      Set.Finite.image2 (· - ·) hends hends
    have hbase :
        ({delta} ∪ Set.image2 (· - ·)
          ({a.1.re, b.1.re, a'.1.re + delta,
            b'.1.re + delta} : Set ℝ)
          {a.1.re, b.1.re, a'.1.re + delta,
            b'.1.re + delta}).Finite := (Set.toFinite _).union hdiff
    apply hbase.subset
    intro x hx
    rcases hx with ⟨_hx0, hxd | ⟨r, hr, s, hs, hxs⟩⟩
    · exact Or.inl hxd
    · exact Or.inr ⟨r, hr, s, hs, hxs.symm⟩
  have hbi : (⋃ delta ∈
      Tiling.AxisParallel.Structure.horizontalContactDisplacements
        C.region C.centres a b a' b', fiber delta).Finite :=
    Set.Finite.biUnion (hfinite a b a' b') (by
      intro delta _hdelta
      exact hfiber delta)
  apply hbi.subset
  intro x hx
  rcases hx with ⟨delta, hdelta, hx0, hxalt⟩
  exact Set.mem_iUnion.mpr ⟨delta,
    Set.mem_iUnion.mpr ⟨hdelta, ⟨hx0, hxalt⟩⟩⟩

private theorem contactCriticalScalars_finite
    (C : ApproximationContext.{0})
    (hfinite : ∀ a b a' b' : ↥C.region.vertices,
      (Tiling.AxisParallel.Structure.horizontalContactDisplacements
        C.region C.centres a b a' b').Finite) :
    (contactCriticalScalars C).Finite := by
  have hs := finite_contact_scalar_skeleton C hfinite
  apply hs.subset
  intro x hx
  rcases hx with ⟨a, b, a', b', delta, hdelta, hx0, hxalt⟩
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b,
    Set.mem_iUnion.mpr ⟨a', Set.mem_iUnion.mpr ⟨b',
      ⟨delta, hdelta, hx0, hxalt⟩⟩⟩⟩⟩

private theorem transportCriticalScalars_finite :
    (∀ (C : ApproximationContext.{0}),
    (∀ a b a' b' : ↥C.region.vertices,
      (Tiling.AxisParallel.Structure.horizontalContactDisplacements
        C.region C.centres a b a' b').Finite) →
    (transportCriticalScalars C).Finite) := by
  intro C hfinite
  exact (contactCriticalScalars_finite C hfinite).union
    C.region.horizontalStepAlphabet.finite_toSet

private theorem contactScalar_mem_coordinateSpace
    {C : ApproximationContext.{0}} {a b a' b' : ↥C.region.vertices}
    {delta x : ℝ}
    (hdelta : delta ∈ Tiling.AxisParallel.Structure.horizontalContactDisplacements
      C.region C.centres a b a' b')
    (hx : x ≠ 0 ∧
      (x = delta ∨
        ∃ r ∈ ({a.1.re, b.1.re, a'.1.re + delta,
          b'.1.re + delta} : Set ℝ),
          ∃ s ∈ ({a.1.re, b.1.re, a'.1.re + delta,
            b'.1.re + delta} : Set ℝ), x = r - s)) :
    x ∈ C.coordinateSpace := by
  rw [horizontalContactDisplacements_iff] at hdelta
  rcases hdelta with ⟨_, _, _, _, _, _, t, s, hdelta, _, _⟩
  have hDelta : delta ∈ C.coordinateSpace := by
    rw [hdelta]
    simpa only [Complex.sub_re] using C.coordinateSpace.sub_mem
      (C.centre_re_mem s.1 s.2) (C.centre_re_mem t.1 t.2)
  have hend : ∀ z ∈ ({a.1.re, b.1.re, a'.1.re + delta,
      b'.1.re + delta} : Set ℝ), z ∈ C.coordinateSpace := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact C.vertex_re_mem a.1 a.2
    · exact C.vertex_re_mem b.1 b.2
    · exact C.coordinateSpace.add_mem (C.vertex_re_mem a'.1 a'.2) hDelta
    · exact C.coordinateSpace.add_mem (C.vertex_re_mem b'.1 b'.2) hDelta
  rcases hx.2 with hxd | ⟨r, hr, s, hs, hxs⟩
  · rw [hxd]
    exact hDelta
  · rw [hxs]
    exact C.coordinateSpace.sub_mem (hend r hr) (hend s hs)

private theorem transportScalar_mem_coordinateSpace
    {C : ApproximationContext.{0}} {x : ℝ}
    (hx : x ∈ transportCriticalScalars C) : x ∈ C.coordinateSpace := by
  rcases hx with hx | hx
  · rcases hx with ⟨a, b, a', b', delta, hdelta, hx⟩
    exact contactScalar_mem_coordinateSpace hdelta hx
  · exact horizontalStep_mem_coordinateSpace C hx

private theorem finiteTransportCriticalAlphabet_exists :
    (∀ (C : ApproximationContext.{0}),
    (∀ a b a' b' : ↥C.region.vertices,
      (Tiling.AxisParallel.Structure.horizontalContactDisplacements
        C.region C.centres a b a' b').Finite) →
    Nonempty (FiniteTransportCriticalAlphabet C)) := by
  intro C hfinite
  classical
  have hS := transportCriticalScalars_finite C hfinite
  let _ : Fintype (↥(transportCriticalScalars C)) := hS.fintype
  let lift : ↥(transportCriticalScalars C) → C.coordinateSpace :=
    fun x ↦ ⟨x.1, transportScalar_mem_coordinateSpace x.2⟩
  let values : Finset C.coordinateSpace := Finset.univ.image lift
  refine ⟨⟨values, lift, ?_, ?_⟩⟩
  · intro x
    rfl
  · intro x
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩

private theorem finiteTransportCriticalAlphabet_signThreshold :
    (∀ (C : ApproximationContext.{0})
    (A : FiniteTransportCriticalAlphabet C),
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C epsilon₀ phi →
        ∀ x : ↥(transportCriticalScalars C),
          Real.sign (mapScalar phi (A.lift x)) = Real.sign x.1) := by
  intro C A
  obtain ⟨epsilon₀, hepsilon₀, hsign⟩ :=
    approximation_preservesSign_finset C A.values
  refine ⟨epsilon₀, hepsilon₀, ?_⟩
  intro phi hphi x
  calc
    Real.sign (mapScalar phi (A.lift x)) =
        Real.sign (A.lift x : ℝ) :=
      hsign phi hphi (A.lift x) (A.lift_mem x)
    _ = Real.sign x.1 := by rw [A.lift_coe x]

private theorem mapScalar_vertical_endpoint
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).im) :
    mapScalar phi xLift =
      D.secondHomeomorph v.im +
        (mapPoint phi (C.centrePoint t.1 t.2)).im := by
  let vi : C.coordinateSpace := ⟨v.im, C.vertex_im_mem v hv⟩
  let ti : C.coordinateSpace := ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
  have hxl : xLift = vi + ti := by
    apply Subtype.ext
    simp [vi, ti, hLift, hx]
  have hvertex := congrArg Complex.im (D.vertex_agreement v hv)
  have hvertex' : mapScalar phi vi = D.secondHomeomorph v.im := by
    simpa [vi, mapPoint, ApproximationContext.vertexPoint,
      D.planarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((phi vi : ℚ) : ℝ) = mapScalar phi vi by rfl, hvertex']
  congr 1
  simp [ti, mapPoint, mapScalar, ApproximationContext.centrePoint]

private theorem mappedVerticalFilledChain_strictMono :
    (∀ {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (q : ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (owner : Fin n → ↥(deformedCenterCarrier P.firstCenters))
    (xLift : Fin (n + 1) → C.coordinateSpace),
    (∀ i, (xLift i : ℝ) = x i) →
    Tiling.AxisParallel.Foundations.FilledSliceChains.IsFilledIndexedSliceChain
      D.firstRegion (deformedCenterCarrier P.firstCenters)
        Axis.vertical q x owner →
    StrictMono (fun i => mapScalar phi (xLift i))) := by
  intro C phi D P q n x owner xLift hLift hchain
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, _hinside⟩ := hchain.2 i
  obtain ⟨v₀, hv₀, hvmap⟩ := by
    rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D] at hv
    simpa only [Set.mem_image] using hv
  obtain ⟨w₀, hw₀, hwmap⟩ := by
    rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D] at hw
    simpa only [Set.mem_image] using hw
  obtain ⟨t, ht⟩ := (owner i).2
  have howner : P.firstCenters t = (owner i : Tiling.Plane) := ht
  have hleft' : x i.castSucc = (v₀ + (t : Tiling.Plane)).im := by
    rw [hleft, Axis.coord, ← hvmap, ← howner]
    rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  have hright' : x i.succ = (w₀ + (t : Tiling.Plane)).im := by
    rw [hright, Axis.coord, ← hwmap, ← howner]
    rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  rw [mapScalar_vertical_endpoint D v₀ hv₀ t (x i.castSucc)
      (xLift i.castSucc) (hLift i.castSucc) hleft',
    mapScalar_vertical_endpoint D w₀ hw₀ t (x i.succ)
      (xLift i.succ) (hLift i.succ) hright']
  have hvw : v₀.im < w₀.im := by
    have hsign : 0 < Axis.coord Axis.vertical (w₀ - v₀) := by
      simpa [Axis.coord, ← hvmap, ← hwmap, D.firstPlanarHomeomorph_apply,
        Complex.sub_im] using hpositive
    exact sub_pos.mp hsign
  simpa [add_comm] using
    (add_lt_add_right (D.secondHomeomorph_strictMono hvw)
      (mapPoint phi (C.centrePoint t.1 t.2)).im)




private theorem closedSupportUnion_cover
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) : closedSupportUnion K T = univ := by
  have hSupport : regularSupport K T = univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
  have hClosure : closure (openUnion K T) = closedSupportUnion K T :=
    closure_openUnion_eq_iUnion_support hTile.2.1
  apply Set.Subset.antisymm (fun _ _ ↦ Set.mem_univ _)
  intro z _
  rw [← hClosure]
  apply interior_subset
  change z ∈ regularSupport K T
  rw [hSupport]
  exact Set.mem_univ z

private theorem seam_frontier_owner
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (_hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    {x : ℝ} (hx : x ∈ Ioo l r) :
    ∃ t : ↥T, linePoint y x ∈
      frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  have hcover := closedSupportUnion_cover hTile
  have hpSupport : linePoint y x ∈ closedSupportUnion K T := by
    rw [hcover]
    exact Set.mem_univ _
  rw [closedSupportUnion, Set.mem_iUnion] at hpSupport
  obtain ⟨t, htsupport⟩ := hpSupport
  refine ⟨t, ?_⟩
  rw [frontier]
  refine ⟨subset_closure htsupport, ?_⟩
  intro hpInterior
  have hpOpen : linePoint y x ∈
      (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    change linePoint y x ∈ interior
      ((t.1 : Tiling.Plane) +ᵥ K.support) at hpInterior
    change linePoint y x ∈
      (t.1 : Tiling.Plane) +ᵥ interior K.support
    simpa only [interior_vadd] using hpInterior
  exact hNoOpen t x hx hpOpen

private theorem seam_support_point_frontier
    {K : Region} {T : Set Tiling.Plane}
    (y l r : ℝ)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    {x : ℝ} (hx : x ∈ Ioo l r) (t : ↥T)
    (hp : linePoint y x ∈ (t.1 : Tiling.Plane) +ᵥ K.support) :
    linePoint y x ∈ frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  rw [frontier]
  refine ⟨subset_closure hp, ?_⟩
  intro hpInterior
  have hpOpen : linePoint y x ∈
      (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    change linePoint y x ∈ interior
      ((t.1 : Tiling.Plane) +ᵥ K.support) at hpInterior
    change linePoint y x ∈
      (t.1 : Tiling.Plane) +ᵥ interior K.support
    simpa only [interior_vadd] using hpInterior
  exact hNoOpen t x hx hpOpen

private theorem seam_relevant_centres_finite
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    (Q : Set Tiling.Plane) (hQ : Bornology.IsBounded Q) :
    {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty}.Finite := by
  let C : Set Tiling.Plane := Q - K.support
  have hC : Bornology.IsBounded C := hQ.sub K.isPolygonal.isBounded
  have hsub :
      {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty} ⊆ T ∩ C := by
    rintro t ⟨ht, z, hztranslate, hzQ⟩
    refine ⟨ht, ?_⟩
    rw [Set.mem_sub]
    rw [mem_vadd_set] at hztranslate
    obtain ⟨k, hk, rfl⟩ := hztranslate
    exact ⟨t + k, hzQ, k, hk, by simp⟩
  exact ((Tiling.AxisParallel.IsPacking.locallyFinite_centres hTile.2.1).1 C hC).subset hsub

private theorem seam_bad_owner_ball
    {K : Region} (F : Set Tiling.Plane) (hF : F.Finite) (p : Tiling.Plane) :
    ∃ epsilon > 0,
      Metric.ball p epsilon ⊆
        (⋃ t ∈ {t | t ∈ F ∧ p ∉ t +ᵥ K.support}, t +ᵥ K.support)ᶜ := by
  have hclosed : IsClosed
      (⋃ t ∈ {t | t ∈ F ∧ p ∉ t +ᵥ K.support}, t +ᵥ K.support) := by
    have hBad : {t | t ∈ F ∧ p ∉ t +ᵥ K.support}.Finite :=
      hF.subset (by intro t ht; exact ht.1)
    apply hBad.isClosed_biUnion
    intro t ht
    exact K.isPolygonal.vadd t |>.isClosed
  have hpcompl : p ∈
      (⋃ t ∈ {t | t ∈ F ∧ p ∉ t +ᵥ K.support}, t +ᵥ K.support)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro t ht
    exact ht.2
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    Metric.isOpen_iff.mp hclosed.isOpen_compl p hpcompl
  exact ⟨epsilon, hepsilon, hball⟩

private theorem seam_finite_opposite_owner
    {K : Region} {T : Set Tiling.Plane}
    {Q : Set Tiling.Plane} {p q : Tiling.Plane}
    (F : Set Tiling.Plane)
    (hFrel : {t : Tiling.Plane |
      t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty} ⊆ F)
    (hqQ : q ∈ Q)
    (hqcover : q ∈ closedSupportUnion K T)
    (t0 : ↥T) (hqnot0 : q ∉ (t0.1 : Tiling.Plane) +ᵥ K.support)
    (havoid : q ∉
      ⋃ t ∈ {t | t ∈ F ∧ p ∉ t +ᵥ K.support}, t +ᵥ K.support) :
    ∃ t1 : ↥T, p ∈ (t1.1 : Tiling.Plane) +ᵥ K.support ∧ t1 ≠ t0 := by
  rw [closedSupportUnion, mem_iUnion] at hqcover
  obtain ⟨t1, hq1⟩ := hqcover
  have ht1F : (t1.1 : Tiling.Plane) ∈ F := by
    apply hFrel
    exact ⟨t1.2, ⟨q, hq1, hqQ⟩⟩
  have hp1 : p ∈ (t1.1 : Tiling.Plane) +ᵥ K.support := by
    by_contra hp1
    apply havoid
    rw [mem_iUnion]
    refine ⟨(t1.1 : Tiling.Plane), ?_⟩
    rw [mem_iUnion]
    exact ⟨⟨ht1F, hp1⟩, hq1⟩
  have htne : t1 ≠ t0 := by
    intro heq
    apply hqnot0
    simpa [heq] using hq1
  exact ⟨t1, hp1, htne⟩

private theorem seam_finite_opposite_owner_of_ball
    {K : Region} {T : Set Tiling.Plane}
    {Q : Set Tiling.Plane} {p : Tiling.Plane}
    (F : Set Tiling.Plane)
    (hFrel : {t : Tiling.Plane |
      t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty} ⊆ F)
    {epsilon : ℝ} (hball : Metric.ball p epsilon ⊆
      (⋃ t ∈ {t | t ∈ F ∧ p ∉ t +ᵥ K.support}, t +ᵥ K.support)ᶜ)
    {q : Tiling.Plane} (hqball : q ∈ Metric.ball p epsilon)
    (hqQ : q ∈ Q)
    (hqcover : q ∈ closedSupportUnion K T)
    (t0 : ↥T) (hqnot0 : q ∉ (t0.1 : Tiling.Plane) +ᵥ K.support) :
    ∃ t1 : ↥T, p ∈ (t1.1 : Tiling.Plane) +ᵥ K.support ∧ t1 ≠ t0 := by
  exact seam_finite_opposite_owner F hFrel hqQ hqcover t0 hqnot0 (hball hqball)

private theorem seam_actual_finite_opposite_owner
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ)
    {Q : Set Tiling.Plane} (hQ : Bornology.IsBounded Q) (p : Tiling.Plane) :
    ∃ epsilon > 0, ∀ (q : Tiling.Plane), q ∈ Metric.ball p epsilon →
      q ∈ Q → q ∈ closedSupportUnion K T →
      ∀ (t0 : ↥T), q ∉ (t0.1 : Tiling.Plane) +ᵥ K.support →
      ∃ t1 : ↥T, p ∈ (t1.1 : Tiling.Plane) +ᵥ K.support ∧ t1 ≠ t0 := by
  let F : Set Tiling.Plane :=
    {u : Tiling.Plane | u ∈ T ∧ ((u +ᵥ K.support) ∩ Q).Nonempty}
  have hF : F.Finite := seam_relevant_centres_finite hTile Q hQ
  obtain ⟨epsilon, hepsilon, hball⟩ := seam_bad_owner_ball F hF p
  refine ⟨epsilon, hepsilon, ?_⟩
  intro q hqball hqQ hqcover t0 hqnot0
  exact seam_finite_opposite_owner_of_ball F
    (by intro t ht; exact ht) (by simpa [F] using hball)
    hqball hqQ hqcover t0 hqnot0

private theorem seam_nonvertex_edge_prefix
    {K : Region} {T : Set Tiling.Plane}
    (_hTile : TilesOn K T univ) (y l r : ℝ) (_hlr : l < r)
    (_hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    {x : ℝ} (_hx : x ∈ Ioo l r)
    (t : ↥T) (hp : linePoint y x ∈
      frontier ((t.1 : Tiling.Plane) +ᵥ K.support))
    (hnotvertex : linePoint y x - t.1 ∉ K.vertices) :
    ∃ (axis : Axis) (v w : ↥K.vertices),
      v.1 ≠ w.1 ∧ Axis.transverseCoord axis v.1 =
        Axis.transverseCoord axis w.1 ∧
      linePoint y x - t.1 ∈ openSegment ℝ v.1 w.1 ∧
      openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices := by
  have hqfront : linePoint y x - t.1 ∈ frontier K.support := by
    rw [Tiling.AxisParallel.frontier_vadd_eq] at hp
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp
    have heq : -(t.1 : Tiling.Plane) +ᵥ linePoint y x =
        linePoint y x - t.1 := by
      simp only [vadd_eq_add]
      ring
    rw [heq] at hp
    exact hp
  exact IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K
    (linePoint y x - t.1) hqfront hnotvertex

private theorem seam_midpoint_horizontal_edge
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅) :
    ∃ t : ↥T, ∃ a b : ↥K.vertices,
      IsIntrinsicHorizontalSide K a b ∧
      linePoint y ((l + r) / 2) ∈
        openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
          (b.1 + (t.1 : Tiling.Plane)) := by
  let m : ℝ := (l + r) / 2
  have hm : m ∈ Ioo l r := by
    dsimp [m]
    constructor <;> linarith
  obtain ⟨t, hfront⟩ := seam_frontier_owner hTile y l r hlr hNoOpen hm
  have hnotvertex : linePoint y m - t.1 ∉ K.vertices := by
    intro hvertex
    obtain ⟨w, hwne, hwtrans, hwside⟩ :=
      IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical
        ⟨linePoint y m - t.1, hvertex⟩
    let v : ↥K.vertices := ⟨linePoint y m - t.1, hvertex⟩
    have hside : IsIntrinsicSide K v w := by
      refine ⟨hwne.symm, Or.inl hwtrans.symm, hwside⟩
    have hpEq : linePoint y m = v.1 + (t.1 : Tiling.Plane) := by
      simp [v, sub_add_cancel]
    have hcoord : m = (v.1 + (t.1 : Tiling.Plane)).re := by
      have heq := congrArg Complex.re hpEq
      simpa [linePoint] using heq
    have hmeet : linePoint y m ∈
        segment ℝ (v.1 + (t.1 : Tiling.Plane))
          (w.1 + (t.1 : Tiling.Plane)) := by
      rw [hpEq]
      exact left_mem_segment ℝ _ _
    have hcut : m ∈ horizontalLineCutSet K T y := by
      exact ⟨⟨t, v, w, hside, Or.inl hcoord, hmeet⟩⟩
    have hmem : m ∈ Ioo l r ∩ horizontalLineCutSet K T y := ⟨hm, hcut⟩
    rw [hNoCut] at hmem
    exact hmem.elim
  obtain ⟨axis, v, w, hvw, htrans, hpseg, hside⟩ :=
    seam_nonvertex_edge_prefix hTile y l r hlr hNoOpen hm t hfront hnotvertex
  cases axis with
  | horizontal =>
      refine ⟨t, v, w, ⟨hvw, htrans, hside⟩, ?_⟩
      have hpseg' : (t.1 : Tiling.Plane) +ᵥ
          (linePoint y m - t.1) ∈
          (t.1 : Tiling.Plane) +ᵥ openSegment ℝ v.1 w.1 :=
        vadd_mem_vadd_set hpseg
      rw [vadd_openSegment ℝ] at hpseg'
      have hpt : (t.1 : Tiling.Plane) +ᵥ
          (linePoint y m - t.1) = linePoint y m := by
        simp [vadd_eq_add]
      rw [hpt] at hpseg'
      simpa [m, vadd_eq_add, add_comm] using hpseg'
  | vertical =>
      have hvwRe : v.1.re = w.1.re := htrans
      have hcoord_re {a b q : Tiling.Plane} (hab : a.re = b.re)
          (hq : q ∈ segment ℝ a b) : q.re = a.re := by
        rw [segment_eq_image_lineMap] at hq
        obtain ⟨s, _, rfl⟩ := hq
        simp only [AffineMap.lineMap_apply_module, Complex.add_re,
          Complex.smul_re, smul_eq_mul]
        rw [hab]
        ring
      have hpseg' : linePoint y m - t.1 ∈ segment ℝ v.1 w.1 :=
        openSegment_subset_segment ℝ v.1 w.1 hpseg
      have hpre : (linePoint y m - t.1).re = v.1.re :=
        hcoord_re hvwRe hpseg'
      have hcoord : m = (v.1 + (t.1 : Tiling.Plane)).re := by
        dsimp only [Complex.sub_re] at hpre
        dsimp only [Complex.add_re]
        simp [linePoint] at hpre
        linarith
      have hmeet : linePoint y m ∈
          segment ℝ (v.1 + (t.1 : Tiling.Plane))
            (w.1 + (t.1 : Tiling.Plane)) := by
        have hpseg' : (t.1 : Tiling.Plane) +ᵥ
            (linePoint y m - t.1) ∈
            (t.1 : Tiling.Plane) +ᵥ openSegment ℝ v.1 w.1 :=
          vadd_mem_vadd_set hpseg
        rw [vadd_openSegment ℝ] at hpseg'
        have hpt : (t.1 : Tiling.Plane) +ᵥ
            (linePoint y m - t.1) = linePoint y m := by
          simp [vadd_eq_add]
        rw [hpt] at hpseg'
        apply openSegment_subset_segment ℝ _ _
        simpa [vadd_eq_add, add_comm] using hpseg'
      have hcut : m ∈ horizontalLineCutSet K T y := by
        exact ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩,
          Or.inl hcoord, hmeet⟩⟩
      have hmem : m ∈ Ioo l r ∩ horizontalLineCutSet K T y := ⟨hm, hcut⟩
      rw [hNoCut] at hmem
      exact hmem.elim

private theorem seam_midpoint_owner_horizontal
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅)
    (t : ↥T)
    (hp : linePoint y ((l + r) / 2) ∈
      frontier ((t.1 : Tiling.Plane) +ᵥ K.support)) :
    ∃ a b : ↥K.vertices,
      IsIntrinsicHorizontalSide K a b ∧
      linePoint y ((l + r) / 2) ∈
        openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
          (b.1 + (t.1 : Tiling.Plane)) := by
  let m : ℝ := (l + r) / 2
  have hm : m ∈ Ioo l r := by
    dsimp [m]
    constructor <;> linarith
  have hnotvertex : linePoint y m - t.1 ∉ K.vertices := by
    intro hvertex
    obtain ⟨w, hwne, hwtrans, hwside⟩ :=
      IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical
        ⟨linePoint y m - t.1, hvertex⟩
    let v : ↥K.vertices := ⟨linePoint y m - t.1, hvertex⟩
    have hside : IsIntrinsicSide K v w := by
      refine ⟨hwne.symm, Or.inl hwtrans.symm, hwside⟩
    have hpEq : linePoint y m = v.1 + (t.1 : Tiling.Plane) := by
      simp [v, sub_add_cancel]
    have hcoord : m = (v.1 + (t.1 : Tiling.Plane)).re := by
      simpa [linePoint] using congrArg Complex.re hpEq
    have hmeet : linePoint y m ∈
        segment ℝ (v.1 + (t.1 : Tiling.Plane))
          (w.1 + (t.1 : Tiling.Plane)) := by
      rw [hpEq]
      exact left_mem_segment ℝ _ _
    have hcut : m ∈ horizontalLineCutSet K T y :=
      ⟨⟨t, v, w, hside, Or.inl hcoord, hmeet⟩⟩
    have hmem : m ∈ Ioo l r ∩ horizontalLineCutSet K T y := ⟨hm, hcut⟩
    rw [hNoCut] at hmem
    exact hmem.elim
  obtain ⟨axis, v, w, hvw, htrans, hpseg, hside⟩ :=
    seam_nonvertex_edge_prefix hTile y l r hlr hNoOpen hm t hp hnotvertex
  cases axis with
  | horizontal =>
      refine ⟨v, w, ⟨hvw, htrans, hside⟩, ?_⟩
      have hpseg' : (t.1 : Tiling.Plane) +ᵥ
          (linePoint y m - t.1) ∈
          (t.1 : Tiling.Plane) +ᵥ openSegment ℝ v.1 w.1 :=
        vadd_mem_vadd_set hpseg
      rw [vadd_openSegment ℝ] at hpseg'
      have hpt : (t.1 : Tiling.Plane) +ᵥ
          (linePoint y m - t.1) = linePoint y m := by
        simp [vadd_eq_add]
      rw [hpt] at hpseg'
      simpa [m, vadd_eq_add, add_comm] using hpseg'
  | vertical =>
      have hvwRe : v.1.re = w.1.re := htrans
      have hcoord_re {a b q : Tiling.Plane} (hab : a.re = b.re)
          (hq : q ∈ segment ℝ a b) : q.re = a.re := by
        rw [segment_eq_image_lineMap] at hq
        obtain ⟨s, _, rfl⟩ := hq
        simp only [AffineMap.lineMap_apply_module, Complex.add_re,
          Complex.smul_re, smul_eq_mul]
        rw [hab]
        ring
      have hpseg' : linePoint y m - t.1 ∈ segment ℝ v.1 w.1 :=
        openSegment_subset_segment ℝ v.1 w.1 hpseg
      have hpre : (linePoint y m - t.1).re = v.1.re :=
        hcoord_re hvwRe hpseg'
      have hcoord : m = (v.1 + (t.1 : Tiling.Plane)).re := by
        dsimp only [Complex.sub_re] at hpre
        dsimp only [Complex.add_re]
        simp [linePoint] at hpre
        linarith
      have hmeet : linePoint y m ∈
          segment ℝ (v.1 + (t.1 : Tiling.Plane))
            (w.1 + (t.1 : Tiling.Plane)) := by
        have hpseg' : (t.1 : Tiling.Plane) +ᵥ
            (linePoint y m - t.1) ∈
            (t.1 : Tiling.Plane) +ᵥ openSegment ℝ v.1 w.1 :=
          vadd_mem_vadd_set hpseg
        rw [vadd_openSegment ℝ] at hpseg'
        have hpt : (t.1 : Tiling.Plane) +ᵥ
            (linePoint y m - t.1) = linePoint y m := by
          simp [vadd_eq_add]
        rw [hpt] at hpseg'
        apply openSegment_subset_segment ℝ _ _
        simpa [vadd_eq_add, add_comm] using hpseg'
      have hcut : m ∈ horizontalLineCutSet K T y :=
        ⟨⟨t, v, w, ⟨hvw, Or.inl hvwRe, hside⟩,
          Or.inl hcoord, hmeet⟩⟩
      have hmem : m ∈ Ioo l r ∩ horizontalLineCutSet K T y := ⟨hm, hcut⟩
      rw [hNoCut] at hmem
      exact hmem.elim

private theorem linePoint_mem_horizontal_openSegment
    {a b : Tiling.Plane} (_hab : a ≠ b) (habIm : a.im = b.im)
    {y x : ℝ} (hy : y = a.im) :
    linePoint y x ∈ openSegment ℝ a b ↔ x ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s, hs, by simpa [linePoint] using congrArg Complex.re h⟩
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    apply Complex.ext
    · simpa [linePoint] using congrArg id h
    · simp only [linePoint, Complex.add_im, Complex.ofReal_im, zero_add,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.I_re, mul_zero, Complex.smul_im, smul_eq_mul]
      rw [hy, habIm]
      ring

private theorem seam_horizontal_side_extends
    {K : Region} {T : Set Tiling.Plane}
    {y l r : ℝ} (_hlr : l < r)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅)
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    {m : ℝ} (hm : m ∈ Ioo l r)
    (hmid : linePoint y m ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane))
      (b.1 + (t.1 : Tiling.Plane))) :
    ∀ x ∈ Ioo l r, linePoint y x ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane))
      (b.1 + (t.1 : Tiling.Plane)) := by
  have hab : a.1 ≠ b.1 := hside.1
  have habIm : (a.1 + (t.1 : Tiling.Plane)).im =
      (b.1 + (t.1 : Tiling.Plane)).im := by
    simpa [Complex.add_im] using hside.2.1
  have hseg := openSegment_subset_segment ℝ _ _ hmid
  have hcoord_im {u v q : Tiling.Plane} (huv : u.im = v.im)
      (hq : q ∈ segment ℝ u v) : q.im = u.im := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_im,
      Complex.smul_im, smul_eq_mul]
    rw [huv]
    ring
  have hy : y = (a.1 + (t.1 : Tiling.Plane)).im := by
    have hi := hcoord_im habIm hseg
    simpa [linePoint] using hi
  have hcutA : (a.1 + (t.1 : Tiling.Plane)).re ∈
      horizontalLineCutSet K T y := by
    have hp : linePoint y (a.1 + (t.1 : Tiling.Plane)).re =
        a.1 + (t.1 : Tiling.Plane) := by
      apply Complex.ext <;> simp [linePoint, hy]
    exact ⟨⟨t, a, b,
      ⟨hside.1, Or.inr hside.2.1, hside.2.2⟩, Or.inl rfl,
      by rw [hp]; exact left_mem_segment ℝ _ _⟩⟩
  have hcutB : (b.1 + (t.1 : Tiling.Plane)).re ∈
      horizontalLineCutSet K T y := by
    have hp : linePoint y (b.1 + (t.1 : Tiling.Plane)).re =
        b.1 + (t.1 : Tiling.Plane) := by
      apply Complex.ext <;> simp [linePoint, hy, habIm]
    exact ⟨⟨t, a, b,
      ⟨hside.1, Or.inr hside.2.1, hside.2.2⟩, Or.inr rfl,
      by rw [hp]; exact right_mem_segment ℝ _ _⟩⟩
  have hcoord_mem : m ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane)).re
      (b.1 + (t.1 : Tiling.Plane)).re := by
    rw [← (linePoint_mem_horizontal_openSegment (by
      intro habEq
      apply hab
      apply Complex.ext
      · have heq := congrArg Complex.re habEq
        dsimp only [Complex.add_re] at heq
        linarith
      · exact hside.2.1) habIm hy)]
    exact hmid
  have hABne : (a.1 + (t.1 : Tiling.Plane)).re ≠
      (b.1 + (t.1 : Tiling.Plane)).re := by
    intro heq
    apply hab
    apply Complex.ext
    · simpa using heq
    · exact hside.2.1
  have hne : (a.1 + (t.1 : Tiling.Plane)) ≠
      (b.1 + (t.1 : Tiling.Plane)) := by
    intro heq
    apply hab
    apply Complex.ext
    · have hre := congrArg Complex.re heq
      dsimp only [Complex.add_re] at hre
      linarith
    · exact hside.2.1
  intro x hx
  rcases lt_or_gt_of_ne hABne with hAB | hBA
  · rw [openSegment_eq_Ioo hAB] at hcoord_mem
    have hml : (a.1 + (t.1 : Tiling.Plane)).re < m := hcoord_mem.1
    have hmr : m < (b.1 + (t.1 : Tiling.Plane)).re := hcoord_mem.2
    have hleft : (a.1 + (t.1 : Tiling.Plane)).re ≤ l := by
      by_contra hn
      have hli : l < (a.1 + (t.1 : Tiling.Plane)).re := lt_of_not_ge hn
      have hmem : (a.1 + (t.1 : Tiling.Plane)).re ∈
          Ioo l r ∩ horizontalLineCutSet K T y :=
        ⟨⟨hli, lt_trans hml hm.2⟩, hcutA⟩
      rw [hNoCut] at hmem
      exact hmem.elim
    have hright : r ≤ (b.1 + (t.1 : Tiling.Plane)).re := by
      by_contra hn
      have hri : (b.1 + (t.1 : Tiling.Plane)).re < r := lt_of_not_ge hn
      have hmem : (b.1 + (t.1 : Tiling.Plane)).re ∈
          Ioo l r ∩ horizontalLineCutSet K T y :=
        ⟨⟨lt_trans hm.1 hmr, hri⟩, hcutB⟩
      rw [hNoCut] at hmem
      exact hmem.elim
    apply (linePoint_mem_horizontal_openSegment hne habIm hy).2
    rw [openSegment_eq_Ioo hAB]
    exact ⟨lt_of_le_of_lt hleft hx.1, lt_of_lt_of_le hx.2 hright⟩
  · have hcoord_mem' : m ∈ openSegment ℝ
        (b.1 + (t.1 : Tiling.Plane)).re
        (a.1 + (t.1 : Tiling.Plane)).re := by
      simpa only [openSegment_symm] using hcoord_mem
    rw [openSegment_eq_Ioo hBA] at hcoord_mem'
    have hml : (b.1 + (t.1 : Tiling.Plane)).re < m := hcoord_mem'.1
    have hmr : m < (a.1 + (t.1 : Tiling.Plane)).re := hcoord_mem'.2
    have hleft : (b.1 + (t.1 : Tiling.Plane)).re ≤ l := by
      by_contra hn
      have hli := lt_of_not_ge hn
      have hmem : (b.1 + (t.1 : Tiling.Plane)).re ∈
          Ioo l r ∩ horizontalLineCutSet K T y :=
        ⟨⟨hli, lt_trans hml hm.2⟩, hcutB⟩
      rw [hNoCut] at hmem
      exact hmem.elim
    have hright : r ≤ (a.1 + (t.1 : Tiling.Plane)).re := by
      by_contra hn
      have hri := lt_of_not_ge hn
      have hmem : (a.1 + (t.1 : Tiling.Plane)).re ∈
          Ioo l r ∩ horizontalLineCutSet K T y :=
        ⟨⟨lt_trans hm.1 hmr, hri⟩, hcutA⟩
      rw [hNoCut] at hmem
      exact hmem.elim
    have hy' : y = (b.1 + (t.1 : Tiling.Plane)).im := hy.trans habIm
    have hrev := (linePoint_mem_horizontal_openSegment hne.symm habIm.symm hy').2
      (by rw [openSegment_eq_Ioo hBA]; exact
        ⟨lt_of_le_of_lt hleft hx.1, lt_of_lt_of_le hx.2 hright⟩)
    simpa only [openSegment_symm] using hrev

private theorem seam_horizontal_direction_of_local_frontier
    {K : Region} (q d : Tiling.Plane) (rho : ℝ)
    (_hd : d ≠ 0)
    (hfront : ∀ z ∈ Metric.ball q rho,
      (z ∈ frontier K.support ↔ z ∈ Tiling.affineLine q d))
    (z : Tiling.Plane) (hzball : z ∈ Metric.ball q rho)
    (hzfront : z ∈ frontier K.support)
    (hzim : z.im = q.im) (hzre : z.re ≠ q.re) :
    d.im = 0 := by
  have hzline : z ∈ Tiling.affineLine q d := (hfront z hzball).1 hzfront
  have hsz : Tiling.signedSide q d z = 0 := Tiling.mem_affineLine.1 hzline
  simp only [Tiling.signedSide, Tiling.planarCross] at hsz
  have hdiff : z.re - q.re ≠ 0 := sub_ne_zero.mpr hzre
  have hprod : d.im * (z.re - q.re) = 0 := by
    rw [hzim] at hsz
    linarith
  exact (mul_eq_zero.mp hprod).resolve_right hdiff

private theorem seam_midpoint_fixed_second_owner
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅)
    (t0 : ↥T) (hm : (l + r) / 2 ∈ Ioo l r)
    {Q : Set Tiling.Plane} {p q : Tiling.Plane} {epsilon : ℝ}
    (hp : p = linePoint y ((l + r) / 2))
    (hball : Metric.ball p epsilon ⊆
      (⋃ t ∈ {t | t ∈
        {u : Tiling.Plane | u ∈ T ∧ ((u +ᵥ K.support) ∩ Q).Nonempty} ∧
          p ∉ t +ᵥ K.support}, t +ᵥ K.support)ᶜ)
    (hqball : q ∈ Metric.ball p epsilon) (hqQ : q ∈ Q)
    (hqcover : q ∈ closedSupportUnion K T)
    (hqnot0 : q ∉ (t0.1 : Tiling.Plane) +ᵥ K.support) :
    ∃ t1 : ↥T, ∃ a' b' : ↥K.vertices,
      t1 ≠ t0 ∧ IsIntrinsicHorizontalSide K a' b' ∧
      (∀ x ∈ Ioo l r, linePoint y x ∈
        openSegment ℝ (a'.1 + (t1.1 : Tiling.Plane))
          (b'.1 + (t1.1 : Tiling.Plane))) := by
  let F : Set Tiling.Plane :=
    {u : Tiling.Plane | u ∈ T ∧ ((u +ᵥ K.support) ∩ Q).Nonempty}
  obtain ⟨t1, hp1, htne⟩ := seam_finite_opposite_owner_of_ball F
    (by intro t ht; exact ht) (by simpa [F] using hball)
    hqball hqQ hqcover t0 hqnot0
  have hfront1 := seam_support_point_frontier y l r hNoOpen hm t1 (by simpa [hp] using hp1)
  obtain ⟨a', b', hside', hmid'⟩ := seam_midpoint_owner_horizontal
    hTile y l r hlr hNoOpen hNoCut t1 hfront1
  refine ⟨t1, a', b', htne, hside', ?_⟩
  exact seam_horizontal_side_extends hlr hNoCut t1 a' b' hside' hm hmid'

private theorem seam_horizontal_side_local_halfPlane
    {K : Region} (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    (q : Tiling.Plane) (hq : q ∈ openSegment ℝ a.1 b.1) :
    ∃ d : Tiling.Plane, d ≠ 0 ∧ d.im = 0 ∧ ∃ rho > 0,
      (K.support ∩ Metric.ball q rho =
          Tiling.positiveHalfPlane q d ∩ Metric.ball q rho ∨
        K.support ∩ Metric.ball q rho =
          Tiling.negativeHalfPlane q d ∩ Metric.ball q rho) := by
  have hqfront : q ∈ frontier K.support := hside.2.2 hq |>.1
  have hqnotvertex : q ∉ K.vertices := by
    intro hqv
    exact (hside.2.2 hq).2 hqv
  have hfrontOpen : q ∈ frontier K.openCarrier := by
    rw [K.frontier_openCarrier_eq_frontier_support]
    exact hqfront
  have hstraight : Tiling.BoundaryLocallyStraightAt K.openCarrier q := by
    by_contra hns
    have hqv : q ∈ K.vertices := by
      rw [IntrinsicVertices.region_vertices_eq_nonStraightBoundary]
      exact ⟨hfrontOpen, hns⟩
    exact hqnotvertex hqv
  obtain ⟨L, hqL, hdim, hlocal⟩ := hstraight
  have hlocalSupport : ∀ᶠ z in 𝓝 q,
      (z ∈ frontier K.support ↔ z ∈ (L : Set Tiling.Plane)) := by
    simpa only [K.frontier_openCarrier_eq_frontier_support] using hlocal
  obtain ⟨d, hd, rho, hrho, hfront⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hqL hdim hlocalSupport
  have hhalf := Tiling.local_eq_closedHalfPlane hd hrho
    K.isPolygonal.closure_interior hfront
  have hnear : ∃ z ∈ openSegment ℝ a.1 b.1, z ≠ q ∧ z ∈ Metric.ball q rho := by
    rw [openSegment_eq_image_lineMap] at hq
    obtain ⟨θ, hθ, rfl⟩ := hq
    let δ := min ((1 - θ) / 2) (rho / (2 * dist a.1 b.1))
    have hδ : 0 < δ := lt_min (half_pos (sub_pos.mpr hθ.2))
      (div_pos hrho (mul_pos zero_lt_two (dist_pos.mpr hside.1)))
    have hθδ : θ + δ ∈ Ioo (0 : ℝ) 1 := by
      refine ⟨hθ.1.trans (lt_add_of_pos_right θ hδ), ?_⟩
      have hδle : δ ≤ (1 - θ) / 2 := min_le_left _ _
      linarith [hθ.2]
    refine ⟨AffineMap.lineMap a.1 b.1 (θ + δ),
      lineMap_mem_openSegment (𝕜 := ℝ) a.1 b.1 hθδ, ?_, ?_⟩
    · intro heq
      have := AffineMap.lineMap_injective ℝ hside.1 heq
      linarith
    · rw [Metric.mem_ball, dist_eq_norm]
      simp only [AffineMap.lineMap_apply_module]
      have hdiff :
          ((1 - (θ + δ)) • a.1 + (θ + δ) • b.1) -
              ((1 - θ) • a.1 + θ • b.1) = δ • (b.1 - a.1) := by
        module
      rw [hdiff]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      dsimp [δ]
      calc
        min ((1 - θ) / 2) (rho / (2 * dist a.1 b.1)) * ‖b.1 - a.1‖ ≤
            (rho / (2 * dist a.1 b.1)) * ‖b.1 - a.1‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = rho / 2 := by
          rw [dist_eq_norm]
          rw [norm_sub_rev]
          field_simp
          exact div_self (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hside.1.symm))
        _ < rho := half_lt_self hrho
  obtain ⟨z, hzside, hzq, hzball⟩ := hnear
  have him (p : Tiling.Plane) (hp : p ∈ openSegment ℝ a.1 b.1) :
      p.im = a.1.im := by
    rw [openSegment_eq_image] at hp
    obtain ⟨s, hs, h⟩ := hp
    rw [← h]
    simp only [Complex.smul_im, Complex.add_im]
    rw [hside.2.1]
    ring
  have hzre : z.re ≠ q.re := by
    intro heq
    apply hzq
    exact Complex.ext heq (by rw [him z hzside, him q hq])
  have hdim0 := seam_horizontal_direction_of_local_frontier q d rho hd hfront z hzball
    (hside.2.2 hzside |>.1) (by rw [him z hzside, him q hq]) hzre
  exact ⟨d, hd, hdim0, rho, hrho, hhalf⟩

private theorem seam_notSupport_of_positiveHalfPlane
    {K : Region} {q d z g t : Tiling.Plane} {rho : ℝ}
    (hhalf : K.support ∩ Metric.ball q rho =
      Tiling.positiveHalfPlane q d ∩ Metric.ball q rho)
    (hzball : z ∈ Metric.ball q rho)
    (htranslate : t +ᵥ z = g)
    (hsign : Tiling.signedSide q d z < 0) :
    g ∉ t +ᵥ K.support := by
  intro hg
  have hz : z ∈ K.support := by
    have hg' := hg
    rw [← htranslate] at hg'
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hg'
    simpa [vadd_eq_add] using hg'
  have hzmem : z ∈ Tiling.positiveHalfPlane q d ∩ Metric.ball q rho := by
    rw [← hhalf]
    exact ⟨hz, hzball⟩
  have hzhalf : z ∈ Tiling.positiveHalfPlane q d := hzmem.1
  have hs := Tiling.mem_positiveHalfPlane.1 hzhalf
  exact (not_lt_of_ge hs) hsign

private theorem seam_notSupport_of_negativeHalfPlane
    {K : Region} {q d z g t : Tiling.Plane} {rho : ℝ}
    (hhalf : K.support ∩ Metric.ball q rho =
      Tiling.negativeHalfPlane q d ∩ Metric.ball q rho)
    (hzball : z ∈ Metric.ball q rho)
    (htranslate : t +ᵥ z = g)
    (hsign : 0 < Tiling.signedSide q d z) :
    g ∉ t +ᵥ K.support := by
  intro hg
  have hz : z ∈ K.support := by
    have hg' := hg
    rw [← htranslate] at hg'
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hg'
    simpa [vadd_eq_add] using hg'
  have hzmem : z ∈ Tiling.negativeHalfPlane q d ∩ Metric.ball q rho := by
    rw [← hhalf]
    exact ⟨hz, hzball⟩
  have hzhalf : z ∈ Tiling.negativeHalfPlane q d := hzmem.1
  have hs := Tiling.mem_negativeHalfPlane.1 hzhalf
  exact (not_lt_of_ge hs) hsign

private theorem seam_midpoint_second_owner
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅)
    (t0 : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    (hmid : linePoint y ((l + r) / 2) ∈
      openSegment ℝ (a.1 + (t0.1 : Tiling.Plane))
        (b.1 + (t0.1 : Tiling.Plane))) :
    ∃ t1 : ↥T, ∃ a' b' : ↥K.vertices,
      t1 ≠ t0 ∧ IsIntrinsicHorizontalSide K a' b' ∧
      (∀ x ∈ Ioo l r, linePoint y x ∈
        openSegment ℝ (a'.1 + (t1.1 : Tiling.Plane))
          (b'.1 + (t1.1 : Tiling.Plane))) := by
  let m : ℝ := (l + r) / 2
  let p : Tiling.Plane := linePoint y m
  let q0 : Tiling.Plane := p - t0.1
  have hm : m ∈ Ioo l r := by
    dsimp [m]
    constructor <;> linarith
  have hq0side : q0 ∈ openSegment ℝ a.1 b.1 := by
    have htranslated : p ∈
        (t0.1 : Tiling.Plane) +ᵥ openSegment ℝ a.1 b.1 := by
      rw [vadd_openSegment ℝ]
      simpa [p, m, vadd_eq_add, add_comm] using hmid
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at htranslated
    simpa [q0, vadd_eq_add, sub_eq_add_neg, add_comm] using htranslated
  obtain ⟨d, hd, hdim0, rho, hrho, hhalf⟩ :=
    seam_horizontal_side_local_halfPlane a b hside q0 hq0side
  have hdre : d.re ≠ 0 := by
    intro hdre
    apply hd
    exact Complex.ext hdre hdim0
  let Q : Set Tiling.Plane := Metric.closedBall p 1
  let F : Set Tiling.Plane :=
    {u : Tiling.Plane | u ∈ T ∧ ((u +ᵥ K.support) ∩ Q).Nonempty}
  have hF : F.Finite := by
    apply seam_relevant_centres_finite hTile Q
    exact Metric.isBounded_closedBall
  obtain ⟨epsilon, hepsilon, hbad⟩ := seam_bad_owner_ball F hF p
  let h : ℝ := min (rho / 2) (min (epsilon / 2) (1 / 2))
  have hh : 0 < h := by
    dsimp [h]
    exact lt_min (half_pos hrho) (lt_min (half_pos hepsilon) (by norm_num))
  have hhrho : h < rho := by
    calc
      h ≤ rho / 2 := min_le_left _ _
      _ < rho := half_lt_self hrho
  have hhepsilon : h < epsilon := by
    calc
      h ≤ min (epsilon / 2) (1 / 2) := min_le_right _ _
      _ ≤ epsilon / 2 := min_le_left _ _
      _ < epsilon := half_lt_self hepsilon
  have hhone : h < 1 := by
    calc
      h ≤ min (epsilon / 2) (1 / 2) := min_le_right _ _
      _ ≤ 1 / 2 := min_le_right _ _
      _ < 1 := by norm_num
  let qPlus : Tiling.Plane := linePoint (y + h) m
  let qMinus : Tiling.Plane := linePoint (y - h) m
  let zPlus : Tiling.Plane := qPlus - t0.1
  let zMinus : Tiling.Plane := qMinus - t0.1
  have hdistPlus : dist qPlus p = h := by
    rw [dist_eq_norm]
    have heq : qPlus - p = (h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [qPlus, p, linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hh]
  have hdistMinus : dist qMinus p = h := by
    rw [dist_eq_norm]
    have heq : qMinus - p = (-h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [qMinus, p, linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  have hqPlusBall : qPlus ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, hdistPlus]
    exact hhepsilon
  have hqMinusBall : qMinus ∈ Metric.ball p epsilon := by
    rw [Metric.mem_ball, hdistMinus]
    exact hhepsilon
  have hqPlusQ : qPlus ∈ Q := by
    rw [Metric.mem_closedBall]
    simpa [Q, hdistPlus] using hhone.le
  have hqMinusQ : qMinus ∈ Q := by
    rw [Metric.mem_closedBall]
    simpa [Q, hdistMinus] using hhone.le
  have hzPlusBall : zPlus ∈ Metric.ball q0 rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : zPlus - q0 = qPlus - p := by
      simp [zPlus, q0]
    rw [heq, ← dist_eq_norm, hdistPlus]
    exact hhrho
  have hzMinusBall : zMinus ∈ Metric.ball q0 rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : zMinus - q0 = qMinus - p := by
      simp [zMinus, q0]
    rw [heq, ← dist_eq_norm, hdistMinus]
    exact hhrho
  have htranslatePlus : (t0.1 : Tiling.Plane) +ᵥ zPlus = qPlus := by
    simp [zPlus, vadd_eq_add]
  have htranslateMinus : (t0.1 : Tiling.Plane) +ᵥ zMinus = qMinus := by
    simp [zMinus, vadd_eq_add]
  have hsignPlus : Tiling.signedSide q0 d zPlus = d.re * h := by
    simp [Tiling.signedSide, Tiling.planarCross, q0, zPlus, qPlus,
      p, linePoint, hdim0]
    ring
  have hsignMinus : Tiling.signedSide q0 d zMinus = -(d.re * h) := by
    simp [Tiling.signedSide, Tiling.planarCross, q0, zMinus, qMinus,
      p, linePoint, hdim0]
    ring
  have hcoverPlus : qPlus ∈ closedSupportUnion K T := by
    rw [closedSupportUnion_cover hTile]
    exact Set.mem_univ _
  have hcoverMinus : qMinus ∈ closedSupportUnion K T := by
    rw [closedSupportUnion_cover hTile]
    exact Set.mem_univ _
  have hbad' : Metric.ball p epsilon ⊆
      (⋃ t ∈ {t | t ∈
        {u : Tiling.Plane | u ∈ T ∧ ((u +ᵥ K.support) ∩ Q).Nonempty} ∧
          p ∉ t +ᵥ K.support}, t +ᵥ K.support)ᶜ := by
    simpa [F] using hbad
  rcases lt_or_gt_of_ne hdre with hdneg | hdpos
  · rcases hhalf with hpositive | hnegative
    · have hnot0 : qPlus ∉ (t0.1 : Tiling.Plane) +ᵥ K.support :=
        seam_notSupport_of_positiveHalfPlane hpositive hzPlusBall
          htranslatePlus (by rw [hsignPlus]; exact mul_neg_of_neg_of_pos hdneg hh)
      exact seam_midpoint_fixed_second_owner hTile y l r hlr hNoOpen hNoCut t0 hm
        (p := p) (q := qPlus) (epsilon := epsilon) (Q := Q) rfl hbad'
        hqPlusBall hqPlusQ hcoverPlus hnot0
    · have hnot0 : qMinus ∉ (t0.1 : Tiling.Plane) +ᵥ K.support :=
        seam_notSupport_of_negativeHalfPlane hnegative hzMinusBall
          htranslateMinus (by
            rw [hsignMinus]
            exact neg_pos.mpr (mul_neg_of_neg_of_pos hdneg hh))
      exact seam_midpoint_fixed_second_owner hTile y l r hlr hNoOpen hNoCut t0 hm
        (p := p) (q := qMinus) (epsilon := epsilon) (Q := Q) rfl hbad'
        hqMinusBall hqMinusQ hcoverMinus hnot0
  · rcases hhalf with hpositive | hnegative
    · have hnot0 : qMinus ∉ (t0.1 : Tiling.Plane) +ᵥ K.support :=
        seam_notSupport_of_positiveHalfPlane hpositive hzMinusBall
          htranslateMinus (by
            rw [hsignMinus]
            exact neg_lt_zero.mpr (mul_pos hdpos hh))
      exact seam_midpoint_fixed_second_owner hTile y l r hlr hNoOpen hNoCut t0 hm
        (p := p) (q := qMinus) (epsilon := epsilon) (Q := Q) rfl hbad'
        hqMinusBall hqMinusQ hcoverMinus hnot0
    · have hnot0 : qPlus ∉ (t0.1 : Tiling.Plane) +ᵥ K.support :=
        seam_notSupport_of_negativeHalfPlane hnegative hzPlusBall
          htranslatePlus (by rw [hsignPlus]; exact mul_pos hdpos hh)
      exact seam_midpoint_fixed_second_owner hTile y l r hlr hNoOpen hNoCut t0 hm
        (p := p) (q := qPlus) (epsilon := epsilon) (Q := Q) rfl hbad'
        hqPlusBall hqPlusQ hcoverPlus hnot0

private theorem seam_horizontal_side_open_germ
    {K : Region} (q d : Tiling.Plane) (rho : ℝ)
    (hd : d ≠ 0) (hdim0 : d.im = 0) (hrho : 0 < rho)
    (hhalf :
      K.support ∩ Metric.ball q rho =
          Tiling.positiveHalfPlane q d ∩ Metric.ball q rho ∨
        K.support ∩ Metric.ball q rho =
          Tiling.negativeHalfPlane q d ∩ Metric.ball q rho) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ((∀ h : ℝ, 0 < h → h < epsilon →
          linePoint (q.im + h) q.re ∈ K.openCarrier) ∨
       (∀ h : ℝ, 0 < h → h < epsilon →
          linePoint (q.im - h) q.re ∈ K.openCarrier)) := by
  have hdre : d.re ≠ 0 := by
    intro hdre
    apply hd
    exact Complex.ext hdre hdim0
  let epsilon : ℝ := rho / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; linarith
  have hballPlus (h : ℝ) (hh : 0 < h) (hhε : h < epsilon) :
      linePoint (q.im + h) q.re ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : linePoint (q.im + h) q.re - q = (h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    dsimp [epsilon] at hhε
    linarith
  have hballMinus (h : ℝ) (hh : 0 < h) (hhε : h < epsilon) :
      linePoint (q.im - h) q.re ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : linePoint (q.im - h) q.re - q = (-h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one]
    rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    dsimp [epsilon] at hhε
    linarith
  have hsignPlus (h : ℝ) :
      Tiling.signedSide q d (linePoint (q.im + h) q.re) = d.re * h := by
    simp [Tiling.signedSide, Tiling.planarCross, linePoint, hdim0]
    ring
  have hsignMinus (h : ℝ) :
      Tiling.signedSide q d (linePoint (q.im - h) q.re) = -(d.re * h) := by
    simp [Tiling.signedSide, Tiling.planarCross, linePoint, hdim0]
    ring
  have hinteriorPlus (h : ℝ) (hh : 0 < h) (hhε : h < epsilon)
      (hbranch : K.support ∩ Metric.ball q rho =
        Tiling.positiveHalfPlane q d ∩ Metric.ball q rho)
      (hstrict : 0 < d.re * h) :
      linePoint (q.im + h) q.re ∈ K.openCarrier := by
    have hzball := hballPlus h hh hhε
    have hzside : linePoint (q.im + h) q.re ∈ Tiling.positiveSide q d :=
      Tiling.mem_positiveSide.2 (by rw [hsignPlus]; exact hstrict)
    have hsubset : Tiling.positiveSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro z hz
      have hzmem : z ∈ K.support ∩ Metric.ball q rho := by
        rw [hbranch]
        exact ⟨Tiling.mem_positiveHalfPlane.2 (Tiling.mem_positiveSide.1 hz.1).le, hz.2⟩
      exact hzmem.1
    have hopen : IsOpen (Tiling.positiveSide q d ∩ Metric.ball q rho) :=
      Tiling.isOpen_positiveSide q d |>.inter Metric.isOpen_ball
    have hzint : linePoint (q.im + h) q.re ∈ interior K.support := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        (hopen.mem_nhds ⟨hzside, hzball⟩) hsubset
    exact hzint
  have hinteriorMinus (h : ℝ) (hh : 0 < h) (hhε : h < epsilon)
      (hbranch : K.support ∩ Metric.ball q rho =
        Tiling.negativeHalfPlane q d ∩ Metric.ball q rho)
      (hstrict : -(d.re * h) < 0) :
      linePoint (q.im - h) q.re ∈ K.openCarrier := by
    have hzball := hballMinus h hh hhε
    have hzside : linePoint (q.im - h) q.re ∈ Tiling.negativeSide q d :=
      Tiling.mem_negativeSide.2 (by rw [hsignMinus]; exact hstrict)
    have hsubset : Tiling.negativeSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro z hz
      have hzmem : z ∈ K.support ∩ Metric.ball q rho := by
        rw [hbranch]
        exact ⟨Tiling.mem_negativeHalfPlane.2 (Tiling.mem_negativeSide.1 hz.1).le, hz.2⟩
      exact hzmem.1
    have hopen : IsOpen (Tiling.negativeSide q d ∩ Metric.ball q rho) :=
      Tiling.isOpen_negativeSide q d |>.inter Metric.isOpen_ball
    have hzint : linePoint (q.im - h) q.re ∈ interior K.support := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        (hopen.mem_nhds ⟨hzside, hzball⟩) hsubset
    exact hzint
  have hinteriorPlusNegative (h : ℝ) (hh : 0 < h) (hhε : h < epsilon)
      (hbranch : K.support ∩ Metric.ball q rho =
        Tiling.negativeHalfPlane q d ∩ Metric.ball q rho)
      (hstrict : d.re * h < 0) :
      linePoint (q.im + h) q.re ∈ K.openCarrier := by
    have hzball := hballPlus h hh hhε
    have hzside : linePoint (q.im + h) q.re ∈ Tiling.negativeSide q d :=
      Tiling.mem_negativeSide.2 (by rw [hsignPlus]; exact hstrict)
    have hsubset : Tiling.negativeSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro z hz
      have hzmem : z ∈ K.support ∩ Metric.ball q rho := by
        rw [hbranch]
        exact ⟨Tiling.mem_negativeHalfPlane.2 (Tiling.mem_negativeSide.1 hz.1).le, hz.2⟩
      exact hzmem.1
    have hopen : IsOpen (Tiling.negativeSide q d ∩ Metric.ball q rho) :=
      Tiling.isOpen_negativeSide q d |>.inter Metric.isOpen_ball
    have hzint : linePoint (q.im + h) q.re ∈ interior K.support := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        (hopen.mem_nhds ⟨hzside, hzball⟩) hsubset
    exact hzint
  have hinteriorMinusPositive (h : ℝ) (hh : 0 < h) (hhε : h < epsilon)
      (hbranch : K.support ∩ Metric.ball q rho =
        Tiling.positiveHalfPlane q d ∩ Metric.ball q rho)
      (hstrict : -(d.re * h) > 0) :
      linePoint (q.im - h) q.re ∈ K.openCarrier := by
    have hzball := hballMinus h hh hhε
    have hzside : linePoint (q.im - h) q.re ∈ Tiling.positiveSide q d :=
      Tiling.mem_positiveSide.2 (by rw [hsignMinus]; exact hstrict)
    have hsubset : Tiling.positiveSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro z hz
      have hzmem : z ∈ K.support ∩ Metric.ball q rho := by
        rw [hbranch]
        exact ⟨Tiling.mem_positiveHalfPlane.2 (Tiling.mem_positiveSide.1 hz.1).le, hz.2⟩
      exact hzmem.1
    have hopen : IsOpen (Tiling.positiveSide q d ∩ Metric.ball q rho) :=
      Tiling.isOpen_positiveSide q d |>.inter Metric.isOpen_ball
    have hzint : linePoint (q.im - h) q.re ∈ interior K.support := by
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset
        (hopen.mem_nhds ⟨hzside, hzball⟩) hsubset
    exact hzint
  rcases lt_or_gt_of_ne hdre with hdneg | hdpos
  · rcases hhalf with hpos | hneg
    · exact ⟨epsilon, hepsilon, Or.inr (fun h hh hhε ↦
        hinteriorMinusPositive h hh hhε hpos (by
          have hp : d.re * h < 0 := mul_neg_of_neg_of_pos hdneg hh
          linarith))⟩
    · exact ⟨epsilon, hepsilon, Or.inl (fun h hh hhε ↦
        hinteriorPlusNegative h hh hhε hneg (by
          exact mul_neg_of_neg_of_pos hdneg hh))⟩
  · rcases hhalf with hpos | hneg
    · exact ⟨epsilon, hepsilon, Or.inl (fun h hh hhε ↦
        hinteriorPlus h hh hhε hpos (mul_pos hdpos hh))⟩
    · exact ⟨epsilon, hepsilon, Or.inr (fun h hh hhε ↦
        hinteriorMinus h hh hhε hneg (by
          have hp : 0 < d.re * h := mul_pos hdpos hh
          linarith))⟩

private theorem seam_placed_horizontal_side_local_uniform_germ
    {K : Region} {T : Set Tiling.Plane}
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    {y x : ℝ}
    (hxside : linePoint y x ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane)) (b.1 + (t.1 : Tiling.Plane))) :
    ∃ delta : ℝ, 0 < delta ∧
      ((∀ z : ℝ, |z - x| < delta → ∀ h : ℝ, 0 < h → h < delta →
          linePoint (y + h) z ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) ∨
       (∀ z : ℝ, |z - x| < delta → ∀ h : ℝ, 0 < h → h < delta →
          linePoint (y - h) z ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)) := by
  let p : Tiling.Plane := linePoint y x
  let q : Tiling.Plane := p - t.1
  have hqside : q ∈ openSegment ℝ a.1 b.1 := by
    have htranslated : p ∈
        (t.1 : Tiling.Plane) +ᵥ openSegment ℝ a.1 b.1 := by
      rw [vadd_openSegment ℝ]
      simpa [p, vadd_eq_add, add_comm] using hxside
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at htranslated
    simpa [q, vadd_eq_add, sub_eq_add_neg, add_comm] using htranslated
  obtain ⟨d, hd, hdim0, rho, hrho, hhalf⟩ :=
    seam_horizontal_side_local_halfPlane a b hside q hqside
  have hdre : d.re ≠ 0 := by
    intro hdre
    apply hd
    exact Complex.ext hdre hdim0
  let delta : ℝ := rho / 4
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hballPlus (z h : ℝ) (hz : |z - x| < delta)
      (hh : 0 < h) (hhd : h < delta) :
      linePoint (y + h) z - t.1 ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (linePoint (y + h) z - t.1) - q =
        ((z - x : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [q, p, linePoint]
    rw [heq]
    calc
      ‖((z - x : ℝ) : ℂ) + (h : ℂ) * Complex.I‖ ≤
          ‖((z - x : ℝ) : ℂ)‖ + ‖(h : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z - x| + h := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hh, Complex.norm_I, mul_one]
      _ < rho := by
        dsimp [delta] at hz hhd
        linarith
  have hballMinus (z h : ℝ) (hz : |z - x| < delta)
      (hh : 0 < h) (hhd : h < delta) :
      linePoint (y - h) z - t.1 ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (linePoint (y - h) z - t.1) - q =
        ((z - x : ℝ) : ℂ) + (-h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [q, p, linePoint]
    rw [heq]
    calc
      ‖((z - x : ℝ) : ℂ) + (-h : ℂ) * Complex.I‖ ≤
          ‖((z - x : ℝ) : ℂ)‖ + ‖(-h : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |z - x| + h := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_neg,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh,
          Complex.norm_I, mul_one]
      _ < rho := by
        dsimp [delta] at hz hhd
        linarith
  have hsignPlus (z h : ℝ) :
      Tiling.signedSide q d (linePoint (y + h) z - t.1) = d.re * h := by
    simp [Tiling.signedSide, Tiling.planarCross, q, p, linePoint, hdim0]
    ring
  have hsignMinus (z h : ℝ) :
      Tiling.signedSide q d (linePoint (y - h) z - t.1) = -(d.re * h) := by
    simp [Tiling.signedSide, Tiling.planarCross, q, p, linePoint, hdim0]
    ring
  have hpositiveInterior (hpositive : K.support ∩ Metric.ball q rho =
      Tiling.positiveHalfPlane q d ∩ Metric.ball q rho) :
      ∀ {w : Tiling.Plane}, w ∈ Metric.ball q rho →
        0 < Tiling.signedSide q d w → w ∈ K.openCarrier := by
    intro w hwball hwsign
    have hwside : w ∈ Tiling.positiveSide q d :=
      Tiling.mem_positiveSide.2 hwsign
    have hsubset : Tiling.positiveSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro u hu
      have hu' : u ∈ K.support ∩ Metric.ball q rho := by
        rw [hpositive]
        exact ⟨Tiling.mem_positiveHalfPlane.2
          (Tiling.mem_positiveSide.1 hu.1).le, hu.2⟩
      exact hu'.1
    apply interior_maximal hsubset
      (Tiling.isOpen_positiveSide q d |>.inter Metric.isOpen_ball)
    exact ⟨hwside, hwball⟩
  have hnegativeInterior (hnegative : K.support ∩ Metric.ball q rho =
      Tiling.negativeHalfPlane q d ∩ Metric.ball q rho) :
      ∀ {w : Tiling.Plane}, w ∈ Metric.ball q rho →
        Tiling.signedSide q d w < 0 → w ∈ K.openCarrier := by
    intro w hwball hwsign
    have hwside : w ∈ Tiling.negativeSide q d :=
      Tiling.mem_negativeSide.2 hwsign
    have hsubset : Tiling.negativeSide q d ∩ Metric.ball q rho ⊆ K.support := by
      intro u hu
      have hu' : u ∈ K.support ∩ Metric.ball q rho := by
        rw [hnegative]
        exact ⟨Tiling.mem_negativeHalfPlane.2
          (Tiling.mem_negativeSide.1 hu.1).le, hu.2⟩
      exact hu'.1
    apply interior_maximal hsubset
      (Tiling.isOpen_negativeSide q d |>.inter Metric.isOpen_ball)
    exact ⟨hwside, hwball⟩
  have htranslateOpen {g w : Tiling.Plane}
      (heq : w = g - t.1) (hw : w ∈ K.openCarrier) :
      g ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [heq, vadd_eq_add, sub_eq_add_neg, add_comm] using hw
  refine ⟨delta, hdelta, ?_⟩
  rcases lt_or_gt_of_ne hdre with hdneg | hdpos
  · rcases hhalf with hpositive | hnegative
    · right
      intro z hz h hh hhd
      apply htranslateOpen rfl
      apply hpositiveInterior hpositive (hballMinus z h hz hh hhd)
      rw [hsignMinus]
      exact neg_pos.mpr (mul_neg_of_neg_of_pos hdneg hh)
    · left
      intro z hz h hh hhd
      apply htranslateOpen rfl
      apply hnegativeInterior hnegative (hballPlus z h hz hh hhd)
      rw [hsignPlus]
      exact mul_neg_of_neg_of_pos hdneg hh
  · rcases hhalf with hpositive | hnegative
    · left
      intro z hz h hh hhd
      apply htranslateOpen rfl
      apply hpositiveInterior hpositive (hballPlus z h hz hh hhd)
      rw [hsignPlus]
      exact mul_pos hdpos hh
    · right
      intro z hz h hh hhd
      apply htranslateOpen rfl
      apply hnegativeInterior hnegative (hballMinus z h hz hh hhd)
      rw [hsignMinus]
      exact neg_lt_zero.mpr (mul_pos hdpos hh)

private theorem seam_placed_horizontal_side_germs_disjoint
    {K : Region} {T : Set Tiling.Plane}
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    {y x : ℝ}
    (hxside : linePoint y x ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane)) (b.1 + (t.1 : Tiling.Plane)))
    (hupper : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y + h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hlower : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y - h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) : False := by
  let p : Tiling.Plane := linePoint y x
  let q : Tiling.Plane := p - t.1
  have hqside : q ∈ openSegment ℝ a.1 b.1 := by
    have htranslated : p ∈
        (t.1 : Tiling.Plane) +ᵥ openSegment ℝ a.1 b.1 := by
      rw [vadd_openSegment ℝ]
      simpa [p, vadd_eq_add, add_comm] using hxside
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at htranslated
    simpa [q, vadd_eq_add, sub_eq_add_neg, add_comm] using htranslated
  obtain ⟨d, hd, hdim0, rho, hrho, hhalf⟩ :=
    seam_horizontal_side_local_halfPlane a b hside q hqside
  have hdre : d.re ≠ 0 := by
    intro hdre
    apply hd
    exact Complex.ext hdre hdim0
  obtain ⟨epsilonU, hepsilonU, hupper⟩ := hupper
  obtain ⟨epsilonL, hepsilonL, hlower⟩ := hlower
  let h : ℝ := min (rho / 2) (min (epsilonU / 2) (epsilonL / 2))
  have hh : 0 < h := by
    dsimp [h]
    exact lt_min (half_pos hrho)
      (lt_min (half_pos hepsilonU) (half_pos hepsilonL))
  have hhrho : h < rho := (min_le_left _ _).trans_lt (half_lt_self hrho)
  have hhU : h < epsilonU :=
    (min_le_right _ _).trans (min_le_left _ _) |>.trans_lt
      (half_lt_self hepsilonU)
  have hhL : h < epsilonL :=
    (min_le_right _ _).trans (min_le_right _ _) |>.trans_lt
      (half_lt_self hepsilonL)
  let gPlus : Tiling.Plane := linePoint (y + h) x
  let gMinus : Tiling.Plane := linePoint (y - h) x
  let zPlus : Tiling.Plane := gPlus - t.1
  let zMinus : Tiling.Plane := gMinus - t.1
  have hzPlusBall : zPlus ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : zPlus - q = (h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [zPlus, gPlus, q, p, linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hh]
    exact hhrho
  have hzMinusBall : zMinus ∈ Metric.ball q rho := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : zMinus - q = (-h : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [zMinus, gMinus, q, p, linePoint]
    rw [heq, norm_mul, Complex.norm_I, mul_one, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
    exact hhrho
  have htranslatePlus : (t.1 : Tiling.Plane) +ᵥ zPlus = gPlus := by
    simp [zPlus, vadd_eq_add]
  have htranslateMinus : (t.1 : Tiling.Plane) +ᵥ zMinus = gMinus := by
    simp [zMinus, vadd_eq_add]
  have hsignPlus : Tiling.signedSide q d zPlus = d.re * h := by
    simp [Tiling.signedSide, Tiling.planarCross, q, p, zPlus, gPlus,
      linePoint, hdim0]
    ring
  have hsignMinus : Tiling.signedSide q d zMinus = -(d.re * h) := by
    simp [Tiling.signedSide, Tiling.planarCross, q, p, zMinus, gMinus,
      linePoint, hdim0]
    ring
  have hgPlusOpen : gPlus ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier :=
    hupper h hh hhU
  have hgMinusOpen : gMinus ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier :=
    hlower h hh hhL
  have hgPlusSupport : gPlus ∈ (t.1 : Tiling.Plane) +ᵥ K.support := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hgPlusOpen ⊢
    exact interior_subset hgPlusOpen
  have hgMinusSupport : gMinus ∈ (t.1 : Tiling.Plane) +ᵥ K.support := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hgMinusOpen ⊢
    exact interior_subset hgMinusOpen
  rcases lt_or_gt_of_ne hdre with hdneg | hdpos
  · rcases hhalf with hpositive | hnegative
    · exact (seam_notSupport_of_positiveHalfPlane hpositive hzPlusBall
        htranslatePlus (by rw [hsignPlus]; exact mul_neg_of_neg_of_pos hdneg hh))
        hgPlusSupport
    · exact (seam_notSupport_of_negativeHalfPlane hnegative hzMinusBall
        htranslateMinus (by
          rw [hsignMinus]
          exact neg_pos.mpr (mul_neg_of_neg_of_pos hdneg hh))) hgMinusSupport
  · rcases hhalf with hpositive | hnegative
    · exact (seam_notSupport_of_positiveHalfPlane hpositive hzMinusBall
        htranslateMinus (by
          rw [hsignMinus]
          exact neg_lt_zero.mpr (mul_pos hdpos hh))) hgMinusSupport
    · exact (seam_notSupport_of_negativeHalfPlane hnegative hzPlusBall
        htranslatePlus (by rw [hsignPlus]; exact mul_pos hdpos hh)) hgPlusSupport

private theorem seam_placed_horizontal_side_global_germ
    {K : Region} {T : Set Tiling.Plane}
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    {y l r : ℝ}
    (hall : ∀ x ∈ Ioo l r, linePoint y x ∈ openSegment ℝ
      (a.1 + (t.1 : Tiling.Plane)) (b.1 + (t.1 : Tiling.Plane))) :
    (∀ x ∈ Ioo l r, ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y + h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) ∨
    (∀ x ∈ Ioo l r, ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y - h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
  let Upper : ℝ → Prop := fun x ↦
    ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y + h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier
  let Lower : ℝ → Prop := fun x ↦
    ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y - h) x ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier
  let U : Set ℝ := {z | z ∈ Ioo l r ∧
    ∃ x ∈ Ioo l r, ∃ delta > 0,
      (∀ w : ℝ, |w - x| < delta → Upper w) ∧ |z - x| < delta}
  let V : Set ℝ := {z | z ∈ Ioo l r ∧
    ∃ x ∈ Ioo l r, ∃ delta > 0,
      (∀ w : ℝ, |w - x| < delta → Lower w) ∧ |z - x| < delta}
  have hUopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨hzI, x, hxI, delta, hdelta, hlocal, hzx⟩
    have hopen : IsOpen {w : ℝ | |w - x| < delta} := by
      have heq : {w : ℝ | |w - x| < delta} = Metric.ball x delta := by
        ext w
        simp [Real.dist_eq, abs_sub_comm]
      rw [heq]
      exact Metric.isOpen_ball
    filter_upwards [isOpen_Ioo.mem_nhds hzI, hopen.mem_nhds hzx] with w hwI hw
    exact ⟨hwI, x, hxI, delta, hdelta, hlocal, hw⟩
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨hzI, x, hxI, delta, hdelta, hlocal, hzx⟩
    have hopen : IsOpen {w : ℝ | |w - x| < delta} := by
      have heq : {w : ℝ | |w - x| < delta} = Metric.ball x delta := by
        ext w
        simp [Real.dist_eq, abs_sub_comm]
      rw [heq]
      exact Metric.isOpen_ball
    filter_upwards [isOpen_Ioo.mem_nhds hzI, hopen.mem_nhds hzx] with w hwI hw
    exact ⟨hwI, x, hxI, delta, hdelta, hlocal, hw⟩
  have hUUpper {z : ℝ} (hz : z ∈ U) : Upper z := by
    rcases hz.2 with ⟨x, _hxI, delta, _hdelta, hlocal, hzx⟩
    exact hlocal z hzx
  have hVLower {z : ℝ} (hz : z ∈ V) : Lower z := by
    rcases hz.2 with ⟨x, _hxI, delta, _hdelta, hlocal, hzx⟩
    exact hlocal z hzx
  have hUVdis : Disjoint U V := by
    rw [Set.disjoint_left]
    intro z hzU hzV
    exact seam_placed_horizontal_side_germs_disjoint t a b hside
      (hall z hzU.1) (hUUpper hzU) (hVLower hzV)
  have hUVcover : Ioo l r ⊆ U ∪ V := by
    intro x hx
    obtain ⟨delta, hdelta, hupper | hlower⟩ :=
      seam_placed_horizontal_side_local_uniform_germ t a b hside (hall x hx)
    · left
      refine ⟨hx, x, hx, delta, hdelta, ?_, ?_⟩
      · intro w hw
        exact ⟨delta, hdelta, hupper w hw⟩
      · simpa using hdelta
    · right
      refine ⟨hx, x, hx, delta, hdelta, ?_, ?_⟩
      · intro w hw
        exact ⟨delta, hdelta, hlower w hw⟩
      · simpa using hdelta
  rcases isPreconnected_Ioo.subset_or_subset hUopen hVopen hUVdis hUVcover with
    hU | hV
  · left
    intro x hx
    exact hUUpper (hU hx)
  · right
    intro x hx
    exact hVLower (hV hx)

private theorem seam_distinct_owners_not_same_upper
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) {y l r : ℝ} (hlr : l < r)
    (t0 t1 : ↥T) (htne : t1 ≠ t0)
    (hupper0 : ∀ x ∈ Ioo l r, ∃ epsilon > 0,
      ∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y + h) x ∈ (t0.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hupper1 : ∀ x ∈ Ioo l r, ∃ epsilon > 0,
      ∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y + h) x ∈ (t1.1 : Tiling.Plane) +ᵥ K.openCarrier) : False := by
  let x : ℝ := (l + r) / 2
  have hx : x ∈ Ioo l r := by
    dsimp [x]
    constructor <;> linarith
  obtain ⟨epsilon0, hepsilon0, h0⟩ := hupper0 x hx
  obtain ⟨epsilon1, hepsilon1, h1⟩ := hupper1 x hx
  let h : ℝ := min (epsilon0 / 2) (epsilon1 / 2)
  have hh : 0 < h := lt_min (half_pos hepsilon0) (half_pos hepsilon1)
  have hh0 : h < epsilon0 :=
    (min_le_left _ _).trans_lt (half_lt_self hepsilon0)
  have hh1 : h < epsilon1 :=
    (min_le_right _ _).trans_lt (half_lt_self hepsilon1)
  have hp0 := h0 h hh hh0
  have hp1 := h1 h hh hh1
  have hdisj := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
    hTile.2.1 t0.2 t1.2 (by
      intro heq
      exact htne (Subtype.ext heq.symm))
  exact Set.disjoint_left.1 hdisj hp0 hp1

private theorem seam_distinct_owners_not_same_lower
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) {y l r : ℝ} (hlr : l < r)
    (t0 t1 : ↥T) (htne : t1 ≠ t0)
    (hlower0 : ∀ x ∈ Ioo l r, ∃ epsilon > 0,
      ∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y - h) x ∈ (t0.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hlower1 : ∀ x ∈ Ioo l r, ∃ epsilon > 0,
      ∀ h : ℝ, 0 < h → h < epsilon →
        linePoint (y - h) x ∈ (t1.1 : Tiling.Plane) +ᵥ K.openCarrier) : False := by
  let x : ℝ := (l + r) / 2
  have hx : x ∈ Ioo l r := by
    dsimp [x]
    constructor <;> linarith
  obtain ⟨epsilon0, hepsilon0, h0⟩ := hlower0 x hx
  obtain ⟨epsilon1, hepsilon1, h1⟩ := hlower1 x hx
  let h : ℝ := min (epsilon0 / 2) (epsilon1 / 2)
  have hh : 0 < h := lt_min (half_pos hepsilon0) (half_pos hepsilon1)
  have hh0 : h < epsilon0 :=
    (min_le_left _ _).trans_lt (half_lt_self hepsilon0)
  have hh1 : h < epsilon1 :=
    (min_le_right _ _).trans_lt (half_lt_self hepsilon1)
  have hp0 := h0 h hh hh0
  have hp1 := h1 h hh hh1
  have hdisj := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp
    hTile.2.1 t0.2 t1.2 (by
      intro heq
      exact htne (Subtype.ext heq.symm))
  exact Set.disjoint_left.1 hdisj hp0 hp1

private theorem horizontalSeamCell_of_no_open
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) (y l r : ℝ) (hlr : l < r)
    (hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hNoCut : Ioo l r ∩ horizontalLineCutSet K T y = ∅) :
    Nonempty (HorizontalSeamCell K T y l r) := by
  let m : ℝ := (l + r) / 2
  have hm : m ∈ Ioo l r := by
    dsimp [m]
    constructor <;> linarith
  obtain ⟨t0, a, b, hside0, hmid0⟩ :=
    seam_midpoint_horizontal_edge hTile y l r hlr hNoOpen hNoCut
  have hall0 : ∀ x ∈ Ioo l r, linePoint y x ∈ openSegment ℝ
      (a.1 + (t0.1 : Tiling.Plane)) (b.1 + (t0.1 : Tiling.Plane)) :=
    seam_horizontal_side_extends hlr hNoCut t0 a b hside0 hm (by
      simpa [m] using hmid0)
  obtain ⟨t1, a', b', htne, hside1, hall1⟩ :=
    seam_midpoint_second_owner hTile y l r hlr hNoOpen hNoCut
      t0 a b hside0 hmid0
  have horient0 :=
    seam_placed_horizontal_side_global_germ t0 a b hside0 hall0
  have horient1 :=
    seam_placed_horizontal_side_global_germ t1 a' b' hside1 hall1
  rcases horient0 with hupper0 | hlower0
  · rcases horient1 with hupper1 | hlower1
    · exact False.elim
        (seam_distinct_owners_not_same_upper hTile hlr t0 t1 htne hupper0 hupper1)
    · refine ⟨{
        upperCenter := t0
        lowerCenter := t1
        centers_ne := htne.symm
        a := a
        b := b
        a' := a'
        b' := b'
        left_lt_right := hlr
        first_horizontal := hside0
        second_horizontal := hside1
        first_side := hall0
        second_side := hall1
        opposite_germs := ?_ }⟩
      intro x hx
      obtain ⟨epsilon0, hepsilon0, h0⟩ := hupper0 x hx
      obtain ⟨epsilon1, hepsilon1, h1⟩ := hlower1 x hx
      refine ⟨min epsilon0 epsilon1, lt_min hepsilon0 hepsilon1, ?_, ?_⟩
      · intro h hh hmin
        exact h0 h hh (hmin.trans_le (min_le_left _ _))
      · intro h hh hmin
        exact h1 h hh (hmin.trans_le (min_le_right _ _))
  · rcases horient1 with hupper1 | hlower1
    · refine ⟨{
        upperCenter := t1
        lowerCenter := t0
        centers_ne := htne
        a := a'
        b := b'
        a' := a
        b' := b
        left_lt_right := hlr
        first_horizontal := hside1
        second_horizontal := hside0
        first_side := hall1
        second_side := hall0
        opposite_germs := ?_ }⟩
      intro x hx
      obtain ⟨epsilon1, hepsilon1, h1⟩ := hupper1 x hx
      obtain ⟨epsilon0, hepsilon0, h0⟩ := hlower0 x hx
      refine ⟨min epsilon1 epsilon0, lt_min hepsilon1 hepsilon0, ?_, ?_⟩
      · intro h hh hmin
        exact h1 h hh (hmin.trans_le (min_le_left _ _))
      · intro h hh hmin
        exact h0 h hh (hmin.trans_le (min_le_right _ _))
    · exact False.elim
        (seam_distinct_owners_not_same_lower hTile hlr t0 t1 htne hlower0 hlower1)
private theorem endpoint_owner_frontier_of_cut
    {K : Region} {T : Set Tiling.Plane} {y x : ℝ}
    (hTile : TilesOn K T univ)
    (owner : ↥T) (W : HorizontalLineCutWitness K T y x)
    (howner : linePoint y x ∈
      (owner.1 : Tiling.Plane) +ᵥ K.support) :
    linePoint y x ∈ frontier ((owner.1 : Tiling.Plane) +ᵥ K.support) := by
  have hWfront : linePoint y x ∈
      frontier ((W.center.1 : Tiling.Plane) +ᵥ K.support) := by
    have hopenSub : openSegment ℝ
        (W.v.1 + (W.center.1 : Tiling.Plane))
        (W.w.1 + (W.center.1 : Tiling.Plane)) ⊆
        frontier ((W.center.1 : Tiling.Plane) +ᵥ K.support) := by
      rw [show W.v.1 + (W.center.1 : Tiling.Plane) =
          (W.center.1 : Tiling.Plane) +ᵥ W.v.1 by simp [add_comm],
        show W.w.1 + (W.center.1 : Tiling.Plane) =
          (W.center.1 : Tiling.Plane) +ᵥ W.w.1 by simp [add_comm],
        ← vadd_openSegment ℝ, Tiling.AxisParallel.frontier_vadd_eq]
      intro q hq
      rw [mem_vadd_set] at hq
      obtain ⟨q₀, hq₀, rfl⟩ := hq
      exact ⟨q₀, (W.side.2.2 hq₀).1, rfl⟩
    have hsegClosure := segment_subset_closure_openSegment
      (𝕜 := ℝ) W.line_meets_side
    exact isClosed_frontier.closure_subset_iff.mpr hopenSub hsegClosure
  have hWclosure : linePoint y x ∈ closure
      ((W.center.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    rw [closure_vadd]
    change linePoint y x ∈ (W.center.1 : Tiling.Plane) +ᵥ closure K.openCarrier
    rw [show closure K.openCarrier = K.support from by
      change closure (interior K.support) = K.support
      exact K.isPolygonal.closure_interior]
    rw [← (K.isPolygonal.isClosed.vadd (W.center.1 : Tiling.Plane)).closure_eq]
    exact frontier_subset_closure hWfront
  have hownerNotInterior : linePoint y x ∉
      interior ((owner.1 : Tiling.Plane) +ᵥ K.support) := by
    intro hownerInterior
    by_cases hsame : W.center = owner
    · have hsame' : (W.center.1 : Tiling.Plane) = owner.1 := congrArg Subtype.val hsame
      have hfront' : linePoint y x ∈ frontier
          ((owner.1 : Tiling.Plane) +ᵥ K.support) := by
        simpa [hsame'] using hWfront
      exact hfront'.2 hownerInterior
    · have hopenOwner : IsOpen ((owner.1 : Tiling.Plane) +ᵥ K.openCarrier) :=
        isOpen_interior.vadd _
      have hownerOpen : linePoint y x ∈
          (owner.1 : Tiling.Plane) +ᵥ K.openCarrier := by
        have hownerInterior' : linePoint y x ∈
            (owner.1 : Tiling.Plane) +ᵥ interior K.support := by
          rw [← interior_vadd]
          exact hownerInterior
        exact hownerInterior'
      obtain ⟨z, hzW, hzO⟩ := mem_closure_iff.mp hWclosure _
        hopenOwner hownerOpen
      have hdis := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        W.center.2 owner.2 (by intro h; exact hsame (Subtype.ext h))
      exact Set.disjoint_left.mp hdis hzO hzW
  rw [frontier]
  exact ⟨subset_closure howner, hownerNotInterior⟩

private theorem endpoint_vertical_data_of_cut
    {K : Region} {T : Set Tiling.Plane} {y l r e : ℝ}
    (hTile : TilesOn K T univ) (center : ↥T)
    (hlr : l < r)
    (he : e = l ∨ e = r)
    (W : HorizontalLineCutWitness K T y e)
    (howner : linePoint y e ∈
      (center.1 : Tiling.Plane) +ᵥ K.support)
    (hcross : ∀ x ∈ Ioo l r,
      linePoint y x ∈ (center.1 : Tiling.Plane) +ᵥ K.openCarrier) :
    ∃ v w : ↥K.vertices,
      IsIntrinsicSide K v w ∧ v.1.re = w.1.re ∧
        e = (v.1 + (center.1 : Tiling.Plane)).re ∧
        linePoint y e ∈ segment ℝ (v.1 + (center.1 : Tiling.Plane))
          (w.1 + (center.1 : Tiling.Plane)) := by
  have hpfront : linePoint y e ∈
      frontier ((center.1 : Tiling.Plane) +ᵥ K.support) :=
    endpoint_owner_frontier_of_cut hTile center W howner
  have hqfront : linePoint y e - center.1 ∈ frontier K.support := by
    rw [Tiling.AxisParallel.frontier_vadd_eq] at hpfront
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hpfront
    change -center.1 + linePoint y e ∈ frontier K.support at hpfront
    rw [show -center.1 + linePoint y e = linePoint y e - center.1 by abel] at hpfront
    exact hpfront
  have hcoord_re {v w q : Tiling.Plane} (hvw : v.re = w.re)
      (hq : q ∈ segment ℝ v w) : q.re = v.re := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re,
      smul_eq_mul]
    rw [hvw]
    ring
  have hcoord_im {v w q : Tiling.Plane} (hvw : v.im = w.im)
      (hq : q ∈ segment ℝ v w) : q.im = v.im := by
    rw [segment_eq_image_lineMap] at hq
    obtain ⟨s, _, rfl⟩ := hq
    simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im,
      smul_eq_mul]
    rw [hvw]
    ring
  by_cases hpvertex : linePoint y e - center.1 ∈ K.vertices
  · obtain ⟨w, hwne, hwtrans, hwside⟩ :=
      IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.vertical
        ⟨linePoint y e - center.1, hpvertex⟩
    let v : ↥K.vertices := ⟨linePoint y e - center.1, hpvertex⟩
    have hside : IsIntrinsicSide K v w := by
      refine ⟨hwne.symm, ?_, hwside⟩
      exact Or.inl hwtrans.symm
    have hpEq : linePoint y e = v.1 + (center.1 : Tiling.Plane) := by
      simp [v]
    have hecoord : e = (v.1 + (center.1 : Tiling.Plane)).re := by
      simpa [linePoint] using congrArg Complex.re hpEq
    have hmeet : linePoint y e ∈
        segment ℝ (v.1 + (center.1 : Tiling.Plane))
          (w.1 + (center.1 : Tiling.Plane)) := by
      rw [hpEq]
      exact left_mem_segment ℝ _ _
    exact ⟨v, w, hside, hwtrans.symm, hecoord, hmeet⟩
  · obtain ⟨axis, v, w, hvw, htrans, hpseg, hside⟩ :=
      IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K
        (linePoint y e - center.1) hqfront hpvertex
    cases axis with
    | vertical =>
        have hpseg' : linePoint y e - center.1 ∈ segment ℝ v.1 w.1 :=
          openSegment_subset_segment ℝ v.1 w.1 hpseg
        have hpre : (linePoint y e - center.1).re = v.1.re :=
          hcoord_re htrans hpseg'
        have hpre' : e - center.1.re = v.1.re := by
          simpa [linePoint] using hpre
        have hecoord : e = (v.1 + (center.1 : Tiling.Plane)).re := by
          dsimp only [Complex.add_re]
          linarith
        have hmeet : linePoint y e ∈
            segment ℝ (v.1 + (center.1 : Tiling.Plane))
              (w.1 + (center.1 : Tiling.Plane)) := by
          have hvadd := vadd_segment (𝕜 := ℝ) (center.1 : Tiling.Plane) v.1 w.1
          have hseg : linePoint y e ∈
              segment ℝ ((center.1 : Tiling.Plane) +ᵥ v.1)
                ((center.1 : Tiling.Plane) +ᵥ w.1) := by
            rw [← hvadd]
            have hqv : (center.1 : Tiling.Plane) +ᵥ
                (linePoint y e - center.1) ∈
                (center.1 : Tiling.Plane) +ᵥ segment ℝ v.1 w.1 :=
              vadd_mem_vadd_set hpseg'
            simpa only [vadd_eq_add, add_comm, add_sub_cancel] using hqv
          simpa [vadd_eq_add, add_comm] using hseg
        exact ⟨v, w, ⟨hvw, Or.inl htrans, hside⟩, htrans, hecoord, hmeet⟩
    | horizontal =>
        change v.1.im = w.1.im at htrans
        have hpseg' : linePoint y e - center.1 ∈ segment ℝ v.1 w.1 :=
          openSegment_subset_segment ℝ v.1 w.1 hpseg
        have hpim' : (linePoint y e - center.1).im = v.1.im :=
          hcoord_im htrans hpseg'
        let a : Tiling.Plane := v.1 + (center.1 : Tiling.Plane)
        let b : Tiling.Plane := w.1 + (center.1 : Tiling.Plane)
        have hab : a ≠ b := by
          intro habEq
          apply hvw
          apply add_right_cancel (b := (center.1 : Tiling.Plane))
          simpa [a, b] using habEq
        have habIm : a.im = b.im := by simp [a, b, htrans]
        have hpRe : e ∈ openSegment ℝ a.re b.re := by
          have h := fct_re_mem_openSegment_of_mem
            (show linePoint y e ∈ openSegment ℝ a b by
              rw [show a = (center.1 : Tiling.Plane) +ᵥ v.1 by simp [a, add_comm],
                show b = (center.1 : Tiling.Plane) +ᵥ w.1 by simp [b, add_comm],
                ← vadd_openSegment ℝ]
              exact ⟨linePoint y e - center.1, hpseg,
                by simp [vadd_eq_add]⟩)
          simpa [a, b, linePoint] using h
        have hJopen : IsOpen (openSegment ℝ a.re b.re) := by
          have habRe : a.re ≠ b.re := by
            intro hre
            exact hab (Complex.ext hre habIm)
          rcases lt_or_gt_of_ne habRe with habLt | hbaLt
          · rw [openSegment_eq_Ioo habLt]
            exact isOpen_Ioo
          · rw [openSegment_symm, openSegment_eq_Ioo hbaLt]
            exact isOpen_Ioo
        obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJopen e hpRe
        have hz : ∃ z : ℝ, z ∈ Ioo l r ∧
            z ∈ openSegment ℝ a.re b.re := by
          rcases he with hel | her
          · let δ : ℝ := min (ε / 2) ((r - l) / 2)
            have hδ : 0 < δ := by
              dsimp [δ]
              exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hlr))
            refine ⟨l + δ, ?_, hball ?_⟩
            · constructor <;> dsimp [δ] at hδ ⊢ <;>
                linarith [hδ, min_le_right (ε / 2) ((r - l) / 2)]
            · change dist (l + δ) e < ε
              rw [hel, Real.dist_eq]
              simp [abs_of_pos hδ]
              linarith [min_le_left (ε / 2) ((r - l) / 2)]
          · let δ : ℝ := min (ε / 2) ((r - l) / 2)
            have hδ : 0 < δ := by
              dsimp [δ]
              exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hlr))
            refine ⟨r - δ, ?_, hball ?_⟩
            · constructor <;> dsimp [δ] at hδ ⊢ <;>
                linarith [hδ, min_le_right (ε / 2) ((r - l) / 2)]
            · change dist (r - δ) e < ε
              rw [her, Real.dist_eq]
              simp [abs_of_pos hδ]
              linarith [min_le_left (ε / 2) ((r - l) / 2)]
        obtain ⟨z, hzI, hzJ⟩ := hz
        have hedgePlaced : openSegment ℝ a b ⊆
            frontier ((center.1 : Tiling.Plane) +ᵥ K.support) := by
          rw [show a = (center.1 : Tiling.Plane) +ᵥ v.1 by simp [a, add_comm],
            show b = (center.1 : Tiling.Plane) +ᵥ w.1 by simp [b, add_comm],
            ← vadd_openSegment ℝ, Tiling.AxisParallel.frontier_vadd_eq]
          rintro z' ⟨q, hq, rfl⟩
          exact ⟨q, (hside hq).1, rfl⟩
        have hy : y = a.im := by
          have hpim : (linePoint y e).im = a.im := by
            rw [show a = v.1 + (center.1 : Tiling.Plane) by rfl]
            have hpim'' : (linePoint y e).im - center.1.im = v.1.im := by
              simpa only [Complex.sub_im] using hpim'
            dsimp only [Complex.add_im]
            linarith [hpim'']
          simpa [linePoint] using hpim
        have hzSide : linePoint y z ∈ openSegment ℝ a b := by
          rw [show linePoint y z = (z : ℂ) + a.im * Complex.I by
            simp [linePoint, hy]]
          exact (fct_horizontal_point_mem_openSegment_iff hab habIm z).2 hzJ
        have hzFront := hedgePlaced hzSide
        have hzOpen := hcross z hzI
        exact (hzFront.2 (by rw [interior_vadd]; exact hzOpen)).elim

private theorem horizontalCrossingCell_of_cuts_and_owner
    {K : Region} {T : Set Tiling.Plane} {y l r : ℝ}
    (hTile : TilesOn K T univ) (hlr : l < r)
    (Wl : HorizontalLineCutWitness K T y l)
    (Wr : HorizontalLineCutWitness K T y r)
    (center : ↥T)
    (hcross : ∀ x ∈ Ioo l r,
      linePoint y x ∈ (center.1 : Tiling.Plane) +ᵥ K.openCarrier) :
    Nonempty (HorizontalCrossingCell K T y l r) := by
  have hlineCont : Continuous (linePoint y) := by
    change Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I)
    fun_prop
  have himage : linePoint y '' Ioo l r ⊆
      (center.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcross x hx
  have hlClosure : l ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact ⟨le_rfl, hlr.le⟩
  have hrClosure : r ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact ⟨hlr.le, le_rfl⟩
  have endpoint_support (e : ℝ) (he : e = l ∨ e = r)
      (W : HorizontalLineCutWitness K T y e) :
      linePoint y e ∈ (center.1 : Tiling.Plane) +ᵥ K.support := by
    have hcl : linePoint y e ∈ closure
        ((center.1 : Tiling.Plane) +ᵥ K.openCarrier) :=
      closure_mono himage <| by
        rcases he with rfl | rfl
        · exact mem_closure_image hlineCont.continuousAt hlClosure
        · exact mem_closure_image hlineCont.continuousAt hrClosure
    rw [closure_vadd] at hcl
    change linePoint y e ∈
      (center.1 : Tiling.Plane) +ᵥ closure K.openCarrier at hcl
    rw [show closure K.openCarrier = K.support from by
      change closure (interior K.support) = K.support
      exact K.isPolygonal.closure_interior] at hcl
    exact hcl
  obtain ⟨leftBottom, leftTop, hleft, hleftCoord, hleftEndpoint, hleftLevel⟩ :=
    endpoint_vertical_data_of_cut hTile center hlr (Or.inl rfl) Wl
      (endpoint_support l (Or.inl rfl) Wl) hcross
  obtain ⟨rightBottom, rightTop, hright, hrightCoord, hrightEndpoint, hrightLevel⟩ :=
    endpoint_vertical_data_of_cut hTile center hlr (Or.inr rfl) Wr
      (endpoint_support r (Or.inr rfl) Wr) hcross
  exact ⟨{
    center := center
    leftBottom := leftBottom
    leftTop := leftTop
    rightBottom := rightBottom
    rightTop := rightTop
    left_lt_right := hlr
    left_coordinate := hleftEndpoint
    right_coordinate := hrightEndpoint
    left_vertical := ⟨hleft, hleftCoord⟩
    right_vertical := ⟨hright, hrightCoord⟩
    left_endpoint_at_level := hleftLevel
    right_endpoint_at_level := hrightLevel
    crossing := hcross }⟩

private theorem horizontalLineCell_classification :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ (y l r : ℝ), l < r →
      l ∈ horizontalLineCutSet K T y →
      r ∈ horizontalLineCutSet K T y →
      Ioo l r ∩ horizontalLineCutSet K T y = ∅ →
      Nonempty (HorizontalCrossingCell K T y l r) ∨
        Nonempty (HorizontalSeamCell K T y l r)) := by
  intro K T hTile y l r hlr hlcut hrcut hNoCut
  obtain ⟨Wl⟩ := hlcut
  obtain ⟨Wr⟩ := hrcut
  by_cases hCross : ∃ center : ↥T, ∀ x ∈ Ioo l r,
      linePoint y x ∈ (center.1 : Tiling.Plane) +ᵥ K.openCarrier
  · obtain ⟨center, hcross⟩ := hCross
    exact Or.inl (horizontalCrossingCell_of_cuts_and_owner
      hTile hlr Wl Wr center hcross)
  · have hNoOpen : ∀ t : ↥T, ∀ x ∈ Ioo l r,
        linePoint y x ∉ (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
      intro t
      rcases horizontalLineCell_constantMembership hTile y l r hlr hNoCut t with
        hcross | hout
      · exact False.elim (hCross ⟨t, hcross⟩)
      · exact hout
    exact Or.inr (horizontalSeamCell_of_no_open
      hTile y l r hlr hNoOpen hNoCut)



private theorem target9_cut_not_on_same_horizontal_side
    {K : Region} {T : Set Tiling.Plane} {y x : ℝ}
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    (hxside : linePoint y x ∈
      openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
        (b.1 + (t.1 : Tiling.Plane)))
    (W : HorizontalLineCutWitness K T y x)
    (hcenter : W.center = t) : False := by
  have hpbase : linePoint y x - t.1 ∈ openSegment ℝ a.1 b.1 := by
    rw [show a.1 + (t.1 : Tiling.Plane) =
        (t.1 : Tiling.Plane) +ᵥ a.1 by simp [add_comm],
      show b.1 + (t.1 : Tiling.Plane) =
        (t.1 : Tiling.Plane) +ᵥ b.1 by simp [add_comm],
      ← vadd_openSegment ℝ] at hxside
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxside
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hxside
  have hpnotvertex : linePoint y x - t.1 ∉ K.vertices := by
    intro hpv
    exact (hside.2.2 hpbase).2 hpv
  have hWseg : linePoint y x - t.1 ∈ segment ℝ W.v.1 W.w.1 := by
    have hseg := W.line_meets_side
    rw [hcenter] at hseg
    rw [show W.v.1 + (t.1 : Tiling.Plane) =
        (t.1 : Tiling.Plane) +ᵥ W.v.1 by simp [add_comm],
      show W.w.1 + (t.1 : Tiling.Plane) =
        (t.1 : Tiling.Plane) +ᵥ W.w.1 by simp [add_comm],
      ← vadd_segment (𝕜 := ℝ)] at hseg
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hseg
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hseg
  have hWendpoints_not_mem (u : ↥K.vertices) :
      linePoint y x - t.1 ≠ u.1 := by
    intro heq
    apply hpnotvertex
    rw [heq]
    exact u.2
  rcases W.side.2.1 with hWvertical | hWhorizontal
  · apply hpnotvertex
    exact K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
      hside.1 hside.2.1 (fun z hz => (hside.2.2 hz).1) hpbase
      W.side.1 hWvertical
      (mem_openSegment_of_ne_left_right
        (hWendpoints_not_mem W.v).symm (hWendpoints_not_mem W.w).symm hWseg)
      (fun z hz => (W.side.2.2 hz).1)
  · have hpim : (linePoint y x - t.1).im = W.v.1.im := by
      rw [segment_eq_image_lineMap] at hWseg
      obtain ⟨s, _hs, hsEq⟩ := hWseg
      rw [← hsEq]
      simp only [AffineMap.lineMap_apply_module,
        Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [hWhorizontal]
      ring
    have hpim' : (linePoint y x).im =
        (W.v.1 + (t.1 : Tiling.Plane)).im := by
      dsimp only [Complex.sub_im] at hpim
      dsimp only [Complex.add_im]
      linarith
    have hcoord := W.x_coordinate
    rw [hcenter] at hcoord
    rcases hcoord with hcoord | hcoord
    · have hpre : (linePoint y x).re =
          (W.v.1 + (t.1 : Tiling.Plane)).re := by
        simpa [linePoint] using hcoord
      have hpeq : linePoint y x = W.v.1 + (t.1 : Tiling.Plane) := by
        apply Complex.ext
        · exact hpre
        · exact hpim'
      apply hpnotvertex
      rw [hpeq]
      simp [sub_eq_add_neg, add_assoc, W.v.2]
    · have hpre : (linePoint y x).re =
          (W.w.1 + (t.1 : Tiling.Plane)).re := by
        simpa [linePoint] using hcoord
      have hpeq : linePoint y x = W.w.1 + (t.1 : Tiling.Plane) := by
        apply Complex.ext
        · exact hpre
        · have hpimW : (linePoint y x - t.1).im = W.w.1.im := by
            simpa [hWhorizontal] using hpim
          dsimp only [Complex.sub_im] at hpimW
          dsimp only [Complex.add_im]
          linarith
      apply hpnotvertex
      rw [hpeq]
      simp [sub_eq_add_neg, add_assoc, W.w.2]

private theorem target9_no_cut_of_open_sides_and_opposite_germs
    {K : Region} {T : Set Tiling.Plane} {y l r : ℝ}
    (hTile : TilesOn K T univ)
    (S : HorizontalSeamCell K T y l r)
    {q : ℝ}
    (hpFirst : linePoint y q ∈ openSegment ℝ
      (S.a.1 + (S.upperCenter.1 : Tiling.Plane))
      (S.b.1 + (S.upperCenter.1 : Tiling.Plane)))
    (hpSecond : linePoint y q ∈ openSegment ℝ
      (S.a'.1 + (S.lowerCenter.1 : Tiling.Plane))
      (S.b'.1 + (S.lowerCenter.1 : Tiling.Plane)))
    (hupperGerm : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y + h) q ∈
        (S.upperCenter.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hlowerGerm : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y - h) q ∈
        (S.lowerCenter.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hcut : q ∈ horizontalLineCutSet K T y) : False := by
  obtain ⟨W⟩ := hcut
  by_cases hWupper : W.center = S.upperCenter
  · exact target9_cut_not_on_same_horizontal_side S.upperCenter S.a S.b
      S.first_horizontal hpFirst W hWupper
  by_cases hWlower : W.center = S.lowerCenter
  · exact target9_cut_not_on_same_horizontal_side S.lowerCenter S.a' S.b'
      S.second_horizontal hpSecond W hWlower
  have hWfront : linePoint y q ∈
      frontier ((W.center.1 : Tiling.Plane) +ᵥ K.support) := by
    have hopenSub : openSegment ℝ
        (W.v.1 + (W.center.1 : Tiling.Plane))
        (W.w.1 + (W.center.1 : Tiling.Plane)) ⊆
        frontier ((W.center.1 : Tiling.Plane) +ᵥ K.support) := by
      rw [show W.v.1 + (W.center.1 : Tiling.Plane) =
          (W.center.1 : Tiling.Plane) +ᵥ W.v.1 by simp [add_comm],
        show W.w.1 + (W.center.1 : Tiling.Plane) =
          (W.center.1 : Tiling.Plane) +ᵥ W.w.1 by simp [add_comm],
        ← vadd_openSegment ℝ, Tiling.AxisParallel.frontier_vadd_eq]
      intro z hz
      rw [mem_vadd_set] at hz
      obtain ⟨z₀, hz₀, rfl⟩ := hz
      exact ⟨z₀, (W.side.2.2 hz₀).1, rfl⟩
    exact isClosed_frontier.closure_subset_iff.mpr hopenSub
      (segment_subset_closure_openSegment (𝕜 := ℝ) W.line_meets_side)
  have hWclosure : linePoint y q ∈ closure
      ((W.center.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    rw [closure_vadd]
    change linePoint y q ∈
      (W.center.1 : Tiling.Plane) +ᵥ closure K.openCarrier
    rw [show closure K.openCarrier = K.support from by
      change closure (interior K.support) = K.support
      exact K.isPolygonal.closure_interior]
    rw [← (K.isPolygonal.isClosed.vadd (W.center.1 : Tiling.Plane)).closure_eq]
    exact frontier_subset_closure hWfront
  obtain ⟨deltaU, hdeltaU, hUniformU⟩ :=
    seam_placed_horizontal_side_local_uniform_germ S.upperCenter S.a S.b
      S.first_horizontal hpFirst
  have hU : ∀ z : ℝ, |z - q| < deltaU → ∀ h : ℝ, 0 < h → h < deltaU →
      linePoint (y + h) z ∈
        (S.upperCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rcases hUniformU with h | h
    · exact h
    · obtain ⟨epsilon, hepsilon, hupper⟩ := hupperGerm
      exact False.elim (seam_placed_horizontal_side_germs_disjoint
        S.upperCenter S.a S.b S.first_horizontal hpFirst
        ⟨epsilon, hepsilon, hupper⟩
        ⟨deltaU, hdeltaU, fun hh hpos hlt =>
          h q (by simpa using hdeltaU) hh hpos hlt⟩)
  obtain ⟨deltaL, hdeltaL, hUniformL⟩ :=
    seam_placed_horizontal_side_local_uniform_germ S.lowerCenter S.a' S.b'
      S.second_horizontal hpSecond
  have hL : ∀ z : ℝ, |z - q| < deltaL → ∀ h : ℝ, 0 < h → h < deltaL →
      linePoint (y - h) z ∈
        (S.lowerCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rcases hUniformL with h | h
    · obtain ⟨epsilon, _hepsilon, hlower⟩ := hlowerGerm
      exact False.elim (seam_placed_horizontal_side_germs_disjoint
        S.lowerCenter S.a' S.b' S.second_horizontal hpSecond
        ⟨deltaL, hdeltaL, fun hh hpos hlt =>
          h q (by simpa using hdeltaL) hh hpos hlt⟩
        ⟨epsilon, _hepsilon, hlower⟩)
    · exact h
  have hpoint (delta : ℝ) (hdelta : 0 < delta) :
      ∃ z' ∈ (W.center.1 : Tiling.Plane) +ᵥ K.openCarrier,
        |z'.re - q| < delta ∧
        ((0 < z'.im - y ∧ z'.im - y < delta) ∨
          (0 < y - z'.im ∧ y - z'.im < delta)) := by
    obtain ⟨z, hzW, hzdist⟩ := Metric.mem_closure_iff.mp hWclosure
      (delta / 4) (by linarith)
    have hn : ‖z - linePoint y q‖ < delta / 4 := by
      simpa [dist_eq_norm, norm_sub_rev] using hzdist
    have hzre : |z.re - q| < delta / 4 := by
      have hzre' : |(z - linePoint y q).re| < delta / 4 :=
        (Complex.abs_re_le_norm _).trans_lt hn
      simpa [linePoint] using hzre'
    have hzim : |z.im - y| < delta / 4 := by
      have hzim' : |(z - linePoint y q).im| < delta / 4 :=
        (Complex.abs_im_le_norm _).trans_lt hn
      simpa [linePoint] using hzim'
    by_cases hzline : z.im = y
    · obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp
        (isOpen_interior.vadd (W.center.1 : Tiling.Plane)) z hzW
      let h : ℝ := min (rho / 2) (delta / 4)
      have hh : 0 < h := by
        dsimp [h]
        positivity
      let z' : Tiling.Plane := z + (h : ℂ) * Complex.I
      have hz'dist : dist z' z < rho := by
        rw [dist_eq_norm]
        have heq : z' - z = (h : ℂ) * Complex.I := by simp [z']
        rw [heq, norm_mul, Complex.norm_I, mul_one,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
        exact (min_le_left _ _).trans_lt (half_lt_self hrho)
      have hz'W : z' ∈ (W.center.1 : Tiling.Plane) +ᵥ K.openCarrier :=
        hball (Metric.mem_ball.mpr hz'dist)
      refine ⟨z', hz'W, ?_, Or.inl ?_⟩
      · have hz'req : z'.re = z.re := by simp [z']
        change |z'.re - q| < delta
        rw [hz'req]
        linarith [hzre]
      · have hz'imq : z'.im - y = h := by
          simp [z', hzline]
        change 0 < z'.im - y ∧ z'.im - y < delta
        rw [hz'imq]
        exact ⟨hh, by dsimp [h]; linarith [min_le_right (rho / 2) (delta / 4)]⟩
    · rcases lt_or_gt_of_ne hzline with hzneg | hzpos
      · refine ⟨z, hzW, ?_, Or.inr ?_⟩
        · linarith [hzre]
        · have habs := (abs_lt.mp hzim)
          exact ⟨by linarith, by linarith⟩
      · refine ⟨z, hzW, ?_, Or.inl ?_⟩
        · linarith [hzre]
        · have habs := (abs_lt.mp hzim)
          exact ⟨by linarith, by linarith⟩
  obtain ⟨z', hz'W, hz're, hz'im⟩ := hpoint
    (min (deltaU / 4) (deltaL / 4)) (by positivity)
  rcases hz'im with hz'im | hz'im
  · have hz'reU : |z'.re - q| < deltaU := by
      have hmin : min (deltaU / 4) (deltaL / 4) ≤ deltaU / 4 := min_le_left _ _
      linarith
    have hz'hU : z'.im - y < deltaU := by
      have hmin : min (deltaU / 4) (deltaL / 4) ≤ deltaU / 4 := min_le_left _ _
      linarith
    have hz'open := hU z'.re hz'reU (z'.im - y) hz'im.1 hz'hU
    have hz'open' : z' ∈
        (S.upperCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
      convert hz'open using 1
      apply Complex.ext <;> simp [linePoint]
    exact Set.disjoint_left.mp
      ((isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        W.center.2 S.upperCenter.2 (by
          intro heq
          apply hWupper
          exact Subtype.ext heq)) hz'W hz'open'
  · have hz'reL : |z'.re - q| < deltaL := by
      have hmin : min (deltaU / 4) (deltaL / 4) ≤ deltaL / 4 := min_le_right _ _
      linarith
    have hz'hL : y - z'.im < deltaL := by
      have hmin : min (deltaU / 4) (deltaL / 4) ≤ deltaL / 4 := min_le_right _ _
      linarith
    have hz'open := hL z'.re hz'reL (y - z'.im) hz'im.1 hz'hL
    have hz'open' : z' ∈
        (S.lowerCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
      convert hz'open using 1
      apply Complex.ext <;> simp [linePoint]
    exact Set.disjoint_left.mp
      ((isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        W.center.2 S.lowerCenter.2 (by
          intro heq
          apply hWlower
          exact Subtype.ext heq)) hz'W hz'open'

private theorem target9_seam_no_cut_in_open_overlap
    {K : Region} {T : Set Tiling.Plane} {y l r : ℝ}
    (hTile : TilesOn K T univ)
    (S : HorizontalSeamCell K T y l r)
    {q : ℝ} (hq : q ∈ Ioo l r)
    (hcut : q ∈ horizontalLineCutSet K T y) : False := by
  obtain ⟨epsilon, hepsilon, hupper, hlower⟩ := S.opposite_germs q hq
  exact target9_no_cut_of_open_sides_and_opposite_germs hTile S
    (S.first_side q hq) (S.second_side q hq)
    ⟨epsilon, hepsilon, hupper⟩ ⟨epsilon, hepsilon, hlower⟩ hcut

private theorem target9_seam_no_cut_at_endpoint
    {K : Region} {T : Set Tiling.Plane} {y l r e : ℝ}
    (hTile : TilesOn K T univ)
    (S : HorizontalSeamCell K T y l r)
    (he : e = l ∨ e = r)
    (hpFirst : linePoint y e ∈ openSegment ℝ
      (S.a.1 + (S.upperCenter.1 : Tiling.Plane))
      (S.b.1 + (S.upperCenter.1 : Tiling.Plane)))
    (hpSecond : linePoint y e ∈ openSegment ℝ
      (S.a'.1 + (S.lowerCenter.1 : Tiling.Plane))
      (S.b'.1 + (S.lowerCenter.1 : Tiling.Plane)))
    (hcut : e ∈ horizontalLineCutSet K T y) : False := by
  obtain ⟨deltaU, hdeltaU, hUniformU⟩ :=
    seam_placed_horizontal_side_local_uniform_germ S.upperCenter S.a S.b
      S.first_horizontal hpFirst
  obtain ⟨deltaL, hdeltaL, hUniformL⟩ :=
    seam_placed_horizontal_side_local_uniform_germ S.lowerCenter S.a' S.b'
      S.second_horizontal hpSecond
  have hlr : l < r := S.left_lt_right
  let d : ℝ := min ((r - l) / 4) (min (deltaU / 4) (deltaL / 4))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdSpan : d ≤ (r - l) / 4 := min_le_left _ _
  have hdU : d ≤ deltaU / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdL : d ≤ deltaL / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let q0 : ℝ := if e = l then e + d else e - d
  have hq0Ioo : q0 ∈ Ioo l r := by
    rcases he with hel | her
    · have hq : q0 = e + d := by simp only [q0, if_pos hel]
      rw [hq, hel]
      constructor <;> linarith
    · have hne : ¬ e = l := by
        intro h
        linarith [hlr]
      have hq : q0 = e - d := by simp only [q0, if_neg hne]
      rw [hq, her]
      constructor <;> linarith
  have hq0distU : |q0 - e| < deltaU := by
    rcases he with hel | her
    · have hq : q0 = e + d := by simp only [q0, if_pos hel]
      rw [hq]
      have hqdiff : e + d - e = d := by ring
      rw [hqdiff, abs_of_pos hd]
      linarith
    · have hne : ¬ e = l := by
        intro h
        linarith [hlr]
      have hq : q0 = e - d := by simp only [q0, if_neg hne]
      rw [hq]
      have hqdiff : e - d - e = -d := by ring
      rw [hqdiff, abs_of_neg (neg_lt_zero.mpr hd)]
      linarith
  have hq0distL : |q0 - e| < deltaL := by
    rcases he with hel | her
    · have hq : q0 = e + d := by simp only [q0, if_pos hel]
      rw [hq]
      have hqdiff : e + d - e = d := by ring
      rw [hqdiff, abs_of_pos hd]
      linarith
    · have hne : ¬ e = l := by
        intro h
        linarith [hlr]
      have hq : q0 = e - d := by simp only [q0, if_neg hne]
      rw [hq]
      have hqdiff : e - d - e = -d := by ring
      rw [hqdiff, abs_of_neg (neg_lt_zero.mpr hd)]
      linarith
  have hpFirst0 := S.first_side q0 hq0Ioo
  have hpSecond0 := S.second_side q0 hq0Ioo
  obtain ⟨epsilon0, hepsilon0, hupper0, hlower0⟩ :=
    S.opposite_germs q0 hq0Ioo
  have hupperE : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y + h) e ∈
        (S.upperCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rcases hUniformU with hU | hU
    · exact ⟨deltaU, hdeltaU, fun h hh hhd =>
        hU e (by simpa using hdeltaU) h hh hhd⟩
    · exact False.elim (seam_placed_horizontal_side_germs_disjoint
        S.upperCenter S.a S.b S.first_horizontal hpFirst0
        ⟨epsilon0, hepsilon0, hupper0⟩
        ⟨deltaU, hdeltaU, fun h hh hhd => hU q0 hq0distU h hh hhd⟩)
  have hlowerE : ∃ epsilon > 0, ∀ h : ℝ, 0 < h → h < epsilon →
      linePoint (y - h) e ∈
        (S.lowerCenter.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    rcases hUniformL with hL | hL
    · exact False.elim (seam_placed_horizontal_side_germs_disjoint
        S.lowerCenter S.a' S.b' S.second_horizontal hpSecond0
        ⟨deltaL, hdeltaL, fun h hh hhd => hL q0 hq0distL h hh hhd⟩
        ⟨epsilon0, hepsilon0, hlower0⟩)
    · exact ⟨deltaL, hdeltaL, fun h hh hhd =>
        hL e (by simpa using hdeltaL) h hh hhd⟩
  exact target9_no_cut_of_open_sides_and_opposite_germs hTile S
    hpFirst hpSecond hupperE hlowerE hcut

private theorem target9_lineEndpoints_mem_segment_of_openSegment_on_Ioo
    {y l r : ℝ} (hlr : l < r) {u v : Tiling.Plane}
    (hall : ∀ x ∈ Ioo l r, linePoint y x ∈ openSegment ℝ u v) :
    linePoint y l ∈ segment ℝ u v ∧ linePoint y r ∈ segment ℝ u v := by
  have hcontinuous : Continuous (linePoint y) := by
    change Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I)
    fun_prop
  have himage : linePoint y '' Ioo l r ⊆ openSegment ℝ u v := by
    rintro _ ⟨x, hx, rfl⟩
    exact hall x hx
  have hclosure : closure (linePoint y '' Ioo l r) ⊆ segment ℝ u v := by
    rw [← closure_openSegment u v]
    exact closure_mono himage
  have hl : l ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact ⟨le_rfl, hlr.le⟩
  have hr : r ∈ closure (Ioo l r) := by
    rw [closure_Ioo hlr.ne]
    exact ⟨hlr.le, le_rfl⟩
  exact ⟨hclosure (hcontinuous.continuousAt.continuousWithinAt.mem_closure_image hl),
    hclosure (hcontinuous.continuousAt.continuousWithinAt.mem_closure_image hr)⟩

private theorem target9_eq_one_of_four_endpoints_of_two_segments
    {p u v u' v' : Tiling.Plane}
    (hfirst : p ∈ segment ℝ u v) (hsecond : p ∈ segment ℝ u' v')
    (hnotBoth : ¬ (p ∈ openSegment ℝ u v ∧ p ∈ openSegment ℝ u' v')) :
    p = u ∨ p = v ∨ p = u' ∨ p = v' := by
  have hfirst' : p = u ∨ p = v ∨ p ∈ openSegment ℝ u v := by
    rw [← insert_endpoints_openSegment] at hfirst
    simpa only [mem_insert_iff] using hfirst
  have hsecond' : p = u' ∨ p = v' ∨ p ∈ openSegment ℝ u' v' := by
    rw [← insert_endpoints_openSegment] at hsecond
    simpa only [mem_insert_iff] using hsecond
  rcases hfirst' with hpu | hpv | hpOpen
  · exact Or.inl hpu
  · exact Or.inr (Or.inl hpv)
  · rcases hsecond' with hpu' | hpv' | hpOpen'
    · exact Or.inr (Or.inr (Or.inl hpu'))
    · exact Or.inr (Or.inr (Or.inr hpv'))
    · exact False.elim (hnotBoth ⟨hpOpen, hpOpen'⟩)

private theorem target9_seam_endpoint_among_four
    {K : Region} {T : Set Tiling.Plane} {y l r e : ℝ}
    (hTile : TilesOn K T univ)
    (S : HorizontalSeamCell K T y l r)
    (he : e = l ∨ e = r)
    (hcut : e ∈ horizontalLineCutSet K T y) :
    linePoint y e = S.a.1 + (S.upperCenter.1 : Tiling.Plane) ∨
      linePoint y e = S.b.1 + (S.upperCenter.1 : Tiling.Plane) ∨
      linePoint y e = S.a'.1 + (S.lowerCenter.1 : Tiling.Plane) ∨
      linePoint y e = S.b'.1 + (S.lowerCenter.1 : Tiling.Plane) := by
  have hfirstEnds := target9_lineEndpoints_mem_segment_of_openSegment_on_Ioo
    S.left_lt_right S.first_side
  have hsecondEnds := target9_lineEndpoints_mem_segment_of_openSegment_on_Ioo
    S.left_lt_right S.second_side
  have hfirst : linePoint y e ∈ segment ℝ
      (S.a.1 + (S.upperCenter.1 : Tiling.Plane))
      (S.b.1 + (S.upperCenter.1 : Tiling.Plane)) := by
    rcases he with rfl | rfl
    · exact hfirstEnds.1
    · exact hfirstEnds.2
  have hsecond : linePoint y e ∈ segment ℝ
      (S.a'.1 + (S.lowerCenter.1 : Tiling.Plane))
      (S.b'.1 + (S.lowerCenter.1 : Tiling.Plane)) := by
    rcases he with rfl | rfl
    · exact hsecondEnds.1
    · exact hsecondEnds.2
  apply target9_eq_one_of_four_endpoints_of_two_segments hfirst hsecond
  rintro ⟨hpFirst, hpSecond⟩
  exact target9_seam_no_cut_at_endpoint hTile S he hpFirst hpSecond hcut

private theorem endpointAlignedLineCode_exists :
    (∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ → ∀ y A B : ℝ, A ≤ B →
      Nonempty (EndpointAlignedLineCode K T y A B)) :=
  endpointAlignedLineCode_exists_of_classification horizontalLineCell_classification

private theorem lt_iff_of_sign_sub_eq {a b A B : ℝ}
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

private theorem mapped_endpoint_difference
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (v w : C.region.vertices) (s t : C.centres)
    (hz : (w.1 + (t : Tiling.Plane)).re -
      (v.1 + (s : Tiling.Plane)).re ∈ C.coordinateSpace) :
    (mapPoint phi (C.vertexPoint w.1 w.2) +
        mapPoint phi (C.centrePoint t.1 t.2)).re -
      (mapPoint phi (C.vertexPoint v.1 v.2) +
        mapPoint phi (C.centrePoint s.1 s.2)).re =
      mapScalar phi ⟨(w.1 + (t : Tiling.Plane)).re -
        (v.1 + (s : Tiling.Plane)).re, hz⟩ := by
  have hcoord :
      (⟨(w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re, hz⟩ : C.coordinateSpace) =
        (⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ : C.coordinateSpace) +
          ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ -
          ((⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ : C.coordinateSpace) +
            ⟨s.1.re, C.centre_re_mem s.1 s.2⟩) := by
    apply Subtype.ext
    simp only [Complex.add_re, Submodule.coe_add, Submodule.coe_sub]
  rw [hcoord]
  simp only [mapPoint, mapScalar, map_sub, map_add, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, add_zero]
  simp [ApproximationContext.vertexPoint, ApproximationContext.centrePoint]

private theorem target9_re_mem_uIcc_of_mem_segment_horizontal
    {u v z : Tiling.Plane} (hz : z ∈ segment ℝ u v) :
    z.re ∈ uIcc u.re v.re := by
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨θ, hθ, rfl⟩
  simp only [AffineMap.lineMap_apply_module, Complex.add_re,
    Complex.smul_re, smul_eq_mul]
  rw [Set.mem_uIcc]
  rcases le_total u.re v.re with huv | hvu
  · exact Or.inl ⟨by
      nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr huv)], by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr huv)]⟩
  · exact Or.inr ⟨by
      nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hvu)], by
      nlinarith [mul_nonneg hθ.1 (sub_nonneg.mpr hvu)]⟩

private theorem properOverlap_contactDisplacement
    {C : ApproximationContext.{0}}
    {s t : ↥C.centres} {a b a' b' : ↥C.region.vertices}
    (hside : IsIntrinsicHorizontalSide C.region a b)
    (hside' : IsIntrinsicHorizontalSide C.region a' b')
    (hOverlap : ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1) :
    (t.1 - s.1).re ∈ horizontalContactDisplacements
      C.region C.centres a b a' b' := by
  rcases hOverlap with ⟨u, v, huv, huvIm, huvSeg⟩
  apply (horizontalContactDisplacements_iff C.region C.centres a b a' b'
    ((t.1 - s.1).re)).2
  refine ⟨hside.1, hside.2.1, hside.2.2,
    hside'.1, hside'.2.1, hside'.2.2, ?_⟩
  refine ⟨s, t, ?_, u, v, huv, huvIm, huvSeg⟩
  rfl

private theorem endpointDifference_mem_contactCriticalScalars
    {C : ApproximationContext.{0}}
    {a b a' b' : ↥C.region.vertices} {delta r q : ℝ}
    (hdelta : delta ∈ horizontalContactDisplacements
      C.region C.centres a b a' b')
    (hr : r ∈ ({a.1.re, b.1.re, a'.1.re + delta,
      b'.1.re + delta} : Set ℝ))
    (hq : q ∈ ({a.1.re, b.1.re, a'.1.re + delta,
      b'.1.re + delta} : Set ℝ))
    (hne : r ≠ q) : r - q ∈ contactCriticalScalars C := by
  exact ⟨a, b, a', b', delta, hdelta, sub_ne_zero.mpr hne,
    Or.inr ⟨r, hr, q, hq, rfl⟩⟩

private theorem target9_endpointSign
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (A : FiniteTransportCriticalAlphabet C)
    (hsign : ∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (A.lift x)) = Real.sign x.1)
    {a b a' b' : ↥C.region.vertices}
    {delta : ℝ}
    (hdelta : delta ∈ horizontalContactDisplacements
      C.region C.centres a b a' b')
    (v w : C.region.vertices) (p q : C.centres)
    (r₀ q₀ : ℝ)
    (hr : r₀ ∈ ({a.1.re, b.1.re, a'.1.re + delta,
      b'.1.re + delta} : Set ℝ))
    (hq : q₀ ∈ ({a.1.re, b.1.re, a'.1.re + delta,
      b'.1.re + delta} : Set ℝ))
    (heq : r₀ - q₀ =
      (w.1 + (p : Tiling.Plane)).re -
        (v.1 + (q : Tiling.Plane)).re) :
    Real.sign ((w.1 + (p : Tiling.Plane)).re -
        (v.1 + (q : Tiling.Plane)).re) =
      Real.sign ((mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint p.1 p.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint q.1 q.2)).re) := by
  let x := (w.1 + (p : Tiling.Plane)).re -
    (v.1 + (q : Tiling.Plane)).re
  have hxmem : x ∈ C.coordinateSpace := by
    exact C.coordinateSpace.sub_mem
      (C.coordinateSpace.add_mem (C.vertex_re_mem w.1 w.2)
        (C.centre_re_mem p.1 p.2))
      (C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
        (C.centre_re_mem q.1 q.2))
  change Real.sign x = _
  have heqx : r₀ - q₀ = x := by
    simpa [x] using heq
  have hm' :
      (mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint p.1 p.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint q.1 q.2)).re =
      mapScalar phi (⟨x, hxmem⟩ : C.coordinateSpace) := by
    simpa [x] using mapped_endpoint_difference C phi v w q p hxmem
  by_cases hx : x = 0
  · have hx0 : (⟨x, hxmem⟩ : C.coordinateSpace) = 0 := Subtype.ext hx
    rw [hm', hx0]
    change Real.sign x = Real.sign (phi 0)
    rw [map_zero, hx, Real.sign_zero]
    norm_num
  · have hcrit : r₀ - q₀ ∈ contactCriticalScalars C := by
      apply endpointDifference_mem_contactCriticalScalars hdelta hr hq
      intro h
      apply hx
      rw [← heqx, h, sub_self]
    have htransport : r₀ - q₀ ∈ transportCriticalScalars C := by
      change r₀ - q₀ ∈ contactCriticalScalars C ∪ _
      exact Or.inl hcrit
    have hlift : A.lift ⟨r₀ - q₀, htransport⟩ =
        (⟨x, hxmem⟩ : C.coordinateSpace) := by
      apply Subtype.ext
      simpa [heqx, x] using A.lift_coe ⟨r₀ - q₀, htransport⟩
    have hsx : Real.sign (mapScalar phi
        (⟨x, hxmem⟩ : C.coordinateSpace)) = Real.sign x := by
      rw [← hlift]
      exact (hsign ⟨r₀ - q₀, htransport⟩).trans
        (congrArg Real.sign heqx)
    rw [hm']
    exact hsx.symm

private theorem target9_horizontalSeamCell_gap_mem_transportCriticalScalars
    {C : ApproximationContext.{0}} {y l r : ℝ}
    (hTile : TilesOn C.region C.centres univ)
    (S : HorizontalSeamCell C.region C.centres y l r)
    (hlcut : l ∈ horizontalLineCutSet C.region C.centres y)
    (hrcut : r ∈ horizontalLineCutSet C.region C.centres y) :
    r - l ∈ transportCriticalScalars C := by
  let delta : ℝ := (S.lowerCenter.1 - S.upperCenter.1).re
  let E : Set ℝ := {S.a.1.re, S.b.1.re, S.a'.1.re + delta,
    S.b'.1.re + delta}
  have hleftFour := target9_seam_endpoint_among_four hTile S (Or.inl rfl) hlcut
  have hrightFour := target9_seam_endpoint_among_four hTile S (Or.inr rfl) hrcut
  have endpointNorm {e : ℝ}
      (hfour : linePoint y e = S.a.1 + (S.upperCenter.1 : Tiling.Plane) ∨
        linePoint y e = S.b.1 + (S.upperCenter.1 : Tiling.Plane) ∨
        linePoint y e = S.a'.1 + (S.lowerCenter.1 : Tiling.Plane) ∨
        linePoint y e = S.b'.1 + (S.lowerCenter.1 : Tiling.Plane)) :
      e - S.upperCenter.1.re ∈ E := by
    change e - S.upperCenter.1.re = S.a.1.re ∨
      e - S.upperCenter.1.re = S.b.1.re ∨
      e - S.upperCenter.1.re = S.a'.1.re + delta ∨
      e - S.upperCenter.1.re = S.b'.1.re + delta
    rcases hfour with h | h | h | h
    · apply Or.inl
      have hre : e = S.a.1.re + S.upperCenter.1.re := by
        simpa [linePoint] using congrArg Complex.re h
      linarith
    · apply Or.inr; apply Or.inl
      have hre : e = S.b.1.re + S.upperCenter.1.re := by
        simpa [linePoint] using congrArg Complex.re h
      linarith
    · apply Or.inr; apply Or.inr; apply Or.inl
      have hre : e = S.a'.1.re + S.lowerCenter.1.re := by
        simpa [linePoint] using congrArg Complex.re h
      dsimp only [delta]
      simp only [Complex.sub_re]
      linarith
    · apply Or.inr; apply Or.inr; apply Or.inr
      have hre : e = S.b'.1.re + S.lowerCenter.1.re := by
        simpa [linePoint] using congrArg Complex.re h
      dsimp only [delta]
      simp only [Complex.sub_re]
      linarith
  have hlNorm : l - S.upperCenter.1.re ∈ E := endpointNorm hleftFour
  have hrNorm : r - S.upperCenter.1.re ∈ E := endpointNorm hrightFour
  let q₀ : ℝ := (2 * l + r) / 3
  let q₁ : ℝ := (l + 2 * r) / 3
  have hq₀ : q₀ ∈ Ioo l r := by
    dsimp [q₀]
    constructor <;> linarith [S.left_lt_right]
  have hq₁ : q₁ ∈ Ioo l r := by
    dsimp [q₁]
    constructor <;> linarith [S.left_lt_right]
  have hq₀q₁ : q₀ < q₁ := by
    dsimp [q₀, q₁]
    linarith [S.left_lt_right]
  have hOverlap : ProperOpenSideOverlap S.a.1 S.b.1 S.a'.1 S.b'.1
      S.upperCenter.1 S.lowerCenter.1 := by
    refine ⟨linePoint y q₀, linePoint y q₁, ?_, by simp [linePoint], ?_⟩
    · intro h
      have hre := congrArg Complex.re h
      simp [linePoint] at hre
      linarith
    · intro z hz
      exact ⟨(convex_openSegment _ _).openSegment_subset
          (S.first_side q₀ hq₀) (S.first_side q₁ hq₁) hz,
        (convex_openSegment _ _).openSegment_subset
          (S.second_side q₀ hq₀) (S.second_side q₁ hq₁) hz⟩
  have hdelta : delta ∈ horizontalContactDisplacements C.region C.centres
      S.a S.b S.a' S.b' := by
    simpa only [delta] using properOverlap_contactDisplacement
      S.first_horizontal S.second_horizontal hOverlap
  have hcritical :
      (r - S.upperCenter.1.re) - (l - S.upperCenter.1.re) ∈
        contactCriticalScalars C := by
    apply endpointDifference_mem_contactCriticalScalars hdelta hrNorm hlNorm
    linarith [S.left_lt_right]
  apply Or.inl
  convert hcritical using 1
  ring

private theorem target9_strictMono_finset_of_adjacent
    {s : Finset ℝ} (f : ↑s → ℝ)
    (hadj : ∀ l r : ↑s, l.1 < r.1 →
      Ioo l.1 r.1 ∩ (s : Set ℝ) = ∅ → f l < f r) :
    StrictMono f := by
  by_cases hs : s.card = 0
  · intro l
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨l.1, l.2⟩
    omega
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hs
  let e : Fin (n + 1) ≃o ↑s := s.orderIsoOfFin hn
  have hordered : StrictMono (fun i : Fin (n + 1) ↦ f (e i)) := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    apply hadj
    · exact e.strictMono Fin.castSucc_lt_succ
    · apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, ⟨⟨hzl, hzr⟩, hzs⟩⟩
      let q : ↑s := ⟨z, hzs⟩
      change e i.castSucc < q at hzl
      change q < e i.succ at hzr
      have hil : i.castSucc < e.symm q := by
        simpa only [OrderIso.symm_apply_apply] using e.symm.strictMono hzl
      have hir : e.symm q < i.succ := by
        simpa only [OrderIso.symm_apply_apply] using e.symm.strictMono hzr
      change i.1 < (e.symm q).1 at hil
      change (e.symm q).1 < i.1 + 1 at hir
      omega
  intro l r hlr
  have hij : e.symm l < e.symm r := e.symm.strictMono hlr
  simpa only [OrderIso.apply_symm_apply] using hordered hij

private theorem target9_mapped_cells_cover_generic
    (cuts : Finset ℝ) (qLeft qRight : ℝ)
    (hqLeft : qLeft ∈ cuts) (hqRight : qRight ∈ cuts)
    (mapped : ↑cuts → ℝ) (hmono : StrictMono mapped)
    {x : ℝ} (hx : x ∈ Ioo (mapped ⟨qLeft, hqLeft⟩)
      (mapped ⟨qRight, hqRight⟩))
    (hxrange : x ∉ Set.range mapped) :
    ∃ l r : ↑cuts, l.1 < r.1 ∧
      Ioo l.1 r.1 ∩ (cuts : Set ℝ) = ∅ ∧
      x ∈ Ioo (mapped l) (mapped r) := by
  let belowQ := cuts.attach.filter (fun q ↦ mapped q < x)
  let aboveQ := cuts.attach.filter (fun q ↦ x < mapped q)
  let below : Finset ℝ := belowQ.image mapped
  let above : Finset ℝ := aboveQ.image mapped
  have hbelow : below.Nonempty := by
    refine ⟨mapped ⟨qLeft, hqLeft⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨qLeft, hqLeft⟩, by simp [belowQ, hx.1]⟩
  have habove : above.Nonempty := by
    refine ⟨mapped ⟨qRight, hqRight⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨qRight, hqRight⟩, by simp [aboveQ, hx.2]⟩
  let ml := below.max' hbelow
  let mr := above.min' habove
  obtain ⟨l, hlbelow, hlmap⟩ := Finset.mem_image.mp
    (show ml ∈ below from Finset.max'_mem below hbelow)
  obtain ⟨r, hra, hrmap⟩ := Finset.mem_image.mp
    (show mr ∈ above from Finset.min'_mem above habove)
  have hxl : mapped l < x := (Finset.mem_filter.mp hlbelow).2
  have hxr : x < mapped r := (Finset.mem_filter.mp hra).2
  have hlrmap : mapped l < mapped r := by
    simpa [hlmap, hrmap, ml, mr] using lt_trans hxl hxr
  have hlr : l.1 < r.1 := by
    by_contra hn
    have hle : r.1 ≤ l.1 := le_of_not_gt hn
    exact (not_lt_of_ge (hmono.monotone hle)) hlrmap
  have hno : Ioo l.1 r.1 ∩ (cuts : Set ℝ) = ∅ := by
    ext z
    constructor
    · rintro ⟨hz, hzcuts⟩
      let q : ↑cuts := ⟨z, hzcuts⟩
      by_cases hzx : mapped q < x
      · have hqbelow : q ∈ belowQ := by simp [belowQ, hzx]
        have hle : mapped q ≤ mapped l := by
          have hqimage : mapped q ∈ below :=
            Finset.mem_image.mpr ⟨q, hqbelow, rfl⟩
          have hmax : mapped q ≤ ml := Finset.le_max' below (mapped q) hqimage
          simpa [ml, hlmap] using hmax
        exact (not_lt_of_ge (hmono.le_iff_le.mp hle)) hz.1
      · have hqx : x < mapped q :=
          lt_of_le_of_ne (le_of_not_gt hzx)
            (by intro heq; exact hxrange ⟨q, heq.symm⟩)
        have hqabove : q ∈ aboveQ := by simp [aboveQ, hqx]
        have hle : mapped r ≤ mapped q := by
          have hqimage : mapped q ∈ above :=
            Finset.mem_image.mpr ⟨q, hqabove, rfl⟩
          have hmin : mr ≤ mapped q := Finset.min'_le above (mapped q) hqimage
          simpa [mr, hrmap] using hmin
        exact (not_lt_of_ge (hmono.le_iff_le.mp hle)) hz.2
    · simp
  exact ⟨l, r, hlr, hno, hxl, hxr⟩

private theorem target9_cut_coordinate_mem
    {C : ApproximationContext.{0}}
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (q : ↥code.cuts) : q.1 ∈ C.coordinateSpace := by
  obtain ⟨W⟩ := code.cut_controlled q.1 q.2
  rcases W.x_coordinate with h | h
  · rw [h]
    exact C.coordinateSpace.add_mem
      (C.vertex_re_mem W.v.1 W.v.2) (C.centre_re_mem W.center.1 W.center.2)
  · rw [h]
    exact C.coordinateSpace.add_mem
      (C.vertex_re_mem W.w.1 W.w.2) (C.centre_re_mem W.center.1 W.center.2)

private noncomputable def target9_cutLift
    {C : ApproximationContext.{0}}
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B) :
    ↥code.cuts → C.coordinateSpace :=
  fun q ↦ ⟨q.1, target9_cut_coordinate_mem code q⟩

private theorem target9_cutLift_coe
    {C : ApproximationContext.{0}}
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (q : ↥code.cuts) : (target9_cutLift code q : ℝ) = q.1 := by
  rfl

private theorem target9_mapScalar_lt_of_sub_mem
    {C : ApproximationContext.{0}}
    (Acrit : FiniteTransportCriticalAlphabet C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hsign : ∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1)
    {x y : C.coordinateSpace} (hxy : (x : ℝ) < (y : ℝ))
    (hgap : (y : ℝ) - (x : ℝ) ∈ transportCriticalScalars C) :
    mapScalar phi x < mapScalar phi y := by
  have hcoord :
      (⟨(y : ℝ) - (x : ℝ), transportScalar_mem_coordinateSpace hgap⟩ :
        C.coordinateSpace) = y - x := by
    apply Subtype.ext
    simp only [Submodule.coe_sub]
  have hmap :
      mapScalar phi
          (⟨(y : ℝ) - (x : ℝ), transportScalar_mem_coordinateSpace hgap⟩) =
        mapScalar phi y - mapScalar phi x := by
    rw [hcoord]
    change (phi (y - x) : ℝ) = (phi y : ℝ) - (phi x : ℝ)
    rw [map_sub]
    simp only [Rat.cast_sub]
  have hsource : Real.sign ((y : ℝ) - (x : ℝ)) = 1 :=
    Real.sign_of_pos (sub_pos.mpr hxy)
  have hsign' : Real.sign
      (mapScalar phi (⟨(y : ℝ) - (x : ℝ),
        transportScalar_mem_coordinateSpace hgap⟩ : C.coordinateSpace)) =
      Real.sign ((y : ℝ) - (x : ℝ)) := by
    have hlift : Acrit.lift ⟨(y : ℝ) - (x : ℝ), hgap⟩ =
        (⟨(y : ℝ) - (x : ℝ), transportScalar_mem_coordinateSpace hgap⟩ :
          C.coordinateSpace) := by
      apply Subtype.ext
      simpa using Acrit.lift_coe ⟨(y : ℝ) - (x : ℝ), hgap⟩
    rw [← hlift]
    exact hsign ⟨(y : ℝ) - (x : ℝ), hgap⟩
  have htarget : Real.sign (mapScalar phi y - mapScalar phi x) = 1 := by
    rw [← hmap]
    exact hsign'.trans hsource
  by_contra hnot
  have hle : mapScalar phi y - mapScalar phi x ≤ 0 := by
    apply le_of_not_gt
    intro hpos
    exact hnot (sub_pos.mp hpos)
  rcases hle.eq_or_lt with hzero | hneg
  · rw [hzero, Real.sign_zero] at htarget
    norm_num at htarget
  · rw [Real.sign_of_neg hneg] at htarget
    norm_num at htarget

private theorem target9_mappedCut_lt_of_gap_mem
    {C : ApproximationContext.{0}}
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (Acrit : FiniteTransportCriticalAlphabet C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hsign : ∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1)
    {q r : ↥code.cuts} (hqr : q.1 < r.1)
    (hgap : r.1 - q.1 ∈ transportCriticalScalars C) :
    mapScalar phi (target9_cutLift code q) <
      mapScalar phi (target9_cutLift code r) := by
  apply target9_mapScalar_lt_of_sub_mem Acrit phi hsign
  · simpa only [target9_cutLift_coe] using hqr
  · simpa only [target9_cutLift_coe] using hgap

private theorem target9_crossing_gap_mem_transportCriticalScalars
    {C : ApproximationContext.{0}} {y l r : ℝ}
    (X : HorizontalCrossingCell C.region C.centres y l r) :
    r - l ∈ transportCriticalScalars C := by
  apply Or.inr
  apply (C.region.mem_horizontalStepAlphabet_iff _).2
  refine ⟨X.leftBottom.1, X.leftBottom.2,
    X.rightBottom.1, X.rightBottom.2, ?_, sub_pos.mpr X.left_lt_right⟩
  have hleft := X.left_coordinate
  have hright := X.right_coordinate
  simp only [Complex.add_re] at hleft hright
  linarith

private theorem target9_adjacent_gap_mem_transportCriticalScalars
    {C : ApproximationContext.{0}}
    (hTile : TilesOn C.region C.centres univ)
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (l r : ↥code.cuts) (hlr : l.1 < r.1)
    (hno : Ioo l.1 r.1 ∩ (code.cuts : Set ℝ) = ∅) :
    r.1 - l.1 ∈ transportCriticalScalars C := by
  rcases code.cell_classification l.1 r.1 l.2 r.2 hlr hno with hX | hS
  · obtain ⟨X⟩ := hX
    exact target9_crossing_gap_mem_transportCriticalScalars X
  · obtain ⟨S⟩ := hS
    exact target9_horizontalSeamCell_gap_mem_transportCriticalScalars hTile S
      (code.cut_controlled l.1 l.2) (code.cut_controlled r.1 r.2)

private theorem target9_mappedCut_strictMono
    {C : ApproximationContext.{0}}
    (hTile : TilesOn C.region C.centres univ)
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (Acrit : FiniteTransportCriticalAlphabet C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hsign : ∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1) :
    StrictMono (fun q ↦ mapScalar phi (target9_cutLift code q)) := by
  apply target9_strictMono_finset_of_adjacent
  intro l r hlr hno
  exact target9_mappedCut_lt_of_gap_mem code Acrit phi hsign hlr
    (target9_adjacent_gap_mem_transportCriticalScalars hTile code l r hlr hno)

private theorem target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).re) :
    mapScalar phi xLift = D.firstHomeomorph v.re +
      (mapFirstPoint phi (C.centrePoint t.1 t.2)).re := by
  let vr : C.coordinateSpace := ⟨v.re, C.vertex_re_mem v hv⟩
  let tr : C.coordinateSpace := ⟨t.1.re, C.centre_re_mem t.1 t.2⟩
  have hxl : xLift = vr + tr := by
    apply Subtype.ext
    simp [vr, tr, hLift, hx]
  have hvertex := congrArg Complex.re (D.first_vertex_agreement v hv)
  have hvertex' : mapScalar phi vr = D.firstHomeomorph v.re := by
    simpa [vr, mapFirstPoint, ApproximationContext.vertexPoint,
      D.firstPlanarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((phi vr : ℚ) : ℝ) = mapScalar phi vr by rfl, hvertex']
  congr 1
  simp [tr, mapFirstPoint, mapScalar, ApproximationContext.centrePoint]

private theorem target9_firstSliceGap_transport
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) {q x₀ x₁ : ℝ}
    (xLift₀ xLift₁ : C.coordinateSpace) (t : ↥C.centres)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hlift₀ : (xLift₀ : ℝ) = x₀) (hlift₁ : (xLift₁ : ℝ) = x₁)
    (hleft : x₀ = (v + (t : Tiling.Plane)).re)
    (hright : x₁ = (w + (t : Tiling.Plane)).re)
    (hinside : axisInterval Axis.horizontal q x₀ x₁ ⊆
      (t : Tiling.Plane) +ᵥ C.region.openCarrier) :
    axisInterval Axis.horizontal q (mapScalar phi xLift₀)
        (mapScalar phi xLift₁) ⊆
      mapFirstPoint phi (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier := by
  intro z hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [D.firstRegion_openCarrier]
  let c := mapFirstPoint phi (C.centrePoint t.1 t.2)
  let r : ℝ := D.firstHomeomorph.symm (z.re - c.re)
  let p : Tiling.Plane := (r : ℂ) + ((q - t.1.im : ℝ) : ℂ) * Complex.I
  have hend₀ := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
    D v hv t x₀ xLift₀ hlift₀ hleft
  have hend₁ := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
    D w hw t x₁ xLift₁ hlift₁ hright
  have hzre : z.re ∈ Ioo (mapScalar phi xLift₀) (mapScalar phi xLift₁) := hz.2
  have hvr : v.re < r := by
    apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzre.1]
  have hrw : r < w.re := by
    apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzre.2]
  have hp : p ∈ C.region.openCarrier := by
    have hs : (t : Tiling.Plane) + p ∈ axisInterval Axis.horizontal q x₀ x₁ := by
      constructor
      · simp [p]
      · rw [hleft, hright]
        simp only [p, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
          Complex.ofReal_im]
        exact ⟨by linarith, by linarith⟩
    have hinside' := hinside hs
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left] using hinside'
  refine ⟨p, hp, ?_⟩
  rw [D.firstPlanarHomeomorph_apply]
  apply Complex.ext
  · simp [p, r, c]
    ring
  · have hzq : z.im = q := hz.1
    simp [p, mapFirstPoint, ApproximationContext.centrePoint, hzq]
    ring

private theorem target9_crossing_preserved_of_cut_data
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B)
    (cutLift : ↥code.cuts → C.coordinateSpace)
    (mappedCut : ↥code.cuts → ℝ)
    (hcut : ∀ q, (cutLift q : ℝ) = q.1)
    (hmapped : ∀ q, mappedCut q = mapScalar phi (cutLift q))
    (l r : ↥code.cuts) (_hlr : l.1 < r.1)
    (X : HorizontalCrossingCell C.region C.centres y l.1 r.1)
    {z : ℝ} (hz : z ∈ Ioo (mappedCut l) (mappedCut r)) :
    linePoint y z ∈
      P.firstCenters X.center +ᵥ D.firstRegion.openCarrier := by
  have hinside : axisInterval Axis.horizontal y l.1 r.1 ⊆
      (X.center.1 : Tiling.Plane) +ᵥ C.region.openCarrier := by
    intro w hw
    change w.im = y ∧ w.re ∈ Ioo l.1 r.1 at hw
    have hwline : linePoint y w.re = w := by
      apply Complex.ext <;> simp [linePoint, hw.1]
    simpa [hwline] using X.crossing w.re hw.2
  have htransport := target9_firstSliceGap_transport D (cutLift l)
    (cutLift r) X.center X.leftBottom.1 X.rightBottom.1
    X.leftBottom.2 X.rightBottom.2 (hcut l) (hcut r)
    X.left_coordinate X.right_coordinate hinside
  have hz' : linePoint y z ∈ axisInterval Axis.horizontal y
      (mapScalar phi (cutLift l)) (mapScalar phi (cutLift r)) := by
    change (linePoint y z).im = y ∧
      (linePoint y z).re ∈ Ioo (mapScalar phi (cutLift l))
        (mapScalar phi (cutLift r))
    exact ⟨by simp [linePoint], by simpa [linePoint, hmapped] using hz⟩
  simpa only [P.firstCenters_apply] using htransport hz'

private theorem firstStage_labelledHorizontalOverlap_preserved :
    (∀ (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (A : FiniteTransportCriticalAlphabet C),
    (∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (A.lift x)) = Real.sign x.1) →
    ∀ (s t : ↥C.centres) (a b a' b' : ↥C.region.vertices),
      IsIntrinsicHorizontalSide C.region a b →
      IsIntrinsicHorizontalSide C.region a' b' →
      ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1 →
        ProperOpenSideOverlap
          (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
          (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
          (P.fullCenters s) (P.fullCenters t)) := by
  intro C phi D P A hsign s t a b a' b' hside hside' hOverlap
  have hdelta : (t.1 - s.1).re ∈
      horizontalContactDisplacements C.region C.centres a b a' b' :=
    properOverlap_contactDisplacement hside hside' hOverlap
  let E : Set ℝ := {a.1.re, b.1.re, a'.1.re + (t.1 - s.1).re,
    b'.1.re + (t.1 - s.1).re}
  have endpointSign
      (v w : C.region.vertices) (p q : C.centres)
      (r₀ q₀ : ℝ) (hr : r₀ ∈ E) (hq : q₀ ∈ E)
      (heq : r₀ - q₀ =
        (w.1 + (p : Tiling.Plane)).re -
          (v.1 + (q : Tiling.Plane)).re) :
      Real.sign ((w.1 + (p : Tiling.Plane)).re -
        (v.1 + (q : Tiling.Plane)).re) =
      Real.sign ((mapPoint phi (C.vertexPoint w.1 w.2) +
          mapPoint phi (C.centrePoint p.1 p.2)).re -
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint q.1 q.2)).re) := by
    let x := (w.1 + (p : Tiling.Plane)).re -
      (v.1 + (q : Tiling.Plane)).re
    have hxmem : x ∈ C.coordinateSpace := by
      exact C.coordinateSpace.sub_mem
        (C.coordinateSpace.add_mem (C.vertex_re_mem w.1 w.2)
          (C.centre_re_mem p.1 p.2))
        (C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem q.1 q.2))
    change Real.sign x = _
    have heqx : r₀ - q₀ = x := by
      simpa [x] using heq
    have hm' :
        (mapPoint phi (C.vertexPoint w.1 w.2) +
            mapPoint phi (C.centrePoint p.1 p.2)).re -
          (mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint q.1 q.2)).re =
        mapScalar phi (⟨x, hxmem⟩ : C.coordinateSpace) := by
      simpa [x] using mapped_endpoint_difference C phi v w q p hxmem
    by_cases hx : x = 0
    · have hx0 : (⟨x, hxmem⟩ : C.coordinateSpace) = 0 := Subtype.ext hx
      rw [hm', hx0]
      change Real.sign x = Real.sign (phi 0)
      rw [map_zero, hx, Real.sign_zero]
      norm_num
    · have hcrit : r₀ - q₀ ∈ contactCriticalScalars C := by
        apply endpointDifference_mem_contactCriticalScalars hdelta hr hq
        intro h
        apply hx
        rw [← heqx, h, sub_self]
      have htransport : r₀ - q₀ ∈ transportCriticalScalars C := by
        change r₀ - q₀ ∈ contactCriticalScalars C ∪ _
        exact Or.inl hcrit
      have hlift : A.lift ⟨r₀ - q₀, htransport⟩ =
          (⟨x, hxmem⟩ : C.coordinateSpace) := by
        apply Subtype.ext
        simpa [heqx, x] using A.lift_coe ⟨r₀ - q₀, htransport⟩
      have hsx : Real.sign (mapScalar phi (⟨x, hxmem⟩ : C.coordinateSpace)) =
          Real.sign x := by
        rw [← hlift]
        exact (hsign ⟨r₀ - q₀, htransport⟩).trans
          (congrArg Real.sign heqx)
      rw [hm']
      exact hsx.symm
  have hAB := endpointSign a b s s b.1.re a.1.re
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re]
      ring)
  have hAB' := endpointSign a b' t s (b'.1.re + (t.1 - s.1).re) a.1.re
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re, Complex.sub_re]
      ring)
  have hA'B := endpointSign a' b s t
    (b.1.re) (a'.1.re + (t.1 - s.1).re)
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re, Complex.sub_re]
      ring)
  have hA'B' := endpointSign a' b' t t
    (b'.1.re + (t.1 - s.1).re) (a'.1.re + (t.1 - s.1).re)
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re, Complex.sub_re]
      ring)
  have hAA' := endpointSign a a' t s
    (a'.1.re + (t.1 - s.1).re) a.1.re
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re, Complex.sub_re]
      ring)
  have hBB' := endpointSign b b' t s
    (b'.1.re + (t.1 - s.1).re) b.1.re
    (by simp [E]) (by simp [E]) (by
      simp only [Complex.add_re, Complex.sub_re]
      ring)
  have hsourceInterval :
      (translatedHorizontalInterval a.1 b.1 s.1 ∩
        translatedHorizontalInterval a'.1 b'.1 t.1).Nonempty := by
    rcases hOverlap with ⟨u, v, huv, _huvIm, huvSeg⟩
    let z : Tiling.Plane := midpoint ℝ u v
    have hz : z ∈ openSegment ℝ u v := midpoint_mem_openSegment u v
    have hz' := huvSeg hz
    have hab : a.1 + s.1 ≠ b.1 + s.1 := by
      intro h
      apply hside.1
      exact add_right_cancel h
    have hab' : a'.1 + t.1 ≠ b'.1 + t.1 := by
      intro h
      apply hside'.1
      exact add_right_cancel h
    have habRe : (a.1 + s.1).re ≠ (b.1 + s.1).re := by
      intro h
      apply hab
      apply Complex.ext h
      simp only [Complex.add_im]
      rw [hside.2.1]
    have hab'Re : (a'.1 + t.1).re ≠ (b'.1 + t.1).re := by
      intro h
      apply hab'
      apply Complex.ext h
      simp only [Complex.add_im]
      rw [hside'.2.1]
    have hz1 := fct_re_mem_openSegment_of_mem hz'.1
    have hz2 := fct_re_mem_openSegment_of_mem hz'.2
    rw [openSegment_eq_Ioo' habRe] at hz1
    rw [openSegment_eq_Ioo' hab'Re] at hz2
    refine ⟨z.re, ?_, ?_⟩
    · simpa only [translatedHorizontalInterval, Complex.add_re,
        min_add_add_right, max_add_add_right] using hz1
    · simpa only [translatedHorizontalInterval, Complex.add_re,
        min_add_add_right, max_add_add_right] using hz2
  have reverseSign {x y X Y : ℝ}
      (h : Real.sign (y - x) = Real.sign (Y - X)) :
      Real.sign (x - y) = Real.sign (X - Y) := by
    calc
      Real.sign (x - y) = Real.sign (-(y - x)) := by rw [neg_sub]
      _ = -Real.sign (y - x) := by rw [Real.sign_neg]
      _ = -Real.sign (Y - X) := by rw [h]
      _ = Real.sign (-(Y - X)) := by rw [Real.sign_neg]
      _ = Real.sign (X - Y) := by rw [neg_sub]
  have hltAB :
      a.1.re + s.1.re < b.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hAB)
  have hltAB' :
      a.1.re + s.1.re < b'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hAB')
  have hltA'B :
      a'.1.re + t.1.re < b.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hA'B)
  have hltA'B' :
      a'.1.re + t.1.re < b'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hA'B')
  have hltAA' :
      a.1.re + s.1.re < a'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hAA')
  have hltBB' :
      b.1.re + s.1.re < b'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq hBB')
  have hltBA :
      b.1.re + s.1.re < a.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hAB))
  have hltB'A :
      b'.1.re + t.1.re < a.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hAB'))
  have hltBA' :
      b.1.re + s.1.re < a'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re <
          (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hA'B))
  have hltB'A' :
      b'.1.re + t.1.re < a'.1.re + t.1.re ↔
        (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hA'B'))
  have hltA'A :
      a'.1.re + t.1.re < a.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint a'.1 a'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint a.1 a.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hAA'))
  have hltB'B :
      b'.1.re + t.1.re < b.1.re + s.1.re ↔
        (mapPoint phi (C.vertexPoint b'.1 b'.2)).re +
            (P.fullCenters t).re <
          (mapPoint phi (C.vertexPoint b.1 b.2)).re +
            (P.fullCenters s).re := by
    simpa only [P.fullCenters_apply, Complex.add_re] using
      (lt_iff_of_sign_sub_eq (reverseSign hBB'))
  have htargetInterval :
      (translatedHorizontalInterval
          (mapPoint phi (C.vertexPoint a.1 a.2))
          (mapPoint phi (C.vertexPoint b.1 b.2)) (P.fullCenters s) ∩
        translatedHorizontalInterval
          (mapPoint phi (C.vertexPoint a'.1 a'.2))
          (mapPoint phi (C.vertexPoint b'.1 b'.2)) (P.fullCenters t)).Nonempty := by
    simpa only [translatedHorizontalInterval, ← min_add_add_right,
      ← max_add_add_right, Set.Ioo_inter_Ioo, Set.nonempty_Ioo,
      max_lt_iff, lt_min_iff, min_lt_iff, lt_max_iff,
      lt_self_iff_false,
      hltAB, hltAB', hltA'B, hltA'B', hltAA', hltBB',
      hltBA, hltB'A, hltBA', hltB'A', hltA'A, hltB'B] using
      hsourceInterval
  have hsourceHeight :
      (a.1 + s.1).im = (a'.1 + t.1).im := by
    rcases hOverlap with ⟨u, v, huv, _huvIm, huvSeg⟩
    have hz := huvSeg (midpoint_mem_openSegment (𝕜 := ℝ) u v)
    have habIm : (a.1 + s.1).im = (b.1 + s.1).im := by
      simp only [Complex.add_im]
      rw [hside.2.1]
    have hab'Im : (a'.1 + t.1).im = (b'.1 + t.1).im := by
      simp only [Complex.add_im]
      rw [hside'.2.1]
    calc
      (a.1 + s.1).im = (midpoint ℝ u v).im :=
        (fct_im_eq_of_mem_openSegment_horizontal habIm hz.1).symm
      _ = (a'.1 + t.1).im :=
        fct_im_eq_of_mem_openSegment_horizontal hab'Im hz.2
  have htargetHeight :
      (D.planarHomeomorph a.1 + P.fullCenters s).im =
        (D.planarHomeomorph a'.1 + P.fullCenters t).im := by
    rw [D.vertex_agreement a.1 a.2, D.vertex_agreement a'.1 a'.2,
      P.fullCenters_apply s, P.fullCenters_apply t]
    let xa : C.coordinateSpace :=
      ⟨a.1.im, C.vertex_im_mem a.1 a.2⟩
    let xs : C.coordinateSpace :=
      ⟨s.1.im, C.centre_im_mem s.1 s.2⟩
    let xa' : C.coordinateSpace :=
      ⟨a'.1.im, C.vertex_im_mem a'.1 a'.2⟩
    let xt : C.coordinateSpace :=
      ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
    have hcoord : xa + xs = xa' + xt := by
      apply Subtype.ext
      simpa only [xa, xs, xa', xt, Submodule.coe_add, Complex.add_im] using
        hsourceHeight
    have hmap := congrArg (fun z : C.coordinateSpace => mapScalar phi z) hcoord
    change (phi (xa + xs) : ℝ) = (phi (xa' + xt) : ℝ) at hmap
    rw [map_add, map_add] at hmap
    simpa only [mapPoint, mapScalar, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint, Complex.add_im, Complex.ofReal_im,
      Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      zero_mul, mul_one, zero_add, add_zero, Rat.cast_add] using hmap
  have htargetInterval' :
      (translatedHorizontalInterval
          (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
            (P.fullCenters s) ∩
        translatedHorizontalInterval
          (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
            (P.fullCenters t)).Nonempty := by
    simpa only [D.vertex_agreement a.1 a.2,
      D.vertex_agreement b.1 b.2, D.vertex_agreement a'.1 a'.2,
      D.vertex_agreement b'.1 b'.2] using htargetInterval
  change (Ioo (min (D.planarHomeomorph a.1).re
      (D.planarHomeomorph b.1).re + (P.fullCenters s).re)
      (max (D.planarHomeomorph a.1).re
        (D.planarHomeomorph b.1).re + (P.fullCenters s).re) ∩
    Ioo (min (D.planarHomeomorph a'.1).re
      (D.planarHomeomorph b'.1).re + (P.fullCenters t).re)
      (max (D.planarHomeomorph a'.1).re
        (D.planarHomeomorph b'.1).re + (P.fullCenters t).re)).Nonempty at htargetInterval'
  obtain ⟨x, hx, hx'⟩ := htargetInterval'
  let lo := max (min (D.planarHomeomorph a.1).re
      (D.planarHomeomorph b.1).re + (P.fullCenters s).re)
    (min (D.planarHomeomorph a'.1).re
      (D.planarHomeomorph b'.1).re + (P.fullCenters t).re)
  let hi := min (max (D.planarHomeomorph a.1).re
      (D.planarHomeomorph b.1).re + (P.fullCenters s).re)
    (max (D.planarHomeomorph a'.1).re
      (D.planarHomeomorph b'.1).re + (P.fullCenters t).re)
  have hlohi : lo < hi :=
    (max_lt hx.1 hx'.1).trans (lt_min hx.2 hx'.2)
  let u : Tiling.Plane := (lo : ℂ) +
    (D.planarHomeomorph a.1 + P.fullCenters s).im * Complex.I
  let v : Tiling.Plane := (hi : ℂ) +
    (D.planarHomeomorph a.1 + P.fullCenters s).im * Complex.I
  have huv : u ≠ v := by
    intro h
    have := congrArg Complex.re h
    simp [u, v] at this
    linarith [hlohi]
  have huvIm : u.im = v.im := by simp [u, v]
  refine ⟨u, v, huv, huvIm, ?_⟩
  intro z hz
  have hzIm : z.im = (D.planarHomeomorph a.1 + P.fullCenters s).im := by
    have hIm : u.im = v.im := by simp [u, v]
    simpa [u] using
      (fct_im_eq_of_mem_openSegment_horizontal hIm hz)
  have hzRe := fct_re_mem_openSegment_of_mem hz
  have hzX : z.re ∈ Ioo lo hi := by
    rw [show u.re = lo by simp [u], show v.re = hi by simp [v],
      openSegment_eq_Ioo' hlohi.ne] at hzRe
    simpa only [u, v, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero,
      Complex.I_im, mul_one, zero_sub, neg_zero, add_zero,
      min_eq_left hlohi.le, max_eq_right hlohi.le] using hzRe
  have hza : z ∈ openSegment ℝ
      (D.planarHomeomorph a.1 + P.fullCenters s)
      (D.planarHomeomorph b.1 + P.fullCenters s) := by
    have hab : D.planarHomeomorph a.1 + P.fullCenters s ≠
        D.planarHomeomorph b.1 + P.fullCenters s := by
      intro h
      apply hside.1
      apply D.planarHomeomorph.injective
      exact add_right_cancel h
    have habIm :
        (D.planarHomeomorph a.1 + P.fullCenters s).im =
          (D.planarHomeomorph b.1 + P.fullCenters s).im := by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
      rw [hside.2.1]
    have hz' : (z.re : ℂ) +
        (D.planarHomeomorph a.1 + P.fullCenters s).im * Complex.I = z := by
      apply Complex.ext
      · simp
      · simp [hzIm]
    rw [← hz', fct_horizontal_point_mem_openSegment_iff hab habIm]
    rw [openSegment_eq_Ioo' (by
      intro h
      exact hab (Complex.ext h habIm))]
    have hzL : min (D.planarHomeomorph a.1).re
        (D.planarHomeomorph b.1).re + (P.fullCenters s).re < z.re :=
      (le_max_left _ _).trans_lt hzX.1
    have hzU : z.re < max (D.planarHomeomorph a.1).re
        (D.planarHomeomorph b.1).re + (P.fullCenters s).re :=
      hzX.2.trans_le (min_le_left _ _)
    have hzL' : min (D.planarHomeomorph a.1 + P.fullCenters s).re
        (D.planarHomeomorph b.1 + P.fullCenters s).re < z.re := by
      simpa only [Complex.add_re, min_add_add_right] using hzL
    have hzU' : z.re < max (D.planarHomeomorph a.1 + P.fullCenters s).re
        (D.planarHomeomorph b.1 + P.fullCenters s).re := by
      simpa only [Complex.add_re, max_add_add_right] using hzU
    exact ⟨hzL', hzU'⟩
  have hzb : z ∈ openSegment ℝ
      (D.planarHomeomorph a'.1 + P.fullCenters t)
      (D.planarHomeomorph b'.1 + P.fullCenters t) := by
    have hab : D.planarHomeomorph a'.1 + P.fullCenters t ≠
        D.planarHomeomorph b'.1 + P.fullCenters t := by
      intro h
      apply hside'.1
      apply D.planarHomeomorph.injective
      exact add_right_cancel h
    have habIm :
        (D.planarHomeomorph a'.1 + P.fullCenters t).im =
          (D.planarHomeomorph b'.1 + P.fullCenters t).im := by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
      rw [hside'.2.1]
    have hz' : (z.re : ℂ) +
        (D.planarHomeomorph a'.1 + P.fullCenters t).im * Complex.I = z := by
      apply Complex.ext
      · simp
      · simp [hzIm, htargetHeight]
    rw [← hz', fct_horizontal_point_mem_openSegment_iff hab habIm]
    rw [openSegment_eq_Ioo' (by
      intro h
      exact hab (Complex.ext h habIm))]
    have hzL : min (D.planarHomeomorph a'.1).re
        (D.planarHomeomorph b'.1).re + (P.fullCenters t).re < z.re :=
      (le_max_right _ _).trans_lt hzX.1
    have hzU : z.re < max (D.planarHomeomorph a'.1).re
        (D.planarHomeomorph b'.1).re + (P.fullCenters t).re :=
      hzX.2.trans_le (min_le_right _ _)
    have hzL' : min (D.planarHomeomorph a'.1 + P.fullCenters t).re
        (D.planarHomeomorph b'.1 + P.fullCenters t).re < z.re := by
      simpa only [Complex.add_re, min_add_add_right] using hzL
    have hzU' : z.re < max (D.planarHomeomorph a'.1 + P.fullCenters t).re
        (D.planarHomeomorph b'.1 + P.fullCenters t).re := by
      simpa only [Complex.add_re, max_add_add_right] using hzU
    exact ⟨hzL', hzU'⟩
  exact ⟨hza, hzb⟩

private theorem target9_seam_preserved_of_cut_data
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (Acrit : FiniteTransportCriticalAlphabet C)
    (hsign : ∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1)
    {y A B : ℝ} (hTile : TilesOn C.region C.centres univ)
    (code : EndpointAlignedLineCode C.region C.centres y A B)
    (l r : ↥code.cuts) (_hlr : l.1 < r.1)
    (_hno : Ioo l.1 r.1 ∩ (code.cuts : Set ℝ) = ∅)
    (S : HorizontalSeamCell C.region C.centres y l.1 r.1) :
    (∀ x ∈ Ioo
        (mapScalar phi (target9_cutLift code l))
        (mapScalar phi (target9_cutLift code r)),
      linePoint y x ∈
        openSegment ℝ
          (D.firstPlanarHomeomorph S.a.1 + P.firstCenters S.upperCenter)
          (D.firstPlanarHomeomorph S.b.1 + P.firstCenters S.upperCenter)) ∧
    ∀ x ∈ Ioo
        (mapScalar phi (target9_cutLift code l))
        (mapScalar phi (target9_cutLift code r)),
      linePoint y x ∈
        openSegment ℝ
          (D.firstPlanarHomeomorph S.a'.1 + P.firstCenters S.lowerCenter)
          (D.firstPlanarHomeomorph S.b'.1 + P.firstCenters S.lowerCenter) := by
  have hdelta : (S.lowerCenter.1 - S.upperCenter.1).re ∈
      horizontalContactDisplacements C.region C.centres S.a S.b S.a' S.b' := by
    let q₀ : ℝ := (2 * l.1 + r.1) / 3
    let q₁ : ℝ := (l.1 + 2 * r.1) / 3
    have hq₀ : q₀ ∈ Ioo l.1 r.1 := by
      dsimp [q₀]
      constructor <;> linarith [S.left_lt_right]
    have hq₁ : q₁ ∈ Ioo l.1 r.1 := by
      dsimp [q₁]
      constructor <;> linarith [S.left_lt_right]
    have hq₀q₁ : q₀ < q₁ := by
      dsimp [q₀, q₁]
      linarith [S.left_lt_right]
    apply properOverlap_contactDisplacement S.first_horizontal
      S.second_horizontal
    refine ⟨linePoint y q₀, linePoint y q₁, ?_, by simp [linePoint], ?_⟩
    · intro h
      have hre := congrArg Complex.re h
      simp [linePoint] at hre
      linarith
    · intro p hp
      exact ⟨(convex_openSegment _ _).openSegment_subset
          (S.first_side q₀ hq₀) (S.first_side q₁ hq₁) hp,
        (convex_openSegment _ _).openSegment_subset
          (S.second_side q₀ hq₀) (S.second_side q₁ hq₁) hp⟩
  let delta : ℝ := (S.lowerCenter.1 - S.upperCenter.1).re
  let E : Set ℝ := {S.a.1.re, S.b.1.re, S.a'.1.re + delta,
    S.b'.1.re + delta}
  have firstEndpoint_re_eq_full (v : C.region.vertices) (t : C.centres) :
      (D.firstPlanarHomeomorph v.1 + P.firstCenters t).re =
        (mapPoint phi (C.vertexPoint v.1 v.2) +
          mapPoint phi (C.centrePoint t.1 t.2)).re := by
    rw [D.first_vertex_agreement v.1 v.2, P.firstCenters_apply]
    simp [mapFirstPoint, mapPoint, ApproximationContext.vertexPoint,
      ApproximationContext.centrePoint]
  have endpointLt
      (v w : C.region.vertices) (q p : C.centres)
      (hv : (v.1 + (q : Tiling.Plane)).re - S.upperCenter.1.re ∈ E)
      (hw : (w.1 + (p : Tiling.Plane)).re - S.upperCenter.1.re ∈ E) :
      (v.1 + (q : Tiling.Plane)).re <
          (w.1 + (p : Tiling.Plane)).re ↔
        (D.firstPlanarHomeomorph v.1 + P.firstCenters q).re <
          (D.firstPlanarHomeomorph w.1 + P.firstCenters p).re := by
    have hs := target9_endpointSign phi Acrit hsign hdelta v w p q
      ((w.1 + (p : Tiling.Plane)).re - S.upperCenter.1.re)
      ((v.1 + (q : Tiling.Plane)).re - S.upperCenter.1.re)
      hw hv (by ring)
    rw [firstEndpoint_re_eq_full w p, firstEndpoint_re_eq_full v q]
    exact lt_iff_of_sign_sub_eq hs
  have endpointLe
      (v w : C.region.vertices) (q p : C.centres)
      (hv : (v.1 + (q : Tiling.Plane)).re - S.upperCenter.1.re ∈ E)
      (hw : (w.1 + (p : Tiling.Plane)).re - S.upperCenter.1.re ∈ E) :
      (v.1 + (q : Tiling.Plane)).re ≤
          (w.1 + (p : Tiling.Plane)).re ↔
        (D.firstPlanarHomeomorph v.1 + P.firstCenters q).re ≤
          (D.firstPlanarHomeomorph w.1 + P.firstCenters p).re := by
    simpa only [not_lt] using
      not_congr (endpointLt w v p q hw hv)
  have hnormA :
      (S.a.1 + (S.upperCenter : Tiling.Plane)).re -
          S.upperCenter.1.re ∈ E := by
    simp [E]
  have hnormB :
      (S.b.1 + (S.upperCenter : Tiling.Plane)).re -
          S.upperCenter.1.re ∈ E := by
    simp [E]
  have hnormA' :
      (S.a'.1 + (S.lowerCenter : Tiling.Plane)).re -
          S.upperCenter.1.re ∈ E := by
    simp only [E, Set.mem_insert_iff, Set.mem_singleton_iff, Complex.add_re]
    exact Or.inr (Or.inr (Or.inl (by simp [delta]; ring)))
  have hnormB' :
      (S.b'.1 + (S.lowerCenter : Tiling.Plane)).re -
          S.upperCenter.1.re ∈ E := by
    simp only [E, Set.mem_insert_iff, Set.mem_singleton_iff, Complex.add_re]
    exact Or.inr (Or.inr (Or.inr (by simp [delta]; ring)))
  have endpointRepresentation (e : ↥code.cuts) (he : e = l ∨ e = r) :
      ∃ v : C.region.vertices, ∃ t : C.centres,
        e.1 = (v.1 + (t : Tiling.Plane)).re ∧
        mapScalar phi (target9_cutLift code e) =
          (D.firstPlanarHomeomorph v.1 + P.firstCenters t).re ∧
        (v.1 + (t : Tiling.Plane)).re - S.upperCenter.1.re ∈ E := by
    have hfour := target9_seam_endpoint_among_four hTile S
      (by rcases he with rfl | rfl <;> simp) (code.cut_controlled e.1 e.2)
    rcases hfour with h | h | h | h
    · refine ⟨S.a, S.upperCenter, ?_, ?_, hnormA⟩
      · simpa [linePoint] using congrArg Complex.re h
      · have hm := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D S.a.1 S.a.2 S.upperCenter e.1 (target9_cutLift code e) rfl
          (by simpa [linePoint] using congrArg Complex.re h)
        calc
          mapScalar phi (target9_cutLift code e) =
              D.firstHomeomorph S.a.1.re +
                (mapFirstPoint phi
                  (C.centrePoint S.upperCenter.1 S.upperCenter.2)).re := hm
          _ = (D.firstPlanarHomeomorph S.a.1 +
              P.firstCenters S.upperCenter).re := by
            rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
            simp
    · refine ⟨S.b, S.upperCenter, ?_, ?_, hnormB⟩
      · simpa [linePoint] using congrArg Complex.re h
      · have hm := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D S.b.1 S.b.2 S.upperCenter e.1 (target9_cutLift code e) rfl
          (by simpa [linePoint] using congrArg Complex.re h)
        calc
          mapScalar phi (target9_cutLift code e) =
              D.firstHomeomorph S.b.1.re +
                (mapFirstPoint phi
                  (C.centrePoint S.upperCenter.1 S.upperCenter.2)).re := hm
          _ = (D.firstPlanarHomeomorph S.b.1 +
              P.firstCenters S.upperCenter).re := by
            rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
            simp
    · refine ⟨S.a', S.lowerCenter, ?_, ?_, hnormA'⟩
      · simpa [linePoint] using congrArg Complex.re h
      · have hm := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D S.a'.1 S.a'.2 S.lowerCenter e.1 (target9_cutLift code e) rfl
          (by simpa [linePoint] using congrArg Complex.re h)
        calc
          mapScalar phi (target9_cutLift code e) =
              D.firstHomeomorph S.a'.1.re +
                (mapFirstPoint phi
                  (C.centrePoint S.lowerCenter.1 S.lowerCenter.2)).re := hm
          _ = (D.firstPlanarHomeomorph S.a'.1 +
              P.firstCenters S.lowerCenter).re := by
            rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
            simp
    · refine ⟨S.b', S.lowerCenter, ?_, ?_, hnormB'⟩
      · simpa [linePoint] using congrArg Complex.re h
      · have hm := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D S.b'.1 S.b'.2 S.lowerCenter e.1 (target9_cutLift code e) rfl
          (by simpa [linePoint] using congrArg Complex.re h)
        calc
          mapScalar phi (target9_cutLift code e) =
              D.firstHomeomorph S.b'.1.re +
                (mapFirstPoint phi
                  (C.centrePoint S.lowerCenter.1 S.lowerCenter.2)).re := hm
          _ = (D.firstPlanarHomeomorph S.b'.1 +
              P.firstCenters S.lowerCenter).re := by
            rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
            simp
  obtain ⟨vl, tl, hlcoord, hlmap, hlnorm⟩ :=
    endpointRepresentation l (Or.inl rfl)
  obtain ⟨vr, tr, hrcoord, hrmap, hrnorm⟩ :=
    endpointRepresentation r (Or.inr rfl)
  have transportUpper (v : C.region.vertices) (t : C.centres)
      (hnorm : (v.1 + (t : Tiling.Plane)).re - S.upperCenter.1.re ∈ E)
      (hmem : (v.1 + (t : Tiling.Plane)).re ∈
        uIcc (S.a.1 + (S.upperCenter : Tiling.Plane)).re
          (S.b.1 + (S.upperCenter : Tiling.Plane)).re) :
      (D.firstPlanarHomeomorph v.1 + P.firstCenters t).re ∈
        uIcc
          (D.firstPlanarHomeomorph S.a.1 +
            P.firstCenters S.upperCenter).re
          (D.firstPlanarHomeomorph S.b.1 +
            P.firstCenters S.upperCenter).re := by
    rw [Set.mem_uIcc] at hmem ⊢
    rcases hmem with hmem | hmem
    · exact Or.inl ⟨(endpointLe S.a v S.upperCenter t hnormA hnorm).mp hmem.1,
        (endpointLe v S.b t S.upperCenter hnorm hnormB).mp hmem.2⟩
    · exact Or.inr ⟨(endpointLe S.b v S.upperCenter t hnormB hnorm).mp hmem.1,
        (endpointLe v S.a t S.upperCenter hnorm hnormA).mp hmem.2⟩
  have transportLower (v : C.region.vertices) (t : C.centres)
      (hnorm : (v.1 + (t : Tiling.Plane)).re - S.upperCenter.1.re ∈ E)
      (hmem : (v.1 + (t : Tiling.Plane)).re ∈
        uIcc (S.a'.1 + (S.lowerCenter : Tiling.Plane)).re
          (S.b'.1 + (S.lowerCenter : Tiling.Plane)).re) :
      (D.firstPlanarHomeomorph v.1 + P.firstCenters t).re ∈
        uIcc
          (D.firstPlanarHomeomorph S.a'.1 +
            P.firstCenters S.lowerCenter).re
          (D.firstPlanarHomeomorph S.b'.1 +
            P.firstCenters S.lowerCenter).re := by
    rw [Set.mem_uIcc] at hmem ⊢
    rcases hmem with hmem | hmem
    · exact Or.inl ⟨(endpointLe S.a' v S.lowerCenter t hnormA' hnorm).mp hmem.1,
        (endpointLe v S.b' t S.lowerCenter hnorm hnormB').mp hmem.2⟩
    · exact Or.inr ⟨(endpointLe S.b' v S.lowerCenter t hnormB' hnorm).mp hmem.1,
        (endpointLe v S.a' t S.lowerCenter hnorm hnormA').mp hmem.2⟩
  have hfirstEnds := target9_lineEndpoints_mem_segment_of_openSegment_on_Ioo
    S.left_lt_right S.first_side
  have hsecondEnds := target9_lineEndpoints_mem_segment_of_openSegment_on_Ioo
    S.left_lt_right S.second_side
  have hlUpperSource : l.1 ∈
      uIcc (S.a.1 + (S.upperCenter : Tiling.Plane)).re
        (S.b.1 + (S.upperCenter : Tiling.Plane)).re := by
    simpa [linePoint] using
      target9_re_mem_uIcc_of_mem_segment_horizontal hfirstEnds.1
  have hrUpperSource : r.1 ∈
      uIcc (S.a.1 + (S.upperCenter : Tiling.Plane)).re
        (S.b.1 + (S.upperCenter : Tiling.Plane)).re := by
    simpa [linePoint] using
      target9_re_mem_uIcc_of_mem_segment_horizontal hfirstEnds.2
  have hlLowerSource : l.1 ∈
      uIcc (S.a'.1 + (S.lowerCenter : Tiling.Plane)).re
        (S.b'.1 + (S.lowerCenter : Tiling.Plane)).re := by
    simpa [linePoint] using
      target9_re_mem_uIcc_of_mem_segment_horizontal hsecondEnds.1
  have hrLowerSource : r.1 ∈
      uIcc (S.a'.1 + (S.lowerCenter : Tiling.Plane)).re
        (S.b'.1 + (S.lowerCenter : Tiling.Plane)).re := by
    simpa [linePoint] using
      target9_re_mem_uIcc_of_mem_segment_horizontal hsecondEnds.2
  have hlUpper := transportUpper vl tl hlnorm (by simpa [hlcoord] using hlUpperSource)
  have hrUpper := transportUpper vr tr hrnorm (by simpa [hrcoord] using hrUpperSource)
  have hlLower := transportLower vl tl hlnorm (by simpa [hlcoord] using hlLowerSource)
  have hrLower := transportLower vr tr hrnorm (by simpa [hrcoord] using hrLowerSource)
  rw [← hlmap] at hlUpper hlLower
  rw [← hrmap] at hrUpper hrLower
  let qmid : ℝ := (l.1 + r.1) / 2
  have hqmid : qmid ∈ Ioo l.1 r.1 := by
    dsimp [qmid]
    constructor <;> linarith [S.left_lt_right]
  have hsourceUpperHeight :
      (S.a.1 + (S.upperCenter : Tiling.Plane)).im = y := by
    have hp := S.first_side qmid hqmid
    have him :
        (S.a.1 + (S.upperCenter : Tiling.Plane)).im =
          (S.b.1 + (S.upperCenter : Tiling.Plane)).im := by
      simp only [Complex.add_im]
      rw [S.first_horizontal.2.1]
    simpa [linePoint] using
      (fct_im_eq_of_mem_openSegment_horizontal him hp).symm
  have hsourceLowerHeight :
      (S.a'.1 + (S.lowerCenter : Tiling.Plane)).im = y := by
    have hp := S.second_side qmid hqmid
    have him :
        (S.a'.1 + (S.lowerCenter : Tiling.Plane)).im =
          (S.b'.1 + (S.lowerCenter : Tiling.Plane)).im := by
      simp only [Complex.add_im]
      rw [S.second_horizontal.2.1]
    simpa [linePoint] using
      (fct_im_eq_of_mem_openSegment_horizontal him hp).symm
  have htargetUpperHeight :
      (D.firstPlanarHomeomorph S.a.1 + P.firstCenters S.upperCenter).im = y := by
    rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simpa [mapFirstPoint, ApproximationContext.centrePoint] using hsourceUpperHeight
  have htargetLowerHeight :
      (D.firstPlanarHomeomorph S.a'.1 + P.firstCenters S.lowerCenter).im = y := by
    rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simpa [mapFirstPoint, ApproximationContext.centrePoint] using hsourceLowerHeight
  have targetInside
      {u v : Tiling.Plane} (huv : u ≠ v) (huvIm : u.im = v.im)
      (huy : u.im = y)
      {ml mr x : ℝ} (hml : ml ∈ uIcc u.re v.re)
      (hmr : mr ∈ uIcc u.re v.re) (hx : x ∈ Ioo ml mr) :
      linePoint y x ∈ openSegment ℝ u v := by
    have hmin : min u.re v.re ≤ ml := by
      rw [Set.mem_uIcc] at hml
      rcases hml with hml | hml
      · exact (min_le_left _ _).trans hml.1
      · exact (min_le_right _ _).trans hml.1
    have hmax : mr ≤ max u.re v.re := by
      rw [Set.mem_uIcc] at hmr
      rcases hmr with hmr | hmr
      · exact hmr.2.trans (le_max_right _ _)
      · exact hmr.2.trans (le_max_left _ _)
    have hline : linePoint y x = (x : ℂ) + u.im * Complex.I := by
      apply Complex.ext <;> simp [linePoint, huy]
    rw [hline, fct_horizontal_point_mem_openSegment_iff huv huvIm]
    rw [openSegment_eq_Ioo' (by
      intro h
      exact huv (Complex.ext h huvIm))]
    exact ⟨hmin.trans_lt hx.1, hx.2.trans_le hmax⟩
  constructor
  · intro x hx
    have hne :
        D.firstPlanarHomeomorph S.a.1 + P.firstCenters S.upperCenter ≠
          D.firstPlanarHomeomorph S.b.1 + P.firstCenters S.upperCenter := by
      intro h
      apply S.first_horizontal.1
      apply D.firstPlanarHomeomorph.injective
      exact add_right_cancel h
    have him :
        (D.firstPlanarHomeomorph S.a.1 + P.firstCenters S.upperCenter).im =
          (D.firstPlanarHomeomorph S.b.1 + P.firstCenters S.upperCenter).im := by
      rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
      rw [S.first_horizontal.2.1]
    exact targetInside hne him htargetUpperHeight hlUpper hrUpper hx
  · intro x hx
    have hne :
        D.firstPlanarHomeomorph S.a'.1 + P.firstCenters S.lowerCenter ≠
          D.firstPlanarHomeomorph S.b'.1 + P.firstCenters S.lowerCenter := by
      intro h
      apply S.second_horizontal.1
      apply D.firstPlanarHomeomorph.injective
      exact add_right_cancel h
    have him :
        (D.firstPlanarHomeomorph S.a'.1 + P.firstCenters S.lowerCenter).im =
          (D.firstPlanarHomeomorph S.b'.1 + P.firstCenters S.lowerCenter).im := by
      rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
      rw [S.second_horizontal.2.1]
    exact targetInside hne him htargetLowerHeight hlLower hrLower hx


private theorem firstStageEndpointAlignedLineCode_transport_exists :
    (∀ (C : ApproximationContext.{0})
    (_hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (Acrit : FiniteTransportCriticalAlphabet C),
    (∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1) →
    ∀ {y A B : ℝ} (code : EndpointAlignedLineCode C.region C.centres y A B),
      Nonempty (FirstStageEndpointAlignedLineCodeTransport C phi D P code)) := by
  intro C hTile phi D P Acrit hsign y A B code
  let mapped : ↥code.cuts → ℝ :=
    fun q ↦ mapScalar phi (target9_cutLift code q)
  have hmono : StrictMono mapped :=
    target9_mappedCut_strictMono hTile code Acrit phi hsign
  refine ⟨{
    cutLift := target9_cutLift code
    cutLift_coe := target9_cutLift_coe code
    mappedCut := mapped
    mappedCut_formula := fun _ ↦ rfl
    mapped_strictMono := hmono
    crossing_preserved := ?_
    seam_preserved := ?_
    mapped_cells_cover := ?_ }⟩
  · intro l r hlr _hno X x hx
    exact target9_crossing_preserved_of_cut_data D P code
      (target9_cutLift code) mapped (target9_cutLift_coe code)
      (fun _ ↦ rfl) l r hlr X hx
  · intro l r hlr hno S
    exact target9_seam_preserved_of_cut_data D P Acrit hsign hTile code
      l r hlr hno S
  · intro x hx hxrange
    exact target9_mapped_cells_cover_generic code.cuts code.qLeft code.qRight
      code.left_mem code.right_mem mapped hmono hx hxrange

private theorem target11_intrinsicHorizontalSide_eq_of_openSegments_meet
    {K : Region} {a b c d : ↥K.vertices}
    (hab : IsIntrinsicHorizontalSide K a b)
    (hcd : IsIntrinsicHorizontalSide K c d)
    (hmeet : (openSegment ℝ a.1 b.1 ∩ openSegment ℝ c.1 d.1).Nonempty) :
    openSegment ℝ a.1 b.1 = openSegment ℝ c.1 d.1 := by
  obtain ⟨p, hpab, hpcd⟩ := hmeet
  have habRe : a.1.re ≠ b.1.re := by
    intro h
    exact hab.1 (Complex.ext h hab.2.1)
  have hcdRe : c.1.re ≠ d.1.re := by
    intro h
    exact hcd.1 (Complex.ext h hcd.2.1)
  have hpabRe := fct_re_mem_openSegment_of_mem hpab
  have hpcdRe := fct_re_mem_openSegment_of_mem hpcd
  rw [openSegment_eq_Ioo' habRe] at hpabRe
  rw [openSegment_eq_Ioo' hcdRe] at hpcdRe
  have hacIm : a.1.im = c.1.im := by
    have hpabIm := fct_im_eq_of_mem_openSegment_horizontal hab.2.1 hpab
    have hpcdIm := fct_im_eq_of_mem_openSegment_horizontal hcd.2.1 hpcd
    exact hpabIm.symm.trans hpcdIm
  let alo : ℝ := min a.1.re b.1.re
  let ahi : ℝ := max a.1.re b.1.re
  let clo : ℝ := min c.1.re d.1.re
  let chi : ℝ := max c.1.re d.1.re
  have lowerA_vertex : linePoint a.1.im alo ∈ K.vertices := by
    rcases le_total a.1.re b.1.re with h | h
    · rw [show alo = a.1.re by simp [alo, min_eq_left h]]
      have heq : linePoint a.1.im a.1.re = a.1 := by
        apply Complex.ext <;> simp [linePoint]
      rw [heq]
      exact a.2
    · rw [show alo = b.1.re by simp [alo, min_eq_right h]]
      have heq : linePoint a.1.im b.1.re = b.1 := by
        apply Complex.ext <;> simp [linePoint, hab.2.1]
      rw [heq]
      exact b.2
  have upperA_vertex : linePoint a.1.im ahi ∈ K.vertices := by
    rcases le_total a.1.re b.1.re with h | h
    · rw [show ahi = b.1.re by simp [ahi, max_eq_right h]]
      have heq : linePoint a.1.im b.1.re = b.1 := by
        apply Complex.ext <;> simp [linePoint, hab.2.1]
      rw [heq]
      exact b.2
    · rw [show ahi = a.1.re by simp [ahi, max_eq_left h]]
      have heq : linePoint a.1.im a.1.re = a.1 := by
        apply Complex.ext <;> simp [linePoint]
      rw [heq]
      exact a.2
  have lowerC_vertex : linePoint a.1.im clo ∈ K.vertices := by
    rcases le_total c.1.re d.1.re with h | h
    · rw [show clo = c.1.re by simp [clo, min_eq_left h], hacIm]
      have heq : linePoint c.1.im c.1.re = c.1 := by
        apply Complex.ext <;> simp [linePoint]
      rw [heq]
      exact c.2
    · rw [show clo = d.1.re by simp [clo, min_eq_right h], hacIm]
      have heq : linePoint c.1.im d.1.re = d.1 := by
        apply Complex.ext <;> simp [linePoint, hcd.2.1]
      rw [heq]
      exact d.2
  have upperC_vertex : linePoint a.1.im chi ∈ K.vertices := by
    rcases le_total c.1.re d.1.re with h | h
    · rw [show chi = d.1.re by simp [chi, max_eq_right h], hacIm]
      have heq : linePoint c.1.im d.1.re = d.1 := by
        apply Complex.ext <;> simp [linePoint, hcd.2.1]
      rw [heq]
      exact d.2
    · rw [show chi = c.1.re by simp [chi, max_eq_left h], hacIm]
      have heq : linePoint c.1.im c.1.re = c.1 := by
        apply Complex.ext <;> simp [linePoint]
      rw [heq]
      exact c.2
  have point_mem_ab {x : ℝ} (hx : x ∈ Ioo alo ahi) :
      linePoint a.1.im x ∈ openSegment ℝ a.1 b.1 := by
    rw [show linePoint a.1.im x =
      (x : ℂ) + a.1.im * Complex.I by rfl,
      fct_horizontal_point_mem_openSegment_iff hab.1 hab.2.1,
      openSegment_eq_Ioo' habRe]
    exact hx
  have point_mem_cd {x : ℝ} (hx : x ∈ Ioo clo chi) :
      linePoint a.1.im x ∈ openSegment ℝ c.1 d.1 := by
    rw [show linePoint a.1.im x =
      (x : ℂ) + c.1.im * Complex.I by simp [linePoint, hacIm],
      fct_horizontal_point_mem_openSegment_iff hcd.1 hcd.2.1,
      openSegment_eq_Ioo' hcdRe]
    exact hx
  have halo : alo = clo := by
    apply le_antisymm
    · by_contra hnot
      have hcloalo : clo < alo := lt_of_not_ge hnot
      have haloChi : alo < chi := lt_trans hpabRe.1 hpcdRe.2
      exact (hcd.2.2 (point_mem_cd ⟨hcloalo, haloChi⟩)).2 lowerA_vertex
    · by_contra hnot
      have haloclo : alo < clo := lt_of_not_ge hnot
      have hcloAhi : clo < ahi := lt_trans hpcdRe.1 hpabRe.2
      exact (hab.2.2 (point_mem_ab ⟨haloclo, hcloAhi⟩)).2 lowerC_vertex
  have hahi : ahi = chi := by
    apply le_antisymm
    · by_contra hnot
      have hchiahi : chi < ahi := lt_of_not_ge hnot
      have haloChi : alo < chi := lt_trans hpabRe.1 hpcdRe.2
      exact (hab.2.2 (point_mem_ab ⟨haloChi, hchiahi⟩)).2 upperC_vertex
    · by_contra hnot
      have hahichi : ahi < chi := lt_of_not_ge hnot
      have hcloAhi : clo < ahi := lt_trans hpcdRe.1 hpabRe.2
      exact (hcd.2.2 (point_mem_cd ⟨hcloAhi, hahichi⟩)).2 upperA_vertex
  have halo' : min a.1.re b.1.re = min c.1.re d.1.re := by
    simpa only [alo, clo] using halo
  have hahi' : max a.1.re b.1.re = max c.1.re d.1.re := by
    simpa only [ahi, chi] using hahi
  ext z
  constructor
  · intro hz
    have hzIm := fct_im_eq_of_mem_openSegment_horizontal hab.2.1 hz
    have hzRe := fct_re_mem_openSegment_of_mem hz
    rw [openSegment_eq_Ioo' habRe] at hzRe
    have hline : (z.re : ℂ) + c.1.im * Complex.I = z := by
      apply Complex.ext <;> simp [hzIm, hacIm]
    rw [← hline, fct_horizontal_point_mem_openSegment_iff hcd.1 hcd.2.1,
      openSegment_eq_Ioo' hcdRe]
    simpa only [← halo', ← hahi'] using hzRe
  · intro hz
    have hzIm := fct_im_eq_of_mem_openSegment_horizontal hcd.2.1 hz
    have hzRe := fct_re_mem_openSegment_of_mem hz
    rw [openSegment_eq_Ioo' hcdRe] at hzRe
    have hline : (z.re : ℂ) + a.1.im * Complex.I = z := by
      apply Complex.ext <;> simp [hzIm, hacIm]
    rw [← hline, fct_horizontal_point_mem_openSegment_iff hab.1 hab.2.1,
      openSegment_eq_Ioo' habRe]
    simpa only [halo', hahi'] using hzRe

private theorem target11_full_intrinsicHorizontalSide
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b) :
    IsIntrinsicHorizontalSide D.deformedRegion
      ⟨D.planarHomeomorph a.1, by
        rw [D.vertices_image]
        exact ⟨a.1, a.2, rfl⟩⟩
      ⟨D.planarHomeomorph b.1, by
        rw [D.vertices_image]
        exact ⟨b.1, b.2, rfl⟩⟩ := by
  refine ⟨fun h ↦ hside.1 (D.planarHomeomorph.injective h), ?_, ?_⟩
  · change (D.planarHomeomorph a.1).im = (D.planarHomeomorph b.1).im
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp [hside.2.1]
  · intro z hz
    have hzimage : z ∈ D.planarHomeomorph '' openSegment ℝ a.1 b.1 := by
      rw [D.image_openSegment_of_axisAligned a.1 b.1 (Or.inr hside.2.1)]
      exact hz
    obtain ⟨q, hq, rfl⟩ := hzimage
    have hqside := hside.2.2 hq
    constructor
    · rw [D.deformedRegion.frontier_openCarrier_eq_frontier_support.symm,
        D.frontier_image]
      refine ⟨q, ?_, rfl⟩
      rw [C.region.frontier_openCarrier_eq_frontier_support]
      exact hqside.1
    · intro hvertex
      rw [D.vertices_image] at hvertex
      obtain ⟨q', hq'vertex, hq'eq⟩ := hvertex
      have hqq' : q = q' := D.planarHomeomorph.injective hq'eq.symm
      exact hqside.2 (hqq' ▸ hq'vertex)

private theorem target11_source_side_eq_of_same_owner_target_meet
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (u : Tiling.Plane) (a b c d : ↥C.region.vertices)
    (hab : IsIntrinsicHorizontalSide C.region a b)
    (hcd : IsIntrinsicHorizontalSide C.region c d)
    (hmeet :
      (openSegment ℝ (D.planarHomeomorph a.1 + u)
          (D.planarHomeomorph b.1 + u) ∩
        openSegment ℝ (D.planarHomeomorph c.1 + u)
          (D.planarHomeomorph d.1 + u)).Nonempty) :
    openSegment ℝ a.1 b.1 = openSegment ℝ c.1 d.1 := by
  obtain ⟨p, hpab, hpcd⟩ := hmeet
  have hpab' : p - u ∈ openSegment ℝ
      (D.planarHomeomorph a.1) (D.planarHomeomorph b.1) := by
    have hp : p ∈ u +ᵥ openSegment ℝ
        (D.planarHomeomorph a.1) (D.planarHomeomorph b.1) := by
      rw [vadd_openSegment ℝ]
      simpa [vadd_eq_add, add_comm] using hpab
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hp
  have hpcd' : p - u ∈ openSegment ℝ
      (D.planarHomeomorph c.1) (D.planarHomeomorph d.1) := by
    have hp : p ∈ u +ᵥ openSegment ℝ
        (D.planarHomeomorph c.1) (D.planarHomeomorph d.1) := by
      rw [vadd_openSegment ℝ]
      simpa [vadd_eq_add, add_comm] using hpcd
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hp
  have htargetEq : openSegment ℝ (D.planarHomeomorph a.1)
      (D.planarHomeomorph b.1) =
      openSegment ℝ (D.planarHomeomorph c.1)
        (D.planarHomeomorph d.1) := by
    exact target11_intrinsicHorizontalSide_eq_of_openSegments_meet
      (target11_full_intrinsicHorizontalSide D a b hab)
      (target11_full_intrinsicHorizontalSide D c d hcd)
      ⟨p - u, hpab', hpcd'⟩
  ext z
  constructor
  · intro hz
    have hzD : D.planarHomeomorph z ∈
        openSegment ℝ (D.planarHomeomorph a.1)
          (D.planarHomeomorph b.1) := by
      rw [← D.image_openSegment_of_axisAligned a.1 b.1 (Or.inr hab.2.1)]
      exact ⟨z, hz, rfl⟩
    rw [htargetEq, ← D.image_openSegment_of_axisAligned c.1 d.1
      (Or.inr hcd.2.1)] at hzD
    obtain ⟨w, hw, hwz⟩ := hzD
    exact D.planarHomeomorph.injective hwz ▸ hw
  · intro hz
    have hzD : D.planarHomeomorph z ∈
        openSegment ℝ (D.planarHomeomorph c.1)
          (D.planarHomeomorph d.1) := by
      rw [← D.image_openSegment_of_axisAligned c.1 d.1 (Or.inr hcd.2.1)]
      exact ⟨z, hz, rfl⟩
    rw [← htargetEq, ← D.image_openSegment_of_axisAligned a.1 b.1
      (Or.inr hab.2.1)] at hzD
    obtain ⟨w, hw, hwz⟩ := hzD
    exact D.planarHomeomorph.injective hwz ▸ hw

private theorem target11_owner_eq_of_three_horizontal_sides
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    {y x : ℝ}
    (u l t : ↥T) (hul : u ≠ l)
    (a b a' b' c d : ↥K.vertices)
    (hab : IsIntrinsicHorizontalSide K a b)
    (ha'b' : IsIntrinsicHorizontalSide K a' b')
    (hcd : IsIntrinsicHorizontalSide K c d)
    (hxu : linePoint y x ∈ openSegment ℝ
      (a.1 + (u.1 : Tiling.Plane)) (b.1 + (u.1 : Tiling.Plane)))
    (hxl : linePoint y x ∈ openSegment ℝ
      (a'.1 + (l.1 : Tiling.Plane)) (b'.1 + (l.1 : Tiling.Plane)))
    (hxt : linePoint y x ∈ openSegment ℝ
      (c.1 + (t.1 : Tiling.Plane)) (d.1 + (t.1 : Tiling.Plane))) :
    t = u ∨ t = l := by
  obtain ⟨du, hdu, hu⟩ :=
    seam_placed_horizontal_side_local_uniform_germ u a b hab hxu
  obtain ⟨dl, hdl, hl⟩ :=
    seam_placed_horizontal_side_local_uniform_germ l a' b' ha'b' hxl
  obtain ⟨dt, hdt, ht⟩ :=
    seam_placed_horizontal_side_local_uniform_germ t c d hcd hxt
  have upperOwnersEq (t0 t1 : ↥T) {δ0 δ1 : ℝ}
        (hδ0 : 0 < δ0) (hδ1 : 0 < δ1)
        (h0 : ∀ z : ℝ, |z - x| < δ0 → ∀ h : ℝ,
          0 < h → h < δ0 →
            linePoint (y + h) z ∈ (t0.1 : Tiling.Plane) +ᵥ K.openCarrier)
        (h1 : ∀ z : ℝ, |z - x| < δ1 → ∀ h : ℝ,
          0 < h → h < δ1 →
            linePoint (y + h) z ∈ (t1.1 : Tiling.Plane) +ᵥ K.openCarrier) :
        t0 = t1 := by
      by_contra hne
      let h : ℝ := min (δ0 / 2) (δ1 / 2)
      have hh : 0 < h := lt_min (half_pos hδ0) (half_pos hδ1)
      have hh0 : h < δ0 := (min_le_left _ _).trans_lt (half_lt_self hδ0)
      have hh1 : h < δ1 := (min_le_right _ _).trans_lt (half_lt_self hδ1)
      have hp0 := h0 x (by simpa using hδ0) h hh hh0
      have hp1 := h1 x (by simpa using hδ1) h hh hh1
      have hdisj := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        t0.2 t1.2 (by intro hval; exact hne (Subtype.ext hval))
      exact Set.disjoint_left.1 hdisj hp0 hp1
  have lowerOwnersEq (t0 t1 : ↥T) {δ0 δ1 : ℝ}
        (hδ0 : 0 < δ0) (hδ1 : 0 < δ1)
        (h0 : ∀ z : ℝ, |z - x| < δ0 → ∀ h : ℝ,
          0 < h → h < δ0 →
            linePoint (y - h) z ∈ (t0.1 : Tiling.Plane) +ᵥ K.openCarrier)
        (h1 : ∀ z : ℝ, |z - x| < δ1 → ∀ h : ℝ,
          0 < h → h < δ1 →
            linePoint (y - h) z ∈ (t1.1 : Tiling.Plane) +ᵥ K.openCarrier) :
        t0 = t1 := by
      by_contra hne
      let h : ℝ := min (δ0 / 2) (δ1 / 2)
      have hh : 0 < h := lt_min (half_pos hδ0) (half_pos hδ1)
      have hh0 : h < δ0 := (min_le_left _ _).trans_lt (half_lt_self hδ0)
      have hh1 : h < δ1 := (min_le_right _ _).trans_lt (half_lt_self hδ1)
      have hp0 := h0 x (by simpa using hδ0) h hh hh0
      have hp1 := h1 x (by simpa using hδ1) h hh hh1
      have hdisj := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        t0.2 t1.2 (by intro hval; exact hne (Subtype.ext hval))
      exact Set.disjoint_left.1 hdisj hp0 hp1
  rcases hu with huU | huL <;>
    rcases hl with hlU | hlL <;>
      rcases ht with htU | htL
  · exact False.elim (hul (upperOwnersEq u l hdu hdl huU hlU))
  · exact False.elim (hul (upperOwnersEq u l hdu hdl huU hlU))
  · exact Or.inl (upperOwnersEq t u hdt hdu htU huU)
  · exact Or.inr (lowerOwnersEq t l hdt hdl htL hlL)
  · exact Or.inr (upperOwnersEq t l hdt hdl htU hlU)
  · exact Or.inl (lowerOwnersEq t u hdt hdu htL huL)
  · exact False.elim (hul (lowerOwnersEq u l hdu hdl huL hlL))
  · exact False.elim (hul (lowerOwnersEq u l hdu hdl huL hlL))

private theorem target11_horizontal_endpoint_mem_cutSet
    {K : Region} {T : Set Tiling.Plane} {y : ℝ}
    (t : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b)
    (hy : y = (a.1 + (t.1 : Tiling.Plane)).im) :
    (a.1 + (t.1 : Tiling.Plane)).re ∈ horizontalLineCutSet K T y := by
  refine ⟨{
    center := t
    v := a
    w := b
    side := ⟨hside.1, Or.inr hside.2.1, hside.2.2⟩
    x_coordinate := Or.inl rfl
    line_meets_side := ?_ }⟩
  have heq : linePoint y (a.1 + (t.1 : Tiling.Plane)).re =
      a.1 + (t.1 : Tiling.Plane) := by
    apply Complex.ext <;> simp [linePoint, hy]
  rw [heq]
  exact left_mem_segment ℝ _ _

private theorem target11_openCarrier_not_mem_horizontal_side
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    (openOwner sideOwner : ↥T) (a b : ↥K.vertices)
    (hside : IsIntrinsicHorizontalSide K a b) {p : Tiling.Plane}
    (hpOpen : p ∈ (openOwner.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hpSide : p ∈ openSegment ℝ
      (a.1 + (sideOwner.1 : Tiling.Plane))
      (b.1 + (sideOwner.1 : Tiling.Plane))) : False := by
  have hpFront : p ∈ frontier
      ((sideOwner.1 : Tiling.Plane) +ᵥ K.support) := by
    have hsubset : openSegment ℝ
        (a.1 + (sideOwner.1 : Tiling.Plane))
        (b.1 + (sideOwner.1 : Tiling.Plane)) ⊆
        frontier ((sideOwner.1 : Tiling.Plane) +ᵥ K.support) := by
      rw [show a.1 + (sideOwner.1 : Tiling.Plane) =
          (sideOwner.1 : Tiling.Plane) +ᵥ a.1 by simp [add_comm],
        show b.1 + (sideOwner.1 : Tiling.Plane) =
          (sideOwner.1 : Tiling.Plane) +ᵥ b.1 by simp [add_comm],
        ← vadd_openSegment ℝ, Tiling.AxisParallel.frontier_vadd_eq]
      rintro _ ⟨q, hq, rfl⟩
      exact ⟨q, (hside.2.2 hq).1, rfl⟩
    exact hsubset hpSide
  by_cases heq : openOwner = sideOwner
  · subst sideOwner
    apply hpFront.2
    rw [interior_vadd]
    exact hpOpen
  · have hpClosure : p ∈ closure
        ((sideOwner.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change p ∈ (sideOwner.1 : Tiling.Plane) +ᵥ closure K.openCarrier
      rw [show closure K.openCarrier = K.support from by
        change closure (interior K.support) = K.support
        exact K.isPolygonal.closure_interior]
      exact (K.isPolygonal.isClosed.vadd
        (sideOwner.1 : Tiling.Plane)).closure_eq ▸ frontier_subset_closure hpFront
    have hopen : IsOpen
        ((openOwner.1 : Tiling.Plane) +ᵥ K.openCarrier) :=
      isOpen_interior.vadd _
    obtain ⟨q, hqSide, hqOpen⟩ :=
      mem_closure_iff.mp hpClosure _ hopen hpOpen
    have hdisj := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      openOwner.2 sideOwner.2 (by
        intro hval
        exact heq (Subtype.ext hval))
    exact Set.disjoint_left.1 hdisj hqSide hqOpen

private theorem target11_first_side_point_to_full
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (t : ↥C.centres) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b)
    {y x : ℝ}
    (hp : linePoint y x ∈ openSegment ℝ
      (D.firstPlanarHomeomorph a.1 + P.firstCenters t)
      (D.firstPlanarHomeomorph b.1 + P.firstCenters t)) :
    linePoint (D.planarHomeomorph a.1 + P.fullCenters t).im x ∈
      openSegment ℝ
        (D.planarHomeomorph a.1 + P.fullCenters t)
        (D.planarHomeomorph b.1 + P.fullCenters t) := by
  have hfirstNe : D.firstPlanarHomeomorph a.1 + P.firstCenters t ≠
      D.firstPlanarHomeomorph b.1 + P.firstCenters t := by
    intro h
    exact hside.1 (D.firstPlanarHomeomorph.injective (add_right_cancel h))
  have hfirstIm :
      (D.firstPlanarHomeomorph a.1 + P.firstCenters t).im =
        (D.firstPlanarHomeomorph b.1 + P.firstCenters t).im := by
    rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
    rw [hside.2.1]
  have hpRe := fct_re_mem_openSegment_of_mem hp
  have hfullNe : D.planarHomeomorph a.1 + P.fullCenters t ≠
      D.planarHomeomorph b.1 + P.fullCenters t := by
    intro h
    exact hside.1 (D.planarHomeomorph.injective (add_right_cancel h))
  have hfullIm :
      (D.planarHomeomorph a.1 + P.fullCenters t).im =
        (D.planarHomeomorph b.1 + P.fullCenters t).im := by
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
    rw [hside.2.1]
  have haRe : (D.firstPlanarHomeomorph a.1 + P.firstCenters t).re =
      (D.planarHomeomorph a.1 + P.fullCenters t).re := by
    rw [D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply,
      P.firstCenters_apply, P.fullCenters_apply]
    simp [mapFirstPoint, mapPoint, ApproximationContext.centrePoint]
  have hbRe : (D.firstPlanarHomeomorph b.1 + P.firstCenters t).re =
      (D.planarHomeomorph b.1 + P.fullCenters t).re := by
    rw [D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply,
      P.firstCenters_apply, P.fullCenters_apply]
    simp [mapFirstPoint, mapPoint, ApproximationContext.centrePoint]
  rw [openSegment_eq_Ioo' (by
    intro h
    exact hfirstNe (Complex.ext h hfirstIm))] at hpRe
  rw [show linePoint (D.planarHomeomorph a.1 + P.fullCenters t).im x =
      (x : ℂ) + (D.planarHomeomorph a.1 + P.fullCenters t).im * Complex.I by
        rfl,
    fct_horizontal_point_mem_openSegment_iff hfullNe hfullIm,
    openSegment_eq_Ioo' (by
      intro h
      exact hfullNe (Complex.ext h hfullIm)), ← haRe, ← hbRe]
  simpa [linePoint] using hpRe

private theorem target11_full_side_point_to_first
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (t : ↥C.centres) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b)
    {y x : ℝ}
    (hp : linePoint y x ∈ openSegment ℝ
      (D.planarHomeomorph a.1 + P.fullCenters t)
      (D.planarHomeomorph b.1 + P.fullCenters t)) :
    linePoint (a.1 + (t.1 : Tiling.Plane)).im x ∈
      openSegment ℝ
        (D.firstPlanarHomeomorph a.1 + P.firstCenters t)
        (D.firstPlanarHomeomorph b.1 + P.firstCenters t) := by
  have hfullNe : D.planarHomeomorph a.1 + P.fullCenters t ≠
      D.planarHomeomorph b.1 + P.fullCenters t := by
    intro h
    exact hside.1 (D.planarHomeomorph.injective (add_right_cancel h))
  have hfullIm :
      (D.planarHomeomorph a.1 + P.fullCenters t).im =
        (D.planarHomeomorph b.1 + P.fullCenters t).im := by
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
    rw [hside.2.1]
  have hpRe := fct_re_mem_openSegment_of_mem hp
  have hfirstNe : D.firstPlanarHomeomorph a.1 + P.firstCenters t ≠
      D.firstPlanarHomeomorph b.1 + P.firstCenters t := by
    intro h
    exact hside.1 (D.firstPlanarHomeomorph.injective (add_right_cancel h))
  have hfirstIm :
      (D.firstPlanarHomeomorph a.1 + P.firstCenters t).im =
        (D.firstPlanarHomeomorph b.1 + P.firstCenters t).im := by
    rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
    rw [hside.2.1]
  have hfirstHeight :
      (D.firstPlanarHomeomorph a.1 + P.firstCenters t).im =
        (a.1 + (t.1 : Tiling.Plane)).im := by
    rw [D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  have haRe : (D.firstPlanarHomeomorph a.1 + P.firstCenters t).re =
      (D.planarHomeomorph a.1 + P.fullCenters t).re := by
    rw [D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply,
      P.firstCenters_apply, P.fullCenters_apply]
    simp [mapFirstPoint, mapPoint, ApproximationContext.centrePoint]
  have hbRe : (D.firstPlanarHomeomorph b.1 + P.firstCenters t).re =
      (D.planarHomeomorph b.1 + P.fullCenters t).re := by
    rw [D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply,
      P.firstCenters_apply, P.fullCenters_apply]
    simp [mapFirstPoint, mapPoint, ApproximationContext.centrePoint]
  rw [openSegment_eq_Ioo' (by
    intro h
    exact hfullNe (Complex.ext h hfullIm))] at hpRe
  rw [show linePoint (a.1 + (t.1 : Tiling.Plane)).im x =
      (x : ℂ) +
        (D.firstPlanarHomeomorph a.1 + P.firstCenters t).im * Complex.I by
        apply Complex.ext <;> simp [linePoint, hfirstHeight],
    fct_horizontal_point_mem_openSegment_iff hfirstNe hfirstIm,
    openSegment_eq_Ioo' (by
      intro h
      exact hfirstNe (Complex.ext h hfirstIm)), haRe, hbRe]
  simpa [linePoint] using hpRe

private theorem target11_full_height_eq
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (s t : ↥C.centres) (a a' : ↥C.region.vertices)
    (hsource : (a.1 + (s.1 : Tiling.Plane)).im =
      (a'.1 + (t.1 : Tiling.Plane)).im) :
    (D.planarHomeomorph a.1 + P.fullCenters s).im =
      (D.planarHomeomorph a'.1 + P.fullCenters t).im := by
  rw [D.vertex_agreement a.1 a.2, D.vertex_agreement a'.1 a'.2,
    P.fullCenters_apply s, P.fullCenters_apply t]
  let xa : C.coordinateSpace :=
    ⟨a.1.im, C.vertex_im_mem a.1 a.2⟩
  let xs : C.coordinateSpace :=
    ⟨s.1.im, C.centre_im_mem s.1 s.2⟩
  let xa' : C.coordinateSpace :=
    ⟨a'.1.im, C.vertex_im_mem a'.1 a'.2⟩
  let xt : C.coordinateSpace :=
    ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
  have hcoord : xa + xs = xa' + xt := by
    apply Subtype.ext
    simpa only [xa, xs, xa', xt, Submodule.coe_add, Complex.add_im] using hsource
  have hmap := congrArg (fun z : C.coordinateSpace => mapScalar phi z) hcoord
  change (phi (xa + xs) : ℝ) = (phi (xa' + xt) : ℝ) at hmap
  rw [map_add, map_add] at hmap
  simpa only [mapPoint, mapScalar, ApproximationContext.vertexPoint,
    ApproximationContext.centrePoint, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    zero_mul, mul_one, zero_add, add_zero, Rat.cast_add] using hmap

private theorem target11_openCarrier_not_mem_frontier
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T univ)
    (openOwner sideOwner : ↥T) {p : Tiling.Plane}
    (hpOpen : p ∈ (openOwner.1 : Tiling.Plane) +ᵥ K.openCarrier)
    (hpFront : p ∈ frontier
      ((sideOwner.1 : Tiling.Plane) +ᵥ K.support)) : False := by
  by_cases heq : openOwner = sideOwner
  · subst sideOwner
    apply hpFront.2
    rw [interior_vadd]
    exact hpOpen
  · have hpClosure : p ∈ closure
        ((sideOwner.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change p ∈ (sideOwner.1 : Tiling.Plane) +ᵥ closure K.openCarrier
      rw [show closure K.openCarrier = K.support from by
        change closure (interior K.support) = K.support
        exact K.isPolygonal.closure_interior]
      exact (K.isPolygonal.isClosed.vadd
        (sideOwner.1 : Tiling.Plane)).closure_eq ▸ frontier_subset_closure hpFront
    have hopen : IsOpen
        ((openOwner.1 : Tiling.Plane) +ᵥ K.openCarrier) :=
      isOpen_interior.vadd _
    obtain ⟨q, hqOpen, hqSide⟩ :=
      mem_closure_iff.mp hpClosure _ hopen hpOpen
    have hdisj := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      openOwner.2 sideOwner.2 (by
        intro hval
        exact heq (Subtype.ext hval))
    exact Set.disjoint_left.1 hdisj hqOpen hqSide

private theorem target11_first_side_mem_frontier
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (t : ↥C.centres) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b)
    {p : Tiling.Plane}
    (hp : p ∈ openSegment ℝ
      (D.firstPlanarHomeomorph a.1 + P.firstCenters t)
      (D.firstPlanarHomeomorph b.1 + P.firstCenters t)) :
    p ∈ frontier ((P.firstCenters t : Tiling.Plane) +ᵥ D.firstRegion.support) := by
  let z : Tiling.Plane := p - P.firstCenters t
  have hz : z ∈ openSegment ℝ (D.firstPlanarHomeomorph a.1)
      (D.firstPlanarHomeomorph b.1) := by
    have hp' : p ∈ (P.firstCenters t : Tiling.Plane) +ᵥ
        openSegment ℝ (D.firstPlanarHomeomorph a.1)
          (D.firstPlanarHomeomorph b.1) := by
      rw [vadd_openSegment ℝ]
      simpa [vadd_eq_add, add_comm] using hp
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp'
    simpa [z, vadd_eq_add, sub_eq_add_neg, add_comm] using hp'
  let q : Tiling.Plane := D.firstPlanarHomeomorph.symm z
  have hqmap : D.firstPlanarHomeomorph q = z :=
    D.firstPlanarHomeomorph.apply_symm_apply z
  have habRe : a.1.re ≠ b.1.re := by
    intro h
    exact hside.1 (Complex.ext h hside.2.1)
  have htargetRe : (D.firstPlanarHomeomorph a.1).re ≠
      (D.firstPlanarHomeomorph b.1).re := by
    intro h
    apply habRe
    apply D.firstHomeomorph.injective
    simpa [D.firstPlanarHomeomorph_apply] using h
  have hzRe := fct_re_mem_openSegment_of_mem hz
  rw [openSegment_eq_Ioo' htargetRe] at hzRe
  have hmapRe : D.firstHomeomorph q.re = z.re := by
    calc
      D.firstHomeomorph q.re = (D.firstPlanarHomeomorph q).re := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      _ = z.re := congrArg Complex.re hqmap
  have haRe : (D.firstPlanarHomeomorph a.1).re =
      D.firstHomeomorph a.1.re := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hbRe : (D.firstPlanarHomeomorph b.1).re =
      D.firstHomeomorph b.1.re := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hqRe : q.re ∈ Ioo (min a.1.re b.1.re) (max a.1.re b.1.re) := by
    rw [haRe, hbRe] at hzRe
    rcases lt_or_gt_of_ne habRe with habLt | hbaLt
    · rw [min_eq_left habLt.le, max_eq_right habLt.le]
      rw [min_eq_left (D.firstHomeomorph_strictMono.monotone habLt.le),
        max_eq_right (D.firstHomeomorph_strictMono.monotone habLt.le)] at hzRe
      exact ⟨D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.1),
        D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.2)⟩
    · rw [min_eq_right hbaLt.le, max_eq_left hbaLt.le]
      rw [min_eq_right (D.firstHomeomorph_strictMono.monotone hbaLt.le),
        max_eq_left (D.firstHomeomorph_strictMono.monotone hbaLt.le)] at hzRe
      exact ⟨D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.1),
        D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.2)⟩
  have hqIm : q.im = a.1.im := by
    have hzIm := fct_im_eq_of_mem_openSegment_horizontal (by
      rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
      simp [hside.2.1]) hz
    have hmapIm := congrArg Complex.im hqmap
    rw [D.firstPlanarHomeomorph_apply] at hmapIm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one,
      zero_add] at hmapIm
    rw [D.firstPlanarHomeomorph_apply] at hzIm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one,
      zero_add] at hzIm
    linarith
  have hq : q ∈ openSegment ℝ a.1 b.1 := by
    have hline : (q.re : ℂ) + a.1.im * Complex.I = q := by
      apply Complex.ext <;> simp [hqIm]
    rw [← hline, fct_horizontal_point_mem_openSegment_iff hside.1 hside.2.1,
      openSegment_eq_Ioo' habRe]
    exact hqRe
  have hqFront : q ∈ frontier C.region.openCarrier := by
    rw [C.region.frontier_openCarrier_eq_frontier_support]
    exact (hside.2.2 hq).1
  have hzFront : z ∈ frontier D.firstRegion.openCarrier := by
    rw [D.firstRegion_openCarrier,
      ← D.firstPlanarHomeomorph.image_frontier C.region.openCarrier]
    exact ⟨q, hqFront, hqmap⟩
  rw [D.firstRegion.frontier_openCarrier_eq_frontier_support] at hzFront
  rw [Tiling.AxisParallel.frontier_vadd_eq]
  refine ⟨z, hzFront, ?_⟩
  simp [z, vadd_eq_add]

private theorem firstStage_targetLabelledHorizontalOverlap_reflected :
    (∀ (C : ApproximationContext.{0})
    (_hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (Acrit : FiniteTransportCriticalAlphabet C),
    (∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1) →
    ∀ (s t : ↥C.centres) (a b a' b' : ↥C.region.vertices),
      IsIntrinsicHorizontalSide C.region a b →
      IsIntrinsicHorizontalSide C.region a' b' →
      (a.1 + (s.1 : Tiling.Plane)).im =
        (a'.1 + (t.1 : Tiling.Plane)).im →
      ProperOpenSideOverlap
        (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
        (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
        (P.fullCenters s) (P.fullCenters t) →
      ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1) := by
  intro C hTile phi D P Acrit hsign s t a b a' b'
    hside hside' hsourceHeight htargetOverlap
  let y : ℝ := (a.1 + (s.1 : Tiling.Plane)).im
  let ea : ℝ := (a.1 + (s.1 : Tiling.Plane)).re
  let eb : ℝ := (b.1 + (s.1 : Tiling.Plane)).re
  let ea' : ℝ := (a'.1 + (t.1 : Tiling.Plane)).re
  let eb' : ℝ := (b'.1 + (t.1 : Tiling.Plane)).re
  let leftBound : ℝ := min (min ea eb) (min ea' eb')
  let rightBound : ℝ := max (max ea eb) (max ea' eb')
  have hLeftEa : leftBound ≤ ea :=
    (min_le_left _ _).trans (min_le_left _ _)
  have hLeftEb : leftBound ≤ eb :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hEaRight : ea ≤ rightBound :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hEbRight : eb ≤ rightBound :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hBounds : leftBound ≤ rightBound := hLeftEa.trans hEaRight
  obtain ⟨code⟩ := endpointAlignedLineCode_exists hTile y leftBound rightBound hBounds
  have heaCut : ea ∈ horizontalLineCutSet C.region C.centres y := by
    apply target11_horizontal_endpoint_mem_cutSet s a b hside
    rfl
  have hebCut : eb ∈ horizontalLineCutSet C.region C.centres y := by
    apply target11_horizontal_endpoint_mem_cutSet s b a
      ⟨hside.1.symm, hside.2.1.symm, by
        simpa only [openSegment_symm] using hside.2.2⟩
    simp [y, hside.2.1]
  have heaIcc : ea ∈ Icc code.qLeft code.qRight := by
    exact ⟨(code.left_of.trans_le hLeftEa).le,
      (hEaRight.trans_lt code.right_of).le⟩
  have hebIcc : eb ∈ Icc code.qLeft code.qRight := by
    exact ⟨(code.left_of.trans_le hLeftEb).le,
      (hEbRight.trans_lt code.right_of).le⟩
  have heaMem : ea ∈ code.cuts := code.cuts_complete ⟨heaCut, heaIcc⟩
  have hebMem : eb ∈ code.cuts := code.cuts_complete ⟨hebCut, hebIcc⟩
  let qa : ↥code.cuts := ⟨ea, heaMem⟩
  let qb : ↥code.cuts := ⟨eb, hebMem⟩
  obtain ⟨transport⟩ := firstStageEndpointAlignedLineCode_transport_exists
    C hTile phi D P Acrit hsign code
  have hmapA : transport.mappedCut qa =
      (D.planarHomeomorph a.1 + P.fullCenters s).re := by
    calc
      transport.mappedCut qa = mapScalar phi (transport.cutLift qa) :=
        transport.mappedCut_formula qa
      _ = D.firstHomeomorph a.1.re +
          (mapFirstPoint phi (C.centrePoint s.1 s.2)).re := by
        apply target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D a.1 a.2 s ea (transport.cutLift qa) (transport.cutLift_coe qa)
        rfl
      _ = (D.planarHomeomorph a.1 + P.fullCenters s).re := by
        rw [D.planarHomeomorph_apply, P.fullCenters_apply]
        simp [mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  have hmapB : transport.mappedCut qb =
      (D.planarHomeomorph b.1 + P.fullCenters s).re := by
    calc
      transport.mappedCut qb = mapScalar phi (transport.cutLift qb) :=
        transport.mappedCut_formula qb
      _ = D.firstHomeomorph b.1.re +
          (mapFirstPoint phi (C.centrePoint s.1 s.2)).re := by
        apply target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
          D b.1 b.2 s eb (transport.cutLift qb) (transport.cutLift_coe qb)
        rfl
      _ = (D.planarHomeomorph b.1 + P.fullCenters s).re := by
        rw [D.planarHomeomorph_apply, P.fullCenters_apply]
        simp [mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  obtain ⟨u, v, huv, huvIm, huvSubset⟩ := htargetOverlap
  have huvRe : u.re ≠ v.re := by
    intro h
    exact huv (Complex.ext h huvIm)
  have hrealInfinite : (openSegment ℝ u.re v.re).Infinite := by
    rw [openSegment_eq_Ioo' huvRe]
    exact Set.Ioo_infinite (min_lt_max.mpr huvRe)
  have hrangeFinite : (Set.range transport.mappedCut).Finite :=
    Set.finite_range transport.mappedCut
  obtain ⟨x, hxReal, hxNotRange⟩ :=
    (hrealInfinite.sdiff hrangeFinite).nonempty
  have hpUV : linePoint u.im x ∈ openSegment ℝ u v := by
    rw [show linePoint u.im x = (x : ℂ) + u.im * Complex.I by rfl,
      fct_horizontal_point_mem_openSegment_iff huv huvIm]
    exact hxReal
  have hxLabel := huvSubset hpUV
  have hxLabelRe := fct_re_mem_openSegment_of_mem hxLabel.1
  have hlabelNe : D.planarHomeomorph a.1 + P.fullCenters s ≠
      D.planarHomeomorph b.1 + P.fullCenters s := by
    intro h
    exact hside.1 (D.planarHomeomorph.injective (add_right_cancel h))
  rw [openSegment_eq_Ioo' (by
    intro h
    apply hlabelNe
    apply Complex.ext h
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp [hside.2.1])] at hxLabelRe
  have hxLabelRe' : x ∈ Ioo
      (min (D.planarHomeomorph a.1 + P.fullCenters s).re
        (D.planarHomeomorph b.1 + P.fullCenters s).re)
      (max (D.planarHomeomorph a.1 + P.fullCenters s).re
        (D.planarHomeomorph b.1 + P.fullCenters s).re) := by
    simpa [linePoint] using hxLabelRe
  have hleftA : transport.mappedCut
      ⟨code.qLeft, code.left_mem⟩ < transport.mappedCut qa := by
    apply transport.mapped_strictMono
    change code.qLeft < ea
    exact code.left_of.trans_le hLeftEa
  have hleftB : transport.mappedCut
      ⟨code.qLeft, code.left_mem⟩ < transport.mappedCut qb := by
    apply transport.mapped_strictMono
    change code.qLeft < eb
    exact code.left_of.trans_le hLeftEb
  have hrightA : transport.mappedCut qa < transport.mappedCut
      ⟨code.qRight, code.right_mem⟩ := by
    apply transport.mapped_strictMono
    change ea < code.qRight
    exact hEaRight.trans_lt code.right_of
  have hrightB : transport.mappedCut qb < transport.mappedCut
      ⟨code.qRight, code.right_mem⟩ := by
    apply transport.mapped_strictMono
    change eb < code.qRight
    exact hEbRight.trans_lt code.right_of
  have hxMappedBounds : x ∈ Ioo
      (transport.mappedCut ⟨code.qLeft, code.left_mem⟩)
      (transport.mappedCut ⟨code.qRight, code.right_mem⟩) := by
    constructor
    · have hmin : transport.mappedCut ⟨code.qLeft, code.left_mem⟩ <
          min (transport.mappedCut qa) (transport.mappedCut qb) :=
        lt_min hleftA hleftB
      rw [hmapA, hmapB] at hmin
      exact hmin.trans hxLabelRe'.1
    · have hmax : max (transport.mappedCut qa) (transport.mappedCut qb) <
          transport.mappedCut ⟨code.qRight, code.right_mem⟩ :=
        max_lt hrightA hrightB
      rw [hmapA, hmapB] at hmax
      exact hxLabelRe'.2.trans hmax
  obtain ⟨l, r, hlr, hno, hxCell⟩ :=
    transport.mapped_cells_cover x hxMappedBounds hxNotRange
  rcases code.cell_classification l.1 r.1 l.2 r.2 hlr hno with hcross | hseam
  · obtain ⟨X⟩ := hcross
    have hxOpen := transport.crossing_preserved l r hlr hno X x hxCell
    have hxFirstSide : linePoint y x ∈ openSegment ℝ
        (D.firstPlanarHomeomorph a.1 + P.firstCenters s)
        (D.firstPlanarHomeomorph b.1 + P.firstCenters s) := by
      simpa only [y] using target11_full_side_point_to_first D P s a b hside hxLabel.1
    have hxFront := target11_first_side_mem_frontier D P s a b hside hxFirstSide
    exact False.elim (target11_openCarrier_not_mem_frontier P.first_tilesOn
      ⟨P.firstCenters X.center, ⟨X.center, rfl⟩⟩
      ⟨P.firstCenters s, ⟨s, rfl⟩⟩ hxOpen hxFront)
  · obtain ⟨S⟩ := hseam
    have hseamFirst := transport.seam_preserved l r hlr hno S
    have hxUpperFirst := hseamFirst.1 x hxCell
    have hxLowerFirst := hseamFirst.2 x hxCell
    have hxUpperFull := target11_first_side_point_to_full D P S.upperCenter
      S.a S.b S.first_horizontal hxUpperFirst
    have hxLowerFull := target11_first_side_point_to_full D P S.lowerCenter
      S.a' S.b' S.second_horizontal hxLowerFirst
    have hUpperSourceHeight :
        (S.a.1 + (S.upperCenter.1 : Tiling.Plane)).im = y := by
      have hp := S.first_side ((l.1 + r.1) / 2) (by
        constructor <;> linarith [S.left_lt_right])
      have him :
          (S.a.1 + (S.upperCenter.1 : Tiling.Plane)).im =
            (S.b.1 + (S.upperCenter.1 : Tiling.Plane)).im := by
        simp only [Complex.add_im]
        rw [S.first_horizontal.2.1]
      simpa [linePoint, y] using
        (fct_im_eq_of_mem_openSegment_horizontal him hp).symm
    have hLowerSourceHeight :
        (S.a'.1 + (S.lowerCenter.1 : Tiling.Plane)).im = y := by
      have hp := S.second_side ((l.1 + r.1) / 2) (by
        constructor <;> linarith [S.left_lt_right])
      have him :
          (S.a'.1 + (S.lowerCenter.1 : Tiling.Plane)).im =
            (S.b'.1 + (S.lowerCenter.1 : Tiling.Plane)).im := by
        simp only [Complex.add_im]
        rw [S.second_horizontal.2.1]
      simpa [linePoint, y] using
        (fct_im_eq_of_mem_openSegment_horizontal him hp).symm
    let yTarget : ℝ := (D.planarHomeomorph a.1 + P.fullCenters s).im
    have hUpperTargetHeight :
        (D.planarHomeomorph S.a.1 + P.fullCenters S.upperCenter).im = yTarget := by
      apply target11_full_height_eq D P S.upperCenter s S.a a
      simpa only [y] using hUpperSourceHeight.trans (show y =
        (a.1 + (s.1 : Tiling.Plane)).im from rfl)
    have hLowerTargetHeight :
        (D.planarHomeomorph S.a'.1 + P.fullCenters S.lowerCenter).im =
          yTarget := by
      apply target11_full_height_eq D P S.lowerCenter s S.a' a
      simpa only [y] using hLowerSourceHeight.trans (show y =
        (a.1 + (s.1 : Tiling.Plane)).im from rfl)
    have hLabelTargetHeight : u.im = yTarget := by
      have him := fct_im_eq_of_mem_openSegment_horizontal (by
        rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
        simp [hside.2.1]) hxLabel.1
      simpa [linePoint, yTarget] using him
    have hxUpperFull' : linePoint yTarget x ∈ openSegment ℝ
        (D.planarHomeomorph S.a.1 + P.fullCenters S.upperCenter)
        (D.planarHomeomorph S.b.1 + P.fullCenters S.upperCenter) := by
      simpa only [hUpperTargetHeight] using hxUpperFull
    have hxLowerFull' : linePoint yTarget x ∈ openSegment ℝ
        (D.planarHomeomorph S.a'.1 + P.fullCenters S.lowerCenter)
        (D.planarHomeomorph S.b'.1 + P.fullCenters S.lowerCenter) := by
      simpa only [hLowerTargetHeight] using hxLowerFull
    have hxLabelS : linePoint yTarget x ∈ openSegment ℝ
        (D.planarHomeomorph a.1 + P.fullCenters s)
        (D.planarHomeomorph b.1 + P.fullCenters s) := by
      simpa only [hLabelTargetHeight] using hxLabel.1
    have hxLabelT : linePoint yTarget x ∈ openSegment ℝ
        (D.planarHomeomorph a'.1 + P.fullCenters t)
        (D.planarHomeomorph b'.1 + P.fullCenters t) := by
      simpa only [hLabelTargetHeight] using hxLabel.2
    let fullOwner : ↥C.centres → ↥(deformedCenterCarrier P.fullCenters) :=
      fun c ↦ ⟨P.fullCenters c, ⟨c, rfl⟩⟩
    let fullVertex : ↥C.region.vertices → ↥D.deformedRegion.vertices :=
      fun w ↦ ⟨D.planarHomeomorph w.1, by
        rw [D.vertices_image]
        exact ⟨w.1, w.2, rfl⟩⟩
    have hsOwner' := target11_owner_eq_of_three_horizontal_sides
      P.full_tilesOn (fullOwner S.upperCenter) (fullOwner S.lowerCenter)
      (fullOwner s) (by
        intro h
        exact S.centers_ne (P.fullCenters.injective
          (congrArg Subtype.val h)))
      (fullVertex S.a) (fullVertex S.b) (fullVertex S.a') (fullVertex S.b')
      (fullVertex a) (fullVertex b)
      (target11_full_intrinsicHorizontalSide D S.a S.b S.first_horizontal)
      (target11_full_intrinsicHorizontalSide D S.a' S.b' S.second_horizontal)
      (target11_full_intrinsicHorizontalSide D a b hside)
      hxUpperFull' hxLowerFull' hxLabelS
    have htOwner' := target11_owner_eq_of_three_horizontal_sides
      P.full_tilesOn (fullOwner S.upperCenter) (fullOwner S.lowerCenter)
      (fullOwner t) (by
        intro h
        exact S.centers_ne (P.fullCenters.injective
          (congrArg Subtype.val h)))
      (fullVertex S.a) (fullVertex S.b) (fullVertex S.a') (fullVertex S.b')
      (fullVertex a') (fullVertex b')
      (target11_full_intrinsicHorizontalSide D S.a S.b S.first_horizontal)
      (target11_full_intrinsicHorizontalSide D S.a' S.b' S.second_horizontal)
      (target11_full_intrinsicHorizontalSide D a' b' hside')
      hxUpperFull' hxLowerFull' hxLabelT
    have hsOwner : s = S.upperCenter ∨ s = S.lowerCenter := by
      rcases hsOwner' with h | h
      · exact Or.inl (P.fullCenters.injective (congrArg Subtype.val h))
      · exact Or.inr (P.fullCenters.injective (congrArg Subtype.val h))
    have htOwner : t = S.upperCenter ∨ t = S.lowerCenter := by
      rcases htOwner' with h | h
      · exact Or.inl (P.fullCenters.injective (congrArg Subtype.val h))
      · exact Or.inr (P.fullCenters.injective (congrArg Subtype.val h))
    have placedEq {c : ↥C.centres} {v w v' w' : ↥C.region.vertices}
        (heq : openSegment ℝ v.1 w.1 = openSegment ℝ v'.1 w'.1) :
        openSegment ℝ (v.1 + (c.1 : Tiling.Plane))
            (w.1 + (c.1 : Tiling.Plane)) =
          openSegment ℝ (v'.1 + (c.1 : Tiling.Plane))
            (w'.1 + (c.1 : Tiling.Plane)) := by
      rw [show v.1 + (c.1 : Tiling.Plane) = (c.1 : Tiling.Plane) +ᵥ v.1 by
          simp [add_comm],
        show w.1 + (c.1 : Tiling.Plane) = (c.1 : Tiling.Plane) +ᵥ w.1 by
          simp [add_comm],
        show v'.1 + (c.1 : Tiling.Plane) = (c.1 : Tiling.Plane) +ᵥ v'.1 by
          simp [add_comm],
        show w'.1 + (c.1 : Tiling.Plane) = (c.1 : Tiling.Plane) +ᵥ w'.1 by
          simp [add_comm],
        ← vadd_openSegment ℝ, ← vadd_openSegment ℝ, heq]
    have properFromHall
        (hallS : ∀ q ∈ Ioo l.1 r.1, linePoint y q ∈
          openSegment ℝ (a.1 + (s.1 : Tiling.Plane))
            (b.1 + (s.1 : Tiling.Plane)))
        (hallT : ∀ q ∈ Ioo l.1 r.1, linePoint y q ∈
          openSegment ℝ (a'.1 + (t.1 : Tiling.Plane))
            (b'.1 + (t.1 : Tiling.Plane))) :
        ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1 := by
      let q₀ : ℝ := (2 * l.1 + r.1) / 3
      let q₁ : ℝ := (l.1 + 2 * r.1) / 3
      have hq₀ : q₀ ∈ Ioo l.1 r.1 := by
        dsimp [q₀]
        constructor <;> linarith [hlr]
      have hq₁ : q₁ ∈ Ioo l.1 r.1 := by
        dsimp [q₁]
        constructor <;> linarith [hlr]
      have hq₀q₁ : q₀ < q₁ := by
        dsimp [q₀, q₁]
        linarith [hlr]
      refine ⟨linePoint y q₀, linePoint y q₁, ?_, by simp [linePoint], ?_⟩
      · intro h
        have hre := congrArg Complex.re h
        simp [linePoint] at hre
        linarith
      · intro z hz
        have hzRe := fct_re_mem_openSegment_of_mem hz
        have hzRe' : z.re ∈ openSegment ℝ q₀ q₁ := by
          simpa [linePoint] using hzRe
        rw [openSegment_eq_Ioo' hq₀q₁.ne] at hzRe'
        have hzI : z.re ∈ Ioo l.1 r.1 := by
          have hzRe'' : z.re ∈ Ioo q₀ q₁ := by
            simpa only [min_eq_left hq₀q₁.le,
              max_eq_right hq₀q₁.le] using hzRe'
          exact ⟨hq₀.1.trans hzRe''.1, hzRe''.2.trans hq₁.2⟩
        have hzIm := fct_im_eq_of_mem_openSegment_horizontal
          (by simp [linePoint]) hz
        have hzLine : linePoint y z.re = z := by
          apply Complex.ext <;> simp [linePoint, hzIm]
        constructor
        · rw [← hzLine]
          exact hallS z.re hzI
        · rw [← hzLine]
          exact hallT z.re hzI
    rcases hsOwner with hsu | hsl <;> rcases htOwner with htu | htl
    · have hsEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.upperCenter) a b S.a S.b hside S.first_horizontal
        ⟨linePoint yTarget x, by simpa only [hsu] using hxLabelS,
          hxUpperFull'⟩
      have htEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.upperCenter) a' b' S.a S.b hside' S.first_horizontal
        ⟨linePoint yTarget x, by simpa only [htu] using hxLabelT,
          hxUpperFull'⟩
      apply properFromHall
      · intro q hq
        rw [hsu, placedEq hsEq]
        exact S.first_side q hq
      · intro q hq
        rw [htu, placedEq htEq]
        exact S.first_side q hq
    · have hsEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.upperCenter) a b S.a S.b hside S.first_horizontal
        ⟨linePoint yTarget x, by simpa only [hsu] using hxLabelS,
          hxUpperFull'⟩
      have htEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.lowerCenter) a' b' S.a' S.b' hside' S.second_horizontal
        ⟨linePoint yTarget x, by simpa only [htl] using hxLabelT,
          hxLowerFull'⟩
      apply properFromHall
      · intro q hq
        rw [hsu, placedEq hsEq]
        exact S.first_side q hq
      · intro q hq
        rw [htl, placedEq htEq]
        exact S.second_side q hq
    · have hsEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.lowerCenter) a b S.a' S.b' hside S.second_horizontal
        ⟨linePoint yTarget x, by simpa only [hsl] using hxLabelS,
          hxLowerFull'⟩
      have htEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.upperCenter) a' b' S.a S.b hside' S.first_horizontal
        ⟨linePoint yTarget x, by simpa only [htu] using hxLabelT,
          hxUpperFull'⟩
      apply properFromHall
      · intro q hq
        rw [hsl, placedEq hsEq]
        exact S.second_side q hq
      · intro q hq
        rw [htu, placedEq htEq]
        exact S.first_side q hq
    · have hsEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.lowerCenter) a b S.a' S.b' hside S.second_horizontal
        ⟨linePoint yTarget x, by simpa only [hsl] using hxLabelS,
          hxLowerFull'⟩
      have htEq := target11_source_side_eq_of_same_owner_target_meet D
        (P.fullCenters S.lowerCenter) a' b' S.a' S.b' hside' S.second_horizontal
        ⟨linePoint yTarget x, by simpa only [htl] using hxLabelT,
          hxLowerFull'⟩
      apply properFromHall
      · intro q hq
        rw [hsl, placedEq hsEq]
        exact S.second_side q hq
      · intro q hq
        rw [htl, placedEq htEq]
        exact S.second_side q hq

private theorem firstStageVerticalEndpointLift :
    (∀ (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D),
    ∀ᵐ q : ℝ ∂volume,
      ∃ lift : ↥(sliceEndpointSet D.firstRegion
          (deformedCenterCarrier P.firstCenters) Axis.vertical q) →
          C.coordinateSpace,
        (∀ x, (lift x : ℝ) = x.1) ∧
        StrictMono (fun x => mapScalar phi (lift x))) := by
  intro C phi D P
  filter_upwards [
      genericSliceEndpointSet_unbounded D.firstRegion
        (deformedCenterCarrier P.firstCenters) P.first_tilesOn Axis.vertical,
      genericSliceChain_betweenEndpoints_with_endpoints D.firstRegion
        (deformedCenterCarrier P.firstCenters) P.first_tilesOn Axis.vertical]
    with q hends hchains
  have sourceVertex (v : Tiling.Plane) (hv : v ∈ D.firstRegion.vertices) :
      ∃ v₀ ∈ C.region.vertices, D.firstPlanarHomeomorph v₀ = v := by
    rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D] at hv
    simpa only [Set.mem_image] using hv
  have endpoint_mem
      (a : ↥(sliceEndpointSet D.firstRegion
        (deformedCenterCarrier P.firstCenters) Axis.vertical q)) :
      a.1 ∈ C.coordinateSpace := by
    rw [not_bddAbove_iff] at hends
    obtain ⟨b, hb, hab⟩ := hends.1 a.1
    obtain ⟨n, hn, x, owner, hx0, _hxlast, hxchain, _hxendpoints⟩ :=
      hchains a.1 a.2 b hb hab
    obtain ⟨v, _w, hv, _hw, hleft, _hright, _hpositive, _hinside⟩ :=
      hxchain.2 (⟨0, hn⟩ : Fin n)
    obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
    obtain ⟨t, ht⟩ := (owner ⟨0, hn⟩).2
    have howner : P.firstCenters t = (owner ⟨0, hn⟩ : Tiling.Plane) := ht
    have ha : a.1 =
        (D.firstPlanarHomeomorph v₀ + P.firstCenters t).im := by
      calc
        a.1 = x 0 := hx0.symm
        _ = x (⟨0, hn⟩ : Fin n).castSucc := rfl
        _ = Axis.coord Axis.vertical
            (v + (owner ⟨0, hn⟩ : Tiling.Plane)) := hleft
        _ = Axis.coord Axis.vertical
            (D.firstPlanarHomeomorph v₀ + P.firstCenters t) := by
              rw [← hvmap, ← howner]
        _ = (D.firstPlanarHomeomorph v₀ + P.firstCenters t).im := rfl
    rw [ha, D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
    simp only [mapFirstPoint, ApproximationContext.centrePoint,
      Complex.add_im, Complex.mul_im, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
    simpa using C.coordinateSpace.add_mem
      (C.vertex_im_mem v₀ hv₀) (C.centre_im_mem t t.2)
  let lift : ↥(sliceEndpointSet D.firstRegion
      (deformedCenterCarrier P.firstCenters) Axis.vertical q) →
      C.coordinateSpace := fun x ↦ ⟨x.1, endpoint_mem x⟩
  refine ⟨lift, ?_, ?_⟩
  · intro x
    rfl
  · intro a b hab
    obtain ⟨n, hn, x, owner, hx0, hxlast, hxchain, _hxendpoints⟩ :=
      hchains a.1 a.2 b.1 b.2 hab
    have xmem (i : Fin (n + 1)) : x i ∈ C.coordinateSpace := by
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · let j : Fin n := ⟨n - 1, by omega⟩
        obtain ⟨v, w, _hv, hw, _hleft, hright, _hpositive, _hinside⟩ :=
          hxchain.2 j
        obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
        obtain ⟨t, ht⟩ := (owner j).2
        have howner : P.firstCenters t = (owner j : Tiling.Plane) := ht
        rw [show Fin.last n = j.succ by
          apply Fin.ext
          simp [j, Nat.sub_add_cancel hn], hright, Axis.coord,
          ← hwmap, ← howner, D.firstPlanarHomeomorph_apply,
          P.firstCenters_apply]
        simp only [mapFirstPoint, ApproximationContext.centrePoint,
          Complex.add_im, Complex.mul_im, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
        simpa using C.coordinateSpace.add_mem
          (C.vertex_im_mem w₀ hw₀) (C.centre_im_mem t t.2)
      · obtain ⟨v, _w, hv, _hw, hleft, _hright, _hpositive, _hinside⟩ :=
          hxchain.2 j
        obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
        obtain ⟨t, ht⟩ := (owner j).2
        have howner : P.firstCenters t = (owner j : Tiling.Plane) := ht
        rw [hleft, Axis.coord, ← hvmap, ← howner,
          D.firstPlanarHomeomorph_apply, P.firstCenters_apply]
        simp only [mapFirstPoint, ApproximationContext.centrePoint,
          Complex.add_im, Complex.mul_im, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add]
        simpa using C.coordinateSpace.add_mem
          (C.vertex_im_mem v₀ hv₀) (C.centre_im_mem t t.2)
    let xLift : Fin (n + 1) → C.coordinateSpace := fun i ↦
      ⟨x i, xmem i⟩
    have hLift : ∀ i, (xLift i : ℝ) = x i := fun _ ↦ rfl
    have hmono := mappedVerticalFilledChain_strictMono D P q x owner xLift
      hLift hxchain
    have hfirst : xLift 0 = lift a := by
      apply Subtype.ext
      simp [xLift, lift, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [xLift, lift, hxlast]
    change mapScalar phi (lift a) < mapScalar phi (lift b)
    rw [← hfirst, ← hlast]
    have hindex : (0 : Fin (n + 1)) < Fin.last n := hn
    exact hmono hindex

private structure SecondStageOrderFibre
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (q : ℝ) where
  lift : ↥(sliceEndpointSet D.firstRegion
      (deformedCenterCarrier P.firstCenters) Axis.vertical q) → C.coordinateSpace
  lift_coe : ∀ x, (lift x : ℝ) = x.1
  mapped_strictMono : StrictMono (fun x => mapScalar phi (lift x))

private theorem secondStageOrderFibres_ae :
    (∀ (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D),
    ∀ᵐ q : ℝ ∂volume, Nonempty (SecondStageOrderFibre C phi D P q)) := by
  intro C phi D P
  filter_upwards [firstStageVerticalEndpointLift C phi D P] with q hq
  obtain ⟨lift, hlift, hmono⟩ := hq
  exact ⟨⟨lift, hlift, hmono⟩⟩

private theorem target16_first_side_preimage_mem
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b) {z : Tiling.Plane}
    (hz : z ∈ openSegment ℝ (D.firstPlanarHomeomorph a.1)
      (D.firstPlanarHomeomorph b.1)) :
    D.firstPlanarHomeomorph.symm z ∈ openSegment ℝ a.1 b.1 := by
  let p : Tiling.Plane := D.firstPlanarHomeomorph.symm z
  have hpmap : D.firstPlanarHomeomorph p = z :=
    D.firstPlanarHomeomorph.apply_symm_apply z
  have habRe : a.1.re ≠ b.1.re := by
    intro h
    exact hside.1 (Complex.ext h hside.2.1)
  have htargetRe : (D.firstPlanarHomeomorph a.1).re ≠
      (D.firstPlanarHomeomorph b.1).re := by
    intro h
    apply habRe
    apply D.firstHomeomorph.injective
    simpa [D.firstPlanarHomeomorph_apply] using h
  have hzRe := fct_re_mem_openSegment_of_mem hz
  rw [openSegment_eq_Ioo' htargetRe] at hzRe
  have hmapRe : D.firstHomeomorph p.re = z.re := by
    calc
      D.firstHomeomorph p.re = (D.firstPlanarHomeomorph p).re := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      _ = z.re := congrArg Complex.re hpmap
  have haRe : (D.firstPlanarHomeomorph a.1).re =
      D.firstHomeomorph a.1.re := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hbRe : (D.firstPlanarHomeomorph b.1).re =
      D.firstHomeomorph b.1.re := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hpRe : p.re ∈ Ioo (min a.1.re b.1.re) (max a.1.re b.1.re) := by
    rw [haRe, hbRe] at hzRe
    rcases lt_or_gt_of_ne habRe with habLt | hbaLt
    · rw [min_eq_left habLt.le, max_eq_right habLt.le]
      rw [min_eq_left (D.firstHomeomorph_strictMono.monotone habLt.le),
        max_eq_right (D.firstHomeomorph_strictMono.monotone habLt.le)] at hzRe
      exact ⟨D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.1),
        D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.2)⟩
    · rw [min_eq_right hbaLt.le, max_eq_left hbaLt.le]
      rw [min_eq_right (D.firstHomeomorph_strictMono.monotone hbaLt.le),
        max_eq_left (D.firstHomeomorph_strictMono.monotone hbaLt.le)] at hzRe
      exact ⟨D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.1),
        D.firstHomeomorph_strictMono.lt_iff_lt.mp (by
          rw [hmapRe]
          exact hzRe.2)⟩
  have hpIm : p.im = a.1.im := by
    have hzIm := fct_im_eq_of_mem_openSegment_horizontal (by
      rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
      simp [hside.2.1]) hz
    have hmapIm := congrArg Complex.im hpmap
    rw [D.firstPlanarHomeomorph_apply] at hmapIm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one,
      zero_add] at hmapIm
    rw [D.firstPlanarHomeomorph_apply] at hzIm
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, zero_mul, mul_one,
      zero_add] at hzIm
    linarith
  have hline : (p.re : ℂ) + a.1.im * Complex.I = p := by
    apply Complex.ext <;> simp [hpIm]
  change p ∈ openSegment ℝ a.1 b.1
  rw [← hline, fct_horizontal_point_mem_openSegment_iff hside.1 hside.2.1,
    openSegment_eq_Ioo' habRe]
  exact hpRe

private theorem target16_first_intrinsicHorizontalSide
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (a b : ↥C.region.vertices)
    (hside : IsIntrinsicHorizontalSide C.region a b) :
    IsIntrinsicHorizontalSide D.firstRegion
      ⟨D.firstPlanarHomeomorph a.1, by
        rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D]
        exact ⟨a.1, a.2, rfl⟩⟩
      ⟨D.firstPlanarHomeomorph b.1, by
        rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D]
        exact ⟨b.1, b.2, rfl⟩⟩ := by
  refine ⟨fun h ↦ hside.1 (D.firstPlanarHomeomorph.injective h), ?_, ?_⟩
  · change (D.firstPlanarHomeomorph a.1).im =
      (D.firstPlanarHomeomorph b.1).im
    rw [D.firstPlanarHomeomorph_apply, D.firstPlanarHomeomorph_apply]
    simp [hside.2.1]
  · intro z hz
    have hp := target16_first_side_preimage_mem D a b hside hz
    have hpSide := hside.2.2 hp
    constructor
    · rw [D.firstRegion.frontier_openCarrier_eq_frontier_support.symm,
        D.firstRegion_openCarrier,
        ← D.firstPlanarHomeomorph.image_frontier C.region.openCarrier]
      refine ⟨D.firstPlanarHomeomorph.symm z, ?_,
        D.firstPlanarHomeomorph.apply_symm_apply z⟩
      rw [C.region.frontier_openCarrier_eq_frontier_support]
      exact hpSide.1
    · intro hzVertex
      rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D] at hzVertex
      obtain ⟨w, hwVertex, hwEq⟩ := hzVertex
      have hpEq : D.firstPlanarHomeomorph.symm z = w := by
        apply D.firstPlanarHomeomorph.injective
        rw [D.firstPlanarHomeomorph.apply_symm_apply]
        exact hwEq.symm
      exact hpSide.2 (hpEq ▸ hwVertex)

private theorem firstStage_horizontalSide_isVerticalFibreEndpoint :
    ∀ (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (s : ↥C.centres) (a b : ↥C.region.vertices),
    a.1 ≠ b.1 → a.1.im = b.1.im →
    openSegment ℝ a.1 b.1 ⊆ frontier C.region.support \ C.region.vertices →
    ∀ q : ℝ,
      q ∈ openSegment ℝ
        (D.planarHomeomorph a.1 + P.fullCenters s).re
        (D.planarHomeomorph b.1 + P.fullCenters s).re →
      (a.1 + (s.1 : Tiling.Plane)).im ∈
        sliceEndpointSet D.firstRegion
          (deformedCenterCarrier P.firstCenters) Axis.vertical q := by
  intro C phi D P s a b hab habIm habEdge q hq
  let hside : IsIntrinsicHorizontalSide C.region a b := ⟨hab, habIm, habEdge⟩
  let firstOwner : ↥(deformedCenterCarrier P.firstCenters) :=
    ⟨P.firstCenters s, ⟨s, rfl⟩⟩
  let aFirst : ↥D.firstRegion.vertices :=
    ⟨D.firstPlanarHomeomorph a.1, by
      rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D]
      exact ⟨a.1, a.2, rfl⟩⟩
  let bFirst : ↥D.firstRegion.vertices :=
    ⟨D.firstPlanarHomeomorph b.1, by
      rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image D]
      exact ⟨b.1, b.2, rfl⟩⟩
  let y : ℝ := (a.1 + (s.1 : Tiling.Plane)).im
  have hfullNe : D.planarHomeomorph a.1 + P.fullCenters s ≠
      D.planarHomeomorph b.1 + P.fullCenters s := by
    intro h
    exact hab (D.planarHomeomorph.injective (add_right_cancel h))
  have hfullIm :
      (D.planarHomeomorph a.1 + P.fullCenters s).im =
        (D.planarHomeomorph b.1 + P.fullCenters s).im := by
    rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
    simp [habIm]
  have hpFull : linePoint
      (D.planarHomeomorph a.1 + P.fullCenters s).im q ∈
      openSegment ℝ (D.planarHomeomorph a.1 + P.fullCenters s)
        (D.planarHomeomorph b.1 + P.fullCenters s) := by
    rw [show linePoint (D.planarHomeomorph a.1 + P.fullCenters s).im q =
        (q : ℂ) + (D.planarHomeomorph a.1 + P.fullCenters s).im * Complex.I by rfl,
      fct_horizontal_point_mem_openSegment_iff hfullNe hfullIm]
    exact hq
  have hpFirst := target11_full_side_point_to_first D P s a b hside hpFull
  have hpFirst' : linePoint y q ∈ openSegment ℝ
      (D.firstPlanarHomeomorph a.1 + P.firstCenters s)
      (D.firstPlanarHomeomorph b.1 + P.firstCenters s) := by
    simpa only [y] using hpFirst
  have hsideFirst : IsIntrinsicHorizontalSide D.firstRegion aFirst bFirst := by
    exact target16_first_intrinsicHorizontalSide D a b hside
  obtain ⟨delta, hdelta, hgerm⟩ :=
    seam_placed_horizontal_side_local_uniform_germ firstOwner aFirst bFirst
      hsideFirst hpFirst'
  have hpFront := target11_first_side_mem_frontier D P s a b hside hpFirst'
  change y ∈ frontier
    {x : ℝ | slicePoint Axis.vertical q x ∈
      openUnion D.firstRegion (deformedCenterCarrier P.firstCenters)}
  rw [frontier]
  constructor
  · apply Metric.mem_closure_iff.2
    intro epsilon hepsilon
    let h : ℝ := min (delta / 2) (epsilon / 2)
    have hh : 0 < h := by
      dsimp [h]
      positivity
    have hhDelta : h < delta := by
      dsimp [h]
      have := min_le_left (delta / 2) (epsilon / 2)
      linarith
    have hhEpsilon : h < epsilon := by
      dsimp [h]
      have := min_le_right (delta / 2) (epsilon / 2)
      linarith
    rcases hgerm with hplus | hminus
    · refine ⟨y + h, ?_, ?_⟩
      · change slicePoint Axis.vertical q (y + h) ∈
          openUnion D.firstRegion (deformedCenterCarrier P.firstCenters)
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        refine ⟨firstOwner, ?_⟩
        simpa [slicePoint, linePoint] using
          hplus q (by simpa using hdelta) h hh hhDelta
      · simpa [Real.dist_eq, abs_of_pos hh] using hhEpsilon
    · refine ⟨y - h, ?_, ?_⟩
      · change slicePoint Axis.vertical q (y - h) ∈
          openUnion D.firstRegion (deformedCenterCarrier P.firstCenters)
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        refine ⟨firstOwner, ?_⟩
        simpa [slicePoint, linePoint] using
          hminus q (by simpa using hdelta) h hh hhDelta
      · simpa [Real.dist_eq, abs_of_pos hh] using hhEpsilon
  · intro hyInterior
    have hyOpen := interior_subset hyInterior
    change slicePoint Axis.vertical q y ∈
      openUnion D.firstRegion (deformedCenterCarrier P.firstCenters) at hyOpen
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hyOpen
    obtain ⟨openOwner, hpOpen⟩ := hyOpen
    apply target11_openCarrier_not_mem_frontier P.first_tilesOn
      openOwner firstOwner hpOpen
    simpa [slicePoint, linePoint] using hpFront

private theorem target17_endpoint_mapped_eq_fullHeight
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (s : ↥C.centres) (a : ↥C.region.vertices)
    (lift : C.coordinateSpace)
    (hlift : (lift : ℝ) = (a.1 + (s.1 : Tiling.Plane)).im) :
    mapScalar phi lift =
      (D.planarHomeomorph a.1 + P.fullCenters s).im := by
  let xa : C.coordinateSpace := ⟨a.1.im, C.vertex_im_mem a.1 a.2⟩
  let xs : C.coordinateSpace := ⟨s.1.im, C.centre_im_mem s.1 s.2⟩
  have hliftEq : lift = xa + xs := by
    apply Subtype.ext
    simpa only [xa, xs, Submodule.coe_add, Complex.add_im] using hlift
  rw [hliftEq, mapScalar, map_add, D.vertex_agreement a.1 a.2,
    P.fullCenters_apply s]
  simp only [mapPoint, ApproximationContext.vertexPoint,
    ApproximationContext.centrePoint, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
    zero_mul, mul_one, zero_add, add_zero, Rat.cast_add]
  rfl

private theorem targetLabelledHorizontalOverlap_reflectsSourceHeight :
    ∀ (C : ApproximationContext.{0})
    (_hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (s t : ↥C.centres) (a b a' b' : ↥C.region.vertices),
    IsIntrinsicHorizontalSide C.region a b →
    IsIntrinsicHorizontalSide C.region a' b' →
    ProperOpenSideOverlap
      (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
      (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
      (P.fullCenters s) (P.fullCenters t) →
    (a.1 + (s.1 : Tiling.Plane)).im =
      (a'.1 + (t.1 : Tiling.Plane)).im := by
  intro C _hTile phi D P s t a b a' b' hside hside' hOverlap
  rcases hOverlap with ⟨u, v, huv, huvIm, hOverlap⟩
  have huvRe : u.re ≠ v.re := by
    intro h
    exact huv (Complex.ext h huvIm)
  let lo : ℝ := min u.re v.re
  let hi : ℝ := max u.re v.re
  have hlohi : lo < hi := by
    dsimp [lo, hi]
    exact min_lt_max.2 huvRe
  have hmeasure : volume (Ioo lo hi) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hlohi)]
  obtain ⟨q, hqIoo, hqGood⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae hmeasure
      ((secondStageOrderFibres_ae C phi D P).filter_mono ae_restrict_le)
  have hqReal : q ∈ openSegment ℝ u.re v.re := by
    rw [openSegment_eq_Ioo' huvRe]
    exact hqIoo
  have hpUV : linePoint u.im q ∈ openSegment ℝ u v := by
    rw [show linePoint u.im q = (q : ℂ) + u.im * Complex.I by rfl,
      fct_horizontal_point_mem_openSegment_iff huv huvIm]
    exact hqReal
  have hpBoth := hOverlap hpUV
  have hqFirst := fct_re_mem_openSegment_of_mem hpBoth.1
  have hqSecond := fct_re_mem_openSegment_of_mem hpBoth.2
  have hfirstEndpoint := firstStage_horizontalSide_isVerticalFibreEndpoint
    C phi D P s a b hside.1 hside.2.1 hside.2.2 q (by
      simpa [linePoint] using hqFirst)
  have hsecondEndpoint := firstStage_horizontalSide_isVerticalFibreEndpoint
    C phi D P t a' b' hside'.1 hside'.2.1 hside'.2.2 q (by
      simpa [linePoint] using hqSecond)
  let firstEndpoint : ↥(sliceEndpointSet D.firstRegion
      (deformedCenterCarrier P.firstCenters) Axis.vertical q) :=
    ⟨(a.1 + (s.1 : Tiling.Plane)).im, hfirstEndpoint⟩
  let secondEndpoint : ↥(sliceEndpointSet D.firstRegion
      (deformedCenterCarrier P.firstCenters) Axis.vertical q) :=
    ⟨(a'.1 + (t.1 : Tiling.Plane)).im, hsecondEndpoint⟩
  rcases hqGood with ⟨F⟩
  have hfirstMap : mapScalar phi (F.lift firstEndpoint) =
      (D.planarHomeomorph a.1 + P.fullCenters s).im := by
    apply target17_endpoint_mapped_eq_fullHeight D P s a
    exact F.lift_coe firstEndpoint
  have hsecondMap : mapScalar phi (F.lift secondEndpoint) =
      (D.planarHomeomorph a'.1 + P.fullCenters t).im := by
    apply target17_endpoint_mapped_eq_fullHeight D P t a'
    exact F.lift_coe secondEndpoint
  have htargetHeight :
      (D.planarHomeomorph a.1 + P.fullCenters s).im =
        (D.planarHomeomorph a'.1 + P.fullCenters t).im := by
    have hpFirstIm := fct_im_eq_of_mem_openSegment_horizontal (by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp [hside.2.1]) hpBoth.1
    have hpSecondIm := fct_im_eq_of_mem_openSegment_horizontal (by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp [hside'.2.1]) hpBoth.2
    exact hpFirstIm.symm.trans hpSecondIm
  apply le_antisymm
  · by_contra hnot
    have hlt : secondEndpoint < firstEndpoint := by
      exact Subtype.mk_lt_mk.2 (lt_of_not_ge hnot)
    have hmapLt := F.mapped_strictMono hlt
    change mapScalar phi (F.lift secondEndpoint) <
      mapScalar phi (F.lift firstEndpoint) at hmapLt
    rw [hfirstMap, hsecondMap, htargetHeight] at hmapLt
    exact (lt_irrefl _ hmapLt)
  · by_contra hnot
    have hlt : firstEndpoint < secondEndpoint := by
      exact Subtype.mk_lt_mk.2 (lt_of_not_ge hnot)
    have hmapLt := F.mapped_strictMono hlt
    change mapScalar phi (F.lift firstEndpoint) <
      mapScalar phi (F.lift secondEndpoint) at hmapLt
    rw [hfirstMap, hsecondMap, htargetHeight] at hmapLt
    exact (lt_irrefl _ hmapLt)

private theorem target18_horizontalProperContact_self
    (K : Region) (t : Tiling.Plane) :
    Continuous.HorizontalProperContact K t t := by
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  let vK : ↥K.vertices := ⟨v, hv⟩
  obtain ⟨wK, hwv, hwIm, hedge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge
      K Axis.horizontal vK
  have hwIm' : vK.1.im = wK.1.im := by
    simpa [Axis.transverseCoord] using hwIm.symm
  refine ⟨vK.1 + t, wK.1 + t, ?_, ?_, ?_⟩
  · intro h
    exact hwv (add_right_cancel h).symm
  · simp only [Complex.add_im]
    linarith
  · intro z hz
    have hz' : z - t ∈ openSegment ℝ vK.1 wK.1 := by
      rw [show vK.1 + t = t +ᵥ vK.1 by simp [add_comm],
        show wK.1 + t = t +ᵥ wK.1 by simp [add_comm],
        ← vadd_openSegment ℝ] at hz
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hz
    have hedge' := hedge hz'
    constructor
    · constructor <;>
        rw [Tiling.AxisParallel.frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem] <;>
        simpa only [vadd_eq_add, neg_add_eq_sub] using hedge'.1
    · intro hvtx
      rcases hvtx with hvtx | hvtx
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hvtx
        exact hedge'.2 (by simpa [sub_eq_add_neg, add_comm] using hvtx)
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hvtx
        exact hedge'.2 (by simpa [sub_eq_add_neg, add_comm] using hvtx)

private theorem target18_properOverlap_contactDisplacement
    {K : Region} {T : Set Tiling.Plane}
    {s t : ↥T} {a b a' b' : ↥K.vertices}
    (hside : IsIntrinsicHorizontalSide K a b)
    (hside' : IsIntrinsicHorizontalSide K a' b')
    (hOverlap : ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1) :
    (t.1 - s.1).re ∈ horizontalContactDisplacements K T a b a' b' := by
  rcases hOverlap with ⟨u, v, huv, huvIm, huvSeg⟩
  apply (horizontalContactDisplacements_iff K T a b a' b'
    ((t.1 - s.1).re)).2
  refine ⟨hside.1, hside.2.1, hside.2.2,
    hside'.1, hside'.2.1, hside'.2.2, ?_⟩
  exact ⟨s, t, rfl, u, v, huv, huvIm, huvSeg⟩

private theorem endpointAlignedSeamCode_preserved :
    ∀ (C : ApproximationContext.{0})
    (_hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (A : FiniteTransportCriticalAlphabet C),
    (∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (A.lift x)) = Real.sign x.1) →
    ∀ s t : ↥C.centres,
      Continuous.HorizontalProperContact C.region s.1 t.1 →
      Continuous.HorizontalProperContact D.deformedRegion
        (P.fullCenters s) (P.fullCenters t) := by
  intro C _hTile phi D P A hsign s t hcontact
  by_cases hst : s = t
  · subst t
    simpa only using target18_horizontalProperContact_self
      D.deformedRegion (P.fullCenters s)
  have hadj : (Continuous.verticalPlateGraph C.region C.centres).Adj s t :=
    (Continuous.verticalPlateGraph_adj_iff s t).2 ⟨hst, hcontact⟩
  obtain ⟨_, a, b, a', b', him, hdelta⟩ :=
    (verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement
      C.region C.centres s t).1 hadj
  rw [horizontalContactDisplacements_iff] at hdelta
  rcases hdelta with
    ⟨hab, habIm, habEdge, ha'b', ha'b'Im, ha'b'Edge,
      t₀, s₀, hdelta0, u, v, huv, huvIm, hOverlap⟩
  have hpBoth := hOverlap (midpoint_mem_openSegment (𝕜 := ℝ) u v)
  have hpFirstIm := fct_im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [habIm]) hpBoth.1
  have hpSecondIm := fct_im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [ha'b'Im]) hpBoth.2
  have him₀ : (s₀.1 - t₀.1).im = a.1.im - a'.1.im := by
    rw [Complex.sub_im]
    simp only [Complex.add_im] at hpFirstIm hpSecondIm
    linarith
  have hdiff : (t.1 : Tiling.Plane) - s.1 = s₀.1 - t₀.1 := by
    apply Complex.ext
    · simpa only [Complex.sub_re] using hdelta0
    · simpa only [Complex.sub_im] using him.trans him₀.symm
  let d : Tiling.Plane := s.1 - t₀.1
  have htShift : s₀.1 + d = t.1 := by
    dsimp only [d]
    linear_combination -hdiff
  have hsShift : t₀.1 + d = s.1 := by simp [d]
  have hOverlapActual : ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s.1 t.1 := by
    refine ⟨u + d, v + d, fun h ↦ huv (add_right_cancel h), ?_, ?_⟩
    · simp only [Complex.add_im]
      linarith
    · rw [show u + d = d +ᵥ u by simp [add_comm],
        show v + d = d +ᵥ v by simp [add_comm], ← vadd_openSegment ℝ]
      rintro _ ⟨z, hz, rfl⟩
      have hzBoth := hOverlap hz
      constructor
      · rw [show a.1 + s.1 = (a.1 + t₀.1) + d by rw [add_assoc, hsShift],
          show b.1 + s.1 = (b.1 + t₀.1) + d by rw [add_assoc, hsShift],
          show (a.1 + t₀.1) + d = d +ᵥ (a.1 + t₀.1) by simp [add_comm],
          show (b.1 + t₀.1) + d = d +ᵥ (b.1 + t₀.1) by simp [add_comm],
          ← vadd_openSegment ℝ]
        exact ⟨z, hzBoth.1, rfl⟩
      · rw [show a'.1 + t.1 = (a'.1 + s₀.1) + d by rw [add_assoc, htShift],
          show b'.1 + t.1 = (b'.1 + s₀.1) + d by rw [add_assoc, htShift],
          show (a'.1 + s₀.1) + d = d +ᵥ (a'.1 + s₀.1) by simp [add_comm],
          show (b'.1 + s₀.1) + d = d +ᵥ (b'.1 + s₀.1) by simp [add_comm],
          ← vadd_openSegment ℝ]
        exact ⟨z, hzBoth.2, rfl⟩
  have hOverlapTarget :=
    firstStage_labelledHorizontalOverlap_preserved
      (C := C) (phi := phi) (D := D) (P := P) (A := A) hsign
      s t a b a' b' ⟨hab, habIm, habEdge⟩
      ⟨ha'b', ha'b'Im, ha'b'Edge⟩ hOverlapActual
  obtain ⟨uTarget, vTarget, huvTarget, huvTargetIm, hOverlapTarget⟩ :=
    hOverlapTarget
  have hOverlapTarget' : ProperOpenSideOverlap
      (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
      (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
      (P.fullCenters s) (P.fullCenters t) :=
    ⟨uTarget, vTarget, huvTarget, huvTargetIm, hOverlapTarget⟩
  let fullOwner : ↥C.centres → ↥(deformedCenterCarrier P.fullCenters) :=
    fun c ↦ ⟨P.fullCenters c, ⟨c, rfl⟩⟩
  let fullVertex : ↥C.region.vertices → ↥D.deformedRegion.vertices :=
    fun w ↦ ⟨D.planarHomeomorph w.1, by
      rw [D.vertices_image]
      exact ⟨w.1, w.2, rfl⟩⟩
  have hfirstTarget : IsIntrinsicHorizontalSide D.deformedRegion
      (fullVertex a) (fullVertex b) :=
    target11_full_intrinsicHorizontalSide D a b ⟨hab, habIm, habEdge⟩
  have hsecondTarget : IsIntrinsicHorizontalSide D.deformedRegion
      (fullVertex a') (fullVertex b') :=
    target11_full_intrinsicHorizontalSide D a' b' ⟨ha'b', ha'b'Im, ha'b'Edge⟩
  have hdeltaTarget :
      (P.fullCenters t - P.fullCenters s).re ∈
        horizontalContactDisplacements D.deformedRegion
          (deformedCenterCarrier P.fullCenters)
          (fullVertex a) (fullVertex b) (fullVertex a') (fullVertex b') := by
    exact target18_properOverlap_contactDisplacement
      (K := D.deformedRegion) (T := deformedCenterCarrier P.fullCenters)
      (s := fullOwner s) (t := fullOwner t)
      (a := fullVertex a) (b := fullVertex b)
      (a' := fullVertex a') (b' := fullVertex b')
      hfirstTarget hsecondTarget hOverlapTarget'
  have hpTarget := hOverlapTarget (midpoint_mem_openSegment (𝕜 := ℝ)
    uTarget vTarget)
  have hpTargetFirstIm := fct_im_eq_of_mem_openSegment_horizontal
    (by
      dsimp only [fullVertex] at hfirstTarget
      simp only [Complex.add_im]
      rw [hfirstTarget.2.1]) hpTarget.1
  have hpTargetSecondIm := fct_im_eq_of_mem_openSegment_horizontal
    (by
      dsimp only [fullVertex] at hsecondTarget
      simp only [Complex.add_im]
      rw [hsecondTarget.2.1]) hpTarget.2
  have himTarget :
      (P.fullCenters t - P.fullCenters s).im =
        (D.planarHomeomorph a.1).im - (D.planarHomeomorph a'.1).im := by
    simp only [Complex.add_im, Complex.sub_im] at hpTargetFirstIm hpTargetSecondIm ⊢
    linarith
  have hfullne : fullOwner s ≠ fullOwner t := by
    intro h
    apply hst
    exact P.fullCenters.injective (congrArg Subtype.val h)
  have htargetAdj :
      (Continuous.verticalPlateGraph D.deformedRegion
        (deformedCenterCarrier P.fullCenters)).Adj (fullOwner s) (fullOwner t) := by
    apply (verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement
      D.deformedRegion (deformedCenterCarrier P.fullCenters)
      (fullOwner s) (fullOwner t)).2
    refine ⟨hfullne, ?_⟩
    refine ⟨fullVertex a, fullVertex b, fullVertex a', fullVertex b', ?_, ?_⟩
    · dsimp only [fullOwner, fullVertex]
      exact himTarget
    · simpa only [fullOwner, fullVertex] using hdeltaTarget
  exact (Continuous.verticalPlateGraph_adj_iff (fullOwner s) (fullOwner t)).1
    htargetAdj |>.2

private theorem target19_intrinsicHorizontalSide_symm
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (A B : ↥D.deformedRegion.vertices)
    (hside : IsIntrinsicHorizontalSide D.deformedRegion A B) :
    IsIntrinsicHorizontalSide C.region (D.vertexEquiv.symm A)
      (D.vertexEquiv.symm B) := by
  let a : ↥C.region.vertices := D.vertexEquiv.symm A
  let b : ↥C.region.vertices := D.vertexEquiv.symm B
  have haEq : D.vertexEquiv a = A := D.vertexEquiv.apply_symm_apply A
  have hbEq : D.vertexEquiv b = B := D.vertexEquiv.apply_symm_apply B
  have haVal : D.planarHomeomorph a.1 = A.1 := by
    simpa only [D.vertexEquiv_apply] using congrArg Subtype.val haEq
  have hbVal : D.planarHomeomorph b.1 = B.1 := by
    simpa only [D.vertexEquiv_apply] using congrArg Subtype.val hbEq
  change IsIntrinsicHorizontalSide C.region a b
  refine ⟨?_, ?_, ?_⟩
  · intro hab
    apply hside.1
    rw [← haVal, ← hbVal, hab]
  · apply D.secondHomeomorph.injective
    have := hside.2.1
    rw [← haVal, ← hbVal, D.planarHomeomorph_apply,
      D.planarHomeomorph_apply] at this
    simpa using this
  · intro x hx
    have him : a.1.im = b.1.im := by
      apply D.secondHomeomorph.injective
      have := hside.2.1
      rw [← haVal, ← hbVal, D.planarHomeomorph_apply,
        D.planarHomeomorph_apply] at this
      simpa using this
    have hxTarget : D.planarHomeomorph x ∈ openSegment ℝ A.1 B.1 := by
      rw [← haVal, ← hbVal,
        ← D.image_openSegment_of_axisAligned a.1 b.1 (Or.inr him)]
      exact ⟨x, hx, rfl⟩
    have hxSide := hside.2.2 hxTarget
    constructor
    · rw [← C.region.frontier_openCarrier_eq_frontier_support]
      have hxFront : D.planarHomeomorph x ∈
          frontier D.deformedRegion.openCarrier := by
        rw [D.deformedRegion.frontier_openCarrier_eq_frontier_support]
        exact hxSide.1
      rw [D.frontier_image] at hxFront
      obtain ⟨y, hyFront, hyEq⟩ := hxFront
      have hyx : y = x := D.planarHomeomorph.injective hyEq
      simpa only [hyx] using hyFront
    · intro hxVertex
      apply hxSide.2
      rw [D.vertices_image]
      exact ⟨x, hxVertex, rfl⟩

private theorem target19_overlap_gives_horizontalProperContact
    {K : Region} {s t : Tiling.Plane} {a b a' b' : ↥K.vertices}
    (hside : IsIntrinsicHorizontalSide K a b)
    (hside' : IsIntrinsicHorizontalSide K a' b')
    (hOverlap : ProperOpenSideOverlap a.1 b.1 a'.1 b'.1 s t) :
    Continuous.HorizontalProperContact K s t := by
  rcases hOverlap with ⟨u, v, huv, huvIm, hOverlap⟩
  refine ⟨u, v, huv, huvIm, fun z hz ↦ ?_⟩
  have hzBoth := hOverlap hz
  have hzFirst : z - s ∈ openSegment ℝ a.1 b.1 := by
    rw [show a.1 + s = s +ᵥ a.1 by simp [add_comm],
      show b.1 + s = s +ᵥ b.1 by simp [add_comm],
      ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.1
  have hzSecond : z - t ∈ openSegment ℝ a'.1 b'.1 := by
    rw [show a'.1 + t = t +ᵥ a'.1 by simp [add_comm],
      show b'.1 + t = t +ᵥ b'.1 by simp [add_comm],
      ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.2
  have hzFirstEdge := hside.2.2 hzFirst
  have hzSecondEdge := hside'.2.2 hzSecond
  constructor
  · constructor
    · rw [Tiling.AxisParallel.frontier_vadd_eq]
      exact ⟨z - s, hzFirstEdge.1, by simp [vadd_eq_add]⟩
    · rw [Tiling.AxisParallel.frontier_vadd_eq]
      exact ⟨z - t, hzSecondEdge.1, by simp [vadd_eq_add]⟩
  · intro hzVertices
    rcases hzVertices with hzVertices | hzVertices
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
      exact hzFirstEdge.2 (by
        simpa only [vadd_eq_add, neg_add_eq_sub] using hzVertices)
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
      exact hzSecondEdge.2 (by
        simpa only [vadd_eq_add, neg_add_eq_sub] using hzVertices)

private theorem endpointAlignedSeamCode_reflected :
    ∀ (C : ApproximationContext.{0})
    (_hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (Acrit : FiniteTransportCriticalAlphabet C),
    (∀ x : ↥(transportCriticalScalars C),
      Real.sign (mapScalar phi (Acrit.lift x)) = Real.sign x.1) →
    ∀ s t : ↥C.centres,
      Continuous.HorizontalProperContact D.deformedRegion
        (P.fullCenters s) (P.fullCenters t) →
      Continuous.HorizontalProperContact C.region s.1 t.1 := by
  intro C _hTile phi D P Acrit hsign s t hcontact
  by_cases hst : s = t
  · subst t
    simpa only using target18_horizontalProperContact_self C.region s.1
  let fullOwner : ↥C.centres → ↥(deformedCenterCarrier P.fullCenters) :=
    fun c ↦ ⟨P.fullCenters c, ⟨c, rfl⟩⟩
  have hfullne : fullOwner s ≠ fullOwner t := by
    intro h
    exact hst (P.fullCenters.injective (congrArg Subtype.val h))
  have hadj : (Continuous.verticalPlateGraph D.deformedRegion
      (deformedCenterCarrier P.fullCenters)).Adj (fullOwner s) (fullOwner t) :=
    (Continuous.verticalPlateGraph_adj_iff (fullOwner s) (fullOwner t)).2
      ⟨hfullne, hcontact⟩
  obtain ⟨_, A, B, A', B', him, hdelta⟩ :=
    (verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement
      D.deformedRegion (deformedCenterCarrier P.fullCenters)
      (fullOwner s) (fullOwner t)).1 hadj
  rw [horizontalContactDisplacements_iff] at hdelta
  rcases hdelta with
    ⟨hAB, hABIm, hABEdge, hA'B', hA'B'Im, hA'B'Edge,
      t₀, s₀, hdelta0, u, v, huv, huvIm, hOverlap⟩
  have hpBoth := hOverlap (midpoint_mem_openSegment (𝕜 := ℝ) u v)
  have hpFirstIm := fct_im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [hABIm]) hpBoth.1
  have hpSecondIm := fct_im_eq_of_mem_openSegment_horizontal
    (by simp only [Complex.add_im]; linarith [hA'B'Im]) hpBoth.2
  have him₀ : (s₀.1 - t₀.1).im = A.1.im - A'.1.im := by
    rw [Complex.sub_im]
    simp only [Complex.add_im] at hpFirstIm hpSecondIm
    linarith
  have hdiff : (fullOwner t : Tiling.Plane) - fullOwner s = s₀.1 - t₀.1 := by
    apply Complex.ext
    · simpa only [Complex.sub_re] using hdelta0
    · simpa only [Complex.sub_im] using him.trans him₀.symm
  let d : Tiling.Plane := (fullOwner s : Tiling.Plane) - t₀.1
  have htShift : s₀.1 + d = (fullOwner t : Tiling.Plane) := by
    dsimp only [d]
    linear_combination -hdiff
  have hsShift : t₀.1 + d = (fullOwner s : Tiling.Plane) := by simp [d]
  have hOverlapActual : ProperOpenSideOverlap A.1 B.1 A'.1 B'.1
      (fullOwner s) (fullOwner t) := by
    refine ⟨u + d, v + d, fun h ↦ huv (add_right_cancel h), ?_, ?_⟩
    · simp only [Complex.add_im]
      linarith
    · rw [show u + d = d +ᵥ u by simp [add_comm],
        show v + d = d +ᵥ v by simp [add_comm], ← vadd_openSegment ℝ]
      rintro _ ⟨z, hz, rfl⟩
      have hzBoth := hOverlap hz
      constructor
      · rw [show A.1 + (fullOwner s : Tiling.Plane) = (A.1 + t₀.1) + d by
            rw [add_assoc, hsShift],
          show B.1 + (fullOwner s : Tiling.Plane) = (B.1 + t₀.1) + d by
            rw [add_assoc, hsShift],
          show (A.1 + t₀.1) + d = d +ᵥ (A.1 + t₀.1) by simp [add_comm],
          show (B.1 + t₀.1) + d = d +ᵥ (B.1 + t₀.1) by simp [add_comm],
          ← vadd_openSegment ℝ]
        exact ⟨z, hzBoth.1, rfl⟩
      · rw [show A'.1 + (fullOwner t : Tiling.Plane) = (A'.1 + s₀.1) + d by
            rw [add_assoc, htShift],
          show B'.1 + (fullOwner t : Tiling.Plane) = (B'.1 + s₀.1) + d by
            rw [add_assoc, htShift],
          show (A'.1 + s₀.1) + d = d +ᵥ (A'.1 + s₀.1) by simp [add_comm],
          show (B'.1 + s₀.1) + d = d +ᵥ (B'.1 + s₀.1) by simp [add_comm],
          ← vadd_openSegment ℝ]
        exact ⟨z, hzBoth.2, rfl⟩
  let a : ↥C.region.vertices := D.vertexEquiv.symm A
  let b : ↥C.region.vertices := D.vertexEquiv.symm B
  let a' : ↥C.region.vertices := D.vertexEquiv.symm A'
  let b' : ↥C.region.vertices := D.vertexEquiv.symm B'
  have hside : IsIntrinsicHorizontalSide C.region a b :=
    target19_intrinsicHorizontalSide_symm D A B ⟨hAB, hABIm, hABEdge⟩
  have hside' : IsIntrinsicHorizontalSide C.region a' b' :=
    target19_intrinsicHorizontalSide_symm D A' B' ⟨hA'B', hA'B'Im, hA'B'Edge⟩
  have haVal : D.planarHomeomorph a.1 = A.1 := by
    simpa only [a, D.vertexEquiv_apply] using
      congrArg Subtype.val (D.vertexEquiv.apply_symm_apply A)
  have hbVal : D.planarHomeomorph b.1 = B.1 := by
    simpa only [b, D.vertexEquiv_apply] using
      congrArg Subtype.val (D.vertexEquiv.apply_symm_apply B)
  have ha'Val : D.planarHomeomorph a'.1 = A'.1 := by
    simpa only [a', D.vertexEquiv_apply] using
      congrArg Subtype.val (D.vertexEquiv.apply_symm_apply A')
  have hb'Val : D.planarHomeomorph b'.1 = B'.1 := by
    simpa only [b', D.vertexEquiv_apply] using
      congrArg Subtype.val (D.vertexEquiv.apply_symm_apply B')
  have hTargetOverlap : ProperOpenSideOverlap
      (D.planarHomeomorph a.1) (D.planarHomeomorph b.1)
      (D.planarHomeomorph a'.1) (D.planarHomeomorph b'.1)
      (P.fullCenters s) (P.fullCenters t) := by
    dsimp only [fullOwner] at hOverlapActual
    simpa only [haVal, hbVal, ha'Val, hb'Val] using hOverlapActual
  have hsourceHeight := targetLabelledHorizontalOverlap_reflectsSourceHeight
    C _hTile phi D P s t a b a' b' hside hside' hTargetOverlap
  have hsourceOverlap := firstStage_targetLabelledHorizontalOverlap_reflected
    C _hTile phi D P Acrit hsign s t a b a' b' hside hside'
      hsourceHeight hTargetOverlap
  exact target19_overlap_gives_horizontalProperContact hside hside' hsourceOverlap

private structure PlateTransportData
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D) where
  plateEquiv :
    Continuous.VerticalPlate C.region C.centres ≃
      Continuous.VerticalPlate D.deformedRegion
        (deformedCenterCarrier P.fullCenters)
  centre_mem : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (t : ↥C.centres),
    (t.1 : Tiling.Plane) ∈ Q.centres ↔
      P.fullCenters t ∈ (plateEquiv Q).centres
  column_iff : ∀ Q : Continuous.VerticalPlate C.region C.centres,
    Continuous.IsVerticalColumn Q ↔
      Continuous.IsVerticalColumn (plateEquiv Q)

private theorem walk_eq_of_edge_eq
    {K : Region} {T : Set Tiling.Plane}
    {f : ↥T → ℝ}
    (hedge : ∀ {u v : ↥T},
      (Continuous.verticalPlateGraph K T).Adj u v → f u = f v) :
    ∀ {u v : ↥T},
      (Continuous.verticalPlateGraph K T).Walk u v → f u = f v := by
  intro u v w
  induction w with
  | nil => rfl
  | @cons u v w huv p ih =>
      exact (hedge huv).trans ih

private theorem contactGraphIso_constructsPlateTransport :
    ∀ (C : ApproximationContext.{0})
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (P : TwoStageDeformationSupportTransport C phi D),
      (∀ s t : ↥C.centres,
        Continuous.HorizontalProperContact C.region s.1 t.1 ↔
          Continuous.HorizontalProperContact D.deformedRegion
            (P.fullCenters s) (P.fullCenters t)) →
      (∀ s t : ↥C.centres,
        Continuous.HorizontalProperContact C.region s.1 t.1 →
        ((s.1 : Tiling.Plane).re = (t.1 : Tiling.Plane).re ↔
          (P.fullCenters s).re = (P.fullCenters t).re)) →
      Nonempty (PlateTransportData C phi D P) := by
  intro C phi D P hContact hcol
  let e := Continuous.deformation_verticalPlateEquiv C phi D P hContact
  have hcentre : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (t : ↥C.centres),
      (t.1 : Tiling.Plane) ∈ Q.centres ↔ P.fullCenters t ∈ (e Q).centres := by
    intro Q t
    rw [show e = Continuous.deformation_verticalPlateEquiv C phi D P hContact by rfl,
      Continuous.deformation_verticalPlateEquiv_centres C phi D P hContact Q]
    constructor
    · intro ht
      exact ⟨t, ht, rfl⟩
    · rintro ⟨u, hu, heq⟩
      have hut : u = t := P.fullCenters.injective heq
      simpa [hut] using hu
  refine ⟨⟨e, hcentre, ?_⟩⟩
  intro Q
  rw [Continuous.isVerticalColumn_iff, Continuous.isVerticalColumn_iff]
  obtain ⟨q, hq⟩ := Q.nonempty_supp
  have hqQ : (q : Tiling.Plane) ∈ Q.centres := ⟨q, hq, rfl⟩
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(P.fullCenters q).re, ?_⟩
    intro z hz
    have hcentres :=
      Continuous.deformation_verticalPlateEquiv_centres C phi D P hContact Q
    rw [hcentres] at hz
    obtain ⟨r, hr, hzr⟩ := hz
    have hqr : (P.fullCenters q).re = (P.fullCenters r).re := by
      change (r : Tiling.Plane) ∈ Q.centres at hr
      obtain ⟨r', hr', heq⟩ := hr
      have hrr : r' = r := Subtype.ext heq
      have hr' : r ∈ Q.supp := hrr ▸ hr'
      obtain ⟨w⟩ := Q.reachable_of_mem_supp hq hr'
      have hwalk : ∀ {u v : ↥C.centres}
          (hu : u ∈ Q.supp)
          (p : (Continuous.verticalPlateGraph C.region C.centres).Walk u v),
          (P.fullCenters u).re = (P.fullCenters v).re := by
        intro u v hu p
        induction p with
        | nil => rfl
        | @cons u v w huv p ih =>
            have hmkU :=
              (SimpleGraph.ConnectedComponent.mem_supp_iff Q u).mp hu
            have hv : v ∈ Q.supp := by
              apply (SimpleGraph.ConnectedComponent.mem_supp_iff Q v).mpr
              exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
                huv).symm.trans hmkU
            have huQ : (u : Tiling.Plane) ∈ Q.centres := ⟨u, hu, rfl⟩
            have hvQ : (v : Tiling.Plane) ∈ Q.centres := ⟨v, hv, rfl⟩
            have hsource := (hx huQ).trans (hx hvQ).symm
            have hedge := (hcol u v
              ((Continuous.verticalPlateGraph_adj_iff u v).mp huv).2).mp hsource
            exact hedge.trans (ih hv)
      exact hwalk hq w
    rw [← hzr]
    exact hqr.symm
  · rintro ⟨x, hx⟩
    refine ⟨(q : Tiling.Plane).re, ?_⟩
    intro z hz
    obtain ⟨r, hr, rfl⟩ := hz
    obtain ⟨w⟩ := Q.reachable_of_mem_supp hq hr
    have hwalk : ∀ {u v : ↥C.centres}
        (hu : u ∈ Q.supp)
        (p : (Continuous.verticalPlateGraph C.region C.centres).Walk u v),
        (u.1 : Tiling.Plane).re = (v.1 : Tiling.Plane).re := by
      intro u v hu p
      induction p with
      | nil => rfl
      | @cons u v w huv p ih =>
          have hmkU :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff Q u).mp hu
          have hv : v ∈ Q.supp := by
            apply (SimpleGraph.ConnectedComponent.mem_supp_iff Q v).mpr
            exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
              huv).symm.trans hmkU
          have huQ : (u : Tiling.Plane) ∈ Q.centres := ⟨u, hu, rfl⟩
          have hvQ : (v : Tiling.Plane) ∈ Q.centres := ⟨v, hv, rfl⟩
          have huT := (hcentre Q u).mp huQ
          have hvT := (hcentre Q v).mp hvQ
          have htarget := (hx huT).trans (hx hvT).symm
          have hedge := (hcol u v
            ((Continuous.verticalPlateGraph_adj_iff u v).mp huv).2).mpr htarget
          exact hedge.trans (ih hv)
    exact (hwalk hq w).symm

private structure PlateBoundaryReconstruction
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
      Continuous.VerticalPlate D.deformedRegion
        (deformedCenterCarrier P.fullCenters))
    (Q : Continuous.VerticalPlate C.region C.centres) where
  boundaryLift : ↥(frontier Q.base) → C.coordinateSpace
  lift_coe : ∀ x, (boundaryLift x : ℝ) = x.1
  homeomorph : ℝ ≃ₜ ℝ
  homeomorph_strictMono : StrictMono homeomorph
  boundary_formula : ∀ x : ↥(frontier Q.base),
    homeomorph x.1 = mapScalar phi (boundaryLift x)
  target_base : (plateEquiv Q).base = homeomorph '' Q.base
  target_frontier : frontier (plateEquiv Q).base =
    mapScalarSet phi (Set.range boundaryLift)
  bounded_chamber : ∀ a b : ↥(frontier Q.base), a.1 < b.1 →
    Ioo a.1 b.1 ∩ frontier Q.base = ∅ →
    (Ioo a.1 b.1 ⊆ Q.base ↔
      Ioo (mapScalar phi (boundaryLift a))
        (mapScalar phi (boundaryLift b)) ⊆ (plateEquiv Q).base)

private theorem plateBoundaryReconstruction_exists_of
    (hPublic :
      ∀ {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
        {D : CoordinateDeformation C phi}
        (P : TwoStageDeformationSupportTransport C phi D)
        (S : Set Tiling.Plane) (_hS : S ⊆ C.centres)
        (X : Set ℝ) (_hXopen : IsOpen X)
        (_hXregular : interior (closure X) = X)
        (_hSupport : regularSupport C.region S = Complex.re ⁻¹' X),
        ∃ (boundaryLift : ↥(frontier X) → C.coordinateSpace) (H : ℝ ≃ₜ ℝ),
          (∀ x, (boundaryLift x : ℝ) = x.1) ∧
          StrictMono H ∧
          (∀ x : ↥(frontier X), H x.1 = mapScalar phi (boundaryLift x)) ∧
          regularSupport D.deformedRegion
            (deformedCenterCarrierOn P.fullCenters
              {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =
            Complex.re ⁻¹' (H '' X))
    (C : ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
      Continuous.VerticalPlate D.deformedRegion
        (deformedCenterCarrier P.fullCenters))
    (hcentres : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (t : ↥C.centres),
      (t.1 : Tiling.Plane) ∈ Q.centres ↔
        P.fullCenters t ∈ (plateEquiv Q).centres) :
    ∀ Q : Continuous.VerticalPlate C.region C.centres,
      Nonempty (PlateBoundaryReconstruction C phi D P plateEquiv Q) := by
  intro Q
  have hQcentres : Q.centres ⊆ C.centres := by
    rintro z ⟨t, _htQ, rfl⟩
    exact t.2
  obtain ⟨hQregular, hQsupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile Q
  have hQopen : IsOpen Q.base := by
    rw [hQregular]
    exact isOpen_interior
  have hSupport : regularSupport C.region Q.centres =
      Complex.re ⁻¹' Q.base := by
    rw [← Q.support_eq_regularSupport]
    exact hQsupport
  obtain ⟨boundaryLift, H, hlift, hHmono, hHboundary, hTargetSupport⟩ :=
    hPublic P Q.centres hQcentres Q.base hQopen hQregular.symm hSupport
  have hTargetCentres :
      deformedCenterCarrierOn P.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ Q.centres} =
        (plateEquiv Q).centres := by
    ext z
    constructor
    · rintro ⟨t, htQ, rfl⟩
      exact (hcentres Q t).mp htQ
    · rintro ⟨u, huQ, huz⟩
      obtain ⟨t, htu⟩ := u.2
      refine ⟨t, (hcentres Q t).mpr ?_, htu.trans huz⟩
      rw [htu]
      exact ⟨u, huQ, rfl⟩
  have hTargetSupport' : (plateEquiv Q).support =
      Complex.re ⁻¹' (H '' Q.base) := by
    rw [(plateEquiv Q).support_eq_regularSupport, ← hTargetCentres]
    exact hTargetSupport
  have hTargetSlab :=
    Continuous.VerticalPlate.support_isVerticalSlab P.full_tilesOn (plateEquiv Q)
  have hTargetBase : (plateEquiv Q).base = H '' Q.base := by
    ext x
    have hx := Set.ext_iff.mp (hTargetSlab.2.symm.trans hTargetSupport') (x : ℂ)
    simpa using hx
  have hTargetFrontier : frontier (plateEquiv Q).base =
      mapScalarSet phi (Set.range boundaryLift) := by
    rw [hTargetBase, ← H.image_frontier]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨boundaryLift ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, ?_⟩
      exact (hHboundary ⟨x, hx⟩).symm
    · rintro ⟨u, ⟨x, rfl⟩, rfl⟩
      exact ⟨x.1, x.2, hHboundary x⟩
  refine ⟨⟨boundaryLift, hlift, H, hHmono, hHboundary, hTargetBase,
    hTargetFrontier, ?_⟩⟩
  intro a b _hab _hgap
  rw [← hHboundary a, ← hHboundary b, hTargetBase,
    ← H.continuous.image_Ioo_of_strictMono hHmono]
  constructor
  · exact Set.image_mono
  · intro hImage x hx
    obtain ⟨y, hy, hxy⟩ := hImage ⟨x, hx, rfl⟩
    have hyx : y = x := hHmono.injective hxy
    simpa [hyx] using hy

private theorem plateBoundaryReconstruction_exists :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (P : TwoStageDeformationSupportTransport C phi D)
      (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
        Continuous.VerticalPlate D.deformedRegion
          (deformedCenterCarrier P.fullCenters))
      (_hcentres : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
        (t : ↥C.centres),
        (t.1 : Tiling.Plane) ∈ Q.centres ↔
          P.fullCenters t ∈ (plateEquiv Q).centres),
      ∀ Q : Continuous.VerticalPlate C.region C.centres,
        Nonempty (PlateBoundaryReconstruction C phi D P plateEquiv Q) := by
  exact plateBoundaryReconstruction_exists_of
    Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph

private theorem plateBoundaryReconstruction_of_publicHomeomorph :
    (∀ {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
      {D : CoordinateDeformation C phi}
      (P : TwoStageDeformationSupportTransport C phi D)
      (S : Set Tiling.Plane) (_hS : S ⊆ C.centres)
      (X : Set ℝ) (_hXopen : IsOpen X)
      (_hXregular : interior (closure X) = X)
      (_hSupport : regularSupport C.region S = Complex.re ⁻¹' X),
      ∃ (boundaryLift : ↥(frontier X) → C.coordinateSpace) (H : ℝ ≃ₜ ℝ),
        (∀ x, (boundaryLift x : ℝ) = x.1) ∧
        StrictMono H ∧
        (∀ x : ↥(frontier X), H x.1 = mapScalar phi (boundaryLift x)) ∧
        regularSupport D.deformedRegion
          (deformedCenterCarrierOn P.fullCenters
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =
          Complex.re ⁻¹' (H '' X)) →
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (P : TwoStageDeformationSupportTransport C phi D)
      (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
        Continuous.VerticalPlate D.deformedRegion
          (deformedCenterCarrier P.fullCenters))
      (_hcentres : ∀ (Q : Continuous.VerticalPlate C.region C.centres)
        (t : ↥C.centres),
        (t.1 : Tiling.Plane) ∈ Q.centres ↔
          P.fullCenters t ∈ (plateEquiv Q).centres),
      ∀ Q : Continuous.VerticalPlate C.region C.centres,
        Nonempty (PlateBoundaryReconstruction C phi D P plateEquiv Q) := by
  intro hPublic
  exact plateBoundaryReconstruction_exists_of hPublic

private theorem componentBoundaryLift_exists :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_D : CoordinateDeformation C phi),
      ∃ lift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
          C.region C.centres) → C.coordinateSpace,
        ∀ x, (lift x : ℝ) = x.1 := by
  intro C hTile phi D
  obtain ⟨P⟩ := exists_twoStageDeformationSupportTransport C phi D hTile
  have hControlled :
      ∀ x : ↥(componentBoundarySet C.region C.centres),
        ∃ z : C.coordinateSpace, (z : ℝ) = x.1 := by
    intro x
    have hx := x.2
    change x.1 ∈ ⋃ Q : Continuous.VerticalPlate C.region C.centres,
      frontier Q.base at hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    have hQcentres : Q.centres ⊆ C.centres := by
      rintro z ⟨t, _htQ, rfl⟩
      exact t.2
    obtain ⟨hQregular, hQsupport⟩ :=
      Continuous.VerticalPlate.support_isVerticalSlab hTile Q
    have hQopen : IsOpen Q.base := by
      rw [hQregular]
      exact isOpen_interior
    have hSupport : regularSupport C.region Q.centres =
        Complex.re ⁻¹' Q.base := by
      rw [← Q.support_eq_regularSupport]
      exact hQsupport
    obtain ⟨boundaryLift, _H, hlift, _hHmono, _hHboundary,
      _hTargetSupport⟩ :=
      coordinateDeformation_subfamilySupport_homeomorph
        P Q.centres hQcentres Q.base hQopen hQregular.symm hSupport
    exact ⟨boundaryLift ⟨x.1, hxQ⟩, hlift ⟨x.1, hxQ⟩⟩
  choose lift hlift using hControlled
  exact ⟨lift, hlift⟩


private theorem target24_componentBoundary_mem_translatedVertices
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T univ) {c : ℝ}
    (hc : c ∈ componentBoundarySet K T) :
    c ∈ Continuous.horizontalTranslatedVertices K T := by
  let _ : Countable T := hTile.1.to_subtype
  have hVerticesFinite : K.vertices.Finite := by
    simpa only [Region.vertices] using K.isPolygonal.vertexSet_finite
  let _ : Countable (↑K.vertices) := hVerticesFinite.countable.to_subtype
  let forbidden : Set ℝ :=
    Set.range fun p : T × ↑K.vertices ↦ p.1.1.im + p.2.1.im
  have hForbiddenCountable : forbidden.Countable := Set.countable_range _
  have hForbiddenNe : forbidden ≠ Set.univ := by
    intro hEq
    apply Cardinal.not_countable_real
    rw [← hEq]
    exact hForbiddenCountable
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem forbidden).mp hForbiddenNe
  let p : Tiling.Plane := ⟨c, y⟩
  have hpLine : p ∈ {z : Tiling.Plane | z.re = c} := by rfl
  have hpUnion := componentBoundaryLine_subset_translatedFrontiers
    hTile c hc hpLine
  rw [Set.mem_iUnion] at hpUnion
  obtain ⟨t, hpFrontier⟩ := hpUnion
  rw [Tiling.AxisParallel.frontier_vadd_eq,
    Set.mem_vadd_set_iff_neg_vadd_mem] at hpFrontier
  rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid
      K hpFrontier with hre | him
  · obtain ⟨v, hv, hvRe⟩ := hre
    rw [Continuous.horizontalTranslatedVertices_eq]
    refine ⟨v, hv, t.1, t.2, ?_⟩
    simp only [Complex.add_re]
    simp only [vadd_eq_add, Complex.add_re, Complex.neg_re] at hvRe
    linarith
  · obtain ⟨v, hv, hvIm⟩ := him
    exfalso
    apply hy
    refine ⟨(t, ⟨v, hv⟩), ?_⟩
    simp only [p, vadd_eq_add, Complex.add_im, Complex.neg_im] at hvIm
    linarith


private theorem target24_mappedBoundaryDifference_eq_stepSum
    (C : ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (lift : ↥(componentBoundarySet C.region C.centres) → C.coordinateSpace)
    (hlift : ∀ x, (lift x : ℝ) = x.1)
    (x y : ↥(componentBoundarySet C.region C.centres)) (hxy : x.1 < y.1) :
    ∃ (n : ℕ), 0 < n ∧ ∃ step : Fin n → ℝ,
      ∃ hstep : ∀ i, step i ∈ C.region.horizontalStepAlphabet,
      mapScalar phi (lift y) - mapScalar phi (lift x) =
        ∑ i, mapScalar phi
          ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
  have hyTranslated :=
    target24_componentBoundary_mem_translatedVertices hTile y.2
  rw [Continuous.horizontalTranslatedVertices_eq] at hyTranslated
  obtain ⟨v, hv, t, ht, hyVertex⟩ := hyTranslated
  let vC : ↥C.region.vertices := ⟨v, hv⟩
  let tC : ↥C.centres := ⟨t, ht⟩
  have hline := componentBoundaryLine_subset_translatedFrontiers
    hTile x.1 x.2
  have hne : (vC.1 + (tC.1 : Tiling.Plane)).re ≠ x.1 := by
    rw [← hyVertex]
    exact ne_of_gt hxy
  obtain ⟨n, hn, step, hstep, hsum⟩ :=
    horizontalBoundaryDistance_eq_stepSum hTile hline vC tC hne
  let stepLift : Fin n → C.coordinateSpace := fun i ↦
    ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩
  have hxyValue : y.1 - x.1 = ∑ i, step i := by
    rw [← hyVertex] at hsum
    have hxy' : x.1 < y.1 := hxy
    rw [abs_of_pos (sub_pos.mpr hxy')] at hsum
    exact hsum
  have hLiftEq : lift y - lift x = ∑ i, stepLift i := by
    apply Subtype.ext
    rw [Submodule.coe_sub, Submodule.coe_sum, hlift y, hlift x]
    simpa only [stepLift] using hxyValue
  have hMapEq : mapScalar phi (lift y) - mapScalar phi (lift x) =
      ∑ i, mapScalar phi (stepLift i) := by
    have hPhi := congrArg phi hLiftEq
    simp only [map_sub, map_sum] at hPhi
    change ((phi (lift y) : ℚ) : ℝ) - ((phi (lift x) : ℚ) : ℝ) =
      ∑ i, ((phi (stepLift i) : ℚ) : ℝ)
    exact_mod_cast hPhi
  exact ⟨n, hn, step, hstep, by simpa only [stepLift] using hMapEq⟩

private theorem componentBoundaryMapped_strictMono :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (lift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres) → C.coordinateSpace),
      (∀ x, (lift x : ℝ) = x.1) →
      (∀ d : ℝ, d ∈ C.region.horizontalStepAlphabet →
        ∀ hd : d ∈ C.coordinateSpace,
          0 < mapScalar phi ⟨d, hd⟩) →
      StrictMono (fun x ↦ mapScalar phi (lift x)) := by
  intro C hTile phi lift hlift hpositive x y hxy
  obtain ⟨n, hn, step, hstep, hMapEq⟩ :=
    target24_mappedBoundaryDifference_eq_stepSum
      C hTile phi lift hlift x y hxy
  rw [← sub_pos, hMapEq]
  exact Finset.sum_pos (fun i _hi ↦ hpositive (step i) (hstep i)
    (horizontalStep_mem_coordinateSpace C (hstep i)))
    ⟨⟨0, hn⟩, by simp⟩

private theorem target25_finite_inter_bounded_of_separated
    {S Q : Set ℝ} {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Pairwise fun x y ↦ delta ≤ dist x y)
    (hQ : Bornology.IsBounded Q) : (S ∩ Q).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hdelta hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · simp only [Metric.mem_ball] at htball
        exact False.elim
          ((not_lt_of_ge (by simpa [dist_comm] using hS htS hs hts)) htball)
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  exact (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
    (inter_subset_inter_right S hR)

private theorem componentBoundaryMapped_orderGeometry :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (lift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres) → C.coordinateSpace),
      (∀ x, (lift x : ℝ) = x.1) →
      StrictMono (fun x ↦ mapScalar phi (lift x)) →
      (∀ d : ℝ, d ∈ C.region.horizontalStepAlphabet →
        ∀ hd : d ∈ C.coordinateSpace,
          0 < mapScalar phi ⟨d, hd⟩) →
      (∀ Q : Set ℝ, Bornology.IsBounded Q →
        (mapScalarSet phi (Set.range lift) ∩ Q).Finite) ∧
      (¬ BddAbove (Tiling.AxisParallel.Structure.componentBoundarySet
          C.region C.centres) →
        ¬ BddAbove (mapScalarSet phi (Set.range lift))) ∧
      (¬ BddBelow (Tiling.AxisParallel.Structure.componentBoundarySet
          C.region C.centres) →
        ¬ BddBelow (mapScalarSet phi (Set.range lift))) := by
  classical
  intro C hTile phi lift hlift hmono hpositive
  let E : Set ℝ := componentBoundarySet C.region C.centres
  let f : ↥E → ℝ := fun x ↦ mapScalar phi (lift x)
  let gapValue : ↥(C.region.horizontalStepAlphabet : Set ℝ) → ℝ :=
    fun d ↦ mapScalar phi
      ⟨d.1, horizontalStep_mem_coordinateSpace C d.2⟩
  let F : Finset ℝ := C.region.horizontalStepAlphabet.attach.image gapValue
  have hFne : F.Nonempty := by
    obtain ⟨d, hd⟩ := C.region.horizontalStepAlphabet_nonempty
    refine ⟨gapValue ⟨d, hd⟩, ?_⟩
    simp only [F, Finset.mem_image]
    exact ⟨⟨d, hd⟩, by simp, rfl⟩
  let delta : ℝ := F.min' hFne
  have hdeltaMem : delta ∈ F := F.min'_mem hFne
  have hdelta : 0 < delta := by
    rw [Finset.mem_image] at hdeltaMem
    obtain ⟨d, _hdAttach, hdValue⟩ := hdeltaMem
    rw [← hdValue]
    exact hpositive d.1 d.2
      (horizontalStep_mem_coordinateSpace C d.2)
  have hGapLower : ∀ x y : ↥E, x.1 < y.1 → delta ≤ f y - f x := by
    intro x y hxy
    obtain ⟨n, hn, step, hstep, hMapEq⟩ :=
      target24_mappedBoundaryDifference_eq_stepSum
        C hTile phi lift hlift x y hxy
    have hterm : ∀ i : Fin n, delta ≤
        mapScalar phi ⟨step i,
          horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
      intro i
      apply F.min'_le
      simp only [F, Finset.mem_image]
      refine ⟨⟨step i, hstep i⟩, by simp, ?_⟩
      rfl
    have hsum : (n : ℝ) * delta ≤
        ∑ i, mapScalar phi ⟨step i,
          horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
      simpa only [nsmul_eq_mul, mul_comm, Finset.card_univ,
        Fintype.card_fin] using
        (Finset.card_nsmul_le_sum Finset.univ
          (fun i : Fin n ↦ mapScalar phi ⟨step i,
            horizontalStep_mem_coordinateSpace C (hstep i)⟩)
          delta (fun i _hi ↦ hterm i))
    have hnReal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [hMapEq]
    nlinarith
  have hRange : Set.range f = mapScalarSet phi (Set.range lift) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨lift x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
  have hSeparated : (Set.range f).Pairwise fun a b ↦ delta ≤ dist a b := by
    rintro a ⟨x, rfl⟩ b ⟨y, rfl⟩ hne
    rcases lt_or_gt_of_ne (fun hxy ↦ hne (congrArg f hxy)) with hxy | hyx
    · rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (hmono hxy)), neg_sub]
      exact hGapLower x y hxy
    · rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (hmono hyx))]
      exact hGapLower y x hyx
  have hRangeFinite : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (Set.range f ∩ Q).Finite :=
    fun Q hQ ↦ target25_finite_inter_bounded_of_separated
      hdelta hSeparated hQ
  have hUpper : ¬ BddAbove E → ¬ BddAbove (Set.range f) := by
    intro hE hImage
    obtain ⟨a0, ha0, _ha⟩ := (not_bddAbove_iff.1 hE) 0
    let a : ↥E := ⟨a0, ha0⟩
    obtain ⟨M, hM⟩ := hImage
    let U : Set ↥E := {x | a.1 ≤ x.1}
    have hImageU : f '' U ⊆ Set.range f ∩ Icc (f a) M := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, hmono.monotone hx, hM ⟨x, rfl⟩⟩
    have hUfinite : U.Finite := by
      apply Set.Finite.of_finite_image
        ((hRangeFinite (Icc (f a) M) (Metric.isBounded_Icc _ _)).subset hImageU)
      exact hmono.injective.injOn
    let _ : Nonempty ↥E := ⟨a⟩
    obtain ⟨u, hu⟩ := hUfinite.bddAbove
    apply hE
    refine ⟨max a.1 u.1, ?_⟩
    intro c hcE
    let ce : ↥E := ⟨c, hcE⟩
    by_cases hc : a.1 ≤ ce.1
    · exact le_max_of_le_right (hu hc)
    · exact le_max_of_le_left (le_of_not_ge hc)
  have hLower : ¬ BddBelow E → ¬ BddBelow (Set.range f) := by
    intro hE hImage
    obtain ⟨a0, ha0, _ha⟩ := (not_bddBelow_iff.1 hE) 0
    let a : ↥E := ⟨a0, ha0⟩
    obtain ⟨M, hM⟩ := hImage
    let U : Set ↥E := {x | x.1 ≤ a.1}
    have hImageU : f '' U ⊆ Set.range f ∩ Icc M (f a) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, rfl⟩, hM ⟨x, rfl⟩, hmono.monotone hx⟩
    have hUfinite : U.Finite := by
      apply Set.Finite.of_finite_image
        ((hRangeFinite (Icc M (f a)) (Metric.isBounded_Icc _ _)).subset hImageU)
      exact hmono.injective.injOn
    let _ : Nonempty ↥E := ⟨a⟩
    obtain ⟨u, hu⟩ := hUfinite.bddBelow
    apply hE
    refine ⟨min a.1 u.1, ?_⟩
    intro c hcE
    let ce : ↥E := ⟨c, hcE⟩
    by_cases hc : ce.1 ≤ a.1
    · exact min_le_of_right_le (hu hc)
    · exact min_le_of_left_le (le_of_not_ge hc)
  rw [← hRange]
  exact ⟨hRangeFinite, hUpper, hLower⟩

private structure ComponentBoundaryTransportData
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (plates : PlateTransportData C phi D P) where
  boundaryLift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
    C.region C.centres) → C.coordinateSpace
  boundaryEquiv :
    ↥(Tiling.AxisParallel.Structure.componentBoundarySet C.region C.centres) ≃
      ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        D.deformedRegion (deformedCenterCarrier P.fullCenters))
  lift_coe : ∀ x, (boundaryLift x : ℝ) = x.1
  boundary_formula : ∀ x,
    (boundaryEquiv x : ℝ) = mapScalar phi (boundaryLift x)
  strictMono : StrictMono boundaryEquiv
  bounded_chamber_label :
    ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (c d : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres)),
      c.1 < d.1 →
      Ioo c.1 d.1 ∩
          Tiling.AxisParallel.Structure.componentBoundarySet C.region C.centres = ∅ →
      (Ioo c.1 d.1 ⊆ Q.base ↔
        Ioo (boundaryEquiv c).1 (boundaryEquiv d).1 ⊆
          (plates.plateEquiv Q).base)
  rightRay_label :
    ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (c : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres)),
      (Ioi c.1 ⊆ Q.base ∧
          Ioi c.1 ∩ Tiling.AxisParallel.Structure.componentBoundarySet
            C.region C.centres = ∅) ↔
        (Ioi (boundaryEquiv c).1 ⊆ (plates.plateEquiv Q).base ∧
          Ioi (boundaryEquiv c).1 ∩
            Tiling.AxisParallel.Structure.componentBoundarySet
              D.deformedRegion (deformedCenterCarrier P.fullCenters) = ∅)
  leftRay_label :
    ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (c : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres)),
      (Iio c.1 ⊆ Q.base ∧
          Iio c.1 ∩ Tiling.AxisParallel.Structure.componentBoundarySet
            C.region C.centres = ∅) ↔
        (Iio (boundaryEquiv c).1 ⊆ (plates.plateEquiv Q).base ∧
          Iio (boundaryEquiv c).1 ∩
            Tiling.AxisParallel.Structure.componentBoundarySet
              D.deformedRegion (deformedCenterCarrier P.fullCenters) = ∅)
  translatedVerticalSide_between :
    ∀ (Q : Continuous.VerticalPlate C.region C.centres)
      (t : ↥C.centres) (v w : ↥C.region.vertices)
      (c d : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres)),
      (t.1 : Tiling.Plane) ∈ Q.centres →
      v.1 ≠ w.1 → v.1.re = w.1.re →
      openSegment ℝ v.1 w.1 ⊆ frontier C.region.support \ C.region.vertices →
      c.1 < d.1 →
      Ioo c.1 d.1 ∩
          Tiling.AxisParallel.Structure.componentBoundarySet C.region C.centres = ∅ →
      Ioo c.1 d.1 ⊆ Q.base →
      c.1 < (v.1 + (t.1 : Tiling.Plane)).re →
      (v.1 + (t.1 : Tiling.Plane)).re < d.1 →
      (boundaryEquiv c).1 <
          (D.planarHomeomorph v.1 + P.fullCenters t).re ∧
        (D.planarHomeomorph v.1 + P.fullCenters t).re <
          (boundaryEquiv d).1

private theorem componentBoundary_target_eq_mappedRange :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (P : TwoStageDeformationSupportTransport C phi D)
      (_plates : PlateTransportData C phi D P)
      (lift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
        C.region C.centres) → C.coordinateSpace),
      (∀ x, (lift x : ℝ) = x.1) →
      Tiling.AxisParallel.Structure.componentBoundarySet
          D.deformedRegion (deformedCenterCarrier P.fullCenters) =
        mapScalarSet phi (Set.range lift) := by
  intro C hTile phi D P plates lift hlift
  have hReconstruction := plateBoundaryReconstruction_exists
    C hTile phi D P plates.plateEquiv plates.centre_mem
  ext y
  constructor
  · intro hy
    change y ∈ ⋃ R : Continuous.VerticalPlate D.deformedRegion
      (deformedCenterCarrier P.fullCenters), frontier R.base at hy
    obtain ⟨R, hyR⟩ := Set.mem_iUnion.mp hy
    let Q : Continuous.VerticalPlate C.region C.centres :=
      plates.plateEquiv.symm R
    obtain ⟨RQ⟩ := hReconstruction Q
    have hPlate : plates.plateEquiv Q = R := by simp [Q]
    have hyMapped : y ∈ mapScalarSet phi (Set.range RQ.boundaryLift) := by
      rw [← RQ.target_frontier, hPlate]
      exact hyR
    obtain ⟨z, ⟨x, rfl⟩, rfl⟩ := hyMapped
    have hxBoundary : x.1 ∈ componentBoundarySet C.region C.centres := by
      change x.1 ∈ ⋃ S : Continuous.VerticalPlate C.region C.centres,
        frontier S.base
      exact Set.mem_iUnion.2 ⟨Q, x.2⟩
    let xTotal : ↥(componentBoundarySet C.region C.centres) :=
      ⟨x.1, hxBoundary⟩
    have hLiftEq : lift xTotal = RQ.boundaryLift x := by
      apply Subtype.ext
      rw [hlift xTotal, RQ.lift_coe x]
    exact ⟨lift xTotal, ⟨xTotal, rfl⟩,
      congrArg (mapScalar phi) hLiftEq⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    have hx := x.2
    change x.1 ∈ ⋃ Q : Continuous.VerticalPlate C.region C.centres,
      frontier Q.base at hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    obtain ⟨RQ⟩ := hReconstruction Q
    let xQ : ↥(frontier Q.base) := ⟨x.1, hxQ⟩
    have hLiftEq : lift x = RQ.boundaryLift xQ := by
      apply Subtype.ext
      rw [hlift x, RQ.lift_coe xQ]
    change mapScalar phi (lift x) ∈
      ⋃ R : Continuous.VerticalPlate D.deformedRegion
        (deformedCenterCarrier P.fullCenters), frontier R.base
    apply Set.mem_iUnion.2
    refine ⟨plates.plateEquiv Q, ?_⟩
    rw [RQ.target_frontier]
    exact ⟨RQ.boundaryLift xQ, ⟨xQ, rfl⟩,
      congrArg (mapScalar phi) hLiftEq.symm⟩

private theorem componentBoundary_map_endpoint_gt
    (C : ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (lift : ↥(componentBoundarySet C.region C.centres) → C.coordinateSpace)
    (hlift : ∀ x, (lift x : ℝ) = x.1)
    (hpositive : ∀ d : ℝ, d ∈ C.region.horizontalStepAlphabet →
      ∀ hd : d ∈ C.coordinateSpace, 0 < mapScalar phi ⟨d, hd⟩)
    (c : ↥(componentBoundarySet C.region C.centres))
    (v : ↥C.region.vertices) (t : ↥C.centres)
    (hct : c.1 < (v.1 + (t.1 : Tiling.Plane)).re) :
    mapScalar phi (lift c) <
      (D.planarHomeomorph v.1 + P.fullCenters t).re := by
  have hline := componentBoundaryLine_subset_translatedFrontiers
    hTile c.1 c.2
  have hne : (v.1 + (t.1 : Tiling.Plane)).re ≠ c.1 := ne_of_gt hct
  obtain ⟨n, hn, step, hstep, hsum⟩ :=
    horizontalBoundaryDistance_eq_stepSum hTile hline v t hne
  let xLift : C.coordinateSpace :=
    ⟨(v.1 + (t.1 : Tiling.Plane)).re,
      C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
        (C.centre_re_mem t.1 t.2)⟩
  have hsum' : (v.1 + (t.1 : Tiling.Plane)).re - c.1 =
      ∑ i, step i := by
    rw [abs_of_pos (sub_pos.mpr hct)] at hsum
    exact hsum
  have hmapEq : mapScalar phi xLift - mapScalar phi (lift c) =
      ∑ i, mapScalar phi
        ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
    have hLiftEq : xLift - lift c = ∑ i, (⟨step i,
        horizontalStep_mem_coordinateSpace C (hstep i)⟩ : C.coordinateSpace) := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_sum, hlift c]
      simpa [xLift] using hsum'
    have hPhi := congrArg phi hLiftEq
    simp only [map_sub, map_sum] at hPhi
    change ((phi xLift : ℚ) : ℝ) - ((phi (lift c) : ℚ) : ℝ) =
      ∑ i, ((phi (⟨step i,
        horizontalStep_mem_coordinateSpace C (hstep i)⟩ : C.coordinateSpace) : ℚ) : ℝ)
    exact_mod_cast hPhi
  have hsumPos : 0 < ∑ i, mapScalar phi
      ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
    exact Finset.sum_pos (fun i _hi ↦ hpositive (step i) (hstep i)
      (horizontalStep_mem_coordinateSpace C (hstep i)))
      ⟨⟨0, hn⟩, by simp⟩
  have hmapGt : mapScalar phi (lift c) < mapScalar phi xLift := by
    rw [← sub_pos, hmapEq]
    exact hsumPos
  have hend := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
    D v.1 v.2 t (v.1 + (t.1 : Tiling.Plane)).re xLift rfl rfl
  have hend' : mapScalar phi xLift =
      (D.planarHomeomorph v.1 + P.fullCenters t).re := by
    calc
      mapScalar phi xLift = D.firstHomeomorph v.1.re +
          (mapFirstPoint phi (C.centrePoint t.1 t.2)).re := hend
      _ = (D.planarHomeomorph v.1 + P.fullCenters t).re := by
        rw [D.planarHomeomorph_apply, P.fullCenters_apply]
        simp [mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  rw [← hend']
  exact hmapGt

private theorem componentBoundary_map_endpoint_lt
    (C : ApproximationContext.{0})
    (hTile : TilesOn C.region C.centres univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (lift : ↥(componentBoundarySet C.region C.centres) → C.coordinateSpace)
    (hlift : ∀ x, (lift x : ℝ) = x.1)
    (hpositive : ∀ d : ℝ, d ∈ C.region.horizontalStepAlphabet →
      ∀ hd : d ∈ C.coordinateSpace, 0 < mapScalar phi ⟨d, hd⟩)
    (c : ↥(componentBoundarySet C.region C.centres))
    (v : ↥C.region.vertices) (t : ↥C.centres)
    (htc : (v.1 + (t.1 : Tiling.Plane)).re < c.1) :
    (D.planarHomeomorph v.1 + P.fullCenters t).re <
      mapScalar phi (lift c) := by
  have hline := componentBoundaryLine_subset_translatedFrontiers
    hTile c.1 c.2
  have hne : (v.1 + (t.1 : Tiling.Plane)).re ≠ c.1 := ne_of_lt htc
  obtain ⟨n, hn, step, hstep, hsum⟩ :=
    horizontalBoundaryDistance_eq_stepSum hTile hline v t hne
  let xLift : C.coordinateSpace :=
    ⟨(v.1 + (t.1 : Tiling.Plane)).re,
      C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
        (C.centre_re_mem t.1 t.2)⟩
  have hsum' : c.1 - (v.1 + (t.1 : Tiling.Plane)).re =
      ∑ i, step i := by
    rw [abs_of_neg (sub_neg.mpr htc), neg_sub] at hsum
    exact hsum
  have hmapEq : mapScalar phi (lift c) - mapScalar phi xLift =
      ∑ i, mapScalar phi
        ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
    have hLiftEq : lift c - xLift = ∑ i, (⟨step i,
        horizontalStep_mem_coordinateSpace C (hstep i)⟩ : C.coordinateSpace) := by
      apply Subtype.ext
      rw [Submodule.coe_sub, Submodule.coe_sum, hlift c]
      simpa [xLift] using hsum'
    have hPhi := congrArg phi hLiftEq
    simp only [map_sub, map_sum] at hPhi
    change ((phi (lift c) : ℚ) : ℝ) - ((phi xLift : ℚ) : ℝ) =
      ∑ i, ((phi (⟨step i,
        horizontalStep_mem_coordinateSpace C (hstep i)⟩ : C.coordinateSpace) : ℚ) : ℝ)
    exact_mod_cast hPhi
  have hsumPos : 0 < ∑ i, mapScalar phi
      ⟨step i, horizontalStep_mem_coordinateSpace C (hstep i)⟩ := by
    exact Finset.sum_pos (fun i _hi ↦ hpositive (step i) (hstep i)
      (horizontalStep_mem_coordinateSpace C (hstep i)))
      ⟨⟨0, hn⟩, by simp⟩
  have hmapLt : mapScalar phi xLift < mapScalar phi (lift c) := by
    rw [← sub_pos, hmapEq]
    exact hsumPos
  have hend := target9_mapScalar_endpoint_eq_firstHomeomorph_add_center
    D v.1 v.2 t (v.1 + (t.1 : Tiling.Plane)).re xLift rfl rfl
  have hend' : mapScalar phi xLift =
      (D.planarHomeomorph v.1 + P.fullCenters t).re := by
    calc
      mapScalar phi xLift = D.firstHomeomorph v.1.re +
          (mapFirstPoint phi (C.centrePoint t.1 t.2)).re := hend
      _ = (D.planarHomeomorph v.1 + P.fullCenters t).re := by
        rw [D.planarHomeomorph_apply, P.fullCenters_apply]
        simp [mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  rw [← hend']
  exact hmapLt

private theorem componentBoundaryTransport_exists :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi)
      (P : TwoStageDeformationSupportTransport C phi D)
      (plates : PlateTransportData C phi D P),
      Nonempty (ComponentBoundaryTransportData C phi D P plates) := by
  intro C hTile phi D P plates
  obtain ⟨lift, hlift⟩ := componentBoundaryLift_exists C hTile phi D
  have hpositive : ∀ d : ℝ, d ∈ C.region.horizontalStepAlphabet →
      ∀ hd : d ∈ C.coordinateSpace,
        0 < mapScalar phi ⟨d, hd⟩ := by
    intro d hd hdC
    obtain ⟨a, ha, b, hb, hab, hpos⟩ :=
      (C.region.mem_horizontalStepAlphabet_iff d).mp hd
    have haC : a.re ∈ C.coordinateSpace := C.vertex_re_mem a ha
    have hbC : b.re ∈ C.coordinateSpace := C.vertex_re_mem b hb
    have hsign := D.source_good.preservesVertexCoordinateSign
      Axis.horizontal b a hb ha
    have hlin := congrArg (fun q : ℚ => (q : ℝ))
      (map_sub phi ⟨b.re, hbC⟩ ⟨a.re, haC⟩)
    have hsub :
        (⟨b.re, hbC⟩ - ⟨a.re, haC⟩ : C.coordinateSpace) =
          ⟨b.re - a.re, C.coordinateSpace.sub_mem hbC haC⟩ := by
      apply Subtype.ext
      rfl
    rw [hsub] at hlin
    have hlin' : mapScalar phi ⟨b.re, hbC⟩ - mapScalar phi ⟨a.re, haC⟩ =
        mapScalar phi ⟨b.re - a.re, C.coordinateSpace.sub_mem hbC haC⟩ := by
      simpa only [mapScalar, Rat.cast_sub] using hlin.symm
    have hsign' : Real.sign (mapScalar phi ⟨b.re, hbC⟩ -
        mapScalar phi ⟨a.re, haC⟩) = Real.sign (b.re - a.re) := by
      simpa [mapPoint, mapScalar, ApproximationContext.vertexPoint,
        Tiling.AxisParallel.Axis.coord] using hsign
    have hdiff : 0 < mapScalar phi ⟨b.re, hbC⟩ -
        mapScalar phi ⟨a.re, haC⟩ := by
      have hsignone : Real.sign (mapScalar phi ⟨b.re, hbC⟩ -
          mapScalar phi ⟨a.re, haC⟩) = 1 := by
        rw [hsign', Real.sign_of_pos (show 0 < b.re - a.re by
          simpa [hab] using hpos)]
      rcases lt_trichotomy
          (mapScalar phi ⟨b.re, hbC⟩ - mapScalar phi ⟨a.re, haC⟩) 0 with hn | hz | hp
      · rw [Real.sign_of_neg hn] at hsignone
        norm_num at hsignone
      · rw [hz, Real.sign_zero] at hsignone
        norm_num at hsignone
      · exact hp
    have hdiff' : 0 < mapScalar phi
        ⟨b.re - a.re, C.coordinateSpace.sub_mem hbC haC⟩ := by
      rw [← hlin']
      exact hdiff
    have heq : (⟨d, hdC⟩ : C.coordinateSpace) =
        ⟨b.re - a.re, C.coordinateSpace.sub_mem hbC haC⟩ := by
      apply Subtype.ext
      exact hab
    rwa [← heq] at hdiff'
  have hmono : StrictMono (fun x ↦ mapScalar phi (lift x)) :=
    componentBoundaryMapped_strictMono C hTile phi lift hlift hpositive
  have hboundaryRange := componentBoundary_target_eq_mappedRange
    C hTile phi D P plates lift hlift
  let E : Set ℝ := componentBoundarySet C.region C.centres
  let E' : Set ℝ := componentBoundarySet D.deformedRegion
      (deformedCenterCarrier P.fullCenters)
  have hmem (x : ↥E) : mapScalar phi (lift x) ∈ E' := by
    change mapScalar phi (lift x) ∈
      componentBoundarySet D.deformedRegion
        (deformedCenterCarrier P.fullCenters)
    rw [hboundaryRange]
    exact ⟨lift x, ⟨x, rfl⟩, rfl⟩
  let boundaryEquiv : ↥E ≃ ↥E' :=
    Equiv.ofBijective (fun x ↦ ⟨mapScalar phi (lift x), hmem x⟩) (by
      constructor
      · intro x y hxy
        apply hmono.injective
        exact congrArg Subtype.val hxy
      · intro y
        have hy : y.1 ∈ mapScalarSet phi (Set.range lift) := by
          rw [← hboundaryRange]
          exact y.2
        rcases hy with ⟨z, ⟨x, rfl⟩, hzx⟩
        refine ⟨x, ?_⟩
        apply Subtype.ext
        exact hzx)
  have hfrontiff (Q : Continuous.VerticalPlate C.region C.centres)
      (c : ↥E) :
      c.1 ∈ frontier Q.base ↔
        (boundaryEquiv c).1 ∈ frontier (plates.plateEquiv Q).base := by
    obtain ⟨RQ⟩ := plateBoundaryReconstruction_exists
      C hTile phi D P plates.plateEquiv plates.centre_mem Q
    have hLiftEq (x : ↥(frontier Q.base)) :
        lift ⟨x.1, Set.mem_iUnion.2 ⟨Q, x.2⟩⟩ =
          RQ.boundaryLift x := by
      apply Subtype.ext
      rw [hlift, RQ.lift_coe]
    constructor
    · intro hc
      let x : ↥(frontier Q.base) := ⟨c.1, hc⟩
      rw [RQ.target_frontier]
      refine ⟨RQ.boundaryLift x, ⟨x, rfl⟩, ?_⟩
      change mapScalar phi (RQ.boundaryLift x) =
        mapScalar phi (lift c)
      rw [← hLiftEq x]
    · intro hc
      rw [RQ.target_frontier] at hc
      rcases hc with ⟨u, ⟨x, rfl⟩, hux⟩
      have hxE : x.1 ∈ E := Set.mem_iUnion.2 ⟨Q, x.2⟩
      have hEq : (⟨x.1, hxE⟩ : ↥E) = c := by
        apply hmono.injective
        change mapScalar phi (lift ⟨x.1, hxE⟩) =
          mapScalar phi (lift c)
        rw [show (⟨x.1, hxE⟩ : ↥E) =
          ⟨x.1, Set.mem_iUnion.2 ⟨Q, x.2⟩⟩ by rfl, hLiftEq]
        exact hux
      have hval := congrArg Subtype.val hEq
      rw [← hval]
      exact x.2
  refine ⟨⟨lift, boundaryEquiv, hlift, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    rfl
  · intro x y hxy
    exact hmono hxy
  · intro Q c d hcd hgap
    obtain ⟨RQ⟩ := plateBoundaryReconstruction_exists
      C hTile phi D P plates.plateEquiv plates.centre_mem Q
    have hEndpoint (x : ↥(frontier Q.base)) :
        (boundaryEquiv ⟨x.1, Set.mem_iUnion.2 ⟨Q, x.2⟩⟩).1 =
          mapScalar phi (RQ.boundaryLift x) := by
      change mapScalar phi (lift ⟨x.1, Set.mem_iUnion.2 ⟨Q, x.2⟩⟩) = _
      apply congrArg (mapScalar phi)
      apply Subtype.ext
      rw [hlift, RQ.lift_coe]
    have hfront_of_subset (hsub : Ioo c.1 d.1 ⊆ Q.base) :
        c.1 ∈ frontier Q.base ∧ d.1 ∈ frontier Q.base := by
      have hccl : c.1 ∈ closure Q.base := by
        apply closure_mono hsub
        rw [closure_Ioo hcd.ne]
        exact ⟨le_rfl, hcd.le⟩
      have hdcl : d.1 ∈ closure Q.base := by
        apply closure_mono hsub
        rw [closure_Ioo hcd.ne]
        exact ⟨hcd.le, le_rfl⟩
      constructor
      · rw [frontier]
        exact ⟨hccl, fun hi ↦ componentBoundary_not_mem_plateBase
          hTile c.2 Q (interior_subset hi)⟩
      · rw [frontier]
        exact ⟨hdcl, fun hi ↦ componentBoundary_not_mem_plateBase
          hTile d.2 Q (interior_subset hi)⟩
    constructor
    · intro hsub
      obtain ⟨hcQ, hdQ⟩ := hfront_of_subset hsub
      let a : ↥(frontier Q.base) := ⟨c.1, hcQ⟩
      let b : ↥(frontier Q.base) := ⟨d.1, hdQ⟩
      have hgapQ : Ioo a.1 b.1 ∩ frontier Q.base = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro x hx
        have hx' : x ∈ Ioo c.1 d.1 ∩ componentBoundarySet C.region C.centres :=
          ⟨hx.1, Set.mem_iUnion.2 ⟨Q, hx.2⟩⟩
        rw [hgap] at hx'
        exact hx'
      have hch := RQ.bounded_chamber a b hcd hgapQ
      have haEq := hEndpoint a
      have hbEq := hEndpoint b
      rw [← haEq, ← hbEq] at hch
      exact hch.1 hsub
    · intro htarget
      have hcT : (boundaryEquiv c).1 ∈
          frontier (plates.plateEquiv Q).base := by
        have hcd' : (boundaryEquiv c).1 < (boundaryEquiv d).1 := hmono hcd
        have hccl : (boundaryEquiv c).1 ∈
            closure (plates.plateEquiv Q).base := by
          apply closure_mono htarget
          rw [closure_Ioo hcd'.ne]
          exact ⟨le_rfl, hcd'.le⟩
        have hnot := componentBoundary_not_mem_plateBase
          P.full_tilesOn (boundaryEquiv c).2 (plates.plateEquiv Q)
        rw [frontier]
        exact ⟨hccl, fun hi ↦ hnot (interior_subset hi)⟩
      have hdT : (boundaryEquiv d).1 ∈
          frontier (plates.plateEquiv Q).base := by
        have hcd' : (boundaryEquiv c).1 < (boundaryEquiv d).1 := hmono hcd
        have hdcl : (boundaryEquiv d).1 ∈
            closure (plates.plateEquiv Q).base := by
          apply closure_mono htarget
          rw [closure_Ioo hcd'.ne]
          exact ⟨hcd'.le, le_rfl⟩
        have hnot := componentBoundary_not_mem_plateBase
          P.full_tilesOn (boundaryEquiv d).2 (plates.plateEquiv Q)
        rw [frontier]
        exact ⟨hdcl, fun hi ↦ hnot (interior_subset hi)⟩
      have hfrontc := (hfrontiff Q c).mpr hcT
      have hfrontd := (hfrontiff Q d).mpr hdT
      let a : ↥(frontier Q.base) := ⟨c.1, hfrontc⟩
      let b : ↥(frontier Q.base) := ⟨d.1, hfrontd⟩
      have hgapQ : Ioo a.1 b.1 ∩ frontier Q.base = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro x hx
        have hx' : x ∈ Ioo c.1 d.1 ∩ componentBoundarySet C.region C.centres :=
          ⟨hx.1, Set.mem_iUnion.2 ⟨Q, hx.2⟩⟩
        rw [hgap] at hx'
        exact hx'
      have hch := RQ.bounded_chamber a b hcd hgapQ
      have haEq := hEndpoint a
      have hbEq := hEndpoint b
      rw [← haEq, ← hbEq] at hch
      exact hch.2 htarget
  · intro Q c
    obtain ⟨RQ⟩ := plateBoundaryReconstruction_exists
      C hTile phi D P plates.plateEquiv plates.centre_mem Q
    have endpoint_eq (hcQ : c.1 ∈ frontier Q.base) :
        RQ.homeomorph c.1 = (boundaryEquiv c).1 := by
      let x : ↥(frontier Q.base) := ⟨c.1, hcQ⟩
      calc
        RQ.homeomorph c.1 = mapScalar phi (RQ.boundaryLift x) :=
          RQ.boundary_formula x
        _ = mapScalar phi (lift c) := by
          apply congrArg (mapScalar phi)
          apply Subtype.ext
          rw [RQ.lift_coe, hlift]
        _ = (boundaryEquiv c).1 := rfl
    constructor
    · rintro ⟨hsub, hgap⟩
      have hccl : c.1 ∈ closure Q.base := by
        apply closure_mono hsub
        rw [closure_Ioi]
        exact self_mem_Ici
      have hcQ : c.1 ∈ frontier Q.base := by
        rw [frontier]
        exact ⟨hccl, fun hi ↦ componentBoundary_not_mem_plateBase
          hTile c.2 Q (interior_subset hi)⟩
      have hceq := endpoint_eq hcQ
      constructor
      · intro y hy
        rw [RQ.target_base]
        let x : ℝ := RQ.homeomorph.symm y
        refine ⟨x, hsub ?_, RQ.homeomorph.apply_symm_apply y⟩
        have hHlt : RQ.homeomorph c.1 < RQ.homeomorph x := by
          simpa [x, hceq] using hy
        exact RQ.homeomorph_strictMono.lt_iff_lt.mp hHlt
      · rw [eq_empty_iff_forall_notMem]
        intro y hy
        let y' : ↥E' := ⟨y, hy.2⟩
        obtain ⟨x, hx⟩ := boundaryEquiv.surjective y'
        have hcx : c.1 < x.1 := by
          apply hmono.lt_iff_lt.mp
          change (boundaryEquiv c).1 < (boundaryEquiv x).1
          rw [hx]
          exact hy.1
        have hxgap : x.1 ∈ Ioi c.1 ∩ componentBoundarySet C.region C.centres :=
          ⟨hcx, x.2⟩
        rw [hgap] at hxgap
        exact hxgap
    · rintro ⟨hsub, hgap⟩
      have hccl : (boundaryEquiv c).1 ∈
          closure (plates.plateEquiv Q).base := by
        apply closure_mono hsub
        rw [closure_Ioi]
        exact self_mem_Ici
      have hcT : (boundaryEquiv c).1 ∈
          frontier (plates.plateEquiv Q).base := by
        rw [frontier]
        exact ⟨hccl, fun hi ↦ componentBoundary_not_mem_plateBase
          P.full_tilesOn (boundaryEquiv c).2 (plates.plateEquiv Q)
          (interior_subset hi)⟩
      have hcQ := (hfrontiff Q c).mpr hcT
      have hceq := endpoint_eq hcQ
      constructor
      · intro x hx
        have hHlt : (boundaryEquiv c).1 < RQ.homeomorph x := by
          rw [← hceq]
          exact RQ.homeomorph_strictMono hx
        have hmem := hsub hHlt
        rw [RQ.target_base] at hmem
        obtain ⟨z, hz, hzx⟩ := hmem
        have hzx' : z = x := RQ.homeomorph.injective hzx
        simpa [hzx'] using hz
      · rw [eq_empty_iff_forall_notMem]
        intro x hx
        let x' : ↥E := ⟨x, hx.2⟩
        have htargetLt : (boundaryEquiv c).1 < (boundaryEquiv x').1 :=
          hmono hx.1
        have htargetGap : (boundaryEquiv x').1 ∈
            Ioi (boundaryEquiv c).1 ∩
              componentBoundarySet D.deformedRegion
                (deformedCenterCarrier P.fullCenters) :=
          ⟨htargetLt, (boundaryEquiv x').2⟩
        rw [hgap] at htargetGap
        exact htargetGap
  · intro Q c
    obtain ⟨RQ⟩ := plateBoundaryReconstruction_exists
      C hTile phi D P plates.plateEquiv plates.centre_mem Q
    have endpoint_eq (hcQ : c.1 ∈ frontier Q.base) :
        RQ.homeomorph c.1 = (boundaryEquiv c).1 := by
      let x : ↥(frontier Q.base) := ⟨c.1, hcQ⟩
      calc
        RQ.homeomorph c.1 = mapScalar phi (RQ.boundaryLift x) :=
          RQ.boundary_formula x
        _ = mapScalar phi (lift c) := by
          apply congrArg (mapScalar phi)
          apply Subtype.ext
          rw [RQ.lift_coe, hlift]
        _ = (boundaryEquiv c).1 := rfl
    constructor
    · rintro ⟨hsub, hgap⟩
      have hccl : c.1 ∈ closure Q.base := by
        apply closure_mono hsub
        rw [closure_Iio]
        exact self_mem_Iic
      have hcQ : c.1 ∈ frontier Q.base := by
        rw [frontier]
        exact ⟨hccl, fun hi ↦ componentBoundary_not_mem_plateBase
          hTile c.2 Q (interior_subset hi)⟩
      have hceq := endpoint_eq hcQ
      constructor
      · intro y hy
        rw [RQ.target_base]
        let x : ℝ := RQ.homeomorph.symm y
        refine ⟨x, hsub ?_, RQ.homeomorph.apply_symm_apply y⟩
        have hHlt : RQ.homeomorph x < RQ.homeomorph c.1 := by
          simpa [x, hceq] using hy
        exact RQ.homeomorph_strictMono.lt_iff_lt.mp hHlt
      · rw [eq_empty_iff_forall_notMem]
        intro y hy
        let y' : ↥E' := ⟨y, hy.2⟩
        obtain ⟨x, hx⟩ := boundaryEquiv.surjective y'
        have hxc : x.1 < c.1 := by
          apply hmono.lt_iff_lt.mp
          change (boundaryEquiv x).1 < (boundaryEquiv c).1
          rw [hx]
          exact hy.1
        have hxgap : x.1 ∈ Iio c.1 ∩ componentBoundarySet C.region C.centres :=
          ⟨hxc, x.2⟩
        rw [hgap] at hxgap
        exact hxgap
    · rintro ⟨hsub, hgap⟩
      have hccl : (boundaryEquiv c).1 ∈
          closure (plates.plateEquiv Q).base := by
        apply closure_mono hsub
        rw [closure_Iio]
        exact self_mem_Iic
      have hcT : (boundaryEquiv c).1 ∈
          frontier (plates.plateEquiv Q).base := by
        rw [frontier]
        exact ⟨hccl, fun hi ↦ componentBoundary_not_mem_plateBase
          P.full_tilesOn (boundaryEquiv c).2 (plates.plateEquiv Q)
          (interior_subset hi)⟩
      have hcQ := (hfrontiff Q c).mpr hcT
      have hceq := endpoint_eq hcQ
      constructor
      · intro x hx
        have hHlt : RQ.homeomorph x < (boundaryEquiv c).1 := by
          rw [← hceq]
          exact RQ.homeomorph_strictMono hx
        have hmem := hsub hHlt
        rw [RQ.target_base] at hmem
        obtain ⟨z, hz, hzx⟩ := hmem
        have hzx' : z = x := RQ.homeomorph.injective hzx
        simpa [hzx'] using hz
      · rw [eq_empty_iff_forall_notMem]
        intro x hx
        let x' : ↥E := ⟨x, hx.2⟩
        have htargetLt : (boundaryEquiv x').1 < (boundaryEquiv c).1 :=
          hmono hx.1
        have htargetGap : (boundaryEquiv x').1 ∈
            Iio (boundaryEquiv c).1 ∩
              componentBoundarySet D.deformedRegion
                (deformedCenterCarrier P.fullCenters) :=
          ⟨htargetLt, (boundaryEquiv x').2⟩
        rw [hgap] at htargetGap
        exact htargetGap
  · intro Q t v w c d _htQ _hvw _hre _hside _hcd _hgap _hsub hc hx
    constructor
    · change mapScalar phi (lift c) <
        (D.planarHomeomorph v.1 + P.fullCenters t).re
      exact componentBoundary_map_endpoint_gt
        C hTile phi D P lift hlift hpositive c v t hc
    · change (D.planarHomeomorph v.1 + P.fullCenters t).re <
        mapScalar phi (lift d)
      exact componentBoundary_map_endpoint_lt
        C hTile phi D P lift hlift hpositive d v t hx
private structure FiniteContactTransportData
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D) where
  contact_iff : ∀ s t : ↥C.centres,
    Continuous.HorizontalProperContact C.region s.1 t.1 ↔
      Continuous.HorizontalProperContact D.deformedRegion
        (P.fullCenters s) (P.fullCenters t)
  plates : PlateTransportData C phi D P
  boundaries : ComponentBoundaryTransportData C phi D P plates

private theorem finiteContactTransportData_exists :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (_hfinite : ∀ a b a' b' : ↥C.region.vertices,
        (Tiling.AxisParallel.Structure.horizontalContactDisplacements
          C.region C.centres a b a' b').Finite),
      ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C epsilon₀ phi →
        ∀ (D : CoordinateDeformation C phi)
          (P : TwoStageDeformationSupportTransport C phi D),
          Nonempty (FiniteContactTransportData C phi D P) := by
  intro C hTile hfinite
  obtain ⟨Acrit⟩ := finiteTransportCriticalAlphabet_exists C hfinite
  obtain ⟨epsilon₀, hepsilon₀, hsignThreshold⟩ :=
    finiteTransportCriticalAlphabet_signThreshold C Acrit
  refine ⟨epsilon₀, hepsilon₀, ?_⟩
  intro phi hphi D P
  have hsign := hsignThreshold phi hphi
  have hContact : ∀ s t : ↥C.centres,
      Continuous.HorizontalProperContact C.region s.1 t.1 ↔
        Continuous.HorizontalProperContact D.deformedRegion
          (P.fullCenters s) (P.fullCenters t) := by
    intro s t
    exact ⟨endpointAlignedSeamCode_preserved
      C hTile phi D P Acrit hsign s t,
      endpointAlignedSeamCode_reflected
        C hTile phi D P Acrit hsign s t⟩
  have hcol : ∀ s t : ↥C.centres,
      Continuous.HorizontalProperContact C.region s.1 t.1 →
      ((s.1 : Tiling.Plane).re = (t.1 : Tiling.Plane).re ↔
        (P.fullCenters s).re = (P.fullCenters t).re) := by
    intro s t hcontact
    constructor
    · intro hst
      rw [P.fullCenters_apply, P.fullCenters_apply]
      simp [mapPoint, mapScalar, ApproximationContext.centrePoint, hst]
    · intro htarget
      by_cases hst : s = t
      · simp [hst]
      · have hadj :
            (Continuous.verticalPlateGraph C.region C.centres).Adj s t :=
          (Continuous.verticalPlateGraph_adj_iff s t).2 ⟨hst, hcontact⟩
        obtain ⟨_, a, b, a', b', _, hdelta⟩ :=
          (verticalPlateGraph_adj_iff_exists_horizontalContactDisplacement
            C.region C.centres s t).1 hadj
        let delta : ℝ := (t.1 - s.1).re
        have hdelta' : delta ∈
            horizontalContactDisplacements C.region C.centres a b a' b' := by
          simpa [delta] using hdelta
        by_cases hdeltaZero : delta = 0
        · exact (sub_eq_zero.mp (by simpa [delta] using hdeltaZero)).symm
        have hcritical : delta ∈ contactCriticalScalars C :=
          ⟨a, b, a', b', delta, hdelta', hdeltaZero, Or.inl rfl⟩
        have htransport : delta ∈ transportCriticalScalars C := Or.inl hcritical
        have hdeltaC : delta ∈ C.coordinateSpace := by
          dsimp only [delta, Complex.sub_re]
          exact C.coordinateSpace.sub_mem
            (C.centre_re_mem t.1 t.2) (C.centre_re_mem s.1 s.2)
        let deltaLift : C.coordinateSpace := ⟨delta, hdeltaC⟩
        have hlift : Acrit.lift ⟨delta, htransport⟩ = deltaLift := by
          apply Subtype.ext
          exact Acrit.lift_coe ⟨delta, htransport⟩
        have hsignDelta : Real.sign (mapScalar phi deltaLift) =
            Real.sign delta := by
          rw [← hlift]
          exact hsign ⟨delta, htransport⟩
        have hmapDelta : mapScalar phi deltaLift =
            (P.fullCenters t).re - (P.fullCenters s).re := by
          let tr : C.coordinateSpace :=
            ⟨t.1.re, C.centre_re_mem t.1 t.2⟩
          let sr : C.coordinateSpace :=
            ⟨s.1.re, C.centre_re_mem s.1 s.2⟩
          have hsub : deltaLift = tr - sr := by
            apply Subtype.ext
            simp [deltaLift, delta, tr, sr]
          rw [hsub, mapScalar, map_sub, Rat.cast_sub,
            P.fullCenters_apply, P.fullCenters_apply]
          simp only [tr, sr, mapPoint, ApproximationContext.centrePoint,
            Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
            mul_one, sub_zero, add_zero]
          rfl
        have hzero : (P.fullCenters t).re -
            (P.fullCenters s).re = 0 := by
          rw [htarget]
          ring
        have hsignZero : Real.sign delta = 0 := by
          rw [← hsignDelta, hmapDelta, hzero, Real.sign_zero]
        exact (hdeltaZero (Real.sign_eq_zero_iff.mp hsignZero)).elim
  obtain ⟨plates⟩ :=
    contactGraphIso_constructsPlateTransport C phi D P hContact hcol
  obtain ⟨boundaries⟩ := componentBoundaryTransport_exists
    C hTile phi D P plates
  exact ⟨⟨hContact, plates, boundaries⟩⟩

theorem finiteContactWitnesses :
    ∀ (C : ApproximationContext.{0})
      (_hTile : TilesOn C.region C.centres univ)
      (_hfinite : ∀ a b a' b' : ↥C.region.vertices,
        (Tiling.AxisParallel.Structure.horizontalContactDisplacements
          C.region C.centres a b a' b').Finite),
      ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C epsilon₀ phi →
        ∀ (D : CoordinateDeformation C phi),
        ∀ (P : TwoStageDeformationSupportTransport C phi D),
          (∀ s t : ↥C.centres,
            Continuous.HorizontalProperContact C.region s.1 t.1 ↔
              Continuous.HorizontalProperContact D.deformedRegion
                (P.fullCenters s) (P.fullCenters t)) ∧
          ∃ (plateEquiv : Continuous.VerticalPlate C.region C.centres ≃
                Continuous.VerticalPlate D.deformedRegion
                  (deformedCenterCarrier P.fullCenters))
            (boundaryLift : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                C.region C.centres) → C.coordinateSpace)
            (boundaryEquiv :
              ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  C.region C.centres) ≃
                ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  D.deformedRegion (deformedCenterCarrier P.fullCenters))),
            (∀ x, (boundaryLift x : ℝ) = x.1) ∧
            (∀ x, (boundaryEquiv x : ℝ) =
              mapScalar phi (boundaryLift x)) ∧
            StrictMono boundaryEquiv ∧
            (∀ (Q : Continuous.VerticalPlate C.region C.centres)
                (t : ↥C.centres),
              (t.1 : Tiling.Plane) ∈ Q.centres ↔
                P.fullCenters t ∈ (plateEquiv Q).centres) ∧
            (∀ Q : Continuous.VerticalPlate C.region C.centres,
              Continuous.IsVerticalColumn Q ↔
                Continuous.IsVerticalColumn (plateEquiv Q)) ∧
            (∀ (Q : Continuous.VerticalPlate C.region C.centres)
                (c d : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  C.region C.centres)),
              c.1 < d.1 →
              Ioo c.1 d.1 ∩
                  Tiling.AxisParallel.Structure.componentBoundarySet
                    C.region C.centres = ∅ →
              (Ioo c.1 d.1 ⊆ Q.base ↔
                Ioo (boundaryEquiv c).1 (boundaryEquiv d).1 ⊆
                  (plateEquiv Q).base)) ∧
            (∀ (Q : Continuous.VerticalPlate C.region C.centres)
                (c : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  C.region C.centres)),
              (Ioi c.1 ⊆ Q.base ∧
                  Ioi c.1 ∩
                    Tiling.AxisParallel.Structure.componentBoundarySet
                      C.region C.centres = ∅) ↔
                (Ioi (boundaryEquiv c).1 ⊆ (plateEquiv Q).base ∧
                  Ioi (boundaryEquiv c).1 ∩
                    Tiling.AxisParallel.Structure.componentBoundarySet
                      D.deformedRegion
                        (deformedCenterCarrier P.fullCenters) = ∅)) ∧
            (∀ (Q : Continuous.VerticalPlate C.region C.centres)
                (c : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  C.region C.centres)),
              (Iio c.1 ⊆ Q.base ∧
                  Iio c.1 ∩
                    Tiling.AxisParallel.Structure.componentBoundarySet
                      C.region C.centres = ∅) ↔
                (Iio (boundaryEquiv c).1 ⊆ (plateEquiv Q).base ∧
                  Iio (boundaryEquiv c).1 ∩
                    Tiling.AxisParallel.Structure.componentBoundarySet
                      D.deformedRegion
                        (deformedCenterCarrier P.fullCenters) = ∅)) ∧
            ∀ (Q : Continuous.VerticalPlate C.region C.centres)
                (t : ↥C.centres) (v w : ↥C.region.vertices)
                (c d : ↥(Tiling.AxisParallel.Structure.componentBoundarySet
                  C.region C.centres)),
              (t.1 : Tiling.Plane) ∈ Q.centres →
              v.1 ≠ w.1 → v.1.re = w.1.re →
              openSegment ℝ v.1 w.1 ⊆
                frontier C.region.support \ C.region.vertices →
              c.1 < d.1 →
              Ioo c.1 d.1 ∩
                  Tiling.AxisParallel.Structure.componentBoundarySet
                    C.region C.centres = ∅ →
              Ioo c.1 d.1 ⊆ Q.base →
              c.1 < (v.1 + (t.1 : Tiling.Plane)).re →
              (v.1 + (t.1 : Tiling.Plane)).re < d.1 →
              (boundaryEquiv c).1 <
                  (D.planarHomeomorph v.1 + P.fullCenters t).re ∧
                (D.planarHomeomorph v.1 + P.fullCenters t).re <
                  (boundaryEquiv d).1 := by
  intro C hTile hfinite
  obtain ⟨epsilon₀, hepsilon₀, htransport⟩ :=
    finiteContactTransportData_exists C hTile hfinite
  refine ⟨epsilon₀, hepsilon₀, ?_⟩
  intro phi hphi D P
  obtain ⟨data⟩ := htransport phi hphi D P
  refine ⟨data.contact_iff, ?_⟩
  exact ⟨data.plates.plateEquiv, data.boundaries.boundaryLift,
    data.boundaries.boundaryEquiv, data.boundaries.lift_coe,
    data.boundaries.boundary_formula, data.boundaries.strictMono,
    data.plates.centre_mem, data.plates.column_iff,
    data.boundaries.bounded_chamber_label,
    data.boundaries.rightRay_label, data.boundaries.leftRay_label,
    data.boundaries.translatedVerticalSide_between⟩

end Tiling.AxisParallel.Structure
