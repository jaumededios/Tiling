import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.Geometry.PolygonalTopology
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Approximation

noncomputable section

/-- The translated vertices `V + T` of a normalized approximation context. -/
def ApproximationContext.translatedVertices
    (C : ApproximationContext) : Set Tiling.Plane :=
  C.region.vertices + C.centres

/-- A translated vertex, lifted to the coordinate-controlled point subtype. -/
def ApproximationContext.translatedVertexPoint
    (C : ApproximationContext) (a : ↥C.translatedVertices) :
    {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} := by
  refine ⟨a.1, ?_, ?_⟩
  · rcases a.2 with ⟨v, hv, t, ht, hvt⟩
    rw [← hvt]
    simpa only [Complex.add_re] using
      C.coordinateSpace.add_mem (C.vertex_re_mem v hv) (C.centre_re_mem t ht)
  · rcases a.2 with ⟨v, hv, t, ht, hvt⟩
    rw [← hvt]
    simpa only [Complex.add_im] using
      C.coordinateSpace.add_mem (C.vertex_im_mem v hv) (C.centre_im_mem t ht)

/-- A selected coordinate of a translated-vertex difference, with its subspace membership. -/
def ApproximationContext.translatedDifferenceScalar
    (C : ApproximationContext) (axis : Tiling.AxisParallel.Axis)
    (a b : ↥C.translatedVertices) : C.coordinateSpace := by
  cases axis with
  | horizontal =>
      exact ⟨((a : Tiling.Plane) - (b : Tiling.Plane)).re, by
        have ha := (C.translatedVertexPoint a).2.1
        have hb := (C.translatedVertexPoint b).2.1
        change (a : Tiling.Plane).re ∈ C.coordinateSpace at ha
        change (b : Tiling.Plane).re ∈ C.coordinateSpace at hb
        simpa only [Complex.sub_re] using C.coordinateSpace.sub_mem ha hb⟩
  | vertical =>
      exact ⟨((a : Tiling.Plane) - (b : Tiling.Plane)).im, by
        have ha := (C.translatedVertexPoint a).2.2
        have hb := (C.translatedVertexPoint b).2.2
        change (a : Tiling.Plane).im ∈ C.coordinateSpace at ha
        change (b : Tiling.Plane).im ∈ C.coordinateSpace at hb
        simpa only [Complex.sub_im] using C.coordinateSpace.sub_mem ha hb⟩

/-- The coordinatewise rational image of a translated vertex. -/
def mapTranslatedVertex
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (a : ↥C.translatedVertices) : Tiling.Plane :=
  mapPoint phi (C.translatedVertexPoint a)

/-- The absolute projected length of a labelled vertex pair. -/
def projectedVertexPairLength
    (C : ApproximationContext) (axis : Tiling.AxisParallel.Axis) :
    (↥C.region.vertices × ↥C.region.vertices) → ℝ :=
  fun e ↦ |Tiling.AxisParallel.Axis.coord axis
    ((e.2 : Tiling.Plane) - (e.1 : Tiling.Plane))|

/-- The absolute projected length of the mapped labelled vertex pair. -/
def mappedProjectedVertexPairLength
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Tiling.AxisParallel.Axis) :
    (↥C.region.vertices × ↥C.region.vertices) → ℝ :=
  fun e ↦ |Tiling.AxisParallel.Axis.coord axis
    (mapPoint phi (C.vertexPoint e.2.1 e.2.2) -
      mapPoint phi (C.vertexPoint e.1.1 e.1.2))|

/-- Coordinate witnesses of translated-vertex differences shorter than `R`. -/
def boundedScalarDifferences
    (C : ApproximationContext) (R : ℝ) : Set C.coordinateSpace :=
  {x | ∃ (axis : Tiling.AxisParallel.Axis) (a b : ↥C.translatedVertices),
    dist (a : Tiling.Plane) b < R ∧
      (x : ℝ) = Tiling.AxisParallel.Axis.coord axis
        ((a : Tiling.Plane) - (b : Tiling.Plane))}

/-- Differences of two short finite sums of intrinsic projected edge lengths. -/
def shortProjectedEdgeSumDifferences
    (C : ApproximationContext) (M : ℝ) : Set C.coordinateSpace :=
  {x | ∃ (axis : Tiling.AxisParallel.Axis) (n m : ℕ),
    (n : ℝ) < M ∧ (m : ℝ) < M ∧
    ∃ (e : Fin n → (↥C.region.vertices × ↥C.region.vertices))
      (f : Fin m → (↥C.region.vertices × ↥C.region.vertices)),
      (∀ j : Fin n,
        (e j).1 ≠ (e j).2 ∧
          openSegment ℝ ((e j).1 : Tiling.Plane) ((e j).2 : Tiling.Plane) ⊆
            frontier C.region.openCarrier ∧
          ∀ u : ↥C.region.vertices,
            (u : Tiling.Plane) ∉
              openSegment ℝ ((e j).1 : Tiling.Plane) ((e j).2 : Tiling.Plane)) ∧
      (∀ j : Fin m,
        (f j).1 ≠ (f j).2 ∧
          openSegment ℝ ((f j).1 : Tiling.Plane) ((f j).2 : Tiling.Plane) ⊆
            frontier C.region.openCarrier ∧
          ∀ u : ↥C.region.vertices,
            (u : Tiling.Plane) ∉
              openSegment ℝ ((f j).1 : Tiling.Plane) ((f j).2 : Tiling.Plane)) ∧
      (x : ℝ) =
        Finset.univ.sum (projectedVertexPairLength C axis ∘ e) -
          Finset.univ.sum (projectedVertexPairLength C axis ∘ f)}

/-- All finite arithmetic and metric controls chosen at one common approximation threshold. -/
structure FLCControlPackage (C : ApproximationContext) where
  source_hasFLC : Tiling.AxisParallel.HasFLC C.centres
  bandBase : Set ℝ
  bandBase_nonempty : bandBase.Nonempty
  bandBase_open : IsOpen bandBase
  bandPeriod : ℝ
  bandPeriod_pos : 0 < bandPeriod
  bandBase_periodic : bandPeriod +ᵥ bandBase = bandBase
  target_eq : C.target = {z : Tiling.Plane | z.re ∈ bandBase}
  source_tilesOn : Tiling.AxisParallel.TilesOn C.region C.centres C.target
  scale : ℝ
  scale_pos : 0 < scale
  controlRadius : ℝ
  scale_lt_controlRadius : scale < controlRadius
  localError : ℝ
  localError_pos : 0 < localError
  localError_eq : localError = scale⁻¹
  coordinateError : ℝ
  coordinateError_pos : 0 < coordinateError
  coordinateError_small : Real.sqrt 2 * coordinateError < localError
  boundedDifferences : Finset Tiling.Plane
  boundedDifferences_exact :
    (boundedDifferences : Set Tiling.Plane) =
      ((C.translatedVertices - C.translatedVertices) ∩
        Metric.closedBall 0 controlRadius)
  scalarAlphabet : Finset C.coordinateSpace
  scalarAlphabet_exact :
    (scalarAlphabet : Set C.coordinateSpace) =
      boundedScalarDifferences C controlRadius
  edgeSumAlphabet : Finset C.coordinateSpace
  edgeSumAlphabet_exact :
    (edgeSumAlphabet : Set C.coordinateSpace) =
      shortProjectedEdgeSumDifferences C scale
  threshold : ℝ
  threshold_pos : 0 < threshold
  forces_good : ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
    IsEpsilonApproximation C threshold phi → IsGoodApproximation C phi
  scalar_close : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ z ∈ scalarAlphabet ∪ edgeSumAlphabet,
      |mapScalar phi z - (z : ℝ)| < coordinateError
  scalar_sign : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ z ∈ scalarAlphabet ∪ edgeSumAlphabet,
      Real.sign (mapScalar phi z) = Real.sign (z : ℝ)
  scalar_zero_iff : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ z ∈ scalarAlphabet ∪ edgeSumAlphabet,
      mapScalar phi z = 0 ↔ (z : ℝ) = 0
  scalar_injective : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ z ∈ scalarAlphabet ∪ edgeSumAlphabet,
      ∀ z' ∈ scalarAlphabet ∪ edgeSumAlphabet,
        mapScalar phi z = mapScalar phi z' ↔ z = z'
  local_accuracy : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ a b : ↥C.translatedVertices,
      dist (a : Tiling.Plane) b < scale →
      dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
        ((a : Tiling.Plane) - (b : Tiling.Plane)) < localError
  coarse_inverse : ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C threshold phi →
    ∀ a b : ↥C.translatedVertices,
      dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) < scale / 2 →
        dist (a : Tiling.Plane) b < scale
  mesh_after_map : ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
    ∃ mesh : ℕ, 0 < mesh ∧
      (∀ t : ↥C.centres, ∃ p q : ℤ,
        mapPoint phi (C.centrePoint t.1 t.2) =
          (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
            (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I) ∧
      (∀ v : ↥C.region.vertices, ∃ p q : ℤ,
        mapPoint phi (C.vertexPoint v.1 v.2) =
          (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
            (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I)

/-- One threshold reflects sign, zero, and equality on a finite scalar alphabet. -/
theorem approximation_reflectsSignAndEquality
    (C : ApproximationContext) (Z : Finset C.coordinateSpace) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
        IsEpsilonApproximation C epsilon0 phi →
        (∀ z ∈ Z, Real.sign (mapScalar phi z) = Real.sign (z : ℝ)) ∧
        (∀ z ∈ Z, mapScalar phi z = 0 ↔ (z : ℝ) = 0) ∧
        ∀ z ∈ Z, ∀ z' ∈ Z, mapScalar phi z = mapScalar phi z' ↔ z = z' := by
  classical
  let differences : Finset C.coordinateSpace :=
    (Z.product Z).image fun zz ↦ zz.1 - zz.2
  let controls := Z ∪ differences
  obtain ⟨epsilon0, hepsilon0, hsign⟩ :=
    approximation_preservesSign_finset C controls
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro phi hphi
  have hsignZ : ∀ z ∈ Z,
      Real.sign (mapScalar phi z) = Real.sign (z : ℝ) := by
    intro z hz
    exact hsign phi hphi z (Finset.mem_union_left differences hz)
  refine ⟨hsignZ, ?_, ?_⟩
  · intro z hz
    constructor
    · intro hzero
      apply Real.sign_eq_zero_iff.mp
      rw [← hsignZ z hz]
      exact Real.sign_eq_zero_iff.mpr hzero
    · intro hzero
      apply Real.sign_eq_zero_iff.mp
      rw [hsignZ z hz]
      exact Real.sign_eq_zero_iff.mpr hzero
  · intro z hz z' hz'
    constructor
    · intro heq
      have hdiff : z - z' ∈ controls := by
        apply Finset.mem_union_right Z
        exact Finset.mem_image.mpr ⟨(z, z'), Finset.mem_product.mpr ⟨hz, hz'⟩, rfl⟩
      have hmapzero : mapScalar phi (z - z') = 0 := by
        have hrat : phi z = phi z' := by
          change ((phi z : ℚ) : ℝ) = ((phi z' : ℚ) : ℝ) at heq
          exact_mod_cast heq
        simp only [mapScalar]
        rw [map_sub, sub_eq_zero.mpr hrat]
        norm_num
      have hcoezero : ((z - z' : C.coordinateSpace) : ℝ) = 0 := by
        rw [← Real.sign_eq_zero_iff, ← hsign phi hphi (z - z') hdiff]
        exact Real.sign_eq_zero_iff.mpr hmapzero
      apply Subtype.ext
      exact sub_eq_zero.mp hcoezero
    · rintro rfl
      rfl

/-- Membership in the deformed intrinsic vertex set, with its source label retained. -/
theorem deformedRegion_vertices
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (w : Tiling.Plane) :
    w ∈ Tiling.vertexSet D.deformedRegion.support ↔
      ∃ v : ↑C.region.vertices,
        w = mapPoint phi (C.vertexPoint v.1 v.2) := by
  rw [← D.deformedRegion.vertices_eq_vertexSet, D.vertices_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, D.vertex_agreement v hv⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v.1, v.2, D.vertex_agreement v.1 v.2⟩

/-- Finite local complexity is unchanged after adding the finite intrinsic vertex set. -/
theorem boundedDifferenceSet_finite
    (C : ApproximationContext)
    (hFLC : Tiling.AxisParallel.HasFLC C.centres)
    (R : ℝ) (hR : 0 < R) :
    ((C.translatedVertices - C.translatedVertices) ∩
      Metric.closedBall 0 R).Finite := by
  have htranslated : Tiling.AxisParallel.HasFLC C.translatedVertices := by
    rw [ApproximationContext.translatedVertices, ← C.region.coe_vertexFinset, add_comm]
    exact hFLC.add_finset C.region.vertexFinset
  exact htranslated.2 R hR

/-- A periodic-band tiling has relatively dense centres and translated vertices. -/
theorem translatedVertices_relativelyDense
    (C : ApproximationContext) (X : Set ℝ) (alpha : ℝ)
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (halpha : 0 < alpha) (hXperiodic : alpha +ᵥ X = X)
    (htarget : C.target = {z : Tiling.Plane | z.re ∈ X})
    (hTile : Tiling.AxisParallel.TilesOn C.region C.centres C.target) :
    ∃ rho : ℝ, 0 < rho ∧
      (∀ z : Tiling.Plane, ∃ a ∈ C.translatedVertices, dist z a < rho) ∧
      ∀ z : Tiling.Plane, ∃ t ∈ C.centres, dist z t < rho := by
  obtain ⟨x₀, hx₀⟩ := hXnonempty
  obtain ⟨R, hRpos, hR⟩ := C.region.isPolygonal.isBounded.exists_pos_norm_le
  let rho := alpha + R + 2
  have hrho : 0 < rho := by dsimp [rho]; linarith
  have htargetOpen : IsOpen C.target := by
    rw [htarget]
    exact hXopen.preimage Complex.continuous_re
  have halphaPeriod : alpha ∈ Tiling.AxisParallel.periodGroup X := hXperiodic
  have hcentres : ∀ z : Tiling.Plane, ∃ t ∈ C.centres, dist z t < rho := by
    intro z
    let n : ℤ := ⌊(z.re - x₀) / alpha⌋
    let xz : ℝ := x₀ + (n : ℝ) * alpha
    let zX : Tiling.Plane := (xz : ℂ) + (z.im : ℂ) * Complex.I
    have hnle : (n : ℝ) ≤ (z.re - x₀) / alpha := Int.floor_le _
    have hnlt : (z.re - x₀) / alpha < (n : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hxzLower : 0 ≤ z.re - xz := by
      dsimp only [xz]
      have := mul_le_mul_of_nonneg_right hnle halpha.le
      rw [div_mul_cancel₀ _ (ne_of_gt halpha)] at this
      linarith
    have hxzUpper : z.re - xz < alpha := by
      dsimp only [xz]
      have := mul_lt_mul_of_pos_right hnlt halpha
      rw [div_mul_cancel₀ _ (ne_of_gt halpha)] at this
      linarith
    have hnPeriod : (n • alpha : ℝ) ∈ Tiling.AxisParallel.periodGroup X :=
      (Tiling.AxisParallel.periodGroup X).zsmul_mem halphaPeriod n
    have hnPeriodic : (n • alpha : ℝ) +ᵥ X = X :=
      (Tiling.AxisParallel.periodGroup_isAddSubgroup X _).mp hnPeriod
    have hxz : xz ∈ X := by
      have hmem : (n • alpha : ℝ) + x₀ ∈ X := by
        rw [← hnPeriodic]
        exact ⟨x₀, hx₀, rfl⟩
      simpa [xz, mul_comm, add_comm] using hmem
    have hzXTarget : zX ∈ C.target := by
      rw [htarget]
      simpa [zX] using hxz
    obtain ⟨delta, hdelta, hdeltaBall⟩ :=
      (Metric.isOpen_iff.mp htargetOpen) zX hzXTarget
    let r := min delta 1
    have hr : 0 < r := lt_min hdelta one_pos
    have hrdelta : r ≤ delta := min_le_left _ _
    have hrone : r ≤ 1 := min_le_right _ _
    have hrball : Metric.ball zX r ⊆ C.target :=
      (Metric.ball_subset_ball hrdelta).trans hdeltaBall
    have hcovered : ∃ w ∈ Metric.ball zX r,
        ∃ t : ↥C.centres, w ∈ ((t : Tiling.Plane) +ᵥ C.region.openCarrier) := by
      by_contra hnone
      push Not at hnone
      have haeOutside : ∀ᵐ w ∂MeasureTheory.volume, w ∉ Metric.ball zX r := by
        filter_upwards [hTile.2.2] with w hw
        intro hwball
        obtain ⟨t, hwt⟩ := hw.mp (hrball hwball)
        exact hnone w hwball t hwt
      have hzero : MeasureTheory.volume (Metric.ball zX r) = 0 :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr haeOutside
      have hpos : 0 < MeasureTheory.volume (Metric.ball zX r) :=
        Metric.isOpen_ball.measure_pos MeasureTheory.volume
          ⟨zX, Metric.mem_ball_self hr⟩
      rw [hzero] at hpos
      exact (lt_irrefl 0 hpos)
    obtain ⟨w, hwball, t, hwt⟩ := hcovered
    have hwtSupport : -(t : Tiling.Plane) + w ∈ C.region.support := by
      have hwtOpen : -(t : Tiling.Plane) + w ∈ C.region.openCarrier := by
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hwt
      change -(t : Tiling.Plane) + w ∈ interior C.region.support at hwtOpen
      apply interior_subset
      exact hwtOpen
    have hwtBound : dist w (t : Tiling.Plane) ≤ R := by
      have := hR (-(t : Tiling.Plane) + w) hwtSupport
      simpa only [dist_eq_norm, sub_eq_add_neg, add_comm] using this
    have hzXdist : dist z zX < alpha := by
      rw [Complex.dist_of_im_eq (by simp [zX])]
      have hzXre : zX.re = xz := by simp [zX]
      rw [hzXre, Real.dist_eq]
      rw [abs_of_nonneg hxzLower]
      exact hxzUpper
    have hwball' : dist zX w < r := by
      simpa only [Metric.mem_ball, dist_comm] using hwball
    have hwnear : dist zX w < 1 := lt_of_lt_of_le hwball' hrone
    refine ⟨t, t.2, ?_⟩
    calc
      dist z (t : Tiling.Plane) ≤ dist z zX + dist zX w + dist w t :=
        (dist_triangle4 z zX w t)
      _ < alpha + 1 + R := by linarith
      _ < rho := by dsimp [rho]; linarith
  refine ⟨rho, hrho, ?_, hcentres⟩
  · intro z
    obtain ⟨t, ht, hzt⟩ := hcentres z
    refine ⟨t, ?_, hzt⟩
    exact ⟨0, C.zero_mem_vertices, t, ht, zero_add t⟩

/-- A relatively dense FLC set is generated from one base point by finitely many bounded steps. -/
theorem boundedSteps_generateCoordinateSpace
    {Y : Set Tiling.Plane}
    (hYFLC : Tiling.AxisParallel.HasFLC Y)
    (rho : ℝ) (hrho : 0 < rho)
    (hYdense : ∀ z : Tiling.Plane, ∃ y ∈ Y, dist z y < rho)
    (y0 : Tiling.Plane) (hy0 : y0 ∈ Y) :
    ∃ steps : Finset Tiling.Plane,
      (∀ d ∈ steps, -d ∈ steps) ∧
      (steps : Set Tiling.Plane) ⊆ Y - Y ∧
      ∀ y ∈ Y, y - y0 ∈ AddSubgroup.closure (steps : Set Tiling.Plane) := by
  classical
  let stepSet := (Y - Y) ∩ Metric.closedBall 0 (3 * rho)
  have hstepFinite : stepSet.Finite := hYFLC.2 (3 * rho) (by linarith)
  let steps := hstepFinite.toFinset
  refine ⟨steps, ?_, ?_, ?_⟩
  · intro d hd
    have hdSet : d ∈ stepSet :=
      hstepFinite.mem_toFinset.mp (show d ∈ hstepFinite.toFinset from hd)
    apply hstepFinite.mem_toFinset.mpr
    refine ⟨?_, ?_⟩
    · rcases hdSet.1 with ⟨a, ha, b, hb, hab⟩
      exact ⟨b, hb, a, ha, by rw [← hab]; simp [sub_eq_add_neg]⟩
    · simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg] using hdSet.2
  · intro d hd
    have hdSet : d ∈ stepSet :=
      hstepFinite.mem_toFinset.mp (show d ∈ hstepFinite.toFinset from hd)
    exact hdSet.1
  · intro y hy
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (dist y y0 / rho)
    have hratioNonneg : 0 ≤ dist y y0 / rho := div_nonneg dist_nonneg hrho.le
    have hnRealPos : 0 < (n : ℝ) := lt_of_le_of_lt hratioNonneg hn
    have hnPos : 0 < n := by exact_mod_cast hnRealPos
    have hsmall : dist y y0 / (n : ℝ) < rho := by
      rw [div_lt_iff₀ hnRealPos]
      have := (div_lt_iff₀ hrho).mp hn
      nlinarith
    let c : Fin (n + 1) → Tiling.Plane := fun i ↦
      y0 + ((i : ℝ) / (n : ℝ)) • (y - y0)
    choose q hqY hqDist using fun i : Fin (n + 1) ↦ hYdense (c i)
    let p : Fin (n + 1) → Tiling.Plane := fun i ↦
      if i = 0 then y0 else if i = Fin.last n then y else q i
    have hpY : ∀ i, p i ∈ Y := by
      intro i
      simp only [p]
      split
      · exact hy0
      · split
        · exact hy
        · exact hqY i
    have hcZero : c 0 = y0 := by simp [c]
    have hcLast : c (Fin.last n) = y := by
      change y0 + ((n : ℝ) / (n : ℝ)) • (y - y0) = y
      rw [div_self (ne_of_gt hnRealPos), one_smul]
      abel
    have hpClose : ∀ i, dist (p i) (c i) < rho := by
      intro i
      by_cases hi0 : i = 0
      · subst i
        rw [hcZero]
        simp [p, hrho]
      · by_cases hiLast : i = Fin.last n
        · subst i
          rw [hcLast]
          have hlast0 : Fin.last n ≠ (0 : Fin (n + 1)) := by
            intro h
            have := congrArg Fin.val h
            simp only [Fin.val_last, Fin.val_zero] at this
            omega
          simp [p, hlast0, hrho]
        · simpa only [p, hi0, hiLast, if_false, dist_comm] using hqDist i
    have hcStep : ∀ i : Fin n,
        dist (c i.succ) (c i.castSucc) = dist y y0 / (n : ℝ) := by
      intro i
      rw [dist_eq_norm]
      change ‖(y0 + (((i.val + 1 : ℕ) : ℝ) / (n : ℝ)) • (y - y0)) -
          (y0 + ((i.val : ℝ) / (n : ℝ)) • (y - y0))‖ =
        dist y y0 / (n : ℝ)
      rw [add_sub_add_left_eq_sub, ← sub_smul]
      have hcoef :
          ((i.val + 1 : ℕ) : ℝ) / (n : ℝ) - (i.val : ℝ) / (n : ℝ) =
            ((n : ℝ)⁻¹) := by
        push_cast
        field_simp
        ring
      rw [hcoef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnRealPos),
        dist_eq_norm, norm_sub_rev, div_eq_mul_inv]
      ring
    have hpStep : ∀ i : Fin n, dist (p i.succ) (p i.castSucc) < 3 * rho := by
      intro i
      have h₁ := dist_triangle (p i.succ) (c i.succ) (p i.castSucc)
      have h₂ := dist_triangle (c i.succ) (c i.castSucc) (p i.castSucc)
      rw [hcStep i] at h₂
      have hclose₁ := hpClose i.succ
      have hclose₂ := hpClose i.castSucc
      rw [dist_comm (p i.castSucc)] at hclose₂
      linarith
    have hstepMem : ∀ i : Fin n, p i.succ - p i.castSucc ∈ steps := by
      intro i
      apply hstepFinite.mem_toFinset.mpr
      refine ⟨?_, ?_⟩
      · exact ⟨p i.succ, hpY i.succ, p i.castSucc, hpY i.castSucc, rfl⟩
      · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        simpa only [dist_eq_norm] using (hpStep i).le
    let pNat : ℕ → Tiling.Plane := fun k ↦
      if hk : k < n + 1 then p ⟨k, hk⟩ else 0
    have hsum :
        ∑ k ∈ Finset.range n, (pNat (k + 1) - pNat k) ∈
          AddSubgroup.closure (steps : Set Tiling.Plane) := by
      apply AddSubgroup.sum_mem
      intro k hk
      have hkn : k < n := Finset.mem_range.mp hk
      have hk1 : k + 1 < n + 1 := by omega
      have hk0 : k < n + 1 := by omega
      have hmem := hstepMem (⟨k, hkn⟩ : Fin n)
      apply AddSubgroup.subset_closure
      simp only [pNat, dif_pos hk1, dif_pos hk0]
      change p ⟨k + 1, hk1⟩ - p ⟨k, hk0⟩ ∈ steps
      simpa using hmem
    rw [Finset.sum_range_sub] at hsum
    have hpNatLast : pNat n = y := by
      have hnlt : n < n + 1 := by omega
      simp only [pNat, dif_pos hnlt]
      have hfin : (⟨n, hnlt⟩ : Fin (n + 1)) = Fin.last n := by ext; rfl
      rw [hfin]
      have hlast0 : Fin.last n ≠ (0 : Fin (n + 1)) := by
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last, Fin.val_zero] at this
        omega
      simp only [p, if_neg hlast0, if_pos]
    have hpNatZero : pNat 0 = y0 := by
      have hzero : 0 < n + 1 := by omega
      simp only [pNat, dif_pos hzero]
      simp [p]
    rwa [hpNatLast, hpNatZero] at hsum

/-- Every rational image of a periodic FLC tiling lies on one common rational mesh. -/
theorem exists_commonRationalMesh
    (C : ApproximationContext)
    (X : Set ℝ) (alpha : ℝ)
    (hFLC : Tiling.AxisParallel.HasFLC C.centres)
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (halpha : 0 < alpha) (hXperiodic : alpha +ᵥ X = X)
    (htarget : C.target = {z : Tiling.Plane | z.re ∈ X})
    (hTile : Tiling.AxisParallel.TilesOn C.region C.centres C.target) :
    ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
      ∃ mesh : ℕ, 0 < mesh ∧
        (∀ t : ↥C.centres, ∃ p q : ℤ,
          mapPoint phi (C.centrePoint t.1 t.2) =
            (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
              (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I) ∧
        (∀ v : ↥C.region.vertices, ∃ p q : ℤ,
          mapPoint phi (C.vertexPoint v.1 v.2) =
            (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
              (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I) := by
  classical
  intro phi
  obtain ⟨rho, hrho, htranslatedDense, _⟩ :=
    translatedVertices_relativelyDense C X alpha hXnonempty hXopen halpha
      hXperiodic htarget hTile
  have htranslatedFLC : Tiling.AxisParallel.HasFLC C.translatedVertices := by
    rw [ApproximationContext.translatedVertices, ← C.region.coe_vertexFinset, add_comm]
    exact hFLC.add_finset C.region.vertexFinset
  have hzeroTranslated : (0 : Tiling.Plane) ∈ C.translatedVertices :=
    ⟨0, C.zero_mem_vertices, 0, C.zero_mem_centres, zero_add 0⟩
  obtain ⟨steps, _, hstepsSub, hgenerated⟩ :=
    boundedSteps_generateCoordinateSpace htranslatedFLC rho hrho htranslatedDense
      0 hzeroTranslated
  let controlledPoints : AddSubgroup Tiling.Plane :=
    { carrier := {z | z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}
      zero_mem' := ⟨C.coordinateSpace.zero_mem, C.coordinateSpace.zero_mem⟩
      add_mem' := by
        rintro a b ⟨haRe, haIm⟩ ⟨hbRe, hbIm⟩
        exact ⟨C.coordinateSpace.add_mem haRe hbRe,
          C.coordinateSpace.add_mem haIm hbIm⟩
      neg_mem' := by
        rintro a ⟨haRe, haIm⟩
        exact ⟨C.coordinateSpace.neg_mem haRe, C.coordinateSpace.neg_mem haIm⟩ }
  have hstepsControlled : (steps : Set Tiling.Plane) ⊆ controlledPoints := by
    intro d hd
    obtain ⟨a, ha, b, hb, rfl⟩ := hstepsSub hd
    have haCoords := (C.translatedVertexPoint ⟨a, ha⟩).2
    have hbCoords := (C.translatedVertexPoint ⟨b, hb⟩).2
    exact ⟨C.coordinateSpace.sub_mem haCoords.1 hbCoords.1,
      C.coordinateSpace.sub_mem haCoords.2 hbCoords.2⟩
  have hclosureControlled : AddSubgroup.closure (steps : Set Tiling.Plane) ≤
      controlledPoints := (AddSubgroup.closure_le controlledPoints).2 hstepsControlled
  let mappedCoord (axis : Tiling.AxisParallel.Axis) (z : Tiling.Plane)
      (hz : z ∈ AddSubgroup.closure (steps : Set Tiling.Plane)) : ℚ :=
    phi ⟨Tiling.AxisParallel.Axis.coord axis z, by
      have hzc := hclosureControlled hz
      cases axis with
      | horizontal => exact hzc.1
      | vertical => exact hzc.2⟩
  let values : Finset ℚ :=
    (steps.attach.image fun d : {x // x ∈ steps} ↦
      mappedCoord Tiling.AxisParallel.Axis.horizontal d.1
        (AddSubgroup.subset_closure d.2)) ∪
    (steps.attach.image fun d : {x // x ∈ steps} ↦
      mappedCoord Tiling.AxisParallel.Axis.vertical d.1
        (AddSubgroup.subset_closure d.2))
  let mesh : ℕ := values.prod Rat.den
  have hmesh : 0 < mesh := by
    dsimp only [mesh]
    exact Finset.prod_pos fun q _ ↦ q.den_pos
  have value_on_mesh {r : ℚ} (hr : r ∈ values) :
      ∃ p : ℤ, r = (p : ℚ) / (mesh : ℚ) := by
    have hden : r.den ∣ mesh := by
      dsimp only [mesh]
      exact Finset.dvd_prod_of_mem (fun q : ℚ ↦ q.den) hr
    obtain ⟨k, hk⟩ := hden
    have hkpos : 0 < k := by nlinarith [r.den_pos]
    refine ⟨r.num * (k : ℤ), ?_⟩
    calc
      r = (r.num : ℚ) / (r.den : ℚ) := r.num_div_den.symm
      _ = ((r.num * (k : ℤ) : ℤ) : ℚ) / (mesh : ℚ) := by
        rw [hk]
        push_cast
        field_simp
  have mappedCoord_on_mesh (axis : Tiling.AxisParallel.Axis)
      (z : Tiling.Plane)
      (hz : z ∈ AddSubgroup.closure (steps : Set Tiling.Plane)) :
      ∃ p : ℤ, mappedCoord axis z hz = (p : ℚ) / (mesh : ℚ) := by
    refine AddSubgroup.closure_induction (p := fun z hz ↦
      ∃ p : ℤ, mappedCoord axis z hz = (p : ℚ) / (mesh : ℚ)) ?_ ?_ ?_ ?_ hz
    · intro d hd
      apply value_on_mesh
      cases axis with
      | horizontal =>
          apply Finset.mem_union_left
          exact Finset.mem_image.mpr
            ⟨(⟨d, hd⟩ : {x // x ∈ steps}), Finset.mem_attach _ _, rfl⟩
      | vertical =>
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr
            ⟨(⟨d, hd⟩ : {x // x ∈ steps}), Finset.mem_attach _ _, rfl⟩
    · refine ⟨0, ?_⟩
      cases axis <;>
        simp only [mappedCoord, Tiling.AxisParallel.Axis.coord, Int.cast_zero,
          zero_div] <;>
        rw [← phi.map_zero] <;>
        congr 1
    · intro a b ha hb
      rintro ⟨pa, hpa⟩ ⟨pb, hpb⟩
      refine ⟨pa + pb, ?_⟩
      have hadd : mappedCoord axis (a + b) (AddSubgroup.add_mem _ ha hb) =
          mappedCoord axis a ha + mappedCoord axis b hb := by
        simp only [mappedCoord]
        rw [← map_add]
        congr 1
        apply Subtype.ext
        cases axis <;> simp [Tiling.AxisParallel.Axis.coord]
      rw [hadd, hpa, hpb]
      push_cast
      ring
    · intro a ha
      rintro ⟨pa, hpa⟩
      refine ⟨-pa, ?_⟩
      have hneg : mappedCoord axis (-a) (AddSubgroup.neg_mem _ ha) =
          -mappedCoord axis a ha := by
        simp only [mappedCoord]
        rw [← map_neg]
        congr 1
        apply Subtype.ext
        cases axis <;> simp [Tiling.AxisParallel.Axis.coord]
      rw [hneg, hpa]
      push_cast
      ring
  have point_on_mesh (a : ↥C.translatedVertices) :
      ∃ p q : ℤ, mapTranslatedVertex phi a =
        (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
          (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I := by
    have haGen : (a : Tiling.Plane) ∈
        AddSubgroup.closure (steps : Set Tiling.Plane) := by
      have := hgenerated a a.2
      simpa using this
    obtain ⟨p, hp⟩ := mappedCoord_on_mesh
      Tiling.AxisParallel.Axis.horizontal a haGen
    obtain ⟨q, hq⟩ := mappedCoord_on_mesh
      Tiling.AxisParallel.Axis.vertical a haGen
    have hpReal := congrArg (fun r : ℚ ↦ (r : ℝ)) hp
    have hqReal := congrArg (fun r : ℚ ↦ (r : ℝ)) hq
    refine ⟨p, q, ?_⟩
    apply Complex.ext
    · simpa [mapTranslatedVertex, mapPoint, mapScalar, mappedCoord,
        ApproximationContext.translatedVertexPoint,
        Tiling.AxisParallel.Axis.coord] using hpReal
    · simpa [mapTranslatedVertex, mapPoint, mapScalar, mappedCoord,
        ApproximationContext.translatedVertexPoint,
        Tiling.AxisParallel.Axis.coord] using hqReal
  refine ⟨mesh, hmesh, ?_, ?_⟩
  · intro t
    let a : ↥C.translatedVertices := ⟨t, by
      exact ⟨0, C.zero_mem_vertices, t, t.2, zero_add (t : Tiling.Plane)⟩⟩
    obtain ⟨p, q, hpq⟩ := point_on_mesh a
    refine ⟨p, q, ?_⟩
    rw [← hpq]
    change mapPoint phi (C.centrePoint t.1 t.2) =
      mapPoint phi (C.translatedVertexPoint a)
    congr 1
  · intro v
    let a : ↥C.translatedVertices := ⟨v, by
      exact ⟨v, v.2, 0, C.zero_mem_centres, add_zero (v : Tiling.Plane)⟩⟩
    obtain ⟨p, q, hpq⟩ := point_on_mesh a
    refine ⟨p, q, ?_⟩
    rw [← hpq]
    change mapPoint phi (C.vertexPoint v.1 v.2) =
      mapPoint phi (C.translatedVertexPoint a)
    congr 1

private theorem mapScalar_translatedDifferenceScalar
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Tiling.AxisParallel.Axis) (a b : ↑C.translatedVertices) :
    mapScalar phi (C.translatedDifferenceScalar axis a b) =
      Tiling.AxisParallel.Axis.coord axis
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) := by
  cases axis <;>
    simp only [ApproximationContext.translatedDifferenceScalar, mapTranslatedVertex,
      mapPoint, mapScalar, Tiling.AxisParallel.Axis.coord, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add]
  all_goals
    norm_cast
    rw [← map_sub]
    rfl

theorem deformation_reflectsFiniteValues
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Tiling.AxisParallel.Axis)
    (a b c d : ↑C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < P.controlRadius)
    (hcd : dist (c : Tiling.Plane) d < P.controlRadius) :
    Real.sign (Tiling.AxisParallel.Axis.coord axis
      (mapTranslatedVertex phi a - mapTranslatedVertex phi b)) =
        Real.sign (Tiling.AxisParallel.Axis.coord axis
          ((a : Tiling.Plane) - (b : Tiling.Plane))) ∧
    (Tiling.AxisParallel.Axis.coord axis
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 ↔
      Tiling.AxisParallel.Axis.coord axis
        ((a : Tiling.Plane) - (b : Tiling.Plane)) = 0) ∧
    (Tiling.AxisParallel.Axis.coord axis
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) =
      Tiling.AxisParallel.Axis.coord axis
        (mapTranslatedVertex phi c - mapTranslatedVertex phi d) →
      Tiling.AxisParallel.Axis.coord axis
        ((a : Tiling.Plane) - (b : Tiling.Plane)) =
      Tiling.AxisParallel.Axis.coord axis
        ((c : Tiling.Plane) - (d : Tiling.Plane))) := by
  let zab := C.translatedDifferenceScalar axis a b
  let zcd := C.translatedDifferenceScalar axis c d
  have habVal : (zab : ℝ) = Tiling.AxisParallel.Axis.coord axis
      ((a : Tiling.Plane) - (b : Tiling.Plane)) := by cases axis <;> rfl
  have hcdVal : (zcd : ℝ) = Tiling.AxisParallel.Axis.coord axis
      ((c : Tiling.Plane) - (d : Tiling.Plane)) := by cases axis <;> rfl
  have hzabScalar : zab ∈ P.scalarAlphabet := by
    have hzab : zab ∈ boundedScalarDifferences C P.controlRadius := by
      exact ⟨axis, a, b, hab, habVal⟩
    rw [← P.scalarAlphabet_exact] at hzab
    exact hzab
  have hzcdScalar : zcd ∈ P.scalarAlphabet := by
    have hzcd : zcd ∈ boundedScalarDifferences C P.controlRadius := by
      exact ⟨axis, c, d, hcd, hcdVal⟩
    rw [← P.scalarAlphabet_exact] at hzcd
    exact hzcd
  have hzab : zab ∈ P.scalarAlphabet ∪ P.edgeSumAlphabet :=
    Finset.mem_union_left _ hzabScalar
  have hzcd : zcd ∈ P.scalarAlphabet ∪ P.edgeSumAlphabet :=
    Finset.mem_union_left _ hzcdScalar
  have habMap := mapScalar_translatedDifferenceScalar phi axis a b
  have hcdMap := mapScalar_translatedDifferenceScalar phi axis c d
  refine ⟨?_, ?_, ?_⟩
  · rw [← habMap, ← habVal]
    exact P.scalar_sign phi hphi zab hzab
  · rw [← habMap, ← habVal]
    exact P.scalar_zero_iff phi hphi zab hzab
  · intro heq
    rw [← habMap, ← hcdMap] at heq
    have heqz := (P.scalar_injective phi hphi zab hzab zcd hzcd).mp heq
    exact habVal ▸ hcdVal ▸ congrArg Subtype.val heqz

theorem deformation_injectiveOnTranslatedVertices
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi) :
    Function.Injective (mapTranslatedVertex phi) := by
  intro a b hab
  have himage : dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) <
      P.scale / 2 := by
    rw [hab, dist_self]
    exact half_pos P.scale_pos
  have hsource := P.coarse_inverse phi hphi a b himage
  have hcontrol := lt_trans hsource P.scale_lt_controlRadius
  have hrefH := deformation_reflectsFiniteValues P phi hphi
    Tiling.AxisParallel.Axis.horizontal a b a b hcontrol hcontrol
  have hrefV := deformation_reflectsFiniteValues P phi hphi
    Tiling.AxisParallel.Axis.vertical a b a b hcontrol hcontrol
  apply Subtype.ext
  apply Complex.ext
  · have hmapped : Tiling.AxisParallel.Axis.coord Tiling.AxisParallel.Axis.horizontal
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 := by
      rw [hab]
      simp [Tiling.AxisParallel.Axis.coord]
    have hsource0 := hrefH.2.1.mp hmapped
    simpa [Tiling.AxisParallel.Axis.coord] using sub_eq_zero.mp hsource0
  · have hmapped : Tiling.AxisParallel.Axis.coord Tiling.AxisParallel.Axis.vertical
        (mapTranslatedVertex phi a - mapTranslatedVertex phi b) = 0 := by
      rw [hab]
      simp [Tiling.AxisParallel.Axis.coord]
    have hsource0 := hrefV.2.1.mp hmapped
    simpa [Tiling.AxisParallel.Axis.coord] using sub_eq_zero.mp hsource0

/-- The local-accuracy field of an `FLCControlPackage`. -/
theorem deformation_localAccuracy
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (a b : ↥C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < P.scale) :
    dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
      ((a : Tiling.Plane) - (b : Tiling.Plane)) < P.localError :=
  P.local_accuracy phi hphi a b hab

/-- The independently established coarse-inverse field of an `FLCControlPackage`. -/
theorem deformation_coarselyProper
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (a b : ↥C.translatedVertices)
    (hab : dist (mapTranslatedVertex phi a)
      (mapTranslatedVertex phi b) < P.scale / 2) :
    dist (a : Tiling.Plane) b < P.scale :=
  P.coarse_inverse phi hphi a b hab

end

universe u

private structure RelativeDenseSegmentChain (Y : Set Tiling.Plane) (L R : ℝ)
    (a b : ↥Y) where
  length : ℕ
  length_pos : 0 < length
  point : Fin (length + 1) → ↥Y
  point_zero : point 0 = a
  point_last : point (Fin.last length) = b
  step_lt : ∀ i : Fin length,
    dist (point i.castSucc : Tiling.Plane) (point i.succ : Tiling.Plane) < R
  length_le : (length : ℝ) ≤ dist (a : Tiling.Plane) b / L + 1

private def CoarseControlConditions (M rho L R eta : ℝ) : Prop :=
  0 < M ∧ 0 < rho ∧ 0 < L ∧ M < R ∧ L + 2 * rho < R ∧ 0 < eta ∧
  Real.sqrt 2 * eta < min M⁻¹ (M / 2) ∧
  eta / L < (1 / Real.sqrt 2 - 1 / 2) / 2 ∧
  eta < (1 / Real.sqrt 2 - 1 / 2) * M / 2

private theorem boundedScalarDifferences_finite
    (C : ApproximationContext.{u}) (hFLC : HasFLC C.centres)
    (R : ℝ) (hR : 0 < R) : (boundedScalarDifferences C R).Finite := by
  let E : Set Tiling.Plane :=
    (C.translatedVertices - C.translatedVertices) ∩ Metric.closedBall 0 R
  have hE : E.Finite := boundedDifferenceSet_finite C hFLC R hR
  let coordLift (axis : Axis) (z : Tiling.Plane)
      (hz : z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace) :
      C.coordinateSpace :=
    match axis with
    | .horizontal => ⟨z.re, hz.1⟩
    | .vertical => ⟨z.im, hz.2⟩
  have hsub : boundedScalarDifferences C R ⊆
      (fun z : ↥E ↦ coordLift .horizontal z.1 (by
        obtain ⟨a, ha, b, hb, hab⟩ := z.2.1
        rw [← hab]
        exact ⟨C.coordinateSpace.sub_mem
          (C.translatedVertexPoint ⟨a, ha⟩).2.1
          (C.translatedVertexPoint ⟨b, hb⟩).2.1,
          C.coordinateSpace.sub_mem
          (C.translatedVertexPoint ⟨a, ha⟩).2.2
          (C.translatedVertexPoint ⟨b, hb⟩).2.2⟩)) '' univ ∪
      (fun z : ↥E ↦ coordLift .vertical z.1 (by
        obtain ⟨a, ha, b, hb, hab⟩ := z.2.1
        rw [← hab]
        exact ⟨C.coordinateSpace.sub_mem
          (C.translatedVertexPoint ⟨a, ha⟩).2.1
          (C.translatedVertexPoint ⟨b, hb⟩).2.1,
          C.coordinateSpace.sub_mem
          (C.translatedVertexPoint ⟨a, ha⟩).2.2
          (C.translatedVertexPoint ⟨b, hb⟩).2.2⟩)) '' univ := by
    rintro x ⟨axis, a, b, hab, hx⟩
    have hdmem : (a.1 - b.1) ∈ E := by
      refine ⟨⟨a.1, a.2, b.1, b.2, rfl⟩, ?_⟩
      simpa [Metric.mem_closedBall, dist_eq_norm] using hab.le
    let d : ↥E := ⟨a.1 - b.1, hdmem⟩
    cases axis with
    | horizontal =>
        apply Or.inl
        refine ⟨d, Set.mem_univ d, ?_⟩
        apply Subtype.ext
        simpa [coordLift, d, Axis.coord, Complex.sub_re] using hx.symm
    | vertical =>
        apply Or.inr
        refine ⟨d, Set.mem_univ d, ?_⟩
        apply Subtype.ext
        simpa [coordLift, d, Axis.coord, Complex.sub_im] using hx.symm
  let _ := hE.fintype
  exact ((Set.finite_univ.image _).union (Set.finite_univ.image _)).subset hsub

private theorem shortProjectedEdgeSumDifferences_finite
    (C : ApproximationContext.{u}) (M : ℝ) :
    (shortProjectedEdgeSumDifferences C M).Finite := by
  classical
  have hVfinite : C.region.vertices.Finite := by
    rw [C.region.vertices_eq_vertexSet]
    exact C.region.isPolygonal.vertexSet_finite
  let _ : Fintype ↥C.region.vertices := hVfinite.fintype
  let _ : Fintype Axis := ⟨{.horizontal, .vertical}, by
    intro axis
    cases axis <;> simp⟩
  let N := Nat.ceil M
  let Chain := Σ n : Fin N,
    Fin n.1 → (↥C.region.vertices × ↥C.region.vertices)
  let _ : Fintype Chain := Fintype.ofFinite Chain
  let value (axis : Axis) (c : Chain) : ℝ :=
    Finset.univ.sum (projectedVertexPairLength C axis ∘ c.2)
  let difference : Axis × Chain × Chain → ℝ :=
    fun d ↦ value d.1 d.2.1 - value d.1 d.2.2
  have hrange : (Set.range difference).Finite := Set.finite_range difference
  apply Set.Finite.of_finite_image
    (f := fun x : C.coordinateSpace ↦ (x : ℝ))
  · apply hrange.subset
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨axis, n, m, hn, hm, e, f, he, hf, hvalue⟩ := hx
    have hnN : n < N := (Nat.lt_ceil).2 hn
    have hmN : m < N := (Nat.lt_ceil).2 hm
    let ce : Chain := ⟨⟨n, hnN⟩, e⟩
    let cf : Chain := ⟨⟨m, hmN⟩, f⟩
    refine ⟨(axis, ce, cf), ?_⟩
    simpa [difference, value, ce, cf] using hvalue.symm
  · intro x _ y _ hxy
    exact Subtype.ext hxy

private theorem finiteControls_commonThreshold
    (C : ApproximationContext.{u}) (Z : Finset C.coordinateSpace)
    (eta : ℝ) (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
        IsEpsilonApproximation C epsilon phi →
        IsGoodApproximation C phi ∧
        (∀ z ∈ Z, |mapScalar phi z - (z : ℝ)| < eta) ∧
        (∀ z ∈ Z, Real.sign (mapScalar phi z) = Real.sign (z : ℝ)) ∧
        (∀ z ∈ Z, mapScalar phi z = 0 ↔ (z : ℝ) = 0) ∧
        ∀ z ∈ Z, ∀ z' ∈ Z, mapScalar phi z = mapScalar phi z' ↔ z = z' := by
  obtain ⟨eg, heg, hgood⟩ := isGoodApproximation_of_sufficientlyFine C
  obtain ⟨ec, hec, hclose⟩ := approximation_uniformOn_finset C Z eta heta
  obtain ⟨er, her, hreflect⟩ := approximation_reflectsSignAndEquality C Z
  let epsilon := min eg (min ec er)
  have hepsilon : 0 < epsilon := lt_min heg (lt_min hec her)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi
  have hphig := hphi.of_le (min_le_left _ _)
  have hphic := hphi.of_le
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hphir := hphi.of_le
    (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hsign, hzero, hinj⟩ := hreflect phi hphir
  exact ⟨hgood phi hphig, hclose phi hphic, hsign, hzero, hinj⟩

private theorem finiteControlAlphabets_exists
    (C : ApproximationContext.{u}) (M R : ℝ)
    (hFLC : HasFLC C.centres) (hR : 0 < R) :
    ∃ (boundedDifferences : Finset Tiling.Plane)
      (scalarAlphabet edgeSumAlphabet : Finset C.coordinateSpace),
      (boundedDifferences : Set Tiling.Plane) =
        ((C.translatedVertices - C.translatedVertices) ∩ Metric.closedBall 0 R) ∧
      (scalarAlphabet : Set C.coordinateSpace) = boundedScalarDifferences C R ∧
      (edgeSumAlphabet : Set C.coordinateSpace) = shortProjectedEdgeSumDifferences C M := by
  classical
  let hD := boundedDifferenceSet_finite C hFLC R hR
  let hS := boundedScalarDifferences_finite C hFLC R hR
  let hE := shortProjectedEdgeSumDifferences_finite C M
  exact ⟨hD.toFinset, hS.toFinset, hE.toFinset,
    hD.coe_toFinset, hS.coe_toFinset, hE.coe_toFinset⟩

private theorem scalarControl_localAccuracy
    {C : ApproximationContext.{u}} (R eta : ℝ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (heta : 0 < eta)
    (hclose : ∀ z ∈ boundedScalarDifferences C R,
      |mapScalar phi z - (z : ℝ)| < eta)
    (a b : ↥C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < R) :
    dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
      ((a : Tiling.Plane) - (b : Tiling.Plane)) < Real.sqrt 2 * eta := by
  let source := (a : Tiling.Plane) - (b : Tiling.Plane)
  let image := mapTranslatedVertex phi a - mapTranslatedVertex phi b
  let error := image - source
  have hcoord (axis : Axis) : |Axis.coord axis error| < eta := by
    let z := C.translatedDifferenceScalar axis a b
    have hzmem : z ∈ boundedScalarDifferences C R := by
      refine ⟨axis, a, b, hab, ?_⟩
      cases axis <;> rfl
    have hz := hclose z hzmem
    rw [mapScalar_translatedDifferenceScalar] at hz
    cases axis <;>
      simpa [z, ApproximationContext.translatedDifferenceScalar, error, image, source,
        Axis.coord, Complex.sub_re, Complex.sub_im]
        using hz
  have hre := hcoord Axis.horizontal
  have him := hcoord Axis.vertical
  have hreSq : error.re ^ 2 < eta ^ 2 := by
    have := (sq_lt_sq₀ (abs_nonneg error.re) heta.le).2 hre
    simpa [sq_abs] using this
  have himSq : error.im ^ 2 < eta ^ 2 := by
    have := (sq_lt_sq₀ (abs_nonneg error.im) heta.le).2 him
    simpa [sq_abs] using this
  have hsqrt : 0 ≤ Real.sqrt 2 * eta := mul_nonneg (Real.sqrt_nonneg _) heta.le
  have hsq : ‖error‖ ^ 2 < (Real.sqrt 2 * eta) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, mul_pow]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith
  have herr : ‖error‖ < Real.sqrt 2 * eta :=
    (sq_lt_sq₀ (norm_nonneg error) hsqrt).1 hsq
  simpa [dist_eq_norm, error, image, source, sub_sub] using herr

private theorem relativeDenseSegmentChain_exists
    (Y : Set Tiling.Plane) (rho L R : ℝ) (hrho : 0 < rho) (hL : 0 < L)
    (hLR : L + 2 * rho < R)
    (hdense : ∀ z : Tiling.Plane, ∃ y ∈ Y, dist z y < rho)
    (a b : ↥Y) (hLab : L < dist (a : Tiling.Plane) b) :
    Nonempty (RelativeDenseSegmentChain Y L R a b) := by
  let D := dist (a : Tiling.Plane) b
  let N := Nat.ceil (D / L)
  have hDL : 1 < D / L := by
    apply (lt_div_iff₀ hL).2
    simpa [D] using hLab
  have hNpos : 0 < N := Nat.ceil_pos.mpr (lt_trans zero_lt_one hDL)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstepLe : D / (N : ℝ) ≤ L := by
    have hceil : D / L ≤ (N : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hNreal]
    have := (div_le_iff₀ hL).mp hceil
    nlinarith
  have hNle : (N : ℝ) ≤ D / L + 1 :=
    le_of_lt (Nat.ceil_lt_add_one (div_nonneg (by simp [D]) hL.le))
  let c : Fin (N + 1) → Tiling.Plane := fun i ↦
    (a : Tiling.Plane) + ((i : ℝ) / (N : ℝ)) •
      ((b : Tiling.Plane) - (a : Tiling.Plane))
  choose q hqY hqdist using fun i : Fin (N + 1) ↦ hdense (c i)
  let p : Fin (N + 1) → Tiling.Plane := fun i ↦
    if i = 0 then a else if i = Fin.last N then b else q i
  have hpY (i : Fin (N + 1)) : p i ∈ Y := by
    simp only [p]
    split
    · exact a.2
    · split
      · exact b.2
      · exact hqY i
  have hcZero : c 0 = a := by simp [c]
  have hcLast : c (Fin.last N) = b := by
    change (a : Tiling.Plane) + ((N : ℝ) / (N : ℝ)) •
      ((b : Tiling.Plane) - (a : Tiling.Plane)) = b
    rw [div_self (ne_of_gt hNreal), one_smul]
    abel
  have hpClose (i : Fin (N + 1)) : dist (p i) (c i) < rho := by
    by_cases hi0 : i = 0
    · subst i
      rw [hcZero]
      simp [p, hrho]
    · by_cases hilast : i = Fin.last N
      · subst i
        rw [hcLast]
        have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_zero] at this
          omega
        simp [p, hlast0, hrho]
      · simpa [p, hi0, hilast, dist_comm] using hqdist i
  have hcStep (i : Fin N) :
      dist (c i.succ) (c i.castSucc) = D / (N : ℝ) := by
    rw [dist_eq_norm]
    change ‖((a : Tiling.Plane) + (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) •
        ((b : Tiling.Plane) - (a : Tiling.Plane))) -
      ((a : Tiling.Plane) + ((i.val : ℝ) / (N : ℝ)) •
        ((b : Tiling.Plane) - (a : Tiling.Plane)))‖ = D / (N : ℝ)
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    have hcoef : (((i.val + 1 : ℕ) : ℝ) / (N : ℝ)) -
        (i.val : ℝ) / (N : ℝ) = (N : ℝ)⁻¹ := by
      push_cast
      field_simp
      ring
    rw [hcoef, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hNreal),
      show ‖(b : Tiling.Plane) - (a : Tiling.Plane)‖ = D by
        rw [norm_sub_rev]
        simp [D, dist_eq_norm], div_eq_mul_inv]
    ring
  have hpStep (i : Fin N) :
      dist (p i.castSucc) (p i.succ) < R := by
    calc
      dist (p i.castSucc) (p i.succ) ≤
          dist (p i.castSucc) (c i.castSucc) +
            dist (c i.castSucc) (c i.succ) + dist (c i.succ) (p i.succ) :=
        dist_triangle4 _ _ _ _
      _ < rho + (D / (N : ℝ)) + rho := by
        rw [dist_comm (c i.castSucc) (c i.succ), hcStep]
        have hlast := hpClose i.succ
        rw [dist_comm] at hlast
        linarith [hpClose i.castSucc, hlast]
      _ ≤ rho + L + rho := by linarith
      _ < R := by linarith
  let point : Fin (N + 1) → ↥Y := fun i ↦ ⟨p i, hpY i⟩
  refine ⟨⟨N, hNpos, point, ?_, ?_, ?_, ?_⟩⟩
  · apply Subtype.ext
    simp [point, p]
  · apply Subtype.ext
    have hlast0 : Fin.last N ≠ (0 : Fin (N + 1)) := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_zero] at this
      omega
    simp [point, p, hlast0]
  · exact hpStep
  · exact hNle

private theorem exists_dominantAxis (z : Tiling.Plane) :
    ∃ axis : Axis, ‖z‖ / Real.sqrt 2 ≤ |Axis.coord axis z| := by
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  by_cases h : |z.re| ≤ |z.im|
  · refine ⟨Axis.vertical, ?_⟩
    change ‖z‖ / Real.sqrt 2 ≤ |z.im|
    rw [div_le_iff₀ hsqrt]
    have hre : z.re ^ 2 ≤ z.im ^ 2 := by
      simpa [sq_abs] using (sq_le_sq₀ (abs_nonneg z.re) (abs_nonneg z.im)).2 h
    have him : 0 ≤ z.im ^ 2 := sq_nonneg _
    have hsq : ‖z‖ ^ 2 ≤ (Real.sqrt 2 * |z.im|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
      nlinarith
    simpa [mul_comm] using (sq_le_sq₀ (norm_nonneg z)
      (mul_nonneg hsqrt.le (abs_nonneg z.im))).1 hsq
  · refine ⟨Axis.horizontal, ?_⟩
    change ‖z‖ / Real.sqrt 2 ≤ |z.re|
    rw [div_le_iff₀ hsqrt]
    have him : z.im ^ 2 ≤ z.re ^ 2 := by
      have himabs : |z.im| ≤ |z.re| := le_of_not_ge h
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg z.im) (abs_nonneg z.re)).2 himabs
    have hre : 0 ≤ z.re ^ 2 := sq_nonneg _
    have hsq : ‖z‖ ^ 2 ≤ (Real.sqrt 2 * |z.re|) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
      nlinarith
    simpa [mul_comm] using (sq_le_sq₀ (norm_nonneg z)
      (mul_nonneg hsqrt.le (abs_nonneg z.re))).1 hsq

private theorem scalarControl_coarseInverse
    {C : ApproximationContext.{u}} (M rho L R eta : ℝ)
    (hcond : CoarseControlConditions M rho L R eta)
    (hdense : ∀ z : Tiling.Plane, ∃ a ∈ C.translatedVertices, dist z a < rho)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hclose : ∀ z ∈ boundedScalarDifferences C R,
      |mapScalar phi z - (z : ℝ)| < eta)
    (a b : ↥C.translatedVertices)
    (himage : dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) < M / 2) :
    dist (a : Tiling.Plane) b < M := by
  rcases hcond with
    ⟨hM, hrho, hL, hMR, hLR, heta, herrSmall, hetaL, hetaM⟩
  let D := dist (a : Tiling.Plane) b
  by_contra hnot
  have hMD : M ≤ D := le_of_not_gt hnot
  by_cases hDR : D < R
  · have hlocal := scalarControl_localAccuracy R eta phi heta hclose a b hDR
    have htriangle : D ≤
        dist (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
          ((a : Tiling.Plane) - (b : Tiling.Plane)) +
        dist (mapTranslatedVertex phi a) (mapTranslatedVertex phi b) := by
      dsimp [D]
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm]
      change ‖(a : Tiling.Plane) - b‖ ≤
        ‖(mapTranslatedVertex phi a - mapTranslatedVertex phi b) -
          ((a : Tiling.Plane) - b)‖ +
        ‖mapTranslatedVertex phi a - mapTranslatedVertex phi b‖
      calc
        ‖(a : Tiling.Plane) - b‖ ≤
            ‖((a : Tiling.Plane) - b) -
              (mapTranslatedVertex phi a - mapTranslatedVertex phi b)‖ +
              ‖mapTranslatedVertex phi a - mapTranslatedVertex phi b‖ :=
          by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using norm_add_le
              (((a : Tiling.Plane) - b) -
                (mapTranslatedVertex phi a - mapTranslatedVertex phi b))
              (mapTranslatedVertex phi a - mapTranslatedVertex phi b)
        _ = _ := by rw [norm_sub_rev]
    have herrHalf : Real.sqrt 2 * eta < M / 2 :=
      lt_of_lt_of_le herrSmall (min_le_right _ _)
    linarith
  · have hRD : R ≤ D := le_of_not_gt hDR
    have hLD : L < D := by linarith
    let chain := Classical.choice
      (relativeDenseSegmentChain_exists C.translatedVertices rho L R hrho hL hLR
        hdense a b hLD)
    obtain ⟨axis, haxis⟩ :=
      exists_dominantAxis ((b : Tiling.Plane) - (a : Tiling.Plane))
    let f : ℕ → ℝ := fun k ↦
      if hk : k < chain.length + 1 then
        Axis.coord axis (mapTranslatedVertex phi (chain.point ⟨k, hk⟩)) else 0
    let g : ℕ → ℝ := fun k ↦
      if hk : k < chain.length + 1 then
        Axis.coord axis (chain.point ⟨k, hk⟩ : Tiling.Plane) else 0
    have hedge (k : ℕ) (hk : k < chain.length) :
        |(f (k + 1) - f k) - (g (k + 1) - g k)| < eta := by
      have hk1 : k + 1 < chain.length + 1 := by omega
      have hk0 : k < chain.length + 1 := by omega
      let i : Fin chain.length := ⟨k, hk⟩
      let z := C.translatedDifferenceScalar axis (chain.point i.succ)
        (chain.point i.castSucc)
      have hzmem : z ∈ boundedScalarDifferences C R := by
        refine ⟨axis, chain.point i.succ, chain.point i.castSucc,
          by simpa [dist_comm] using chain.step_lt i, ?_⟩
        cases axis <;> rfl
      have hz := hclose z hzmem
      rw [mapScalar_translatedDifferenceScalar] at hz
      simp only [f, g, dif_pos hk1, dif_pos hk0]
      cases axis <;>
        simpa [i, z, ApproximationContext.translatedDifferenceScalar,
          Axis.coord, Complex.sub_re, Complex.sub_im] using hz
    have herrsum :
        |(f chain.length - f 0) - (g chain.length - g 0)| <
          (chain.length : ℝ) * eta := by
      let e : ℕ → ℝ := fun k ↦
        (f (k + 1) - f k) - (g (k + 1) - g k)
      have htel : ∑ k ∈ Finset.range chain.length, e k =
          (f chain.length - f 0) - (g chain.length - g 0) := by
        calc
          ∑ k ∈ Finset.range chain.length, e k =
              (∑ k ∈ Finset.range chain.length, (f (k + 1) - f k)) -
                ∑ k ∈ Finset.range chain.length, (g (k + 1) - g k) := by
            simp only [e, Finset.sum_sub_distrib]
          _ = _ := by rw [Finset.sum_range_sub, Finset.sum_range_sub]
      rw [← htel]
      calc
        |∑ k ∈ Finset.range chain.length, e k| ≤
            ∑ k ∈ Finset.range chain.length, |e k| :=
          Finset.abs_sum_le_sum_abs _ _
        _ < ∑ _k ∈ Finset.range chain.length, eta := by
          apply Finset.sum_lt_sum
          · intro k hk
            exact (hedge k (Finset.mem_range.mp hk)).le
          · refine ⟨0, Finset.mem_range.mpr chain.length_pos, ?_⟩
            exact hedge 0 chain.length_pos
        _ = (chain.length : ℝ) * eta := by simp
    have hf0 : f 0 = Axis.coord axis (mapTranslatedVertex phi a) := by
      simp [f, chain.point_zero]
    have hflast : f chain.length = Axis.coord axis (mapTranslatedVertex phi b) := by
      simp only [f, dif_pos (by omega : chain.length < chain.length + 1)]
      rw [show chain.point ⟨chain.length, by omega⟩ =
        chain.point (Fin.last chain.length) by congr]
      rw [chain.point_last]
    have hg0 : g 0 = Axis.coord axis (a : Tiling.Plane) := by
      simp [g, chain.point_zero]
    have hglast : g chain.length = Axis.coord axis (b : Tiling.Plane) := by
      simp only [g, dif_pos (by omega : chain.length < chain.length + 1)]
      rw [show chain.point ⟨chain.length, by omega⟩ =
        chain.point (Fin.last chain.length) by congr]
      rw [chain.point_last]
    rw [hf0, hflast, hg0, hglast] at herrsum
    have hsource : D / Real.sqrt 2 ≤
        |Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane))| := by
      simpa [D, dist_eq_norm, norm_sub_rev] using haxis
    have hlenEta : (chain.length : ℝ) * eta <
        (1 / Real.sqrt 2 - 1 / 2) * D := by
      have hlen := chain.length_le
      have hratio : (chain.length : ℝ) * eta ≤ (D / L + 1) * eta :=
        mul_le_mul_of_nonneg_right hlen heta.le
      have hfirst : D / L * eta <
          ((1 / Real.sqrt 2 - 1 / 2) / 2) * D := by
        have hDpos : 0 < D := lt_of_lt_of_le hM hMD
        have := mul_lt_mul_of_pos_right hetaL hDpos
        field_simp [ne_of_gt hL] at this ⊢
        nlinarith
      have hsecond : eta <
          ((1 / Real.sqrt 2 - 1 / 2) / 2) * D :=
        lt_of_lt_of_le hetaM (by
          have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
          have hs : Real.sqrt 2 < 2 := by
            nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
          have hc : 0 ≤ 1 / Real.sqrt 2 - 1 / 2 := by
            rw [sub_nonneg, one_div, one_div]
            exact (inv_le_inv₀ (by norm_num : (0 : ℝ) < 2) hsqrt).2 hs.le
          calc
            (1 / Real.sqrt 2 - 1 / 2) * M / 2 ≤
                (1 / Real.sqrt 2 - 1 / 2) * D / 2 := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hMD hc) (by norm_num)
            _ = ((1 / Real.sqrt 2 - 1 / 2) / 2) * D := by ring)
      nlinarith
    have himageCoord :
        |Axis.coord axis (mapTranslatedVertex phi b - mapTranslatedVertex phi a)| >
          D / 2 := by
      have habs := abs_sub_abs_le_abs_sub
        (Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)))
        (Axis.coord axis (mapTranslatedVertex phi b - mapTranslatedVertex phi a))
      rw [abs_sub_comm] at habs
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hrewrite :
          (Axis.coord axis (mapTranslatedVertex phi b) -
            Axis.coord axis (mapTranslatedVertex phi a)) =
          Axis.coord axis (mapTranslatedVertex phi b - mapTranslatedVertex phi a) := by
        cases axis <;> rfl
      have hrewriteSource :
          (Axis.coord axis (b : Tiling.Plane) - Axis.coord axis (a : Tiling.Plane)) =
          Axis.coord axis ((b : Tiling.Plane) - (a : Tiling.Plane)) := by
        cases axis <;> rfl
      rw [hrewrite, hrewriteSource] at herrsum
      have hcEq : 1 / Real.sqrt 2 -
          (1 / Real.sqrt 2 - 1 / 2) = (1 / 2 : ℝ) := by ring
      have hdecomp : D / Real.sqrt 2 -
          (1 / Real.sqrt 2 - 1 / 2) * D = D / 2 := by
        rw [div_eq_mul_inv, one_div]
        nlinarith
      nlinarith
    have hcoordNorm :
        |Axis.coord axis (mapTranslatedVertex phi b - mapTranslatedVertex phi a)| ≤
          ‖mapTranslatedVertex phi b - mapTranslatedVertex phi a‖ := by
      cases axis with
      | horizontal => exact Complex.abs_re_le_norm _
      | vertical => exact Complex.abs_im_le_norm _
    rw [← dist_eq_norm] at hcoordNorm
    have := dist_comm (mapTranslatedVertex phi a) (mapTranslatedVertex phi b)
    linarith

private theorem coarseControlParameters_exists
    (M rho : ℝ) (hM : 0 < M) (hrho : 0 < rho) :
    ∃ L R eta : ℝ, CoarseControlConditions M rho L R eta := by
  let L := M + 1
  let R := L + 2 * rho + 1
  let c := 1 / Real.sqrt 2 - 1 / 2
  have hL : 0 < L := by dsimp [L]; linarith
  have hR : M < R := by dsimp [R, L]; linarith
  have hLR : L + 2 * rho < R := by dsimp [R]; linarith
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtTwo : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hc : 0 < c := by
    dsimp [c]
    rw [sub_pos, one_div, one_div]
    exact (inv_lt_inv₀ (by norm_num : (0 : ℝ) < 2) hsqrt).2 hsqrtTwo
  let A := min M⁻¹ (M / 2) / Real.sqrt 2
  let B := c * L / 2
  let C0 := c * M / 2
  have hA : 0 < A := div_pos (lt_min (inv_pos.mpr hM) (half_pos hM)) hsqrt
  have hB : 0 < B := div_pos (mul_pos hc hL) (by norm_num)
  have hC : 0 < C0 := div_pos (mul_pos hc hM) (by norm_num)
  obtain ⟨eta, heta, hetaBound⟩ := exists_between (show (0 : ℝ) < min A (min B C0) by
    exact lt_min hA (lt_min hB hC))
  refine ⟨L, R, eta, hM, hrho, hL, hR, hLR, heta, ?_, ?_, ?_⟩
  · have hetaA : eta < A := lt_of_lt_of_le hetaBound (min_le_left _ _)
    dsimp [A] at hetaA
    simpa [mul_comm] using (lt_div_iff₀ hsqrt).mp hetaA
  · have hetaB : eta < B :=
      lt_of_lt_of_le hetaBound (le_trans (min_le_right _ _) (min_le_left _ _))
    dsimp [B] at hetaB
    rw [div_lt_iff₀ hL]
    dsimp [c] at hetaB ⊢
    nlinarith
  · have hetaC : eta < C0 :=
      lt_of_lt_of_le hetaBound (le_trans (min_le_right _ _) (min_le_right _ _))
    simpa [C0, c] using hetaC

theorem exists_flcControlPackage
    (C : ApproximationContext.{u}) (X : Set ℝ) (alpha M : ℝ)
    (hFLC : HasFLC C.centres) (hXne : X.Nonempty) (hXopen : IsOpen X)
    (halpha : 0 < alpha) (hperiod : alpha +ᵥ X = X)
    (htarget : C.target = {z : Tiling.Plane | z.re ∈ X})
    (hTile : TilesOn C.region C.centres C.target) (hM : 0 < M) :
    ∃ P : FLCControlPackage C,
      P.bandBase = X ∧ P.bandPeriod = alpha ∧ P.scale = M := by
  obtain ⟨rho, hrho, hdense, _hcentres⟩ :=
    translatedVertices_relativelyDense C X alpha hXne hXopen halpha
      hperiod htarget hTile
  obtain ⟨L, R, eta, hcond⟩ := coarseControlParameters_exists M rho hM hrho
  rcases hcond with
    ⟨_, _, hL, hMR, hLR, heta, herrSmall, hetaL, hetaM⟩
  obtain ⟨boundedDifferences, scalarAlphabet, edgeSumAlphabet,
      hbounded, hscalar, hedge⟩ :=
    finiteControlAlphabets_exists C M R hFLC (lt_trans hM hMR)
  let Z := scalarAlphabet ∪ edgeSumAlphabet
  obtain ⟨threshold, hthreshold, hcontrols⟩ :=
    finiteControls_commonThreshold C Z eta heta
  let P : FLCControlPackage C := {
    source_hasFLC := hFLC
    bandBase := X
    bandBase_nonempty := hXne
    bandBase_open := hXopen
    bandPeriod := alpha
    bandPeriod_pos := halpha
    bandBase_periodic := hperiod
    target_eq := htarget
    source_tilesOn := hTile
    scale := M
    scale_pos := hM
    controlRadius := R
    scale_lt_controlRadius := hMR
    localError := M⁻¹
    localError_pos := inv_pos.mpr hM
    localError_eq := rfl
    coordinateError := eta
    coordinateError_pos := heta
    coordinateError_small := lt_of_lt_of_le herrSmall (min_le_left _ _)
    boundedDifferences := boundedDifferences
    boundedDifferences_exact := hbounded
    scalarAlphabet := scalarAlphabet
    scalarAlphabet_exact := hscalar
    edgeSumAlphabet := edgeSumAlphabet
    edgeSumAlphabet_exact := hedge
    threshold := threshold
    threshold_pos := hthreshold
    forces_good := fun phi hphi ↦ (hcontrols phi hphi).1
    scalar_close := fun phi hphi ↦ (hcontrols phi hphi).2.1
    scalar_sign := fun phi hphi ↦ (hcontrols phi hphi).2.2.1
    scalar_zero_iff := fun phi hphi ↦ (hcontrols phi hphi).2.2.2.1
    scalar_injective := fun phi hphi ↦ (hcontrols phi hphi).2.2.2.2
    local_accuracy := by
      intro phi hphi a b hab
      apply lt_trans (scalarControl_localAccuracy R eta phi heta ?_ a b
        (lt_trans hab hMR))
        (lt_of_lt_of_le herrSmall (min_le_left _ _))
      intro z hz
      apply (hcontrols phi hphi).2.1 z
      rw [← hscalar] at hz
      exact Finset.mem_union_left _ hz
    coarse_inverse := by
      intro phi hphi a b hab
      apply scalarControl_coarseInverse M rho L R eta
        ⟨hM, hrho, hL, hMR, hLR, heta, herrSmall, hetaL, hetaM⟩ hdense phi ?_ a b hab
      intro z hz
      apply (hcontrols phi hphi).2.1 z
      rw [← hscalar] at hz
      exact Finset.mem_union_left _ hz
    mesh_after_map := exists_commonRationalMesh C X alpha hFLC hXne hXopen
      halpha hperiod htarget hTile }
  exact ⟨P, rfl, rfl, rfl⟩

/-- Local accuracy controls the diameter of the deformed region. -/
theorem deformedRegion_diam_le_add_localError
    {C : ApproximationContext} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (hD : Metric.diam C.region.support < P.scale) :
    Metric.diam D.deformedRegion.support ≤
      Metric.diam C.region.support + P.localError := by
  obtain ⟨p, hp, q, hq, _hmax, hdiam⟩ :=
    IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
  rw [hdiam]
  rw [D.vertices_image] at hp hq
  obtain ⟨v, hv, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  let a : ↥C.translatedVertices := ⟨v, v, hv, 0, C.zero_mem_centres, add_zero v⟩
  let b : ↥C.translatedVertices := ⟨w, w, hw, 0, C.zero_mem_centres, add_zero w⟩
  have hva : mapTranslatedVertex phi a = D.planarHomeomorph v := by
    rw [D.vertex_agreement v hv]
    rfl
  have hwb : mapTranslatedVertex phi b = D.planarHomeomorph w := by
    rw [D.vertex_agreement w hw]
    rfl
  have hvSupport : v ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hv)
  have hwSupport : w ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region hw)
  have hvw : dist (a : Tiling.Plane) b < P.scale := by
    change dist v w < P.scale
    exact lt_of_le_of_lt
      (Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hvSupport hwSupport) hD
  have hlocal := P.local_accuracy phi hphi a b hvw
  rw [hva, hwb] at hlocal
  change dist (D.planarHomeomorph v - D.planarHomeomorph w) (v - w) <
    P.localError at hlocal
  rw [dist_eq_norm]
  calc
    ‖D.planarHomeomorph v - D.planarHomeomorph w‖ =
        ‖(D.planarHomeomorph v - D.planarHomeomorph w) - (v - w) + (v - w)‖ := by
      congr 1
      abel
    _ ≤ ‖(D.planarHomeomorph v - D.planarHomeomorph w) - (v - w)‖ + ‖v - w‖ :=
      norm_add_le _ _
    _ ≤ P.localError + ‖v - w‖ := by
      simpa [dist_eq_norm] using add_le_add_right hlocal.le ‖v - w‖
    _ ≤ P.localError + Metric.diam C.region.support := by
      simpa [dist_eq_norm] using add_le_add_left
        (Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hvSupport hwSupport)
        P.localError
    _ = Metric.diam C.region.support + P.localError := add_comm _ _

end Tiling.AxisParallel.Approximation
