import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Topology.LocallyFellMatching
import Tiling.AxisParallel.Approximation.ControlledPeriodLifting
import Tiling.AxisParallel.Terminal.BoundaryReconstruction
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.NoProperVertexStabilizer
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.Geometry.PackingTopology
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.FLCMetricAndRelationRigidity
import Tiling.AxisParallel.Approximation.RectangularRegionImage
import Tiling.AxisParallel.Approximation.CoordinateExtension
import Tiling.AxisParallel.OneDimensional.PeriodicPointEnumeration
import Tiling.AxisParallel.Foundations.QuadrantGermGeometry
import Mathlib.Data.Int.LeastGreatest
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Terminal.RationalSliceCore
import Tiling.AxisParallel.Terminal.NoGapSliceGeometry

/-!
# T06 vertical packing lower adapters

This scratch candidate assembles the accepted lower geometry, synchronization,
and finite-scale declarations for the vertical packing owner.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Bornology Filter Function MeasureTheory Set Topology
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology

universe u

private structure AxisBoundaryCodeTransport
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) where
  properVertexEquiv :
    ↥(properVertices (regularSupport C.region (Subtype.val '' S))) ≃
      ↥(properVertices (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S)))
  source_provenance : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    ∃ (v : ↥C.region.vertices) (t : S), x.1 = v.1 + t.1.1
  target_formula : ∀ (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))))
      (v : ↥C.region.vertices) (t : S), x.1 = v.1 + t.1.1 →
    (properVertexEquiv x).1 = D.planarHomeomorph v.1 + Tphi t.1
  cone_preserved : ∀ x,
    localCone _ x.1 hSource x.2 =
      localCone _ (properVertexEquiv x).1 hTarget (properVertexEquiv x).2
  completeLineEquiv :
    ↥(completeBoundaryLines _ hSource) ≃
      ↥(completeBoundaryLines _ hTarget)
  completeLine_axis : ∀ L,
    (completeLineEquiv L).1.axis = L.1.axis
  completeLine_insideSide : ∀ L,
    (completeLineEquiv L).1.insideOnPositiveSide = L.1.insideOnPositiveSide
  completeLineLevelLift : ↥(completeBoundaryLines _ hSource) → C.coordinateSpace
  completeLineLevelLift_coe : ∀ L,
    (completeLineLevelLift L : ℝ) = L.1.level
  completeLineLevel_formula : ∀ L,
    (completeLineEquiv L).1.level = mapScalar phi (completeLineLevelLift L)

private structure ProperVertexTranslation
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (S₀ S₁ : Set ↥C.centres)
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
    (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
    (eta : Tiling.Plane) where
  beta : {z : Tiling.Plane //
    z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}
  map_beta : mapPoint phi beta = eta
  sourceEquiv : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))) ≃
    ↥(properVertices (regularSupport C.region (Subtype.val '' S₁)))
  source_formula : ∀ x, (sourceEquiv x).1 = beta.1 + x.1
  image_formula : ∀ x,
    (B₁.properVertexEquiv (sourceEquiv x)).1 =
      eta + B₀.properVertexEquiv x

private theorem connectedRationalPeriodLift :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → Linked G (Subtype.val '' S) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧ mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S := by
  intro C P phi hphi Tphi hTphi S G hSne hLinked hG hmargin imagePeriod hne hperiod
  rcases hLinked with ⟨hSnonempty, hconn⟩
  have hIndexed : IndexedShortEdgeConnected C G S := by
    intro x hx y hy
    exact hconn x hx y hy
  exact connectedIndexedPeriodLift P phi hphi Tphi hTphi S G hSne hIndexed hG hmargin
    imagePeriod hne hperiod

private theorem t06_connectedRationalPeriodLift_adapter
    (_hIndexed :
      ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
        (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C P.threshold phi →
      ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
        (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      ∀ (S : Set ↥C.centres) (G : ℝ),
        S.Nonempty → IndexedShortEdgeConnected C G S →
        G < P.scale → G + P.localError < P.scale / 2 →
      ∀ imagePeriod : Tiling.Plane,
        imagePeriod ≠ 0 →
        imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
          deformedCenterCarrierOn Tphi S →
        ∃ alpha : ControlledDisplacement C,
          alpha.1 ≠ 0 ∧ mapPoint phi alpha = imagePeriod ∧
          alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S)
    : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → Linked G (Subtype.val '' S) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧ mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S := by
  intro C P phi hphi Tphi hTphi S G hSne hLinked hG hmargin imagePeriod hne hperiod
  exact connectedRationalPeriodLift P phi hphi Tphi hTphi S G hSne hLinked hG hmargin
    imagePeriod hne hperiod

private theorem t06_connectedRationalPeriodLift
    (_hIndexed :
      ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
        (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C P.threshold phi →
      ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
        (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      ∀ (S : Set ↥C.centres) (G : ℝ),
        S.Nonempty → IndexedShortEdgeConnected C G S →
        G < P.scale → G + P.localError < P.scale / 2 →
      ∀ imagePeriod : Tiling.Plane,
        imagePeriod ≠ 0 →
        imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
          deformedCenterCarrierOn Tphi S →
        ∃ alpha : ControlledDisplacement C,
          alpha.1 ≠ 0 ∧ mapPoint phi alpha = imagePeriod ∧
          alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S)
    : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → Linked G (Subtype.val '' S) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧ mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S := by
  intro C P phi hphi Tphi hTphi S G hSne hLinked hG hmargin imagePeriod hne hperiod
  exact connectedRationalPeriodLift P phi hphi Tphi hTphi S G hSne hLinked hG hmargin
    imagePeriod hne hperiod

private theorem t06_periodLifts_synchronize_adapter
    (_hprov : ∀ (C : ApproximationContext.{0})
      (_hTiles : TilesOn C.region C.centres C.target)
      (S : Set ↥C.centres),
      properVertices (regularSupport C.region (Subtype.val '' S)) ⊆
        C.translatedVertices)
    (_hperiod : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C P.threshold phi →
      ∀ (S₀ S₁ : Set ↥C.centres)
        (alpha₀ alpha₁ beta : ControlledDisplacement C)
        (imagePeriod : Tiling.Plane),
        mapPoint phi alpha₀ = imagePeriod →
        mapPoint phi alpha₁ = imagePeriod →
        alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
        alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
        properVertices (regularSupport C.region (Subtype.val '' S₀)) ⊆
          C.translatedVertices →
        properVertices (regularSupport C.region (Subtype.val '' S₁)) ⊆
          C.translatedVertices →
        (∀ w, w ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₀)) →
          beta.1 + w ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₁))) →
        (properVertices
          (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
        alpha₀ = alpha₁)
    : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (S₀ S₁ : Set ↥C.centres)
      (alpha₀ alpha₁ beta : ControlledDisplacement C)
      (imagePeriod : Tiling.Plane)
      (sourceEquiv :
        ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))) ≃
          ↥(properVertices (regularSupport C.region (Subtype.val '' S₁)))),
      (∀ x, (sourceEquiv x).1 = beta.1 + x.1) →
      mapPoint phi alpha₀ = imagePeriod →
      mapPoint phi alpha₁ = imagePeriod →
      alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
      alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
      (properVertices
        (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
      alpha₀ = alpha₁ := by
  intro C P phi hphi S₀ S₁ alpha₀ alpha₁ beta imagePeriod sourceEquiv hsource
    hmap₀ hmap₁ hper₀ hper₁ hne
  refine periodLifts_eq_of_properVertexShift P phi hphi S₀ S₁ alpha₀ alpha₁ beta
    imagePeriod hmap₀ hmap₁ hper₀ hper₁
    (_hprov C P.source_tilesOn S₀) (_hprov C P.source_tilesOn S₁) ?_ hne
  intro w hw
  rw [← hsource ⟨w, hw⟩]
  exact (sourceEquiv ⟨w, hw⟩).property

private theorem boundaryCodeComponents_reconstructTranslation :
    ∀ {F₀ F₁ : Set Tiling.Plane}
      (hF₀ : IsLocallyAxisParallelPolygonal F₀)
      (hF₁ : IsLocallyAxisParallelPolygonal F₁) (beta : Tiling.Plane),
    F₀.Nonempty → F₁.Nonempty → F₀ ≠ univ → F₁ ≠ univ →
    (boundaryCode F₁ hF₁).properVertexSet =
      ((boundaryCode F₀ hF₀).vadd beta).properVertexSet →
    (boundaryCode F₁ hF₁).coneGraph =
      ((boundaryCode F₀ hF₀).vadd beta).coneGraph →
    (boundaryCode F₁ hF₁).completeLines =
      ((boundaryCode F₀ hF₀).vadd beta).completeLines →
    F₁ = beta +ᵥ F₀ := by
  intro F₀ F₁ hF₀ hF₁ beta hne₀ hne₁ hproper₀ hproper₁ hv hc hl
  apply eq_vadd_of_boundaryCode hF₀.1 hF₁.1 hF₀.2.1 hF₁.2.1
    hne₀ hne₁ hproper₀ hproper₁ hF₀ hF₁
  exact (boundaryCode_eq_vadd_iff hF₀ hF₁ beta).2 ⟨hv, hc, hl⟩

private theorem connectedPeriodLifts_synchronize :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S₀ S₁ : Set ↥C.centres)
      (hSource₀ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₀)))
      (hSource₁ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₁)))
      (hTarget₀ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
      (hTarget₁ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
      (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
      (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
      (eta : Tiling.Plane)
      (_V : ProperVertexTranslation C phi D Tphi S₀ S₁
        hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta)
      (alpha₀ alpha₁ : ControlledDisplacement C)
      (imagePeriod : Tiling.Plane),
      mapPoint phi alpha₀ = imagePeriod →
      mapPoint phi alpha₁ = imagePeriod →
      alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
      alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
      (properVertices (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
      alpha₀ = alpha₁ := by
  intro C P phi hphi D Tphi hTphi S₀ S₁ hSource₀ hSource₁ hTarget₀ hTarget₁
    B₀ B₁ eta V alpha₀ alpha₁ imagePeriod hmap₀ hmap₁ hper₀ hper₁ hne
  refine periodLifts_eq_of_properVertexShift P phi hphi S₀ S₁ alpha₀ alpha₁
    V.beta imagePeriod hmap₀ hmap₁ hper₀ hper₁
    (properVertices_regularSupport_image_subset_translatedVertices C
      P.source_tilesOn S₀)
    (properVertices_regularSupport_image_subset_translatedVertices C
      P.source_tilesOn S₁) ?_ hne
  intro w hw
  have hs := V.source_formula ⟨w, hw⟩
  rw [← hs]
  exact (V.sourceEquiv ⟨w, hw⟩).property

private theorem t06_connectedPeriodLifts_synchronize
    (_hprov : ∀ (C : ApproximationContext.{0})
      (_hTiles : TilesOn C.region C.centres C.target)
      (S : Set ↥C.centres),
      properVertices (regularSupport C.region (Subtype.val '' S)) ⊆
        C.translatedVertices)
    (_hperiod : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C P.threshold phi →
      ∀ (S₀ S₁ : Set ↥C.centres)
        (alpha₀ alpha₁ beta : ControlledDisplacement C)
        (imagePeriod : Tiling.Plane),
        mapPoint phi alpha₀ = imagePeriod →
        mapPoint phi alpha₁ = imagePeriod →
        alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
        alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
        properVertices (regularSupport C.region (Subtype.val '' S₀)) ⊆
          C.translatedVertices →
        properVertices (regularSupport C.region (Subtype.val '' S₁)) ⊆
          C.translatedVertices →
        (∀ w, w ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₀)) →
          beta.1 + w ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₁))) →
        (properVertices
          (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
        alpha₀ = alpha₁)
    : ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S₀ S₁ : Set ↥C.centres)
      (hSource₀ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₀)))
      (hSource₁ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₁)))
      (hTarget₀ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
      (hTarget₁ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
      (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
      (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
      (eta : Tiling.Plane)
      (_V : ProperVertexTranslation C phi D Tphi S₀ S₁
        hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta)
      (alpha₀ alpha₁ : ControlledDisplacement C)
      (imagePeriod : Tiling.Plane),
      mapPoint phi alpha₀ = imagePeriod →
      mapPoint phi alpha₁ = imagePeriod →
      alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀ →
      alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁ →
      (properVertices (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
      alpha₀ = alpha₁ := by
  intro C P phi hphi D Tphi hTphi S₀ S₁ hSource₀ hSource₁ hTarget₀ hTarget₁
    B₀ B₁ eta V alpha₀ alpha₁ imagePeriod hmap₀ hmap₁ hper₀ hper₁ hne
  exact connectedPeriodLifts_synchronize P phi hphi D Tphi hTphi S₀ S₁
    hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta V alpha₀ alpha₁ imagePeriod
    hmap₀ hmap₁ hper₀ hper₁ hne

private theorem packingUniformSeparation (K : Region) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (S : Set Tiling.Plane),
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements S) →
        ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist s t := by
  exact Tiling.AxisParallel.exists_packingSeparation K

private def transverseVertexDifferenceScalar
    (C : ApproximationContext) (axis : Axis)
    (v w : ↥C.region.vertices) : C.coordinateSpace := by
  cases axis with
  | horizontal =>
      exact ⟨v.1.im - w.1.im, C.coordinateSpace.sub_mem
        (C.vertex_im_mem v.1 v.2) (C.vertex_im_mem w.1 w.2)⟩
  | vertical =>
      exact ⟨v.1.re - w.1.re, C.coordinateSpace.sub_mem
        (C.vertex_re_mem v.1 v.2) (C.vertex_re_mem w.1 w.2)⟩

private theorem transverseVertexDifference_mem_scalarAlphabet
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hdiam : Metric.diam C.region.support < P.controlRadius) :
    ∀ (axis : Axis) (v w : ↥C.region.vertices),
      transverseVertexDifferenceScalar C axis v w ∈ P.scalarAlphabet := by
  intro axis v w
  let a : ↥C.translatedVertices :=
    ⟨(v : Tiling.Plane), (v : Tiling.Plane), v.2, 0, C.zero_mem_centres,
      add_zero (v : Tiling.Plane)⟩
  let b : ↥C.translatedVertices :=
    ⟨(w : Tiling.Plane), (w : Tiling.Plane), w.2, 0, C.zero_mem_centres,
      add_zero (w : Tiling.Plane)⟩
  have hv : (v : Tiling.Plane) ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
  have hw : (w : Tiling.Plane) ∈ C.region.support := by
    rw [← C.region.isPolygonal.closure_interior]
    exact frontier_subset_closure
      (IntrinsicVertices.region_vertices_subset_frontier C.region w.2)
  have hd : dist (a : Tiling.Plane) b < P.controlRadius := by
    change dist (v : Tiling.Plane) w < P.controlRadius
    exact lt_of_le_of_lt
      (Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hv hw) hdiam
  have hz : transverseVertexDifferenceScalar C axis v w ∈
      boundedScalarDifferences C P.controlRadius := by
    refine ⟨axis.swap, a, b, hd, ?_⟩
    cases axis <;> rfl
  rw [← P.scalarAlphabet_exact] at hz
  exact hz

private theorem finiteFootprintDifference_reflected
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi) :
    ∀ (axis : Axis) (w w' v₀ v₁ : ↥C.region.vertices),
      transverseVertexDifferenceScalar C axis w w' ∈ P.scalarAlphabet →
      transverseVertexDifferenceScalar C axis v₀ v₁ ∈ P.scalarAlphabet →
      mapScalar phi (transverseVertexDifferenceScalar C axis w w') =
        mapScalar phi (transverseVertexDifferenceScalar C axis v₀ v₁) →
      axis.transverseCoord w.1 - axis.transverseCoord w'.1 =
        axis.transverseCoord v₀.1 - axis.transverseCoord v₁.1 := by
  intro axis w w' v₀ v₁ hw hv hmap
  have hmem := (P.scalar_injective phi hphi
    (transverseVertexDifferenceScalar C axis w w')
    (Finset.mem_union_left _ hw)
    (transverseVertexDifferenceScalar C axis v₀ v₁)
    (Finset.mem_union_left _ hv)).mp hmap
  have hval := congrArg Subtype.val hmem
  cases axis <;> exact hval

private theorem region_support_diam_pos (K : Region) :
    0 < Metric.diam K.support := by
  have hopen : 0 < Metric.diam K.openCarrier :=
    region_openCarrier_diam_pos K
  have heq : Metric.diam K.support = Metric.diam K.openCarrier := by
    change Metric.diam K.support = Metric.diam (interior K.support)
    nth_rewrite 1 [← K.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  rw [heq]
  exact hopen

private theorem localError_lt_diam_of_two_div_lt_scale
    {C : ApproximationContext.{u}} (P : FLCControlPackage C)
    (sourceDiameter : ℝ) (hpos : 0 < sourceDiameter)
    (hscale : 2 / sourceDiameter < P.scale) :
    P.localError < sourceDiameter := by
  have htwo : 0 < 2 / sourceDiameter := div_pos (by norm_num) hpos
  have hinv : P.scale⁻¹ < (2 / sourceDiameter)⁻¹ :=
    (inv_lt_inv₀ P.scale_pos htwo).2 hscale
  calc
    P.localError = P.scale⁻¹ := P.localError_eq
    _ < (2 / sourceDiameter)⁻¹ := hinv
    _ = sourceDiameter / 2 := by field_simp
    _ < sourceDiameter := by linarith

private noncomputable def t06RecoveryScale
    (K : Region) (ell delta G : ℝ) (N : ℕ) : ℝ :=
  max
    (max 3 (max (2 / delta) (max (2 * ell + 2) (max (2 * G + 2)
      (max ((N : ℝ) * G + 2 * Metric.diam K.support)
        (Metric.diam K.support))))))
    (2 / Metric.diam K.support)

private theorem t06RecoveryScale_bounds
    (K : Region) (ell delta G : ℝ) (N : ℕ)
    (hdelta : 0 < delta) :
    0 < t06RecoveryScale K ell delta G N ∧
    ∀ {C : ApproximationContext.{u}}, C.region = K →
    ∀ (P : FLCControlPackage C),
      t06RecoveryScale K ell delta G N < P.scale →
      P.localError < delta / 2 ∧
      ell + 2 * P.localError < P.scale / 2 ∧
      G + P.localError < P.scale / 2 ∧
      (N : ℝ) * G + 2 * Metric.diam K.support < P.scale ∧
      Metric.diam K.support < P.controlRadius ∧
      Metric.diam K.support < P.scale ∧
      P.localError ≤ Metric.diam K.support := by
  constructor
  · unfold t06RecoveryScale
    positivity
  · intro C hCK P hscale
    have hD : 0 < Metric.diam K.support := region_support_diam_pos K
    let d₁ : ℝ := max ((N : ℝ) * G + 2 * Metric.diam K.support)
      (Metric.diam K.support)
    let d₂ : ℝ := max (2 * G + 2) d₁
    let d₃ : ℝ := max (2 * ell + 2) d₂
    let d₄ : ℝ := max (2 / delta) d₃
    let m : ℝ := max 3 d₄
    have hscale' : max m (2 / Metric.diam K.support) < P.scale := by
      simpa [t06RecoveryScale, m, d₄, d₃, d₂, d₁] using hscale
    have hm : m < P.scale := lt_of_le_of_lt (le_max_left _ _) hscale'
    have hrecip : 2 / Metric.diam K.support < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hscale'
    have hthree : 3 < P.scale :=
      lt_of_le_of_lt (le_max_left _ _) hm
    have hd₄ : d₄ < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hm
    have hdeltaScale : 2 / delta < P.scale :=
      lt_of_le_of_lt (le_max_left _ _) hd₄
    have hd₃ : d₃ < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hd₄
    have hEllScale : 2 * ell + 2 < P.scale :=
      lt_of_le_of_lt (le_max_left _ _) hd₃
    have hd₂ : d₂ < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hd₃
    have hGScale : 2 * G + 2 < P.scale :=
      lt_of_le_of_lt (le_max_left _ _) hd₂
    have hd₁ : d₁ < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hd₂
    have hNScale : (N : ℝ) * G + 2 * Metric.diam K.support < P.scale :=
      lt_of_le_of_lt (le_max_left _ _) hd₁
    have hDScale : Metric.diam K.support < P.scale :=
      lt_of_le_of_lt (le_max_right _ _) hd₁
    have hlocal_delta : P.localError < delta / 2 := by
      have htwo : 0 < 2 / delta := div_pos (by norm_num) hdelta
      have hi : P.scale⁻¹ < (2 / delta)⁻¹ :=
        (inv_lt_inv₀ P.scale_pos htwo).2 hdeltaScale
      calc
        P.localError = P.scale⁻¹ := P.localError_eq
        _ < (2 / delta)⁻¹ := hi
        _ = delta / 2 := by field_simp
    have hlocal_one : P.localError < 1 := by
      rw [P.localError_eq]
      exact (inv_lt_one₀ P.scale_pos).2 (by linarith [hthree])
    have hEll : ell + 2 * P.localError < P.scale / 2 := by
      have hthird : P.localError < (1 : ℝ) / 3 := by
        rw [P.localError_eq]
        have hi : P.scale⁻¹ < (3 : ℝ)⁻¹ :=
          (inv_lt_inv₀ P.scale_pos (by norm_num)).2 hthree
        simpa using hi
      have hfourLocal : 4 * P.localError < 2 := by linarith
      nlinarith [hEllScale, hfourLocal]
    have hG : G + P.localError < P.scale / 2 := by
      linarith [hlocal_one, hGScale]
    have hcontrol : Metric.diam K.support < P.controlRadius :=
      lt_trans hDScale P.scale_lt_controlRadius
    have hlocal_D : P.localError ≤ Metric.diam K.support := by
      have hi : P.scale⁻¹ < (2 / Metric.diam K.support)⁻¹ :=
        (inv_lt_inv₀ P.scale_pos (div_pos (by norm_num) hD)).2 hrecip
      rw [P.localError_eq]
      exact (calc
        P.scale⁻¹ < (2 / Metric.diam K.support)⁻¹ := hi
        _ = Metric.diam K.support / 2 := by field_simp
        _ ≤ Metric.diam K.support := by linarith).le
    subst hCK
    exact ⟨hlocal_delta, hEll, hG, hNScale, hcontrol, hDScale, hlocal_D⟩


private theorem noProperVertices_isCenterColumn :
    ∀ (axis : Axis) {K : Region} {S : Set Tiling.Plane},
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      S.Nonempty →
      (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
      properVertices (regularSupport K S) = ∅ →
      IsCenterColumn axis K S := by
  intro axis K S hpacking hSne halign hvertices
  have hbounded := Tiling.AxisParallel.regularSupportTransverseProjection_bounded
    (K := K) (S := S) axis halign
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : ℝ)
  have hSneSupport : (regularSupport K S).Nonempty := by
    obtain ⟨s, hs⟩ := hSne
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    change x ∈ K.openCarrier at hx
    have hopen : IsOpen (openUnion K S) := by
      rw [openUnion]
      exact isOpen_iUnion fun s ↦
        (Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
    refine ⟨s + x, ?_⟩
    change s + x ∈ interior (closure (openUnion K S))
    apply (hopen.subset_interior_closure : openUnion K S ⊆ _)
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using hx
  obtain ⟨x, hx⟩ := hSneSupport
  obtain ⟨v, hv, hstab⟩ :=
    Tiling.AxisParallel.exists_stabilizerDirection_of_noProperVertices
      (regularSupport_isRegularOpen K S).1
      (regularSupport_isRegularOpen K S).2 hvertices
  cases axis with
  | horizontal =>
      have hzero : v.im = 0 := by
        by_contra hvim
        let r : ℝ := (R + |x.im| + 1) / v.im
        have hr : r * v.im = R + |x.im| + 1 := by
          dsimp [r]
          field_simp
        have hpoint' : r • v +ᵥ x ∈ r • v +ᵥ regularSupport K S := by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [vadd_eq_add] using hx
        have hpoint : r • v + x ∈ regularSupport K S := by
          have heq := AddAction.mem_stabilizer_iff.mp (hstab r)
          have hpoint'' := heq ▸ hpoint'
          simpa only [vadd_eq_add] using hpoint''
        have himage : (r • v + x).im ∈ Metric.closedBall (0 : ℝ) R :=
          hR ⟨r • v + x, hpoint, rfl⟩
        have himage' : |(r • v + x).im| ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using himage
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at himage'
        rw [hr] at himage'
        have hinside : R < R + |x.im| + 1 + x.im := by
          linarith [neg_abs_le x.im]
        exact (not_lt_of_ge himage') (hinside.trans_le (le_abs_self _))
      have hvre : v.re ≠ 0 := by
        intro hvre
        apply hv
        apply Complex.ext <;> simp [hzero, hvre]
      have hhorizontal : ∀ a : ℝ, (a : ℂ) +ᵥ regularSupport K S =
          regularSupport K S := by
        intro a
        rw [show (a : ℂ) = (a / v.re) • v by
          apply Complex.ext
          · simp [hzero, hvre]
          · simp [hzero]]
        exact AddAction.mem_stabilizer_iff.mp (hstab (a / v.re))
      exact ⟨hpacking, hSne, halign, hhorizontal⟩
  | vertical =>
      have hzero : v.re = 0 := by
        by_contra hvre
        let r : ℝ := (R + |x.re| + 1) / v.re
        have hr : r * v.re = R + |x.re| + 1 := by
          dsimp [r]
          field_simp
        have hpoint' : r • v +ᵥ x ∈ r • v +ᵥ regularSupport K S := by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [vadd_eq_add] using hx
        have hpoint : r • v + x ∈ regularSupport K S := by
          have heq := AddAction.mem_stabilizer_iff.mp (hstab r)
          have hpoint'' := heq ▸ hpoint'
          simpa only [vadd_eq_add] using hpoint''
        have himage : (r • v + x).re ∈ Metric.closedBall (0 : ℝ) R :=
          hR ⟨r • v + x, hpoint, rfl⟩
        have himage' : |(r • v + x).re| ≤ R := by
          simpa [Metric.mem_closedBall, dist_zero_right] using himage
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at himage'
        rw [hr] at himage'
        have hinside : R < R + |x.re| + 1 + x.re := by
          linarith [neg_abs_le x.re]
        exact (not_lt_of_ge himage') (hinside.trans_le (le_abs_self _))
      have hvim : v.im ≠ 0 := by
        intro hvim
        apply hv
        apply Complex.ext <;> simp [hzero, hvim]
      have hvertical : ∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ regularSupport K S =
          regularSupport K S := by
        intro a
        rw [show (a : ℂ) * Complex.I = (a / v.im) • v by
          apply Complex.ext
          · simp [hzero]
          · simp [hzero, hvim]]
        exact AddAction.mem_stabilizer_iff.mp (hstab (a / v.im))
      exact ⟨hpacking, hSne, halign, hvertical⟩


private def PointedFellConverges (Y : ℕ → Set ℝ) (Z : Set ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x ∈ Set.Icc (-R) R,
      |Metric.infDist x (Y n) - Metric.infDist x Z| < ε

private def imaginaryEmbedding (y : ℝ) : Tiling.Plane :=
  (y : ℂ) * Complex.I

private theorem imaginaryEmbedding_isometry :
    Isometry imaginaryEmbedding := by
  intro x y
  rw [edist_dist, edist_dist]
  rw [dist_eq_norm, dist_eq_norm]
  congr 1
  simp [imaginaryEmbedding, Complex.norm_def, Complex.normSq_apply]
  simpa [pow_two] using (Real.sqrt_sq_eq_abs (x - y))

private theorem imaginaryEmbedding_image_infDist (x : ℝ) (S : Set ℝ) :
    Metric.infDist (imaginaryEmbedding x) (imaginaryEmbedding '' S) =
      Metric.infDist x S :=
  Metric.infDist_image imaginaryEmbedding_isometry

private theorem image_uniformlySeparated
    {δ : ℝ} (_hδ : 0 < δ) {S : Set ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    IsUniformlySeparated δ (imaginaryEmbedding '' S) := by
  intro x hx y hy hxy
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have hxy' : x' ≠ y' := by
    intro h
    subst y'
    exact hxy rfl
  simpa [imaginaryEmbedding_isometry.dist_eq] using hS x' hx' y' hy' hxy'

private theorem image_closed_of_separated
    {δ : ℝ} (hδ : 0 < δ) {S : Set ℝ}
    (hS : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    IsClosed (imaginaryEmbedding '' S) := by
  apply Metric.isClosed_of_pairwise_le_dist hδ
  exact image_uniformlySeparated hδ hS

private theorem locallyFell_eventually_exists_mem_ball
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : LocallyFellConverges A L) {x : Tiling.Plane} (hx : x ∈ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∃ y ∈ A n, dist y x < ε := by
  rcases hconv with ⟨hA, hL, hconv⟩
  let U : Set (OnePoint Tiling.Plane) :=
    (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Metric.ball x ε
  have hUopen : IsOpen U := OnePoint.isOpen_image_coe.mpr Metric.isOpen_ball
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | ((Q : Set (OnePoint Tiling.Plane)) ∩ U).Nonempty}
  have hVopen : IsOpen V :=
    TopologicalSpace.NonemptyCompacts.isOpen_inter_nonempty_of_isOpen hUopen
  have hlimit : fellCompactification L hL ∈ V := by
    refine ⟨(x : OnePoint Tiling.Plane), ?_, ⟨x, ?_, rfl⟩⟩
    · simp [Tiling.Topology.fellCompactification, hx]
    · exact Metric.mem_ball_self hε
  filter_upwards [hconv (hVopen.mem_nhds hlimit)] with n hn
  rcases hn with ⟨w, hwQ, hwU⟩
  rcases hwU with ⟨y, hy, rfl⟩
  refine ⟨y, ?_, Metric.mem_ball.mp hy⟩
  simpa [Tiling.Topology.fellCompactification] using hwQ

private theorem isPacking_of_locallyFellConverges
    {K : Region} {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hA : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (A n)))
    (hconv : LocallyFellConverges A L) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements L) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  intro s hsL t htL hst
  change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
  rw [Set.disjoint_left]
  intro x hxs hxt
  let U : Set Tiling.Plane := {c | x - c ∈ K.openCarrier}
  have hUopen : IsOpen U :=
    K.openCarrier_regularOpen.1.preimage (continuous_const.sub continuous_id)
  have hsU : s ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxs
    simp only [vadd_eq_add] at hxs
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxs
  have htU : t ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt
    simp only [vadd_eq_add] at hxt
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxt
  obtain ⟨rs, hrs, hrsU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
  obtain ⟨rt, hrt, hrtU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds htU)
  let epsilon := min rs (min rt (dist s t / 3))
  have hdist : 0 < dist s t := dist_pos.mpr hst
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hrs (lt_min hrt (by positivity))
  have heps_rs : epsilon ≤ rs := min_le_left _ _
  have heps_rt : epsilon ≤ rt := (min_le_right _ _).trans (min_le_left _ _)
  have heps_dist : epsilon ≤ dist s t / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  rcases hconv with ⟨hAclosed, hLclosed, hconv⟩
  have hsEventually :=
    locallyFell_eventually_exists_mem_ball ⟨hAclosed, hLclosed, hconv⟩ hsL hepsilon
  have htEventually :=
    locallyFell_eventually_exists_mem_ball ⟨hAclosed, hLclosed, hconv⟩ htL hepsilon
  obtain ⟨n, ⟨s', hs'A, hs'dist⟩, ⟨t', ht'A, ht'dist⟩⟩ :=
    (hsEventually.and htEventually).exists
  have hs'U : s' ∈ U := hrsU (by
    rw [Metric.mem_ball]
    exact hs'dist.trans_le heps_rs)
  have ht'U : t' ∈ U := hrtU (by
    rw [Metric.mem_ball]
    exact ht'dist.trans_le heps_rt)
  have hs't' : s' ≠ t' := by
    intro heq
    subst t'
    have htriangle : dist s t ≤ dist s s' + dist s' t := dist_triangle _ _ _
    rw [dist_comm s s'] at htriangle
    have hsBound : dist s' s < dist s t / 3 := hs'dist.trans_le heps_dist
    have htBound : dist s' t < dist s t / 3 := ht'dist.trans_le heps_dist
    linarith
  have hdisjoint :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K (A n)).mp
      (hA n) hs'A ht'A hs't'
  apply Set.disjoint_left.mp hdisjoint
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using hs'U
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using ht'U

private theorem imaginaryEmbedding_image_univ :
    imaginaryEmbedding '' (Set.univ : Set ℝ) = {z : Tiling.Plane | z.re = 0} := by
  ext z
  constructor
  · rintro ⟨y, -, rfl⟩
    simp [imaginaryEmbedding]
  · intro hz
    refine ⟨z.im, Set.mem_univ _, ?_⟩
    apply Complex.ext
    · simpa [imaginaryEmbedding] using hz.symm
    · simp [imaginaryEmbedding]

private theorem locallyFell_limit_on_imaginaryAxis
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hA : ∀ n, A n ⊆ imaginaryEmbedding '' (Set.univ : Set ℝ))
    (hconv : LocallyFellConverges A L) :
    L ⊆ imaginaryEmbedding '' (Set.univ : Set ℝ) := by
  rcases hconv with ⟨hAclosed, hLclosed, hconv⟩
  let axis : Set Tiling.Plane := imaginaryEmbedding '' (Set.univ : Set ℝ)
  have haxisClosed : IsClosed axis := by
    dsimp [axis]
    rw [imaginaryEmbedding_image_univ]
    exact isClosed_eq Complex.continuous_re continuous_const
  let axisInf : Set (OnePoint Tiling.Plane) :=
    (fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' axis ∪
      {OnePoint.infty}
  have haxisInfClosed : IsClosed axisInf := by
    rw [← isOpen_compl_iff]
    have hopen : IsOpen (axisᶜ) := haxisClosed.isOpen_compl
    have himageOpen : IsOpen
        ((fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' axisᶜ) :=
      OnePoint.isOpen_image_coe.mpr hopen
    have hcomp : axisInfᶜ =
        (fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' axisᶜ := by
      ext z
      refine OnePoint.rec ?_ (fun z ↦ ?_) z
      · simp [axisInf]
      · simp [axisInf]
    rw [hcomp]
    exact himageOpen
  let V : Set (TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane)) :=
    {Q | (Q : Set (OnePoint Tiling.Plane)) ⊆ axisInf}
  have hVclosed : IsClosed V :=
    TopologicalSpace.NonemptyCompacts.isClosed_subsets_of_isClosed haxisInfClosed
  have hmem : ∀ n,
      fellCompactification (A n) (hAclosed n) ∈ V := by
    intro n
    change (fellCompactification (A n) (hAclosed n) :
      Set (OnePoint Tiling.Plane)) ⊆ axisInf
    intro z hz
    change z ∈ ((fun w : Tiling.Plane ↦ (w : OnePoint Tiling.Plane)) '' A n ∪
      {OnePoint.infty}) at hz
    rcases hz with ⟨w, hw, rfl⟩ | rfl
    · exact Set.mem_union_left _ ⟨w, hA n (by simpa using hw), rfl⟩
    · exact Set.mem_union_right _ (Set.mem_singleton _)
  have hlimV : fellCompactification L hLclosed ∈ V :=
    hVclosed.mem_of_tendsto hconv (Filter.Eventually.of_forall hmem)
  intro x hx
  have hxK : (x : OnePoint Tiling.Plane) ∈
      (fellCompactification L hLclosed : Set (OnePoint Tiling.Plane)) := by
    simp [Tiling.Topology.fellCompactification, hx]
  have hxaxis : (x : OnePoint Tiling.Plane) ∈
      (fun z : Tiling.Plane ↦ (z : OnePoint Tiling.Plane)) '' axis := by
    have hxlim : (x : OnePoint Tiling.Plane) ∈ axisInf := hlimV hxK
    rcases hxlim with hlim | hlim
    · exact hlim
    · exact False.elim (OnePoint.coe_ne_infty x (Set.mem_singleton_iff.mp hlim))
  obtain ⟨y, hy, hxy⟩ := hxaxis
  have hyx : y = x := OnePoint.coe_injective hxy
  rw [← hyx]
  simpa [axis] using hy

private theorem locallyFell_infDist_uniform
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane} {δ : ℝ}
    (hδ : 0 < δ) (hAclosed : ∀ n, IsClosed (A n)) (hLclosed : IsClosed L)
    (hsepA : ∀ n, IsUniformlySeparated δ (A n))
    (hsepL : IsUniformlySeparated δ L)
    (h0A : ∀ n, 0 ∈ A n) (h0L : 0 ∈ L)
    (hconv : LocallyFellConverges A L) :
    ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ n, N ≤ n → ∀ x ∈ Metric.closedBall 0 R,
        |Metric.infDist x (A n) - Metric.infDist x L| < ε := by
  intro R hR ε hε
  let η : ℝ := min (ε / 3) (δ / 6)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by linarith) (by linarith)
  have hηε : η < ε / 2 := by
    have : η ≤ ε / 3 := min_le_left _ _
    linarith
  have hηδ : η < δ / 3 := by
    have : η ≤ δ / 6 := min_le_right _ _
    linarith
  let B : ℝ := 2 * R + ε + 1
  let C : Set Tiling.Plane := Metric.closedBall 0 B
  have hB : 0 < B := by
    dsimp [B]
    linarith
  have hC : IsCompact C := isCompact_closedBall 0 B
  have hmatching :=
    (Tiling.AxisParallel.Topology.locallyFell_matchingPoints
      hδ hAclosed hLclosed hsepA hsepL).mp hconv
  have hevent := hmatching C hC η hη hηδ
  rw [eventually_atTop] at hevent
  obtain ⟨N, hN⟩ := hevent
  refine ⟨N, fun n hn x hx ↦ ?_⟩
  have hmatch := hN n hn
  have hxR : dist 0 x ≤ R := by
    simpa [C] using Metric.mem_closedBall.mp hx
  have hA0 : (A n).Nonempty := ⟨0, h0A n⟩
  have hL0 : L.Nonempty := ⟨0, h0L⟩
  let dA := Metric.infDist x (A n)
  let dL := Metric.infDist x L
  have hdA : dA ≤ R := by
    dsimp [dA]
    exact (Metric.infDist_le_dist_of_mem (h0A n)).trans (by simpa [dist_comm] using hxR)
  have hdL : dL ≤ R := by
    dsimp [dL]
    exact (Metric.infDist_le_dist_of_mem h0L).trans (by simpa [dist_comm] using hxR)
  have hupper : dA < dL + 2 * η := by
    obtain ⟨y, hyL, hxy⟩ :=
      (Metric.infDist_lt_iff hL0).mp (show dL < dL + η by linarith)
    have hyC : y ∈ C := by
      apply Metric.mem_closedBall.mpr
      have h0x : dist 0 x ≤ R := hxR
      have hxy' : dist x y < dL + η := hxy
      have hdL' : dL ≤ R := hdL
      dsimp [C, B]
      have := dist_triangle 0 x y
      rw [dist_comm x y] at hxy'
      have hthis : dist y 0 ≤ dist 0 x + dist x y := by
        simpa [dist_comm] using this
      linarith
    obtain ⟨y', hy', _⟩ := hmatch.1 y ⟨hyL, hyC⟩
    have hy'A := hy'.1
    have hyy' := hy'.2
    have hdist : dist x y' ≤ dist x y + dist y y' := dist_triangle _ _ _
    have hdA_y' : dA ≤ dist x y' := Metric.infDist_le_dist_of_mem hy'A
    dsimp [dA, dL]
    linarith [hdA_y']
  have hlower : dL < dA + 2 * η := by
    obtain ⟨y, hyA, hxy⟩ :=
      (Metric.infDist_lt_iff hA0).mp (show dA < dA + η by linarith)
    have hyC : y ∈ C := by
      apply Metric.mem_closedBall.mpr
      have h0x : dist 0 x ≤ R := hxR
      have hxy' : dist x y < dA + η := hxy
      have hdA' : dA ≤ R := hdA
      dsimp [C, B]
      have := dist_triangle 0 x y
      rw [dist_comm x y] at hxy'
      have hthis : dist y 0 ≤ dist 0 x + dist x y := by
        simpa [dist_comm] using this
      linarith
    obtain ⟨y', hy', _⟩ := hmatch.2 y ⟨hyA, hyC⟩
    have hy'L := hy'.1
    have hyy' := hy'.2
    have hdist : dist x y' ≤ dist x y + dist y y' := dist_triangle _ _ _
    have hdL_y' : dL ≤ dist x y' := Metric.infDist_le_dist_of_mem hy'L
    have hyy : dist y y' < η := by simpa [dist_comm] using hyy'
    dsimp [dA, dL]
    linarith [hdL_y', hyy]
  dsimp [dA, dL] at hupper hlower ⊢
  rw [abs_lt]
  constructor <;> linarith

private theorem pointedPackingCompactness
    {K : Region} {Y : ℕ → Set ℝ} {δ : ℝ} :
    0 < δ →
    (∀ n, 0 ∈ Y n) →
    (∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y) →
    (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n))) →
    ∃ (φ : ℕ → ℕ) (Z : Set ℝ), StrictMono φ ∧ 0 ∈ Z ∧
      PointedFellConverges (fun n ↦ Y (φ n)) Z ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y) ∧
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)) := by
  intro hδ h0Y hsepY hpackY
  let A : ℕ → Set Tiling.Plane := fun n ↦ imaginaryEmbedding '' Y n
  have hApack : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (A n)) := by
    intro n
    exact hpackY n
  have hAsep : ∀ n, IsUniformlySeparated δ (A n) := by
    intro n
    exact image_uniformlySeparated hδ (hsepY n)
  have hAclosed : ∀ n, IsClosed (A n) := by
    intro n
    exact image_closed_of_separated hδ (hsepY n)
  obtain ⟨φ, L, hφ, hLclosed, hLsep, hconv⟩ :=
    Tiling.AxisParallel.Foundations.exists_locallyFellConvergent_subsequence
      δ hδ A hAclosed hAsep
  have h0A : ∀ n, 0 ∈ A (φ n) := by
    intro n
    refine ⟨0, h0Y (φ n), ?_⟩
    simp [imaginaryEmbedding]
  have h0L : 0 ∈ L := by
    apply Tiling.AxisParallel.Topology.mem_of_locallyFellConverges_of_tendsto_mem
      hconv h0A
    exact tendsto_const_nhds
  have hLaxis : L ⊆ imaginaryEmbedding '' (Set.univ : Set ℝ) := by
    refine locallyFell_limit_on_imaginaryAxis (A := A ∘ φ) (L := L) ?_ hconv
    intro n z hz
    change z ∈ imaginaryEmbedding '' Y (φ n) at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact ⟨y, Set.mem_univ _, rfl⟩
  let Z : Set ℝ := {y | imaginaryEmbedding y ∈ L}
  have hL_eq : L = imaginaryEmbedding '' Z := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, hzy⟩ := hLaxis hz
      refine ⟨y, ?_, hzy⟩
      simpa [Z, hzy] using hz
    · rintro ⟨y, hy, rfl⟩
      exact hy
  have h0Z : 0 ∈ Z := by
    change imaginaryEmbedding 0 ∈ L
    simpa [imaginaryEmbedding] using h0L
  have hZsep : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hxy
    have hxL : imaginaryEmbedding x ∈ L := hx
    have hyL : imaginaryEmbedding y ∈ L := hy
    have hxy' : imaginaryEmbedding x ≠ imaginaryEmbedding y := by
      intro h
      exact hxy (by simpa [imaginaryEmbedding] using congrArg Complex.im h)
    simpa [imaginaryEmbedding_isometry.dist_eq] using hLsep hxL hyL hxy'
  have hLpack := isPacking_of_locallyFellConverges
    (fun n ↦ hApack (φ n)) hconv
  have hconvUniform : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ N, ∀ n, N ≤ n → ∀ x ∈ Metric.closedBall 0 R,
        |Metric.infDist x (A (φ n)) - Metric.infDist x L| < ε := by
    apply locallyFell_infDist_uniform hδ
      (fun n ↦ hAclosed (φ n)) hLclosed
      (fun n ↦ hAsep (φ n)) hLsep h0A h0L hconv
  refine ⟨φ, Z, hφ, h0Z, ?_, hZsep, ?_⟩
  · intro R hR ε hε
    obtain ⟨N, hN⟩ := hconvUniform R hR ε hε
    refine ⟨N, fun n hn x hx ↦ ?_⟩
    have hxR : |x| ≤ R := (abs_le).2 ⟨by linarith [hx.1], hx.2⟩
    have hxplane : imaginaryEmbedding x ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall]
      have hdist : dist 0 (imaginaryEmbedding x) = |x| := by
        calc
          dist 0 (imaginaryEmbedding x) =
              dist (imaginaryEmbedding 0) (imaginaryEmbedding x) := by
                simp [imaginaryEmbedding]
          _ = dist 0 x := imaginaryEmbedding_isometry.dist_eq _ _
          _ = |x| := by simp [Real.norm_eq_abs, dist_eq_norm]
      rw [dist_comm, hdist]
      exact hxR
    have hplane := hN n hn (imaginaryEmbedding x) hxplane
    rw [imaginaryEmbedding_image_infDist, hL_eq,
      imaginaryEmbedding_image_infDist] at hplane
    exact hplane
  · change Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (imaginaryEmbedding '' Z))
    rw [← hL_eq]
    exact hLpack


private def centre_vertex
    {C : ApproximationContext} (s : ↥C.centres) : ↥C.translatedVertices :=
  ⟨s, ⟨0, C.zero_mem_vertices, s, s.2, zero_add (s : Tiling.Plane)⟩⟩

private theorem centre_vertex_map
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (s : ↥C.centres) :
    mapTranslatedVertex phi (centre_vertex s) = Tphi s := by
  rw [mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint (centre_vertex s) = C.centrePoint s.1 s.2 := by
    apply Subtype.ext
    rfl
  rw [hpoint, ← hTphi s]

private theorem mapPoint_add_local
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : ControlledDisplacement C) :
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



private structure AlignedCompleteLineOrigins
    (C : ApproximationContext.{0}) (axis : Axis)
    (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S))) where
  anchor : S
  centreLevel : ℝ
  centreLevel_mem : centreLevel ∈ C.coordinateSpace
  centres_aligned : ∀ s : S,
    axis.transverseCoord s.1.1 = centreLevel
  completeLine_axis : ∀ L : ↥(completeBoundaryLines _ hSource),
    L.1.axis = axis
  completeLineVertex :
    ↥(completeBoundaryLines _ hSource) → ↥C.region.vertices
  completeLine_origin : ∀ L,
    L.1.level = axis.transverseCoord (completeLineVertex L).1 + centreLevel

private theorem sourceAxisAligned_of_imageAxisAligned
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (G : ℝ)
    (hLinked : Linked G (Subtype.val '' S)) (hG : G < P.scale)
    (hImageAligned : ∃ imageLevel : ℝ,
      ∀ s : S, axis.transverseCoord (Tphi s.1) = imageLevel) :
    ∃ sourceLevel : ℝ,
      ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel := by
  rcases hLinked with ⟨hNonempty, hconn⟩
  rcases hNonempty with ⟨x₀, hx₀⟩
  rcases hx₀ with ⟨s₀, hs₀, rfl⟩
  let s0 : S := ⟨s₀, hs₀⟩
  rcases hImageAligned with ⟨imageLevel, hImageAligned⟩
  have hprop : ∀ x ∈ Subtype.val '' S,
      axis.transverseCoord x = axis.transverseCoord s0.1.1 := by
    intro x hx
    have hprop' : ∀ y, y ∈ Subtype.val '' S →
        Relation.ReflTransGen
          (fun u v : Tiling.Plane =>
            u ∈ Subtype.val '' S ∧ v ∈ Subtype.val '' S ∧ dist u v < G)
          s0.1.1 y →
        axis.transverseCoord y = axis.transverseCoord s0.1.1 := by
      intro y hy hpath
      induction hpath with
      | refl => rfl
      | tail hpath hstep ih =>
        rcases hstep with ⟨hx, hy, hdist⟩
        rcases hx with ⟨sx, hsx, rfl⟩
        rcases hy with ⟨sy, hsy, rfl⟩
        have hxs : axis.transverseCoord (Tphi sx) = imageLevel := by
          simpa only using hImageAligned (show S from ⟨sx, hsx⟩)
        have hys : axis.transverseCoord (Tphi sy) = imageLevel := by
          simpa only using hImageAligned (show S from ⟨sy, hsy⟩)
        have hm1 := centre_vertex_map phi Tphi hTphi sx
        have hm2 := centre_vertex_map phi Tphi hTphi sy
        have hcontrol : dist (centre_vertex sx : Tiling.Plane)
            (centre_vertex sy : Tiling.Plane) < P.controlRadius := by
          simpa [centre_vertex] using
            lt_trans hdist (lt_trans hG P.scale_lt_controlRadius)
        have hreflect := deformation_reflectsFiniteValues P phi hphi axis.swap
          (centre_vertex sx) (centre_vertex sy)
          (centre_vertex sx) (centre_vertex sy) hcontrol hcontrol
        have hzeroImg : Axis.coord axis.swap
            (mapTranslatedVertex phi (centre_vertex sx) -
              mapTranslatedVertex phi (centre_vertex sy)) = 0 := by
          rw [hm1, hm2]
          have hcoord : Axis.coord axis.swap (Tphi sx - Tphi sy) =
              axis.transverseCoord (Tphi sx) -
                axis.transverseCoord (Tphi sy) := by
            cases axis <;> rfl
          rw [hcoord, hxs, hys]
          ring
        have hzeroSource : Axis.coord axis.swap
            ((centre_vertex sx : Tiling.Plane) - centre_vertex sy) = 0 :=
          (hreflect.2.1).mp hzeroImg
        have hzero : axis.transverseCoord
            ((sx : Tiling.Plane) - sy) = 0 := by
          cases axis <;>
            simpa [centre_vertex, Axis.swap, Axis.coord, Axis.transverseCoord,
              Complex.sub_re, Complex.sub_im] using hzeroSource
        have hxycoord : axis.transverseCoord (sx : Tiling.Plane) =
            axis.transverseCoord (sy : Tiling.Plane) := by
          rw [show axis.transverseCoord ((sx : Tiling.Plane) - sy) =
              axis.transverseCoord (sx : Tiling.Plane) -
                axis.transverseCoord (sy : Tiling.Plane) by
                cases axis <;> rfl] at hzero
          linarith
        exact hxycoord.symm.trans (ih ⟨sx, hsx, rfl⟩)
    exact hprop' x hx (hconn s0.1.1 ⟨s0.1, s0.2, rfl⟩ x hx)
  refine ⟨axis.transverseCoord s0.1.1, ?_⟩
  intro s
  exact hprop s.1 ⟨s.1, s.2, rfl⟩

private theorem mappedCompleteLineLevel_fromOrigin
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
    (B : AxisBoundaryCodeTransport C phi D Tphi S hSource hTarget)
    (O : AlignedCompleteLineOrigins C axis S hSource)
    (L : ↥(completeBoundaryLines _ hSource)) :
    (B.completeLineEquiv L).1.level =
      axis.transverseCoord
        (D.planarHomeomorph (O.completeLineVertex L).1 + Tphi O.anchor.1) := by
  rw [B.completeLineLevel_formula L]
  let v := O.completeLineVertex L
  let a := O.anchor
  have hq : axis.transverseCoord v.1 + O.centreLevel ∈ C.coordinateSpace := by
    cases axis with
    | horizontal =>
        exact C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2) O.centreLevel_mem
    | vertical =>
        exact C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2) O.centreLevel_mem
  have hscalar : B.completeLineLevelLift L =
      ⟨axis.transverseCoord v.1 + O.centreLevel, hq⟩ := by
    apply Subtype.ext
    rw [B.completeLineLevelLift_coe L, O.completeLine_origin L]
  rw [hscalar]
  have hmap : mapScalar phi
      (⟨axis.transverseCoord v.1 + O.centreLevel, hq⟩ : C.coordinateSpace) =
      axis.transverseCoord (D.planarHomeomorph v.1 + Tphi a.1) := by
    have hvmap := D.vertex_agreement v.1 v.2
    have hamap := hTphi a.1
    have halevel := O.centres_aligned a
    cases axis with
    | horizontal =>
        have hadd := mapPoint_add_local phi
          (C.vertexPoint v.1 v.2) (C.centrePoint a.1.1 a.1.2)
        rw [← hvmap, ← hamap] at hadd
        have halevel' : a.1.1.im = O.centreLevel := by
          simpa [Axis.transverseCoord] using halevel
        simpa [ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
          Axis.transverseCoord, mapPoint, mapScalar,
          Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, add_zero, zero_add, halevel'] using
          congrArg Complex.im hadd
    | vertical =>
        have hadd := mapPoint_add_local phi
          (C.vertexPoint v.1 v.2) (C.centrePoint a.1.1 a.1.2)
        rw [← hvmap, ← hamap] at hadd
        have halevel' : a.1.1.re = O.centreLevel := by
          simpa [Axis.transverseCoord] using halevel
        simpa [ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
          Axis.transverseCoord, mapPoint, mapScalar,
          Complex.add_re, Complex.add_im, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im, mul_zero, mul_one, add_zero, zero_add, halevel'] using
          congrArg Complex.re hadd
  exact hmap

private theorem completeBoundaryLines_vadd_local
    {F : Set Tiling.Plane} (hF : IsLocallyAxisParallelPolygonal F)
    (eta : Tiling.Plane)
    (hF' : IsLocallyAxisParallelPolygonal (eta +ᵥ F)) :
    completeBoundaryLines (eta +ᵥ F) hF' =
        (fun L ↦ L.vadd eta) '' completeBoundaryLines F hF := by
  have hfrontier : frontier (eta +ᵥ F) = eta +ᵥ frontier F :=
    frontier_vadd_eq eta F
  have hmem (z : Tiling.Plane) : z ∈ eta +ᵥ F ↔ z - eta ∈ F := by
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwz' : eta + w = z := by simpa only [vadd_eq_add] using hwz
      rw [← hwz']
      simpa only [add_sub_cancel_left] using hw
    · intro hz
      refine ⟨z - eta, hz, ?_⟩
      change eta + (z - eta) = z
      abel
  have hdist_sub (z x : Tiling.Plane) :
      dist (z - eta) (x - eta) = dist z x := by
    exact dist_sub_right z x eta
  have hdist_add (z x : Tiling.Plane) :
      dist (eta + z) (eta + x) = dist z x := by
    exact dist_add_left eta z x
  have hside (L : CompleteBoundaryLine) (z : Tiling.Plane) :
      (if L.insideOnPositiveSide then
          L.level < L.axis.transverseCoord (z - eta)
        else L.axis.transverseCoord (z - eta) < L.level) ↔
    (if (L.vadd eta).insideOnPositiveSide then
          (L.vadd eta).level < (L.vadd eta).axis.transverseCoord z
        else (L.vadd eta).axis.transverseCoord z < (L.vadd eta).level) := by
    rcases L with ⟨axis, level, positive⟩
    change (if positive then level < axis.transverseCoord (z - eta)
      else axis.transverseCoord (z - eta) < level) ↔
      (if positive then level + axis.transverseCoord eta < axis.transverseCoord z
        else axis.transverseCoord z < level + axis.transverseCoord eta)
    have hcoord : axis.transverseCoord (z - eta) =
        axis.transverseCoord z - axis.transverseCoord eta := by
      cases axis <;> rfl
    rw [hcoord]
    cases axis <;> cases positive
    all_goals norm_num
    all_goals constructor <;> intro h <;> linarith
  have hline : ∀ L : CompleteBoundaryLine,
      L ∈ completeBoundaryLines F hF ↔
        L.vadd eta ∈ completeBoundaryLines (eta +ᵥ F) hF' := by
    intro L
    constructor
    · intro hL
      change (L.vadd eta).carrier ⊆ frontier (eta +ᵥ F) ∧ _
      constructor
      · intro z hz
        have hzlevel : L.axis.transverseCoord z =
            L.level + L.axis.transverseCoord eta := hz
        let x := z - eta
        have hx : x ∈ L.carrier := by
          change L.axis.transverseCoord x = L.level
          dsimp [x]
          rw [show L.axis.transverseCoord (z - eta) =
              L.axis.transverseCoord z - L.axis.transverseCoord eta by
                cases L.axis <;> rfl, hzlevel]
          ring
        have hxf := hL.1 hx
        rw [hfrontier]
        refine ⟨x, hxf, ?_⟩
        dsimp [x]
        abel
      · intro z hz
        have hzlevel : L.axis.transverseCoord z =
            L.level + L.axis.transverseCoord eta := hz
        let x := z - eta
        have hx : x ∈ L.carrier := by
          change L.axis.transverseCoord x = L.level
          dsimp [x]
          rw [show L.axis.transverseCoord (z - eta) =
              L.axis.transverseCoord z - L.axis.transverseCoord eta by
                cases L.axis <;> rfl, hzlevel]
          ring
        rcases hL.2 x hx with ⟨r, hr, hlocal⟩
        refine ⟨r, hr, ?_⟩
        intro w hw
        have hw' : w - eta ∈ Metric.ball (z - eta) r := by
          change dist (w - eta) (z - eta) < r
          rw [hdist_sub]
          exact hw
        have hsrc := hlocal (w - eta) hw'
        exact (hmem w).trans (hsrc.trans (hside L w))
    · intro hL
      change (L.vadd eta).carrier ⊆ frontier (eta +ᵥ F) ∧ _ at hL
      constructor
      · intro x hx
        have hxeq : (eta + x) ∈ (L.vadd eta).carrier := by
          change (L.vadd eta).axis.transverseCoord (eta + x) =
            (L.vadd eta).level
          dsimp [CompleteBoundaryLine.vadd]
          rw [show L.axis.transverseCoord (eta + x) =
              L.axis.transverseCoord eta + L.axis.transverseCoord x by
                cases L.axis <;> rfl]
          rw [show L.axis.transverseCoord x = L.level from hx]
          ring
        have hxf := hL.1 hxeq
        rw [hfrontier] at hxf
        rcases hxf with ⟨y, hy, hyx⟩
        have hyx' : y = x := by
          change eta + y = eta + x at hyx
          exact add_left_cancel hyx
        simpa only [hyx'] using hy
      · intro x hx
        have hxeq : (eta + x) ∈ (L.vadd eta).carrier := by
          change (L.vadd eta).axis.transverseCoord (eta + x) =
            (L.vadd eta).level
          dsimp [CompleteBoundaryLine.vadd]
          rw [show L.axis.transverseCoord (eta + x) =
              L.axis.transverseCoord eta + L.axis.transverseCoord x by
                cases L.axis <;> rfl]
          rw [show L.axis.transverseCoord x = L.level from hx]
          ring
        rcases hL.2 (eta + x) hxeq with ⟨r, hr, hlocal⟩
        refine ⟨r, hr, ?_⟩
        intro z hz
        have hz' : eta + z ∈ Metric.ball (eta + x) r := by
          change dist (eta + z) (eta + x) < r
          rw [hdist_add]
          exact hz
        have htarget := hlocal (eta + z) hz'
        have hmem' : eta + z ∈ eta +ᵥ F ↔ z ∈ F := by
          simpa only [add_sub_cancel_left] using hmem (eta + z)
        have hside' := (hside L (eta + z)).symm
        simpa only [add_sub_cancel_left] using
          hmem'.symm.trans (htarget.trans hside')
  apply Set.ext
  intro L
  constructor
  · intro hL
    let L' : CompleteBoundaryLine :=
      { axis := L.axis, level := L.level - L.axis.transverseCoord eta,
        insideOnPositiveSide := L.insideOnPositiveSide }
    have hLL' : L'.vadd eta = L := by
      cases L
      simp [L', CompleteBoundaryLine.vadd]
    refine ⟨L', (hline L').mpr ?_, ?_⟩
    · simpa only [hLL'] using hL
    · exact hLL'
  · rintro ⟨L, hL, rfl⟩
    exact (hline L).mp hL

private theorem localCone_vadd_local
    {F : Set Tiling.Plane} (hF : IsLocallyAxisParallelPolygonal F)
    (eta x : Tiling.Plane)
    (hF' : IsLocallyAxisParallelPolygonal (eta +ᵥ F))
    (hx : x ∈ properVertices F)
    (hx' : eta + x ∈ properVertices (eta +ᵥ F)) :
    localCone (eta +ᵥ F) (eta + x) hF' hx' =
      localCone F x hF hx := by
  exact (localCone_eq_of_vadd_eq hF hF' hx hx' rfl).symm

private theorem translatedBoundaryData
    {F₀ F₁ : Set Tiling.Plane}
    (hF₀ : IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : IsLocallyAxisParallelPolygonal F₁)
    (eta : Tiling.Plane)
    (hEq : F₁ = eta +ᵥ F₀) :
    completeBoundaryLines F₁ hF₁ =
        (fun L ↦ L.vadd eta) '' completeBoundaryLines F₀ hF₀ ∧
      ∀ (x : Tiling.Plane)
        (hx₀ : x ∈ properVertices F₀)
        (hx₁ : eta + x ∈ properVertices F₁),
        localCone F₁ (eta + x) hF₁ hx₁ =
          localCone F₀ x hF₀ hx₀ := by
  subst F₁
  constructor
  · exact completeBoundaryLines_vadd_local hF₀ eta hF₁
  · intro x hx₀ hx₁
    exact localCone_vadd_local hF₀ eta x hF₁ hx₀ hx₁

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology

/- Finite windows and coordinate arrangements transport a proper-vertex witness
   to nearby packings; diagonal selection then yields pointwise persistence. -/

private theorem finite_scalar_window_finset
    {S : Set ℝ} {a b δ : ℝ}
    (hδ : 0 < δ)
    (hsep : S.Pairwise fun x y ↦ δ ≤ dist x y) :
    ∃ Q : Finset ℝ, ∀ z : ℝ, z ∈ Q ↔ z ∈ S ∩ Set.Icc a b := by
  have hclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hδ hsep
  have hdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s δ, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · have hsep' := hsep htS hs hts
        simp only [Metric.mem_ball] at htball
        exact False.elim ((not_lt_of_ge (by simpa [dist_comm] using hsep')) htball)
    · rintro rfl
      exact ⟨Metric.mem_ball_self hδ, hs⟩
  have hcompact : IsCompact (S ∩ Set.Icc a b) := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact hclosed.inter isClosed_Icc
    · exact (Metric.isBounded_Icc a b).subset inter_subset_right
  have hfinite : (S ∩ Set.Icc a b).Finite :=
    hcompact.finite (hdiscrete.mono inter_subset_left)
  classical
  refine ⟨hfinite.toFinset, ?_⟩
  intro z
  simp [hfinite.mem_toFinset]

private theorem finite_imaginary_window_finset
    {S : Set ℝ} {a b δ : ℝ}
    (hδ : 0 < δ)
    (hsep : S.Pairwise fun x y ↦ δ ≤ dist x y) :
    ∃ Q : Finset Tiling.Plane,
      ∀ t : Tiling.Plane, t ∈ Q ↔
        ∃ y ∈ S ∩ Set.Icc a b, imaginaryEmbedding y = t := by
  obtain ⟨P, hP⟩ := finite_scalar_window_finset hδ hsep
  refine ⟨P.image imaginaryEmbedding, ?_⟩
  intro t
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hyP, rfl⟩
    exact ⟨y, (hP y).mp hyP, rfl⟩
  · rintro ⟨y, hyS, rfl⟩
    exact ⟨y, (hP y).mpr hyS, rfl⟩

private theorem approximant_window_finsets
    {K : Region} {Y : ℕ → Set ℝ} (R : ℝ)
    (hY : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y n))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n, ∃ Qn : Finset Tiling.Plane,
      ∀ t : Tiling.Plane, t ∈ Qn ↔
        ∃ y ∈ Y n ∩ Set.Icc (-R) R,
          imaginaryEmbedding y = t := by
  obtain ⟨δ, hδ, hδall⟩ := Tiling.AxisParallel.exists_packingSeparation K
  refine ⟨δ, hδ, ?_⟩
  intro n
  have hsepn : ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hxy
    have hplane := hδall (imaginaryEmbedding '' Y n) (hY n)
    have hxy' : imaginaryEmbedding x ≠
        imaginaryEmbedding y := by
      intro heq
      apply hxy
      simpa [imaginaryEmbedding] using congrArg Complex.im heq
    have hdist := hplane (imaginaryEmbedding x)
      ⟨x, hx, rfl⟩ (imaginaryEmbedding y) ⟨y, hy, rfl⟩ hxy'
    have hdist' : dist (imaginaryEmbedding x)
        (imaginaryEmbedding y) = dist x y := by
      rw [dist_eq_norm]
      change ‖(x : ℂ) * Complex.I - (y : ℂ) * Complex.I‖ = dist x y
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul]
      simp only [Complex.norm_I, mul_one, dist_eq_norm, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hdist'] at hdist
    exact hdist
  exact finite_imaginary_window_finset hδ hsepn

private theorem window_openUnion_eq_of_relevant
    {K : Region} {S : Set Tiling.Plane} {Q : Finset Tiling.Plane}
    {c : Tiling.Plane} {r : ℝ}
    (hQmem : ∀ t ∈ (Q : Set Tiling.Plane), t ∈ S)
    (hQsub : ∀ t ∈ S,
      ((t +ᵥ K.openCarrier) ∩ Metric.ball c r).Nonempty →
        t ∈ (Q : Set Tiling.Plane)) :
    ∀ z ∈ Metric.ball c r,
      z ∈ openUnion K S ↔ z ∈ openUnion K (Q : Set Tiling.Plane) := by
  intro z hz
  constructor
  · intro hzS
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier] at hzS ⊢
    rw [Set.mem_iUnion] at hzS ⊢
    obtain ⟨t, htz⟩ := hzS
    have hrel : (((t : Tiling.Plane) +ᵥ K.openCarrier) ∩ Metric.ball c r).Nonempty := by
      refine ⟨z, ?_⟩
      exact ⟨htz, hz⟩
    have htQ : (t : Tiling.Plane) ∈ (Q : Set Tiling.Plane) :=
      hQsub (t : Tiling.Plane) t.property hrel
    exact ⟨⟨t, htQ⟩, htz⟩
  · intro hzQ
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier] at hzQ ⊢
    rw [Set.mem_iUnion] at hzQ ⊢
    obtain ⟨t, htz⟩ := hzQ
    have htS : (t : Tiling.Plane) ∈ S := by
      exact hQmem (t : Tiling.Plane) t.property
    exact ⟨⟨t, htS⟩, htz⟩

private theorem scalar_window_contains_relevant
    {K : Region} {S : Set ℝ} {y : ℝ}
    {w : Tiling.Plane} {r RK R : ℝ}
    (_hy : y ∈ S)
    (hK : ∀ z ∈ K.support, dist z 0 ≤ RK)
    (_hr : 0 ≤ r)
    (hR : RK + r + dist w 0 ≤ R)
    (hrel : ((imaginaryEmbedding y +ᵥ K.support) ∩
      Metric.ball w r).Nonempty) :
    y ∈ Set.Icc (-R) R := by
  obtain ⟨z, hzK, hzw⟩ := hrel
  obtain ⟨u, hu, huz⟩ := hzK
  have hzu : dist (u : Tiling.Plane) 0 ≤ RK := hK u hu
  have hcenter : dist (imaginaryEmbedding y) 0 ≤
      RK + dist z 0 := by
    have hdist : dist (imaginaryEmbedding y) z = dist u 0 := by
      simp only [dist_eq_norm]
      simp only [sub_zero]
      change ‖(imaginaryEmbedding y) - z‖ = ‖u‖
      rw [← huz]
      change ‖(imaginaryEmbedding y) -
        (imaginaryEmbedding y + u)‖ = ‖u‖
      simp [sub_eq_add_neg]
    calc
      dist (imaginaryEmbedding y) 0 ≤
          dist (imaginaryEmbedding y) z + dist z 0 :=
        dist_triangle _ _ _
      _ = dist u 0 + dist z 0 := by rw [hdist]
      _ ≤ RK + dist z 0 := add_le_add hzu (le_refl _)
  have hzw' : dist z 0 ≤ r + dist w 0 := by
    have := (Metric.mem_ball.mp hzw)
    exact (dist_triangle z w 0).trans
      (add_le_add (le_of_lt this) (le_refl _))
  have hscalar : |y| ≤ R := by
    have hzscalar : dist (imaginaryEmbedding y) 0 = |y| := by
      simp [imaginaryEmbedding, dist_eq_norm, Complex.norm_def]
    rw [hzscalar] at hcenter
    linarith
  exact ⟨(neg_le_neg hscalar).trans (neg_abs_le y),
    (le_abs_self y).trans hscalar⟩

private theorem finite_window_relevant_subset
    {K : Region} {S : Set ℝ} {Q : Finset Tiling.Plane}
    {w : Tiling.Plane} {r RK R : ℝ}
    (hQchar : ∀ t : Tiling.Plane, t ∈ Q ↔
      ∃ y ∈ S ∩ Set.Icc (-R) R,
        imaginaryEmbedding y = t)
    (hK : ∀ z ∈ K.support, dist z 0 ≤ RK)
    (hr : 0 ≤ r)
    (hR : RK + r + dist w 0 ≤ R) :
    ∀ t ∈ S, ((imaginaryEmbedding t +ᵥ K.openCarrier) ∩
      Metric.ball w r).Nonempty →
      imaginaryEmbedding t ∈ (Q : Set Tiling.Plane) := by
  intro t ht hrel
  have hsupport : K.openCarrier ⊆ K.support := interior_subset
  have hrel' : ((imaginaryEmbedding t +ᵥ K.support) ∩
      Metric.ball w r).Nonempty := by
    obtain ⟨z, hzopen, hzw⟩ := hrel
    obtain ⟨u, hu, huz⟩ := Set.mem_vadd_set.mp hzopen
    refine ⟨z, ?_, hzw⟩
    rw [← huz]
    exact ⟨u, hsupport hu, rfl⟩
  have htIcc := scalar_window_contains_relevant ht hK hr hR hrel'
  exact (hQchar (imaginaryEmbedding t)).mpr
    ⟨t, ⟨ht, htIcc⟩, rfl⟩

private theorem finite_window_regularSupport_local
    {K : Region} {S : Set Tiling.Plane} {Q : Finset Tiling.Plane}
    {w : Tiling.Plane} {r : ℝ}
    (hr : 0 < r)
    (hQmem : ∀ t ∈ (Q : Set Tiling.Plane), t ∈ S)
    (hQsub : ∀ t ∈ S,
      ((t +ᵥ K.openCarrier) ∩ Metric.ball w r).Nonempty →
        t ∈ (Q : Set Tiling.Plane)) :
    ∃ r' : ℝ, 0 < r' ∧ ∀ z ∈ Metric.ball w r',
      z ∈ regularSupport K S ↔ z ∈ regularSupport K (Q : Set Tiling.Plane) := by
  have hlocal := regularSupport_eq_of_openUnion_eq_on_ball hr
      (window_openUnion_eq_of_relevant hQmem hQsub)
  refine ⟨r / 4, by positivity, ?_⟩
  intro z hz
  simpa [regularSupport, Tiling.Polygonal.regularSupport,
    ← openUnion.eq_def] using hlocal z hz

/-!
# Finite full-line coordinate arrangements

This block isolates the coordinate part of the finite-arrangement argument.
The sorted coordinate lists are represented by strict `Fin`-indexed level
maps; the outer artificial lines are therefore part of the data.  The
remaining production-side bridge is the identification of a tile's Boolean
cell value with `regularSupport` away from the vertex coordinate grid.
-/





open Set




open Tiling.AxisParallel.IntrinsicVertices

open Tiling AxisParallel
open Tiling.AxisParallel.IntrinsicVertices

private structure FullLineCoordinateGrid (m n : ℕ) where
  xLevel : Fin (m + 1) → ℝ
  yLevel : Fin (n + 1) → ℝ
  x_strict : StrictMono xLevel
  y_strict : StrictMono yLevel

private def gridCell {m n : ℕ} (G : FullLineCoordinateGrid m n)
    (i : Fin m) (j : Fin n) : Set Tiling.Plane :=
  {z | G.xLevel i.castSucc < z.re ∧ z.re < G.xLevel i.succ ∧
    G.yLevel j.castSucc < z.im ∧ z.im < G.yLevel j.succ}

private def gridAnchor {m n : ℕ} (G : FullLineCoordinateGrid m n)
    (i : Fin m) (j : Fin n) : Tiling.Plane :=
  ((G.xLevel i.castSucc + G.xLevel i.succ) / 2 : ℝ) +
    ((G.yLevel j.castSucc + G.yLevel j.succ) / 2 : ℝ) * Complex.I

private theorem gridAnchor_mem_cell
    {m n : ℕ}
    (G : FullLineCoordinateGrid m n) (i : Fin m) (j : Fin n) :
    gridAnchor G i j ∈ gridCell G i j := by
  dsimp [gridAnchor, gridCell]
  simp
  constructor
  · nlinarith [G.x_strict (Fin.castSucc_lt_succ : i.castSucc < i.succ)]
  · constructor
    · nlinarith [G.x_strict (Fin.castSucc_lt_succ : i.castSucc < i.succ)]
    · constructor
      · nlinarith [G.y_strict (Fin.castSucc_lt_succ : j.castSucc < j.succ)]
      · nlinarith [G.y_strict (Fin.castSucc_lt_succ : j.castSucc < j.succ)]

private theorem mem_vadd_openCarrier_iff_sub_mem
    {K : Region} {t x : Tiling.Plane} :
    x ∈ t +ᵥ K.openCarrier ↔ x - t ∈ K.openCarrier := by
  constructor
  · rintro ⟨z, hz, hzx⟩
    change t + z = x at hzx
    rw [← hzx]
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz
  · intro hx
    refine ⟨x - t, hx, ?_⟩
    change t + (x - t) = x
    abel

private theorem translated_openCarrier_cell_constancy
    {K : Region} {t x y : Tiling.Plane}
    (hxoff : OffVertexCoordinateGrid K (x - t))
    (hyoff : OffVertexCoordinateGrid K (y - t))
    (hsame : SameVertexGridCell K (x - t) (y - t)) :
    (x ∈ t +ᵥ K.openCarrier ↔ y ∈ t +ᵥ K.openCarrier) := by
  rw [mem_vadd_openCarrier_iff_sub_mem, mem_vadd_openCarrier_iff_sub_mem]
  exact sameVertexGridCell_openCarrier_iff K (x - t) (y - t) hxoff hyoff hsame

private theorem finite_openUnion_cell_constancy
    {K : Region} (Q : Finset Tiling.Plane) {x y : Tiling.Plane}
    (hconst : ∀ t ∈ Q,
      OffVertexCoordinateGrid K (x - t) ∧
        OffVertexCoordinateGrid K (y - t) ∧
        SameVertexGridCell K (x - t) (y - t)) :
    (x ∈ openUnion K (Q : Set Tiling.Plane) ↔
      y ∈ openUnion K (Q : Set Tiling.Plane)) := by
  change (x ∈ ⋃ s : (Q : Set Tiling.Plane),
      (s : Tiling.Plane) +ᵥ K.openCarrier ↔
      y ∈ ⋃ s : (Q : Set Tiling.Plane),
        (s : Tiling.Plane) +ᵥ K.openCarrier)
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
    have hxy := translated_openCarrier_cell_constancy
      (t := (s : Tiling.Plane)) (x := x) (y := y)
      (hconst (s : Tiling.Plane) s.property).1
      (hconst (s : Tiling.Plane) s.property).2.1
      (hconst (s : Tiling.Plane) s.property).2.2
    exact Set.mem_iUnion.mpr ⟨s, hxy.mp hs⟩
  · intro hy
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hy
    have hxy := translated_openCarrier_cell_constancy
      (t := (s : Tiling.Plane)) (x := x) (y := y)
      (hconst (s : Tiling.Plane) s.property).1
      (hconst (s : Tiling.Plane) s.property).2.1
      (hconst (s : Tiling.Plane) s.property).2.2
    exact Set.mem_iUnion.mpr ⟨s, hxy.mpr hs⟩


open Tiling AxisParallel

private structure BooleanQuad where
  northwest : Bool
  northeast : Bool
  southwest : Bool
  southeast : Bool

private def straightQuad (q : BooleanQuad) : Prop :=
  (q.northwest = q.northeast ∧ q.southwest = q.southeast) ∨
    (q.northwest = q.southwest ∧ q.northeast = q.southeast)

private def nonstraightQuad (q : BooleanQuad) : Prop := ¬ straightQuad q

private def quadAt {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i : Fin m) (j : Fin n) : BooleanQuad where
  northwest := M i.castSucc j.castSucc
  northeast := M i.castSucc j.succ
  southwest := M i.succ j.castSucc
  southeast := M i.succ j.succ

private theorem adjacent_eq_gives_constant
    {n : ℕ} (f : Fin (n + 1) → Bool)
    (h : ∀ j : Fin n, f j.castSucc = f j.succ) :
    ∀ j, f j = f 0 := by
  intro j
  induction j using Fin.induction with
  | zero => rfl
  | succ j ih =>
      exact (h j).symm.trans ih

private theorem straight_edge_propagation
    {a b c d : Bool}
    (h : straightQuad ⟨a, b, c, d⟩) :
    (a = b → c = d) ∧
      (a ≠ b → c ≠ d) ∧
        (a ≠ b → a = c ∧ b = d) := by
  rcases h with ⟨hab, hcd⟩ | ⟨hac, hbd⟩
  · refine ⟨fun _ ↦ hcd, fun hne ↦ (hne hab).elim, ?_⟩
    intro hne
    exact (hne hab).elim
  · refine ⟨?_, ?_, fun _ ↦ ⟨hac, hbd⟩⟩
    · intro hab
      exact hac.symm.trans (hab.trans hbd)
    · intro hne hcd
      apply hne
      exact hac.trans (hcd.trans hbd.symm)

private theorem pair_matches_if_first_not_constant
    {n : ℕ} (f g : Fin (n + 1) → Bool)
    (hedge : ∀ j : Fin n,
      straightQuad ⟨f j.castSucc, f j.succ, g j.castSucc, g j.succ⟩)
    (hf : ¬ ∀ j, f j = f 0) :
    ∀ j, f j = g j := by
  induction n with
  | zero =>
      exfalso
      apply hf
      intro j
      exact Fin.eq_zero j ▸ rfl
  | succ n ih =>
      let fprev : Fin (n + 1) → Bool := fun j ↦ f j.castSucc
      let gprev : Fin (n + 1) → Bool := fun j ↦ g j.castSucc
      have hedgePrev : ∀ j : Fin n,
          straightQuad ⟨fprev j.castSucc, fprev j.succ,
            gprev j.castSucc, gprev j.succ⟩ := by
        intro j
        exact hedge j.castSucc
      by_cases hfprev : ∀ j : Fin (n + 1), fprev j = fprev 0
      · have hlastDiff : f (Fin.last n).castSucc ≠ f (Fin.last n).succ := by
          intro hlast
          apply hf
          intro j
          refine Fin.lastCases ?_ (fun j ↦ ?_) j
          · exact hlast.symm.trans (hfprev (Fin.last n))
          · exact hfprev j
        have hprevAdj : ∀ j : Fin n,
            gprev j.castSucc = gprev j.succ := by
          intro j
          have hprop := straight_edge_propagation (hedgePrev j)
          apply hprop.1
          exact (hfprev j.castSucc).trans (hfprev j.succ).symm
        have hprevConst := adjacent_eq_gives_constant gprev hprevAdj
        have hlastProp := straight_edge_propagation (hedge (Fin.last n))
        have hmatchLast :
            f (Fin.last n).castSucc = g (Fin.last n).castSucc := by
          exact (hlastProp.2.2 hlastDiff).1
        have hmatchLastSucc :
            f (Fin.last n).succ = g (Fin.last n).succ := by
          exact (hlastProp.2.2 hlastDiff).2
        intro j
        refine Fin.lastCases hmatchLastSucc (fun j ↦ ?_) j
        exact (hfprev j).trans ((hfprev (Fin.last n)).symm.trans
          (hmatchLast.trans ((hprevConst (Fin.last n)).trans
            (hprevConst j).symm)))
      · have hprefix : ∀ j : Fin (n + 1), fprev j = gprev j := by
          apply ih fprev gprev hedgePrev
          exact hfprev
        have hlastMatch :
            f (Fin.last n).succ = g (Fin.last n).succ := by
          have hprop := straight_edge_propagation (hedge (Fin.last n))
          by_cases htop : f (Fin.last n).castSucc = f (Fin.last n).succ
          · have hbottom := hprop.1 htop
            exact htop.symm.trans ((hprefix (Fin.last n)).trans hbottom)
          · exact (hprop.2.2 htop).2
        intro j
        refine Fin.lastCases hlastMatch (fun j ↦ ?_) j
        exact hprefix j

private theorem grid_straight_classification
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (hstraight : ∀ i : Fin m, ∀ j : Fin n,
      straightQuad (quadAt M i j)) :
    (∀ i : Fin (m + 1), ∀ j : Fin (n + 1), M i j = M i 0) ∨
      (∀ j : Fin (n + 1), ∀ i : Fin (m + 1), M i j = M 0 j) := by
  induction m with
  | zero =>
      right
      intro j i
      exact Fin.eq_zero i ▸ rfl
  | succ m ih =>
      let Mprev : Fin (m + 1) → Fin (n + 1) → Bool :=
        fun i j ↦ M i.castSucc j
      have hprev : ∀ i : Fin m, ∀ j : Fin n,
          straightQuad (quadAt Mprev i j) := by
        intro i j
        exact hstraight i.castSucc j
      rcases ih Mprev hprev with hrows | hcols
      · have hlastAdj : ∀ j : Fin n,
            M (Fin.last m).succ j.castSucc = M (Fin.last m).succ j.succ := by
          intro j
          have hprop := straight_edge_propagation (hstraight (Fin.last m) j)
          apply hprop.1
          exact (hrows (Fin.last m) j.castSucc).trans
            (hrows (Fin.last m) j.succ).symm
        have hlastConst := adjacent_eq_gives_constant
          (fun j ↦ M (Fin.last m).succ j) hlastAdj
        left
        intro i j
        refine Fin.lastCases (hlastConst j) (fun i ↦ ?_) i
        exact hrows i j
      · by_cases htop : ∀ j : Fin (n + 1), M 0 j = M 0 0
        · have hlastAdj : ∀ j : Fin n,
              M (Fin.last m).succ j.castSucc = M (Fin.last m).succ j.succ := by
            intro j
            have hprop := straight_edge_propagation (hstraight (Fin.last m) j)
            apply hprop.1
            have hc₁ : M (Fin.last m).castSucc j.castSucc = M 0 j.castSucc := by
              simpa only [Mprev, Fin.castSucc_zero] using hcols j.castSucc (Fin.last m)
            have hc₂ : M (Fin.last m).castSucc j.succ = M 0 j.succ := by
              simpa only [Mprev, Fin.castSucc_zero] using hcols j.succ (Fin.last m)
            have ht : M 0 j.castSucc = M 0 j.succ :=
              (htop j.castSucc).trans ((htop j.succ).symm)
            exact hc₁.trans (ht.trans hc₂.symm)
          have hlastConst := adjacent_eq_gives_constant
            (fun j ↦ M (Fin.last m).succ j) hlastAdj
          left
          intro i j
          refine Fin.lastCases (hlastConst j) (fun i ↦ ?_) i
          have hcj : M i.castSucc j = M 0 j := by
            simpa only [Mprev, Fin.castSucc_zero] using hcols j i
          have hc₀ : M i.castSucc 0 = M 0 0 := by
            simpa only [Mprev, Fin.castSucc_zero] using hcols 0 i
          have ht : M 0 j = M 0 0 :=
            (htop j).trans ((htop 0).symm)
          exact hcj.trans (ht.trans hc₀.symm)
        · let fold : Fin (n + 1) → Bool :=
            fun j ↦ M (Fin.last m).castSucc j
          let glast : Fin (n + 1) → Bool :=
            fun j ↦ M (Fin.last m).succ j
          have hedgeLast : ∀ j : Fin n,
              straightQuad ⟨fold j.castSucc, fold j.succ,
                glast j.castSucc, glast j.succ⟩ := by
            intro j
            exact hstraight (Fin.last m) j
          have hfold : ¬ ∀ j : Fin (n + 1), fold j = fold 0 := by
            intro hfoldConst
            apply htop
            intro j
            exact (hcols j (Fin.last m)).symm.trans
              ((hfoldConst j).trans (hcols 0 (Fin.last m)))
          have hmatch := pair_matches_if_first_not_constant
            fold glast hedgeLast hfold
          right
          intro j i
          refine Fin.lastCases ?_ (fun i ↦ ?_) i
          · exact (hmatch j).symm.trans (hcols j (Fin.last m))
          · exact hcols j i

private def rectangleQuad {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i₀ i₁ : Fin (m + 1)) (j₀ j₁ : Fin (n + 1)) : BooleanQuad where
  northwest := M i₀ j₀
  northeast := M i₀ j₁
  southwest := M i₁ j₀
  southeast := M i₁ j₁

private theorem rectangle_quad_straight
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (hstraight : ∀ i : Fin m, ∀ j : Fin n,
      straightQuad (quadAt M i j))
    (i₀ i₁ : Fin (m + 1)) (j₀ j₁ : Fin (n + 1)) :
    straightQuad (rectangleQuad M i₀ i₁ j₀ j₁) := by
  rcases grid_straight_classification M hstraight with hrows | hcols
  · apply Or.inl
    constructor
    · exact (hrows i₀ j₀).trans (hrows i₀ j₁).symm
    · exact (hrows i₁ j₀).trans (hrows i₁ j₁).symm
  · apply Or.inr
    constructor
    · exact (hcols j₀ i₀).trans (hcols j₀ i₁).symm
    · exact (hcols j₁ i₀).trans (hcols j₁ i₁).symm

private theorem exists_nonstraight_intervening_of_nonstraight_rectangle
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i₀ i₁ : Fin (m + 1)) (j₀ j₁ : Fin (n + 1))
    (hrectangle : nonstraightQuad (rectangleQuad M i₀ i₁ j₀ j₁)) :
    ∃ i : Fin m, ∃ j : Fin n, nonstraightQuad (quadAt M i j) := by
  by_contra hnone
  apply hrectangle
  apply rectangle_quad_straight M
  intro i j
  by_contra hbad
  exact hnone ⟨i, j, hbad⟩

private def SignedTwoAxisFrontierGerm
    (D : Set Tiling.Plane) (x : Tiling.Plane) (r : ℝ)
    (reSign imSign : Bool) : Prop :=
  ∀ t : ℝ, 0 < t → t < r →
    x + (if reSign then (t : Tiling.Plane) else -(t : Tiling.Plane)) ∈ frontier D ∧
      x + (if imSign then (t : Tiling.Plane) * Complex.I
        else -((t : Tiling.Plane) * Complex.I)) ∈ frontier D

private theorem not_boundaryLocallyStraight_of_signedTwoAxisFrontierGerm
    {D : Set Tiling.Plane} {x : Tiling.Plane} {r : ℝ}
    {reSign imSign : Bool} (hr : 0 < r)
    (haxis : SignedTwoAxisFrontierGerm D x r reSign imSign) :
    ¬ Tiling.BoundaryLocallyStraightAt D x := by
  intro hstraight
  obtain ⟨L, hxL, hLdim, hlocal⟩ := hstraight
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
  let δ : ℝ := min r ρ / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hδr : δ < r := by
    dsimp [δ]
    have hmin : min r ρ ≤ r := min_le_left _ _
    nlinarith
  have hδρ : δ < ρ := by
    dsimp [δ]
    have hmin : min r ρ ≤ ρ := min_le_right _ _
    nlinarith
  let reVec : Tiling.Plane :=
    if reSign then (δ : Tiling.Plane) else -(δ : Tiling.Plane)
  let imVec : Tiling.Plane :=
    if imSign then (δ : Tiling.Plane) * Complex.I
      else -((δ : Tiling.Plane) * Complex.I)
  let y : Tiling.Plane := x + reVec
  let z : Tiling.Plane := x + imVec
  have hyball : y ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [y, reVec]
    simp only [add_sub_cancel_left]
    by_cases hs : reSign = true
    · simpa [hs, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hδρ
    · have hs' : reSign = false := Bool.eq_false_of_not_eq_true hs
      simpa [hs', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ] using hδρ
  have hzball : z ∈ Metric.ball x ρ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    dsimp [z, imVec]
    simp only [add_sub_cancel_left]
    by_cases hs : imSign = true
    · simpa [hs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ, Complex.norm_I] using hδρ
    · have hs' : imSign = false := Bool.eq_false_of_not_eq_true hs
      simpa [hs', norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hδ, Complex.norm_I] using hδρ
  obtain ⟨hyfront, hzfront⟩ := haxis δ hδ hδr
  have hyL : y ∈ L := (hball hyball).mp hyfront
  have hzL : z ∈ L := (hball hzball).mp hzfront
  have hsRe : reVec ∈ L.direction := by
    have h := L.vsub_mem_direction hyL hxL
    change y - x ∈ L.direction at h
    rw [show y - x = reVec by dsimp [y]; abel] at h
    exact h
  have hsIm : imVec ∈ L.direction := by
    have h := L.vsub_mem_direction hzL hxL
    change z - x ∈ L.direction at h
    rw [show z - x = imVec by dsimp [z]; abel] at h
    exact h
  have hdirδ : (δ : Tiling.Plane) ∈ L.direction := by
    by_cases hs : reSign
    · simpa [reVec, hs] using hsRe
    · have hneg := L.direction.neg_mem (show -(δ : Tiling.Plane) ∈ L.direction by
        simpa [reVec, hs] using hsRe)
      simpa using hneg
  have hdirI : (δ : Tiling.Plane) * Complex.I ∈ L.direction := by
    by_cases hs : imSign
    · simpa [imVec, hs] using hsIm
    · have hneg := L.direction.neg_mem
        (show -((δ : Tiling.Plane) * Complex.I) ∈ L.direction by
          simpa [imVec, hs] using hsIm)
      simpa using hneg
  have htop : L.direction = ⊤ := by
    apply top_unique
    intro w hw
    have h₁ := L.direction.smul_mem (w.re / δ) hdirδ
    have h₂ := L.direction.smul_mem (w.im / δ) hdirI
    have hsum := L.direction.add_mem h₁ h₂
    change w ∈ L.direction
    have hw_eq : w = (w.re / δ) • (δ : Tiling.Plane) +
        (w.im / δ) • ((δ : Tiling.Plane) * Complex.I) := by
      apply Complex.ext <;>
        simp only [Complex.add_re, Complex.add_im, Complex.smul_re,
          Complex.smul_im, smul_eq_mul, Complex.mul_re, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          mul_zero, mul_one, sub_zero, add_zero, zero_add]
      · field_simp [ne_of_gt hδ]
      · field_simp [ne_of_gt hδ]
    rw [hw_eq]
    exact hsum
  rw [htop, finrank_top, Complex.finrank_real_complex] at hLdim
  norm_num at hLdim

private theorem nonstraightQuad_has_both_axis_changes (q : BooleanQuad)
    (hnon : nonstraightQuad q) :
    (q.northwest ≠ q.northeast ∨ q.southwest ≠ q.southeast) ∧
      (q.northwest ≠ q.southwest ∨ q.northeast ≠ q.southeast) := by
  constructor
  · by_contra h
    push Not at h
    exact hnon (Or.inl h)
  · by_contra h
    push Not at h
    exact hnon (Or.inr h)

private def quadrantAtBool (qre qim : Bool) (a z : Tiling.Plane) : Prop :=
  (if qre then a.re < z.re else z.re < a.re) ∧
    (if qim then a.im < z.im else z.im < a.im)

private def quadValue (q : BooleanQuad) (qre qim : Bool) : Bool :=
  if qim then
    if qre then q.northeast else q.northwest
  else if qre then q.southeast else q.southwest

private def QuadrantGermOccupancy
    (D : Set Tiling.Plane) (a : Tiling.Plane) (r : ℝ) (q : BooleanQuad) : Prop :=
  ∀ (qre qim : Bool) (z : Tiling.Plane),
    z ∈ Metric.ball a r → quadrantAtBool qre qim a z →
      (z ∈ D ↔ quadValue q qre qim = true)

private def ApproachesQuadrant
    (a : Tiling.Plane) (r : ℝ) (qre qim : Bool) (y : Tiling.Plane) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ z : Tiling.Plane, z ∈ Metric.ball a r ∧
      quadrantAtBool qre qim a z ∧ dist z y < ε

private theorem frontier_of_opposite_quadrant_germs
    {D : Set Tiling.Plane} {a y : Tiling.Plane} {r : ℝ}
    (q : BooleanQuad)
    (hoccupies : QuadrantGermOccupancy D a r q)
    (qre₀ qim₀ qre₁ qim₁ : Bool)
    (happroach₀ : ApproachesQuadrant a r qre₀ qim₀ y)
    (happroach₁ : ApproachesQuadrant a r qre₁ qim₁ y)
    (hneq : quadValue q qre₀ qim₀ ≠ quadValue q qre₁ qim₁) :
    y ∈ frontier D := by
  have hclosure : y ∈ closure D := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    by_cases h₀ : quadValue q qre₀ qim₀ = true
    · obtain ⟨z, hzball, hzq, hzy⟩ := happroach₀ ε hε
      exact ⟨z, (hoccupies qre₀ qim₀ z hzball hzq).mpr h₀, by
        simpa [dist_comm] using hzy⟩
    · have h₁ : quadValue q qre₁ qim₁ = true := by
        cases hval : quadValue q qre₁ qim₁ <;> simp_all
      obtain ⟨z, hzball, hzq, hzy⟩ := happroach₁ ε hε
      exact ⟨z, (hoccupies qre₁ qim₁ z hzball hzq).mpr h₁, by
        simpa [dist_comm] using hzy⟩
  have hnotInterior : y ∉ interior D := by
    intro hy
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hy)
    by_cases h₀ : quadValue q qre₀ qim₀ = true
    · have h₁ : quadValue q qre₁ qim₁ ≠ true := by
        intro h₁
        exact hneq (h₀.trans h₁.symm)
      obtain ⟨z, hzball, hzq, hzy⟩ := happroach₁ ε hε
      have hznot : z ∉ D := by
        intro hzD
        exact h₁ ((hoccupies qre₁ qim₁ z hzball hzq).mp hzD)
      exact hznot (interior_subset (hball hzy))
    · have h₁ : quadValue q qre₁ qim₁ = true := by
        cases hval : quadValue q qre₁ qim₁ <;> simp_all
      obtain ⟨z, hzball, hzq, hzy⟩ := happroach₀ ε hε
      have hznot : z ∉ D := by
        intro hzD
        exact h₀ ((hoccupies qre₀ qim₀ z hzball hzq).mp hzD)
      exact hznot (interior_subset (hball hzy))
  rw [frontier]
  exact ⟨hclosure, hnotInterior⟩

private theorem approachesQuadrant_realAxis
    {a : Tiling.Plane} {r t : ℝ} (ht : 0 < t) (htr : t < r) (sgn qim : Bool) :
    ApproachesQuadrant a r sgn qim
      (a + (if sgn then (t : Tiling.Plane) else -(t : Tiling.Plane))) := by
  intro ε hε
  let s : ℝ := min (ε / 2) ((r - t) / 2)
  have hrt : 0 < r - t := sub_pos.mpr htr
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsε : s < ε := by
    dsimp [s]
    have hmin : min (ε / 2) ((r - t) / 2) ≤ ε / 2 := min_le_left _ _
    nlinarith
  have hsr : t + s < r := by
    dsimp [s]
    have hmin : min (ε / 2) ((r - t) / 2) ≤ (r - t) / 2 := min_le_right _ _
    nlinarith
  let y : Tiling.Plane :=
    a + (if sgn then (t : Tiling.Plane) else -(t : Tiling.Plane))
  let z : Tiling.Plane :=
    y + (if qim then (s : Tiling.Plane) * Complex.I
      else -((s : Tiling.Plane) * Complex.I))
  have hzy : dist z y = s := by
    rw [Complex.dist_eq]
    dsimp [z]
    by_cases hq : qim = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        Complex.norm_I]
    · have hq' : qim = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        Complex.norm_I]
  have hya : dist y a = t := by
    rw [Complex.dist_eq]
    dsimp [y]
    by_cases hq : sgn = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    · have hq' : sgn = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc
      dist z a ≤ dist z y + dist y a := dist_triangle z y a
      _ = s + t := by rw [hzy, hya]
      _ < r := by linarith
  · dsimp [quadrantAtBool, z, y]
    by_cases hsng : sgn = true <;> by_cases hqim : qim = true
    · simp [hsng, hqim, ht, hs]
    · have hqim' : qim = false := Bool.eq_false_of_not_eq_true hqim
      simp [hsng, hqim', ht, hs]
    · have hsng' : sgn = false := Bool.eq_false_of_not_eq_true hsng
      simp [hsng', hqim, ht, hs]
    · have hsng' : sgn = false := Bool.eq_false_of_not_eq_true hsng
      simp [hsng', hqim, ht, hs]
  · change dist z y < ε
    rw [hzy]
    exact hsε

private theorem approachesQuadrant_imagAxis
    {a : Tiling.Plane} {r t : ℝ} (ht : 0 < t) (htr : t < r)
    (sgn qre : Bool) :
    ApproachesQuadrant a r qre sgn
      (a + (if sgn then (t : Tiling.Plane) * Complex.I
        else -((t : Tiling.Plane) * Complex.I))) := by
  intro ε hε
  let s : ℝ := min (ε / 2) ((r - t) / 2)
  have hrt : 0 < r - t := sub_pos.mpr htr
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsε : s < ε := by
    dsimp [s]
    have hmin : min (ε / 2) ((r - t) / 2) ≤ ε / 2 := min_le_left _ _
    nlinarith
  have hsr : t + s < r := by
    dsimp [s]
    have hmin : min (ε / 2) ((r - t) / 2) ≤ (r - t) / 2 := min_le_right _ _
    nlinarith
  let y : Tiling.Plane :=
    a + (if sgn then (t : Tiling.Plane) * Complex.I
      else -((t : Tiling.Plane) * Complex.I))
  let z : Tiling.Plane :=
    y + (if qre then (s : Tiling.Plane) else -(s : Tiling.Plane))
  have hzy : dist z y = s := by
    rw [Complex.dist_eq]
    dsimp [z]
    by_cases hq : qre = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    · have hq' : qre = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hya : dist y a = t := by
    rw [Complex.dist_eq]
    dsimp [y]
    by_cases hq : sgn = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, Complex.norm_I]
    · have hq' : sgn = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, Complex.norm_I]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc
      dist z a ≤ dist z y + dist y a := dist_triangle z y a
      _ = s + t := by rw [hzy, hya]
      _ < r := by linarith
  · dsimp [quadrantAtBool, z, y]
    by_cases hsng : sgn = true <;> by_cases hqre : qre = true
    · simp [hsng, hqre, ht, hs]
    · have hqre' : qre = false := Bool.eq_false_of_not_eq_true hqre
      simp [hsng, hqre', ht, hs]
    · have hsng' : sgn = false := Bool.eq_false_of_not_eq_true hsng
      simp [hsng', hqre, ht, hs]
    · have hsng' : sgn = false := Bool.eq_false_of_not_eq_true hsng
      have hqre' : qre = false := Bool.eq_false_of_not_eq_true hqre
      simp [hsng', hqre', ht, hs]
  · change dist z y < ε
    rw [hzy]
    exact hsε

private theorem properVertex_of_nonstraightQuadrantGerm
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hfrontier : a ∈ frontier D) (hr : 0 < r)
    (q : BooleanQuad) (hnon : nonstraightQuad q)
    (hoccupies : QuadrantGermOccupancy D a r q)
    (happroachRe :
      ∀ (sgn : Bool) (t : ℝ), 0 < t → t < r →
        ApproachesQuadrant a r sgn false
            (a + (if sgn then (t : Tiling.Plane) else -(t : Tiling.Plane))) ∧
        ApproachesQuadrant a r sgn true
            (a + (if sgn then (t : Tiling.Plane) else -(t : Tiling.Plane))))
    (happroachIm :
      ∀ (sgn : Bool) (t : ℝ), 0 < t → t < r →
        ApproachesQuadrant a r false sgn
            (a + (if sgn then (t : Tiling.Plane) * Complex.I
              else -((t : Tiling.Plane) * Complex.I))) ∧
        ApproachesQuadrant a r true sgn
            (a + (if sgn then (t : Tiling.Plane) * Complex.I
              else -((t : Tiling.Plane) * Complex.I)))) :
    a ∈ Tiling.AxisParallel.properVertices D := by
  change Tiling.AxisParallel.IsProperVertex D a
  refine ⟨hfrontier, ?_⟩
  obtain ⟨hImDiff, hReDiff⟩ := nonstraightQuad_has_both_axis_changes q hnon
  intro hstraight
  rcases hImDiff with hup | hdown <;> rcases hReDiff with hleft | hright
  · have hnot := not_boundaryLocallyStraight_of_signedTwoAxisFrontierGerm
      (reSign := false) (imSign := true) hr (by
        intro t ht htr
        have hRe := happroachRe false t ht htr
        have hIm := happroachIm true t ht htr
        have hfRe := frontier_of_opposite_quadrant_germs q hoccupies
          false true false false hRe.2 hRe.1 (by simpa [quadValue] using hleft)
        have hfIm := frontier_of_opposite_quadrant_germs q hoccupies
          false true true true hIm.1 hIm.2 (by simpa [quadValue] using hup)
        exact ⟨by simpa using hfRe, by simpa using hfIm⟩)
    exact hnot hstraight
  · have hnot := not_boundaryLocallyStraight_of_signedTwoAxisFrontierGerm
      (reSign := true) (imSign := true) hr (by
        intro t ht htr
        have hRe := happroachRe true t ht htr
        have hIm := happroachIm true t ht htr
        have hfRe := frontier_of_opposite_quadrant_germs q hoccupies
          true true true false hRe.2 hRe.1 (by simpa [quadValue] using hright)
        have hfIm := frontier_of_opposite_quadrant_germs q hoccupies
          false true true true hIm.1 hIm.2 (by simpa [quadValue] using hup)
        exact ⟨by simpa using hfRe, by simpa using hfIm⟩)
    exact hnot hstraight
  · have hnot := not_boundaryLocallyStraight_of_signedTwoAxisFrontierGerm
      (reSign := false) (imSign := false) hr (by
        intro t ht htr
        have hRe := happroachRe false t ht htr
        have hIm := happroachIm false t ht htr
        have hfRe := frontier_of_opposite_quadrant_germs q hoccupies
          false true false false hRe.2 hRe.1 (by simpa [quadValue] using hleft)
        have hfIm := frontier_of_opposite_quadrant_germs q hoccupies
          false false true false hIm.1 hIm.2 (by simpa [quadValue] using hdown)
        exact ⟨by simpa using hfRe, by simpa using hfIm⟩)
    exact hnot hstraight
  · have hnot := not_boundaryLocallyStraight_of_signedTwoAxisFrontierGerm
      (reSign := true) (imSign := false) hr (by
        intro t ht htr
        have hRe := happroachRe true t ht htr
        have hIm := happroachIm false t ht htr
        have hfRe := frontier_of_opposite_quadrant_germs q hoccupies
          true true true false hRe.2 hRe.1 (by simpa [quadValue] using hright)
        have hfIm := frontier_of_opposite_quadrant_germs q hoccupies
          false false true false hIm.1 hIm.2 (by simpa [quadValue] using hdown)
        exact ⟨by simpa using hfRe, by simpa using hfIm⟩)
    exact hnot hstraight

private theorem properVertex_of_nonstraightQuadrantGerm'
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hfrontier : a ∈ frontier D) (hr : 0 < r)
    (q : BooleanQuad) (hnon : nonstraightQuad q)
    (hoccupies : QuadrantGermOccupancy D a r q) :
    a ∈ Tiling.AxisParallel.properVertices D := by
  apply properVertex_of_nonstraightQuadrantGerm hfrontier hr q hnon hoccupies
  · intro sgn t ht htr
    exact ⟨approachesQuadrant_realAxis ht htr sgn false,
      approachesQuadrant_realAxis ht htr sgn true⟩
  · intro sgn t ht htr
    exact ⟨approachesQuadrant_imagAxis ht htr sgn false,
      approachesQuadrant_imagAxis ht htr sgn true⟩


private def arrangementCellValue {m n : ℕ}
    (D : Set Tiling.Plane) (G : FullLineCoordinateGrid m n)
    (i : Fin m) (j : Fin n) : Bool :=
  by classical exact decide (gridAnchor G i j ∈ D)

private def arrangementMatrix {m n : ℕ}
    (D : Set Tiling.Plane) (G : FullLineCoordinateGrid m n) :
    Fin m → Fin n → Bool :=
  fun i j ↦ arrangementCellValue D G i j

open Tiling.AxisParallel.IntrinsicVertices

private def sharedGridAnchor {m n : ℕ}
    (G : FullLineCoordinateGrid (m + 1) (n + 1))
    (i : Fin m) (j : Fin n) : Tiling.Plane :=
  (G.xLevel i.succ.castSucc : Tiling.Plane) +
    (G.yLevel j.succ.castSucc : Tiling.Plane) * Complex.I

private def gridQuadAt {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i : Fin m) (j : Fin n) : BooleanQuad where
  northwest := M i.castSucc j.succ
  northeast := M i.succ j.succ
  southwest := M i.castSucc j.castSucc
  southeast := M i.succ j.castSucc

private theorem shared_quadrant_cell
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    (i : Fin m) (j : Fin n) {r : ℝ}
    (_hr : 0 < r)
    (hleft : r < G.xLevel i.succ.castSucc - G.xLevel i.castSucc.castSucc)
    (hright : r < G.xLevel i.succ.succ - G.xLevel i.succ.castSucc)
    (hbelow : r < G.yLevel j.succ.castSucc - G.yLevel j.castSucc.castSucc)
    (habove : r < G.yLevel j.succ.succ - G.yLevel j.succ.castSucc)
    (qre qim : Bool) (z : Tiling.Plane)
    (hzball : z ∈ Metric.ball (sharedGridAnchor G i j) r)
    (hzq : quadrantAtBool qre qim (sharedGridAnchor G i j) z) :
    z ∈ gridCell G (if qre then i.succ else i.castSucc)
      (if qim then j.succ else j.castSucc) := by
  have hnorm : ‖z - sharedGridAnchor G i j‖ < r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hzball
  have hreabs : |z.re - (sharedGridAnchor G i j).re| < r := by
    exact lt_of_le_of_lt
      (by simpa only [Complex.sub_re] using
        (Complex.abs_re_le_norm (z - sharedGridAnchor G i j))) hnorm
  have himabs : |z.im - (sharedGridAnchor G i j).im| < r := by
    exact lt_of_le_of_lt
      (by simpa only [Complex.sub_im] using
        (Complex.abs_im_le_norm (z - sharedGridAnchor G i j))) hnorm
  have hcenterX : G.xLevel i.castSucc.succ = G.xLevel i.succ.castSucc := by
    rfl
  have hcenterY : G.yLevel j.castSucc.succ = G.yLevel j.succ.castSucc := by
    rfl
  cases qre <;> cases qim
  all_goals
    dsimp [gridCell] at ⊢
    dsimp [sharedGridAnchor] at hreabs himabs
    simp at hreabs himabs
    rcases hzq with ⟨hzre, hzim⟩
    norm_num [quadrantAtBool, sharedGridAnchor] at hzre hzim
    constructor
    · nlinarith [(abs_lt.mp hreabs).1, hleft, hcenterX]
    · constructor
      · nlinarith [(abs_lt.mp hreabs).2, hright, hcenterX]
      · constructor
        · nlinarith [(abs_lt.mp himabs).1, hbelow, hcenterY]
        · nlinarith [(abs_lt.mp himabs).2, habove, hcenterY]

private theorem sharedGrid_quadrantGerm_of_cellValues
    {m n : ℕ} {D : Set Tiling.Plane}
    (G : FullLineCoordinateGrid (m + 1) (n + 1))
    (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i : Fin m) (j : Fin n) {r : ℝ}
    (_hr : 0 < r)
    (hleft : r < G.xLevel i.succ.castSucc - G.xLevel i.castSucc.castSucc)
    (hright : r < G.xLevel i.succ.succ - G.xLevel i.succ.castSucc)
    (hbelow : r < G.yLevel j.succ.castSucc - G.yLevel j.castSucc.castSucc)
    (habove : r < G.yLevel j.succ.succ - G.yLevel j.succ.castSucc)
    (hcell : ∀ (u : Fin (m + 1)) (v : Fin (n + 1)) (z : Tiling.Plane),
      z ∈ gridCell G u v → (z ∈ D ↔ M u v = true)) :
    QuadrantGermOccupancy D (sharedGridAnchor G i j) r (gridQuadAt M i j) := by
  intro qre qim z hzball hzq
  have hzcell := shared_quadrant_cell G i j _hr hleft hright hbelow habove
    qre qim z hzball hzq
  have hmem := hcell (if qre then i.succ else i.castSucc)
    (if qim then j.succ else j.castSucc) z hzcell
  cases qre <;> cases qim <;>
    simpa [quadValue, gridQuadAt] using hmem

private theorem approachesQuadrant_anchor
    {a : Tiling.Plane} {r : ℝ} (hr : 0 < r) (qre qim : Bool) :
    ApproachesQuadrant a r qre qim a := by
  intro ε hε
  let s : ℝ := min (ε / 4) (r / 4)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsε : 2 * s < ε := by
    dsimp [s]
    have hmin : min (ε / 4) (r / 4) ≤ ε / 4 := min_le_left _ _
    nlinarith
  have hsr : 2 * s < r := by
    dsimp [s]
    have hmin : min (ε / 4) (r / 4) ≤ r / 4 := min_le_right _ _
    nlinarith
  let y : Tiling.Plane :=
    a + (if qre then (s : Tiling.Plane) else -(s : Tiling.Plane))
  let z : Tiling.Plane :=
    y + (if qim then (s : Tiling.Plane) * Complex.I
      else -((s : Tiling.Plane) * Complex.I))
  have hzy : dist z y = s := by
    rw [Complex.dist_eq]
    dsimp [z]
    by_cases hq : qim = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        Complex.norm_I]
    · have hq' : qim = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs,
        Complex.norm_I]
  have hya : dist y a = s := by
    rw [Complex.dist_eq]
    dsimp [y]
    by_cases hq : qre = true
    · simp [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
    · have hq' : qre = false := Bool.eq_false_of_not_eq_true hq
      simp [hq', Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball]
    calc
      dist z a ≤ dist z y + dist y a := dist_triangle z y a
      _ = 2 * s := by rw [hzy, hya]; ring
      _ < r := hsr
  · dsimp [quadrantAtBool, z, y]
    by_cases hqre : qre = true <;> by_cases hqim : qim = true
    · simp [hqre, hqim, hs]
    · have hqim' : qim = false := Bool.eq_false_of_not_eq_true hqim
      simp [hqre, hqim', hs]
    · have hqre' : qre = false := Bool.eq_false_of_not_eq_true hqre
      simp [hqre', hqim, hs]
    · have hqre' : qre = false := Bool.eq_false_of_not_eq_true hqre
      have hqim' : qim = false := Bool.eq_false_of_not_eq_true hqim
      simp [hqre', hqim', hs]
  · calc
      dist z a ≤ dist z y + dist y a := dist_triangle z y a
      _ = 2 * s := by rw [hzy, hya]; ring
      _ < ε := hsε

private theorem nonstraightQuadrantGerm_frontier
    {D : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r) (q : BooleanQuad) (hnon : nonstraightQuad q)
    (hoccupies : QuadrantGermOccupancy D a r q) :
    a ∈ frontier D := by
  obtain ⟨hImDiff, hReDiff⟩ := nonstraightQuad_has_both_axis_changes q hnon
  rcases hImDiff with hup | hdown
  · have hf := frontier_of_opposite_quadrant_germs q hoccupies
      false true true true (approachesQuadrant_anchor hr false true)
      (approachesQuadrant_anchor hr true true) (by
        simpa [quadValue] using hup)
    exact hf
  · have hf := frontier_of_opposite_quadrant_germs q hoccupies
      false false true false (approachesQuadrant_anchor hr false false)
      (approachesQuadrant_anchor hr true false) (by
        simpa [quadValue] using hdown)
    exact hf

private theorem sharedGrid_nonstraight_cell_properVertex
    {m n : ℕ} {D : Set Tiling.Plane}
    (G : FullLineCoordinateGrid (m + 1) (n + 1))
    (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i : Fin m) (j : Fin n) {r : ℝ}
    (hr : 0 < r)
    (hleft : r < G.xLevel i.succ.castSucc - G.xLevel i.castSucc.castSucc)
    (hright : r < G.xLevel i.succ.succ - G.xLevel i.succ.castSucc)
    (hbelow : r < G.yLevel j.succ.castSucc - G.yLevel j.castSucc.castSucc)
    (habove : r < G.yLevel j.succ.succ - G.yLevel j.succ.castSucc)
    (hcell : ∀ (u : Fin (m + 1)) (v : Fin (n + 1)) (z : Tiling.Plane),
      z ∈ gridCell G u v → (z ∈ D ↔ M u v = true))
    (hnon : nonstraightQuad (gridQuadAt M i j)) :
    sharedGridAnchor G i j ∈ properVertices D := by
  have hocc := sharedGrid_quadrantGerm_of_cellValues G M i j hr
    hleft hright hbelow habove hcell
  have hfront := nonstraightQuadrantGerm_frontier hr (gridQuadAt M i j)
    hnon hocc
  exact properVertex_of_nonstraightQuadrantGerm' hfront hr
    (gridQuadAt M i j) hnon hocc

private def gridRectangleQuad {m n : ℕ}
    (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (iL iR : Fin (m + 1)) (jB jT : Fin (n + 1)) : BooleanQuad where
  northwest := M iL jT
  northeast := M iR jT
  southwest := M iL jB
  southeast := M iR jB

private theorem straight_gridQuad_iff
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (i : Fin m) (j : Fin n) :
    straightQuad (gridQuadAt M i j) ↔ straightQuad (quadAt M i j) := by
  change ((M i.castSucc j.succ = M i.succ j.succ ∧
      M i.castSucc j.castSucc = M i.succ j.castSucc) ∨
    (M i.castSucc j.succ = M i.castSucc j.castSucc ∧
      M i.succ j.succ = M i.succ j.castSucc)) ↔
    ((M i.castSucc j.castSucc = M i.castSucc j.succ ∧
      M i.succ j.castSucc = M i.succ j.succ) ∨
    (M i.castSucc j.castSucc = M i.succ j.castSucc ∧
      M i.castSucc j.succ = M i.succ j.succ))
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩
    · exact Or.inl ⟨h.2, h.1⟩

private theorem straight_gridRectangle_iff
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (iL iR : Fin (m + 1)) (jB jT : Fin (n + 1)) :
    straightQuad (gridRectangleQuad M iL iR jB jT) ↔
      straightQuad (rectangleQuad M iL iR jB jT) := by
  change ((M iL jT = M iR jT ∧ M iL jB = M iR jB) ∨
      (M iL jT = M iL jB ∧ M iR jT = M iR jB)) ↔
    ((M iL jB = M iL jT ∧ M iR jB = M iR jT) ∨
      (M iL jB = M iR jB ∧ M iL jT = M iR jT))
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩
    · exact Or.inl ⟨h.2, h.1⟩

private theorem exists_nonstraight_gridQuad_of_nonstraight_rectangle
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (iL iR : Fin (m + 1)) (jB jT : Fin (n + 1))
    (hrectangle : nonstraightQuad (gridRectangleQuad M iL iR jB jT)) :
    ∃ i : Fin m, ∃ j : Fin n, nonstraightQuad (gridQuadAt M i j) := by
  have hrect' : nonstraightQuad (rectangleQuad M iL iR jB jT) := by
    intro hs
    exact hrectangle ((straight_gridRectangle_iff M iL iR jB jT).mpr hs)
  obtain ⟨i, j, hbad⟩ :=
    exists_nonstraight_intervening_of_nonstraight_rectangle
      M iL iR jB jT hrect'
  exact ⟨i, j, by
    intro hs
    exact hbad ((straight_gridQuad_iff M i j).mp hs)⟩

private noncomputable def finsetLevel {k : ℕ} (F : Finset ℝ) (hF : F.card = k)
    (i : Fin k) : ℝ :=
  ((F.orderIsoOfFin hF i : F) : ℝ)

private theorem finsetLevel_strict {k : ℕ} (F : Finset ℝ)
    (hF : F.card = k) : StrictMono (finsetLevel F hF) := by
  intro i j hij
  exact (F.orderIsoOfFin hF).lt_iff_lt.mpr hij

private noncomputable def finsetCoordinateGrid {m n : ℕ}
    (Fx Fy : Finset ℝ) (hx : Fx.card = m + 2) (hy : Fy.card = n + 2) :
    FullLineCoordinateGrid (m + 1) (n + 1) :=
  { xLevel := fun i => finsetLevel Fx rfl (Fin.cast hx.symm i)
    yLevel := fun i => finsetLevel Fy rfl (Fin.cast hy.symm i)
    x_strict := by
      intro i j hij
      apply finsetLevel_strict Fx rfl
      simpa using hij
    y_strict := by
      intro i j hij
      apply finsetLevel_strict Fy rfl
      simpa using hij }

private theorem grid_compare_mem_level
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    {i : Fin (m + 1)} {j : Fin (n + 1)} {z w : Tiling.Plane} {a : ℝ}
    (hz : z ∈ gridCell G i j) (hw : w ∈ gridCell G i j)
    (ha : ∃ k : Fin (m + 2), G.xLevel k = a) :
    (z.re < a ↔ w.re < a) := by
  obtain ⟨k, rfl⟩ := ha
  rcases lt_or_ge k i.succ with hleft | hright
  · have hleft' : k ≤ i.castSucc := (Fin.le_castSucc_iff).2 hleft
    have hzlt : z.re < G.xLevel k → False := by
      intro h
      exact (not_lt_of_ge (G.x_strict.monotone hleft')) (lt_trans hz.1 h)
    have hwlt : w.re < G.xLevel k → False := by
      intro h
      exact (not_lt_of_ge (G.x_strict.monotone hleft')) (lt_trans hw.1 h)
    constructor <;> intro h
    · exact False.elim (hzlt h)
    · exact False.elim (hwlt h)
  · have hright' : i.succ ≤ k := hright
    have hzlt : z.re < G.xLevel k :=
      lt_of_lt_of_le hz.2.1 (G.x_strict.monotone hright')
    have hwlt : w.re < G.xLevel k :=
      lt_of_lt_of_le hw.2.1 (G.x_strict.monotone hright')
    constructor
    · intro _
      exact hwlt
    · intro _
      exact hzlt

private theorem gridCell_off_level
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    {i : Fin (m + 1)} {j : Fin (n + 1)} {z : Tiling.Plane} {a : ℝ}
    (hz : z ∈ gridCell G i j)
    (ha : ∃ k : Fin (m + 2), G.xLevel k = a) : z.re ≠ a := by
  obtain ⟨k, rfl⟩ := ha
  rcases lt_or_ge k i.succ with hleft | hright
  · have hleft' : k ≤ i.castSucc := (Fin.le_castSucc_iff).2 hleft
    exact ne_of_gt (lt_of_le_of_lt (G.x_strict.monotone hleft') hz.1)
  · exact ne_of_lt (lt_of_lt_of_le hz.2.1 (G.x_strict.monotone hright))

private theorem grid_compare_mem_level_y
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    {i : Fin (m + 1)} {j : Fin (n + 1)} {z w : Tiling.Plane} {a : ℝ}
    (hz : z ∈ gridCell G i j) (hw : w ∈ gridCell G i j)
    (ha : ∃ k : Fin (n + 2), G.yLevel k = a) :
    (z.im < a ↔ w.im < a) := by
  obtain ⟨k, rfl⟩ := ha
  rcases lt_or_ge k j.succ with hleft | hright
  · have hleft' : k ≤ j.castSucc := (Fin.le_castSucc_iff).2 hleft
    have hzlt : z.im < G.yLevel k → False := by
      intro h
      exact (not_lt_of_ge (G.y_strict.monotone hleft')) (lt_trans hz.2.2.1 h)
    have hwlt : w.im < G.yLevel k → False := by
      intro h
      exact (not_lt_of_ge (G.y_strict.monotone hleft')) (lt_trans hw.2.2.1 h)
    constructor <;> intro h
    · exact False.elim (hzlt h)
    · exact False.elim (hwlt h)
  · have hzlt : z.im < G.yLevel k :=
      lt_of_lt_of_le hz.2.2.2 (G.y_strict.monotone hright)
    have hwlt : w.im < G.yLevel k :=
      lt_of_lt_of_le hw.2.2.2 (G.y_strict.monotone hright)
    constructor
    · intro _
      exact hwlt
    · intro _
      exact hzlt

private theorem gridCell_off_level_y
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    {i : Fin (m + 1)} {j : Fin (n + 1)} {z : Tiling.Plane} {a : ℝ}
    (hz : z ∈ gridCell G i j)
    (ha : ∃ k : Fin (n + 2), G.yLevel k = a) : z.im ≠ a := by
  obtain ⟨k, rfl⟩ := ha
  rcases lt_or_ge k j.succ with hleft | hright
  · have hleft' : k ≤ j.castSucc := (Fin.le_castSucc_iff).2 hleft
    exact ne_of_gt (lt_of_le_of_lt (G.y_strict.monotone hleft') hz.2.2.1)
  · exact ne_of_lt (lt_of_lt_of_le hz.2.2.2 (G.y_strict.monotone hright))

private def translatedVertexRealLevels (K : Region) (Q : Finset Tiling.Plane) : Finset ℝ := by
  classical
  exact Q.biUnion (fun t => K.vertexFinset.image (fun v => (t + v).re))

private def translatedVertexImagLevels (K : Region) (Q : Finset Tiling.Plane) : Finset ℝ := by
  classical
  exact Q.biUnion (fun t => K.vertexFinset.image (fun v => (t + v).im))

private theorem translated_real_level_mem
    {K : Region} {Q : Finset Tiling.Plane} {t v : Tiling.Plane}
    (ht : t ∈ Q) (hv : v ∈ K.vertices) :
    (t + v).re ∈ translatedVertexRealLevels K Q := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ht, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨v, ?_, rfl⟩
  change v ∈ (K.vertexFinset : Set Tiling.Plane)
  rw [K.coe_vertexFinset]
  exact hv

private theorem translated_imag_level_mem
    {K : Region} {Q : Finset Tiling.Plane} {t v : Tiling.Plane}
    (ht : t ∈ Q) (hv : v ∈ K.vertices) :
    (t + v).im ∈ translatedVertexImagLevels K Q := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨t, ht, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨v, ?_, rfl⟩
  change v ∈ (K.vertexFinset : Set Tiling.Plane)
  rw [K.coe_vertexFinset]
  exact hv

private theorem regularSupport_cell_constancy_of_translated_levels
    {K : Region} {Q : Finset Tiling.Plane}
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    {i : Fin (m + 1)} {j : Fin (n + 1)}
    {x y : Tiling.Plane}
    (hx : x ∈ gridCell G i j) (hy : y ∈ gridCell G i j)
    (hreal : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (m + 2), G.xLevel k = (t + v).re)
    (himag : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (n + 2), G.yLevel k = (t + v).im) :
    (x ∈ regularSupport K (Q : Set Tiling.Plane) ↔
      y ∈ regularSupport K (Q : Set Tiling.Plane)) := by
  have hconst : ∀ {z w : Tiling.Plane}, z ∈ gridCell G i j →
      w ∈ gridCell G i j → ∀ t ∈ Q,
      OffVertexCoordinateGrid K (z - t) ∧
        OffVertexCoordinateGrid K (w - t) ∧
        SameVertexGridCell K (z - t) (w - t) := by
    intro z w hz hw t ht
    have hoff (z : Tiling.Plane) (hz : z ∈ gridCell G i j) :
        OffVertexCoordinateGrid K (z - t) := by
      intro v hv
      constructor
      · intro heq
        have heq' : z.re = (t + v).re := by
          change z.re - t.re = v.re at heq
          simpa [Complex.add_re, add_comm] using sub_eq_iff_eq_add.mp heq
        exact gridCell_off_level G hz (hreal t ht v hv) heq'
      · intro heq
        have heq' : z.im = (t + v).im := by
          change z.im - t.im = v.im at heq
          simpa [Complex.add_im, add_comm] using sub_eq_iff_eq_add.mp heq
        exact gridCell_off_level_y G hz (himag t ht v hv) heq'
    have hzo := hoff z hz
    have hwo := hoff w hw
    have hs : SameVertexGridCell K (z - t) (w - t) := by
      constructor
      · intro v hv
        have hcmp := grid_compare_mem_level G hz hw (hreal t ht v hv)
        change z.re - t.re < v.re ↔ w.re - t.re < v.re
        simpa [sub_lt_iff_lt_add, add_comm] using hcmp
      · intro v hv
        have hcmp := grid_compare_mem_level_y G hz hw (himag t ht v hv)
        change z.im - t.im < v.im ↔ w.im - t.im < v.im
        simpa [sub_lt_iff_lt_add, add_comm] using hcmp
    exact ⟨hzo, hwo, hs⟩
  have hopen : IsOpen (gridCell G i j) := by
    dsimp [gridCell]
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter <| by
        exact (isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const))
  have hU : ∀ z ∈ gridCell G i j,
      z ∈ openUnion K (Q : Set Tiling.Plane) ↔
        x ∈ openUnion K (Q : Set Tiling.Plane) := by
    intro z hz
    exact (finite_openUnion_cell_constancy Q
      (x := z) (y := x) (by
        intro t ht
        exact hconst hz hx t ht)).trans Iff.rfl
  have hreg : ∀ z ∈ gridCell G i j,
      z ∈ interior (closure (openUnion K (Q : Set Tiling.Plane))) ↔
        z ∈ openUnion K (Q : Set Tiling.Plane) := by
    intro z hz
    by_cases hzu : x ∈ openUnion K (Q : Set Tiling.Plane)
    · constructor
      · intro _
        exact (hU z hz).mpr hzu
      · intro hzU
        apply (mem_interior_iff_mem_nhds).2
        exact Filter.mem_of_superset (hopen.mem_nhds hz) (fun w hw ↦
          subset_closure ((hU w hw).mpr hzu))
    · have hsub : openUnion K (Q : Set Tiling.Plane) ⊆
          (gridCell G i j)ᶜ := by
        intro w hw hcell
        exact hzu ((hU w hcell).mp hw)
      have hcl : closure (openUnion K (Q : Set Tiling.Plane)) ⊆
          (gridCell G i j)ᶜ := closure_minimal hsub (isClosed_compl_iff.mpr hopen)
      constructor
      · intro hzreg
        exact False.elim ((hcl (interior_subset hzreg)) hz)
      · intro hzU
        exact False.elim (hzu ((hU z hz).mp hzU))
  exact (hreg x hx).trans ((hU y hy).symm.trans (hreg y hy).symm)

private noncomputable def finsetLevelPred (L : Finset ℝ) (hcard : 1 ≤ L.card)
    (i : Fin (L.card - 1 + 1)) : ℝ :=
  finsetLevel L rfl (Fin.cast (Nat.sub_add_cancel hcard) i)

private theorem exists_finset_bracket
    (L : Finset ℝ) (hL : L.Nonempty) {x : ℝ}
    (hxlow : L.min' hL < x) (hxhigh : x < L.max' hL)
    (hxnot : x ∉ L) :
    ∃ i : Fin (L.card - 1),
      finsetLevelPred L (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hL)) i.castSucc < x ∧
        x < finsetLevelPred L (Nat.succ_le_iff.mpr (Finset.card_pos.mpr hL)) i.succ := by
  classical
  let below : Finset ℝ := L.filter (fun a ↦ a < x)
  let above : Finset ℝ := L.filter (fun a ↦ x < a)
  have hbelow : below.Nonempty := by
    refine ⟨L.min' hL, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.min'_mem L hL, hxlow⟩
  have habove : above.Nonempty := by
    refine ⟨L.max' hL, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.max'_mem L hL, hxhigh⟩
  let a : ℝ := below.max' hbelow
  let b : ℝ := above.min' habove
  have haL : a ∈ L := by
    exact (Finset.mem_filter.mp (Finset.max'_mem below hbelow)).1
  have haX : a < x := by
    exact (Finset.mem_filter.mp (Finset.max'_mem below hbelow)).2
  have hbL : b ∈ L := by
    exact (Finset.mem_filter.mp (Finset.min'_mem above habove)).1
  have hbX : x < b := by
    exact (Finset.mem_filter.mp (Finset.min'_mem above habove)).2
  let e := L.orderIsoOfFin rfl
  let p : Fin L.card := e.symm ⟨a, haL⟩
  let q : Fin L.card := e.symm ⟨b, hbL⟩
  have hpq : p < q := by
    apply (e.symm).lt_iff_lt.mpr
    exact haX.trans hbX
  have hpval : p.val < L.card - 1 := by
    have hpqval : p.val < q.val := (Fin.lt_def).mp hpq
    have hqval : q.val < L.card := q.isLt
    omega
  let i : Fin (L.card - 1) := ⟨p.val, hpval⟩
  let hcard : 1 ≤ L.card := Nat.succ_le_iff.mpr (Finset.card_pos.mpr hL)
  have hip : Fin.cast (Nat.sub_add_cancel hcard) i.castSucc = p := by
    ext
    rfl
  by_cases hsucc : q.val = p.val + 1
  · have hiq : Fin.cast (Nat.sub_add_cancel hcard) i.succ = q := by
      apply Fin.ext
      simp [i, hsucc]
    refine ⟨i, ?_, ?_⟩
    · simpa [finsetLevelPred, finsetLevel, e, hip, p, a, hcard] using haX
    · have hbx : x < b := hbX
      simpa [finsetLevelPred, finsetLevel, e, hiq, q, b, hcard] using hbx
  · have hqgt : p.val + 1 < q.val := by omega
    let r : Fin L.card := ⟨p.val + 1, by omega⟩
    have hpr : p < r := by
      apply Fin.lt_def.mpr
      simp [r]
    have hrq : r < q := by
      apply Fin.lt_def.mpr
      simp [r]
      omega
    let c : ℝ := e r
    have hcL : c ∈ L := (e r).property
    have hca : a < c := by
      have h := (e.lt_iff_lt.mpr hpr)
      have hreal : (e p : ℝ) < (e r : ℝ) := by simpa using h
      simpa [c, p, a] using hreal
    have hcb : c < b := by
      have h := (e.lt_iff_lt.mpr hrq)
      have hreal : (e r : ℝ) < (e q : ℝ) := by simpa using h
      simpa [c, q, b] using hreal
    have hcne : c ≠ x := by
      intro hcx
      apply hxnot
      simpa [c, hcx] using hcL
    rcases lt_or_gt_of_ne hcne with hcx | hxc
    · have hcmem : c ∈ below := Finset.mem_filter.mpr ⟨hcL, hcx⟩
      have hle := Finset.le_max' below c hcmem
      exact False.elim ((not_le_of_gt hca) (by simpa [a] using hle))
    · have hcmem : c ∈ above := Finset.mem_filter.mpr ⟨hcL, hxc⟩
      have hle := Finset.min'_le above c hcmem
      exact False.elim ((not_lt_of_ge (by simpa [b] using hle)) hcb)

private theorem ordered_corner_cells_of_nonstraight
    {m n : ℕ} (G : FullLineCoordinateGrid (m + 1) (n + 1))
    (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (iL iR : Fin (m + 1)) (jB jT : Fin (n + 1))
    {pSW pSE pNW pNE : Tiling.Plane}
    (hSW : pSW ∈ gridCell G iL jB)
    (hSE : pSE ∈ gridCell G iR jB)
    (hNW : pNW ∈ gridCell G iL jT)
    (hNE : pNE ∈ gridCell G iR jT)
    (hx : pSW.re < pSE.re) (hy : pSW.im < pNW.im)
    (hnon : nonstraightQuad (gridRectangleQuad M iL iR jB jT)) :
    iL < iR ∧ jB < jT := by
  have hile : iL ≤ iR := by
    by_contra hnot
    have hir : iR < iL := lt_of_not_ge hnot
    have hstep : iR.succ ≤ iL.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hlevel : G.xLevel iR.succ ≤ G.xLevel iL.castSucc :=
      G.x_strict.monotone hstep
    have hbad : pSE.re < pSW.re :=
      lt_trans (lt_of_lt_of_le hSE.2.1 hlevel) hSW.1
    linarith
  have hineq : iL ≠ iR := by
    intro heq
    subst iR
    exact hnon (Or.inl ⟨rfl, rfl⟩)
  have hjle : jB ≤ jT := by
    by_contra hnot
    have hjr : jT < jB := lt_of_not_ge hnot
    have hstep : jT.succ ≤ jB.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hlevel : G.yLevel jT.succ ≤ G.yLevel jB.castSucc :=
      G.y_strict.monotone hstep
    have hbad : pNW.im < pSW.im :=
      lt_trans hNW.2.2.2 (lt_of_le_of_lt hlevel hSW.2.2.1)
    linarith
  have hjneq : jB ≠ jT := by
    intro heq
    subst jT
    exact hnon (Or.inr ⟨rfl, rfl⟩)
  exact ⟨lt_of_le_of_ne hile hineq, lt_of_le_of_ne hjle hjneq⟩

private theorem exists_finset_grid_bracket_card
    (F : Finset ℝ) {m : ℕ} (hF : F.card = m + 2) {x : ℝ}
    (hFne : F.Nonempty) (hlo : F.min' hFne < x)
    (hhi : x < F.max' hFne) (hnot : x ∉ F) :
    ∃ i : Fin (m + 1),
      (finsetCoordinateGrid F F hF hF).xLevel i.castSucc < x ∧
        x < (finsetCoordinateGrid F F hF hF).xLevel i.succ := by
  obtain ⟨i₀, hi₀, hi₁⟩ := exists_finset_bracket F hFne hlo hhi hnot
  have hidx : F.card - 1 = m + 1 := by omega
  let i : Fin (m + 1) := Fin.cast hidx i₀
  have hcast0 :
      Fin.cast hF.symm i.castSucc =
        Fin.cast (Nat.sub_add_cancel (Finset.card_pos.mpr hFne)) i₀.castSucc := by
    apply Fin.ext
    rfl
  have hcast1 :
      Fin.cast hF.symm i.succ =
        Fin.cast (Nat.sub_add_cancel (Finset.card_pos.mpr hFne)) i₀.succ := by
    apply Fin.ext
    rfl
  refine ⟨i, ?_, ?_⟩
  · simpa [finsetCoordinateGrid, finsetLevelPred, finsetLevel, i, hidx, hcast0] using hi₀
  · simpa [finsetCoordinateGrid, finsetLevelPred, finsetLevel, i, hidx, hcast1] using hi₁

private theorem imaginaryEmbedding_dist_zero (y : ℝ) :
    dist (imaginaryEmbedding y) 0 = |y| := by
  simp [imaginaryEmbedding, dist_eq_norm, Complex.norm_def]

private theorem exists_outer_level_augmentation
    (F : Finset ℝ) {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ m : ℕ, ∃ F' : Finset ℝ,
      F' = insert lo (insert hi F) ∧ F'.card = m + 2 ∧
        F ⊆ F' ∧ lo ∈ F' ∧ hi ∈ F' := by
  let F' : Finset ℝ := insert lo (insert hi F)
  have hsub : ({lo, hi} : Finset ℝ) ⊆ F' := by
    intro x hx
    have hx' : x = lo ∨ x = hi := by simpa using hx
    simp only [F', Finset.mem_insert]
    rcases hx' with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hcard2 : 2 ≤ F'.card := by
    have hcard := Finset.card_le_card hsub
    simpa [F', hlohi.ne] using hcard
  refine ⟨F'.card - 2, F', rfl, ?_, ?_, ?_, ?_⟩
  · omega
  · intro x hx
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hx)
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

private theorem exists_nonstraight_gridQuad_between
    {m n : ℕ} (M : Fin (m + 1) → Fin (n + 1) → Bool)
    (iL iR : Fin (m + 1)) (jB jT : Fin (n + 1))
    (hi : iL < iR) (hj : jB < jT)
    (hnon : nonstraightQuad (gridRectangleQuad M iL iR jB jT)) :
    ∃ i : Fin m, ∃ j : Fin n,
      iL.val ≤ i.val ∧ i.val < iR.val ∧
      jB.val ≤ j.val ∧ j.val < jT.val ∧
      nonstraightQuad (gridQuadAt M i j) := by
  let di : ℕ := iR.val - iL.val
  let dj : ℕ := jT.val - jB.val
  have hdi : 0 < di := by dsimp [di]; omega
  have hdj : 0 < dj := by dsimp [dj]; omega
  let Msub : Fin (di + 1) → Fin (dj + 1) → Bool := fun a b ↦
    M ⟨iL.val + a.val, by dsimp [di]; omega⟩
      ⟨jB.val + b.val, by dsimp [dj]; omega⟩
  have hrect : nonstraightQuad
      (gridRectangleQuad Msub 0 (Fin.last di) 0 (Fin.last dj)) := by
    intro hs
    apply hnon
    change ((Msub 0 (Fin.last dj) = Msub (Fin.last di) (Fin.last dj) ∧
        Msub 0 0 = Msub (Fin.last di) 0) ∨
      (Msub 0 (Fin.last dj) = Msub 0 0 ∧
        Msub (Fin.last di) (Fin.last dj) = Msub (Fin.last di) 0)) at hs
    change ((M iL jT = M iR jT ∧ M iL jB = M iR jB) ∨
      (M iL jT = M iL jB ∧ M iR jT = M iR jB))
    have e₁ : Msub 0 (Fin.last dj) = M iL jT := by
      dsimp [Msub, di, dj]; congr 2; omega
    have e₂ : Msub (Fin.last di) (Fin.last dj) = M iR jT := by
      dsimp [Msub]; congr 2 <;> dsimp [di, dj] <;> try omega
    have e₃ : Msub 0 0 = M iL jB := by
      dsimp [Msub]
    have e₄ : Msub (Fin.last di) 0 = M iR jB := by
      dsimp [Msub, di, dj]; congr 2; omega
    rw [e₁, e₂, e₃, e₄] at hs
    exact hs
  obtain ⟨a, b, hab⟩ := exists_nonstraight_gridQuad_of_nonstraight_rectangle
    Msub 0 (Fin.last di) 0 (Fin.last dj) hrect
  let i : Fin m := ⟨iL.val + a.val, by omega⟩
  let j : Fin n := ⟨jB.val + b.val, by omega⟩
  refine ⟨i, j, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [i]; omega
  · dsimp [i, di] at *; omega
  · dsimp [j]; omega
  · dsimp [j, dj] at *; omega
  · unfold nonstraightQuad at hab ⊢
    unfold straightQuad at hab ⊢
    simp only [gridQuadAt] at hab ⊢
    change ¬ ((Msub a.castSucc b.succ = Msub a.succ b.succ ∧
      Msub a.castSucc b.castSucc = Msub a.succ b.castSucc) ∨
      (Msub a.castSucc b.succ = Msub a.castSucc b.castSucc ∧
        Msub a.succ b.succ = Msub a.succ b.castSucc)) at hab
    have e₁ : Msub a.castSucc b.succ = M i.castSucc j.succ := by
      dsimp [Msub, i, j]; congr 2
    have e₂ : Msub a.succ b.succ = M i.succ j.succ := by
      dsimp [Msub, i, j]; congr 2
    have e₃ : Msub a.castSucc b.castSucc = M i.castSucc j.castSucc := by
      dsimp [Msub, i, j]
    have e₄ : Msub a.succ b.castSucc = M i.succ j.castSucc := by
      dsimp [Msub, i, j]; congr 2
    rw [e₁, e₂, e₃, e₄] at hab
    exact hab

open Classical in
private theorem concrete_finiteArrangement_properVertex
    {K : Region} (Q : Finset Tiling.Plane)
    {m n : ℕ} (Fx Fy : Finset ℝ)
    (hFx : Fx.card = m + 2) (hFy : Fy.card = n + 2)
    (hFxne : Fx.Nonempty) (hFyne : Fy.Nonempty)
    (xL xR yB yT : ℝ)
    (hxord : xL < xR) (hyord : yB < yT)
    (hxLlow : Fx.min' hFxne < xL) (hxLhigh : xL < Fx.max' hFxne)
    (hxRlow : Fx.min' hFxne < xR) (hxRhigh : xR < Fx.max' hFxne)
    (hyBlow : Fy.min' hFyne < yB) (hyBhigh : yB < Fy.max' hFyne)
    (hyTlow : Fy.min' hFyne < yT) (hyThigh : yT < Fy.max' hFyne)
    (hxLnot : xL ∉ Fx) (hxRnot : xR ∉ Fx)
    (hyBnot : yB ∉ Fy) (hyTnot : yT ∉ Fy)
    (hreal : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (m + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).xLevel k = (t + v).re)
    (himag : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (n + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).yLevel k = (t + v).im)
    (hnon : nonstraightQuad {
      northwest := decide (((xL : Tiling.Plane) + (yT : Tiling.Plane) * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      northeast := decide (((xR : Tiling.Plane) + (yT : Tiling.Plane) * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      southwest := decide (((xL : Tiling.Plane) + (yB : Tiling.Plane) * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      southeast := decide (((xR : Tiling.Plane) + (yB : Tiling.Plane) * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane)) }) :
    ∃ a : Tiling.Plane,
      a ∈ properVertices (regularSupport K (Q : Set Tiling.Plane)) ∧
      xL < a.re ∧ a.re < xR ∧ yB < a.im ∧ a.im < yT := by
  let G := finsetCoordinateGrid Fx Fy hFx hFy
  let D : Set Tiling.Plane := regularSupport K (Q : Set Tiling.Plane)
  let pSW : Tiling.Plane := (xL : Tiling.Plane) + (yB : Tiling.Plane) * Complex.I
  let pSE : Tiling.Plane := (xR : Tiling.Plane) + (yB : Tiling.Plane) * Complex.I
  let pNW : Tiling.Plane := (xL : Tiling.Plane) + (yT : Tiling.Plane) * Complex.I
  let pNE : Tiling.Plane := (xR : Tiling.Plane) + (yT : Tiling.Plane) * Complex.I
  obtain ⟨iL, hiL₀, hiL₁⟩ := exists_finset_grid_bracket_card Fx hFx
    hFxne hxLlow hxLhigh hxLnot
  obtain ⟨iR, hiR₀, hiR₁⟩ := exists_finset_grid_bracket_card Fx hFx
    hFxne hxRlow hxRhigh hxRnot
  obtain ⟨jB, hjB₀, hjB₁⟩ := exists_finset_grid_bracket_card Fy hFy
    hFyne hyBlow hyBhigh hyBnot
  obtain ⟨jT, hjT₀, hjT₁⟩ := exists_finset_grid_bracket_card Fy hFy
    hFyne hyTlow hyThigh hyTnot
  have hcell : ∀ (u : Fin (m + 1)) (v : Fin (n + 1)) (z : Tiling.Plane),
      z ∈ gridCell G u v → (z ∈ D ↔ arrangementMatrix D G u v = true) := by
    intro u v z hz
    have hreg := regularSupport_cell_constancy_of_translated_levels
      (K := K) (Q := Q) G hz (gridAnchor_mem_cell G u v) hreal himag
    simpa [D, arrangementMatrix, arrangementCellValue] using hreg
  have hSW : pSW ∈ gridCell G iL jB := by
    simpa [pSW, G, gridCell, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] using ⟨hiL₀, hiL₁, hjB₀, hjB₁⟩
  have hSE : pSE ∈ gridCell G iR jB := by
    simpa [pSE, G, gridCell, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] using ⟨hiR₀, hiR₁, hjB₀, hjB₁⟩
  have hNW : pNW ∈ gridCell G iL jT := by
    simpa [pNW, G, gridCell, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] using ⟨hiL₀, hiL₁, hjT₀, hjT₁⟩
  have hNE : pNE ∈ gridCell G iR jT := by
    simpa [pNE, G, gridCell, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im] using ⟨hiR₀, hiR₁, hjT₀, hjT₁⟩
  let M : Fin (m + 1) → Fin (n + 1) → Bool := arrangementMatrix D G
  have hnon' : nonstraightQuad (gridRectangleQuad M iL iR jB jT) := by
    have hdec (p : Tiling.Plane) (u : Fin (m + 1)) (v : Fin (n + 1))
        (hp : p ∈ gridCell G u v) :
        decide (p ∈ D) = M u v := by
      have hm := hcell u v p hp
      by_cases hq : M u v = true
      · have hp' : p ∈ D := hm.mpr hq
        simp [hp', hq]
      · have hp' : p ∉ D := by
          intro hpD
          exact hq (hm.mp hpD)
        simp [hp', hq]
    have hSW' := hdec pSW iL jB hSW
    have hSE' := hdec pSE iR jB hSE
    have hNW' := hdec pNW iL jT hNW
    have hNE' := hdec pNE iR jT hNE
    simpa [gridRectangleQuad, M, pSW, pSE, pNW, pNE, D,
      hSW', hSE', hNW', hNE'] using hnon
  have hord := ordered_corner_cells_of_nonstraight G M iL iR jB jT
    hSW hSE hNW hNE (by simpa [pSW, pSE] using hxord)
    (by simpa [pSW, pNW] using hyord) hnon'
  have hradius : ∀ (i : Fin m) (j : Fin n), ∃ r : ℝ, 0 < r ∧
      r < G.xLevel i.succ.castSucc - G.xLevel i.castSucc.castSucc ∧
      r < G.xLevel i.succ.succ - G.xLevel i.succ.castSucc ∧
      r < G.yLevel j.succ.castSucc - G.yLevel j.castSucc.castSucc ∧
      r < G.yLevel j.succ.succ - G.yLevel j.succ.castSucc := by
    intro i j
    let a := G.xLevel i.succ.castSucc - G.xLevel i.castSucc.castSucc
    let b := G.xLevel i.succ.succ - G.xLevel i.succ.castSucc
    let c := G.yLevel j.succ.castSucc - G.yLevel j.castSucc.castSucc
    let d := G.yLevel j.succ.succ - G.yLevel j.succ.castSucc
    have ha : 0 < a := by dsimp [a]; exact sub_pos.mpr (G.x_strict (Fin.castSucc_lt_succ))
    have hb : 0 < b := by
      dsimp [b]
      have h : i.succ.castSucc < i.succ.succ := Fin.castSucc_lt_succ
      exact sub_pos.mpr (G.x_strict h)
    have hc : 0 < c := by dsimp [c]; exact sub_pos.mpr (G.y_strict (Fin.castSucc_lt_succ))
    have hd : 0 < d := by
      dsimp [d]
      have h : j.succ.castSucc < j.succ.succ := Fin.castSucc_lt_succ
      exact sub_pos.mpr (G.y_strict h)
    have hmina : min (min a b) (min c d) ≤ a :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hminb : min (min a b) (min c d) ≤ b :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    have hminc : min (min a b) (min c d) ≤ c :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hmind : min (min a b) (min c d) ≤ d :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    refine ⟨min (min a b) (min c d) / 2, ?_, ?_, ?_, ?_, ?_⟩
    · positivity
    all_goals nlinarith [ha, hb, hc, hd, hmina, hminb, hminc, hmind]
  obtain ⟨i, j, hiL, hiR, hjB, hjT, hbad⟩ :=
    exists_nonstraight_gridQuad_between M iL iR jB jT
      hord.1 hord.2 hnon'
  obtain ⟨r, hr, hleft, hright, hbelow, habove⟩ := hradius i j
  have hproper := sharedGrid_nonstraight_cell_properVertex G M i j hr
    hleft hright hbelow habove hcell hbad
  have hxL₁ : xL < G.xLevel iL.succ := by
    simpa [G, finsetCoordinateGrid] using hiL₁
  have hxR₀ : G.xLevel iR.castSucc < xR := by
    simpa [G, finsetCoordinateGrid] using hiR₀
  have hyB₁ : yB < G.yLevel jB.succ := by
    simpa [G, finsetCoordinateGrid] using hjB₁
  have hyT₀ : G.yLevel jT.castSucc < yT := by
    simpa [G, finsetCoordinateGrid] using hjT₀
  have hxleft : G.xLevel iL.succ ≤ G.xLevel i.succ.castSucc := by
    apply G.x_strict.monotone
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hxright : G.xLevel i.succ.castSucc ≤ G.xLevel iR.castSucc := by
    apply G.x_strict.monotone
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  have hyleft : G.yLevel jB.succ ≤ G.yLevel j.succ.castSucc := by
    apply G.y_strict.monotone
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hyright : G.yLevel j.succ.castSucc ≤ G.yLevel jT.castSucc := by
    apply G.y_strict.monotone
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega
  refine ⟨sharedGridAnchor G i j, by simpa [D] using hproper, ?_, ?_, ?_, ?_⟩
  · simpa [sharedGridAnchor] using lt_of_lt_of_le hxL₁ hxleft
  · simpa [sharedGridAnchor] using lt_of_le_of_lt hxright hxR₀
  · simpa [sharedGridAnchor] using lt_of_lt_of_le hyB₁ hyleft
  · simpa [sharedGridAnchor] using lt_of_le_of_lt hyright hyT₀

/-!
# T06 finite padded-patch stability

This scratch block isolates the metric part of the proper-vertex persistence
argument.  A sample with a positive distance margin from a translated tile
boundary keeps its membership when the scalar centre is replaced by a close
matched centre.  A bounded tile support also puts every tile meeting a compact
sample box into one padded centre window.

The remaining geometric input is deliberately explicit: a proper limit vertex
must supply four quadrant samples with these margins simultaneously for the
finite family of relevant translated supports.
-/






open Bornology Filter Function MeasureTheory Set Topology




open Tiling.AxisParallel

private def MembershipMargin
    (U : Set Tiling.Plane) (s x : Tiling.Plane) (rho : ℝ) : Prop :=
  (x - s ∈ U ∧ rho < Metric.infDist (x - s) Uᶜ) ∨
    (x - s ∉ U ∧ rho < Metric.infDist (x - s) U)

private theorem dist_sub_center
    (x s t : Tiling.Plane) :
    dist (x - t) (x - s) = dist t s := by
  convert dist_add_left x (-t) (-s) using 1 <;> simp [sub_eq_add_neg]

private theorem mem_vadd_iff_sub_mem
    {U : Set Tiling.Plane} {s x : Tiling.Plane} :
    x ∈ s +ᵥ U ↔ x - s ∈ U := by
  constructor
  · rintro ⟨u, hu, hus⟩
    change s + u = x at hus
    have hu' : u = x - s := by
      rw [← hus]
      abel
    simpa only [hu'] using hu
  · intro hu
    refine ⟨x - s, hu, ?_⟩
    change s + (x - s) = x
    abel

private theorem membership_translate_stable
    {U : Set Tiling.Plane} {s t x : Tiling.Plane} {rho : ℝ}
    (hmargin : MembershipMargin U s x rho)
    (hshift : dist s t < rho) :
    x ∈ t +ᵥ U ↔ x ∈ s +ᵥ U := by
  rcases hmargin with ⟨hxs, hmargin⟩ | ⟨hxs, hmargin⟩
  · have hdist : dist (x - t) (x - s) < Metric.infDist (x - s) Uᶜ := by
      rw [dist_sub_center]
      exact (dist_comm t s ▸ hshift).trans hmargin
    have hxt : x - t ∈ U :=
      Metric.ball_infDist_compl_subset (s := U) hdist
    constructor
    · intro _
      exact mem_vadd_iff_sub_mem.mpr hxs
    · intro _
      exact mem_vadd_iff_sub_mem.mpr hxt
  · have hdist : dist (x - t) (x - s) < Metric.infDist (x - s) U := by
      rw [dist_sub_center]
      exact (dist_comm t s ▸ hshift).trans hmargin
    have hxt : x - t ∉ U := by
      intro hxt
      have hnot : x - t ∈ Uᶜ := by
        apply Metric.ball_infDist_compl_subset (x := x - s) (s := Uᶜ)
        simpa only [Metric.mem_ball, compl_compl, dist_comm] using hdist
      exact hnot hxt
    constructor
    · intro h
      exfalso
      apply hxt
      exact mem_vadd_iff_sub_mem.mp h
    · intro h
      exfalso
      apply hxs
      exact mem_vadd_iff_sub_mem.mp h

private theorem relevant_center_bound
    {K : Region} {Q : Set Tiling.Plane} {s c : Tiling.Plane} {R rho : ℝ}
    (hK : ∀ z ∈ K.support, dist z 0 ≤ R)
    (hs : ((s +ᵥ K.support) ∩ Q).Nonempty)
    (hc : ∀ z ∈ Q, dist z c ≤ rho) :
    dist s c ≤ R + rho := by
  obtain ⟨x, hx⟩ := hs
  rcases hx with ⟨hxK, hxQ⟩
  have hxK' : x - s ∈ K.support := mem_vadd_iff_sub_mem.mp hxK
  have hdistK : dist (x - s) 0 ≤ R := hK (x - s) hxK'
  have hxs : dist s x ≤ R := by
    have hdist : dist (x - s) 0 = dist s x := by
      simpa [dist_comm] using (dist_sub_right s x s)
    rw [hdist] at hdistK
    exact hdistK
  exact (dist_triangle s x c).trans (add_le_add hxs (hc x hxQ))

/- A finite family of off-frontier samples has one common positive metric
   margin.  This is the exact finite-arrangement interface needed after the
   local quadrant samples have been selected. -/
private theorem finite_membership_margin
    {ι : Type*} [Finite ι]
    (hne : Nonempty ι)
    (U : ι → Set Tiling.Plane)
    (hU : ∀ i, (U i).Nonempty ∧ (U i)ᶜ.Nonempty)
    {x : Tiling.Plane}
    (hx : ∀ i, x ∉ frontier (U i)) :
    ∃ rho > 0, ∀ i,
      (x ∈ U i ∧ rho < Metric.infDist x (U i)ᶜ) ∨
        (x ∉ U i ∧ rho < Metric.infDist x (U i)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let d : ι → ℝ := fun i ↦
    if x ∈ U i then Metric.infDist x (U i)ᶜ else Metric.infDist x (U i)
  have hd : ∀ i, 0 < d i := by
    intro i
    by_cases hxi : x ∈ U i
    · have hxiInterior : x ∈ interior (U i) := by
        have hmem : x ∈ U i \ frontier (U i) := ⟨hxi, hx i⟩
        simpa only [self_sdiff_frontier] using hmem
      have hxnot : x ∉ closure (U i)ᶜ := by
        rw [closure_compl]
        change ¬¬x ∈ interior (U i)
        exact not_not_intro hxiInterior
      have hpos : 0 < Metric.infDist x (U i)ᶜ :=
        (Metric.infDist_pos_iff_notMem_closure (hU i).2).mp hxnot
      simpa only [d, hxi, ↓reduceIte] using hpos
    · have hxcompl : x ∈ (U i)ᶜ := hxi
      have hfrontCompl : x ∉ frontier ((U i)ᶜ) := by
        simpa only [frontier_compl] using hx i
      have hxcomplInterior : x ∈ interior ((U i)ᶜ) := by
        have hmem : x ∈ (U i)ᶜ \ frontier ((U i)ᶜ) :=
          ⟨hxcompl, hfrontCompl⟩
        simpa only [self_sdiff_frontier] using hmem
      have hxnot : x ∉ closure (U i) := by
        simpa only [interior_compl, mem_compl_iff] using hxcomplInterior
      have hpos : 0 < Metric.infDist x (U i) :=
        (Metric.infDist_pos_iff_notMem_closure (hU i).1).mp hxnot
      simpa only [d, hxi, ↓reduceIte] using hpos
  let vals : Finset ℝ := Finset.univ.image d
  have hvals : vals.Nonempty := by
    change (Finset.univ.image d).Nonempty
    exact Finset.image_nonempty.mpr ⟨hne.some, Finset.mem_univ _⟩
  let m : ℝ := vals.min' hvals
  have hm : 0 < m := by
    have hj : m ∈ vals := by
      exact Finset.min'_mem vals hvals
    obtain ⟨i, hi, hdi⟩ := Finset.mem_image.mp hj
    simpa only [hdi, m] using hd i
  refine ⟨m / 2, div_pos hm (by norm_num), ?_⟩
  intro i
  have hmi : m ≤ d i := by
    exact Finset.min'_le vals (d i)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hhalf : m / 2 < d i := by linarith
  by_cases hxi : x ∈ U i
  · left
    exact ⟨hxi, by simpa only [d, hxi, ↓reduceIte] using hhalf⟩
  · right
    exact ⟨hxi, by simpa only [d, hxi, ↓reduceIte] using hhalf⟩

private inductive SampleQuadrant
  | southwest | southeast | northwest | northeast
  deriving DecidableEq

private def sampleQuadrantAt (q : SampleQuadrant) (a : Tiling.Plane) :
    Set Tiling.Plane :=
  match q with
  | .southwest => {z | z.re < a.re ∧ z.im < a.im}
  | .southeast => {z | a.re < z.re ∧ z.im < a.im}
  | .northwest => {z | z.re < a.re ∧ a.im < z.im}
  | .northeast => {z | a.re < z.re ∧ a.im < z.im}

private theorem sampleQuadrantAt_convex (q : SampleQuadrant) (a : Tiling.Plane) :
    Convex ℝ (sampleQuadrantAt q a) := by
  intro x hx y hy α β hα hβ hαβ
  have hlt : ∀ {u v c : ℝ}, u < c → v < c → α * u + β * v < c := by
    intro u v c hu hv
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [hα0, hβ1, hv]
    · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hu' := mul_lt_mul_of_pos_left hu hαpos
      have hv' := mul_le_mul_of_nonneg_left (le_of_lt hv) hβ
      have hsum : α * c + β * c = c := by
        calc
          α * c + β * c = (α + β) * c := by ring
          _ = 1 * c := by rw [hαβ]
          _ = c := by ring
      nlinarith [hαβ, hsum]
  have hgt : ∀ {u v c : ℝ}, c < u → c < v → c < α * u + β * v := by
    intro u v c hu hv
    by_cases hα0 : α = 0
    · have hβ1 : β = 1 := by linarith
      simp [hα0, hβ1, hv]
    · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hu' := mul_lt_mul_of_pos_left hu hαpos
      have hv' := mul_le_mul_of_nonneg_left (le_of_lt hv) hβ
      have hsum : α * c + β * c = c := by
        calc
          α * c + β * c = (α + β) * c := by ring
          _ = 1 * c := by rw [hαβ]
          _ = c := by ring
      nlinarith [hαβ, hsum]
  cases q
  · dsimp [sampleQuadrantAt] at hx ⊢
    exact ⟨by simpa using hlt hx.1 hy.1, by simpa using hlt hx.2 hy.2⟩
  · dsimp [sampleQuadrantAt] at hx ⊢
    exact ⟨by simpa using hgt hx.1 hy.1, by simpa using hlt hx.2 hy.2⟩
  · dsimp [sampleQuadrantAt] at hx ⊢
    exact ⟨by simpa using hlt hx.1 hy.1, by simpa using hgt hx.2 hy.2⟩
  · dsimp [sampleQuadrantAt] at hx ⊢
    exact ⟨by simpa using hgt hx.1 hy.1, by simpa using hgt hx.2 hy.2⟩

private theorem sampleQuadrant_ball_nonempty
    {a : Tiling.Plane} {r : ℝ} (hr : 0 < r) (q : SampleQuadrant) :
    (Metric.ball a r ∩ sampleQuadrantAt q a).Nonempty := by
  let d : ℝ := r / 4
  have hdist (sgnRe sgnIm : ℝ) (hre : sgnRe = 1 ∨ sgnRe = -1)
      (him : sgnIm = 1 ∨ sgnIm = -1) :
      dist a (a + sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) < r := by
    rw [dist_eq_norm, Complex.norm_def, Real.sqrt_lt' hr]
    have hnorm : Complex.normSq
        (sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) = 2 * d ^ 2 := by
      rcases hre with rfl | rfl <;> rcases him with rfl | rfl <;>
        norm_num [Complex.normSq_apply] <;> ring_nf
    rw [show a - (a + sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) =
      -(sgnRe * (d : ℂ) + sgnIm * (d : ℂ) * Complex.I) by ring,
      Complex.normSq_neg, hnorm]
    dsimp [d]
    nlinarith
  cases q
  · refine ⟨a - (d : ℂ) - (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a - (d : ℂ) - (d : ℂ) * Complex.I =
          a + (-1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist (-1) (-1) (Or.inr rfl) (Or.inr rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a + (d : ℂ) - (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a + (d : ℂ) - (d : ℂ) * Complex.I =
          a + (1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist 1 (-1) (Or.inl rfl) (Or.inr rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a - (d : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a - (d : ℂ) + (d : ℂ) * Complex.I =
          a + (-1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num; ring
      rw [heq]
      exact hdist (-1) 1 (Or.inr rfl) (Or.inl rfl)
    · constructor <;> simp [d, hr]
  · refine ⟨a + (d : ℂ) + (d : ℂ) * Complex.I, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have heq : a + (d : ℂ) + (d : ℂ) * Complex.I =
          a + (1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I := by
        norm_num
      rw [heq]
      exact hdist 1 1 (Or.inl rfl) (Or.inl rfl)
    · constructor <;> simp [d, hr]

private theorem sample_quadrant_mem_closure_of_weak
    (q : SampleQuadrant) (a x : Tiling.Plane) :
    (match q with
      | .southwest => x.re ≤ a.re ∧ x.im ≤ a.im
      | .southeast => a.re ≤ x.re ∧ x.im ≤ a.im
      | .northwest => x.re ≤ a.re ∧ a.im ≤ x.im
      | .northeast => a.re ≤ x.re ∧ a.im ≤ x.im) →
      x ∈ closure (sampleQuadrantAt q a) := by
  intro h
  apply Metric.mem_closure_iff.2
  intro ε hε
  obtain ⟨y, ⟨hyball, hyq⟩⟩ := sampleQuadrant_ball_nonempty hε q
  refine ⟨y, ?_, ?_⟩
  · cases q <;> dsimp [sampleQuadrantAt] at hyq ⊢
    · exact ⟨lt_of_lt_of_le hyq.1 h.1, lt_of_lt_of_le hyq.2 h.2⟩
    · exact ⟨lt_of_le_of_lt h.1 hyq.1, lt_of_lt_of_le hyq.2 h.2⟩
    · exact ⟨lt_of_lt_of_le hyq.1 h.1, lt_of_le_of_lt h.2 hyq.2⟩
    · exact ⟨lt_of_le_of_lt h.1 hyq.1, lt_of_le_of_lt h.2 hyq.2⟩
  · simpa [Metric.mem_ball, dist_comm] using hyball

private theorem exists_sample_quadrant_closure (a y : Tiling.Plane) :
    ∃ q : SampleQuadrant, y ∈ closure (sampleQuadrantAt q a) := by
  by_cases hre : y.re ≤ a.re
  · by_cases him : y.im ≤ a.im
    · exact ⟨.southwest,
        sample_quadrant_mem_closure_of_weak .southwest a y ⟨hre, him⟩⟩
    · exact ⟨.northwest,
        sample_quadrant_mem_closure_of_weak .northwest a y
          ⟨hre, le_of_not_ge him⟩⟩
  · by_cases him : y.im ≤ a.im
    · exact ⟨.southeast,
        sample_quadrant_mem_closure_of_weak .southeast a y
          ⟨le_of_not_ge hre, him⟩⟩
    · exact ⟨.northeast,
        sample_quadrant_mem_closure_of_weak .northeast a y
          ⟨le_of_not_ge hre, le_of_not_ge him⟩⟩

private theorem all_quadrants_full_mem_interior
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hregular : interior (closure F) = F) (hr : 0 < r)
    (hfull : ∀ q : SampleQuadrant,
      Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F) :
    a ∈ interior F := by
  have hball : Metric.ball a (r / 2) ⊆ closure F := by
    intro z hz
    have hzball : z ∈ Metric.ball a r := by
      rw [Metric.mem_ball] at hz ⊢
      linarith
    by_cases hre : z.re ≤ a.re
    · by_cases him : z.im ≤ a.im
      · have hzq := sample_quadrant_mem_closure_of_weak .southwest a z ⟨hre, him⟩
        have hzqi := Metric.isOpen_ball.closure_inter ⟨hzq, hzball⟩
        exact closure_mono (hfull .southwest) (by
          simpa only [inter_comm] using hzqi)
      · have hzq := sample_quadrant_mem_closure_of_weak .northwest a z
          ⟨hre, le_of_not_ge him⟩
        have hzqi := Metric.isOpen_ball.closure_inter ⟨hzq, hzball⟩
        exact closure_mono (hfull .northwest) (by
          simpa only [inter_comm] using hzqi)
    · by_cases him : z.im ≤ a.im
      · have hzq := sample_quadrant_mem_closure_of_weak .southeast a z
          ⟨le_of_not_ge hre, him⟩
        have hzqi := Metric.isOpen_ball.closure_inter ⟨hzq, hzball⟩
        exact closure_mono (hfull .southeast) (by
          simpa only [inter_comm] using hzqi)
      · have hzq := sample_quadrant_mem_closure_of_weak .northeast a z
          ⟨le_of_not_ge hre, le_of_not_ge him⟩
        have hzqi := Metric.isOpen_ball.closure_inter ⟨hzq, hzball⟩
        exact closure_mono (hfull .northeast) (by
          simpa only [inter_comm] using hzqi)
  have hballint : Metric.ball a (r / 2) ⊆ interior (closure F) :=
    interior_maximal hball Metric.isOpen_ball
  have hballF : Metric.ball a (r / 2) ⊆ F := by
    simpa only [hregular] using hballint
  exact mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2
    ⟨r / 2, by linarith, hballF⟩)

private theorem all_quadrants_disjoint_not_mem_closure
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hr : 0 < r)
    (hdisj : ∀ q : SampleQuadrant,
      Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F) :
    a ∉ closure F := by
  intro ha
  obtain ⟨y, hyball, hyF⟩ := mem_closure_iff.1 ha
    (Metric.ball a (r / 2)) Metric.isOpen_ball (Metric.mem_ball_self (by linarith))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hopen y hyF
  have hymargin : 0 < r / 2 - dist y a := by
    have hyball' : dist y a < r / 2 := by
      simpa only [Metric.mem_ball] using hyball
    linarith
  let ρ := min δ (r / 2 - dist y a) / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact div_pos (lt_min hδ hymargin) (by norm_num)
  obtain ⟨q, hqcl⟩ := exists_sample_quadrant_closure a y
  have hqinter := Metric.isOpen_ball.closure_inter ⟨hqcl, Metric.mem_ball_self hρ⟩
  obtain ⟨z, hzball, hzqball⟩ := mem_closure_iff.1 hqinter
    (Metric.ball y ρ) Metric.isOpen_ball (Metric.mem_ball_self hρ)
  have hρδ : ρ ≤ δ := by
    dsimp [ρ]
    have hmin : 0 ≤ min δ (r / 2 - dist y a) :=
      le_min hδ.le hymargin.le
    exact (div_le_self hmin (by norm_num)).trans (min_le_left _ _)
  have hzF : z ∈ F := hδsub (Metric.ball_subset_ball hρδ hzball)
  have hza : z ∈ Metric.ball a r := by
    rw [Metric.mem_ball]
    calc
      dist z a ≤ dist z y + dist y a := dist_triangle _ _ _
      _ < ρ + dist y a := by linarith [Metric.mem_ball.1 hzball]
      _ < r := by
        have hρbound : ρ ≤ (r / 2 - dist y a) / 2 := by
          dsimp [ρ]
          exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num : (0 : ℝ) ≤ 2)
        linarith
  exact Set.disjoint_left.mp (hdisj q) ⟨hza, hzqball.1⟩ hzF

private theorem proper_vertex_not_constant_quadrants
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F) (hr : 0 < r)
    (hproper : a ∈ frontier F ∧ ¬BoundaryLocallyStraightAt F a)
    (hpattern :
      (∀ q : SampleQuadrant,
        Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F) ∨
      (∀ q : SampleQuadrant,
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F)) :
    False := by
  rcases hpattern with hfull | hdisj
  · have haF := all_quadrants_full_mem_interior hregular hr hfull
    exact Set.disjoint_left.1 disjoint_interior_frontier haF hproper.1
  · exact all_quadrants_disjoint_not_mem_closure hopen hr hdisj
      (frontier_subset_closure hproper.1)
private theorem sample_quadrant_constancy_one
    {D : Set Tiling.Plane} {a : Tiling.Plane} (q : SampleQuadrant)
    (hopen : IsOpen D)
    (hcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier D →
      z.re = a.re ∨ z.im = a.im) :
    ∃ r > 0,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ D ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) D) := by
  obtain ⟨r₀, hr₀, hcross₀⟩ := hcross
  let r := r₀ / 2
  have hr : 0 < r := by dsimp [r]; linarith
  let Q : Set Tiling.Plane := Metric.ball a r ∩ sampleQuadrantAt q a
  have hQopen : IsOpen Q := by
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
  have hQpre : IsPreconnected Q := by
    exact (convex_ball a r |>.inter (sampleQuadrantAt_convex q a)).isPreconnected
  let U : Set Tiling.Plane := D ∩ Q
  let V : Set Tiling.Plane := (closure D)ᶜ ∩ Q
  have hUopen : IsOpen U := hopen.inter hQopen
  have hVopen : IsOpen V := isClosed_closure.isOpen_compl.inter hQopen
  have hUVdisj : Disjoint U V := by
    apply Set.disjoint_left.2
    intro z hzU hzV
    exact hzV.1 (subset_closure hzU.1)
  have hQsub : Q ⊆ U ∪ V := by
    intro z hzQ
    by_cases hzD : z ∈ D
    · exact Or.inl ⟨hzD, hzQ⟩
    · right
      refine ⟨?_, hzQ⟩
      intro hzcl
      have hzfront : z ∈ frontier D := by
        change z ∈ closure D \ interior D
        exact ⟨hzcl, by simpa [hopen.interior_eq] using hzD⟩
      have hzaxis : z.re ≠ a.re ∧ z.im ≠ a.im := by
        cases q <;> dsimp [sampleQuadrantAt] at hzQ ⊢ <;>
          constructor <;> linarith [hzQ.2.1, hzQ.2.2]
      have hznear : z ∈ Metric.ball a r₀ :=
        Metric.ball_subset_ball (by dsimp [r]; linarith) hzQ.1
      obtain hzre | hzim := hcross₀ z hznear hzfront
      · exact hzaxis.1 hzre
      · exact hzaxis.2 hzim
  obtain hleft | hright := hQpre.subset_or_subset hUopen hVopen hUVdisj hQsub
  · refine ⟨r, hr, Or.inl ?_⟩
    exact fun z hz => (hleft hz).1
  · refine ⟨r, hr, Or.inr ?_⟩
    apply Set.disjoint_left.2
    intro z hzQ hzD
    exact (hright hzQ).1 (subset_closure hzD)

private theorem sample_quadrant_constancy
    {F : Set Tiling.Plane} {a : Tiling.Plane} (hopen : IsOpen F)
    (hcross : ∃ r > 0, ∀ z ∈ Metric.ball a r, z ∈ frontier F →
      z.re = a.re ∨ z.im = a.im) :
    ∃ r > 0, ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F) := by
  obtain ⟨r₀, hr₀, h₀⟩ := sample_quadrant_constancy_one .southwest hopen hcross
  obtain ⟨r₁, hr₁, h₁⟩ := sample_quadrant_constancy_one .southeast hopen hcross
  obtain ⟨r₂, hr₂, h₂⟩ := sample_quadrant_constancy_one .northwest hopen hcross
  obtain ⟨r₃, hr₃, h₃⟩ := sample_quadrant_constancy_one .northeast hopen hcross
  let r := min r₀ (min r₁ (min r₂ r₃))
  refine ⟨r, lt_min hr₀ (lt_min hr₁ (lt_min hr₂ hr₃)), ?_⟩
  have hr₀' : r ≤ r₀ := min_le_left _ _
  have hr₁' : r ≤ r₁ := (min_le_right r₀ _).trans (min_le_left _ _)
  have hr₂' : r ≤ r₂ := (min_le_right r₀ _).trans
    ((min_le_right r₁ _).trans (min_le_left _ _))
  have hr₃' : r ≤ r₃ := (min_le_right r₀ _).trans
    ((min_le_right r₁ _).trans (min_le_right _ _))
  intro q
  cases q
  · rcases h₀ with h | h
    · exact Or.inl (fun z hz => h
        (inter_subset_inter (Metric.ball_subset_ball hr₀') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left
        (inter_subset_inter (Metric.ball_subset_ball hr₀') Set.Subset.rfl))
  · rcases h₁ with h | h
    · exact Or.inl (fun z hz => h
        (inter_subset_inter (Metric.ball_subset_ball hr₁') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left
        (inter_subset_inter (Metric.ball_subset_ball hr₁') Set.Subset.rfl))
  · rcases h₂ with h | h
    · exact Or.inl (fun z hz => h
        (inter_subset_inter (Metric.ball_subset_ball hr₂') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left
        (inter_subset_inter (Metric.ball_subset_ball hr₂') Set.Subset.rfl))
  · rcases h₃ with h | h
    · exact Or.inl (fun z hz => h
        (inter_subset_inter (Metric.ball_subset_ball hr₃') Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left
        (inter_subset_inter (Metric.ball_subset_ball hr₃') Set.Subset.rfl))

private theorem regularSupport_sample_quadrant_constancy
    {K : Region} {Q : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Q)) (a : Tiling.Plane) :
    ∃ r > 0, ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ regularSupport K Q ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) (regularSupport K Q)) := by
  exact sample_quadrant_constancy
    (regularSupport_isRegularOpen K Q).1
    (regularSupport_localBoundaryCross hpacking a)

private theorem finite_coordinate_margin
    (L : Finset ℝ) {x : ℝ} (hx : x ∉ L) :
    ∃ rho > 0, ∀ y ∈ L, rho < dist x y := by
  classical
  by_cases hL : L.Nonempty
  · let vals : Finset ℝ := L.image (fun y ↦ dist x y)
    have hvals : vals.Nonempty := by
      change (L.image (fun y ↦ dist x y)).Nonempty
      exact Finset.image_nonempty.mpr hL
    let m : ℝ := vals.min' hvals
    have hm : 0 < m := by
      have hm_mem : m ∈ vals := Finset.min'_mem vals hvals
      obtain ⟨y, hy, hdist⟩ := Finset.mem_image.mp hm_mem
      have hyne : x ≠ y := by
        intro hxy
        apply hx
        simpa [hxy] using hy
      have hpos : 0 < dist x y := dist_pos.mpr hyne
      rw [← hdist]
      exact hpos
    refine ⟨m / 2, div_pos hm (by norm_num), ?_⟩
    intro y hy
    have hmy : m ≤ dist x y := by
      exact Finset.min'_le vals (dist x y)
        (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
    linarith
  · have hLempty : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    subst L
    exact ⟨1, zero_lt_one, by simp⟩

private def SampleOccupiesQuadrant (F : Set Tiling.Plane)
    (a : Tiling.Plane) (q : SampleQuadrant) : Prop :=
  ∃ r : ℝ, 0 < r ∧
    Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F

private theorem sample_localQuadrantOccupies_iff_full
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ} (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F)) (q : SampleQuadrant) :
    SampleOccupiesQuadrant F a q ↔ Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F := by
  constructor
  · intro hocc
    rcases hconst q with hfull | hdisj
    · exact hfull
    · rcases hocc with ⟨s, hs, hsub⟩
      exfalso
      obtain ⟨z, hz⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) q
      have hzsmall : z ∈ Metric.ball a r ∩ sampleQuadrantAt q a :=
        inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
          Set.Subset.rfl hz
      have hzocc : z ∈ F := hsub (inter_subset_inter
        (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl hz)
      exact Set.disjoint_left.mp hdisj hzsmall hzocc
  · intro hfull
    exact ⟨r, hr, hfull⟩

private theorem sample_localOffAxis_membership
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    {x : Tiling.Plane} (hx : x ∈ Metric.ball a r)
    (hxa : x.re ≠ a.re) (hya : x.im ≠ a.im) :
    ∃ q : SampleQuadrant, x ∈ sampleQuadrantAt q a ∧
      (x ∈ F ↔ SampleOccupiesQuadrant F a q) := by
  have hbranch (q : SampleQuadrant) (hq : x ∈ sampleQuadrantAt q a) :
      x ∈ F ↔ SampleOccupiesQuadrant F a q := by
    rcases hconst q with hfull | hdisj
    · constructor
      · intro _
        exact ⟨r, hr, hfull⟩
      · intro _
        exact hfull ⟨hx, hq⟩
    · constructor
      · intro hxf
        exact False.elim (Set.disjoint_left.mp hdisj ⟨hx, hq⟩ hxf)
      · intro hocc
        rcases hocc with ⟨s, hs, hsub⟩
        obtain ⟨z, hz⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) q
        have hzsmall : z ∈ Metric.ball a r ∩ sampleQuadrantAt q a :=
          inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
            Set.Subset.rfl hz
        have hzocc := hsub (inter_subset_inter
          (Metric.ball_subset_ball (min_le_right _ _)) Set.Subset.rfl hz)
        exact False.elim (Set.disjoint_left.mp hdisj hzsmall hzocc)
  cases lt_or_gt_of_ne hxa with
  | inl hre =>
    cases lt_or_gt_of_ne hya with
    | inl him => exact ⟨.southwest, by dsimp [sampleQuadrantAt]; exact ⟨hre, him⟩,
        hbranch .southwest ⟨hre, him⟩⟩
    | inr him => exact ⟨.northwest, by dsimp [sampleQuadrantAt]; exact ⟨hre, him⟩,
        hbranch .northwest ⟨hre, him⟩⟩
  | inr hre =>
    cases lt_or_gt_of_ne hya with
    | inl him => exact ⟨.southeast, by dsimp [sampleQuadrantAt]; exact ⟨hre, him⟩,
        hbranch .southeast ⟨hre, him⟩⟩
    | inr him => exact ⟨.northeast, by dsimp [sampleQuadrantAt]; exact ⟨hre, him⟩,
        hbranch .northeast ⟨hre, him⟩⟩

private theorem sample_axisRay_vertical
    {F : Set Tiling.Plane} {a x : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hxball : x ∈ Metric.ball a r) (hxeq : x.re = a.re)
    (hup : a.im < x.im) :
    x ∈ F ↔ SampleOccupiesQuadrant F a .northwest ∧
      SampleOccupiesQuadrant F a .northeast := by
  have hxball' : dist x a < r := by
    simpa only [Metric.mem_ball, dist_comm] using hxball
  have hmargin : 0 < r - dist x a := by linarith
  constructor
  · intro hxF
    constructor
    · rcases hconst .northwest with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min hδ₀ (by linarith)
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hδbound : δ ≤ (r - dist x a) / 2 := by
          dsimp [δ]
          exact min_le_right _ _
        have hxc : x ∈ closure (sampleQuadrantAt .northwest a) := by
          apply sample_quadrant_mem_closure_of_weak .northwest a x
          exact ⟨le_of_eq hxeq, le_of_lt hup⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by linarith [hδbound, hmargin]
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
    · rcases hconst .northeast with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min hδ₀ (by linarith)
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hδbound : δ ≤ (r - dist x a) / 2 := by
          dsimp [δ]
          exact min_le_right _ _
        have hxc : x ∈ closure (sampleQuadrantAt .northeast a) := by
          apply sample_quadrant_mem_closure_of_weak .northeast a x
          exact ⟨le_of_eq hxeq.symm, le_of_lt hup⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by linarith [hδbound, hmargin]
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
  · rintro ⟨hNW, hNE⟩
    have hNWsub := (sample_localQuadrantOccupies_iff_full hr hconst .northwest).1 hNW
    have hNEsub := (sample_localQuadrantOccupies_iff_full hr hconst .northeast).1 hNE
    let δ := min (r - dist x a) ((x.im - a.im) / 2) / 2
    have hδpos : 0 < δ := by
      have himargin : 0 < (x.im - a.im) / 2 := by linarith
      dsimp [δ]
      exact div_pos (lt_min hmargin himargin) (by norm_num)
    have hδbound : δ ≤ (r - dist x a) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδim : δ ≤ (x.im - a.im) / 4 := by
      dsimp [δ]
      calc
        min (r - dist x a) ((x.im - a.im) / 2) / 2 ≤
            ((x.im - a.im) / 2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ = (x.im - a.im) / 4 := by ring
    have hballcl : Metric.ball x δ ⊆ closure F := by
      intro z hz
      have hza : z ∈ Metric.ball a r := by
        rw [Metric.mem_ball]
        calc
          dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
          _ < δ + dist x a := by linarith [Metric.mem_ball.1 hz]
          _ < r := by linarith [hδbound, hmargin]
      have hzim : a.im < z.im := by
        have hi : |z.im - x.im| ≤ dist z x := by
          simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (z - x)
        have hi' : |z.im - x.im| < (x.im - a.im) / 2 :=
          lt_of_le_of_lt hi (lt_of_lt_of_le (Metric.mem_ball.1 hz)
            (by linarith [hδim]))
        rw [abs_lt] at hi'
        linarith
      by_cases hzr : z.re ≤ a.re
      · have hzweak : z ∈ closure (sampleQuadrantAt .northwest a) :=
          sample_quadrant_mem_closure_of_weak .northwest a z ⟨hzr, le_of_lt hzim⟩
        have hzq : z ∈ closure (Metric.ball a r ∩ sampleQuadrantAt .northwest a) := by
          simpa only [inter_comm] using
            Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hNWsub hzq
      · have hzweak : z ∈ closure (sampleQuadrantAt .northeast a) :=
          sample_quadrant_mem_closure_of_weak .northeast a z ⟨le_of_not_ge hzr, le_of_lt hzim⟩
        have hzq : z ∈ closure (Metric.ball a r ∩ sampleQuadrantAt .northeast a) := by
          simpa only [inter_comm] using
            Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hNEsub hzq
    rw [← hregular]
    exact mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨δ, hδpos, hballcl⟩)

private theorem sample_sample_axisRay_vertical_down
    {F : Set Tiling.Plane} {a x : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hxball : x ∈ Metric.ball a r) (hxeq : x.re = a.re)
    (hdown : x.im < a.im) :
    x ∈ F ↔ SampleOccupiesQuadrant F a .southwest ∧
      SampleOccupiesQuadrant F a .southeast := by
  have hxball' : dist x a < r := by simpa only [Metric.mem_ball, dist_comm] using hxball
  have hmargin : 0 < r - dist x a := by linarith
  constructor
  · intro hxF
    constructor
    · rcases hconst .southwest with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .southwest a x
          ⟨le_of_eq hxeq, le_of_lt hdown⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
    · rcases hconst .southeast with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .southeast a x
          ⟨le_of_eq hxeq.symm, le_of_lt hdown⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
  · rintro ⟨hSW, hSE⟩
    have hSWsub := (sample_localQuadrantOccupies_iff_full hr hconst .southwest).1 hSW
    have hSEsub := (sample_localQuadrantOccupies_iff_full hr hconst .southeast).1 hSE
    let δ := min (r - dist x a) ((a.im - x.im) / 2) / 2
    have hδpos : 0 < δ := by
      have hm : 0 < (a.im - x.im) / 2 := by linarith
      dsimp [δ]
      exact div_pos (lt_min hmargin hm) (by norm_num)
    have hδbound : δ ≤ (r - dist x a) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδim : δ ≤ (a.im - x.im) / 4 := by
      dsimp [δ]
      calc
        min (r - dist x a) ((a.im - x.im) / 2) / 2 ≤
            ((a.im - x.im) / 2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ = (a.im - x.im) / 4 := by ring
    have hballcl : Metric.ball x δ ⊆ closure F := by
      intro z hz
      have hza : z ∈ Metric.ball a r := by
        rw [Metric.mem_ball]
        calc
          dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
          _ < δ + dist x a := by linarith [Metric.mem_ball.1 hz]
          _ < r := by linarith [hδbound, hmargin]
      have hzim : z.im < a.im := by
        have hi : |z.im - x.im| ≤ dist z x := by
          simpa only [Complex.sub_im, dist_eq_norm] using Complex.abs_im_le_norm (z - x)
        have hi' : |z.im - x.im| < (a.im - x.im) / 2 :=
          lt_of_le_of_lt hi (lt_of_lt_of_le (Metric.mem_ball.1 hz) (by linarith [hδim]))
        rw [abs_lt] at hi'
        linarith
      by_cases hzr : z.re ≤ a.re
      · have hzweak := sample_quadrant_mem_closure_of_weak .southwest a z
          ⟨hzr, le_of_lt hzim⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hSWsub (by simpa only [inter_comm] using hzq)
      · have hzweak := sample_quadrant_mem_closure_of_weak .southeast a z
          ⟨le_of_not_ge hzr, le_of_lt hzim⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hSEsub (by simpa only [inter_comm] using hzq)
    rw [← hregular]
    exact mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨δ, hδpos, hballcl⟩)

private theorem horizontal_pattern_side_membership
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hSW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F)
    (hSE : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F)
    (hNW : Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F)
    (hNE : Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F)
    {z : Tiling.Plane} (hz : z ∈ Metric.ball a r) :
    (a.im < z.im → z ∈ F) ∧ (z.im < a.im → z ∉ F) := by
  have hNWocc : SampleOccupiesQuadrant F a .northwest :=
    (sample_localQuadrantOccupies_iff_full hr hconst .northwest).2 hNW
  have hNEocc : SampleOccupiesQuadrant F a .northeast :=
    (sample_localQuadrantOccupies_iff_full hr hconst .northeast).2 hNE
  have hSWocc : ¬SampleOccupiesQuadrant F a .southwest := by
    intro h
    obtain ⟨s, hs, hsub⟩ := h
    obtain ⟨x, hx⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) .southwest
    have hxsmall : x ∈ Metric.ball a r ∩ sampleQuadrantAt .southwest a :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
    have hxF : x ∈ F := hsub ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    exact Set.disjoint_left.mp hSW hxsmall hxF
  have hSEocc : ¬SampleOccupiesQuadrant F a .southeast := by
    intro h
    obtain ⟨s, hs, hsub⟩ := h
    obtain ⟨x, hx⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) .southeast
    have hxsmall : x ∈ Metric.ball a r ∩ sampleQuadrantAt .southeast a :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
    have hxF : x ∈ F := hsub ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    exact Set.disjoint_left.mp hSE hxsmall hxF
  constructor
  · intro hupper
    by_cases hzeq : z.re = a.re
    · exact (sample_axisRay_vertical hopen hregular hr hconst hz hzeq hupper).2
        ⟨hNWocc, hNEocc⟩
    · obtain ⟨q, hq, hmem⟩ := sample_localOffAxis_membership hr hconst hz hzeq
        (ne_of_gt hupper)
      cases q with
      | southwest =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | southeast =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | northwest => exact hmem.mpr hNWocc
      | northeast => exact hmem.mpr hNEocc
  · intro hlower
    by_cases hzeq : z.re = a.re
    · intro hF
      have hquad :=
        (sample_sample_axisRay_vertical_down hopen hregular hr hconst hz hzeq hlower).mp hF
      exact hSWocc hquad.1
    · obtain ⟨q, hq, hmem⟩ := sample_localOffAxis_membership hr hconst hz hzeq
        (ne_of_lt hlower)
      cases q with
      | southwest =>
          intro hF
          exact hSWocc (hmem.mp hF)
      | southeast =>
          intro hF
          exact hSEocc (hmem.mp hF)
      | northwest =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | northeast =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith

private theorem sample_axisRay_horizontal
    {F : Set Tiling.Plane} {a x : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hxball : x ∈ Metric.ball a r) (hyeq : x.im = a.im)
    (hright : a.re < x.re) :
    x ∈ F ↔ SampleOccupiesQuadrant F a .southeast ∧
      SampleOccupiesQuadrant F a .northeast := by
  have hxball' : dist x a < r := by simpa only [Metric.mem_ball, dist_comm] using hxball
  have hmargin : 0 < r - dist x a := by linarith
  constructor
  · intro hxF
    constructor
    · rcases hconst .southeast with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .southeast a x
          ⟨le_of_lt hright, le_of_eq hyeq⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
    · rcases hconst .northeast with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .northeast a x
          ⟨le_of_lt hright, le_of_eq hyeq.symm⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
  · rintro ⟨hSE, hNE⟩
    have hSEsub := (sample_localQuadrantOccupies_iff_full hr hconst .southeast).1 hSE
    have hNEsub := (sample_localQuadrantOccupies_iff_full hr hconst .northeast).1 hNE
    let δ := min (r - dist x a) ((x.re - a.re) / 2) / 2
    have hδpos : 0 < δ := by
      have hm : 0 < (x.re - a.re) / 2 := by linarith
      dsimp [δ]
      exact div_pos (lt_min hmargin hm) (by norm_num)
    have hδbound : δ ≤ (r - dist x a) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδre : δ ≤ (x.re - a.re) / 4 := by
      dsimp [δ]
      calc
        min (r - dist x a) ((x.re - a.re) / 2) / 2 ≤
            ((x.re - a.re) / 2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ = (x.re - a.re) / 4 := by ring
    have hballcl : Metric.ball x δ ⊆ closure F := by
      intro z hz
      have hza : z ∈ Metric.ball a r := by
        rw [Metric.mem_ball]
        calc
          dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
          _ < δ + dist x a := by linarith [Metric.mem_ball.1 hz]
          _ < r := by linarith [hδbound, hmargin]
      have hzr : a.re < z.re := by
        have hi : |z.re - x.re| ≤ dist z x := by
          simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (z - x)
        have hi' : |z.re - x.re| < (x.re - a.re) / 2 :=
          lt_of_le_of_lt hi (lt_of_lt_of_le (Metric.mem_ball.1 hz) (by linarith [hδre]))
        rw [abs_lt] at hi'
        linarith
      by_cases hzi : z.im ≤ a.im
      · have hzweak := sample_quadrant_mem_closure_of_weak .southeast a z
          ⟨le_of_lt hzr, hzi⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hSEsub (by simpa only [inter_comm] using hzq)
      · have hzweak := sample_quadrant_mem_closure_of_weak .northeast a z
          ⟨le_of_lt hzr, le_of_not_ge hzi⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hNEsub (by simpa only [inter_comm] using hzq)
    rw [← hregular]
    exact mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨δ, hδpos, hballcl⟩)

private theorem sample_sample_axisRay_horizontal_left
    {F : Set Tiling.Plane} {a x : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hxball : x ∈ Metric.ball a r) (hyeq : x.im = a.im)
    (hleft : x.re < a.re) :
    x ∈ F ↔ SampleOccupiesQuadrant F a .southwest ∧
      SampleOccupiesQuadrant F a .northwest := by
  have hxball' : dist x a < r := by simpa only [Metric.mem_ball, dist_comm] using hxball
  have hmargin : 0 < r - dist x a := by linarith
  constructor
  · intro hxF
    constructor
    · rcases hconst .southwest with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .southwest a x
          ⟨le_of_lt hleft, le_of_eq hyeq⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
    · rcases hconst .northwest with h | h
      · exact ⟨r, hr, h⟩
      · obtain ⟨δ₀, hδ₀, hδ₀sub⟩ := Metric.isOpen_iff.1 hopen x hxF
        let δ := min δ₀ ((r - dist x a) / 2)
        have hδ : 0 < δ := lt_min hδ₀ (by linarith [hmargin])
        have hδsub : Metric.ball x δ ⊆ F := fun y hy =>
          hδ₀sub (Metric.ball_subset_ball (min_le_left _ _) hy)
        have hxc := sample_quadrant_mem_closure_of_weak .northwest a x
          ⟨le_of_lt hleft, le_of_eq hyeq.symm⟩
        obtain ⟨y, hyball, hyq⟩ := mem_closure_iff.1 hxc
          (Metric.ball x δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
        have hya : y ∈ Metric.ball a r := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y x + dist x a := dist_triangle _ _ _
            _ < δ + dist x a := by linarith [Metric.mem_ball.1 hyball]
            _ < r := by
              have hb : δ ≤ (r - dist x a) / 2 := by dsimp [δ]; exact min_le_right _ _
              linarith
        exact False.elim (Set.disjoint_left.mp h ⟨hya, hyq⟩ (hδsub hyball))
  · rintro ⟨hSW, hNW⟩
    have hSWsub := (sample_localQuadrantOccupies_iff_full hr hconst .southwest).1 hSW
    have hNWsub := (sample_localQuadrantOccupies_iff_full hr hconst .northwest).1 hNW
    let δ := min (r - dist x a) ((a.re - x.re) / 2) / 2
    have hδpos : 0 < δ := by
      have hm : 0 < (a.re - x.re) / 2 := by linarith
      dsimp [δ]
      exact div_pos (lt_min hmargin hm) (by norm_num)
    have hδbound : δ ≤ (r - dist x a) / 2 := by
      dsimp [δ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hδre : δ ≤ (a.re - x.re) / 4 := by
      dsimp [δ]
      calc
        min (r - dist x a) ((a.re - x.re) / 2) / 2 ≤
            ((a.re - x.re) / 2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ = (a.re - x.re) / 4 := by ring
    have hballcl : Metric.ball x δ ⊆ closure F := by
      intro z hz
      have hza : z ∈ Metric.ball a r := by
        rw [Metric.mem_ball]
        calc
          dist z a ≤ dist z x + dist x a := dist_triangle _ _ _
          _ < δ + dist x a := by linarith [Metric.mem_ball.1 hz]
          _ < r := by linarith [hδbound, hmargin]
      have hzr : z.re < a.re := by
        have hi : |z.re - x.re| ≤ dist z x := by
          simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (z - x)
        have hi' : |z.re - x.re| < (a.re - x.re) / 2 :=
          lt_of_le_of_lt hi (lt_of_lt_of_le (Metric.mem_ball.1 hz) (by linarith [hδre]))
        rw [abs_lt] at hi'
        linarith
      by_cases hzi : z.im ≤ a.im
      · have hzweak := sample_quadrant_mem_closure_of_weak .southwest a z
          ⟨le_of_lt hzr, hzi⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hSWsub (by simpa only [inter_comm] using hzq)
      · have hzweak := sample_quadrant_mem_closure_of_weak .northwest a z
          ⟨le_of_lt hzr, le_of_not_ge hzi⟩
        have hzq := Metric.isOpen_ball.closure_inter ⟨hzweak, Metric.mem_ball.1 hza⟩
        exact closure_mono hNWsub (by simpa only [inter_comm] using hzq)
    rw [← hregular]
    exact mem_interior_iff_mem_nhds.2 (Metric.mem_nhds_iff.2 ⟨δ, hδpos, hballcl⟩)


private theorem vertical_pattern_side_membership
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hSW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F)
    (hNW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northwest a) F)
    (hSE : Metric.ball a r ∩ sampleQuadrantAt .southeast a ⊆ F)
    (hNE : Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F)
    {z : Tiling.Plane} (hz : z ∈ Metric.ball a r) :
    (a.re < z.re → z ∈ F) ∧ (z.re < a.re → z ∉ F) := by
  have hSEocc : SampleOccupiesQuadrant F a .southeast :=
    (sample_localQuadrantOccupies_iff_full hr hconst .southeast).2 hSE
  have hNEocc : SampleOccupiesQuadrant F a .northeast :=
    (sample_localQuadrantOccupies_iff_full hr hconst .northeast).2 hNE
  have hSWocc : ¬SampleOccupiesQuadrant F a .southwest := by
    intro h
    obtain ⟨s, hs, hsub⟩ := h
    obtain ⟨x, hx⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) .southwest
    have hxsmall : x ∈ Metric.ball a r ∩ sampleQuadrantAt .southwest a :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
    have hxF : x ∈ F := hsub ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    exact Set.disjoint_left.mp hSW hxsmall hxF
  have hNWocc : ¬SampleOccupiesQuadrant F a .northwest := by
    intro h
    obtain ⟨s, hs, hsub⟩ := h
    obtain ⟨x, hx⟩ := sampleQuadrant_ball_nonempty (lt_min hr hs) .northwest
    have hxsmall : x ∈ Metric.ball a r ∩ sampleQuadrantAt .northwest a :=
      ⟨Metric.ball_subset_ball (min_le_left _ _) hx.1, hx.2⟩
    have hxF : x ∈ F := hsub ⟨Metric.ball_subset_ball (min_le_right _ _) hx.1, hx.2⟩
    exact Set.disjoint_left.mp hNW hxsmall hxF
  constructor
  · intro hright
    by_cases hzeq : z.im = a.im
    · exact (sample_axisRay_horizontal hopen hregular hr hconst hz hzeq hright).2
        ⟨hSEocc, hNEocc⟩
    · obtain ⟨q, hq, hmem⟩ := sample_localOffAxis_membership hr hconst hz
        (ne_of_gt hright) hzeq
      cases q with
      | southwest =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | northwest =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | southeast => exact hmem.mpr hSEocc
      | northeast => exact hmem.mpr hNEocc
  · intro hleft
    by_cases hzeq : z.im = a.im
    · intro hF
      have hquad :=
        (sample_sample_axisRay_horizontal_left hopen hregular hr hconst hz hzeq hleft).mp hF
      exact hSWocc hquad.1
    · obtain ⟨q, hq, hmem⟩ := sample_localOffAxis_membership hr hconst hz
        (ne_of_lt hleft) hzeq
      cases q with
      | southwest => intro hF; exact hSWocc (hmem.mp hF)
      | northwest => intro hF; exact hNWocc (hmem.mp hF)
      | southeast =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith
      | northeast =>
          exfalso
          dsimp [sampleQuadrantAt] at hq
          linarith

private def horizontalSampleLine (a : Tiling.Plane) : AffineSubspace ℝ Tiling.Plane :=
  AffineSubspace.mk' a (Submodule.span ℝ ({(1 : Tiling.Plane)} : Set Tiling.Plane))

private theorem horizontalSampleLine_dim (a : Tiling.Plane) :
    Module.finrank ℝ (horizontalSampleLine a).direction = 1 := by
  rw [show (horizontalSampleLine a).direction =
      Submodule.span ℝ ({(1 : Tiling.Plane)} : Set Tiling.Plane) by
        simp [horizontalSampleLine]]
  exact finrank_span_singleton (by norm_num)

private theorem mem_horizontalSampleLine_iff (a z : Tiling.Plane) :
    z ∈ horizontalSampleLine a ↔ z.im = a.im := by
  constructor
  · intro hz
    rw [horizontalSampleLine, AffineSubspace.mem_mk'] at hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
    have him := congrArg Complex.im hc
    dsimp [vsub_eq_sub] at him
    norm_num at him
    linarith
  · intro hz
    rw [horizontalSampleLine, AffineSubspace.mem_mk']
    apply Submodule.mem_span_singleton.mpr
    refine ⟨z.re - a.re, ?_⟩
    apply Complex.ext <;> simp [vsub_eq_sub, hz]

private theorem horizontal_pattern_boundaryStraight
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hSW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F)
    (hSE : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F)
    (hNW : Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F)
    (hNE : Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F) :
    BoundaryLocallyStraightAt F a := by
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρr : ρ < r := by dsimp [ρ]; linarith
  have hside {z : Tiling.Plane} (hz : z ∈ Metric.ball a ρ) :
      (a.im < z.im → z ∈ F) ∧ (z.im < a.im → z ∉ F) :=
    horizontal_pattern_side_membership hopen hregular hr hconst hSW hSE hNW hNE
      (Metric.ball_subset_ball (le_of_lt hρr) hz)
  have hfrontier_line : ∀ z ∈ Metric.ball a ρ,
      (z ∈ frontier F ↔ z.im = a.im) := by
    intro z hz
    constructor
    · intro hzfront
      by_contra hzneq
      rcases lt_or_gt_of_ne hzneq with hzbelow | hzabove
      · have hzdist : dist z a < ρ := Metric.mem_ball.1 hz
        let δ : ℝ := min ((ρ - dist z a) / 2) ((a.im - z.im) / 2)
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min (by linarith) (by linarith)
        obtain ⟨y, hyball, hyF⟩ := mem_closure_iff.1
          (frontier_subset_closure hzfront) (Metric.ball z δ) Metric.isOpen_ball
            (Metric.mem_ball_self hδ)
        have hyA : y ∈ Metric.ball a ρ := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y z + dist z a := dist_triangle _ _ _
            _ < δ + dist z a := by linarith [Metric.mem_ball.1 hyball]
            _ < ρ := by
              dsimp [δ]
              have hmin := min_le_left ((ρ - dist z a) / 2) ((a.im - z.im) / 2)
              linarith
        have himle : |y.im - z.im| ≤ dist y z := by
          simpa [Complex.dist_eq] using Complex.abs_im_le_norm (y - z)
        have hybelow : y.im < a.im := by
          have hyz : dist y z < (a.im - z.im) / 2 := by
            have hmin : δ ≤ (a.im - z.im) / 2 := by
              dsimp [δ]
              exact min_le_right _ _
            exact lt_of_lt_of_le (Metric.mem_ball.1 hyball) hmin
          have hyzi : y.im < z.im + (a.im - z.im) / 2 := by
            linarith [le_abs_self (y.im - z.im), himle]
          linarith
        exact (hside hyA).2 hybelow hyF
      · have hzF := (hside hz).1 hzabove
        have hzint : z ∈ interior F := by simpa only [hopen.interior_eq] using hzF
        exact Set.disjoint_left.mp disjoint_interior_frontier hzint hzfront
    · intro hzline
      have hzcl : z ∈ closure F := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        by_cases hzre : z.re ≤ a.re
        · have hzweak := sample_quadrant_mem_closure_of_weak .northwest a z
            ⟨hzre, le_of_eq hzline.symm⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hε, hz⟩
          obtain ⟨y, hyε, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
          have hyF := hNW ⟨Metric.ball_subset_ball (le_of_lt hρr) hyq.2.2, hyq.1⟩
          exact ⟨y, hyF, by simpa [dist_comm] using hyε⟩
        · have hzweak := sample_quadrant_mem_closure_of_weak .northeast a z
            ⟨le_of_not_ge hzre, le_of_eq hzline.symm⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hε, hz⟩
          obtain ⟨y, hyε, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
          have hyF := hNE ⟨Metric.ball_subset_ball (le_of_lt hρr) hyq.2.2, hyq.1⟩
          exact ⟨y, hyF, by simpa [dist_comm] using hyε⟩
      have hznotF : z ∉ F := by
        intro hzF
        obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hopen z hzF
        by_cases hzre : z.re ≤ a.re
        · have hzweak := sample_quadrant_mem_closure_of_weak .southwest a z
            ⟨hzre, le_of_eq hzline⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hδ, hz⟩
          obtain ⟨y, hyδ, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
          exact (hside hyq.2.2).2 (by
            dsimp [sampleQuadrantAt] at hyq
            exact hyq.1.2) (hδsub hyδ)
        · have hzweak := sample_quadrant_mem_closure_of_weak .southeast a z
            ⟨le_of_not_ge hzre, le_of_eq hzline⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hδ, hz⟩
          obtain ⟨y, hyδ, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
          exact (hside hyq.2.2).2 (by
            dsimp [sampleQuadrantAt] at hyq
            exact hyq.1.2) (hδsub hyδ)
      rw [frontier]
      exact ⟨hzcl, by simpa only [hopen.interior_eq] using hznotF⟩
  refine ⟨horizontalSampleLine a, ?_, horizontalSampleLine_dim a, ?_⟩
  · exact by simp [horizontalSampleLine]
  · rw [Metric.eventually_nhds_iff]
    exact ⟨ρ, hρ, by
      intro z hz
      change z ∈ frontier F ↔ z ∈ horizontalSampleLine a
      rw [mem_horizontalSampleLine_iff]
      exact hfrontier_line z hz⟩

private def verticalSampleLine (a : Tiling.Plane) : AffineSubspace ℝ Tiling.Plane :=
  AffineSubspace.mk' a (Submodule.span ℝ ({(Complex.I : Tiling.Plane)} : Set Tiling.Plane))

private theorem verticalSampleLine_dim (a : Tiling.Plane) :
    Module.finrank ℝ (verticalSampleLine a).direction = 1 := by
  rw [show (verticalSampleLine a).direction =
      Submodule.span ℝ ({(Complex.I : Tiling.Plane)} : Set Tiling.Plane) by
        simp [verticalSampleLine]]
  exact finrank_span_singleton (by norm_num)

private theorem mem_verticalSampleLine_iff (a z : Tiling.Plane) :
    z ∈ verticalSampleLine a ↔ z.re = a.re := by
  constructor
  · intro hz
    rw [verticalSampleLine, AffineSubspace.mem_mk'] at hz
    rcases Submodule.mem_span_singleton.mp hz with ⟨c, hc⟩
    have hre := congrArg Complex.re hc
    dsimp [vsub_eq_sub] at hre
    norm_num at hre
    linarith
  · intro hz
    rw [verticalSampleLine, AffineSubspace.mem_mk']
    apply Submodule.mem_span_singleton.mpr
    refine ⟨z.im - a.im, ?_⟩
    apply Complex.ext <;> simp [vsub_eq_sub, hz]

private theorem vertical_pattern_boundaryStraight
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    (hSW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F)
    (hNW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northwest a) F)
    (hSE : Metric.ball a r ∩ sampleQuadrantAt .southeast a ⊆ F)
    (hNE : Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F) :
    BoundaryLocallyStraightAt F a := by
  let ρ : ℝ := r / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρr : ρ < r := by dsimp [ρ]; linarith
  have hside {z : Tiling.Plane} (hz : z ∈ Metric.ball a ρ) :
      (a.re < z.re → z ∈ F) ∧ (z.re < a.re → z ∉ F) :=
    vertical_pattern_side_membership hopen hregular hr hconst hSW hNW hSE hNE
      (Metric.ball_subset_ball (le_of_lt hρr) hz)
  have hfrontier_line : ∀ z ∈ Metric.ball a ρ,
      (z ∈ frontier F ↔ z.re = a.re) := by
    intro z hz
    constructor
    · intro hzfront
      by_contra hzneq
      rcases lt_or_gt_of_ne hzneq with hzleft | hzright
      · have hzdist : dist z a < ρ := Metric.mem_ball.1 hz
        let δ : ℝ := min ((ρ - dist z a) / 2) ((a.re - z.re) / 2)
        have hδ : 0 < δ := by
          dsimp [δ]
          exact lt_min (by linarith) (by linarith)
        obtain ⟨y, hyball, hyF⟩ := mem_closure_iff.1
          (frontier_subset_closure hzfront) (Metric.ball z δ) Metric.isOpen_ball
            (Metric.mem_ball_self hδ)
        have hyA : y ∈ Metric.ball a ρ := by
          rw [Metric.mem_ball]
          calc
            dist y a ≤ dist y z + dist z a := dist_triangle _ _ _
            _ < δ + dist z a := by linarith [Metric.mem_ball.1 hyball]
            _ < ρ := by
              dsimp [δ]
              have hmin := min_le_left ((ρ - dist z a) / 2) ((a.re - z.re) / 2)
              linarith
        have hrel : |y.re - z.re| ≤ dist y z := by
          simpa [Complex.dist_eq] using Complex.abs_re_le_norm (y - z)
        have hyleft : y.re < a.re := by
          have hyz : dist y z < (a.re - z.re) / 2 := by
            have hmin : δ ≤ (a.re - z.re) / 2 := by
              dsimp [δ]
              exact min_le_right _ _
            exact lt_of_lt_of_le (Metric.mem_ball.1 hyball) hmin
          have hyzi : y.re < z.re + (a.re - z.re) / 2 := by
            linarith [le_abs_self (y.re - z.re), hrel]
          linarith
        exact (hside hyA).2 hyleft hyF
      · have hzF := (hside hz).1 hzright
        have hzint : z ∈ interior F := by simpa only [hopen.interior_eq] using hzF
        exact Set.disjoint_left.mp disjoint_interior_frontier hzint hzfront
    · intro hzline
      have hzcl : z ∈ closure F := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        by_cases hzim : z.im ≤ a.im
        · have hzweak := sample_quadrant_mem_closure_of_weak .southeast a z
            ⟨le_of_eq hzline.symm, hzim⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hε, hz⟩
          obtain ⟨y, hyε, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
          have hyF := hSE ⟨Metric.ball_subset_ball (le_of_lt hρr) hyq.2.2, hyq.1⟩
          exact ⟨y, hyF, by simpa [dist_comm] using hyε⟩
        · have hzweak := sample_quadrant_mem_closure_of_weak .northeast a z
            ⟨le_of_eq hzline.symm, le_of_not_ge hzim⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hε, hz⟩
          obtain ⟨y, hyε, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
          have hyF := hNE ⟨Metric.ball_subset_ball (le_of_lt hρr) hyq.2.2, hyq.1⟩
          exact ⟨y, hyF, by simpa [dist_comm] using hyε⟩
      have hznotF : z ∉ F := by
        intro hzF
        obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hopen z hzF
        by_cases hzim : z.im ≤ a.im
        · have hzweak := sample_quadrant_mem_closure_of_weak .southwest a z
            ⟨le_of_eq hzline, hzim⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hδ, hz⟩
          obtain ⟨y, hyδ, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
          exact (hside hyq.2.2).2 (by
            dsimp [sampleQuadrantAt] at hyq
            exact hyq.1.1) (hδsub hyδ)
        · have hzweak := sample_quadrant_mem_closure_of_weak .northwest a z
            ⟨le_of_eq hzline, le_of_not_ge hzim⟩
          have hzq := (Metric.isOpen_ball.inter Metric.isOpen_ball).closure_inter
            ⟨hzweak, Metric.mem_ball_self hδ, hz⟩
          obtain ⟨y, hyδ, hyq⟩ := mem_closure_iff.1 hzq
            (Metric.ball z δ) Metric.isOpen_ball (Metric.mem_ball_self hδ)
          exact (hside hyq.2.2).2 (by
            dsimp [sampleQuadrantAt] at hyq
            exact hyq.1.1) (hδsub hyδ)
      rw [frontier]
      exact ⟨hzcl, by simpa only [hopen.interior_eq] using hznotF⟩
  refine ⟨verticalSampleLine a, ?_, verticalSampleLine_dim a, ?_⟩
  · exact by simp [verticalSampleLine]
  · rw [Metric.eventually_nhds_iff]
    exact ⟨ρ, hρ, by
      intro z hz
      change z ∈ frontier F ↔ z ∈ verticalSampleLine a
      rw [mem_verticalSampleLine_iff]
      exact hfrontier_line z hz⟩

private theorem regular_open_complement_interior
    {F : Set Tiling.Plane} (hregular : interior (closure F) = F) :
    interior (closure (interior Fᶜ)) = interior Fᶜ := by
  rw [interior_compl, closure_compl, interior_compl, hregular]

private theorem frontier_regular_open_complement_interior
    {F : Set Tiling.Plane} (hregular : interior (closure F) = F) :
    frontier (interior Fᶜ) = frontier F := by
  rw [interior_compl, frontier_compl, frontier]
  simp only [closure_closure, hregular, frontier]
  rw [← hregular]
  simp only [interior_interior]

private theorem boundaryStraight_of_complement_interior
    {F : Set Tiling.Plane} {a : Tiling.Plane}
    (hregular : interior (closure F) = F)
    (hstraight : BoundaryLocallyStraightAt (interior Fᶜ) a) :
    BoundaryLocallyStraightAt F a := by
  rcases hstraight with ⟨L, ha, hdim, hlocal⟩
  refine ⟨L, ha, hdim, ?_⟩
  filter_upwards [hlocal] with z hz
  rw [← frontier_regular_open_complement_interior hregular]
  exact hz

private theorem sampleQuadrantAt_isOpen (a : Tiling.Plane) (q : SampleQuadrant) :
    IsOpen (sampleQuadrantAt q a) := by
  cases q
  · exact (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  · exact (isOpen_lt Complex.continuous_re continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)

private theorem vertical_pattern_boundaryStraight_left
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hSW : Metric.ball a r ∩ sampleQuadrantAt .southwest a ⊆ F)
    (hNW : Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F)
    (hSE : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F)
    (hNE : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northeast a) F) :
    BoundaryLocallyStraightAt F a := by
  let G : Set Tiling.Plane := interior Fᶜ
  have hGopen : IsOpen G := isOpen_interior
  have hGregular : interior (closure G) = G := by
    dsimp [G]
    exact regular_open_complement_interior hregular
  have hGsubset : G ⊆ Fᶜ := interior_subset
  have hU_to_G {U : Set Tiling.Plane} (hUopen : IsOpen U)
      (hUcomp : U ⊆ Fᶜ) : U ⊆ G := interior_maximal hUcomp hUopen
  have hconstG : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ G ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) G) := by
    intro q
    cases q with
    | southwest =>
        right
        refine Set.disjoint_left.2 ?_
        intro x hx hxG
        exact hGsubset hxG (hSW hx)
    | southeast =>
        left
        exact hU_to_G
          (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .southeast))
          (fun x hx => Set.disjoint_left.mp hSE hx)
    | northwest =>
        right
        refine Set.disjoint_left.2 ?_
        intro x hx hxG
        exact hGsubset hxG (hNW hx)
    | northeast =>
        left
        exact hU_to_G
          (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northeast))
          (fun x hx => Set.disjoint_left.mp hNE hx)
  have hstraightG : BoundaryLocallyStraightAt G a := by
    dsimp [G]
    apply vertical_pattern_boundaryStraight hGopen hGregular hr hconstG
    · exact Set.disjoint_left.2 (by
        intro x hx hxG
        exact hGsubset hxG (hSW hx))
    · exact Set.disjoint_left.2 (by
        intro x hx hxG
        exact hGsubset hxG (hNW hx))
    · intro x hx
      exact hU_to_G
        (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .southeast))
        (fun x hx => Set.disjoint_left.mp hSE hx) hx
    · intro x hx
      exact hU_to_G
        (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northeast))
        (fun x hx => Set.disjoint_left.mp hNE hx) hx
  exact boundaryStraight_of_complement_interior hregular hstraightG

private theorem horizontal_pattern_boundaryStraight_left
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hSW : Metric.ball a r ∩ sampleQuadrantAt .southwest a ⊆ F)
    (hSE : Metric.ball a r ∩ sampleQuadrantAt .southeast a ⊆ F)
    (hNW : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northwest a) F)
    (hNE : Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northeast a) F) :
    BoundaryLocallyStraightAt F a := by
  let G : Set Tiling.Plane := interior Fᶜ
  have hGopen : IsOpen G := isOpen_interior
  have hGregular : interior (closure G) = G := by
    dsimp [G]
    exact regular_open_complement_interior hregular
  have hGsubset : G ⊆ Fᶜ := interior_subset
  have hU_to_G {U : Set Tiling.Plane} (hUopen : IsOpen U)
      (hUcomp : U ⊆ Fᶜ) : U ⊆ G := interior_maximal hUcomp hUopen
  have hconstG : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ G ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) G) := by
    intro q
    cases q with
    | southwest =>
        right
        exact Set.disjoint_left.2 (by
          intro x hx hxG
          exact hGsubset hxG (hSW hx))
    | southeast =>
        right
        exact Set.disjoint_left.2 (by
          intro x hx hxG
          exact hGsubset hxG (hSE hx))
    | northwest =>
        left
        exact hU_to_G
          (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northwest))
          (fun x hx => Set.disjoint_left.mp hNW hx)
    | northeast =>
        left
        exact hU_to_G
          (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northeast))
          (fun x hx => Set.disjoint_left.mp hNE hx)
  have hstraightG : BoundaryLocallyStraightAt G a := by
    dsimp [G]
    apply horizontal_pattern_boundaryStraight hGopen hGregular hr hconstG
    · exact Set.disjoint_left.2 (by
        intro x hx hxG
        exact hGsubset hxG (hSW hx))
    · exact Set.disjoint_left.2 (by
        intro x hx hxG
        exact hGsubset hxG (hSE hx))
    · intro x hx
      exact hU_to_G
        (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northwest))
        (fun x hx => Set.disjoint_left.mp hNW hx) hx
    · intro x hx
      exact hU_to_G
        (Metric.isOpen_ball.inter (sampleQuadrantAt_isOpen a .northeast))
        (fun x hx => Set.disjoint_left.mp hNE hx) hx
  exact boundaryStraight_of_complement_interior hregular hstraightG

private theorem proper_vertex_quadrantQuad_nonstraight
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hr : 0 < r)
    (hproper : a ∈ frontier F ∧ ¬BoundaryLocallyStraightAt F a)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F)) :
    ¬(
      (∀ q : SampleQuadrant, Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F) ∨
      (∀ q : SampleQuadrant, Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F) ∨
      (Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F ∧
        Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F ∧
        Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F) ∨
      (Metric.ball a r ∩ sampleQuadrantAt .southwest a ⊆ F ∧
        Metric.ball a r ∩ sampleQuadrantAt .southeast a ⊆ F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northwest a) F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northeast a) F) ∨
      (Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southwest a) F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northwest a) F ∧
        Metric.ball a r ∩ sampleQuadrantAt .southeast a ⊆ F ∧
        Metric.ball a r ∩ sampleQuadrantAt .northeast a ⊆ F) ∨
      (Metric.ball a r ∩ sampleQuadrantAt .southwest a ⊆ F ∧
        Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F ∧
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northeast a) F)) := by
  intro hpatterns
  rcases hpatterns with hall | hpatterns
  · exact proper_vertex_not_constant_quadrants hopen hregular hr hproper
      (Or.inl hall)
  rcases hpatterns with hnone | hpatterns
  · exact proper_vertex_not_constant_quadrants hopen hregular hr hproper
      (Or.inr hnone)
  rcases hpatterns with hhor | hpatterns
  · exact hproper.2 (horizontal_pattern_boundaryStraight hopen hregular hr hconst
      hhor.1 hhor.2.1 hhor.2.2.1 hhor.2.2.2)
  rcases hpatterns with hhor | hpatterns
  · exact hproper.2 (horizontal_pattern_boundaryStraight_left hregular hr
      hhor.1 hhor.2.1 hhor.2.2.1 hhor.2.2.2)
  rcases hpatterns with hver | hpatterns
  · exact hproper.2 (vertical_pattern_boundaryStraight hopen hregular hr hconst
      hver.1 hver.2.1 hver.2.2.1 hver.2.2.2)
  exact hproper.2 (vertical_pattern_boundaryStraight_left hregular hr
    hpatterns.1 hpatterns.2.1 hpatterns.2.2.1 hpatterns.2.2.2)


private theorem finiteWindowMatching
    {Y : ℕ → Set ℝ} {Z : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hconv : PointedFellConverges Y Z)
    (hsepY : ∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y)
    (hsepZ : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y)
    (hZne : Z.Nonempty)
    (R : ℝ) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) (hεδ : ε < δ / 3) :
    ∃ N, ∀ n, N ≤ n →
      (∀ z ∈ Z ∩ Set.Icc (-R) R,
        ∃! y, y ∈ Y n ∧ dist z y < ε) ∧
      (∀ y ∈ Y n ∩ Set.Icc (-R) R,
        ∃! z, z ∈ Z ∧ dist z y < ε) := by
  obtain ⟨z₀, hz₀⟩ := hZne
  let q : ℝ := z₀ + δ / 2
  have hqsep : δ / 2 ≤ Metric.infDist q Z := by
    have hZne' : Z.Nonempty := ⟨z₀, hz₀⟩
    apply (Metric.le_infDist hZne').2
    intro z hz
    by_cases hzz : z = z₀
    · subst z
      have hq0 : dist q z₀ = δ / 2 := by
        dsimp [q]
        rw [dist_eq_norm]
        rw [Real.norm_eq_abs]
        change |(z₀ + δ / 2) - z₀| = δ / 2
        rw [add_sub_cancel_left, abs_of_pos (by linarith)]
      exact hq0.symm.le
    · have hpair := hsepZ z₀ hz₀ z hz (Ne.symm hzz)
      have htri : dist z₀ z ≤ dist z₀ q + dist q z := dist_triangle _ _ _
      have hq0 : dist q z₀ = δ / 2 := by
        dsimp [q]
        rw [dist_eq_norm]
        rw [Real.norm_eq_abs]
        change |(z₀ + δ / 2) - z₀| = δ / 2
        rw [add_sub_cancel_left, abs_of_pos (by linarith)]
      have hq0' : dist z₀ q = δ / 2 := by simpa [dist_comm] using hq0
      rw [hq0'] at htri
      linarith
  let R₀ : ℝ := |q| + 1
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith [abs_nonneg q]
  have hqIcc : q ∈ Set.Icc (-R₀) R₀ := by
    dsimp [R₀]
    constructor <;> linarith [le_abs_self q, neg_le_abs q]
  have hδ₈ : 0 < δ / 8 := div_pos hδ (by norm_num)
  obtain ⟨N₀, hN₀⟩ := hconv R₀ hR₀ (δ / 8) hδ₈
  have hε' : 0 < min (ε / 3) (δ / 6) := by
    exact lt_min (by linarith) (by linarith)
  obtain ⟨N₁, hN₁⟩ := hconv R (by exact hR) (min (ε / 3) (δ / 6)) hε'
  refine ⟨max N₀ N₁, fun n hn ↦ ?_⟩
  have hn₀ : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hn₁ : N₁ ≤ n := le_trans (le_max_right _ _) hn
  have hYne : (Y n).Nonempty := by
    by_contra hne
    have hzero : Metric.infDist q (Y n) = 0 := by
      rw [show Y n = ∅ by exact Set.not_nonempty_iff_eq_empty.mp hne]
      exact Metric.infDist_empty
    have hqconv := hN₀ n hn₀ q hqIcc
    rw [hzero] at hqconv
    have hqabs : δ / 2 ≤ |Metric.infDist q Z| := by
      rw [abs_of_nonneg Metric.infDist_nonneg]
      exact hqsep
    have hqconv' : |Metric.infDist q Z| < δ / 8 := by simpa using hqconv
    linarith
  have hηε : min (ε / 3) (δ / 6) < ε := by
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηδ : min (ε / 3) (δ / 6) < δ / 3 := by
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hforward : ∀ z ∈ Z ∩ Set.Icc (-R) R,
      ∃! y, y ∈ Y n ∧ dist z y < ε := by
    intro z hz
    have hzconv := hN₁ n hn₁ z hz.2
    have hzero : Metric.infDist z Z = 0 := Metric.infDist_zero_of_mem hz.1
    rw [hzero] at hzconv
    have hlt : Metric.infDist z (Y n) < min (ε / 3) (δ / 6) := by
      rw [abs_lt] at hzconv
      linarith
    obtain ⟨y, hyY, hzy⟩ := (Metric.infDist_lt_iff hYne).mp hlt
    refine ⟨y, ⟨hyY, hzy.trans hηε⟩, ?_⟩
    intro y' hy'
    by_contra hne
    have hpair := hsepY n y' hy'.1 y hyY hne
    have htriangle : dist y' y ≤ dist y' z + dist z y := dist_triangle _ _ _
    have hy'z : dist y' z < ε := by simpa [dist_comm] using hy'.2
    have hzy' : dist z y' < ε := by simpa [dist_comm] using hy'.2
    linarith
  have hbackward : ∀ y ∈ Y n ∩ Set.Icc (-R) R,
      ∃! z, z ∈ Z ∧ dist z y < ε := by
    intro y hy
    have hyconv := hN₁ n hn₁ y hy.2
    have hzero : Metric.infDist y (Y n) = 0 := Metric.infDist_zero_of_mem hy.1
    rw [hzero] at hyconv
    have hlt : Metric.infDist y Z < min (ε / 3) (δ / 6) := by
      rw [abs_lt] at hyconv
      linarith
    have hZne' : Z.Nonempty := ⟨z₀, hz₀⟩
    obtain ⟨z, hzZ, hyz⟩ := (Metric.infDist_lt_iff hZne').mp hlt
    have hyz' : dist z y < min (ε / 3) (δ / 6) := by
      simpa [dist_comm] using hyz
    have hzy : dist z y < ε := hyz'.trans hηε
    refine ⟨z, ⟨hzZ, hzy⟩, ?_⟩
    intro z' hz'
    by_contra hne
    have hpair := hsepZ z' hz'.1 z hzZ hne
    have htriangle : dist z' z ≤ dist z' y + dist y z := dist_triangle _ _ _
    have hz'y : dist z' y < ε := by simpa [dist_comm] using hz'.2
    have hyz' : dist y z' < ε := by simpa [dist_comm] using hz'.2
    linarith
  exact ⟨hforward, hbackward⟩

private theorem finiteWindow_four_sample_transport
    {K : Region} {Y : ℕ → Set ℝ} {Z : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hconv : PointedFellConverges Y Z)
    (hsepY : ∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y)
    (hsepZ : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y)
    (hZne : Z.Nonempty)
    {Q : Set Tiling.Plane} {RK B : ℝ}
    {U : Set Tiling.Plane} {p : Fin 4 → Tiling.Plane}
    (hRK : 0 ≤ RK) (hB : 0 ≤ B)
    (hK : ∀ z ∈ K.support, dist z 0 ≤ RK)
    (hQ : ∀ z ∈ Q, dist z 0 ≤ B)
    (hQsample : ∀ i, p i ∈ Q)
    (ε : ℝ) (hε : 0 < ε)
    (hεδ : ε < δ / 3)
    (hU : U ⊆ K.support)
    (hmargin : ∀ i z, z ∈ Z →
      MembershipMargin U (imaginaryEmbedding z) (p i) ε) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i, (p i ∈ ⋃ z ∈ ((fun x : ℝ => (x : ℂ) * Complex.I) '' Z), z +ᵥ U ↔
        p i ∈ ⋃ y ∈ ((fun x : ℝ => (x : ℂ) * Complex.I) '' (Y n)), y +ᵥ U) := by
  let R : ℝ := RK + B + 1
  have hR : 0 < R := by dsimp [R]; linarith
  obtain ⟨N, hN⟩ := finiteWindowMatching hδ hconv hsepY hsepZ hZne R hR ε hε hεδ
  refine ⟨N, fun n hn i => ?_⟩
  constructor
  · intro hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨z, hp⟩ := hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨hz, hp⟩ := hp
    obtain ⟨z0, hz0, rfl⟩ := hz
    have hpS : p i ∈ imaginaryEmbedding z0 +ᵥ K.support := by
      rw [mem_vadd_iff_sub_mem] at hp ⊢
      exact hU hp
    have hrel : ((imaginaryEmbedding z0 +ᵥ K.support) ∩ Q).Nonempty :=
      ⟨p i, ⟨hpS, hQsample i⟩⟩
    have hbound := relevant_center_bound (K := K) (Q := Q)
      (s := imaginaryEmbedding z0) (c := 0) hK hrel hQ
    have habs : |z0| ≤ RK + B := by
      rw [imaginaryEmbedding_dist_zero] at hbound
      exact hbound
    have hzIcc : z0 ∈ Set.Icc (-R) R := by
      dsimp [R]
      constructor <;> linarith [neg_abs_le z0, le_abs_self z0]
    obtain ⟨y, hy, hzy⟩ := (hN n hn).1 z0 ⟨hz0, hzIcc⟩ |>.exists
    have hplane : dist (imaginaryEmbedding z0)
        (imaginaryEmbedding y) < ε := by
      calc
        dist (imaginaryEmbedding z0)
            (imaginaryEmbedding y) = |z0 - y| := by
              rw [dist_eq_norm]
              change ‖(z0 : ℂ) * Complex.I - (y : ℂ) * Complex.I‖ = |z0 - y|
              rw [← sub_mul, norm_mul]
              simp only [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_I,
                Real.norm_eq_abs, mul_one]
        _ < ε := hzy
    have hstable := membership_translate_stable (hmargin i z0 hz0) hplane
    rw [Set.mem_iUnion]
    refine ⟨imaginaryEmbedding y, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨⟨y, hy, rfl⟩, hstable.mpr hp⟩
  · intro hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨y, hp⟩ := hp
    rw [Set.mem_iUnion] at hp
    obtain ⟨hy, hp⟩ := hp
    obtain ⟨y0, hy0, rfl⟩ := hy
    have hpS : p i ∈ imaginaryEmbedding y0 +ᵥ K.support := by
      rw [mem_vadd_iff_sub_mem] at hp ⊢
      exact hU hp
    have hrel : ((imaginaryEmbedding y0 +ᵥ K.support) ∩ Q).Nonempty :=
      ⟨p i, ⟨hpS, hQsample i⟩⟩
    have hbound := relevant_center_bound (K := K) (Q := Q)
      (s := imaginaryEmbedding y0) (c := 0) hK hrel hQ
    have habs : |y0| ≤ RK + B := by
      rw [imaginaryEmbedding_dist_zero] at hbound
      exact hbound
    have hyIcc : y0 ∈ Set.Icc (-R) R := by
      dsimp [R]
      constructor <;> linarith [neg_abs_le y0, le_abs_self y0]
    obtain ⟨z, hz, hyz⟩ := (hN n hn).2 y0 ⟨hy0, hyIcc⟩ |>.exists
    have hplane : dist (imaginaryEmbedding z)
        (imaginaryEmbedding y0) < ε := by
      calc
        dist (imaginaryEmbedding z)
            (imaginaryEmbedding y0) = |z - y0| := by
              rw [dist_eq_norm]
              change ‖(z : ℂ) * Complex.I - (y0 : ℂ) * Complex.I‖ = |z - y0|
              rw [← sub_mul, norm_mul]
              simp only [← Complex.ofReal_sub, Complex.norm_real, Complex.norm_I,
                Real.norm_eq_abs, mul_one]
        _ < ε := hyz
    have hstable := membership_translate_stable (hmargin i z hz) hplane
    rw [Set.mem_iUnion]
    refine ⟨imaginaryEmbedding z, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨⟨z, hz, rfl⟩, hstable.mp hp⟩

private structure FourSampleTransportData
    (D : Set Tiling.Plane) (w : Tiling.Plane) (r : ℝ)
    (centres : Finset Tiling.Plane) (U : Set Tiling.Plane)
    (levelsX levelsY : Finset ℝ) where
  p : SampleQuadrant → Tiling.Plane
  q : SampleQuadrant → Prop
  p_ball : ∀ s, p s ∈ Metric.ball w r
  p_quadrant : ∀ s, p s ∈ sampleQuadrantAt s w
  p_membership : ∀ s, p s ∈ D ↔ q s
  q_nonstraight : ¬(
      (∀ s, q s) ∨ (∀ s, ¬q s) ∨
      (¬q .southwest ∧ ¬q .southeast ∧ q .northwest ∧ q .northeast) ∨
      (q .southwest ∧ q .southeast ∧ ¬q .northwest ∧ ¬q .northeast) ∨
      (¬q .southwest ∧ ¬q .northwest ∧ q .southeast ∧ q .northeast) ∨
      (q .southwest ∧ q .northwest ∧ ¬q .southeast ∧ ¬q .northeast))
  membership_margin : ∃ ρ > 0, ∀ s : SampleQuadrant, ∀ c : centres,
    MembershipMargin U (c : Tiling.Plane) (p s) ρ
  coordinate_margin : ∃ ρx > 0, ∃ ρy > 0, ∀ s, ∀ x ∈ levelsX,
      ρx < dist (p s).re x ∧ ∀ y ∈ levelsY, ρy < dist (p s).im y

private theorem fourSample_margins_of_finite_arrangement
    {centres : Finset Tiling.Plane} {U : Set Tiling.Plane}
    {levelsX levelsY : Finset ℝ} {p : SampleQuadrant → Tiling.Plane}
    (hcne : centres.Nonempty)
    (hU : ∀ _ : centres, (U.Nonempty ∧ Uᶜ.Nonempty))
    (hfront : ∀ c : centres, ∀ s : SampleQuadrant,
      p s ∉ frontier ((c : Tiling.Plane) +ᵥ U))
    (hlevelsX : ∀ s, (p s).re ∉ levelsX)
    (hlevelsY : ∀ s, (p s).im ∉ levelsY) :
    (∃ ρ > 0, ∀ s : SampleQuadrant, ∀ c : centres,
      MembershipMargin U (c : Tiling.Plane) (p s) ρ) ∧
    (∃ ρx > 0, ∃ ρy > 0, ∀ s, ∀ x ∈ levelsX,
      ρx < dist (p s).re x ∧ ∀ y ∈ levelsY, ρy < dist (p s).im y) := by
  classical
  have hcs : (↑centres : Set Tiling.Plane).Nonempty := by
    simpa using hcne
  have hm (s : SampleQuadrant) : ∃ ρ > 0, ∀ c : centres,
      MembershipMargin U (c : Tiling.Plane) (p s) ρ := by
    let V : centres → Set Tiling.Plane := fun c => (c : Tiling.Plane) +ᵥ U
    have hV : ∀ c : centres, (V c).Nonempty ∧ (V c)ᶜ.Nonempty := by
      intro c
      constructor
      · exact (hU c).1.vadd_set
      · rcases (hU c).2 with ⟨u, hu⟩
        refine ⟨(c : Tiling.Plane) +ᵥ u, ?_⟩
        intro hmem
        apply hu
        simpa [V] using (Set.mem_vadd_set_iff_neg_vadd_mem.mp hmem)
    obtain ⟨ρ, hρ, hρall⟩ := finite_membership_margin hcs.to_subtype V hV
      (x := p s) (fun c => hfront c s)
    refine ⟨ρ, hρ, ?_⟩
    have hcomp (c : centres) :
        ((c : Tiling.Plane) +ᵥ U)ᶜ =
          (fun y : Tiling.Plane => (c : Tiling.Plane) + y) '' Uᶜ := by
      ext x
      constructor
      · intro hx
        refine ⟨x - (c : Tiling.Plane), ?_, ?_⟩
        · intro hu
          apply hx
          exact mem_vadd_iff_sub_mem.mpr hu
        · change (c : Tiling.Plane) + (x - (c : Tiling.Plane)) = x
          abel
      · rintro ⟨y, hy, rfl⟩ hmem
        apply hy
        simpa [sub_eq_add_neg, add_assoc] using
          (mem_vadd_iff_sub_mem.mp hmem)
    have hdist (c : centres) :
        Metric.infDist (p s) ((c : Tiling.Plane) +ᵥ U)ᶜ =
          Metric.infDist (p s - (c : Tiling.Plane)) Uᶜ := by
      rw [hcomp]
      have h := Metric.infDist_image (isometry_add_left (c : Tiling.Plane))
        (x := p s - (c : Tiling.Plane)) (t := Uᶜ)
      simpa [sub_eq_add_neg, add_assoc] using h
    have hdistU (c : centres) :
        Metric.infDist (p s) ((c : Tiling.Plane) +ᵥ U) =
          Metric.infDist (p s - (c : Tiling.Plane)) U := by
      have hsetU : (c : Tiling.Plane) +ᵥ U =
          (fun y : Tiling.Plane => (c : Tiling.Plane) + y) '' U := by
        ext x
        constructor
        · intro hx
          refine ⟨x - (c : Tiling.Plane), mem_vadd_iff_sub_mem.mp hx, ?_⟩
          abel
        · rintro ⟨y, hy, rfl⟩
          apply mem_vadd_iff_sub_mem.mpr
          simpa [sub_eq_add_neg, add_assoc] using hy
      rw [hsetU]
      have h := Metric.infDist_image (isometry_add_left (c : Tiling.Plane))
        (x := p s - (c : Tiling.Plane)) (t := U)
      simpa [sub_eq_add_neg, add_assoc] using h
    intro c
    have hraw := hρall c
    change
      (p s ∈ (c : Tiling.Plane) +ᵥ U ∧
          ρ < Metric.infDist (p s) ((c : Tiling.Plane) +ᵥ U)ᶜ) ∨
        (p s ∉ (c : Tiling.Plane) +ᵥ U ∧
          ρ < Metric.infDist (p s) ((c : Tiling.Plane) +ᵥ U)) at hraw
    rcases hraw with hraw | hraw
    · rw [hdist c] at hraw
      exact Or.inl ⟨mem_vadd_iff_sub_mem.mp hraw.1, hraw.2⟩
    · rw [hdistU c] at hraw
      exact Or.inr ⟨by
          intro hmem
          exact hraw.1 (mem_vadd_iff_sub_mem.mpr hmem),
        hraw.2⟩
  obtain ⟨ρ₀, hρ₀, hm₀⟩ := hm .southwest
  obtain ⟨ρ₁, hρ₁, hm₁⟩ := hm .southeast
  obtain ⟨ρ₂, hρ₂, hm₂⟩ := hm .northwest
  obtain ⟨ρ₃, hρ₃, hm₃⟩ := hm .northeast
  let ρ := min ρ₀ (min ρ₁ (min ρ₂ ρ₃))
  have hρ : 0 < ρ := lt_min hρ₀ (lt_min hρ₁ (lt_min hρ₂ hρ₃))
  have hmono {a b : ℝ} (hab : b ≤ a) {c : centres} {s : SampleQuadrant}
      (h : MembershipMargin U (c : Tiling.Plane) (p s) a) :
      MembershipMargin U (c : Tiling.Plane) (p s) b := by
    rcases h with h | h
    · exact Or.inl ⟨h.1, lt_of_le_of_lt hab h.2⟩
    · exact Or.inr ⟨h.1, lt_of_le_of_lt hab h.2⟩
  have hmall : ∀ s : SampleQuadrant, ∀ c : centres,
      MembershipMargin U (c : Tiling.Plane) (p s) ρ := by
    intro s c
    cases s
    · exact hmono (min_le_left _ _) (hm₀ c)
    · exact hmono ((min_le_right _ _).trans (min_le_left _ _)) (hm₁ c)
    · exact hmono ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
        (hm₂ c)
    · exact hmono ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))) (hm₃ c)
  have hcoord (s : SampleQuadrant) : ∃ ρx > 0, ∀ x ∈ levelsX,
      ρx < dist (p s).re x := by
    exact finite_coordinate_margin levelsX (hlevelsX s)
  have hcoordY (s : SampleQuadrant) : ∃ ρy > 0, ∀ y ∈ levelsY,
      ρy < dist (p s).im y := by
    exact finite_coordinate_margin levelsY (hlevelsY s)
  obtain ⟨ρx₀, hρx₀, hx₀⟩ := hcoord .southwest
  obtain ⟨ρx₁, hρx₁, hx₁⟩ := hcoord .southeast
  obtain ⟨ρx₂, hρx₂, hx₂⟩ := hcoord .northwest
  obtain ⟨ρx₃, hρx₃, hx₃⟩ := hcoord .northeast
  obtain ⟨ρy₀, hρy₀, hy₀⟩ := hcoordY .southwest
  obtain ⟨ρy₁, hρy₁, hy₁⟩ := hcoordY .southeast
  obtain ⟨ρy₂, hρy₂, hy₂⟩ := hcoordY .northwest
  obtain ⟨ρy₃, hρy₃, hy₃⟩ := hcoordY .northeast
  let ρx := min ρx₀ (min ρx₁ (min ρx₂ ρx₃))
  let ρy := min ρy₀ (min ρy₁ (min ρy₂ ρy₃))
  have hρx : 0 < ρx := lt_min hρx₀ (lt_min hρx₁ (lt_min hρx₂ hρx₃))
  have hρy : 0 < ρy := lt_min hρy₀ (lt_min hρy₁ (lt_min hρy₂ hρy₃))
  refine ⟨⟨ρ, hρ, hmall⟩, ρx, hρx, ρy, hρy, ?_⟩
  intro s x hx
  constructor
  · cases s
    · exact lt_of_le_of_lt (min_le_left _ _) (hx₀ x hx)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (hx₁ x hx)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
        (hx₂ x hx)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))) (hx₃ x hx)
  · intro y hy
    cases s
    · exact lt_of_le_of_lt (min_le_left _ _) (hy₀ y hy)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (hy₁ y hy)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_left _ _)))
        (hy₂ y hy)
    · exact lt_of_le_of_lt ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))) (hy₃ y hy)

private def fourSampleTransportData_of_quadrant_constancy
    {F : Set Tiling.Plane} {a : Tiling.Plane} {r : ℝ}
    (hopen : IsOpen F) (hregular : interior (closure F) = F)
    (hproper : a ∈ frontier F ∧ ¬BoundaryLocallyStraightAt F a)
    (hr : 0 < r)
    (hconst : ∀ q : SampleQuadrant,
      (Metric.ball a r ∩ sampleQuadrantAt q a ⊆ F ∨
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt q a) F))
    {centres : Finset Tiling.Plane} {U : Set Tiling.Plane}
    {levelsX levelsY : Finset ℝ}
    (p : SampleQuadrant → Tiling.Plane)
    (hp : ∀ q : SampleQuadrant,
      p q ∈ Metric.ball a (r / 2) ∩ sampleQuadrantAt q a)
    (hcne : centres.Nonempty)
    (hU : ∀ _ : centres, (U.Nonempty ∧ Uᶜ.Nonempty))
    (hfront : ∀ c : centres, ∀ s : SampleQuadrant,
      p s ∉ frontier ((c : Tiling.Plane) +ᵥ U))
    (hlevelsX : ∀ s, (p s).re ∉ levelsX)
    (hlevelsY : ∀ s, (p s).im ∉ levelsY) :
    FourSampleTransportData F a (r / 2) centres U levelsX levelsY := by
  let q : SampleQuadrant → Prop := fun s ↦ SampleOccupiesQuadrant F a s
  have hpmem : ∀ s, p s ∈ F ↔ q s := by
    intro s
    dsimp [q]
    have hpr : p s ∈ Metric.ball a r ∩ sampleQuadrantAt s a :=
      inter_subset_inter (Metric.ball_subset_ball (by linarith)) Set.Subset.rfl (hp s)
    rcases hconst s with hfull | hdisj
    · have hocc : SampleOccupiesQuadrant F a s :=
        (sample_localQuadrantOccupies_iff_full hr hconst s).2 hfull
      constructor
      · intro _
        exact hocc
      · intro _
        exact hfull hpr
    · have hnocc : ¬SampleOccupiesQuadrant F a s := by
        intro hocc
        rcases hocc with ⟨t, ht, hsub⟩
        obtain ⟨z, hz⟩ := sampleQuadrant_ball_nonempty (lt_min hr ht) s
        apply Set.disjoint_left.mp hdisj
          (inter_subset_inter (Metric.ball_subset_ball (min_le_left _ _))
            Set.Subset.rfl hz)
        exact hsub (inter_subset_inter (Metric.ball_subset_ball (min_le_right _ _))
          Set.Subset.rfl hz)
      constructor
      · intro hmem
        exact False.elim (Set.disjoint_left.mp hdisj hpr hmem)
      · intro hmem
        exact False.elim (hnocc hmem)
  have hqnon : ¬(
      (∀ s, q s) ∨ (∀ s, ¬q s) ∨
      (¬q .southwest ∧ ¬q .southeast ∧ q .northwest ∧ q .northeast) ∨
      (q .southwest ∧ q .southeast ∧ ¬q .northwest ∧ ¬q .northeast) ∨
      (¬q .southwest ∧ ¬q .northwest ∧ q .southeast ∧ q .northeast) ∨
      (q .southwest ∧ q .northwest ∧ ¬q .southeast ∧ ¬q .northeast)) := by
    have hquad := proper_vertex_quadrantQuad_nonstraight
      hopen hregular hr hproper hconst
    have hfull : ∀ s, q s →
        Metric.ball a r ∩ sampleQuadrantAt s a ⊆ F := by
      intro s hs
      exact (sample_localQuadrantOccupies_iff_full hr hconst s).mp hs
    have hdisj : ∀ s, ¬q s →
        Disjoint (Metric.ball a r ∩ sampleQuadrantAt s a) F := by
      intro s hs
      rcases hconst s with h | h
      · exact False.elim (hs ((sample_localQuadrantOccupies_iff_full
          hr hconst s).mpr h))
      · exact h
    intro hbad
    apply hquad
    rcases hbad with hall | hnone | hhor | hhor' | hver | hver'
    · exact Or.inl (fun s ↦
        hfull s (hall s))
    · exact Or.inr (Or.inl (fun s ↦ hdisj s (hnone s)))
    · exact Or.inr (Or.inr (Or.inl ⟨
        hdisj .southwest hhor.1, hdisj .southeast hhor.2.1,
        hfull .northwest hhor.2.2.1, hfull .northeast hhor.2.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨
        hfull .southwest hhor'.1, hfull .southeast hhor'.2.1,
        hdisj .northwest hhor'.2.2.1, hdisj .northeast hhor'.2.2.2⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨
        hdisj .southwest hver.1, hdisj .northwest hver.2.1,
        hfull .southeast hver.2.2.1, hfull .northeast hver.2.2.2⟩))))
    · have hlast :
          (Metric.ball a r ∩ sampleQuadrantAt .southwest a ⊆ F) ∧
          (Metric.ball a r ∩ sampleQuadrantAt .northwest a ⊆ F) ∧
          Disjoint (Metric.ball a r ∩ sampleQuadrantAt .southeast a) F ∧
          Disjoint (Metric.ball a r ∩ sampleQuadrantAt .northeast a) F := ⟨
        hfull .southwest hver'.1, hfull .northwest hver'.2.1,
        hdisj .southeast hver'.2.2.1, hdisj .northeast hver'.2.2.2⟩
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hlast))))
  have hmc := fourSample_margins_of_finite_arrangement
    hcne hU hfront hlevelsX hlevelsY
  exact ⟨p, q, (fun s ↦ (hp s).1), (fun s ↦ (hp s).2), hpmem,
    hqnon, hmc.1, hmc.2⟩

private theorem exists_explicit_diagonal_samples
    {w : Tiling.Plane} {r : ℝ} {levelsX levelsY : Finset ℝ}
    (hr : 0 < r) :
    ∃ d : ℝ, 0 < d ∧ d < r / (4 * Real.sqrt 2) ∧
      d ∉ (levelsX.biUnion (fun x ↦ {‖x - w.re‖})) ∪
        (levelsY.biUnion (fun y ↦ {‖y - w.im‖})) ∧
      let p : SampleQuadrant → Tiling.Plane := fun s ↦
        match s with
        | .southwest => w - d - d * Complex.I
        | .southeast => w + d - d * Complex.I
        | .northwest => w - d + d * Complex.I
        | .northeast => w + d + d * Complex.I
      (∀ s, p s ∈ Metric.ball w (r / 2)) ∧
      (∀ s, p s ∈ sampleQuadrantAt s w) ∧
      (∀ s, (p s).re ∉ levelsX) ∧ (∀ s, (p s).im ∉ levelsY) := by
  classical
  let bad : Finset ℝ :=
    (levelsX.biUnion (fun x ↦ {‖x - w.re‖})) ∪
      (levelsY.biUnion (fun y ↦ {‖y - w.im‖}))
  have hupper : 0 < r / (4 * Real.sqrt 2) := by
    positivity
  have hinf : (Set.Ioo (0 : ℝ) (r / (4 * Real.sqrt 2))).Infinite := by
    exact Set.Ioo_infinite hupper
  obtain ⟨d, hdI, hdnot⟩ := hinf.exists_notMem_finset bad
  refine ⟨d, hdI.1, hdI.2, ?_, ?_⟩
  · simpa [bad] using hdnot
  let p : SampleQuadrant → Tiling.Plane := fun s ↦
    match s with
    | .southwest => w - d - d * Complex.I
    | .southeast => w + d - d * Complex.I
    | .northwest => w - d + d * Complex.I
    | .northeast => w + d + d * Complex.I
  dsimp
  constructor
  · intro s
    cases s <;> dsimp [p]
    all_goals rw [Metric.mem_ball, dist_comm, dist_eq_norm, Complex.norm_def]
    all_goals have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    all_goals have hsqrtpos : 0 < Real.sqrt 2 := by positivity
    all_goals norm_num [Complex.normSq_apply]
    all_goals rw [show d * d + d * d = 2 * d ^ 2 by ring]
    all_goals rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    all_goals norm_num [Real.sqrt_sq_eq_abs, abs_of_pos hdI.1]
    all_goals have hmul : d * (4 * Real.sqrt 2) < r :=
      (lt_div_iff₀ (by positivity : 0 < (4 : ℝ) * Real.sqrt 2)).mp hdI.2
    all_goals nlinarith [hmul]
  · constructor
    · intro s
      cases s <;> simp [sampleQuadrantAt, hdI.1]
    · constructor
      · intro s hx
        cases s
        · apply hdnot
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hx, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hx, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hx, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          left
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hx, ?_⟩
          simp [abs_of_pos hdI.1]
      · intro s hy
        cases s
        · apply hdnot
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hy, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hy, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hy, ?_⟩
          simp [abs_of_pos hdI.1]
        · apply hdnot
          apply Finset.mem_union.mpr
          right
          apply Finset.mem_biUnion.mpr
          refine ⟨_, hy, ?_⟩
          simp [abs_of_pos hdI.1]

private theorem region_openCarrier_compl_nonempty (K : Region) :
    K.openCarrierᶜ.Nonempty := by
  have hb : Bornology.IsBounded K.openCarrier :=
    K.isPolygonal.isBounded.subset interior_subset
  obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff.1 hb)
  refine ⟨x + ((R + 1 : ℝ) : ℂ), ?_⟩
  intro hz
  have hzdist := hR hz hx
  have hRnonneg : 0 ≤ R := by
    have hxx := hR hx hx
    simpa using hxx
  have hdist : dist x (x + ((R + 1 : ℝ) : ℂ)) ≤ R := by
    simpa [dist_comm] using hzdist
  rw [dist_eq_norm] at hdist
  change ‖x - (x + ((R + 1 : ℝ) : ℂ))‖ ≤ R at hdist
  rw [show x - (x + ((R + 1 : ℝ) : ℂ)) = -((R + 1 : ℝ) : ℂ) by ring,
    norm_neg] at hdist
  norm_num [Complex.norm_def, Complex.normSq_apply] at hdist
  rw [show (R + 1) * (R + 1) = (R + 1) ^ 2 by ring,
    Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R + 1)] at hdist
  linarith

private theorem finite_openCarrier_frontier_cross_radius
    (K : Region) (Q : Finset Tiling.Plane) (a : Tiling.Plane)
    (hQ : Q.Nonempty) :
    ∃ r > 0, ∀ t ∈ Q, ∀ z ∈ Metric.ball a r,
      z ∈ frontier (t +ᵥ K.openCarrier) → z.re = a.re ∨ z.im = a.im := by
  classical
  induction Q using Finset.induction_on with
  | empty => simp at hQ
  | @insert t Q ht ih =>
      by_cases hQne : Q.Nonempty
      · obtain ⟨r₀, hr₀, hcross₀⟩ := ih hQne
        obtain ⟨rt, hrt, hcrosst⟩ := translated_openCarrier_frontier_cross K t a
        refine ⟨min rt r₀, lt_min hrt hr₀, ?_⟩
        intro s hs z hz hzfront
        simp only [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact hcrosst z (Metric.ball_subset_ball (min_le_left _ _) hz) hzfront
        · exact hcross₀ s hs z (Metric.ball_subset_ball (min_le_right _ _) hz) hzfront
      · have hQempty : Q = ∅ := Finset.not_nonempty_iff_eq_empty.mp hQne
        subst Q
        obtain ⟨rt, hrt, hcrosst⟩ := translated_openCarrier_frontier_cross K t a
        refine ⟨rt, hrt, ?_⟩
        intro s hs
        simp only [Finset.mem_insert] at hs
        rcases hs with rfl | hs
        · exact hcrosst
        · simp at hs

private structure ExplicitFourSampleTransportData
    (D : Set Tiling.Plane) (w : Tiling.Plane) (r : ℝ)
    (centres : Finset Tiling.Plane) (U : Set Tiling.Plane)
    (levelsX levelsY : Finset ℝ) where
  data : FourSampleTransportData D w r centres U levelsX levelsY
  re_left : (data.p .southwest).re = (data.p .northwest).re
  re_right : (data.p .southeast).re = (data.p .northeast).re
  im_bottom : (data.p .southwest).im = (data.p .southeast).im
  im_top : (data.p .northwest).im = (data.p .northeast).im

/-!
# Diagonal proper-witness selector

This file isolates the final diagonal step: eventual witnesses at every fixed
accuracy are assembled into one sequence which is eventually a witness at
each index and converges to the marked point.
-/





open Filter Set Topology



private theorem diagonal_proper_witness
    {P : ℕ → Tiling.Plane → Prop} {w : Tiling.Plane}
    (hP : ∀ k : ℕ, 1 ≤ k →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∃ a : Tiling.Plane, P n a ∧ dist a w < (1 : ℝ) / (k + 1)) :
    ∃ wn : ℕ → Tiling.Plane,
      (∀ᶠ n : ℕ in atTop, P n (wn n)) ∧
      Tendsto wn atTop (𝓝 w) := by
  classical
  let N : ℕ → ℕ := fun k ↦
    if hk : 1 ≤ k then Classical.choose (hP k hk) else 0
  have hN : ∀ k : ℕ, 1 ≤ k →
      ∀ n : ℕ, N k ≤ n →
        ∃ a : Tiling.Plane, P n a ∧ dist a w < (1 : ℝ) / (k + 1) := by
    intro k hk n hn
    simpa [N, hk] using (Classical.choose_spec (hP k hk) n (by
      simpa [N, hk] using hn))
  let A : ℕ → ℕ → Tiling.Plane := fun k n ↦
    if hk : 1 ≤ k then
      if hn : N k ≤ n then Classical.choose (hN k hk n hn) else w
    else w
  have hA : ∀ k : ℕ, 1 ≤ k → ∀ n : ℕ, N k ≤ n →
      P n (A k n) ∧ dist (A k n) w < (1 : ℝ) / (k + 1) := by
    intro k hk n hn
    simpa [A, hk, hn] using (Classical.choose_spec (hN k hk n hn))
  let E : ℕ → Finset ℕ := fun n ↦
    (Finset.range (n + 1)).filter (fun k ↦ 1 ≤ k ∧ N k ≤ n)
  let W : ℕ → Tiling.Plane := fun n ↦
    if hn : (E n).Nonempty then A ((E n).max' hn) n else w
  have hW_mem : ∀ᶠ n : ℕ in atTop, P n (W n) := by
    filter_upwards [eventually_ge_atTop (max 1 (N 1))] with n hn
    have h1n : 1 ≤ n := le_trans (le_max_left _ _) hn
    have hN1n : N 1 ≤ n := le_trans (le_max_right _ _) hn
    have hE : (E n).Nonempty := by
      refine ⟨1, ?_⟩
      simp only [E, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, le_rfl, hN1n⟩
    have hmax : (E n).max' hE ∈ E n := Finset.max'_mem _ hE
    have hmaxP : 1 ≤ (E n).max' hE :=
      (Finset.mem_filter.mp hmax).2.1
    have hmaxN : N ((E n).max' hE) ≤ n :=
      (Finset.mem_filter.mp hmax).2.2
    dsimp [W, hE]
    rw [dif_pos hE]
    exact (hA _ hmaxP n hmaxN).1
  refine ⟨W, hW_mem, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (2 / ε)
  have hMpos : 0 < (M : ℝ) + 1 := by positivity
  have hMsmall : (1 : ℝ) / (M + 1) < ε := by
    have hM' : 2 < ε * ((M : ℝ) + 1) := by
      have hbound : (2 : ℝ) / ε < (M : ℝ) + 1 := by
        exact lt_of_lt_of_le hM (by linarith)
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hbound
    rw [div_lt_iff₀ hMpos]
    nlinarith
  refine ⟨max (M + 1) (N (M + 1)), ?_⟩
  intro n hn
  have hMn : M + 1 ≤ n := le_trans (le_max_left _ _) hn
  have hNMn : N (M + 1) ≤ n := le_trans (le_max_right _ _) hn
  have hE : (E n).Nonempty := by
    refine ⟨M + 1, ?_⟩
    simp only [E, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, hNMn⟩
  have hmax : (E n).max' hE ∈ E n := Finset.max'_mem _ hE
  have hmaxge : M + 1 ≤ (E n).max' hE := by
    exact Finset.le_max' (E n) (M + 1) (by
      simp only [E, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, hNMn⟩)
  have hmaxP : 1 ≤ (E n).max' hE :=
    (Finset.mem_filter.mp hmax).2.1
  have hmaxN : N ((E n).max' hE) ≤ n :=
    (Finset.mem_filter.mp hmax).2.2
  have hdist : dist (W n) w < (1 : ℝ) / ((E n).max' hE + 1) := by
    dsimp [W]
    rw [dif_pos hE]
    exact (hA _ hmaxP n hmaxN).2
  have hden : (M : ℝ) + 1 ≤ ((E n).max' hE : ℝ) + 1 := by
    have hdenNat : M + 1 ≤ (E n).max' hE + 1 := by omega
    exact_mod_cast hdenNat
  have hpos : 0 < ((E n).max' hE : ℝ) + 1 := by positivity
  have hsmall : (1 : ℝ) / ((E n).max' hE + 1) ≤ (1 : ℝ) / (M + 1) := by
    exact (one_div_le_one_div_of_le hMpos hden)
  exact hdist.trans_le (hsmall.trans hMsmall.le)


private theorem far_membershipMargin
    {K : Region} {U : Set Tiling.Plane}
    {A B z : ℝ} {p : Tiling.Plane}
    (hU : U ⊆ K.support)
    (hK : ∀ u ∈ K.support, dist u 0 ≤ A)
    (hp : dist p 0 ≤ B)
    (hUne : U.Nonempty)
    (hz : z ∉ Set.Icc (-(A + B + 1)) (A + B + 1)) :
    MembershipMargin U (imaginaryEmbedding z) p (1 / 2 : ℝ) := by
  obtain ⟨u₀, hu₀⟩ := hUne
  have hAnonneg : 0 ≤ A := le_trans dist_nonneg (hK u₀ (hU hu₀))
  have hBnonneg : 0 ≤ B := le_trans dist_nonneg hp
  have hCnonneg : 0 ≤ A + B + 1 := by linarith
  have hzabs : A + B + 1 < |z| := by
    by_cases hz0 : z < 0
    · have hzleft : z < -(A + B + 1) := by
        by_contra hnot
        apply hz
        exact ⟨le_of_not_gt hnot, by linarith⟩
      rw [abs_of_neg hz0]
      linarith
    · have hz0' : 0 ≤ z := le_of_not_gt hz0
      have hzright : A + B + 1 < z := by
        by_contra hnot
        apply hz
        exact ⟨by linarith, le_of_not_gt hnot⟩
      simpa only [abs_of_nonneg hz0'] using hzright
  have hcenter : A + B + 1 < dist (imaginaryEmbedding z) 0 := by
    simpa only [imaginaryEmbedding_dist_zero] using hzabs
  have hfar (u : Tiling.Plane) (hu : u ∈ U) :
      (1 : ℝ) < dist (p - imaginaryEmbedding z) u := by
    have huK : u ∈ K.support := hU hu
    have htri := dist_triangle (imaginaryEmbedding z) (p - u) 0
    have hrewrite : dist (imaginaryEmbedding z) (p - u) =
        dist (p - imaginaryEmbedding z) u := by
      rw [dist_eq_norm, dist_eq_norm]
      have hneg : imaginaryEmbedding z - (p - u) =
          -((p - imaginaryEmbedding z) - u) := by
        simp only [sub_eq_add_neg]
        abel
      rw [hneg, norm_neg]
    have hpu_eq : dist (p - u) 0 = dist p u := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      simp only [sub_eq_add_neg]
      abel
    have hpu : dist (p - u) 0 ≤ B + A := by
      calc
        dist (p - u) 0 = dist p u := hpu_eq
        _ ≤ dist p 0 + dist u 0 := by
          simpa [dist_comm] using (dist_triangle p 0 u)
        _ ≤ B + A := add_le_add hp (hK u huK)
    rw [hrewrite] at htri
    linarith
  have hnot : p - imaginaryEmbedding z ∉ U := by
    intro hmem
    have hbad := hfar (p - imaginaryEmbedding z) hmem
    have hzero : dist (p - imaginaryEmbedding z) 0 ≤ A := hK
      (p - imaginaryEmbedding z) (hU hmem)
    rw [dist_self] at hbad
    linarith
  right
  refine ⟨hnot, ?_⟩
  have hInf : (1 : ℝ) ≤ Metric.infDist (p - imaginaryEmbedding z) U :=
    (Metric.le_infDist ⟨u₀, hu₀⟩).2 (fun u hu ↦ le_of_lt (hfar u hu))
  linarith


private theorem scalar_all_membership_margin
    {K : Region} {U : Set Tiling.Plane} {Q : Finset Tiling.Plane}
    {Z : Set ℝ} {R A B rho : ℝ} {p : Fin 4 → Tiling.Plane}
    (hQeq : (Q : Set Tiling.Plane) =
      imaginaryEmbedding '' (Z ∩ Set.Icc (-R) R))
    (hfinite : ∀ i : Fin 4, ∀ c : Q,
      MembershipMargin U (c : Tiling.Plane) (p i) rho)
    (hrho : 0 < rho)
    (hUsub : U ⊆ K.support)
    (hK : ∀ u ∈ K.support, dist u 0 ≤ A)
    (hp : ∀ i, dist (p i) 0 ≤ B)
    (hUne : U.Nonempty)
    (hR : A + B + 1 ≤ R) :
    ∃ eps > 0, ∀ i : Fin 4, ∀ z ∈ Z,
      MembershipMargin U (imaginaryEmbedding z) (p i) eps := by
  let eps : ℝ := min rho (1 / 2)
  have heps : 0 < eps := lt_min hrho (by norm_num)
  have hepsrho : eps ≤ rho := min_le_left _ _
  have hepshalf : eps ≤ (1 / 2 : ℝ) := min_le_right _ _
  refine ⟨eps, heps, ?_⟩
  intro i z hz
  by_cases hzIcc : z ∈ Set.Icc (-R) R
  case pos =>
    have hzQ : imaginaryEmbedding z ∈ (Q : Set Tiling.Plane) := by
      rw [hQeq]
      exact ⟨z, ⟨hz, hzIcc⟩, rfl⟩
    let c : Q := ⟨imaginaryEmbedding z, hzQ⟩
    have hm := hfinite i c
    rcases hm with ⟨hm, hmρ⟩ | ⟨hm, hmρ⟩
    · exact Or.inl ⟨by simpa [c] using hm,
        lt_of_le_of_lt hepsrho (by simpa [c] using hmρ)⟩
    · exact Or.inr ⟨by simpa [c] using hm,
        lt_of_le_of_lt hepsrho (by simpa [c] using hmρ)⟩
  case neg =>
    have hfar := far_membershipMargin hUsub hK (hp i) hUne
      (z := z) (by
        intro hz'
        apply hzIcc
        exact ⟨le_trans (neg_le_neg hR) hz'.1, le_trans hz'.2 hR⟩)
    rcases hfar with ⟨hm, hmρ⟩ | ⟨hm, hmρ⟩
    · exact Or.inl ⟨hm, lt_of_le_of_lt hepshalf hmρ⟩
    · exact Or.inr ⟨hm, lt_of_le_of_lt hepshalf hmρ⟩

private theorem packing_of_subset_centres
    {K : Region} {S T : Set Tiling.Plane}
    (hST : S ⊆ T)
    (hT : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements T)) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
  intro i hi j hj hij
  change i.1 ∈ S at hi
  change j.1 ∈ S at hj
  let i' : K.toPolygonalRegion.placements T :=
    ⟨i, hST hi⟩
  let j' : K.toPolygonalRegion.placements T :=
    ⟨j, hST hj⟩
  have hij' : i' ≠ j' := by
    intro heq
    apply hij
    exact congrArg Subtype.val heq
  simpa [i', j'] using hT (hST hi) (hST hj) hij



private theorem properVertex_limit_setup
    {K : Region} {Y : ℕ → Set ℝ} {Z : Set ℝ}
    (hY : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n)))
    (hZ : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)))
    {w : Tiling.Plane}
    (hw : w ∈ properVertices (regularSupport K
      ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z))) :
    ∃ δ > 0, (∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y) ∧
      (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y) ∧
      ∃ v ∈ K.vertices, ∃ z ∈ Z,
        w = v + imaginaryEmbedding z := by
  obtain ⟨v, hv, s, hs, hws⟩ := Tiling.AxisParallel.properVertexProvenance hZ w hw
  obtain ⟨z, hz, hsz⟩ := hs
  obtain ⟨δ, hδ, hsep⟩ := Tiling.AxisParallel.exists_packingSeparation K
  have hsepY : ∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y := by
    intro n x hx y hy hxy
    have hxy' : imaginaryEmbedding x ≠
        imaginaryEmbedding y := by
      intro heq
      apply hxy
      simpa [imaginaryEmbedding] using congrArg Complex.im heq
    have hp := hsep _ (hY n) _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy'
    have hdist : dist (imaginaryEmbedding x)
        (imaginaryEmbedding y) = dist x y := by
      rw [dist_eq_norm]
      change ‖(x : ℂ) * Complex.I - (y : ℂ) * Complex.I‖ = dist x y
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul]
      simp only [Complex.norm_I, mul_one, dist_eq_norm, Complex.norm_real,
        Real.norm_eq_abs]
    have hp' : δ ≤ dist (imaginaryEmbedding x)
        (imaginaryEmbedding y) := by
      simpa [imaginaryEmbedding] using hp
    rw [hdist] at hp'
    exact hp'
  have hsepZ : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hxy
    have hxy' : imaginaryEmbedding x ≠
        imaginaryEmbedding y := by
      intro heq
      apply hxy
      simpa [imaginaryEmbedding] using congrArg Complex.im heq
    have hp := hsep _ hZ _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy'
    have hdist : dist (imaginaryEmbedding x)
        (imaginaryEmbedding y) = dist x y := by
      rw [dist_eq_norm]
      change ‖(x : ℂ) * Complex.I - (y : ℂ) * Complex.I‖ = dist x y
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul]
      simp only [Complex.norm_I, mul_one, dist_eq_norm, Complex.norm_real,
        Real.norm_eq_abs]
    have hp' : δ ≤ dist (imaginaryEmbedding x)
        (imaginaryEmbedding y) := by
      simpa [imaginaryEmbedding] using hp
    rw [hdist] at hp'
    exact hp'
  refine ⟨δ, hδ, hsepY, hsepZ, v, hv, z, hz, ?_⟩
  rw [← hsz] at hws
  simpa [imaginaryEmbedding] using hws

private theorem four_sample_eventual_transport_of_margin
    {K : Region} {Y : ℕ → Set ℝ} {Z : Set ℝ} {δ : ℝ}
    (hδ : 0 < δ)
    (hconv : PointedFellConverges Y Z)
    (hsepY : ∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y)
    (hsepZ : ∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y)
    (hZne : Z.Nonempty)
    {U : Set Tiling.Plane} {p : Fin 4 → Tiling.Plane}
    {RK B ε : ℝ}
    (hRK : 0 ≤ RK) (hB : 0 ≤ B)
    (hK : ∀ z ∈ K.support, dist z 0 ≤ RK)
    (hp : ∀ i, dist (p i) 0 ≤ B)
    (hε : 0 < ε) (hεδ : ε < δ / 3)
    (hU : U ⊆ K.support)
    (hmargin : ∀ i z, z ∈ Z →
      MembershipMargin U (imaginaryEmbedding z) (p i) ε) :
    ∃ N, ∀ n, N ≤ n →
      ∀ i, (p i ∈ ⋃ z ∈ ((fun x : ℝ => (x : ℂ) * Complex.I) '' Z),
        z +ᵥ U ↔
        p i ∈ ⋃ y ∈ ((fun x : ℝ => (x : ℂ) * Complex.I) '' (Y n)),
          y +ᵥ U) := by
  let Q : Set Tiling.Plane := Set.range p
  have hQ : ∀ z ∈ Q, dist z 0 ≤ B := by
    intro z hz
    obtain ⟨i, rfl⟩ := hz
    exact hp i
  have hQsample : ∀ i, p i ∈ Q := by
    intro i
    exact ⟨i, rfl⟩
  exact finiteWindow_four_sample_transport hδ hconv hsepY hsepZ hZne
    hRK hB hK hQ hQsample ε hε hεδ hU hmargin

open Classical in
private theorem finite_grid_selector_of_samples
    {K : Region} {Q : Finset Tiling.Plane}
    (_hQne : Q.Nonempty)
    (_hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Q : Set Tiling.Plane)))
    {w : Tiling.Plane} {r : ℝ}
    (d : ExplicitFourSampleTransportData
      (regularSupport K (Q : Set Tiling.Plane)) w r Q K.openCarrier
      (translatedVertexRealLevels K Q) (translatedVertexImagLevels K Q))
    {m n : ℕ} {Fx Fy : Finset ℝ}
    (hFx : Fx.card = m + 2) (hFy : Fy.card = n + 2)
    (hFxne : Fx.Nonempty) (hFyne : Fy.Nonempty)
    {xL xR yB yT : ℝ}
    (hxord : xL < xR) (hyord : yB < yT)
    (hxLlow : Fx.min' hFxne < xL) (hxLhigh : xL < Fx.max' hFxne)
    (hxRlow : Fx.min' hFxne < xR) (hxRhigh : xR < Fx.max' hFxne)
    (hyBlow : Fy.min' hFyne < yB) (hyBhigh : yB < Fy.max' hFyne)
    (hyTlow : Fy.min' hFyne < yT) (hyThigh : yT < Fy.max' hFyne)
    (hxLnot : xL ∉ Fx) (hxRnot : xR ∉ Fx)
    (hyBnot : yB ∉ Fy) (hyTnot : yT ∉ Fy)
    (hreal : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (m + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).xLevel k = (t + v).re)
    (himag : ∀ (t : Tiling.Plane), t ∈ Q → ∀ v ∈ K.vertices,
      ∃ k : Fin (n + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).yLevel k = (t + v).im)
    (hpSW : d.data.p .southwest = (xL : Tiling.Plane) + yB * Complex.I)
    (hpSE : d.data.p .southeast = (xR : Tiling.Plane) + yB * Complex.I)
    (hpNW : d.data.p .northwest = (xL : Tiling.Plane) + yT * Complex.I)
    (hpNE : d.data.p .northeast = (xR : Tiling.Plane) + yT * Complex.I) :
    ∃ a : Tiling.Plane,
      a ∈ properVertices (regularSupport K (Q : Set Tiling.Plane)) ∧
      xL < a.re ∧ a.re < xR ∧ yB < a.im ∧ a.im < yT := by
  have hq_to_bool : ∀ q : SampleQuadrant, d.data.q q ↔
      (match q with
        | .northwest =>
            ((xL : Tiling.Plane) + yT * Complex.I) ∈
              regularSupport K (Q : Set Tiling.Plane)
        | .northeast =>
            ((xR : Tiling.Plane) + yT * Complex.I) ∈
              regularSupport K (Q : Set Tiling.Plane)
        | .southwest =>
            ((xL : Tiling.Plane) + yB * Complex.I) ∈
              regularSupport K (Q : Set Tiling.Plane)
        | .southeast =>
            ((xR : Tiling.Plane) + yB * Complex.I) ∈
              regularSupport K (Q : Set Tiling.Plane)) := by
    intro q
    cases q
    · simpa [hpSW] using (d.data.p_membership .southwest).symm
    · simpa [hpSE] using (d.data.p_membership .southeast).symm
    · simpa [hpNW] using (d.data.p_membership .northwest).symm
    · simpa [hpNE] using (d.data.p_membership .northeast).symm
  have hnon : nonstraightQuad {
      northwest := decide (((xL : Tiling.Plane) + yT * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      northeast := decide (((xR : Tiling.Plane) + yT * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      southwest := decide (((xL : Tiling.Plane) + yB * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane))
      southeast := decide (((xR : Tiling.Plane) + yB * Complex.I) ∈
        regularSupport K (Q : Set Tiling.Plane)) } := by
    by_cases h₁ : d.data.q .northwest <;>
      by_cases h₂ : d.data.q .northeast <;>
      by_cases h₃ : d.data.q .southwest <;>
      by_cases h₄ : d.data.q .southeast <;>
      all_goals
        have hqbad := d.data.q_nonstraight
        simp only [h₁, h₂, h₃, h₄] at hqbad
        simp only [hq_to_bool] at h₁ h₂ h₃ h₄
        simp_all [nonstraightQuad, straightQuad] <;> aesop
  exact concrete_finiteArrangement_properVertex Q Fx Fy hFx hFy hFxne hFyne
    xL xR yB yT hxord hyord hxLlow hxLhigh hxRlow hxRhigh hyBlow hyBhigh
    hyTlow hyThigh hxLnot hxRnot hyBnot hyTnot hreal himag hnon

private theorem approximant_translated_levels_avoidance_local
    {K : Region} {Q Qn : Finset Tiling.Plane}
    {p : Fin 4 → Tiling.Plane} {eps rho : ℝ}
    (hmatch : ∀ c ∈ Qn, ∃ d ∈ Q, dist c d < eps)
    (hreal : ∀ i : Fin 4, ∀ x ∈ translatedVertexRealLevels K Q,
      rho < dist (p i).re x)
    (himag : ∀ i : Fin 4, ∀ y ∈ translatedVertexImagLevels K Q,
      rho < dist (p i).im y)
    (hepsrho : eps < rho) :
    ∀ i : Fin 4,
      (p i).re ∉ translatedVertexRealLevels K Qn ∧
      (p i).im ∉ translatedVertexImagLevels K Qn := by
  intro i
  constructor
  · intro hlevel
    rcases Finset.mem_biUnion.mp hlevel with ⟨c, hc, hlevel⟩
    rcases Finset.mem_image.mp hlevel with ⟨v, hv, hpv⟩
    obtain ⟨d, hd, hcd⟩ := hmatch c hc
    have hvK : v ∈ K.vertices := by
      change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
      rw [K.coe_vertexFinset] at hv
      exact hv
    have hlim : (d + v).re ∈ translatedVertexRealLevels K Q := by
      classical
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨v, ?_, rfl⟩
      change v ∈ (K.vertexFinset : Set Tiling.Plane)
      rw [K.coe_vertexFinset]
      exact hvK
    have hmargin := hreal i (d + v).re hlim
    have hcoord : dist (p i).re (d + v).re < eps := by
      calc
        dist (p i).re (d + v).re = dist (c + v).re (d + v).re := by
          rw [hpv]
        _ ≤ dist (c + v) (d + v) := by
          rw [Real.dist_eq, dist_eq_norm]
          have hcoord : (c + v).re - (d + v).re =
              ((c + v) - (d + v)).re := by simp only [Complex.sub_re]
          rw [hcoord]
          exact Complex.abs_re_le_norm ((c + v) - (d + v))
        _ = dist c d := by simp [dist_add_right]
        _ < eps := hcd
    linarith
  · intro hlevel
    rcases Finset.mem_biUnion.mp hlevel with ⟨c, hc, hlevel⟩
    rcases Finset.mem_image.mp hlevel with ⟨v, hv, hpv⟩
    obtain ⟨d, hd, hcd⟩ := hmatch c hc
    have hvK : v ∈ K.vertices := by
      change v ∈ (K.vertexFinset : Set Tiling.Plane) at hv
      rw [K.coe_vertexFinset] at hv
      exact hv
    have hlim : (d + v).im ∈ translatedVertexImagLevels K Q := by
      classical
      apply Finset.mem_biUnion.mpr
      refine ⟨d, hd, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨v, ?_, rfl⟩
      change v ∈ (K.vertexFinset : Set Tiling.Plane)
      rw [K.coe_vertexFinset]
      exact hvK
    have hmargin := himag i (d + v).im hlim
    have hcoord : dist (p i).im (d + v).im < eps := by
      calc
        dist (p i).im (d + v).im = dist (c + v).im (d + v).im := by
          rw [hpv]
        _ ≤ dist (c + v) (d + v) := by
          rw [Real.dist_eq, dist_eq_norm]
          have hcoord : (c + v).im - (d + v).im =
              ((c + v) - (d + v)).im := by simp only [Complex.sub_im]
          rw [hcoord]
          exact Complex.abs_im_le_norm ((c + v) - (d + v))
        _ = dist c d := by simp [dist_add_right]
        _ < eps := hcd
    linarith

private theorem finite_openUnion_frontier_subset_translated_grid
    {K : Region} {Q : Finset Tiling.Plane} {x : Tiling.Plane}
    (hx : x ∈ frontier (openUnion K (Q : Set Tiling.Plane))) :
    (∃ t ∈ Q, ∃ v ∈ K.vertices, x.re = (t + v).re) ∨
      (∃ t ∈ Q, ∃ v ∈ K.vertices, x.im = (t + v).im) := by
  rw [openUnion] at hx
  have hfront := Foundations.FilledSliceChains.frontier_iUnion_subset_iUnion_frontier
    (locallyFinite_of_finite
      fun t : (Q : Set Tiling.Plane) ↦ (t : Tiling.Plane) +ᵥ K.openCarrier) hx
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hfront
  rw [frontier_vadd_eq] at ht
  have hsource : x - (t : Tiling.Plane) ∈ frontier K.openCarrier := by
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using ht
  rw [K.frontier_openCarrier_eq_frontier_support] at hsource
  rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K
      hsource with ⟨v, hv, hcoord⟩ | ⟨v, hv, hcoord⟩
  · left
    refine ⟨(t : Tiling.Plane), t.property, v, hv, ?_⟩
    have := congrArg Complex.re (show x - (t : Tiling.Plane) = _ from rfl)
    change x.re - (t : Tiling.Plane).re = v.re at hcoord
    rw [Complex.add_re]
    linarith
  · right
    refine ⟨(t : Tiling.Plane), t.property, v, hv, ?_⟩
    change x.im - (t : Tiling.Plane).im = v.im at hcoord
    rw [Complex.add_im]
    linarith

private theorem regularSupport_iff_openUnion_of_off_translated_levels
    {K : Region} {Q : Finset Tiling.Plane} {x : Tiling.Plane}
    (hxoff : (∀ t ∈ Q, ∀ v ∈ K.vertices,
        x.re ≠ (t + v).re ∧ x.im ≠ (t + v).im)) :
    x ∈ regularSupport K (Q : Set Tiling.Plane) ↔
      x ∈ openUnion K (Q : Set Tiling.Plane) := by
  let U : Set Tiling.Plane := openUnion K (Q : Set Tiling.Plane)
  have hopen : IsOpen U := by
    dsimp [U, openUnion]
    exact isOpen_iUnion fun t : (Q : Set Tiling.Plane) ↦
      K.openCarrier_regularOpen.1.vadd (t : Tiling.Plane)
  constructor
  · intro hxreg
    by_contra hxU
    have hxcl : x ∈ closure U := interior_subset hxreg
    have hxfront : x ∈ frontier U := by
      rw [frontier]
      exact ⟨hxcl, by rw [hopen.interior_eq]; exact hxU⟩
    obtain h | h := finite_openUnion_frontier_subset_translated_grid hxfront
    · obtain ⟨t, ht, v, hv, hcoord⟩ := h
      exact (hxoff t ht v hv).1 hcoord
    · obtain ⟨t, ht, v, hv, hcoord⟩ := h
      exact (hxoff t ht v hv).2 hcoord
  · intro hxU
    apply mem_interior_iff_mem_nhds.mpr
    exact Filter.mem_of_superset (hopen.mem_nhds hxU) subset_closure

private theorem regularSupport_sample_transport_of_openUnion
    {K : Region} {Q Qn : Finset Tiling.Plane} {x : Tiling.Plane}
    (hQoff : ∀ v ∈ Q, ∀ u ∈ K.vertices,
      x.re ≠ (v + u).re ∧ x.im ≠ (v + u).im)
    (hQnoff : ∀ v ∈ Qn, ∀ u ∈ K.vertices,
      x.re ≠ (v + u).re ∧ x.im ≠ (v + u).im)
    (hopen : x ∈ openUnion K (Q : Set Tiling.Plane) ↔
      x ∈ openUnion K (Qn : Set Tiling.Plane)) :
    x ∈ regularSupport K (Q : Set Tiling.Plane) ↔
      x ∈ regularSupport K (Qn : Set Tiling.Plane) := by
  rw [regularSupport_iff_openUnion_of_off_translated_levels hQoff,
    regularSupport_iff_openUnion_of_off_translated_levels hQnoff]
  exact hopen

private theorem finite_approximant_k_local_witness
    {K : Region} {Q Qn : Finset Tiling.Plane} {w : Tiling.Plane} {r : ℝ}
    {S : Set Tiling.Plane} {rloc : ℝ}
    (d : ExplicitFourSampleTransportData
      (regularSupport K (Q : Set Tiling.Plane)) w r Q K.openCarrier
      (translatedVertexRealLevels K Q) (translatedVertexImagLevels K Q))
    (hQnne : Qn.Nonempty)
    (hQnpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Qn : Set Tiling.Plane)))
    (hfront : ∀ c : Qn, ∀ s : SampleQuadrant,
      d.data.p s ∉ frontier ((c : Tiling.Plane) +ᵥ K.openCarrier))
    (hlevels : ∀ s,
      (d.data.p s).re ∉ translatedVertexRealLevels K Qn ∧
      (d.data.p s).im ∉ translatedVertexImagLevels K Qn)
    (hmem : ∀ s : SampleQuadrant,
      d.data.p s ∈ regularSupport K (Qn : Set Tiling.Plane) ↔ d.data.q s)
    (hlocal : ∀ z ∈ Metric.ball w rloc,
      z ∈ regularSupport K (Qn : Set Tiling.Plane) ↔
        z ∈ regularSupport K S)
    (hrloc : 0 < rloc)
    {m n : ℕ} {Fx Fy : Finset ℝ}
    (hFx : Fx.card = m + 2) (hFy : Fy.card = n + 2)
    (hFxne : Fx.Nonempty) (hFyne : Fy.Nonempty)
    {xL xR yB yT : ℝ}
    (hxord : xL < xR) (hyord : yB < yT)
    (hxLlow : Fx.min' hFxne < xL) (hxLhigh : xL < Fx.max' hFxne)
    (hxRlow : Fx.min' hFxne < xR) (hxRhigh : xR < Fx.max' hFxne)
    (hyBlow : Fy.min' hFyne < yB) (hyBhigh : yB < Fy.max' hFyne)
    (hyTlow : Fy.min' hFyne < yT) (hyThigh : yT < Fy.max' hFyne)
    (hxLnot : xL ∉ Fx) (hxRnot : xR ∉ Fx)
    (hyBnot : yB ∉ Fy) (hyTnot : yT ∉ Fy)
    (hreal : ∀ (t : Tiling.Plane), t ∈ Qn → ∀ v ∈ K.vertices,
      ∃ k : Fin (m + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).xLevel k = (t + v).re)
    (himag : ∀ (t : Tiling.Plane), t ∈ Qn → ∀ v ∈ K.vertices,
      ∃ k : Fin (n + 2),
        (finsetCoordinateGrid Fx Fy hFx hFy).yLevel k = (t + v).im)
    (hpSW : d.data.p .southwest = (xL : Tiling.Plane) + yB * Complex.I)
    (hpSE : d.data.p .southeast = (xR : Tiling.Plane) + yB * Complex.I)
    (hpNW : d.data.p .northwest = (xL : Tiling.Plane) + yT * Complex.I)
    (hpNE : d.data.p .northeast = (xR : Tiling.Plane) + yT * Complex.I)
    (hrect : ∀ z : Tiling.Plane,
      xL < z.re → z.re < xR → yB < z.im → z.im < yT →
      z ∈ Metric.ball w (rloc / 2)) :
    ∃ z, z ∈ properVertices (regularSupport K S) ∧
      xL < z.re ∧ z.re < xR ∧ yB < z.im ∧ z.im < yT := by
  obtain ⟨hmN, hcN⟩ := fourSample_margins_of_finite_arrangement
    hQnne (fun _ ↦ ⟨K.isPolygonal.interior_nonempty K.nonempty,
      region_openCarrier_compl_nonempty K⟩) hfront
      (fun s ↦ (hlevels s).1) (fun s ↦ (hlevels s).2)
  let dataN : FourSampleTransportData
      (regularSupport K (Qn : Set Tiling.Plane)) w r Qn K.openCarrier
      (translatedVertexRealLevels K Qn) (translatedVertexImagLevels K Qn) :=
    { p := d.data.p
      q := d.data.q
      p_ball := d.data.p_ball
      p_quadrant := d.data.p_quadrant
      p_membership := hmem
      q_nonstraight := d.data.q_nonstraight
      membership_margin := hmN
      coordinate_margin := hcN }
  let dN : ExplicitFourSampleTransportData
      (regularSupport K (Qn : Set Tiling.Plane)) w r Qn K.openCarrier
      (translatedVertexRealLevels K Qn) (translatedVertexImagLevels K Qn) :=
    ⟨dataN, d.re_left, d.re_right, d.im_bottom, d.im_top⟩
  obtain ⟨z, hz, hzL, hzR, hzB, hzT⟩ := finite_grid_selector_of_samples
    (_hQne := hQnne) (_hpacking := hQnpack) dN hFx hFy hFxne hFyne
    hxord hyord hxLlow hxLhigh hxRlow hxRhigh hyBlow hyBhigh hyTlow hyThigh
    hxLnot hxRnot hyBnot hyTnot hreal himag (by simpa [dN, dataN] using hpSW)
      (by simpa [dN, dataN] using hpSE) (by simpa [dN, dataN] using hpNW)
      (by simpa [dN, dataN] using hpNE)
  have hzball : z ∈ Metric.ball w (rloc / 2) := hrect z hzL hzR hzB hzT
  have hzfull : z ∈ properVertices (regularSupport K S) := by
    have heq : regularSupport K (Qn : Set Tiling.Plane) =ᶠ[nhds z]
        regularSupport K S := by
      have hball : Metric.ball w (rloc / 2) ∈ nhds z :=
        Metric.isOpen_ball.mem_nhds hzball
      filter_upwards [hball] with y hy
      have hybig : y ∈ Metric.ball w rloc := by
        rw [Metric.mem_ball] at hy ⊢
        linarith [dist_triangle w y z, dist_comm y z]
      exact propext (hlocal y hybig)
    exact (isProperVertex_iff_of_eventuallyEq heq).mp hz
  exact ⟨z, hzfull, hzL, hzR, hzB, hzT⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel

private theorem support_bound_for_callsite
    {K : Region} :
    ∃ RK : ℝ, 0 ≤ RK ∧ ∀ z ∈ K.support, dist z 0 ≤ RK := by
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨R, hR⟩ := Metric.isBounded_iff.1 K.isPolygonal.isBounded
  have hRnonneg : 0 ≤ R := by
    have h := hR (interior_subset hu) (interior_subset hu)
    exact le_trans dist_nonneg h
  let RK : ℝ := R + dist u 0
  refine ⟨RK, ?_, ?_⟩
  · dsimp [RK]
    positivity
  · intro z hz
    have hzu := hR hz (interior_subset hu)
    dsimp [RK]
    exact (dist_triangle z u 0).trans (add_le_add hzu (le_refl _))

private theorem exists_fourSampleTransportData_bounded
    {K : Region} {Q : Finset Tiling.Plane}
    (hQne : Q.Nonempty)
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (Q : Set Tiling.Plane)))
    {w : Tiling.Plane}
    (hw : w ∈ properVertices (regularSupport K (Q : Set Tiling.Plane)))
    {levelsX levelsY : Finset ℝ} {bound : ℝ} (hbound : 0 < bound) :
    ∃ r > 0, r ≤ bound ∧
      Nonempty (ExplicitFourSampleTransportData
        (regularSupport K (Q : Set Tiling.Plane)) w
        (r / 2) Q K.openCarrier levelsX levelsY) := by
  classical
  have hopen : IsOpen (regularSupport K (Q : Set Tiling.Plane)) :=
    (regularSupport_isRegularOpen K (Q : Set Tiling.Plane)).1
  have hregular : interior (closure (regularSupport K (Q : Set Tiling.Plane))) =
      regularSupport K (Q : Set Tiling.Plane) :=
    (regularSupport_isRegularOpen K (Q : Set Tiling.Plane)).2
  obtain ⟨r₀, hr₀, hconst₀⟩ :=
    regularSupport_sample_quadrant_constancy hpacking w
  obtain ⟨r₁, hr₁, hcross⟩ :=
    finite_openCarrier_frontier_cross_radius K Q w hQne
  let r := min r₀ (min r₁ bound)
  have hr : 0 < r := lt_min hr₀ (lt_min hr₁ hbound)
  have hconst : ∀ q : SampleQuadrant,
      (Metric.ball w r ∩ sampleQuadrantAt q w ⊆
          regularSupport K (Q : Set Tiling.Plane) ∨
        Disjoint (Metric.ball w r ∩ sampleQuadrantAt q w)
          (regularSupport K (Q : Set Tiling.Plane))) := by
    intro q
    rcases hconst₀ q with h | h
    · exact Or.inl (fun z hz => h
        (inter_subset_inter
          (Metric.ball_subset_ball (min_le_left _ _)) Set.Subset.rfl hz))
    · exact Or.inr (h.mono_left
        (inter_subset_inter
          (Metric.ball_subset_ball (min_le_left _ _)) Set.Subset.rfl))
  obtain ⟨d, hdpos, hdsmall, hdnot, hpball₀, hpquad₀, hlevelsX, hlevelsY⟩ :=
    exists_explicit_diagonal_samples (levelsX := levelsX) (levelsY := levelsY) hr
  let p : SampleQuadrant → Tiling.Plane := fun s ↦
    match s with
    | .southwest => w - d - d * Complex.I
    | .southeast => w + d - d * Complex.I
    | .northwest => w - d + d * Complex.I
    | .northeast => w + d + d * Complex.I
  have hpball : ∀ s, p s ∈ Metric.ball w (r / 2) := by
    simpa [p] using hpball₀
  have hpquad : ∀ s, p s ∈ sampleQuadrantAt s w := by
    simpa [p] using hpquad₀
  have hpcoord : ∀ s, (p s).re ≠ w.re ∧ (p s).im ≠ w.im := by
    intro s
    cases s <;>
      dsimp [p] <;>
      constructor <;> intro h <;> norm_num at h ⊢ <;> linarith [hdpos]
  have hfront : ∀ c : Q, ∀ s : SampleQuadrant,
      p s ∉ frontier ((c : Tiling.Plane) +ᵥ K.openCarrier) := by
    intro c s hz
    have hpball₁ : p s ∈ Metric.ball w r₁ :=
      Metric.ball_subset_ball (by
        dsimp [r]
        have hrle : r ≤ r₁ := by
          exact (min_le_right r₀ (min r₁ bound)).trans (min_le_left _ _)
        linarith) (hpball s)
    rcases hcross c c.property (p s) hpball₁ hz with h | h
    · exact (hpcoord s).1 h
    · exact (hpcoord s).2 h
  have hU : ∀ _ : Q, K.openCarrier.Nonempty ∧ K.openCarrierᶜ.Nonempty := by
    intro c
    exact ⟨K.isPolygonal.interior_nonempty K.nonempty,
      region_openCarrier_compl_nonempty K⟩
  refine ⟨r, hr, ?_, ?_⟩
  · dsimp [r]
    exact (min_le_right _ _).trans (min_le_right _ _)
  · let data := fourSampleTransportData_of_quadrant_constancy
      hopen hregular hw hr hconst p (fun s ↦ ⟨hpball s, hpquad s⟩)
        hQne hU hfront hlevelsX hlevelsY
    have hdata_p : data.p = p := by
      simp [data, fourSampleTransportData_of_quadrant_constancy]
    refine ⟨⟨data, ?_, ?_, ?_, ?_⟩⟩
    all_goals rw [hdata_p]; simp [p]

private theorem outer_levels_from_extrema_callsite
    (F : Finset ℝ) {a b : ℝ} (hab : a < b)
    (ha : a ∉ F) (hb : b ∉ F) :
    ∃ (lo hi : ℝ) (m : ℕ) (F' : Finset ℝ),
      lo < a ∧ b < hi ∧ lo < hi ∧
      F' = insert lo (insert hi F) ∧ F'.card = m + 2 ∧ F ⊆ F' ∧
      F'.Nonempty ∧ a ∉ F' ∧ b ∉ F' ∧
      ∀ x ∈ F, lo ≤ x ∧ x ≤ hi := by
  classical
  by_cases hF : F.Nonempty
  · let lo : ℝ := min (F.min' hF) (a - 1)
    let hi : ℝ := max (F.max' hF) (b + 1)
    have hlo : lo < a := by
      dsimp [lo]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hhi : b < hi := by
      dsimp [hi]
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    obtain ⟨m, F', hFeq, hcard, hsub, hloF, hhiF⟩ :=
      exists_outer_level_augmentation F (lo := lo) (hi := hi)
        (lt_trans hlo (lt_trans hab hhi))
    have hF'ne : F'.Nonempty := ⟨lo, by rw [hFeq]; simp⟩
    have hbounds : ∀ x ∈ F, lo ≤ x ∧ x ≤ hi := by
      intro x hx
      constructor
      · exact (min_le_left _ _).trans (Finset.min'_le F x hx)
      · exact (Finset.le_max' F x hx).trans (le_max_left _ _)
    have haF' : a ∉ F' := by
      rw [hFeq]
      simp only [Finset.mem_insert]
      intro h
      rcases h with h | h | h
      · linarith [hlo]
      · linarith [hhi]
      · exact ha h
    have hbF' : b ∉ F' := by
      rw [hFeq]
      simp only [Finset.mem_insert]
      intro h
      rcases h with h | h | h
      · linarith [hlo, hab]
      · linarith [hhi]
      · exact hb h
    refine ⟨lo, hi, m, F', hlo, hhi,
      lt_trans hlo (lt_trans hab hhi), hFeq, hcard, hsub, hF'ne, haF', hbF', hbounds⟩
  · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    obtain ⟨m, F', hFeq, hcard, hsub, hloF, hhiF⟩ :=
      exists_outer_level_augmentation ∅ (lo := a - 1) (hi := b + 1) (by linarith)
    have hF'ne : F'.Nonempty := ⟨a - 1, by rw [hFeq]; simp⟩
    have haF' : a ∉ F' := by
      rw [hFeq]
      simp only [Finset.mem_insert]
      intro h
      rcases h with h | h | h
      · linarith
      · linarith
      · exact ha h
    have hbF' : b ∉ F' := by
      rw [hFeq]
      simp only [Finset.mem_insert]
      intro h
      rcases h with h | h | h
      · linarith
      · linarith
      · exact hb h
    refine ⟨a - 1, b + 1, m, F', by linarith, by linarith, by linarith,
      hFeq, hcard, hsub, hF'ne, haF', hbF', ?_⟩
    intro x hx
    simp at hx
private theorem finset_level_enumeration_callsite
    {k : ℕ} (F : Finset ℝ) (hF : F.card = k) (x : ℝ) (hx : x ∈ F) :
    ∃ i : Fin k,
      ((F.orderIsoOfFin hF i : F) : ℝ) = x := by
  let e := F.orderIsoOfFin hF
  let u : F := ⟨x, hx⟩
  exact ⟨e.symm u, by
    change ((e (e.symm u) : F) : ℝ) = x
    simp [u, e]⟩

private theorem properVertex_eventual_k_witness
    {K : Region} {Y : ℕ → Set ℝ} {Z : Set ℝ}
    (hY : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n)))
    (hZ : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)))
    (hconv : PointedFellConverges Y Z)
    {w : Tiling.Plane}
    (hw : w ∈ properVertices (regularSupport K
      ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)))
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ a : Tiling.Plane,
        a ∈ properVertices (regularSupport K
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n)) ∧
        dist a w < (1 : ℝ) / (k + 1) := by
  classical
  obtain ⟨δ, hδ, hsepY, hsepZ, v, hv, z, hz, hwvz⟩ :=
    properVertex_limit_setup hY hZ hw
  obtain ⟨RK, hRK, hK⟩ := support_bound_for_callsite
  let B : ℝ := RK + dist w 0 + 1
  let R₀ : ℝ := RK + B + 1
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hR₀ : 0 < R₀ := by
    dsimp [R₀]
    linarith
  have hzbound : |z| ≤ B := by
    have hvfront :=
      Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K
    rw [K.frontier_openCarrier_eq_frontier_support] at hvfront
    have hvcl : v ∈ closure K.support := frontier_subset_closure (hvfront hv)
    have hvK : v ∈ K.support := K.isPolygonal.isClosed.closure_eq ▸ hvcl
    have hvdist := hK v hvK
    have hzdist : |z| ≤ dist w 0 + dist v 0 := by
      rw [← imaginaryEmbedding_dist_zero z]
      have hdist : dist (imaginaryEmbedding z) 0 =
          dist w v := by
        rw [hwvz]
        simp [imaginaryEmbedding]
      rw [hdist]
      exact (dist_triangle w 0 v).trans
        (add_le_add (le_refl _) (by
          rw [dist_comm]))
    dsimp [B]
    linarith
  obtain ⟨Q, hQchar⟩ := finite_imaginary_window_finset
    (a := -R₀) (b := R₀) hδ hsepZ
  have hQne : Q.Nonempty := by
    refine ⟨imaginaryEmbedding z, ?_⟩
    apply (hQchar _).2
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    dsimp [R₀]
    exact ⟨by linarith [neg_abs_le z, hzbound],
      by linarith [le_abs_self z, hzbound]⟩
  have hQsub : ∀ t ∈ ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z),
      ((t +ᵥ K.openCarrier) ∩ Metric.ball w 1).Nonempty →
        t ∈ (Q : Set Tiling.Plane) := by
    intro t ht hrel
    obtain ⟨y, hy, rfl⟩ := ht
    exact finite_window_relevant_subset hQchar hK (by positivity)
      (by dsimp [R₀, B]; linarith)
      y hy hrel
  have hQmem : ∀ t ∈ (Q : Set Tiling.Plane),
      t ∈ ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z) := by
    intro t ht
    obtain ⟨y, hy, hyt⟩ := (hQchar t).1 ht
    exact ⟨y, hy.1, hyt⟩
  have hQpack := packing_of_subset_centres hQmem hZ
  obtain ⟨rlocZ, hrlocZ, hlocalZ⟩ := finite_window_regularSupport_local
    (w := w) (r := 1) (by positivity) hQmem hQsub
  have hwQ : w ∈ properVertices (regularSupport K (Q : Set Tiling.Plane)) := by
    have heq : regularSupport K
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z) =ᶠ[nhds w]
        regularSupport K (Q : Set Tiling.Plane) := by
      have hball : Metric.ball w (rlocZ / 2) ∈ nhds w :=
        Metric.isOpen_ball.mem_nhds
          (Metric.mem_ball_self (div_pos hrlocZ (by norm_num)))
      filter_upwards [hball] with x hx
      apply propext
      exact hlocalZ x (by
        rw [Metric.mem_ball] at hx ⊢
        linarith [dist_triangle w x w])
    exact (isProperVertex_iff_of_eventuallyEq heq).mp hw
  let bound : ℝ := min 1 ((1 : ℝ) / (16 * (k + 1)))
  have hbound : 0 < bound := by
    dsimp [bound]
    positivity
  obtain ⟨rD, hrD, hrDbound, hd⟩ := exists_fourSampleTransportData_bounded
    hQne hQpack hwQ
      (levelsX := translatedVertexRealLevels K Q)
      (levelsY := translatedVertexImagLevels K Q) hbound
  obtain ⟨d⟩ := hd
  have hbound1 : bound ≤ 1 := min_le_left _ _
  have hQeq : (Q : Set Tiling.Plane) =
      imaginaryEmbedding '' (Z ∩ Set.Icc (-R₀) R₀) := by
    ext t
    simpa [imaginaryEmbedding, imaginaryEmbedding] using
      (hQchar t)
  obtain ⟨rho, hrho, hmarginQ⟩ := d.data.membership_margin
  let p4 : Fin 4 → Tiling.Plane := fun i =>
    match i.1 with
    | 0 => d.data.p .southwest
    | 1 => d.data.p .southeast
    | 2 => d.data.p .northwest
    | _ => d.data.p .northeast
  have hp4 : ∀ i, dist (p4 i) 0 ≤ B := by
    intro i
    fin_cases i
    · dsimp [p4]
      change dist (d.data.p .southwest) 0 ≤ B
      have hpi := d.data.p_ball .southwest
      rw [Metric.mem_ball] at hpi
      have htri := dist_triangle (d.data.p .southwest) w 0
      dsimp [B]
      linarith
    · dsimp [p4]
      change dist (d.data.p .southeast) 0 ≤ B
      have hpi := d.data.p_ball .southeast
      rw [Metric.mem_ball] at hpi
      have htri := dist_triangle (d.data.p .southeast) w 0
      dsimp [B]
      linarith
    · dsimp [p4]
      change dist (d.data.p .northwest) 0 ≤ B
      have hpi := d.data.p_ball .northwest
      rw [Metric.mem_ball] at hpi
      have htri := dist_triangle (d.data.p .northwest) w 0
      dsimp [B]
      linarith
    · dsimp [p4]
      change dist (d.data.p .northeast) 0 ≤ B
      have hpi := d.data.p_ball .northeast
      rw [Metric.mem_ball] at hpi
      have htri := dist_triangle (d.data.p .northeast) w 0
      dsimp [B]
      linarith
  have hmarginQ4 : ∀ i : Fin 4, ∀ c : Q,
      MembershipMargin K.openCarrier (c : Tiling.Plane) (p4 i) rho := by
    intro i
    fin_cases i <;> dsimp [p4]
    all_goals
      intro c
      exact hmarginQ _ c
  obtain ⟨eps, heps, hmarginZ⟩ := scalar_all_membership_margin
    (K := K) (U := K.openCarrier) (Q := Q) (Z := Z) (R := R₀)
    (A := RK) (B := B) (rho := rho) (p := p4)
    hQeq
    hmarginQ4 hrho interior_subset hK
    hp4
    (by
      exact K.isPolygonal.interior_nonempty K.nonempty)
    (by dsimp [R₀]; linarith)
  let epsT : ℝ := min eps (δ / 4)
  have hepsT : 0 < epsT := lt_min heps (by linarith)
  have hmarginZT : ∀ i z, z ∈ Z →
      MembershipMargin K.openCarrier (imaginaryEmbedding z)
        (p4 i) epsT := by
    intro i z hz
    rcases hmarginZ i z hz with h | h
    · exact Or.inl ⟨h.1, lt_of_le_of_lt (min_le_left _ _) h.2⟩
    · exact Or.inr ⟨h.1, lt_of_le_of_lt (min_le_left _ _) h.2⟩
  obtain ⟨Ntransport, htransport⟩ :=
    four_sample_eventual_transport_of_margin hδ hconv hsepY hsepZ
      ⟨z, hz⟩ hRK hB hK
      hp4 hepsT
      (by
        dsimp [epsT]
        exact lt_of_le_of_lt (min_le_right _ _) (by linarith))
      interior_subset hmarginZT
  obtain ⟨rhoX, hrhoX, rhoY, hrhoY, hcoordmargin⟩ :=
    d.data.coordinate_margin
  let eta : ℝ := min (min epsT (min (rhoX / 2) (rhoY / 2))) (1 / 4)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaδ : eta < δ / 3 := by
    have hetaeps : eta ≤ epsT :=
      (min_le_left _ _).trans (min_le_left _ _)
    have hepsTδ : epsT ≤ δ / 4 := min_le_right _ _
    exact lt_of_le_of_lt (hetaeps.trans hepsTδ) (by linarith)
  obtain ⟨Nmatch, hmatch⟩ := finiteWindowMatching hδ hconv hsepY hsepZ
    ⟨z, hz⟩ R₀ hR₀ eta heta hetaδ
  let Rn : ℝ := B + 1 / 4
  have hRn : 0 < Rn := by
    dsimp [Rn]
    linarith
  obtain ⟨δY, hδY, hQnchar⟩ := approximant_window_finsets Rn hY
  refine ⟨max Nmatch Ntransport, ?_⟩
  intro n hn
  have hnM : Nmatch ≤ n := le_trans (le_max_left _ _) hn
  have hnT : Ntransport ≤ n := le_trans (le_max_right _ _) hn
  have hmatch_n := hmatch n hnM
  obtain ⟨Qn, hQnchar_n⟩ := hQnchar n
  have hzIcc : z ∈ Set.Icc (-R₀) R₀ := by
    exact ⟨by linarith [neg_abs_le z, hzbound],
      by linarith [le_abs_self z, hzbound]⟩
  have hQnne : Qn.Nonempty := by
    obtain ⟨y, hy, hzy⟩ := (hmatch_n.1 z ⟨hz, hzIcc⟩).exists
    have hybound : |y| ≤ Rn := by
      have hyz : |y| ≤ |z| + dist z y := by
        have htri : dist y 0 ≤ dist y z + dist z 0 :=
          dist_triangle _ _ _
        simpa [Real.dist_eq, dist_comm, add_comm] using htri
      dsimp [Rn]
      have heta4 : eta ≤ 1 / 4 := min_le_right _ _
      linarith
    refine ⟨imaginaryEmbedding y, ?_⟩
    apply (hQnchar_n _).2
    have hyIcc : y ∈ Set.Icc (-Rn) Rn := by
      exact ⟨by linarith [neg_abs_le y, hybound],
        by linarith [le_abs_self y, hybound]⟩
    refine ⟨y, ?_, rfl⟩
    exact ⟨hy, hyIcc⟩
  have hQnmem : ∀ t ∈ (Qn : Set Tiling.Plane),
      t ∈ ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n) := by
    intro t ht
    obtain ⟨y, hy, hyt⟩ := (hQnchar_n t).1 ht
    exact ⟨y, hy.1, hyt⟩
  have hQnpack := packing_of_subset_centres hQnmem (hY n)
  have hQnsub : ∀ t ∈ ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n),
      ((t +ᵥ K.openCarrier) ∩ Metric.ball w 1).Nonempty →
        t ∈ (Qn : Set Tiling.Plane) := by
    intro t ht hrel
    obtain ⟨y, hy, rfl⟩ := ht
    exact finite_window_relevant_subset hQnchar_n hK (by positivity)
      (by dsimp [Rn, B]; linarith)
      y hy hrel
  let rlocY : ℝ := 1 / 4
  have hrlocY : 0 < rlocY := by norm_num [rlocY]
  have hlocalY : ∀ q ∈ Metric.ball w rlocY,
      q ∈ regularSupport K ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n) ↔
        q ∈ regularSupport K (Qn : Set Tiling.Plane) := by
    exact regularSupport_eq_of_openUnion_eq_on_ball
      (by norm_num : (0 : ℝ) < 1) (window_openUnion_eq_of_relevant hQnmem hQnsub)
  have hQnmatch : ∀ c ∈ (Qn : Set Tiling.Plane),
      ∃ d ∈ (Q : Set Tiling.Plane), dist c d < eta := by
    intro c hc
    obtain ⟨y, hy, hcy⟩ := (hQnchar_n c).1 hc
    have hyR0 : y ∈ Set.Icc (-R₀) R₀ := by
      rcases hy.2 with ⟨hyl, hyr⟩
      dsimp [Rn] at hyl hyr
      dsimp [R₀, Rn, B]
      exact ⟨by linarith [hRK, hyl, (dist_nonneg : 0 ≤ dist w 0)],
        by linarith [hRK, hyr, (dist_nonneg : 0 ≤ dist w 0)]⟩
    obtain ⟨d, hd, hdy⟩ := (hmatch_n.2 y ⟨hy.1, hyR0⟩).exists
    have hdIcc : d ∈ Set.Icc (-R₀) R₀ := by
      have hyd : dist d y < eta := hdy
      have hybound : |y| ≤ Rn := (abs_le).2 hy.2
      have hdabs : |d| ≤ |y| + dist y d := by
        have htri : dist d 0 ≤ dist d y + dist y 0 :=
          dist_triangle _ _ _
        simpa [Real.dist_eq, dist_comm, add_comm] using htri
      dsimp [R₀, Rn, B]
      have heta4 : eta ≤ 1 / 4 := min_le_right _ _
      have hyd' : dist y d < eta := by simpa [dist_comm] using hyd
      have hdupper : d ≤ Rn + eta := by
        calc
          d ≤ |d| := le_abs_self d
          _ ≤ |y| + dist y d := hdabs
          _ ≤ Rn + eta := add_le_add hybound (le_of_lt hyd')
      have hdlower : -(Rn + eta) ≤ d := by
        exact le_trans (by linarith [hdabs, hybound, hyd'])
          (neg_abs_le d)
      dsimp [Rn] at hdupper hdlower
      constructor
      · linarith [hdlower, heta4, hRK, hB, (dist_nonneg : 0 ≤ dist w 0)]
      · linarith [hdupper, heta4, hRK, hB, (dist_nonneg : 0 ≤ dist w 0)]
    refine ⟨imaginaryEmbedding d,
      (hQchar _).2 ⟨d, ⟨hd, hdIcc⟩, rfl⟩, ?_⟩
    rw [← hcy]
    have hdist : dist (imaginaryEmbedding y)
        (imaginaryEmbedding d) = dist y d := by
      rw [dist_eq_norm]
      change ‖(y : ℂ) * Complex.I - (d : ℂ) * Complex.I‖ = dist y d
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul]
      simp only [Complex.norm_I, mul_one, dist_eq_norm, Complex.norm_real,
        Real.norm_eq_abs]
    rw [hdist]
    simpa only [dist_comm] using hdy
  have hp4ball : ∀ i : Fin 4, p4 i ∈ Metric.ball w 1 := by
    intro i
    have hrD1 : rD ≤ 1 := le_trans hrDbound (min_le_left _ _)
    fin_cases i
    · dsimp [p4]
      have hh := d.data.p_ball .southwest
      rw [Metric.mem_ball] at hh
      have hlt : dist (d.data.p .southwest) w < 1 := by linarith
      simpa [p4] using hlt
    · dsimp [p4]
      have hh := d.data.p_ball .southeast
      rw [Metric.mem_ball] at hh
      have hlt : dist (d.data.p .southeast) w < 1 := by linarith
      simpa [p4] using hlt
    · dsimp [p4]
      have hh := d.data.p_ball .northwest
      rw [Metric.mem_ball] at hh
      have hlt : dist (d.data.p .northwest) w < 1 := by linarith
      simpa [p4] using hlt
    · dsimp [p4]
      have hh := d.data.p_ball .northeast
      rw [Metric.mem_ball] at hh
      have hlt : dist (d.data.p .northeast) w < 1 := by linarith
      simpa [p4] using hlt
  have hopenQ : ∀ i : Fin 4,
      p4 i ∈ openUnion K (Q : Set Tiling.Plane) ↔
        p4 i ∈ openUnion K (Qn : Set Tiling.Plane) := by
    intro i
    have hZQ := window_openUnion_eq_of_relevant hQmem hQsub
      (p4 i) (hp4ball i)
    have hYQn := window_openUnion_eq_of_relevant hQnmem hQnsub
      (p4 i) (hp4ball i)
    have htr := htransport n hnT i
    have htr' : p4 i ∈ openUnion K
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z) ↔
        p4 i ∈ openUnion K
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n) := by
      simpa [openUnion, Tiling.Polygonal.openUnion, Tiling.AxisParallel.Region.openCarrier,
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using htr
    exact hZQ.symm.trans (htr'.trans hYQn)
  have hreal : ∀ i : Fin 4, ∀ x ∈ translatedVertexRealLevels K Q,
      rhoX < dist (p4 i).re x := by
    intro i x hx
    fin_cases i
    · exact (hcoordmargin .southwest x hx).1
    · exact (hcoordmargin .southeast x hx).1
    · exact (hcoordmargin .northwest x hx).1
    · exact (hcoordmargin .northeast x hx).1
  have himag : ∀ i : Fin 4, ∀ y ∈ translatedVertexImagLevels K Q,
      rhoY < dist (p4 i).im y := by
    intro i y hy
    obtain ⟨c, hc⟩ := hQne
    obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
    have hx0 : (c + v).re ∈ translatedVertexRealLevels K Q :=
      translated_real_level_mem hc hv
    fin_cases i
    · exact (hcoordmargin .southwest _ hx0).2 y hy
    · exact (hcoordmargin .southeast _ hx0).2 y hy
    · exact (hcoordmargin .northwest _ hx0).2 y hy
    · exact (hcoordmargin .northeast _ hx0).2 y hy
  have hQoff : ∀ i : Fin 4, ∀ c ∈ Q, ∀ v ∈ K.vertices,
      (p4 i).re ≠ (c + v).re ∧ (p4 i).im ≠ (c + v).im := by
    intro i c hc v hv
    have hx := hreal i ((c + v).re) (translated_real_level_mem hc hv)
    have hy := himag i ((c + v).im) (translated_imag_level_mem hc hv)
    constructor
    · intro heq
      rw [heq, dist_self] at hx
      exact (not_lt_of_ge (le_of_lt hrhoX)) hx
    · intro heq
      rw [heq, dist_self] at hy
      exact (not_lt_of_ge (le_of_lt hrhoY)) hy
  have hQnmatch' : ∀ c ∈ Qn, ∃ d ∈ Q, dist c d < eta := hQnmatch
  have havoid := approximant_translated_levels_avoidance_local
    (K := K) (Q := Q) (Qn := Qn) (p := p4) (eps := eta)
    (rho := min rhoX rhoY) hQnmatch'
    (fun i x hx => lt_of_le_of_lt (min_le_left _ _) (hreal i x hx))
    (fun i y hy => lt_of_le_of_lt (min_le_right _ _) (himag i y hy))
    (by
      have hx : eta < rhoX := by
        dsimp [eta]
        exact lt_of_le_of_lt
          ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
          (by linarith [hrhoX])
      have hy : eta < rhoY := by
        dsimp [eta]
        exact lt_of_le_of_lt
          ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
          (by linarith [hrhoY])
      exact lt_min hx hy)
  have hQnoff : ∀ i : Fin 4, ∀ c ∈ Qn, ∀ v ∈ K.vertices,
      (p4 i).re ≠ (c + v).re ∧ (p4 i).im ≠ (c + v).im := by
    intro i c hc v hv
    have hlev := havoid i
    have hrealmem : (c + v).re ∈ translatedVertexRealLevels K Qn :=
      translated_real_level_mem hc hv
    have himagemem : (c + v).im ∈ translatedVertexImagLevels K Qn :=
      translated_imag_level_mem hc hv
    constructor
    · intro heq
      apply hlev.1
      rw [heq]
      exact hrealmem
    · intro heq
      apply hlev.2
      rw [heq]
      exact himagemem
  have hmem : ∀ s : SampleQuadrant,
      d.data.p s ∈ regularSupport K (Qn : Set Tiling.Plane) ↔ d.data.q s := by
    intro s
    let i : Fin 4 := match s with
      | .southwest => 0
      | .southeast => 1
      | .northwest => 2
      | .northeast => 3
    have hreg := regularSupport_sample_transport_of_openUnion
      (K := K) (Q := Q) (Qn := Qn) (x := p4 i)
      (by
        intro c hc v hv
        exact hQoff i c hc v hv)
      (by
        intro c hc v hv
        exact hQnoff i c hc v hv)
      (hopenQ i)
    cases s <;> dsimp only [i, p4] at hreg
    · exact hreg.symm.trans (d.data.p_membership .southwest)
    · exact hreg.symm.trans (d.data.p_membership .southeast)
    · exact hreg.symm.trans (d.data.p_membership .northwest)
    · exact hreg.symm.trans (d.data.p_membership .northeast)
  have hfront : ∀ c : Qn, ∀ s : SampleQuadrant,
      d.data.p s ∉ frontier ((c : Tiling.Plane) +ᵥ K.openCarrier) := by
    intro c s hbad
    let i : Fin 4 := match s with
      | .southwest => 0
      | .southeast => 1
      | .northwest => 2
      | .northeast => 3
    have hpi : p4 i = d.data.p s := by
      cases s <;> rfl
    have hsource : d.data.p s - (c : Tiling.Plane) ∈ frontier K.openCarrier := by
      rw [frontier_vadd_eq] at hbad
      simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hbad
    rw [K.frontier_openCarrier_eq_frontier_support] at hsource
    rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K
      hsource with ⟨v, hv, hcoord⟩ | ⟨v, hv, hcoord⟩
    · have hlev : (c + v).re ∈ translatedVertexRealLevels K Qn :=
        translated_real_level_mem c.property hv
      apply (havoid i).1
      have heq : (p4 i).re = (c + v).re := by
        rw [hpi]
        change (d.data.p s - (c : Tiling.Plane)).re = v.re at hcoord
        rw [Complex.sub_re] at hcoord
        rw [Complex.add_re]
        linarith
      rw [heq]
      exact hlev
    · have hlev : (c + v).im ∈ translatedVertexImagLevels K Qn :=
        translated_imag_level_mem c.property hv
      apply (havoid i).2
      have heq : (p4 i).im = (c + v).im := by
        rw [hpi]
        change (d.data.p s - (c : Tiling.Plane)).im = v.im at hcoord
        rw [Complex.sub_im] at hcoord
        rw [Complex.add_im]
        linarith
      rw [heq]
      exact hlev
  have hlevels : ∀ s,
      (d.data.p s).re ∉ translatedVertexRealLevels K Qn ∧
      (d.data.p s).im ∉ translatedVertexImagLevels K Qn := by
    intro s
    cases s with
    | southwest => simpa [p4] using havoid 0
    | southeast => simpa [p4] using havoid 1
    | northwest => simpa [p4] using havoid 2
    | northeast => simpa [p4] using havoid 3
  let xL : ℝ := (d.data.p .southwest).re
  let xR : ℝ := (d.data.p .southeast).re
  let yB : ℝ := (d.data.p .southwest).im
  let yT : ℝ := (d.data.p .northwest).im
  have hsw := d.data.p_quadrant .southwest
  have hse := d.data.p_quadrant .southeast
  have hnw := d.data.p_quadrant .northwest
  have hne := d.data.p_quadrant .northeast
  simp only [sampleQuadrantAt, Set.mem_ofPred_eq] at hsw hse hnw hne
  have hxord : xL < xR := by
    dsimp [xL, xR]
    linarith [hsw.1, hse.1]
  have hyord : yB < yT := by
    dsimp [yB, yT]
    linarith [hsw.2, hnw.2]
  have hxLnot : xL ∉ translatedVertexRealLevels K Qn := by
    simpa [xL] using (hlevels .southwest).1
  have hxRnot : xR ∉ translatedVertexRealLevels K Qn := by
    simpa [xR] using (hlevels .southeast).1
  have hyBnot : yB ∉ translatedVertexImagLevels K Qn := by
    simpa [yB] using (hlevels .southwest).2
  have hyTnot : yT ∉ translatedVertexImagLevels K Qn := by
    simpa [yT] using (hlevels .northwest).2
  obtain ⟨lox, hix, mx, Fx, hlo, hhi, hlohi, hFx, hFxcard, hFxsub,
      hFxne, hxLnot', hxRnot', _hxBounds⟩ :=
    outer_levels_from_extrema_callsite
      (translatedVertexRealLevels K Qn) hxord hxLnot hxRnot
  obtain ⟨loy, hiy, my, Fy, hylow, hyhi, hylohi, hFy, hFycard, hFysub,
      hFyne, hyBnot', hyTnot', _hyBounds⟩ :=
    outer_levels_from_extrema_callsite
      (translatedVertexImagLevels K Qn) hyord hyBnot hyTnot
  have hxLlow : Fx.min' hFxne < xL := by
    exact lt_of_le_of_lt
      (Finset.min'_le Fx lox (by rw [hFx]; simp)) hlo
  have hxRlow : Fx.min' hFxne < xR := by
    exact lt_of_le_of_lt
      (Finset.min'_le Fx lox (by rw [hFx]; simp)) (lt_trans hlo hxord)
  have hxLhigh : xL < Fx.max' hFxne := by
    exact lt_of_lt_of_le (lt_trans hxord hhi)
      (Finset.le_max' Fx hix (by rw [hFx]; simp))
  have hxRhigh : xR < Fx.max' hFxne := by
    exact lt_of_lt_of_le hhi (Finset.le_max' Fx hix (by rw [hFx]; simp))
  have hyBlow : Fy.min' hFyne < yB := by
    exact lt_of_le_of_lt
      (Finset.min'_le Fy loy (by rw [hFy]; simp)) hylow
  have hyTlow : Fy.min' hFyne < yT := by
    exact lt_of_le_of_lt
      (Finset.min'_le Fy loy (by rw [hFy]; simp)) (lt_trans hylow hyord)
  have hyBhigh : yB < Fy.max' hFyne := by
    exact lt_of_lt_of_le (lt_trans hyord hyhi)
      (Finset.le_max' Fy hiy (by rw [hFy]; simp))
  have hyThigh : yT < Fy.max' hFyne := by
    exact lt_of_lt_of_le hyhi (Finset.le_max' Fy hiy (by rw [hFy]; simp))
  have hrealGrid : ∀ (t : Tiling.Plane), t ∈ Qn → ∀ v ∈ K.vertices,
      ∃ j : Fin (mx + 2),
        (finsetCoordinateGrid Fx Fy hFxcard hFycard).xLevel j = (t + v).re := by
    intro t ht v hv
    obtain ⟨j, hj⟩ := finset_level_enumeration_callsite Fx hFxcard
      (t + v).re (hFxsub (translated_real_level_mem ht hv))
    refine ⟨j, ?_⟩
    change finsetLevel Fx rfl (Fin.cast hFxcard.symm j) = (t + v).re
    convert hj using 1; simp [finsetLevel]
  have himagGrid : ∀ (t : Tiling.Plane), t ∈ Qn → ∀ v ∈ K.vertices,
      ∃ j : Fin (my + 2),
        (finsetCoordinateGrid Fx Fy hFxcard hFycard).yLevel j = (t + v).im := by
    intro t ht v hv
    obtain ⟨j, hj⟩ := finset_level_enumeration_callsite Fy hFycard
      (t + v).im (hFysub (translated_imag_level_mem ht hv))
    refine ⟨j, ?_⟩
    change finsetLevel Fy rfl (Fin.cast hFycard.symm j) = (t + v).im
    convert hj using 1; simp [finsetLevel]
  have hpSW : d.data.p .southwest = (xL : Tiling.Plane) + yB * Complex.I := by
    apply Complex.ext <;> simp [xL, yB]
  have hpSE : d.data.p .southeast = (xR : Tiling.Plane) + yB * Complex.I := by
    apply Complex.ext
    · simp [xR]
    · simpa [yB] using d.im_bottom.symm
  have hpNW : d.data.p .northwest = (xL : Tiling.Plane) + yT * Complex.I := by
    apply Complex.ext
    · simpa [xL] using d.re_left.symm
    · simp [yT]
  have hpNE : d.data.p .northeast = (xR : Tiling.Plane) + yT * Complex.I := by
    apply Complex.ext
    · simpa [xR] using d.re_right.symm
    · simpa [yT] using d.im_top.symm
  have hcorner_re_left : |xL - w.re| < rD / 2 := by
    have hh := d.data.p_ball .southwest
    rw [Metric.mem_ball] at hh
    have hn : ‖d.data.p .southwest - w‖ < rD / 2 := by
      simpa [dist_eq_norm] using hh
    have hc := Complex.abs_re_le_norm (d.data.p .southwest - w)
    rw [Complex.sub_re] at hc
    dsimp [xL]
    linarith
  have hcorner_re_right : |xR - w.re| < rD / 2 := by
    have hh := d.data.p_ball .southeast
    rw [Metric.mem_ball] at hh
    have hn : ‖d.data.p .southeast - w‖ < rD / 2 := by
      simpa [dist_eq_norm] using hh
    have hc := Complex.abs_re_le_norm (d.data.p .southeast - w)
    rw [Complex.sub_re] at hc
    dsimp [xR]
    linarith
  have hcorner_im_bottom : |yB - w.im| < rD / 2 := by
    have hh := d.data.p_ball .southwest
    rw [Metric.mem_ball] at hh
    have hn : ‖d.data.p .southwest - w‖ < rD / 2 := by
      simpa [dist_eq_norm] using hh
    have hc := Complex.abs_im_le_norm (d.data.p .southwest - w)
    rw [Complex.sub_im] at hc
    dsimp [yB]
    linarith
  have hcorner_im_top : |yT - w.im| < rD / 2 := by
    have hh := d.data.p_ball .northwest
    rw [Metric.mem_ball] at hh
    have hn : ‖d.data.p .northwest - w‖ < rD / 2 := by
      simpa [dist_eq_norm] using hh
    have hc := Complex.abs_im_le_norm (d.data.p .northwest - w)
    rw [Complex.sub_im] at hc
    dsimp [yT]
    linarith
  have hrect : ∀ z : Tiling.Plane,
      xL < z.re → z.re < xR → yB < z.im → z.im < yT →
      z ∈ Metric.ball w (rlocY / 2) := by
    intro z hzL hzR hzB hzT
    have hzre : |z.re - w.re| < rD / 2 := by
      rw [abs_lt]
      rcases (abs_lt.mp hcorner_re_left) with ⟨hxl₀, hxl₁⟩
      rcases (abs_lt.mp hcorner_re_right) with ⟨hxr₀, hxr₁⟩
      constructor <;> linarith
    have hzim : |z.im - w.im| < rD / 2 := by
      rw [abs_lt]
      rcases (abs_lt.mp hcorner_im_bottom) with ⟨hyb₀, hyb₁⟩
      rcases (abs_lt.mp hcorner_im_top) with ⟨hyt₀, hyt₁⟩
      constructor <;> linarith
    have hnormle : dist z w ≤ |(z - w).re| + |(z - w).im| := by
      rw [dist_eq_norm]
      exact Complex.norm_le_abs_re_add_abs_im _
    have hsum : |(z - w).re| + |(z - w).im| < rD := by
      rw [Complex.sub_re, Complex.sub_im]
      linarith only [hzre, hzim]
    have hdist : dist z w < rD := lt_of_le_of_lt hnormle hsum
    have hrDloc : rD < rlocY / 2 := by
      dsimp [rlocY]
      have hbound' : rD ≤ 1 / (16 * ((k : ℝ) + 1)) := by
        exact le_trans hrDbound (min_le_right _ _)
      have hsmall : (1 : ℝ) / (16 * ((k : ℝ) + 1)) ≤ 1 / 16 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith only [hk0]
      exact lt_of_le_of_lt (hbound'.trans hsmall) (by norm_num)
    rw [Metric.mem_ball]
    exact lt_of_lt_of_le (by simpa [dist_comm] using hdist) (le_of_lt hrDloc)
  have hlocal' : ∀ q ∈ Metric.ball w rlocY,
      q ∈ regularSupport K (Qn : Set Tiling.Plane) ↔
        q ∈ regularSupport K ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n) := by
    intro q hq
    exact (hlocalY q hq).symm
  obtain ⟨a, ha, haL, haR, haB, haT⟩ := finite_approximant_k_local_witness
    (K := K) (Q := Q) (Qn := Qn) (w := w) (r := rD / 2)
    (S := (fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n) (rloc := rlocY)
    d hQnne hQnpack hfront hlevels hmem hlocal' hrlocY
    hFxcard hFycard hFxne hFyne hxord hyord hxLlow hxLhigh hxRlow hxRhigh
    hyBlow hyBhigh hyTlow hyThigh hxLnot' hxRnot' hyBnot' hyTnot'
    hrealGrid himagGrid hpSW hpSE hpNW hpNE hrect
  have hdistaw : dist a w < rD := by
    have hare : |a.re - w.re| < rD / 2 := by
      rw [abs_lt]
      rcases abs_lt.mp hcorner_re_left with ⟨hl, _hr⟩
      rcases abs_lt.mp hcorner_re_right with ⟨_hl, hr⟩
      constructor <;> linarith
    have haim : |a.im - w.im| < rD / 2 := by
      rw [abs_lt]
      rcases abs_lt.mp hcorner_im_bottom with ⟨hl, _hr⟩
      rcases abs_lt.mp hcorner_im_top with ⟨_hl, hr⟩
      constructor <;> linarith
    have hnorm : dist a w ≤ |a.re - w.re| + |a.im - w.im| := by
      rw [dist_eq_norm]
      simpa only [Complex.sub_re, Complex.sub_im] using
        Complex.norm_le_abs_re_add_abs_im (a - w)
    exact lt_of_le_of_lt hnorm (by linarith only [hare, haim])
  refine ⟨a, ha, ?_⟩
  have hgoal : rD ≤ (1 : ℝ) / (k + 1) := by
    exact le_trans hrDbound (by
      dsimp [bound]
      apply le_trans (min_le_right _ _)
      apply one_div_le_one_div_of_le (by positivity)
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith only [hk0])
  exact lt_of_lt_of_le hdistaw hgoal

private theorem properVertices_persist_pointedLimit :
    ∀ {K : Region} {Y : ℕ → Set ℝ} {Z : Set ℝ},
      (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n))) →
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements
          ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)) →
      PointedFellConverges Y Z →
      ∀ w ∈ properVertices (regularSupport K
        ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Z)),
        ∃ wn : ℕ → Tiling.Plane,
          (∀ᶠ n in Filter.atTop,
            wn n ∈ properVertices (regularSupport K
              ((fun y : ℝ ↦ (y : ℂ) * Complex.I) '' Y n))) ∧
          Filter.Tendsto wn Filter.atTop (𝓝 w) := by
  intro K Y Z hY hZ hconv w hw
  apply diagonal_proper_witness
  intro k hk
  exact properVertex_eventual_k_witness hY hZ hconv hw k hk

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology

private theorem compactness_contradiction_core
    {K : Region} {δ : ℝ}
    (hnoncol : ¬ ∃ Col : Set Tiling.Plane,
      IsCenterColumn Axis.vertical K Col)
    (hcompact :
      ∀ {Y : ℕ → Set ℝ},
        (∀ n, 0 ∈ Y n) →
        (∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y) →
        (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements
            (imaginaryEmbedding '' Y n))) →
        ∃ (φ : ℕ → ℕ) (Z : Set ℝ), StrictMono φ ∧ 0 ∈ Z ∧
          PointedFellConverges (fun n ↦ Y (φ n)) Z ∧
          (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y) ∧
          Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements
              (imaginaryEmbedding '' Z)))
    (hnoProper :
      ∀ (axis : Axis) {S : Set Tiling.Plane},
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements S) →
        S.Nonempty →
        (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
        properVertices (regularSupport K S) = ∅ →
        IsCenterColumn axis K S)
    (hpersist :
      ∀ {Y : ℕ → Set ℝ} {Z : Set ℝ},
        (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements
            (imaginaryEmbedding '' Y n))) →
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements
            (imaginaryEmbedding '' Z)) →
        PointedFellConverges Y Z →
        ∀ w ∈ properVertices (regularSupport K
          (imaginaryEmbedding '' Z)),
          ∃ wn : ℕ → Tiling.Plane,
            (∀ᶠ n in Filter.atTop,
              wn n ∈ properVertices (regularSupport K
                (imaginaryEmbedding '' Y n))) ∧
            Filter.Tendsto wn Filter.atTop (𝓝 w))
    (hbad :
      ∀ R : ℝ, 0 < R →
        ∃ Y : Set ℝ,
          0 ∈ Y ∧
          (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y) ∧
          Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y)) ∧
          (∀ w ∈ properVertices (regularSupport K
              (imaginaryEmbedding '' Y)), R ≤ dist w 0)) :
    False := by
  let Y : ℕ → Set ℝ := fun n ↦
    Classical.choose (hbad ((n : ℝ) + 1) (by positivity))
  have hYspec : ∀ n : ℕ,
      0 ∈ Y n ∧
        (∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y) ∧
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y n)) ∧
        (∀ w ∈ properVertices (regularSupport K
            (imaginaryEmbedding '' Y n)),
          (n : ℝ) + 1 ≤ dist w 0) := by
    intro n
    simpa [Y] using
      (Classical.choose_spec (hbad ((n : ℝ) + 1) (by positivity)))
  have hY0 : ∀ n, 0 ∈ Y n := fun n ↦ (hYspec n).1
  have hYsep : ∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n,
      x ≠ y → δ ≤ dist x y := fun n ↦ (hYspec n).2.1
  have hYpack : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y n)) :=
    fun n ↦ (hYspec n).2.2.1
  obtain ⟨φ, Z, hφ, h0Z, hconv, _hZsep, hZpack⟩ :=
    hcompact hY0 hYsep hYpack
  have hYpack_subseq : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        (imaginaryEmbedding '' Y (φ n))) :=
    fun n ↦ hYpack (φ n)
  have hZempty : properVertices (regularSupport K
      (imaginaryEmbedding '' Z)) = ∅ := by
    apply Set.Subset.antisymm
    · intro w hw
      obtain ⟨wn, hwevent, hwtend⟩ :=
        hpersist (Y := fun n ↦ Y (φ n)) hYpack_subseq hZpack hconv w hw
      rw [Metric.tendsto_atTop] at hwtend
      obtain ⟨Ntend, htend⟩ := hwtend 1 (by norm_num)
      obtain ⟨Nevent, hevent⟩ := (eventually_atTop.1 hwevent)
      have hφge : ∀ n : ℕ, n ≤ φ n := by
        intro n
        induction n with
        | zero => exact Nat.zero_le _
        | succ n ih =>
            have hstep : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
            omega
      obtain ⟨M, hM⟩ := exists_nat_gt (dist w 0 + 1)
      let n : ℕ := max Ntend (max Nevent (max M 1))
      have hnT : Ntend ≤ n := le_max_left _ _
      have hnE : Nevent ≤ n := le_trans (le_max_left _ _) (le_max_right _ _)
      have hnM : M ≤ n :=
        le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
          (le_max_right _ _)
      have hnOne : 1 ≤ n :=
        le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
          (le_max_right _ _)
      have hnearW : dist (wn n) w < 1 := htend n hnT
      have hnear0 : dist (wn n) 0 < 1 + dist w 0 := by
        have htri : dist (wn n) 0 ≤ dist (wn n) w + dist w 0 :=
          dist_triangle _ _ _
        linarith
      have hproper := (hYspec (φ n)).2.2.2
        (wn n) (hevent n hnE)
      have hφn : (M : ℝ) ≤ (φ n : ℝ) := by
        exact_mod_cast (le_trans hnM (hφge n))
      have hM' : dist w 0 + 1 < (M : ℝ) := by exact hM
      have hbadlarge : dist w 0 + 1 < (φ n : ℝ) + 1 := by
        linarith
      have hproper' : (φ n : ℝ) + 1 ≤ dist (wn n) 0 := hproper
      linarith
    · intro w hw
      exact hw.elim
  have hZne : (imaginaryEmbedding '' Z).Nonempty := by
    exact ⟨imaginaryEmbedding 0, ⟨0, h0Z, rfl⟩⟩
  have hZalign : ∃ c : ℝ, ∀ s ∈ imaginaryEmbedding '' Z,
      Axis.vertical.transverseCoord s = c := by
    refine ⟨0, ?_⟩
    rintro s ⟨y, _hy, rfl⟩
    simp [imaginaryEmbedding, Axis.transverseCoord]
  have hcolumn : IsCenterColumn Axis.vertical K
      (imaginaryEmbedding '' Z) :=
    hnoProper Axis.vertical hZpack hZne hZalign hZempty
  exact hnoncol ⟨imaginaryEmbedding '' Z, hcolumn⟩


private theorem centered_vertical_carrier_eq_imaginary_image
    {S : Set Plane} {s : Plane}
    (hs : s ∈ S)
    (halign : ∃ c : ℝ, ∀ z ∈ S, Axis.vertical.transverseCoord z = c) :
    ∃ Y : Set ℝ, (-s) +ᵥ S = imaginaryEmbedding '' Y := by
  obtain ⟨c, hc⟩ := halign
  let Y : Set ℝ := {y | imaginaryEmbedding y ∈ (-s) +ᵥ S}
  refine ⟨Y, ?_⟩
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hRe : t.re = s.re := by
      simpa [Axis.transverseCoord] using (hc t ht).trans (hc s hs).symm
    refine ⟨(t - s).im, ?_, ?_⟩
    · change imaginaryEmbedding (t - s).im ∈ (-s) +ᵥ S
      refine ⟨t, ht, ?_⟩
      apply Complex.ext <;> simp [imaginaryEmbedding, hRe, sub_eq_add_neg, add_comm]
    · apply Complex.ext <;> simp [imaginaryEmbedding, hRe, sub_eq_add_neg, add_comm]
  · rintro ⟨y, hy, rfl⟩
    change imaginaryEmbedding y ∈ (-s) +ᵥ S at hy
    obtain ⟨t, ht, hty⟩ := hy
    exact ⟨t, ht, hty⟩

/- The core graph-transfer fact: replacing every vertex of a connected set by
   a point within B preserves connectivity after increasing the edge radius by
   2B. -/
private theorem linked_of_twoSided_nearby
    {S V : Set Plane} {R B : ℝ}
    (hR : 0 < R) (_hB : 0 ≤ B)
    (hS : Linked R S)
    (hnear : ∀ s ∈ S, ∃ v ∈ V, dist v s ≤ B)
    (hsource : ∀ v ∈ V, ∃ s ∈ S, dist v s ≤ B) :
    Linked (R + 2 * B) V := by
  classical
  let f : ∀ (s : Plane), s ∈ S → V := fun s hs =>
    ⟨Classical.choose (hnear s hs), (Classical.choose_spec (hnear s hs)).1⟩
  have hf_dist (s : Plane) (hs : s ∈ S) : dist (f s hs).1 s ≤ B :=
    (Classical.choose_spec (hnear s hs)).2
  have hV : V.Nonempty := by
    obtain ⟨s, hs⟩ := hS.1
    exact ⟨(f s hs).1, (f s hs).2⟩
  refine ⟨hV, ?_⟩
  let rS : Plane → Plane → Prop := fun u v => u ∈ S ∧ v ∈ S ∧ dist u v < R
  let rV : Plane → Plane → Prop :=
    fun u v => u ∈ V ∧ v ∈ V ∧ dist u v < R + 2 * B
  have hmap : ∀ {a b : Plane}, Relation.ReflTransGen rS a b →
      ∀ ha : a ∈ S, ∀ hb : b ∈ S,
        Relation.ReflTransGen rV (f a ha).1 (f b hb).1 := by
    intro a b hab
    induction hab with
    | refl => intro ha hb; exact Relation.ReflTransGen.refl
    | @tail m c hxy hyz ih =>
        intro ha hb
        rcases hyz with ⟨hm, hb', hmb⟩
        apply Relation.ReflTransGen.tail (ih ha hm)
        refine ⟨(f m hm).2, (f c hb').2, ?_⟩
        have hleft : dist (f m hm).1 m ≤ B := hf_dist m hm
        have hright : dist c (f c hb').1 ≤ B := by
          simpa only [dist_comm] using hf_dist c hb'
        calc
          dist (f m hm).1 (f c hb').1 ≤
              dist (f m hm).1 m + dist m (f c hb').1 := dist_triangle _ _ _
          _ ≤ B + dist m c + B := by
            calc
              dist (f m hm).1 m + dist m (f c hb').1 ≤
                  B + (dist m c + dist c (f c hb').1) := by
                gcongr
                exact dist_triangle m c (f c hb').1
              _ ≤ B + (dist m c + B) := by gcongr
              _ = B + dist m c + B := by ring
          _ < R + 2 * B := by linarith
  intro x hx y hy
  obtain ⟨sx, hsx, hxs⟩ := hsource x hx
  obtain ⟨sy, hsy, hys⟩ := hsource y hy
  have hpath : Relation.ReflTransGen rS sx sy := hS.2 sx hsx sy hsy
  have hleft : dist x (f sx hsx).1 < R + 2 * B := by
    have hf := hf_dist sx hsx
    have htri : dist x (f sx hsx).1 ≤ dist x sx + dist sx (f sx hsx).1 :=
      dist_triangle _ _ _
    have hfs : dist sx (f sx hsx).1 ≤ B := by
      simpa only [dist_comm] using hf
    calc
      dist x (f sx hsx).1 ≤ dist x sx + dist sx (f sx hsx).1 := htri
      _ ≤ B + B := by gcongr
      _ < R + 2 * B := by linarith
  have hright : dist (f sy hsy).1 y < R + 2 * B := by
    have hf := hf_dist sy hsy
    have hsy' : dist sy y ≤ B := by simpa only [dist_comm] using hys
    calc
      dist (f sy hsy).1 y ≤ dist (f sy hsy).1 sy + dist sy y := dist_triangle _ _ _
      _ ≤ B + B := add_le_add hf hsy'
      _ < R + 2 * B := by linarith
  have hchain : Relation.ReflTransGen rV (f sx hsx).1 (f sy hsy).1 :=
    hmap hpath hsx hsy
  have hleft' : rV x (f sx hsx).1 := ⟨hx, (f sx hsx).2, hleft⟩
  have hright' : rV (f sy hsy).1 y := ⟨(f sy hsy).2, hy, hright⟩
  exact (Relation.ReflTransGen.single hleft').trans
    (hchain.trans (Relation.ReflTransGen.single hright'))

private theorem properVertex_provenance_near_source
    {K : Region} {S V : Set Plane} {B : ℝ}
    (hprov : ∀ x ∈ V, ∃ v ∈ K.vertices, ∃ s ∈ S, x = v + s)
    (hvertex : ∀ v ∈ K.vertices, dist v 0 ≤ B) :
    ∀ x ∈ V, ∃ s ∈ S, dist x s ≤ B := by
  intro x hx
  obtain ⟨v, hv, s, hs, rfl⟩ := hprov x hx
  refine ⟨s, hs, ?_⟩
  rw [dist_eq_norm]
  simpa [vadd_eq_add] using hvertex v hv

private theorem uniform_nearby_imaginary_origin
    {K : Region} {δ : ℝ}
    (hnoncol : ¬ ∃ Col : Set Plane, IsCenterColumn Axis.vertical K Col)
    (hcompact :
      ∀ {Y : ℕ → Set ℝ},
        (∀ n, 0 ∈ Y n) →
        (∀ n, ∀ x ∈ Y n, ∀ y ∈ Y n, x ≠ y → δ ≤ dist x y) →
        (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y n))) →
        ∃ (φ : ℕ → ℕ) (Z : Set ℝ), StrictMono φ ∧ 0 ∈ Z ∧
          PointedFellConverges (fun n ↦ Y (φ n)) Z ∧
          (∀ x ∈ Z, ∀ y ∈ Z, x ≠ y → δ ≤ dist x y) ∧
          Tiling.IsPacking K.toPolygonalRegion.prototileFamily
            (K.toPolygonalRegion.placements (imaginaryEmbedding '' Z)))
    (hnoProper :
      ∀ (axis : Axis) {S : Set Plane},
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements S) →
        S.Nonempty →
        (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
        properVertices (regularSupport K S) = ∅ → IsCenterColumn axis K S)
    (hpersist :
      ∀ {Y : ℕ → Set ℝ} {Z : Set ℝ},
        (∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y n))) →
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Z)) →
        PointedFellConverges Y Z →
        ∀ w ∈ properVertices (regularSupport K (imaginaryEmbedding '' Z)),
          ∃ wn : ℕ → Plane,
            (∀ᶠ n in Filter.atTop,
              wn n ∈ properVertices (regularSupport K
                (imaginaryEmbedding '' Y n))) ∧
            Filter.Tendsto wn Filter.atTop (𝓝 w)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (Y : Set ℝ), 0 ∈ Y →
        (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y) →
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y)) →
    ∃ w ∈ properVertices (regularSupport K (imaginaryEmbedding '' Y)),
          dist w 0 ≤ B := by
  by_contra hbound
  have hfail : ∀ B : ℝ, 0 ≤ B →
      ∃ Y : Set ℝ, 0 ∈ Y ∧
        (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y) ∧
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y)) ∧
        ¬ ∃ w ∈ properVertices (regularSupport K
            (imaginaryEmbedding '' Y)), dist w 0 ≤ B := by
    intro B hB
    by_contra h
    apply hbound
    refine ⟨B, hB, ?_⟩
    intro Y h0 hYsep hYpack
    by_contra hnear
    exact h ⟨Y, h0, hYsep, hYpack, hnear⟩
  have hbad : ∀ R : ℝ, 0 < R →
      ∃ Y : Set ℝ,
        0 ∈ Y ∧
        (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y) ∧
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y)) ∧
        (∀ w ∈ properVertices (regularSupport K
            (imaginaryEmbedding '' Y)), R ≤ dist w 0) := by
    intro R hR
    obtain ⟨Y, h0, hYsep, hYpack, hfar⟩ := hfail R hR.le
    refine ⟨Y, h0, hYsep, hYpack, ?_⟩
    intro w hw
    have hnot : ¬ dist w 0 ≤ R := by
      intro hd
      exact hfar ⟨w, hw, hd⟩
    exact le_of_lt (lt_of_not_ge hnot)
  exact compactness_contradiction_core hnoncol hcompact hnoProper hpersist hbad

private theorem packing_vadd
    (K : Region) (S : Set Plane) (u : Plane)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (u +ᵥ S)) := by
  apply (isPacking_iff_openCarrier_disjoint K (u +ᵥ S)).2
  intro a ha b hb hab
  obtain ⟨s, hs, rfl⟩ := ha
  obtain ⟨t, ht, rfl⟩ := hb
  have hst : s ≠ t := by
    intro h
    apply hab
    subst t
    rfl
  have hdis := (isPacking_iff_openCarrier_disjoint K S).1 hpack hs ht hst
  have hleft : (u + s) +ᵥ K.openCarrier = u +ᵥ (s +ᵥ K.openCarrier) := by
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hz
    all_goals (convert hz using 1; abel_nf)
  have hright : (u + t) +ᵥ K.openCarrier = u +ᵥ (t +ᵥ K.openCarrier) := by
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    constructor <;> intro hz
    all_goals (convert hz using 1; abel_nf)
  change Disjoint ((u + s) +ᵥ K.openCarrier) ((u + t) +ᵥ K.openCarrier)
  rw [hleft, hright, Set.disjoint_left]
  intro z hz hz'
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨y, hy, hxy⟩ := hz'
  have hxy' : x = y :=
    (add_left_cancel (show u + y = u + x from hxy)).symm
  subst y
  exact (Set.disjoint_left.mp hdis) hx hy

/- The origin estimate applies at every centre after translation. -/
private theorem uniform_nearby_every_center_of_origin_bound
    {K : Region} {δ B : ℝ}
    (horigin : ∀ (Y : Set ℝ), 0 ∈ Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y) →
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements (imaginaryEmbedding '' Y)) →
      ∃ w ∈ properVertices (regularSupport K (imaginaryEmbedding '' Y)),
        dist w 0 ≤ B)
    (hsep : ∀ {S : Set Plane},
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    ∀ (S : Set Plane) (s : Plane),
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      s ∈ S →
      (∃ c : ℝ, ∀ z ∈ S, Axis.vertical.transverseCoord z = c) →
      ∃ w ∈ properVertices (regularSupport K S), dist w s ≤ B := by
  intro S s hpack hs halign
  obtain ⟨Y, hYeq⟩ := centered_vertical_carrier_eq_imaginary_image hs halign
  have h0Y : 0 ∈ Y := by
    have h0 : imaginaryEmbedding 0 ∈ (-s) +ᵥ S := by
      exact ⟨s, hs, by simp [imaginaryEmbedding, vadd_eq_add]⟩
    rw [hYeq] at h0
    obtain ⟨y, hy, heq⟩ := h0
    have hy0 : y = 0 := by
      simpa [imaginaryEmbedding] using congrArg Complex.im heq
    exact hy0 ▸ hy
  have hYsep : ∀ x ∈ Y, ∀ y ∈ Y, x ≠ y → δ ≤ dist x y := by
    intro x hx y hy hxy
    have hxS : imaginaryEmbedding x ∈ (-s) +ᵥ S := by
      rw [hYeq]
      exact ⟨x, hx, rfl⟩
    have hyS : imaginaryEmbedding y ∈ (-s) +ᵥ S := by
      rw [hYeq]
      exact ⟨y, hy, rfl⟩
    have hxy' : imaginaryEmbedding x ≠ imaginaryEmbedding y := by
      intro h
      apply hxy
      have him := congrArg Complex.im h
      simpa [imaginaryEmbedding] using him
    have hsep' := hsep (packing_vadd K S (-s) hpack)
      (imaginaryEmbedding x) hxS (imaginaryEmbedding y) hyS hxy'
    simpa only [imaginaryEmbedding_isometry.dist_eq] using hsep'
  have hYpack := packing_vadd K S (-s) hpack
  rw [hYeq] at hYpack
  obtain ⟨w, hw, hdist⟩ := horigin Y h0Y hYsep hYpack
  rw [← hYeq, regularSupport_vadd, properVertices_vadd_eq] at hw
  obtain ⟨v, hv, hvw⟩ := hw
  refine ⟨v, hv, ?_⟩
  have hdist' : dist ((-s) + v) 0 ≤ B := by
    rw [show -s + v = w from hvw]
    exact hdist
  have hvs : -s + v = v - s := by abel
  simpa only [hvs, dist_eq_norm, sub_zero] using hdist'

private theorem coordinateSwap_packing_iff (K : Region) (S : Set Tiling.Plane) :
    Tiling.IsPacking K.coordinateSwap.toPolygonalRegion.prototileFamily
      (K.coordinateSwap.toPolygonalRegion.placements (coordinateSwap '' S)) ↔
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
  rw [isPacking_iff_openCarrier_disjoint, isPacking_iff_openCarrier_disjoint]
  constructor
  · intro h s hs t ht hst
    have hst' : coordinateSwap s ≠ coordinateSwap t := fun heq ↦
      hst (coordinateSwap.injective heq)
    have hd := h ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ hst'
    change Disjoint (coordinateSwap s +ᵥ K.coordinateSwap.openCarrier)
      (coordinateSwap t +ᵥ K.coordinateSwap.openCarrier) at hd
    rw [coordinateSwap_openCarrier, ← coordinateSwap_image_vadd,
      ← coordinateSwap_image_vadd] at hd
    change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
    rw [Set.disjoint_left] at hd ⊢
    intro x hxs hxt
    exact hd ⟨x, hxs, rfl⟩ ⟨x, hxt, rfl⟩
  · intro h p hp q hq hpq
    obtain ⟨s, hs, rfl⟩ := hp
    obtain ⟨t, ht, rfl⟩ := hq
    have hst : s ≠ t := fun heq ↦ hpq (congrArg coordinateSwap heq)
    have hd := h hs ht hst
    change Disjoint (coordinateSwap s +ᵥ K.coordinateSwap.openCarrier)
      (coordinateSwap t +ᵥ K.coordinateSwap.openCarrier)
    rw [coordinateSwap_openCarrier, ← coordinateSwap_image_vadd,
      ← coordinateSwap_image_vadd, Set.disjoint_left]
    rintro x ⟨y, hy, hyx⟩ ⟨z, hz, hzx⟩
    have hyz : y = z := coordinateSwap.injective (hyx.trans hzx.symm)
    exact (Set.disjoint_left.mp hd) hy (hyz ▸ hz)

private theorem coordinateSwap_dist (x y : Tiling.Plane) :
    dist (coordinateSwap x) (coordinateSwap y) = dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← coordinateSwap.map_sub,
    Complex.norm_def, Complex.norm_def]
  congr 1
  simp only [Complex.normSq_apply, coordinateSwap_re, coordinateSwap_im]
  ring

private theorem column_swap_back
    {K : Region} {Col : Set Tiling.Plane}
    (hCol : IsCenterColumn Axis.vertical K.coordinateSwap Col) :
    IsCenterColumn Axis.horizontal K (coordinateSwap '' Col) := by
  have hpack := (coordinateSwap_packing_iff K (coordinateSwap '' Col)).mp (by
    simpa only [IntrinsicVertices.coordinateSwap_image_image] using hCol.1)
  have hsupport : regularSupport K (coordinateSwap '' Col) =
      coordinateSwap '' regularSupport K.coordinateSwap Col := by
    have hs := regularSupport_coordinateSwap K (coordinateSwap '' Col)
    rw [IntrinsicVertices.coordinateSwap_image_image] at hs
    have hs' := congrArg (coordinateSwap '' ·) hs
    simpa only [IntrinsicVertices.coordinateSwap_image_image] using hs'.symm
  refine ⟨hpack, hCol.2.1.image coordinateSwap, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := hCol.2.2.1
    refine ⟨c, ?_⟩
    rintro s ⟨t, ht, rfl⟩
    simpa only [Axis.transverseCoord, coordinateSwap_im] using hc t ht
  · intro a
    rw [hsupport]
    have hs := coordinateSwap_image_vadd ((a : ℂ) * Complex.I)
      (regularSupport K.coordinateSwap Col)
    have hswap : coordinateSwap ((a : ℂ) * Complex.I) = (a : ℂ) := by
      apply Complex.ext <;> simp
    rw [hswap] at hs
    rw [← hs, hCol.2.2.2 a]

private theorem boundaryStraight_coordinateSwap
    {D : Set Tiling.Plane} {x : Tiling.Plane}
    (h : Tiling.BoundaryLocallyStraightAt D x) :
    Tiling.BoundaryLocallyStraightAt (coordinateSwap '' D) (coordinateSwap x) := by
  obtain ⟨L, hx, hdim, hlocal⟩ := h
  let L' := L.map coordinateSwap.toLinearMap.toAffineMap
  refine ⟨L', AffineSubspace.mem_map_of_mem _ hx, ?_, ?_⟩
  · dsimp only [L']
    rw [AffineSubspace.map_direction]
    exact (coordinateSwap.toLinearEquiv.finrank_map_eq L.direction).trans hdim
  · have htend : Tendsto coordinateSwap (𝓝 (coordinateSwap x)) (𝓝 x) := by
      simpa only [coordinateSwap_apply_apply] using
        coordinateSwap.continuous.tendsto (coordinateSwap x)
    filter_upwards [hlocal.filter_mono htend] with y hy
    change coordinateSwap y ∈ frontier D ↔ coordinateSwap y ∈ L at hy
    have hfront : frontier (coordinateSwap '' D) =
        coordinateSwap '' frontier D :=
      (coordinateSwap.toHomeomorph.image_frontier D).symm
    rw [hfront]
    have hmem (S : Set Tiling.Plane) : y ∈ coordinateSwap '' S ↔
        coordinateSwap y ∈ S := by
      rw [← coordinateSwap_apply_apply y]
      exact coordinateSwap.injective.mem_set_image
    rw [hmem, hy]
    change coordinateSwap y ∈ L ↔ y ∈ L.map coordinateSwap.toLinearMap.toAffineMap
    rw [← coordinateSwap_apply_apply y]
    exact (AffineSubspace.mem_map_iff_mem_of_injective coordinateSwap.injective).symm

private theorem properVertices_coordinateSwap (D : Set Tiling.Plane) :
    properVertices (coordinateSwap '' D) = coordinateSwap '' properVertices D := by
  have hfrontEq : frontier (coordinateSwap '' D) = coordinateSwap '' frontier D :=
    (coordinateSwap.toHomeomorph.image_frontier D).symm
  have himage (S : Set Tiling.Plane) : coordinateSwap '' (coordinateSwap '' S) = S := by
    ext z
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      simpa only [coordinateSwap_apply_apply] using hv
    · intro hz
      exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩
  ext x
  constructor
  · intro hx
    refine ⟨coordinateSwap x, ?_, coordinateSwap_apply_apply x⟩
    change coordinateSwap x ∈ frontier D ∧
      ¬ Tiling.BoundaryLocallyStraightAt D (coordinateSwap x)
    constructor
    · have hfront := hx.1
      rw [hfrontEq] at hfront
      obtain ⟨y, hy, hyx⟩ := hfront
      have heq : y = coordinateSwap x := by
        rw [← hyx, coordinateSwap_apply_apply]
      exact heq ▸ hy
    · intro hs
      have hs' := boundaryStraight_coordinateSwap hs
      rw [coordinateSwap_apply_apply] at hs'
      exact hx.2 hs'
  · rintro ⟨y, hy, rfl⟩
    change coordinateSwap y ∈ frontier (coordinateSwap '' D) ∧
      ¬ Tiling.BoundaryLocallyStraightAt (coordinateSwap '' D) (coordinateSwap y)
    constructor
    · rw [hfrontEq]
      exact ⟨y, hy.1, rfl⟩
    · intro hs
      have hs' := boundaryStraight_coordinateSwap hs
      rw [himage, coordinateSwap_apply_apply] at hs'
      exact hy.2 hs'

private theorem nonColumnable_uniformNearby_vertical
    (K : Region)
    (hnoncol : ¬ ∃ Col : Set Plane, IsCenterColumn Axis.vertical K Col) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ S : Set Plane,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      (∃ c : ℝ, ∀ s ∈ S, Axis.vertical.transverseCoord s = c) →
      ∀ s ∈ S, ∃ w ∈ properVertices (regularSupport K S), dist w s ≤ B := by
  obtain ⟨δ, hδ, hsep⟩ := packingUniformSeparation K
  obtain ⟨B, hB, horigin⟩ := uniform_nearby_imaginary_origin
    (K := K) (δ := δ) hnoncol (pointedPackingCompactness hδ)
    (fun axis ↦ noProperVertices_isCenterColumn axis)
    properVertices_persist_pointedLimit
  refine ⟨B, hB, ?_⟩
  intro S hpack halign s hs
  exact uniform_nearby_every_center_of_origin_bound horigin
    (fun {T} hT ↦ hsep T hT) S s hpack hs halign

private theorem nonColumnable_uniformProperVertexLinked :
    ∀ (K : Region) (axis : Axis),
      (¬ ∃ Col : Set Plane, IsCenterColumn axis K Col) →
      ∃ ell : ℝ, 0 < ell ∧ ∀ S : Set Plane,
        Tiling.IsPacking K.toPolygonalRegion.prototileFamily
          (K.toPolygonalRegion.placements S) →
        S.Nonempty →
        (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
        Linked (60 * Metric.diam K.openCarrier) S →
        Linked ell (properVertices (regularSupport K S)) := by
  intro K axis hnoncol
  have hnearAxis : ∃ B : ℝ, 0 ≤ B ∧ ∀ S : Set Plane,
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements S) →
      (∃ c : ℝ, ∀ s ∈ S, axis.transverseCoord s = c) →
      ∀ s ∈ S, ∃ w ∈ properVertices (regularSupport K S), dist w s ≤ B := by
    cases axis with
    | vertical => exact nonColumnable_uniformNearby_vertical K hnoncol
    | horizontal =>
        have hnoncol' : ¬ ∃ Col : Set Plane,
            IsCenterColumn Axis.vertical K.coordinateSwap Col := by
          rintro ⟨Col, hCol⟩
          exact hnoncol ⟨coordinateSwap '' Col, column_swap_back hCol⟩
        obtain ⟨B, hB, hnear⟩ :=
          nonColumnable_uniformNearby_vertical K.coordinateSwap hnoncol'
        refine ⟨B, hB, ?_⟩
        intro S hpack halign s hs
        have hpack' := (coordinateSwap_packing_iff K S).2 hpack
        have halign' : ∃ c : ℝ, ∀ t ∈ coordinateSwap '' S,
            Axis.vertical.transverseCoord t = c := by
          obtain ⟨c, hc⟩ := halign
          refine ⟨c, ?_⟩
          rintro t ⟨u, hu, rfl⟩
          simpa only [Axis.transverseCoord, coordinateSwap_re] using hc u hu
        obtain ⟨w, hw, hdist⟩ := hnear (coordinateSwap '' S) hpack' halign'
          (coordinateSwap s) ⟨s, hs, rfl⟩
        rw [regularSupport_coordinateSwap, properVertices_coordinateSwap] at hw
        obtain ⟨v, hv, hvw⟩ := hw
        refine ⟨v, hv, ?_⟩
        rw [← hvw, coordinateSwap_dist] at hdist
        exact hdist
  obtain ⟨B₀, hB₀, hnear⟩ := hnearAxis
  obtain ⟨RK, hRK, hK⟩ := support_bound_for_callsite (K := K)
  let B : ℝ := max B₀ RK
  have hB : 0 ≤ B := hB₀.trans (le_max_left _ _)
  have hdiam : 0 < Metric.diam K.openCarrier := by
    rw [← Metric.diam_closure]
    change 0 < Metric.diam (closure (interior K.support))
    rw [K.isPolygonal.closure_interior]
    exact region_support_diam_pos K
  have hR : 0 < 60 * Metric.diam K.openCarrier := mul_pos (by norm_num) hdiam
  refine ⟨60 * Metric.diam K.openCarrier + 2 * B, by positivity, ?_⟩
  intro S hpack _hSne halign hlinked
  apply linked_of_twoSided_nearby hR hB hlinked
  · intro s hs
    obtain ⟨w, hw, hdist⟩ := hnear S hpack halign s hs
    exact ⟨w, hw, hdist.trans (le_max_left _ _)⟩
  · apply properVertex_provenance_near_source (Tiling.AxisParallel.properVertexProvenance hpack)
    intro v hv
    have hvfront := Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K hv
    rw [K.frontier_openCarrier_eq_frontier_support] at hvfront
    have hvsupport : v ∈ K.support :=
      K.isPolygonal.isClosed.closure_eq ▸ frontier_subset_closure hvfront
    exact (hK v hvsupport).trans (le_max_right _ _)


end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem transverseCoord_add (axis : Axis) (x y : Tiling.Plane) :
    axis.transverseCoord (x + y) = axis.transverseCoord x + axis.transverseCoord y := by
  cases axis <;> rfl

private theorem mapped_transverseVertexDifference
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (axis : Axis) (v w : ↥C.region.vertices) :
    mapScalar phi (transverseVertexDifferenceScalar C axis v w) =
      axis.transverseCoord (D.planarHomeomorph v.1) -
        axis.transverseCoord (D.planarHomeomorph w.1) := by
  rw [D.vertex_agreement v.1 v.2, D.vertex_agreement w.1 w.2]
  cases axis <;>
    simp only [transverseVertexDifferenceScalar, Axis.transverseCoord,
      mapPoint, mapScalar, ApproximationContext.vertexPoint,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero]
  all_goals
    norm_cast
    rw [← map_sub]
    rfl

private theorem mapped_centres_transverse_eq_of_alignedOrigins
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (O : AlignedCompleteLineOrigins C axis S hSource) (s t : S) :
    axis.transverseCoord (Tphi s.1) = axis.transverseCoord (Tphi t.1) := by
  have hcoord : axis.transverseCoord s.1.1 = axis.transverseCoord t.1.1 :=
    (O.centres_aligned s).trans (O.centres_aligned t).symm
  rw [hTphi s.1, hTphi t.1]
  cases axis <;>
    simp only [Axis.transverseCoord, mapPoint, mapScalar,
      ApproximationContext.centrePoint, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, sub_zero]
  all_goals
    congr 2
    exact Subtype.ext hcoord

private theorem completeLine_from_transportedFootprint
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (hdiam : Metric.diam C.region.support < P.controlRadius)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S₀ S₁ : Set ↥C.centres)
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
    (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
    (eta : Tiling.Plane)
    (V : ProperVertexTranslation C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta)
    (hne : (properVertices
      (regularSupport C.region (Subtype.val '' S₀))).Nonempty)
    (O₀ : AlignedCompleteLineOrigins C axis S₀ hSource₀)
    (O₁ : AlignedCompleteLineOrigins C axis S₁ hSource₁)
    (L₀ : ↥(completeBoundaryLines _ hSource₀))
    (L₁ : ↥(completeBoundaryLines _ hSource₁))
    (hImage : (B₁.completeLineEquiv L₁).1 =
      (B₀.completeLineEquiv L₀).1.vadd eta) :
    L₁.1 = L₀.1.vadd V.beta.1 := by
  classical
  obtain ⟨x, hx⟩ := hne
  let x₀ : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))) := ⟨x, hx⟩
  let x₁ := V.sourceEquiv x₀
  obtain ⟨v₀, t₀, hv₀⟩ := B₀.source_provenance x₀
  obtain ⟨v₁, t₁, hv₁⟩ := B₁.source_provenance x₁
  have hbeta : axis.transverseCoord V.beta.1 =
      axis.transverseCoord v₁.1 - axis.transverseCoord v₀.1 +
        O₁.centreLevel - O₀.centreLevel := by
    have h := congrArg axis.transverseCoord (V.source_formula x₀)
    rw [hv₀, hv₁, transverseCoord_add, transverseCoord_add,
      transverseCoord_add, O₀.centres_aligned t₀, O₁.centres_aligned t₁] at h
    linarith
  have hanchor := congrArg axis.transverseCoord (V.image_formula x₀)
  rw [B₀.target_formula x₀ v₀ t₀ hv₀,
    B₁.target_formula x₁ v₁ t₁ hv₁,
    transverseCoord_add, transverseCoord_add, transverseCoord_add] at hanchor
  have hline := congrArg CompleteBoundaryLine.level hImage
  simp only [CompleteBoundaryLine.vadd] at hline
  rw [mappedCompleteLineLevel_fromOrigin phi D Tphi hTphi axis S₀
    hSource₀ hTarget₀ B₀ O₀ L₀,
    mappedCompleteLineLevel_fromOrigin phi D Tphi hTphi axis S₁
    hSource₁ hTarget₁ B₁ O₁ L₁,
    B₀.completeLine_axis, O₀.completeLine_axis,
    transverseCoord_add, transverseCoord_add,
    mapped_centres_transverse_eq_of_alignedOrigins phi Tphi hTphi axis S₀
      hSource₀ O₀ O₀.anchor t₀,
    mapped_centres_transverse_eq_of_alignedOrigins phi Tphi hTphi axis S₁
      hSource₁ O₁ O₁.anchor t₁] at hline
  have hmap : mapScalar phi (transverseVertexDifferenceScalar C axis
      (O₁.completeLineVertex L₁) (O₀.completeLineVertex L₀)) =
      mapScalar phi (transverseVertexDifferenceScalar C axis v₁ v₀) := by
    rw [mapped_transverseVertexDifference phi D axis,
      mapped_transverseVertexDifference phi D axis]
    linarith
  have hlevels := finiteFootprintDifference_reflected P phi hphi axis
    (O₁.completeLineVertex L₁) (O₀.completeLineVertex L₀) v₁ v₀
    (transverseVertexDifference_mem_scalarAlphabet P hdiam axis _ _)
    (transverseVertexDifference_mem_scalarAlphabet P hdiam axis _ _) hmap
  have hlevel : L₁.1.level = (L₀.1.vadd V.beta.1).level := by
    simp only [CompleteBoundaryLine.vadd, O₀.completeLine_axis]
    rw [O₀.completeLine_origin, O₁.completeLine_origin]
    linarith
  have hside := congrArg CompleteBoundaryLine.insideOnPositiveSide hImage
  simp only [CompleteBoundaryLine.vadd] at hside
  rw [B₀.completeLine_insideSide, B₁.completeLine_insideSide] at hside
  cases L₀ with
  | mk l₀ hl₀ =>
      cases L₁ with
      | mk l₁ hl₁ =>
          cases l₀
          cases l₁
          simp only [CompleteBoundaryLine.vadd] at hlevel hside ⊢
          have ha₀ := O₀.completeLine_axis ⟨_, hl₀⟩
          have ha₁ := O₁.completeLine_axis ⟨_, hl₁⟩
          cases ha₀
          cases ha₁
          cases hlevel
          cases hside
          rfl

private theorem completeLineFootprint_of_properVertexTranslation :
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    Metric.diam C.region.support < P.controlRadius →
    ∀ (D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (S₀ S₁ : Set ↥C.centres)
      (hSource₀ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₀)))
      (hSource₁ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₁)))
      (hTarget₀ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
      (hTarget₁ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
      (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
      (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
      (eta : Tiling.Plane),
      regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
        eta +ᵥ regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S₀) →
    ∀ (V : ProperVertexTranslation C phi D Tphi S₀ S₁
        hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta),
      (properVertices
        (regularSupport C.region (Subtype.val '' S₀))).Nonempty →
    ∀ (_O₀ : AlignedCompleteLineOrigins C axis S₀ hSource₀)
      (_O₁ : AlignedCompleteLineOrigins C axis S₁ hSource₁),
      (boundaryCode (regularSupport C.region
        (Subtype.val '' S₁)) hSource₁).completeLines =
          ((boundaryCode (regularSupport C.region
            (Subtype.val '' S₀)) hSource₀).vadd V.beta).completeLines ∧
        regularSupport C.region (Subtype.val '' S₁) =
          V.beta.1 +ᵥ regularSupport C.region (Subtype.val '' S₀) := by
  intro C P phi hphi hdiam D Tphi hTphi axis S₀ S₁ hSource₀ hSource₁
    hTarget₀ hTarget₁ B₀ B₁ eta hTargetEq V hne O₀ O₁
  classical
  have htargetLines := (translatedBoundaryData hTarget₀ hTarget₁ eta hTargetEq).1
  have hlines : completeBoundaryLines _ hSource₁ =
      (fun L ↦ L.vadd V.beta.1) '' completeBoundaryLines _ hSource₀ := by
    apply Set.Subset.antisymm
    · intro l₁ hl₁
      let L₁ : ↥(completeBoundaryLines _ hSource₁) := ⟨l₁, hl₁⟩
      have htarget : (B₁.completeLineEquiv L₁).1 ∈
          (fun L ↦ L.vadd eta) '' completeBoundaryLines _ hTarget₀ := by
        simpa only [htargetLines] using (B₁.completeLineEquiv L₁).2
      obtain ⟨k₀, hk₀, hshift⟩ := htarget
      let L₀ := B₀.completeLineEquiv.symm ⟨k₀, hk₀⟩
      have hImage : (B₁.completeLineEquiv L₁).1 =
          (B₀.completeLineEquiv L₀).1.vadd eta := by
        simpa only [L₀, Equiv.apply_symm_apply] using hshift.symm
      have hsource := completeLine_from_transportedFootprint P phi hphi hdiam
        D Tphi hTphi axis S₀ S₁ hSource₀ hSource₁ hTarget₀ hTarget₁
        B₀ B₁ eta V hne O₀ O₁ L₀ L₁ hImage
      exact ⟨L₀.1, L₀.2, hsource.symm⟩
    · rintro l₁ ⟨l₀, hl₀, rfl⟩
      let L₀ : ↥(completeBoundaryLines _ hSource₀) := ⟨l₀, hl₀⟩
      have htarget : (B₀.completeLineEquiv L₀).1.vadd eta ∈
          completeBoundaryLines _ hTarget₁ := by
        rw [htargetLines]
        exact ⟨_, (B₀.completeLineEquiv L₀).2, rfl⟩
      let L₁ := B₁.completeLineEquiv.symm ⟨_, htarget⟩
      have hImage : (B₁.completeLineEquiv L₁).1 =
          (B₀.completeLineEquiv L₀).1.vadd eta := by
        simp only [L₁, Equiv.apply_symm_apply]
      have hsource := completeLine_from_transportedFootprint P phi hphi hdiam
        D Tphi hTphi axis S₀ S₁ hSource₀ hSource₁ hTarget₀ hTarget₁
        B₀ B₁ eta V hne O₀ O₁ L₀ L₁ hImage
      simpa only [hsource] using L₁.2
  have hvertices : properVertices (regularSupport C.region (Subtype.val '' S₁)) =
      V.beta.1 +ᵥ properVertices (regularSupport C.region (Subtype.val '' S₀)) := by
    ext x
    constructor
    · intro hx
      let y := V.sourceEquiv.symm ⟨x, hx⟩
      refine ⟨y.1, y.2, ?_⟩
      simpa only [y, Equiv.apply_symm_apply, vadd_eq_add] using (V.source_formula y).symm
    · rintro ⟨y, hy, rfl⟩
      simpa only [V.source_formula, vadd_eq_add] using (V.sourceEquiv ⟨y, hy⟩).2
  have hcones : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))),
      localCone _ (V.sourceEquiv x).1 hSource₁ (V.sourceEquiv x).2 =
        localCone _ x.1 hSource₀ x.2 := by
    intro x
    have hximage : eta + (B₀.properVertexEquiv x).1 ∈ properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)) := by
      rw [← V.image_formula x]
      exact (B₁.properVertexEquiv (V.sourceEquiv x)).2
    have hcone := (translatedBoundaryData hTarget₀ hTarget₁ eta hTargetEq).2
      (B₀.properVertexEquiv x).1 (B₀.properVertexEquiv x).2 hximage
    calc
      _ = localCone _ (B₁.properVertexEquiv (V.sourceEquiv x)).1 hTarget₁
          (B₁.properVertexEquiv (V.sourceEquiv x)).2 := B₁.cone_preserved _
      _ = localCone _ (B₀.properVertexEquiv x).1 hTarget₀
          (B₀.properVertexEquiv x).2 := by
        simpa only [localCone, V.image_formula x] using hcone
      _ = _ := (B₀.cone_preserved x).symm
  have hconeGraph : (boundaryCode _ hSource₁).coneGraph =
      ((boundaryCode _ hSource₀).vadd V.beta.1).coneGraph := by
    ext p
    rcases p with ⟨x, cone⟩
    constructor
    · rintro ⟨hx, hcone⟩
      have hxbeta : x ∈ V.beta.1 +ᵥ properVertices
          (regularSupport C.region (Subtype.val '' S₀)) := by
        rw [← hvertices]
        exact hx
      refine ⟨hxbeta, ?_⟩
      obtain ⟨y, hy, hxy⟩ := hxbeta
      have hsource := V.source_formula ⟨y, hy⟩
      have hxsource : (V.sourceEquiv ⟨y, hy⟩).1 = x := hsource.trans hxy
      have h : localCone _ x hSource₁ hx = localCone _ y hSource₀ hy := by
        simpa only [localCone, hxsource] using hcones ⟨y, hy⟩
      dsimp only [boundaryCode, BoundaryCode.vadd] at hcone ⊢
      have hsub : x - V.beta.1 = y := by
        change V.beta.1 + y = x at hxy
        rw [← hxy]
        abel
      simpa only [localCone, hsub] using hcone.trans h
    · rintro ⟨hx, hcone⟩
      have hxproper : x ∈ properVertices
          (regularSupport C.region (Subtype.val '' S₁)) := by
        rw [hvertices]
        exact hx
      refine ⟨hxproper, ?_⟩
      obtain ⟨y, hy, hxy⟩ := hx
      have hsource := V.source_formula ⟨y, hy⟩
      have hxsource : (V.sourceEquiv ⟨y, hy⟩).1 = x := hsource.trans hxy
      have h : localCone _ y hSource₀ hy = localCone _ x hSource₁ hxproper := by
        simpa only [localCone, hxsource] using (hcones ⟨y, hy⟩).symm
      dsimp only [boundaryCode, BoundaryCode.vadd] at hcone ⊢
      have hsub : x - V.beta.1 = y := by
        change V.beta.1 + y = x at hxy
        rw [← hxy]
        abel
      have hcone' : cone = localCone _ y hSource₀ hy := by
        simpa only [localCone, hsub] using hcone
      exact hcone'.trans h
  obtain ⟨x, hx⟩ := hne
  have hx₁ := (V.sourceEquiv ⟨x, hx⟩).2
  have hF₀ne : (regularSupport C.region (Subtype.val '' S₀)).Nonempty :=
    Set.Nonempty.of_closure ⟨x, frontier_subset_closure hx.1⟩
  have hF₁ne : (regularSupport C.region (Subtype.val '' S₁)).Nonempty :=
    Set.Nonempty.of_closure ⟨_, frontier_subset_closure hx₁.1⟩
  have hF₀proper : regularSupport C.region (Subtype.val '' S₀) ≠ univ := by
    intro h
    have hf := hx.1
    simp only [h, frontier_univ, Set.mem_empty_iff_false] at hf
  have hF₁proper : regularSupport C.region (Subtype.val '' S₁) ≠ univ := by
    intro h
    have hf := hx₁.1
    simp only [h, frontier_univ, Set.mem_empty_iff_false] at hf
  refine ⟨hlines, boundaryCodeComponents_reconstructTranslation hSource₀ hSource₁
    V.beta.1 hF₀ne hF₁ne hF₀proper hF₁proper hvertices hconeGraph hlines⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- The source-first maximum already activates the published A06 cone margin. -/
private theorem t06RecoveryScale_incidenceMargin
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (ell delta : ℝ) (N : ℕ)
    (hscale : t06RecoveryScale C.region ell delta
      (60 * Metric.diam C.region.openCarrier) N < P.scale) :
    10 * (Metric.diam C.region.openCarrier + 1) < P.scale := by
  have heq : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
    change Metric.diam C.region.support = Metric.diam (interior C.region.support)
    nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  simp only [t06RecoveryScale, max_lt_iff] at hscale
  rcases hscale with ⟨⟨_, _, _, hG, _, _⟩, hrecip⟩
  rw [heq] at hrecip
  have hD : 0 < Metric.diam C.region.openCarrier := region_openCarrier_diam_pos C.region
  have hproduct : 2 < P.scale * Metric.diam C.region.openCarrier :=
    (div_lt_iff₀ hD).mp hrecip
  by_cases hsmall : Metric.diam C.region.openCarrier < (1 : ℝ) / 10
  · by_contra hnot
    have hupper : P.scale ≤ 10 * (Metric.diam C.region.openCarrier + 1) :=
      le_of_not_gt hnot
    have hscale11 : P.scale < 11 := by linarith
    nlinarith [P.scale_pos]
  · have hlarge := le_of_not_gt hsmall
    linarith

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.IntrinsicVertices

private def axisPoint (axis : Axis) (transverse along : ℝ) : Tiling.Plane :=
  match axis with
  | .horizontal => (along : ℂ) + (transverse : ℂ) * Complex.I
  | .vertical => (transverse : ℂ) + (along : ℂ) * Complex.I

private theorem alignedCompleteLineOrigins_construct
    {C : ApproximationContext.{0}} (axis : Axis)
    (S : Set ↥C.centres)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hS : S.Nonempty) (sourceLevel : ℝ)
    (halign : ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel) :
    Nonempty (AlignedCompleteLineOrigins C axis S hSource) := by
  classical
  let anchor : S := ⟨hS.choose, hS.choose_spec⟩
  have hlevelMem : sourceLevel ∈ C.coordinateSpace := by
    cases axis with
    | horizontal =>
        rw [← halign anchor]
        exact C.centre_im_mem anchor.1.1 anchor.1.2
    | vertical =>
        rw [← halign anchor]
        exact C.centre_re_mem anchor.1.1 anchor.1.2
  have hproj := Tiling.AxisParallel.regularSupportTransverseProjection_bounded
    axis (K := C.region) (S := Subtype.val '' S) ⟨sourceLevel, by
      rintro x ⟨s, hs, rfl⟩
      exact halign ⟨s, hs⟩⟩
  have hVFinite : C.region.vertices.Finite := by
    rw [← C.region.coe_vertexFinset]
    exact C.region.vertexFinset.finite_toSet
  have hImageCountable : Countable ↥(Subtype.val '' S) :=
    (Tiling.AxisParallel.IsPacking.locallyFinite_centres hPacking).2.to_subtype
  have hSCountable : Countable S := by
    let f : S → ↥(Subtype.val '' S) :=
      fun s => ⟨s.1.1, ⟨s.1, s.2, rfl⟩⟩
    have hf : Function.Injective f := by
      intro s t hst
      have hplane : s.1.1 = t.1.1 :=
        congrArg (fun q : ↥(Subtype.val '' S) => q.1) hst
      apply Subtype.ext
      exact Subtype.ext hplane
    exact @Function.Injective.countable S ↥(Subtype.val '' S) hImageCountable f hf
  let _ : Countable S := hSCountable
  let _ : Countable ↥C.region.vertices := hVFinite.countable.to_subtype
  let bad : Set ℝ := Set.range fun p : S × ↥C.region.vertices =>
    axis.coord p.2.1 + axis.coord p.1.1.1
  have hbad : bad.Countable := Set.countable_range _
  have hbadNe : bad ≠ Set.univ := by
    intro h
    have hcount : Countable ℝ := by
      let f : ℝ → ↥bad := fun x => ⟨x, by rw [h]; exact Set.mem_univ x⟩
      have hf : Function.Injective f := by
        intro x y hxy
        exact congrArg Subtype.val hxy
      exact @Function.Injective.countable ℝ ↥bad hbad.to_subtype f hf
    exact (not_countable : ¬ Countable ℝ) hcount
  obtain ⟨along, halong⟩ := (Set.ne_univ_iff_exists_notMem _).mp hbadNe
  have hLineAxis (L : ↥(completeBoundaryLines _ hSource)) : L.1.axis = axis := by
    by_contra hne
    let lineAxis := L.1.axis
    have hswap : L.1.axis = axis.swap := by
      cases axis with
      | horizontal =>
          cases hlineAxis : lineAxis with
          | horizontal => exact (hne (by simpa [lineAxis] using hlineAxis)).elim
          | vertical => simpa [lineAxis, Axis.swap] using hlineAxis
      | vertical =>
          cases hlineAxis : lineAxis with
          | horizontal => simpa [lineAxis, Axis.swap] using hlineAxis
          | vertical => exact (hne (by simpa [lineAxis] using hlineAxis)).elim
    obtain ⟨R, hR⟩ := hproj.subset_closedBall 0
    let z := axisPoint axis (R + 1) L.1.level
    have hzLine : z ∈ L.1.carrier := by
      change L.1.axis.transverseCoord z = L.1.level
      rw [hswap]
      cases axis <;> simp [z, axisPoint, Axis.transverseCoord, Axis.swap]
    have hzFront : z ∈ frontier (regularSupport C.region (Subtype.val '' S)) := by
      have hzFront := L.2.1 hzLine
      exact hzFront
    have hzClosed : z ∈ closure (regularSupport C.region (Subtype.val '' S)) := hzFront.1
    have hprojClosed : IsClosed
        (axis.transverseCoord ⁻¹' Metric.closedBall (0 : ℝ) R) := by
      cases axis <;> simp only [Axis.transverseCoord]
      · exact (Metric.isClosed_closedBall.preimage Complex.continuous_im)
      · exact (Metric.isClosed_closedBall.preimage Complex.continuous_re)
    have hprojSubset : regularSupport C.region (Subtype.val '' S) ⊆
        axis.transverseCoord ⁻¹' Metric.closedBall (0 : ℝ) R := by
      intro x hx
      exact hR ⟨x, hx, rfl⟩
    have hzBound := closure_minimal hprojSubset hprojClosed hzClosed
    have hzCoord : axis.transverseCoord z = R + 1 := by
      cases axis <;> simp [z, axisPoint, Axis.transverseCoord]
    change axis.transverseCoord z ∈ Metric.closedBall (0 : ℝ) R at hzBound
    rw [hzCoord, Metric.mem_closedBall, Real.dist_eq] at hzBound
    simp only [sub_zero] at hzBound
    have : R + 1 ≤ |R + 1| := le_abs_self _
    linarith
  have hOriginExists (L : ↥(completeBoundaryLines _ hSource)) :
      ∃ v : ↥C.region.vertices,
        L.1.level = axis.transverseCoord v.1 + sourceLevel := by
    let z := axisPoint axis L.1.level along
    have hzLine : z ∈ L.1.carrier := by
      rw [CompleteBoundaryLine.carrier, hLineAxis L]
      cases axis <;> simp [z, axisPoint, Axis.transverseCoord]
    have hzFront : z ∈ frontier (regularSupport C.region (Subtype.val '' S)) :=
      L.2.1 hzLine
    have hzClosure : z ∈ closure (openUnion C.region (Subtype.val '' S)) := by
      have hFsub : regularSupport C.region (Subtype.val '' S) ⊆
          closure (openUnion C.region (Subtype.val '' S)) := by
        change interior (closure (openUnion C.region (Subtype.val '' S))) ⊆
          closure (openUnion C.region (Subtype.val '' S))
        exact interior_subset
      simpa only [closure_closure] using closure_mono hFsub hzFront.1
    rw [closure_openUnion_eq_iUnion_support hPacking] at hzClosure
    rcases Set.mem_iUnion.mp hzClosure with ⟨sImg, hzTile⟩
    rcases sImg.property with ⟨s, hsS, hsEq⟩
    change (s : Tiling.Plane) = sImg.1 at hsEq
    rw [← hsEq] at hzTile
    let s : S := ⟨s, hsS⟩
    have hzNotF : z ∉ regularSupport C.region (Subtype.val '' S) := by
      rw [frontier, hSource.1.interior_eq] at hzFront
      exact hzFront.2
    have hzNotInterior : z ∉ interior (s.1.1 +ᵥ C.region.support) := by
      intro hInterior
      have hTileSubset : (s.1.1 : Tiling.Plane) +ᵥ C.region.support ⊆
          closure (openUnion C.region (Subtype.val '' S)) := by
        rw [closure_openUnion_eq_iUnion_support hPacking]
        exact Set.subset_iUnion (fun t : ↥(Subtype.val '' S) =>
          (t.1 : Tiling.Plane) +ᵥ C.region.support)
          ⟨s.1.1, ⟨s.1, s.2, rfl⟩⟩
      have hInteriorF : z ∈ interior (regularSupport C.region (Subtype.val '' S)) := by
        simpa [regularSupport, Tiling.Polygonal.regularSupport,
          ← openUnion.eq_def] using interior_mono hTileSubset hInterior
      exact hzNotF (by simpa [regularSupport, Tiling.Polygonal.regularSupport,
        ← openUnion.eq_def] using hInteriorF)
    have hzTileFront : z ∈ frontier (s.1.1 +ᵥ C.region.support) := by
      rw [(C.region.isPolygonal.vadd s.1.1).isClosed.frontier_eq]
      exact ⟨hzTile, hzNotInterior⟩
    have hzSourceFront : z - s.1.1 ∈ frontier C.region.support := by
      simpa only [Tiling.AxisParallel.frontier_vadd_eq,
        Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hzTileFront
    have hgrid := frontier_subset_vertexCoordinateGrid C.region hzSourceFront
    cases axis with
    | horizontal =>
        rcases hgrid with hRe | hIm
        · rcases hRe with ⟨v, hv, hcoord⟩
          have hBad : along ∈ bad := by
            refine ⟨(s, ⟨v, hv⟩), ?_⟩
            have hAlong : z.re = along := by simp [z, axisPoint]
            have hcoord' : z.re - s.1.1.re = v.re := by
              simpa [Complex.sub_re] using hcoord
            have hEq : Axis.horizontal.coord v + Axis.horizontal.coord s.1.1 = along := by
              simpa [Axis.coord] using (by linarith : v.re + s.1.1.re = along)
            exact hEq
          exact (halong hBad).elim
        · rcases hIm with ⟨v, hv, hcoord⟩
          refine ⟨⟨v, hv⟩, ?_⟩
          have hline := hzLine
          rw [CompleteBoundaryLine.carrier, hLineAxis L] at hline
          change (z.im = L.1.level) at hline
          have hcoord' : z.im - s.1.1.im = v.im := by
            simpa [Complex.sub_im] using hcoord
          have hcenter : s.1.1.im = sourceLevel := by
            simpa [Axis.transverseCoord] using halign s
          have hsum : z.im = v.im + sourceLevel := by linarith
          rw [hsum] at hline
          simpa [Axis.transverseCoord, add_comm] using hline.symm
    | vertical =>
        rcases hgrid with hRe | hIm
        · rcases hRe with ⟨v, hv, hcoord⟩
          refine ⟨⟨v, hv⟩, ?_⟩
          have hline := hzLine
          rw [CompleteBoundaryLine.carrier, hLineAxis L] at hline
          change (z.re = L.1.level) at hline
          have hcoord' : z.re - s.1.1.re = v.re := by
            simpa [Complex.sub_re] using hcoord
          have hcenter : s.1.1.re = sourceLevel := by
            simpa [Axis.transverseCoord] using halign s
          have hsum : z.re = v.re + sourceLevel := by linarith
          rw [hsum] at hline
          simpa [Axis.transverseCoord, add_comm] using hline.symm
        · rcases hIm with ⟨v, hv, hcoord⟩
          have hBad : along ∈ bad := by
            refine ⟨(s, ⟨v, hv⟩), ?_⟩
            have hAlong : z.im = along := by simp [z, axisPoint]
            have hcoord' : z.im - s.1.1.im = v.im := by
              simpa [Complex.sub_im] using hcoord
            have hEq : Axis.vertical.coord v + Axis.vertical.coord s.1.1 = along := by
              simpa [Axis.coord] using (by linarith : v.im + s.1.1.im = along)
            exact hEq
          exact (halong hBad).elim
  choose vertex hvertex using hOriginExists
  exact ⟨{
    anchor := anchor
    centreLevel := sourceLevel
    centreLevel_mem := hlevelMem
    centres_aligned := halign
    completeLine_axis := hLineAxis
    completeLineVertex := vertex
    completeLine_origin := fun L => hvertex L
  }⟩

private theorem alignedCompleteLineOrigins_fromEngine
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (G : ℝ)
    (hLinked : Linked G (Subtype.val '' S)) (hG : G < P.scale)
    (hImageAligned : ∃ imageLevel : ℝ,
      ∀ s : S, axis.transverseCoord (Tphi s.1) = imageLevel)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S))) :
    Nonempty (AlignedCompleteLineOrigins C axis S hSource) := by
  obtain ⟨sourceLevel, hSourceAligned⟩ :=
    sourceAxisAligned_of_imageAxisAligned P phi hphi Tphi hTphi axis S G
      hLinked hG hImageAligned
  obtain ⟨x, s, hs, rfl⟩ := hLinked.1
  exact alignedCompleteLineOrigins_construct axis S hPacking hSource
    ⟨s, hs⟩ sourceLevel hSourceAligned

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem properVertexTranslation_construct
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres) (ell : ℝ)
    (hLinked : Linked ell (properVertices
      (regularSupport C.region (Subtype.val '' S₀))))
    (hMargin : ell + 2 * P.localError < P.scale / 2)
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (B₀ : AxisBoundaryCodeTransport C phi D Tphi S₀ hSource₀ hTarget₀)
    (B₁ : AxisBoundaryCodeTransport C phi D Tphi S₁ hSource₁ hTarget₁)
    (eta : Tiling.Plane)
    (hTargetSupport : regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi S₁) =
      eta +ᵥ regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)) :
    Nonempty (ProperVertexTranslation C phi D Tphi S₀ S₁
      hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta) := by
  classical
  let F₀ : Set Tiling.Plane :=
    regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)
  let F₁ : Set Tiling.Plane :=
    regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)
  have hProper : properVertices F₁ = eta +ᵥ properVertices F₀ := by
    dsimp [F₀, F₁]
    rw [hTargetSupport, properVertices_vadd_eq]
  let translate : ↥(properVertices F₀) ≃ ↥(properVertices F₁) := {
    toFun := fun x => ⟨eta + x.1, by
      rw [hProper]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp [x.2]⟩
    invFun := fun y => ⟨y.1 - eta, by
      have hy : y.1 ∈ eta +ᵥ properVertices F₀ := by
        rw [← hProper]
        exact y.2
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hy⟩
    left_inv := fun x => by
      apply Subtype.ext
      simp
    right_inv := fun y => by
      apply Subtype.ext
      simp
  }
  let sourceEquiv := B₀.properVertexEquiv.trans
    (translate.trans B₁.properVertexEquiv.symm)
  have hThetaImage (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀)))) :
      (B₁.properVertexEquiv (sourceEquiv x)).1 =
        eta + (B₀.properVertexEquiv x).1 := by
    simp only [sourceEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
    change (translate (B₀.properVertexEquiv x)).1 = _
    rfl
  obtain ⟨x₀, hx₀⟩ := hLinked.1
  let anchor : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))) := ⟨x₀, hx₀⟩
  let y₀ := sourceEquiv anchor
  obtain ⟨v₀, t₀, h₀⟩ := B₀.source_provenance anchor
  obtain ⟨v₁, t₁, h₁⟩ := B₁.source_provenance y₀
  let beta : ControlledDisplacement C := by
    refine ⟨y₀.1 - anchor.1, ?_, ?_⟩
    · rw [h₁, h₀]
      exact C.coordinateSpace.sub_mem
        (C.coordinateSpace.add_mem (C.vertex_re_mem v₁.1 v₁.2)
          (C.centre_re_mem t₁.1.1 t₁.1.2))
        (C.coordinateSpace.add_mem (C.vertex_re_mem v₀.1 v₀.2)
          (C.centre_re_mem t₀.1.1 t₀.1.2))
    · rw [h₁, h₀]
      exact C.coordinateSpace.sub_mem
        (C.coordinateSpace.add_mem (C.vertex_im_mem v₁.1 v₁.2)
          (C.centre_im_mem t₁.1.1 t₁.1.2))
        (C.coordinateSpace.add_mem (C.vertex_im_mem v₀.1 v₀.2)
          (C.centre_im_mem t₀.1.1 t₀.1.2))
  let translatedWitness (v : ↥C.region.vertices) (t : ↥C.centres) :
      ↥C.translatedVertices :=
    ⟨v.1 + t.1, ⟨v.1, v.2, t.1, t.2, rfl⟩⟩
  have hMapped0 (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀))))
      (v : ↥C.region.vertices) (t : {s : ↥C.centres // s ∈ S₀})
      (hx : x.1 = v.1 + t.1.1) :
      mapTranslatedVertex phi (translatedWitness v t.1) =
        (B₀.properVertexEquiv x).1 := by
    have hpt : C.translatedVertexPoint (translatedWitness v t.1) =
        ⟨v.1 + t.1.1, C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem t.1.1 t.1.2),
          C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2)
          (C.centre_im_mem t.1.1 t.1.2)⟩ := by
      apply Subtype.ext
      rfl
    calc
      mapTranslatedVertex phi (translatedWitness v t.1) =
          mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint t.1.1 t.1.2) := by
        rw [mapTranslatedVertex, hpt]
        exact mapPoint_add_local phi (C.vertexPoint v.1 v.2)
          (C.centrePoint t.1.1 t.1.2)
      _ = D.planarHomeomorph v.1 + Tphi t.1 := by
        rw [← D.vertex_agreement v.1 v.2, ← hTphi t.1]
      _ = (B₀.properVertexEquiv x).1 := (B₀.target_formula x v t hx).symm
  have hMapped1 (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₁))))
      (v : ↥C.region.vertices) (t : {s : ↥C.centres // s ∈ S₁})
      (hx : x.1 = v.1 + t.1.1) :
      mapTranslatedVertex phi (translatedWitness v t.1) =
        (B₁.properVertexEquiv x).1 := by
    have hpt : C.translatedVertexPoint (translatedWitness v t.1) =
        ⟨v.1 + t.1.1, C.coordinateSpace.add_mem (C.vertex_re_mem v.1 v.2)
          (C.centre_re_mem t.1.1 t.1.2),
          C.coordinateSpace.add_mem (C.vertex_im_mem v.1 v.2)
          (C.centre_im_mem t.1.1 t.1.2)⟩ := by
      apply Subtype.ext
      rfl
    calc
      mapTranslatedVertex phi (translatedWitness v t.1) =
          mapPoint phi (C.vertexPoint v.1 v.2) +
            mapPoint phi (C.centrePoint t.1.1 t.1.2) := by
        rw [mapTranslatedVertex, hpt]
        exact mapPoint_add_local phi (C.vertexPoint v.1 v.2)
          (C.centrePoint t.1.1 t.1.2)
      _ = D.planarHomeomorph v.1 + Tphi t.1 := by
        rw [← D.vertex_agreement v.1 v.2, ← hTphi t.1]
      _ = (B₁.properVertexEquiv x).1 := (B₁.target_formula x v t hx).symm
  let anchorPoint : ControlledDisplacement C := by
    refine ⟨anchor.1, ?_, ?_⟩
    · rw [h₀]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v₀.1 v₀.2)
        (C.centre_re_mem t₀.1.1 t₀.1.2)
    · rw [h₀]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₀.1 v₀.2)
        (C.centre_im_mem t₀.1.1 t₀.1.2)
  let targetAnchorPoint : ControlledDisplacement C := by
    refine ⟨y₀.1, ?_, ?_⟩
    · rw [h₁]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v₁.1 v₁.2)
        (C.centre_re_mem t₁.1.1 t₁.1.2)
    · rw [h₁]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₁.1 v₁.2)
        (C.centre_im_mem t₁.1.1 t₁.1.2)
  have hBetaAdd :
      (⟨beta.1 + anchorPoint.1,
        C.coordinateSpace.add_mem beta.2.1 anchorPoint.2.1,
        C.coordinateSpace.add_mem beta.2.2 anchorPoint.2.2⟩ : ControlledDisplacement C) =
      targetAnchorPoint := by
    apply Subtype.ext
    simp [beta, anchorPoint, targetAnchorPoint]
  have hMapBeta : mapPoint phi beta = eta := by
    have hadd := mapPoint_add_local phi beta anchorPoint
    have hlabel₀ := hMapped0 anchor v₀ t₀ h₀
    have hlabel₁ := hMapped1 y₀ v₁ t₁ h₁
    have hpoint₀ : C.translatedVertexPoint (translatedWitness v₀ t₀.1) =
        anchorPoint := by
      apply Subtype.ext
      exact h₀.symm
    have hpoint₁ : C.translatedVertexPoint (translatedWitness v₁ t₁.1) =
        targetAnchorPoint := by
      apply Subtype.ext
      exact h₁.symm
    have hlabel₀' : mapPoint phi anchorPoint =
        (B₀.properVertexEquiv anchor).1 := by
      calc
        mapPoint phi anchorPoint =
            mapPoint phi (C.translatedVertexPoint (translatedWitness v₀ t₀.1)) := by
              rw [hpoint₀]
        _ = mapTranslatedVertex phi (translatedWitness v₀ t₀.1) := rfl
        _ = (B₀.properVertexEquiv anchor).1 := hlabel₀
    have hlabel₁' : mapPoint phi targetAnchorPoint =
        (B₁.properVertexEquiv y₀).1 := by
      calc
        mapPoint phi targetAnchorPoint =
            mapPoint phi (C.translatedVertexPoint (translatedWitness v₁ t₁.1)) := by
              rw [hpoint₁]
        _ = mapTranslatedVertex phi (translatedWitness v₁ t₁.1) := rfl
        _ = (B₁.properVertexEquiv y₀).1 := hlabel₁
    have hdiff : mapPoint phi beta =
        mapTranslatedVertex phi (translatedWitness v₁ t₁.1) -
          mapTranslatedVertex phi (translatedWitness v₀ t₀.1) := by
      calc
        mapPoint phi beta =
            mapPoint phi beta + mapPoint phi anchorPoint - mapPoint phi anchorPoint := by
              abel
        _ = mapPoint phi
              ⟨beta.1 + anchorPoint.1,
                C.coordinateSpace.add_mem beta.2.1 anchorPoint.2.1,
                C.coordinateSpace.add_mem beta.2.2 anchorPoint.2.2⟩ -
              mapPoint phi anchorPoint := by rw [hadd]
        _ = mapPoint phi targetAnchorPoint - mapPoint phi anchorPoint := by
              rw [hBetaAdd]
        _ = mapTranslatedVertex phi (translatedWitness v₁ t₁.1) -
              mapTranslatedVertex phi (translatedWitness v₀ t₀.1) := by
              rw [hlabel₁', hlabel₀']
              rw [← hlabel₁, ← hlabel₀]
    rw [hlabel₁, hlabel₀, hThetaImage anchor] at hdiff
    simpa [sub_eq_add_neg, add_assoc] using hdiff
  have hEdgeTranslation
      (x y : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
      (hxy : dist x.1 y.1 < ell) :
      (sourceEquiv y).1 - y.1 = (sourceEquiv x).1 - x.1 := by
    obtain ⟨vx, tx, hxLabel⟩ := B₀.source_provenance x
    obtain ⟨vy, ty, hyLabel⟩ := B₀.source_provenance y
    let x' := sourceEquiv x
    let y' := sourceEquiv y
    obtain ⟨wx, sx, hx'Label⟩ := B₁.source_provenance x'
    obtain ⟨wy, sy, hy'Label⟩ := B₁.source_provenance y'
    let ax := translatedWitness vx tx.1
    let ay := translatedWitness vy ty.1
    let bx := translatedWitness wx sx.1
    let b_y := translatedWitness wy sy.1
    have hax : (ax : Tiling.Plane) = x.1 := by
      change vx.1 + tx.1.1 = x.1
      exact hxLabel.symm
    have hay : (ay : Tiling.Plane) = y.1 := by
      change vy.1 + ty.1.1 = y.1
      exact hyLabel.symm
    have hbx : (bx : Tiling.Plane) = x'.1 := by
      change wx.1 + sx.1.1 = x'.1
      exact hx'Label.symm
    have hby : (b_y : Tiling.Plane) = y'.1 := by
      change wy.1 + sy.1.1 = y'.1
      exact hy'Label.symm
    have hmapax := hMapped0 x vx tx hxLabel
    have hmapay := hMapped0 y vy ty hyLabel
    have hmapbx := hMapped1 x' wx sx hx'Label
    have hmapby := hMapped1 y' wy sy hy'Label
    have hImageX : mapTranslatedVertex phi bx =
        eta + mapTranslatedVertex phi ax := by
      rw [hmapbx, hThetaImage x, hmapax]
    have hImageY : mapTranslatedVertex phi b_y =
        eta + mapTranslatedVertex phi ay := by
      rw [hmapby, hThetaImage y, hmapay]
    have hSourceBound : dist (ax : Tiling.Plane) (ay : Tiling.Plane) < P.scale := by
      rw [hax, hay]
      have hEll : ell < P.scale := by
        nlinarith [hMargin, P.localError_pos, P.scale_pos]
      exact lt_trans hxy hEll
    have hLocal0 := deformation_localAccuracy P phi hphi ax ay hSourceBound
    have hImageBound0 : dist (mapTranslatedVertex phi ax)
        (mapTranslatedVertex phi ay) < ell + P.localError := by
      rw [dist_eq_norm]
      calc
        ‖mapTranslatedVertex phi ax - mapTranslatedVertex phi ay‖ =
            ‖(mapTranslatedVertex phi ax - mapTranslatedVertex phi ay) -
              ((ax : Tiling.Plane) - (ay : Tiling.Plane)) +
              ((ax : Tiling.Plane) - (ay : Tiling.Plane))‖ := by
          congr 1
          abel
        _ ≤ ‖(mapTranslatedVertex phi ax - mapTranslatedVertex phi ay) -
              ((ax : Tiling.Plane) - (ay : Tiling.Plane))‖ +
              ‖(ax : Tiling.Plane) - (ay : Tiling.Plane)‖ := norm_add_le _ _
        _ < P.localError + ell := by
          have hlocal : ‖(mapTranslatedVertex phi ax - mapTranslatedVertex phi ay) -
                ((ax : Tiling.Plane) - (ay : Tiling.Plane))‖ < P.localError := by
            simpa [dist_eq_norm] using hLocal0
          have hdist : ‖(ax : Tiling.Plane) - (ay : Tiling.Plane)‖ < ell := by
            simpa [dist_eq_norm, hax, hay] using hxy
          exact add_lt_add hlocal hdist
        _ = ell + P.localError := by ring
    have hImageBound0Half : dist (mapTranslatedVertex phi ax)
        (mapTranslatedVertex phi ay) < P.scale / 2 :=
      lt_trans hImageBound0 (by nlinarith [hMargin, P.localError_pos])
    have hImageBound0' : dist (mapTranslatedVertex phi ay)
        (mapTranslatedVertex phi ax) < P.scale / 2 := by
      rw [dist_comm]
      exact hImageBound0Half
    have hImageBound1 : dist (mapTranslatedVertex phi bx)
        (mapTranslatedVertex phi b_y) < P.scale / 2 := by
      rw [hImageX, hImageY, dist_add_left]
      exact hImageBound0Half
    have hImageBound1' : dist (mapTranslatedVertex phi b_y)
        (mapTranslatedVertex phi bx) < P.scale / 2 := by
      rw [dist_comm]
      exact hImageBound1
    have hSourceBound1 := deformation_coarselyProper P phi hphi bx b_y hImageBound1
    have hImageDisp : mapTranslatedVertex phi b_y - mapTranslatedVertex phi bx =
        mapTranslatedVertex phi ay - mapTranslatedVertex phi ax := by
      rw [hImageX, hImageY]
      abel
    have hImageCoord (axis : Axis) :
        Axis.coord axis (mapTranslatedVertex phi ay - mapTranslatedVertex phi ax) =
          Axis.coord axis (mapTranslatedVertex phi b_y - mapTranslatedVertex phi bx) :=
      (congrArg (Axis.coord axis) hImageDisp).symm
    have hre := deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      Axis.horizontal ax ay bx b_y hImageBound0' hImageBound1' (hImageCoord .horizontal)
    have him := deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      Axis.vertical ax ay bx b_y hImageBound0' hImageBound1' (hImageCoord .vertical)
    have hSourceDisp : (b_y : Tiling.Plane) - (bx : Tiling.Plane) =
        (ay : Tiling.Plane) - (ax : Tiling.Plane) := by
      apply Complex.ext
      · simpa [Axis.coord] using hre.symm
      · simpa [Axis.coord] using him.symm
    rw [hax, hay, hbx, hby] at hSourceDisp
    calc
      (sourceEquiv y).1 - y.1 =
          ((sourceEquiv y).1 - (sourceEquiv x).1) +
            ((sourceEquiv x).1 - y.1) := by abel
      _ = (y.1 - x.1) + ((sourceEquiv x).1 - y.1) := by rw [hSourceDisp]
      _ = (sourceEquiv x).1 - x.1 := by abel
  have hPathDefect : ∀ {x y : Tiling.Plane},
      Relation.ReflTransGen
        (fun u v : Tiling.Plane =>
          u ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)) ∧
          v ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)) ∧
          dist u v < ell) x y →
      ∀ hx : x ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
      ∀ hy : y ∈ properVertices (regularSupport C.region (Subtype.val '' S₀)),
        (sourceEquiv ⟨x, hx⟩).1 - x = (sourceEquiv ⟨y, hy⟩).1 - y := by
    intro x y hpath
    induction hpath using Relation.ReflTransGen.head_induction_on with
    | refl => intro hx hy; rfl
    | head hedge htail ih =>
        intro hx hy
        rcases hedge with ⟨hxmid, hymid, hlen⟩
        have hfirst := hEdgeTranslation ⟨_, hxmid⟩ ⟨_, hymid⟩ hlen
        exact hfirst.symm.trans (ih hymid hy)
  have hSourceFormula (x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S₀)))) :
      (sourceEquiv x).1 = beta.1 + x.1 := by
    have hpath := hLinked.2 anchor.1 anchor.2 x.1 x.2
    have hdefect := hPathDefect hpath anchor.2 x.2
    have hanchor : (sourceEquiv anchor).1 - anchor.1 = beta.1 := rfl
    have hx : (sourceEquiv x).1 - x.1 = beta.1 := hdefect.symm.trans hanchor
    calc
      (sourceEquiv x).1 = ((sourceEquiv x).1 - x.1) + x.1 := by abel
      _ = beta.1 + x.1 := by rw [hx]
  refine ⟨⟨beta, hMapBeta, sourceEquiv, hSourceFormula, hThetaImage⟩⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional Tiling.AxisParallel.Foundations

private theorem periodicSequence_coversReal
    (n : ℕ) (p : ℝ) (x : ℤ → ℝ)
    (hp : 0 < p) (hx : StrictMono x)
    (hshift : ∀ j : ℤ, x (j + Int.ofNat n) = x j + p) :
    ∀ z : ℝ, ∃ j : ℤ, x j ≤ z ∧ z < x (j + 1) := by
  intro z
  let k : ℤ := Int.floor ((z - x 0) / p)
  have hleft : x (k * Int.ofNat n) ≤ z := by
    have hfloor := Int.floor_le ((z - x 0) / p)
    have hmul : (k : ℝ) * p ≤ z - x 0 := by
      exact (le_div_iff₀ hp).mp hfloor
    have h := periodic_shift_iterate hshift k 0
    simp only [zero_add] at h
    rw [h]
    linarith
  have hright : z < x ((k + 1) * Int.ofNat n) := by
    have hfloor := Int.lt_floor_add_one ((z - x 0) / p)
    have hmul : z - x 0 < ((k : ℝ) + 1) * p :=
      (div_lt_iff₀ hp).mp hfloor
    have h := periodic_shift_iterate hshift (k + 1) 0
    simp only [zero_add] at h
    rw [h]
    push_cast
    linarith
  obtain ⟨j, hj, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun j => x j ≤ z)
    ⟨(k + 1) * Int.ofNat n, by
      intro j hj
      by_contra hnot
      have hlt : (k + 1) * Int.ofNat n < j := lt_of_not_ge hnot
      exact (not_lt_of_ge hj) (hright.trans (hx hlt))⟩
    ⟨k * Int.ofNat n, hleft⟩
  refine ⟨j, hj, ?_⟩
  by_contra hnot
  have hnext := hmax (j + 1) (le_of_not_gt hnot)
  omega

private theorem orderedPeriodicCoordinateSet_extension
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (E : Set ℝ) (hEcoord : ∀ x ∈ E, x ∈ C.coordinateSpace)
    (hne : E.Nonempty)
    (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (p : C.coordinateSpace) (hp : 0 < (p : ℝ))
    (hperiod : (p : ℝ) +ᵥ E = E)
    (horder : ∀ x y : E, x.1 < y.1 →
      mapScalar phi ⟨x.1, hEcoord x.1 x.2⟩ <
        mapScalar phi ⟨y.1, hEcoord y.1 y.2⟩) :
    ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧
      (∀ x (hx : x ∈ E), H x = mapScalar phi ⟨x, hEcoord x hx⟩) ∧
      (∀ z : ℝ, H (z + (p : ℝ)) = H z + mapScalar phi p) := by
  classical
  obtain ⟨X⟩ := periodicIntEnumeration_exists E p hp hne hfinite hperiod
  have hxmem (j : ℤ) : X.point j ∈ E := by
    simpa only [X.point_range] using Set.mem_range_self (f := X.point) j
  let y : ℤ → ℝ := fun j => mapScalar phi
    ⟨X.point j, hEcoord (X.point j) (hxmem j)⟩
  have hy : StrictMono y := by
    intro i j hij
    exact horder ⟨X.point i, hxmem i⟩ ⟨X.point j, hxmem j⟩ (X.point_strictMono hij)
  have hyp (j : ℤ) : y (j + Int.ofNat X.count) = y j + mapScalar phi p := by
    have hsub : (⟨X.point (j + Int.ofNat X.count),
        hEcoord _ (hxmem _)⟩ : C.coordinateSpace) =
        ⟨X.point j, hEcoord _ (hxmem _)⟩ + p := by
      apply Subtype.ext
      exact X.point_period j
    dsimp only [y]
    rw [hsub]
    simp only [mapScalar, map_add, Rat.cast_add]
  have hq : 0 < mapScalar phi p := by
    have hn : (0 : ℤ) < Int.ofNat X.count := by
      change (0 : ℤ) < (X.count : ℤ)
      exact_mod_cast X.count_pos
    have h := hy hn
    rw [show Int.ofNat X.count = 0 + Int.ofNat X.count by omega, hyp] at h
    linarith
  obtain ⟨H, hH, hknots, hHp⟩ := exists_periodic_strictMonoHomeomorph_extension
    X.count p (mapScalar phi p) X.point y X.count_pos hp hq
    X.point_strictMono hy X.point_period hyp
    (periodicSequence_coversReal X.count p X.point hp X.point_strictMono X.point_period)
    (periodicSequence_coversReal X.count (mapScalar phi p) y hq hy hyp)
  refine ⟨H, hH, ?_, hHp⟩
  intro x hx
  have hxrange : x ∈ Set.range X.point := by rw [X.point_range]; exact hx
  obtain ⟨j, rfl⟩ := hxrange
  exact hknots j

private theorem coordinateProduct_tileImage_of_vertexAgreement
    (K : Region) (hx hy hx' hy' : ℝ ≃ₜ ℝ)
    (hmx : StrictMono hx) (hmy : StrictMono hy)
    (hmx' : StrictMono hx') (hmy' : StrictMono hy')
    (s t : Tiling.Plane)
    (hvertices : ∀ v ∈ K.vertices,
      coordinateProductHomeomorph hx hy (s + v) =
        t + coordinateProductHomeomorph hx' hy' v) :
    coordinateProductHomeomorph hx hy '' (s +ᵥ K.openCarrier) =
      t +ᵥ (coordinateProductHomeomorph hx' hy' '' K.openCarrier) := by
  let gx : ℝ ≃ₜ ℝ :=
    ((Homeomorph.addRight s.re).trans hx).trans (Homeomorph.addRight (-t.re))
  let gy : ℝ ≃ₜ ℝ :=
    ((Homeomorph.addRight s.im).trans hy).trans (Homeomorph.addRight (-t.im))
  have hgx : StrictMono gx := by
    intro x y hxy
    change hx (x + s.re) + -t.re < hx (y + s.re) + -t.re
    simpa only [add_comm] using
      add_lt_add_right (hmx (add_lt_add_right hxy s.re)) (-t.re)
  have hgy : StrictMono gy := by
    intro x y hxy
    change hy (x + s.im) + -t.im < hy (y + s.im) + -t.im
    simpa only [add_comm] using
      add_lt_add_right (hmy (add_lt_add_right hxy s.im)) (-t.im)
  have hlocal : coordinateProductHomeomorph gx gy '' K.openCarrier =
      coordinateProductHomeomorph hx' hy' '' K.openCarrier := by
    apply coordinateProductImage_openCarrier_unique K gx gy hx' hy'
      hgx hgy hmx' hmy'
    · intro v hv
      have h := congrArg Complex.re (hvertices v hv)
      simp only [coordinateProductHomeomorph_apply, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at h
      change hx (v.re + s.re) + -t.re = hx' v.re
      rw [add_comm v.re s.re]
      linarith
    · intro v hv
      have h := congrArg Complex.im (hvertices v hv)
      simp only [coordinateProductHomeomorph_apply, Complex.add_im,
        Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, zero_add] at h
      change hy (v.im + s.im) + -t.im = hy' v.im
      rw [add_comm v.im s.im]
      linarith
  have hformula (u : Tiling.Plane) :
      coordinateProductHomeomorph hx hy (s + u) =
        t + coordinateProductHomeomorph gx gy u := by
    apply Complex.ext <;>
      simp [coordinateProductHomeomorph_apply, gx, gy, add_comm]
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨coordinateProductHomeomorph gx gy u, ?_, ?_⟩
    · rw [← hlocal]
      exact ⟨u, hu, rfl⟩
    · exact (hformula u).symm
  · rintro ⟨w, hw, rfl⟩
    rw [← hlocal] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    exact ⟨s + u, ⟨u, hu, rfl⟩, hformula u⟩

private theorem placedTileImages_openUnion_and_regularSupport
    {C : ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (S : Set ↥C.centres)
    (H : Tiling.Plane ≃ₜ Tiling.Plane)
    (htiles : ∀ s : S,
      H '' (s.1.1 +ᵥ C.region.openCarrier) =
        Tphi s.1 +ᵥ D.deformedRegion.openCarrier) :
    openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) =
      H '' openUnion C.region (Subtype.val '' S) ∧
    regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S) =
      H '' regularSupport C.region (Subtype.val '' S) := by
  have hunion : openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) =
      H '' openUnion C.region (Subtype.val '' S) := by
    ext z
    constructor
    · intro hz
      obtain ⟨t, ht⟩ := Set.mem_iUnion.mp hz
      obtain ⟨s, hs, hst⟩ := t.2
      have hzTile : z ∈ H '' (s.1 +ᵥ C.region.openCarrier) := by
        rw [htiles ⟨s, hs⟩]
        simpa only [hst, Region.openCarrier] using ht
      obtain ⟨w, hw, hwz⟩ := hzTile
      refine ⟨w, ?_, hwz⟩
      exact Set.mem_iUnion.mpr ⟨⟨s.1, ⟨s, hs, rfl⟩⟩, hw⟩
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hw
      obtain ⟨t, ht, hts⟩ := s.2
      have hwTile : H w ∈ Tphi t +ᵥ D.deformedRegion.openCarrier := by
        rw [← htiles ⟨t, ht⟩]
        exact ⟨w, by simpa only [hts, Region.openCarrier] using hs, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨Tphi t, ⟨t, ht, rfl⟩⟩, hwTile⟩
  refine ⟨hunion, ?_⟩
  change interior (closure (openUnion _ _)) = H '' interior (closure (openUnion _ _))
  rw [hunion, ← H.image_closure, ← H.image_interior]

private def axisSection (K : Region) (axis : Axis) (q : ℝ) : Set ℝ :=
  {x | axisPoint axis q x ∈ K.openCarrier}

private def regularizedAxisSectionUnion
    (K : Region) (axis : Axis) (S : Set Tiling.Plane) (q : ℝ) : Set ℝ :=
  interior (closure (⋃ s : S, axis.coord s.1 +ᵥ axisSection K axis q))

private theorem axisPoint_sub_rowCentre
    (axis : Axis) (c q x : ℝ) (s : Tiling.Plane)
    (hs : axis.transverseCoord s = c) :
    axisPoint axis (c + q) x - s = axisPoint axis q (x - axis.coord s) := by
  cases axis <;> apply Complex.ext <;>
    simp [axisPoint, Axis.coord, Axis.transverseCoord] at hs ⊢ <;> linarith

private theorem mem_openUnion_axisPoint_iff
    (K : Region) (axis : Axis) (S : Set Tiling.Plane) (c q x : ℝ)
    (halign : ∀ s ∈ S, axis.transverseCoord s = c) :
    axisPoint axis (c + q) x ∈ openUnion K S ↔
      x ∈ ⋃ s : S, axis.coord s.1 +ᵥ axisSection K axis q := by
  simp only [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs ⊢
    change axisPoint axis q (-axis.coord s.1 + x) ∈ K.openCarrier
    have heq := axisPoint_sub_rowCentre axis c q x s.1 (halign s.1 s.2)
    simpa only [vadd_eq_add, neg_add_eq_sub, ← heq] using hs
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs ⊢
    change -s.1 + axisPoint axis (c + q) x ∈ K.openCarrier
    have heq := axisPoint_sub_rowCentre axis c q x s.1 (halign s.1 s.2)
    simpa only [axisSection, Set.mem_ofPred_eq, vadd_eq_add,
      neg_add_eq_sub, ← heq] using hs

private theorem axisSectionUnion_image_of_openUnion_image
    (K K' : Region) (axis : Axis) (S S' : Set Tiling.Plane)
    (c c' q q' : ℝ) (H : Tiling.Plane ≃ₜ Tiling.Plane) (h : ℝ ≃ₜ ℝ)
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (halign' : ∀ s ∈ S', axis.transverseCoord s = c')
    (hunion : openUnion K' S' = H '' openUnion K S)
    (hpoint : ∀ x, H (axisPoint axis (c + q) x) =
      axisPoint axis (c' + q') (h x)) :
    (⋃ s : S', axis.coord s.1 +ᵥ axisSection K' axis q') =
      h '' (⋃ s : S, axis.coord s.1 +ᵥ axisSection K axis q) := by
  ext y
  rw [← mem_openUnion_axisPoint_iff K' axis S' c' q' y halign']
  rw [hunion]
  constructor
  · rintro ⟨z, hz, hzy⟩
    have hzEq : z = axisPoint axis (c + q) (h.symm y) := by
      apply H.injective
      rw [hpoint, h.apply_symm_apply]
      exact hzy
    refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
    rw [← mem_openUnion_axisPoint_iff K axis S c q (h.symm y) halign]
    simpa only [← hzEq] using hz
  · rintro ⟨x, hx, rfl⟩
    refine ⟨axisPoint axis (c + q) x, ?_, hpoint x⟩
    exact (mem_openUnion_axisPoint_iff K axis S c q x halign).mpr hx

private theorem regularizedAxisSectionUnion_image_of_openUnion_image
    (K K' : Region) (axis : Axis) (S S' : Set Tiling.Plane)
    (c c' q q' : ℝ) (H : Tiling.Plane ≃ₜ Tiling.Plane) (h : ℝ ≃ₜ ℝ)
    (halign : ∀ s ∈ S, axis.transverseCoord s = c)
    (halign' : ∀ s ∈ S', axis.transverseCoord s = c')
    (hunion : openUnion K' S' = H '' openUnion K S)
    (hpoint : ∀ x, H (axisPoint axis (c + q) x) =
      axisPoint axis (c' + q') (h x)) :
    regularizedAxisSectionUnion K' axis S' q' =
      h '' regularizedAxisSectionUnion K axis S q := by
  unfold regularizedAxisSectionUnion
  rw [axisSectionUnion_image_of_openUnion_image K K' axis S S' c c' q q'
    H h halign halign' hunion hpoint, ← h.image_closure, ← h.image_interior]

private theorem coordinateProduct_quadrantAt_iff
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (x z : Tiling.Plane) (q : Quadrant) :
    z ∈ quadrantAt q x ↔
      coordinateProductHomeomorph hx hy z ∈
        quadrantAt q (coordinateProductHomeomorph hx hy x) := by
  cases q <;>
    simp [quadrantAt, coordinateProductHomeomorph_apply,
      hhx.lt_iff_lt, hhy.lt_iff_lt]

private theorem SetOccupiesQuadrant_coordinateProductImage
    (F F' : Set Tiling.Plane)
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (x : Tiling.Plane) (q : Quadrant) :
    SetOccupiesQuadrant F' (coordinateProductHomeomorph hx hy x) q ↔
      SetOccupiesQuadrant F x q := by
  constructor
  · rintro ⟨r, hr, hocc⟩
    obtain ⟨s, hs, hcont⟩ :=
      (Metric.continuousAt_iff.1
        (coordinateProductHomeomorph hx hy).continuous.continuousAt) r hr
    refine ⟨s, hs, ?_⟩
    intro z ⟨hz, hq⟩
    have hnear : dist (coordinateProductHomeomorph hx hy z)
        (coordinateProductHomeomorph hx hy x) < r := hcont hz
    have hq' := (coordinateProduct_quadrantAt_iff hx hy hhx hhy x z q).mp hq
    have hmem := hocc ⟨hnear, hq'⟩
    rw [himage] at hmem
    rcases hmem with ⟨w, hw, hzw⟩
    have hwz : w = z := by
      apply (coordinateProductHomeomorph hx hy).injective
      simpa using hzw
    simpa [hwz] using hw
  · rintro ⟨r, hr, hocc⟩
    obtain ⟨s, hs, hcont⟩ :=
      (Metric.continuousAt_iff.1
        (coordinateProductHomeomorph hx hy).symm.continuous.continuousAt) r hr
    refine ⟨s, hs, ?_⟩
    intro z' ⟨hz', hq'⟩
    let z := (coordinateProductHomeomorph hx hy).symm z'
    have hz : dist z x < r := by
      simpa [z, dist_comm] using hcont hz'
    have hq : z ∈ quadrantAt q x := by
      apply (coordinateProduct_quadrantAt_iff hx hy hhx hhy x z q).mpr
      simpa [z] using hq'
    have hmem := hocc ⟨hz, hq⟩
    have hzimage : z' ∈ coordinateProductHomeomorph hx hy '' F :=
      ⟨z, hmem, by simp [z]⟩
    simpa [himage] using hzimage

private theorem properVertex_coordinateProductImage_iff
    (F F' : Set Tiling.Plane)
    (hFopen : IsOpen F) (hFregular : interior (closure F) = F)
    (hFpolygonal : IsLocallyAxisParallelPolygonal F)
    (hF'open : IsOpen F') (hF'regular : interior (closure F') = F')
    (hF'polygonal : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (x : Tiling.Plane) :
    IsProperVertex F' (coordinateProductHomeomorph hx hy x) ↔
      IsProperVertex F x := by
  obtain ⟨r, hr, p, hp, hocc⟩ :=
    exists_quadrantPattern_germ hFopen hFregular hFpolygonal x
  obtain ⟨r', hr', p', hp', hocc'⟩ :=
    exists_quadrantPattern_germ hF'open hF'regular hF'polygonal
      (coordinateProductHomeomorph hx hy x)
  have hpat : p' = p := by
    funext q
    have hq := SetOccupiesQuadrant_coordinateProductImage F F' hx hy hhx hhy
      himage x q
    rw [← hocc q, ← hocc' q] at hq
    cases hpq : p q <;> cases hp'q : p' q <;> simp_all
  rw [properVertex_iff_nonstraightPattern hF'open hF'regular hr' p' hp',
    properVertex_iff_nonstraightPattern hFopen hFregular hr p hp, hpat]

private theorem coordinateProduct_quadrant_iff
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (x z : Tiling.Plane) (q : Bool × Bool) :
    (if q.1 then x.re < z.re else z.re < x.re) ∧
      (if q.2 then x.im < z.im else z.im < x.im) ↔
    (if q.1 then
        (coordinateProductHomeomorph hx hy x).re <
          (coordinateProductHomeomorph hx hy z).re
      else
        (coordinateProductHomeomorph hx hy z).re <
          (coordinateProductHomeomorph hx hy x).re) ∧
      (if q.2 then
        (coordinateProductHomeomorph hx hy x).im <
          (coordinateProductHomeomorph hx hy z).im
      else
        (coordinateProductHomeomorph hx hy z).im <
          (coordinateProductHomeomorph hx hy x).im) := by
  rcases q with ⟨qx, qy⟩
  cases qx <;> cases qy <;>
    simp [coordinateProductHomeomorph_apply, hhx.lt_iff_lt, hhy.lt_iff_lt]

/-- A coordinatewise increasing plane homeomorphism transports the four local quadrant germs
    whenever the whole region is its image. This uses exact set transport, not a scale margin. -/
private theorem localCone_coordinateProductImage
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (x : Tiling.Plane) (hxproper : IsProperVertex F x)
    (hx'proper : IsProperVertex F' (coordinateProductHomeomorph hx hy x)) :
    localCone F' (coordinateProductHomeomorph hx hy x) hF' hx'proper =
      localCone F x hF hxproper := by
  classical
  ext q
  simp only [localCone]
  constructor
  · rintro ⟨r, hr, hocc⟩
    obtain ⟨s, hs, hcont⟩ :=
      (Metric.continuousAt_iff.1
        (coordinateProductHomeomorph hx hy).continuous.continuousAt) r hr
    refine ⟨s, hs, ?_⟩
    intro z hz hquad
    have hnear : dist (coordinateProductHomeomorph hx hy z)
        (coordinateProductHomeomorph hx hy x) < r := by
      exact hcont hz
    have hquad' := (coordinateProduct_quadrant_iff hx hy hhx hhy x z q).1 hquad
    have hmem' := hocc (coordinateProductHomeomorph hx hy z) hnear hquad'
    have : coordinateProductHomeomorph hx hy z ∈
        coordinateProductHomeomorph hx hy '' F := by
      rw [← himage]
      exact hmem'
    rcases this with ⟨w, hw, hzw⟩
    have hwz : w = z := by
      apply (coordinateProductHomeomorph hx hy).injective
      simpa using hzw
    simpa [hwz] using hw
  · rintro ⟨r, hr, hocc⟩
    obtain ⟨s, hs, hcont⟩ :=
      (Metric.continuousAt_iff.1
        (coordinateProductHomeomorph hx hy).symm.continuous.continuousAt) r hr
    refine ⟨s, hs, ?_⟩
    intro z hz hquad
    let w := (coordinateProductHomeomorph hx hy).symm z
    have hwnear : dist w x < r := by
      have := hcont hz
      simpa [w, dist_comm] using this
    change (if q.1 then
        (coordinateProductHomeomorph hx hy x).re < z.re
      else z.re < (coordinateProductHomeomorph hx hy x).re) ∧
      (if q.2 then
        (coordinateProductHomeomorph hx hy x).im < z.im
      else z.im < (coordinateProductHomeomorph hx hy x).im) at hquad
    have hquad' :
        (if q.1 then x.re < w.re else w.re < x.re) ∧
          (if q.2 then x.im < w.im else w.im < x.im) := by
      apply (coordinateProduct_quadrant_iff hx hy hhx hhy x w q).2
      simpa [w] using hquad
    have hwmem := hocc w hwnear hquad'
    have hzimage : z ∈ coordinateProductHomeomorph hx hy '' F :=
      ⟨w, hwmem, by simp [w]⟩
    simpa [himage] using hzimage

private def coordinateProductBoundaryLine
    (hx hy : ℝ ≃ₜ ℝ) (L : CompleteBoundaryLine) : CompleteBoundaryLine where
  axis := L.axis
  level := match L.axis with
    | .horizontal => hy L.level
    | .vertical => hx L.level
  insideOnPositiveSide := L.insideOnPositiveSide

private theorem coordinateProductBoundaryLine_carrier_image
    (hx hy : ℝ ≃ₜ ℝ) (L : CompleteBoundaryLine) :
    coordinateProductHomeomorph hx hy '' L.carrier =
      (coordinateProductBoundaryLine hx hy L).carrier := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases hax : L.axis <;>
      simp only [CompleteBoundaryLine.carrier, coordinateProductBoundaryLine,
        Axis.transverseCoord, hax, coordinateProductHomeomorph_apply,
        Set.mem_ofPred_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
        sub_zero] at hw ⊢
    · exact congrArg hy hw
    · exact congrArg hx hw
  · intro hz
    refine ⟨(coordinateProductHomeomorph hx hy).symm z, ?_, by simp⟩
    cases hax : L.axis
    · have hz' : z.im = hy L.level := by
        simpa [CompleteBoundaryLine.carrier, coordinateProductBoundaryLine,
          hax, Axis.transverseCoord] using hz
      have hzsymm :
          hy ((coordinateProductHomeomorph hx hy).symm z).im = z.im := by
        calc
          hy ((coordinateProductHomeomorph hx hy).symm z).im =
              (coordinateProductHomeomorph hx hy
                ((coordinateProductHomeomorph hx hy).symm z)).im := by
                  rw [coordinateProductHomeomorph_apply]
                  simp
          _ = z.im := congrArg Complex.im
            ((coordinateProductHomeomorph hx hy).apply_symm_apply z)
      rw [CompleteBoundaryLine.carrier, hax, Axis.transverseCoord]
      exact hy.injective (hzsymm.trans hz')
    · have hz' : z.re = hx L.level := by
        simpa [CompleteBoundaryLine.carrier, coordinateProductBoundaryLine,
          hax, Axis.transverseCoord] using hz
      have hzsymm :
          hx ((coordinateProductHomeomorph hx hy).symm z).re = z.re := by
        calc
          hx ((coordinateProductHomeomorph hx hy).symm z).re =
              (coordinateProductHomeomorph hx hy
                ((coordinateProductHomeomorph hx hy).symm z)).re := by
                  rw [coordinateProductHomeomorph_apply]
                  simp
          _ = z.re := congrArg Complex.re
            ((coordinateProductHomeomorph hx hy).apply_symm_apply z)
      rw [CompleteBoundaryLine.carrier, hax, Axis.transverseCoord]
      exact hx.injective (hzsymm.trans hz')

private theorem coordinateProductBoundaryLine_side_iff
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (L : CompleteBoundaryLine) (z : Tiling.Plane) :
    (if L.insideOnPositiveSide then
        (coordinateProductBoundaryLine hx hy L).level <
          L.axis.transverseCoord (coordinateProductHomeomorph hx hy z)
      else
        L.axis.transverseCoord (coordinateProductHomeomorph hx hy z) <
          (coordinateProductBoundaryLine hx hy L).level) ↔
    (if L.insideOnPositiveSide then
        L.level < L.axis.transverseCoord z
      else L.axis.transverseCoord z < L.level) := by
  cases hax : L.axis <;> cases L.insideOnPositiveSide <;>
    simp [coordinateProductBoundaryLine, Axis.transverseCoord, hax,
      coordinateProductHomeomorph_apply, hhx.lt_iff_lt, hhy.lt_iff_lt]

private theorem completeBoundaryLine_coordinateProductImage_iff
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (L : CompleteBoundaryLine) :
    coordinateProductBoundaryLine hx hy L ∈ completeBoundaryLines F' hF' ↔
      L ∈ completeBoundaryLines F hF := by
  classical
  let H := coordinateProductHomeomorph hx hy
  let L' := coordinateProductBoundaryLine hx hy L
  have hcarrier : H '' L.carrier = L'.carrier :=
    coordinateProductBoundaryLine_carrier_image hx hy L
  have hfrontier : frontier F' = H '' frontier F := by
    rw [himage, H.image_frontier]
  have himem (z : Tiling.Plane) : z ∈ F' ↔ H.symm z ∈ F := by
    rw [himage]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hweq : w = H.symm z := H.injective (by simpa using hwz)
      simpa [hweq] using hw
    · intro hz
      exact ⟨H.symm z, hz, H.apply_symm_apply z⟩
  have hmem (z : Tiling.Plane) : H z ∈ F' ↔ z ∈ F := by
    simpa using himem (H z)
  change (L'.carrier ⊆ frontier F' ∧
    ∀ x ∈ L'.carrier, ∃ r : ℝ, 0 < r ∧
      ∀ z, z ∈ Metric.ball x r →
        (z ∈ F' ↔ if L'.insideOnPositiveSide then
          L'.level < L'.axis.transverseCoord z
        else L'.axis.transverseCoord z < L'.level)) ↔
    (L.carrier ⊆ frontier F ∧
    ∀ x ∈ L.carrier, ∃ r : ℝ, 0 < r ∧
      ∀ z, z ∈ Metric.ball x r →
        (z ∈ F ↔ if L.insideOnPositiveSide then
          L.level < L.axis.transverseCoord z
        else L.axis.transverseCoord z < L.level))
  constructor
  · rintro ⟨hbdry, hside⟩
    constructor
    · intro x hxLine
      have hx' : H x ∈ L'.carrier := by
        rw [← hcarrier]
        exact ⟨x, hxLine, rfl⟩
      have hfx := hbdry hx'
      rw [hfrontier] at hfx
      rcases hfx with ⟨w, hw, hweq⟩
      have hwx : w = x := H.injective (by simpa using hweq)
      simpa [hwx] using hw
    · intro x hxLine
      have hx' : H x ∈ L'.carrier := by
        rw [← hcarrier]
        exact ⟨x, hxLine, rfl⟩
      obtain ⟨r, hr, hlocal⟩ := hside (H x) hx'
      obtain ⟨s, hs, hcont⟩ :=
        (Metric.continuousAt_iff.1 (H.continuous.continuousAt (x := x))) r hr
      refine ⟨s, hs, ?_⟩
      intro z hz
      have hwnear : dist (H z) (H x) < r := hcont hz
      have hlocal' := hlocal (H z) hwnear
      rw [hmem] at hlocal'
      have hsideiff :=
        coordinateProductBoundaryLine_side_iff hx hy hhx hhy L z
      simp only [coordinateProductBoundaryLine] at hsideiff
      simpa [H] using hlocal'.trans hsideiff
  · rintro ⟨hbdry, hside⟩
    constructor
    · intro y hyLine
      rw [← hcarrier] at hyLine
      rcases hyLine with ⟨x, hxLine, rfl⟩
      rw [hfrontier]
      exact ⟨x, hbdry hxLine, rfl⟩
    · intro y hyLine
      have hy' : H.symm y ∈ L.carrier := by
        have hymap : H (H.symm y) ∈ L'.carrier := by simpa using hyLine
        rw [← hcarrier] at hymap
        rcases hymap with ⟨x, hx, hxy⟩
        have hxeq : x = H.symm y := H.injective (by simpa using hxy)
        simpa [hxeq] using hx
      obtain ⟨r, hr, hlocal⟩ := hside (H.symm y) hy'
      obtain ⟨s, hs, hcont⟩ :=
        (Metric.continuousAt_iff.1
          (H.symm.continuous.continuousAt (x := y))) r hr
      refine ⟨s, hs, ?_⟩
      intro z hz
      have hnear : dist (H.symm z) (H.symm y) < r := hcont hz
      have hlocal' := hlocal (H.symm z) hnear
      rw [← himem z] at hlocal'
      have hsideiff :=
        coordinateProductBoundaryLine_side_iff hx hy hhx hhy L (H.symm z)
      simp only [coordinateProductBoundaryLine] at hsideiff
      simpa [H, L', coordinateProductBoundaryLine] using hlocal'.trans hsideiff.symm

private theorem coordinateProductBoundaryLine_symm_comp
    (hx hy : ℝ ≃ₜ ℝ) (L : CompleteBoundaryLine) :
    coordinateProductBoundaryLine hx.symm hy.symm
        (coordinateProductBoundaryLine hx hy L) = L := by
  cases L with
  | mk axis level inside =>
    cases axis <;>
      simp [coordinateProductBoundaryLine]

private theorem coordinateProductBoundaryLine_comp_symm
    (hx hy : ℝ ≃ₜ ℝ) (L : CompleteBoundaryLine) :
    coordinateProductBoundaryLine hx hy
        (coordinateProductBoundaryLine hx.symm hy.symm L) = L := by
  cases L with
  | mk axis level inside =>
    cases axis <;>
      simp [coordinateProductBoundaryLine]

private def completeBoundaryLines_coordinateProductEquiv
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F) :
    {L : CompleteBoundaryLine // L ∈ completeBoundaryLines F hF} ≃
      {L : CompleteBoundaryLine // L ∈ completeBoundaryLines F' hF'} where
  toFun L := ⟨coordinateProductBoundaryLine hx hy L.1,
    (completeBoundaryLine_coordinateProductImage_iff F F' hF hF' hx hy
      hhx hhy himage L.1).2 L.2⟩
  invFun L := ⟨coordinateProductBoundaryLine hx.symm hy.symm L.1, by
    have hcomp := coordinateProductBoundaryLine_comp_symm hx hy L.1
    have htransport := completeBoundaryLine_coordinateProductImage_iff
      F F' hF hF' hx hy hhx hhy himage
      (coordinateProductBoundaryLine hx.symm hy.symm L.1)
    have htarget :
        coordinateProductBoundaryLine hx hy
          (coordinateProductBoundaryLine hx.symm hy.symm L.1) ∈
          completeBoundaryLines F' hF' := by
      rw [hcomp]
      exact L.2
    exact htransport.mp htarget⟩
  left_inv L := by
    apply Subtype.ext
    exact coordinateProductBoundaryLine_symm_comp hx hy L.1
  right_inv L := by
    apply Subtype.ext
    exact coordinateProductBoundaryLine_comp_symm hx hy L.1

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private def axisTranslatedVertexScalar
    (C : ApproximationContext.{0}) (axis : Axis)
    (v : ↥C.region.vertices) (t : ↥C.centres) : C.coordinateSpace := by
  cases axis with
  | horizontal =>
      exact ⟨v.1.re + t.1.re, C.coordinateSpace.add_mem
        (C.vertex_re_mem v.1 v.2) (C.centre_re_mem t.1 t.2)⟩
  | vertical =>
      exact ⟨v.1.im + t.1.im, C.coordinateSpace.add_mem
        (C.vertex_im_mem v.1 v.2) (C.centre_im_mem t.1 t.2)⟩

private theorem axisTranslatedVertexScalar_coe
    (C : ApproximationContext.{0}) (axis : Axis)
    (v : ↥C.region.vertices) (t : ↥C.centres) :
    (axisTranslatedVertexScalar C axis v t : ℝ) = axis.coord (v.1 + t.1) := by
  cases axis <;> rfl

private theorem mapped_axisTranslatedVertexScalar
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (v : ↥C.region.vertices) (t : ↥C.centres) :
    mapScalar phi (axisTranslatedVertexScalar C axis v t) =
      axis.coord (D.planarHomeomorph v.1 + Tphi t) := by
  rw [D.vertex_agreement v.1 v.2, hTphi t]
  cases axis <;>
    simp only [axisTranslatedVertexScalar, Axis.coord, mapPoint, mapScalar,
      ApproximationContext.vertexPoint, ApproximationContext.centrePoint,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add, sub_zero]
  all_goals
    norm_cast
    rw [← map_add]
    rfl

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private def properVertices_coordinateProductEquiv
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F) :
    ↥(properVertices F) ≃ ↥(properVertices F') := by
  let H := coordinateProductHomeomorph hx hy
  have hproper (x : Tiling.Plane) : H x ∈ properVertices F' ↔ x ∈ properVertices F :=
    properVertex_coordinateProductImage_iff F F' hF.1 hF.2.1 hF
      hF'.1 hF'.2.1 hF' hx hy hmx hmy himage x
  exact {
    toFun := fun x => ⟨H x.1, (hproper x.1).2 x.2⟩
    invFun := fun x => ⟨H.symm x.1, (hproper (H.symm x.1)).1
      (by simpa only [H.apply_symm_apply] using x.2)⟩
    left_inv := fun x => Subtype.ext (H.symm_apply_apply x.1)
    right_inv := fun x => Subtype.ext (H.apply_symm_apply x.1) }

private theorem rowProperVertex_targetFormula
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S) =
      coordinateProductHomeomorph hx hy ''
        regularSupport C.region (Subtype.val '' S))
    (hvertices : ∀ (v : ↥C.region.vertices) (s : S),
      coordinateProductHomeomorph hx hy (v.1 + s.1.1) =
        D.planarHomeomorph v.1 + Tphi s.1)
    (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S))))
    (v : ↥C.region.vertices) (s : S) (hxs : x.1 = v.1 + s.1.1) :
    (properVertices_coordinateProductEquiv _ _ hSource hTarget hx hy
      hmx hmy himage x).1 = D.planarHomeomorph v.1 + Tphi s.1 := by
  change coordinateProductHomeomorph hx hy x.1 = _
  rw [hxs]
  exact hvertices v s

private theorem coordinateProductEquiv_conePreserved
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (x : ↥(properVertices F)) :
    localCone F x.1 hF x.2 =
      localCone F' (properVertices_coordinateProductEquiv F F' hF hF' hx hy
        hmx hmy himage x).1 hF' (properVertices_coordinateProductEquiv F F' hF hF'
          hx hy hmx hmy himage x).2 := by
  exact (localCone_coordinateProductImage F F' hF hF' hx hy hmx hmy
    himage x.1 x.2 (properVertices_coordinateProductEquiv F F' hF hF' hx hy
      hmx hmy himage x).2).symm

private theorem coordinateProductLineEquiv_axis
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (L : ↥(completeBoundaryLines F hF)) :
    (completeBoundaryLines_coordinateProductEquiv F F' hF hF' hx hy
      hmx hmy himage L).1.axis = L.1.axis := rfl

private theorem coordinateProductLineEquiv_insideSide
    (F F' : Set Tiling.Plane)
    (hF : IsLocallyAxisParallelPolygonal F)
    (hF' : IsLocallyAxisParallelPolygonal F')
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : F' = coordinateProductHomeomorph hx hy '' F)
    (L : ↥(completeBoundaryLines F hF)) :
    (completeBoundaryLines_coordinateProductEquiv F F' hF hF' hx hy
      hmx hmy himage L).1.insideOnPositiveSide = L.1.insideOnPositiveSide := rfl

private theorem rowProperVertex_sourceProvenance
    {C : ApproximationContext.{0}} (S : Set ↥C.centres)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S)))) :
    ∃ (v : ↥C.region.vertices) (t : S), x.1 = v.1 + t.1.1 := by
  obtain ⟨v, hv, t, ht, hxt⟩ := Tiling.AxisParallel.properVertexProvenance
    hPacking x.1 x.2
  obtain ⟨s, hs, hst⟩ := ht
  refine ⟨⟨v, hv⟩, ⟨s, hs⟩, ?_⟩
  simpa only [hst] using hxt

private def rowCompleteLineLevelLift
    (C : ApproximationContext.{0}) (axis : Axis) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (O : AlignedCompleteLineOrigins C axis S hSource)
    (L : ↥(completeBoundaryLines _ hSource)) : C.coordinateSpace :=
  axisTranslatedVertexScalar C axis.swap (O.completeLineVertex L) O.anchor.1

private theorem rowCompleteLineLevelLift_coe
    (C : ApproximationContext.{0}) (axis : Axis) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (O : AlignedCompleteLineOrigins C axis S hSource)
    (L : ↥(completeBoundaryLines _ hSource)) :
    (rowCompleteLineLevelLift C axis S hSource O L : ℝ) = L.1.level := by
  rw [rowCompleteLineLevelLift, axisTranslatedVertexScalar_coe]
  have hswap (z : Tiling.Plane) : axis.swap.coord z = axis.transverseCoord z := by
    cases axis <;> rfl
  rw [hswap, transverseCoord_add, O.centres_aligned O.anchor]
  exact (O.completeLine_origin L).symm

private theorem rowCompleteLineLevelLift_formula
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (O : AlignedCompleteLineOrigins C axis S hSource)
    (hx hy : ℝ ≃ₜ ℝ)
    (hvertices : ∀ (v : ↥C.region.vertices) (s : S),
      coordinateProductHomeomorph hx hy (v.1 + s.1.1) =
        D.planarHomeomorph v.1 + Tphi s.1)
    (L : ↥(completeBoundaryLines _ hSource)) :
    (coordinateProductBoundaryLine hx hy L.1).level =
      mapScalar phi (rowCompleteLineLevelLift C axis S hSource O L) := by
  have hformula := hvertices (O.completeLineVertex L) O.anchor
  have hswap (z : Tiling.Plane) : axis.swap.coord z = axis.transverseCoord z := by
    cases axis <;> rfl
  have hsourceLevel : axis.transverseCoord
      ((O.completeLineVertex L).1 + O.anchor.1.1) = L.1.level := by
    rw [transverseCoord_add, O.centres_aligned O.anchor]
    exact (O.completeLine_origin L).symm
  rw [rowCompleteLineLevelLift,
    mapped_axisTranslatedVertexScalar phi D Tphi hTphi, hswap, ← hformula]
  have hax := O.completeLine_axis L
  cases axis <;>
    simp only [coordinateProductBoundaryLine, hax, Axis.transverseCoord,
      coordinateProductHomeomorph_apply, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add,
      sub_zero] at hsourceLevel ⊢ <;>
    exact congrArg _ hsourceLevel.symm

private theorem axisBoundaryCode_of_rowCoordinateHomeomorph
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
    (O : AlignedCompleteLineOrigins C axis S hSource)
    (hx hy : ℝ ≃ₜ ℝ) (hmx : StrictMono hx) (hmy : StrictMono hy)
    (himage : regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S) =
      coordinateProductHomeomorph hx hy ''
        regularSupport C.region (Subtype.val '' S))
    (hvertices : ∀ (v : ↥C.region.vertices) (s : S),
      coordinateProductHomeomorph hx hy (v.1 + s.1.1) =
        D.planarHomeomorph v.1 + Tphi s.1) :
    Nonempty (AxisBoundaryCodeTransport C phi D Tphi S hSource hTarget) := by
  let F := regularSupport C.region (Subtype.val '' S)
  let F' := regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)
  let eVertex := properVertices_coordinateProductEquiv F F' hSource hTarget
    hx hy hmx hmy himage
  let eLine := completeBoundaryLines_coordinateProductEquiv F F' hSource hTarget
    hx hy hmx hmy himage
  let lift := rowCompleteLineLevelLift C axis S hSource O
  refine ⟨{
    properVertexEquiv := eVertex
    source_provenance := rowProperVertex_sourceProvenance S hPacking
    target_formula := rowProperVertex_targetFormula phi D Tphi S hSource hTarget
      hx hy hmx hmy himage hvertices
    cone_preserved := coordinateProductEquiv_conePreserved F F' hSource hTarget
      hx hy hmx hmy himage
    completeLineEquiv := eLine
    completeLine_axis := coordinateProductLineEquiv_axis F F' hSource hTarget
      hx hy hmx hmy himage
    completeLine_insideSide := coordinateProductLineEquiv_insideSide F F' hSource hTarget
      hx hy hmx hmy himage
    completeLineLevelLift := lift
    completeLineLevelLift_coe := rowCompleteLineLevelLift_coe C axis S hSource O
    completeLineLevel_formula := rowCompleteLineLevelLift_formula phi D Tphi hTphi
      axis S hSource O hx hy hvertices }⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private def alignedVertexCoordinateGrid
    (C : ApproximationContext.{0}) (axis : Axis) (S : Set ↥C.centres) : Set ℝ :=
  {r | ∃ v ∈ C.region.vertices, ∃ s : S,
    r = axis.coord v + axis.coord s.1.1}

private theorem alignedVertexCoordinateGrid_nonempty
    {C : ApproximationContext.{0}} (axis : Axis) (S : Set ↥C.centres)
    (hS : S.Nonempty) :
    (alignedVertexCoordinateGrid C axis S).Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair C.region
  exact ⟨axis.coord v + axis.coord s, v, hv, ⟨s, hs⟩, rfl⟩

private theorem alignedVertexCoordinateGrid_coordinate_mem
    {C : ApproximationContext.{0}} (axis : Axis) (S : Set ↥C.centres)
    (x : ℝ) (hx : x ∈ alignedVertexCoordinateGrid C axis S) :
    x ∈ C.coordinateSpace := by
  rcases hx with ⟨v, hv, s, rfl⟩
  cases axis with
  | horizontal =>
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v hv)
        (C.centre_re_mem s.1.1 s.1.2)
  | vertical =>
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v hv)
        (C.centre_im_mem s.1.1 s.1.2)

private theorem alignedVertexCoordinateGrid_periodic
    {C : ApproximationContext.{0}} (axis : Axis) (S : Set ↥C.centres)
    (tau : Tiling.Plane)
    (hperiod : tau +ᵥ Subtype.val '' S = Subtype.val '' S) :
    axis.coord tau +ᵥ alignedVertexCoordinateGrid C axis S =
      alignedVertexCoordinateGrid C axis S := by
  have hcoordAdd (x y : Tiling.Plane) :
      axis.coord (x + y) = axis.coord x + axis.coord y := by
    cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
  have hshift (s : S) :
      ∃ t : S, t.1.1 = tau + s.1.1 := by
    have hs : tau + s.1.1 ∈ Subtype.val '' S := by
      rw [← hperiod]
      exact Set.mem_vadd_set.mpr ⟨s.1.1, ⟨s.1, s.2, rfl⟩, rfl⟩
    rcases hs with ⟨t, ht, hts⟩
    exact ⟨⟨t, ht⟩, hts⟩
  have hshiftBack (s : S) :
      ∃ t : S, s.1.1 = tau + t.1.1 := by
    have hs : s.1.1 ∈ tau +ᵥ Subtype.val '' S := by
      rw [hperiod]
      exact ⟨s.1, s.2, rfl⟩
    rcases Set.mem_vadd_set.mp hs with ⟨t, ht, hts⟩
    rcases ht with ⟨u, hu, hut⟩
    have hut' : u = t := by simpa using hut
    exact ⟨⟨u, hu⟩, by simpa [hut'] using hts.symm⟩
  ext x
  constructor
  · intro hx
    rcases Set.mem_vadd_set.mp hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨v, hv, s, rfl⟩
    rcases hshift s with ⟨t, ht⟩
    refine ⟨v, hv, t, ?_⟩
    calc
      x = axis.coord tau + (axis.coord v + axis.coord s.1.1) := hxy.symm
      _ = axis.coord v + axis.coord (tau + s.1.1) := by rw [hcoordAdd]; abel
      _ = axis.coord v + axis.coord t.1.1 := by rw [← ht]
  · intro hx
    rcases hx with ⟨v, hv, s, rfl⟩
    rcases hshiftBack s with ⟨t, ht⟩
    refine Set.mem_vadd_set.mpr ⟨axis.coord v + axis.coord t.1.1, ?_, ?_⟩
    · exact ⟨v, hv, t, rfl⟩
    · calc
        axis.coord tau + (axis.coord v + axis.coord t.1.1) =
            axis.coord v + axis.coord (tau + t.1.1) := by rw [hcoordAdd]; abel
        _ = axis.coord v + axis.coord s.1.1 := by rw [ht]

private theorem alignedVertexCoordinateGrid_locallyFinite
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (axis : Axis) (S : Set ↥C.centres) (sourceLevel : ℝ)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (alignedVertexCoordinateGrid C axis S ∩ Q).Finite := by
  classical
  let V : Set Tiling.Plane := C.region.vertices + (Subtype.val '' S)
  have hverticesFinite : C.region.vertices.Finite := by
    rw [← C.region.coe_vertexFinset]
    exact C.region.vertexFinset.finite_toSet
  let Rset : Set ℝ := axis.transverseCoord '' C.region.vertices
  have hRfinite : Rset.Finite := hverticesFinite.image _
  obtain ⟨M, hM⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hRfinite.isBounded
  have htransBound (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      |axis.transverseCoord v| ≤ M := by
    have hv' : axis.transverseCoord v ∈ Rset := ⟨v, hv, rfl⟩
    have hball := hM hv'
    simpa [Metric.mem_closedBall, Real.dist_eq] using hball
  have htranslated : HasFLC C.translatedVertices := by
    rw [ApproximationContext.translatedVertices, ← C.region.coe_vertexFinset, add_comm]
    exact P.source_hasFLC.add_finset C.region.vertexFinset
  have hVsubset : V ⊆ C.translatedVertices := by
    intro z hz
    rcases hz with ⟨v, hv, t, ht, hvt⟩
    refine ⟨v, hv, t, ?_, hvt⟩
    rw [Set.mem_image] at ht
    rcases ht with ⟨s, hs, rfl⟩
    exact s.2
  have hVlocal : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q → (V ∩ Q).Finite := by
    intro Q hQ
    apply (htranslated.1 Q hQ).subset
    intro z hz
    exact ⟨hVsubset hz.1, hz.2⟩
  intro Q hQ
  obtain ⟨R, hQR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hQ
  let T : ℝ := M + |sourceLevel| + 1
  let B : Set Tiling.Plane := match axis with
    | .horizontal => Icc (-R) R ×ℂ Icc (-T) T
    | .vertical => Icc (-T) T ×ℂ Icc (-R) R
  have hB : Bornology.IsBounded B := by
    cases axis <;> simp only [B] <;>
      exact (Metric.isBounded_Icc _ _).reProdIm (Metric.isBounded_Icc _ _)
  have hVfinite : (V ∩ B).Finite := hVlocal B hB
  have hEfinite :
      (axis.coord '' (V ∩ B)).Finite := hVfinite.image _
  have hcoordAdd (x y : Tiling.Plane) :
      axis.coord (x + y) = axis.coord x + axis.coord y := by
    cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
  apply hEfinite.subset
  intro x hx
  change x ∈ alignedVertexCoordinateGrid C axis S ∧ x ∈ Q at hx
  rcases hx with ⟨hxE, hxQ⟩
  rcases hxE with ⟨v, hv, s, hs, rfl⟩
  let z := v + s.1.1
  have hzCoord : axis.coord z = axis.coord v + axis.coord s.1.1 := by
    change axis.coord (v + s.1.1) = _
    exact hcoordAdd v s.1.1
  have hxCoord : axis.coord z ∈ Q := by simpa [hzCoord] using hxQ
  have hxBound : |axis.coord z| ≤ R := by
    have h := hQR hxCoord
    simpa [Metric.mem_closedBall, Real.dist_eq] using h
  have htrans : axis.transverseCoord z =
      axis.transverseCoord v + sourceLevel := by
    have h := hAligned s
    cases axis <;> simp [z, Axis.transverseCoord, Complex.add_re,
      Complex.add_im] at h ⊢ <;> linarith
  have hzTransAbs : |axis.transverseCoord z| ≤ T := by
    rw [htrans]
    have habs := abs_add_le (axis.transverseCoord v) sourceLevel
    dsimp [T]
    linarith [htransBound v hv]
  have hzB : z ∈ B := by
    cases axis with
    | horizontal =>
        change z.re ∈ Icc (-R) R ∧ z.im ∈ Icc (-T) T
        exact ⟨abs_le.mp hxBound, abs_le.mp hzTransAbs⟩
    | vertical =>
        change z.re ∈ Icc (-T) T ∧ z.im ∈ Icc (-R) R
        exact ⟨abs_le.mp hzTransAbs, abs_le.mp hxBound⟩
  have hzV : z ∈ V := by
    change ∃ v ∈ C.region.vertices, ∃ y ∈ Subtype.val '' S, v + y = z
    refine ⟨v, hv, s.1.1, ?_, rfl⟩
    exact ⟨s.1, s.2, rfl⟩
  rw [← hzCoord]
  exact Set.mem_image_of_mem axis.coord
    (show z ∈ V ∩ B from ⟨hzV, hzB⟩)

private def axisControlledScalar
    (C : ApproximationContext.{0}) (axis : Axis) (a : ControlledDisplacement C) :
    C.coordinateSpace := by
  cases axis with
  | horizontal => exact ⟨a.1.re, a.2.1⟩
  | vertical => exact ⟨a.1.im, a.2.2⟩

private theorem axisControlledScalar_coe
    (C : ApproximationContext.{0}) (axis : Axis) (a : ControlledDisplacement C) :
    (axisControlledScalar C axis a : ℝ) = axis.coord a.1 := by
  cases axis <;> rfl

private theorem neg_period_of_period
    (a : Tiling.Plane) (S : Set Tiling.Plane) (h : a +ᵥ S = S) :
    -a +ᵥ S = S := by
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · intro hx
    have hax : a + x ∈ S := by simpa using hx
    rw [← h] at hax
    obtain ⟨y, hy, hya⟩ := hax
    have hyx : y = x := by simpa using hya
    simpa [hyx] using hy
  · intro hx
    have hax : a + x ∈ a +ᵥ S := ⟨x, hx, rfl⟩
    rw [h] at hax
    simpa using hax

private theorem alignedRowCoordinateExtension
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres)
    (alpha : ControlledDisplacement C)
    (hS : S.Nonempty)
    (hperiod : alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S)
    (hAlphaNonzero : axis.coord alpha.1 ≠ 0)
    (hfinite : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (alignedVertexCoordinateGrid C axis S ∩ Q).Finite)
    (hlabelOrder : ∀ (v : ↥C.region.vertices) (s : S)
      (w : ↥C.region.vertices) (t : S),
      axis.coord (v.1 + s.1.1) < axis.coord (w.1 + t.1.1) →
      axis.coord (D.planarHomeomorph v.1 + Tphi s.1) <
        axis.coord (D.planarHomeomorph w.1 + Tphi t.1)) :
    ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧
      (∀ x (hx : x ∈ alignedVertexCoordinateGrid C axis S),
        H x = mapScalar phi ⟨x, alignedVertexCoordinateGrid_coordinate_mem axis S x hx⟩) ∧
      ∃ beta : ControlledDisplacement C,
        0 < axis.coord beta.1 ∧
        (∀ x, H (x + axis.coord beta.1) =
          H x + mapScalar phi (axisControlledScalar C axis beta)) := by
  classical
  let E := alignedVertexCoordinateGrid C axis S
  let negAlpha : ControlledDisplacement C := ⟨-alpha.1,
    C.coordinateSpace.neg_mem alpha.2.1,
    C.coordinateSpace.neg_mem alpha.2.2⟩
  let beta : ControlledDisplacement C :=
    if h : 0 < axis.coord alpha.1 then alpha else negAlpha
  have hbetaPos : 0 < axis.coord beta.1 := by
    dsimp [beta]
    split_ifs with h
    · exact h
    · have hn : axis.coord alpha.1 < 0 := by
        rcases lt_or_gt_of_ne hAlphaNonzero with hneg | hpos
        · exact hneg
        · exact False.elim (h hpos)
      have hcoordNeg : axis.coord negAlpha.1 = -axis.coord alpha.1 := by
        cases axis <;> simp [negAlpha, Axis.coord]
      rw [hcoordNeg]
      exact neg_pos.mpr hn
  have hbetaPeriod : beta.1 +ᵥ Subtype.val '' S = Subtype.val '' S := by
    dsimp [beta]
    split_ifs with h
    · exact hperiod
    · exact neg_period_of_period alpha.1 (Subtype.val '' S) hperiod
  let p : C.coordinateSpace := axisControlledScalar C axis beta
  have hp : 0 < (p : ℝ) := by
    rw [axisControlledScalar_coe]
    exact hbetaPos
  have hEcoord : ∀ x ∈ E, x ∈ C.coordinateSpace := by
    intro x hx
    exact alignedVertexCoordinateGrid_coordinate_mem axis S x hx
  have hne : E.Nonempty := alignedVertexCoordinateGrid_nonempty axis S hS
  have hEperiod : (p : ℝ) +ᵥ E = E := by
    rw [axisControlledScalar_coe]
    exact alignedVertexCoordinateGrid_periodic axis S beta.1 hbetaPeriod
  have horder : ∀ x y : E, x.1 < y.1 →
      mapScalar phi ⟨x.1, hEcoord x.1 x.2⟩ <
        mapScalar phi ⟨y.1, hEcoord y.1 y.2⟩ := by
    intro x y hxy
    rcases x.2 with ⟨v, hv, s, hxv⟩
    rcases y.2 with ⟨w, hw, t, hyw⟩
    rw [hxv, hyw] at hxy
    have hcoordAdd (a b : Tiling.Plane) :
        axis.coord (a + b) = axis.coord a + axis.coord b := by
      cases axis <;> simp [Axis.coord, Complex.add_re, Complex.add_im]
    have hsourceV : axis.coord (v + s.1.1) = axis.coord v + axis.coord s.1.1 :=
      hcoordAdd v s.1.1
    have hsourceW : axis.coord (w + t.1.1) = axis.coord w + axis.coord t.1.1 :=
      hcoordAdd w t.1.1
    have hcoordVmem : axis.coord v + axis.coord s.1.1 ∈ C.coordinateSpace :=
      hEcoord _ ⟨v, hv, s, rfl⟩
    have hcoordWmem : axis.coord w + axis.coord t.1.1 ∈ C.coordinateSpace :=
      hEcoord _ ⟨w, hw, t, rfl⟩
    have hscalarX :
        (⟨x.1, hEcoord x.1 x.2⟩ : C.coordinateSpace) =
          ⟨axis.coord v + axis.coord s.1.1, hcoordVmem⟩ := by
      apply Subtype.ext
      exact hxv
    have hscalarY :
        (⟨y.1, hEcoord y.1 y.2⟩ : C.coordinateSpace) =
          ⟨axis.coord w + axis.coord t.1.1, hcoordWmem⟩ := by
      apply Subtype.ext
      exact hyw
    have hscalarV :
        (⟨axis.coord v + axis.coord s.1.1, hcoordVmem⟩ : C.coordinateSpace) =
          axisTranslatedVertexScalar C axis ⟨v, hv⟩ s.1 := by
      apply Subtype.ext
      calc
        axis.coord v + axis.coord s.1.1 = axis.coord (v + s.1.1) := hsourceV.symm
        _ = (axisTranslatedVertexScalar C axis ⟨v, hv⟩ s.1 : ℝ) :=
          (axisTranslatedVertexScalar_coe C axis ⟨v, hv⟩ s.1).symm
    have hscalarW :
        (⟨axis.coord w + axis.coord t.1.1, hcoordWmem⟩ : C.coordinateSpace) =
          axisTranslatedVertexScalar C axis ⟨w, hw⟩ t.1 := by
      apply Subtype.ext
      calc
        axis.coord w + axis.coord t.1.1 = axis.coord (w + t.1.1) := hsourceW.symm
        _ = (axisTranslatedVertexScalar C axis ⟨w, hw⟩ t.1 : ℝ) :=
          (axisTranslatedVertexScalar_coe C axis ⟨w, hw⟩ t.1).symm
    have htargetV := mapped_axisTranslatedVertexScalar phi D Tphi hTphi
      axis ⟨v, hv⟩ s.1
    have htargetW := mapped_axisTranslatedVertexScalar phi D Tphi hTphi
      axis ⟨w, hw⟩ t.1
    rw [hscalarX, hscalarY, hscalarV, hscalarW, htargetV, htargetW]
    apply hlabelOrder ⟨v, hv⟩ s ⟨w, hw⟩ t
    simpa [hsourceV, hsourceW] using hxy
  obtain ⟨H, hH, hknots, hHp⟩ := orderedPeriodicCoordinateSet_extension
    phi E hEcoord hne hfinite p hp hEperiod horder
  refine ⟨H, hH, hknots, beta, hbetaPos, ?_⟩
  intro x
  have hpc : (p : ℝ) = axis.coord beta.1 := by
    change (axisControlledScalar C axis beta : ℝ) = axis.coord beta.1
    exact axisControlledScalar_coe C axis beta
  simpa only [hpc] using hHp x


private def rowTransverseHomeomorph (h : ℝ ≃ₜ ℝ) (c c' : ℝ) : ℝ ≃ₜ ℝ :=
  ((Homeomorph.addRight (-c)).trans h).trans (Homeomorph.addRight c')

private theorem rowTransverseHomeomorph_strictMono
    (h : ℝ ≃ₜ ℝ) (hm : StrictMono h) (c c' : ℝ) :
    StrictMono (rowTransverseHomeomorph h c c') := by
  intro x y hxy
  change h (x + -c) + c' < h (y + -c) + c'
  simpa only [add_comm] using
    add_lt_add_right (hm (add_lt_add_right hxy (-c))) c'

private theorem rowCoordinateFactors_of_alongVertexAgreement
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (axis : Axis) (S : Set ↥C.centres) (c c' : ℝ)
    (halign : ∀ s : S, axis.transverseCoord s.1.1 = c)
    (halign' : ∀ s : S, axis.transverseCoord (Tphi s.1) = c')
    (hAlong : ℝ ≃ₜ ℝ) (hAlongMono : StrictMono hAlong)
    (hknots : ∀ (v : ↥C.region.vertices) (s : S),
      hAlong (axis.coord (v.1 + s.1.1)) =
        axis.coord (D.planarHomeomorph v.1 + Tphi s.1)) :
    ∃ hx hy : ℝ ≃ₜ ℝ, StrictMono hx ∧ StrictMono hy ∧
      (∀ (v : ↥C.region.vertices) (s : S),
        coordinateProductHomeomorph hx hy (v.1 + s.1.1) =
          D.planarHomeomorph v.1 + Tphi s.1) ∧
      (∀ q x : ℝ, coordinateProductHomeomorph hx hy (axisPoint axis (c + q) x) =
        axisPoint axis (c' + axis.transverseCoord
          (D.planarHomeomorph (axisPoint axis q 0))) (hAlong x)) := by
  cases axis with
  | horizontal =>
      refine ⟨hAlong, rowTransverseHomeomorph D.secondHomeomorph c c',
        hAlongMono, rowTransverseHomeomorph_strictMono _
          D.secondHomeomorph_strictMono _ _, ?_, ?_⟩
      · intro v s
        apply Complex.ext
        · simpa only [coordinateProductHomeomorph_apply, Axis.coord,
            Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
            Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
            using hknots v s
        · have hs := halign s
          have hs' := halign' s
          change s.1.1.im = c at hs
          change (Tphi s.1).im = c' at hs'
          simp [coordinateProductHomeomorph_apply, rowTransverseHomeomorph,
            D.planarHomeomorph_apply, hs, hs']
      · intro q x
        apply Complex.ext <;>
          simp [coordinateProductHomeomorph_apply, rowTransverseHomeomorph,
            axisPoint, Axis.transverseCoord, D.planarHomeomorph_apply, add_comm]
  | vertical =>
      refine ⟨rowTransverseHomeomorph D.firstHomeomorph c c', hAlong,
        rowTransverseHomeomorph_strictMono _ D.firstHomeomorph_strictMono _ _,
        hAlongMono, ?_, ?_⟩
      · intro v s
        apply Complex.ext
        · have hs := halign s
          have hs' := halign' s
          change s.1.1.re = c at hs
          change (Tphi s.1).re = c' at hs'
          simp [coordinateProductHomeomorph_apply, rowTransverseHomeomorph,
            D.planarHomeomorph_apply, hs, hs']
        · simpa only [coordinateProductHomeomorph_apply, Axis.coord,
            Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
            using hknots v s
      · intro q x
        apply Complex.ext <;>
          simp [coordinateProductHomeomorph_apply, rowTransverseHomeomorph,
            axisPoint, Axis.transverseCoord, D.planarHomeomorph_apply, add_comm]

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem alignedRowGeometry_of_labelOrder
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (S : Set ↥C.centres) (c c' : ℝ)
    (hS : S.Nonempty)
    (halign : ∀ s : S, axis.transverseCoord s.1.1 = c)
    (halign' : ∀ s : S, axis.transverseCoord (Tphi s.1) = c')
    (alpha : ControlledDisplacement C)
    (hperiod : alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S)
    (hAlphaNonzero : axis.coord alpha.1 ≠ 0)
    (hlabelOrder : ∀ (v : ↥C.region.vertices) (s : S)
      (w : ↥C.region.vertices) (t : S),
      axis.coord (v.1 + s.1.1) < axis.coord (w.1 + t.1.1) →
      axis.coord (D.planarHomeomorph v.1 + Tphi s.1) <
        axis.coord (D.planarHomeomorph w.1 + Tphi t.1)) :
    ∃ hAlong hx hy : ℝ ≃ₜ ℝ,
      StrictMono hAlong ∧ StrictMono hx ∧ StrictMono hy ∧
      (∀ (v : ↥C.region.vertices) (s : S),
        hAlong (axis.coord (v.1 + s.1.1)) =
          axis.coord (D.planarHomeomorph v.1 + Tphi s.1)) ∧
      (∀ (v : ↥C.region.vertices) (s : S),
        coordinateProductHomeomorph hx hy (v.1 + s.1.1) =
          D.planarHomeomorph v.1 + Tphi s.1) ∧
      openUnion D.deformedRegion (deformedCenterCarrierOn Tphi S) =
        coordinateProductHomeomorph hx hy '' openUnion C.region (Subtype.val '' S) ∧
      regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S) =
        coordinateProductHomeomorph hx hy ''
          regularSupport C.region (Subtype.val '' S) ∧
      (∀ q x : ℝ, coordinateProductHomeomorph hx hy (axisPoint axis (c + q) x) =
        axisPoint axis (c' + axis.transverseCoord
          (D.planarHomeomorph (axisPoint axis q 0))) (hAlong x)) := by
  obtain ⟨hAlong, hAlongMono, hknots, _beta, _hbetaPos, _hAlongPeriod⟩ :=
    alignedRowCoordinateExtension phi D Tphi hTphi axis S alpha hS hperiod
      hAlphaNonzero (alignedVertexCoordinateGrid_locallyFinite P axis S c halign)
      hlabelOrder
  have hAlongVertices (v : ↥C.region.vertices) (s : S) :
      hAlong (axis.coord (v.1 + s.1.1)) =
        axis.coord (D.planarHomeomorph v.1 + Tphi s.1) := by
    have hmem : axis.coord (v.1 + s.1.1) ∈ alignedVertexCoordinateGrid C axis S := by
      refine ⟨v.1, v.2, s, ?_⟩
      cases axis <;> rfl
    have h := hknots (axis.coord (v.1 + s.1.1)) hmem
    have hscalar : (⟨axis.coord (v.1 + s.1.1),
        alignedVertexCoordinateGrid_coordinate_mem axis S _ hmem⟩ :
        C.coordinateSpace) = axisTranslatedVertexScalar C axis v s.1 := by
      apply Subtype.ext
      exact (axisTranslatedVertexScalar_coe C axis v s.1).symm
    rw [hscalar, mapped_axisTranslatedVertexScalar phi D Tphi hTphi] at h
    exact h
  obtain ⟨hx, hy, hmx, hmy, hvertices, hfibres⟩ :=
    rowCoordinateFactors_of_alongVertexAgreement D Tphi axis S c c'
      halign halign' hAlong hAlongMono hAlongVertices
  have hDproduct : coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph =
      D.planarHomeomorph := by
    ext z
    rw [coordinateProductHomeomorph_apply]
    exact (D.planarHomeomorph_apply z).symm
  have htiles (s : S) :
      coordinateProductHomeomorph hx hy '' (s.1.1 +ᵥ C.region.openCarrier) =
        Tphi s.1 +ᵥ D.deformedRegion.openCarrier := by
    have ht := coordinateProduct_tileImage_of_vertexAgreement C.region hx hy
      D.firstHomeomorph D.secondHomeomorph hmx hmy D.firstHomeomorph_strictMono
      D.secondHomeomorph_strictMono s.1.1 (Tphi s.1) (by
        intro v hv
        rw [hDproduct, add_comm s.1.1 v, add_comm (Tphi s.1)]
        exact hvertices ⟨v, hv⟩ s)
    rw [hDproduct, ← D.deformedRegion_openCarrier] at ht
    exact ht
  obtain ⟨hunion, hsupport⟩ := placedTileImages_openUnion_and_regularSupport
    D Tphi S (coordinateProductHomeomorph hx hy) htiles
  exact ⟨hAlong, hx, hy, hAlongMono, hmx, hmy, hAlongVertices,
    hvertices, hunion, hsupport, hfibres⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem t06_linkedCut_crossing
    {r : ℝ} {U A : Set Tiling.Plane}
    (hLinked : Linked r U) (hA : A ⊆ U)
    {x y : Tiling.Plane} (hx : x ∈ A) (hy : y ∈ U) (hynot : y ∉ A) :
    ∃ u ∈ A, ∃ v ∈ U \ A, dist u v < r := by
  obtain ⟨_, hconn⟩ := hLinked
  have hpath := hconn x (hA hx) y hy
  have hcut : ∀ {a b : Tiling.Plane},
      Relation.ReflTransGen
        (fun u v : Tiling.Plane => u ∈ U ∧ v ∈ U ∧ dist u v < r) a b →
      a ∈ A → b ∉ A → ∃ u ∈ A, ∃ v ∈ U \ A, dist u v < r := by
    intro a b hab
    induction hab with
    | refl =>
        intro ha hb
        exact (hb ha).elim
    | @tail c d hprev hedge ih =>
        intro ha hd
        rcases hedge with ⟨hcU, hdU, hdist⟩
        by_cases hcA : c ∈ A
        · exact ⟨c, hcA, d, ⟨hdU, hd⟩, hdist⟩
        · exact ih ha hcA
  exact hcut hpath hx hynot

private theorem t06_alignedRow_consecutiveGap_lt
    {r : ℝ} {U : Set Tiling.Plane} (axis : Axis)
    (hLinked : Linked r U) {x y : Tiling.Plane}
    (hx : x ∈ U) (hy : y ∈ U)
    (hxy : axis.coord x < axis.coord y)
    (hNoBetween : ∀ z ∈ U, axis.coord x < axis.coord z →
      axis.coord z < axis.coord y → False) :
    axis.coord y - axis.coord x < r := by
  let A : Set Tiling.Plane := {z ∈ U | axis.coord z ≤ axis.coord x}
  have hA : A ⊆ U := by
    intro z hz
    exact hz.1
  have hxA : x ∈ A := ⟨hx, le_rfl⟩
  have hyA : y ∉ A := by
    intro h
    exact (not_le_of_gt hxy) h.2
  obtain ⟨u, huA, v, hvDiff, huv⟩ :=
    t06_linkedCut_crossing hLinked hA hxA hy hyA
  have huvSource : axis.coord v - axis.coord u < r := by
    have hproj : |axis.coord (u - v)| ≤ dist u v := by
      cases axis with
      | horizontal =>
          simpa [Axis.coord, Complex.dist_eq] using Complex.abs_re_le_norm (u - v)
      | vertical =>
          simpa [Axis.coord, Complex.dist_eq] using Complex.abs_im_le_norm (u - v)
    have hu : axis.coord u ≤ axis.coord x := huA.2
    have hvx : axis.coord x < axis.coord v := by
      by_contra h
      exact hvDiff.2 ⟨hvDiff.1, le_of_not_gt h⟩
    have hvy : axis.coord y ≤ axis.coord v := by
      by_contra h
      exact hNoBetween v hvDiff.1 hvx (lt_of_not_ge h)
    have hpos : 0 ≤ axis.coord v - axis.coord u := by linarith
    have habs : |axis.coord (u - v)| = axis.coord v - axis.coord u := by
      rw [show axis.coord (u - v) = -(axis.coord v - axis.coord u) by
        cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im]]
      rw [abs_neg]
      exact abs_of_nonneg hpos
    rw [habs] at hproj
    have hdist : dist u v < r := huv
    exact lt_of_le_of_lt hproj hdist
  have hu : axis.coord u ≤ axis.coord x := huA.2
  have hv : axis.coord y ≤ axis.coord v := by
    have hxv : axis.coord x < axis.coord v := by
      by_contra h
      exact hvDiff.2 ⟨hvDiff.1, le_of_not_gt h⟩
    by_contra h
    exact hNoBetween v hvDiff.1 hxv (lt_of_not_ge h)
  linarith

private theorem t06_dist_eq_abs_axisCoord_of_transverse_eq
    (axis : Axis) (p q : Tiling.Plane)
    (htrans : axis.transverseCoord p = axis.transverseCoord q) :
    dist p q = |axis.coord (p - q)| := by
  cases axis with
  | horizontal =>
      have him : p.im - q.im = 0 := by
        simpa [Axis.transverseCoord] using sub_eq_zero.mpr htrans
      rw [Complex.dist_eq, Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      rw [him]
      rw [show (p.re - q.re) * (p.re - q.re) = (p.re - q.re) ^ 2 by ring]
      simp only [zero_mul, add_zero, Axis.coord, Complex.sub_re]
      exact Real.sqrt_sq_eq_abs _
  | vertical =>
      have hre : p.re - q.re = 0 := by
        simpa [Axis.transverseCoord] using sub_eq_zero.mpr htrans
      rw [Complex.dist_eq, Complex.norm_def]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      rw [hre]
      rw [show (p.im - q.im) * (p.im - q.im) = (p.im - q.im) ^ 2 by ring]
      simp only [zero_mul, zero_add, Axis.coord, Complex.sub_im]
      exact Real.sqrt_sq_eq_abs _

private theorem t06_alignedCoordinateInterval_finite
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (S : Set ↥C.centres) (axis : Axis) (sourceLevel : ℝ)
    (hS : S.Nonempty)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel)
    (a b : ℝ) :
    {z : Tiling.Plane | z ∈ Subtype.val '' S ∧
      axis.coord z ∈ Icc a b}.Finite := by
  let U : Set Tiling.Plane := Subtype.val '' S
  obtain ⟨s₀, hs₀⟩ := hS
  let anchor : Tiling.Plane := s₀.1
  let R : ℝ := |a| + |b| + |axis.coord anchor| + 1
  let Q : Set Tiling.Plane := Metric.closedBall anchor R
  have hQ : Bornology.IsBounded Q := Metric.isBounded_closedBall
  have hlocal := P.source_hasFLC.1 Q hQ
  have hfinite : (C.centres ∩ Q).Finite := hlocal
  apply hfinite.subset
  intro z hz
  rcases hz.1 with ⟨s, hs, rfl⟩
  have htrans : axis.transverseCoord anchor =
      axis.transverseCoord (s : Tiling.Plane) := by
    calc
      axis.transverseCoord anchor = sourceLevel := hAligned ⟨s₀, hs₀⟩
      _ = axis.transverseCoord (s : Tiling.Plane) := (hAligned ⟨s, hs⟩).symm
  have hdist : dist anchor (s : Tiling.Plane) =
      |axis.coord (anchor - (s : Tiling.Plane))| :=
    t06_dist_eq_abs_axisCoord_of_transverse_eq axis anchor s htrans
  have hcoord : axis.coord (anchor - (s : Tiling.Plane)) =
      axis.coord anchor - axis.coord (s : Tiling.Plane) := by
    cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im]
  have hlevel : axis.coord (s : Tiling.Plane) ∈ Icc a b := hz.2
  have hlevelAbs : |axis.coord (s : Tiling.Plane)| ≤ |a| + |b| := by
    apply abs_le.mpr
    constructor <;> rcases hlevel with ⟨ha, hb⟩
    · linarith [neg_abs_le a, le_abs_self b, abs_nonneg b]
    · linarith [le_abs_self a, le_abs_self b, abs_nonneg a]
  have hdiffAbs : |axis.coord anchor - axis.coord (s : Tiling.Plane)| ≤ R := by
    have htri := abs_sub_le (axis.coord anchor) 0 (axis.coord (s : Tiling.Plane))
    rw [sub_zero, zero_sub, abs_neg] at htri
    dsimp [R]
    linarith [htri, hlevelAbs]
  have hball : (s : Tiling.Plane) ∈ Q := by
    change (s : Tiling.Plane) ∈ Metric.closedBall anchor R
    rw [Metric.mem_closedBall, dist_comm]
    rw [hdist, hcoord]
    exact hdiffAbs
  exact ⟨s.2, hball⟩

private theorem t06_strictMono_of_consecutive
    {E : Set ℝ}
    (hlocal : ∀ a b : ℝ,
      {x : E | x.1 ∈ Icc a b}.Finite)
    (f : E → ℝ)
    (hstep : ∀ x y : E, x.1 < y.1 →
      (∀ z : E, x.1 < z.1 → z.1 < y.1 → False) → f x < f y) :
    StrictMono f := by
  have haux : ∀ n : ℕ, ∀ x y : E,
      x.1 < y.1 →
      ((hlocal x.1 y.1).toFinset.card = n) → f x < f y := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x y hxy hcard
        let Fxy := (hlocal x.1 y.1).toFinset
        by_cases hmid : ∃ z : E, x.1 < z.1 ∧ z.1 < y.1
        · rcases hmid with ⟨z, hxz, hzy⟩
          let Fxz := (hlocal x.1 z.1).toFinset
          let Fzy := (hlocal z.1 y.1).toFinset
          have hFxzsub : Fxz ⊆ Fxy := by
            intro q hq
            have hq' : q.1 ∈ Icc x.1 z.1 := by
              simpa [Fxz, Set.mem_Icc] using hq
            have hq'' : q.1 ∈ Icc x.1 y.1 := by
              rcases hq' with ⟨hleft, hright⟩
              exact ⟨hleft, le_of_lt (lt_of_le_of_lt hright hzy)⟩
            simpa [Fxy, Set.mem_Icc] using hq''
          have hFzysub : Fzy ⊆ Fxy := by
            intro q hq
            have hq' : q.1 ∈ Icc z.1 y.1 := by
              simpa [Fzy, Set.mem_Icc] using hq
            have hq'' : q.1 ∈ Icc x.1 y.1 := by
              rcases hq' with ⟨hleft, hright⟩
              exact ⟨le_trans (le_of_lt hxz) hleft, hright⟩
            simpa [Fxy, Set.mem_Icc] using hq''
          have hyFxy : y ∈ Fxy := by
            simpa [Fxy, Set.mem_Icc] using
              (show y.1 ∈ Icc x.1 y.1 from ⟨le_of_lt hxy, le_rfl⟩)
          have hy_not_Fxz : y ∉ Fxz := by
            intro hy
            have hy' : y.1 ∈ Icc x.1 z.1 := by
              simpa [Fxz, Set.mem_Icc] using hy
            exact (not_le_of_gt hzy) hy'.2
          have hxFxy : x ∈ Fxy := by
            simpa [Fxy, Set.mem_Icc] using
              (show x.1 ∈ Icc x.1 y.1 from ⟨le_rfl, le_of_lt hxy⟩)
          have hx_not_Fzy : x ∉ Fzy := by
            intro hx
            have hx' : x.1 ∈ Icc z.1 y.1 := by
              simpa [Fzy, Set.mem_Icc] using hx
            exact (not_le_of_gt hxz) hx'.1
          have hFxzlt : Fxz.card < Fxy.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨hFxzsub, by
                intro heq
                exact hy_not_Fxz (heq.symm ▸ hyFxy)⟩)
          have hFzylt : Fzy.card < Fxy.card :=
            Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
              ⟨hFzysub, by
                intro heq
                exact hx_not_Fzy (heq.symm ▸ hxFxy)⟩)
          rw [hcard] at hFxzlt hFzylt
          have hleft := ih Fxz.card hFxzlt x z hxz rfl
          have hright := ih Fzy.card hFzylt z y hzy rfl
          exact lt_trans hleft hright
        · exact hstep x y hxy (by
            intro z hxz hzy
            exact hmid ⟨z, hxz, hzy⟩)
  intro x y hxy
  exact haux _ x y hxy rfl

private def t06_axisCoordScalar
    (C : ApproximationContext.{0}) (axis : Axis)
    (s : ↥C.centres) : C.coordinateSpace :=
  match axis with
  | .horizontal => ⟨s.1.re, C.centre_re_mem s.1 s.2⟩
  | .vertical => ⟨s.1.im, C.centre_im_mem s.1 s.2⟩

private theorem t06_axisCoordScalar_val
    {C : ApproximationContext.{0}} (axis : Axis) (s : ↥C.centres) :
    (t06_axisCoordScalar C axis s : ℝ) = axis.coord (s : Tiling.Plane) := by
  cases axis <;> rfl

private theorem t06_axisCoord_mapPoint_centre
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (axis : Axis)
    (s : ↥C.centres) :
    axis.coord (mapPoint phi (C.centrePoint s.1 s.2)) =
      mapScalar phi (t06_axisCoordScalar C axis s) := by
  cases axis with
  | horizontal =>
      simp [t06_axisCoordScalar, Axis.coord, mapPoint, mapScalar,
        ApproximationContext.centrePoint, Complex.add_re,
        Complex.mul_re, Complex.I_re, Complex.I_im]
  | vertical =>
      simp [t06_axisCoordScalar, Axis.coord, mapPoint, mapScalar,
        ApproximationContext.centrePoint, Complex.add_im,
        Complex.I_re, Complex.I_im]

private theorem t06_axisCoord_centre_mem
    {C : ApproximationContext.{0}} (axis : Axis) (s : ↥C.centres) :
    axis.coord (s : Tiling.Plane) ∈ C.coordinateSpace := by
  cases axis with
  | horizontal => exact C.centre_re_mem s.1 s.2
  | vertical => exact C.centre_im_mem s.1 s.2

private theorem t06_centerLevelSet_locallyFinite
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (S : Set ↥C.centres) (axis : Axis) (sourceLevel : ℝ)
    (hS : S.Nonempty)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel) :
    let E : Set ℝ := {r | ∃ s : S, axis.coord s.1.1 = r}
    ∀ a b : ℝ, {r : E | r.1 ∈ Icc a b}.Finite := by
  classical
  intro E a b
  let U : Set Tiling.Plane := Subtype.val '' S
  let H : Set Tiling.Plane := {z | z ∈ U ∧ axis.coord z ∈ Icc a b}
  have hH : H.Finite := by
    exact t06_alignedCoordinateInterval_finite P S axis sourceLevel hS hAligned a b
  have himage : (axis.coord '' H).Finite := hH.image axis.coord
  refine Set.Finite.of_injOn
    (s := {r : E | r.1 ∈ Icc a b})
    (t := axis.coord '' H) (f := fun r : E => r.1) ?_ ?_ himage
  · intro r hr
    let s : S := Classical.choose r.2
    have hcoord : axis.coord s.1.1 = r.1 := Classical.choose_spec r.2
    have hinterval : axis.coord (s : Tiling.Plane) ∈ Icc a b := by
      exact hcoord.symm ▸ hr
    have hsH : (s : Tiling.Plane) ∈ H := by
      exact ⟨⟨s, s.2, rfl⟩, hinterval⟩
    exact ⟨(s : Tiling.Plane), hsH, hcoord⟩
  · intro r hr s hs heq
    exact Subtype.ext heq

private theorem t06_axisCoord_abs_le_dist
    (axis : Axis) (p q : Tiling.Plane) :
    |axis.coord (p - q)| ≤ dist p q := by
  cases axis with
  | horizontal =>
      simpa [Axis.coord, Complex.dist_eq] using Complex.abs_re_le_norm (p - q)
  | vertical =>
      simpa [Axis.coord, Complex.dist_eq] using Complex.abs_im_le_norm (p - q)

private theorem t06_centerMap_halfSlope
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres) (axis : Axis) (sourceLevel : ℝ) (G δ : ℝ)
    (hS : S.Nonempty)
    (hLinked : Linked G (Subtype.val '' S)) (hG : G < P.scale)
    (_hδ : 0 < δ)
    (hSep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist (s : Tiling.Plane) t)
    (hError : P.localError < δ / 2)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = sourceLevel) :
    let E : Set ℝ := {r | ∃ s : S, axis.coord s.1.1 = r}
    ∀ x y : E, x.1 < y.1 →
      mapScalar phi ⟨y.1, by
        rcases y.2 with ⟨s, hcoord⟩
        exact hcoord ▸ t06_axisCoord_centre_mem axis s.1⟩ -
        mapScalar phi ⟨x.1, by
          rcases x.2 with ⟨s, hcoord⟩
          exact hcoord ▸ t06_axisCoord_centre_mem axis s.1⟩ > (y.1 - x.1) / 2 := by
  classical
  intro E
  let coordScalar : ∀ x : E, C.coordinateSpace := fun x => by
    refine ⟨x.1, ?_⟩
    let s : S := Classical.choose x.2
    have hcoord : axis.coord s.1.1 = x.1 := Classical.choose_spec x.2
    exact hcoord ▸ t06_axisCoord_centre_mem axis s.1
  let f : E → ℝ := fun x => mapScalar phi (coordScalar x)
  have hlocal : ∀ a b : ℝ, {x : E | x.1 ∈ Icc a b}.Finite :=
    t06_centerLevelSet_locallyFinite P S axis sourceLevel hS hAligned
  have hmap (s : S) :
      f ⟨axis.coord s.1.1, ⟨s, rfl⟩⟩ = axis.coord (Tphi s.1) := by
    let x : E := ⟨axis.coord s.1.1, ⟨s, rfl⟩⟩
    have hscalar : coordScalar x = t06_axisCoordScalar C axis s.1 := by
      apply Subtype.ext
      change x.1 = (t06_axisCoordScalar C axis s.1 : ℝ)
      rw [show x.1 = axis.coord (s.1 : Tiling.Plane) by rfl,
        t06_axisCoordScalar_val]
    calc
      f x = mapScalar phi (t06_axisCoordScalar C axis s.1) := by
        simp [f, hscalar]
      _ = axis.coord (mapPoint phi (C.centrePoint s.1.1 s.1.2)) :=
        (t06_axisCoord_mapPoint_centre phi axis s.1).symm
      _ = axis.coord (Tphi s.1) := by rw [← hTphi s.1]
  have hstep : ∀ x y : E, x.1 < y.1 →
      (∀ z : E, x.1 < z.1 → z.1 < y.1 → False) →
      (fun x => f x - x.1 / 2) x < (fun x => f x - x.1 / 2) y := by
    intro x y hxy hNoMid
    let s : S := Classical.choose x.2
    have hscoord : axis.coord s.1.1 = x.1 := Classical.choose_spec x.2
    let t : S := Classical.choose y.2
    have htcoord : axis.coord t.1.1 = y.1 := Classical.choose_spec y.2
    let U : Set Tiling.Plane := Subtype.val '' S
    have hsU : s.1.1 ∈ U := ⟨s, s.2, rfl⟩
    have htU : t.1.1 ∈ U := ⟨t, t.2, rfl⟩
    have hNoBetween : ∀ z ∈ U, axis.coord s.1.1 < axis.coord z →
        axis.coord z < axis.coord t.1.1 → False := by
      intro z hz hsz hzt
      rcases hz with ⟨u, hu, hzu⟩
      let hzlevel : E := ⟨axis.coord u.1, ⟨⟨u, hu⟩, rfl⟩⟩
      apply hNoMid hzlevel
      · have hlevel : (hzlevel : ℝ) = axis.coord (u : Tiling.Plane) := rfl
        rw [hlevel, ← hscoord, hzu]
        exact hsz
      · have hlevel : (hzlevel : ℝ) = axis.coord (u : Tiling.Plane) := rfl
        rw [hlevel, ← htcoord, hzu]
        exact hzt
    have hgap := t06_alignedRow_consecutiveGap_lt axis hLinked hsU htU
      (by simpa [hscoord, htcoord] using hxy) hNoBetween
    have htrans : axis.transverseCoord s.1.1 = axis.transverseCoord t.1.1 := by
      rw [hAligned s, hAligned t]
    have hdistEq := t06_dist_eq_abs_axisCoord_of_transverse_eq axis
      s.1.1 t.1.1 htrans
    have hsourceCoord : axis.coord (s.1.1 - t.1.1) = x.1 - y.1 := by
      rw [show axis.coord (s.1.1 - t.1.1) =
        axis.coord s.1.1 - axis.coord t.1.1 by
          cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im],
        hscoord, htcoord]
    have hdist : dist (s.1.1 : Tiling.Plane) t.1.1 = y.1 - x.1 := by
      rw [hdistEq, hsourceCoord, abs_of_nonpos (by linarith)]
      ring
    have hst : s.1 ≠ t.1 := by
      intro hEq
      have hcoord := congrArg (fun z : Tiling.Plane => axis.coord z)
        (congrArg (fun z : ↥C.centres => (z : Tiling.Plane)) hEq)
      rw [hscoord, htcoord] at hcoord
      exact (ne_of_lt hxy) hcoord
    have hsep := hSep s.1 s.2 t.1 t.2 hst
    rw [hdist] at hsep
    have hcenterControl : dist (centre_vertex s.1) (centre_vertex t.1) < P.scale := by
      change dist (s.1.1 : Tiling.Plane) t.1.1 < P.scale
      rw [hdist]
      exact lt_trans (by simpa [hscoord, htcoord] using hgap) hG
    have hacc := deformation_localAccuracy P phi hphi
      (centre_vertex s.1) (centre_vertex t.1) hcenterControl
    have hcentermap1 := centre_vertex_map phi Tphi hTphi s.1
    have hcentermap2 := centre_vertex_map phi Tphi hTphi t.1
    have hprojected : |(f y - f x) - (y.1 - x.1)| < P.localError := by
      have hproj := t06_axisCoord_abs_le_dist axis
        (mapTranslatedVertex phi (centre_vertex s.1) -
          mapTranslatedVertex phi (centre_vertex t.1))
        ((centre_vertex s.1 : Tiling.Plane) - centre_vertex t.1)
      have hcoord : axis.coord
          ((mapTranslatedVertex phi (centre_vertex s.1) -
            mapTranslatedVertex phi (centre_vertex t.1)) -
            ((centre_vertex s.1 : Tiling.Plane) - centre_vertex t.1)) =
          -((f y - f x) - (y.1 - x.1)) := by
        have hfx : f x = axis.coord (Tphi s.1) := by
          rw [show x = (⟨axis.coord s.1.1, ⟨s, rfl⟩⟩ : E) by
            exact Subtype.ext hscoord.symm]
          exact hmap s
        have hfy : f y = axis.coord (Tphi t.1) := by
          rw [show y = (⟨axis.coord t.1.1, ⟨t, rfl⟩⟩ : E) by
            exact Subtype.ext htcoord.symm]
          exact hmap t
        rw [show axis.coord (_ - _) =
          axis.coord (mapTranslatedVertex phi (centre_vertex s.1) -
            mapTranslatedVertex phi (centre_vertex t.1)) -
          axis.coord ((centre_vertex s.1 : Tiling.Plane) - centre_vertex t.1) by
            cases axis <;> simp [Axis.coord, Complex.sub_re, Complex.sub_im],
          hcentermap1, hcentermap2, hfx, hfy]
        rw [show axis.coord ((centre_vertex s.1 : Tiling.Plane) -
            centre_vertex t.1) = axis.coord s.1.1 - axis.coord t.1.1 by
              cases axis <;> simp [centre_vertex, Axis.coord,
                Complex.sub_re, Complex.sub_im], hscoord, htcoord]
        rw [show axis.coord (Tphi s.1 - Tphi t.1) =
          axis.coord (Tphi s.1) - axis.coord (Tphi t.1) by cases axis <;> rfl]
        ring
      rw [hcoord, abs_neg] at hproj
      exact lt_of_le_of_lt hproj hacc
    have hlower := (abs_lt.mp hprojected).1
    have hgapLower : δ ≤ y.1 - x.1 := by
      simpa [hdist] using hsep
    dsimp
    linarith
  have hgStrict : StrictMono (fun x : E => f x - x.1 / 2) :=
    t06_strictMono_of_consecutive hlocal (fun x => f x - x.1 / 2) hstep
  intro x y hxy
  have h := hgStrict hxy
  dsimp at h
  linarith

private theorem axisCoord_add (axis : Axis) (x y : Tiling.Plane) :
    axis.coord (x + y) = axis.coord x + axis.coord y := by
  cases axis <;> rfl

private theorem axisCoord_sub (axis : Axis) (x y : Tiling.Plane) :
    axis.coord (x - y) = axis.coord x - axis.coord y := by
  cases axis <;> rfl

private theorem linkedRadius_exceedsPackingSeparation
    {C : ApproximationContext.{0}} (S : Set ↥C.centres) (G δ : ℝ)
    (hLinked : Linked G (Subtype.val '' S))
    (hSep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist (s : Tiling.Plane) t)
    (s t : S) (hne : s ≠ t) : δ < G := by
  have hsU : s.1.1 ∈ Subtype.val '' S := ⟨s.1, s.2, rfl⟩
  have htU : t.1.1 ∈ Subtype.val '' S := ⟨t.1, t.2, rfl⟩
  have hst : s.1.1 ≠ t.1.1 := by
    intro h
    exact hne (Subtype.ext (Subtype.ext h))
  have hA : ({s.1.1} : Set Tiling.Plane) ⊆ Subtype.val '' S := by
    intro z hz
    simpa only [Set.mem_singleton_iff.mp hz] using hsU
  obtain ⟨u, hu, v, hv, huv⟩ := t06_linkedCut_crossing hLinked hA
    (Set.mem_singleton _) htU (by
      intro h
      exact hst (Set.mem_singleton_iff.mp h).symm)
  obtain ⟨r, hr, hrv⟩ := hv.1
  have hsr : s.1 ≠ r := by
    intro h
    apply hv.2
    exact Set.mem_singleton_iff.mpr (hrv.symm.trans (congrArg Subtype.val h.symm))
  have hsep := hSep s.1 s.2 r hr hsr
  rw [hrv] at hsep
  rw [Set.mem_singleton_iff.mp hu] at huv
  exact lt_of_le_of_lt hsep huv

private theorem intrinsicVertex_mem_support
    (K : Region) (v : Tiling.Plane) (hv : v ∈ K.vertices) : v ∈ K.support := by
  rw [← K.isPolygonal.closure_interior]
  exact frontier_subset_closure
    (Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K hv)

private def translatedVertexLabel
    (C : ApproximationContext.{0}) (v : ↥C.region.vertices) (s : ↥C.centres) :
    ↥C.translatedVertices := ⟨v.1 + s.1, v.1, v.2, s.1, s.2, rfl⟩

private theorem translatedVertexLabel_map
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ s, Tphi s = mapPoint phi (C.centrePoint s.1 s.2))
    (v : ↥C.region.vertices) (s : ↥C.centres) :
    mapTranslatedVertex phi (translatedVertexLabel C v s) =
      D.planarHomeomorph v.1 + Tphi s := by
  rw [D.vertex_agreement v.1 v.2, hTphi s, mapTranslatedVertex]
  have hpoint : C.translatedVertexPoint (translatedVertexLabel C v s) =
      ⟨(C.vertexPoint v.1 v.2).1 + (C.centrePoint s.1 s.2).1,
        C.coordinateSpace.add_mem (C.vertexPoint v.1 v.2).2.1
          (C.centrePoint s.1 s.2).2.1,
        C.coordinateSpace.add_mem (C.vertexPoint v.1 v.2).2.2
          (C.centrePoint s.1 s.2).2.2⟩ := by
    apply Subtype.ext
    rfl
  rw [hpoint]
  exact mapPoint_add_local phi (C.vertexPoint v.1 v.2) (C.centrePoint s.1 s.2)

private theorem alignedCentres_halfSlope
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ s, Tphi s = mapPoint phi (C.centrePoint s.1 s.2))
    (S : Set ↥C.centres) (axis : Axis) (c G δ : ℝ)
    (hS : S.Nonempty) (hLinked : Linked G (Subtype.val '' S))
    (hG : G < P.scale) (hδ : 0 < δ)
    (hSep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist (s : Tiling.Plane) t)
    (hError : P.localError < δ / 2)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = c)
    (s t : S) (hst : axis.coord s.1.1 < axis.coord t.1.1) :
    (axis.coord t.1.1 - axis.coord s.1.1) / 2 <
      axis.coord (Tphi t.1) - axis.coord (Tphi s.1) := by
  have h := t06_centerMap_halfSlope P phi hphi Tphi hTphi S axis c G δ
    hS hLinked hG hδ hSep hError hAligned
    ⟨axis.coord s.1.1, ⟨s, rfl⟩⟩ ⟨axis.coord t.1.1, ⟨t, rfl⟩⟩ hst
  have h' : (axis.coord t.1.1 - axis.coord s.1.1) / 2 <
      mapScalar phi (t06_axisCoordScalar C axis t.1) -
        mapScalar phi (t06_axisCoordScalar C axis s.1) := by
    cases axis <;> exact h
  rw [← t06_axisCoord_mapPoint_centre phi axis t.1,
    ← t06_axisCoord_mapPoint_centre phi axis s.1, ← hTphi t.1, ← hTphi s.1] at h'
  exact h'

private theorem mappedTranslatedPair_axis_positive
    {C : ApproximationContext} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (axis : Axis) (a b : ↥C.translatedVertices)
    (hab : dist (a : Tiling.Plane) b < P.controlRadius)
    (hpositive : 0 < axis.coord ((a : Tiling.Plane) - b)) :
    0 < axis.coord (mapTranslatedVertex phi a - mapTranslatedVertex phi b) := by
  have hreflect := deformation_reflectsFiniteValues P phi hphi axis a b a b hab hab
  have hsign := hreflect.1
  rw [Real.sign_of_pos hpositive] at hsign
  rcases lt_trichotomy
      (axis.coord (mapTranslatedVertex phi a - mapTranslatedVertex phi b)) 0 with
    hnegative | heq | hpositive'
  · rw [Real.sign_of_neg hnegative] at hsign
    norm_num at hsign
  · rw [Real.sign_eq_zero_iff.mpr heq] at hsign
    norm_num at hsign
  · exact hpositive'

private theorem alignedRowLabelOrder
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ s, Tphi s = mapPoint phi (C.centrePoint s.1 s.2))
    (axis : Axis) (S : Set ↥C.centres) (G δ : ℝ) (N : ℕ) (c : ℝ)
    (hS : S.Nonempty) (hLinked : Linked G (Subtype.val '' S))
    (hδ : 0 < δ)
    (hSep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → δ ≤ dist (s : Tiling.Plane) t)
    (hNδ : 4 * Metric.diam C.region.support < (N : ℝ) * δ)
    (hError : P.localError < δ / 2)
    (hScale : (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale)
    (hMargin : G + P.localError < P.scale / 2)
    (hTargetDiameter : Metric.diam D.deformedRegion.support ≤
      2 * Metric.diam C.region.support)
    (hAligned : ∀ s : S, axis.transverseCoord s.1.1 = c)
    (v : ↥C.region.vertices) (s : S) (w : ↥C.region.vertices) (t : S)
    (hsource : axis.coord (v.1 + s.1.1) < axis.coord (w.1 + t.1.1)) :
    axis.coord (D.planarHomeomorph v.1 + Tphi s.1) <
      axis.coord (D.planarHomeomorph w.1 + Tphi t.1) := by
  have hG : G < P.scale := by linarith [P.localError_pos, P.scale_pos]
  let d := Metric.diam C.region.support
  have hd : 0 < d := by
    have heq : Metric.diam C.region.support = Metric.diam C.region.openCarrier := by
      change Metric.diam C.region.support = Metric.diam (interior C.region.support)
      nth_rewrite 1 [← C.region.isPolygonal.closure_interior]
      exact Metric.diam_closure _
    dsimp [d]
    rw [heq]
    exact region_openCarrier_diam_pos C.region
  have hv := intrinsicVertex_mem_support C.region v.1 v.2
  have hw := intrinsicVertex_mem_support C.region w.1 w.2
  have hvw : dist v.1 w.1 ≤ d :=
    Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded hv hw
  have hsourceVertices : |axis.coord v.1 - axis.coord w.1| ≤ d := by
    simpa only [axisCoord_sub] using
      (t06_axisCoord_abs_le_dist axis v.1 w.1).trans hvw
  have hDv : D.planarHomeomorph v.1 ∈ D.deformedRegion.support := by
    apply intrinsicVertex_mem_support
    rw [D.vertices_image]
    exact ⟨v.1, v.2, rfl⟩
  have hDw : D.planarHomeomorph w.1 ∈ D.deformedRegion.support := by
    apply intrinsicVertex_mem_support
    rw [D.vertices_image]
    exact ⟨w.1, w.2, rfl⟩
  have htargetVertices :
      |axis.coord (D.planarHomeomorph v.1) - axis.coord (D.planarHomeomorph w.1)| ≤
        2 * d := by
    have hdist := Metric.dist_le_diam_of_mem
      D.deformedRegion.isPolygonal.isBounded hDv hDw
    simpa only [axisCoord_sub] using
      (t06_axisCoord_abs_le_dist axis (D.planarHomeomorph v.1)
        (D.planarHomeomorph w.1)).trans (hdist.trans hTargetDiameter)
  rw [axisCoord_add, axisCoord_add] at hsource ⊢
  by_cases hst : s = t
  · subst t
    have hvwCoord : axis.coord v.1 < axis.coord w.1 := by linarith
    have himage : axis.coord (D.planarHomeomorph v.1) <
        axis.coord (D.planarHomeomorph w.1) := by
      cases axis with
      | horizontal =>
          simpa [Axis.coord, D.planarHomeomorph_apply] using
            D.firstHomeomorph_strictMono hvwCoord
      | vertical =>
          simpa [Axis.coord, D.planarHomeomorph_apply] using
            D.secondHomeomorph_strictMono hvwCoord
    linarith
  · have hδG := linkedRadius_exceedsPackingSeparation S G δ hLinked hSep s t hst
    have hNG : 4 * d < (N : ℝ) * G :=
      lt_of_lt_of_le hNδ (mul_le_mul_of_nonneg_left hδG.le (Nat.cast_nonneg N))
    by_cases hlarge : 4 * d ≤ |axis.coord s.1.1 - axis.coord t.1.1|
    · have hcentreOrder : axis.coord s.1.1 < axis.coord t.1.1 := by
        by_contra hnot
        have hle := le_of_not_gt hnot
        rw [abs_of_nonneg (sub_nonneg.mpr hle)] at hlarge
        have hvertexLower := (abs_le.mp hsourceVertices).1
        linarith
      have hfour : 4 * d ≤ axis.coord t.1.1 - axis.coord s.1.1 := by
        simpa only [abs_of_nonpos (sub_nonpos.mpr hcentreOrder.le), neg_sub]
          using hlarge
      have hhalf := alignedCentres_halfSlope P phi hphi Tphi hTphi S axis c G δ
        hS hLinked hG hδ hSep hError hAligned s t hcentreOrder
      have hvertexUpper := (abs_le.mp htargetVertices).2
      linarith
    · have hsmall : |axis.coord s.1.1 - axis.coord t.1.1| < 4 * d :=
        lt_of_not_ge hlarge
      have hcentreDist : dist s.1.1 t.1.1 =
          |axis.coord s.1.1 - axis.coord t.1.1| := by
        rw [t06_dist_eq_abs_axisCoord_of_transverse_eq axis s.1.1 t.1.1
          ((hAligned s).trans (hAligned t).symm), axisCoord_sub]
      have htriangle : dist (v.1 + s.1.1) (w.1 + t.1.1) ≤
          dist v.1 w.1 + dist s.1.1 t.1.1 := by
        calc
          dist (v.1 + s.1.1) (w.1 + t.1.1) ≤
              dist (v.1 + s.1.1) (w.1 + s.1.1) +
                dist (w.1 + s.1.1) (w.1 + t.1.1) := dist_triangle _ _ _
          _ = _ := by rw [dist_add_right, dist_add_left]
      have hcontrol : dist (translatedVertexLabel C w t.1 : Tiling.Plane)
          (translatedVertexLabel C v s.1) < P.controlRadius := by
        change dist (w.1 + t.1.1) (v.1 + s.1.1) < P.controlRadius
        rw [dist_comm]
        rw [hcentreDist] at htriangle
        have hbound : dist (v.1 + s.1.1) (w.1 + t.1.1) <
            (N : ℝ) * G + 2 * Metric.diam C.region.support := by
          dsimp [d] at hd hvw hNG hsmall
          linarith
        exact hbound.trans (hScale.trans P.scale_lt_controlRadius)
      have hpositive : 0 < axis.coord
          ((translatedVertexLabel C w t.1 : Tiling.Plane) -
            translatedVertexLabel C v s.1) := by
        change 0 < axis.coord ((w.1 + t.1.1) - (v.1 + s.1.1))
        rw [axisCoord_sub, axisCoord_add, axisCoord_add]
        linarith
      have himage := mappedTranslatedPair_axis_positive P phi hphi axis
        (translatedVertexLabel C w t.1) (translatedVertexLabel C v s.1)
        hcontrol hpositive
      rw [translatedVertexLabel_map phi D Tphi hTphi,
        translatedVertexLabel_map phi D Tphi hTphi,
        axisCoord_sub, axisCoord_add, axisCoord_add] at himage
      linarith

private def IsTransverseGridCell
    (K : Region) (axis : Axis) (I : Set ℝ) : Prop :=
  I.Nonempty ∧ IsOpen I ∧ IsPreconnected I ∧
    I ∩ (IntrinsicVertices.intrinsicCoordinateLevels K axis.swap : Set ℝ) = ∅ ∧
    ∀ J : Set ℝ, J.Nonempty → IsOpen J → IsPreconnected J →
      J ∩ (IntrinsicVertices.intrinsicCoordinateLevels K axis.swap : Set ℝ) = ∅ →
      I ⊆ J → J ⊆ I

/-- An actual intrinsic vertex and indexed centre witnessing an endpoint of a tile section. -/
private structure LabelledSectionEndpoint
    (C : ApproximationContext.{0}) (axis : Axis)
    (S : Set ↥C.centres) (q : ℝ) where
  vertex : ↥C.region.vertices
  center : S
  endpoint : axis.coord vertex.1 ∈ frontier (axisSection C.region axis q)

private def LabelledSectionEndpoint.value
    {C : ApproximationContext.{0}} {axis : Axis}
    {S : Set ↥C.centres} {q : ℝ}
    (e : LabelledSectionEndpoint C axis S q) : ℝ :=
  axis.coord e.vertex.1 + axis.coord e.center.1.1

private structure GlobalAxisLineCodeTransport
    (C : ApproximationContext.{0}) (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (axis : Axis)
    (S : Set ↥C.centres) where
  mappedEndpoint : ∀ {q}, LabelledSectionEndpoint C axis S q → ℝ
  mappedEndpoint_formula : ∀ {q} (e : LabelledSectionEndpoint C axis S q),
    mappedEndpoint e = axis.coord
      (D.planarHomeomorph e.vertex.1 + Tphi e.center.1)
  weakOrder_iff : ∀ {q q'}
      (e : LabelledSectionEndpoint C axis S q)
      (f : LabelledSectionEndpoint C axis S q'),
    e.value ≤ f.value ↔ mappedEndpoint e ≤ mappedEndpoint f
  cell_full_iff : ∀ I q,
    IsTransverseGridCell C.region axis I → q ∈ I →
    (regularizedAxisSectionUnion C.region axis (Subtype.val '' S) q = univ ↔
      regularizedAxisSectionUnion D.deformedRegion axis
        {t | ∃ s : S, t = Tphi s.1} (axis.transverseCoord
          (D.planarHomeomorph (axisPoint axis q 0))) = univ)
  cell_empty_iff : ∀ I q,
    IsTransverseGridCell C.region axis I → q ∈ I →
    (regularizedAxisSectionUnion C.region axis (Subtype.val '' S) q = ∅ ↔
      regularizedAxisSectionUnion D.deformedRegion axis
        {t | ∃ s : S, t = Tphi s.1} (axis.transverseCoord
          (D.planarHomeomorph (axisPoint axis q 0))) = ∅)

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem globalAxisLineCodeTransport_construct :
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (S : Set ↥C.centres) (G : ℝ) (N : ℕ),
      S.Nonempty → Linked G (Subtype.val '' S) →
      ∀ (delta : ℝ), 0 < delta →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s.1.1 t.1.1) →
      (N : ℝ) * delta > 4 * Metric.diam C.region.support →
      P.localError < delta / 2 →
      (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale →
      G + P.localError < P.scale / 2 →
      Metric.diam D.deformedRegion.support ≤ 2 * Metric.diam C.region.support →
      (∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) →
      (∃ p, p ≠ 0 ∧ axis.transverseCoord p = 0 ∧
        p +ᵥ deformedCenterCarrierOn Tphi S = deformedCenterCarrierOn Tphi S) →
      Nonempty (GlobalAxisLineCodeTransport C P phi D Tphi axis S) := by
  intro C P phi hphi D Tphi hTphi axis S G N hS hLinked delta hdelta
    hSep hNdelta hError hScale hMargin hDiameter hImageAligned hImagePeriod
  have hG : G < P.scale := by linarith [P.localError_pos, P.scale_pos]
  have hSepPlane : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) t := by
    intro s hs t ht hst
    apply (hSep s hs t ht hst).trans
    simpa only [Axis.coord, Complex.sub_re, Real.dist_eq] using
      t06_axisCoord_abs_le_dist Axis.horizontal (s : Tiling.Plane) t
  obtain ⟨c, hAligned⟩ := sourceAxisAligned_of_imageAxisAligned P phi hphi Tphi hTphi
    axis S G hLinked hG hImageAligned
  obtain ⟨p, hp, hpAxis, hpPeriod⟩ := hImagePeriod
  obtain ⟨alpha, halpha, halphaAxis, _hMapAlpha, halphaPeriod⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S G hS
      hLinked.2 hImageAligned hG hMargin p hp hpAxis hpPeriod
  have halphaCoord : axis.coord alpha.1 ≠ 0 := by
    intro hz
    apply halpha
    cases axis with
    | horizontal => exact Complex.ext hz halphaAxis
    | vertical => exact Complex.ext halphaAxis hz
  obtain ⟨c', hAligned'⟩ := hImageAligned
  obtain ⟨hAlong, hx, hy, hAlongMono, _hmx, _hmy, hAlongVertices,
      _hVertices, hUnion, _hSupport, hFibres⟩ :=
    alignedRowGeometry_of_labelOrder P phi D Tphi hTphi axis S c c' hS hAligned
      hAligned' alpha halphaPeriod halphaCoord
      (alignedRowLabelOrder P phi hphi D Tphi hTphi axis S G delta N c hS hLinked
        hdelta hSepPlane hNdelta hError hScale hMargin hDiameter hAligned)
  have hCarrier : {t | ∃ s : S, t = Tphi s.1} = deformedCenterCarrierOn Tphi S := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  have hSourceAligned : ∀ s ∈ Subtype.val '' S, axis.transverseCoord s = c := by
    rintro s ⟨t, ht, rfl⟩
    exact hAligned ⟨t, ht⟩
  have hTargetAligned : ∀ s ∈ deformedCenterCarrierOn Tphi S,
      axis.transverseCoord s = c' := by
    rintro s ⟨t, ht, rfl⟩
    exact hAligned' ⟨t, ht⟩
  have hSection (q : ℝ) : regularizedAxisSectionUnion D.deformedRegion axis
      (deformedCenterCarrierOn Tphi S)
        (axis.transverseCoord (D.planarHomeomorph (axisPoint axis q 0))) =
      hAlong '' regularizedAxisSectionUnion C.region axis (Subtype.val '' S) q :=
    regularizedAxisSectionUnion_image_of_openUnion_image C.region D.deformedRegion
      axis (Subtype.val '' S) (deformedCenterCarrierOn Tphi S) c c' q
      (axis.transverseCoord (D.planarHomeomorph (axisPoint axis q 0)))
      (coordinateProductHomeomorph hx hy) hAlong hSourceAligned hTargetAligned
      hUnion (hFibres q)
  refine ⟨{
    mappedEndpoint := fun {_q} e => axis.coord
      (D.planarHomeomorph e.vertex.1 + Tphi e.center.1)
    mappedEndpoint_formula := fun _ => rfl
    weakOrder_iff := ?_
    cell_full_iff := ?_
    cell_empty_iff := ?_ }⟩
  · intro _q _q' e f
    rw [← hAlongVertices e.vertex e.center, ← hAlongVertices f.vertex f.center]
    dsimp only [LabelledSectionEndpoint.value]
    rw [← axisCoord_add, ← axisCoord_add]
    exact hAlongMono.le_iff_le.symm
  · intro _I q _hI _hq
    rw [hCarrier, hSection q]
    constructor
    · intro hfull
      rw [hfull]
      exact Set.image_univ_of_surjective hAlong.surjective
    · intro hfull
      apply (Set.image_injective.mpr hAlong.injective)
      exact hfull.trans (Set.image_univ_of_surjective hAlong.surjective).symm
  · intro _I q _hI _hq
    rw [hCarrier, hSection q]
    exact Set.image_eq_empty.symm

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem globalAxisBoundaryCodeTransport_exists :
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (S : Set ↥C.centres) (G delta : ℝ) (N : ℕ),
      S.Nonempty → Linked G (Subtype.val '' S) → 0 < delta →
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → delta ≤ dist s.1.1 t.1.1) →
      (N : ℝ) * delta > 4 * Metric.diam C.region.support →
      P.localError < delta / 2 →
      (N : ℝ) * G + 2 * Metric.diam C.region.support < P.scale →
      G + P.localError < P.scale / 2 →
      Metric.diam D.deformedRegion.support ≤ 2 * Metric.diam C.region.support →
      (∃ c : ℝ, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) →
      (∃ imagePeriod : Tiling.Plane, imagePeriod ≠ 0 ∧
        axis.transverseCoord imagePeriod = 0 ∧
        imagePeriod +ᵥ deformedCenterCarrierOn Tphi S = deformedCenterCarrierOn Tphi S) →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S)) →
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S)) →
    ∀ (hSource : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S)))
      (hTarget : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))),
      Nonempty (AxisBoundaryCodeTransport C phi D Tphi S hSource hTarget) := by
  intro C P phi hphi D Tphi hTphi axis S G delta N hS hLinked hdelta hSep
    hNdelta hError hScale hMargin hDiameter hImageAligned hImagePeriod
    hPacking _hTargetPacking hSource hTarget
  have hG : G < P.scale := by linarith [P.localError_pos, P.scale_pos]
  have hSepPlane : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) t := by
    intro s hs t ht hst
    apply (hSep s hs t ht hst).trans
    simpa only [Axis.coord, Complex.sub_re, Real.dist_eq] using
      t06_axisCoord_abs_le_dist Axis.horizontal (s : Tiling.Plane) t
  obtain ⟨c, hAligned⟩ := sourceAxisAligned_of_imageAxisAligned P phi hphi Tphi hTphi
    axis S G hLinked hG hImageAligned
  obtain ⟨p, hp, hpAxis, hpPeriod⟩ := hImagePeriod
  obtain ⟨alpha, halpha, halphaAxis, _hMapAlpha, halphaPeriod⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S G hS
      hLinked.2 hImageAligned hG hMargin p hp hpAxis hpPeriod
  have halphaCoord : axis.coord alpha.1 ≠ 0 := by
    intro hz
    apply halpha
    cases axis with
    | horizontal => exact Complex.ext hz halphaAxis
    | vertical => exact Complex.ext halphaAxis hz
  obtain ⟨c', hAligned'⟩ := hImageAligned
  obtain ⟨_hAlong, hx, hy, _hAlongMono, hmx, hmy, _hAlongVertices,
      hVertices, _hUnion, hSupport, _hFibres⟩ :=
    alignedRowGeometry_of_labelOrder P phi D Tphi hTphi axis S c c' hS hAligned
      hAligned' alpha halphaPeriod halphaCoord
      (alignedRowLabelOrder P phi hphi D Tphi hTphi axis S G delta N c hS hLinked
        hdelta hSepPlane hNdelta hError hScale hMargin hDiameter hAligned)
  obtain ⟨O⟩ := alignedCompleteLineOrigins_construct axis S hPacking hSource hS c hAligned
  exact axisBoundaryCode_of_rowCoordinateHomeomorph phi D Tphi hTphi axis S
    hPacking hSource hTarget O hx hy hmx hmy hSupport hVertices

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem regionSupport_diam_eq_openCarrier (K : Region) :
    Metric.diam K.support = Metric.diam K.openCarrier := by
  change Metric.diam K.support = Metric.diam (interior K.support)
  nth_rewrite 1 [← K.isPolygonal.closure_interior]
  exact Metric.diam_closure _

private theorem deformedRegion_diameter_of_recoveryScale
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (ell delta G : ℝ) (N : ℕ)
    (hscale : t06RecoveryScale C.region ell delta G N < P.scale)
    (hdiamScale : Metric.diam C.region.support < P.scale) :
    Metric.diam D.deformedRegion.support ≤ 2 * Metric.diam C.region.support := by
  have hd : 0 < Metric.diam C.region.support := region_support_diam_pos C.region
  have hrecip : 2 / Metric.diam C.region.support < P.scale :=
    lt_of_le_of_lt (le_max_right _ _) hscale
  have htwo : 0 < 2 / Metric.diam C.region.support := div_pos (by norm_num) hd
  have herror : P.localError < Metric.diam C.region.support / 2 := by
    calc
      P.localError = P.scale⁻¹ := P.localError_eq
      _ < (2 / Metric.diam C.region.support)⁻¹ :=
        (inv_lt_inv₀ P.scale_pos htwo).2 hrecip
      _ = Metric.diam C.region.support / 2 := by field_simp
  have hSupport : D.deformedRegion.support = D.planarHomeomorph '' C.region.support :=
    region_support_image_of_openCarrier_image C.region D.deformedRegion
      D.planarHomeomorph D.deformedRegion_openCarrier
  have hmove : ∀ v ∈ C.region.vertices,
      dist (D.planarHomeomorph v) v ≤ P.localError := by
    intro v hv
    let a : ↥C.translatedVertices :=
      ⟨v, v, hv, 0, C.zero_mem_centres, add_zero v⟩
    let b : ↥C.translatedVertices :=
      ⟨0, 0, C.zero_mem_vertices, 0, C.zero_mem_centres, zero_add 0⟩
    have haMap : mapTranslatedVertex phi a = D.planarHomeomorph v := by
      rw [D.vertex_agreement v hv]
      change mapPoint phi (C.translatedVertexPoint a) = mapPoint phi (C.vertexPoint v hv)
      congr 1
    have hbMap : mapTranslatedVertex phi b = 0 := by
      change (↑(phi 0) : ℝ) + (↑(phi 0) : ℝ) * Complex.I = 0
      simp
    have hvSupport := intrinsicVertex_mem_support C.region v hv
    have h0Support := intrinsicVertex_mem_support C.region 0 C.zero_mem_vertices
    have hab : dist (a : Tiling.Plane) b < P.scale :=
      (Metric.dist_le_diam_of_mem C.region.isPolygonal.isBounded
        hvSupport h0Support).trans_lt hdiamScale
    have hlocal := deformation_localAccuracy P phi hphi a b hab
    rw [haMap, hbMap, sub_zero] at hlocal
    simpa only [a, b, sub_zero] using hlocal.le
  have hdiam := coordinateProductImage_diam_le C.region D.deformedRegion
    D.planarHomeomorph P.localError P.localError_pos.le hSupport D.vertices_image hmove
  rw [← regionSupport_diam_eq_openCarrier C.region,
    ← regionSupport_diam_eq_openCarrier D.deformedRegion] at hdiam
  linarith

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private structure AxisLocalTransportOutput
    (C : ApproximationContext.{0})
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Axis) (S₀ S₁ : Set ↥C.centres)
    (imagePeriod eta : Tiling.Plane) where
  beta : {z : Tiling.Plane //
    z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}
  alpha : {z : Tiling.Plane //
    z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}
  support_eq : regularSupport C.region (Subtype.val '' S₁) =
    beta.1 +ᵥ regularSupport C.region (Subtype.val '' S₀)
  map_beta : mapPoint phi beta = eta
  alpha_ne : alpha.1 ≠ 0
  alpha_aligned : axis.transverseCoord alpha.1 = 0
  period₀ : alpha.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀
  period₁ : alpha.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁
  map_alpha : mapPoint phi alpha = imagePeriod
  proper₀ : properVertices
    (regularSupport C.region (Subtype.val '' S₀)) ≠ ∅
  proper₁ : properVertices
    (regularSupport C.region (Subtype.val '' S₁)) ≠ ∅

private theorem nonColumnableAxisTransport_of_controls :
  ∀ {C : ApproximationContext.{0}} (axis : Axis)
    (_hNoColumn : ¬ ∃ Col : Set Tiling.Plane,
      IsCenterColumn axis C.region Col),
    ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
    ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
    ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C P.threshold phi →
    ∀ (D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (S₀ S₁ : Set ↥C.centres) (G : ℝ),
      G = 60 * Metric.diam C.region.openCarrier →
      S₀.Nonempty → S₁.Nonempty →
      Linked G (Subtype.val '' S₀) → Linked G (Subtype.val '' S₁) →
      (∃ c, ∀ s : S₀, axis.transverseCoord (Tphi s.1) = c) →
      (∃ c, ∀ s : S₁, axis.transverseCoord (Tphi s.1) = c) →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)) →
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S₁)) →
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S₀)) →
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S₁)) →
    ∀ (imagePeriod eta : Tiling.Plane),
      imagePeriod ≠ 0 → axis.transverseCoord imagePeriod = 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₀ =
        deformedCenterCarrierOn Tphi S₀ →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₁ =
        deformedCenterCarrierOn Tphi S₁ →
      regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
        eta +ᵥ regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S₀) →
      Nonempty (AxisLocalTransportOutput C phi axis S₀ S₁ imagePeriod eta) := by
  intro C axis hNoColumn
  obtain ⟨delta, hdelta, hSeparation⟩ := packingUniformSeparation C.region
  obtain ⟨ell, _hell, hProperLinked⟩ :=
    nonColumnable_uniformProperVertexLinked C.region axis hNoColumn
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * Metric.diam C.region.support / delta)
  have hNdelta : 4 * Metric.diam C.region.support < (N : ℝ) * delta :=
    (div_lt_iff₀ hdelta).mp hN
  let G₀ : ℝ := 60 * Metric.diam C.region.openCarrier
  let recoveryScale := t06RecoveryScale C.region ell delta G₀ N
  refine ⟨recoveryScale, (t06RecoveryScale_bounds.{0} C.region ell delta G₀ N hdelta).1, ?_⟩
  intro P hscale phi hphi D Tphi hTphi S₀ S₁ G hGeq hS₀ hS₁ hLinked₀ hLinked₁
    hImageAligned₀ hImageAligned₁ hPacking₀ hPacking₁ hImagePacking₀ hImagePacking₁
    imagePeriod eta hp hpAxis hPeriod₀ hPeriod₁ hTargetSupport
  subst G
  obtain ⟨hError, hEllMargin, hGMargin, hNScale, hDControl, hDScale, _hErrorDiameter⟩ :=
    (t06RecoveryScale_bounds.{0} C.region ell delta G₀ N hdelta).2 rfl P hscale
  have hG : G₀ < P.scale := by linarith [P.localError_pos, P.scale_pos]
  obtain ⟨c₀, hAligned₀⟩ := sourceAxisAligned_of_imageAxisAligned P phi hphi Tphi hTphi
    axis S₀ G₀ hLinked₀ hG hImageAligned₀
  obtain ⟨c₁, hAligned₁⟩ := sourceAxisAligned_of_imageAxisAligned P phi hphi Tphi hTphi
    axis S₁ G₀ hLinked₁ hG hImageAligned₁
  have hSetAligned₀ : ∃ c, ∀ s ∈ Subtype.val '' S₀, axis.transverseCoord s = c := by
    refine ⟨c₀, ?_⟩
    rintro s ⟨t, ht, rfl⟩
    exact hAligned₀ ⟨t, ht⟩
  have hSetAligned₁ : ∃ c, ∀ s ∈ Subtype.val '' S₁, axis.transverseCoord s = c := by
    refine ⟨c₁, ?_⟩
    rintro s ⟨t, ht, rfl⟩
    exact hAligned₁ ⟨t, ht⟩
  have hProper₀ := hProperLinked (Subtype.val '' S₀) hPacking₀
    (hS₀.image Subtype.val) hSetAligned₀ hLinked₀
  have hProper₁ := hProperLinked (Subtype.val '' S₁) hPacking₁
    (hS₁.image Subtype.val) hSetAligned₁ hLinked₁
  have hSource₀ := packing_regularSupport_isLocallyAxisParallelPolygonal hPacking₀
  have hSource₁ := packing_regularSupport_isLocallyAxisParallelPolygonal hPacking₁
  have hTarget₀ := packing_regularSupport_isLocallyAxisParallelPolygonal hImagePacking₀
  have hTarget₁ := packing_regularSupport_isLocallyAxisParallelPolygonal hImagePacking₁
  have hSep₀ : ∀ s ∈ S₀, ∀ t ∈ S₀, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) t := by
    intro s hs t ht hst
    exact hSeparation _ hPacking₀ s ⟨s, hs, rfl⟩ t ⟨t, ht, rfl⟩
      (fun heq => hst (Subtype.ext heq))
  have hSep₁ : ∀ s ∈ S₁, ∀ t ∈ S₁, s ≠ t →
      delta ≤ dist (s : Tiling.Plane) t := by
    intro s hs t ht hst
    exact hSeparation _ hPacking₁ s ⟨s, hs, rfl⟩ t ⟨t, ht, rfl⟩
      (fun heq => hst (Subtype.ext heq))
  have hDiameter := deformedRegion_diameter_of_recoveryScale P phi hphi D
    ell delta G₀ N hscale hDScale
  obtain ⟨alpha₀, halpha₀, haxis₀, hmap₀, hper₀⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S₀ G₀ hS₀
      hLinked₀.2 hImageAligned₀ hG hGMargin imagePeriod hp hpAxis hPeriod₀
  obtain ⟨alpha₁, _halpha₁, _haxis₁, hmap₁, hper₁⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S₁ G₀ hS₁
      hLinked₁.2 hImageAligned₁ hG hGMargin imagePeriod hp hpAxis hPeriod₁
  have halphaCoord₀ : axis.coord alpha₀.1 ≠ 0 := by
    intro hz
    apply halpha₀
    cases axis with
    | horizontal => exact Complex.ext hz haxis₀
    | vertical => exact Complex.ext haxis₀ hz
  have halphaCoord₁ : axis.coord alpha₁.1 ≠ 0 := by
    intro hz
    apply _halpha₁
    cases axis with
    | horizontal => exact Complex.ext hz _haxis₁
    | vertical => exact Complex.ext _haxis₁ hz
  obtain ⟨c₀', hAligned₀'⟩ := hImageAligned₀
  obtain ⟨c₁', hAligned₁'⟩ := hImageAligned₁
  obtain ⟨_hAlong₀, hx₀, hy₀, _hAlongMono₀, hmx₀, hmy₀, _hAlongVertices₀,
      hVertices₀, _hUnion₀, hSupport₀, _hFibres₀⟩ :=
    alignedRowGeometry_of_labelOrder P phi D Tphi hTphi axis S₀ c₀ c₀' hS₀ hAligned₀
      hAligned₀' alpha₀ hper₀ halphaCoord₀
      (alignedRowLabelOrder P phi hphi D Tphi hTphi axis S₀ G₀ delta N c₀ hS₀ hLinked₀
        hdelta hSep₀ hNdelta hError hNScale hGMargin hDiameter hAligned₀)
  obtain ⟨_hAlong₁, hx₁, hy₁, _hAlongMono₁, hmx₁, hmy₁, _hAlongVertices₁,
      hVertices₁, _hUnion₁, hSupport₁, _hFibres₁⟩ :=
    alignedRowGeometry_of_labelOrder P phi D Tphi hTphi axis S₁ c₁ c₁' hS₁ hAligned₁
      hAligned₁' alpha₁ hper₁ halphaCoord₁
      (alignedRowLabelOrder P phi hphi D Tphi hTphi axis S₁ G₀ delta N c₁ hS₁ hLinked₁
        hdelta hSep₁ hNdelta hError hNScale hGMargin hDiameter hAligned₁)
  obtain ⟨O₀⟩ := alignedCompleteLineOrigins_construct axis S₀ hPacking₀ hSource₀
    hS₀ c₀ hAligned₀
  obtain ⟨O₁⟩ := alignedCompleteLineOrigins_construct axis S₁ hPacking₁ hSource₁
    hS₁ c₁ hAligned₁
  obtain ⟨B₀⟩ := axisBoundaryCode_of_rowCoordinateHomeomorph phi D Tphi hTphi axis S₀
    hPacking₀ hSource₀ hTarget₀ O₀ hx₀ hy₀ hmx₀ hmy₀ hSupport₀ hVertices₀
  obtain ⟨B₁⟩ := axisBoundaryCode_of_rowCoordinateHomeomorph phi D Tphi hTphi axis S₁
    hPacking₁ hSource₁ hTarget₁ O₁ hx₁ hy₁ hmx₁ hmy₁ hSupport₁ hVertices₁
  obtain ⟨V⟩ := properVertexTranslation_construct P phi hphi D Tphi hTphi S₀ S₁ ell
    hProper₀ hEllMargin hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ eta hTargetSupport
  obtain ⟨_hLines, hSupport⟩ := completeLineFootprint_of_properVertexTranslation
    P phi hphi hDControl D Tphi hTphi axis S₀ S₁ hSource₀ hSource₁ hTarget₀ hTarget₁
    B₀ B₁ eta hTargetSupport V hProper₀.1 O₀ O₁
  have hProvenance (S : Set ↥C.centres)
      (hPacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S))) :
      properVertices (regularSupport C.region (Subtype.val '' S)) ⊆
        C.translatedVertices := by
    intro x hx
    obtain ⟨v, hv, s, hs, rfl⟩ := Tiling.AxisParallel.properVertexProvenance hPacking x hx
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨v, hv, t, t.2, rfl⟩
  have hAlpha : alpha₀ = alpha₁ :=
    periodLifts_eq_of_properVertexShift P phi hphi S₀ S₁ alpha₀ alpha₁ V.beta
      imagePeriod hmap₀ hmap₁ hper₀ hper₁ (hProvenance S₀ hPacking₀)
      (hProvenance S₁ hPacking₁)
      (fun w hw => by rw [← V.source_formula ⟨w, hw⟩]; exact (V.sourceEquiv ⟨w, hw⟩).2)
      hProper₀.1
  exact ⟨{
    beta := V.beta
    alpha := alpha₀
    support_eq := hSupport
    map_beta := V.map_beta
    alpha_ne := halpha₀
    alpha_aligned := haxis₀
    period₀ := hper₀
    period₁ := by simpa only [hAlpha] using hper₁
    map_alpha := hmap₀
    proper₀ := hProper₀.1.ne_empty
    proper₁ := hProper₁.1.ne_empty }⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

theorem nonColumnableAxisLocalTransport :
    ∀ {C : ApproximationContext.{0}}
    (_hFLC : HasFLC C.centres)
    (axis : Axis)
    (_hNoColumn : ¬ ∃ Col : Set Tiling.Plane,
      IsCenterColumn axis C.region Col),
    ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
      ∀ (P : FLCControlPackage C),
        recoveryScale < P.scale →
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C P.threshold phi →
      ∀ (D : CoordinateDeformation C phi),
      ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
        (∀ t : ↥C.centres,
          Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      ∀ (S₀ S₁ : Set ↥C.centres),
      ∀ (G : ℝ), G = 60 * Metric.diam C.region.openCarrier →
        (Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
            (C.region.toPolygonalRegion.placements (Set.image Subtype.val S₀)) ∧
          Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
            (C.region.toPolygonalRegion.placements (Set.image Subtype.val S₁)) ∧
          Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
            (D.deformedRegion.toPolygonalRegion.placements
              (deformedCenterCarrierOn Tphi S₀)) ∧
          Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
            (D.deformedRegion.toPolygonalRegion.placements
              (deformedCenterCarrierOn Tphi S₁))) →
        S₀.Nonempty ∧ S₁.Nonempty →
        ((∃ c : ℝ, ∀ s : S₀,
            axis.transverseCoord (Tphi (s : ↥C.centres)) = c) ∧
          (∃ c : ℝ, ∀ s : S₁,
            axis.transverseCoord (Tphi (s : ↥C.centres)) = c)) →
        Linked G (Set.image Subtype.val S₀) ∧
          Linked G (Set.image Subtype.val S₁) →
      ∀ (imagePeriod : Tiling.Plane),
        imagePeriod ≠ 0 →
        axis.transverseCoord imagePeriod = 0 →
        (imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₀ =
            deformedCenterCarrierOn Tphi S₀ ∧
          imagePeriod +ᵥ deformedCenterCarrierOn Tphi S₁ =
            deformedCenterCarrierOn Tphi S₁) →
      ∀ (eta : Tiling.Plane),
        regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
            eta +ᵥ regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀) →
        ∃ beta alpha : {z : Tiling.Plane //
            z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          regularSupport C.region (Set.image Subtype.val S₁) =
              (beta : Tiling.Plane) +ᵥ regularSupport C.region (Set.image Subtype.val S₀) ∧
          mapPoint phi beta = eta ∧
          (alpha : Tiling.Plane) ≠ 0 ∧
          axis.transverseCoord (alpha : Tiling.Plane) = 0 ∧
          (alpha : Tiling.Plane) +ᵥ Set.image Subtype.val S₀ =
            Set.image Subtype.val S₀ ∧
          (alpha : Tiling.Plane) +ᵥ Set.image Subtype.val S₁ =
            Set.image Subtype.val S₁ ∧
          mapPoint phi alpha = imagePeriod ∧
          properVertices (regularSupport C.region (Set.image Subtype.val S₀)) ≠ ∅ ∧
          properVertices (regularSupport C.region (Set.image Subtype.val S₁)) ≠ ∅ := by
  intro C _hFLC axis hNoColumn
  obtain ⟨recoveryScale, hpos, hControls⟩ := nonColumnableAxisTransport_of_controls axis hNoColumn
  refine ⟨recoveryScale, hpos, ?_⟩
  intro P hscale phi hphi D Tphi hTphi S₀ S₁ G hGeq hPacking hNonempty
    hAligned hLinked imagePeriod hp hpAxis hPeriod eta hSupport
  obtain ⟨O⟩ := hControls P hscale phi hphi D Tphi hTphi S₀ S₁ G hGeq
    hNonempty.1 hNonempty.2 hLinked.1 hLinked.2 hAligned.1 hAligned.2
    hPacking.1 hPacking.2.1 hPacking.2.2.1 hPacking.2.2.2
    imagePeriod eta hp hpAxis hPeriod.1 hPeriod.2 hSupport
  exact ⟨O.beta, O.alpha, O.support_eq, O.map_beta, O.alpha_ne,
    O.alpha_aligned, O.period₀, O.period₁, O.map_alpha, O.proper₀, O.proper₁⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem orbitPhasePreimage_image
    {K : Region} {ι : Type*} {T : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition K T)
    (i : Fin Dcmp.numberOfParts)
    (Tphi : ι ↪ Tiling.Plane)
    (hRange : Set.range Tphi = T)
    (Q : RationalSlice (Dcmp.direction i)) :
    Tphi '' {t | Tphi t ∈ Q.centres (Dcmp.part i)} =
      Q.centres (Dcmp.part i) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ht
  · intro hx
    have hxT : x ∈ T := by
      rw [← Dcmp.parts_union]
      exact Set.mem_iUnion.2 ⟨i, hx.1⟩
    rw [← hRange] at hxT
    obtain ⟨t, rfl⟩ := Set.mem_range.mp hxT
    exact ⟨t, hx, rfl⟩

private theorem orbitPhasePreimage_nonempty
    {K : Region} {ι : Type*} {Tphi : ι ↪ Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition K (Set.range Tphi))
    (i : Fin Dcmp.numberOfParts)
    {Q : RationalSlice (Dcmp.direction i)}
    (hQ : Q ∈ (Dcmp.orbit i).phases) :
    ({t : ι | Tphi t ∈ Q.centres (Dcmp.part i)}).Nonempty := by
  obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty Q).mp hQ
  have hxT : x ∈ Set.range Tphi := by
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.2 ⟨i, hx.1⟩
  obtain ⟨t, ht⟩ := Set.mem_range.mp hxT
  refine ⟨t, ?_⟩
  change Tphi t ∈ Q.centres (Dcmp.part i)
  simpa [ht] using hx

private theorem sourceSlice_linked_of_noGapPhase
    {K : Region} {ι : Type*} {Tphi : ι ↪ Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition K (Set.range Tphi))
    (i : Fin Dcmp.numberOfParts)
    (sourcePoint : ι → Tiling.Plane)
    (originalSlice : RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hSlice : ∀ Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice Q = Set.image sourcePoint
        {t : ι | Tphi t ∈ Q.centres (Dcmp.part i)})
    {r : ℝ} {Q : RationalSlice (Dcmp.direction i)}
    (hQ : Q ∈ (Dcmp.orbit i).noGapPhases originalSlice r) :
    Linked r (originalSlice Q) := by
  have hNonempty : ∀ Q, Q ∈ (Dcmp.orbit i).phases →
      (originalSlice Q).Nonempty := by
    intro Q hQ
    rw [hSlice Q hQ]
    exact (orbitPhasePreimage_nonempty Dcmp i hQ).image _
  exact (Dcmp.orbit i).linked_originalSlice_of_mem_noGapPhases
    originalSlice hNonempty hQ

private theorem rationalSlice_centres_re_eq_of_vertical_direction
    {u : RationalDirection} (Q : RationalSlice u) (T : Set Tiling.Plane)
    (hvertical : u.toPlane.re = 0)
    {x y : Tiling.Plane}
    (hx : x ∈ Q.centres T) (hy : y ∈ Q.centres T) : x.re = y.re := by
  have hxQ : QuotientAddGroup.mk' (realDirectionSubgroup u) x = Q := by
    change x ∈ T ∧ x ∈ Q.carrier at hx
    rcases hx with ⟨_, hxQ⟩
    change QuotientAddGroup.mk' (realDirectionSubgroup u) x = Q at hxQ
    exact hxQ
  have hyQ : QuotientAddGroup.mk' (realDirectionSubgroup u) y = Q := by
    change y ∈ T ∧ y ∈ Q.carrier at hy
    rcases hy with ⟨_, hyQ⟩
    change QuotientAddGroup.mk' (realDirectionSubgroup u) y = Q at hyQ
    exact hyQ
  have hdiff : x - y ∈ realDirectionSubgroup u :=
    (QuotientAddGroup.eq_iff_sub_mem).mp (hxQ.trans hyQ.symm)
  rcases hdiff with ⟨r, hr⟩
  have hre : (x - y).re = 0 := by
    rw [hr]
    simp [hvertical]
  have : x.re - y.re = 0 := by simpa only [Complex.sub_re] using hre
  linarith

private theorem packing_mono_onCentreCarrier
    (K : Region) {A S : Set Tiling.Plane}
    (hA : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hSA : S ⊆ A) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
  apply (isPacking_iff_openCarrier_disjoint K S).2
  intro x hx y hy hxy
  exact (isPacking_iff_openCarrier_disjoint K A).1 hA
    (hSA hx) (hSA hy) hxy

theorem nonColumnableVerticalNoGapOrbitTransport :
    ∀ {C : ApproximationContext.{0}}
    (_hFLC : HasFLC C.centres)
    (_hNoColumn : ¬ ∃ Col : Set Tiling.Plane,
      IsCenterColumn Axis.vertical C.region Col),
    ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
      ∀ (P : FLCControlPackage C),
        recoveryScale < P.scale →
      ∀ (B : PeriodicBandData C),
        IsPeriodicBandFineness B P.threshold →
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C P.threshold phi →
      ∀ (D : CoordinateDeformation C phi),
      ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
        (∀ t : ↥C.centres,
          Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion
        (Set.range Tphi)),
      ∀ (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
        RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
        (∀ i Q, Q ∈ (Dcmp.orbit i).phases →
          originalSlice i Q = Set.image Subtype.val
            {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
      ∀ (i : Fin Dcmp.numberOfParts),
      ∀ (Q : RationalSlice (Dcmp.direction i)),
        (∀ m : ℤ,
          Q.vadd (m • Dcmp.gamma.toPlane) ∈
            (Dcmp.orbit i).noGapPhases (originalSlice i)
              (60 * Metric.diam C.region.openCarrier)) →
        (Dcmp.direction i).toPlane.re = 0 →
        ∃ alpha : {z : Tiling.Plane //
            z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          (alpha : Tiling.Plane) ≠ 0 ∧
          mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
          (∀ m : ℤ,
            (alpha : Tiling.Plane) +ᵥ
                originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
              originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
          ∀ m : ℤ,
            ∃ beta : {z : Tiling.Plane //
                z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
              regularSupport C.region
                  (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
                (beta : Tiling.Plane) +ᵥ
                  regularSupport C.region (originalSlice i Q) ∧
              mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
              properVertices (regularSupport C.region
                  (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C hFLC hNoColumn
  obtain ⟨recoveryScale, hRecovery, hAxis⟩ :=
    nonColumnableAxisLocalTransport hFLC Axis.vertical hNoColumn
  refine ⟨recoveryScale, hRecovery, ?_⟩
  intro P hScale B hFine phi hphi D Tphi hTphi Dcmp originalSlice hOriginalSlice
    i Q hNoGap hVertical
  obtain ⟨Tband, _Xband, _period, hTband, _hOpen, _hRegular, _hXne,
    _hXproper, _hPeriodEq, _hPeriodPos, _hPeriod, _hFrontier, _hChamber,
    hTiles, _hSupport⟩ :=
      periodicBandDeformation B P.threshold hFine phi hphi D
  have hTbandEq : ∀ t : ↥C.centres, Tband t = Tphi t := by
    intro t
    rw [hTband, hTphi]
  have hTbandRange : Set.range Tband = Set.range Tphi := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hTbandEq t).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, hTbandEq t⟩
  have hImagePacking : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) := by
    have hTilesPack := hTiles.2.1
    change Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tband)) at hTilesPack
    rw [hTbandRange] at hTilesPack
    exact hTilesPack
  let phase : ℤ → Set ↥C.centres := fun m =>
    {t | Tphi t ∈ (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i)}
  have hPhase : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈ (Dcmp.orbit i).phases := by
    intro m
    exact (hNoGap m).1
  have hPhaseSlice : ∀ m, originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
      Set.image Subtype.val (phase m) := by
    intro m
    exact hOriginalSlice i _ (hPhase m)
  have hRange : Set.range Tphi = Set.range Tphi := rfl
  have hPhaseImage (m : ℤ) :
      Tphi '' phase m =
        (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i) := by
    exact orbitPhasePreimage_image Dcmp i Tphi hRange _
  have hPhaseNonempty : ∀ m, (phase m).Nonempty := by
    intro m
    exact orbitPhasePreimage_nonempty Dcmp i (hPhase m)
  have hSourcePacking (m : ℤ) : Tiling.IsPacking
      C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' phase m)) := by
    apply packing_mono_onCentreCarrier C.region P.source_tilesOn.2.1
    rintro x ⟨t, ht, rfl⟩
    exact t.2
  have hTargetPacking (m : ℤ) : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Tphi '' phase m)) := by
    apply packing_mono_onCentreCarrier D.deformedRegion hImagePacking
    rintro x ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hPhaseAligned (m : ℤ) : ∃ c, ∀ t : phase m,
      Axis.vertical.transverseCoord (Tphi t.1) = c := by
    obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty _).mp (hPhase m)
    refine ⟨x.re, ?_⟩
    intro t
    change (Tphi t.1).re = x.re
    exact (rationalSlice_centres_re_eq_of_vertical_direction
      (Q.vadd (m • Dcmp.gamma.toPlane)) (Dcmp.part i) hVertical
      (by simpa [RationalSlice.centres] using hx)
      (by simpa [phase, RationalSlice.centres] using t.2)).symm
  have hImagePeriod (m : ℤ) :
      (Dcmp.direction i).toPlane +ᵥ Tphi '' phase m = Tphi '' phase m := by
    have hp := (Dcmp.orbit i).slice_periodic
      (Q.vadd (m • Dcmp.gamma.toPlane)) (hPhase m)
    rw [Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq] at hp
    simpa [hPhaseImage m] using hp
  have hImageSupport (m : ℤ) :
      regularSupport D.deformedRegion (Tphi '' phase m) =
        (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion (Tphi '' phase 0) := by
    rw [hPhaseImage m, hPhaseImage 0]
    have hQphase : Q ∈ (Dcmp.orbit i).phases := by
      simpa [RationalSlice.vadd] using hPhase 0
    have hs := (Dcmp.orbit i).regularSupport_transport Q hQphase m
    simpa [RationalSlice.vadd] using hs.symm
  let G : ℝ := 60 * Metric.diam C.region.openCarrier
  have hNoGap' : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i) G := by
    simpa [G] using hNoGap
  have hLinked (m : ℤ) : Linked G (Subtype.val '' phase m) := by
    rw [← hPhaseSlice m]
    exact sourceSlice_linked_of_noGapPhase Dcmp i Subtype.val (originalSlice i)
      (by intro Q hQ; exact hOriginalSlice i Q hQ) (hNoGap' m)
  let imagePeriod : Tiling.Plane := (Dcmp.direction i).toPlane
  have hImagePeriodNe : imagePeriod ≠ 0 := by
    intro hz
    apply (Dcmp.direction i).property
    funext j
    fin_cases j
    · have hzero : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.re hz
      change (Dcmp.direction i).coordinates 0 = 0
      exact_mod_cast hzero
    · have hzero : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.im hz
      change (Dcmp.direction i).coordinates 1 = 0
      exact_mod_cast hzero
  have hImagePeriodAxis : Axis.vertical.transverseCoord imagePeriod = 0 := by
    simpa [imagePeriod, Axis.transverseCoord, Axis.coord] using hVertical
  have hOrbitTransport : ∀ m : ℤ,
      ∃ beta alpha : ControlledDisplacement C,
        regularSupport C.region (Subtype.val '' phase m) =
          (beta : Tiling.Plane) +ᵥ
            regularSupport C.region (Subtype.val '' phase 0) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        (alpha : Tiling.Plane) ≠ 0 ∧
        (alpha : Tiling.Plane) +ᵥ Subtype.val '' phase m = Subtype.val '' phase m ∧
        mapPoint phi alpha = imagePeriod ∧
        properVertices (regularSupport C.region (Subtype.val '' phase m)) ≠ ∅ := by
    intro m
    have halign0 := hPhaseAligned 0
    have halignm := hPhaseAligned m
    have hSupport :
        regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi (phase m)) =
          (m • Dcmp.gamma.toPlane) +ᵥ
            regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi (phase 0)) := by
      simpa [deformedCenterCarrierOn] using hImageSupport m
    obtain ⟨b, a, hsupp, hmapb, hane, _haligned, hperiod0, hperiodm,
      hmapa, _hproper0, hproperm⟩ :=
      hAxis P hScale phi hphi D Tphi hTphi (phase 0) (phase m) G rfl
        ⟨hSourcePacking 0, hSourcePacking m,
          hTargetPacking 0, hTargetPacking m⟩
        ⟨hPhaseNonempty 0, hPhaseNonempty m⟩
        ⟨halign0, halignm⟩
        ⟨(hLinked 0), (hLinked m)⟩
        imagePeriod hImagePeriodNe hImagePeriodAxis
        ⟨hImagePeriod 0, hImagePeriod m⟩
        (m • Dcmp.gamma.toPlane) hSupport
    exact ⟨b, a, hsupp, hmapb, hane, hperiodm, hmapa, hproperm⟩
  choose beta alpha hSupport hMapBeta hAlphaNe hPeriod hMapAlpha hProper using hOrbitTransport
  have hSynchronize : ∀ m : ℤ, alpha m = alpha 0 := by
    apply periodLifts_synchronizeFamily P phi hphi 0 phase alpha beta imagePeriod
    · exact hMapAlpha
    · exact hPeriod
    · exact hSupport
    · exact Set.nonempty_iff_ne_empty.mpr (hProper 0)
  have hSliceZero : originalSlice i Q = Subtype.val '' phase 0 := by
    simpa [RationalSlice.vadd] using hPhaseSlice 0
  refine ⟨alpha 0, hAlphaNe 0,
    hMapAlpha 0, ?_, ?_⟩
  · intro m
    rw [hPhaseSlice m, ← hSynchronize m]
    exact hPeriod m
  · intro m
    refine ⟨beta m, ?_, hMapBeta m, ?_⟩
    · simpa only [← hPhaseSlice m, ← hSliceZero] using hSupport m
    · simpa only [← hPhaseSlice m] using hProper m

end Tiling.AxisParallel.Terminal
