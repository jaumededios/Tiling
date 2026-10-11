import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.FLCIncidenceGermsAndColumns
import Tiling.AxisParallel.Approximation.FLCMetricAndRelationRigidity
import Tiling.AxisParallel.Approximation.ControlledPeriodLifting
import Tiling.AxisParallel.Terminal.BoundaryReconstruction
import Tiling.AxisParallel.Terminal.RationalFinerStructure

/-!
# Oblique slice transport — dependency-closed scratch candidate

Frozen owner-local vocabulary from the accepted tight-radius T08 packet plus CarrierNeutral r2.
All 17 allocated obligations are discharged. Private aliases preserve the frozen signatures;
no obligation bundle, axiom, or theorem-valued production premise is used. The two orbit
endpoints expose their literal signatures; all owner-local assembly stays private.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option linter.unusedVariables false

open Bornology Function Set
open Filter Topology
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Terminal

/-- The controlled plane already used by A01/A05.  This is an abbreviation,
not a new geometric carrier. -/
private abbrev ControlledPlane (C : ApproximationContext.{0}) :=
  {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
    z.im ∈ C.coordinateSpace}

/-- Indexed preimage of a literal image-centre set. -/
private def indexedPreimage {C : ApproximationContext.{0}}
    (Tphi : ↥C.centres ↪ Tiling.Plane) (A : Set Tiling.Plane) :
    Set ↥C.centres :=
  {t | Tphi t ∈ A}

/-- Exact output shape of A04's pending `periodicBandDeformation`. -/
private structure BandDeformationOutput
    (C : ApproximationContext.{0}) (B : PeriodicBandData C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) where
  centers : ↥C.centres ↪ Tiling.Plane
  base : Set ℝ
  period : ℝ
  centers_apply : ∀ t,
    centers t = mapPoint phi (C.centrePoint t.1 t.2)
  base_open : IsOpen base
  base_regular : interior (closure base) = base
  base_nonempty : base.Nonempty
  base_proper : base ≠ univ
  period_eq : period =
    mapScalar phi ⟨B.period, B.period_mem_coordinateSpace⟩
  period_pos : 0 < period
  base_periodic : period +ᵥ base = base
  frontier_eq : frontier base = Set.range (B.deformedBoundary phi)
  occupied_iff : ∀ j : ℤ, B.occupied j = true ↔
    Ioo (B.deformedBoundary phi j) (B.deformedBoundary phi (j + 1)) ⊆ base
  tiles : TilesOn D.deformedRegion (deformedCenterCarrier centers)
    {z : Tiling.Plane | z.re ∈ base}
  support_eq : regularSupport D.deformedRegion
    (deformedCenterCarrier centers) = {z : Tiling.Plane | z.re ∈ base}

private def bandDeformationOutput_existsStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (B : PeriodicBandData C)
    (P : FLCControlPackage C) (hFine : IsPeriodicBandFineness B P.threshold)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi),
    Nonempty (BandDeformationOutput C B phi D)

/-- All facts about one orbit phase that must be proved from A04, T04, the
literal indexed preimage, and no-gap membership. -/
private structure ObliquePhaseGeometry
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (G : ℝ) where
  indices : Set ↥C.centres
  indices_eq : indices = indexedPreimage Tphi (Q.centres (Dcmp.part i))
  source_eq : originalSlice i Q = Subtype.val '' indices
  image_eq : deformedCenterCarrierOn Tphi indices = Q.centres (Dcmp.part i)
  phase_mem : Q ∈ (Dcmp.orbit i).phases
  indices_nonempty : indices.Nonempty
  source_linked : Linked G (Subtype.val '' indices)
  source_packing : Tiling.IsPacking
    C.region.toPolygonalRegion.prototileFamily
    (C.region.toPolygonalRegion.placements (Subtype.val '' indices))
  image_packing : Tiling.IsPacking
    D.deformedRegion.toPolygonalRegion.prototileFamily
    (D.deformedRegion.toPolygonalRegion.placements
      (deformedCenterCarrierOn Tphi indices))
  image_in_line : deformedCenterCarrierOn Tphi indices ⊆ Q.carrier
  image_period : (Dcmp.direction i).toPlane +ᵥ
    deformedCenterCarrierOn Tphi indices = deformedCenterCarrierOn Tphi indices

private def noGapPhaseGeometry_existsStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} {D : CoordinateDeformation C phi}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hImageTiles : ∃ E : Set Tiling.Plane,
      TilesOn D.deformedRegion (Set.range Tphi) E)
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        indexedPreimage Tphi (Q.centres (Dcmp.part i)))
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (G : ℝ),
    Q ∈ (Dcmp.orbit i).noGapPhases (originalSlice i) G →
    Nonempty (ObliquePhaseGeometry C phi D Tphi Dcmp originalSlice i Q G)

private def phaseSupports_polygonalStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi)}
    {originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane}
    {i : Fin Dcmp.numberOfParts} {Q : RationalSlice (Dcmp.direction i)}
    {G : ℝ},
    ObliquePhaseGeometry C phi D Tphi Dcmp originalSlice i Q G →
    IsLocallyAxisParallelPolygonal (regularSupport C.region (originalSlice i Q)) ∧
      IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (Q.centres (Dcmp.part i)))

/-- The labelled proper-vertex correspondence for one phase.  It retains a
source tile vertex and indexed centre; this is what makes the A05/A06 calls
well typed. -/
private structure ObliqueProperVertexTransport
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (S : Set ↥C.centres)
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) where
  properVertexEquiv :
    ↥(properVertices (regularSupport C.region (Subtype.val '' S))) ≃
      ↥(properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
  source_label : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    ∃ (v : ↥C.region.vertices) (t : S),
    x.1 = v.1 + t.1.1
  target_formula : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    ∀ (v : ↥C.region.vertices) (t : S),
    x.1 = v.1 + t.1.1 →
    (properVertexEquiv x).1 = D.planarHomeomorph v.1 + Tphi t.1
  cone_preserved : ∀ x : ↥(properVertices
      (regularSupport C.region (Subtype.val '' S))),
    localCone _ x.1 hSource x.2 =
      localCone _ (properVertexEquiv x).1 hTarget (properVertexEquiv x).2

/-- A potential translated tile-edge label.  Actual boundary coverage later
restricts to intrinsic edges; finiteness is already true for this larger set. -/
private structure LabelledTileSegment
    (C : ApproximationContext.{0}) (S : Set ↥C.centres) where
  vertex₀ : ↥C.region.vertices
  vertex₁ : ↥C.region.vertices
  vertices_ne : vertex₀ ≠ vertex₁
  center : S

private def LabelledTileSegment.sourceSegment
    {C : ApproximationContext.{0}} {S : Set ↥C.centres}
    (e : LabelledTileSegment C S) : Set Tiling.Plane :=
  segment ℝ (e.vertex₀.1 + e.center.1.1) (e.vertex₁.1 + e.center.1.1)

private def LabelledTileSegment.imageSegment
    {C : ApproximationContext.{0}} {S : Set ↥C.centres}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (e : LabelledTileSegment C S) :
    Set Tiling.Plane :=
  segment ℝ (D.planarHomeomorph e.vertex₀.1 + Tphi e.center.1)
    (D.planarHomeomorph e.vertex₁.1 + Tphi e.center.1)

private def sourceSegmentsOnAxisLine
    {C : ApproximationContext.{0}} {S : Set ↥C.centres}
    (axis : Axis) (level : ℝ) : Set (LabelledTileSegment C S) :=
  {e | e.sourceSegment ⊆ {z | axis.transverseCoord z = level}}

private def imageSegmentsOnAxisLine
    {C : ApproximationContext.{0}} {S : Set ↥C.centres}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane) (axis : Axis) (level : ℝ) :
    Set (LabelledTileSegment C S) :=
  {e | e.imageSegment D Tphi ⊆ {z | axis.transverseCoord z = level}}

/-- Both coordinate projections are injective on an oblique affine line. -/
private def obliqueLine_coordinateInjectiveStatement : Prop :=
  ∀ (u : RationalDirection) (Q : RationalSlice u),
    u.toPlane.re * u.toPlane.im ≠ 0 →
    Set.InjOn Complex.re Q.carrier ∧ Set.InjOn Complex.im Q.carrier

/-- For every horizontal or vertical line, only finitely many labelled source
and image tile segments can lie on it.  This is the precise finite/bounded
projection input to the no-complete-line argument. -/
private def obliqueAxisLine_segmentCopies_finiteStatement : Prop :=
  ∀ {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (u : RationalDirection) (Q : RationalSlice u) (S : Set ↥C.centres),
    u.toPlane.re * u.toPlane.im ≠ 0 →
    deformedCenterCarrierOn Tphi S ⊆ Q.carrier →
    ∀ (axis : Axis) (level : ℝ),
      (sourceSegmentsOnAxisLine axis level :
          Set (LabelledTileSegment C S)).Finite ∧
      (imageSegmentsOnAxisLine (S := S) D Tphi axis level).Finite

/-- Correctly quantified version of the preceding statement for an arbitrary
oblique rational direction. -/
private def obliqueBoundaryTransport_existsStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (u : RationalDirection) (S : Set ↥C.centres) (Q : RationalSlice u),
    u.toPlane.re * u.toPlane.im ≠ 0 →
    S.Nonempty → deformedCenterCarrierOn Tphi S ⊆ Q.carrier →
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)) →
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)) →
    10 * (Metric.diam C.region.openCarrier + 1) < P.scale →
    ∀ (hSource : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S)))
      (hTarget : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))),
      properVertices (regularSupport C.region (Subtype.val '' S)) ≠ ∅ ∧
      properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) ≠ ∅ ∧
      completeBoundaryLines _ hSource = ∅ ∧
      completeBoundaryLines _ hTarget = ∅ ∧
      Nonempty (ObliqueProperVertexTransport C phi D Tphi S hSource hTarget) ∧
      ∀ t : S, ∃ v : ↥C.region.vertices,
        v.1 + t.1.1 ∈ properVertices
          (regularSupport C.region (Subtype.val '' S))

/-- Label provenance for every proper vertex and one exposed proper vertex over every centre
turn a `G`-linked centre family into a `(G+2d)`-linked proper-vertex family. -/
private def obliqueProperVertices_tightlyLinkedStatement : Prop :=
  ∀ {C : ApproximationContext.{0}}
      {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
      {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
      {S : Set ↥C.centres} {G : ℝ}
      (hSource : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S)))
      (hTarget : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
      (B : ObliqueProperVertexTransport C phi D Tphi S hSource hTarget),
    S.Nonempty → 0 < G → Linked G (Subtype.val '' S) →
    (∀ t : S, ∃ v : ↥C.region.vertices,
      v.1 + t.1.1 ∈ properVertices
        (regularSupport C.region (Subtype.val '' S))) →
    Linked (G + 2 * Metric.diam C.region.openCarrier) (properVertices
      (regularSupport C.region (Subtype.val '' S)))

/-- The public scale hypotheses put the tight proper-vertex radius, including both endpoint
approximation errors, strictly inside the coarse-inverse half-scale window. -/
private def obliqueProperVertexRadius_lt_halfScaleStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C) (G : ℝ),
    G = 60 * Metric.diam C.region.openCarrier →
    3 * G < P.scale →
    10 * (Metric.diam C.region.openCarrier + 1) < P.scale →
    G + 2 * Metric.diam C.region.openCarrier + 2 * P.localError < P.scale / 2

/-- Literal source support lift of one image support translation. -/
private structure ObliqueSupportLift
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (S₀ S₁ : Set ↥C.centres) (eta : Tiling.Plane) where
  beta : ControlledPlane C
  support_eq : regularSupport C.region (Subtype.val '' S₁) =
    beta.1 +ᵥ regularSupport C.region (Subtype.val '' S₀)
  map_beta : mapPoint phi beta = eta
  proper₀ : properVertices
    (regularSupport C.region (Subtype.val '' S₀)) ≠ ∅
  proper₁ : properVertices
    (regularSupport C.region (Subtype.val '' S₁)) ≠ ∅

private def obliqueSupportTranslation_liftStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres) (ell : ℝ) (eta : Tiling.Plane),
    ell + 2 * P.localError < P.scale / 2 →
    10 * (Metric.diam C.region.openCarrier + 1) < P.scale →
    ∀ (hSource₀ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₀)))
      (hSource₁ : IsLocallyAxisParallelPolygonal
        (regularSupport C.region (Subtype.val '' S₁)))
      (hTarget₀ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
      (hTarget₁ : IsLocallyAxisParallelPolygonal
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
      (B₀ : ObliqueProperVertexTransport C phi D Tphi S₀ hSource₀ hTarget₀)
      (B₁ : ObliqueProperVertexTransport C phi D Tphi S₁ hSource₁ hTarget₁),
      Linked ell
        (properVertices (regularSupport C.region (Subtype.val '' S₀))) →
      properVertices (regularSupport C.region (Subtype.val '' S₁)) ≠ ∅ →
      completeBoundaryLines _ hSource₀ = ∅ →
      completeBoundaryLines _ hSource₁ = ∅ →
      regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
        eta +ᵥ regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S₀) →
      Nonempty (ObliqueSupportLift C phi S₀ S₁ eta)

/-- One connected indexed family lifts its nonzero image period.  The proof
uses only controlled translated vertices and A05/A07 bounded reflection. -/
private structure ConnectedPeriodLift
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (S : Set ↥C.centres) (imagePeriod : Tiling.Plane) where
  alpha : ControlledPlane C
  alpha_ne : alpha.1 ≠ 0
  map_alpha : mapPoint phi alpha = imagePeriod
  period : alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S

private def connectedObliquePeriodLiftStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres) (G : ℝ),
    S.Nonempty → Linked G (Subtype.val '' S) →
    3 * G < P.scale → 3 < P.scale →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      Nonempty (ConnectedPeriodLift C phi S imagePeriod)

/-- Two phasewise lifts of the same image period coincide after the already
proved support translation; no global injectivity of `mapPoint` is used. -/
private def connectedPeriodLifts_synchronizeStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres) (imagePeriod eta : Tiling.Plane)
    (L₀ : ConnectedPeriodLift C phi S₀ imagePeriod)
    (L₁ : ConnectedPeriodLift C phi S₁ imagePeriod)
    (B : ObliqueSupportLift C phi S₀ S₁ eta),
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)) →
    Metric.diam C.region.openCarrier < P.controlRadius →
    L₀.alpha = L₁.alpha

/-- Exact frozen T08 public endpoint. -/
private def obliqueNoGapOrbitTransportStatement : Prop :=
  ∀ {C : Tiling.AxisParallel.Approximation.ApproximationContext.{0}}
    (P : Tiling.AxisParallel.Approximation.FLCControlPackage C)
    (B : Tiling.AxisParallel.Approximation.PeriodicBandData C)
    (hFine : Tiling.AxisParallel.Approximation.IsPeriodicBandFineness
      B P.threshold)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : Tiling.AxisParallel.Approximation.IsEpsilonApproximation
      C P.threshold phi)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = Tiling.AxisParallel.Approximation.mapPoint phi
        (C.centrePoint t.1 t.2))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion
      (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (diameter G M : ℝ)
    (hDiameter : diameter = Metric.diam C.region.openCarrier)
    (hScales : 0 < diameter ∧ G = 60 * diameter ∧
      max (3 * G) 3 < M ∧ M ≤ P.scale ∧
      10 * (diameter + 1) < P.scale)
    (i : Fin Dcmp.numberOfParts)
    (hOblique : (Dcmp.direction i).toPlane.re *
      (Dcmp.direction i).toPlane.im ≠ 0)
    (Q : RationalSlice (Dcmp.direction i))
    (hOrbitNoGap : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i) G),
    ∃ alpha : {z : Tiling.Plane //
        z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
      (alpha : Tiling.Plane) ≠ 0 ∧
      Tiling.AxisParallel.Approximation.mapPoint phi alpha =
        (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ,
        (alpha : Tiling.Plane) +ᵥ
            originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ,
        ∃ beta : {z : Tiling.Plane //
            z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          Tiling.AxisParallel.regularSupport C.region
              (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
            (beta : Tiling.Plane) +ᵥ
              Tiling.AxisParallel.regularSupport C.region
                (originalSlice i Q) ∧
          Tiling.AxisParallel.Approximation.mapPoint phi beta =
            m • Dcmp.gamma.toPlane ∧
          Tiling.AxisParallel.properVertices
            (Tiling.AxisParallel.regularSupport C.region
              (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅

/-- Private owner bridge: a packed family tiles its own regular support. -/
private def tilesOn_regularSupport_of_isPackingStatement : Prop :=
  ∀ {K : Region} {S : Set Tiling.Plane},
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) →
    TilesOn K S (regularSupport K S)

private def obliqueNoGapOrbitTransport_of_imagePackingStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (_hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)),
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) →
    ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
      (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
        RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
    (∀ i Q, Q ∈ (Dcmp.orbit i).phases → originalSlice i Q = Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
    ∀ (diameter G M : ℝ), diameter = Metric.diam C.region.openCarrier →
    (0 < diameter ∧ G = 60 * diameter ∧ max (3 * G) 3 < M ∧
      M ≤ P.scale ∧ 10 * (diameter + 1) < P.scale) →
    ∀ (i : Fin Dcmp.numberOfParts),
    (Dcmp.direction i).toPlane.re * (Dcmp.direction i).toPlane.im ≠ 0 →
    ∀ (Q : RationalSlice (Dcmp.direction i)),
    (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i) G) →
    ∃ alpha : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
      (alpha : Tiling.Plane) ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ, (alpha : Tiling.Plane) +ᵥ
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
          z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          (beta : Tiling.Plane) +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅

/-! ## Controlled-period-lifting consumer adapters -/

/-- Exact arithmetic bridge from T08's frozen scale assumptions to the shared
controlled-period-lifting margins. -/
private def t08_scaleMarginsStatement : Prop :=
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C) (G : ℝ),
    3 * G < P.scale → 3 < P.scale →
      G < P.scale ∧ G + P.localError < P.scale / 2


private theorem bandDeformationOutput_exists : bandDeformationOutput_existsStatement := by
  intro C B P hFine phi hphi D
  obtain ⟨Tphi, Xphi, aphi, hmap, hopen, hregular, hnonempty, hproper,
    hperiod, hpositive, hperiodic, hfrontier, hoccupied, htiles, hsupport⟩ :=
    periodicBandDeformation B P.threshold hFine phi hphi D
  exact ⟨⟨Tphi, Xphi, aphi, hmap, hopen, hregular, hnonempty, hproper,
    hperiod, hpositive, hperiodic, hfrontier, hoccupied, htiles, hsupport⟩⟩

private theorem tilesOn_regularSupport_of_isPacking :
    tilesOn_regularSupport_of_isPackingStatement := by
  intro K S hpacking
  refine ⟨(IsPacking.locallyFinite_centres hpacking).2, hpacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpacking] with x hx
  constructor
  · intro hxreg
    have hxU : x ∈ openUnion K S := (Iff.of_eq hx).mpr hxreg
    exact Set.mem_iUnion.mp hxU
  · intro hraw
    have hxU : x ∈ openUnion K S := Set.mem_iUnion.mpr hraw
    exact (Iff.of_eq hx).mp hxU

private theorem noGapPhaseGeometry_exists : noGapPhaseGeometry_existsStatement := by
  intro C P phi D Tphi hImageTiles Dcmp originalSlice hPreimage i Q G hQ
  have hphase : Q ∈ (Dcmp.orbit i).phases := hQ.1
  have hnotGap : ¬IsGappedSlice G (originalSlice i Q) := by
    intro hgap
    exact hQ.2 ⟨hphase, hgap⟩
  let S := indexedPreimage Tphi (Q.centres (Dcmp.part i))
  have hpart : Dcmp.part i ⊆ Set.range Tphi := by
    intro z hz
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have hImage : deformedCenterCarrierOn Tphi S = Q.centres (Dcmp.part i) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      obtain ⟨t, rfl⟩ := hpart hz.1
      exact ⟨t, hz, rfl⟩
  have hSne : S.Nonempty := by
    obtain ⟨z, hz⟩ := ((Dcmp.orbit i).phase_iff_nonempty Q).mp hphase
    obtain ⟨t, rfl⟩ := hpart hz.1
    exact ⟨t, hz⟩
  have hSource : originalSlice i Q = Subtype.val '' S := hPreimage i Q hphase
  have hLinked : Linked G (Subtype.val '' S) := by
    refine ⟨hSne.image Subtype.val, ?_⟩
    intro x hx y hy
    let R : Tiling.Plane → Tiling.Plane → Prop :=
      fun a b ↦ a ∈ Subtype.val '' S ∧ b ∈ Subtype.val '' S ∧ dist a b < G
    let : Std.Symm R := ⟨by
      intro a b hab
      exact ⟨hab.2.1, hab.1, by simpa only [dist_comm] using hab.2.2⟩⟩
    have hpath : Relation.EqvGen R x y := by
      by_contra hnot
      apply hnotGap
      rw [hSource]
      exact ⟨x, hx, y, hy, hnot⟩
    rwa [Relation.EqvGen.eqvGen_eq_reflTransGen] at hpath
  have hSourceSub : Subtype.val '' S ⊆ C.centres := by
    rintro z ⟨t, ht, rfl⟩
    exact t.2
  have hSourcePack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)) := by
    intro a ha b hb hab
    exact P.source_tilesOn.2.1 (hSourceSub ha) (hSourceSub hb) hab
  have hImageSub : deformedCenterCarrierOn Tphi S ⊆ Set.range Tphi := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  obtain ⟨E, hTiles⟩ := hImageTiles
  have hImagePack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (deformedCenterCarrierOn Tphi S)) := by
    intro a ha b hb hab
    exact hTiles.2.1 (hImageSub ha) (hImageSub hb) hab
  have hLine : deformedCenterCarrierOn Tphi S ⊆ Q.carrier := by
    rw [hImage]
    exact Set.inter_subset_right
  have hPeriod : (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi S =
      deformedCenterCarrierOn Tphi S := by
    rw [hImage]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp ((Dcmp.orbit i).slice_periodic Q hphase)
  exact ⟨⟨S, rfl, hSource, hImage, hphase, hSne, hLinked, hSourcePack,
    hImagePack, hLine, hPeriod⟩⟩

private theorem t08_scaleMargins : t08_scaleMarginsStatement := by
  intro C P G hG hs
  have hspos : 0 < P.scale := P.scale_pos
  have herror : P.scale⁻¹ < (3 : ℝ)⁻¹ :=
    (inv_lt_inv₀ P.scale_pos (by norm_num)).2 hs
  rw [P.localError_eq]
  constructor <;> norm_num at herror <;> linarith

private theorem obliqueProperVertexRadius_lt_halfScale :
    obliqueProperVertexRadius_lt_halfScaleStatement := by
  intro C P G hG hscale hdiam
  have hd := Metric.diam_nonneg (s := C.region.openCarrier)
  have hs : 10 < P.scale := by linarith
  have herror : P.scale⁻¹ < (10 : ℝ)⁻¹ :=
    (inv_lt_inv₀ P.scale_pos (by norm_num)).2 hs
  rw [P.localError_eq]
  norm_num at herror
  linarith

private theorem connectedObliquePeriodLift : connectedObliquePeriodLiftStatement := by
  intro C P phi hphi Tphi hTphi S G hSne hLinked hG hs u hu hperiod
  obtain ⟨hscale, hmargin⟩ := t08_scaleMargins P G hG hs
  obtain ⟨alpha, hne, hmap, hsourcePeriod⟩ := connectedIndexedPeriodLift P phi hphi
    Tphi hTphi S G hSne hLinked.2 hscale hmargin u hu hperiod
  exact ⟨⟨alpha, hne, hmap, hsourcePeriod⟩⟩

private theorem connectedPeriodLifts_synchronize :
    connectedPeriodLifts_synchronizeStatement := by
  intro C P phi hphi Tphi hTphi S₀ S₁ imagePeriod eta L₀ L₁ B _hpack _hradius
  apply periodLifts_eq_of_properVertexShift P phi hphi S₀ S₁
    L₀.alpha L₁.alpha B.beta imagePeriod L₀.map_alpha L₁.map_alpha L₀.period L₁.period
    (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn S₀)
    (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn S₁)
  · intro w hw
    rw [B.support_eq, properVertices_vadd_eq]
    exact Set.mem_vadd_set.mpr ⟨w, hw, rfl⟩
  · exact Set.nonempty_iff_ne_empty.mpr B.proper₀

private theorem obliqueLine_coordinateInjective
    (u : RationalDirection) (Q : RationalSlice u)
    (hu : u.toPlane.re * u.toPlane.im ≠ 0) :
    Set.InjOn Complex.re Q.carrier ∧ Set.InjOn Complex.im Q.carrier := by
  have hcoords := mul_ne_zero_iff.mp hu
  have hdiff : ∀ {x y : Tiling.Plane}, x ∈ Q.carrier → y ∈ Q.carrier →
      ∃ r : ℝ, x - y = r • u.toPlane := by
    intro x y hx hy
    change QuotientAddGroup.mk' (realDirectionSubgroup u) x = Q at hx
    change QuotientAddGroup.mk' (realDirectionSubgroup u) y = Q at hy
    exact (QuotientAddGroup.eq_iff_sub_mem.mp (hx.trans hy.symm))
  constructor
  · intro x hx y hy hxy
    obtain ⟨r, hr⟩ := hdiff hx hy
    have hrre := congrArg Complex.re hr
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, hxy, sub_self] at hrre
    have hrzero : r = 0 := (mul_eq_zero.mp hrre.symm).resolve_right hcoords.1
    apply sub_eq_zero.mp
    simpa only [hrzero, zero_smul] using hr
  · intro x hx y hy hxy
    obtain ⟨r, hr⟩ := hdiff hx hy
    have hrim := congrArg Complex.im hr
    simp only [Complex.sub_im, Complex.smul_im, smul_eq_mul, hxy, sub_self] at hrim
    have hrzero : r = 0 := (mul_eq_zero.mp hrim.symm).resolve_right hcoords.2
    apply sub_eq_zero.mp
    simpa only [hrzero, zero_smul] using hr

private theorem labelledTileSegment_eq
    {C : ApproximationContext.{0}} {S : Set ↥C.centres}
    {e f : LabelledTileSegment C S}
    (h₀ : e.vertex₀ = f.vertex₀) (h₁ : e.vertex₁ = f.vertex₁)
    (hc : e.center = f.center) : e = f := by
  cases e
  cases f
  cases h₀
  cases h₁
  cases hc
  rfl

private theorem mapped_transverseCoord_eq
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (axis : Axis) (s t : ↥C.centres)
    (hst : axis.transverseCoord s.1 = axis.transverseCoord t.1) :
    axis.transverseCoord (Tphi s) = axis.transverseCoord (Tphi t) := by
  rw [hTphi s, hTphi t]
  cases axis with
  | horizontal =>
    have hs : (⟨s.1.im, C.centre_im_mem s.1 s.2⟩ : C.coordinateSpace) =
        ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := Subtype.ext hst
    simpa [mapPoint, ApproximationContext.centrePoint, Axis.transverseCoord] using
      congrArg (mapScalar phi) hs
  | vertical =>
    have hs : (⟨s.1.re, C.centre_re_mem s.1 s.2⟩ : C.coordinateSpace) =
        ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := Subtype.ext hst
    simpa [mapPoint, ApproximationContext.centrePoint, Axis.transverseCoord] using
      congrArg (mapScalar phi) hs

private theorem obliqueAxisLine_segmentCopies_finite
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (u : RationalDirection) (Q : RationalSlice u) (S : Set ↥C.centres)
    (hu : u.toPlane.re * u.toPlane.im ≠ 0)
    (hline : deformedCenterCarrierOn Tphi S ⊆ Q.carrier)
    (axis : Axis) (level : ℝ) :
    (sourceSegmentsOnAxisLine axis level : Set (LabelledTileSegment C S)).Finite ∧
      (imageSegmentsOnAxisLine (S := S) D Tphi axis level).Finite := by
  classical
  have hvertices : C.region.vertices.Finite := C.region.isPolygonal.vertexSet_finite
  have := hvertices.to_subtype
  have htrans : Set.InjOn axis.transverseCoord Q.carrier := by
    obtain ⟨hre, him⟩ := obliqueLine_coordinateInjective u Q hu
    cases axis
    · exact him
    · exact hre
  have hmem (t : S) : Tphi t.1 ∈ Q.carrier := hline ⟨t.1, t.2, rfl⟩
  let labels : LabelledTileSegment C S → ↥C.region.vertices × ↥C.region.vertices :=
    fun e => (e.vertex₀, e.vertex₁)
  constructor
  · apply Set.Finite.of_injOn (f := labels) (t := Set.univ)
      (fun _ _ => Set.mem_univ _)
    · intro e he f hf hef
      have h₀ : e.vertex₀ = f.vertex₀ := congrArg Prod.fst hef
      have h₁ : e.vertex₁ = f.vertex₁ := congrArg Prod.snd hef
      have he₀ : axis.transverseCoord (e.vertex₀.1 + e.center.1.1) = level :=
        he (left_mem_segment ℝ _ _)
      have hf₀ : axis.transverseCoord (f.vertex₀.1 + f.center.1.1) = level :=
        hf (left_mem_segment ℝ _ _)
      have hc : axis.transverseCoord e.center.1.1 =
          axis.transverseCoord f.center.1.1 := by
        rw [h₀] at he₀
        cases axis <;>
          simp only [Axis.transverseCoord, Complex.add_im, Complex.add_re] at he₀ hf₀ ⊢ <;>
          linarith
      have hmap := mapped_transverseCoord_eq phi Tphi hTphi axis e.center.1 f.center.1 hc
      have hc' : e.center = f.center :=
        Subtype.ext (Tphi.injective (htrans (hmem e.center) (hmem f.center) hmap))
      exact labelledTileSegment_eq h₀ h₁ hc'
    · exact Set.finite_univ
  · apply Set.Finite.of_injOn (f := labels) (t := Set.univ)
      (fun _ _ => Set.mem_univ _)
    · intro e he f hf hef
      have h₀ : e.vertex₀ = f.vertex₀ := congrArg Prod.fst hef
      have h₁ : e.vertex₁ = f.vertex₁ := congrArg Prod.snd hef
      have he₀ : axis.transverseCoord
          (D.planarHomeomorph e.vertex₀.1 + Tphi e.center.1) = level :=
        he (left_mem_segment ℝ _ _)
      have hf₀ : axis.transverseCoord
          (D.planarHomeomorph f.vertex₀.1 + Tphi f.center.1) = level :=
        hf (left_mem_segment ℝ _ _)
      have hc : axis.transverseCoord (Tphi e.center.1) =
          axis.transverseCoord (Tphi f.center.1) := by
        rw [h₀] at he₀
        cases axis <;>
          simp only [Axis.transverseCoord, Complex.add_im, Complex.add_re] at he₀ hf₀ ⊢ <;>
          linarith
      have hc' : e.center = f.center :=
        Subtype.ext (Tphi.injective (htrans (hmem e.center) (hmem f.center) hc))
      exact labelledTileSegment_eq h₀ h₁ hc'
    · exact Set.finite_univ


private theorem obliqueProperVertices_tightlyLinked
    {C : ApproximationContext.{0}}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S : Set ↥C.centres} {G : ℝ}
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)))
    (B : ObliqueProperVertexTransport C phi D Tphi S hSource hTarget)
    (hS : S.Nonempty) (hG : 0 < G) (hLinked : Linked G (Subtype.val '' S))
    (hExpose : ∀ t : S, ∃ v : ↥C.region.vertices,
      v.1 + t.1.1 ∈ properVertices
        (regularSupport C.region (Subtype.val '' S))) :
    Linked (G + 2 * Metric.diam C.region.openCarrier) (properVertices
      (regularSupport C.region (Subtype.val '' S))) := by
  classical
  let V := properVertices (regularSupport C.region (Subtype.val '' S))
  let d := Metric.diam C.region.openCarrier
  have hd : 0 ≤ d := Metric.diam_nonneg
  have hvertexDist (v w : ↥C.region.vertices) : dist v.1 w.1 ≤ d := by
    have hv : v.1 ∈ closure C.region.openCarrier :=
      frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier C.region v.2)
    have hw : w.1 ∈ closure C.region.openCarrier :=
      frontier_subset_closure (IntrinsicVertices.region_vertices_subset_frontier C.region w.2)
    have hbounded : Bornology.IsBounded (closure C.region.openCarrier) := by
      change Bornology.IsBounded (closure (interior C.region.support))
      rw [C.region.isPolygonal.closure_interior]
      exact C.region.isPolygonal.isBounded
    simpa only [Metric.diam_closure] using Metric.dist_le_diam_of_mem hbounded hv hw
  have hexposed : ∀ z ∈ Subtype.val '' S, ∃ v : ↥C.region.vertices, v.1 + z ∈ V := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    exact hExpose ⟨t, ht⟩
  choose chosenVertex hchosenVertex using hexposed
  let vertex (z : Tiling.Plane) : ↥C.region.vertices :=
    if hz : z ∈ Subtype.val '' S then chosenVertex z hz else ⟨0, C.zero_mem_vertices⟩
  let f (z : Tiling.Plane) : Tiling.Plane := (vertex z).1 + z
  have hf {z : Tiling.Plane} (hz : z ∈ Subtype.val '' S) : f z ∈ V := by
    simpa only [f, vertex, dif_pos hz] using hchosenVertex z hz
  have hlabelMove (v : ↥C.region.vertices) (z : Tiling.Plane) :
      dist (v.1 + z) (f z) < G + 2 * d := by
    have hdist : dist (v.1 + z) (f z) ≤ d := by
      simpa only [f, dist_add_right] using hvertexDist v (vertex z)
    linarith
  let R : Tiling.Plane → Tiling.Plane → Prop :=
    fun a b => a ∈ V ∧ b ∈ V ∧ dist a b < G + 2 * d
  have hlift : (fun a b : Tiling.Plane =>
      a ∈ Subtype.val '' S ∧ b ∈ Subtype.val '' S ∧ dist a b < G) ≤ (R on f) := by
    intro a b hab
    refine ⟨hf hab.1, hf hab.2.1, ?_⟩
    have hdist : dist (f a) (f b) ≤ d + dist a b := by
      apply (dist_add_add_le _ _ _ _).trans
      gcongr
      exact hvertexDist (vertex a) (vertex b)
    linarith [hab.2.2]
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ := hS
    obtain ⟨v, hv⟩ := hExpose ⟨t, ht⟩
    exact ⟨v.1 + t.1, hv⟩
  · intro x hx y hy
    obtain ⟨vx, tx, hxlabel⟩ := B.source_label ⟨x, hx⟩
    obtain ⟨vy, ty, hylabel⟩ := B.source_label ⟨y, hy⟩
    change x = vx.1 + tx.1.1 at hxlabel
    change y = vy.1 + ty.1.1 at hylabel
    have htx : tx.1.1 ∈ Subtype.val '' S := ⟨tx.1, tx.2, rfl⟩
    have hty : ty.1.1 ∈ Subtype.val '' S := ⟨ty.1, ty.2, rfl⟩
    have hpath := Relation.ReflTransGen.lift f hlift _ _
      (hLinked.2 tx.1.1 htx ty.1.1 hty)
    have hxstep : Relation.ReflTransGen R x (f tx.1.1) :=
      Relation.ReflTransGen.single ⟨hx, hf htx, by
        rw [hxlabel]
        exact hlabelMove vx tx.1.1⟩
    have hystep : Relation.ReflTransGen R (f ty.1.1) y :=
      Relation.ReflTransGen.single ⟨hf hty, hy, by
        rw [dist_comm, hylabel]
        exact hlabelMove vy ty.1.1⟩
    exact hxstep.trans (hpath.trans hystep)

private def obliqueNormalValue (n z : Tiling.Plane) : ℝ :=
  n.re * z.re + n.im * z.im

/-- At an exposed point, an axis-parallel locally straight frontier would have
a nonzero axis tangent orthogonal to a normal with two nonzero coordinates. -/
private theorem properVertex_of_oblique_exposure
    {F : Set Tiling.Plane} {x n : Tiling.Plane}
    (hnre : n.re ≠ 0) (hnim : n.im ≠ 0)
    (hx : x ∈ frontier F)
    (hhalf : ∀ z ∈ frontier F, obliqueNormalValue n z ≤ obliqueNormalValue n x)
    (hcross : ∃ q > 0, ∀ z ∈ Metric.ball x q, z ∈ frontier F →
      z.re = x.re ∨ z.im = x.im) :
    Tiling.AxisParallel.IsProperVertex F x := by
  refine ⟨hx, ?_⟩
  rintro ⟨L, hxL, hdim, hlocal⟩
  obtain ⟨v, hv, r, hr, hline⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hxL hdim hlocal
  obtain ⟨q, hq, hcrossq⟩ := hcross
  let epsilon : ℝ := min r q / (2 * (‖v‖ + 1))
  have hmin : 0 < min r q := lt_min hr hq
  have hepsilon : 0 < epsilon := by
    dsimp only [epsilon]
    exact div_pos hmin (by positivity)
  have hstep : epsilon * ‖v‖ < min r q := by
    calc
      epsilon * ‖v‖ < epsilon * (‖v‖ + 1) := by
        exact mul_lt_mul_of_pos_left (by linarith) hepsilon
      _ = min r q / 2 := by
        dsimp only [epsilon]
        field_simp
      _ < min r q := half_lt_self hmin
  have hplusdist : dist (x + epsilon • v) x < min r q := by
    rw [dist_eq_norm]
    have heq : x + epsilon • v - x = epsilon • v := by abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hepsilon]
    exact hstep
  have hminusdist : dist (x + (-epsilon) • v) x < min r q := by
    rw [dist_eq_norm]
    have heq : x + (-epsilon) • v - x = -(epsilon • v) := by
      rw [neg_smul]
      abel
    rw [heq, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hepsilon]
    exact hstep
  have hplus : x + epsilon • v ∈ frontier F :=
    (hline _ (Metric.mem_ball.mpr
      (hplusdist.trans_le (min_le_left _ _)))).2
      (Tiling.vadd_smul_mem_affineLine x v epsilon)
  have hminus : x + (-epsilon) • v ∈ frontier F :=
    (hline _ (Metric.mem_ball.mpr
      (hminusdist.trans_le (min_le_left _ _)))).2
      (Tiling.vadd_smul_mem_affineLine x v (-epsilon))
  have haxis : v.re = 0 ∨ v.im = 0 := by
    rcases hcrossq _ (Metric.mem_ball.mpr
      (hplusdist.trans_le (min_le_right _ _))) hplus with h | h
    · left
      have hmul : epsilon * v.re = 0 := by
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at h
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hepsilon.ne'
    · right
      have hmul : epsilon * v.im = 0 := by
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at h
        linarith
      exact (mul_eq_zero.mp hmul).resolve_left hepsilon.ne'
  have hnormal : obliqueNormalValue n v = 0 := by
    have hp := hhalf _ hplus
    have hm := hhalf _ hminus
    simp only [obliqueNormalValue, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] at hp hm ⊢
    have hproduct : epsilon * (n.re * v.re + n.im * v.im) = 0 := by
      nlinarith
    exact (mul_eq_zero.mp hproduct).resolve_left hepsilon.ne'
  apply hv
  apply Complex.ext
  · rcases haxis with hre | him
    · exact hre
    · have hmul : n.re * v.re = 0 := by
        simpa only [obliqueNormalValue, him, mul_zero, add_zero] using hnormal
      exact (mul_eq_zero.mp hmul).resolve_left hnre
  · rcases haxis with hre | him
    · have hmul : n.im * v.im = 0 := by
        simpa only [obliqueNormalValue, hre, mul_zero, zero_add] using hnormal
      exact (mul_eq_zero.mp hmul).resolve_left hnim
    · exact him

/-- Any oblique-normal maximizer on a compact tile is an intrinsic vertex;
this requires neither a connected tile nor a chosen edge presentation. -/
private theorem exists_normal_max_vertex (K : Tiling.AxisParallel.Region)
    (n : Tiling.Plane) (hnre : n.re ≠ 0) (hnim : n.im ≠ 0) :
    ∃ v : ↥K.vertices, ∀ z ∈ K.support,
      obliqueNormalValue n z ≤ obliqueNormalValue n v.1 := by
  obtain ⟨x, hx, hmax⟩ := K.isPolygonal.isCompact.exists_isMaxOn
    K.nonempty (show ContinuousOn (obliqueNormalValue n) K.support by
      unfold obliqueNormalValue
      fun_prop)
  have hxnot : x ∉ K.openCarrier := by
    intro hxopen
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
      (Tiling.AxisParallel.Region.openCarrier_regularOpen K).1 x hxopen
    let epsilon : ℝ := r / (2 * (‖n‖ + 1))
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      exact div_pos hr (by positivity)
    have hstep : epsilon * ‖n‖ < r := by
      calc
        epsilon * ‖n‖ < epsilon * (‖n‖ + 1) := by
          exact mul_lt_mul_of_pos_left (by linarith) hepsilon
        _ = r / 2 := by
          dsimp only [epsilon]
          field_simp
        _ < r := half_lt_self hr
    have hdist : dist (x + epsilon • n) x < r := by
      rw [dist_eq_norm]
      have heq : x + epsilon • n - x = epsilon • n := by abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hepsilon]
      exact hstep
    have hy : x + epsilon • n ∈ K.support :=
      interior_subset (hball (Metric.mem_ball.mpr hdist))
    have hvalue := hmax hy
    change obliqueNormalValue n (x + epsilon • n) ≤ obliqueNormalValue n x at hvalue
    simp only [obliqueNormalValue, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] at hvalue
    have hsq : 0 < n.re ^ 2 + n.im ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hnre, sq_nonneg n.im]
    nlinarith
  have hclosure : closure K.openCarrier = K.support :=
    K.isPolygonal.closure_interior
  have hxfront : x ∈ frontier K.openCarrier := by
    rw [frontier, hclosure,
      (Tiling.AxisParallel.Region.openCarrier_regularOpen K).1.interior_eq]
    exact ⟨hx, hxnot⟩
  have hhalf : ∀ z ∈ frontier K.openCarrier,
      obliqueNormalValue n z ≤ obliqueNormalValue n x := by
    intro z hz
    apply hmax
    rw [frontier, hclosure] at hz
    exact hz.1
  have hcross : ∃ q > 0, ∀ z ∈ Metric.ball x q,
      z ∈ frontier K.openCarrier → z.re = x.re ∨ z.im = x.im := by
    obtain ⟨q, hq, hball⟩ := K.isAxisParallel.localBoundaryCross x
    refine ⟨q, hq, ?_⟩
    intro z hz hzfront
    apply hball z hz
    rwa [← Tiling.AxisParallel.Region.frontier_openCarrier_eq_frontier_support K]
  have hxproper := properVertex_of_oblique_exposure hnre hnim hxfront hhalf hcross
  have hxvertex : x ∈ K.vertices := by
    rw [Tiling.AxisParallel.IntrinsicVertices.region_vertices_eq_nonStraightBoundary]
    exact hxproper
  exact ⟨⟨x, hxvertex⟩, fun z hz => hmax hz⟩

private theorem controlledMap_add
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : ControlledPlane C) :
    mapPoint phi ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
      C.coordinateSpace.add_mem x.2.2 y.2.2⟩ =
      mapPoint phi x + mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero]
    exact_mod_cast (map_add phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, add_zero, zero_add]
    exact_mod_cast (map_add phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem controlledMap_sub
    {C : ApproximationContext.{0}} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : ControlledPlane C) :
    mapPoint phi ⟨x.1 - y.1, C.coordinateSpace.sub_mem x.2.1 y.2.1,
      C.coordinateSpace.sub_mem x.2.2 y.2.2⟩ =
      mapPoint phi x - mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    exact_mod_cast (map_sub phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact_mod_cast (map_sub phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private def sourceTranslatedVertex
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    {S : Set ↥C.centres}
    {hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S))}
    {hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))}
    (B : ObliqueProperVertexTransport C phi D Tphi S hSource hTarget)
    (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S)))) :
    ↥C.translatedVertices :=
  ⟨x.1, by
    obtain ⟨v, t, hxt⟩ := B.source_label x
    exact ⟨v.1, v.2, t.1.1, t.1.2, hxt.symm⟩⟩

private theorem transport_mapTranslatedVertex
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    {S : Set ↥C.centres}
    {hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S))}
    {hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))}
    (B : ObliqueProperVertexTransport C phi D Tphi S hSource hTarget)
    (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S)))) :
    mapTranslatedVertex phi (sourceTranslatedVertex B x) = (B.properVertexEquiv x).1 := by
  obtain ⟨v, t, hxt⟩ := B.source_label x
  rw [B.target_formula x v t hxt, D.vertex_agreement v.1 v.2, hTphi t.1]
  rw [← controlledMap_add]
  unfold mapTranslatedVertex
  congr 1
  apply Subtype.ext
  exact hxt

private theorem mapped_shortEdge_lt_halfScale
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (ell : ℝ) (hmargin : ell + 2 * P.localError < P.scale / 2)
    (x y : ↥C.translatedVertices) (hxy : dist x.1 y.1 < ell) :
    dist (mapTranslatedVertex phi x) (mapTranslatedVertex phi y) <
      ell + 2 * P.localError ∧
    dist (mapTranslatedVertex phi x) (mapTranslatedVertex phi y) < P.scale / 2 := by
  have hsrc : dist x.1 y.1 < P.scale := by
    have hs := P.scale_pos
    have he := P.localError_pos
    linarith
  have herr := deformation_localAccuracy P phi hphi x y hsrc
  have htriangle := dist_triangle
    (mapTranslatedVertex phi x - mapTranslatedVertex phi y)
    (x.1 - y.1) (0 : Tiling.Plane)
  have hbound : dist (mapTranslatedVertex phi x) (mapTranslatedVertex phi y) ≤
      dist (mapTranslatedVertex phi x - mapTranslatedVertex phi y) (x.1 - y.1) +
        dist x.1 y.1 := by
    simpa only [dist_eq_norm, sub_zero] using htriangle
  have hstrict : dist (mapTranslatedVertex phi x) (mapTranslatedVertex phi y) <
      ell + 2 * P.localError := by
    have he := P.localError_pos
    linarith
  exact ⟨hstrict, hstrict.trans hmargin⟩

private theorem reflected_shortEdge
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (ell : ℝ) (hmargin : ell + 2 * P.localError < P.scale / 2)
    (x y a b : ↥C.translatedVertices)
    (hxy : dist x.1 y.1 < ell)
    (hImage : mapTranslatedVertex phi b - mapTranslatedVertex phi a =
      mapTranslatedVertex phi y - mapTranslatedVertex phi x) :
    b.1 - a.1 = y.1 - x.1 := by
  have h0 := (mapped_shortEdge_lt_halfScale P phi hphi ell hmargin y x
    (by simpa only [dist_comm] using hxy)).2
  have h1 : dist (mapTranslatedVertex phi b) (mapTranslatedVertex phi a) <
      P.scale / 2 := by
    simpa only [dist_eq_norm, hImage] using h0
  apply Complex.ext
  · exact deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      .horizontal a b x y h1 h0 (congrArg Complex.re hImage)
  · exact deformation_reflectsBoundedCoordinateDisplacement P phi hphi
      .vertical a b x y h1 h0 (congrArg Complex.im hImage)

/-! This is a genuine consequence of the frozen support-lift hypotheses, but
only its proper-vertex-set conclusion. It does not stand in for support equality.
-/

private theorem supportTranslation_properVertexLift
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres) (ell : ℝ) (eta : Tiling.Plane)
    (hmargin : ell + 2 * P.localError < P.scale / 2)
    (hSource₀ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₀)))
    (hSource₁ : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S₁)))
    (hTarget₀ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)))
    (hTarget₁ : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)))
    (B₀ : ObliqueProperVertexTransport C phi D Tphi S₀ hSource₀ hTarget₀)
    (B₁ : ObliqueProperVertexTransport C phi D Tphi S₁ hSource₁ hTarget₁)
    (hLinked : Linked ell
      (properVertices (regularSupport C.region (Subtype.val '' S₀))))
    (htrans : regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
      eta +ᵥ regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)) :
    ∃ beta : ControlledPlane C, mapPoint phi beta = eta ∧
      properVertices (regularSupport C.region (Subtype.val '' S₁)) =
        beta.1 +ᵥ properVertices (regularSupport C.region (Subtype.val '' S₀)) := by
  let V₀ := properVertices (regularSupport C.region (Subtype.val '' S₀))
  let V₁ := properVertices (regularSupport C.region (Subtype.val '' S₁))
  have htargetVertices :
      properVertices
          (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)) =
        eta +ᵥ properVertices
          (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)) := by
    rw [htrans, properVertices_vadd_eq]
  have hforward (x : ↥V₀) : eta + (B₀.properVertexEquiv x).1 ∈
      properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁)) := by
    rw [htrans, properVertices_vadd_eq]
    exact Set.mem_vadd_set.mpr ⟨_, (B₀.properVertexEquiv x).2, rfl⟩
  let sigma : ↥V₀ → ↥V₁ := fun x =>
    B₁.properVertexEquiv.symm ⟨eta + (B₀.properVertexEquiv x).1, hforward x⟩
  have hsigma (x : ↥V₀) :
      (B₁.properVertexEquiv (sigma x)).1 = eta + (B₀.properVertexEquiv x).1 := by
    simp only [sigma, Equiv.apply_symm_apply]
  have honto : Function.Surjective sigma := by
    intro y
    have hy := (Set.ext_iff.mp htargetVertices _).mp (B₁.properVertexEquiv y).2
    obtain ⟨z, hz, hzy⟩ := Set.mem_vadd_set.mp hy
    let x : ↥V₀ := B₀.properVertexEquiv.symm ⟨z, hz⟩
    refine ⟨x, ?_⟩
    apply B₁.properVertexEquiv.injective
    apply Subtype.ext
    rw [hsigma]
    simpa only [x, Equiv.apply_symm_apply, vadd_eq_add] using hzy
  have hmapSigma (x : ↥V₀) :
      mapTranslatedVertex phi (sourceTranslatedVertex B₁ (sigma x)) =
        eta + mapTranslatedVertex phi (sourceTranslatedVertex B₀ x) := by
    rw [transport_mapTranslatedVertex hTphi B₁, hsigma,
      transport_mapTranslatedVertex hTphi B₀]
  have edge_disp (x y : ↥V₀) (hxy : dist x.1 y.1 < ell) :
      (sigma x).1 - x.1 = (sigma y).1 - y.1 := by
    have hImage :
        mapTranslatedVertex phi (sourceTranslatedVertex B₁ (sigma y)) -
            mapTranslatedVertex phi (sourceTranslatedVertex B₁ (sigma x)) =
          mapTranslatedVertex phi (sourceTranslatedVertex B₀ y) -
            mapTranslatedVertex phi (sourceTranslatedVertex B₀ x) := by
      rw [hmapSigma, hmapSigma]
      abel
    have h := reflected_shortEdge P phi hphi ell hmargin
      (sourceTranslatedVertex B₀ x) (sourceTranslatedVertex B₀ y)
      (sourceTranslatedVertex B₁ (sigma x)) (sourceTranslatedVertex B₁ (sigma y))
      hxy hImage
    change (sigma y).1 - (sigma x).1 = y.1 - x.1 at h
    apply Complex.ext
    · have hr := congrArg Complex.re h
      simp only [Complex.sub_re] at hr ⊢
      linarith
    · have hi := congrArg Complex.im h
      simp only [Complex.sub_im] at hi ⊢
      linarith
  let dispOf : ∀ (x : Tiling.Plane), x ∈ V₀ → Tiling.Plane :=
    fun x hx => (sigma ⟨x, hx⟩).1 - x
  have path_disp : ∀ {x y : Tiling.Plane}
      (hp : Relation.ReflTransGen
        (fun u v : Tiling.Plane => u ∈ V₀ ∧ v ∈ V₀ ∧ dist u v < ell) x y),
      ∀ hx : x ∈ V₀, ∀ hy : y ∈ V₀, dispOf x hx = dispOf y hy := by
    intro x y hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hx hy
        rfl
    | head edge htail ih =>
        intro hx hy
        rcases edge with ⟨hu, hv, huv⟩
        exact (edge_disp ⟨_, hu⟩ ⟨_, hv⟩ huv).trans (ih hv hy)
  obtain ⟨x₀val, hx₀⟩ := hLinked.1
  let x₀ : ↥V₀ := ⟨x₀val, hx₀⟩
  let a := C.translatedVertexPoint (sourceTranslatedVertex B₁ (sigma x₀))
  let b := C.translatedVertexPoint (sourceTranslatedVertex B₀ x₀)
  let beta : ControlledPlane C :=
    ⟨a.1 - b.1, C.coordinateSpace.sub_mem a.2.1 b.2.1,
      C.coordinateSpace.sub_mem a.2.2 b.2.2⟩
  have hdisp (x : ↥V₀) : (sigma x).1 - x.1 = beta.1 := by
    have hp := hLinked.2 x₀.1 x₀.2 x.1 x.2
    exact (path_disp hp x₀.2 x.2).symm
  have hmap : mapPoint phi beta = eta := by
    rw [controlledMap_sub]
    change mapTranslatedVertex phi (sourceTranslatedVertex B₁ (sigma x₀)) -
      mapTranslatedVertex phi (sourceTranslatedVertex B₀ x₀) = eta
    rw [hmapSigma]
    abel
  refine ⟨beta, hmap, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨x, hxy⟩ := honto (⟨y, hy⟩ : ↥V₁)
    refine Set.mem_vadd_set.mpr ⟨x.1, x.2, ?_⟩
    have hd := hdisp x
    have hxyval := congrArg Subtype.val hxy
    change (sigma x).1 = y at hxyval
    change beta.1 + x.1 = y
    rw [← hxyval, ← hd]
    abel
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Set.mem_vadd_set.mp hy
    let sx : ↥V₀ := ⟨x, hx⟩
    have hd := hdisp sx
    have hySigma : y = (sigma sx).1 := by
      change beta.1 + x = y at hxy
      rw [← hxy, ← hd]
      change (sigma sx).1 - x + x = (sigma sx).1
      abel
    rw [hySigma]
    exact (sigma sx).2

private theorem exposed_vertex_over_every_center
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (n : Tiling.Plane) (hnre : n.re ≠ 0) (hnim : n.im ≠ 0)
    (hnormal : ∀ s ∈ S, ∀ t ∈ S,
      obliqueNormalValue n s = obliqueNormalValue n t) (t : S) :
    ∃ v : ↥K.vertices,
      v.1 + t.1 ∈ properVertices (regularSupport K S) := by
  obtain ⟨v, hmax⟩ := exists_normal_max_vertex K n hnre hnim
  let x : Tiling.Plane := v.1 + t.1
  let H : Set Tiling.Plane := {z | obliqueNormalValue n z ≤ obliqueNormalValue n x}
  have hH : IsClosed H := by
    apply isClosed_le
    · unfold obliqueNormalValue
      fun_prop
    · fun_prop
  have hRaw : openUnion K S ⊆ H := by
    intro z hz
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hz
    obtain ⟨w, hw, hwz⟩ := Set.mem_vadd_set.mp hs
    have hvalue := hmax w (interior_subset hw)
    have hcenter := hnormal s.1 s.2 t.1 t.2
    change s.1 + w = z at hwz
    rw [← hwz]
    change obliqueNormalValue n (s.1 + w) ≤ obliqueNormalValue n (v.1 + t.1)
    simp only [obliqueNormalValue, Complex.add_re, Complex.add_im] at hvalue hcenter ⊢
    linarith
  have hClosedRaw : closure (openUnion K S) ⊆ H := closure_minimal hRaw hH
  have hSupport : regularSupport K S ⊆ H := interior_subset.trans hClosedRaw
  have hClosedSupport : closure (regularSupport K S) ⊆ H :=
    closure_minimal hSupport hH
  have hxRaw : x ∈ closure (openUnion K S) := by
    rw [closure_openUnion_eq_iUnion_support hpack]
    apply Set.mem_iUnion.mpr
    refine ⟨t, Set.mem_vadd_set.mpr ⟨v.1, ?_, ?_⟩⟩
    · rw [← K.isPolygonal.closure_interior]
      exact (Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K v.2).1
    · change t.1 + v.1 = x
      dsimp only [x]
      abel
  have hRawOpen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    exact (Tiling.AxisParallel.Region.openCarrier_regularOpen K).1.vadd s.1
  have hxClosed : x ∈ closure (regularSupport K S) :=
    closure_mono hRawOpen.subset_interior_closure hxRaw
  have hxNot : x ∉ regularSupport K S := by
    intro hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
    let epsilon : ℝ := r / (2 * (‖n‖ + 1))
    have hepsilon : 0 < epsilon := by
      dsimp only [epsilon]
      exact div_pos hr (by positivity)
    have hstep : epsilon * ‖n‖ < r := by
      calc
        epsilon * ‖n‖ < epsilon * (‖n‖ + 1) :=
          mul_lt_mul_of_pos_left (by linarith) hepsilon
        _ = r / 2 := by dsimp only [epsilon]; field_simp
        _ < r := half_lt_self hr
    have hdist : dist (x + epsilon • n) x < r := by
      rw [dist_eq_norm]
      have heq : x + epsilon • n - x = epsilon • n := by abel
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hepsilon]
      exact hstep
    have hvalue := hSupport (hball (Metric.mem_ball.mpr hdist))
    change obliqueNormalValue n (x + epsilon • n) ≤ obliqueNormalValue n x at hvalue
    simp only [obliqueNormalValue, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] at hvalue
    have hsq : 0 < n.re ^ 2 + n.im ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hnre, sq_nonneg n.im]
    nlinarith
  have hxFront : x ∈ frontier (regularSupport K S) := by
    have hOpen : IsOpen (regularSupport K S) := isOpen_interior
    rw [frontier, hOpen.interior_eq]
    exact ⟨hxClosed, hxNot⟩
  refine ⟨v, ?_⟩
  apply properVertex_of_oblique_exposure hnre hnim hxFront
  · intro z hz
    exact hClosedSupport (frontier_subset_closure hz)
  · exact regularSupport_localBoundaryCross hpack x

private theorem oblique_image_exposed_vertex
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (u : RationalDirection) (S : Set ↥C.centres) (Q : RationalSlice u)
    (hu : u.toPlane.re * u.toPlane.im ≠ 0)
    (hline : deformedCenterCarrierOn Tphi S ⊆ Q.carrier)
    (hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S))) (t : S) :
    ∃ v : ↥C.region.vertices,
      D.planarHomeomorph v.1 + Tphi t.1 ∈ properVertices
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
  let n : Tiling.Plane := (-u.toPlane.im : ℂ) + (u.toPlane.re : ℂ) * Complex.I
  have hnre : n.re ≠ 0 := by
    simpa [n] using neg_ne_zero.mpr (mul_ne_zero_iff.mp hu).2
  have hnim : n.im ≠ 0 := by
    simpa [n] using (mul_ne_zero_iff.mp hu).1
  have hnormal : ∀ s ∈ deformedCenterCarrierOn Tphi S,
      ∀ t ∈ deformedCenterCarrierOn Tphi S,
      obliqueNormalValue n s = obliqueNormalValue n t := by
    intro s hs t ht
    have hsq := hline hs
    have htq := hline ht
    change QuotientAddGroup.mk' (realDirectionSubgroup u) s = Q at hsq
    change QuotientAddGroup.mk' (realDirectionSubgroup u) t = Q at htq
    obtain ⟨r, hr⟩ := QuotientAddGroup.eq_iff_sub_mem.mp (hsq.trans htq.symm)
    have hre := congrArg Complex.re hr
    have him := congrArg Complex.im hr
    simp only [Complex.sub_re, Complex.sub_im, Complex.smul_re,
      Complex.smul_im, smul_eq_mul] at hre him
    simp only [obliqueNormalValue, n, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, sub_zero, add_zero, neg_zero]
    have hsre : s.re = t.re + r * u.toPlane.re := by linarith
    have hsim : s.im = t.im + r * u.toPlane.im := by linarith
    rw [hsre, hsim]
    ring
  let targetCenter : ↥(deformedCenterCarrierOn Tphi S) :=
    ⟨Tphi t.1, ⟨t.1, t.2, rfl⟩⟩
  obtain ⟨w, hw⟩ := exposed_vertex_over_every_center D.deformedRegion
    (deformedCenterCarrierOn Tphi S) hpack n hnre hnim hnormal targetCenter
  have hwVertex : w.1 ∈ D.planarHomeomorph '' C.region.vertices := by
    simpa only [D.vertices_image] using w.2
  obtain ⟨v, hv, hvw⟩ := hwVertex
  refine ⟨⟨v, hv⟩, ?_⟩
  simpa only [hvw, targetCenter] using hw

private theorem deformation_offset_germ
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres) (a : ↥C.translatedVertices)
    (ha : a.1 ∈ C.region.vertices + Subtype.val '' S) :
    ∀ᶠ d in nhds (0 : Tiling.Plane),
      a.1 + d ∈ regularSupport C.region (Subtype.val '' S) ↔
        mapTranslatedVertex phi a + d ∈ regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi S) := by
  obtain ⟨r₀, hr₀, hforward⟩ := deformation_preserves_localCone
    P hScale phi hphi D Tphi hTphi S a ha
  obtain ⟨r₁, hr₁, hbackward⟩ := deformation_reflects_localCone
    P hScale phi hphi D Tphi hTphi S a ha
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨min r₀ r₁, lt_min hr₀ hr₁, ?_⟩
  intro d hd
  exact ⟨hforward d (hd.trans_le (min_le_left _ _)),
    hbackward d (hd.trans_le (min_le_right _ _))⟩

private theorem oblique_source_exposed_vertex
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (u : RationalDirection) (S : Set ↥C.centres) (Q : RationalSlice u)
    (hu : u.toPlane.re * u.toPlane.im ≠ 0)
    (hline : deformedCenterCarrierOn Tphi S ⊆ Q.carrier)
    (hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S))) (t : S) :
    ∃ v : ↥C.region.vertices,
      v.1 + t.1.1 ∈ properVertices (regularSupport C.region (Subtype.val '' S)) := by
  obtain ⟨v, hv⟩ := oblique_image_exposed_vertex D Tphi u S Q hu hline hpack t
  let a : ↥C.translatedVertices :=
    ⟨v.1 + t.1.1, ⟨v.1, v.2, t.1.1, t.1.2, rfl⟩⟩
  have ha : a.1 ∈ C.region.vertices + Subtype.val '' S :=
    ⟨v.1, v.2, t.1.1, ⟨t.1, t.2, rfl⟩, rfl⟩
  have hmap : mapTranslatedVertex phi a = D.planarHomeomorph v.1 + Tphi t.1 := by
    rw [D.vertex_agreement v.1 v.2, hTphi t.1, ← controlledMap_add]
    unfold mapTranslatedVertex
    congr 1
  refine ⟨v, ?_⟩
  change IsProperVertex (regularSupport C.region (Subtype.val '' S)) a.1
  change IsProperVertex (regularSupport D.deformedRegion
    (deformedCenterCarrierOn Tphi S)) (D.planarHomeomorph v.1 + Tphi t.1) at hv
  apply (isProperVertex_iff_of_offset_germ
    (deformation_offset_germ P hScale phi hphi D Tphi hTphi S a ha)).mpr
  simpa only [hmap] using hv

private theorem mapTranslatedVertex_label
    {C : ApproximationContext.{0}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {Tphi : ↥C.centres ↪ Tiling.Plane}
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (a : ↥C.translatedVertices) (v : ↥C.region.vertices)
    (t : ↥C.centres) (ha : a.1 = v.1 + t.1) :
    mapTranslatedVertex phi a = D.planarHomeomorph v.1 + Tphi t := by
  rw [D.vertex_agreement v.1 v.2, hTphi t]
  have hadd := controlledMap_add phi
    (C.vertexPoint v.1 v.2) (C.centrePoint t.1 t.2)
  rw [← hadd]
  unfold mapTranslatedVertex
  congr 1
  apply Subtype.ext
  exact ha

/-- A06 gives the literal labelled proper-vertex equivalence without an oblique premise. -/
private theorem obliqueProperVertexTransport_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S : Set ↥C.centres)
    (hpackSource : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hpackTarget : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) :
    Nonempty (ObliqueProperVertexTransport C phi D Tphi S hSource hTarget) := by
  classical
  let Source := properVertices (regularSupport C.region (Subtype.val '' S))
  let Target := properVertices
    (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))
  have hlabel (x : ↥Source) :
      ∃ (v : ↥C.region.vertices) (t : S), x.1 = v.1 + t.1.1 := by
    obtain ⟨v, hv, s, hs, hxs⟩ :=
      properVertexProvenance hpackSource x.1 x.2
    obtain ⟨t, ht, rfl⟩ := hs
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hxs⟩
  let a (x : ↥Source) : ↥C.translatedVertices :=
    ⟨x.1, by
      obtain ⟨v, t, hxt⟩ := hlabel x
      exact ⟨v.1, v.2, t.1.1, t.1.2, hxt.symm⟩⟩
  have ha (x : ↥Source) :
      (a x : Tiling.Plane) ∈ C.region.vertices + Subtype.val '' S := by
    obtain ⟨v, t, hxt⟩ := hlabel x
    exact ⟨v.1, v.2, t.1.1, ⟨t.1, t.2, rfl⟩, hxt.symm⟩
  have hgerm (x : ↥Source) :
      ∀ᶠ u in 𝓝 (0 : Tiling.Plane),
        (x.1 + u ∈ regularSupport C.region (Subtype.val '' S) ↔
          mapTranslatedVertex phi (a x) + u ∈
            regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) := by
    exact deformation_offset_germ P hScale phi hphi D Tphi hTphi S (a x) (ha x)
  have hproper (x : ↥Source) :
      mapTranslatedVertex phi (a x) ∈ Target := by
    exact (isProperVertex_iff_of_offset_germ (hgerm x)).mp x.2
  let f : ↥Source → ↥Target := fun x => ⟨mapTranslatedVertex phi (a x), hproper x⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    have hmap : mapTranslatedVertex phi (a x) =
        mapTranslatedVertex phi (a y) := congrArg Subtype.val hxy
    have haxay := deformation_injectiveOnTranslatedVertices P phi hphi hmap
    apply Subtype.ext
    change (a x).1 = (a y).1
    exact congrArg Subtype.val haxay
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨w, hw, s, hs, hys⟩ :=
      properVertexProvenance hpackTarget y.1 y.2
    rw [D.vertices_image] at hw
    obtain ⟨v, hv, hvw⟩ := hw
    obtain ⟨t, ht, hst⟩ := hs
    let a' : ↥C.translatedVertices :=
      ⟨v + t.1, ⟨v, hv, t.1, t.2, rfl⟩⟩
    have ha' : (a' : Tiling.Plane) ∈ C.region.vertices + Subtype.val '' S :=
      ⟨v, hv, t.1, ⟨t, ht, rfl⟩, rfl⟩
    have hmap : mapTranslatedVertex phi a' = y.1 := by
      have hlabelMap := mapTranslatedVertex_label (D := D) (Tphi := Tphi)
        hTphi a' ⟨v, hv⟩ t rfl
      rw [hlabelMap, hvw, hst]
      exact hys.symm
    have hproper' : (a' : Tiling.Plane) ∈ Source := by
      have h := deformation_offset_germ P hScale phi hphi D Tphi
        hTphi S a' ha'
      apply (isProperVertex_iff_of_offset_germ h).mpr
      have hyproper : IsProperVertex
          (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))
          y.1 := y.2
      simpa only [hmap] using hyproper
    let x : ↥Source := ⟨a'.1, hproper'⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    change mapTranslatedVertex phi (a x) = y.1
    have hax : a x = a' := Subtype.ext rfl
    rw [hax, hmap]
  let e : ↥Source ≃ ↥Target := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨{
    properVertexEquiv := e
    source_label := hlabel
    target_formula := ?_
    cone_preserved := ?_
  }⟩
  · intro x v t hxt
    change mapTranslatedVertex phi (a x) = D.planarHomeomorph v.1 + Tphi t.1
    exact mapTranslatedVertex_label hTphi (a x) v t.1 hxt
  · intro x
    change localCone _ x.1 hSource x.2 =
      localCone _ (mapTranslatedVertex phi (a x)) hTarget (hproper x)
    exact localCone_eq_of_eventually_mem_iff_offset
      hSource hTarget x.2 (hproper x) (hgerm x)


private theorem obliqueSupportTranslation_lift : obliqueSupportTranslation_liftStatement := by
  intro C P phi hphi D Tphi hTphi S₀ S₁ ell eta hmargin hScale
    hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ hLinked hProper₁ hLines₀ hLines₁ htrans
  obtain ⟨beta, hmap, hvertices⟩ := supportTranslation_properVertexLift
    P phi hphi D Tphi hTphi S₀ S₁ ell eta hmargin
    hSource₀ hSource₁ hTarget₀ hTarget₁ B₀ B₁ hLinked htrans
  have hcone (x : ↥(properVertices (regularSupport C.region (Subtype.val '' S₀))))
      (y : ↥(properVertices (regularSupport C.region (Subtype.val '' S₁))))
      (hxy : y.1 = beta.1 + x.1) :
      localCone _ x.1 hSource₀ x.2 = localCone _ y.1 hSource₁ y.2 := by
    have himage : (B₁.properVertexEquiv y).1 = eta + (B₀.properVertexEquiv x).1 := by
      rw [← transport_mapTranslatedVertex hTphi B₁ y,
        ← transport_mapTranslatedVertex hTphi B₀ x, ← hmap]
      have hcontrolled : C.translatedVertexPoint (sourceTranslatedVertex B₁ y) =
          ⟨beta.1 + (C.translatedVertexPoint (sourceTranslatedVertex B₀ x)).1,
            C.coordinateSpace.add_mem beta.2.1
              (C.translatedVertexPoint (sourceTranslatedVertex B₀ x)).2.1,
            C.coordinateSpace.add_mem beta.2.2
              (C.translatedVertexPoint (sourceTranslatedVertex B₀ x)).2.2⟩ :=
        Subtype.ext hxy
      unfold mapTranslatedVertex
      rw [hcontrolled, controlledMap_add]
    have hy : IsProperVertex
        (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁))
        (eta + (B₀.properVertexEquiv x).1) := by
      rw [← himage]
      exact (B₁.properVertexEquiv y).2
    have ht := localCone_eq_of_vadd_eq hTarget₀ hTarget₁
      (B₀.properVertexEquiv x).2 hy htrans
    have ht' : localCone _ (B₀.properVertexEquiv x).1 hTarget₀
        (B₀.properVertexEquiv x).2 =
      localCone _ (B₁.properVertexEquiv y).1 hTarget₁
        (B₁.properVertexEquiv y).2 := by
      simpa only [localCone, ← himage] using ht
    exact (B₀.cone_preserved x).trans (ht'.trans (B₁.cone_preserved y).symm)
  have hPullback (y : Tiling.Plane)
      (hy : y ∈ beta.1 +ᵥ properVertices (regularSupport C.region (Subtype.val '' S₀))) :
      IsProperVertex (regularSupport C.region (Subtype.val '' S₀)) (y - beta.1) := by
    change y - beta.1 ∈ properVertices (regularSupport C.region (Subtype.val '' S₀))
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using
      (Set.mem_vadd_set_iff_neg_vadd_mem.mp hy)
  have hCode : boundaryCode (regularSupport C.region (Subtype.val '' S₁)) hSource₁ =
      (boundaryCode (regularSupport C.region (Subtype.val '' S₀)) hSource₀).vadd beta.1 := by
    apply (boundaryCode_eq_vadd_iff hSource₀ hSource₁ beta.1).mpr
    refine ⟨hvertices, ?_, ?_⟩
    · ext p
      rcases p with ⟨y, q⟩
      change (∃ hy : y ∈ properVertices (regularSupport C.region (Subtype.val '' S₁)),
          q = localCone _ y hSource₁ hy) ↔
        (∃ hy : y ∈ beta.1 +ᵥ properVertices
            (regularSupport C.region (Subtype.val '' S₀)),
          q = localCone _ (y - beta.1) hSource₀ (hPullback y hy))
      constructor
      · rintro ⟨hy, hq⟩
        have hy' : y ∈ beta.1 +ᵥ properVertices
            (regularSupport C.region (Subtype.val '' S₀)) := by
          rw [← hvertices]
          exact hy
        refine ⟨hy', ?_⟩
        have hx : y - beta.1 ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₀)) := by
          obtain ⟨x, hx, hxy⟩ := Set.mem_vadd_set.mp hy'
          have h : y - beta.1 = x := by
            change beta.1 + x = y at hxy
            rw [← hxy]
            abel
          simpa only [h] using hx
        exact hq.trans (hcone ⟨y - beta.1, hx⟩ ⟨y, hy⟩ (by
          change y = beta.1 + (y - beta.1)
          simp)).symm
      · rintro ⟨hy', hq⟩
        have hy : y ∈ properVertices (regularSupport C.region (Subtype.val '' S₁)) := by
          rw [hvertices]
          exact hy'
        refine ⟨hy, ?_⟩
        have hx : y - beta.1 ∈ properVertices
            (regularSupport C.region (Subtype.val '' S₀)) := by
          obtain ⟨x, hx, hxy⟩ := Set.mem_vadd_set.mp hy'
          have h : y - beta.1 = x := by
            change beta.1 + x = y at hxy
            rw [← hxy]
            abel
          simpa only [h] using hx
        exact hq.trans (hcone ⟨y - beta.1, hx⟩ ⟨y, hy⟩ (by
          change y = beta.1 + (y - beta.1)
          simp))
    · change completeBoundaryLines _ hSource₁ =
        (fun L => L.vadd beta.1) '' completeBoundaryLines _ hSource₀
      rw [hLines₀, hLines₁, Set.image_empty]
  obtain ⟨x, hx⟩ := hLinked.1
  have hFront₀ : (frontier (regularSupport C.region (Subtype.val '' S₀))).Nonempty :=
    ⟨x, hx.1⟩
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hProper₁
  have hFront₁ : (frontier (regularSupport C.region (Subtype.val '' S₁))).Nonempty :=
    ⟨y, hy.1⟩
  have hreg₀ := regularSupport_isRegularOpen C.region (Subtype.val '' S₀)
  have hreg₁ := regularSupport_isRegularOpen C.region (Subtype.val '' S₁)
  have hsupp := eq_vadd_of_boundaryCode hreg₀.1 hreg₁.1 hreg₀.2 hreg₁.2
    (nonempty_frontier_iff.mp hFront₀).1 (nonempty_frontier_iff.mp hFront₁).1
    (nonempty_frontier_iff.mp hFront₀).2 (nonempty_frontier_iff.mp hFront₁).2
    hSource₀ hSource₁ hCode
  exact ⟨⟨beta, hsupp, hmap, Set.nonempty_iff_ne_empty.mp hLinked.1, hProper₁⟩⟩

set_option linter.style.haveILetI false in
private theorem obliqueNoCompleteAxisLines
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (u : RationalDirection) (Q : RationalSlice u) (S : Set ↥C.centres)
    (hu : u.toPlane.re * u.toPlane.im ≠ 0)
    (hline : deformedCenterCarrierOn Tphi S ⊆ Q.carrier)
    (hSourcePack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S)))
    (hImagePack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements
        (deformedCenterCarrierOn Tphi S)))
    (hSource : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' S)))
    (hTarget : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S))) :
    completeBoundaryLines _ hSource = ∅ ∧
      completeBoundaryLines _ hTarget = ∅ := by
  classical
  have hvertices : C.region.vertices.Finite := C.region.isPolygonal.vertexSet_finite
  letI : Finite ↥C.region.vertices := hvertices.to_subtype
  have hS : S.Countable :=
    Set.countable_of_injective_of_countable_image Subtype.val_injective.injOn
      ((IsPacking.locallyFinite_centres hSourcePack).2)
  letI : Countable S := hS.to_subtype
  have hlabels : Countable (LabelledTileSegment C S) := by
    apply Function.Injective.countable
      (f := fun e : LabelledTileSegment C S => (e.vertex₀, e.vertex₁, e.center))
    intro e f hef
    exact labelledTileSegment_eq
      (congrArg (fun p => p.1) hef)
      (congrArg (fun p => p.2.1) hef)
      (congrArg (fun p => p.2.2) hef)
  letI : Countable (LabelledTileSegment C S) := hlabels
  have hSourceCover : frontier (regularSupport C.region (Subtype.val '' S)) ⊆
      ⋃ e : LabelledTileSegment C S, e.sourceSegment := by
    intro x hx
    obtain ⟨s, v, w, hne, hseg⟩ :=
      regularSupport_frontier_mem_translatedVertexSegment hSourcePack hx
    obtain ⟨t, ht, hst⟩ := s.2
    let e : LabelledTileSegment C S :=
      ⟨v, w, hne, ⟨t, ht⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    simpa only [LabelledTileSegment.sourceSegment, e, hst] using hseg
  have hImageCover :
      frontier (regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S)) ⊆
      ⋃ e : LabelledTileSegment C S, e.imageSegment D Tphi := by
    intro x hx
    obtain ⟨s, v, w, hne, hseg⟩ :=
      regularSupport_frontier_mem_translatedVertexSegment hImagePack hx
    obtain ⟨t, ht, hst⟩ := s.2
    let v₀ : ↥C.region.vertices := (D.vertexEquiv).symm v
    let w₀ : ↥C.region.vertices := (D.vertexEquiv).symm w
    have hne₀ : v₀ ≠ w₀ := by
      intro h
      apply hne
      simpa only [v₀, w₀, Equiv.apply_symm_apply] using
        congrArg D.vertexEquiv h
    let e : LabelledTileSegment C S :=
      ⟨v₀, w₀, hne₀, ⟨t, ht⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e, ?_⟩
    have hv : D.planarHomeomorph v₀.1 = v.1 := by
      change (D.vertexEquiv v₀).1 = v.1
      simpa only [v₀] using congrArg Subtype.val (D.vertexEquiv.apply_symm_apply v)
    have hw : D.planarHomeomorph w₀.1 = w.1 := by
      change (D.vertexEquiv w₀).1 = w.1
      simpa only [w₀] using congrArg Subtype.val (D.vertexEquiv.apply_symm_apply w)
    simpa only [LabelledTileSegment.imageSegment, e, hst, hv, hw] using hseg
  constructor
  · apply Set.Subset.antisymm
    · intro L hL
      exfalso
      have hfinite := (obliqueAxisLine_segmentCopies_finite phi D Tphi hTphi
        u Q S hu hline L.axis L.level).1
      have hbad := axisLine_not_subset_countableSegments
        (fun e : LabelledTileSegment C S => e.vertex₀.1 + e.center.1.1)
        (fun e : LabelledTileSegment C S => e.vertex₁.1 + e.center.1.1)
        L.axis L.level hfinite
      apply hbad
      exact hL.1.trans hSourceCover
    · exact Set.empty_subset _
  · apply Set.Subset.antisymm
    · intro L hL
      exfalso
      have hfinite := (obliqueAxisLine_segmentCopies_finite phi D Tphi hTphi
        u Q S hu hline L.axis L.level).2
      have hbad := axisLine_not_subset_countableSegments
        (fun e : LabelledTileSegment C S =>
          D.planarHomeomorph e.vertex₀.1 + Tphi e.center.1)
        (fun e : LabelledTileSegment C S =>
          D.planarHomeomorph e.vertex₁.1 + Tphi e.center.1)
        L.axis L.level hfinite
      apply hbad
      exact hL.1.trans hImageCover
    · exact Set.empty_subset _


private theorem obliqueBoundaryTransport_exists : obliqueBoundaryTransport_existsStatement := by
  intro C P phi hphi D Tphi hTphi u S Q hu hS hline hPackSource hPackTarget hScale
    hSource hTarget
  have hExpose := oblique_source_exposed_vertex P hScale phi hphi D Tphi hTphi
    u S Q hu hline hPackTarget
  obtain ⟨t, ht⟩ := hS
  obtain ⟨v, hv⟩ := hExpose ⟨t, ht⟩
  have hProperSource : properVertices
      (regularSupport C.region (Subtype.val '' S)) ≠ ∅ := by
    exact Set.nonempty_iff_ne_empty.mp ⟨v.1 + t.1, hv⟩
  obtain ⟨w, hw⟩ := oblique_image_exposed_vertex D Tphi u S Q hu hline hPackTarget ⟨t, ht⟩
  have hProperTarget : properVertices (regularSupport D.deformedRegion
      (deformedCenterCarrierOn Tphi S)) ≠ ∅ :=
    Set.nonempty_iff_ne_empty.mp ⟨D.planarHomeomorph w.1 + Tphi t, hw⟩
  have hLines := obliqueNoCompleteAxisLines phi D Tphi hTphi u Q S hu hline
    hPackSource hPackTarget hSource hTarget
  exact ⟨hProperSource, hProperTarget, hLines.1, hLines.2,
    obliqueProperVertexTransport_exists P hScale phi hphi D Tphi hTphi S
      hPackSource hPackTarget hSource hTarget, hExpose⟩

private theorem phaseSupports_polygonal : phaseSupports_polygonalStatement := by
  intro C phi D Tphi Dcmp originalSlice i Q G data
  constructor
  · rw [data.source_eq]
    exact packing_regularSupport_isLocallyAxisParallelPolygonal data.source_packing
  · rw [← data.image_eq]
    exact packing_regularSupport_isLocallyAxisParallelPolygonal data.image_packing

theorem obliqueNoGapOrbitTransport_of_imagePacking :
  ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (_hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (_hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)),
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) →
    ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
      (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
        RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
    (∀ i Q, Q ∈ (Dcmp.orbit i).phases → originalSlice i Q = Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
    ∀ (diameter G M : ℝ), diameter = Metric.diam C.region.openCarrier →
    (0 < diameter ∧ G = 60 * diameter ∧ max (3 * G) 3 < M ∧
      M ≤ P.scale ∧ 10 * (diameter + 1) < P.scale) →
    ∀ (i : Fin Dcmp.numberOfParts),
    (Dcmp.direction i).toPlane.re * (Dcmp.direction i).toPlane.im ≠ 0 →
    ∀ (Q : RationalSlice (Dcmp.direction i)),
    (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i) G) →
    ∃ alpha : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
      (alpha : Tiling.Plane) ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ, (alpha : Tiling.Plane) +ᵥ
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
          z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          (beta : Tiling.Plane) +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C P phi hphi D Tphi hTphi hImagePack Dcmp originalSlice hPreimage
    diameter G M hDiameter hScales i hOblique Q hOrbitNoGap
  classical
  let q (m : ℤ) : RationalSlice (Dcmp.direction i) :=
    Q.vadd (m • Dcmp.gamma.toPlane)
  have hBaseNoGap : Q ∈ (Dcmp.orbit i).noGapPhases (originalSlice i) G := by
    simpa [q, RationalSlice.vadd] using hOrbitNoGap 0
  have hImageTiles : ∃ E : Set Tiling.Plane,
      TilesOn D.deformedRegion (Set.range Tphi) E :=
    ⟨regularSupport D.deformedRegion (Set.range Tphi),
      tilesOn_regularSupport_of_isPacking hImagePack⟩
  let base : ObliquePhaseGeometry C phi D Tphi Dcmp originalSlice i Q G :=
    Classical.choice (noGapPhaseGeometry_exists P Tphi hImageTiles Dcmp
      originalSlice hPreimage i Q G hBaseNoGap)
  let phase (m : ℤ) : ObliquePhaseGeometry C phi D Tphi Dcmp originalSlice
      i (q m) G :=
    Classical.choice (noGapPhaseGeometry_exists P Tphi hImageTiles Dcmp
      originalSlice hPreimage i (q m) G (hOrbitNoGap m))
  have hScale : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale := by
    simpa only [← hDiameter] using hScales.2.2.2.2
  have h3G : 3 * G < P.scale :=
    (lt_of_le_of_lt (le_max_left (3 * G) 3) hScales.2.2.1).trans_le
      hScales.2.2.2.1
  have h3 : 3 < P.scale :=
    (lt_of_le_of_lt (le_max_right (3 * G) 3) hScales.2.2.1).trans_le
      hScales.2.2.2.1
  have hG : 0 < G := by
    rw [hScales.2.1]
    exact mul_pos (by norm_num) hScales.1
  have hDir : (Dcmp.direction i).toPlane ≠ 0 := by
    intro hz
    apply hOblique
    simp only [hz, Complex.zero_re, Complex.zero_im, mul_zero]
  have hSourceBase : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' base.indices)) := by
    rw [← base.source_eq]
    exact (phaseSupports_polygonal base).1
  have hTargetBase : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi base.indices)) := by
    rw [base.image_eq]
    exact (phaseSupports_polygonal base).2
  have hSourcePhase (m : ℤ) : IsLocallyAxisParallelPolygonal
      (regularSupport C.region (Subtype.val '' (phase m).indices)) := by
    rw [← (phase m).source_eq]
    exact (phaseSupports_polygonal (phase m)).1
  have hTargetPhase (m : ℤ) : IsLocallyAxisParallelPolygonal
      (regularSupport D.deformedRegion
        (deformedCenterCarrierOn Tphi (phase m).indices)) := by
    rw [(phase m).image_eq]
    exact (phaseSupports_polygonal (phase m)).2
  have hBoundaryBase := obliqueBoundaryTransport_exists P phi hphi D Tphi hTphi
    (Dcmp.direction i) base.indices Q hOblique base.indices_nonempty
    base.image_in_line base.source_packing base.image_packing hScale
    hSourceBase hTargetBase
  have hBoundaryPhase (m : ℤ) := obliqueBoundaryTransport_exists P phi hphi
    D Tphi hTphi (Dcmp.direction i) (phase m).indices (q m) hOblique
    (phase m).indices_nonempty (phase m).image_in_line
    (phase m).source_packing (phase m).image_packing hScale
    (hSourcePhase m) (hTargetPhase m)
  let Bbase : ObliqueProperVertexTransport C phi D Tphi base.indices
      hSourceBase hTargetBase := Classical.choice hBoundaryBase.2.2.2.2.1
  let Bphase (m : ℤ) : ObliqueProperVertexTransport C phi D Tphi
      (phase m).indices (hSourcePhase m) (hTargetPhase m) :=
    Classical.choice (hBoundaryPhase m).2.2.2.2.1
  have hLinkedBase : Linked
      (G + 2 * Metric.diam C.region.openCarrier)
      (properVertices (regularSupport C.region
        (Subtype.val '' base.indices))) :=
    obliqueProperVertices_tightlyLinked hSourceBase hTargetBase Bbase
      base.indices_nonempty hG base.source_linked hBoundaryBase.2.2.2.2.2
  have hMargin :
      G + 2 * Metric.diam C.region.openCarrier + 2 * P.localError <
        P.scale / 2 :=
    obliqueProperVertexRadius_lt_halfScale P G
      (by simpa only [hDiameter] using hScales.2.1) h3G hScale
  have hImageShift (m : ℤ) :
      regularSupport D.deformedRegion
          (deformedCenterCarrierOn Tphi (phase m).indices) =
        (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion
            (deformedCenterCarrierOn Tphi base.indices) := by
    calc
      _ = regularSupport D.deformedRegion
          ((q m).centres (Dcmp.part i)) := by rw [(phase m).image_eq]
      _ = (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion
            (Q.centres (Dcmp.part i)) :=
        (rationalSlices_shiftTransport Dcmp i Q base.phase_mem m).2.symm
      _ = (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion
            (deformedCenterCarrierOn Tphi base.indices) := by
        rw [base.image_eq]
  let supportLift (m : ℤ) : ObliqueSupportLift C phi base.indices
      (phase m).indices (m • Dcmp.gamma.toPlane) :=
    Classical.choice (obliqueSupportTranslation_lift P phi hphi D Tphi hTphi
      base.indices (phase m).indices
      (G + 2 * Metric.diam C.region.openCarrier)
      (m • Dcmp.gamma.toPlane) hMargin hScale hSourceBase (hSourcePhase m)
      hTargetBase (hTargetPhase m) Bbase (Bphase m) hLinkedBase
      (hBoundaryPhase m).1 hBoundaryBase.2.2.1
      (hBoundaryPhase m).2.2.1 (hImageShift m))
  let Lbase : ConnectedPeriodLift C phi base.indices
      (Dcmp.direction i).toPlane :=
    Classical.choice (connectedObliquePeriodLift P phi hphi Tphi hTphi
      base.indices G base.indices_nonempty base.source_linked h3G h3
      (Dcmp.direction i).toPlane hDir base.image_period)
  let Lphase (m : ℤ) : ConnectedPeriodLift C phi (phase m).indices
      (Dcmp.direction i).toPlane :=
    Classical.choice (connectedObliquePeriodLift P phi hphi Tphi hTphi
      (phase m).indices G (phase m).indices_nonempty
      (phase m).source_linked h3G h3
      (Dcmp.direction i).toPlane hDir (phase m).image_period)
  have hRadius : Metric.diam C.region.openCarrier < P.controlRadius := by
    calc
      _ < P.scale := by
        linarith [hScale, Metric.diam_nonneg (s := C.region.openCarrier)]
      _ < P.controlRadius := P.scale_lt_controlRadius
  have hSync (m : ℤ) : Lbase.alpha = (Lphase m).alpha :=
    connectedPeriodLifts_synchronize P phi hphi Tphi hTphi
      base.indices (phase m).indices (Dcmp.direction i).toPlane
      (m • Dcmp.gamma.toPlane) Lbase (Lphase m) (supportLift m)
      base.source_packing hRadius
  refine ⟨Lbase.alpha, Lbase.alpha_ne, Lbase.map_alpha, ?_, ?_⟩
  · intro m
    calc
      (Lbase.alpha : Tiling.Plane) +ᵥ originalSlice i (q m) =
          (Lbase.alpha : Tiling.Plane) +ᵥ
            Subtype.val '' (phase m).indices := by rw [(phase m).source_eq]
      _ = Subtype.val '' (phase m).indices := by
        rw [hSync m]
        exact (Lphase m).period
      _ = originalSlice i (q m) := (phase m).source_eq.symm
  · intro m
    refine ⟨(supportLift m).beta, ?_, (supportLift m).map_beta, ?_⟩
    · change regularSupport C.region (originalSlice i (q m)) =
        (supportLift m).beta.1 +ᵥ regularSupport C.region (originalSlice i Q)
      rw [(phase m).source_eq, base.source_eq]
      exact (supportLift m).support_eq
    · change properVertices (regularSupport C.region (originalSlice i (q m))) ≠ ∅
      rw [(phase m).source_eq]
      exact (hBoundaryPhase m).1

theorem obliqueNoGapOrbitTransport :
  ∀ {C : Tiling.AxisParallel.Approximation.ApproximationContext.{0}}
    (P : Tiling.AxisParallel.Approximation.FLCControlPackage C)
    (B : Tiling.AxisParallel.Approximation.PeriodicBandData C)
    (hFine : Tiling.AxisParallel.Approximation.IsPeriodicBandFineness
      B P.threshold)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : Tiling.AxisParallel.Approximation.IsEpsilonApproximation
      C P.threshold phi)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t : ↥C.centres,
      Tphi t = Tiling.AxisParallel.Approximation.mapPoint phi
        (C.centrePoint t.1 t.2))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion
      (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (diameter G M : ℝ)
    (hDiameter : diameter = Metric.diam C.region.openCarrier)
    (hScales : 0 < diameter ∧ G = 60 * diameter ∧
      max (3 * G) 3 < M ∧ M ≤ P.scale ∧
      10 * (diameter + 1) < P.scale)
    (i : Fin Dcmp.numberOfParts)
    (hOblique : (Dcmp.direction i).toPlane.re *
      (Dcmp.direction i).toPlane.im ≠ 0)
    (Q : RationalSlice (Dcmp.direction i))
    (hOrbitNoGap : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i) G),
    ∃ alpha : {z : Tiling.Plane //
        z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
      (alpha : Tiling.Plane) ≠ 0 ∧
      Tiling.AxisParallel.Approximation.mapPoint phi alpha =
        (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ,
        (alpha : Tiling.Plane) +ᵥ
            originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ,
        ∃ beta : {z : Tiling.Plane //
            z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          Tiling.AxisParallel.regularSupport C.region
              (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
            (beta : Tiling.Plane) +ᵥ
              Tiling.AxisParallel.regularSupport C.region
                (originalSlice i Q) ∧
          Tiling.AxisParallel.Approximation.mapPoint phi beta =
            m • Dcmp.gamma.toPlane ∧
          Tiling.AxisParallel.properVertices
            (Tiling.AxisParallel.regularSupport C.region
              (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C P B hFine phi hphi D Tphi hTphi Dcmp originalSlice hPreimage
    diameter G M hDiameter hScales i hOblique Q hOrbitNoGap
  obtain ⟨out⟩ := bandDeformationOutput_exists B P hFine phi hphi D
  have hEmb : out.centers = Tphi := by
    ext t
    exact (out.centers_apply t).trans (hTphi t).symm
  have hImagePack : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) := by
    have hTiles := out.tiles
    rw [hEmb] at hTiles
    exact hTiles.2.1
  exact obliqueNoGapOrbitTransport_of_imagePacking P phi hphi D Tphi hTphi
    hImagePack Dcmp originalSlice hPreimage diameter G M hDiameter hScales
    i hOblique Q hOrbitNoGap

end Tiling.AxisParallel.Terminal
