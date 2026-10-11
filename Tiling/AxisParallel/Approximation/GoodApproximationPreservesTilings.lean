import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.Basic
import Tiling.Geometry.PackingTopology
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.LocallyFinite

set_option linter.unusedVariables false

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Approximation


/-- Simultaneous first/full coordinate tiling transport, retaining the original centre labels. -/
structure TwoStageDeformationSupportTransport
    (C : ApproximationContext) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C φ) where
  source_tilesOn : Tiling.AxisParallel.TilesOn C.region C.centres Set.univ
  firstCenters : ↥C.centres ↪ Tiling.Plane
  fullCenters : ↥C.centres ↪ Tiling.Plane
  firstCenters_apply : ∀ t : ↥C.centres,
    firstCenters t = mapFirstPoint φ (C.centrePoint t.1 t.2)
  fullCenters_apply : ∀ t : ↥C.centres,
    fullCenters t = mapPoint φ (C.centrePoint t.1 t.2)
  first_tilesOn :
    Tiling.AxisParallel.TilesOn D.firstRegion
      (deformedCenterCarrier firstCenters) Set.univ
  full_tilesOn :
    Tiling.AxisParallel.TilesOn D.deformedRegion
      (deformedCenterCarrier fullCenters) Set.univ
  first_locallyFinite :
    LocallyFinite (deformedCenterSingletonFamily firstCenters)
  full_locallyFinite :
    LocallyFinite (deformedCenterSingletonFamily fullCenters)
  subfamily_support :
    ∀ (S : Set Tiling.Plane), S ⊆ C.centres → ∀ (X : Set ℝ),
      IsOpen X → interior (closure X) = X →
      Tiling.AxisParallel.regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X} →
      ∃ Xφ : Set ℝ, IsOpen Xφ ∧ interior (closure Xφ) = Xφ ∧
        Tiling.AxisParallel.regularSupport D.deformedRegion
          (deformedCenterCarrierOn fullCenters
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =
            {z : Tiling.Plane | z.re ∈ Xφ}

private theorem regularSupport_eq_univ_of_tilesOn
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane)
    (hTiles : Tiling.AxisParallel.TilesOn K S Set.univ) :
    Tiling.AxisParallel.regularSupport K S = Set.univ := by
  have hraw : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Tiling.AxisParallel.openUnion K S := by
    filter_upwards [hTiles.2.2] with x hx
    have hx' : ∃ s : S, x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier) := hx.mp (Set.mem_univ x)
    exact Set.mem_iUnion.mpr hx'
  have hclosure : closure (Tiling.AxisParallel.openUnion K S) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_contra hx
    have hxcomp : x ∈ (closure (Tiling.AxisParallel.openUnion K S))ᶜ := hx
    have hzero : MeasureTheory.volume
        ((closure (Tiling.AxisParallel.openUnion K S))ᶜ) = 0 := by
      apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hraw] with y hy
      exact fun hyc ↦ hyc (subset_closure hy)
    have hpos : 0 < MeasureTheory.volume
        ((closure (Tiling.AxisParallel.openUnion K S))ᶜ) :=
      isClosed_closure.isOpen_compl.measure_pos MeasureTheory.volume ⟨x, hxcomp⟩
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)
  simp only [Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
    ← Tiling.AxisParallel.openUnion.eq_def, hclosure, interior_univ]

theorem regularSupport_coordinateDeformation
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C φ}
    (P : TwoStageDeformationSupportTransport C φ D) :
    Tiling.AxisParallel.regularSupport C.region C.centres = Set.univ ∧
    Tiling.AxisParallel.regularSupport D.firstRegion
      (deformedCenterCarrier P.firstCenters) = Set.univ ∧
    Tiling.AxisParallel.regularSupport D.deformedRegion
      (deformedCenterCarrier P.fullCenters) = Set.univ := by
  exact ⟨regularSupport_eq_univ_of_tilesOn C.region C.centres P.source_tilesOn,
    regularSupport_eq_univ_of_tilesOn D.firstRegion
      (deformedCenterCarrier P.firstCenters) P.first_tilesOn,
    regularSupport_eq_univ_of_tilesOn D.deformedRegion
      (deformedCenterCarrier P.fullCenters) P.full_tilesOn⟩

private def controlledCoord {C : ApproximationContext}
    (axis : Tiling.AxisParallel.Axis)
    (x : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
      z.im ∈ C.coordinateSpace}) : C.coordinateSpace :=
  match axis with
  | .horizontal => ⟨x.1.re, x.2.1⟩
  | .vertical => ⟨x.1.im, x.2.2⟩

private theorem mapScalar_controlledCoord {C : ApproximationContext}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (axis : Tiling.AxisParallel.Axis)
    (x : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
      z.im ∈ C.coordinateSpace}) :
    mapScalar phi (controlledCoord axis x) =
      Tiling.AxisParallel.Axis.coord axis (mapPoint phi x) := by
  cases axis <;>
    simp [controlledCoord, mapScalar, mapPoint, Tiling.AxisParallel.Axis.coord]

private theorem positive_of_same_sign {x y : ℝ}
    (h : Real.sign x = Real.sign y) (hy : 0 < y) : 0 < x := by
  rw [Real.sign_of_pos hy] at h
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx] at h
    norm_num at h
  · simp at h
  · exact hx

theorem filledSlice_order
    (C : ApproximationContext) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsGoodApproximation C phi) (axis : Tiling.AxisParallel.Axis)
    (n : ℕ) (hn : 0 < n)
    (x : Fin (n + 1) →
      {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace})
    (hstep : ∀ i : Fin n,
      ∃ (v w : Tiling.Plane) (_hv : v ∈ C.region.vertices)
        (_hw : w ∈ C.region.vertices),
        0 < Tiling.AxisParallel.Axis.coord axis (w - v) ∧
        Tiling.AxisParallel.Axis.coord axis
          ((x i.succ : Tiling.Plane) - (x i.castSucc : Tiling.Plane)) =
            Tiling.AxisParallel.Axis.coord axis (w - v)) :
    Tiling.AxisParallel.Axis.coord axis
      (mapPoint phi (x (Fin.last n)) - mapPoint phi (x 0)) > 0 := by
  let y : Fin (n + 1) → ℝ := fun i ↦
    Tiling.AxisParallel.Axis.coord axis (mapPoint phi (x i))
  have hyStep : ∀ i : Fin n, y i.castSucc < y i.succ := by
    intro i
    obtain ⟨v, w, hv, hw, hvwPos, hxvw⟩ := hstep i
    have hvertexSign := hphi.preservesVertexCoordinateSign axis w v hw hv
    have hvertexPos : 0 < Tiling.AxisParallel.Axis.coord axis
        (mapPoint phi (C.vertexPoint w hw) - mapPoint phi (C.vertexPoint v hv)) :=
      positive_of_same_sign hvertexSign hvwPos
    have hscalar :
        controlledCoord axis (x i.succ) - controlledCoord axis (x i.castSucc) =
          controlledCoord axis (C.vertexPoint w hw) -
            controlledCoord axis (C.vertexPoint v hv) := by
      apply Subtype.ext
      cases axis <;>
        simpa [controlledCoord, ApproximationContext.vertexPoint,
          Tiling.AxisParallel.Axis.coord] using hxvw
    have hmapped := congrArg phi hscalar
    have hmappedReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hmapped
    have heq : y i.succ - y i.castSucc =
        Tiling.AxisParallel.Axis.coord axis
          (mapPoint phi (C.vertexPoint w hw) - mapPoint phi (C.vertexPoint v hv)) := by
      simp only [map_sub, Rat.cast_sub] at hmappedReal
      change mapScalar phi (controlledCoord axis (x i.succ)) -
          mapScalar phi (controlledCoord axis (x i.castSucc)) =
        mapScalar phi (controlledCoord axis (C.vertexPoint w hw)) -
          mapScalar phi (controlledCoord axis (C.vertexPoint v hv)) at hmappedReal
      rw [mapScalar_controlledCoord phi axis (x i.succ),
        mapScalar_controlledCoord phi axis (x i.castSucc),
        mapScalar_controlledCoord phi axis (C.vertexPoint w hw),
        mapScalar_controlledCoord phi axis (C.vertexPoint v hv)] at hmappedReal
      cases axis <;>
        simpa [y, Tiling.AxisParallel.Axis.coord] using hmappedReal
    linarith
  have hy : StrictMono y := Fin.strictMono_iff_lt_succ.mpr hyStep
  have hindex : (0 : Fin (n + 1)) < Fin.last n := by
    exact hn
  have hends := hy hindex
  have hdiff : y (Fin.last n) - y 0 > 0 := sub_pos.mpr hends
  cases axis <;>
    simpa [y, Tiling.AxisParallel.Axis.coord] using hdiff


open Function MeasureTheory
open scoped Topology

noncomputable section

open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private def IsSecondStageSourceChain (C : ApproximationContext)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C φ)
    (q : ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ) (owner : Fin n → ↥C.centres) : Prop :=
  StrictMono x ∧ ∀ i : Fin n,
    ∃ v w : Tiling.Plane, v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
      x i.castSucc = (v + (owner i : Tiling.Plane)).im ∧
      x i.succ = (w + (owner i : Tiling.Plane)).im ∧ 0 < (w - v).im ∧
      axisInterval Axis.vertical q (x i.castSucc) (x i.succ) ⊆
        mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ D.firstRegion.openCarrier

/-- A transported chain retains strict endpoint order, original owner indices, and target-tile
containment.  It intentionally does not demand a target intrinsic-vertex presentation. -/
private def IsTransportedIndexedSliceChain {ι : Type*} (K : Region) (center : ι → Tiling.Plane)
    (axis : Axis) (q : ℝ) {n : ℕ} (x : Fin (n + 1) → ℝ)
    (owner : Fin n → ι) : Prop :=
  StrictMono x ∧ ∀ i : Fin n,
    axisInterval axis q (x i.castSucc) (x i.succ) ⊆ center (owner i) +ᵥ K.openCarrier

private def IsControlledGapWord {V : Submodule ℚ ℝ} (Δ : Set ℝ) (f : V → ℝ)
    (a b : V) (n : ℕ) (x : Fin (n + 1) → V) : Prop :=
  0 < n ∧ x 0 = a ∧ x (Fin.last n) = b ∧
    StrictMono (fun i => ((x i : V) : ℝ)) ∧
    ∀ i : Fin n, f (x i.succ) - f (x i.castSucc) ∈ Δ

private def IsPositiveGapWord (Δ : Set ℝ) (a b : ℝ)
    (n : ℕ) (y : Fin (n + 1) → ℝ) : Prop :=
  0 < n ∧ y 0 = a ∧ y (Fin.last n) = b ∧ StrictMono y ∧
    ∀ i : Fin n, y i.succ - y i.castSucc ∈ Δ

private structure BoundaryOrderData (C : ApproximationContext) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (X : Set ℝ) where
  lift : ↥(frontier X) → C.coordinateSpace
  lift_coe : ∀ x, (lift x : ℝ) = x.1
  mapped_strictMono : StrictMono (fun x => mapScalar φ (lift x))
  source_locallyFinite : ∀ Q : Set ℝ, Bornology.IsBounded Q → (frontier X ∩ Q).Finite
  mapped_locallyFinite : ∀ Q : Set ℝ, Bornology.IsBounded Q →
    (mapScalarSet φ (Set.range lift) ∩ Q).Finite
  upper_cofinal : ¬ BddAbove (frontier X) → ¬ BddAbove (mapScalarSet φ (Set.range lift))
  lower_cofinal : ¬ BddBelow (frontier X) → ¬ BddBelow (mapScalarSet φ (Set.range lift))

private def secondStagePlanarHomeomorph {C : ApproximationContext}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ) :
    Tiling.Plane ≃ₜ Tiling.Plane :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (((Homeomorph.refl ℝ).prodCongr D.secondHomeomorph).trans
      Complex.equivRealProdCLM.toHomeomorph.symm)

private structure SecondStageTransportData (C : ApproximationContext)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C φ) where
  firstInjective : Injective (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2))
  firstTiles : TilesOn D.firstRegion
    (Set.range (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2))) univ
  region_image : D.deformedRegion.openCarrier =
    secondStagePlanarHomeomorph D '' D.firstRegion.openCarrier
  apply_formula : ∀ z, secondStagePlanarHomeomorph D z =
    z.re + D.secondHomeomorph z.im * Complex.I


private theorem controlledSourceEndpointLift :
    ∀ {C : ApproximationContext.{u}},
      TilesOn C.region C.centres univ → ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
        ∃ lift : ↥(sliceEndpointSet C.region C.centres axis q) → C.coordinateSpace,
          ∀ x, (lift x : ℝ) = x.1 := by
  intro C hTile axis
  filter_upwards
    [genericSliceEndpointSet_unbounded C.region C.centres hTile axis,
      genericSliceChain_betweenEndpoints C.region C.centres hTile axis] with q hends hchain
  have endpoint_mem (a : ↥(sliceEndpointSet C.region C.centres axis q)) :
      a.1 ∈ C.coordinateSpace := by
    rw [not_bddAbove_iff] at hends
    obtain ⟨b, hb, hab⟩ := hends.1 a.1
    obtain ⟨n, hn, x, owner, hx0, _hxlast, hxchain⟩ :=
      hchain a.1 a.2 b hb hab
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ :=
      hxchain.2 (⟨0, hn⟩ : Fin n)
    have ha : a.1 = axis.coord (v + (owner ⟨0, hn⟩).1) := by
      rw [← hleft, ← hx0]
      rfl
    rw [ha]
    cases axis
    · exact C.coordinateSpace.add_mem
        (C.vertex_re_mem v hv) (C.centre_re_mem _ (owner ⟨0, hn⟩).2)
    · exact C.coordinateSpace.add_mem
        (C.vertex_im_mem v hv) (C.centre_im_mem _ (owner ⟨0, hn⟩).2)
  let lift : ↥(sliceEndpointSet C.region C.centres axis q) → C.coordinateSpace :=
    fun x => ⟨x.1, endpoint_mem x⟩
  exact ⟨lift, fun _ => rfl⟩

private theorem controlledSliceChain :
    ∀ {C : ApproximationContext.{u}},
      TilesOn C.region C.centres univ → ∀ axis : Axis, ∀ᵐ q : ℝ ∂volume,
      ∀ a b : ℝ, a < b → ∃ (n : ℕ) (_hn : 0 < n)
        (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) ∧ x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
          IsFilledIndexedSliceChain C.region C.centres axis q x owner := by
  intro C hTile axis
  filter_upwards
    [genericIndexedSliceChain C.region C.centres hTile axis] with q hchain
  intro a b hab
  obtain ⟨n, hn, x, owner, hxa, hbx, hxchain⟩ := hchain a b hab
  cases n with
  | zero => omega
  | succ n =>
      have xmem : ∀ i : Fin (n + 2), x i ∈ C.coordinateSpace := by
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ :=
            hxchain.2 (Fin.last n)
          rw [show Fin.last (n + 1) = (Fin.last n).succ by ext; simp, hright]
          cases axis
          · exact C.coordinateSpace.add_mem
              (C.vertex_re_mem w hw) (C.centre_re_mem _ (owner (Fin.last n)).2)
          · exact C.coordinateSpace.add_mem
              (C.vertex_im_mem w hw) (C.centre_im_mem _ (owner (Fin.last n)).2)
        · obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ :=
            hxchain.2 j
          rw [hleft]
          cases axis
          · exact C.coordinateSpace.add_mem
              (C.vertex_re_mem v hv) (C.centre_re_mem _ (owner j).2)
          · exact C.coordinateSpace.add_mem
              (C.vertex_im_mem v hv) (C.centre_im_mem _ (owner j).2)
      let xLift : Fin (n + 2) → C.coordinateSpace := fun i => ⟨x i, xmem i⟩
      exact ⟨n + 1, by omega, x, xLift, owner, fun _ => rfl, hxa, hbx, hxchain⟩

private theorem firstRegionVerticalEndpointLift_of_filledSliceChains
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (P : SecondStageTransportData C φ D)
    (hVertices :
      D.firstRegion.vertices = D.firstPlanarHomeomorph '' C.region.vertices) :
    ∀ᵐ q : ℝ ∂volume,
      ∃ lift : ↥(sliceEndpointSet D.firstRegion
          (Set.range (fun t : ↥C.centres =>
            mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q) →
          C.coordinateSpace,
        ∀ x, (lift x : ℝ) = x.1 := by
  let A : Set Tiling.Plane :=
    Set.range (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2))
  filter_upwards
    [genericSliceEndpointSet_unbounded D.firstRegion A P.firstTiles Axis.vertical,
      genericSliceChain_betweenEndpoints D.firstRegion A P.firstTiles Axis.vertical] with
      q hends hchain
  have endpoint_mem (a : ↥(sliceEndpointSet D.firstRegion A Axis.vertical q)) :
      a.1 ∈ C.coordinateSpace := by
    rw [not_bddAbove_iff] at hends
    obtain ⟨b, hb, hab⟩ := hends.1 a.1
    obtain ⟨n, hn, x, owner, hx0, _hxlast, hxchain⟩ :=
      hchain a.1 a.2 b hb hab
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ :=
      hxchain.2 (⟨0, hn⟩ : Fin n)
    rw [hVertices] at hv
    obtain ⟨v0, hv0, rfl⟩ := hv
    obtain ⟨t, ht⟩ := (owner ⟨0, hn⟩).2
    have ha : a.1 =
        (D.firstPlanarHomeomorph v0 +
          mapFirstPoint φ (C.centrePoint t.1 t.2)).im := by
      calc
        a.1 = x 0 := hx0.symm
        _ = x (⟨0, hn⟩ : Fin n).castSucc := rfl
        _ = Axis.vertical.coord
            (D.firstPlanarHomeomorph v0 + (owner ⟨0, hn⟩).1) := hleft
        _ = (D.firstPlanarHomeomorph v0 +
            mapFirstPoint φ (C.centrePoint t.1 t.2)).im := by
              rw [← ht]
              rfl
    have hHim : (D.firstPlanarHomeomorph v0).im = v0.im := by
      rw [D.firstPlanarHomeomorph_apply]
      simp
    have hTim : (mapFirstPoint φ (C.centrePoint t.1 t.2)).im = t.1.im := by
      simp [mapFirstPoint, ApproximationContext.centrePoint]
    rw [ha, Complex.add_im, hHim, hTim]
    exact C.coordinateSpace.add_mem
      (C.vertex_im_mem v0 hv0) (C.centre_im_mem t.1 t.2)
  let lift : ↥(sliceEndpointSet D.firstRegion A Axis.vertical q) →
      C.coordinateSpace := fun x => ⟨x.1, endpoint_mem x⟩
  exact ⟨lift, fun _ => rfl⟩

private theorem mapScalar_endpoint_eq_firstHomeomorph_add_center
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).re) :
    mapScalar φ xLift =
      D.firstHomeomorph v.re +
        (mapFirstPoint φ (C.centrePoint t.1 t.2)).re := by
  let vr : C.coordinateSpace := ⟨v.re, C.vertex_re_mem v hv⟩
  let tr : C.coordinateSpace := ⟨t.1.re, C.centre_re_mem t.1 t.2⟩
  have hxl : xLift = vr + tr := by
    apply Subtype.ext
    simp [vr, tr, hLift, hx]
  have hvertex := congrArg Complex.re (D.first_vertex_agreement v hv)
  have hvertex' : mapScalar φ vr = D.firstHomeomorph v.re := by
    simpa [vr, mapFirstPoint, ApproximationContext.vertexPoint,
      D.firstPlanarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((φ vr : ℚ) : ℝ) = mapScalar φ vr by rfl, hvertex']
  congr 1
  simp [tr, mapFirstPoint, mapScalar, ApproximationContext.centrePoint]

private theorem firstSliceChain_mapped_strictMono
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q : ℝ} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) (hLift : ∀ i, (xLift i : ℝ) = x i)
    (hchain : IsFilledIndexedSliceChain
      C.region C.centres Axis.horizontal q x owner) :
    StrictMono (fun i => mapScalar φ (xLift i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  have hvw : v.re < w.re := by
    simpa [Axis.coord] using (sub_pos.mp hpositive)
  rw [mapScalar_endpoint_eq_firstHomeomorph_add_center D v hv (owner i)
      (x i.castSucc) (xLift i.castSucc) (hLift i.castSucc) hleft,
    mapScalar_endpoint_eq_firstHomeomorph_add_center D w hw (owner i)
      (x i.succ) (xLift i.succ) (hLift i.succ) hright]
  simpa [add_comm] using
    (add_lt_add_right (D.firstHomeomorph_strictMono hvw)
      (mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2)).re)

private theorem firstSliceGap_transport
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q x₀ x₁ : ℝ}
    (xLift₀ xLift₁ : C.coordinateSpace) (t : ↥C.centres)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hlift₀ : (xLift₀ : ℝ) = x₀) (hlift₁ : (xLift₁ : ℝ) = x₁)
    (hleft : x₀ = (v + (t : Tiling.Plane)).re)
    (hright : x₁ = (w + (t : Tiling.Plane)).re)
    (hinside : axisInterval Axis.horizontal q x₀ x₁ ⊆
      (t : Tiling.Plane) +ᵥ C.region.openCarrier) :
    axisInterval Axis.horizontal q (mapScalar φ xLift₀) (mapScalar φ xLift₁) ⊆
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier := by
  intro z hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [D.firstRegion_openCarrier]
  let c := mapFirstPoint φ (C.centrePoint t.1 t.2)
  let r : ℝ := D.firstHomeomorph.symm (z.re - c.re)
  let p : Tiling.Plane := (r : ℂ) + ((q - t.1.im : ℝ) : ℂ) * Complex.I
  have hend₀ := mapScalar_endpoint_eq_firstHomeomorph_add_center
    D v hv t x₀ xLift₀ hlift₀ hleft
  have hend₁ := mapScalar_endpoint_eq_firstHomeomorph_add_center
    D w hw t x₁ xLift₁ hlift₁ hright
  have hzre : z.re ∈ Ioo (mapScalar φ xLift₀) (mapScalar φ xLift₁) := hz.2
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
          Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul, sub_zero]
        constructor <;> linarith
    have := hinside hs
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_cancel_left] using this
  refine ⟨p, hp, ?_⟩
  rw [D.firstPlanarHomeomorph_apply]
  apply Complex.ext
  · simp [p, r, c]
    ring
  · have hzq : z.im = q := hz.1
    simp [p, mapFirstPoint, ApproximationContext.centrePoint, hzq]
    ring

private theorem firstSliceChain_transport
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (_hT : TilesOn C.region C.centres univ) :
    ∀ᵐ q : ℝ ∂volume, ∀ {n : ℕ} (x : Fin (n + 1) → ℝ)
      (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
      (∀ i, (xLift i : ℝ) = x i) →
      IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner →
      IsTransportedIndexedSliceChain D.firstRegion
        (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2))
        Axis.horizontal q (fun i => mapScalar φ (xLift i)) owner := by
  filter_upwards [] with q
  intro n x xLift owner hLift hchain
  refine ⟨firstSliceChain_mapped_strictMono D x xLift owner hLift hchain, ?_⟩
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, _hpositive, hinside⟩ := hchain.2 i
  exact firstSliceGap_transport D (xLift i.castSucc) (xLift i.succ) (owner i)
    v w hv hw (hLift i.castSucc) (hLift i.succ) hleft hright hinside


theorem firstRegion_vertices_image
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    D.firstRegion.vertices = D.firstPlanarHomeomorph '' C.region.vertices := by
  obtain ⟨L, _hsupport, hopen, hvertices⟩ :=
    exists_coordinateProductImageRegion C.region D.firstHomeomorph
      (Homeomorph.refl ℝ) D.firstHomeomorph_strictMono strictMono_id
  have hplanar :
      coordinateProductHomeomorph
          D.firstHomeomorph (Homeomorph.refl ℝ) =
        D.firstPlanarHomeomorph := by
    ext z
    rw [D.firstPlanarHomeomorph_apply]
    apply Complex.ext <;>
      simp [coordinateProductHomeomorph]
  have hregion : L = D.firstRegion := by
    apply region_ext_openCarrier
    rw [hopen, hplanar, D.firstRegion_openCarrier]
  rw [← hregion, hvertices, hplanar]


private theorem strictMono_gap_owner_unique {n : ℕ}
    {x : Fin (n + 1) → ℝ} (hx : StrictMono x) {i j : Fin n} {a : ℝ}
    (hi : a ∈ Ioo (x i.castSucc) (x i.succ))
    (hj : a ∈ Ioo (x j.castSucc) (x j.succ)) : i = j := by
  rcases lt_trichotomy i j with hij | hij | hij
  · have hs : i.succ ≤ j.castSucc := by
      change i.1 + 1 ≤ j.1
      omega
    have hxs : x i.succ ≤ x j.castSucc := hx.monotone hs
    linarith [hi.2, hj.1]
  · exact hij
  · have hs : j.succ ≤ i.castSucc := by
      change j.1 + 1 ≤ i.1
      omega
    have hxs : x j.succ ≤ x i.castSucc := hx.monotone hs
    linarith [hj.2, hi.1]

private theorem filledChain_owner_eq_of_mem
    {K : Region} {T : Set Tiling.Plane} (hT : TilesOn K T univ)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner)
    (i : Fin n) (t : ↥T) {z : Tiling.Plane}
    (hzi : z ∈ axisInterval Axis.horizontal q (x i.castSucc) (x i.succ))
    (hzt : z ∈ (t : Tiling.Plane) +ᵥ K.openCarrier) : owner i = t := by
  by_contra hne
  have hd := (isPacking_iff_openCarrier_disjoint K T).mp hT.2.1
    (owner i).2 t.2 (fun h => hne (Subtype.ext h))
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  exact Set.disjoint_left.1 hd (hinside hzi) hzt

private theorem strictMono_exists_gap {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) {a : ℝ} (hleft : x 0 < a)
    (hright : a < x (Fin.last n)) (hne : ∀ k, a ≠ x k) :
    ∃ i : Fin n, a ∈ Ioo (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => exfalso; simpa using (lt_asymm hleft hright)
  | succ n ih =>
      rcases lt_trichotomy a (x 1) with ha | ha | ha
      · exact ⟨⟨0, Nat.succ_pos _⟩, hleft, ha⟩
      · exact False.elim (hne 1 ha)
      · let y : Fin (n + 1) → ℝ := fun k => x k.succ
        have hy : StrictMono y := by
          intro i j hij
          apply hx
          simpa using hij
        have hylast : a < y (Fin.last n) := by
          simpa [y] using hright
        have hyne : ∀ k, a ≠ y k := fun k => hne k.succ
        obtain ⟨i, hi⟩ := ih y hy ha hylast hyne
        refine ⟨i.succ, ?_⟩
        simpa [y] using hi

private def firstSourcePoint
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    Tiling.Plane :=
  (t : Tiling.Plane) +
    D.firstPlanarHomeomorph.symm
      (-(mapFirstPoint φ (C.centrePoint t.1 t.2)) + z)

private theorem firstSourcePoint_mem
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) {z : Tiling.Plane}
    (hz : z ∈ mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
      D.firstRegion.openCarrier) :
    firstSourcePoint D t z ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [firstSourcePoint, vadd_eq_add, neg_add_cancel_left]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.firstRegion_openCarrier] at hz
  obtain ⟨p, hp, heq⟩ := hz
  simp only [vadd_eq_add] at heq
  rw [← heq, Homeomorph.symm_apply_apply]
  exact hp

private theorem firstSourcePoint_im
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    (firstSourcePoint D t z).im = z.im := by
  have himage (p : Tiling.Plane) : (D.firstPlanarHomeomorph p).im = p.im := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  let y := -(mapFirstPoint φ (C.centrePoint t.1 t.2)) + z
  have hinv : (D.firstPlanarHomeomorph.symm y).im = y.im := by
    have hp := himage (D.firstPlanarHomeomorph.symm y)
    rw [Homeomorph.apply_symm_apply] at hp
    exact hp.symm
  change t.1.im + (D.firstPlanarHomeomorph.symm y).im = z.im
  rw [hinv]
  simp [y, mapFirstPoint, ApproximationContext.centrePoint]

private theorem exists_mem_Ioo_avoiding_finset {a b : ℝ} (hab : a < b)
    (F : Finset ℝ) : ∃ x ∈ Ioo a b, x ∉ F := by
  by_contra h
  push Not at h
  have hsub : Ioo a b ⊆ (F : Set ℝ) := fun x hx => h x hx
  exact Set.Ioo_infinite hab ((F.finite_toSet).subset hsub)

private theorem exists_mem_Ioo_of_ae_real {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hP : ∀ᵐ x : ℝ ∂volume, P x) :
    ∃ x ∈ Ioo a b, P x := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    intro hz
    have : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo a b), hz]
      simp
    rw [Real.volume_Ioo] at this
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at this
  let hne : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hμ
  have hp' : ∀ᵐ x ∂volume.restrict (Ioo a b), P x := hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, hp, hx⟩
  exact ⟨x, hx, hp⟩

private def firstOwnerMap
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (r : ℝ) : ℝ :=
  D.firstHomeomorph (r - t.1.re) +
    (mapFirstPoint φ (C.centrePoint t.1 t.2)).re

private theorem firstOwnerMap_strictMono
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) :
    StrictMono (firstOwnerMap D t) := by
  intro a b hab
  simpa [firstOwnerMap, add_comm] using
    add_lt_add_right (D.firstHomeomorph_strictMono (by linarith : a - t.1.re < b - t.1.re))
      (mapFirstPoint φ (C.centrePoint t.1 t.2)).re

private theorem firstOwnerMap_chainEndpoint
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q : ℝ} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) (hLift : ∀ i, (xLift i : ℝ) = x i)
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (i : Fin n) :
    firstOwnerMap D (owner i) (x i.castSucc) = mapScalar φ (xLift i.castSucc) ∧
      firstOwnerMap D (owner i) (x i.succ) = mapScalar φ (xLift i.succ) := by
  obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hchain.2 i
  constructor
  · rw [mapScalar_endpoint_eq_firstHomeomorph_add_center D v hv (owner i)
      _ _ (hLift i.castSucc) hleft]
    simp [firstOwnerMap, hleft, Axis.coord]
  · rw [mapScalar_endpoint_eq_firstHomeomorph_add_center D w hw (owner i)
      _ _ (hLift i.succ) hright]
    simp [firstOwnerMap, hright, Axis.coord]

private theorem firstOwnerMap_firstSourcePoint_re
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    firstOwnerMap D t (firstSourcePoint D t z).re = z.re := by
  have hre (p : Tiling.Plane) :
      (D.firstPlanarHomeomorph p).re = D.firstHomeomorph p.re := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  let y := -(mapFirstPoint φ (C.centrePoint t.1 t.2)) + z
  have hinv : D.firstHomeomorph (D.firstPlanarHomeomorph.symm y).re = y.re := by
    rw [← hre]
    exact congrArg Complex.re (D.firstPlanarHomeomorph.apply_symm_apply y)
  simp only [firstOwnerMap, firstSourcePoint, Complex.add_re]
  have harg : t.1.re + (D.firstPlanarHomeomorph.symm y).re - t.1.re =
      (D.firstPlanarHomeomorph.symm y).re := by ring
  change D.firstHomeomorph
      (t.1.re + (D.firstPlanarHomeomorph.symm y).re - t.1.re) +
        (mapFirstPoint φ (C.centrePoint t.1 t.2)).re = z.re
  rw [harg]
  rw [hinv]
  simp [y]

private theorem firstTranslatedInteriors_overlap_reflect :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (s t : ↥C.centres),
      ((mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ D.firstRegion.openCarrier) ∩
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier)).Nonempty →
        s = t := by
  intro C φ D hT s t hoverlap
  obtain ⟨z, hzs, hzt⟩ := hoverlap
  let O : Set Tiling.Plane :=
    (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ D.firstRegion.openCarrier) ∩
      (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier)
  have hOopen : IsOpen O :=
    (D.firstRegion.openCarrier_regularOpen.1.vadd _).inter
      (D.firstRegion.openCarrier_regularOpen.1.vadd _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOopen z ⟨hzs, hzt⟩
  have hgood : ∀ᵐ q : ℝ ∂volume,
      (∀ a b : ℝ, a < b → ∃ (n : ℕ) (_hn : 0 < n)
        (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) ∧ x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
          IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner) ∧
      (∀ {n : ℕ} (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) →
        IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner →
        IsTransportedIndexedSliceChain D.firstRegion
          (fun u : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint u.1 u.2))
          Axis.horizontal q (fun i ↦ mapScalar φ (xLift i)) owner) := by
    filter_upwards
      [controlledSliceChain hT Axis.horizontal,
        firstSliceChain_transport D hT] with q hchain htransport
    exact ⟨hchain, htransport⟩
  obtain ⟨q, hqI, hchainAt, htransportAt⟩ :=
    exists_mem_Ioo_of_ae_real (by linarith [hε] : z.im - ε / 4 < z.im + ε / 4) hgood
  let sl : Tiling.Plane := firstSourcePoint D s (Complex.mk (z.re - ε / 4) q)
  let tl : Tiling.Plane := firstSourcePoint D t (Complex.mk (z.re - ε / 4) q)
  let sh : Tiling.Plane := firstSourcePoint D s (Complex.mk (z.re + ε / 4) q)
  let th : Tiling.Plane := firstSourcePoint D t (Complex.mk (z.re + ε / 4) q)
  let A : ℝ := min sl.re tl.re - 1
  let B : ℝ := max sh.re th.re + 1
  have hslope : sl.re < sh.re := by
    apply (firstOwnerMap_strictMono D s).lt_iff_lt.mp
    rw [firstOwnerMap_firstSourcePoint_re, firstOwnerMap_firstSourcePoint_re]
    linarith [hε]
  have hminmax : min sl.re tl.re ≤ max sh.re th.re :=
    (min_le_left _ _).trans (hslope.le.trans (le_max_left _ _))
  have hAB : A < B := by dsimp [A, B]; linarith
  obtain ⟨n, hn, x, xLift, owner, hLift, hxA, hBx, hchain⟩ := hchainAt A B hAB
  let forbidden : Finset ℝ :=
    (Finset.univ.image (fun k : Fin (n + 1) ↦ firstOwnerMap D s (x k))) ∪
      (Finset.univ.image (fun k : Fin (n + 1) ↦ firstOwnerMap D t (x k)))
  obtain ⟨p, hpI, hpavoid⟩ := exists_mem_Ioo_avoiding_finset
    (by linarith [hε] : z.re - ε / 4 < z.re + ε / 4) forbidden
  let w : Tiling.Plane := Complex.mk p q
  have hwball : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, show w - z =
      ((p - z.re : ℝ) : ℂ) + ((q - z.im : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp [w]]
    calc
      ‖((p - z.re : ℝ) : ℂ) + ((q - z.im : ℝ) : ℂ) * Complex.I‖
          ≤ ‖((p - z.re : ℝ) : ℂ)‖ +
              ‖((q - z.im : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |p - z.re| + |q - z.im| := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_I, mul_one]
      _ < ε := by
        have hpabs : |p - z.re| < ε / 4 := (abs_lt).2 ⟨by linarith [hpI.1], by linarith [hpI.2]⟩
        have hqabs : |q - z.im| < ε / 4 := (abs_lt).2 ⟨by linarith [hqI.1], by linarith [hqI.2]⟩
        linarith
  have hwo : w ∈ O := hball hwball
  have hws := firstSourcePoint_mem D s hwo.1
  have hwt := firstSourcePoint_mem D t hwo.2
  let rs := (firstSourcePoint D s w).re
  let rt := (firstSourcePoint D t w).re
  have hslrs : sl.re < rs := by
    apply (firstOwnerMap_strictMono D s).lt_iff_lt.mp
    rw [firstOwnerMap_firstSourcePoint_re, firstOwnerMap_firstSourcePoint_re]
    exact hpI.1
  have htlrt : tl.re < rt := by
    apply (firstOwnerMap_strictMono D t).lt_iff_lt.mp
    rw [firstOwnerMap_firstSourcePoint_re, firstOwnerMap_firstSourcePoint_re]
    exact hpI.1
  have hrssh : rs < sh.re := by
    apply (firstOwnerMap_strictMono D s).lt_iff_lt.mp
    rw [firstOwnerMap_firstSourcePoint_re, firstOwnerMap_firstSourcePoint_re]
    exact hpI.2
  have hrtth : rt < th.re := by
    apply (firstOwnerMap_strictMono D t).lt_iff_lt.mp
    rw [firstOwnerMap_firstSourcePoint_re, firstOwnerMap_firstSourcePoint_re]
    exact hpI.2
  have hrsA : x 0 < rs := by
    have : A < rs := by dsimp [A]; linarith [min_le_left sl.re tl.re]
    exact lt_of_le_of_lt hxA this
  have hrtA : x 0 < rt := by
    have : A < rt := by dsimp [A]; linarith [min_le_right sl.re tl.re]
    exact lt_of_le_of_lt hxA this
  have hrsB : rs < x (Fin.last n) := by
    have : rs < B := by dsimp [B]; linarith [le_max_left sh.re th.re]
    exact lt_of_lt_of_le this hBx
  have hrtB : rt < x (Fin.last n) := by
    have : rt < B := by dsimp [B]; linarith [le_max_right sh.re th.re]
    exact lt_of_lt_of_le this hBx
  have hrsne : ∀ k, rs ≠ x k := by
    intro k heq
    apply hpavoid
    apply Finset.mem_union_left
    apply Finset.mem_image.2
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [← heq, firstOwnerMap_firstSourcePoint_re]
  have hrtne : ∀ k, rt ≠ x k := by
    intro k heq
    apply hpavoid
    apply Finset.mem_union_right
    apply Finset.mem_image.2
    refine ⟨k, Finset.mem_univ _, ?_⟩
    rw [← heq, firstOwnerMap_firstSourcePoint_re]
  obtain ⟨i, hi⟩ := strictMono_exists_gap x hchain.1 hrsA hrsB hrsne
  obtain ⟨j, hj⟩ := strictMono_exists_gap x hchain.1 hrtA hrtB hrtne
  have hwsi : firstSourcePoint D s w ∈
      axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) := by
    exact ⟨by simp [firstSourcePoint_im, w], hi⟩
  have hwtj : firstSourcePoint D t w ∈
      axisInterval Axis.horizontal q (x j.castSucc) (x j.succ) := by
    exact ⟨by simp [firstSourcePoint_im, w], hj⟩
  have hoi : owner i = s := filledChain_owner_eq_of_mem hT hchain i s hwsi hws
  have hoj : owner j = t := filledChain_owner_eq_of_mem hT hchain j t hwtj hwt
  have htrans := htransportAt x xLift owner hLift hchain
  have hepi := firstOwnerMap_chainEndpoint D x xLift owner hLift hchain i
  have hepj := firstOwnerMap_chainEndpoint D x xLift owner hLift hchain j
  have hwi : w ∈ axisInterval Axis.horizontal q
      (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ)) := by
    refine ⟨by simp [w], ?_⟩
    rw [← hepi.1, ← hepi.2, hoi]
    have hm := firstOwnerMap_strictMono D s
    constructor
    · rw [← firstOwnerMap_firstSourcePoint_re D s w]
      exact hm hi.1
    · rw [← firstOwnerMap_firstSourcePoint_re D s w]
      exact hm hi.2
  have hwj : w ∈ axisInterval Axis.horizontal q
      (mapScalar φ (xLift j.castSucc)) (mapScalar φ (xLift j.succ)) := by
    refine ⟨by simp [w], ?_⟩
    rw [← hepj.1, ← hepj.2, hoj]
    have hm := firstOwnerMap_strictMono D t
    constructor
    · rw [← firstOwnerMap_firstSourcePoint_re D t w]
      exact hm hj.1
    · rw [← firstOwnerMap_firstSourcePoint_re D t w]
      exact hm hj.2
  have hij : i = j := strictMono_gap_owner_unique htrans.1 hwi.2 hwj.2
  rw [← hoi, ← hoj, hij]

private theorem firstCenter_formula_injective :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      Injective (fun t : ↥C.centres ↦
        mapFirstPoint φ (C.centrePoint t.1 t.2)) := by
  intro C φ D hT s t heq
  apply firstTranslatedInteriors_overlap_reflect D hT s t
  obtain ⟨p, hp⟩ := D.firstRegion.isPolygonal.interior_nonempty D.firstRegion.nonempty
  change mapFirstPoint φ (C.centrePoint s.1 s.2) =
    mapFirstPoint φ (C.centrePoint t.1 t.2) at heq
  refine ⟨mapFirstPoint φ (C.centrePoint s.1 s.2) + p, ?_, ?_⟩
  · exact ⟨p, hp, rfl⟩
  · rw [← heq]
    exact ⟨p, hp, rfl⟩

private theorem firstCoordinateDeformation_tilesOn_of_exhaustion
    (hexhaust : ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ),
      TilesOn C.region C.centres univ → ∀ᵐ q : ℝ ∂volume,
        ∀ᵐ x : ℝ ∂volume, ∃ t : ↥C.centres,
          (x : ℂ) + (q : ℂ) * Complex.I ∈
            mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier) :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ), ∃ T₁ : ↥C.centres ↪ Tiling.Plane,
      (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn D.firstRegion (deformedCenterCarrier T₁) univ := by
  intro C φ D hT
  let T₁ : ↥C.centres ↪ Tiling.Plane :=
    ⟨fun t ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
      firstCenter_formula_injective D hT⟩
  refine ⟨T₁, fun _ ↦ rfl, ?_⟩
  let _ : Countable ↥C.centres := hT.1.to_subtype
  refine ⟨Set.countable_range T₁, ?_, ?_⟩
  · apply (isPacking_iff_openCarrier_disjoint D.firstRegion
      (deformedCenterCarrier T₁)).2
    intro a ha b hb hab
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    apply Set.disjoint_left.2
    intro z hzs hzt
    apply hab
    apply congrArg T₁
    exact firstTranslatedInteriors_overlap_reflect D hT s t ⟨z, hzs, hzt⟩
  · have hslices := hexhaust D hT
    have hmeas : MeasurableSet {p : ℝ × ℝ | ∃ t : ↥C.centres,
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈
          mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier} := by
      have hopen : IsOpen (openUnion D.firstRegion (deformedCenterCarrier T₁)) :=
        isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _
      have hcontinuous : Continuous (fun p : ℝ × ℝ ↦
          (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
      have hm := hopen.measurableSet.preimage hcontinuous.measurable
      convert hm using 1
      ext p
      simp only [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, deformedCenterCarrier, T₁, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨⟨T₁ t, ⟨t, rfl⟩⟩, ht⟩
      · rintro ⟨a, ha⟩
        obtain ⟨t, ht⟩ := a.2
        refine ⟨t, ?_⟩
        have ha' := ha
        rw [← ht] at ha'
        exact ha'
    have hswapped : ∀ᵐ x : ℝ ∂volume, ∀ᵐ q : ℝ ∂volume,
        ∃ t : ↥C.centres, (x : ℂ) + (q : ℂ) * Complex.I ∈
          mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier :=
      (MeasureTheory.Measure.ae_ae_comm hmeas).2 hslices
    have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, ∃ t : ↥C.centres,
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier :=
      (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).2 hswapped
    have hplane := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
    filter_upwards [hplane] with z hz
    simp only [mem_univ, true_iff]
    rcases hz with ⟨t, ht⟩
    refine ⟨⟨T₁ t, ⟨t, rfl⟩⟩, ?_⟩
    change z ∈ mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
      D.firstRegion.openCarrier
    rw [show z = (z.re : ℂ) + (z.im : ℂ) * Complex.I by
      apply Complex.ext <;> simp]
    exact ht

private theorem secondStagePlanarHomeomorph_apply
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (z : Tiling.Plane) :
    secondStagePlanarHomeomorph D z =
      z.re + D.secondHomeomorph z.im * Complex.I := by
  rw [secondStagePlanarHomeomorph]
  change Complex.equivRealProdCLM.symm
    (z.re, D.secondHomeomorph z.im) = _
  rw [Complex.equivRealProdCLM_symm_apply]

private theorem secondStage_region_image
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    D.deformedRegion.openCarrier =
      secondStagePlanarHomeomorph D '' D.firstRegion.openCarrier := by
  rw [D.deformedRegion_openCarrier, D.firstRegion_openCarrier, Set.image_image]
  congr 1
  funext z
  rw [secondStagePlanarHomeomorph_apply,
    D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply]
  apply Complex.ext <;> simp

private theorem secondStageTransportData_exists_of_first
    (hfirst : ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ),
      TilesOn C.region C.centres univ → ∃ T₁ : ↥C.centres ↪ Tiling.Plane,
        (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) ∧
          TilesOn D.firstRegion (deformedCenterCarrier T₁) univ) :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      Nonempty (SecondStageTransportData C φ D) := by
  intro C φ D hT
  obtain ⟨T₁, hT₁, htiles⟩ := hfirst D hT
  have hrange : deformedCenterCarrier T₁ =
      Set.range (fun t : ↥C.centres ↦
        mapFirstPoint φ (C.centrePoint t.1 t.2)) := by
    ext z
    simp only [deformedCenterCarrier, Set.mem_range]
    constructor <;> rintro ⟨t, rfl⟩ <;> exact ⟨t, by simp [hT₁]⟩
  refine ⟨{
    firstInjective := by
      intro s t heq
      apply T₁.injective
      simpa only [hT₁] using heq
    firstTiles := by simpa only [← hrange] using htiles
    region_image := secondStage_region_image D
    apply_formula := secondStagePlanarHomeomorph_apply D }⟩

private theorem fin_gap_telescope {n : ℕ} (y : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (y i.succ - y i.castSucc) = y (Fin.last n) - y 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      let y' : Fin (n + 1) → ℝ := fun i ↦ y i.succ
      have htail : ∑ i : Fin n, (y' i.succ - y' i.castSucc) =
          y (Fin.last (n + 1)) - y 1 := by
        simpa [y'] using ih y'
      change (y 1 - y 0) + ∑ i : Fin n, (y' i.succ - y' i.castSucc) =
        y (Fin.last (n + 1)) - y 0
      rw [htail]
      ring

private theorem positiveGapWord_telescope
    {Δ : Set ℝ} {a b : ℝ} {n : ℕ} {y : Fin (n + 1) → ℝ}
    (h : IsPositiveGapWord Δ a b n y) :
    ∑ i : Fin n, (y i.succ - y i.castSucc) = b - a := by
  rw [fin_gap_telescope, h.2.1, h.2.2.1]

private theorem positiveGapWords_upper_cofinal
    {E Δ : Set ℝ} {f : E → ℝ}
    (hΔfin : Δ.Finite) (hΔpos : ∀ d ∈ Δ, 0 < d)
    (hf : StrictMono f)
    (hwords : ∀ a b : E, a.1 < b.1 → ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
      IsPositiveGapWord Δ (f a) (f b) n word)
    (hE : ¬ BddAbove E) : ¬ BddAbove (Set.range f) := by
  classical
  intro himage
  obtain ⟨a0, ha0, _⟩ := (not_bddAbove_iff.1 hE) 0
  let a : E := ⟨a0, ha0⟩
  obtain ⟨b0, hb0, hab⟩ := (not_bddAbove_iff.1 hE) a0
  let b : E := ⟨b0, hb0⟩
  obtain ⟨n0, word0, hw0⟩ := hwords a b hab
  have hΔne : Δ.Nonempty := by
    let i : Fin n0 := ⟨0, hw0.1⟩
    exact ⟨word0 i.succ - word0 i.castSucc, hw0.2.2.2.2 i⟩
  let F : Finset ℝ := hΔfin.toFinset
  let δ : ℝ := F.min' (by simpa [F] using hΔne)
  have hδmem : δ ∈ Δ := by
    simpa [F, δ] using F.min'_mem (by simpa [F] using hΔne)
  have hδ : 0 < δ := hΔpos δ hδmem
  obtain ⟨M, hM⟩ := himage
  obtain ⟨N, hN⟩ := exists_nat_gt ((M - f a) / δ)
  let _ : Finite ↥Δ := hΔfin
  let Codes := Σ k : Fin N, Fin k.1 → ↥Δ
  let value : Codes → ℝ := fun c ↦ f a + ∑ i, (c.2 i).1
  have hvalues : (Set.range value).Finite := Set.finite_range value
  let U : Set E := {b | a.1 < b.1}
  have hfu : f '' U ⊆ Set.range value := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨n, word, hw⟩ := hwords a c hc
    have hlower : (n : ℝ) * δ ≤ f c - f a := by
      rw [← positiveGapWord_telescope hw]
      simpa [nsmul_eq_mul, mul_comm] using
        (Finset.card_nsmul_le_sum Finset.univ
          (fun i : Fin n ↦ word i.succ - word i.castSucc) δ (by
            intro i _
            exact F.min'_le _ (by simpa [F] using hw.2.2.2.2 i)))
    have hfcM : f c ≤ M := hM ⟨c, rfl⟩
    have hnN : n < N := by
      have hnreal : (n : ℝ) < N := by
        have hMN : M - f a < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
        nlinarith
      exact_mod_cast hnreal
    let code : Codes := ⟨⟨n, hnN⟩,
      fun i ↦ ⟨word i.succ - word i.castSucc, hw.2.2.2.2 i⟩⟩
    refine ⟨code, ?_⟩
    simp only [value, code]
    linarith [positiveGapWord_telescope hw]
  have hUfinite : U.Finite := by
    apply Set.Finite.of_finite_image (hvalues.subset hfu)
    exact hf.injective.injOn
  let _ : Nonempty E := ⟨a⟩
  obtain ⟨u, hu⟩ := hUfinite.bddAbove
  apply hE
  refine ⟨max a.1 u.1, ?_⟩
  intro c hcE
  let ce : E := ⟨c, hcE⟩
  by_cases hc : a.1 < ce.1
  · exact le_max_of_le_right (hu hc)
  · exact le_max_of_le_left (le_of_not_gt hc)

private theorem positiveGapWords_lower_cofinal
    {E Δ : Set ℝ} {f : E → ℝ}
    (hΔfin : Δ.Finite) (hΔpos : ∀ d ∈ Δ, 0 < d)
    (hf : StrictMono f)
    (hwords : ∀ a b : E, a.1 < b.1 → ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
      IsPositiveGapWord Δ (f a) (f b) n word)
    (hE : ¬ BddBelow E) : ¬ BddBelow (Set.range f) := by
  classical
  intro himage
  obtain ⟨a0, ha0, _⟩ := (not_bddBelow_iff.1 hE) 0
  let a : E := ⟨a0, ha0⟩
  obtain ⟨b0, hb0, hba⟩ := (not_bddBelow_iff.1 hE) a0
  let b : E := ⟨b0, hb0⟩
  obtain ⟨n0, word0, hw0⟩ := hwords b a hba
  have hΔne : Δ.Nonempty := by
    let i : Fin n0 := ⟨0, hw0.1⟩
    exact ⟨word0 i.succ - word0 i.castSucc, hw0.2.2.2.2 i⟩
  let F : Finset ℝ := hΔfin.toFinset
  let δ : ℝ := F.min' (by simpa [F] using hΔne)
  have hδmem : δ ∈ Δ := by
    simpa [F, δ] using F.min'_mem (by simpa [F] using hΔne)
  have hδ : 0 < δ := hΔpos δ hδmem
  obtain ⟨M, hM⟩ := himage
  obtain ⟨N, hN⟩ := exists_nat_gt ((f a - M) / δ)
  let _ : Finite ↥Δ := hΔfin
  let Codes := Σ k : Fin N, Fin k.1 → ↥Δ
  let value : Codes → ℝ := fun c ↦ f a - ∑ i, (c.2 i).1
  have hvalues : (Set.range value).Finite := Set.finite_range value
  let U : Set E := {b | b.1 < a.1}
  have hfu : f '' U ⊆ Set.range value := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨n, word, hw⟩ := hwords c a hc
    have hlower : (n : ℝ) * δ ≤ f a - f c := by
      rw [← positiveGapWord_telescope hw]
      simpa [nsmul_eq_mul, mul_comm] using
        (Finset.card_nsmul_le_sum Finset.univ
          (fun i : Fin n ↦ word i.succ - word i.castSucc) δ (by
            intro i _
            exact F.min'_le _ (by simpa [F] using hw.2.2.2.2 i)))
    have hMfc : M ≤ f c := hM ⟨c, rfl⟩
    have hnN : n < N := by
      have hMN : f a - M < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
      have hnreal : (n : ℝ) < N := by nlinarith
      exact_mod_cast hnreal
    let code : Codes := ⟨⟨n, hnN⟩,
      fun i ↦ ⟨word i.succ - word i.castSucc, hw.2.2.2.2 i⟩⟩
    refine ⟨code, ?_⟩
    simp only [value, code]
    linarith [positiveGapWord_telescope hw]
  have hUfinite : U.Finite := by
    apply Set.Finite.of_finite_image (hvalues.subset hfu)
    exact hf.injective.injOn
  let _ : Nonempty E := ⟨a⟩
  obtain ⟨u, hu⟩ := hUfinite.bddBelow
  apply hE
  refine ⟨min a.1 u.1, ?_⟩
  intro c hcE
  let ce : E := ⟨c, hcE⟩
  by_cases hc : ce.1 < a.1
  · exact min_le_of_right_le (hu hc)
  · exact min_le_of_left_le (le_of_not_gt hc)

private theorem positiveGapWords_cofinal :
    ∀ {E Δ : Set ℝ} {f : E → ℝ},
    Δ.Finite → (∀ d ∈ Δ, 0 < d) → StrictMono f →
    (∀ a b : E, a.1 < b.1 → ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
      IsPositiveGapWord Δ (f a) (f b) n word) →
    (¬ BddAbove E → ¬ BddAbove (Set.range f)) ∧
      (¬ BddBelow E → ¬ BddBelow (Set.range f)) := by
  intro E Δ f hΔfin hΔpos hf hwords
  exact ⟨positiveGapWords_upper_cofinal hΔfin hΔpos hf hwords,
    positiveGapWords_lower_cofinal hΔfin hΔpos hf hwords⟩

private theorem horizontalFilledChain_coordinateLift
    {C : ApproximationContext.{u}} {q : ℝ} {n : ℕ}
    (hn : 0 < n) (x : Fin (n + 1) → ℝ) (owner : Fin n → ↥C.centres)
    (hchain : IsFilledIndexedSliceChain C.region C.centres
      Axis.horizontal q x owner) :
    ∃ xLift : Fin (n + 1) → C.coordinateSpace,
      ∀ i, (xLift i : ℝ) = x i := by
  have xmem : ∀ i : Fin (n + 1), x i ∈ C.coordinateSpace := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · let j : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
      have hjsucc : j.succ = Fin.last n := by
        ext
        simp [j]
        omega
      obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 j
      rw [← hjsucc, hright]
      exact C.coordinateSpace.add_mem
        (C.vertex_re_mem w hw) (C.centre_re_mem _ (owner j).2)
    · obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 j
      rw [hleft]
      exact C.coordinateSpace.add_mem
        (C.vertex_re_mem v hv) (C.centre_re_mem _ (owner j).2)
  exact ⟨fun i ↦ ⟨x i, xmem i⟩, fun _ ↦ rfl⟩

private theorem firstStage_slice_exhaustion :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ), ∀ᵐ q : ℝ ∂volume,
        ∀ᵐ p : ℝ ∂volume, ∃ t : ↥C.centres,
          (p : ℂ) + (q : ℂ) * Complex.I ∈
            mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier := by
  intro C φ D hT
  filter_upwards
    [controlledSourceEndpointLift hT Axis.horizontal,
      genericSliceEndpointSet_unbounded C.region C.centres hT Axis.horizontal,
      genericSliceChain_betweenEndpoints C.region C.centres hT Axis.horizontal,
      firstSliceChain_transport D hT] with q hlift hunbounded hbetween htransport
  obtain ⟨lift, hliftcoe⟩ := hlift
  let E := sliceEndpointSet C.region C.centres Axis.horizontal q
  let f : ↥E → ℝ := fun a ↦ mapScalar φ (lift a)
  let P : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter
    (fun vw ↦ vw.1.1.re < vw.2.1.re)
  let Δf : Finset ℝ := P.image fun vw ↦
    D.firstHomeomorph vw.2.1.re - D.firstHomeomorph vw.1.1.re
  let Δ : Set ℝ := ↑Δf
  have hΔfin : Δ.Finite := Δf.finite_toSet
  have hΔpos : ∀ d ∈ Δ, 0 < d := by
    intro d hd
    obtain ⟨vw, hvwP, rfl⟩ := Finset.mem_image.1 hd
    have hvw := (Finset.mem_filter.1 hvwP).2
    exact sub_pos.2 (D.firstHomeomorph_strictMono hvw)
  have chainData (a b : ↥E) (hab : a.1 < b.1) :
      ∃ (n : ℕ), 0 < n ∧ ∃ (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        x 0 = a.1 ∧ x (Fin.last n) = b.1 ∧
        (∀ i, (xLift i : ℝ) = x i) ∧
        IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner ∧
        IsTransportedIndexedSliceChain D.firstRegion
          (fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2))
          Axis.horizontal q (fun i ↦ mapScalar φ (xLift i)) owner := by
    obtain ⟨n, hn, x, owner, hx0, hxlast, hchain⟩ :=
      hbetween a.1 a.2 b.1 b.2 hab
    obtain ⟨xLift, hxLift⟩ := horizontalFilledChain_coordinateLift hn x owner hchain
    exact ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain,
      htransport x xLift owner hxLift hchain⟩
  have hf : StrictMono f := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain, hmapped⟩ :=
      chainData a b hab
    have h0 : xLift 0 = lift a := by apply Subtype.ext; simp [hxLift, hliftcoe, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxLift, hliftcoe, hxlast]
    have h0last : (0 : Fin (n + 1)) < Fin.last n := by
      change 0 < n
      exact hn
    simpa only [f, h0, hlast] using hmapped.1 h0last
  have hwords : ∀ a b : ↥E, a.1 < b.1 →
      ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
        IsPositiveGapWord Δ (f a) (f b) n word := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain, hmapped⟩ :=
      chainData a b hab
    let word : Fin (n + 1) → ℝ := fun i ↦ mapScalar φ (xLift i)
    refine ⟨n, word, hn, ?_, ?_, hmapped.1, ?_⟩
    · have h0 : xLift 0 = lift a := by apply Subtype.ext; simp [hxLift, hliftcoe, hx0]
      simp [word, f, h0]
    · have hlast : xLift (Fin.last n) = lift b := by
        apply Subtype.ext
        simp [hxLift, hliftcoe, hxlast]
      simp [word, f, hlast]
    · intro i
      obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
      have hvw : v.re < w.re := by simpa [Axis.coord] using hpositive
      have hvF : v ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF : w ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      have hpair : (⟨v, hvF⟩, ⟨w, hwF⟩) ∈ P := by
        simp [P, hvw]
      have hep := firstOwnerMap_chainEndpoint D x xLift owner hxLift hchain i
      apply Finset.mem_image.2
      refine ⟨(⟨v, hvF⟩, ⟨w, hwF⟩), hpair, ?_⟩
      simp only [word]
      rw [← hep.1, ← hep.2]
      simp [firstOwnerMap, hleft, hright, Axis.coord]
  have hcofinal := positiveGapWords_cofinal hΔfin hΔpos hf hwords
  have hfends : ¬ BddAbove (Set.range f) ∧ ¬ BddBelow (Set.range f) :=
    ⟨hcofinal.1 hunbounded.1, hcofinal.2 hunbounded.2⟩
  have hmapCountable : (Set.range (mapScalar φ)).Countable := by
    apply (Set.countable_range (fun r : ℚ ↦ (r : ℝ))).mono
    rintro y ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  have havoid : ∀ᵐ p : ℝ ∂volume, p ∉ Set.range (mapScalar φ) :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp
      (hmapCountable.measure_zero volume)
  filter_upwards [havoid] with p hp
  obtain ⟨ya, ⟨a, rfl⟩, hay⟩ := (not_bddBelow_iff.1 hfends.2) p
  obtain ⟨yb, ⟨b, rfl⟩, hyb⟩ := (not_bddAbove_iff.1 hfends.1) p
  have hab : a.1 < b.1 := hf.lt_iff_lt.mp (hay.trans hyb)
  obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain, hmapped⟩ :=
    chainData a b hab
  have hleft : mapScalar φ (xLift 0) < p := by
    have h0 : xLift 0 = lift a := by apply Subtype.ext; simp [hxLift, hliftcoe, hx0]
    simpa [f, h0] using hay
  have hright : p < mapScalar φ (xLift (Fin.last n)) := by
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxLift, hliftcoe, hxlast]
    simpa [f, hlast] using hyb
  have hpne : ∀ k, p ≠ mapScalar φ (xLift k) := by
    intro k hk
    exact hp ⟨xLift k, hk.symm⟩
  obtain ⟨i, hi⟩ := strictMono_exists_gap (fun k ↦ mapScalar φ (xLift k))
    hmapped.1 hleft hright hpne
  exact ⟨owner i, hmapped.2 i ⟨by simp, by simpa using hi⟩⟩

theorem firstCoordinateDeformation_tilesOn :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ), ∃ T₁ : ↥C.centres ↪ Tiling.Plane,
      (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn D.firstRegion (deformedCenterCarrier T₁) univ :=
  firstCoordinateDeformation_tilesOn_of_exhaustion
    (firstStage_slice_exhaustion)

private theorem secondStageTransportData_exists :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      Nonempty (SecondStageTransportData C φ D) :=
  secondStageTransportData_exists_of_first
    (firstCoordinateDeformation_tilesOn)

private theorem firstRegionVerticalEndpointLift :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume,
        ∃ lift : ↥(sliceEndpointSet D.firstRegion
            (Set.range (fun t : ↥C.centres =>
              mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q) →
            C.coordinateSpace,
          ∀ x, (lift x : ℝ) = x.1 := by
  intro C φ D hT P
  exact firstRegionVerticalEndpointLift_of_filledSliceChains D hT P
    (firstRegion_vertices_image D)

private theorem secondStageSourceChain_betweenEndpoints :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (_P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume,
        ∀ (a : ℝ), a ∈ sliceEndpointSet D.firstRegion
          (Set.range (fun t : ↥C.centres =>
            mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q →
        ∀ (b : ℝ), b ∈ sliceEndpointSet D.firstRegion
          (Set.range (fun t : ↥C.centres =>
            mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q →
        a < b →
        ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
          (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
          x 0 = a ∧ x (Fin.last n) = b ∧ (∀ i, (xLift i : ℝ) = x i) ∧
            IsSecondStageSourceChain C φ D q x owner := by
  intro C φ D hT P
  let A : Set Tiling.Plane := Set.range fun t : ↥C.centres =>
    mapFirstPoint φ (C.centrePoint t.1 t.2)
  filter_upwards [genericSliceChain_betweenEndpoints D.firstRegion A P.firstTiles Axis.vertical]
      with q hchain
  intro a ha b hb hab
  obtain ⟨n, hn, x, ownerA, hx0, hxlast, hx⟩ := hchain a ha b hb hab
  let owner : Fin n → ↥C.centres := fun i => Classical.choose (ownerA i).2
  have howner (i : Fin n) : (ownerA i : Tiling.Plane) =
      mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) :=
    (Classical.choose_spec (ownerA i).2).symm
  have himage := firstRegion_vertices_image D
  have sourceVertex (v : Tiling.Plane) (hv : v ∈ D.firstRegion.vertices) :
      ∃ v₀ ∈ C.region.vertices, D.firstPlanarHomeomorph v₀ = v := by
    rw [himage] at hv
    simpa only [Set.mem_image] using hv
  have endpoint_mem (i : Fin (n + 1)) : x i ∈ C.coordinateSpace := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · let j : Fin n := ⟨n - 1, by omega⟩
      obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 j
      obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
      have hi : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (mapFirstPoint φ (C.centrePoint (owner j).1
          (owner j).2)).im = (owner j : Tiling.Plane).im := by
        simp [mapFirstPoint, ApproximationContext.centrePoint]
      rw [show Fin.last n = j.succ by
        apply Fin.ext
        simp [j, Nat.sub_add_cancel hn], hright, ← hwmap, howner, Axis.coord,
        Complex.add_im, hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem w₀ hw₀)
        (C.centre_im_mem _ (owner j).2)
    · obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 j
      obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
      have hi : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (mapFirstPoint φ (C.centrePoint (owner j).1 (owner j).2)).im =
          (owner j : Tiling.Plane).im := by
        simp [mapFirstPoint, ApproximationContext.centrePoint]
      rw [hleft, ← hvmap, howner, Axis.coord, Complex.add_im, hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₀ hv₀)
        (C.centre_im_mem _ (owner j).2)
  let xLift : Fin (n + 1) → C.coordinateSpace := fun i => ⟨x i, endpoint_mem i⟩
  refine ⟨n, hn, x, xLift, owner, hx0, hxlast, fun _ => rfl, hx.1, ?_⟩
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 i
  obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
  obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
  have hvim : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hwim : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have htim : (mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2)).im =
      (owner i : Tiling.Plane).im := by
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  refine ⟨v₀, w₀, hv₀, hw₀, ?_, ?_, ?_, ?_⟩
  · simpa [Axis.coord, ← hvmap, howner i, Complex.add_im, hvim, htim] using hleft
  · simpa [Axis.coord, ← hwmap, howner i, Complex.add_im, hwim, htim] using hright
  · simpa [Axis.coord, ← hvmap, ← hwmap, Complex.sub_im, hvim, hwim] using hpos
  · simpa [howner i] using hins


private theorem secondStageSourceChain_exists :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (_P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume, ∀ a b : ℝ, a < b →
        ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
          (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
          (∀ i, (xLift i : ℝ) = x i) ∧ x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
            IsSecondStageSourceChain C φ D q x owner := by
  intro C φ D hT P
  let A : Set Tiling.Plane := Set.range fun t : ↥C.centres =>
    mapFirstPoint φ (C.centrePoint t.1 t.2)
  filter_upwards [genericIndexedSliceChain D.firstRegion A P.firstTiles Axis.vertical]
      with q hchain
  intro a b hab
  obtain ⟨n, hn, x, ownerA, hxa, hbx, hx⟩ := hchain a b hab
  let owner : Fin n → ↥C.centres := fun i => Classical.choose (ownerA i).2
  have howner (i : Fin n) : (ownerA i : Tiling.Plane) =
      mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) :=
    (Classical.choose_spec (ownerA i).2).symm
  have himage := firstRegion_vertices_image D
  have sourceVertex (v : Tiling.Plane) (hv : v ∈ D.firstRegion.vertices) :
      ∃ v₀ ∈ C.region.vertices, D.firstPlanarHomeomorph v₀ = v := by
    rw [himage] at hv
    simpa only [Set.mem_image] using hv
  have endpoint_mem (i : Fin (n + 1)) : x i ∈ C.coordinateSpace := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · let j : Fin n := ⟨n - 1, by omega⟩
      obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 j
      obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
      have hi : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (mapFirstPoint φ (C.centrePoint (owner j).1
          (owner j).2)).im = (owner j : Tiling.Plane).im := by
        simp [mapFirstPoint, ApproximationContext.centrePoint]
      rw [show Fin.last n = j.succ by
        apply Fin.ext
        simp [j, Nat.sub_add_cancel hn], hright, ← hwmap, howner, Axis.coord,
        Complex.add_im, hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem w₀ hw₀)
        (C.centre_im_mem _ (owner j).2)
    · obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 j
      obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
      have hi : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (mapFirstPoint φ (C.centrePoint (owner j).1 (owner j).2)).im =
          (owner j : Tiling.Plane).im := by
        simp [mapFirstPoint, ApproximationContext.centrePoint]
      rw [hleft, ← hvmap, howner, Axis.coord, Complex.add_im, hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₀ hv₀)
        (C.centre_im_mem _ (owner j).2)
  let xLift : Fin (n + 1) → C.coordinateSpace := fun i => ⟨x i, endpoint_mem i⟩
  refine ⟨n, hn, x, xLift, owner, fun _ => rfl, hxa, hbx, hx.1, ?_⟩
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpos, hins⟩ := hx.2 i
  obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
  obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
  have hvim : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have hwim : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
    rw [D.firstPlanarHomeomorph_apply]
    simp
  have htim : (mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2)).im =
      (owner i : Tiling.Plane).im := by
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  refine ⟨v₀, w₀, hv₀, hw₀, ?_, ?_, ?_, ?_⟩
  · simpa [Axis.coord, ← hvmap, howner i, Complex.add_im, hvim, htim] using hleft
  · simpa [Axis.coord, ← hwmap, howner i, Complex.add_im, hwim, htim] using hright
  · simpa [Axis.coord, ← hvmap, ← hwmap, Complex.sub_im, hvim, hwim] using hpos
  · simpa [howner i] using hins

private theorem mapScalar_endpoint_eq_secondHomeomorph_add_center
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).im) :
    mapScalar φ xLift =
      D.secondHomeomorph v.im +
        (mapPoint φ (C.centrePoint t.1 t.2)).im := by
  let vi : C.coordinateSpace := ⟨v.im, C.vertex_im_mem v hv⟩
  let ti : C.coordinateSpace := ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
  have hxl : xLift = vi + ti := by
    apply Subtype.ext
    simp [vi, ti, hLift, hx]
  have hvertex := congrArg Complex.im (D.vertex_agreement v hv)
  have hvertex' : mapScalar φ vi = D.secondHomeomorph v.im := by
    simpa [vi, mapPoint, ApproximationContext.vertexPoint,
      D.planarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((φ vi : ℚ) : ℝ) = mapScalar φ vi by rfl, hvertex']
  congr 1
  simp [ti, mapPoint, mapScalar, ApproximationContext.centrePoint]

private theorem secondSliceChain_mapped_strictMono
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q : ℝ} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) (hLift : ∀ i, (xLift i : ℝ) = x i)
    (hchain : IsSecondStageSourceChain C φ D q x owner) :
    StrictMono (fun i => mapScalar φ (xLift i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  have hvw : v.im < w.im := sub_pos.mp hpositive
  rw [mapScalar_endpoint_eq_secondHomeomorph_add_center D v hv (owner i)
      (x i.castSucc) (xLift i.castSucc) (hLift i.castSucc) hleft,
    mapScalar_endpoint_eq_secondHomeomorph_add_center D w hw (owner i)
      (x i.succ) (xLift i.succ) (hLift i.succ) hright]
  simpa [add_comm] using
    (add_lt_add_right (D.secondHomeomorph_strictMono hvw)
      (mapPoint φ (C.centrePoint (owner i).1 (owner i).2)).im)

private theorem secondSliceGap_transport
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q x₀ x₁ : ℝ}
    (xLift₀ xLift₁ : C.coordinateSpace) (t : ↥C.centres)
    (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hlift₀ : (xLift₀ : ℝ) = x₀) (hlift₁ : (xLift₁ : ℝ) = x₁)
    (hleft : x₀ = (v + (t : Tiling.Plane)).im)
    (hright : x₁ = (w + (t : Tiling.Plane)).im)
    (hinside : axisInterval Axis.vertical q x₀ x₁ ⊆
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier) :
    axisInterval Axis.vertical q (mapScalar φ xLift₀) (mapScalar φ xLift₁) ⊆
      mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier := by
  intro z hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, secondStage_region_image D]
  let c₁ := mapFirstPoint φ (C.centrePoint t.1 t.2)
  let c := mapPoint φ (C.centrePoint t.1 t.2)
  let r : ℝ := D.secondHomeomorph.symm (z.im - c.im)
  let p : Tiling.Plane := ((q - c₁.re : ℝ) : ℂ) + (r : ℂ) * Complex.I
  have hend₀ := mapScalar_endpoint_eq_secondHomeomorph_add_center
    D v hv t x₀ xLift₀ hlift₀ hleft
  have hend₁ := mapScalar_endpoint_eq_secondHomeomorph_add_center
    D w hw t x₁ xLift₁ hlift₁ hright
  have hzim : z.im ∈ Ioo (mapScalar φ xLift₀) (mapScalar φ xLift₁) := hz.2
  have hvr : v.im < r := by
    apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzim.1]
  have hrw : r < w.im := by
    apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzim.2]
  have hp : p ∈ D.firstRegion.openCarrier := by
    have hs : c₁ + p ∈ axisInterval Axis.vertical q x₀ x₁ := by
      constructor
      · simp [p, c₁]
      · rw [hleft, hright]
        simp only [p, c₁, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_im, zero_add, mul_one]
        have hcim : c₁.im = (t : Tiling.Plane).im := by
          simp [c₁, mapFirstPoint, ApproximationContext.centrePoint]
        rw [hcim]
        simp only [Complex.ofReal_re, Complex.I_re, mul_zero, add_zero]
        constructor <;> linarith
    have := hinside hs
    simpa [c₁, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_assoc] using this
  refine ⟨p, hp, ?_⟩
  rw [secondStagePlanarHomeomorph_apply]
  apply Complex.ext
  · have hzq : z.re = q := hz.1
    simp [p, c₁, mapFirstPoint, mapPoint, mapScalar,
      ApproximationContext.centrePoint, hzq]
    ring
  · simp [p, r, c]
    ring

private theorem secondStageSliceChain_transport :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (_P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume, ∀ {n : ℕ} (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) →
        IsSecondStageSourceChain C φ D q x owner →
        IsTransportedIndexedSliceChain D.deformedRegion
          (fun t : ↥C.centres => mapPoint φ (C.centrePoint t.1 t.2))
          Axis.vertical q (fun i => mapScalar φ (xLift i)) owner := by
  intro C φ D hT P
  filter_upwards [] with q
  intro n x xLift owner hLift hchain
  refine ⟨secondSliceChain_mapped_strictMono D x xLift owner hLift hchain, ?_⟩
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  exact secondSliceGap_transport D (xLift i.castSucc) (xLift i.succ) (owner i)
    v w hv hw (hLift i.castSucc) (hLift i.succ) hleft hright hinside

private theorem secondStage_mappedEndpoints_order_cofinal :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume,
        ∃ lift : ↥(sliceEndpointSet D.firstRegion
            (Set.range (fun t : ↥C.centres =>
              mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q) →
            C.coordinateSpace,
          (∀ a, (lift a : ℝ) = a.1) ∧
          StrictMono (fun a => mapScalar φ (lift a)) ∧
          ¬ BddAbove (Set.range (fun a => mapScalar φ (lift a))) ∧
          ¬ BddBelow (Set.range (fun a => mapScalar φ (lift a))) := by
  intro C φ D hT P
  let A : Set Tiling.Plane := Set.range fun t : ↥C.centres =>
    mapFirstPoint φ (C.centrePoint t.1 t.2)
  filter_upwards
      [firstRegionVerticalEndpointLift D hT P,
        genericSliceEndpointSet_unbounded D.firstRegion A P.firstTiles Axis.vertical,
        secondStageSourceChain_betweenEndpoints D hT P] with q hlift hunbounded hbetween
  obtain ⟨lift, hliftcoe⟩ := hlift
  let E := sliceEndpointSet D.firstRegion A Axis.vertical q
  let f : ↥E → ℝ := fun a => mapScalar φ (lift a)
  let pairs : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter fun vw => vw.1.1.im < vw.2.1.im
  let Δf : Finset ℝ := pairs.image fun vw =>
    D.secondHomeomorph vw.2.1.im - D.secondHomeomorph vw.1.1.im
  let Δ : Set ℝ := ↑Δf
  have hΔfin : Δ.Finite := Δf.finite_toSet
  have hΔpos : ∀ d ∈ Δ, 0 < d := by
    intro d hd
    obtain ⟨vw, hvw, rfl⟩ := Finset.mem_image.mp hd
    exact sub_pos.mpr (D.secondHomeomorph_strictMono (Finset.mem_filter.mp hvw).2)
  have chainData (a b : ↥E) (hab : a.1 < b.1) :
      ∃ (n : ℕ), 0 < n ∧ ∃ (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        x 0 = a.1 ∧ x (Fin.last n) = b.1 ∧
        (∀ i, (xLift i : ℝ) = x i) ∧
        IsSecondStageSourceChain C φ D q x owner := by
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxlift, hsource⟩ :=
      hbetween a.1 a.2 b.1 b.2 hab
    exact ⟨n, hn, x, xLift, owner, hx0, hxlast, hxlift, hsource⟩
  have hf : StrictMono f := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxlift, hsource⟩ :=
      chainData a b hab
    have h0 : xLift 0 = lift a := by
      apply Subtype.ext
      simp [hxlift, hliftcoe, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxlift, hliftcoe, hxlast]
    have hindex : (0 : Fin (n + 1)) < Fin.last n := hn
    simpa only [f, h0, hlast] using
      (secondSliceChain_mapped_strictMono D x xLift owner hxlift hsource hindex)
  have hwords : ∀ a b : ↥E, a.1 < b.1 →
      ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
        IsPositiveGapWord Δ (f a) (f b) n word := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxlift, hsource⟩ :=
      chainData a b hab
    let word : Fin (n + 1) → ℝ := fun i => mapScalar φ (xLift i)
    have hmono := secondSliceChain_mapped_strictMono D x xLift owner hxlift hsource
    refine ⟨n, word, hn, ?_, ?_, hmono, ?_⟩
    · have h0 : xLift 0 = lift a := by
        apply Subtype.ext
        simp [hxlift, hliftcoe, hx0]
      simp [word, f, h0]
    · have hlast : xLift (Fin.last n) = lift b := by
        apply Subtype.ext
        simp [hxlift, hliftcoe, hxlast]
      simp [word, f, hlast]
    · intro i
      obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hsource.2 i
      have hvw : v.im < w.im := sub_pos.mp hpositive
      have hvF : v ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF : w ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      have hpair : (⟨v, hvF⟩, ⟨w, hwF⟩) ∈ pairs := by
        simp [pairs, hvw]
      apply Finset.mem_image.mpr
      refine ⟨(⟨v, hvF⟩, ⟨w, hwF⟩), hpair, ?_⟩
      simp only [word]
      rw [mapScalar_endpoint_eq_secondHomeomorph_add_center D v hv (owner i)
          (x i.castSucc) (xLift i.castSucc) (hxlift i.castSucc) hleft,
        mapScalar_endpoint_eq_secondHomeomorph_add_center D w hw (owner i)
          (x i.succ) (xLift i.succ) (hxlift i.succ) hright]
      ring
  have hcofinal := positiveGapWords_cofinal hΔfin hΔpos hf hwords
  exact ⟨lift, hliftcoe, hf, hcofinal.1 hunbounded.1, hcofinal.2 hunbounded.2⟩

private theorem secondStage_slice_exhaustion :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (P : SecondStageTransportData C φ D),
      ∀ᵐ q : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, ∃ t : ↥C.centres,
        (q : ℂ) + (y : ℂ) * Complex.I ∈
          mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier := by
  intro C φ D hT P
  filter_upwards
      [secondStage_mappedEndpoints_order_cofinal D hT P,
        secondStageSourceChain_betweenEndpoints D hT P,
        secondStageSliceChain_transport D hT P] with q hends hbetween htransport
  obtain ⟨lift, hlift, hmono, hunboundedAbove, hunboundedBelow⟩ := hends
  let E := sliceEndpointSet D.firstRegion
    (Set.range (fun t : ↥C.centres =>
      mapFirstPoint φ (C.centrePoint t.1 t.2))) Axis.vertical q
  let f : ↥E → ℝ := fun a => mapScalar φ (lift a)
  have hmapCountable : (Set.range (mapScalar φ)).Countable := by
    apply (Set.countable_range (fun r : ℚ => (r : ℝ))).mono
    rintro z ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  filter_upwards [hmapCountable.ae_notMem volume] with y hy
  obtain ⟨_, ⟨a, rfl⟩, hay⟩ := not_bddBelow_iff.mp hunboundedBelow y
  obtain ⟨_, ⟨b, rfl⟩, hyb⟩ := not_bddAbove_iff.mp hunboundedAbove y
  have hab : a.1 < b.1 := hmono.lt_iff_lt.mp (hay.trans hyb)
  obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxlift, hsource⟩ :=
    hbetween a.1 a.2 b.1 b.2 hab
  have htarget := htransport x xLift owner hxlift hsource
  have hleft : mapScalar φ (xLift 0) < y := by
    have h0 : xLift 0 = lift a := by
      apply Subtype.ext
      simp [hxlift, hlift, hx0]
    simpa [f, h0] using hay
  have hright : y < mapScalar φ (xLift (Fin.last n)) := by
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxlift, hlift, hxlast]
    simpa [f, hlast] using hyb
  have hyne : ∀ k, y ≠ mapScalar φ (xLift k) := by
    intro k heq
    exact hy ⟨xLift k, heq.symm⟩
  obtain ⟨i, hi⟩ := strictMono_exists_gap
    (fun k => mapScalar φ (xLift k)) htarget.1 hleft hright hyne
  refine ⟨owner i, htarget.2 i ?_⟩
  exact ⟨by simp, by simpa using hi⟩

private def secondOwnerMap
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (y : ℝ) : ℝ :=
  D.secondHomeomorph
      (y - (mapFirstPoint φ (C.centrePoint t.1 t.2)).im) +
    (mapPoint φ (C.centrePoint t.1 t.2)).im

private theorem secondOwnerMap_strictMono
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) :
    StrictMono (secondOwnerMap D t) := by
  intro a b hab
  dsimp [secondOwnerMap]
  simpa [add_comm] using
    add_lt_add_right (D.secondHomeomorph_strictMono (sub_lt_sub_right hab _))
      (mapPoint φ (C.centrePoint t.1 t.2)).im

private theorem secondOwnerMap_chainEndpoint
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q : ℝ} {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) (hLift : ∀ i, (xLift i : ℝ) = x i)
    (hchain : IsSecondStageSourceChain C φ D q x owner) (i : Fin n) :
    secondOwnerMap D (owner i) (x i.castSucc) = mapScalar φ (xLift i.castSucc) ∧
      secondOwnerMap D (owner i) (x i.succ) = mapScalar φ (xLift i.succ) := by
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  rw [mapScalar_endpoint_eq_secondHomeomorph_add_center D v hv (owner i)
      (x i.castSucc) (xLift i.castSucc) (hLift i.castSucc) hleft,
    mapScalar_endpoint_eq_secondHomeomorph_add_center D w hw (owner i)
      (x i.succ) (xLift i.succ) (hLift i.succ) hright]
  constructor <;>
    simp [secondOwnerMap, hleft, hright, mapFirstPoint,
      ApproximationContext.centrePoint]

private def secondSourcePoint
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres)
    (z : Tiling.Plane) : Tiling.Plane :=
  z.re +
    (D.secondHomeomorph.symm
      (z.im - (mapPoint φ (C.centrePoint t.1 t.2)).im) +
      (mapFirstPoint φ (C.centrePoint t.1 t.2)).im) * Complex.I

private theorem secondOwnerMap_secondSourcePoint_im
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    secondOwnerMap D t (secondSourcePoint D t z).im = z.im := by
  simp [secondOwnerMap, secondSourcePoint]

private theorem secondSourcePoint_re
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    (secondSourcePoint D t z).re = z.re := by
  simp [secondSourcePoint]

private theorem secondSourcePoint_mem
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane)
    (hz : z ∈ mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
      D.deformedRegion.openCarrier) :
    secondSourcePoint D t z ∈
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, secondStage_region_image D] at hz
  obtain ⟨p, hp, hpz⟩ := hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hpre : secondStagePlanarHomeomorph D
      (-mapFirstPoint φ (C.centrePoint t.1 t.2) + secondSourcePoint D t z) =
      -mapPoint φ (C.centrePoint t.1 t.2) + z := by
    rw [secondStagePlanarHomeomorph_apply]
    apply Complex.ext
    · simp [secondSourcePoint, mapFirstPoint, mapPoint,
        ApproximationContext.centrePoint]
    · simp [secondSourcePoint, mapFirstPoint, mapPoint,
        ApproximationContext.centrePoint]
      ring
  have heq := (secondStagePlanarHomeomorph D).injective (hpre.trans hpz.symm)
  change -mapFirstPoint φ (C.centrePoint t.1 t.2) +
      secondSourcePoint D t z ∈ D.firstRegion.openCarrier
  rw [heq]
  exact hp

private theorem secondChain_owner_eq_of_mem
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (P : SecondStageTransportData C φ D)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥C.centres}
    {z : Tiling.Plane}
    (hchain : IsSecondStageSourceChain C φ D q x owner)
    (i : Fin n) (t : ↥C.centres)
    (hzI : secondSourcePoint D t z ∈ axisInterval Axis.vertical q
      (x i.castSucc) (x i.succ))
    (hzT : secondSourcePoint D t z ∈
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ D.firstRegion.openCarrier) :
    owner i = t := by
  apply Subtype.ext
  by_contra hne
  have hp := (isPacking_iff_openCarrier_disjoint D.firstRegion _).mp P.firstTiles.2.1
  have hcentrene :
      mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) ≠
        mapFirstPoint φ (C.centrePoint t.1 t.2) := by
    intro heq
    exact hne (congrArg Subtype.val (P.firstInjective heq))
  have hd := hp
    (show mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) ∈
      Set.range (fun u : ↥C.centres => mapFirstPoint φ (C.centrePoint u.1 u.2)) from
      ⟨owner i, rfl⟩)
    (show mapFirstPoint φ (C.centrePoint t.1 t.2) ∈
      Set.range (fun u : ↥C.centres => mapFirstPoint φ (C.centrePoint u.1 u.2)) from
      ⟨t, rfl⟩) hcentrene
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  exact Set.disjoint_left.mp hd (hinside hzI) hzT

private theorem secondStage_slice_exhaustion_and_overlap :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (P : SecondStageTransportData C φ D),
      (∀ᵐ q : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume, ∃ t : ↥C.centres,
        (q : ℂ) + (y : ℂ) * Complex.I ∈
          mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier) ∧
      ∀ s t : ↥C.centres,
        ((mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier) ∩
          (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier)).Nonempty →
          s = t := by
  intro C φ D hT P
  refine ⟨secondStage_slice_exhaustion D hT P, ?_⟩
  intro s t hoverlap
  obtain ⟨z, hzs, hzt⟩ := hoverlap
  let O : Set Tiling.Plane :=
    (mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier) ∩
      (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier)
  have hOopen : IsOpen O :=
    (D.deformedRegion.openCarrier_regularOpen.1.vadd _).inter
      (D.deformedRegion.openCarrier_regularOpen.1.vadd _)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOopen z ⟨hzs, hzt⟩
  have hgood : ∀ᵐ q : ℝ ∂volume,
      (∀ a b : ℝ, a < b → ∃ (n : ℕ) (_hn : 0 < n)
        (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) ∧ x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
          IsSecondStageSourceChain C φ D q x owner) ∧
      (∀ {n : ℕ} (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) →
        IsSecondStageSourceChain C φ D q x owner →
        IsTransportedIndexedSliceChain D.deformedRegion
          (fun u : ↥C.centres ↦ mapPoint φ (C.centrePoint u.1 u.2))
          Axis.vertical q (fun i ↦ mapScalar φ (xLift i)) owner) := by
    filter_upwards [secondStageSourceChain_exists D hT P,
      secondStageSliceChain_transport D hT P] with q hc ht
    exact ⟨hc, ht⟩
  obtain ⟨q, hqI, hchainAt, htransportAt⟩ :=
    exists_mem_Ioo_of_ae_real (by linarith [hε] : z.re - ε / 4 < z.re + ε / 4) hgood
  let sl := secondSourcePoint D s (Complex.mk q (z.im - ε / 4))
  let tl := secondSourcePoint D t (Complex.mk q (z.im - ε / 4))
  let sh := secondSourcePoint D s (Complex.mk q (z.im + ε / 4))
  let th := secondSourcePoint D t (Complex.mk q (z.im + ε / 4))
  let A := min sl.im tl.im - 1
  let B := max sh.im th.im + 1
  have hslope : sl.im < sh.im := by
    apply (secondOwnerMap_strictMono D s).lt_iff_lt.mp
    rw [secondOwnerMap_secondSourcePoint_im, secondOwnerMap_secondSourcePoint_im]
    linarith [hε]
  have hAB : A < B := by
    dsimp [A, B]
    linarith [min_le_left sl.im tl.im,
      hslope.le.trans (le_max_left sh.im th.im)]
  obtain ⟨n, hn, x, xLift, owner, hLift, hxA, hBx, hchain⟩ := hchainAt A B hAB
  let forbidden : Finset ℝ :=
    (Finset.univ.image (fun k : Fin (n + 1) ↦ secondOwnerMap D s (x k))) ∪
      Finset.univ.image (fun k : Fin (n + 1) ↦ secondOwnerMap D t (x k))
  obtain ⟨p, hpI, hpavoid⟩ := exists_mem_Ioo_avoiding_finset
    (by linarith [hε] : z.im - ε / 4 < z.im + ε / 4) forbidden
  let w : Tiling.Plane := Complex.mk q p
  have hwball : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, dist_eq_norm, show w - z =
      ((q - z.re : ℝ) : ℂ) + ((p - z.im : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp [w]]
    calc
      ‖((q - z.re : ℝ) : ℂ) + ((p - z.im : ℝ) : ℂ) * Complex.I‖
          ≤ ‖((q - z.re : ℝ) : ℂ)‖ + ‖((p - z.im : ℝ) : ℂ) * Complex.I‖ :=
            norm_add_le _ _
      _ = |q - z.re| + |p - z.im| := by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul,
          Complex.norm_I, mul_one]
      _ < ε := by
        have hqabs : |q - z.re| < ε / 4 := (abs_lt).2 ⟨by linarith [hqI.1], by linarith [hqI.2]⟩
        have hpabs : |p - z.im| < ε / 4 := (abs_lt).2 ⟨by linarith [hpI.1], by linarith [hpI.2]⟩
        linarith
  have hwo : w ∈ O := hball hwball
  have hws := secondSourcePoint_mem D s w hwo.1
  have hwt := secondSourcePoint_mem D t w hwo.2
  let rs := (secondSourcePoint D s w).im
  let rt := (secondSourcePoint D t w).im
  have hrsA : x 0 < rs := by
    have hsl : sl.im < rs := by
      apply (secondOwnerMap_strictMono D s).lt_iff_lt.mp
      rw [secondOwnerMap_secondSourcePoint_im, secondOwnerMap_secondSourcePoint_im]
      exact hpI.1
    have : A < rs := by dsimp [A]; linarith [min_le_left sl.im tl.im]
    exact lt_of_le_of_lt hxA this
  have hrtA : x 0 < rt := by
    have htl : tl.im < rt := by
      apply (secondOwnerMap_strictMono D t).lt_iff_lt.mp
      rw [secondOwnerMap_secondSourcePoint_im, secondOwnerMap_secondSourcePoint_im]
      exact hpI.1
    have : A < rt := by dsimp [A]; linarith [min_le_right sl.im tl.im]
    exact lt_of_le_of_lt hxA this
  have hrsB : rs < x (Fin.last n) := by
    have hrs : rs < sh.im := by
      apply (secondOwnerMap_strictMono D s).lt_iff_lt.mp
      rw [secondOwnerMap_secondSourcePoint_im, secondOwnerMap_secondSourcePoint_im]
      exact hpI.2
    have : rs < B := by dsimp [B]; linarith [le_max_left sh.im th.im]
    exact lt_of_lt_of_le this hBx
  have hrtB : rt < x (Fin.last n) := by
    have hrt : rt < th.im := by
      apply (secondOwnerMap_strictMono D t).lt_iff_lt.mp
      rw [secondOwnerMap_secondSourcePoint_im, secondOwnerMap_secondSourcePoint_im]
      exact hpI.2
    have : rt < B := by dsimp [B]; linarith [le_max_right sh.im th.im]
    exact lt_of_lt_of_le this hBx
  have hrsne : ∀ k, rs ≠ x k := by
    intro k heq
    apply hpavoid
    apply Finset.mem_union_left
    refine Finset.mem_image.2 ⟨k, Finset.mem_univ _, ?_⟩
    rw [← heq, secondOwnerMap_secondSourcePoint_im]
  have hrtne : ∀ k, rt ≠ x k := by
    intro k heq
    apply hpavoid
    apply Finset.mem_union_right
    refine Finset.mem_image.2 ⟨k, Finset.mem_univ _, ?_⟩
    rw [← heq, secondOwnerMap_secondSourcePoint_im]
  obtain ⟨i, hi⟩ := strictMono_exists_gap x hchain.1 hrsA hrsB hrsne
  obtain ⟨j, hj⟩ := strictMono_exists_gap x hchain.1 hrtA hrtB hrtne
  have hwsi : secondSourcePoint D s w ∈ axisInterval Axis.vertical q
      (x i.castSucc) (x i.succ) := ⟨by simp [secondSourcePoint_re, w], hi⟩
  have hwtj : secondSourcePoint D t w ∈ axisInterval Axis.vertical q
      (x j.castSucc) (x j.succ) := ⟨by simp [secondSourcePoint_re, w], hj⟩
  have hoi := secondChain_owner_eq_of_mem D P hchain i s hwsi hws
  have hoj := secondChain_owner_eq_of_mem D P hchain j t hwtj hwt
  have htrans := htransportAt x xLift owner hLift hchain
  have hepi := secondOwnerMap_chainEndpoint D x xLift owner hLift hchain i
  have hepj := secondOwnerMap_chainEndpoint D x xLift owner hLift hchain j
  have hwi : w ∈ axisInterval Axis.vertical q
      (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ)) := by
    refine ⟨by simp [w], ?_⟩
    rw [← hepi.1, ← hepi.2, hoi]
    constructor <;> rw [← secondOwnerMap_secondSourcePoint_im D s w]
    · exact secondOwnerMap_strictMono D s hi.1
    · exact secondOwnerMap_strictMono D s hi.2
  have hwj : w ∈ axisInterval Axis.vertical q
      (mapScalar φ (xLift j.castSucc)) (mapScalar φ (xLift j.succ)) := by
    refine ⟨by simp [w], ?_⟩
    rw [← hepj.1, ← hepj.2, hoj]
    constructor <;> rw [← secondOwnerMap_secondSourcePoint_im D t w]
    · exact secondOwnerMap_strictMono D t hj.1
    · exact secondOwnerMap_strictMono D t hj.2
  have hij : i = j := strictMono_gap_owner_unique htrans.1 hwi.2 hwj.2
  rw [← hoi, ← hoj, hij]

private theorem fullCenter_formula_injective :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      Injective (fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2)) := by
  intro C φ D hT
  let P := Classical.choice (secondStageTransportData_exists D hT)
  intro s t heq
  apply (secondStage_slice_exhaustion_and_overlap D hT P).2 s t
  obtain ⟨p, hp⟩ := D.deformedRegion.isPolygonal.interior_nonempty
    D.deformedRegion.nonempty
  change mapPoint φ (C.centrePoint s.1 s.2) =
    mapPoint φ (C.centrePoint t.1 t.2) at heq
  refine ⟨mapPoint φ (C.centrePoint s.1 s.2) + p, ⟨p, hp, rfl⟩, ?_⟩
  rw [← heq]
  exact ⟨p, hp, rfl⟩

private theorem secondStage_tilesOn :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (P : SecondStageTransportData C φ D),
      TilesOn D.deformedRegion
        (Set.range (fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2))) univ := by
  intro C φ D hT P
  let center : ↥C.centres → Tiling.Plane := fun t ↦
    mapPoint φ (C.centrePoint t.1 t.2)
  let _ : Countable ↥C.centres := hT.1.to_subtype
  refine ⟨Set.countable_range center, ?_, ?_⟩
  · apply (isPacking_iff_openCarrier_disjoint D.deformedRegion (Set.range center)).2
    intro a ha b hb hab
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    apply Set.disjoint_left.2
    intro z hzs hzt
    apply hab
    congr 1
    exact (secondStage_slice_exhaustion_and_overlap D hT P).2 s t ⟨z, hzs, hzt⟩
  · have hslices := (secondStage_slice_exhaustion_and_overlap D hT P).1
    have hmeas : MeasurableSet {p : ℝ × ℝ | ∃ t : ↥C.centres,
        ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈
          center t +ᵥ D.deformedRegion.openCarrier} := by
      have hopen : IsOpen (openUnion D.deformedRegion (Set.range center)) :=
        isOpen_iUnion fun _ ↦ D.deformedRegion.openCarrier_regularOpen.1.vadd _
      have hcontinuous : Continuous (fun p : ℝ × ℝ ↦
          (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by fun_prop
      have hm := hopen.measurableSet.preimage hcontinuous.measurable
      convert hm using 1
      ext p
      simp only [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, mem_preimage, mem_iUnion]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨⟨center t, ⟨t, rfl⟩⟩, ht⟩
      · rintro ⟨a, ha⟩
        obtain ⟨t, ht⟩ := a.2
        refine ⟨t, ?_⟩
        simpa [← ht] using ha
    have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, ∃ t : ↥C.centres,
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          center t +ᵥ D.deformedRegion.openCarrier :=
      (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).2 hslices
    have hplane := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
    filter_upwards [hplane] with z hz
    simp only [mem_univ, true_iff]
    rcases hz with ⟨t, ht⟩
    refine ⟨⟨center t, ⟨t, rfl⟩⟩, ?_⟩
    change z ∈ center t +ᵥ D.deformedRegion.openCarrier
    rw [show z = (z.re : ℂ) + (z.im : ℂ) * Complex.I by
      apply Complex.ext <;> simp]
    exact ht

/-- Rational coordinate deformation preserves a whole-plane translational tiling. -/
theorem coordinateDeformation_tilesOn :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ), ∃ Tφ : ↥C.centres ↪ Tiling.Plane,
      (∀ t, Tφ t = mapPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn D.deformedRegion (deformedCenterCarrier Tφ) univ := by
  intro C φ D hT
  let Tφ : ↥C.centres ↪ Tiling.Plane :=
    ⟨fun t ↦ mapPoint φ (C.centrePoint t.1 t.2),
      fullCenter_formula_injective D hT⟩
  refine ⟨Tφ, fun _ ↦ rfl, ?_⟩
  simpa [deformedCenterCarrier, Tφ] using
    secondStage_tilesOn D hT (Classical.choice (secondStageTransportData_exists D hT))


private theorem deformedSingletonFamily_locallyFinite :
    ∀ (K : Region) {ι : Type*} (E : ι ↪ Tiling.Plane),
      TilesOn K (deformedCenterCarrier E) univ →
        LocallyFinite (deformedCenterSingletonFamily E) := by
  intro K ι E hTile x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
  have hfinite := (IsPacking.locallyFinite_centres hTile.2.1).1
    (Metric.closedBall x 1) Metric.isBounded_closedBall
  apply (hfinite.preimage Subtype.val_injective.injOn).subset
  rintro t ⟨z, hzt, hzball⟩
  simp only [deformedCenterSingletonFamily, mem_singleton_iff] at hzt
  subst z
  exact ⟨t.2, Metric.mem_closedBall'.2 (Metric.mem_ball'.1 hzball).le⟩

/-- A strict order map preserving both unbounded ends preserves bounded-window finiteness. -/
theorem strictOrderImage_locallyFinite
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hupper : ¬ BddAbove E → ¬ BddAbove (Set.range f))
    (hlower : ¬ BddBelow E → ¬ BddBelow (Set.range f)) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (Set.range f ∩ Q).Finite := by
  classical
  intro Q hQ
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : ℝ)
  have hQR : Q ⊆ Icc (-R) R := by
    simpa [Real.closedBall_eq_Icc] using hR
  obtain ⟨l, hl⟩ : ∃ l : ℝ, ∀ x : E, -R ≤ f x → l ≤ x.1 := by
    by_cases h : BddBelow E
    · exact ⟨sInf E, fun x _ ↦ csInf_le h x.2⟩
    · obtain ⟨_, ⟨a, rfl⟩, ha⟩ := (not_bddBelow_iff.1 (hlower h)) (-R)
      refine ⟨a.1, fun x hxR ↦ ?_⟩
      by_contra hx
      have := hf (lt_of_not_ge hx)
      linarith
  obtain ⟨u, hu⟩ : ∃ u : ℝ, ∀ x : E, f x ≤ R → x.1 ≤ u := by
    by_cases h : BddAbove E
    · exact ⟨sSup E, fun x _ ↦ le_csSup h x.2⟩
    · obtain ⟨_, ⟨b, rfl⟩, hb⟩ := (not_bddAbove_iff.1 (hupper h)) R
      refine ⟨b.1, fun x hxR ↦ ?_⟩
      by_contra hx
      have := hf (lt_of_not_ge hx)
      linarith
  have hfinite : (E ∩ Icc l u).Finite :=
    hlocal (Icc l u) (Metric.isBounded_Icc l u)
  let g : ℝ → ℝ := fun x ↦ if hx : x ∈ E then f ⟨x, hx⟩ else 0
  apply (hfinite.image g).subset
  rintro y ⟨hyRange, hyQ⟩
  obtain ⟨x, hxy⟩ := hyRange
  have hyR := hQR hyQ
  refine ⟨x.1, ⟨x.2, hl x ?_, hu x ?_⟩, ?_⟩
  · simpa [hxy] using hyR.1
  · simpa [hxy] using hyR.2
  · simp [g, x.2, hxy]

theorem exists_greatest_mem_le_of_boundedWindowFinite
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x : ℝ} (hne : ∃ a ∈ E, a ≤ x) :
    ∃ a ∈ E, a ≤ x ∧ ∀ b ∈ E, b ≤ x → b ≤ a := by
  classical
  obtain ⟨c, hcE, hcx⟩ := hne
  let F : Finset ℝ := (hlocal (Icc c x) (Metric.isBounded_Icc c x)).toFinset
  have hcF : c ∈ F := by simp [F, hcE, hcx]
  let a := F.max' ⟨c, hcF⟩
  have haF : a ∈ F := Finset.max'_mem F ⟨c, hcF⟩
  have haData : a ∈ E ∧ c ≤ a ∧ a ≤ x := by simpa [F] using haF
  refine ⟨a, haData.1, haData.2.2, ?_⟩
  intro b hbE hbx
  by_cases hcb : c ≤ b
  · exact Finset.le_max' F b (by simp [F, hbE, hcb, hbx])
  · exact (lt_of_not_ge hcb).le.trans haData.2.1

theorem exists_least_mem_ge_of_boundedWindowFinite
    {E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x : ℝ} (hne : ∃ b ∈ E, x ≤ b) :
    ∃ b ∈ E, x ≤ b ∧ ∀ a ∈ E, x ≤ a → b ≤ a := by
  classical
  obtain ⟨c, hcE, hxc⟩ := hne
  let F : Finset ℝ := (hlocal (Icc x c) (Metric.isBounded_Icc x c)).toFinset
  have hcF : c ∈ F := by simp [F, hcE, hxc]
  let b := F.min' ⟨c, hcF⟩
  have hbF : b ∈ F := Finset.min'_mem F ⟨c, hcF⟩
  have hbData : b ∈ E ∧ x ≤ b ∧ b ≤ c := by simpa [F] using hbF
  refine ⟨b, hbData.1, hbData.2.1, ?_⟩
  intro a haE hxa
  by_cases hac : a ≤ c
  · exact Finset.min'_le F a (by simp [F, haE, hxa, hac])
  · exact hbData.2.2.trans (lt_of_not_ge hac).le

private theorem no_mem_Ioo_greatest_le_least_ge
    {E : Set ℝ} {x a b : ℝ}
    (ha : a ∈ E ∧ a ≤ x ∧ ∀ c ∈ E, c ≤ x → c ≤ a)
    (hb : b ∈ E ∧ x ≤ b ∧ ∀ c ∈ E, x ≤ c → b ≤ c) :
    E ∩ Ioo a b = ∅ := by
  ext c
  simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
  rintro ⟨hcE, hac, hcb⟩
  rcases le_total c x with hcx | hxc
  · exact (not_le_of_gt hac) (ha.2.2 c hcE hcx)
  · exact (not_le_of_gt hcb) (hb.2.2 c hcE hxc)

private noncomputable def locallyFinitePred (E : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (h : ∃ a ∈ E, a ≤ x) : ℝ :=
  Classical.choose (exists_greatest_mem_le_of_boundedWindowFinite hlocal h)

private theorem locallyFinitePred_spec (E : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (h : ∃ a ∈ E, a ≤ x) :
    locallyFinitePred E hlocal x h ∈ E ∧ locallyFinitePred E hlocal x h ≤ x ∧
      ∀ a ∈ E, a ≤ x → a ≤ locallyFinitePred E hlocal x h :=
  Classical.choose_spec (exists_greatest_mem_le_of_boundedWindowFinite hlocal h)

private noncomputable def locallyFiniteSucc (E : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (h : ∃ b ∈ E, x ≤ b) : ℝ :=
  Classical.choose (exists_least_mem_ge_of_boundedWindowFinite hlocal h)

private theorem locallyFiniteSucc_spec (E : Set ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (h : ∃ b ∈ E, x ≤ b) :
    locallyFiniteSucc E hlocal x h ∈ E ∧ x ≤ locallyFiniteSucc E hlocal x h ∧
      ∀ b ∈ E, x ≤ b → locallyFiniteSucc E hlocal x h ≤ b :=
  Classical.choose_spec (exists_least_mem_ge_of_boundedWindowFinite hlocal h)

private noncomputable def locallyFiniteAffineExtension (E : Set ℝ) (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite) : ℝ → ℝ := by
  classical
  exact fun x =>
    if hl : ∃ a ∈ E, a ≤ x then
      let a := locallyFinitePred E hlocal x hl
      if hu : ∃ b ∈ E, x ≤ b then
        let b := locallyFiniteSucc E hlocal x hu
        if hab : a = b then f ⟨a, (locallyFinitePred_spec E hlocal x hl).1⟩
        else f ⟨a, (locallyFinitePred_spec E hlocal x hl).1⟩ +
          (x - a) *
            (f ⟨b, (locallyFiniteSucc_spec E hlocal x hu).1⟩ -
              f ⟨a, (locallyFinitePred_spec E hlocal x hl).1⟩) / (b - a)
      else f ⟨a, (locallyFinitePred_spec E hlocal x hl).1⟩ + (x - a)
    else if hu : ∃ b ∈ E, x ≤ b then
      let b := locallyFiniteSucc E hlocal x hu
      f ⟨b, (locallyFiniteSucc_spec E hlocal x hu).1⟩ + (x - b)
    else x

private theorem locallyFiniteAffineExtension_apply_mem
    {E : Set ℝ} (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x : ℝ} (hx : x ∈ E) : locallyFiniteAffineExtension E f hlocal x = f ⟨x, hx⟩ := by
  classical
  have hl : ∃ a ∈ E, a ≤ x := ⟨x, hx, le_rfl⟩
  have hu : ∃ b ∈ E, x ≤ b := ⟨x, hx, le_rfl⟩
  have hpred : locallyFinitePred E hlocal x hl = x := by
    apply le_antisymm (locallyFinitePred_spec E hlocal x hl).2.1
    exact (locallyFinitePred_spec E hlocal x hl).2.2 x hx le_rfl
  have hsucc : locallyFiniteSucc E hlocal x hu = x := by
    apply le_antisymm
    · exact (locallyFiniteSucc_spec E hlocal x hu).2.2 x hx le_rfl
    · exact (locallyFiniteSucc_spec E hlocal x hu).2.1
  rw [locallyFiniteAffineExtension, dif_pos hl, dif_pos hu]
  dsimp only
  split
  · congr
  · rename_i hne
    exact False.elim (hne (hpred.trans hsucc.symm))

private theorem locallyFiniteAffineExtension_apply_boundedGap
    {E : Set ℝ} (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (hl : ∃ a ∈ E, a ≤ x) (hu : ∃ b ∈ E, x ≤ b)
    (hne : locallyFinitePred E hlocal x hl ≠ locallyFiniteSucc E hlocal x hu) :
    locallyFiniteAffineExtension E f hlocal x =
      f ⟨locallyFinitePred E hlocal x hl,
        (locallyFinitePred_spec E hlocal x hl).1⟩ +
      (x - locallyFinitePred E hlocal x hl) *
        (f ⟨locallyFiniteSucc E hlocal x hu,
            (locallyFiniteSucc_spec E hlocal x hu).1⟩ -
          f ⟨locallyFinitePred E hlocal x hl,
            (locallyFinitePred_spec E hlocal x hl).1⟩) /
        (locallyFiniteSucc E hlocal x hu - locallyFinitePred E hlocal x hl) := by
  classical
  rw [locallyFiniteAffineExtension, dif_pos hl, dif_pos hu, dif_neg hne]

private theorem locallyFiniteAffineExtension_apply_rightRay
    {E : Set ℝ} (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (hl : ∃ a ∈ E, a ≤ x) (hu : ¬ ∃ b ∈ E, x ≤ b) :
    locallyFiniteAffineExtension E f hlocal x =
      f ⟨locallyFinitePred E hlocal x hl,
        (locallyFinitePred_spec E hlocal x hl).1⟩ +
        (x - locallyFinitePred E hlocal x hl) := by
  classical
  rw [locallyFiniteAffineExtension, dif_pos hl, dif_neg hu]

private theorem locallyFiniteAffineExtension_apply_leftRay
    {E : Set ℝ} (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (hl : ¬ ∃ a ∈ E, a ≤ x) (hu : ∃ b ∈ E, x ≤ b) :
    locallyFiniteAffineExtension E f hlocal x =
      f ⟨locallyFiniteSucc E hlocal x hu,
        (locallyFiniteSucc_spec E hlocal x hu).1⟩ +
        (x - locallyFiniteSucc E hlocal x hu) := by
  classical
  rw [locallyFiniteAffineExtension, dif_neg hl, dif_pos hu]

private theorem locallyFiniteAffineExtension_apply_emptyRegion
    {E : Set ℝ} (f : E → ℝ)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (x : ℝ) (hl : ¬ ∃ a ∈ E, a ≤ x) (hu : ¬ ∃ b ∈ E, x ≤ b) :
    locallyFiniteAffineExtension E f hlocal x = x := by
  classical
  rw [locallyFiniteAffineExtension, dif_neg hl, dif_neg hu]

private theorem locallyFiniteAffineExtension_strictMono_sameBoundedGap
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x y : ℝ} (hxy : x < y)
    (hlx : ∃ a ∈ E, a ≤ x) (hux : ∃ b ∈ E, x ≤ b)
    (hly : ∃ a ∈ E, a ≤ y) (huy : ∃ b ∈ E, y ≤ b)
    (hpred : locallyFinitePred E hlocal x hlx = locallyFinitePred E hlocal y hly)
    (hsucc : locallyFiniteSucc E hlocal x hux = locallyFiniteSucc E hlocal y huy)
    (hne : locallyFinitePred E hlocal x hlx ≠ locallyFiniteSucc E hlocal x hux) :
    locallyFiniteAffineExtension E f hlocal x <
      locallyFiniteAffineExtension E f hlocal y := by
  rw [locallyFiniteAffineExtension_apply_boundedGap f hlocal x hlx hux hne]
  have hne' : locallyFinitePred E hlocal y hly ≠ locallyFiniteSucc E hlocal y huy := by
    simpa [← hpred, ← hsucc] using hne
  rw [locallyFiniteAffineExtension_apply_boundedGap f hlocal y hly huy hne']
  have hab_le : locallyFinitePred E hlocal x hlx ≤
      locallyFiniteSucc E hlocal x hux :=
    (locallyFinitePred_spec E hlocal x hlx).2.1.trans
      (locallyFiniteSucc_spec E hlocal x hux).2.1
  have hab : locallyFinitePred E hlocal x hlx < locallyFiniteSucc E hlocal x hux :=
    lt_of_le_of_ne hab_le (fun h ↦ hne h)
  have hfab :
      f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ <
        f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ := by
    apply hf
    exact hab
  have hpredF :
      f ⟨locallyFinitePred E hlocal y hly,
          (locallyFinitePred_spec E hlocal y hly).1⟩ =
        f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ := by
    congr 1
    apply Subtype.ext
    exact hpred.symm
  have hsuccF :
      f ⟨locallyFiniteSucc E hlocal y huy,
          (locallyFiniteSucc_spec E hlocal y huy).1⟩ =
        f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ := by
    congr 1
    apply Subtype.ext
    exact hsucc.symm
  rw [hpredF, hsuccF, ← hpred, ← hsucc]
  have hden : 0 < locallyFiniteSucc E hlocal x hux -
      locallyFinitePred E hlocal x hlx := sub_pos.mpr hab
  have hnum : 0 <
      f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ -
        f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ := sub_pos.mpr hfab
  have hslope : 0 <
      (f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ -
        f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩) /
        (locallyFiniteSucc E hlocal x hux -
          locallyFinitePred E hlocal x hlx) := div_pos hnum hden
  have hmul := mul_lt_mul_of_pos_right
    (sub_lt_sub_right hxy (locallyFinitePred E hlocal x hlx)) hslope
  simpa [mul_div_assoc] using add_lt_add_left hmul
    (f ⟨locallyFinitePred E hlocal x hlx,
      (locallyFinitePred_spec E hlocal x hlx).1⟩)

private theorem locallyFiniteAffineExtension_lt_knot
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {x c : ℝ} (hcE : c ∈ E) (hxc : x < c) :
    locallyFiniteAffineExtension E f hlocal x < f ⟨c, hcE⟩ := by
  classical
  have hu : ∃ b ∈ E, x ≤ b := ⟨c, hcE, hxc.le⟩
  let b := locallyFiniteSucc E hlocal x hu
  have hb := locallyFiniteSucc_spec E hlocal x hu
  have hbc : b ≤ c := hb.2.2 c hcE hxc.le
  by_cases hl : ∃ a ∈ E, a ≤ x
  · let a := locallyFinitePred E hlocal x hl
    have ha := locallyFinitePred_spec E hlocal x hl
    by_cases hab : a = b
    · have hxa : x = a := le_antisymm (hab ▸ hb.2.1) ha.2.1
      rw [hxa, locallyFiniteAffineExtension_apply_mem f hlocal ha.1]
      apply hf
      change a < c
      rw [← hxa]
      exact hxc
    · rw [locallyFiniteAffineExtension_apply_boundedGap f hlocal x hl hu hab]
      have hab_le : a ≤ b := ha.2.1.trans hb.2.1
      have hablt : a < b := lt_of_le_of_ne hab_le (fun h ↦ hab h)
      have hfb : f ⟨b, hb.1⟩ ≤ f ⟨c, hcE⟩ := hf.monotone hbc
      have hxb : x < b := by
        apply lt_of_le_of_ne hb.2.1
        intro hbx
        apply hab
        apply le_antisymm hab_le
        exact ha.2.2 b hb.1 hbx.symm.le
      have hfa : f ⟨a, ha.1⟩ < f ⟨b, hb.1⟩ := hf hablt
      have hden : 0 < b - a := sub_pos.mpr hablt
      have hslope : 0 < (f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a) :=
        div_pos (sub_pos.mpr hfa) hden
      have hmul := mul_lt_mul_of_pos_right (sub_lt_sub_right hxb a) hslope
      have htoB : f ⟨a, ha.1⟩ +
          (x - a) * (f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a) <
          f ⟨b, hb.1⟩ := by
        calc
          _ = f ⟨a, ha.1⟩ + (x - a) *
              ((f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a)) := by ring
          _ < f ⟨a, ha.1⟩ + (b - a) *
              ((f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a)) :=
            by simpa [add_comm] using add_lt_add_right hmul (f ⟨a, ha.1⟩)
          _ = f ⟨b, hb.1⟩ := by field_simp; ring
      exact htoB.trans_le hfb
  · rw [locallyFiniteAffineExtension_apply_leftRay f hlocal x hl hu]
    have hxb : x < b := lt_of_le_of_ne hb.2.1
      (fun h ↦ hl ⟨b, hb.1, h.symm.le⟩)
    have hleft : f ⟨b, hb.1⟩ + (x - b) < f ⟨b, hb.1⟩ := by linarith
    exact hleft.trans_le (hf.monotone hbc)

private theorem knot_lt_locallyFiniteAffineExtension
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    {c y : ℝ} (hcE : c ∈ E) (hcy : c < y) :
    f ⟨c, hcE⟩ < locallyFiniteAffineExtension E f hlocal y := by
  classical
  have hl : ∃ a ∈ E, a ≤ y := ⟨c, hcE, hcy.le⟩
  let a := locallyFinitePred E hlocal y hl
  have ha := locallyFinitePred_spec E hlocal y hl
  have hca : c ≤ a := ha.2.2 c hcE hcy.le
  by_cases hu : ∃ b ∈ E, y ≤ b
  · let b := locallyFiniteSucc E hlocal y hu
    have hb := locallyFiniteSucc_spec E hlocal y hu
    by_cases hab : a = b
    · have hya : y = a := le_antisymm (hab ▸ hb.2.1) ha.2.1
      rw [hya, locallyFiniteAffineExtension_apply_mem f hlocal ha.1]
      apply hf
      change c < a
      rw [← hya]
      exact hcy
    · rw [locallyFiniteAffineExtension_apply_boundedGap f hlocal y hl hu hab]
      have hab_le : a ≤ b := ha.2.1.trans hb.2.1
      have hablt : a < b := lt_of_le_of_ne hab_le (fun h ↦ hab h)
      have hay : a < y := by
        apply lt_of_le_of_ne ha.2.1
        intro hay
        apply hab
        apply le_antisymm hab_le
        exact hb.2.2 a ha.1 hay.symm.le
      have hfa : f ⟨a, ha.1⟩ < f ⟨b, hb.1⟩ := hf hablt
      have hslope : 0 < (f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a) :=
        div_pos (sub_pos.mpr hfa) (sub_pos.mpr hablt)
      have hfromA : f ⟨a, ha.1⟩ < f ⟨a, ha.1⟩ +
          (y - a) * (f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a) := by
        have hm : 0 < (y - a) *
            ((f ⟨b, hb.1⟩ - f ⟨a, ha.1⟩) / (b - a)) :=
          mul_pos (sub_pos.mpr hay) hslope
        simpa [mul_div_assoc] using add_lt_add_left hm (f ⟨a, ha.1⟩)
      exact (hf.monotone hca).trans_lt hfromA
  · rw [locallyFiniteAffineExtension_apply_rightRay f hlocal y hl hu]
    have hay : a < y := lt_of_le_of_ne ha.2.1
      (fun h ↦ hu ⟨a, ha.1, h.symm.le⟩)
    have hright : f ⟨a, ha.1⟩ < f ⟨a, ha.1⟩ + (y - a) := by linarith
    exact (hf.monotone hca).trans_lt hright

private theorem locallyFiniteAffineExtension_strictMono
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite) :
    StrictMono (locallyFiniteAffineExtension E f hlocal) := by
  classical
  intro x y hxy
  by_cases hxE : x ∈ E
  · rw [locallyFiniteAffineExtension_apply_mem f hlocal hxE]
    exact knot_lt_locallyFiniteAffineExtension hf hlocal hxE hxy
  by_cases hyE : y ∈ E
  · rw [locallyFiniteAffineExtension_apply_mem f hlocal hyE]
    exact locallyFiniteAffineExtension_lt_knot hf hlocal hyE hxy
  by_cases hmid : ∃ c ∈ E, x < c ∧ c < y
  · obtain ⟨c, hcE, hxc, hcy⟩ := hmid
    exact (locallyFiniteAffineExtension_lt_knot hf hlocal hcE hxc).trans
      (knot_lt_locallyFiniteAffineExtension hf hlocal hcE hcy)
  have hliff : (∃ a ∈ E, a ≤ x) ↔ ∃ a ∈ E, a ≤ y := by
    constructor
    · rintro ⟨a, haE, hax⟩
      exact ⟨a, haE, hax.trans hxy.le⟩
    · rintro ⟨a, haE, hay⟩
      refine ⟨a, haE, ?_⟩
      by_contra hax
      have hxa := lt_of_not_ge hax
      rcases hay.eq_or_lt with hayeq | haylt
      · exact hyE (hayeq ▸ haE)
      · exact hmid ⟨a, haE, hxa, haylt⟩
  have huiff : (∃ b ∈ E, x ≤ b) ↔ ∃ b ∈ E, y ≤ b := by
    constructor
    · rintro ⟨b, hbE, hxb⟩
      refine ⟨b, hbE, ?_⟩
      by_contra hyb
      have hby := lt_of_not_ge hyb
      rcases hxb.eq_or_lt with hxbeq | hxblt
      · exact hxE (hxbeq ▸ hbE)
      · exact hmid ⟨b, hbE, hxblt, hby⟩
    · rintro ⟨b, hbE, hyb⟩
      exact ⟨b, hbE, hxy.le.trans hyb⟩
  by_cases hlx : ∃ a ∈ E, a ≤ x
  · have hly := hliff.mp hlx
    have hpred : locallyFinitePred E hlocal x hlx =
        locallyFinitePred E hlocal y hly := by
      apply le_antisymm
      · exact (locallyFinitePred_spec E hlocal y hly).2.2 _
          (locallyFinitePred_spec E hlocal x hlx).1
          ((locallyFinitePred_spec E hlocal x hlx).2.1.trans hxy.le)
      · apply (locallyFinitePred_spec E hlocal x hlx).2.2 _
          (locallyFinitePred_spec E hlocal y hly).1
        by_contra hxle
        have hxp := lt_of_not_ge hxle
        rcases (locallyFinitePred_spec E hlocal y hly).2.1.eq_or_lt with hpy | hpy
        · exact hyE (hpy ▸ (locallyFinitePred_spec E hlocal y hly).1)
        · exact hmid ⟨_, (locallyFinitePred_spec E hlocal y hly).1, hxp, hpy⟩
    by_cases huy : ∃ b ∈ E, y ≤ b
    · have hux := huiff.mpr huy
      have hsucc : locallyFiniteSucc E hlocal x hux =
          locallyFiniteSucc E hlocal y huy := by
        apply le_antisymm
        · exact (locallyFiniteSucc_spec E hlocal x hux).2.2 _
            (locallyFiniteSucc_spec E hlocal y huy).1
            (hxy.le.trans (locallyFiniteSucc_spec E hlocal y huy).2.1)
        · apply (locallyFiniteSucc_spec E hlocal y huy).2.2 _
            (locallyFiniteSucc_spec E hlocal x hux).1
          by_contra hyb
          have hby := lt_of_not_ge hyb
          rcases (locallyFiniteSucc_spec E hlocal x hux).2.1.eq_or_lt with hxb | hxb
          · exact hxE (hxb ▸ (locallyFiniteSucc_spec E hlocal x hux).1)
          · exact hmid ⟨_, (locallyFiniteSucc_spec E hlocal x hux).1, hxb, hby⟩
      have hne : locallyFinitePred E hlocal x hlx ≠
          locallyFiniteSucc E hlocal x hux := by
        intro heq
        apply hxE
        have hxval : x = locallyFinitePred E hlocal x hlx := by
          apply le_antisymm
          · rw [heq]
            exact (locallyFiniteSucc_spec E hlocal x hux).2.1
          · exact (locallyFinitePred_spec E hlocal x hlx).2.1
        rw [hxval]
        exact (locallyFinitePred_spec E hlocal x hlx).1
      exact locallyFiniteAffineExtension_strictMono_sameBoundedGap hf hlocal hxy
        hlx hux hly huy hpred hsucc hne
    · have hux : ¬ ∃ b ∈ E, x ≤ b := fun h ↦ huy (huiff.mp h)
      rw [locallyFiniteAffineExtension_apply_rightRay f hlocal x hlx hux,
        locallyFiniteAffineExtension_apply_rightRay f hlocal y hly huy]
      have hpredF : f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ =
          f ⟨locallyFinitePred E hlocal y hly,
            (locallyFinitePred_spec E hlocal y hly).1⟩ := by
        congr 1
        apply Subtype.ext
        exact hpred
      rw [hpredF, hpred]
      linarith
  · have hnly : ¬ ∃ a ∈ E, a ≤ y := fun h ↦ hlx (hliff.mpr h)
    by_cases huy : ∃ b ∈ E, y ≤ b
    · have hux := huiff.mpr huy
      have hsucc : locallyFiniteSucc E hlocal x hux =
          locallyFiniteSucc E hlocal y huy := by
        apply le_antisymm
        · exact (locallyFiniteSucc_spec E hlocal x hux).2.2 _
            (locallyFiniteSucc_spec E hlocal y huy).1
            (hxy.le.trans (locallyFiniteSucc_spec E hlocal y huy).2.1)
        · apply (locallyFiniteSucc_spec E hlocal y huy).2.2 _
            (locallyFiniteSucc_spec E hlocal x hux).1
          by_contra hyb
          have hby := lt_of_not_ge hyb
          rcases (locallyFiniteSucc_spec E hlocal x hux).2.1.eq_or_lt with hxb | hxb
          · exact hxE (hxb ▸ (locallyFiniteSucc_spec E hlocal x hux).1)
          · exact hmid ⟨_, (locallyFiniteSucc_spec E hlocal x hux).1, hxb, hby⟩
      rw [locallyFiniteAffineExtension_apply_leftRay f hlocal x hlx hux,
        locallyFiniteAffineExtension_apply_leftRay f hlocal y hnly huy]
      have hsuccF : f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ =
          f ⟨locallyFiniteSucc E hlocal y huy,
            (locallyFiniteSucc_spec E hlocal y huy).1⟩ := by
        congr 1
        apply Subtype.ext
        exact hsucc
      rw [hsuccF, hsucc]
      linarith
    · have hux : ¬ ∃ b ∈ E, x ≤ b := fun h ↦ huy (huiff.mp h)
      rw [locallyFiniteAffineExtension_apply_emptyRegion f hlocal x hlx hux,
        locallyFiniteAffineExtension_apply_emptyRegion f hlocal y hnly huy]
      exact hxy

private theorem locallyFiniteAffineExtension_surjective
    {E : Set ℝ} {f : E → ℝ} (hf : StrictMono f)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (himageLocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (Set.range f ∩ Q).Finite) :
    Function.Surjective (locallyFiniteAffineExtension E f hlocal) := by
  classical
  intro y
  let F : Set ℝ := Set.range f
  by_cases hl : ∃ u ∈ F, u ≤ y
  · obtain ⟨u, huF, huy, huGreatest⟩ :=
      exists_greatest_mem_le_of_boundedWindowFinite himageLocal hl
    obtain ⟨a, hfa⟩ := huF
    by_cases huyEq : u = y
    · refine ⟨a.1, ?_⟩
      rw [locallyFiniteAffineExtension_apply_mem f hlocal a.2, hfa, huyEq]
    by_cases hr : ∃ v ∈ F, y ≤ v
    · obtain ⟨v, hvF, hyv, hvLeast⟩ :=
        exists_least_mem_ge_of_boundedWindowFinite himageLocal hr
      obtain ⟨b, hfb⟩ := hvF
      by_cases hyvEq : y = v
      · refine ⟨b.1, ?_⟩
        rw [locallyFiniteAffineExtension_apply_mem f hlocal b.2, hfb, ← hyvEq]
      have huylt : u < y := lt_of_le_of_ne huy huyEq
      have hyvlt : y < v := lt_of_le_of_ne hyv hyvEq
      have huv : u < v := huylt.trans hyvlt
      have hab : a.1 < b.1 := by
        apply hf.lt_iff_lt.mp
        simpa [hfa, hfb] using huv
      have hgapF : F ∩ Ioo u v = ∅ :=
        no_mem_Ioo_greatest_le_least_ge
          ⟨⟨a, hfa⟩, huy, huGreatest⟩ ⟨⟨b, hfb⟩, hyv, hvLeast⟩
      have hgapE : E ∩ Ioo a.1 b.1 = ∅ := by
        ext c
        simp only [mem_inter_iff, mem_Ioo, mem_empty_iff_false, iff_false]
        rintro ⟨hcE, hac, hcb⟩
        have hfc : f ⟨c, hcE⟩ ∈ F := ⟨⟨c, hcE⟩, rfl⟩
        have hfI : f ⟨c, hcE⟩ ∈ Ioo u v := by
          constructor
          · rw [← hfa]
            exact hf (show a < ⟨c, hcE⟩ from hac)
          · rw [← hfb]
            exact hf (show (⟨c, hcE⟩ : E) < b from hcb)
        have hc : f ⟨c, hcE⟩ ∈ F ∩ Ioo u v := ⟨hfc, hfI⟩
        rw [hgapF] at hc
        exact hc
      let x := a.1 + (y - u) * (b.1 - a.1) / (v - u)
      have hden : 0 < v - u := sub_pos.mpr huv
      have hxa : a.1 < x := by
        dsimp [x]
        have : 0 < (y - u) * (b.1 - a.1) / (v - u) :=
          div_pos (mul_pos (sub_pos.mpr huylt) (sub_pos.mpr hab)) hden
        linarith
      have hxb : x < b.1 := by
        dsimp [x]
        have hratio : (y - u) / (v - u) < 1 := by
          apply (div_lt_one hden).2
          linarith
        have hba : 0 < b.1 - a.1 := sub_pos.mpr hab
        have := mul_lt_mul_of_pos_right hratio hba
        field_simp at this ⊢
        nlinarith
      have hlx : ∃ c ∈ E, c ≤ x := ⟨a.1, a.2, hxa.le⟩
      have hux : ∃ c ∈ E, x ≤ c := ⟨b.1, b.2, hxb.le⟩
      have hpred : locallyFinitePred E hlocal x hlx = a.1 := by
        apply le_antisymm
        · by_contra hpa
          have hap := lt_of_not_ge hpa
          have hpx := (locallyFinitePred_spec E hlocal x hlx).2.1
          have hpb : locallyFinitePred E hlocal x hlx < b.1 := hpx.trans_lt hxb
          have hpE := (locallyFinitePred_spec E hlocal x hlx).1
          have hp : locallyFinitePred E hlocal x hlx ∈ E ∩ Ioo a.1 b.1 :=
            ⟨hpE, hap, hpb⟩
          rw [hgapE] at hp
          exact hp
        · exact (locallyFinitePred_spec E hlocal x hlx).2.2 a.1 a.2 hxa.le
      have hsucc : locallyFiniteSucc E hlocal x hux = b.1 := by
        apply le_antisymm
        · exact (locallyFiniteSucc_spec E hlocal x hux).2.2 b.1 b.2 hxb.le
        · by_contra hbs
          have hsb := lt_of_not_ge hbs
          have hxs := (locallyFiniteSucc_spec E hlocal x hux).2.1
          have has : a.1 < locallyFiniteSucc E hlocal x hux := hxa.trans_le hxs
          have hsE := (locallyFiniteSucc_spec E hlocal x hux).1
          have hs : locallyFiniteSucc E hlocal x hux ∈ E ∩ Ioo a.1 b.1 :=
            ⟨hsE, has, hsb⟩
          rw [hgapE] at hs
          exact hs
      have hpne : locallyFinitePred E hlocal x hlx ≠
          locallyFiniteSucc E hlocal x hux := by simpa [hpred, hsucc] using ne_of_lt hab
      refine ⟨x, ?_⟩
      rw [locallyFiniteAffineExtension_apply_boundedGap f hlocal x hlx hux hpne]
      have hpredF : f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ = u := by
        rw [show (⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ : E) = a by
            apply Subtype.ext; exact hpred]
        exact hfa
      have hsuccF : f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ = v := by
        rw [show (⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ : E) = b by
            apply Subtype.ext; exact hsucc]
        exact hfb
      rw [hpredF, hsuccF, hpred, hsucc]
      dsimp [x]
      field_simp [ne_of_gt hden, ne_of_gt (sub_pos.mpr hab)]
      ring
    · let x := a.1 + (y - u)
      have huylt : u < y := lt_of_le_of_ne huy huyEq
      have hxa : a.1 < x := by dsimp [x]; linarith
      have hlx : ∃ c ∈ E, c ≤ x := ⟨a.1, a.2, hxa.le⟩
      have hux : ¬ ∃ c ∈ E, x ≤ c := by
        rintro ⟨c, hcE, hxc⟩
        apply hr
        refine ⟨f ⟨c, hcE⟩, ⟨⟨c, hcE⟩, rfl⟩, ?_⟩
        have hac : a.1 < c := hxa.trans_le hxc
        by_contra hnot
        have hfcY : f ⟨c, hcE⟩ ≤ y := le_of_not_ge hnot
        have hfcU := huGreatest (f ⟨c, hcE⟩) ⟨⟨c, hcE⟩, rfl⟩ hfcY
        exact (not_le_of_gt (hf (show a < ⟨c, hcE⟩ from hac)))
          (by simpa [hfa] using hfcU)
      have hpred : locallyFinitePred E hlocal x hlx = a.1 := by
        apply le_antisymm
        · by_contra hpa
          have hap := lt_of_not_ge hpa
          let p : E := ⟨locallyFinitePred E hlocal x hlx,
            (locallyFinitePred_spec E hlocal x hlx).1⟩
          rcases le_total (f p) y with hpy | hyp
          · exact (not_le_of_gt (hf (show a < p from hap)))
              (by simpa [hfa] using huGreatest (f p) ⟨p, rfl⟩ hpy)
          · exact hr ⟨f p, ⟨p, rfl⟩, hyp⟩
        · exact (locallyFinitePred_spec E hlocal x hlx).2.2 a.1 a.2 hxa.le
      refine ⟨x, ?_⟩
      rw [locallyFiniteAffineExtension_apply_rightRay f hlocal x hlx hux]
      have hpredF : f ⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ = u := by
        rw [show (⟨locallyFinitePred E hlocal x hlx,
          (locallyFinitePred_spec E hlocal x hlx).1⟩ : E) = a by
            apply Subtype.ext; exact hpred]
        exact hfa
      rw [hpredF, hpred]
      simp [x]
  · by_cases hr : ∃ v ∈ F, y ≤ v
    · obtain ⟨v, hvF, hyv, hvLeast⟩ :=
        exists_least_mem_ge_of_boundedWindowFinite himageLocal hr
      obtain ⟨b, hfb⟩ := hvF
      let x := b.1 + (y - v)
      have hyvlt : y < v := lt_of_le_of_ne hyv
        (fun h ↦ hl ⟨v, ⟨b, hfb⟩, h.symm.le⟩)
      have hxb : x < b.1 := by dsimp [x]; linarith
      have hlx : ¬ ∃ c ∈ E, c ≤ x := by
        rintro ⟨c, hcE, hcx⟩
        apply hl
        refine ⟨f ⟨c, hcE⟩, ⟨⟨c, hcE⟩, rfl⟩, ?_⟩
        have hcb : c < b.1 := hcx.trans_lt hxb
        by_contra hnot
        have hyfc : y ≤ f ⟨c, hcE⟩ := le_of_not_ge hnot
        have hvfc := hvLeast (f ⟨c, hcE⟩) ⟨⟨c, hcE⟩, rfl⟩ hyfc
        exact (not_le_of_gt (hf (show (⟨c, hcE⟩ : E) < b from hcb)))
          (by simpa [hfb] using hvfc)
      have hux : ∃ c ∈ E, x ≤ c := ⟨b.1, b.2, hxb.le⟩
      have hsucc : locallyFiniteSucc E hlocal x hux = b.1 := by
        apply le_antisymm
        · exact (locallyFiniteSucc_spec E hlocal x hux).2.2 b.1 b.2 hxb.le
        · by_contra hbs
          let s : E := ⟨locallyFiniteSucc E hlocal x hux,
            (locallyFiniteSucc_spec E hlocal x hux).1⟩
          have hsb := lt_of_not_ge hbs
          rcases le_total (f s) y with hsy | hys
          · exact hl ⟨f s, ⟨s, rfl⟩, hsy⟩
          · exact (not_le_of_gt (hf (show s < b from hsb)))
              (by simpa [hfb] using hvLeast (f s) ⟨s, rfl⟩ hys)
      refine ⟨x, ?_⟩
      rw [locallyFiniteAffineExtension_apply_leftRay f hlocal x hlx hux]
      have hsuccF : f ⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ = v := by
        rw [show (⟨locallyFiniteSucc E hlocal x hux,
          (locallyFiniteSucc_spec E hlocal x hux).1⟩ : E) = b by
            apply Subtype.ext; exact hsucc]
        exact hfb
      rw [hsuccF, hsucc]
      simp [x]
    · have hE : E = ∅ := by
        ext a
        simp only [mem_empty_iff_false, iff_false]
        intro haE
        rcases le_total (f ⟨a, haE⟩) y with hay | hya
        · exact hl ⟨_, ⟨⟨a, haE⟩, rfl⟩, hay⟩
        · exact hr ⟨_, ⟨⟨a, haE⟩, rfl⟩, hya⟩
      refine ⟨y, ?_⟩
      have hnleft : ¬ ∃ a ∈ E, a ≤ y := by simp [hE]
      have hnright : ¬ ∃ b ∈ E, y ≤ b := by simp [hE]
      exact locallyFiniteAffineExtension_apply_emptyRegion f hlocal y hnleft hnright

private theorem boundaryOrderData_of_controlledGapWords
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    {X : Set ℝ}
    (hsource : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (frontier X ∩ Q).Finite)
    (lift : ↥(frontier X) → C.coordinateSpace) (Δ : Set ℝ)
    (hlift : ∀ x, (lift x : ℝ) = x.1)
    (hΔfin : Δ.Finite) (hΔpos : ∀ d ∈ Δ, 0 < d)
    (hwords : ∀ a b : ↥(frontier X), a.1 < b.1 →
      ∃ (n : ℕ) (word : Fin (n + 1) → C.coordinateSpace),
        IsControlledGapWord Δ (mapScalar φ) (lift a) (lift b) n word) :
    Nonempty (BoundaryOrderData C φ X) := by
  let f : ↥(frontier X) → ℝ := fun x ↦ mapScalar φ (lift x)
  have hf : StrictMono f := by
    intro a b hab
    obtain ⟨n, word, hn, h0, hlast, _hsourceMono, hgap⟩ := hwords a b hab
    have hmapped : StrictMono (fun i ↦ mapScalar φ (word i)) :=
      Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
        have hp := hΔpos _ (hgap i)
        exact sub_pos.mp hp
    have hidx : (0 : Fin (n + 1)) < Fin.last n := by
      cases n with
      | zero => omega
      | succ n => exact Fin.last_pos
    simpa only [f, h0, hlast] using hmapped hidx
  have hpositiveWords : ∀ a b : ↥(frontier X), a.1 < b.1 →
      ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
        IsPositiveGapWord Δ (f a) (f b) n word := by
    intro a b hab
    obtain ⟨n, word, hn, h0, hlast, hmono, hgap⟩ := hwords a b hab
    refine ⟨n, fun i ↦ mapScalar φ (word i), hn, ?_, ?_, ?_, hgap⟩
    · simp [f, h0]
    · simp [f, hlast]
    · exact Fin.strictMono_iff_lt_succ.mpr fun i ↦ by
        have hp := hΔpos _ (hgap i)
        exact sub_pos.mp hp
  have hcofinal := positiveGapWords_cofinal hΔfin hΔpos hf hpositiveWords
  have himageFinite := strictOrderImage_locallyFinite hf hsource
    hcofinal.1 hcofinal.2
  have hrange : Set.range f = mapScalarSet φ (Set.range lift) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨lift x, ⟨x, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨x, rfl⟩, hz⟩
      exact ⟨x, hz⟩
  exact ⟨{
    lift := lift
    lift_coe := hlift
    mapped_strictMono := hf
    source_locallyFinite := hsource
    mapped_locallyFinite := by simpa [← hrange] using himageFinite
    upper_cofinal := by simpa [← hrange] using hcofinal.1
    lower_cofinal := by simpa [← hrange] using hcofinal.2 }⟩

private theorem subfamily_tilesOn_verticalCylinder
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres) {X : Set ℝ}
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X}) :
    TilesOn C.region S {z : Tiling.Plane | z.re ∈ X} := by
  refine ⟨hT.1.mono hS, hT.2.1.mono ?_, ?_⟩
  · intro p hp
    exact hS hp
  · have hae := openUnion_aeEq_regularSupport
      (hT.2.1.mono fun p hp ↦ hS hp)
    filter_upwards [hae] with z hz
    calc
      z.re ∈ X ↔ z ∈ regularSupport C.region S := by rw [hSupport]; rfl
      _ ↔ z ∈ openUnion C.region S := Iff.of_eq hz.symm
      _ ↔ ∃ s : S, z ∈ (s.1 : Tiling.Plane) +ᵥ C.region.openCarrier := by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]

private theorem verticalCylinder_frontier_locallyFinite_of_subfamily
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres) {X : Set ℝ}
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X}) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q → (frontier X ∩ Q).Finite := by
  intro Q hQ
  rw [inter_comm]
  exact (TilesOn.verticalCylinder_frontier_locallyFinite
    (subfamily_tilesOn_verticalCylinder hT hS hSupport) hXopen hXregular (closure Q)
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hQ.closure)).subset
        (inter_subset_inter_left _ subset_closure)

private theorem slabFrontier_not_mem_ambientOpenUnion
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres) {X : Set ℝ}
    (hXopen : IsOpen X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X})
    (x : ↥(frontier X)) (q : ℝ) :
    slicePoint Axis.horizontal q x.1 ∉ openUnion C.region C.centres := by
  intro hz
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hz
  obtain ⟨t, hzt⟩ := hz
  let z := slicePoint Axis.horizontal q x.1
  have hzClosureSupport : z ∈ closure (regularSupport C.region S) := by
    rw [hSupport]
    change z ∈ closure (Complex.re ⁻¹' X)
    rw [Complex.closure_preimage_re]
    change z.re ∈ closure X
    change (((x.1 : ℂ) + (q : ℂ) * Complex.I).re ∈ closure X)
    simpa using frontier_subset_closure x.2
  have hzClosureRaw : z ∈ closure (openUnion C.region S) := by
    change z ∈ closure (interior (closure (openUnion C.region S))) at hzClosureSupport
    simpa only [closure_closure] using (closure_mono
      (interior_subset : interior (closure (openUnion C.region S)) ⊆
        closure (openUnion C.region S))) hzClosureSupport
  by_cases htS : (t.1 : Tiling.Plane) ∈ S
  · have htileSubset : (t.1 : Tiling.Plane) +ᵥ C.region.openCarrier ⊆
        regularSupport C.region S := by
      rw [regularSupport]
      let U := (t.1 : Tiling.Plane) +ᵥ C.region.openCarrier
      have hopen : IsOpen U := C.region.openCarrier_regularOpen.1.vadd t.1
      apply interior_maximal
      · intro w hw
        apply subset_closure
        rw [Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        exact ⟨⟨t.1, htS⟩, hw⟩
      · exact hopen
    have hzSupport := htileSubset hzt
    rw [hSupport] at hzSupport
    have hxX : x.1 ∈ X := by
      change (((x.1 : ℂ) + (q : ℂ) * Complex.I).re ∈ X) at hzSupport
      simpa using hzSupport
    exact x.2.2 (by rw [hXopen.interior_eq]; exact hxX)
  · have hdisjoint : Disjoint ((t.1 : Tiling.Plane) +ᵥ C.region.openCarrier)
        (openUnion C.region S) := by
      rw [Set.disjoint_left]
      intro w hwt hwS
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hwS
      obtain ⟨s, hws⟩ := hwS
      have hne : (t.1 : Tiling.Plane) ≠ s.1 := by
        intro heq
        exact htS (heq ▸ s.2)
      have hd := (isPacking_iff_openCarrier_disjoint C.region C.centres).mp
        hT.2.1 t.2 (hS s.2) hne
      exact Set.disjoint_left.1 hd hwt hws
    have hopen := C.region.openCarrier_regularOpen.1.vadd t.1
    have hclosureSubset : closure (openUnion C.region S) ⊆
        ((t.1 : Tiling.Plane) +ᵥ C.region.openCarrier)ᶜ := by
      apply closure_minimal
      · intro w hw hwt
        exact Set.disjoint_left.1 hdisjoint hwt hw
      · exact hopen.isClosed_compl
    exact (hclosureSubset hzClosureRaw) hzt

private theorem ambientHorizontalSlice_dense_ae
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ) :
    ∀ᵐ q : ℝ ∂volume,
      Dense {x : ℝ | slicePoint Axis.horizontal q x ∈
        openUnion C.region C.centres} := by
  have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae
    hT.2.2
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
      ∃ s : ↥C.centres,
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
          (s.1 : Tiling.Plane) +ᵥ C.region.openCarrier := by
    filter_upwards [hpull] with p hp
    have hp' : ({ re := p.1, im := p.2 } : ℂ) =
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    simp only [mem_univ, true_iff] at hp
    change ∃ s : ↥C.centres, ({ re := p.1, im := p.2 } : ℂ) ∈
      (s.1 : Tiling.Plane) +ᵥ C.region.openCarrier at hp
    rwa [hp'] at hp
  have hmeas : MeasurableSet {p : ℝ × ℝ | ∃ s : ↥C.centres,
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈
        (s.1 : Tiling.Plane) +ᵥ C.region.openCarrier} := by
    have hopen : IsOpen (openUnion C.region C.centres) :=
      isOpen_iUnion fun _ ↦ C.region.openCarrier_regularOpen.1.vadd _
    convert hopen.measurableSet.preimage (by fun_prop :
      Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).measurable using 1
    ext p
    simp only [mem_ofPred_eq, mem_preimage, openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, mem_iUnion]
  have hiter := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
  have hswap : ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      ∃ s : ↥C.centres, (x : ℂ) + (q : ℂ) * Complex.I ∈
        (s.1 : Tiling.Plane) +ᵥ C.region.openCarrier :=
    (MeasureTheory.Measure.ae_ae_comm hmeas).1 hiter
  filter_upwards [hswap] with q hq
  apply (volume : Measure ℝ).dense_of_ae
  filter_upwards [hq] with x hx
  rw [show slicePoint Axis.horizontal q x =
      (x : ℂ) + (q : ℂ) * Complex.I by rfl, openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
  exact hx

private theorem slabBoundary_controlledGapWords :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (S : Set Tiling.Plane)
      (hS : S ⊆ C.centres) (X : Set ℝ), IsOpen X →
      interior (closure X) = X →
      regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X} →
      ∃ (lift : ↥(frontier X) → C.coordinateSpace) (Δ : Set ℝ),
        (∀ x, (lift x : ℝ) = x.1) ∧ Δ.Finite ∧ (∀ d ∈ Δ, 0 < d) ∧
        ((∃ a b : ↥(frontier X), a.1 < b.1) → Δ.Nonempty) ∧
        ∀ a b : ↥(frontier X), a.1 < b.1 →
          ∃ (n : ℕ) (word : Fin (n + 1) → C.coordinateSpace),
            IsControlledGapWord Δ (mapScalar φ) (lift a) (lift b) n word := by
  intro C φ D hT S hS X hXopen hXregular hSupport
  have hevent : ∀ᵐ q : ℝ ∂volume,
      Dense {x : ℝ | slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} ∧
      (∃ lift : ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) →
          C.coordinateSpace, ∀ x, (lift x : ℝ) = x.1) ∧
      (∀ a ∈ sliceEndpointSet C.region C.centres Axis.horizontal q,
        ∀ b ∈ sliceEndpointSet C.region C.centres Axis.horizontal q, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
            (owner : Fin n → ↥C.centres), x 0 = a ∧ x (Fin.last n) = b ∧
              IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner) := by
    filter_upwards [ambientHorizontalSlice_dense_ae hT,
    controlledSourceEndpointLift hT Axis.horizontal,
    genericSliceChain_betweenEndpoints C.region C.centres hT Axis.horizontal] with
      q hdense hambLift hbetween
    exact ⟨hdense, hambLift, hbetween⟩
  obtain ⟨q, hdense, hambLift, hbetween⟩ := hevent.exists
  obtain ⟨ambientLift, hambCoe⟩ := hambLift
  let U : Set ℝ := {r | slicePoint Axis.horizontal q r ∈ openUnion C.region C.centres}
  have hopenU : IsOpen U := by
    exact (isOpen_iUnion fun _ ↦ C.region.openCarrier_regularOpen.1.vadd _).preimage
      (by
        change Continuous (fun r : ℝ ↦ (r : ℂ) + (q : ℂ) * Complex.I)
        fun_prop)
  have boundaryEndpoint (a : ↥(frontier X)) : a.1 ∈
      sliceEndpointSet C.region C.centres Axis.horizontal q := by
    have hnot : a.1 ∉ U := slabFrontier_not_mem_ambientOpenUnion
      hT hS hXopen hSupport a q
    change a.1 ∈ frontier U
    rw [frontier, hdense.closure_eq, hopenU.interior_eq]
    exact ⟨mem_univ _, hnot⟩
  let boundaryAsEndpoint : ↥(frontier X) →
      ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) :=
    fun a ↦ ⟨a.1, boundaryEndpoint a⟩
  let lift : ↥(frontier X) → C.coordinateSpace :=
    fun a ↦ ambientLift (boundaryAsEndpoint a)
  let P : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter (fun vw ↦ vw.1.1.re < vw.2.1.re)
  let Δf : Finset ℝ := P.image fun vw ↦
    D.firstHomeomorph vw.2.1.re - D.firstHomeomorph vw.1.1.re
  let Δ : Set ℝ := ↑Δf
  have hΔfin : Δ.Finite := Δf.finite_toSet
  have hΔpos : ∀ d ∈ Δ, 0 < d := by
    intro d hd
    obtain ⟨vw, hvw, rfl⟩ := Finset.mem_image.1 hd
    exact sub_pos.2 (D.firstHomeomorph_strictMono (Finset.mem_filter.1 hvw).2)
  have makeWord (a b : ↥(frontier X)) (hab : a.1 < b.1) :
      ∃ (n : ℕ) (word : Fin (n + 1) → C.coordinateSpace),
        IsControlledGapWord Δ (mapScalar φ) (lift a) (lift b) n word := by
    obtain ⟨n, hn, x, owner, hx0, hxlast, hchain⟩ := hbetween
      a.1 (boundaryEndpoint a) b.1 (boundaryEndpoint b) hab
    obtain ⟨xLift, hxLift⟩ := horizontalFilledChain_coordinateLift hn x owner hchain
    have h0 : xLift 0 = lift a := by
      apply Subtype.ext
      simp [hxLift, lift, boundaryAsEndpoint, hambCoe, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxLift, lift, boundaryAsEndpoint, hambCoe, hxlast]
    refine ⟨n, xLift, hn, h0, hlast, ?_, ?_⟩
    · simpa only [hxLift] using hchain.1
    · intro i
      obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
      have hvw : v.re < w.re := by simpa [Axis.coord] using hpositive
      have hvF := (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF := (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      apply Finset.mem_image.2
      refine ⟨(⟨v, hvF⟩, ⟨w, hwF⟩), by simp [P, hvw], ?_⟩
      have hep := firstOwnerMap_chainEndpoint D x xLift owner hxLift hchain i
      rw [← hep.1, ← hep.2]
      simp [firstOwnerMap, hleft, hright, Axis.coord]
  refine ⟨lift, Δ, ?_, hΔfin, hΔpos, ?_, makeWord⟩
  · intro a
    exact hambCoe (boundaryAsEndpoint a)
  · rintro ⟨a, b, hab⟩
    obtain ⟨n, word, hn, h0, hlast, hmono, hgap⟩ := makeWord a b hab
    exact ⟨_, hgap ⟨0, hn⟩⟩

private theorem boundaryOrderData_exists :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (S : Set Tiling.Plane)
      (hS : S ⊆ C.centres) (X : Set ℝ), IsOpen X →
      interior (closure X) = X →
      regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X} →
        Nonempty (BoundaryOrderData C φ X) := by
  intro C φ D hT S hS X hXopen hXregular hSupport
  obtain ⟨lift, Δ, hlift, hΔfin, hΔpos, _hΔnonempty, hwords⟩ :=
    slabBoundary_controlledGapWords D hT S hS X hXopen hXregular hSupport
  exact boundaryOrderData_of_controlledGapWords
    (verticalCylinder_frontier_locallyFinite_of_subfamily
      hT hS hXopen hXregular hSupport)
    lift Δ hlift hΔfin hΔpos hwords

private theorem exists_boundaryHomeomorph :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} {X : Set ℝ}
      (B : BoundaryOrderData C φ X),
      ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧
        ∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x) := by
  intro C φ X B
  let f : ↥(frontier X) → ℝ := fun x ↦ mapScalar φ (B.lift x)
  let h : ℝ → ℝ := locallyFiniteAffineExtension (frontier X) f B.source_locallyFinite
  have hmono : StrictMono h :=
    locallyFiniteAffineExtension_strictMono B.mapped_strictMono B.source_locallyFinite
  have himageLocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (Set.range f ∩ Q).Finite := by
    intro Q hQ
    have heq : Set.range f = mapScalarSet φ (Set.range B.lift) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨B.lift x, ⟨x, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨x, rfl⟩, hz⟩
        exact ⟨x, hz⟩
    rw [heq]
    exact B.mapped_locallyFinite Q hQ
  have hsurj : Function.Surjective h :=
    locallyFiniteAffineExtension_surjective B.mapped_strictMono
      B.source_locallyFinite himageLocal
  let e : ℝ ≃o ℝ :=
    { toEquiv := Equiv.ofBijective h ⟨hmono.injective, hsurj⟩
      map_rel_iff' := hmono.le_iff_le }
  refine ⟨e.toHomeomorph, e.strictMono, ?_⟩
  intro x
  change h x.1 = mapScalar φ (B.lift x)
  simpa [f, h] using
    (locallyFiniteAffineExtension_apply_mem f B.source_locallyFinite x.2)

private theorem firstStage_selectedOwner_gaps :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ) (S : Set Tiling.Plane)
      (hS : S ⊆ C.centres),
      ∀ᵐ q : ℝ ∂volume, ∀ {n : ℕ} (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        (∀ i, (xLift i : ℝ) = x i) →
        IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner →
        ∀ i : Fin n,
          (axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) ⊆
            openUnion C.region S ↔ (owner i : Tiling.Plane) ∈ S) ∧
          (axisInterval Axis.horizontal q (mapScalar φ (xLift i.castSucc))
              (mapScalar φ (xLift i.succ)) ⊆
            openUnion D.firstRegion
              (deformedCenterCarrierOn
                ⟨fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2),
                  firstCenter_formula_injective D hT⟩
                {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔
            (owner i : Tiling.Plane) ∈ S) := by
  intro C φ D hT S hS
  filter_upwards [firstSliceChain_transport D hT] with q htransport
  intro n x xLift owner hxLift hchain i
  obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hsourceOwner⟩ := hchain.2 i
  have htargetChain := htransport x xLift owner hxLift hchain
  have htargetOwner := htargetChain.2 i
  have sourceIff : axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) ⊆
      openUnion C.region S ↔ (owner i : Tiling.Plane) ∈ S := by
    constructor
    · intro hsub
      let r := (x i.castSucc + x i.succ) / 2
      have hr : r ∈ Ioo (x i.castSucc) (x i.succ) := by
        have hs := hchain.1 (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
        dsimp [r]
        constructor <;> linarith
      let z := slicePoint Axis.horizontal q r
      have hzI : z ∈ axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) := by
        change z.im = q ∧ z.re ∈ Ioo (x i.castSucc) (x i.succ)
        constructor
        · change ((r : ℂ) + (q : ℂ) * Complex.I).im = q
          simp
        · change ((r : ℂ) + (q : ℂ) * Complex.I).re ∈ Ioo _ _
          simpa using hr
      have hzS := hsub hzI
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzS
      obtain ⟨s, hzs⟩ := hzS
      by_contra hnot
      have hne : (owner i : Tiling.Plane) ≠ s.1 := fun heq ↦ hnot (heq ▸ s.2)
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint C.region C.centres).mp hT.2.1
          (owner i).2 (hS s.2) hne) (hsourceOwner hzI) hzs
    · intro hi z hz
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      exact ⟨⟨owner i, hi⟩, hsourceOwner hz⟩
  have targetIff : axisInterval Axis.horizontal q
      (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ)) ⊆
      openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2),
            firstCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔
      (owner i : Tiling.Plane) ∈ S := by
    let E : ↥C.centres ↪ Tiling.Plane :=
      ⟨fun t ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
        firstCenter_formula_injective D hT⟩
    have hpackE : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
        (D.firstRegion.toPolygonalRegion.placements (deformedCenterCarrier E)) := by
      apply (isPacking_iff_openCarrier_disjoint D.firstRegion
        (deformedCenterCarrier E)).2
      intro a ha b hb hab
      obtain ⟨s, rfl⟩ := ha
      obtain ⟨t, rfl⟩ := hb
      apply Set.disjoint_left.2
      intro z hzs hzt
      apply hab
      apply congrArg E
      exact firstTranslatedInteriors_overlap_reflect D hT s t ⟨z, hzs, hzt⟩
    constructor
    · intro hsub
      let r := (mapScalar φ (xLift i.castSucc) +
        mapScalar φ (xLift i.succ)) / 2
      have hr : r ∈ Ioo (mapScalar φ (xLift i.castSucc))
          (mapScalar φ (xLift i.succ)) := by
        have hs := htargetChain.1
          (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
        dsimp [r]
        constructor <;> linarith
      let z := slicePoint Axis.horizontal q r
      have hzI : z ∈ axisInterval Axis.horizontal q
          (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ)) :=
        by
          change z.im = q ∧ z.re ∈ Ioo _ _
          constructor
          · change ((r : ℂ) + (q : ℂ) * Complex.I).im = q
            simp
          · change ((r : ℂ) + (q : ℂ) * Complex.I).re ∈ Ioo _ _
            simpa using hr
      have hzS := hsub hzI
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzS
      obtain ⟨s, hzs⟩ := hzS
      obtain ⟨t, htSel, htEq⟩ := s.2
      by_contra hnot
      have hne : E (owner i) ≠ s.1 := by
        intro heq
        apply hnot
        have : owner i = t := E.injective (heq.trans htEq.symm)
        simpa [this] using htSel
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint D.firstRegion (deformedCenterCarrier E)).mp
          hpackE ⟨owner i, rfl⟩ ⟨t, htEq⟩ hne) (htargetOwner hzI) hzs
    · intro hi z hz
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      refine ⟨⟨E (owner i), ⟨owner i, hi, rfl⟩⟩, ?_⟩
      exact htargetOwner hz
  exact ⟨sourceIff, targetIff⟩

private theorem source_selectedComplement_rawAE
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) (X : Set ℝ)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X}) :
    openUnion C.region S =ᵐ[volume] {z : Tiling.Plane | z.re ∈ X} ∧
      openUnion C.region (C.centres \ S) =ᵐ[volume]
        {z : Tiling.Plane | z.re ∉ X} := by
  have packing_mono {A : Set Tiling.Plane} (hA : A ⊆ C.centres) :
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements A) := by
    apply (isPacking_iff_openCarrier_disjoint C.region A).2
    intro a ha b hb hab
    exact (isPacking_iff_openCarrier_disjoint C.region C.centres).1 hT.2.1
      (hA ha) (hA hb) hab
  have hpackS := packing_mono hS
  have hdiff : C.centres \ S ⊆ C.centres := fun _ h ↦ h.1
  have hpackDiff := packing_mono hdiff
  have hselected : openUnion C.region S =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ X} :=
    (openUnion_aeEq_regularSupport hpackS).trans (Filter.Eventually.of_forall fun z ↦ by
      rw [hSupport])
  refine ⟨hselected, ?_⟩
  filter_upwards [hT.2.2, hselected,
    openUnion_aeEq_regularSupport hpackDiff] with z hamb hsel _hrawDiff
  simp only [mem_univ, true_iff] at hamb
  have hselIff : openUnion C.region S z ↔ ({z : Tiling.Plane | z.re ∈ X} : Set _ ) z :=
    Iff.of_eq hsel
  apply propext
  constructor
  · intro hzDiff hzX
    have hzDiff' : z ∈ openUnion C.region (C.centres \ S) := hzDiff
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzDiff'
    obtain ⟨t, hzt⟩ := hzDiff'
    apply t.2.2
    have hzSel : z ∈ openUnion C.region S := hselIff.mpr hzX
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzSel
    obtain ⟨s, hzs⟩ := hzSel
    have heq : t.1 = s.1 := by
      by_contra hne
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint C.region C.centres).1 hT.2.1
          t.2.1 (hS s.2) hne) hzt hzs
    exact heq ▸ s.2
  · intro hznot
    obtain ⟨t, hzt⟩ := hamb
    by_cases htS : t.1 ∈ S
    · exact False.elim (hznot (hselIff.mp (by
        change z ∈ openUnion C.region S
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        exact ⟨⟨t.1, htS⟩, hzt⟩)))
    · change z ∈ openUnion C.region (C.centres \ S)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      exact ⟨⟨t.1, t.2, htS⟩, hzt⟩

private theorem source_selectedComplement_sliceAE
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) (X : Set ℝ)
    (hXo : IsOpen X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X}) :
    ∀ᵐ q : ℝ ∂volume, ∀ᵐ r : ℝ ∂volume,
      (slicePoint Axis.horizontal q r ∈ openUnion C.region S ↔ r ∈ X) ∧
      (slicePoint Axis.horizontal q r ∈ openUnion C.region (C.centres \ S) ↔
        r ∉ X) := by
  obtain ⟨hsel, hcomp⟩ := source_selectedComplement_rawAE hT S hS X hSupport
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      (z ∈ openUnion C.region S ↔ z.re ∈ X) ∧
      (z ∈ openUnion C.region (C.centres \ S) ↔ z.re ∉ X) := by
    filter_upwards [hsel, hcomp] with z hzS hzC
    exact ⟨Iff.of_eq hzS, Iff.of_eq hzC⟩
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hxy : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      (((x : ℂ) + (y : ℂ) * Complex.I ∈ openUnion C.region S ↔ x ∈ X) ∧
       ((x : ℂ) + (y : ℂ) * Complex.I ∈ openUnion C.region (C.centres \ S) ↔
         x ∉ X)) := by
    have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod hpull
    filter_upwards [hslices] with x hx
    filter_upwards [hx] with y hy
    have heq : ({ re := x, im := y } : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rwa [← heq]
  have hmeas : MeasurableSet {p : ℝ × ℝ |
      (((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ openUnion C.region S ↔ p.1 ∈ X) ∧
       ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ openUnion C.region
          (C.centres \ S) ↔ p.1 ∉ X))} := by
    have hopenS : IsOpen (openUnion C.region S) :=
      isOpen_iUnion fun t ↦ C.region.openCarrier_regularOpen.1.vadd t.1
    have hopenC : IsOpen (openUnion C.region (C.centres \ S)) :=
      isOpen_iUnion fun t ↦ C.region.openCarrier_regularOpen.1.vadd t.1
    let g : ℝ × ℝ → Tiling.Plane := fun p ↦
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    have hg : Continuous g := by fun_prop
    exact ((hopenS.preimage hg).measurableSet.iff
      (hXo.preimage continuous_fst).measurableSet).inter
      ((hopenC.preimage hg).measurableSet.iff
        (hXo.measurableSet.compl.preimage continuous_fst.measurable))
  have hyx := (MeasureTheory.Measure.ae_ae_comm hmeas).mp hxy
  filter_upwards [hyx] with q hq
  filter_upwards [hq] with r hr
  simpa [slicePoint, Axis.coord] using hr

private theorem firstStage_mappedEndpoints_order_cofinal :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      ∀ᵐ q : ℝ ∂volume,
        ∃ lift : ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) →
            C.coordinateSpace,
          (∀ a, (lift a : ℝ) = a.1) ∧
          StrictMono (fun a => mapScalar φ (lift a)) ∧
          ¬ BddAbove (Set.range (fun a => mapScalar φ (lift a))) ∧
          ¬ BddBelow (Set.range (fun a => mapScalar φ (lift a))) := by
  intro C φ D hT
  filter_upwards
      [controlledSourceEndpointLift hT Axis.horizontal,
        genericSliceEndpointSet_unbounded C.region C.centres hT Axis.horizontal,
        genericSliceChain_betweenEndpoints C.region C.centres hT Axis.horizontal,
        firstSliceChain_transport D hT] with q hlift hunbounded hbetween htransport
  obtain ⟨lift, hliftcoe⟩ := hlift
  let E := sliceEndpointSet C.region C.centres Axis.horizontal q
  let f : ↥E → ℝ := fun a => mapScalar φ (lift a)
  have chainData (a b : ↥E) (hab : a.1 < b.1) :
      ∃ (n : ℕ), 0 < n ∧ ∃ (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace) (owner : Fin n → ↥C.centres),
        x 0 = a.1 ∧ x (Fin.last n) = b.1 ∧
        (∀ i, (xLift i : ℝ) = x i) ∧
        IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner := by
    obtain ⟨n, hn, x, owner, hx0, hxlast, hchain⟩ :=
      hbetween a.1 a.2 b.1 b.2 hab
    obtain ⟨xLift, hxLift⟩ := horizontalFilledChain_coordinateLift hn x owner hchain
    exact ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain⟩
  have hf : StrictMono f := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain⟩ :=
      chainData a b hab
    have h0 : xLift 0 = lift a := by
      apply Subtype.ext
      simp [hxLift, hliftcoe, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxLift, hliftcoe, hxlast]
    have htarget := htransport x xLift owner hxLift hchain
    have hindex : (0 : Fin (n + 1)) < Fin.last n := hn
    simpa only [f, h0, hlast] using htarget.1 hindex
  let pairs : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter fun vw => vw.1.1.re < vw.2.1.re
  let Δf : Finset ℝ := pairs.image fun vw =>
    D.firstHomeomorph vw.2.1.re - D.firstHomeomorph vw.1.1.re
  let Δ : Set ℝ := ↑Δf
  have hΔfin : Δ.Finite := Δf.finite_toSet
  have hΔpos : ∀ d ∈ Δ, 0 < d := by
    intro d hd
    obtain ⟨vw, hvw, rfl⟩ := Finset.mem_image.mp hd
    exact sub_pos.mpr (D.firstHomeomorph_strictMono (Finset.mem_filter.mp hvw).2)
  have hwords : ∀ a b : ↥E, a.1 < b.1 →
      ∃ (n : ℕ) (word : Fin (n + 1) → ℝ),
        IsPositiveGapWord Δ (f a) (f b) n word := by
    intro a b hab
    obtain ⟨n, hn, x, xLift, owner, hx0, hxlast, hxLift, hchain⟩ :=
      chainData a b hab
    let word : Fin (n + 1) → ℝ := fun i => mapScalar φ (xLift i)
    have htarget := htransport x xLift owner hxLift hchain
    refine ⟨n, word, hn, ?_, ?_, htarget.1, ?_⟩
    · have h0 : xLift 0 = lift a := by
        apply Subtype.ext
        simp [hxLift, hliftcoe, hx0]
      simp [word, f, h0]
    · have hlast : xLift (Fin.last n) = lift b := by
        apply Subtype.ext
        simp [hxLift, hliftcoe, hxlast]
      simp [word, f, hlast]
    · intro i
      obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
      have hvw : v.re < w.re := by simpa [Axis.coord] using sub_pos.mp hpositive
      have hvF := (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF := (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      apply Finset.mem_image.2
      refine ⟨(⟨v, hvF⟩, ⟨w, hwF⟩), by simp [pairs, hvw], ?_⟩
      have hep := firstOwnerMap_chainEndpoint D x xLift owner hxLift hchain i
      simp only [word]
      rw [← hep.1, ← hep.2]
      simp [firstOwnerMap, hleft, hright, Axis.coord]
  have hcofinal := positiveGapWords_cofinal hΔfin hΔpos hf hwords
  exact ⟨lift, hliftcoe, hf, hcofinal.1 hunbounded.1, hcofinal.2 hunbounded.2⟩

private theorem firstStage_endpointHomeomorphism :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (hT : TilesOn C.region C.centres univ),
      ∀ᵐ q : ℝ ∂volume,
        ∃ (lift : ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) →
            C.coordinateSpace) (G : ℝ ≃ₜ ℝ),
          (∀ a, (lift a : ℝ) = a.1) ∧ StrictMono G ∧
          ∀ a, G a.1 = mapScalar φ (lift a) := by
  intro C φ D hT
  filter_upwards
      [firstStage_mappedEndpoints_order_cofinal D hT,
        genericSliceEndpointSet_locallyFinite C.region C.centres hT Axis.horizontal]
      with q horder hlocal
  obtain ⟨lift, hlift, hf, hupper, hlower⟩ := horder
  let E := sliceEndpointSet C.region C.centres Axis.horizontal q
  let f : ↥E → ℝ := fun a => mapScalar φ (lift a)
  have hlocal' : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite := hlocal
  have himage : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (Set.range f ∩ Q).Finite :=
    strictOrderImage_locallyFinite hf hlocal'
      (fun _ ↦ hupper) (fun _ ↦ hlower)
  let g := locallyFiniteAffineExtension E f hlocal'
  have hgmono : StrictMono g := locallyFiniteAffineExtension_strictMono hf hlocal'
  have hgsurj : Function.Surjective g :=
    locallyFiniteAffineExtension_surjective hf hlocal' himage
  let e : ℝ ≃o ℝ :=
    { toEquiv := Equiv.ofBijective g ⟨hgmono.injective, hgsurj⟩
      map_rel_iff' := hgmono.le_iff_le }
  refine ⟨lift, e.toHomeomorph, hlift, e.strictMono, ?_⟩
  intro a
  change g a.1 = mapScalar φ (lift a)
  simpa [g, f] using locallyFiniteAffineExtension_apply_mem f hlocal' a.2

private theorem exists_frontier_mem_uIcc_of_membership_ne
    {X : Set ℝ} (hXo : IsOpen X) {x y : ℝ}
    (hne : ¬ (x ∈ X ↔ y ∈ X)) :
    (frontier X ∩ uIcc x y).Nonempty := by
  by_contra hempty
  have hsub : uIcc x y ⊆ (frontier X)ᶜ := by
    intro z hz hzfront
    exact hempty ⟨z, hzfront, hz⟩
  have hunion : uIcc x y ⊆ X ∪ interior Xᶜ := by
    intro z hz
    have := hsub hz
    rw [compl_frontier_eq_union_interior, hXo.interior_eq] at this
    exact this
  have hdisj : Disjoint X (interior Xᶜ) :=
    Set.disjoint_of_subset_right interior_subset disjoint_compl_right
  rcases em (x ∈ X) with hx | hx
  · have hxint : (uIcc x y ∩ X).Nonempty := ⟨x, left_mem_uIcc, hx⟩
    have hall := ordConnected_uIcc.isPreconnected.subset_left_of_subset_union
      hXo isOpen_interior hdisj hunion hxint
    exact hne ⟨fun _ ↦ hall right_mem_uIcc, fun _ ↦ hx⟩
  · have hy : y ∈ X := by
      by_contra hy
      exact hne ⟨fun h ↦ False.elim (hx h), fun h ↦ False.elim (hy h)⟩
    have hyint : (uIcc x y ∩ X).Nonempty := ⟨y, right_mem_uIcc, hy⟩
    have hall := ordConnected_uIcc.isPreconnected.subset_left_of_subset_union
      hXo isOpen_interior hdisj hunion hyint
    exact hx (hall left_mem_uIcc)

private theorem mem_iff_of_mem_Ioo_of_disjoint_frontier
    {X : Set ℝ} (hXo : IsOpen X) {a b r s : ℝ}
    (hr : r ∈ Ioo a b) (hs : s ∈ Ioo a b)
    (hgap : Ioo a b ∩ frontier X = ∅) :
    (r ∈ X ↔ s ∈ X) := by
  by_contra hne
  obtain ⟨c, hcF, hc⟩ := exists_frontier_mem_uIcc_of_membership_ne hXo hne
  have hcI : c ∈ Ioo a b := by
    rcases le_total r s with hrs | hsr
    · rw [uIcc_of_le hrs] at hc
      exact ⟨lt_of_lt_of_le hr.1 hc.1, lt_of_le_of_lt hc.2 hs.2⟩
    · simp only [uIcc, min_eq_right hsr, max_eq_left hsr] at hc
      exact ⟨lt_of_lt_of_le hs.1 hc.1, lt_of_le_of_lt hc.2 hr.2⟩
  have : c ∈ Ioo a b ∩ frontier X := ⟨hcI, hcF⟩
  simp [hgap] at this

private theorem image_eq_of_strictMonoHomeomorph_agree_frontier
    {X : Set ℝ} (hXo : IsOpen X) (H G : ℝ ≃ₜ ℝ)
    (hH : StrictMono H) (hG : StrictMono G)
    (hagree : ∀ c : ↥(frontier X), H c.1 = G c.1) :
    H '' X = G '' X := by
  ext z
  let x := H.symm z
  let y := G.symm z
  have hHx : H x = z := H.apply_symm_apply z
  have hGy : G y = z := G.apply_symm_apply z
  have hcut (c : ↥(frontier X)) : x < c.1 ↔ y < c.1 := by
    rw [← hH.lt_iff_lt, hHx, hagree c, ← hGy, hG.lt_iff_lt]
  have hcut' (c : ↥(frontier X)) : c.1 < x ↔ c.1 < y := by
    rw [← hH.lt_iff_lt, hHx, hagree c, ← hGy, hG.lt_iff_lt]
  have hmem : x ∈ X ↔ y ∈ X := by
    by_contra hne
    obtain ⟨c, hcfront, hcI⟩ := exists_frontier_mem_uIcc_of_membership_ne hXo hne
    let cf : ↥(frontier X) := ⟨c, hcfront⟩
    rcases lt_trichotomy x y with hxy | hxy | hyx
    · have hc : x ≤ c ∧ c ≤ y := by simpa [uIcc_of_le hxy.le] using hcI
      by_cases hxc : x = c
      · have : c < y := hxc ▸ hxy
        exact (not_lt_of_ge hc.1) ((hcut' cf).mpr this)
      · exact (not_lt_of_ge hc.2) ((hcut cf).mp (lt_of_le_of_ne hc.1 hxc))
    · exact hne (hxy ▸ Iff.rfl)
    · have hc : y ≤ c ∧ c ≤ x := by simpa [uIcc_of_ge hyx.le] using hcI
      by_cases hyc : y = c
      · have : c < x := hyc ▸ hyx
        exact (not_lt_of_ge hc.1) ((hcut' cf).mp this)
      · exact (not_lt_of_ge hc.2) ((hcut cf).mpr (lt_of_le_of_ne hc.1 hyc))
  constructor
  · rintro ⟨a, haX, rfl⟩
    refine ⟨G.symm (H a), ?_, G.apply_symm_apply (H a)⟩
    exact hmem.mp (by simpa [x, y] using haX)
  · rintro ⟨a, haX, rfl⟩
    refine ⟨H.symm (G a), ?_, H.apply_symm_apply (G a)⟩
    exact hmem.mpr (by simpa [x, y] using haX)

private theorem firstStage_endpointHomeomorphism_agrees_boundary
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) (X : Set ℝ)
    (hXo : IsOpen X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X})
    (B : BoundaryOrderData C φ X) (H : ℝ ≃ₜ ℝ)
    (hHe : ∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x)) :
    ∀ᵐ q : ℝ ∂volume,
      ∃ (lift : ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) →
          C.coordinateSpace) (G : ℝ ≃ₜ ℝ),
        (∀ a, (lift a : ℝ) = a.1) ∧ StrictMono G ∧
        (∀ a, G a.1 = mapScalar φ (lift a)) ∧
        ∀ x : ↥(frontier X), G x.1 = H x.1 := by
  filter_upwards [firstStage_endpointHomeomorphism D hT,
    ambientHorizontalSlice_dense_ae hT] with q hG hdense
  obtain ⟨lift, G, hlift, hGmono, hGendpoint⟩ := hG
  have boundaryEndpoint (a : ↥(frontier X)) : a.1 ∈
      sliceEndpointSet C.region C.centres Axis.horizontal q := by
    have hnot := slabFrontier_not_mem_ambientOpenUnion hT hS hXo hSupport a q
    have hopen : IsOpen
        {x : ℝ | slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} := by
      exact (isOpen_iUnion fun _ ↦ C.region.openCarrier_regularOpen.1.vadd _).preimage
        (by change Continuous (fun x : ℝ ↦ (x : ℂ) + (q : ℂ) * Complex.I); fun_prop)
    change a.1 ∈ frontier
      {x : ℝ | slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres}
    rw [frontier, hdense.closure_eq, hopen.interior_eq]
    exact ⟨mem_univ _, hnot⟩
  let asEndpoint (a : ↥(frontier X)) :
      ↥(sliceEndpointSet C.region C.centres Axis.horizontal q) :=
    ⟨a.1, boundaryEndpoint a⟩
  refine ⟨lift, G, hlift, hGmono, hGendpoint, ?_⟩
  intro a
  rw [hGendpoint (asEndpoint a), hHe a]
  congr 1
  apply Subtype.ext
  simpa [asEndpoint, hlift] using (B.lift_coe a).symm

private theorem firstStage_transportedGap_mem_selected_iff
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) {q : ℝ} {n : ℕ}
    {x : Fin (n + 1) → ℝ} {xLift : Fin (n + 1) → C.coordinateSpace}
    {owner : Fin n → ↥C.centres}
    (htransport : IsTransportedIndexedSliceChain D.firstRegion
      (fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2))
      Axis.horizontal q (fun i ↦ mapScalar φ (xLift i)) owner)
    (i : Fin n) {z : Tiling.Plane}
    (hzI : z ∈ axisInterval Axis.horizontal q
      (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ))) :
    z ∈ openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
            firstCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔
      (owner i : Tiling.Plane) ∈ S := by
  let E : ↥C.centres ↪ Tiling.Plane :=
    ⟨fun t ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
      firstCenter_formula_injective D hT⟩
  have hpack : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
      (D.firstRegion.toPolygonalRegion.placements (deformedCenterCarrier E)) := by
    apply (isPacking_iff_openCarrier_disjoint D.firstRegion
      (deformedCenterCarrier E)).2
    intro a ha b hb hab
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    apply Set.disjoint_left.2
    intro w hws hwt
    apply hab
    apply congrArg E
    exact firstTranslatedInteriors_overlap_reflect D hT s t ⟨w, hws, hwt⟩
  have hzOwner : z ∈ E (owner i) +ᵥ D.firstRegion.openCarrier :=
    htransport.2 i hzI
  constructor
  · intro hzS
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzS
    obtain ⟨s, hzs⟩ := hzS
    obtain ⟨t, htS, htEq⟩ := s.2
    have hzt : z ∈ E t +ᵥ D.firstRegion.openCarrier := by
      rw [htEq]
      exact hzs
    have heq : owner i = t := by
      apply E.injective
      by_contra hne
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint D.firstRegion (deformedCenterCarrier E)).1
          hpack ⟨owner i, rfl⟩ ⟨t, rfl⟩ hne) hzOwner hzt
    simpa [heq] using htS
  · intro hi
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
    exact ⟨⟨E (owner i), ⟨owner i, hi, rfl⟩⟩, hzOwner⟩

private theorem firstStage_gap_owner_iff_chamber_selected
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) {X : Set ℝ}
    (hXo : IsOpen X) {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    {owner : Fin n → ↥C.centres}
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (hslice : ∀ᵐ r : ℝ ∂volume,
      (slicePoint Axis.horizontal q r ∈ openUnion C.region S ↔ r ∈ X) ∧
      (slicePoint Axis.horizontal q r ∈ openUnion C.region (C.centres \ S) ↔
        r ∉ X))
    {a b : ℝ} (hab : a < b) (hfrontier : Ioo a b ∩ frontier X = ∅)
    (i : Fin n)
    (hinside : Ioo (x i.castSucc) (x i.succ) ⊆ Ioo a b) :
    ((owner i : Tiling.Plane) ∈ S ↔ Ioo a b ⊆ X) := by
  have hxi : x i.castSucc < x i.succ :=
    hchain.1 (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  obtain ⟨r, hrI, hrGood⟩ := exists_mem_Ioo_of_ae_real hxi hslice
  have hrChamber : r ∈ Ioo a b := hinside hrI
  obtain ⟨_v, _w, _hv, _hw, _hleft, _hright, _hpositive, hownerGap⟩ := hchain.2 i
  have howner : slicePoint Axis.horizontal q r ∈
      (owner i : Tiling.Plane) +ᵥ C.region.openCarrier :=
    hownerGap (by
      simp only [axisInterval, Set.mem_ofPred_eq, slicePoint]
      exact ⟨by simp, by simpa using hrI⟩)
  have hownerSelected : (owner i : Tiling.Plane) ∈ S ↔ r ∈ X := by
    constructor
    · intro hi
      exact hrGood.1.mp (by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        exact ⟨⟨owner i, hi⟩, howner⟩)
    · intro hrX
      have hrSel := hrGood.1.mpr hrX
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hrSel
      obtain ⟨t, hrt⟩ := hrSel
      have heq : (owner i : Tiling.Plane) = t.1 := by
        by_contra hne
        exact Set.disjoint_left.1
          ((isPacking_iff_openCarrier_disjoint C.region C.centres).1 hT.2.1
            (owner i).2 (hS t.2) hne) howner hrt
      exact heq ▸ t.2
  rw [hownerSelected]
  constructor
  · intro hrX s hs
    exact (mem_iff_of_mem_Ioo_of_disjoint_frontier hXo hrChamber hs hfrontier).mp hrX
  · intro hall
    exact hall hrChamber

private theorem filledGap_owner_mem_iff_of_sliceAE
    {C : ApproximationContext.{u}} (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) {X : Set ℝ}
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥C.centres}
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (hslice : ∀ᵐ r : ℝ ∂volume,
      (slicePoint Axis.horizontal q r ∈ openUnion C.region S ↔ r ∈ X) ∧
      (slicePoint Axis.horizontal q r ∈ openUnion C.region (C.centres \ S) ↔
        r ∉ X))
    (i : Fin n) :
    ∃ r ∈ Ioo (x i.castSucc) (x i.succ),
      ((owner i : Tiling.Plane) ∈ S ↔ r ∈ X) := by
  have hxi : x i.castSucc < x i.succ :=
    hchain.1 (show i.castSucc < i.succ from Fin.castSucc_lt_succ)
  obtain ⟨r, hrI, hrGood⟩ := exists_mem_Ioo_of_ae_real hxi hslice
  obtain ⟨_v, _w, _hv, _hw, _hleft, _hright, _hpositive, hownerGap⟩ := hchain.2 i
  have howner : slicePoint Axis.horizontal q r ∈
      (owner i : Tiling.Plane) +ᵥ C.region.openCarrier := hownerGap (by
    simp only [axisInterval, Set.mem_ofPred_eq, slicePoint]
    exact ⟨by simp, by simpa using hrI⟩)
  refine ⟨r, hrI, ?_⟩
  constructor
  · intro hi
    exact hrGood.1.mp (by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      exact ⟨⟨owner i, hi⟩, howner⟩)
  · intro hrX
    have hrSel := hrGood.1.mpr hrX
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hrSel
    obtain ⟨t, hrt⟩ := hrSel
    have heq : (owner i : Tiling.Plane) = t.1 := by
      by_contra hne
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint C.region C.centres).1 hT.2.1
          (owner i).2 (hS t.2) hne) howner hrt
    exact heq ▸ t.2

private theorem firstStage_transportedGap_mem_iff_chamber_selected
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) {X : Set ℝ}
    (hXo : IsOpen X) {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    {xLift : Fin (n + 1) → C.coordinateSpace} {owner : Fin n → ↥C.centres}
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (htransport : IsTransportedIndexedSliceChain D.firstRegion
      (fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2))
      Axis.horizontal q (fun i ↦ mapScalar φ (xLift i)) owner)
    (hslice : ∀ᵐ r : ℝ ∂volume,
      (slicePoint Axis.horizontal q r ∈ openUnion C.region S ↔ r ∈ X) ∧
      (slicePoint Axis.horizontal q r ∈ openUnion C.region (C.centres \ S) ↔
        r ∉ X))
    {a b : ℝ} (hab : a < b) (hfrontier : Ioo a b ∩ frontier X = ∅)
    (i : Fin n) (hinside : Ioo (x i.castSucc) (x i.succ) ⊆ Ioo a b)
    {z : Tiling.Plane}
    (hzI : z ∈ axisInterval Axis.horizontal q
      (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ))) :
    (z ∈ openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
            firstCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔ Ioo a b ⊆ X) := by
  rw [firstStage_transportedGap_mem_selected_iff (x := x) D hT S htransport i hzI]
  exact firstStage_gap_owner_iff_chamber_selected hT S hS hXo hchain hslice
    hab hfrontier i hinside

private theorem filledGap_disjoint_slabFrontier
    {C : ApproximationContext.{u}} {X : Set ℝ} {q : ℝ} {n : ℕ}
    {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥C.centres}
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (hboundary : ∀ a : ↥(frontier X),
      slicePoint Axis.horizontal q a.1 ∉ openUnion C.region C.centres)
    (i : Fin n) :
    Ioo (x i.castSucc) (x i.succ) ∩ frontier X = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  rintro a ⟨haI, haF⟩
  apply hboundary ⟨a, haF⟩
  obtain ⟨_v, _w, _hv, _hw, _hl, _hr, _hp, hinside⟩ := hchain.2 i
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
  refine ⟨owner i, hinside ?_⟩
  simp only [axisInterval, Set.mem_ofPred_eq, slicePoint]
  constructor
  · simp
  · simpa using haI

private theorem slabFrontier_between_chainEndpoints_eq_entry
    {C : ApproximationContext.{u}} {X : Set ℝ} {q : ℝ} {n : ℕ}
    {x : Fin (n + 1) → ℝ} {owner : Fin n → ↥C.centres}
    (hchain : IsFilledIndexedSliceChain C.region C.centres Axis.horizontal q x owner)
    (hboundary : ∀ a : ↥(frontier X),
      slicePoint Axis.horizontal q a.1 ∉ openUnion C.region C.centres)
    (c : ↥(frontier X)) (hleft : x 0 ≤ c.1)
    (hright : c.1 ≤ x (Fin.last n)) :
    ∃ k : Fin (n + 1), c.1 = x k := by
  by_contra hnone
  have hne : ∀ k : Fin (n + 1), c.1 ≠ x k := by
    intro k hk
    exact hnone ⟨k, hk⟩
  have hleft' : x 0 < c.1 := lt_of_le_of_ne hleft (hne 0).symm
  have hright' : c.1 < x (Fin.last n) := lt_of_le_of_ne hright (hne _)
  obtain ⟨i, hi⟩ := strictMono_exists_gap x hchain.1 hleft' hright' hne
  have hdisj := filledGap_disjoint_slabFrontier hchain hboundary i
  have : c.1 ∈ Ioo (x i.castSucc) (x i.succ) ∩ frontier X := ⟨hi, c.2⟩
  simp [hdisj] at this

private theorem mapped_chain_entry_eq_boundaryHomeomorph
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    {X : Set ℝ} (B : BoundaryOrderData C φ X) (H : ℝ ≃ₜ ℝ)
    (hHe : ∀ c : ↥(frontier X), H c.1 = mapScalar φ (B.lift c))
    {n : ℕ} {x : Fin (n + 1) → ℝ}
    {xLift : Fin (n + 1) → C.coordinateSpace}
    (hxLift : ∀ k, (xLift k : ℝ) = x k)
    (c : ↥(frontier X)) {k : Fin (n + 1)} (hck : c.1 = x k) :
    H c.1 = mapScalar φ (xLift k) := by
  rw [hHe c]
  congr 1
  apply Subtype.ext
  rw [B.lift_coe c, hxLift k]
  exact hck

private theorem reconstructedBase_geometry_and_chambers :
    ∀ {C : ApproximationContext.{u}}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} {X : Set ℝ}
      (B : BoundaryOrderData C φ X) (hXo : IsOpen X)
      (hXr : interior (closure X) = X) (H : ℝ ≃ₜ ℝ), StrictMono H →
      (∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x)) →
      IsOpen (H '' X) ∧ interior (closure (H '' X)) = H '' X ∧
      frontier (H '' X) = mapScalarSet φ (Set.range B.lift) ∧
      ∀ a b : ↥(frontier X), a.1 < b.1 → Ioo a.1 b.1 ∩ frontier X = ∅ →
        (Ioo a.1 b.1 ⊆ X ↔
          Ioo (mapScalar φ (B.lift a)) (mapScalar φ (B.lift b)) ⊆ H '' X) := by
  intro C φ X B hXo hXr H hmono hformula
  refine ⟨H.isOpenMap _ hXo, ?_, ?_, ?_⟩
  · rw [← H.image_closure, ← H.image_interior, hXr]
  · rw [← H.image_frontier]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨B.lift ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, (hformula ⟨x, hx⟩).symm⟩
    · rintro ⟨z, ⟨x, rfl⟩, hz⟩
      exact ⟨x.1, x.2, by simpa [hformula x] using hz⟩
  · intro a b hab _hgap
    rw [← hformula a, ← hformula b]
    have hIoo : H '' Ioo a.1 b.1 = Ioo (H a.1) (H b.1) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hmono hx.1, hmono hx.2⟩
      · intro hy
        refine ⟨H.symm y, ?_, H.apply_symm_apply y⟩
        constructor
        · apply hmono.lt_iff_lt.mp
          simpa using hy.1
        · apply hmono.lt_iff_lt.mp
          simpa using hy.2
    rw [← hIoo]
    constructor
    · intro hsub y hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨x, hsub hx, hxy⟩
    · intro hsub x hx
      obtain ⟨z, hzX, hz⟩ := hsub ⟨x, hx, rfl⟩
      have hzx : z = x := H.injective hz
      simpa [hzx] using hzX

private theorem firstStage_selectedComplement_rawAE
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres)
    (X : Set ℝ) (hXo : IsOpen X) (_hXr : interior (closure X) = X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X})
    (B : BoundaryOrderData C φ X) (H : ℝ ≃ₜ ℝ) (hHm : StrictMono H)
    (hHe : ∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x)) :
    openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
            firstCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ H '' X} ∧
    openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
            firstCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∉ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∉ H '' X} := by
  have hmapCountable : (Set.range (mapScalar φ)).Countable := by
    apply (Set.countable_range (fun r : ℚ ↦ (r : ℝ))).mono
    rintro y ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  have hslices : ∀ᵐ q : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      let z := slicePoint Axis.horizontal q y
      (z ∈ openUnion D.firstRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
              firstCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔ y ∈ H '' X) ∧
      (z ∈ openUnion D.firstRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
              firstCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∉ S}) ↔ y ∉ H '' X) := by
    filter_upwards
        [source_selectedComplement_sliceAE hT S hS X hXo hSupport,
          ambientHorizontalSlice_dense_ae hT,
          genericSliceEndpointSet_unbounded C.region C.centres hT Axis.horizontal,
          genericSliceChain_betweenEndpoints C.region C.centres hT Axis.horizontal,
          firstStage_mappedEndpoints_order_cofinal D hT,
          firstSliceChain_transport D hT]
      with q hsource hdense hunbounded hbetween horder htransport
    obtain ⟨lift, hlift, hf, hfupper, hflower⟩ := horder
    let E := sliceEndpointSet C.region C.centres Axis.horizontal q
    let f : ↥E → ℝ := fun a ↦ mapScalar φ (lift a)
    have boundaryEndpoint (c : ↥(frontier X)) : c.1 ∈ E := by
      have hnot := slabFrontier_not_mem_ambientOpenUnion hT hS hXo hSupport c q
      change c.1 ∈ frontier {r : ℝ |
        slicePoint Axis.horizontal q r ∈ openUnion C.region C.centres}
      rw [frontier, hdense.closure_eq]
      have hopen : IsOpen {r : ℝ |
          slicePoint Axis.horizontal q r ∈ openUnion C.region C.centres} :=
        (isOpen_iUnion fun _ ↦ C.region.openCarrier_regularOpen.1.vadd _).preimage
          (by change Continuous (fun r : ℝ ↦ (r : ℂ) + (q : ℂ) * Complex.I); fun_prop)
      rw [hopen.interior_eq]
      exact ⟨mem_univ _, hnot⟩
    have hboundary (c : ↥(frontier X)) :
        slicePoint Axis.horizontal q c.1 ∉ openUnion C.region C.centres :=
      slabFrontier_not_mem_ambientOpenUnion hT hS hXo hSupport c q
    filter_upwards [hmapCountable.ae_notMem volume] with y hy
    let x₀ := H.symm y
    obtain ⟨as, hasE, has⟩ := not_bddBelow_iff.mp hunbounded.2 x₀
    obtain ⟨_, ⟨am, rfl⟩, ham⟩ := not_bddBelow_iff.mp hflower y
    obtain ⟨bs, hbsE, hbs⟩ := not_bddAbove_iff.mp hunbounded.1 x₀
    obtain ⟨_, ⟨bm, rfl⟩, hbm⟩ := not_bddAbove_iff.mp hfupper y
    let a : ↥E := min ⟨as, hasE⟩ am
    let b : ↥E := max ⟨bs, hbsE⟩ bm
    have hax : a.1 < x₀ := lt_of_le_of_lt (min_le_left _ _) has
    have hxb : x₀ < b.1 := lt_of_lt_of_le hbs (le_max_left _ _)
    have hay : f a < y := lt_of_le_of_lt (hf.monotone (min_le_right _ _)) ham
    have hyb : y < f b := lt_of_lt_of_le hbm (hf.monotone (le_max_right _ _))
    have hab : a.1 < b.1 := hax.trans hxb
    obtain ⟨n, hn, xc, owner, hx0, hxlast, hchain⟩ :=
      hbetween a.1 a.2 b.1 b.2 hab
    obtain ⟨xLift, hxLift⟩ := horizontalFilledChain_coordinateLift hn xc owner hchain
    have h0 : xLift 0 = lift a := by
      apply Subtype.ext
      simp [hxLift, hlift, hx0]
    have hlast : xLift (Fin.last n) = lift b := by
      apply Subtype.ext
      simp [hxLift, hlift, hxlast]
    have hmapped := htransport xc xLift owner hxLift hchain
    have hyne : ∀ k, y ≠ mapScalar φ (xLift k) := by
      intro k hk
      exact hy ⟨xLift k, hk.symm⟩
    obtain ⟨i, hi⟩ := strictMono_exists_gap (fun k ↦ mapScalar φ (xLift k))
      hmapped.1 (by simpa [f, h0] using hay) (by simpa [f, hlast] using hyb) hyne
    obtain ⟨r, hrI, hownerX⟩ :=
      filledGap_owner_mem_iff_of_sliceAE hT S hS hchain hsource i
    have hrx : r ∈ X ↔ x₀ ∈ X := by
      by_contra hne
      obtain ⟨c, hcF, hcBetween⟩ :=
        exists_frontier_mem_uIcc_of_membership_ne hXo hne
      let c' : ↥(frontier X) := ⟨c, hcF⟩
      have hcAB : a.1 ≤ c ∧ c ≤ b.1 := by
        rcases le_total r x₀ with hrx₀ | hx₀r
        · rw [uIcc_of_le hrx₀] at hcBetween
          have har : a.1 < r := by
            rw [← hx0]
            exact (hchain.1.monotone (Fin.zero_le _)).trans_lt hrI.1
          exact ⟨le_trans har.le hcBetween.1,
            le_trans hcBetween.2 (le_of_lt hxb)⟩
        · simp only [uIcc, min_eq_right hx₀r, max_eq_left hx₀r] at hcBetween
          have hrb : r < b.1 := by
            rw [← hxlast]
            exact hrI.2.trans_le (hchain.1.monotone (Fin.le_last _))
          exact ⟨le_trans (le_of_lt hax) hcBetween.1,
            le_trans hcBetween.2 hrb.le⟩
      obtain ⟨k, hck⟩ := slabFrontier_between_chainEndpoints_eq_entry hchain
        hboundary c' (by simpa [hx0] using hcAB.1) (by simpa [hxlast] using hcAB.2)
      have hmapc : H c = mapScalar φ (xLift k) :=
        mapped_chain_entry_eq_boundaryHomeomorph B H hHe hxLift c' hck
      rcases le_total r x₀ with hrx₀ | hx₀r
      · rw [uIcc_of_le hrx₀] at hcBetween
        have hrightc : xc i.succ ≤ c := by
          by_contra hnot
          have hcI : c ∈ Ioo (xc i.castSucc) (xc i.succ) :=
            ⟨lt_of_lt_of_le hrI.1 hcBetween.1, lt_of_not_ge hnot⟩
          have hd := filledGap_disjoint_slabFrontier hchain hboundary i
          have : c ∈ Ioo (xc i.castSucc) (xc i.succ) ∩ frontier X := ⟨hcI, hcF⟩
          simp [hd] at this
        have hik : i.succ ≤ k := hchain.1.le_iff_le.mp (by rw [← hck]; exact hrightc)
        have : y < H c := hi.2.trans_le (by simpa [hmapc] using hmapped.1.monotone hik)
        exact (not_lt_of_ge (hHm.monotone hcBetween.2) (by simpa [x₀] using this))
      · simp only [uIcc, min_eq_right hx₀r, max_eq_left hx₀r] at hcBetween
        have hcleft : c ≤ xc i.castSucc := by
          by_contra hnot
          have hcI : c ∈ Ioo (xc i.castSucc) (xc i.succ) :=
            ⟨lt_of_not_ge hnot, lt_of_le_of_lt hcBetween.2 hrI.2⟩
          have hd := filledGap_disjoint_slabFrontier hchain hboundary i
          have : c ∈ Ioo (xc i.castSucc) (xc i.succ) ∩ frontier X := ⟨hcI, hcF⟩
          simp [hd] at this
        have hki : k ≤ i.castSucc := hchain.1.le_iff_le.mp (by rw [← hck]; exact hcleft)
        have hmc : H c ≤ mapScalar φ (xLift i.castSucc) := by
          rw [hmapc]
          exact hmapped.1.monotone hki
        have : H c < y := hmc.trans_lt hi.1
        exact (not_lt_of_ge (hHm.monotone hcBetween.1) (by simpa [x₀] using this))
    have hyHX : y ∈ H '' X ↔ x₀ ∈ X := by
      constructor
      · rintro ⟨w, hw, hwy⟩
        have : w = x₀ := H.injective (hwy.trans (H.apply_symm_apply y).symm)
        simpa [this] using hw
      · intro hx
        exact ⟨x₀, hx, H.apply_symm_apply y⟩
    let z := slicePoint Axis.horizontal q y
    have hzI : z ∈ axisInterval Axis.horizontal q
        (mapScalar φ (xLift i.castSucc)) (mapScalar φ (xLift i.succ)) := by
      simp only [z, axisInterval, Set.mem_ofPred_eq, slicePoint]
      exact ⟨by simp, by simpa using hi⟩
    have hsel := firstStage_transportedGap_mem_selected_iff
      (x := xc) D hT S hmapped i hzI
    have hcomp := firstStage_transportedGap_mem_selected_iff
      (x := xc) D hT (C.centres \ S) hmapped i hzI
    have hownerComp : ((owner i : Tiling.Plane) ∈ C.centres \ S) ↔ r ∉ X := by
      simp only [Set.mem_sdiff, (owner i).2, true_and]
      exact not_congr hownerX
    have hcarrierEq : {t : ↥C.centres | (t : Tiling.Plane) ∈ C.centres \ S} =
        {t : ↥C.centres | (t : Tiling.Plane) ∉ S} := by
      ext t
      simp
    dsimp only [z]
    constructor
    · rw [hsel, hownerX, hrx, hyHX]
    · rw [← hcarrierEq, hcomp, hownerComp, not_congr hrx, not_congr hyHX]
  have hmeas : MeasurableSet {p : ℝ × ℝ |
      let z := slicePoint Axis.horizontal p.2 p.1
      (z ∈ openUnion D.firstRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
              firstCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) ↔ p.1 ∈ H '' X) ∧
      (z ∈ openUnion D.firstRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
              firstCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∉ S}) ↔ p.1 ∉ H '' X)} := by
    let U := openUnion D.firstRegion
      (deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
          firstCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S})
    let V := openUnion D.firstRegion
      (deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
          firstCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∉ S})
    let g : ℝ × ℝ → Tiling.Plane := fun p ↦ slicePoint Axis.horizontal p.2 p.1
    have hg : Continuous g := by
      change Continuous (fun p : ℝ × ℝ ↦ (p.1 : ℂ) + (p.2 : ℂ) * Complex.I)
      fun_prop
    have hU : IsOpen U :=
      isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _
    have hV : IsOpen V :=
      isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _
    have hHX : IsOpen (H '' X) := H.isOpenMap X hXo
    exact ((hU.preimage hg).measurableSet.iff
      (hHX.preimage continuous_fst).measurableSet).inter
      ((hV.preimage hg).measurableSet.iff
        (hHX.measurableSet.compl.preimage continuous_fst.measurable))
  have hxy := (MeasureTheory.Measure.ae_ae_comm hmeas).mpr hslices
  have hprod := (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).2 hxy
  have hplane :=
    Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
  constructor
  · filter_upwards [hplane] with z hz
    have heq : slicePoint Axis.horizontal
        (Complex.measurableEquivRealProd z).2 (Complex.measurableEquivRealProd z).1 = z := by
      apply Complex.ext <;> simp [slicePoint]
    apply propext
    constructor
    · intro h
      exact hz.1.mp (heq.symm ▸ h)
    · intro h
      exact heq ▸ hz.1.mpr h
  · filter_upwards [hplane] with z hz
    have heq : slicePoint Axis.horizontal
        (Complex.measurableEquivRealProd z).2 (Complex.measurableEquivRealProd z).1 = z := by
      apply Complex.ext <;> simp [slicePoint]
    apply propext
    constructor
    · intro h
      exact hz.2.mp (heq.symm ▸ h)
    · intro h
      exact heq ▸ hz.2.mpr h

private theorem reconstructedBase_firstStage_support
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres)
    (X : Set ℝ) (hXo : IsOpen X) (hXr : interior (closure X) = X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X})
    (B : BoundaryOrderData C φ X) (H : ℝ ≃ₜ ℝ) (hHm : StrictMono H)
    (hHe : ∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x)) :
    regularSupport D.firstRegion
      (deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
          firstCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) = {z | z.re ∈ H '' X} := by
  let A := deformedCenterCarrierOn
    ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
      firstCenter_formula_injective D hT⟩
    {t : ↥C.centres | (t : Tiling.Plane) ∈ S}
  let U := openUnion D.firstRegion A
  have hopenU : IsOpen U :=
    isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _
  have hregSupport : interior (closure (regularSupport D.firstRegion A)) =
      regularSupport D.firstRegion A := by
    apply le_antisymm
    · change interior (closure (interior (closure U))) ⊆ interior (closure U)
      apply interior_mono
      simpa only [closure_closure] using
        (closure_mono (interior_subset : interior (closure U) ⊆ closure U))
    · exact interior_maximal subset_closure isOpen_interior
  obtain ⟨hHXopen, hHXreg, _⟩ :=
    reconstructedBase_geometry_and_chambers B hXo hXr H hHm hHe
  have haeRaw := (firstStage_selectedComplement_rawAE D hT S hS X hXo hXr
    hSupport B H hHm hHe).1
  have hpack : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
      (D.firstRegion.toPolygonalRegion.placements A) := by
    let E : ↥C.centres ↪ Tiling.Plane :=
      ⟨fun t ↦ mapFirstPoint φ (C.centrePoint t.1 t.2),
        firstCenter_formula_injective D hT⟩
    have hpackE : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
        (D.firstRegion.toPolygonalRegion.placements (deformedCenterCarrier E)) := by
      apply (isPacking_iff_openCarrier_disjoint D.firstRegion
        (deformedCenterCarrier E)).2
      intro a ha b hb hab
      obtain ⟨s, rfl⟩ := ha
      obtain ⟨t, rfl⟩ := hb
      apply Set.disjoint_left.2
      intro z hzs hzt
      apply hab
      apply congrArg E
      exact firstTranslatedInteriors_overlap_reflect D hT s t ⟨z, hzs, hzt⟩
    apply (isPacking_iff_openCarrier_disjoint D.firstRegion A).2
    intro a ha b hb hab
    obtain ⟨s, hs, hsa⟩ := ha
    obtain ⟨t, ht, htb⟩ := hb
    apply (isPacking_iff_openCarrier_disjoint D.firstRegion
      (deformedCenterCarrier E)).1 hpackE
    · exact ⟨s, hsa⟩
    · exact ⟨t, htb⟩
    · exact hab
  have hae : regularSupport D.firstRegion A =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ H '' X} :=
    (openUnion_aeEq_regularSupport hpack).symm.trans haeRaw
  apply regularOpen_eq_of_aeEq isOpen_interior hregSupport
    (hHXopen.preimage Complex.continuous_re)
  · change interior (closure (Complex.re ⁻¹' (H '' X))) = Complex.re ⁻¹' (H '' X)
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hHXreg]
  · exact hae

private theorem complement_rawAE_of_tilesOn_selected_rawAE
    {K : Region} {T S : Set Tiling.Plane} (hT : TilesOn K T univ)
    (hS : S ⊆ T) {Y : Set Tiling.Plane}
    (hsel : openUnion K S =ᵐ[volume] Y) :
    openUnion K (T \ S) =ᵐ[volume] Yᶜ := by
  filter_upwards [hT.2.2, hsel] with z hamb hzSel
  simp only [mem_univ, true_iff] at hamb
  apply propext
  constructor
  · intro hzDiff hzY
    change z ∈ openUnion K (T \ S) at hzDiff
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzDiff
    obtain ⟨t, hzt⟩ := hzDiff
    have hzS : z ∈ openUnion K S := hzSel.mpr hzY
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at hzS
    obtain ⟨s, hzs⟩ := hzS
    have heq : t.1 = s.1 := by
      by_contra hne
      exact Set.disjoint_left.1
        ((isPacking_iff_openCarrier_disjoint K T).1 hT.2.1
          t.2.1 (hS s.2) hne) hzt hzs
    exact t.2.2 (heq ▸ s.2)
  · intro hzNot
    obtain ⟨t, hzt⟩ := hamb
    by_cases htS : t.1 ∈ S
    · exact False.elim (hzNot (hzSel.mp (by
        change z ∈ openUnion K S
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        exact ⟨⟨t.1, htS⟩, hzt⟩)))
    · change z ∈ openUnion K (T \ S)
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      exact ⟨⟨t.1, t.2, htS⟩, hzt⟩

private theorem isOpen_eq_empty_of_ae_notMem_real {U : Set ℝ}
    (hU : IsOpen U) (hae : ∀ᵐ x : ℝ ∂volume, x ∉ U) : U = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨y, hy, hyGood⟩ := exists_mem_Ioo_of_ae_real
    (show x - ε / 2 < x + ε / 2 by linarith) hae
  apply hyGood
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

private theorem secondStage_selectedVerticalSlices
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (P : SecondStageTransportData C φ D)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) (Xφ : Set ℝ)
    (hFirst : openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2), P.firstInjective⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ Xφ}) :
    ∀ᵐ r : ℝ ∂volume,
      (r ∈ Xφ → ∀ᵐ y : ℝ ∂volume,
        (r : ℂ) + (y : ℂ) * Complex.I ∈ openUnion D.deformedRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
              fullCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S})) ∧
      (r ∉ Xφ → ∀ᵐ y : ℝ ∂volume,
        (r : ℂ) + (y : ℂ) * Complex.I ∉ openUnion D.deformedRegion
          (deformedCenterCarrierOn
            ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
              fullCenter_formula_injective D hT⟩
            {t : ↥C.centres | (t : Tiling.Plane) ∈ S})) := by
  let E : ↥C.centres ↪ Tiling.Plane :=
    ⟨fun t ↦ mapFirstPoint φ (C.centrePoint t.1 t.2), P.firstInjective⟩
  let A := deformedCenterCarrierOn E {t : ↥C.centres | (t : Tiling.Plane) ∈ S}
  let T₁ := deformedCenterCarrier E
  have hAsub : A ⊆ T₁ := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hcompAE := complement_rawAE_of_tilesOn_selected_rawAE P.firstTiles hAsub hFirst
  have hcompSet : T₁ \ A =
      deformedCenterCarrierOn E {t : ↥C.centres | (t : Tiling.Plane) ∉ S} := by
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, hz⟩
      refine ⟨t, ?_, rfl⟩
      intro htS
      exact hz ⟨t, htS, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      rintro ⟨s, hs, hEq⟩
      exact ht (congrArg Subtype.val (E.injective hEq.symm) ▸ hs)
  change openUnion D.firstRegion (T₁ \ A) =ᵐ[volume]
    ({z : Tiling.Plane | z.re ∈ Xφ})ᶜ at hcompAE
  rw [hcompSet] at hcompAE
  have hFirstPair :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hFirst
  have hCompPair :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hcompAE
  have hFirstSlices := MeasureTheory.Measure.ae_ae_of_ae_prod hFirstPair
  have hCompSlices := MeasureTheory.Measure.ae_ae_of_ae_prod hCompPair
  filter_upwards [hFirstSlices, hCompSlices, secondStage_slice_exhaustion D hT P]
    with r hrS hrC htarget
  have hopenS : IsOpen {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈
      openUnion D.firstRegion A} :=
    (isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _).preimage
      (by fun_prop)
  have hopenC : IsOpen {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈
      openUnion D.firstRegion (deformedCenterCarrierOn E
        {t : ↥C.centres | (t : Tiling.Plane) ∉ S})} :=
    (isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _).preimage
      (by fun_prop)
  constructor
  · intro hrX
    have hCempty : {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈
        openUnion D.firstRegion (deformedCenterCarrierOn E
          {t : ↥C.centres | (t : Tiling.Plane) ∉ S})} = ∅ := by
      apply isOpen_eq_empty_of_ae_notMem_real hopenC
      filter_upwards [hrC] with y hy
      have heq : Complex.measurableEquivRealProd.symm (r, y) =
          (r : ℂ) + (y : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [heq] at hy
      intro h
      have h' := hy.mp h
      change ((r : ℂ) + (y : ℂ) * Complex.I).re ∉ Xφ at h'
      have hrNot' : r ∉ Xφ := by simpa using h'
      exact hrNot' hrX
    filter_upwards [htarget] with y hy
    obtain ⟨t, htz⟩ := hy
    have htS : (t : Tiling.Plane) ∈ S := by
      by_contra ht
      have hsource := secondSourcePoint_mem D t ((r : ℂ) + (y : ℂ) * Complex.I) htz
      have : (secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I)).im ∈
          {u : ℝ | (r : ℂ) + (u : ℂ) * Complex.I ∈
            openUnion D.firstRegion (deformedCenterCarrierOn E
              {s : ↥C.centres | (s : Tiling.Plane) ∉ S})} := by
        change _ ∈ openUnion D.firstRegion _
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
        refine ⟨⟨E t, t, ht, rfl⟩, ?_⟩
        have hwEq : (r : ℂ) +
            ((secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I)).im : ℂ) *
              Complex.I = secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I) := by
          apply Complex.ext
          · simp [secondSourcePoint_re]
          · simp
        rw [hwEq]
        simpa [E] using hsource
      simp [hCempty] at this
    change _ ∈ openUnion D.deformedRegion _
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
    exact ⟨⟨mapPoint φ (C.centrePoint t.1 t.2), t, htS, rfl⟩, htz⟩
  · intro hrNot
    have hSempty : {y : ℝ | (r : ℂ) + (y : ℂ) * Complex.I ∈
        openUnion D.firstRegion A} = ∅ := by
      apply isOpen_eq_empty_of_ae_notMem_real hopenS
      filter_upwards [hrS] with y hy
      have heq : Complex.measurableEquivRealProd.symm (r, y) =
          (r : ℂ) + (y : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [heq] at hy
      intro h
      have h' := hy.mp h
      change ((r : ℂ) + (y : ℂ) * Complex.I).re ∈ Xφ at h'
      exact hrNot (by simpa using h')
    filter_upwards [] with y
    intro htargetS
    change _ ∈ openUnion D.deformedRegion _ at htargetS
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion] at htargetS
    obtain ⟨z, hz⟩ := htargetS
    obtain ⟨t, htS, htEq⟩ := z.2
    have htz : (r : ℂ) + (y : ℂ) * Complex.I ∈
        mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier := by
      rw [← htEq] at hz
      exact hz
    have hsource := secondSourcePoint_mem D t ((r : ℂ) + (y : ℂ) * Complex.I)
      htz
    have : (secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I)).im ∈
        {u : ℝ | (r : ℂ) + (u : ℂ) * Complex.I ∈ openUnion D.firstRegion A} := by
      change _ ∈ openUnion D.firstRegion A
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, mem_iUnion]
      refine ⟨⟨E t, t, htS, rfl⟩, ?_⟩
      have hwEq : (r : ℂ) +
          ((secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I)).im : ℂ) *
            Complex.I = secondSourcePoint D t ((r : ℂ) + (y : ℂ) * Complex.I) := by
        apply Complex.ext
        · simp [secondSourcePoint_re]
        · simp
      rw [hwEq]
      simpa [E] using hsource
    simp [hSempty] at this

private theorem secondStage_selected_rawAE
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (P : SecondStageTransportData C φ D)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres) (Xφ : Set ℝ)
    (hFirst : openUnion D.firstRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2), P.firstInjective⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ Xφ}) :
    openUnion D.deformedRegion
        (deformedCenterCarrierOn
          ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
            fullCenter_formula_injective D hT⟩
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ Xφ} := by
  let U := openUnion D.firstRegion
    (deformedCenterCarrierOn
      ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2), P.firstInjective⟩
      {t : ↥C.centres | (t : Tiling.Plane) ∈ S})
  let V := openUnion D.deformedRegion
    (deformedCenterCarrierOn
      ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
        fullCenter_formula_injective D hT⟩
      {t : ↥C.centres | (t : Tiling.Plane) ∈ S})
  have hUpair := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hFirst
  have hUslices := MeasureTheory.Measure.ae_ae_of_ae_prod hUpair
  have hVslices := secondStage_selectedVerticalSlices D hT P S hS Xφ hFirst
  have hiter : ∀ᵐ r : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      ((r : ℂ) + (y : ℂ) * Complex.I ∈ V ↔
        (r : ℂ) + (y : ℂ) * Complex.I ∈ U) := by
    filter_upwards [hUslices, hVslices] with r hrU hrV
    by_cases hrX : r ∈ Xφ
    · filter_upwards [hrU, hrV.1 hrX] with y hyU hyV
      have heq : Complex.measurableEquivRealProd.symm (r, y) =
          (r : ℂ) + (y : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [heq] at hyU
      constructor <;> intro
      · apply hyU.mpr
        change ((r : ℂ) + (y : ℂ) * Complex.I).re ∈ Xφ
        simpa using hrX
      · exact hyV
    · filter_upwards [hrU, hrV.2 hrX] with y hyU hyV
      have heq : Complex.measurableEquivRealProd.symm (r, y) =
          (r : ℂ) + (y : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [heq] at hyU
      constructor
      · exact fun h ↦ False.elim (hyV h)
      · intro h
        have : r ∈ Xφ := by
          have := hyU.mp h
          change ((r : ℂ) + (y : ℂ) * Complex.I).re ∈ Xφ at this
          simpa using this
        exact False.elim (hrX this)
  have hmeas : MeasurableSet {p : ℝ × ℝ |
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ V ↔
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ U} := by
    let g : ℝ × ℝ → Tiling.Plane := fun p ↦
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
    have hg : Continuous g := by fun_prop
    have hUopen : IsOpen U :=
      isOpen_iUnion fun _ ↦ D.firstRegion.openCarrier_regularOpen.1.vadd _
    have hVopen : IsOpen V :=
      isOpen_iUnion fun _ ↦ D.deformedRegion.openCarrier_regularOpen.1.vadd _
    exact (hVopen.preimage hg).measurableSet.iff (hUopen.preimage hg).measurableSet
  have hprod := (MeasureTheory.Measure.ae_prod_iff_ae_ae hmeas).2 hiter
  have hplane := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
  have hVU : V =ᵐ[volume] U := by
    filter_upwards [hplane] with z hz
    have heq : ((Complex.measurableEquivRealProd z).1 : ℂ) +
        ((Complex.measurableEquivRealProd z).2 : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp
    apply propext
    rw [heq] at hz
    exact hz
  exact hVU.trans hFirst

private theorem reconstructedBase_secondStage_support
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres)
    (X : Set ℝ) (hXo : IsOpen X) (hXr : interior (closure X) = X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X})
    (B : BoundaryOrderData C φ X) (H : ℝ ≃ₜ ℝ) (hHm : StrictMono H)
    (hHe : ∀ x : ↥(frontier X), H x.1 = mapScalar φ (B.lift x)) :
    regularSupport D.deformedRegion
      (deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
          fullCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) = {z | z.re ∈ H '' X} := by
  let P := (secondStageTransportData_exists D hT).some
  let A := deformedCenterCarrierOn
    ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
      fullCenter_formula_injective D hT⟩
    {t : ↥C.centres | (t : Tiling.Plane) ∈ S}
  let U := openUnion D.deformedRegion A
  have hFirst := (firstStage_selectedComplement_rawAE D hT S hS X hXo hXr
    hSupport B H hHm hHe).1
  have hFirstP : openUnion D.firstRegion
      (deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapFirstPoint φ (C.centrePoint t.1 t.2), P.firstInjective⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ H '' X} := by
    simpa only [] using hFirst
  have haeRaw := secondStage_selected_rawAE D hT P S hS (H '' X) hFirstP
  have hpackFull := (secondStage_tilesOn D hT P).2.1
  have hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements A) := by
    apply (isPacking_iff_openCarrier_disjoint D.deformedRegion A).2
    intro a ha b hb hab
    obtain ⟨s, hs, hsa⟩ := ha
    obtain ⟨t, ht, htb⟩ := hb
    apply (isPacking_iff_openCarrier_disjoint D.deformedRegion
      (Set.range (fun u : ↥C.centres ↦ mapPoint φ (C.centrePoint u.1 u.2)))).1 hpackFull
    · exact ⟨s, hsa⟩
    · exact ⟨t, htb⟩
    · exact hab
  have hae : regularSupport D.deformedRegion A =ᵐ[volume]
      {z : Tiling.Plane | z.re ∈ H '' X} :=
    (openUnion_aeEq_regularSupport hpack).symm.trans haeRaw
  obtain ⟨hHXopen, hHXreg, _⟩ :=
    reconstructedBase_geometry_and_chambers B hXo hXr H hHm hHe
  have hregSupport : interior (closure (regularSupport D.deformedRegion A)) =
      regularSupport D.deformedRegion A := by
    apply le_antisymm
    · change interior (closure (interior (closure U))) ⊆ interior (closure U)
      apply interior_mono
      simpa only [closure_closure] using
        (closure_mono (interior_subset : interior (closure U) ⊆ closure U))
    · exact interior_maximal subset_closure isOpen_interior
  apply regularOpen_eq_of_aeEq isOpen_interior hregSupport
    (hHXopen.preimage Complex.continuous_re)
  · change interior (closure (Complex.re ⁻¹' (H '' X))) = Complex.re ⁻¹' (H '' X)
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hHXreg]
  · exact hae

theorem coordinateDeformation_subfamilySupport
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C φ}
    (P : TwoStageDeformationSupportTransport C φ D) (S : Set Tiling.Plane)
    (hS : S ⊆ C.centres) (X : Set ℝ) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (hSupport : regularSupport C.region S = {z : Tiling.Plane | z.re ∈ X}) :
    ∃ (Xφ : Set ℝ) (boundaryLift : ↥(frontier X) → C.coordinateSpace),
      IsOpen Xφ ∧ interior (closure Xφ) = Xφ ∧
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧
      regularSupport D.deformedRegion
        (deformedCenterCarrierOn P.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) = {z | z.re ∈ Xφ} ∧
      frontier Xφ = mapScalarSet φ (Set.range boundaryLift) ∧
      ∀ a b : ↥(frontier X), a.1 < b.1 → Ioo a.1 b.1 ∩ frontier X = ∅ →
        (Ioo a.1 b.1 ⊆ X ↔ Ioo (mapScalar φ (boundaryLift a))
          (mapScalar φ (boundaryLift b)) ⊆ Xφ) := by
  let hT := P.source_tilesOn
  let B := (boundaryOrderData_exists D hT S hS X hXopen hXregular hSupport).some
  obtain ⟨H, hHm, hHe⟩ := exists_boundaryHomeomorph B
  obtain ⟨hopen, hregular, hfrontier, hchambers⟩ :=
    reconstructedBase_geometry_and_chambers B hXopen hXregular H hHm hHe
  have hsupportMap := reconstructedBase_secondStage_support D hT S hS X hXopen
    hXregular hSupport B H hHm hHe
  have hcentres : deformedCenterCarrierOn P.fullCenters
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} =
      deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
          fullCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} := by
    ext z
    constructor <;> rintro ⟨t, ht, rfl⟩
    · exact ⟨t, ht, (P.fullCenters_apply t).symm⟩
    · exact ⟨t, ht, P.fullCenters_apply t⟩
  refine ⟨H '' X, B.lift, hopen, hregular, B.lift_coe, ?_, hfrontier, ?_⟩
  · rw [hcentres]
    exact hsupportMap
  · exact hchambers

theorem coordinateDeformation_subfamilySupport_homeomorph
    {C : ApproximationContext.{u}} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (S : Set Tiling.Plane) (hS : S ⊆ C.centres)
    (X : Set ℝ) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (hSupport : regularSupport C.region S = Complex.re ⁻¹' X) :
    ∃ (boundaryLift : ↥(frontier X) → C.coordinateSpace) (H : ℝ ≃ₜ ℝ),
      (∀ x, (boundaryLift x : ℝ) = x.1) ∧ StrictMono H ∧
      (∀ x : ↥(frontier X), H x.1 = mapScalar phi (boundaryLift x)) ∧
      regularSupport D.deformedRegion
        (deformedCenterCarrierOn P.fullCenters
          {t : ↥C.centres | (t : Tiling.Plane) ∈ S}) = Complex.re ⁻¹' (H '' X) := by
  let hT := P.source_tilesOn
  let B := (boundaryOrderData_exists D hT S hS X hXopen hXregular hSupport).some
  obtain ⟨H, hHm, hHe⟩ := exists_boundaryHomeomorph B
  have hsupportMap := reconstructedBase_secondStage_support D hT S hS X hXopen
    hXregular hSupport B H hHm hHe
  have hcentres : deformedCenterCarrierOn P.fullCenters
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} =
      deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapPoint phi (C.centrePoint t.1 t.2),
          fullCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} := by
    ext z
    constructor <;> rintro ⟨t, ht, rfl⟩
    · exact ⟨t, ht, (P.fullCenters_apply t).symm⟩
    · exact ⟨t, ht, P.fullCenters_apply t⟩
  refine ⟨B.lift, H, B.lift_coe, hHm, hHe, ?_⟩
  rw [hcentres]
  exact hsupportMap

theorem exists_twoStageDeformationSupportTransport
    (C : ApproximationContext.{u}) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C φ) (hT : TilesOn C.region C.centres univ) :
    Nonempty (TwoStageDeformationSupportTransport C φ D) := by
  obtain ⟨firstCenters, hfirstApply, hfirstTiles⟩ := firstCoordinateDeformation_tilesOn D hT
  obtain ⟨fullCenters, hfullApply, hfullTiles⟩ := coordinateDeformation_tilesOn D hT
  refine ⟨{
    source_tilesOn := hT
    firstCenters := firstCenters
    fullCenters := fullCenters
    firstCenters_apply := hfirstApply
    fullCenters_apply := hfullApply
    first_tilesOn := hfirstTiles
    full_tilesOn := hfullTiles
    first_locallyFinite :=
      deformedSingletonFamily_locallyFinite D.firstRegion firstCenters hfirstTiles
    full_locallyFinite :=
      deformedSingletonFamily_locallyFinite D.deformedRegion fullCenters hfullTiles
    subfamily_support := ?_ }⟩
  intro S hS X hXopen hXregular hSupport
  let B := (boundaryOrderData_exists D hT S hS X hXopen hXregular hSupport).some
  obtain ⟨H, hHm, hHe⟩ := exists_boundaryHomeomorph B
  obtain ⟨hopen, hregular, _⟩ :=
    reconstructedBase_geometry_and_chambers B hXopen hXregular H hHm hHe
  have hsupportMap := reconstructedBase_secondStage_support D hT S hS X hXopen
    hXregular hSupport B H hHm hHe
  have hcentres : deformedCenterCarrierOn fullCenters
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} =
      deformedCenterCarrierOn
        ⟨fun t : ↥C.centres ↦ mapPoint φ (C.centrePoint t.1 t.2),
          fullCenter_formula_injective D hT⟩
        {t : ↥C.centres | (t : Tiling.Plane) ∈ S} := by
    ext z
    constructor <;> rintro ⟨t, ht, rfl⟩
    · exact ⟨t, ht, (hfullApply t).symm⟩
    · exact ⟨t, ht, hfullApply t⟩
  refine ⟨H '' X, hopen, hregular, ?_⟩
  rw [hcentres]
  exact hsupportMap


end

end Tiling.AxisParallel.Approximation
