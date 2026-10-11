import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry

import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.RationalSlabPeriodicity
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodConsequences

import Mathlib.Data.Finset.Card
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Topology.HullCore

import Tiling.AxisParallel.Foundations.QuadrantGermGeometry
import Tiling.AxisParallel.Structure.HorizontalComplexityCharacterization.BoundaryDensity

set_option linter.style.header false

open Set

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- A horizontal fibre which persists in a translated orbit limit. -/
structure PersistentHorizontalFibreData
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (source : Tiling.AxisParallel.Topology.TilingSpace C.region Set.univ) where
  source_centres_eq : (source.centres : Set Tiling.Plane) = C.centres
  limit : Tiling.AxisParallel.Topology.TilingSpace C.region Set.univ
  limit_mem_hull : limit ∈ Tiling.AxisParallel.Topology.orbitHull source
  translations : ℕ → Tiling.AxisParallel.aePeriodGroup Set.univ
  converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence translations source))
    (limit.centres : Set Tiling.Plane)
  anchor : Tiling.Plane
  anchor_mem_context : anchor ∈ C.centres
  movingCentre : ℕ → Tiling.Plane
  movingCentre_mem_context : ∀ n : ℕ, movingCentre n ∈ C.centres
  translations_eq : ∀ n : ℕ,
    (translations n : Tiling.Plane) = anchor - movingCentre n
  fibre : Set Tiling.Plane
  fibre_eq : fibre =
    (limit.centres : Set Tiling.Plane) ∩ {z : Tiling.Plane | z.im = anchor.im}
  anchor_mem_fibre : anchor ∈ fibre
  horizontalPlate : Tiling.AxisParallel.Continuous.VerticalPlate
    C.region.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' (limit.centres : Set Tiling.Plane))
  horizontalPlate_isColumn :
    Tiling.AxisParallel.Continuous.IsVerticalColumn horizontalPlate
  horizontalPlate_centres : horizontalPlate.centres =
    Tiling.AxisParallel.coordinateSwap '' fibre
  persistent_pullback : ∀ s ∈ fibre, ∀ᶠ n : ℕ in Filter.atTop,
    s - (translations n : Tiling.Plane) ∈ C.centres

/-- Quantitative order data for the deformed image of a persistent horizontal fibre. -/
structure HorizontalColumnOrderData
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    {source : Tiling.AxisParallel.Topology.TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) where
  coordinateLift : ↑H.fibre →
    {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}
  coordinateLift_coe : ∀ s : ↑H.fibre,
    (coordinateLift s : Tiling.Plane) = s.1
  image : ↑H.fibre ↪ Tiling.Plane
  image_apply : ∀ s : ↑H.fibre,
    image s = Tiling.AxisParallel.Approximation.mapPoint phi (coordinateLift s)
  lambda : ℝ
  Lambda : ℝ
  lambda_pos : 0 < lambda
  lambda_le_Lambda : lambda ≤ Lambda
  horizontal_bounds : ∀ s t : ↑H.fibre, s.1.re < t.1.re →
    lambda * (t.1.re - s.1.re) ≤ (image t).re - (image s).re ∧
      (image t).re - (image s).re ≤ Lambda * (t.1.re - s.1.re)
  common_secondCoordinate : ∀ s t : ↑H.fibre,
    (image s).im = (image t).im

private def liesInFiniteQuadrant
    (x z : Tiling.Plane) (q : Fin 2 × Fin 2) : Prop :=
  (if q.1 = 1 then x.re < z.re else z.re < x.re) ∧
    (if q.2 = 1 then x.im < z.im else z.im < x.im)

/-- The four-bit local occupancy germ of a planar set at a point. -/
noncomputable def finiteQuadrantGerm
    (D : Set Tiling.Plane) (x : Tiling.Plane) : Finset (Fin 2 × Fin 2) := by
  classical
  exact Finset.univ.filter fun q ↦
    ∃ r : ℝ, 0 < r ∧
      ∀ z : Tiling.Plane,
        z ∈ Metric.ball x r → liesInFiniteQuadrant x z q → z ∈ D

/-- Orbit-limit data for a horizontal column after coordinate deformation. -/
structure HorizontalColumnOrbitLimitData
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    {source : Tiling.AxisParallel.Topology.TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (O : HorizontalColumnOrderData C H phi) where
  deformedSource : Tiling.AxisParallel.Topology.TilingSpace D.deformedRegion Set.univ
  deformedSource_centres : (deformedSource.centres : Set Tiling.Plane) =
    Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  translations : ℕ → Tiling.AxisParallel.aePeriodGroup Set.univ
  translations_eq : ∀ n : ℕ,
    (translations n : Tiling.Plane) =
      P.fullCenters ⟨H.anchor, H.anchor_mem_context⟩ -
        P.fullCenters ⟨H.movingCentre (subsequence n),
          H.movingCentre_mem_context (subsequence n)⟩
  limit : Tiling.AxisParallel.Topology.TilingSpace D.deformedRegion Set.univ
  limit_mem_hull : limit ∈ Tiling.AxisParallel.Topology.orbitHull deformedSource
  converges : Tiling.AxisParallel.Topology.LocallyFellConverges
    (Tiling.AxisParallel.Topology.TilingSpace.centresSequence
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence translations
        deformedSource)) (limit.centres : Set Tiling.Plane)
  rowImage_subset : Set.range O.image ⊆ (limit.centres : Set Tiling.Plane)
  rowImage_eventuallyMem : ∀ s : ↑H.fibre, ∀ᶠ n : ℕ in Filter.atTop,
    O.image s ∈
      ((Tiling.AxisParallel.Topology.TilingSpace.translate
        (translations n) deformedSource).centres : Set Tiling.Plane)
  horizontalColumn : Tiling.AxisParallel.Continuous.VerticalPlate
    D.deformedRegion.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' (limit.centres : Set Tiling.Plane))
  horizontalColumn_isColumn :
    Tiling.AxisParallel.Continuous.IsVerticalColumn horizontalColumn
  horizontalColumn_centres : horizontalColumn.centres =
    Tiling.AxisParallel.coordinateSwap '' Set.range O.image
  horizontalColumn_support : horizontalColumn.support =
    Complex.re ⁻¹' horizontalColumn.base

/-- A translated orbit limit containing both a horizontal and a vertical column. -/
structure SimultaneousColumnsLimitData
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    {source : Tiling.AxisParallel.Topology.TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (O : HorizontalColumnOrderData C H phi) where
  horizontal : HorizontalColumnOrbitLimitData C H phi D P O
  verticalColumn : Tiling.AxisParallel.Continuous.VerticalPlate
    D.deformedRegion (horizontal.limit.centres : Set Tiling.Plane)
  verticalColumn_isColumn :
    Tiling.AxisParallel.Continuous.IsVerticalColumn verticalColumn
  verticalColumn_support : verticalColumn.support =
    Complex.re ⁻¹' verticalColumn.base

end Tiling.AxisParallel.Structure


open scoped Pointwise Topology

namespace Tiling.AxisParallel.Structure

open MeasureTheory Set Filter
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval
open Tiling.AxisParallel.OneDimensional.ColumnSlices
open Tiling.RationalPolygonal

private theorem verticalPlate_centres_subset_local
    {K : Region} {T : Set Plane} (P : VerticalPlate K T) :
    P.centres ⊆ T := by
  rintro _ ⟨t, _ht, rfl⟩
  exact t.2

private theorem region_eq_of_support_eq_local {K L : Region}
    (h : K.support = L.support) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      simp only [Region.mk.injEq]
      cases K with
      | mk Ks Kp Kn =>
        cases L with
        | mk Ls Lp Ln =>
          simpa only [Tiling.RationalPolygonal.PolygonalRegion.mk.injEq] using h

private theorem tilesOn_regularSupport_of_subset_local
    {K : Region} {S T E : Set Plane}
    (hST : S ⊆ T) (hTile : TilesOn K T E) :
    TilesOn K S (regularSupport K S) := by
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    intro s hs t ht hst
    exact hTile.2.1 (hST hs) (hST ht) hst
  refine ⟨hTile.1.mono hST, hpacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpacking] with x hx
  exact (Iff.of_eq hx.symm).trans (by
    change x ∈ (⋃ s : S, (s : Plane) +ᵥ K.openCarrier) ↔
      ∃ s : S, x ∈ (s : Plane) +ᵥ K.openCarrier
    exact Set.mem_iUnion)

private theorem coordinateSwap_smul_real_local (a : ℝ) :
    coordinateSwap (a : ℂ) = (a : ℂ) * Complex.I := by
  apply Complex.ext <;> simp

private theorem fibre_tilesOnRegularSupport
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) :
    TilesOn C.region H.fibre
      (regularSupport C.region H.fibre) := by
  have hSwapTiles :
      TilesOn C.region.coordinateSwap
        (coordinateSwap '' (H.limit.centres : Set Plane)) Set.univ := by
    simpa using tilesOn_coordinateSwap H.limit.tilesOn
  have hSsub : H.horizontalPlate.centres ⊆
      coordinateSwap '' (H.limit.centres : Set Plane) :=
    verticalPlate_centres_subset_local H.horizontalPlate
  have hPlateTiles : TilesOn C.region.coordinateSwap
      H.horizontalPlate.centres
      (regularSupport C.region.coordinateSwap H.horizontalPlate.centres) :=
    tilesOn_regularSupport_of_subset_local hSsub hSwapTiles
  have hBack := tilesOn_coordinateSwap hPlateTiles
  have hCentres : coordinateSwap '' H.horizontalPlate.centres = H.fibre := by
    rw [H.horizontalPlate_centres]
    ext z
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
      simpa using hv
    · intro hz
      exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩,
        coordinateSwap_apply_apply z⟩
  have hSupport : regularSupport C.region.coordinateSwap H.horizontalPlate.centres =
      coordinateSwap '' regularSupport C.region H.fibre := by
    rw [H.horizontalPlate_centres]
    exact regularSupport_coordinateSwap C.region H.fibre
  have hRegion : C.region.coordinateSwap.coordinateSwap = C.region := by
    apply region_eq_of_support_eq_local
    change coordinateSwap '' (coordinateSwap '' C.region.support) = C.region.support
    exact IntrinsicVertices.coordinateSwap_image_image C.region.support
  rw [hCentres] at hBack
  rw [hSupport] at hBack
  rw [hRegion] at hBack
  simpa [IntrinsicVertices.coordinateSwap_image_image] using hBack

private theorem fibre_isHorizontalCenterColumn
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) :
    IsCenterColumn Axis.horizontal C.region H.fibre := by
  have hSwapTiles :
      TilesOn C.region.coordinateSwap
        (coordinateSwap '' (H.limit.centres : Set Plane)) Set.univ := by
    simpa using tilesOn_coordinateSwap H.limit.tilesOn
  have hSwapColumn := VerticalPlate.isCenterColumn_of_isVerticalColumn
    hSwapTiles H.horizontalPlate H.horizontalPlate_isColumn
  rcases hSwapColumn with ⟨_hpack, _hne, ⟨c, hc⟩, _hinv⟩
  have hTiles := fibre_tilesOnRegularSupport H
  refine ⟨hTiles.2.1, ?_, ?_, ?_⟩
  · exact ⟨H.anchor, H.anchor_mem_fibre⟩
  · refine ⟨c, ?_⟩
    intro z hz
    have hswap : coordinateSwap z ∈ H.horizontalPlate.centres := by
      rw [H.horizontalPlate_centres]
      exact ⟨z, hz, rfl⟩
    simpa [Axis.transverseCoord] using hc (coordinateSwap z) hswap
  · intro a
    have hInv := _hinv a
    have hSupport : regularSupport C.region.coordinateSwap H.horizontalPlate.centres =
        coordinateSwap '' regularSupport C.region H.fibre := by
      rw [H.horizontalPlate_centres]
      exact regularSupport_coordinateSwap C.region H.fibre
    rw [hSupport] at hInv
    have hImage := Tiling.AxisParallel.coordinateSwap_image_vadd
      (a : Plane) (regularSupport C.region H.fibre)
    change ((a : ℂ) * Complex.I) +ᵥ
      coordinateSwap '' regularSupport C.region H.fibre =
      coordinateSwap '' regularSupport C.region H.fibre at hInv
    have hInv' : coordinateSwap ''
          ((a : ℂ) +ᵥ regularSupport C.region H.fibre) =
        coordinateSwap '' regularSupport C.region H.fibre := by
      calc
        coordinateSwap '' ((a : ℂ) +ᵥ regularSupport C.region H.fibre) =
            coordinateSwap (a : ℂ) +ᵥ
              coordinateSwap '' regularSupport C.region H.fibre := hImage
        _ = ((a : ℂ) * Complex.I) +ᵥ
              coordinateSwap '' regularSupport C.region H.fibre := by
          rw [coordinateSwap_smul_real_local]
        _ = coordinateSwap '' regularSupport C.region H.fibre := hInv
    change (a : ℂ) +ᵥ regularSupport C.region H.fibre =
      regularSupport C.region H.fibre
    exact (Set.image_eq_image coordinateSwap.injective).mp hInv'

private theorem sourceRow_genericSections_lineTile
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) (y : ℝ)
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (hny : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty) :
    OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre) := by
  have hSwapTiles :
      TilesOn C.region.coordinateSwap
        (coordinateSwap '' (H.limit.centres : Set Plane)) Set.univ := by
    simpa using tilesOn_coordinateSwap H.limit.tilesOn
  have hSwapColumn := VerticalPlate.isCenterColumn_of_isVerticalColumn
    hSwapTiles H.horizontalPlate H.horizontalPlate_isColumn
  have hSwapColumn' : IsCenterColumn Axis.vertical C.region.coordinateSwap
      (coordinateSwap '' H.fibre) := by
    simpa [H.horizontalPlate_centres] using hSwapColumn
  have hSwapColumnForIff := hSwapColumn'
  rcases hSwapColumn' with ⟨hpack, hne, ⟨c, hc⟩, hinv⟩
  have hCyl : coordinateSwap '' H.fibre =
      {z : Plane | z.re = c ∧ z.im ∈ Complex.re '' H.fibre} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hwc := hc (coordinateSwap w) ⟨w, hw, rfl⟩
      refine ⟨?_, ?_⟩
      · simpa [Axis.transverseCoord] using hwc
      · exact ⟨w, hw, rfl⟩
    · rintro ⟨hzre, ⟨w, hw, hwi⟩⟩
      have hwc := hc (coordinateSwap w) ⟨w, hw, rfl⟩
      refine ⟨w, hw, ?_⟩
      apply Complex.ext
      · change w.im = z.re
        change w.im = c at hwc
        exact hwc.trans hzre.symm
      · simpa using hwi
  have hlevels :
      (C.region.coordinateSwap).vertexFinset.image Complex.re =
        C.region.vertexFinset.image Complex.im := by
    ext r
    constructor
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨v, hv, rfl⟩
      have hv' : v ∈ Tiling.vertexSet
          (coordinateSwap '' C.region.support) := by
        have hv'' : v ∈ (C.region.coordinateSwap).vertices := by
          have hvin : v ∈
              (↑(C.region.coordinateSwap.vertexFinset) : Set Plane) := hv
          rw [C.region.coordinateSwap.coe_vertexFinset] at hvin
          exact hvin
        simpa [Region.vertices, Region.coordinateSwap] using hv''
      have hv'' : v ∈ coordinateSwap '' Tiling.vertexSet C.region.support :=
        (IntrinsicVertices.coordinateSwap_vertexSet C.region.support) ▸ hv'
      rcases hv'' with ⟨w, hw, hvw⟩
      refine Finset.mem_image.mpr ⟨w, ?_, ?_⟩
      · change w ∈ (↑C.region.vertexFinset : Set Plane)
        rw [C.region.coe_vertexFinset]
        simpa [Region.vertices] using hw
      · simpa only [coordinateSwap_re] using congrArg Complex.re hvw
    · intro hr
      rcases Finset.mem_image.mp hr with ⟨w, hw, rfl⟩
      have hw' : w ∈ Tiling.vertexSet C.region.support := by
        have hw'' : w ∈ C.region.vertices := by
          have hwin : w ∈ (↑C.region.vertexFinset : Set Plane) := hw
          rw [C.region.coe_vertexFinset] at hwin
          exact hwin
        simpa [Region.vertices] using hw''
      have hv' : coordinateSwap w ∈
          Tiling.vertexSet (coordinateSwap '' C.region.support) :=
        (IntrinsicVertices.coordinateSwap_vertexSet C.region.support).symm ▸
          (show coordinateSwap w ∈ coordinateSwap '' Tiling.vertexSet C.region.support from
            ⟨w, hw', rfl⟩)
      refine Finset.mem_image.mpr ⟨coordinateSwap w, ?_, ?_⟩
      · change coordinateSwap w ∈
          (↑(C.region.coordinateSwap.vertexFinset) : Set Plane)
        rw [C.region.coordinateSwap.coe_vertexFinset]
        simpa [Region.vertices, Region.coordinateSwap] using hv'
      · simp
  have hy' : y ∉ (C.region.coordinateSwap).vertexFinset.image Complex.re := by
    intro hy'
    apply hy
    rw [← hlevels]
    exact hy'
  have hslice :
      OneDimensional.ColumnSlices.verticalSlice C.region.coordinateSwap y =
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    ext x
    change ((y : ℂ) + (x : ℂ) * Complex.I ∈
        C.region.coordinateSwap.openCarrier) ↔
      Complex.mk x y ∈ C.region.openCarrier
    rw [Tiling.AxisParallel.coordinateSwap_openCarrier]
    constructor
    · rintro ⟨z, hz, heq⟩
      have heq' : coordinateSwap ((y : ℂ) + (x : ℂ) * Complex.I) = z := by
        calc
          coordinateSwap ((y : ℂ) + (x : ℂ) * Complex.I) =
              coordinateSwap (coordinateSwap z) := congrArg coordinateSwap heq.symm
          _ = z := coordinateSwap_apply_apply z
      rw [← coordinateSwap_apply_apply (Complex.mk x y)]
      rw [show coordinateSwap (Complex.mk x y) =
          (y : ℂ) + (x : ℂ) * Complex.I by
            apply Complex.ext <;> simp]
      rw [heq']
      exact hz
    · intro hx
      refine ⟨Complex.mk x y, hx, ?_⟩
      apply Complex.ext <;> simp
  have hnonempty' :
      (OneDimensional.ColumnSlices.verticalSlice
        C.region.coordinateSwap y).Nonempty := by
    simpa [hslice] using hny
  have hline := (Tiling.AxisParallel.Foundations.centerColumn_iff_genericSlices
    (C := coordinateSwap '' H.fibre) (c := c)
    (Y := Complex.re '' H.fibre) hCyl ?_ hpack).mp hSwapColumnForIff
  · simpa [hslice] using hline y hy' hnonempty'
  · exact ⟨H.anchor.re, ⟨H.anchor, H.anchor_mem_fibre, rfl⟩⟩

private structure LabelledHorizontalSectionEndpoint
    (C : ApproximationContext) {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) (y : ℝ) where
  centre : ↑H.fibre
  relative : ℝ
  vertex : ↑C.region.vertices
  relative_eq : relative = vertex.1.re
  relative_frontier : relative ∈ frontier
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)

private def LabelledHorizontalSectionEndpoint.value
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {y : ℝ}
    (e : LabelledHorizontalSectionEndpoint C H y) : ℝ :=
  e.relative + e.centre.1.re

private def LabelledHorizontalSectionEndpoint.imageValue
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {y : ℝ}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (O : HorizontalColumnOrderData C H phi)
    (e : LabelledHorizontalSectionEndpoint C H y) : ℝ :=
  D.firstHomeomorph e.relative + (O.image e.centre).re

private theorem labelledEndpoint_coordinateLift_imageValue
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {y : ℝ}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (O : HorizontalColumnOrderData C H phi)
    (e : LabelledHorizontalSectionEndpoint C H y) :
    ∃ xLift : C.coordinateSpace,
      (xLift : ℝ) = e.value ∧
        mapScalar phi xLift = e.imageValue D O := by
  let vr : C.coordinateSpace :=
    ⟨e.relative, by
      rw [e.relative_eq]
      exact C.vertex_re_mem e.vertex.1 e.vertex.2⟩
  let tr : C.coordinateSpace :=
    ⟨(O.coordinateLift e.centre).1.re, (O.coordinateLift e.centre).2.1⟩
  let xLift : C.coordinateSpace := vr + tr
  have hrel : (vr : ℝ) = e.relative := by rfl
  have hcenter : (tr : ℝ) = e.centre.1.re := by
    change (O.coordinateLift e.centre).1.re = e.centre.1.re
    rw [show (O.coordinateLift e.centre : Plane) = e.centre.1 by
      exact O.coordinateLift_coe e.centre]
  have hxe : (xLift : ℝ) = e.value := by
    change (vr : ℝ) + (tr : ℝ) = e.relative + e.centre.1.re
    rw [hrel, hcenter]
  have hvertex : mapScalar phi vr = D.firstHomeomorph e.relative := by
    have hv := congrArg Complex.re
      (D.first_vertex_agreement e.vertex.1 e.vertex.2)
    simpa [vr, mapFirstPoint, ApproximationContext.vertexPoint,
      D.firstPlanarHomeomorph_apply, e.relative_eq] using hv.symm
  have hcentre : mapScalar phi tr = (O.image e.centre).re := by
    simpa [tr, mapPoint, mapScalar] using
      (congrArg Complex.re (O.image_apply e.centre)).symm
  refine ⟨xLift, hxe, ?_⟩
  rw [show mapScalar phi xLift = mapScalar phi vr + mapScalar phi tr by
    simp [xLift, mapScalar]]
  simp only [hvertex, hcentre, LabelledHorizontalSectionEndpoint.imageValue]

private structure FibreGapWordData
    (C : ApproximationContext) {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) where
  relativeHeight : ℝ
  slice : Set ℝ
  slice_eq : slice = Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
    C.region relativeHeight
  relativeHeight_generic : ∀ v : ↥C.region.vertices, v.1.im ≠ relativeHeight
  presentation : OneDimensional.FiniteInterval.IntervalPresentation slice
  slice_nonempty : slice.Nonempty
  endpoint : ℝ
  endpoint_mem : endpoint ∈ presentation.endpoints
  gapAlphabet : Set ℝ
  gapAlphabet_eq : gapAlphabet = presentation.gapLengths
  between : ∀ s t : ↥H.fibre, s.1.re < t.1.re →
    ∃ n : ℕ, ∃ word : Fin n → ℝ,
      (∀ i, word i ∈ gapAlphabet) ∧
      t.1.re - s.1.re = ∑ i, word i

private theorem fibreGapWordData_exists
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) :
    Nonempty (FibreGapWordData C H) := by
  obtain ⟨z, hz⟩ := C.region.isPolygonal.interior_nonempty C.region.nonempty
  change z ∈ C.region.openCarrier at hz
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (C.region.openCarrier_regularOpen.1.mem_nhds hz)
  let J : Set ℝ := Set.Ioo (z.im - ε / 2) (z.im + ε / 2)
  have hJinf : J.Infinite := by
    dsimp [J]
    exact Set.Ioo_infinite (by linarith)
  have hFfin : ((C.region.vertexFinset.image Complex.im : Finset ℝ) : Set ℝ).Finite :=
    (C.region.vertexFinset.image Complex.im).finite_toSet
  obtain ⟨y, hyJ, hy⟩ := (hJinf.sdiff hFfin).nonempty
  have hyabs : |y - z.im| < ε := by
    dsimp [J] at hyJ
    rw [abs_lt]
    constructor <;> linarith [hyJ.1, hyJ.2]
  let q : Tiling.Plane := (z.re : ℂ) + (y : ℂ) * Complex.I
  have hqball : q ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hdiff : q - z = ((y - z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [q]
    rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    exact hyabs
  have hq : q ∈ C.region.openCarrier := hball hqball
  have hslice :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y).Nonempty := by
    change ∃ x : ℝ, Complex.mk x y ∈ C.region.openCarrier
    refine ⟨z.re, ?_⟩
    have hq' : Complex.mk z.re y = q := by
      apply Complex.ext <;> simp [q]
    rw [hq']
    exact hq
  have hfinite :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_isFiniteIntervalRegion
      C.region hy
  let P := OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion hfinite
  have hvol := ColumnSlices.finiteIntervalRegion_volume_toReal_pos hfinite hslice
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hslice
  have hTile := sourceRow_genericSections_lineTile H y hy hslice
  have hyvertex : ∀ v : ↥C.region.vertices, v.1.im ≠ y := by
    intro v hv
    apply hy
    change y ∈ (C.region.vertexFinset.image Complex.im : Finset ℝ)
    apply Finset.mem_image.mpr
    refine ⟨v.1, ?_, hv⟩
    change v.1 ∈ (C.region.vertexFinset : Set Tiling.Plane)
    simpa only [C.region.coe_vertexFinset] using v.2
  refine ⟨⟨y, _, rfl, hyvertex, P, hslice, e₀, he₀, P.gapLengths, rfl, ?_⟩⟩
  intro s t hst
  let L : Set ℝ := Complex.re '' H.fibre
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P L ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top hvol
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  have hsL : s.1.re ∈ L := ⟨s.1, s.2, rfl⟩
  have htL : t.1.re ∈ L := ⟨t.1, t.2, rfl⟩
  have hsE : s.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨s.1.re, hsL, e₀, he₀, rfl⟩
  have htE : t.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨t.1.re, htL, e₀, he₀, rfl⟩
  obtain ⟨chain⟩ := OneDimensional.FiniteInterval.endpointChain_nonempty
    hlocal hsE htE (by linarith)
  let word : Fin chain.length → ℝ := fun i =>
    chain.point i.succ - chain.point i.castSucc
  refine ⟨chain.length, word, ?_, ?_⟩
  · intro i
    dsimp [word]
    exact OneDimensional.FiniteInterval.consecutive_translatedEndpoint_gap
      P hvol hTile (chain.consecutive i)
  · have htelescope := OneDimensional.FiniteInterval.endpointChain_telescope chain
    calc
      t.1.re - s.1.re = (t.1.re + e₀) - (s.1.re + e₀) := by ring
      _ = ∑ i, word i := by simpa [word] using htelescope.symm


open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.Structure
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval
open Tiling.AxisParallel.OneDimensional.ColumnSlices
open Tiling.RationalPolygonal

/-!
The transverse-column argument combines source-column transport, aggregate-support
periodicity, a fixed generic `ColumnSlices` atom, and finite normalized whole-line
tilings.  No centre-set period is inferred from an aggregate-support period.
-/

/-! A dependency-closed version of the fixed-slice record.  Its only geometric
input is the nonempty polygonal region carried by `D`; no orbit-limit data is
used. -/

private structure FixedGenericVerticalSliceData
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) where
  relativeFirstCoordinate : ℝ
  generic : relativeFirstCoordinate ∉
    D.deformedRegion.vertexFinset.image Complex.re
  slice : Set ℝ
  slice_eq : slice = verticalSlice D.deformedRegion relativeFirstCoordinate
  slice_nonempty : slice.Nonempty
  presentation : IntervalPresentation slice
  completeColumn_lineTiles : ∀ {c : ℝ} {Y : Set ℝ}, Y.Nonempty →
    IsCenterColumn Axis.vertical D.deformedRegion
      {z : Plane | z.re = c ∧ z.im ∈ Y} →
    LineTiles slice Y

private theorem fixedGenericVerticalSliceData_exists
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    Nonempty (FixedGenericVerticalSliceData D) := by
  obtain ⟨z, hz⟩ := D.deformedRegion.isPolygonal.interior_nonempty
    D.deformedRegion.nonempty
  change z ∈ D.deformedRegion.openCarrier at hz
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp
      (D.deformedRegion.openCarrier_regularOpen.1.mem_nhds hz)
  let J : Set ℝ := Set.Ioo (z.re - ε / 2) (z.re + ε / 2)
  have hJinf : J.Infinite := by
    dsimp [J]
    exact Set.Ioo_infinite (by linarith)
  have hFfin :
      ((D.deformedRegion.vertexFinset.image Complex.re : Finset ℝ) : Set ℝ).Finite :=
    (D.deformedRegion.vertexFinset.image Complex.re).finite_toSet
  obtain ⟨r, hrJ, hrgen⟩ := (hJinf.sdiff hFfin).nonempty
  have hrabs : |r - z.re| < ε := by
    dsimp [J] at hrJ
    rw [abs_lt]
    constructor <;> linarith [hrJ.1, hrJ.2]
  let q : Plane := (r : ℂ) + z.im * Complex.I
  have hqball : q ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hdiff : q - z = ((r - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [q]
    rw [hdiff, Complex.norm_real]
    exact hrabs
  have hq : q ∈ D.deformedRegion.openCarrier := hball hqball
  have hslice : (verticalSlice D.deformedRegion r).Nonempty := by
    change ∃ y : ℝ, ((r : ℂ) + (y : ℂ) * Complex.I) ∈
      D.deformedRegion.openCarrier
    exact ⟨z.im, by simpa [q] using hq⟩
  obtain ⟨hfinite, _hlocal⟩ :=
    Region.verticalSlice_finiteIntervals D.deformedRegion hrgen
  let P := IntervalPresentation.ofIsFiniteIntervalRegion hfinite
  refine ⟨{
    relativeFirstCoordinate := r
    generic := hrgen
    slice := verticalSlice D.deformedRegion r
    slice_eq := rfl
    slice_nonempty := hslice
    presentation := P
    completeColumn_lineTiles := ?_ }⟩
  intro c Y hY hColumn
  simpa [P] using
    (genericSliceTilings_of_completeColumn hY hColumn r hrgen hslice)

private structure AnchoredDeformedColumn
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} (T : Set Plane) where
  plate : VerticalPlate D.deformedRegion T
  isColumn : IsVerticalColumn plate
  anchor : Plane
  anchor_mem : anchor ∈ plate.centres
  normalized : Set Plane
  normalized_eq : normalized = -anchor +ᵥ plate.centres
  zero_mem : 0 ∈ normalized

private theorem normalizedDeformedColumns_finite
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {T : Set Plane}
    (hTile : TilesOn D.deformedRegion T Set.univ) :
    {N : Set Plane | ∃ Q : AnchoredDeformedColumn (C := C) (D := D) T,
      N = Q.normalized}.Finite := by
  obtain ⟨F⟩ := fixedGenericVerticalSliceData_exists D
  let B := F.slice
  have hBfinite : IsFiniteIntervalRegion B := F.presentation.isFiniteIntervalRegion
  have hBpositive : 0 < (volume B).toReal := by
    apply ENNReal.toReal_pos
    · exact ne_of_gt (F.presentation.isOpen.measure_pos volume F.slice_nonempty)
    · exact F.presentation.volume_ne_top
  have hfinite : {L : Set ℝ | LineTiles B L ∧ 0 ∈ L}.Finite :=
    finite_normalizedCentreSets hBfinite hBpositive
  let image : Set Plane → Set ℝ := fun N ↦ Complex.im '' N
  let Dset : Set (Set Plane) :=
    {N : Set Plane | ∃ Q : AnchoredDeformedColumn (C := C) (D := D) T,
      N = Q.normalized}
  have hNre : ∀ {N : Set Plane}, N ∈ Dset → ∀ z ∈ N, z.re = 0 := by
    rintro N ⟨Q, rfl⟩ z hz
    rw [Q.normalized_eq] at hz
    rcases hz with ⟨w, hw, rfl⟩
    obtain ⟨c, hc⟩ := Q.isColumn
    have hca := hc Q.anchor_mem
    have hwc : w.re = c := hc hw
    have hac : Q.anchor.re = c := hca
    simp [hwc, hac]
  have himage : (image '' Dset).Finite := by
    apply hfinite.subset
    rintro L ⟨N, hN, rfl⟩
    rcases hN with ⟨Q, rfl⟩
    obtain ⟨c, hc⟩ := Q.isColumn
    have hColumn : IsCenterColumn Axis.vertical D.deformedRegion Q.plate.centres :=
      VerticalPlate.isCenterColumn_of_isVerticalColumn hTile Q.plate Q.isColumn
    let Y : Set ℝ := Complex.im '' Q.plate.centres
    have hY : Y.Nonempty := by
      exact ⟨Q.anchor.im, ⟨Q.anchor, Q.anchor_mem, rfl⟩⟩
    have hshape : Q.plate.centres = {z : Plane | z.re = c ∧ z.im ∈ Y} := by
      ext z
      constructor
      · intro hz
        exact ⟨hc hz, ⟨z, hz, rfl⟩⟩
      · rintro ⟨hzre, ⟨w, hw, hwim⟩⟩
        have hzw : z = w := by
          apply Complex.ext
          · exact (hzre.trans (hc hw).symm)
          · exact hwim.symm
        simpa [hzw] using hw
    have hline : LineTiles B Y := by
      have hColumn' : IsCenterColumn Axis.vertical D.deformedRegion
          {z : Plane | z.re = c ∧ z.im ∈ Y} := by
        simpa [hshape] using hColumn
      simpa [B, F.slice_eq] using F.completeColumn_lineTiles hY hColumn'
    have hnormline : LineTiles B (Complex.im '' Q.normalized) := by
      rw [Q.normalized_eq]
      have himage_eq : Complex.im '' (-Q.anchor +ᵥ Q.plate.centres) =
          (-Q.anchor.im) +ᵥ Y := by
        ext y
        constructor
        · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
          refine ⟨w.im, ⟨w, hw, rfl⟩, ?_⟩
          simp [vadd_eq_add]
        · rintro ⟨y₀, ⟨w, hw, rfl⟩, rfl⟩
          refine ⟨-Q.anchor + w, ⟨w, hw, rfl⟩, ?_⟩
          simp [vadd_eq_add]
      rw [himage_eq]
      simpa [LineTiles] using
        Foundations.lineTilesOn_translate hline (-Q.anchor.im)
    change LineTiles B (Complex.im '' Q.normalized) ∧ 0 ∈ Complex.im '' Q.normalized
    refine ⟨hnormline, ?_⟩
    exact ⟨0, Q.zero_mem, rfl⟩
  apply Set.Finite.of_finite_image himage
  intro N hN N' hN' heq
  ext z
  constructor
  · intro hz
    have hz' : z.im ∈ image N' := by
      rw [← heq]
      exact ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwim⟩ := hz'
    have hzre : z.re = 0 := hNre hN z hz
    have hwre : w.re = 0 := hNre hN' w hw
    have hzw : z = w := by
      apply Complex.ext
      · rw [hzre, hwre]
      · exact hwim.symm
    rw [hzw]
    exact hw
  · intro hz
    have hz' : z.im ∈ image N := by
      rw [heq]
      exact ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hwim⟩ := hz'
    have hzre : z.re = 0 := hNre hN' z hz
    have hwre : w.re = 0 := hNre hN w hw
    have hzw : z = w := by
      apply Complex.ext
      · rw [hzre, hwre]
      · exact hwim.symm
    rw [hzw]
    exact hw

private theorem locallyFellConverges_comp_strictMono_adapter
    {A : ℕ → Set Plane} {S : Set Plane} (phi : ℕ → ℕ)
    (hphi : StrictMono phi)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A S) :
    Tiling.AxisParallel.Topology.LocallyFellConverges (fun n ↦ A (phi n)) S := by
  rcases hconv with ⟨hA, hS, hconv⟩
  exact ⟨fun n ↦ hA (phi n), hS, hconv.comp hphi.tendsto_atTop⟩

private theorem translatedNormalized_subset_ambientLimit_adapter
    {K : Region} (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ)
    (N : Set Plane) (anchor : ℕ → Plane) (limitAnchor : Plane)
    (hsubset : ∀ n, anchor n +ᵥ N ⊆ ((T n).centres : Set Plane))
    (hanchor : Tendsto anchor atTop (nhds limitAnchor))
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
      (S.centres : Set Plane)) :
    limitAnchor +ᵥ N ⊆ (S.centres : Set Plane) := by
  rintro x ⟨u, hu, rfl⟩
  apply Tiling.AxisParallel.Continuous.mem_of_locallyFellConverges_of_tendsto_mem hconv
    (zseq := fun n ↦ anchor n + u)
  · intro n
    exact hsubset n ⟨u, hu, rfl⟩
  · simpa only [vadd_eq_add] using hanchor.add_const u

/-! The following arithmetic seam uses support periodicity only to move one support
point by integer multiples of the support period.  The centres enter solely through
the local support-to-centre proximity hypothesis. -/

private theorem support_period_integer_translate
    {S : Set Plane} {p : Plane} (hperiod : SetPeriodicBy S p)
    (z : Plane) (hz : z ∈ S) :
    ∀ n : ℤ, z + (n : ℝ) • p ∈ S := by
  intro n
  cases n with
  | ofNat n =>
      induction n with
      | zero => simpa
      | succ n ih =>
          have hstep := (hperiod (z + (n : ℝ) • p)).mpr ih
          convert hstep using 1
          apply Complex.ext <;> simp [Int.ofNat_eq_natCast, Nat.cast_add]
          <;> ring
  | negSucc n =>
      have hback : ∀ m : ℕ, z - (m : ℝ) • p ∈ S := by
        intro m
        induction m with
        | zero => simpa
        | succ m ih =>
            have hstep := (hperiod (z - ((m + 1 : ℕ) : ℝ) • p)).mp (by
              convert ih using 1
              apply Complex.ext <;>
                simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
                  Complex.smul_re, Complex.smul_im,
                  Nat.cast_add, Nat.cast_one, smul_eq_mul]
              <;> ring)
            exact hstep
      convert hback (n + 1) using 1
      apply Complex.ext <;>
        simp only [Int.cast_negSucc, Complex.add_re, Complex.add_im, Complex.sub_re,
          Complex.sub_im, Complex.smul_re, Complex.smul_im,
          smul_eq_mul]
      <;> ring

private theorem supportPeriod_density_axisProximity_adapter
    {S C : Set Plane} {p : Plane} {delta : ℝ}
    (hperiod : SetPeriodicBy S p) (_hp : 0 < p.re)
    (z₀ : Plane) (hz₀ : z₀ ∈ S)
    (hphase : ∀ x : ℝ, ∃ n : ℤ,
      |z₀.re + (n : ℝ) * p.re - x| ≤ p.re)
    (hnear : ∀ z ∈ S, ∃ a ∈ C, |a.re - z.re| ≤ delta) :
    ∀ x : ℝ, ∃ a ∈ C, |a.re - x| ≤ delta + p.re := by
  intro x
  obtain ⟨n, hn⟩ := hphase x
  have hz : z₀ + (n : ℝ) • p ∈ S :=
    support_period_integer_translate hperiod z₀ hz₀ n
  obtain ⟨a, haC, ha⟩ := hnear (z₀ + (n : ℝ) • p) hz
  refine ⟨a, haC, ?_⟩
  have hzre : (z₀ + (n : ℝ) • p).re = z₀.re + (n : ℝ) * p.re := by
    simp
  calc
    |a.re - x| ≤ |a.re - (z₀ + (n : ℝ) • p).re| +
        |(z₀ + (n : ℝ) • p).re - x| := by
      rw [show a.re - x = (a.re - (z₀ + (n : ℝ) • p).re) +
        ((z₀ + (n : ℝ) • p).re - x) by ring]
      exact abs_add_le _ _
    _ ≤ delta + p.re := by
      have ha' : |a.re - (z₀.re + (n : ℝ) * p.re)| ≤ delta := by
        simpa only [hzre] using ha
      calc
        |a.re - (z₀ + (n : ℝ) • p).re| +
            |(z₀ + (n : ℝ) • p).re - x| ≤
            delta + |z₀.re + (n : ℝ) * p.re - x| := by
              rw [hzre]
              exact add_le_add ha' le_rfl
        _ ≤ delta + p.re := add_le_add le_rfl hn

/-! The C04 endpoint is consumed only as an occupied-support period.  The
remaining bridge from occupied support to column centres is intentionally an
explicit S04/S02 seam here; this adapter never upgrades support periodicity to
centre-set periodicity. -/

private theorem deformedColumnAxes_relativelyDense_from_support_and_proximity
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {T : Set Plane}
    {beta delta : ℝ}
    (hbeta : 0 < beta)
    (hdelta : 0 ≤ delta)
    (hperiod : SetPeriodicBy
      (regularSupport D.deformedRegion (verticalColumnCentres D.deformedRegion T))
      ((beta : ℝ) : ℂ))
    (z₀ : Plane)
    (hz₀ : z₀ ∈ regularSupport D.deformedRegion
      (verticalColumnCentres D.deformedRegion T))
    (hphase : ∀ x : ℝ, ∃ n : ℤ,
      |z₀.re + (n : ℝ) * beta - x| ≤ beta)
    (hnear : ∀ z ∈ regularSupport D.deformedRegion
      (verticalColumnCentres D.deformedRegion T),
      ∃ a ∈ verticalColumnCentres D.deformedRegion T,
        |a.re - z.re| ≤ delta) :
    ∃ R : ℝ, 0 < R ∧
      ∀ x : ℝ, ∃ a ∈ verticalColumnCentres D.deformedRegion T,
        |a.re - x| ≤ R := by
  refine ⟨delta + beta, ?_, ?_⟩
  · linarith
  · exact supportPeriod_density_axisProximity_adapter hperiod hbeta z₀ hz₀ hphase hnear

private theorem verticalColumnSupport_proximity
    {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    ∃ delta : ℝ, 0 ≤ delta ∧
      ∀ z ∈ regularSupport K (verticalColumnCentres K T),
        ∃ a ∈ verticalColumnCentres K T, |a.re - z.re| ≤ delta := by
  obtain ⟨rho, hrho⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  have hrhone : 0 ≤ rho := by
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hk' : k ∈ K.support := interior_subset hk
    have hball := hrho hk'
    have hdist : dist k 0 ≤ rho := by simpa [Metric.mem_closedBall] using hball
    exact le_trans dist_nonneg hdist
  have hpackS : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        (verticalColumnCentres K T)) := by
    apply (isPacking_iff_openCarrier_disjoint K
      (verticalColumnCentres K T)).mpr
    intro s hs t ht hst
    apply (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
    · rcases Set.mem_iUnion.mp hs with ⟨P, hP⟩
      rcases hP with ⟨u, hu, rfl⟩
      exact u.property
    · rcases Set.mem_iUnion.mp ht with ⟨P, hP⟩
      rcases hP with ⟨u, hu, rfl⟩
      exact u.property
    · exact hst
  refine ⟨rho, hrhone, ?_⟩
  intro z hz
  change z ∈ interior (closure (openUnion K (verticalColumnCentres K T))) at hz
  have hzcl : z ∈ closure (openUnion K (verticalColumnCentres K T)) :=
    interior_subset hz
  rw [closure_openUnion_eq_iUnion_support hpackS] at hzcl
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hzcl
  obtain ⟨k, hk, rfl⟩ := hs
  refine ⟨s, s.property, ?_⟩
  have hball := hrho hk
  have hnorm : ‖k‖ ≤ rho := by
    simpa [Metric.mem_closedBall] using hball
  have hre : |k.re| ≤ ‖k‖ := Complex.abs_re_le_norm k
  simpa [vadd_eq_add] using hre.trans hnorm

private theorem deformedColumnAxes_relativelyDense
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {T : Set Plane}
    (hTile : TilesOn D.deformedRegion T Set.univ)
    (hRational : Tiling.RationalPolygonal.IsRelativelyRational
      D.deformedRegion.toPolygonalRegion)
    (hCne : (verticalColumnCentres D.deformedRegion T).Nonempty) :
    ∃ beta R : ℝ, 0 < beta ∧ 0 < R ∧
      SetPeriodicBy
        (regularSupport D.deformedRegion
          (verticalColumnCentres D.deformedRegion T)) ((beta : ℝ) : ℂ) ∧
      ∀ x : ℝ, ∃ a ∈ verticalColumnCentres D.deformedRegion T,
        |a.re - x| ≤ R := by
  obtain ⟨beta, hbeta, hperiod, _hplate⟩ :=
    rationalVerticalPlateSupport_periodic hTile hRational
  obtain ⟨delta, hdelta, hnear⟩ := verticalColumnSupport_proximity hTile
  obtain ⟨a, ha⟩ := hCne
  obtain ⟨k, hk⟩ := D.deformedRegion.isPolygonal.interior_nonempty
    D.deformedRegion.nonempty
  have hkopen : k ∈ D.deformedRegion.openCarrier := by
    exact hk
  have hopen : IsOpen (openUnion D.deformedRegion
      (verticalColumnCentres D.deformedRegion T)) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun s ↦ D.deformedRegion.openCarrier_regularOpen.1.vadd s.1
  let s : verticalColumnCentres D.deformedRegion T := ⟨a, ha⟩
  have hraw : (a + k) ∈ openUnion D.deformedRegion
      (verticalColumnCentres D.deformedRegion T) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨s, ?_⟩
    exact ⟨k, hkopen, rfl⟩
  have hz₀ : a + k ∈ regularSupport D.deformedRegion
      (verticalColumnCentres D.deformedRegion T) :=
    hopen.subset_interior_closure hraw
  have hphase : ∀ x : ℝ, ∃ n : ℤ,
      |(a + k).re + (n : ℝ) * beta - x| ≤ beta := by
    intro x
    let n : ℤ := Int.floor ((x - (a + k).re) / beta)
    refine ⟨n, ?_⟩
    have hlo := Int.floor_le ((x - (a + k).re) / beta)
    have hhi := Int.lt_floor_add_one ((x - (a + k).re) / beta)
    have hlo' := (le_div_iff₀ hbeta).mp hlo
    have hhi' := (div_lt_iff₀ hbeta).mp hhi
    have hdesired :
        |(a + k).re + (Int.floor ((x - (a + k).re) / beta) : ℝ) * beta - x| ≤ beta := by
      rw [abs_le]
      constructor <;> linarith [hlo', hhi']
    simpa [n] using hdesired
  obtain ⟨R, hRpos, hdense⟩ :=
    deformedColumnAxes_relativelyDense_from_support_and_proximity
      hbeta hdelta hperiod (a + k) hz₀ hphase hnear
  exact ⟨beta, R, hbeta, hRpos, hperiod, hdense⟩

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open MeasureTheory Set Filter
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval
open Tiling.AxisParallel.OneDimensional.ColumnSlices
open Tiling.RationalPolygonal

private structure S06FibreGapWordData
    (C : ApproximationContext) {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) where
  relativeHeight : ℝ
  slice : Set ℝ
  slice_eq : slice = Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
    C.region relativeHeight
  relativeHeight_generic : ∀ v : ↥C.region.vertices, v.1.im ≠ relativeHeight
  presentation : OneDimensional.FiniteInterval.IntervalPresentation slice
  slice_nonempty : slice.Nonempty
  endpoint : ℝ
  endpoint_mem : endpoint ∈ presentation.endpoints
  gapAlphabet : Set ℝ
  gapAlphabet_eq : gapAlphabet = presentation.gapLengths
  between : ∀ s t : ↥H.fibre, s.1.re < t.1.re →
    ∃ n : ℕ, ∃ word : Fin n → ℝ,
      (∀ i, word i ∈ gapAlphabet) ∧
      t.1.re - s.1.re = ∑ i, word i

private theorem s06_fibreGapWordData_exists
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) :
    Nonempty (S06FibreGapWordData C H) := by
  obtain ⟨z, hz⟩ := C.region.isPolygonal.interior_nonempty C.region.nonempty
  change z ∈ C.region.openCarrier at hz
  obtain ⟨ε, hε, hball⟩ :=
    Metric.mem_nhds_iff.mp (C.region.openCarrier_regularOpen.1.mem_nhds hz)
  let J : Set ℝ := Set.Ioo (z.im - ε / 2) (z.im + ε / 2)
  have hJinf : J.Infinite := by
    dsimp [J]
    exact Set.Ioo_infinite (by linarith)
  have hFfin : ((C.region.vertexFinset.image Complex.im : Finset ℝ) : Set ℝ).Finite :=
    (C.region.vertexFinset.image Complex.im).finite_toSet
  obtain ⟨y, hyJ, hy⟩ := (hJinf.sdiff hFfin).nonempty
  have hyabs : |y - z.im| < ε := by
    dsimp [J] at hyJ
    rw [abs_lt]
    constructor <;> linarith [hyJ.1, hyJ.2]
  let q : Tiling.Plane := (z.re : ℂ) + (y : ℂ) * Complex.I
  have hqball : q ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hdiff : q - z = ((y - z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [q]
    rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    exact hyabs
  have hq : q ∈ C.region.openCarrier := hball hqball
  have hslice :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y).Nonempty := by
    change ∃ x : ℝ, Complex.mk x y ∈ C.region.openCarrier
    refine ⟨z.re, ?_⟩
    have hq' : Complex.mk z.re y = q := by
      apply Complex.ext <;> simp [q]
    rw [hq']
    exact hq
  have hfinite :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice_isFiniteIntervalRegion
      C.region hy
  let P := OneDimensional.FiniteInterval.IntervalPresentation.ofIsFiniteIntervalRegion hfinite
  have hvol := ColumnSlices.finiteIntervalRegion_volume_toReal_pos hfinite hslice
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hslice
  have hTile := sourceRow_genericSections_lineTile H y hy hslice
  have hyvertex : ∀ v : ↥C.region.vertices, v.1.im ≠ y := by
    intro v hv
    apply hy
    change y ∈ (C.region.vertexFinset.image Complex.im : Finset ℝ)
    apply Finset.mem_image.mpr
    refine ⟨v.1, ?_, hv⟩
    change v.1 ∈ (C.region.vertexFinset : Set Tiling.Plane)
    simpa only [C.region.coe_vertexFinset] using v.2
  refine ⟨⟨y, _, rfl, hyvertex, P, hslice, e₀, he₀, P.gapLengths, rfl, ?_⟩⟩
  intro s t hst
  let L : Set ℝ := Complex.re '' H.fibre
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P L ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top hvol
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  have hsL : s.1.re ∈ L := ⟨s.1, s.2, rfl⟩
  have htL : t.1.re ∈ L := ⟨t.1, t.2, rfl⟩
  have hsE : s.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨s.1.re, hsL, e₀, he₀, rfl⟩
  have htE : t.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨t.1.re, htL, e₀, he₀, rfl⟩
  obtain ⟨chain⟩ := OneDimensional.FiniteInterval.endpointChain_nonempty
    hlocal hsE htE (by linarith)
  let word : Fin chain.length → ℝ := fun i =>
    chain.point i.succ - chain.point i.castSucc
  refine ⟨chain.length, word, ?_, ?_⟩
  · intro i
    dsimp [word]
    exact OneDimensional.FiniteInterval.consecutive_translatedEndpoint_gap
      P hvol hTile (chain.consecutive i)
  · have htelescope := OneDimensional.FiniteInterval.endpointChain_telescope chain
    calc
      t.1.re - s.1.re = (t.1.re + e₀) - (s.1.re + e₀) := by ring
      _ = ∑ i, word i := by simpa [word] using htelescope.symm

private theorem s06_fibre_coordinateSpace_mem
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) (s : ↥H.fibre) :
    s.1.re ∈ C.coordinateSpace ∧ s.1.im ∈ C.coordinateSpace := by
  obtain ⟨n, hn⟩ := Filter.Eventually.exists (H.persistent_pullback s.1 s.2)
  have htr_re : ((H.translations n : Tiling.Plane).re) ∈ C.coordinateSpace := by
    rw [H.translations_eq n]
    simpa using C.coordinateSpace.sub_mem
      (C.centre_re_mem H.anchor H.anchor_mem_context)
      (C.centre_re_mem (H.movingCentre n) (H.movingCentre_mem_context n))
  have htr_im : ((H.translations n : Tiling.Plane).im) ∈ C.coordinateSpace := by
    rw [H.translations_eq n]
    simpa using C.coordinateSpace.sub_mem
      (C.centre_im_mem H.anchor H.anchor_mem_context)
      (C.centre_im_mem (H.movingCentre n) (H.movingCentre_mem_context n))
  constructor
  · have hsub := C.centre_re_mem (s.1 - (H.translations n : Tiling.Plane)) hn
    have hadd := C.coordinateSpace.add_mem hsub htr_re
    simpa [Complex.sub_re, Complex.add_re] using hadd
  · have hsub := C.centre_im_mem (s.1 - (H.translations n : Tiling.Plane)) hn
    have hadd := C.coordinateSpace.add_mem hsub htr_im
    simpa [Complex.sub_im, Complex.add_im] using hadd

private theorem s06_canonical_horizontal_presentation
    {C : ApproximationContext} {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im) :
    ∃ P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y),
      ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e := by
  obtain ⟨G⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalGenericSlicePresentation_exists
      C.region hy
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := G.n
    left := G.left
    right := G.right
    lt := G.lt
    union_eq := G.union_eq }
  refine ⟨P, ?_⟩
  intro e he
  simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
  rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨G.leftVertex i, G.leftVertex_coord i⟩
  · exact ⟨G.rightVertex i, G.rightVertex_coord i⟩

private theorem s06_consecutive_endpoint_owned
    {B L : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hBpositive : 0 < (volume B).toReal) (hTile : OneDimensional.LineTiles B L)
    {x y : ℝ}
    (hxy : OneDimensional.FiniteInterval.ConsecutiveIn
      (OneDimensional.FiniteInterval.translatedEndpointSet P L) x y) :
    ∃ l ∈ L, ∃ e₁ ∈ P.endpoints, ∃ e₂ ∈ P.endpoints,
      e₁ < e₂ ∧ x = l + e₁ ∧ y = l + e₂ := by
  have hsource :=
    (Tiling.AxisParallel.Foundations.finiteOpenIntervals_source_iff_ae
      P.isFiniteIntervalRegion hBpositive).1 hTile
  have hmid : ∃ l ∈ L, (x + y) / 2 ∈ l +ᵥ closure B := by
    have hm : (x + y) / 2 ∈ ⋃ l : L, l.1 +ᵥ closure B := by
      rw [hsource.2.2]
      exact Set.mem_univ _
    rw [Set.mem_iUnion] at hm
    obtain ⟨l, hl⟩ := hm
    exact ⟨l.1, l.2, hl⟩
  let z : ℝ := (x + y) / 2
  obtain ⟨l, hl, hzcl⟩ := hmid
  have hxz : x < z := by dsimp [z]; linarith [hxy.2.2.1]
  have hzy : z < y := by dsimp [z]; linarith [hxy.2.2.1]
  have hzcl' : z - l ∈ closure B := by
    dsimp [z]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzcl
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzcl
  have hzB : z - l ∈ B := by
    by_contra hzB
    have he : z - l ∈ (P.endpoints : Set ℝ) :=
      P.closure_diff_subset_endpoints ⟨hzcl', hzB⟩
    have hzE : z ∈
        OneDimensional.FiniteInterval.translatedEndpointSet P L :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
        ⟨l, hl, z - l, he, by ring⟩
    exact Set.disjoint_left.1 hxy.2.2.2 hzE ⟨hxz, hzy⟩
  rw [P.union_eq, Set.mem_iUnion] at hzB
  obtain ⟨i, hi⟩ := hzB
  have hleftEnd : P.left i ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hrightEnd : P.right i ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hleftE : l + P.left i ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.left i, hleftEnd, rfl⟩
  have hrightE : l + P.right i ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.right i, hrightEnd, rfl⟩
  have hleft_lt_z : l + P.left i < z := by linarith [hi.1]
  have hz_lt_right : z < l + P.right i := by linarith [hi.2]
  have hleft_le_x : l + P.left i ≤ x := by
    by_contra h
    have hxleft : x < l + P.left i := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hleftE
      ⟨hxleft, lt_trans hleft_lt_z hzy⟩
  have hy_le_right : y ≤ l + P.right i := by
    by_contra h
    have hrighty : l + P.right i < y := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hrightE
      ⟨lt_trans hxz hz_lt_right, hrighty⟩
  obtain ⟨m, hm, ex, hex, hxeq⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hxy.1
  obtain ⟨n, hn, ey, hey, hyeq⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hxy.2.1
  have hxOwned : ∃ ex ∈ P.endpoints, x = l + ex := by
    by_cases hxleft : x = l + P.left i
    · exact ⟨P.left i, hleftEnd, hxleft⟩
    · have hleft_lt_x : l + P.left i < x :=
        lt_of_le_of_ne hleft_le_x (Ne.symm hxleft)
      have hxOpen : x ∈ l +ᵥ B := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
        refine ⟨i, ?_⟩
        simp only [vadd_eq_add]
        constructor <;> linarith
      have hm_eq_l : m = l := by
        by_contra hml
        have hxNot :=
          OneDimensional.FiniteInterval.endpoint_not_mem_other_openTile
            P hTile.2.2.2.1 hm hl hml hex
        exact hxNot (hxeq ▸ hxOpen)
      exact ⟨ex, hex, by simpa [hm_eq_l] using hxeq⟩
  have hyOwned : ∃ ey ∈ P.endpoints, y = l + ey := by
    by_cases hyright : y = l + P.right i
    · exact ⟨P.right i, hrightEnd, hyright⟩
    · have hy_lt_right : y < l + P.right i :=
        lt_of_le_of_ne hy_le_right hyright
      have hyOpen : y ∈ l +ᵥ B := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
        refine ⟨i, ?_⟩
        simp only [vadd_eq_add]
        constructor <;> linarith
      have hn_eq_l : n = l := by
        by_contra hnl
        have hyNot :=
          OneDimensional.FiniteInterval.endpoint_not_mem_other_openTile
            P hTile.2.2.2.1 hn hl hnl hey
        exact hyNot (hyeq ▸ hyOpen)
      exact ⟨ey, hey, by simpa [hn_eq_l] using hyeq⟩
  obtain ⟨ex', hex', hxeq'⟩ := hxOwned
  obtain ⟨ey', hey', hyeq'⟩ := hyOwned
  refine ⟨l, hl, ex', hex', ey', hey', ?_, hxeq', hyeq'⟩
  linarith [hxy.2.2.1]

private theorem s06_consecutive_map_gap
    {C : ApproximationContext} {y : ℝ}
    {P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)}
    {L : Set ℝ} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    (hLcoord : ∀ l ∈ L, l ∈ C.coordinateSpace)
    (hBpositive : 0 < (volume
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)).toReal)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) L)
    {x y' : ℝ}
    (hxy : OneDimensional.FiniteInterval.ConsecutiveIn
      (OneDimensional.FiniteInterval.translatedEndpointSet P L) x y')
    (xLift yLift : C.coordinateSpace)
    (hx : (xLift : ℝ) = x) (hy' : (yLift : ℝ) = y') :
    ∃ l ∈ L, ∃ e₁ ∈ P.endpoints, ∃ e₂ ∈ P.endpoints,
      e₁ < e₂ ∧ x = l + e₁ ∧ y' = l + e₂ ∧
      ∃ q₁ q₂ : C.coordinateSpace, (q₁ : ℝ) = e₁ ∧ (q₂ : ℝ) = e₂ ∧
        mapScalar phi yLift - mapScalar phi xLift =
          mapScalar phi q₂ - mapScalar phi q₁ := by
  obtain ⟨l, hl, e₁, he₁, e₂, he₂, hlt, hxeq, hyeq⟩ :=
    s06_consecutive_endpoint_owned P hBpositive hTile hxy
  obtain ⟨v₁, hv₁⟩ := hvertex e₁ he₁
  obtain ⟨v₂, hv₂⟩ := hvertex e₂ he₂
  let lLift : C.coordinateSpace := ⟨l, hLcoord l hl⟩
  let e₁Lift : C.coordinateSpace := ⟨e₁, by
    rw [← hv₁]
    exact C.vertex_re_mem v₁.1 v₁.2⟩
  let e₂Lift : C.coordinateSpace := ⟨e₂, by
    rw [← hv₂]
    exact C.vertex_re_mem v₂.1 v₂.2⟩
  have hxLift : xLift = lLift + e₁Lift := by
    apply Subtype.ext
    simp [lLift, e₁Lift, hx, hxeq]
  have hyLift : yLift = lLift + e₂Lift := by
    apply Subtype.ext
    simp [lLift, e₂Lift, hy', hyeq]
  refine ⟨l, hl, e₁, he₁, e₂, he₂, hlt, hxeq, hyeq,
    e₁Lift, e₂Lift, rfl, rfl, ?_⟩
  rw [hxLift, hyLift]
  simp only [mapScalar, map_add, Rat.cast_add, sub_eq_add_neg]
  ring

private theorem s06_mapped_endpoint_gap_pos
    {C : ApproximationContext} {y : ℝ}
    {P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    {e₁ e₂ : ℝ} (h₁ : e₁ ∈ P.endpoints) (h₂ : e₂ ∈ P.endpoints)
    (h₁₂ : e₁ < e₂) :
    ∃ x₁ x₂ : C.coordinateSpace, (x₁ : ℝ) = e₁ ∧ (x₂ : ℝ) = e₂ ∧
      0 < mapScalar phi x₂ - mapScalar phi x₁ := by
  obtain ⟨v, hv⟩ := hvertex e₁ h₁
  obtain ⟨w, hw⟩ := hvertex e₂ h₂
  have hsign := D.source_good.preservesVertexCoordinateSign
    Axis.horizontal w.1 v.1 w.2 v.2
  have hsource : Real.sign (Axis.coord Axis.horizontal (w.1 - v.1)) = 1 := by
    exact Real.sign_of_pos (by simpa [Axis.coord, hw, hv] using h₁₂)
  have hmap : Real.sign
      (Axis.coord Axis.horizontal
        (mapPoint phi (C.vertexPoint w.1 w.2) -
          mapPoint phi (C.vertexPoint v.1 v.2))) = 1 := by
    rw [hsign, hsource]
  have hpos : 0 < Axis.coord Axis.horizontal
      (mapPoint phi (C.vertexPoint w.1 w.2) -
        mapPoint phi (C.vertexPoint v.1 v.2)) := by
    by_contra hnonpos
    have hle : Axis.coord Axis.horizontal
        (mapPoint phi (C.vertexPoint w.1 w.2) -
          mapPoint phi (C.vertexPoint v.1 v.2)) ≤ 0 := le_of_not_gt hnonpos
    rcases hle.eq_or_lt with hzero | hneg
    · rw [hzero, Real.sign_zero] at hmap
      norm_num at hmap
    · rw [Real.sign_of_neg hneg] at hmap
      norm_num at hmap
  let x₁ : C.coordinateSpace := ⟨e₁, by
    rw [← hv]
    exact C.vertex_re_mem v.1 v.2⟩
  let x₂ : C.coordinateSpace := ⟨e₂, by
    rw [← hw]
    exact C.vertex_re_mem w.1 w.2⟩
  refine ⟨x₁, x₂, rfl, rfl, ?_⟩
  have hx₁ : x₁ = ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ := by
    apply Subtype.ext
    exact hv.symm
  have hx₂ : x₂ = ⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ := by
    apply Subtype.ext
    exact hw.symm
  rw [hx₁, hx₂]
  have hvcoord : (⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ : C.coordinateSpace) =
      ⟨(C.vertexPoint v.1 v.2).1.re, (C.vertexPoint v.1 v.2).2.1⟩ := by
    apply Subtype.ext
    rfl
  have hwcoord : (⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ : C.coordinateSpace) =
      ⟨(C.vertexPoint w.1 w.2).1.re, (C.vertexPoint w.1 w.2).2.1⟩ := by
    apply Subtype.ext
    rfl
  rw [hvcoord, hwcoord]
  simpa [mapPoint, mapScalar, Axis.coord] using hpos

private theorem s06_mapped_gap_ratio_alphabet
    {C : ApproximationContext} {y : ℝ}
    {P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    (hpairs : ∃ e₁ ∈ P.endpoints, ∃ e₂ ∈ P.endpoints, e₁ < e₂) :
    ∃ R : Finset ℝ, R.Nonempty ∧ (∀ r ∈ R, 0 < r) ∧
      (∀ (e₁ : ℝ), e₁ ∈ P.endpoints → ∀ (e₂ : ℝ), e₂ ∈ P.endpoints → e₁ < e₂ →
        ∃ q₁ q₂ : C.coordinateSpace, (q₁ : ℝ) = e₁ ∧ (q₂ : ℝ) = e₂ ∧
          (mapScalar phi q₂ - mapScalar phi q₁) / (e₂ - e₁) ∈ R) := by
  let eLift : ℝ → C.coordinateSpace := fun e =>
    if he : e ∈ P.endpoints then
      ⟨e, by
        obtain ⟨v, hv⟩ := hvertex e he
        rw [← hv]
        exact C.vertex_re_mem v.1 v.2⟩
    else 0
  let R : Finset ℝ :=
    (P.endpoints.product P.endpoints).filter (fun p : ℝ × ℝ => p.1 < p.2) |>.image
      (fun p : ℝ × ℝ =>
        (mapScalar phi (eLift p.2) - mapScalar phi (eLift p.1)) /
          (p.2 - p.1))
  have hRpos : ∀ r ∈ R, 0 < r := by
    intro r hr
    obtain ⟨⟨e₁, e₂⟩, hmem, rfl⟩ := Finset.mem_image.mp hr
    have hmem' := Finset.mem_filter.mp hmem
    have hprod := Finset.mem_product.mp hmem'.1
    obtain ⟨x₁, x₂, hx₁, hx₂, hpos⟩ :=
      s06_mapped_endpoint_gap_pos (D := D) hvertex hprod.1 hprod.2 hmem'.2
    have he₁ : (eLift e₁ : ℝ) = e₁ := by simp [eLift, hprod.1]
    have he₂ : (eLift e₂ : ℝ) = e₂ := by simp [eLift, hprod.2]
    have hpos' : 0 < mapScalar phi (eLift e₂) - mapScalar phi (eLift e₁) := by
      have heq₁ : eLift e₁ = x₁ := Subtype.ext (by simpa [he₁] using hx₁.symm)
      have heq₂ : eLift e₂ = x₂ := Subtype.ext (by simpa [he₂] using hx₂.symm)
      rw [heq₁, heq₂]
      exact hpos
    exact div_pos hpos'
      (sub_pos.mpr hmem'.2)
  have hRne : R.Nonempty := by
    obtain ⟨e₁, he₁, e₂, he₂, hlt⟩ := hpairs
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hzero
    have hmem :
        (mapScalar phi (eLift e₂) - mapScalar phi (eLift e₁)) /
          (e₂ - e₁) ∈ R := by
      apply Finset.mem_image.mpr
      refine ⟨(e₁, e₂), ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he₁, he₂⟩, hlt⟩
    rw [hzero] at hmem
    simp at hmem
  refine ⟨R, hRne, hRpos, ?_⟩
  intro e₁ he₁ e₂ he₂ hlt
  let q₁ := eLift e₁
  let q₂ := eLift e₂
  have hq₁ : (q₁ : ℝ) = e₁ := by simp [q₁, eLift, he₁]
  have hq₂ : (q₂ : ℝ) = e₂ := by simp [q₂, eLift, he₂]
  refine ⟨q₁, q₂, hq₁, hq₂, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(e₁, e₂), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he₁, he₂⟩, hlt⟩
  · simp [q₁, q₂]

private noncomputable def s06_fibreCoordinateLift
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) (s : ↥H.fibre) :
    {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} :=
  ⟨s.1, s06_fibre_coordinateSpace_mem H s |>.1,
    s06_fibre_coordinateSpace_mem H s |>.2⟩

private noncomputable def s06_fibreImage
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) : ↥H.fibre → Tiling.Plane :=
  fun s => mapPoint phi (s06_fibreCoordinateLift H s)

private theorem s06_fibreImage_apply
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (s : ↥H.fibre) :
    s06_fibreImage H phi s =
      mapPoint phi (s06_fibreCoordinateLift H s) := rfl

private theorem s06_fibreImage_im_eq
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (s t : ↥H.fibre) :
    (s06_fibreImage H phi s).im = (s06_fibreImage H phi t).im := by
  have him : s.1.im = t.1.im := by
    have hs := s.2
    have ht := t.2
    have hs' : s.1 ∈ (H.limit.centres : Set Tiling.Plane) ∩
        {z : Tiling.Plane | z.im = H.anchor.im} := H.fibre_eq ▸ hs
    have ht' : t.1 ∈ (H.limit.centres : Set Tiling.Plane) ∩
        {z : Tiling.Plane | z.im = H.anchor.im} := H.fibre_eq ▸ ht
    exact hs'.2.trans ht'.2.symm
  simp only [s06_fibreImage, mapPoint, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, zero_mul,
    add_zero]
  have hsub :
      (s06_fibreCoordinateLift H s).1.im = s.1.im := rfl
  have hsub' :
      (s06_fibreCoordinateLift H t).1.im = t.1.im := rfl
  have hq : (s06_fibreCoordinateLift H s).1.im =
      (s06_fibreCoordinateLift H t).1.im := by
    rw [hsub, hsub', him]
  have hiq :
      (⟨(s06_fibreCoordinateLift H s).1.im,
        (s06_fibreCoordinateLift H s).2.2⟩ : C.coordinateSpace) =
      ⟨(s06_fibreCoordinateLift H t).1.im,
        (s06_fibreCoordinateLift H t).2.2⟩ := Subtype.ext hq
  rw [hiq]

private theorem s06_fibreImage_injective_of_strictOrder
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (horder : ∀ s t : ↥H.fibre, s.1.re < t.1.re →
      (s06_fibreImage H phi s).re < (s06_fibreImage H phi t).re) :
    Function.Injective (s06_fibreImage H phi) := by
  intro s t hst
  by_contra hne
  rcases lt_or_gt_of_ne (show s.1.re ≠ t.1.re from by
    intro heq
    apply hne
    apply Subtype.ext
    apply Complex.ext
    · exact heq
    · have hs := s.2
      have ht := t.2
      have hs' : s.1 ∈ (H.limit.centres : Set Tiling.Plane) ∩
          {z : Tiling.Plane | z.im = H.anchor.im} := H.fibre_eq ▸ hs
      have ht' : t.1 ∈ (H.limit.centres : Set Tiling.Plane) ∩
          {z : Tiling.Plane | z.im = H.anchor.im} := H.fibre_eq ▸ ht
      exact hs'.2.trans ht'.2.symm) with hlt | hgt
  · exact (ne_of_lt (horder s t hlt)) (congrArg Complex.re hst)
  · exact (ne_of_lt (horder t s hgt)) (congrArg Complex.re hst).symm

private theorem s06_fibreImage_strictOrder
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    {y : ℝ}
    {P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)}
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre))
    (s t : ↥H.fibre) (hst : s.1.re < t.1.re) :
    (s06_fibreImage H phi s).re < (s06_fibreImage H phi t).re := by
  let L : Set ℝ := Complex.re '' H.fibre
  have hLcoord : ∀ l ∈ L, l ∈ C.coordinateSpace := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := hl
    exact (s06_fibre_coordinateSpace_mem H ⟨z, hz⟩).1
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hPne
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P L ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top (by
          exact ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  have hsL : s.1.re ∈ L := ⟨s.1, s.2, rfl⟩
  have htL : t.1.re ∈ L := ⟨t.1, t.2, rfl⟩
  have hsE : s.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨s.1.re, hsL, e₀, he₀, rfl⟩
  have htE : t.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨t.1.re, htL, e₀, he₀, rfl⟩
  obtain ⟨chain⟩ := OneDimensional.FiniteInterval.endpointChain_nonempty
    hlocal hsE htE (by linarith)
  have hpoint : ∀ i : Fin (chain.length + 1),
      chain.point i ∈ OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    intro i
    by_cases hilast : i = Fin.last chain.length
    · rw [hilast, chain.last]
      exact htE
    · have hi : i.val < chain.length := by
        exact Nat.lt_of_le_of_ne (Fin.le_last i)
          (fun heq => hilast (Fin.ext heq))
      let j : Fin chain.length := ⟨i.val, hi⟩
      have hj : j.castSucc = i := Fin.ext rfl
      rw [← hj]
      exact (chain.consecutive j).1
  have hcoord : ∀ i : Fin (chain.length + 1),
      chain.point i ∈ C.coordinateSpace := by
    intro i
    obtain ⟨l, hl, e, he, hxeq⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1
        (hpoint i)
    obtain ⟨v, hv⟩ := hvertex e he
    rw [hxeq]
    exact C.coordinateSpace.add_mem (hLcoord l hl) (by
      rw [← hv]
      exact C.vertex_re_mem v.1 v.2)
  let xLift : Fin (chain.length + 1) → C.coordinateSpace := fun i =>
    ⟨chain.point i, hcoord i⟩
  have hstep : ∀ i : Fin chain.length,
      0 < mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc) := by
    intro i
    obtain ⟨l, hl, e₁, he₁, e₂, he₂, hlt, hxeq, hyeq, q₁, q₂,
      hq₁, hq₂, hmap⟩ := s06_consecutive_map_gap hvertex hLcoord
      (by exact ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
      hTile (chain.consecutive i) (xLift i.castSucc) (xLift i.succ) rfl rfl
    obtain ⟨r₁, r₂, hr₁, hr₂, hpos⟩ :=
      s06_mapped_endpoint_gap_pos (D := D) hvertex he₁ he₂ hlt
    have hqeq₁ : q₁ = r₁ := Subtype.ext (hq₁.trans hr₁.symm)
    have hqeq₂ : q₂ = r₂ := Subtype.ext (hq₂.trans hr₂.symm)
    rw [hqeq₁, hqeq₂] at hmap
    exact hmap ▸ hpos
  have hlen : 0 < chain.length := by
    by_contra hz
    have hz' : chain.length = 0 := Nat.eq_zero_of_not_pos hz
    have heq : (chain.point 0 : ℝ) = chain.point (Fin.last chain.length) := by
      have hfin : (0 : Fin (chain.length + 1)) = Fin.last chain.length := by
        apply Fin.ext
        omega
      rw [hfin]
    rw [chain.first, chain.last] at heq
    linarith
  have hsumpos : 0 < ∑ i : Fin chain.length,
      (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) := by
    apply Finset.sum_pos (fun i _ => hstep i)
    exact ⟨⟨0, hlen⟩, by simp⟩
  have htel : ∑ i : Fin chain.length,
      (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
      mapScalar phi (xLift (Fin.last chain.length)) - mapScalar phi (xLift 0) := by
    let f : ℕ → ℝ := fun i =>
      mapScalar phi (xLift ⟨min i chain.length,
        Nat.lt_succ_of_le (Nat.min_le_right i chain.length)⟩)
    calc
      ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
          ∑ i ∈ Finset.range chain.length, (f (i + 1) - f i) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            have hil : i < chain.length := Finset.mem_range.mp hi
            simp [f, hil, Nat.min_eq_left hil.le]
      _ = f chain.length - f 0 := Finset.sum_range_sub f chain.length
      _ = mapScalar phi (xLift (Fin.last chain.length)) - mapScalar phi (xLift 0) := by
        have hfin : (⟨chain.length,
            Nat.lt_succ_self chain.length⟩ : Fin (chain.length + 1)) =
            Fin.last chain.length := by apply Fin.ext; rfl
        simp [f, hfin]
  have himagediff :
      (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re =
        mapScalar phi (xLift (Fin.last chain.length)) - mapScalar phi (xLift 0) := by
    let hsLift := s06_fibreCoordinateLift H s
    let htLift := s06_fibreCoordinateLift H t
    obtain ⟨v₀, hv₀⟩ := hvertex e₀ he₀
    let e₀Lift : C.coordinateSpace := ⟨e₀, by
      rw [← hv₀]
      exact C.vertex_re_mem v₀.1 v₀.2⟩
    have hfirst : xLift 0 = ⟨hsLift.1.re, hsLift.2.1⟩ + e₀Lift := by
      apply Subtype.ext
      simp [xLift, hsLift, s06_fibreCoordinateLift, e₀Lift, chain.first]
    have hlast : xLift (Fin.last chain.length) = ⟨htLift.1.re, htLift.2.1⟩ + e₀Lift := by
      apply Subtype.ext
      simp [xLift, htLift, s06_fibreCoordinateLift, e₀Lift, chain.last]
    rw [hfirst, hlast]
    simp only [mapScalar, map_add, Rat.cast_add, sub_eq_add_neg]
    change (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re = _
    simp [s06_fibreImage, mapPoint, hsLift, htLift]
    rfl
  apply sub_pos.mp
  rw [himagediff, ← htel]
  exact hsumpos

private theorem s06_fibreImage_bounds
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    {y : ℝ}
    {P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)}
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre)) :
    ∃ lam Λ : ℝ, 0 < lam ∧ lam ≤ Λ ∧
      ∀ s t : ↥H.fibre, s.1.re < t.1.re →
        lam * (t.1.re - s.1.re) ≤
            (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re ∧
          (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re ≤
            Λ * (t.1.re - s.1.re) := by
  have hpairs : ∃ e₁ ∈ P.endpoints, ∃ e₂ ∈ P.endpoints, e₁ < e₂ := by
    obtain ⟨x, hx⟩ := hPne
    rw [P.union_eq, Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    have hleft : P.left i ∈ P.endpoints := by
      rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
        Finset.mem_union]
      exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hright : P.right i ∈ P.endpoints := by
      rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
        Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    exact ⟨P.left i, hleft, P.right i, hright, P.lt i⟩
  obtain ⟨R, hRne, hRpos, hRmem⟩ :=
    s06_mapped_gap_ratio_alphabet (D := D) hvertex hpairs
  let lam : ℝ := R.min' hRne
  let Λ : ℝ := R.max' hRne
  have hlampos : 0 < lam := by
    exact hRpos lam (Finset.min'_mem R hRne)
  have hlamΛ : lam ≤ Λ := by
    exact Finset.min'_le R (R.max' hRne) (Finset.max'_mem R hRne)
  refine ⟨lam, Λ, hlampos, hlamΛ, ?_⟩
  intro s t hst
  let L : Set ℝ := Complex.re '' H.fibre
  have hLcoord : ∀ l ∈ L, l ∈ C.coordinateSpace := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := hl
    exact (s06_fibre_coordinateSpace_mem H ⟨z, hz⟩).1
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hPne
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P L ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top (by
          exact ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  have hsL : s.1.re ∈ L := ⟨s.1, s.2, rfl⟩
  have htL : t.1.re ∈ L := ⟨t.1, t.2, rfl⟩
  have hsE : s.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨s.1.re, hsL, e₀, he₀, rfl⟩
  have htE : t.1.re + e₀ ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨t.1.re, htL, e₀, he₀, rfl⟩
  obtain ⟨chain⟩ := OneDimensional.FiniteInterval.endpointChain_nonempty
    hlocal hsE htE (by linarith)
  have hpoint : ∀ i : Fin (chain.length + 1),
      chain.point i ∈ OneDimensional.FiniteInterval.translatedEndpointSet P L := by
    intro i
    by_cases hilast : i = Fin.last chain.length
    · rw [hilast, chain.last]
      exact htE
    · have hi : i.val < chain.length := by
        exact Nat.lt_of_le_of_ne (Fin.le_last i)
          (fun heq => hilast (Fin.ext heq))
      let j : Fin chain.length := ⟨i.val, hi⟩
      have hj : j.castSucc = i := Fin.ext rfl
      rw [← hj]
      exact (chain.consecutive j).1
  have hcoord : ∀ i : Fin (chain.length + 1),
      chain.point i ∈ C.coordinateSpace := by
    intro i
    obtain ⟨l, hl, e, he, hxeq⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1
        (hpoint i)
    obtain ⟨v, hv⟩ := hvertex e he
    rw [hxeq]
    exact C.coordinateSpace.add_mem (hLcoord l hl) (by
      rw [← hv]
      exact C.vertex_re_mem v.1 v.2)
  let xLift : Fin (chain.length + 1) → C.coordinateSpace := fun i =>
    ⟨chain.point i, hcoord i⟩
  have hlen : 0 < chain.length := by
    by_contra hz
    have hz' : chain.length = 0 := Nat.eq_zero_of_not_pos hz
    have heq : (chain.point 0 : ℝ) = chain.point (Fin.last chain.length) := by
      have hfin : (0 : Fin (chain.length + 1)) = Fin.last chain.length := by
        apply Fin.ext
        omega
      rw [hfin]
    rw [chain.first, chain.last] at heq
    linarith
  have hstep : ∀ i : Fin chain.length,
      lam * ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) ≤
          mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc) ∧
        mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc) ≤
          Λ * ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) := by
    intro i
    obtain ⟨l, hl, e₁, he₁, e₂, he₂, hlt, hxeq, hyeq, q₁, q₂,
      hq₁, hq₂, hmap⟩ := s06_consecutive_map_gap hvertex hLcoord
      (by exact ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
      hTile (chain.consecutive i) (xLift i.castSucc) (xLift i.succ) rfl rfl
    obtain ⟨r₁, r₂, hr₁, hr₂, hratio⟩ := hRmem e₁ he₁ e₂ he₂ hlt
    have hqeq₁ : q₁ = r₁ := Subtype.ext (hq₁.trans hr₁.symm)
    have hqeq₂ : q₂ = r₂ := Subtype.ext (hq₂.trans hr₂.symm)
    have hmap' := hmap
    rw [hqeq₁, hqeq₂] at hmap'
    have hden : (xLift i.succ : ℝ) - (xLift i.castSucc : ℝ) = e₂ - e₁ := by
      change chain.point i.succ - chain.point i.castSucc = e₂ - e₁
      rw [hyeq, hxeq]
      ring
    have hratio' :
        (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) /
            ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) ∈ R := by
      rw [hmap', hden]
      exact hratio
    have hgap : 0 < (xLift i.succ : ℝ) - (xLift i.castSucc : ℝ) := by
      rw [hden]
      linarith
    have hlo : lam ≤
        (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) /
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) :=
      Finset.min'_le R _ hratio'
    have hup :
        (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) /
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) ≤ Λ :=
      Finset.le_max' R _ hratio'
    constructor
    · exact (le_div_iff₀ hgap).mp hlo |>.trans_eq (by rfl)
    · exact (div_le_iff₀ hgap).mp hup
  have hsourceTel :
      ∑ i : Fin chain.length,
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) = t.1.re - s.1.re := by
    let f : ℕ → ℝ := fun i =>
      (xLift ⟨min i chain.length,
        Nat.lt_succ_of_le (Nat.min_le_right i chain.length)⟩ : ℝ)
    calc
      ∑ i : Fin chain.length,
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) =
          ∑ i ∈ Finset.range chain.length, (f (i + 1) - f i) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            have hil : i < chain.length := Finset.mem_range.mp hi
            simp [f, hil, Nat.min_eq_left hil.le]
      _ = f chain.length - f 0 := Finset.sum_range_sub f chain.length
      _ = t.1.re - s.1.re := by
        have hfirst_re : (xLift 0 : ℝ) = s.1.re + e₀ := by
          change chain.point 0 = s.1.re + e₀
          exact chain.first
        have hlast_re : (xLift (Fin.last chain.length) : ℝ) =
            t.1.re + e₀ := by
          change chain.point (Fin.last chain.length) = t.1.re + e₀
          exact chain.last
        have hfin : (⟨chain.length,
            Nat.lt_succ_self chain.length⟩ : Fin (chain.length + 1)) =
            Fin.last chain.length := by apply Fin.ext; rfl
        simp [f, hfin, hfirst_re, hlast_re]
  have hmapTel :
      ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
        (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re := by
    let f : ℕ → ℝ := fun i =>
      mapScalar phi (xLift ⟨min i chain.length,
        Nat.lt_succ_of_le (Nat.min_le_right i chain.length)⟩)
    calc
      ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
          ∑ i ∈ Finset.range chain.length, (f (i + 1) - f i) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            have hil : i < chain.length := Finset.mem_range.mp hi
            simp [f, hil, Nat.min_eq_left hil.le]
      _ = f chain.length - f 0 := Finset.sum_range_sub f chain.length
      _ = (s06_fibreImage H phi t).re - (s06_fibreImage H phi s).re := by
        obtain ⟨v₀, hv₀⟩ := hvertex e₀ he₀
        let e₀Lift : C.coordinateSpace := ⟨e₀, by
          rw [← hv₀]
          exact C.vertex_re_mem v₀.1 v₀.2⟩
        have hfirst : xLift 0 =
            ⟨s.1.re, (s06_fibre_coordinateSpace_mem H s).1⟩ + e₀Lift := by
          apply Subtype.ext
          change chain.point 0 = s.1.re + e₀
          exact chain.first
        have hlast : xLift (Fin.last chain.length) =
            ⟨t.1.re, (s06_fibre_coordinateSpace_mem H t).1⟩ + e₀Lift := by
          apply Subtype.ext
          change chain.point (Fin.last chain.length) = t.1.re + e₀
          exact chain.last
        have hfin : (⟨chain.length,
            Nat.lt_succ_self chain.length⟩ : Fin (chain.length + 1)) =
            Fin.last chain.length := by apply Fin.ext; rfl
        simp [f, hfin, hfirst, hlast]
        simp only [mapScalar, map_add, Rat.cast_add, sub_eq_add_neg]
        ring_nf
        have htc :
            (⟨t.1.re, (s06_fibreCoordinateLift H t).2.1⟩ : C.coordinateSpace) =
              ⟨(s06_fibreCoordinateLift H t).1.re,
                (s06_fibreCoordinateLift H t).2.1⟩ := by
          apply Subtype.ext
          rfl
        have hsc :
            (⟨s.1.re, (s06_fibreCoordinateLift H s).2.1⟩ : C.coordinateSpace) =
              ⟨(s06_fibreCoordinateLift H s).1.re,
                (s06_fibreCoordinateLift H s).2.1⟩ := by
          apply Subtype.ext
          rfl
        change mapScalar phi
              (⟨t.1.re, (s06_fibreCoordinateLift H t).2.1⟩ : C.coordinateSpace) -
            mapScalar phi
              (⟨s.1.re, (s06_fibreCoordinateLift H s).2.1⟩ : C.coordinateSpace) = _
        rw [htc, hsc]
        simp [s06_fibreImage, mapPoint, mapScalar]
  have hsumlo :
      lam * ∑ i : Fin chain.length,
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) ≤
        ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (hstep i).1
  have hsumup :
      ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) ≤
      Λ * ∑ i : Fin chain.length,
          ((xLift i.succ : ℝ) - (xLift i.castSucc : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => (hstep i).2
  rw [hsourceTel, hmapTel] at hsumlo hsumup
  exact ⟨hsumlo, hsumup⟩

theorem horizontalColumn_globalOrder
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi) :
    Nonempty (HorizontalColumnOrderData C H phi) := by
  obtain ⟨G⟩ := s06_fibreGapWordData_exists H
  have hPne :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region
        G.relativeHeight).Nonempty := by
    rw [← G.slice_eq]
    exact G.slice_nonempty
  have hyfin : G.relativeHeight ∉ C.region.vertexFinset.image Complex.im := by
    intro hy
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hy
    have hp' : p ∈ (C.region.vertexFinset : Set Tiling.Plane) := by
      simpa using hp
    have hpv : p ∈ C.region.vertices := by
      simpa only [C.region.coe_vertexFinset] using hp'
    have hv : (⟨p, hpv⟩ : ↥C.region.vertices).1.im = G.relativeHeight := hpe
    exact G.relativeHeight_generic ⟨p, hpv⟩ hv
  obtain ⟨P, hvertex⟩ := s06_canonical_horizontal_presentation hyfin
  have hTile := sourceRow_genericSections_lineTile H G.relativeHeight
    hyfin hPne
  obtain ⟨lam, Λ, hlampos, hlamΛ, hbounds⟩ :=
    s06_fibreImage_bounds H phi D hvertex hPne hTile
  have horder : ∀ s t : ↥H.fibre, s.1.re < t.1.re →
      (s06_fibreImage H phi s).re < (s06_fibreImage H phi t).re := by
    intro s t hst
    exact s06_fibreImage_strictOrder H phi D hvertex hPne hTile s t hst
  let image : ↥H.fibre ↪ Tiling.Plane :=
    ⟨s06_fibreImage H phi,
      s06_fibreImage_injective_of_strictOrder H phi horder⟩
  refine ⟨{
    coordinateLift := s06_fibreCoordinateLift H
    coordinateLift_coe := fun s => rfl
    image := image
    image_apply := fun s => s06_fibreImage_apply H phi s
    lambda := lam
    Lambda := Λ
    lambda_pos := hlampos
    lambda_le_Lambda := hlamΛ
    horizontal_bounds := ?_
    common_secondCoordinate := ?_ }⟩
  · intro s t hst
    exact hbounds s t hst
  · intro s t
    exact s06_fibreImage_im_eq H phi s t

private theorem s06_labelledEndpoint_strictOrder
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (O : HorizontalColumnOrderData C H phi)
    {y : ℝ} (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (e f : LabelledHorizontalSectionEndpoint C H y)
    (hef : e.value < f.value) : e.imageValue D O < f.imageValue D O := by
  obtain ⟨G⟩ := s06_fibreGapWordData_exists H
  have hPne :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y).Nonempty := by
    have hcl : e.relative ∈ closure
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) :=
      e.relative_frontier.1
    rw [mem_closure_iff] at hcl
    have hne := hcl Set.univ isOpen_univ (by simp)
    simpa using hne
  obtain ⟨P, hvertex⟩ := s06_canonical_horizontal_presentation hy
  have hTile := sourceRow_genericSections_lineTile H y hy hPne
  have hvol := ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne
  have hLcoord : ∀ l ∈ (Complex.re '' H.fibre), l ∈ C.coordinateSpace := by
    intro l hl
    obtain ⟨z, hz, rfl⟩ := hl
    exact (s06_fibre_coordinateSpace_mem H ⟨z, hz⟩).1
  have heP : e.relative ∈ P.endpoints :=
    P.frontier_subset_endpoints e.relative_frontier
  have hfP : f.relative ∈ P.endpoints :=
    P.frontier_subset_endpoints f.relative_frontier
  have heE : e.value ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨e.centre.1.re, ⟨e.centre.1, e.centre.2, rfl⟩,
      e.relative, heP, by simp [LabelledHorizontalSectionEndpoint.value,
        add_comm]⟩
  have hfE : f.value ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨f.centre.1.re, ⟨f.centre.1, f.centre.2, rfl⟩,
      f.relative, hfP, by simp [LabelledHorizontalSectionEndpoint.value,
        add_comm]⟩
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top hvol
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
  obtain ⟨xf, hxf, hxfim⟩ := labelledEndpoint_coordinateLift_imageValue D O f
  obtain ⟨chain⟩ := OneDimensional.FiniteInterval.endpointChain_nonempty
    hlocal heE hfE (le_of_lt hef)
  have hpoint : ∀ i : Fin (chain.length + 1),
      chain.point i ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) := by
    intro i
    by_cases hilast : i = Fin.last chain.length
    · rw [hilast, chain.last]
      exact hfE
    · have hi : i.val < chain.length := by
        exact Nat.lt_of_le_of_ne (Fin.le_last i)
          (fun heq => hilast (Fin.ext heq))
      let j : Fin chain.length := ⟨i.val, hi⟩
      have hj : j.castSucc = i := Fin.ext rfl
      rw [← hj]
      exact (chain.consecutive j).1
  have hcoord : ∀ i : Fin (chain.length + 1), chain.point i ∈ C.coordinateSpace := by
    intro i
    obtain ⟨l, hl, a, ha, hia⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1
        (hpoint i)
    obtain ⟨v, hv⟩ := hvertex a ha
    rw [hia]
    exact C.coordinateSpace.add_mem (hLcoord l hl) (by
      rw [← hv]
      exact C.vertex_re_mem v.1 v.2)
  let xLift : Fin (chain.length + 1) → C.coordinateSpace := fun i =>
    ⟨chain.point i, hcoord i⟩
  have hstep : ∀ i : Fin chain.length,
      0 < mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc) := by
    intro i
    obtain ⟨l, hl, a₁, ha₁, a₂, ha₂, ha, hia, hib, q₁, q₂,
      hq₁, hq₂, hmap⟩ := s06_consecutive_map_gap hvertex hLcoord hvol hTile
      (chain.consecutive i) (xLift i.castSucc) (xLift i.succ) rfl rfl
    obtain ⟨r₁, r₂, hr₁, hr₂, hpos⟩ :=
      s06_mapped_endpoint_gap_pos (D := D) hvertex ha₁ ha₂ ha
    have hqeq₁ : q₁ = r₁ := Subtype.ext (hq₁.trans hr₁.symm)
    have hqeq₂ : q₂ = r₂ := Subtype.ext (hq₂.trans hr₂.symm)
    rw [hqeq₁, hqeq₂] at hmap
    exact hmap ▸ hpos
  have hlen : 0 < chain.length := by
    by_contra hz
    have hz' : chain.length = 0 := Nat.eq_zero_of_not_pos hz
    have heq : (chain.point 0 : ℝ) = chain.point (Fin.last chain.length) := by
      have hfin : (0 : Fin (chain.length + 1)) = Fin.last chain.length := by
        apply Fin.ext
        omega
      rw [hfin]
    rw [chain.first, chain.last] at heq
    linarith
  have hsumpos : 0 < ∑ i : Fin chain.length,
      (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) := by
    apply Finset.sum_pos (fun i _ => hstep i)
    exact ⟨⟨0, hlen⟩, by simp⟩
  have htel : ∑ i : Fin chain.length,
      (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
      mapScalar phi (xLift (Fin.last chain.length)) - mapScalar phi (xLift 0) := by
    let F : ℕ → ℝ := fun i =>
      mapScalar phi (xLift ⟨min i chain.length,
        Nat.lt_succ_of_le (Nat.min_le_right i chain.length)⟩)
    calc
      ∑ i : Fin chain.length,
          (mapScalar phi (xLift i.succ) - mapScalar phi (xLift i.castSucc)) =
          ∑ i ∈ Finset.range chain.length, (F (i + 1) - F i) := by
            rw [Finset.sum_fin_eq_sum_range]
            apply Finset.sum_congr rfl
            intro i hi
            have hil : i < chain.length := Finset.mem_range.mp hi
            simp [F, hil, Nat.min_eq_left hil.le]
      _ = F chain.length - F 0 := Finset.sum_range_sub F chain.length
      _ = mapScalar phi (xLift (Fin.last chain.length)) - mapScalar phi (xLift 0) := by
        have hfin : (⟨chain.length,
            Nat.lt_succ_self chain.length⟩ : Fin (chain.length + 1)) =
            Fin.last chain.length := by apply Fin.ext; rfl
        simp [F, hfin]
  have hfirst : xLift 0 = xe := by
    apply Subtype.ext
    change chain.point 0 = (xe : ℝ)
    rw [chain.first, hxe]
  have hlast : xLift (Fin.last chain.length) = xf := by
    apply Subtype.ext
    change chain.point (Fin.last chain.length) = (xf : ℝ)
    rw [chain.last, hxf]
  rw [hfirst, hlast, hxeim, hxfim] at htel
  exact sub_pos.mp (by rw [← htel]; exact hsumpos)

private theorem genericBand_endpointOrderTransport
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (y : ℝ) (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (e f : LabelledHorizontalSectionEndpoint C H y)
    (hef : e.value < f.value)
    (hsep : ∀ g : LabelledHorizontalSectionEndpoint C H y,
      g.value ≤ e.value ∨ f.value ≤ g.value) :
    e.imageValue D O < f.imageValue D O ∧
      ∀ g : LabelledHorizontalSectionEndpoint C H y,
        g.imageValue D O ≤ e.imageValue D O ∨
          f.imageValue D O ≤ g.imageValue D O := by
  have hstrict := s06_labelledEndpoint_strictOrder H D O hy e f hef
  refine ⟨hstrict, ?_⟩
  intro g
  rcases hsep g with hg | hg
  · rcases lt_or_eq_of_le hg with hlt | heq
    · exact Or.inl (le_of_lt (s06_labelledEndpoint_strictOrder H D O hy g e hlt))
    · have hcoord : e.value = g.value := heq.symm
      obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
      obtain ⟨xg, hxg, hxgim⟩ := labelledEndpoint_coordinateLift_imageValue D O g
      have hxeg : xe = xg := Subtype.ext (hxe.trans (hcoord.trans hxg.symm))
      have him : g.imageValue D O = e.imageValue D O := by
        calc
          g.imageValue D O = mapScalar phi xg := hxgim.symm
          _ = mapScalar phi xe := congrArg (mapScalar phi) hxeg.symm
          _ = e.imageValue D O := hxeim
      exact Or.inl (le_of_eq him)
  · rcases lt_or_eq_of_le hg with hlt | heq
    · exact Or.inr (le_of_lt (s06_labelledEndpoint_strictOrder H D O hy f g hlt))
    · have hcoord : f.value = g.value := heq
      obtain ⟨xf, hxf, hxfim⟩ := labelledEndpoint_coordinateLift_imageValue D O f
      obtain ⟨xg, hxg, hxgim⟩ := labelledEndpoint_coordinateLift_imageValue D O g
      have hxfg : xf = xg := Subtype.ext (hxf.trans (hcoord.trans hxg.symm))
      have him : f.imageValue D O = g.imageValue D O := by
        calc
          f.imageValue D O = mapScalar phi xf := hxfim.symm
          _ = mapScalar phi xg := congrArg (mapScalar phi) hxfg
          _ = g.imageValue D O := hxgim
      exact Or.inr (le_of_eq him)

private def horizontalPresentationLeftCoord
    {C : ApproximationContext} {y : ℝ}
    (S : Foundations.GenericSlices.HorizontalGenericSlicePresentation C.region y)
    (i : Fin S.n) : C.coordinateSpace :=
  ⟨S.left i, by
    rw [← S.leftVertex_coord i]
    exact C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩

private def horizontalPresentationRightCoord
    {C : ApproximationContext} {y : ℝ}
    (S : Foundations.GenericSlices.HorizontalGenericSlicePresentation C.region y)
    (i : Fin S.n) : C.coordinateSpace :=
  ⟨S.right i, by
    rw [← S.rightVertex_coord i]
    exact C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩

private theorem deformedHorizontalSlice_eq_mappedPresentation
    {C : ApproximationContext} {y : ℝ}
    (S : Foundations.GenericSlices.HorizontalGenericSlicePresentation C.region y)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    Foundations.GenericSlices.horizontalSlice D.deformedRegion
        (D.secondHomeomorph y) =
      ⋃ i : Fin S.n,
        Set.Ioo (mapScalar phi (horizontalPresentationLeftCoord S i))
          (mapScalar phi (horizontalPresentationRightCoord S i)) := by
  have hslice : Foundations.GenericSlices.horizontalSlice D.deformedRegion
        (D.secondHomeomorph y) =
      D.firstHomeomorph '' Foundations.GenericSlices.horizontalSlice C.region y := by
    ext x
    constructor
    · intro hx
      rw [Foundations.GenericSlices.horizontalSlice, D.deformedRegion_openCarrier] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      have hzim : z.im = y := by
        have h := congrArg Complex.im hzx
        rw [D.planarHomeomorph_apply] at h
        simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul,
          add_zero, zero_add, mul_one] at h
        exact D.secondHomeomorph.injective h
      have hzre : D.firstHomeomorph z.re = x := by
        have h := congrArg Complex.re hzx
        rw [D.planarHomeomorph_apply] at h
        simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
          zero_mul, sub_zero, add_zero, zero_add] using h
      refine ⟨z.re, ?_, hzre⟩
      change Complex.mk z.re y ∈ C.region.openCarrier
      have hz' : Complex.mk z.re y = z := by
        apply Complex.ext <;> simp [hzim]
      rw [hz']
      exact hz
    · rintro ⟨z, hz, rfl⟩
      rw [Foundations.GenericSlices.horizontalSlice, D.deformedRegion_openCarrier]
      refine ⟨Complex.mk z y, ?_, ?_⟩
      · exact hz
      · rw [D.planarHomeomorph_apply]
        apply Complex.ext <;> simp
  rw [hslice]
  calc
    D.firstHomeomorph '' Foundations.GenericSlices.horizontalSlice C.region y =
        D.firstHomeomorph '' (⋃ i : Fin S.n, Set.Ioo (S.left i) (S.right i)) :=
      congrArg (fun U : Set ℝ => D.firstHomeomorph '' U) (S.union_eq)
    _ = ⋃ i : Fin S.n,
        D.firstHomeomorph '' Set.Ioo (S.left i) (S.right i) := by
      rw [Set.image_iUnion]
    _ = ⋃ i : Fin S.n,
        Set.Ioo (mapScalar phi (horizontalPresentationLeftCoord S i))
          (mapScalar phi (horizontalPresentationRightCoord S i)) := by
      apply iUnion_congr
      intro i
      rw [D.firstHomeomorph.continuous.image_Ioo_of_strictMono
        D.firstHomeomorph_strictMono]
      have hleft : D.firstHomeomorph (S.left i) =
          mapScalar phi (horizontalPresentationLeftCoord S i) := by
        have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
        rw [D.planarHomeomorph_apply] at hv
        have hre := congrArg Complex.re hv
        have hcoord : horizontalPresentationLeftCoord S i =
            ⟨(S.leftVertex i).1.re,
              C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
          apply Subtype.ext
          exact (S.leftVertex_coord i).symm
        have hleft : S.left i = (S.leftVertex i).1.re :=
          (S.leftVertex_coord i).symm
        rw [hleft, hcoord]
        simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
      have hright : D.firstHomeomorph (S.right i) =
          mapScalar phi (horizontalPresentationRightCoord S i) := by
        have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
        rw [D.planarHomeomorph_apply] at hv
        have hre := congrArg Complex.re hv
        have hcoord : horizontalPresentationRightCoord S i =
            ⟨(S.rightVertex i).1.re,
              C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
          apply Subtype.ext
          exact (S.rightVertex_coord i).symm
        have hright : S.right i = (S.rightVertex i).1.re :=
          (S.rightVertex_coord i).symm
        rw [hright, hcoord]
        simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
      rw [hleft, hright]

private theorem lineTiles_mem_openUnion_of_not_mem_translatedEndpoints
    {B L : Set ℝ}
    (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hTile : OneDimensional.LineTiles B L)
    (hBpositive : 0 < (volume B).toReal) {x : ℝ}
    (hx : x ∉ OneDimensional.FiniteInterval.translatedEndpointSet P L) :
    x ∈ OneDimensional.FiniteInterval.lineOpenUnion B L := by
  have hlocal :=
    OneDimensional.FiniteInterval.finiteInterval_lineTilesOn_centres_locallyFinite
      P.isFiniteIntervalRegion hBpositive hTile
  have hclosedlocal :=
    OneDimensional.FiniteInterval.locallyFinite_closedTranslates_of_boundedWindowFinite
      P hlocal
  have hreg := OneDimensional.FiniteInterval.LineTilesOn.regularizedTarget_eq
    P hTile hBpositive isOpen_univ (by simp)
  have hxreg : x ∈ OneDimensional.FiniteInterval.regularizedTarget B L := by
    rw [hreg]
    exact mem_univ x
  by_contra hxo
  exact hx (regularizedTarget_diff_lineOpenUnion_subset_translatedEndpointSet
    P hclosedlocal ⟨hxreg, hxo⟩)

private def mappedTranslatedEndpointSet
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B) : Set ℝ :=
  {x | ∃ s : ↥H.fibre, ∃ e ∈ P.endpoints,
    x = (O.image s).re + D.firstHomeomorph e}

private theorem translatedEndpoint_coordinate_mem
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {B : Set ℝ}
    (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    {x : ℝ} (hx : x ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre)) :
    x ∈ C.coordinateSpace := by
  obtain ⟨l, hl, e, he, hxeq⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hx
  obtain ⟨z, hz, hzl⟩ := hl
  have hl_eq : l = z.re := hzl.symm
  subst l
  obtain ⟨v, hv⟩ := hvertex e he
  rw [hxeq]
  exact C.coordinateSpace.add_mem
    ((s06_fibre_coordinateSpace_mem H ⟨z, hz⟩).1) (by
      rw [← hv]
      exact C.vertex_re_mem v.1 v.2)

private theorem mappedTranslatedEndpointSet_mem
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    {x : ℝ} (hx : x ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre)) :
    mapScalar phi ⟨x, translatedEndpoint_coordinate_mem P hvertex hx⟩ ∈
      mappedTranslatedEndpointSet D O P := by
  obtain ⟨l, ⟨z, hz, rfl⟩, e, he, hxeq⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hx
  obtain ⟨v, hv⟩ := hvertex e he
  let lLift : C.coordinateSpace :=
    ⟨z.re, (s06_fibre_coordinateSpace_mem H ⟨z, hz⟩).1⟩
  let eLift : C.coordinateSpace :=
    ⟨e, by rw [← hv]; exact C.vertex_re_mem v.1 v.2⟩
  have hxLift :
      (⟨x, translatedEndpoint_coordinate_mem P hvertex hx⟩ : C.coordinateSpace) =
        lLift + eLift := by
    apply Subtype.ext
    change x = z.re + e
    exact hxeq
  refine ⟨⟨z, hz⟩, e, he, ?_⟩
  rw [hxLift, mapScalar, map_add]
  have hlmap : mapScalar phi lLift = (O.image ⟨z, hz⟩).re := by
    have hcoord :
        lLift = ⟨(O.coordinateLift ⟨z, hz⟩).1.re,
          (O.coordinateLift ⟨z, hz⟩).2.1⟩ := by
      apply Subtype.ext
      simpa [lLift] using (congrArg Complex.re (O.coordinateLift_coe ⟨z, hz⟩)).symm
    rw [hcoord]
    simpa [mapPoint, mapScalar] using
      (congrArg Complex.re (O.image_apply ⟨z, hz⟩)).symm
  have hemap : mapScalar phi eLift = D.firstHomeomorph e := by
    have hvmap := D.vertex_agreement v.1 v.2
    rw [D.planarHomeomorph_apply] at hvmap
    have hre := congrArg Complex.re hvmap
    rw [show eLift = ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ by
      apply Subtype.ext
      exact hv.symm]
    simpa [hv, mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  push_cast
  change mapScalar phi lLift + mapScalar phi eLift = _
  rw [hlmap, hemap]

private theorem mappedTranslatedEndpointSet_reverse
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hvertex : ∀ e ∈ P.endpoints, ∃ v : ↥C.region.vertices, v.1.re = e)
    {y : ℝ} (hy : y ∈ mappedTranslatedEndpointSet D O P) :
    ∃ (x : ℝ) (hx : x ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre)),
      y = mapScalar phi
        ⟨x, translatedEndpoint_coordinate_mem P hvertex hx⟩ := by
  rcases hy with ⟨s, e, he, rfl⟩
  let x : ℝ := s.1.re + e
  have hs : s.1.re ∈ Complex.re '' H.fibre := ⟨s.1, s.2, rfl⟩
  have hx : x ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre) := by
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
    exact ⟨s.1.re, hs, e, he, rfl⟩
  let lLift : C.coordinateSpace :=
    ⟨s.1.re, (s06_fibre_coordinateSpace_mem H s).1⟩
  obtain ⟨v, hv⟩ := hvertex e he
  let eLift : C.coordinateSpace :=
    ⟨e, by rw [← hv]; exact C.vertex_re_mem v.1 v.2⟩
  have hxLift :
      (⟨x, translatedEndpoint_coordinate_mem P hvertex hx⟩ : C.coordinateSpace) =
        lLift + eLift := by
    apply Subtype.ext
    simp [x, lLift, eLift]
  have hlmap : mapScalar phi lLift = (O.image s).re := by
    have hcoord :
        lLift = ⟨(O.coordinateLift s).1.re, (O.coordinateLift s).2.1⟩ := by
      apply Subtype.ext
      simpa [lLift] using (congrArg Complex.re (O.coordinateLift_coe s)).symm
    rw [hcoord]
    simpa [mapPoint, mapScalar] using (congrArg Complex.re (O.image_apply s)).symm
  have hemap : mapScalar phi eLift = D.firstHomeomorph e := by
    have hvmap := D.vertex_agreement v.1 v.2
    rw [D.planarHomeomorph_apply] at hvmap
    have hre := congrArg Complex.re hvmap
    rw [show eLift = ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ by
      apply Subtype.ext
      exact hv.symm]
    simpa [hv, mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  refine ⟨x, hx, ?_⟩
  rw [hxLift]
  calc
    (O.image s).re + D.firstHomeomorph e =
        mapScalar phi lLift + mapScalar phi eLift := by rw [hlmap, hemap]
    _ = mapScalar phi (lLift + eLift) := by
      simp only [mapScalar, map_add, Rat.cast_add]

private theorem targetTranslatedEndpointSet_eq_mapped
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    let P' : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion (D.secondHomeomorph y)) := {
      n := S.n
      left := fun i => mapScalar phi (horizontalPresentationLeftCoord S i)
      right := fun i => mapScalar phi (horizontalPresentationRightCoord S i)
      lt := fun i => by
        rw [show mapScalar phi (horizontalPresentationLeftCoord S i) =
          D.firstHomeomorph (S.left i) by
            have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
            rw [D.planarHomeomorph_apply] at hv
            have hre := congrArg Complex.re hv
            have hcoord : horizontalPresentationLeftCoord S i =
                ⟨(S.leftVertex i).1.re,
                  C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
              apply Subtype.ext
              exact (S.leftVertex_coord i).symm
            rw [hcoord, ← S.leftVertex_coord i]
            simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm]
        rw [show mapScalar phi (horizontalPresentationRightCoord S i) =
          D.firstHomeomorph (S.right i) by
            have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
            rw [D.planarHomeomorph_apply] at hv
            have hre := congrArg Complex.re hv
            have hcoord : horizontalPresentationRightCoord S i =
                ⟨(S.rightVertex i).1.re,
                  C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
              apply Subtype.ext
              exact (S.rightVertex_coord i).symm
            rw [hcoord, ← S.rightVertex_coord i]
            simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm]
        exact D.firstHomeomorph_strictMono (S.lt i)
      union_eq := deformedHorizontalSlice_eq_mappedPresentation S D }
    OneDimensional.FiniteInterval.translatedEndpointSet P'
        (Complex.re '' Set.range O.image) =
      mappedTranslatedEndpointSet D O P := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hmapleft (i : Fin S.n) :
      mapScalar phi (horizontalPresentationLeftCoord S i) =
        D.firstHomeomorph (S.left i) := by
    have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationLeftCoord S i =
        ⟨(S.leftVertex i).1.re,
          C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.leftVertex_coord i).symm
    rw [hcoord, ← S.leftVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  have hmapright (i : Fin S.n) :
      mapScalar phi (horizontalPresentationRightCoord S i) =
        D.firstHomeomorph (S.right i) := by
    have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationRightCoord S i =
        ⟨(S.rightVertex i).1.re,
          C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.rightVertex_coord i).symm
    rw [hcoord, ← S.rightVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  let P' : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y)) := {
    n := S.n
    left := fun i => mapScalar phi (horizontalPresentationLeftCoord S i)
    right := fun i => mapScalar phi (horizontalPresentationRightCoord S i)
    lt := fun i => by
      rw [hmapleft, hmapright]
      exact D.firstHomeomorph_strictMono (S.lt i)
    union_eq := deformedHorizontalSlice_eq_mappedPresentation S D }
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm, u, hu, hxu⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P').1 hx
    obtain ⟨z, ⟨s, hs, rfl⟩, rfl⟩ := hm
    obtain ⟨i, hi⟩ | ⟨i, hi⟩ := by
      simpa only [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
        Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] using hu
    · subst u
      refine ⟨s, S.left i, ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · calc
          x = (O.image s).re + P'.left i := hxu
          _ = (O.image s).re + D.firstHomeomorph (S.left i) := by
            rw [show P'.left i = D.firstHomeomorph (S.left i) by
              exact hmapleft i]
    · subst u
      refine ⟨s, S.right i, ?_, ?_⟩
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · calc
          x = (O.image s).re + P'.right i := hxu
          _ = (O.image s).re + D.firstHomeomorph (S.right i) := by
            rw [show P'.right i = D.firstHomeomorph (S.right i) by
              exact hmapright i]
  · rintro ⟨s, u, hu, rfl⟩
    apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P').2
    obtain ⟨i, hi⟩ | ⟨i, hi⟩ := by
      simpa only [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
        Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] using hu
    · refine ⟨(O.image s).re, ⟨O.image s, ⟨s, rfl⟩, rfl⟩,
        P'.left i, ?_, ?_⟩
      · exact Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · subst u
        simpa [P'] using congrArg (fun t : ℝ => (O.image s).re + t)
          (hmapleft i).symm
    · refine ⟨(O.image s).re, ⟨O.image s, ⟨s, rfl⟩, rfl⟩,
        P'.right i, ?_, ?_⟩
      · exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      · subst u
        simpa [P'] using congrArg (fun t : ℝ => (O.image s).re + t)
          (hmapright i).symm

private theorem image_centres_countable_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (O : HorizontalColumnOrderData C H phi) :
    (Complex.re '' Set.range O.image).Countable := by
  have hlimit : (H.limit.centres : Set Tiling.Plane).Countable := H.limit.tilesOn.1
  have hfibre : H.fibre.Countable := by
    apply hlimit.mono
    rw [H.fibre_eq]
    exact inter_subset_left
  let _ : Countable ↥H.fibre := hfibre.to_subtype
  rw [show Complex.re '' Set.range O.image =
      Set.range (fun s : ↥H.fibre => (O.image s).re) by
    ext x
    constructor
    · rintro ⟨z, ⟨s, rfl⟩, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨O.image s, ⟨s, rfl⟩, rfl⟩]
  exact Set.countable_range _
private theorem translatedEndpointSet_unbounded_local
    {B L : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hTile : OneDimensional.LineTiles B L)
    (hBpositive : 0 < (volume B).toReal) :
    ¬ BddAbove (OneDimensional.FiniteInterval.translatedEndpointSet P L) ∧
      ¬ BddBelow (OneDimensional.FiniteInterval.translatedEndpointSet P L) := by
  have hBne : B.Nonempty := by
    by_contra hB
    have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    rw [hB', measure_empty, ENNReal.toReal_zero] at hBpositive
    exact (lt_irrefl 0) hBpositive
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hBne
  have hBbounded : ∃ R : ℝ, B ⊆ Set.Icc (-R) R := by
    obtain ⟨R, hR⟩ := P.isBounded.subset_closedBall (0 : ℝ)
    refine ⟨R, ?_⟩
    simpa [Real.closedBall_eq_Icc] using hR
  constructor
  · intro hE
    obtain ⟨M, hM⟩ := hE
    obtain ⟨R, hBR⟩ := hBbounded
    have hLupper : ∀ l ∈ L, l ≤ M - e₀ := by
      intro l hl
      have hmem : l + e₀ ∈
          OneDimensional.FiniteInterval.translatedEndpointSet P L :=
        (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
          ⟨l, hl, e₀, he₀, rfl⟩
      linarith [hM hmem]
    have hUsub : OneDimensional.FiniteInterval.lineOpenUnion B L ⊆
        Set.Iic (M - e₀ + R) := by
      intro x hx
      rw [OneDimensional.FiniteInterval.lineOpenUnion, Set.mem_iUnion] at hx
      obtain ⟨l, ⟨b, hb, rfl⟩⟩ := hx
      have hb' := hBR hb
      change l.1 + b ≤ M - e₀ + R
      linarith [hLupper l l.2, hb'.2]
    have hUae : ∀ᵐ x : ℝ ∂volume,
        x ∈ OneDimensional.FiniteInterval.lineOpenUnion B L := by
      filter_upwards [OneDimensional.FiniteInterval.LineTilesOn.lineOpenUnion_ae hTile]
        with x hx
      exact hx.mpr (Set.mem_univ x)
    have hDense : Dense (OneDimensional.FiniteInterval.lineOpenUnion B L) :=
      (volume : Measure ℝ).dense_of_ae hUae
    have hUopen : IsOpen (Set.Ioi (M - e₀ + R)) := isOpen_Ioi
    have hUne : (Set.Ioi (M - e₀ + R)).Nonempty :=
      ⟨M - e₀ + R + 1, by simp⟩
    obtain ⟨x, hxU, hxOpen⟩ := hDense.exists_mem_open hUopen hUne
    have hxupper : x ≤ M - e₀ + R := by
      simpa only [Set.mem_Iic] using hUsub hxU
    have hxopen' : M - e₀ + R < x := by
      simpa only [Set.mem_Ioi] using hxOpen
    exact (not_lt_of_ge hxupper) hxopen'
  · intro hE
    obtain ⟨m, hm⟩ := hE
    obtain ⟨R, hBR⟩ := hBbounded
    have hLlower : ∀ l ∈ L, m - e₀ ≤ l := by
      intro l hl
      have hmem : l + e₀ ∈
          OneDimensional.FiniteInterval.translatedEndpointSet P L :=
        (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
          ⟨l, hl, e₀, he₀, rfl⟩
      linarith [hm hmem]
    have hUsub : OneDimensional.FiniteInterval.lineOpenUnion B L ⊆
        Set.Ici (m - e₀ - R) := by
      intro x hx
      rw [OneDimensional.FiniteInterval.lineOpenUnion, Set.mem_iUnion] at hx
      obtain ⟨l, ⟨b, hb, rfl⟩⟩ := hx
      have hb' := hBR hb
      change m - e₀ - R ≤ l.1 + b
      linarith [hLlower l l.2, hb'.1]
    have hUae : ∀ᵐ x : ℝ ∂volume,
        x ∈ OneDimensional.FiniteInterval.lineOpenUnion B L := by
      filter_upwards [OneDimensional.FiniteInterval.LineTilesOn.lineOpenUnion_ae hTile]
        with x hx
      exact hx.mpr (Set.mem_univ x)
    have hDense : Dense (OneDimensional.FiniteInterval.lineOpenUnion B L) :=
      (volume : Measure ℝ).dense_of_ae hUae
    have hUopen : IsOpen (Set.Iio (m - e₀ - R)) := isOpen_Iio
    have hUne : (Set.Iio (m - e₀ - R)).Nonempty :=
      ⟨m - e₀ - R - 1, by simp⟩
    obtain ⟨x, hxU, hxOpen⟩ := hDense.exists_mem_open hUopen hUne
    have hxlower : m - e₀ - R ≤ x := by
      simpa only [Set.mem_Ici] using hUsub hxU
    have hxopen' : x < m - e₀ - R := by
      simpa only [Set.mem_Iio] using hxOpen
    exact (not_le_of_gt hxopen') hxlower

private theorem mappedTranslatedEndpointSet_unbounded_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {B : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hTile : OneDimensional.LineTiles B (Complex.re '' H.fibre))
    (hBpositive : 0 < (volume B).toReal) :
    ¬ BddAbove (mappedTranslatedEndpointSet D O P) ∧
      ¬ BddBelow (mappedTranslatedEndpointSet D O P) := by
  have hBne : B.Nonempty := by
    by_contra hB
    have hB' : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hB
    rw [hB', measure_empty, ENNReal.toReal_zero] at hBpositive
    exact (lt_irrefl 0) hBpositive
  obtain ⟨e₀, he₀⟩ := P.endpoints_nonempty hBne
  obtain ⟨R, hBR⟩ := P.isBounded.subset_closedBall (0 : ℝ)
  have hclosure : closure B ⊆ Set.Icc (-R) R := by
    apply closure_minimal
    · simpa [Real.closedBall_eq_Icc] using hBR
    · exact isClosed_Icc
  have hendUpper : ∀ e ∈ P.endpoints, e ≤ R := by
    intro e he
    exact (hclosure (P.endpoint_subset_closure he)).2
  have hendLower : ∀ e ∈ P.endpoints, -R ≤ e := by
    intro e he
    exact (hclosure (P.endpoint_subset_closure he)).1
  have hsourceUnbounded := translatedEndpointSet_unbounded_local P hTile hBpositive
  let a : ↥H.fibre := ⟨H.anchor, H.anchor_mem_fibre⟩
  constructor
  · intro htarget
    obtain ⟨M, hM⟩ := htarget
    have hL : BddAbove (Complex.re '' H.fibre) := by
      refine ⟨max a.1.re
        (a.1.re + (M - D.firstHomeomorph e₀ - (O.image a).re) / O.lambda), ?_⟩
      intro l hl
      obtain ⟨z, hz, rfl⟩ := hl
      let s : ↥H.fibre := ⟨z, hz⟩
      have hmem : (O.image s).re + D.firstHomeomorph e₀ ∈
          mappedTranslatedEndpointSet D O P := ⟨s, e₀, he₀, rfl⟩
      have himage : (O.image s).re + D.firstHomeomorph e₀ ≤ M := hM hmem
      by_cases hsa : a.1.re < s.1.re
      · have hb := (O.horizontal_bounds a s hsa).1
        have hbound : O.lambda * (s.1.re - a.1.re) ≤
            M - D.firstHomeomorph e₀ - (O.image a).re := by
          nlinarith [hb, himage]
        have hdiv : s.1.re - a.1.re ≤
            (M - D.firstHomeomorph e₀ - (O.image a).re) / O.lambda := by
          apply (le_div_iff₀ O.lambda_pos).2
          simpa [mul_comm] using hbound
        exact le_max_of_le_right (by linarith)
      · exact le_max_of_le_left (le_of_not_gt hsa)
    obtain ⟨K, hK⟩ := hL
    apply hsourceUnbounded.1
    refine ⟨K + R, ?_⟩
    intro x hx
    obtain ⟨l, hl, e, he, rfl⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hx
    linarith [hK hl, hendUpper e he]
  · intro htarget
    obtain ⟨m, hm⟩ := htarget
    have hL : BddBelow (Complex.re '' H.fibre) := by
      refine ⟨min a.1.re
        (a.1.re - ((O.image a).re - (m - D.firstHomeomorph e₀)) / O.lambda), ?_⟩
      intro l hl
      obtain ⟨z, hz, rfl⟩ := hl
      let s : ↥H.fibre := ⟨z, hz⟩
      have hmem : (O.image s).re + D.firstHomeomorph e₀ ∈
          mappedTranslatedEndpointSet D O P := ⟨s, e₀, he₀, rfl⟩
      have himage : m ≤ (O.image s).re + D.firstHomeomorph e₀ := hm hmem
      by_cases hsa : s.1.re < a.1.re
      · have hb := (O.horizontal_bounds s a hsa).1
        have hbound : O.lambda * (a.1.re - s.1.re) ≤
            (O.image a).re - (m - D.firstHomeomorph e₀) := by
          nlinarith [hb, himage]
        have hdiv : a.1.re - s.1.re ≤
            ((O.image a).re - (m - D.firstHomeomorph e₀)) / O.lambda := by
          apply (le_div_iff₀ O.lambda_pos).2
          simpa [mul_comm] using hbound
        exact (min_le_right _ _).trans (by linarith)
      · exact (min_le_left _ _).trans (le_of_not_gt hsa)
    obtain ⟨K, hK⟩ := hL
    apply hsourceUnbounded.2
    refine ⟨K - R, ?_⟩
    intro x hx
    obtain ⟨l, hl, e, he, rfl⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hx
    linarith [hK hl, hendLower e he]

private theorem s06_horizontalPresentation_left_frontier
    {C : ApproximationContext} {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) (i : Fin S.n) :
    S.left i ∈ frontier
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
  have hopen : IsOpen
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    rw [S.union_eq]
    exact isOpen_iUnion fun i => isOpen_Ioo
  have hcl : S.left i ∈ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    rw [S.closure_eq, Set.mem_iUnion]
    exact ⟨i, ⟨le_rfl, (S.lt i).le⟩⟩
  have hnot : S.left i ∉
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    intro hu
    have hu' : S.left i ∈ ⋃ j : Fin S.n, Ioo (S.left j) (S.right j) := by
      simpa only [S.union_eq] using hu
    rw [Set.mem_iUnion] at hu'
    obtain ⟨j, hj⟩ := hu'
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.1)
    · rcases S.pairwise_gap i j hij with hgap | hgap
      · exact (not_lt_of_ge (S.lt i).le) (hgap.trans hj.1)
      · exact (not_lt_of_ge hj.2.le) hgap
  rw [frontier, hopen.interior_eq]
  exact ⟨hcl, hnot⟩

private theorem s06_horizontalPresentation_right_frontier
    {C : ApproximationContext} {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) (i : Fin S.n) :
    S.right i ∈ frontier
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
  have hopen : IsOpen
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    rw [S.union_eq]
    exact isOpen_iUnion fun i => isOpen_Ioo
  have hcl : S.right i ∈ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    rw [S.closure_eq, Set.mem_iUnion]
    exact ⟨i, ⟨(S.lt i).le, le_rfl⟩⟩
  have hnot : S.right i ∉
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    intro hu
    have hu' : S.right i ∈ ⋃ j : Fin S.n, Ioo (S.left j) (S.right j) := by
      simpa only [S.union_eq] using hu
    rw [Set.mem_iUnion] at hu'
    obtain ⟨j, hj⟩ := hu'
    by_cases hij : i = j
    · subst j
      exact (lt_irrefl _ hj.2)
    · rcases S.pairwise_gap i j hij with hgap | hgap
      · exact (not_lt_of_ge hj.1.le) hgap
      · exact (not_lt_of_ge (S.lt i).le) (hj.2.trans hgap)
  rw [frontier, hopen.interior_eq]
  exact ⟨hcl, hnot⟩

private theorem s06_labelled_of_horizontal_endpoint
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) (l : ↥H.fibre) (u : ℝ)
    (hu : u ∈
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq).endpoints) :
    ∃ e : LabelledHorizontalSectionEndpoint C H y,
      e.centre = l ∧ e.relative = u ∧ e.value = l.1.re + u := by
  simp only [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
    Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hu
  rcases hu with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · let e : LabelledHorizontalSectionEndpoint C H y := {
      centre := l
      relative := S.left i
      vertex := S.leftVertex i
      relative_eq := (S.leftVertex_coord i).symm
      relative_frontier := s06_horizontalPresentation_left_frontier S i }
    refine ⟨e, rfl, rfl, ?_⟩
    simp [e, LabelledHorizontalSectionEndpoint.value, add_comm]
  · let e : LabelledHorizontalSectionEndpoint C H y := {
      centre := l
      relative := S.right i
      vertex := S.rightVertex i
      relative_eq := (S.rightVertex_coord i).symm
      relative_frontier := s06_horizontalPresentation_right_frontier S i }
    refine ⟨e, rfl, rfl, ?_⟩
    simp [e, LabelledHorizontalSectionEndpoint.value, add_comm]

private theorem mappedEndpoint_strictMono_canonical
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    StrictMono (fun x : OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) =>
      mapScalar phi
        ⟨x.1, translatedEndpoint_coordinate_mem P (by
          intro e he
          simp only [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
            Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
          rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
          · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩) x.2⟩) := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hvertex : ∀ e ∈ P.endpoints,
      ∃ v : ↥C.region.vertices, v.1.re = e := by
    intro e he
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
    · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩
  intro x z hxz
  obtain ⟨l, hl, u, hu, hxu⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 x.2
  obtain ⟨m, hm, v, hv, hzv⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 z.2
  obtain ⟨lx, hlx, rfl⟩ := hl
  obtain ⟨mz, hmz, rfl⟩ := hm
  let sx : ↥H.fibre := ⟨lx, hlx⟩
  let sz : ↥H.fibre := ⟨mz, hmz⟩
  obtain ⟨ex, hexc, hexu, hexval⟩ :=
    s06_labelled_of_horizontal_endpoint H S sx u hu
  obtain ⟨ez, hezc, hezv, ezval⟩ :=
    s06_labelled_of_horizontal_endpoint H S sz v hv
  have hexlt : ex.value < ez.value := by
    calc
      ex.value = x.1 := by simpa [hexval, sx] using hxu.symm
      _ < z.1 := hxz
      _ = ez.value := by simpa [ezval, sz] using hzv
  obtain ⟨xx, hxx, hxxmap⟩ := labelledEndpoint_coordinateLift_imageValue D O ex
  obtain ⟨zz, hzz, hzzmap⟩ := labelledEndpoint_coordinateLift_imageValue D O ez
  have hxf : xx =
      ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩ := by
    apply Subtype.ext
    rw [hxx, hexval, hxu]
  have hzf : zz =
      ⟨z.1, translatedEndpoint_coordinate_mem P hvertex z.2⟩ := by
    apply Subtype.ext
    rw [hzz, ezval, hzv]
  rw [hxf] at hxxmap
  rw [hzf] at hzzmap
  calc
    mapScalar phi ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩ =
        LabelledHorizontalSectionEndpoint.imageValue D O ex := hxxmap
    _ < LabelledHorizontalSectionEndpoint.imageValue D O ez :=
      s06_labelledEndpoint_strictOrder H D O hy ex ez hexlt
    _ = mapScalar phi ⟨z.1, translatedEndpoint_coordinate_mem P hvertex z.2⟩ :=
      hzzmap.symm

private theorem mappedEndpointSet_locallyFinite_canonical
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre)) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (mappedTranslatedEndpointSet D O P ∩ Q).Finite := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hvertex : ∀ e ∈ P.endpoints,
      ∃ v : ↥C.region.vertices, v.1.re = e := by
    intro e he
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
    · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩
  let f : OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre) → ℝ := fun x =>
    mapScalar phi
      ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩
  have hfrange : Set.range f = mappedTranslatedEndpointSet D O P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact mappedTranslatedEndpointSet_mem D O P hvertex x.2
    · intro hz
      obtain ⟨x, hx, hzx⟩ := mappedTranslatedEndpointSet_reverse D O P hvertex hz
      exact ⟨⟨x, hx⟩, hzx.symm⟩
  have hf : StrictMono f := by
    exact mappedEndpoint_strictMono_canonical H D O hy S
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre) ∩ Q).Finite := by
    obtain ⟨_, _, _, _, hcentres, _⟩ :=
      Tiling.AxisParallel.Foundations.linePacking_uniformlySeparated
        hTile P.volume_ne_top
        (ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
    exact OneDimensional.FiniteInterval.translatedEndpointSet_boundedWindowFinite P hcentres
  have hupper : ¬ BddAbove
      (OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre)) → ¬ BddAbove (Set.range f) := by
    intro hE hr
    apply (mappedTranslatedEndpointSet_unbounded_local D O P hTile
      (ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)).1
    simpa [hfrange] using hr
  have hlower : ¬ BddBelow
      (OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre)) → ¬ BddBelow (Set.range f) := by
    intro hE hr
    apply (mappedTranslatedEndpointSet_unbounded_local D O P hTile
      (ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)).2
    simpa [hfrange] using hr
  intro Q hQ
  simpa [hfrange] using
    (Approximation.strictOrderImage_locallyFinite hf hlocal
      (fun hE => hupper hE)
      (fun hE => hlower hE) Q hQ)

private theorem consecutive_range_iff_strictMono
    {E : Set ℝ} {f : ↥E → ℝ} (hf : StrictMono f)
    {a b : ℝ} (ha : a ∈ E) (hb : b ∈ E) :
    OneDimensional.FiniteInterval.ConsecutiveIn E a b ↔
      OneDimensional.FiniteInterval.ConsecutiveIn (Set.range f)
        (f ⟨a, ha⟩) (f ⟨b, hb⟩) := by
  constructor
  · intro hab
    refine ⟨⟨⟨a, ha⟩, rfl⟩, ⟨⟨b, hb⟩, rfl⟩,
      hf hab.2.2.1, ?_⟩
    rw [Set.disjoint_left]
    rintro z ⟨c, rfl⟩ hz
    have hac : a < c.1 := hf.lt_iff_lt.mp hz.1
    have hcb : c.1 < b := hf.lt_iff_lt.mp hz.2
    exact Set.disjoint_left.mp hab.2.2.2 c.2 ⟨hac, hcb⟩
  · intro hab
    refine ⟨ha, hb, (hf.lt_iff_lt).mp hab.2.2.1, ?_⟩
    rw [Set.disjoint_left]
    rintro z hzE hzI
    have hfa : f ⟨a, ha⟩ < f ⟨z, hzE⟩ := hf hzI.1
    have hfb : f ⟨z, hzE⟩ < f ⟨b, hb⟩ := hf hzI.2
    exact Set.disjoint_left.mp hab.2.2.2
      ⟨⟨z, hzE⟩, rfl⟩ ⟨hfa, hfb⟩

private theorem mappedEndpoint_consecutive_iff
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    ∀ {a b : ℝ}
      (ha : a ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre))
      (hb : b ∈ OneDimensional.FiniteInterval.translatedEndpointSet P
        (Complex.re '' H.fibre)),
      OneDimensional.FiniteInterval.ConsecutiveIn
        (OneDimensional.FiniteInterval.translatedEndpointSet P
          (Complex.re '' H.fibre)) a b ↔
      OneDimensional.FiniteInterval.ConsecutiveIn
        (mappedTranslatedEndpointSet D O P)
        (mapScalar phi ((⟨a, translatedEndpoint_coordinate_mem P (by
          intro e he
          simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
            Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
          rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
          · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩)
          ha⟩ : C.coordinateSpace)))
        (mapScalar phi ((⟨b, translatedEndpoint_coordinate_mem P (by
          intro e he
          simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
            Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
          rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
          · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
          · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩)
          hb⟩ : C.coordinateSpace))) := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hvertex : ∀ e ∈ P.endpoints,
      ∃ v : ↥C.region.vertices, v.1.re = e := by
    intro e he
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
    · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩
  let f : OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre) → ℝ := fun x =>
    mapScalar phi ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩
  have hf : StrictMono f := mappedEndpoint_strictMono_canonical H D O hy S
  have hmap : Set.range f = mappedTranslatedEndpointSet D O P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact mappedTranslatedEndpointSet_mem D O P hvertex x.2
    · intro hz
      obtain ⟨x, hx, hzx⟩ := mappedTranslatedEndpointSet_reverse D O P hvertex hz
      exact ⟨⟨x, hx⟩, hzx.symm⟩
  intro a b ha hb
  have hca := consecutive_range_iff_strictMono hf ha hb
  rw [← hmap]
  simpa [f] using hca

private theorem s06_consecutive_endpoint_component
    {C : ApproximationContext} {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) {L : Set ℝ}
    (hBpositive : 0 < (volume
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)).toReal)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) L)
    {x y' : ℝ}
    (hxy : OneDimensional.FiniteInterval.ConsecutiveIn
      (OneDimensional.FiniteInterval.translatedEndpointSet
        (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
          S.lt S.union_eq) L) x y') :
    ∃ l ∈ L, ∃ i : Fin S.n,
      x = l + S.left i ∧ y' = l + S.right i := by
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hsource :=
    (Tiling.AxisParallel.Foundations.finiteOpenIntervals_source_iff_ae
      P.isFiniteIntervalRegion hBpositive).1 hTile
  have hmid : ∃ l ∈ L, (x + y') / 2 ∈ l +ᵥ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    have hm : (x + y') / 2 ∈ ⋃ l : L, l.1 +ᵥ closure
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
      rw [hsource.2.2]
      exact Set.mem_univ _
    rw [Set.mem_iUnion] at hm
    obtain ⟨l, hl⟩ := hm
    exact ⟨l.1, l.2, hl⟩
  let z : ℝ := (x + y') / 2
  obtain ⟨l, hl, hzcl⟩ := hmid
  have hxz : x < z := by dsimp [z]; linarith [hxy.2.2.1]
  have hzy : z < y' := by dsimp [z]; linarith [hxy.2.2.1]
  have hzcl' : z - l ∈ closure
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := by
    dsimp [z]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzcl
    simpa only [vadd_eq_add, sub_eq_add_neg, add_comm] using hzcl
  have hzB : z - l ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    by_contra hzB
    have he : z - l ∈ (P.endpoints : Set ℝ) :=
      P.closure_diff_subset_endpoints ⟨hzcl', hzB⟩
    have hzE : z ∈ OneDimensional.FiniteInterval.translatedEndpointSet P L :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
        ⟨l, hl, z - l, he, by ring⟩
    exact Set.disjoint_left.1 hxy.2.2.2 hzE ⟨hxz, hzy⟩
  rw [P.union_eq, Set.mem_iUnion] at hzB
  obtain ⟨i, hi⟩ := hzB
  have hleftEnd : P.left i ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hrightEnd : P.right i ∈ P.endpoints := by
    rw [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union]
    exact Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hleftE : l + P.left i ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.left i, hleftEnd, rfl⟩
  have hrightE : l + P.right i ∈
      OneDimensional.FiniteInterval.translatedEndpointSet P L :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      ⟨l, hl, P.right i, hrightEnd, rfl⟩
  have hleft_le_x : l + P.left i ≤ x := by
    by_contra h
    have hxleft : x < l + P.left i := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hleftE
      ⟨hxleft, lt_trans (by linarith [hi.1]) hzy⟩
  have hy_le_right : y' ≤ l + P.right i := by
    by_contra h
    have hrighty : l + P.right i < y' := lt_of_not_ge h
    exact Set.disjoint_left.1 hxy.2.2.2 hrightE
      ⟨lt_trans hxz (by linarith [hi.2]), hrighty⟩
  have hend_not_mem : ∀ e ∈ P.endpoints, e ∉
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    intro e he heB
    rw [P.union_eq] at heB
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp heB
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · by_cases hij : i = j
      · subst j
        exact (lt_irrefl _ hj.1)
      · rcases S.pairwise_gap i j hij with hgap | hgap
        · exact (not_lt_of_ge (S.lt i).le) (hgap.trans hj.1)
        · exact (lt_irrefl _ (hj.2.trans hgap))
    · by_cases hij : i = j
      · subst j
        exact (lt_irrefl _ hj.2)
      · rcases S.pairwise_gap i j hij with hgap | hgap
        · exact (not_lt_of_ge hgap.le) hj.1
        · exact (lt_irrefl _ (hgap.trans ((S.lt i).trans hj.2)))
  have hx_eq : x = l + P.left i := by
    by_contra heq
    have hlt : l + P.left i < x := lt_of_le_of_ne hleft_le_x (Ne.symm heq)
    have hx_mem : x ∈ l +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      simp only [vadd_eq_add]
      constructor <;> linarith [hlt, hi.2, hxy.2.2.1]
    obtain ⟨m, hm, ex, hex, hxeq⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hxy.1
    have hm_eq_l : m = l := by
      by_contra hml
      exact OneDimensional.FiniteInterval.endpoint_not_mem_other_openTile
        P hTile.2.2.2.1 hm hl hml hex (hxeq ▸ hx_mem)
    have hexB : ex ∈
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx_mem
      simpa [hxeq, hm_eq_l, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hx_mem
    exact hend_not_mem ex hex hexB
  have hy_eq : y' = l + P.right i := by
    by_contra heq
    have hlt : y' < l + P.right i := lt_of_le_of_ne hy_le_right heq
    have hy_mem : y' ∈ l +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      simp only [vadd_eq_add]
      constructor <;> linarith [hi.1, hlt, hxy.2.2.1]
    obtain ⟨n, hn, ey, hey, hyeq⟩ :=
      (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hxy.2.1
    have hn_eq_l : n = l := by
      by_contra hnl
      exact OneDimensional.FiniteInterval.endpoint_not_mem_other_openTile
        P hTile.2.2.2.1 hn hl hnl hey (hyeq ▸ hy_mem)
    have heyB : ey ∈
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy_mem
      simpa [hyeq, hn_eq_l, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hy_mem
    exact hend_not_mem ey hey heyB
  exact ⟨l, hl, i, by simpa [P] using hx_eq, by simpa [P] using hy_eq⟩

private theorem endpoint_map_wellDefined_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    {s t : ↥H.fibre} {u v : ℝ}
    (hu : u ∈ (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
      S.lt S.union_eq).endpoints)
    (hv : v ∈ (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
      S.lt S.union_eq).endpoints)
    (heq : s.1.re + u = t.1.re + v) :
    (O.image s).re + D.firstHomeomorph u =
      (O.image t).re + D.firstHomeomorph v := by
  obtain ⟨e, hec, heu, _⟩ := s06_labelled_of_horizontal_endpoint H S s u hu
  obtain ⟨g, hgc, hgv, _⟩ := s06_labelled_of_horizontal_endpoint H S t v hv
  obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
  obtain ⟨xg, hxg, hxgim⟩ := labelledEndpoint_coordinateLift_imageValue D O g
  have hxeq : xe = xg := by
    apply Subtype.ext
    have hval : e.value = g.value := by
      simpa [LabelledHorizontalSectionEndpoint.value, hec, hgc, heu, hgv,
        add_comm] using heq
    exact (hxe.trans hval).trans hxg.symm
  have himage : e.imageValue D O = g.imageValue D O := by
    calc
      e.imageValue D O = mapScalar phi xe := hxeim.symm
      _ = mapScalar phi xg := congrArg (mapScalar phi) hxeq
      _ = g.imageValue D O := hxgim
  simpa [LabelledHorizontalSectionEndpoint.imageValue, hec, hgc, heu, hgv,
    add_comm] using himage

private theorem endpoint_map_formula_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) {x : ℝ}
    (hx : x ∈ OneDimensional.FiniteInterval.translatedEndpointSet
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq) (Complex.re '' H.fibre)) :
    ∃ s : ↥H.fibre, ∃ u ∈
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq).endpoints,
      x = s.1.re + u ∧
      ∃ q : C.coordinateSpace, (q : ℝ) = x ∧
        mapScalar phi q = (O.image s).re + D.firstHomeomorph u := by
  obtain ⟨l, hl, u, hu, hxu⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq)).1 hx
  obtain ⟨s, hs, hsl⟩ := hl
  obtain ⟨e, hec, heu, _⟩ := s06_labelled_of_horizontal_endpoint H S ⟨s, hs⟩ u hu
  obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
  let xcoord : C.coordinateSpace := ⟨x, translatedEndpoint_coordinate_mem
    (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
      S.lt S.union_eq) (by
        intro q hq
        simp only [OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
          Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hq
        rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨S.leftVertex i, by simpa using S.leftVertex_coord i⟩
        · exact ⟨S.rightVertex i, by simpa using S.rightVertex_coord i⟩) hx⟩
  have hxeq : xe =
      xcoord := by
    apply Subtype.ext
    rw [hxe]
    calc
      e.value = (⟨s, hs⟩ : ↥H.fibre).1.re + u := by
        simp [LabelledHorizontalSectionEndpoint.value, hec, heu, add_comm]
      _ = l + u := by rw [hsl]
      _ = x := hxu.symm
  rw [hxeq] at hxeim
  have hxu' : x = (⟨s, hs⟩ : ↥H.fibre).1.re + u := by
    simpa [hsl] using hxu
  refine ⟨⟨s, hs⟩, u, hu, hxu', ⟨xcoord, rfl, ?_⟩⟩
  simpa [LabelledHorizontalSectionEndpoint.imageValue, hec, heu,
    add_comm] using hxeim

private theorem mapped_target_consecutive_gap_mem_openUnion
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre)) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    ∀ {a b : ℝ},
      OneDimensional.FiniteInterval.ConsecutiveIn
        (mappedTranslatedEndpointSet D O P) a b →
      Set.Ioo a b ⊆
        OneDimensional.FiniteInterval.lineOpenUnion
          (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
            D.deformedRegion (D.secondHomeomorph y))
          (Complex.re '' Set.range O.image) := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hvertex : ∀ e ∈ P.endpoints,
      ∃ v : ↥C.region.vertices, v.1.re = e := by
    intro e he
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
    · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩
  let f : OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre) → ℝ := fun x =>
    mapScalar phi ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩
  have hf : StrictMono f := mappedEndpoint_strictMono_canonical H D O hy S
  have hmap : Set.range f = mappedTranslatedEndpointSet D O P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact mappedTranslatedEndpointSet_mem D O P hvertex x.2
    · intro hz
      obtain ⟨x, hx, hzx⟩ := mappedTranslatedEndpointSet_reverse D O P hvertex hz
      exact ⟨⟨x, hx⟩, hzx.symm⟩
  have hleftMap (i : Fin S.n) :
      D.firstHomeomorph (S.left i) =
        mapScalar phi (horizontalPresentationLeftCoord S i) := by
    have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationLeftCoord S i =
        ⟨(S.leftVertex i).1.re,
          C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.leftVertex_coord i).symm
    rw [hcoord, ← S.leftVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
  have hrightMap (i : Fin S.n) :
      D.firstHomeomorph (S.right i) =
        mapScalar phi (horizontalPresentationRightCoord S i) := by
    have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationRightCoord S i =
        ⟨(S.rightVertex i).1.re,
          C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.rightVertex_coord i).symm
    rw [hcoord, ← S.rightVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
  intro a b hab x hx
  obtain ⟨a₀, ha₀, haEq⟩ := mappedTranslatedEndpointSet_reverse D O P hvertex hab.1
  obtain ⟨b₀, hb₀, hbEq⟩ := mappedTranslatedEndpointSet_reverse D O P hvertex hab.2.1
  have hrangeCon : OneDimensional.FiniteInterval.ConsecutiveIn
      (Set.range f) (f ⟨a₀, ha₀⟩) (f ⟨b₀, hb₀⟩) := by
    rw [hmap]
    simpa [haEq, hbEq] using hab
  have hsourceCon := (consecutive_range_iff_strictMono hf ha₀ hb₀).2 hrangeCon
  obtain ⟨l, hl, i, haLi, hbLi⟩ :=
    s06_consecutive_endpoint_component S
      (ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne)
      hTile hsourceCon
  obtain ⟨s, hs, hsl⟩ := hl
  let s0 : ↥H.fibre := ⟨s, hs⟩
  have hsl0 : s0.1.re = l := by simpa [s0] using hsl
  obtain ⟨la, hla, ua, hua, haRep⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 ha₀
  obtain ⟨sa, hsa, hsaeq⟩ := hla
  obtain ⟨lb, hlb, ub, hub, hbRep⟩ :=
    (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).1 hb₀
  obtain ⟨sb, hsb, hsbeq⟩ := hlb
  have haMap0 : f ⟨a₀, ha₀⟩ = (O.image ⟨sa, hsa⟩).re + D.firstHomeomorph ua := by
    dsimp [f]
    obtain ⟨e, hec, heu, _⟩ :=
      s06_labelled_of_horizontal_endpoint H S ⟨sa, hsa⟩ ua hua
    obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
    have hxeq : xe =
        ⟨a₀, translatedEndpoint_coordinate_mem P hvertex ha₀⟩ := by
      apply Subtype.ext
      rw [hxe]
      calc
        e.value = (⟨sa, hsa⟩ : ↥H.fibre).1.re + ua := by
          simp [LabelledHorizontalSectionEndpoint.value, hec, heu, add_comm]
        _ = la + ua := by rw [hsaeq]
        _ = a₀ := haRep.symm
    rw [hxeq] at hxeim
    simpa [LabelledHorizontalSectionEndpoint.imageValue, hec, heu,
      add_comm] using hxeim
  have hbMap0 : f ⟨b₀, hb₀⟩ = (O.image ⟨sb, hsb⟩).re + D.firstHomeomorph ub := by
    dsimp [f]
    obtain ⟨e, hec, heu, _⟩ :=
      s06_labelled_of_horizontal_endpoint H S ⟨sb, hsb⟩ ub hub
    obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
    have hxeq : xe =
        ⟨b₀, translatedEndpoint_coordinate_mem P hvertex hb₀⟩ := by
      apply Subtype.ext
      rw [hxe]
      calc
        e.value = (⟨sb, hsb⟩ : ↥H.fibre).1.re + ub := by
          simp [LabelledHorizontalSectionEndpoint.value, hec, heu, add_comm]
        _ = lb + ub := by rw [hsbeq]
        _ = b₀ := hbRep.symm
    rw [hxeq] at hxeim
    simpa [LabelledHorizontalSectionEndpoint.imageValue, hec, heu,
      add_comm] using hxeim
  have hleftEndS : S.left i ∈
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq).endpoints := by
    simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints]
  have hrightEndS : S.right i ∈
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq).endpoints := by
    simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints]
  have hwellA : (O.image ⟨sa, hsa⟩).re + D.firstHomeomorph ua =
      (O.image s0).re + D.firstHomeomorph (S.left i) := by
    apply endpoint_map_wellDefined_local H D O S hua hleftEndS
    calc
      sa.re + ua = a₀ := by
        calc
          sa.re + ua = la + ua := by rw [hsaeq]
          _ = a₀ := haRep.symm
      _ = l + S.left i := haLi
      _ = s0.1.re + S.left i := by rw [hsl0]
  have hwellB : (O.image ⟨sb, hsb⟩).re + D.firstHomeomorph ub =
      (O.image s0).re + D.firstHomeomorph (S.right i) := by
    apply endpoint_map_wellDefined_local H D O S hub hrightEndS
    calc
      sb.re + ub = b₀ := by
        calc
          sb.re + ub = lb + ub := by rw [hsbeq]
          _ = b₀ := hbRep.symm
      _ = l + S.right i := hbLi
      _ = s0.1.re + S.right i := by rw [hsl0]
  have haMap' : a = (O.image s0).re + D.firstHomeomorph (S.left i) := by
    calc
      a = f ⟨a₀, ha₀⟩ := haEq
      _ = (O.image ⟨sa, hsa⟩).re + D.firstHomeomorph ua := haMap0
      _ = _ := hwellA
  have hbMap' : b = (O.image s0).re + D.firstHomeomorph (S.right i) := by
    calc
      b = f ⟨b₀, hb₀⟩ := hbEq
      _ = (O.image ⟨sb, hsb⟩).re + D.firstHomeomorph ub := hbMap0
      _ = _ := hwellB
  let q := D.firstHomeomorph.symm (x - (O.image s0).re)
  have hqleft : S.left i < q := by
    apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
    rw [D.firstHomeomorph.apply_symm_apply]
    linarith [hx.1, haMap']
  have hqright : q < S.right i := by
    apply D.firstHomeomorph_strictMono.lt_iff_lt.mp
    rw [D.firstHomeomorph.apply_symm_apply]
    linarith [hx.2, hbMap']
  have hqbase : q ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
    rw [S.union_eq, Set.mem_iUnion]
    exact ⟨i, ⟨hqleft, hqright⟩⟩
  have hqtarget : D.firstHomeomorph q ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y) := by
    rw [deformedHorizontalSlice_eq_mappedPresentation S D, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [← hleftMap i, ← hrightMap i]
    exact ⟨D.firstHomeomorph_strictMono hqleft,
      D.firstHomeomorph_strictMono hqright⟩
  rw [OneDimensional.FiniteInterval.lineOpenUnion, Set.mem_iUnion]
  refine ⟨⟨(O.image s0).re, ⟨O.image s0, ⟨s0, rfl⟩, rfl⟩⟩, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simpa [vadd_eq_add, q, sub_eq_add_neg, add_comm] using hqtarget

private theorem endpoint_component_formula_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y) {s : ↥H.fibre} {u : ℝ}
    (hu : u ∈
      (OneDimensional.FiniteInterval.IntervalPresentation.mk S.n S.left S.right
        S.lt S.union_eq).endpoints) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    mapScalar phi ⟨s.1.re + u, translatedEndpoint_coordinate_mem P (by
      intro e he
      simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
        Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
      rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
      · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩)
      ((OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
        ⟨s.1.re, ⟨s.1, s.2, rfl⟩, u, hu, rfl⟩)⟩ =
      (O.image s).re + D.firstHomeomorph u := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  obtain ⟨e, hec, heu, _⟩ := s06_labelled_of_horizontal_endpoint H S s u hu
  obtain ⟨xe, hxe, hxeim⟩ := labelledEndpoint_coordinateLift_imageValue D O e
  have hxeq : xe =
      ⟨s.1.re + u, translatedEndpoint_coordinate_mem P (by
        intro q hq
        simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
          Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hq
        rcases hq with ⟨i, rfl⟩ | ⟨i, rfl⟩
        · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
        · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩)
        ((OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
          ⟨s.1.re, ⟨s.1, s.2, rfl⟩, u, hu, rfl⟩)⟩ := by
    apply Subtype.ext
    rw [hxe]
    simp [LabelledHorizontalSectionEndpoint.value, hec, heu, add_comm]
  rw [hxeq] at hxeim
  simpa [LabelledHorizontalSectionEndpoint.imageValue, hec, heu, add_comm]
    using hxeim

private theorem target_mem_openUnion_of_not_mem_endpoints
    {B L E : Set ℝ}
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite)
    (hupper : ¬ BddAbove E) (hlower : ¬ BddBelow E)
    (hgap : ∀ {a b : ℝ},
      OneDimensional.FiniteInterval.ConsecutiveIn E a b →
        Set.Ioo a b ⊆ OneDimensional.FiniteInterval.lineOpenUnion B L)
    {x : ℝ} (hx : x ∉ E) :
    x ∈ OneDimensional.FiniteInterval.lineOpenUnion B L := by
  obtain ⟨a, haE, hax⟩ := (not_bddBelow_iff.1 hlower) x
  obtain ⟨b, hbE, hxb⟩ := (not_bddAbove_iff.1 hupper) x
  have hax' : a ≤ x := hax.le
  have hxb' : x ≤ b := hxb.le
  obtain ⟨a', ha'E, ha'x, ha'greatest⟩ :=
    Approximation.exists_greatest_mem_le_of_boundedWindowFinite hlocal ⟨a, haE, hax'⟩
  obtain ⟨b', hb'E, hxb', hb'least⟩ :=
    Approximation.exists_least_mem_ge_of_boundedWindowFinite hlocal ⟨b, hbE, hxb'⟩
  have hneA : x ≠ a' := by
    intro hxa
    apply hx
    rw [hxa]
    exact ha'E
  have hneB : x ≠ b' := by
    intro hxb
    apply hx
    rw [hxb]
    exact hb'E
  have ha'xlt : a' < x := lt_of_le_of_ne ha'x hneA.symm
  have hxb'lt : x < b' := lt_of_le_of_ne hxb' hneB
  have hab' : OneDimensional.FiniteInterval.ConsecutiveIn E a' b' := by
    refine ⟨ha'E, hb'E, lt_trans ha'xlt hxb'lt, ?_⟩
    rw [Set.disjoint_left]
    intro c hcE hcI
    rcases le_total c x with hcx | hxc
    · exact (not_lt_of_ge (ha'greatest c hcE hcx)) hcI.1
    · exact (not_lt_of_ge (hb'least c hcE hxc)) hcI.2
  exact hgap hab' ⟨ha'xlt, hxb'lt⟩

private theorem mapped_target_mem_openUnion_of_not_mem_endpoints
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre)) :
    let P : OneDimensional.FiniteInterval.IntervalPresentation
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
      n := S.n
      left := S.left
      right := S.right
      lt := S.lt
      union_eq := S.union_eq }
    ∀ {x : ℝ}, x ∉ mappedTranslatedEndpointSet D O P →
      x ∈ OneDimensional.FiniteInterval.lineOpenUnion
        (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion (D.secondHomeomorph y))
        (Complex.re '' Set.range O.image) := by
  dsimp
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hpos : 0 < (volume
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)).toReal :=
    ColumnSlices.finiteIntervalRegion_volume_toReal_pos P.isFiniteIntervalRegion hPne
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (mappedTranslatedEndpointSet D O P ∩ Q).Finite :=
    mappedEndpointSet_locallyFinite_canonical H D O hy S hPne hTile
  have hunb := mappedTranslatedEndpointSet_unbounded_local D O P hTile hpos
  intro x hx
  apply target_mem_openUnion_of_not_mem_endpoints hlocal hunb.1 hunb.2
    (mapped_target_consecutive_gap_mem_openUnion H D O hy S hPne hTile) hx

private theorem source_translates_disjoint_local
    {B L : Set ℝ} (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hTile : OneDimensional.LineTiles B L)
    {s t : ℝ} (hs : s ∈ L) (ht : t ∈ L) (hst : s ≠ t) :
    Disjoint (s +ᵥ B) (t +ᵥ B) := by
  rw [Set.disjoint_left]
  intro z hzs hzt
  have hopen : IsOpen B := P.isOpen
  have hne : ((s +ᵥ B) ∩ (t +ᵥ B)).Nonempty := ⟨z, hzs, hzt⟩
  have hpos : 0 < volume ((s +ᵥ B) ∩ (t +ᵥ B)) :=
    ((hopen.vadd s).inter (hopen.vadd t)).measure_pos volume hne
  have hzero := hTile.2.2.2.1 hs ht hst
  exact hpos.ne' hzero

private theorem mapped_target_pairwise_aedisjoint
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (S : Tiling.AxisParallel.Foundations.GenericSlices.HorizontalGenericSlicePresentation
      C.region y)
    (_hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty)
    (hTile : OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (Complex.re '' H.fibre)) :
    Set.Pairwise (Complex.re '' Set.range O.image)
      (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
        ((· +ᵥ (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion (D.secondHomeomorph y))) : ℝ → Set ℝ)) := by
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hvertex : ∀ e ∈ P.endpoints,
      ∃ v : ↥C.region.vertices, v.1.re = e := by
    intro e he
    simp only [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints,
      Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at he
    rcases he with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨S.leftVertex i, by simpa [P] using S.leftVertex_coord i⟩
    · exact ⟨S.rightVertex i, by simpa [P] using S.rightVertex_coord i⟩
  let f : OneDimensional.FiniteInterval.translatedEndpointSet P
      (Complex.re '' H.fibre) → ℝ := fun x =>
    mapScalar phi ⟨x.1, translatedEndpoint_coordinate_mem P hvertex x.2⟩
  have hf : StrictMono f := mappedEndpoint_strictMono_canonical H D O hy S
  have hleftMap (i : Fin S.n) :
      D.firstHomeomorph (S.left i) =
        mapScalar phi (horizontalPresentationLeftCoord S i) := by
    have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationLeftCoord S i =
        ⟨(S.leftVertex i).1.re,
          C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.leftVertex_coord i).symm
    rw [hcoord, ← S.leftVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
  have hrightMap (i : Fin S.n) :
      D.firstHomeomorph (S.right i) =
        mapScalar phi (horizontalPresentationRightCoord S i) := by
    have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationRightCoord S i =
        ⟨(S.rightVertex i).1.re,
          C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.rightVertex_coord i).symm
    rw [hcoord, ← S.rightVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩ _ ⟨_, ⟨t, rfl⟩, rfl⟩ hne
  have hst : s ≠ t := by
    intro hst
    apply hne
    rw [hst]
  have hstRe : s.1.re ≠ t.1.re := by
    intro hstRe
    apply hst
    apply Subtype.ext
    apply Complex.ext
    · exact hstRe
    · have hs' : s.1 ∈ (H.limit.centres : Set Plane) ∩
          {z | z.im = H.anchor.im} := by
        rw [← H.fibre_eq]
        exact s.2
      have ht' : t.1 ∈ (H.limit.centres : Set Plane) ∩
          {z | z.im = H.anchor.im} := by
        rw [← H.fibre_eq]
        exact t.2
      exact hs'.2.trans ht'.2.symm
  have hsL : s.1.re ∈ Complex.re '' H.fibre := ⟨s.1, s.2, rfl⟩
  have htL : t.1.re ∈ Complex.re '' H.fibre := ⟨t.1, t.2, rfl⟩
  have hsrcDisj : Disjoint
      (s.1.re +ᵥ Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y)
      (t.1.re +ᵥ Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) :=
    source_translates_disjoint_local P hTile hsL htL hstRe
  have htgtDisj : Disjoint
      ((O.image s).re +ᵥ Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y))
      ((O.image t).re +ᵥ Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y)) := by
    rw [Set.disjoint_left]
    intro z hzS hzT
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzS hzT
    rw [deformedHorizontalSlice_eq_mappedPresentation S D] at hzS hzT
    obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzS
    obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hzT
    have hleftS : (s.1.re + S.left i) ∈
        OneDimensional.FiniteInterval.translatedEndpointSet P
          (Complex.re '' H.fibre) := by
      apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      exact ⟨s.1.re, hsL, S.left i,
        by simp [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints], rfl⟩
    have hrightS : (s.1.re + S.right i) ∈
        OneDimensional.FiniteInterval.translatedEndpointSet P
          (Complex.re '' H.fibre) := by
      apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      exact ⟨s.1.re, hsL, S.right i,
        by simp [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints], rfl⟩
    have hleftT : (t.1.re + S.left j) ∈
        OneDimensional.FiniteInterval.translatedEndpointSet P
          (Complex.re '' H.fibre) := by
      apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      exact ⟨t.1.re, htL, S.left j,
        by simp [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints], rfl⟩
    have hrightT : (t.1.re + S.right j) ∈
        OneDimensional.FiniteInterval.translatedEndpointSet P
          (Complex.re '' H.fibre) := by
      apply (OneDimensional.FiniteInterval.mem_translatedEndpointSet_iff P).2
      exact ⟨t.1.re, htL, S.right j,
        by simp [P, OneDimensional.FiniteInterval.IntervalPresentation.endpoints], rfl⟩
    have hmapSleft : f ⟨s.1.re + S.left i, hleftS⟩ =
        (O.image s).re + D.firstHomeomorph (S.left i) := by
      exact endpoint_component_formula_local H D O S (by
        simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints])
    have hmapSright : f ⟨s.1.re + S.right i, hrightS⟩ =
        (O.image s).re + D.firstHomeomorph (S.right i) := by
      exact endpoint_component_formula_local H D O S (by
        simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints])
    have hmapTleft : f ⟨t.1.re + S.left j, hleftT⟩ =
        (O.image t).re + D.firstHomeomorph (S.left j) := by
      exact endpoint_component_formula_local H D O S (by
        simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints])
    have hmapTright : f ⟨t.1.re + S.right j, hrightT⟩ =
        (O.image t).re + D.firstHomeomorph (S.right j) := by
      exact endpoint_component_formula_local H D O S (by
        simp [OneDimensional.FiniteInterval.IntervalPresentation.endpoints])
    have hleftS' : (O.image s).re + D.firstHomeomorph (S.left i) < z := by
      have hz := hzi.1
      change mapScalar phi (horizontalPresentationLeftCoord S i) <
        -(O.image s).re + z at hz
      rw [← hleftMap i] at hz
      linarith
    have hrightS' : z < (O.image s).re + D.firstHomeomorph (S.right i) := by
      have hz := hzi.2
      change -(O.image s).re + z <
        mapScalar phi (horizontalPresentationRightCoord S i) at hz
      rw [← hrightMap i] at hz
      linarith
    have hleftT' : (O.image t).re + D.firstHomeomorph (S.left j) < z := by
      have hz := hzj.1
      change mapScalar phi (horizontalPresentationLeftCoord S j) <
        -(O.image t).re + z at hz
      rw [← hleftMap j] at hz
      linarith
    have hrightT' : z < (O.image t).re + D.firstHomeomorph (S.right j) := by
      have hz := hzj.2
      change -(O.image t).re + z <
        mapScalar phi (horizontalPresentationRightCoord S j) at hz
      rw [← hrightMap j] at hz
      linarith
    have hcross₁ : s.1.re + S.left i < t.1.re + S.right j := by
      have hm : f ⟨s.1.re + S.left i, hleftS⟩ <
          f ⟨t.1.re + S.right j, hrightT⟩ := by
        rw [hmapSleft, hmapTright]
        exact lt_trans hleftS' hrightT'
      exact hf.lt_iff_lt.mp hm
    have hcross₂ : t.1.re + S.left j < s.1.re + S.right i := by
      have hm : f ⟨t.1.re + S.left j, hleftT⟩ <
          f ⟨s.1.re + S.right i, hrightS⟩ := by
        rw [hmapTleft, hmapSright]
        exact lt_trans hleftT' hrightS'
      exact hf.lt_iff_lt.mp hm
    let r := (max (s.1.re + S.left i) (t.1.re + S.left j) +
      min (s.1.re + S.right i) (t.1.re + S.right j)) / 2
    have hlow : max (s.1.re + S.left i) (t.1.re + S.left j) <
        min (s.1.re + S.right i) (t.1.re + S.right j) := by
      refine lt_min (max_lt (by linarith [S.lt i]) hcross₂)
        (max_lt hcross₁ (by linarith [S.lt j]))
    have hrs : r ∈ s.1.re +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
      refine ⟨i, ?_⟩
      simp only [vadd_eq_add]
      dsimp [r]
      constructor
      · linarith [le_max_left (s.1.re + S.left i)
          (t.1.re + S.left j)]
      · linarith [min_le_left (s.1.re + S.right i)
          (t.1.re + S.right j)]
    have hrt : r ∈ t.1.re +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, P.union_eq, Set.mem_iUnion]
      refine ⟨j, ?_⟩
      simp only [vadd_eq_add]
      dsimp [r]
      constructor
      · linarith [le_max_right (s.1.re + S.left i)
          (t.1.re + S.left j)]
      · linarith [min_le_right (s.1.re + S.right i)
          (t.1.re + S.right j)]
    exact Set.disjoint_left.mp hsrcDisj hrs hrt
  exact htgtDisj.aedisjoint

private theorem lineTiles_of_coverage_off_countable_local
    {B L E : Set ℝ}
    (hB : MeasurableSet B)
    (hL : L.Countable)
    (hpair : Set.Pairwise L
      (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
        ((· +ᵥ B) : ℝ → Set ℝ)))
    (hE : E.Countable)
    (hcover : ∀ x : ℝ, x ∉ E →
      ∃ l ∈ L, x ∈ (l : ℝ) +ᵥ B) :
    OneDimensional.LineTiles B L := by
  refine ⟨hB, MeasurableSet.univ, hL, hpair, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hE.measure_zero volume)] with x hx
  constructor
  · intro _
    obtain ⟨l, hl, hxl⟩ := hcover x hx
    exact ⟨⟨l, hl⟩, hxl⟩
  · intro _
    exact Set.mem_univ x

private theorem lineTiles_of_endpoint_coverage_local
    {B L : Set ℝ}
    (P : OneDimensional.FiniteInterval.IntervalPresentation B)
    (hL : L.Countable)
    (hpair : Set.Pairwise L
      (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume)
        ((· +ᵥ B) : ℝ → Set ℝ)))
    (hcover : ∀ x : ℝ,
      x ∉ OneDimensional.FiniteInterval.translatedEndpointSet P L →
      ∃ l ∈ L, x ∈ (l : ℝ) +ᵥ B) :
    OneDimensional.LineTiles B L := by
  apply lineTiles_of_coverage_off_countable_local
    (OneDimensional.FiniteInterval.IsFiniteIntervalRegion.isOpen
      P.isFiniteIntervalRegion).measurableSet hL hpair
    (OneDimensional.FiniteInterval.translatedEndpointSet_countable P hL)
  exact hcover

private theorem imageRow_genericSections_lineTile
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    {y : ℝ}
    (hy : y ∉ C.region.vertexFinset.image Complex.im)
    (hPne : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      C.region y).Nonempty) :
    OneDimensional.LineTiles
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y))
      (Complex.re '' Set.range O.image) := by
  obtain ⟨S⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalGenericSlicePresentation_exists
      C.region hy
  let P : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y) := {
    n := S.n
    left := S.left
    right := S.right
    lt := S.lt
    union_eq := S.union_eq }
  have hmapleft (i : Fin S.n) :
      mapScalar phi (horizontalPresentationLeftCoord S i) =
        D.firstHomeomorph (S.left i) := by
    have hv := D.vertex_agreement (S.leftVertex i).1 (S.leftVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationLeftCoord S i =
        ⟨(S.leftVertex i).1.re,
          C.vertex_re_mem (S.leftVertex i).1 (S.leftVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.leftVertex_coord i).symm
    rw [hcoord, ← S.leftVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  have hmapright (i : Fin S.n) :
      mapScalar phi (horizontalPresentationRightCoord S i) =
        D.firstHomeomorph (S.right i) := by
    have hv := D.vertex_agreement (S.rightVertex i).1 (S.rightVertex i).2
    rw [D.planarHomeomorph_apply] at hv
    have hre := congrArg Complex.re hv
    have hcoord : horizontalPresentationRightCoord S i =
        ⟨(S.rightVertex i).1.re,
          C.vertex_re_mem (S.rightVertex i).1 (S.rightVertex i).2⟩ := by
      apply Subtype.ext
      exact (S.rightVertex_coord i).symm
    rw [hcoord, ← S.rightVertex_coord i]
    simpa [mapScalar, mapPoint, ApproximationContext.vertexPoint] using hre.symm
  let P' : OneDimensional.FiniteInterval.IntervalPresentation
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion (D.secondHomeomorph y)) := {
    n := S.n
    left := fun i => mapScalar phi (horizontalPresentationLeftCoord S i)
    right := fun i => mapScalar phi (horizontalPresentationRightCoord S i)
    lt := fun i => by
      rw [hmapleft, hmapright]
      exact D.firstHomeomorph_strictMono (S.lt i)
    union_eq := deformedHorizontalSlice_eq_mappedPresentation S D }
  have htargetE :
      OneDimensional.FiniteInterval.translatedEndpointSet P'
          (Complex.re '' Set.range O.image) =
        mappedTranslatedEndpointSet D O P := by
    simpa [P, P'] using (targetTranslatedEndpointSet_eq_mapped H D O S)
  have hTile := sourceRow_genericSections_lineTile H y hy hPne
  have hcover : ∀ x : ℝ, x ∉
      OneDimensional.FiniteInterval.translatedEndpointSet P'
        (Complex.re '' Set.range O.image) →
      ∃ l ∈ Complex.re '' Set.range O.image, x ∈ l +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion (D.secondHomeomorph y) := by
    intro x hx
    have hx' : x ∉ mappedTranslatedEndpointSet D O P := by
      intro hxm
      apply hx
      rw [htargetE]
      exact hxm
    have hxline := mapped_target_mem_openUnion_of_not_mem_endpoints H D O hy S hPne
      hTile hx'
    rw [OneDimensional.FiniteInterval.lineOpenUnion] at hxline
    obtain ⟨l, hxl⟩ := Set.mem_iUnion.mp hxline
    exact ⟨l, l.property, hxl⟩
  apply lineTiles_of_endpoint_coverage_local P'
    (image_centres_countable_local H O) ?_ hcover
  exact mapped_target_pairwise_aedisjoint H D O hy S hPne hTile

end Tiling.AxisParallel.Structure

open MeasureTheory
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

namespace Tiling.AxisParallel.Structure

open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Topology

private theorem finitePatch_complete_bothWays
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (O : HorizontalColumnOrderData C H phi) (s : ↥H.fibre)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    ∃ Q : Finset (↥H.fibre), s ∈ Q ∧
      (∀ t : ↥H.fibre, dist t.1 s.1 ≤ R → t ∈ Q) ∧
      (∀ t : ↥H.fibre,
        dist (O.image t) (O.image s) ≤ R' → t ∈ Q) := by
  let S : Set (↥H.fibre) := {t | dist t.1 s.1 ≤ R}
  let S' : Set (↥H.fibre) :=
    {t | dist t.1 s.1 ≤ R' / O.lambda}
  let I : Set (↥H.fibre) := {t | dist (O.image t) (O.image s) ≤ R'}
  have hpack := H.limit.tilesOn.2.1
  have hlocal := (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpack).1
  have hsource_image :
      ((fun t : ↥H.fibre => (t : Plane)) '' S).Finite := by
    apply (hlocal (Metric.closedBall (s : Plane) R)
      (Metric.isBounded_closedBall)).subset
    rintro z ⟨t, ht, rfl⟩
    refine ⟨?_, ?_⟩
    · have ht' : (t : Plane) ∈
          (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
        rw [← H.fibre_eq]
        exact t.2
      exact ht'.1
    · exact ht
  have hS : S.Finite := by
    apply hsource_image.of_finite_image
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have hsource_image' :
      ((fun t : ↥H.fibre => (t : Plane)) '' S').Finite := by
    apply (hlocal (Metric.closedBall (s : Plane) (R' / O.lambda))
      (Metric.isBounded_closedBall)).subset
    rintro z ⟨t, ht, rfl⟩
    have ht' : (t : Plane) ∈
        (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
      rw [← H.fibre_eq]
      exact t.2
    exact ⟨ht'.1, ht⟩
  have hS' : S'.Finite := by
    apply hsource_image'.of_finite_image
    intro x hx y hy hxy
    exact Subtype.ext hxy
  have hsame_im : ∀ t : ↥H.fibre, t.1.im = s.1.im := by
    intro t
    have ht : (t : Plane) ∈
        (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
      rw [← H.fibre_eq]
      exact t.2
    have hs : (s : Plane) ∈
        (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
      rw [← H.fibre_eq]
      exact s.2
    exact ht.2.trans hs.2.symm
  have hsource_dist : ∀ t : ↥H.fibre,
      dist t.1 s.1 = |t.1.re - s.1.re| := by
    intro t
    rw [Complex.dist_eq]
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [show t.1.im - s.1.im = 0 by linarith [hsame_im t]]
    rw [show (t.1.re - s.1.re) * (t.1.re - s.1.re) =
      (t.1.re - s.1.re) ^ 2 by ring]
    rw [zero_mul, add_zero, Real.sqrt_sq_eq_abs]
  have himage_dist : ∀ t : ↥H.fibre,
      dist (O.image t) (O.image s) =
        |(O.image t).re - (O.image s).re| := by
    intro t
    rw [Complex.dist_eq]
    rw [Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im]
    rw [show (O.image t).im - (O.image s).im = 0 by
      linarith [O.common_secondCoordinate t s]]
    rw [show ((O.image t).re - (O.image s).re) *
      ((O.image t).re - (O.image s).re) =
      ((O.image t).re - (O.image s).re) ^ 2 by ring]
    rw [zero_mul, add_zero, Real.sqrt_sq_eq_abs]
  have hI_sub : I ⊆ S' := by
    intro t ht
    dsimp [I] at ht
    rw [himage_dist t] at ht
    dsimp [S']
    rw [hsource_dist t]
    by_cases hts : t.1.re ≤ s.1.re
    · by_cases heq : t.1.re = s.1.re
      · have hteq : t = s := by
          apply Subtype.ext
          apply Complex.ext
          · exact heq
          · exact hsame_im t |>.trans (hsame_im s).symm
        subst t
        have hnonneg : 0 ≤ R' / O.lambda :=
          div_nonneg hR'.le O.lambda_pos.le
        simpa using hnonneg
      · have hbound :=
          (O.horizontal_bounds t s (lt_of_le_of_ne hts heq)).1
        have hmul : 0 ≤ O.lambda * (s.1.re - t.1.re) :=
          mul_nonneg O.lambda_pos.le (sub_nonneg.mpr hts)
        have himg_nonneg : 0 ≤ (O.image s).re - (O.image t).re :=
          hmul.trans hbound
        have habs : |(O.image t).re - (O.image s).re| =
            (O.image s).re - (O.image t).re := by
          have hnonpos : (O.image t).re - (O.image s).re ≤ 0 :=
            sub_nonpos.mpr (sub_nonneg.mp himg_nonneg)
          rw [abs_of_nonpos hnonpos]
          ring
        rw [habs] at ht
        have hsrc : s.1.re - t.1.re ≤ R' / O.lambda := by
          apply (le_div_iff₀ O.lambda_pos).2
          nlinarith [hbound, ht]
        have hdist : |t.1.re - s.1.re| ≤ R' / O.lambda := by
          rw [abs_of_nonpos (sub_nonpos.mpr hts)]
          linarith
        exact hdist
    · have hst : s.1.re < t.1.re := lt_of_not_ge hts
      have hbound := (O.horizontal_bounds s t hst).1
      have hmul : 0 ≤ O.lambda * (t.1.re - s.1.re) :=
        mul_nonneg O.lambda_pos.le (sub_nonneg.mpr hst.le)
      have himg_nonneg : 0 ≤ (O.image t).re - (O.image s).re :=
        hmul.trans hbound
      have habs : |(O.image t).re - (O.image s).re| =
          (O.image t).re - (O.image s).re := abs_of_nonneg himg_nonneg
      rw [habs] at ht
      have hsrc : t.1.re - s.1.re ≤ R' / O.lambda := by
        apply (le_div_iff₀ O.lambda_pos).2
        nlinarith [hbound, ht]
      have hdist : |t.1.re - s.1.re| ≤ R' / O.lambda := by
        rw [abs_of_nonneg (sub_nonneg.mpr hst.le)]
        exact hsrc
      exact hdist
  have hI : I.Finite := hS'.subset hI_sub
  let Q : Finset (↥H.fibre) := (hS.union hI).toFinset
  have hsQ : s ∈ Q := by
    simp only [Q, Set.Finite.mem_toFinset]
    exact Or.inl (by dsimp [S]; simpa using hR.le)
  refine ⟨Q, hsQ, ?_, ?_⟩
  · intro t ht
    simp only [Q, Set.Finite.mem_toFinset]
    exact Or.inl ht
  · intro t ht
    simp only [Q, Set.Finite.mem_toFinset]
    exact Or.inr ht

private structure IndexedFinitePatchTransportData
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D)
    (O : HorizontalColumnOrderData C H phi) (s : ↥H.fibre) where
  sourceRadius : ℝ
  imageRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  imageRadius_pos : 0 < imageRadius
  patch : Finset (↥H.fibre)
  centre_mem : s ∈ patch
  source_complete : ∀ t : ↥H.fibre,
    dist t.1 s.1 ≤ sourceRadius → t ∈ patch
  image_complete : ∀ t : ↥H.fibre,
    dist (O.image t) (O.image s) ≤ imageRadius → t ∈ patch
  stage : ℕ
  sourceLabel : ↥patch → ↥C.centres
  sourceLabel_coe : ∀ t : ↥patch,
    (sourceLabel t : Plane) =
      t.1.1 - (H.translations stage : Plane)
  deformedTranslation : Plane
  deformedTranslation_eq : deformedTranslation =
    P.fullCenters ⟨H.anchor, H.anchor_mem_context⟩ -
      P.fullCenters ⟨H.movingCentre stage,
        H.movingCentre_mem_context stage⟩
  image_eq_translatedFullCenters : ∀ t : ↥patch,
    O.image t.1 = deformedTranslation + P.fullCenters (sourceLabel t)

private theorem finite_eventual_common_stage
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (Q : Finset (↥H.fibre)) :
    ∃ n : ℕ, ∀ t : ↥H.fibre, t ∈ Q →
      t.1 - (H.translations n : Plane) ∈ C.centres := by
  have hev : ∀ t : ↥H.fibre, t ∈ Q →
      ∀ᶠ n : ℕ in Filter.atTop,
        t.1 - (H.translations n : Plane) ∈ C.centres := by
    intro t ht
    exact H.persistent_pullback t.1 t.2
  have hall : ∀ᶠ n : ℕ in Filter.atTop, ∀ t : ↥H.fibre, t ∈ Q →
      t.1 - (H.translations n : Plane) ∈ C.centres := by
    exact Q.eventually_all.2 hev
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hall
  exact ⟨n, hn⟩

private theorem mapPoint_sub_local
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    mapPoint phi
        ⟨x.1 - y.1, C.coordinateSpace.sub_mem x.2.1 y.2.1,
          C.coordinateSpace.sub_mem x.2.2 y.2.2⟩ =
      mapPoint phi x - mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      sub_zero, add_zero]
    exact_mod_cast (map_sub phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.sub_re, Complex.sub_im,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
      add_zero, zero_add]
    exact_mod_cast (map_sub phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem mapPoint_add_local
    {C : ApproximationContext} (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x y : {z : Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    mapPoint phi
        ⟨x.1 + y.1, C.coordinateSpace.add_mem x.2.1 y.2.1,
          C.coordinateSpace.add_mem x.2.2 y.2.2⟩ =
      mapPoint phi x + mapPoint phi y := by
  apply Complex.ext
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one]
    norm_num
    norm_cast
    exact_mod_cast (map_add phi
      (⟨x.1.re, x.2.1⟩ : C.coordinateSpace)
      (⟨y.1.re, y.2.1⟩ : C.coordinateSpace))
  · simp only [mapPoint, mapScalar, Complex.add_re, Complex.add_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
    exact_mod_cast (map_add phi
      (⟨x.1.im, x.2.2⟩ : C.coordinateSpace)
      (⟨y.1.im, y.2.2⟩ : C.coordinateSpace))

private theorem indexedFinitePatchTransportData_exists
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (O : HorizontalColumnOrderData C H phi) (s : ↥H.fibre)
    (R R' : ℝ) (hR : 0 < R) (hR' : 0 < R') :
    ∃ F : IndexedFinitePatchTransportData H phi D P O s,
      R ≤ F.sourceRadius ∧ R' ≤ F.imageRadius := by
  obtain ⟨Q, hsQ, hsourceQ, himageQ⟩ :=
    finitePatch_complete_bothWays O s R R' hR hR'
  obtain ⟨stage, hstage⟩ := finite_eventual_common_stage H Q
  let sourceLabel : ↥Q → ↥C.centres := fun t =>
    ⟨t.1.1 - (H.translations stage : Plane), hstage t.1 t.2⟩
  let deformedTranslation : Plane :=
    P.fullCenters ⟨H.anchor, H.anchor_mem_context⟩ -
      P.fullCenters ⟨H.movingCentre stage, H.movingCentre_mem_context stage⟩
  let F : IndexedFinitePatchTransportData H phi D P O s := {
    sourceRadius := R
    imageRadius := R'
    sourceRadius_pos := hR
    imageRadius_pos := hR'
    patch := Q
    centre_mem := hsQ
    source_complete := hsourceQ
    image_complete := himageQ
    stage := stage
    sourceLabel := sourceLabel
    sourceLabel_coe := by
      intro t
      rfl
    deformedTranslation := deformedTranslation
    deformedTranslation_eq := by rfl
    image_eq_translatedFullCenters := by
      intro t
      let xt : {z : Plane // z.re ∈ C.coordinateSpace ∧
          z.im ∈ C.coordinateSpace} := O.coordinateLift t.1
      let xa : {z : Plane // z.re ∈ C.coordinateSpace ∧
          z.im ∈ C.coordinateSpace} :=
        C.centrePoint H.anchor H.anchor_mem_context
      let xm : {z : Plane // z.re ∈ C.coordinateSpace ∧
          z.im ∈ C.coordinateSpace} :=
        C.centrePoint (H.movingCentre stage)
          (H.movingCentre_mem_context stage)
      have hxt : (xt : Plane) = t.1 := O.coordinateLift_coe t.1
      have htrans : (H.translations stage : Plane) =
          H.anchor - H.movingCentre stage := H.translations_eq stage
      have hpoint : C.centrePoint (sourceLabel t).1 (sourceLabel t).2 =
          ⟨(xt : Plane) - ((xa : Plane) - (xm : Plane)),
            C.coordinateSpace.sub_mem xt.2.1
              (C.coordinateSpace.sub_mem xa.2.1 xm.2.1),
            C.coordinateSpace.sub_mem xt.2.2
              (C.coordinateSpace.sub_mem xa.2.2 xm.2.2)⟩ := by
        apply Subtype.ext
        change (sourceLabel t : Plane) =
          (xt : Plane) - ((xa : Plane) - (xm : Plane))
        dsimp [sourceLabel]
        rw [htrans, hxt]
        simp [ApproximationContext.centrePoint, xa, xm, sub_eq_add_neg]
      rw [O.image_apply]
      change mapPoint phi xt =
        deformedTranslation + P.fullCenters (sourceLabel t)
      dsimp [deformedTranslation]
      rw [P.fullCenters_apply (sourceLabel t)]
      rw [P.fullCenters_apply, P.fullCenters_apply]
      change mapPoint phi xt =
        mapPoint phi xa - mapPoint phi xm +
          mapPoint phi (C.centrePoint (sourceLabel t).1 (sourceLabel t).2)
      let xsub : {z : Plane // z.re ∈ C.coordinateSpace ∧
          z.im ∈ C.coordinateSpace} :=
        ⟨(xa : Plane) - (xm : Plane),
          C.coordinateSpace.sub_mem xa.2.1 xm.2.1,
          C.coordinateSpace.sub_mem xa.2.2 xm.2.2⟩
      let xxsub : {z : Plane // z.re ∈ C.coordinateSpace ∧
          z.im ∈ C.coordinateSpace} :=
        ⟨(xt : Plane) - (xsub : Plane),
          C.coordinateSpace.sub_mem xt.2.1 xsub.2.1,
          C.coordinateSpace.sub_mem xt.2.2 xsub.2.2⟩
      have hpoint' : C.centrePoint (sourceLabel t).1 (sourceLabel t).2 =
          xxsub := by
        apply Subtype.ext
        exact congrArg Subtype.val hpoint
      have hxx := mapPoint_sub_local phi xt xsub
      have hxs := mapPoint_sub_local phi xa xm
      rw [hpoint', hxx, hxs]
      ring }
  refine ⟨F, le_rfl, le_rfl⟩


private theorem fullCenters_re_eq_of_source_re_eq
    {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    {s t : C.centres}
    (hre : (s : Plane).re = (t : Plane).re) :
    (P.fullCenters s).re = (P.fullCenters t).re := by
  rw [P.fullCenters_apply s, P.fullCenters_apply t]
  simp only [mapPoint, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
    sub_zero, add_zero, mapScalar]
  congr 2
  apply Subtype.ext
  exact hre

private theorem deformation_originalColumn_hasColumn
    {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (Q : VerticalPlate C.region C.centres)
    (hQcolumn : IsVerticalColumn Q) :
    ∃ A : Set (VerticalPlate D.deformedRegion
        (deformedCenterCarrier P.fullCenters)),
      A.Nonempty ∧
      (∀ R ∈ A, IsVerticalColumn R) ∧
      deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t.1 : Plane) ∈ Q.centres} =
        ⋃ R : A, R.1.centres := by
  let S : Set Plane := deformedCenterCarrierOn P.fullCenters
      {t : C.centres | (t.1 : Plane) ∈ Q.centres}
  have hQtile : TilesOn C.region C.centres Set.univ := P.source_tilesOn
  have hQslab := VerticalPlate.support_isVerticalSlab hQtile Q
  have hsource : regularSupport C.region Q.centres =
      Complex.re ⁻¹' Q.base := by
    rw [← Q.support_eq_regularSupport]
    exact hQslab.2
  have hQsub : Q.centres ⊆ C.centres := by
    intro z hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact s.property
  have hQbaseOpen : IsOpen Q.base := by
    rw [hQslab.1]
    exact isOpen_interior
  obtain ⟨Xphi, hXopen, hXregular, hSsupport⟩ :=
    P.subfamily_support Q.centres hQsub Q.base hQbaseOpen hQslab.1.symm hsource
  have hST : S ⊆ deformedCenterCarrier P.fullCenters := by
    rintro z ⟨t, ht, rfl⟩
    exact ⟨t, rfl⟩
  have hpack : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements S) := by
    apply (isPacking_iff_openCarrier_disjoint D.deformedRegion S).mpr
    intro s hs t ht hst
    exact (isPacking_iff_openCarrier_disjoint D.deformedRegion
      (deformedCenterCarrier P.fullCenters)).mp P.full_tilesOn.2.1
      (hST hs) (hST ht) hst
  obtain ⟨q₀, hq₀⟩ := Q.nonempty_supp
  have hq₀centre : (q₀ : Plane) ∈ Q.centres := ⟨q₀, hq₀, rfl⟩
  have hSne : S.Nonempty := by
    refine ⟨P.fullCenters q₀, ?_⟩
    exact ⟨q₀, hq₀centre, rfl⟩
  obtain ⟨rho, hrho⟩ :=
    D.deformedRegion.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  obtain ⟨x₀, hx₀⟩ := hQcolumn
  have hXbound : ∀ x ∈ Xphi,
      (P.fullCenters q₀).re - rho ≤ x ∧ x ≤ (P.fullCenters q₀).re + rho := by
    intro x hx
    have hz : ((x : ℝ) : ℂ) ∈ regularSupport D.deformedRegion S := by
      rw [hSsupport]
      exact hx
    have hzcl : ((x : ℝ) : ℂ) ∈ closure (openUnion D.deformedRegion S) :=
      interior_subset hz
    rw [closure_openUnion_eq_iUnion_support hpack] at hzcl
    obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hzcl
    rw [mem_vadd_set] at hs
    obtain ⟨u, hu, hxu⟩ := hs
    obtain ⟨t, ht, hst⟩ := s.property
    have htQ : (t : Plane) ∈ Q.centres := ht
    have htre : (t : Plane).re = (q₀ : Plane).re :=
      (hx₀ htQ).trans (hx₀ hq₀centre).symm
    have htre' : (P.fullCenters t).re = (P.fullCenters q₀).re :=
      fullCenters_re_eq_of_source_re_eq P htre
    have hcenter : (P.fullCenters t).re = (P.fullCenters q₀).re := htre'
    have hre := congrArg Complex.re hxu
    rw [← hst] at hre
    have huabs : |u.re| ≤ rho := by
      have hball := hrho hu
      have hnorm : ‖u‖ ≤ rho := by
        simpa [Metric.mem_closedBall] using hball
      exact (Complex.abs_re_le_norm u).trans hnorm
    rw [abs_le] at huabs
    simp only [vadd_eq_add, Complex.add_re] at hre
    rw [hcenter] at hre
    have hre' : (P.fullCenters q₀).re + u.re = x := by simpa using hre
    constructor
    · linarith [huabs.1, hre']
    · linarith [huabs.2, hre']
  have hone : BddBelow Xphi := ⟨(P.fullCenters q₀).re - rho, by
    intro x hx
    exact (hXbound x hx).1⟩
  let A : Set (VerticalPlate D.deformedRegion
      (deformedCenterCarrier P.fullCenters)) :=
    {R | (R.centres ∩ S).Nonempty}
  have hAne : A.Nonempty := by
    obtain ⟨z, hz⟩ := hSne
    have hzc : z ∈ deformedCenterCarrier P.fullCenters := hST hz
    rw [← iUnion_verticalPlateCentres D.deformedRegion
      (deformedCenterCarrier P.fullCenters)] at hzc
    obtain ⟨R, hR⟩ := Set.mem_iUnion.mp hzc
    refine ⟨R, ?_⟩
    exact ⟨z, hR, hz⟩
  have hAdata : ∀ R ∈ A, R.centres ⊆ S ∧ IsVerticalColumn R := by
    intro R hR
    exact Tiling.AxisParallel.Continuous.rationalOneSidedSlab_saturatesColumns
      P.full_tilesOn (by
        obtain ⟨v, hv, w, hw, hmax, hdiam⟩ :=
          IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
        refine ⟨v, hv, ?_⟩
        intro z hz
        obtain ⟨vx, vy, hvx, hvy⟩ := D.rational_vertices v hv
        obtain ⟨zx, zy, hzx, hzy⟩ := D.rational_vertices z hz
        refine ⟨zx - vx, zy - vy, ?_, ?_⟩
        · rw [Complex.sub_re, hvx, hzx]
          norm_num
        · rw [Complex.sub_im, hvy, hzy]
          norm_num)
      hST hXopen hXregular hSsupport (Or.inl hone) R hR
  refine ⟨A, hAne, fun R hR => (hAdata R hR).2, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    have hzc : z ∈ deformedCenterCarrier P.fullCenters := hST hz
    rw [← iUnion_verticalPlateCentres D.deformedRegion
      (deformedCenterCarrier P.fullCenters)] at hzc
    obtain ⟨R, hR⟩ := Set.mem_iUnion.mp hzc
    exact Set.mem_iUnion.mpr ⟨⟨R, ⟨z, hR, hz⟩⟩, hR⟩
  · intro z hz
    obtain ⟨R, hzR⟩ := Set.mem_iUnion.mp hz
    exact (hAdata R R.property).1 hzR

private theorem imageRow_isPacking
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi) :
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range O.image)) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ hst
  apply Set.disjoint_left.2
  intro z hzs hzt
  let Oxy : Set Plane :=
    ((O.image s) +ᵥ D.deformedRegion.openCarrier) ∩
      ((O.image t) +ᵥ D.deformedRegion.openCarrier)
  have hOopen : IsOpen Oxy :=
    (D.deformedRegion.openCarrier_regularOpen.1.vadd _).inter
      (D.deformedRegion.openCarrier_regularOpen.1.vadd _)
  have hzO : z ∈ Oxy := ⟨hzs, hzt⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hOopen z hzO
  let c : ℝ := (O.image s).im
  let F : Set ℝ :=
    ((C.region.vertexFinset.image Complex.im).image D.secondHomeomorph : Finset ℝ)
  have hFfin : F.Finite := by
    exact (C.region.vertexFinset.image Complex.im).image D.secondHomeomorph |>.finite_toSet
  let J : Set ℝ := Set.Ioo (z.im - c - ε / 2) (z.im - c + ε / 2)
  have hJinf : J.Infinite := by
    dsimp [J]
    exact Set.Ioo_infinite (by linarith)
  obtain ⟨q, hqJ, hqF⟩ := (hJinf.sdiff hFfin).nonempty
  have hqabs : |(q + c) - z.im| < ε := by
    rw [abs_lt]
    dsimp [J] at hqJ
    constructor <;> linarith [hqJ.1, hqJ.2]
  let w : Plane := (z.re : ℂ) + ((q + c : ℝ) : ℂ) * Complex.I
  have hwball : w ∈ Metric.ball z ε := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hdiff : w - z = ((q + c - z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [w]
    rw [hdiff, norm_mul, Complex.norm_real, Complex.norm_I, mul_one]
    exact hqabs
  have hwS : w ∈ (O.image s) +ᵥ D.deformedRegion.openCarrier :=
    hball hwball |>.1
  have hwT : w ∈ (O.image t) +ᵥ D.deformedRegion.openCarrier :=
    hball hwball |>.2
  have hstRe : (O.image s).re ≠ (O.image t).re := by
    intro h
    apply hst
    apply Complex.ext h
    exact O.common_secondCoordinate s t
  have hqsource : D.secondHomeomorph.symm q ∉
      C.region.vertexFinset.image Complex.im := by
    intro hqv
    obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hqv
    apply hqF
    have hvim : v.im ∈ (C.region.vertexFinset.image Complex.im : Finset ℝ) := by
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    have hgv : D.secondHomeomorph v.im ∈
        (C.region.vertexFinset.image Complex.im).image D.secondHomeomorph := by
      exact Finset.mem_image.mpr ⟨v.im, hvim, rfl⟩
    have hqeq : q = D.secondHomeomorph v.im := by
      simpa using (congrArg D.secondHomeomorph hvq).symm
    change q ∈ ((C.region.vertexFinset.image Complex.im).image D.secondHomeomorph : Set ℝ)
    rw [hqeq]
    exact hgv
  have hsource_nonempty :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region
        (D.secondHomeomorph.symm q)).Nonempty := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hwS
    obtain ⟨u, hu, hwu⟩ := by
      rw [D.deformedRegion_openCarrier] at hwS
      exact hwS
    have huim : D.secondHomeomorph u.im = q := by
      have := congrArg Complex.im (D.planarHomeomorph_apply u)
      rw [hwu] at this
      simpa [c, w, O.common_secondCoordinate s t] using this.symm
    have huim' : u.im = D.secondHomeomorph.symm q := by
      apply D.secondHomeomorph.injective
      simpa using huim
    refine ⟨u.re, ?_⟩
    change Complex.mk u.re (D.secondHomeomorph.symm q) ∈ C.region.openCarrier
    have heq : Complex.mk u.re (D.secondHomeomorph.symm q) = u := by
      apply Complex.ext <;> simp [huim']
    rw [heq]
    exact hu
  have hline := imageRow_genericSections_lineTile H D O hqsource hsource_nonempty
  have hA : (O.image s).re ∈ Complex.re '' Set.range O.image :=
    ⟨O.image s, ⟨s, rfl⟩, rfl⟩
  have hB : (O.image t).re ∈ Complex.re '' Set.range O.image :=
    ⟨O.image t, ⟨t, rfl⟩, rfl⟩
  have hsliceOpen : IsOpen
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q) := by
    change IsOpen ((fun x : ℝ => Complex.mk x q) ⁻¹' D.deformedRegion.openCarrier)
    apply D.deformedRegion.openCarrier_regularOpen.1.preimage
    have hc : Continuous (fun x : ℝ => (x : ℂ) + (q : ℂ) * Complex.I) := by
      fun_prop
    convert hc using 1
    funext x
    apply Complex.ext <;> simp
  have hxs : z.re - (O.image s).re ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q := by
    change Complex.mk (z.re - (O.image s).re) q ∈ D.deformedRegion.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hwS
    have heq : Complex.mk (z.re - (O.image s).re) q = -O.image s + w := by
      apply Complex.ext <;> simp [w, c, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, O.common_secondCoordinate s t]
    rw [heq]
    exact hwS
  have hxt : z.re - (O.image t).re ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q := by
    change Complex.mk (z.re - (O.image t).re) q ∈ D.deformedRegion.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hwT
    have heq : Complex.mk (z.re - (O.image t).re) q = -O.image t + w := by
      apply Complex.ext <;> simp [w, c, sub_eq_add_neg, add_comm,
        add_left_comm, add_assoc, O.common_secondCoordinate s t]
    rw [heq]
    exact hwT
  have hzA : z.re ∈ (O.image s).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hxs
  have hzB : z.re ∈ (O.image t).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hxt
  have hpos : 0 < volume (((O.image s).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q) ∩ ((O.image t).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q)) :=
    ((hsliceOpen.vadd _).inter (hsliceOpen.vadd _)).measure_pos volume
      ⟨z.re, hzA, hzB⟩
  have hzero : MeasureTheory.AEDisjoint volume
      ((O.image s).re +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion q)
      ((O.image t).re +ᵥ
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
          D.deformedRegion q) := by
    have hzero0 := hline.2.2.2.1 hA hB hstRe
    rw [D.secondHomeomorph.apply_symm_apply] at hzero0
    exact hzero0
  change volume (((O.image s).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q) ∩ ((O.image t).re +ᵥ
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q)) = 0 at hzero
  exact hpos.ne' hzero


private theorem openUnion_eq_on_ball_of_complete
    {K : Region} {S T : Set Plane} {a b v : Plane} {R δ : ℝ}
    (hcenter : a = v + b)
    (hv : v ∈ closure K.openCarrier)
    (hdiam : Metric.diam (closure K.openCarrier) = δ)
    (_hδ : δ < R)
    (hsub : S ⊆ T)
    (hcomplete : ∀ t : Plane, t ∈ T → dist t b ≤ R → t ∈ S) :
    ∀ z ∈ Metric.ball a (R - δ),
      z ∈ openUnion K S ↔ z ∈ openUnion K T := by
  intro z hz
  constructor
  · intro hzS
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, mem_iUnion] at hzS ⊢
    obtain ⟨t, ht⟩ := hzS
    exact ⟨⟨t, hsub t.2⟩, ht⟩
  · intro hzT
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, mem_iUnion] at hzT ⊢
    obtain ⟨t, ht⟩ := hzT
    rcases mem_vadd_set.mp ht with ⟨w, hw, htw⟩
    have hdistvw : dist v w ≤ δ := by
      have hv' : v ∈ K.support := by
        rw [← K.isPolygonal.closure_interior]
        exact hv
      have hw' : w ∈ K.support := by
        rw [← K.isPolygonal.closure_interior]
        exact subset_closure hw
      have h := Metric.dist_le_diam_of_mem K.isPolygonal.isBounded hv' hw'
      have hclosure : closure K.openCarrier = K.support :=
        K.isPolygonal.closure_interior
      rw [hclosure] at hdiam
      simpa [hdiam] using h
    have hdisttb : dist (t : Plane) b ≤ R := by
      have htri : dist (t : Plane) b ≤
          dist ((t : Plane) + w) (b + v) + dist v w := by
        calc
          dist (t : Plane) b = dist ((t : Plane) + w) (b + w) :=
            (dist_add_right (t : Plane) b w).symm
          _ ≤ dist ((t : Plane) + w) (b + v) + dist (b + v) (b + w) :=
            dist_triangle _ _ _
          _ = dist ((t : Plane) + w) (b + v) + dist v w := by
            rw [dist_add_left]
      have hz' : dist z a < R - δ := by
        simpa [Metric.mem_ball, dist_comm] using hz
      change (t : Plane) + w = z at htw
      have hbv : b + v = a := by rw [add_comm, hcenter]
      rw [htw, hbv] at htri
      linarith
    have hts : (t : Plane) ∈ S := hcomplete t t.2 hdisttb
    exact ⟨⟨t, hts⟩, ht⟩

private theorem source_openUnion_complete_on_ball
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source}
    (Q : Finset ↑H.fibre) (v : ↑C.region.vertices) (s : ↑H.fibre)
    (_hsQ : s ∈ Q) {sourceRadius : ℝ}
    (hsource : Metric.diam (closure C.region.openCarrier) < sourceRadius)
    (hQsource : ∀ t : ↑H.fibre, dist t.1 s.1 ≤ sourceRadius → t ∈ Q) :
    ∀ z ∈ Metric.ball (v.1 + s.1)
        (sourceRadius - Metric.diam (closure C.region.openCarrier)),
      z ∈ openUnion C.region
          (((↑) : ↑H.fibre → Plane) '' (Q : Set ↑H.fibre)) ↔
        z ∈ openUnion C.region H.fibre := by
  intro z hz
  apply openUnion_eq_on_ball_of_complete (K := C.region)
    (S := ((↑) : ↑H.fibre → Plane) '' (Q : Set ↑H.fibre))
    (T := H.fibre) (a := v.1 + s.1) (b := s.1) (v := v.1)
    rfl (by
      exact frontier_subset_closure
        ((IntrinsicVertices.region_vertices_subset_frontier C.region) v.2))
    rfl hsource (by
      rintro _ ⟨t, ht, rfl⟩
      exact t.2) (by
      intro t ht hdist
      let u : ↑H.fibre := ⟨t, ht⟩
      exact ⟨u, hQsource u hdist, rfl⟩) z hz

private theorem image_openUnion_complete_on_ball
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (Q : Finset ↑H.fibre) (v : ↑C.region.vertices) (s : ↑H.fibre)
    (_hsQ : s ∈ Q) {imageRadius : ℝ}
    (himage : Metric.diam (closure D.deformedRegion.openCarrier) < imageRadius)
    (hQimage : ∀ t : ↑H.fibre,
      dist (O.image t) (O.image s) ≤ imageRadius → t ∈ Q) :
    ∀ z ∈ Metric.ball (D.planarHomeomorph v.1 + O.image s)
        (imageRadius - Metric.diam (closure D.deformedRegion.openCarrier)),
      z ∈ openUnion D.deformedRegion (O.image '' (Q : Set ↑H.fibre)) ↔
        z ∈ openUnion D.deformedRegion (Set.range O.image) := by
  intro z hz
  have hv : D.planarHomeomorph v.1 ∈
      closure D.deformedRegion.openCarrier := by
    apply frontier_subset_closure
    have hvvert : D.planarHomeomorph v.1 ∈ D.deformedRegion.vertices := by
      rw [D.vertices_image]
      exact ⟨v.1, v.2, rfl⟩
    exact (IntrinsicVertices.region_vertices_subset_frontier D.deformedRegion) hvvert
  apply openUnion_eq_on_ball_of_complete (K := D.deformedRegion)
    (S := O.image '' (Q : Set ↑H.fibre))
    (T := Set.range O.image)
    (a := D.planarHomeomorph v.1 + O.image s) (b := O.image s)
    (v := D.planarHomeomorph v.1) rfl hv rfl himage (by
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩) (by
      intro t ht hdist
      rcases ht with ⟨u, rfl⟩
      let q : ↑H.fibre := u
      exact ⟨q, hQimage q hdist, rfl⟩) z hz

private theorem source_regularSupport_complete_on_ball
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source}
    (Q : Finset ↑H.fibre) (v : ↑C.region.vertices) (s : ↑H.fibre)
    (_hsQ : s ∈ Q) {sourceRadius : ℝ}
    (hsource : Metric.diam (closure C.region.openCarrier) < sourceRadius)
    (hQsource : ∀ t : ↑H.fibre, dist t.1 s.1 ≤ sourceRadius → t ∈ Q) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ Metric.ball (v.1 + s.1) r,
      z ∈ regularSupport C.region
          (((↑) : ↑H.fibre → Plane) '' (Q : Set ↑H.fibre)) ↔
        z ∈ regularSupport C.region H.fibre := by
  have hr : 0 < sourceRadius - Metric.diam (closure C.region.openCarrier) :=
    sub_pos.mpr hsource
  obtain ⟨r, hrpos, hreg⟩ := regularSupport_local_eq_of_openUnion_eq_on_ball hr
    (source_openUnion_complete_on_ball Q v s _hsQ hsource hQsource)
  exact ⟨r, hrpos, hreg⟩

private theorem image_regularSupport_complete_on_ball
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (Q : Finset ↑H.fibre) (v : ↑C.region.vertices) (s : ↑H.fibre)
    (_hsQ : s ∈ Q) {imageRadius : ℝ}
    (himage : Metric.diam (closure D.deformedRegion.openCarrier) < imageRadius)
    (hQimage : ∀ t : ↑H.fibre,
      dist (O.image t) (O.image s) ≤ imageRadius → t ∈ Q) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈
        Metric.ball (D.planarHomeomorph v.1 + O.image s) r,
      z ∈ regularSupport D.deformedRegion (O.image '' (Q : Set ↑H.fibre)) ↔
        z ∈ regularSupport D.deformedRegion (Set.range O.image) := by
  have hr : 0 < imageRadius - Metric.diam (closure D.deformedRegion.openCarrier) :=
    sub_pos.mpr himage
  obtain ⟨r, hrpos, hreg⟩ := regularSupport_local_eq_of_openUnion_eq_on_ball hr
    (image_openUnion_complete_on_ball D O Q v s _hsQ himage hQimage)
  exact ⟨r, hrpos, hreg⟩

private theorem source_row_support_cylinder_exact
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) :
    regularSupport C.region H.fibre =
      Complex.im ⁻¹' interior
        (closure (H.anchor.im +ᵥ (Complex.im '' C.region.openCarrier))) := by
  obtain ⟨c, _hne, hcoord, hsupport⟩ :=
    centerColumn_regularSupport (fibre_isHorizontalCenterColumn H)
  have hc : c = H.anchor.im := by
    symm
    simpa [Axis.transverseCoord] using
      hcoord H.anchor H.anchor_mem_fibre
  rw [hsupport, hc]
  rfl


private def imageRowBase_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (O : HorizontalColumnOrderData C H phi) : Set ℝ :=
  (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im +ᵥ
    interior (closure (Complex.im '' D.deformedRegion.openCarrier))

private theorem sourceSlice_nonempty_of_deformedSlice_nonempty
    {C : ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) {y q : ℝ}
    (hq : q = D.secondHomeomorph y)
    (hD : (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
      D.deformedRegion q).Nonempty) :
    (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y).Nonempty := by
  obtain ⟨x, hx⟩ := hD
  change Complex.mk x q ∈ D.deformedRegion.openCarrier at hx
  rw [D.deformedRegion_openCarrier] at hx
  obtain ⟨u, hu, hxu⟩ := hx
  have him : D.secondHomeomorph u.im = q := by
    have h := congrArg Complex.im (D.planarHomeomorph_apply u)
    rw [hxu] at h
    simpa using h.symm
  have huim : u.im = y := by
    apply D.secondHomeomorph.injective
    simpa [hq] using him
  refine ⟨u.re, ?_⟩
  change Complex.mk u.re y ∈ C.region.openCarrier
  have heq : Complex.mk u.re y = u := by
    apply Complex.ext <;> simp [huim]
  rw [heq]
  exact hu

private theorem imageRow_swap_packing
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi) :
    Tiling.IsPacking D.deformedRegion.coordinateSwap.toPolygonalRegion.prototileFamily
      (D.deformedRegion.coordinateSwap.toPolygonalRegion.placements
        (coordinateSwap '' Set.range O.image)) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hst
  obtain ⟨s₀, rfl⟩ := hs
  obtain ⟨t₀, rfl⟩ := ht
  apply Set.disjoint_left.2
  intro z hzs hzt
  have himage : O.image s₀ ≠ O.image t₀ := by
    intro heq
    exact hst (congrArg coordinateSwap heq)
  have hdis := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
    D.deformedRegion (Set.range O.image)).mp (imageRow_isPacking H D O)
    ⟨s₀, rfl⟩ ⟨t₀, rfl⟩ himage
  rw [Tiling.AxisParallel.coordinateSwap_openCarrier] at hzs hzt
  change z ∈ coordinateSwap (O.image s₀) +ᵥ
      (coordinateSwap '' D.deformedRegion.openCarrier) at hzs
  change z ∈ coordinateSwap (O.image t₀) +ᵥ
      (coordinateSwap '' D.deformedRegion.openCarrier) at hzt
  rw [← Tiling.AxisParallel.coordinateSwap_image_vadd
    (O.image s₀) D.deformedRegion.openCarrier] at hzs
  rw [← Tiling.AxisParallel.coordinateSwap_image_vadd
    (O.image t₀) D.deformedRegion.openCarrier] at hzt
  obtain ⟨ws, hws, hwsz⟩ := hzs
  obtain ⟨wt, hwt, hwtz⟩ := hzt
  have hsw : ws = wt := by
    apply coordinateSwap.injective
    rw [hwsz, hwtz]
  exact (Set.disjoint_left.mp hdis) hws (hsw ▸ hwt)

private theorem imageRow_swap_cylinder
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (O : HorizontalColumnOrderData C H phi) :
    coordinateSwap '' Set.range O.image =
      {z : Plane | z.re = (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im ∧
        z.im ∈ Complex.re '' Set.range O.image} := by
  let s₀ : H.fibre := ⟨H.anchor, H.anchor_mem_fibre⟩
  let c : ℝ := (O.image s₀).im
  ext z
  constructor
  · rintro ⟨w, ⟨s, rfl⟩, rfl⟩
    refine ⟨?_, ⟨O.image s, ⟨s, rfl⟩, rfl⟩⟩
    dsimp [c]
    exact (O.common_secondCoordinate s₀ s).symm
  · rintro ⟨hz, ⟨w, ⟨s, rfl⟩, hzw⟩⟩
    refine ⟨O.image s, ⟨s, rfl⟩, ?_⟩
    apply Complex.ext
    · simpa [c, coordinateSwap] using (hz.trans (O.common_secondCoordinate s₀ s)).symm
    · simpa [coordinateSwap] using hzw

private theorem imageRow_swap_vertex_levels
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {_H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    D.deformedRegion.coordinateSwap.vertexFinset.image Complex.re =
      D.deformedRegion.vertexFinset.image Complex.im := by
  have hverts :
      (D.deformedRegion.vertexFinset : Set Plane) =
        D.planarHomeomorph '' (C.region.vertexFinset : Set Plane) := by
    rw [D.deformedRegion.coe_vertexFinset, D.vertices_image,
      C.region.coe_vertexFinset]
  ext r
  constructor
  · intro hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hv' : v ∈ Tiling.vertexSet
        (coordinateSwap '' D.deformedRegion.support) := by
      have hv0 : v ∈ D.deformedRegion.coordinateSwap.vertices := by
        change v ∈ (D.deformedRegion.coordinateSwap.vertexFinset : Set Plane) at hv
        rw [D.deformedRegion.coordinateSwap.coe_vertexFinset] at hv
        exact hv
      simpa [Region.vertices, Region.coordinateSwap] using hv0
    rw [IntrinsicVertices.coordinateSwap_vertexSet D.deformedRegion.support] at hv'
    obtain ⟨w, hw, hvw⟩ := hv'
    have hwv : w ∈ D.deformedRegion.vertices := by
      simpa [Region.vertices] using hw
    have hwi : w.im ∈ D.deformedRegion.vertexFinset.image Complex.im := by
      apply Finset.mem_image.mpr
      exact ⟨w, by
        change w ∈ (D.deformedRegion.vertexFinset : Set Plane)
        simpa [D.deformedRegion.coe_vertexFinset] using hwv, rfl⟩
    have hvre : v.re = w.im := by
      rw [← hvw]
      rfl
    rw [hvre]
    exact hwi
  · intro hr
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
    have hwv : w ∈ D.deformedRegion.vertices := by
      have : w ∈ (D.deformedRegion.vertexFinset : Set Plane) := by
        exact Finset.mem_coe.mpr hw
      simpa [D.deformedRegion.coe_vertexFinset] using this
    have hv : coordinateSwap w ∈
        (D.deformedRegion.coordinateSwap.vertexFinset : Set Plane) := by
      rw [D.deformedRegion.coordinateSwap.coe_vertexFinset]
      have hvset : coordinateSwap w ∈ Tiling.vertexSet
          (coordinateSwap '' D.deformedRegion.support) := by
        rw [IntrinsicVertices.coordinateSwap_vertexSet D.deformedRegion.support]
        exact ⟨w, by simpa [Region.vertices] using hwv, rfl⟩
      simpa [Region.vertices, Region.coordinateSwap] using hvset
    exact Finset.mem_image.mpr ⟨coordinateSwap w, hv, by simp⟩

private theorem imageRow_deformed_vertex_im_levels
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {_H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    D.deformedRegion.vertexFinset.image Complex.im =
      (C.region.vertexFinset.image Complex.im).image D.secondHomeomorph := by
  have hverts :
      (D.deformedRegion.vertexFinset : Set Plane) =
        D.planarHomeomorph '' (C.region.vertexFinset : Set Plane) := by
    rw [D.deformedRegion.coe_vertexFinset, D.vertices_image,
      C.region.coe_vertexFinset]
  ext r
  constructor
  · intro hr
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hr
    have hvset : v ∈ (D.deformedRegion.vertexFinset : Set Plane) := by
      exact Finset.mem_coe.mpr hv
    rw [hverts] at hvset
    obtain ⟨u, hu, huv⟩ := hvset
    have hu' : u ∈ C.region.vertexFinset := by
      exact Finset.mem_coe.mpr hu
    refine Finset.mem_image.mpr ⟨u.im, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨u, hu', rfl⟩
    · have him : (D.planarHomeomorph u).im = D.secondHomeomorph u.im := by
        rw [D.planarHomeomorph_apply]
        simp
      rw [← huv, him]
  · intro hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hq
    have hu' : u ∈ (C.region.vertexFinset : Set Plane) := by
      exact Finset.mem_coe.mpr hu
    have huv : D.planarHomeomorph u ∈
        (D.deformedRegion.vertexFinset : Set Plane) := by
      rw [hverts]
      exact ⟨u, hu', rfl⟩
    have hv : D.planarHomeomorph u ∈ D.deformedRegion.vertexFinset := huv
    exact Finset.mem_image.mpr ⟨D.planarHomeomorph u, hv,
      by rw [D.planarHomeomorph_apply]; simp⟩

private theorem imageRow_swap_source_vertex_levels
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {_H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    D.deformedRegion.coordinateSwap.vertexFinset.image Complex.re =
      (C.region.vertexFinset.image Complex.im).image D.secondHomeomorph := by
  rw [imageRow_swap_vertex_levels (_H := _H) D,
    imageRow_deformed_vertex_im_levels (_H := _H) D]

private theorem imageRow_swap_verticalSlice_eq
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {_H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (q : ℝ) :
    OneDimensional.ColumnSlices.verticalSlice D.deformedRegion.coordinateSwap q =
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q := by
  ext x
  change ((q : ℂ) + (x : ℂ) * Complex.I ∈
      D.deformedRegion.coordinateSwap.openCarrier) ↔
    Complex.mk x q ∈ D.deformedRegion.openCarrier
  rw [Tiling.AxisParallel.coordinateSwap_openCarrier]
  constructor
  · rintro ⟨z, hz, heq⟩
    have heq' : coordinateSwap ((q : ℂ) + (x : ℂ) * Complex.I) = z := by
      calc
        coordinateSwap ((q : ℂ) + (x : ℂ) * Complex.I) =
            coordinateSwap (coordinateSwap z) := congrArg coordinateSwap heq.symm
        _ = z := coordinateSwap_apply_apply z
    rw [← coordinateSwap_apply_apply (Complex.mk x q)]
    rw [show coordinateSwap (Complex.mk x q) =
        (q : ℂ) + (x : ℂ) * Complex.I by
          apply Complex.ext <;> simp]
    rw [heq']
    exact hz
  · intro hx
    refine ⟨Complex.mk x q, hx, ?_⟩
    apply Complex.ext <;> simp

private theorem imageRow_isCenterColumn_swap
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi) :
    IsCenterColumn Axis.vertical D.deformedRegion.coordinateSwap
      (coordinateSwap '' Set.range O.image) := by
  have hpack := imageRow_swap_packing H D O
  have hCyl := imageRow_swap_cylinder H O
  have hlevels := imageRow_swap_source_vertex_levels (_H := H) D
  have hYne : (Complex.re '' Set.range O.image).Nonempty := by
    exact ⟨(O.image ⟨H.anchor, H.anchor_mem_fibre⟩).re,
      ⟨O.image ⟨H.anchor, H.anchor_mem_fibre⟩, ⟨_, rfl⟩, rfl⟩⟩
  apply (Tiling.AxisParallel.Foundations.centerColumn_iff_genericSlices
    (K := D.deformedRegion.coordinateSwap)
    (C := coordinateSwap '' Set.range O.image)
    (c := (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im)
    (Y := Complex.re '' Set.range O.image) hCyl hYne hpack).2
  intro q hq hqne
  let y : ℝ := D.secondHomeomorph.symm q
  have hqy : q = D.secondHomeomorph y := by simp [y]
  have hy : y ∉ C.region.vertexFinset.image Complex.im := by
    intro hyv
    apply hq
    rw [hlevels]
    exact Finset.mem_image.mpr ⟨y, hyv, by simp [y]⟩
  have hslice := imageRow_swap_verticalSlice_eq (_H := H) D q
  have hDne :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice
        D.deformedRegion q).Nonempty := by
    simpa [hslice] using hqne
  have hsource :
      (Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice C.region y).Nonempty := by
    apply sourceSlice_nonempty_of_deformedSlice_nonempty D hqy
    exact hDne
  have hline := imageRow_genericSections_lineTile H D O hy hsource
  rw [← hqy] at hline
  simpa [hslice] using hline

private theorem coordinateSwap_im_preimage12 (B : Set ℝ) :
    coordinateSwap '' (Complex.im ⁻¹' B) =
      {z : Plane | z.re ∈ B} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [coordinateSwap] using hw
  · intro hz
    refine ⟨coordinateSwap z, ?_, coordinateSwap_apply_apply z⟩
    simpa [coordinateSwap] using hz

private theorem coordinateSwap_re_image12 (A : Set Plane) :
    Complex.re '' (coordinateSwap '' A) = Complex.im '' A := by
  ext r
  constructor
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, by simp [coordinateSwap]⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨coordinateSwap w, ⟨w, hw, rfl⟩, by simp [coordinateSwap]⟩

private theorem imageRow_regularSupport_horizontalInvariant
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi) :
    regularSupport D.deformedRegion (Set.range O.image) =
        Complex.im ⁻¹' imageRowBase_local H D O ∧
      ∀ x : ℝ,
        (x : ℂ) +ᵥ regularSupport D.deformedRegion (Set.range O.image) =
          regularSupport D.deformedRegion (Set.range O.image) := by
  have hcolumn := imageRow_isCenterColumn_swap H D O
  obtain ⟨c, _hne, hcoord, hsupport⟩ :=
    Tiling.AxisParallel.centerColumn_regularSupport hcolumn
  let c₀ : ℝ := (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im
  have hc : c = c₀ := by
    have ha := hcoord (coordinateSwap (O.image ⟨H.anchor, H.anchor_mem_fibre⟩))
      ⟨O.image ⟨H.anchor, H.anchor_mem_fibre⟩, ⟨_, rfl⟩, rfl⟩
    simpa [c₀, Axis.transverseCoord, coordinateSwap] using ha.symm
  have himage : Complex.re '' D.deformedRegion.coordinateSwap.openCarrier =
      Complex.im '' D.deformedRegion.openCarrier := by
    rw [Tiling.AxisParallel.coordinateSwap_openCarrier]
    exact coordinateSwap_re_image12 D.deformedRegion.openCarrier
  have hsupport' :
      regularSupport D.deformedRegion (Set.range O.image) =
        Complex.im ⁻¹' imageRowBase_local H D O := by
    have hswap := Tiling.AxisParallel.regularSupport_coordinateSwap
      D.deformedRegion (Set.range O.image)
    rw [hswap] at hsupport
    have hright :
        {z : Plane | z.re ∈ interior (closure
          (c +ᵥ (Complex.re '' D.deformedRegion.coordinateSwap.openCarrier)))} =
          coordinateSwap '' (Complex.im ⁻¹' imageRowBase_local H D O) := by
      rw [himage, hc]
      rw [closure_vadd, interior_vadd]
      ext z
      simp [imageRowBase_local, c₀, coordinateSwap_im_preimage12]
    change coordinateSwap '' regularSupport D.deformedRegion (Set.range O.image) =
      {z : Plane | z.re ∈ interior (closure
        (c +ᵥ (Complex.re '' D.deformedRegion.coordinateSwap.openCarrier)))} at hsupport
    rw [hright] at hsupport
    exact (Set.image_eq_image coordinateSwap.injective).mp hsupport
  refine ⟨hsupport', ?_⟩
  intro x
  rw [hsupport']
  ext z
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change ((-(x : ℂ) + z).im ∈ imageRowBase_local H D O) ↔
    z.im ∈ imageRowBase_local H D O
  simp [imageRowBase_local]



private def rowQuadrant (a z : Plane) (q : Fin 2 × Fin 2) : Prop :=
  (if q.1 = 1 then a.re < z.re else z.re < a.re) ∧
    (if q.2 = 1 then a.im < z.im else z.im < a.im)

private noncomputable def rowTransportHomeomorph
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (δ u w : ℝ) : Plane ≃ₜ Plane :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (((Homeomorph.addRight δ).prodCongr
      ((Homeomorph.addRight (-u)).trans D.secondHomeomorph |>.trans
        (Homeomorph.addLeft w))).trans
      Complex.equivRealProdCLM.toHomeomorph.symm)

private theorem rowTransportHomeomorph_apply
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (δ u w : ℝ) (z : Plane) :
    rowTransportHomeomorph D δ u w z =
      (z.re + δ : ℂ) + (w + D.secondHomeomorph (z.im - u)) * Complex.I := by
  rw [rowTransportHomeomorph]
  change Complex.equivRealProdCLM.symm
    (z.re + δ, w + D.secondHomeomorph (z.im + -u)) = _
  rw [Complex.equivRealProdCLM_symm_apply]
  simp [sub_eq_add_neg, add_comm]

private theorem rowTransport_quadrant_preserving
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (δ u w : ℝ)
    (a z : Plane) (q : Fin 2 × Fin 2) :
    rowQuadrant a z q ↔
      rowQuadrant (rowTransportHomeomorph D δ u w a)
        (rowTransportHomeomorph D δ u w z) q := by
  rw [rowTransportHomeomorph_apply, rowTransportHomeomorph_apply]
  simp only [rowQuadrant, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, mul_one, sub_zero, add_zero, zero_add, mul_zero]
  by_cases hq₁ : q.1 = 1 <;> by_cases hq₂ : q.2 = 1
  all_goals
    simp [hq₁, hq₂, add_lt_add_iff_left,
      D.secondHomeomorph_strictMono.lt_iff_lt, sub_lt_sub_iff_right]

private theorem finiteQuadrantGerm_mem_rowQuadrant_iff
    {U : Set Plane} {a : Plane} (q : Fin 2 × Fin 2) :
    q ∈ finiteQuadrantGerm U a ↔
      ∃ r : ℝ, 0 < r ∧ ∀ z, z ∈ Metric.ball a r →
        rowQuadrant a z q → z ∈ U := by
  simp only [finiteQuadrantGerm, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun z hz hq => h z hz hq⟩
  · rintro ⟨r, hr, h⟩
    exact ⟨r, hr, fun z hz hq => h z hz hq⟩

private theorem finiteQuadrantGerm_eq_of_homeomorph_image
    {U V : Set Plane} {a b : Plane} (F : Plane ≃ₜ Plane)
    (hFa : F a = b) (hV : V = F '' U)
    (hquad : ∀ q z, rowQuadrant a z q ↔ rowQuadrant b (F z) q) :
    finiteQuadrantGerm U a = finiteQuadrantGerm V b := by
  classical
  ext q
  rw [finiteQuadrantGerm_mem_rowQuadrant_iff,
    finiteQuadrantGerm_mem_rowQuadrant_iff]
  constructor
  · rintro ⟨r, hr, hq⟩
    obtain ⟨δ, hδ, hδsub⟩ :=
      (Metric.continuousAt_iff.mp F.symm.continuous.continuousAt) r hr
    refine ⟨δ, hδ, ?_⟩
    intro y hy hqy
    let x := F.symm y
    have hFsymm : F.symm b = a := by rw [← hFa]; simp
    have hxb : x ∈ Metric.ball a r := by
      rw [Metric.mem_ball]
      have hx := hδsub (x := y) hy
      simpa [x, hFsymm] using hx
    have hxq : rowQuadrant a x q :=
      (hquad q x).mpr (by simpa [x] using hqy)
    have hxU : x ∈ U := hq x hxb hxq
    rw [hV]
    exact ⟨x, hxU, by simp [x]⟩
  · rintro ⟨r, hr, hq⟩
    obtain ⟨δ, hδ, hδsub⟩ :=
      (Metric.continuousAt_iff.mp F.continuous.continuousAt) r hr
    refine ⟨δ, hδ, ?_⟩
    intro x hx hqx
    let y := F x
    have hyb : y ∈ Metric.ball b r := by
      rw [Metric.mem_ball]
      have hy := hδsub (x := x) hx
      simpa [y, hFa] using hy
    have hyq : rowQuadrant b y q := (hquad q x).mp hqx
    have hyV : y ∈ V := hq y hyb hyq
    rcases hV ▸ hyV with ⟨z, hzU, hzy⟩
    have hzx : z = x := by
      apply F.injective
      simpa [y] using hzy
    simpa [hzx] using hzU



private theorem secondProjection_openCarrier_image_owner
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    Complex.im '' D.deformedRegion.openCarrier =
      D.secondHomeomorph '' (Complex.im '' C.region.openCarrier) := by
  rw [D.deformedRegion_openCarrier]
  ext y
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z.im, ⟨z, hz, rfl⟩, ?_⟩
    rw [D.planarHomeomorph_apply]
    simp
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨D.planarHomeomorph z, ⟨z, hz, rfl⟩, ?_⟩
    rw [D.planarHomeomorph_apply]
    simp

private theorem secondProjection_regularized_image17
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    interior (closure (Complex.im '' D.deformedRegion.openCarrier)) =
      D.secondHomeomorph '' interior (closure (Complex.im '' C.region.openCarrier)) := by
  rw [secondProjection_openCarrier_image_owner D,
    ← D.secondHomeomorph.image_closure,
    ← D.secondHomeomorph.image_interior]

private theorem horizontalCylinderImage_owner
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source) {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (v : ↥C.region.vertices) (s : ↥H.fibre) :
    regularSupport D.deformedRegion (Set.range O.image) =
      rowTransportHomeomorph D
        ((D.planarHomeomorph v.1 + O.image s).re - (v.1 + s.1).re)
        H.anchor.im
        (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im ''
        regularSupport C.region H.fibre := by
  let sa : ↥H.fibre := ⟨H.anchor, H.anchor_mem_fibre⟩
  let a : Plane := v.1 + s.1
  let b : Plane := D.planarHomeomorph v.1 + O.image s
  let δ : ℝ := b.re - a.re
  let u : ℝ := H.anchor.im
  let w : ℝ := (O.image sa).im
  let F : Plane ≃ₜ Plane := rowTransportHomeomorph D δ u w
  have hsheight : s.1.im = u := by
    have hs' : (s : Plane) ∈
        (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
      rw [← H.fibre_eq]
      exact s.2
    exact hs'.2
  have hsim : (O.image s).im = w := by
    exact O.common_secondCoordinate s sa
  have hsource :
      regularSupport C.region H.fibre =
        Complex.im ⁻¹' (u +ᵥ
          interior (closure (Complex.im '' C.region.openCarrier))) := by
    simpa [u, closure_vadd, interior_vadd] using source_row_support_cylinder_exact H
  have himage :
      regularSupport D.deformedRegion (Set.range O.image) =
        Complex.im ⁻¹' (w +ᵥ
          interior (closure (Complex.im '' D.deformedRegion.openCarrier))) := by
    simpa [imageRowBase_local, w] using
      (imageRow_regularSupport_horizontalInvariant H D O).1
  have hproj := secondProjection_regularized_image17 D
  have himage' :
      regularSupport D.deformedRegion (Set.range O.image) =
        Complex.im ⁻¹' (w +ᵥ
          D.secondHomeomorph '' interior
            (closure (Complex.im '' C.region.openCarrier))) := by
    rw [himage, hproj]
  have hset :
      F '' (Complex.im ⁻¹' (u +ᵥ
          interior (closure (Complex.im '' C.region.openCarrier)))) =
        Complex.im ⁻¹' (w +ᵥ
          D.secondHomeomorph '' interior
            (closure (Complex.im '' C.region.openCarrier))) := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (rowTransportHomeomorph D δ u w x).im ∈ w +ᵥ D.secondHomeomorph ''
        interior (closure (Complex.im '' C.region.openCarrier))
      have hx' : x.im ∈ u +ᵥ
          interior (closure (Complex.im '' C.region.openCarrier)) := hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      rw [rowTransportHomeomorph_apply]
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_im, Complex.I_re, zero_mul, mul_one, add_zero, zero_add]
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      exact ⟨x.im - u,
        by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hx', by simp⟩
    · intro hz
      change z.im ∈ w +ᵥ D.secondHomeomorph ''
        interior (closure (Complex.im '' C.region.openCarrier)) at hz
      have hz' : z.im ∈ w +ᵥ
          D.secondHomeomorph '' interior
            (closure (Complex.im '' C.region.openCarrier)) := hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz'
      obtain ⟨y, hy, hzy⟩ := hz'
      let t : Plane := (z.re - δ : ℂ) + (y + u : ℂ) * Complex.I
      have htmem : t.im ∈ u +ᵥ
          interior (closure (Complex.im '' C.region.openCarrier)) := by
        rw [show t.im = y + u by simp [t]]
        exact ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩
      have hFt : F t = z := by
        rw [rowTransportHomeomorph_apply]
        apply Complex.ext
        · simp [t, δ]
        · simp [t, hzy, sub_eq_add_neg, add_comm]
      exact ⟨t, htmem, hFt⟩
  rw [himage', ← hset, hsource]


private theorem finiteQuadrantGerm_eq_of_eq_on_ball
    {U V : Set Plane} {a : Plane} {R : ℝ} (hR : 0 < R)
    (hUV : ∀ z ∈ Metric.ball a R, z ∈ U ↔ z ∈ V) :
    finiteQuadrantGerm U a = finiteQuadrantGerm V a := by
  classical
  ext q
  rw [finiteQuadrantGerm_mem_rowQuadrant_iff,
    finiteQuadrantGerm_mem_rowQuadrant_iff]
  constructor
  · rintro ⟨r, hr, hq⟩
    refine ⟨min r R, lt_min hr hR, ?_⟩
    intro z hz hquad
    exact (hUV z (Metric.ball_subset_ball (min_le_right _ _) hz)).mp
      (hq z (Metric.ball_subset_ball (min_le_left _ _) hz) hquad)
  · rintro ⟨r, hr, hq⟩
    refine ⟨min r R, lt_min hr hR, ?_⟩
    intro z hz hquad
    exact (hUV z (Metric.ball_subset_ball (min_le_right _ _) hz)).mpr
      (hq z (Metric.ball_subset_ball (min_le_left _ _) hz) hquad)



private theorem finiteQuadrantGerm_of_horizontalCylinderImage
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (O : HorizontalColumnOrderData C H phi)
    (v : ↥C.region.vertices) (s : ↥H.fibre)
    (himage :
      regularSupport D.deformedRegion (Set.range O.image) =
        rowTransportHomeomorph D
          ((D.planarHomeomorph v.1 + O.image s).re - (v.1 + s.1).re)
          H.anchor.im
          (O.image ⟨H.anchor, H.anchor_mem_fibre⟩).im ''
          regularSupport C.region H.fibre) :
    finiteQuadrantGerm (regularSupport C.region H.fibre) (v.1 + s.1) =
      finiteQuadrantGerm (regularSupport D.deformedRegion (Set.range O.image))
        (D.planarHomeomorph v.1 + O.image s) := by
  let sa : ↥H.fibre := ⟨H.anchor, H.anchor_mem_fibre⟩
  let a : Plane := v.1 + s.1
  let b : Plane := D.planarHomeomorph v.1 + O.image s
  let δ : ℝ := b.re - a.re
  let F : Plane ≃ₜ Plane := rowTransportHomeomorph D δ H.anchor.im (O.image sa).im
  have hsheight : s.1.im = H.anchor.im := by
    have hs' : (s : Plane) ∈
        (H.limit.centres : Set Plane) ∩ {z : Plane | z.im = H.anchor.im} := by
      rw [← H.fibre_eq]
      exact s.2
    exact hs'.2
  have hsim : (O.image s).im = (O.image sa).im :=
    O.common_secondCoordinate s sa
  have hFa : F a = b := by
    rw [rowTransportHomeomorph_apply]
    change (a.re + δ : ℂ) +
      ((O.image sa).im + D.secondHomeomorph (a.im - H.anchor.im)) * Complex.I =
        D.planarHomeomorph v.1 + O.image s
    rw [D.planarHomeomorph_apply]
    apply Complex.ext <;>
      simp [D.planarHomeomorph_apply, a, b, δ, hsheight, hsim, sa,
        sub_eq_add_neg] <;> ring
  have hquad : ∀ q z, rowQuadrant a z q ↔ rowQuadrant b (F z) q := by
    intro q z
    rw [← hFa]
    dsimp [F]
    exact rowTransport_quadrant_preserving D δ H.anchor.im (O.image sa).im a z q
  exact finiteQuadrantGerm_eq_of_homeomorph_image F hFa himage hquad

private theorem completeFinitePatch_germ
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (Q : Finset (↥H.fibre)) (v : ↥C.region.vertices) (s : ↥H.fibre) :
    s ∈ Q → ∀ sourceRadius imageRadius : ℝ,
      Metric.diam (closure C.region.openCarrier) < sourceRadius →
      Metric.diam (closure D.deformedRegion.openCarrier) < imageRadius →
      (∀ t : ↥H.fibre, dist t.1 s.1 ≤ sourceRadius → t ∈ Q) →
      (∀ t : ↥H.fibre, dist (O.image t) (O.image s) ≤ imageRadius → t ∈ Q) →
      finiteQuadrantGerm
          (regularSupport C.region
            (((↑) : ↥H.fibre → Tiling.Plane) '' (Q : Set ↥H.fibre))) (v.1 + s.1) =
        finiteQuadrantGerm
          (regularSupport D.deformedRegion (O.image '' (Q : Set ↥H.fibre)))
          (D.planarHomeomorph v.1 + O.image s) := by
  intro hsQ sourceRadius imageRadius hsource himage hQsource hQimage
  obtain ⟨rs, hrs, hs⟩ := source_regularSupport_complete_on_ball Q v s hsQ hsource hQsource
  obtain ⟨ri, hri, hi⟩ := image_regularSupport_complete_on_ball D O Q v s hsQ himage hQimage
  have hsf := finiteQuadrantGerm_eq_of_eq_on_ball hrs hs
  have hif := finiteQuadrantGerm_eq_of_eq_on_ball hri hi
  have hrow := finiteQuadrantGerm_of_horizontalCylinderImage H D O v s
    (horizontalCylinderImage_owner H D O v s)
  exact hsf.trans (hrow.trans hif.symm)

theorem deformation_preservesFiniteQuadrantGerm
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) (O : HorizontalColumnOrderData C H phi)
    (Q : Finset (↥H.fibre)) (v : ↥C.region.vertices) (s : ↥H.fibre) :
    s ∈ Q → ∀ sourceRadius imageRadius : ℝ,
      Metric.diam (closure C.region.openCarrier) < sourceRadius →
      Metric.diam (closure D.deformedRegion.openCarrier) < imageRadius →
      (∀ t : ↥H.fibre, dist t.1 s.1 ≤ sourceRadius → t ∈ Q) →
      (∀ t : ↥H.fibre, dist (O.image t) (O.image s) ≤ imageRadius → t ∈ Q) →
      finiteQuadrantGerm
          (regularSupport C.region
            (((↑) : ↥H.fibre → Tiling.Plane) '' (Q : Set ↥H.fibre))) (v.1 + s.1) =
        finiteQuadrantGerm
          (regularSupport D.deformedRegion (O.image '' (Q : Set ↥H.fibre)))
          (D.planarHomeomorph v.1 + O.image s) := by
  exact completeFinitePatch_germ D O Q v s

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open Tiling AxisParallel
open Tiling.AxisParallel.Foundations

private def pairQuadrant (q : Fin 2 × Fin 2) : Quadrant :=
  match q.1.1, q.2.1 with
  | 0, 0 => .southwest
  | 0, 1 => .northwest
  | 1, 0 => .southeast
  | _, _ => .northeast

private theorem pairQuadrant_zero_zero :
    pairQuadrant (0, 0) = .southwest := by rfl

private theorem pairQuadrant_one_zero :
    pairQuadrant (1, 0) = .southeast := by rfl

private theorem pairQuadrant_zero_one :
    pairQuadrant (0, 1) = .northwest := by rfl

private theorem pairQuadrant_one_one :
    pairQuadrant (1, 1) = .northeast := by rfl

private theorem finiteQuadrantGerm_mem_iff_occupies
    {D : Set Plane} {a : Plane} (q : Fin 2 × Fin 2) :
    q ∈ finiteQuadrantGerm D a ↔
      SetOccupiesQuadrant D a (pairQuadrant q) := by
  classical
  rcases q with ⟨i, j⟩
  fin_cases i <;> fin_cases j
  · simp only [finiteQuadrantGerm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (∃ r, 0 < r ∧ ∀ z ∈ Metric.ball a r,
      (z.re < a.re ∧ z.im < a.im) → z ∈ D) ↔
        SetOccupiesQuadrant D a .southwest
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz
      have hq := hz.2
      change z.re < a.re ∧ z.im < a.im at hq
      exact hsub z hz.1 hq
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz hq
      apply hsub
      refine ⟨hz, ?_⟩
      change z.re < a.re ∧ z.im < a.im
      exact hq
  · simp only [finiteQuadrantGerm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (∃ r, 0 < r ∧ ∀ z ∈ Metric.ball a r,
      (z.re < a.re ∧ a.im < z.im) → z ∈ D) ↔
        SetOccupiesQuadrant D a .northwest
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz
      have hq := hz.2
      change z.re < a.re ∧ a.im < z.im at hq
      exact hsub z hz.1 hq
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz hq
      apply hsub
      refine ⟨hz, ?_⟩
      change z.re < a.re ∧ a.im < z.im
      exact hq
  · simp only [finiteQuadrantGerm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (∃ r, 0 < r ∧ ∀ z ∈ Metric.ball a r,
      (a.re < z.re ∧ z.im < a.im) → z ∈ D) ↔
        SetOccupiesQuadrant D a .southeast
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz
      have hq := hz.2
      change a.re < z.re ∧ z.im < a.im at hq
      exact hsub z hz.1 hq
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz hq
      apply hsub
      refine ⟨hz, ?_⟩
      change a.re < z.re ∧ z.im < a.im
      exact hq
  · simp only [finiteQuadrantGerm, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (∃ r, 0 < r ∧ ∀ z ∈ Metric.ball a r,
      (a.re < z.re ∧ a.im < z.im) → z ∈ D) ↔
        SetOccupiesQuadrant D a .northeast
    constructor
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz
      have hq := hz.2
      change a.re < z.re ∧ a.im < z.im at hq
      exact hsub z hz.1 hq
    · rintro ⟨r, hr, hsub⟩
      refine ⟨r, hr, ?_⟩
      intro z hz hq
      apply hsub
      refine ⟨hz, ?_⟩
      change a.re < z.re ∧ a.im < z.im
      exact hq

private def quadrantPair : Quadrant → Fin 2 × Fin 2
  | .southwest => (0, 0)
  | .southeast => (1, 0)
  | .northwest => (0, 1)
  | .northeast => (1, 1)

private theorem pairQuadrant_quadrantPair (q : Quadrant) :
    pairQuadrant (quadrantPair q) = q := by
  cases q <;> rfl

private theorem germ_target_iff_nonstraight
    {G : Finset (Fin 2 × Fin 2)} {p : QuadrantPattern}
    (hmem : ∀ q, q ∈ G ↔ p (pairQuadrant q) = true) :
    nonstraightPattern p ↔
      G.card = 1 ∨ G.card = 3 ∨
        ∃ q r : Fin 2 × Fin 2,
          q ∈ G ∧ r ∈ G ∧ q.1 ≠ r.1 ∧ q.2 ≠ r.2 ∧ G = ({q, r} : Finset (Fin 2 × Fin 2)) := by
  classical
  rcases Bool.eq_false_or_eq_true (p .southwest) with hsw | hsw <;>
    rcases Bool.eq_false_or_eq_true (p .southeast) with hse | hse <;>
    rcases Bool.eq_false_or_eq_true (p .northwest) with hnw | hnw <;>
    rcases Bool.eq_false_or_eq_true (p .northeast) with hne | hne
  all_goals
    have hG : G = (Finset.univ : Finset (Fin 2 × Fin 2)).filter
        (fun q => p (pairQuadrant q) = true) := by
      apply Finset.ext
      intro q
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hmem q
    have h00 : p (pairQuadrant (0, 0)) = p .southwest := by
      rw [pairQuadrant_zero_zero]
    have h10 : p (pairQuadrant (1, 0)) = p .southeast := by
      rw [pairQuadrant_one_zero]
    have h01 : p (pairQuadrant (0, 1)) = p .northwest := by
      rw [pairQuadrant_zero_one]
    have h11 : p (pairQuadrant (1, 1)) = p .northeast := by
      rw [pairQuadrant_one_one]
    have huniv : (Finset.univ : Finset (Fin 2 × Fin 2)) =
        {(0, 0), (0, 1), (1, 0), (1, 1)} := by
      apply Finset.ext
      intro q
      rcases q with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> simp
    rw [hG]
    rw [huniv]
    simp only [Finset.filter_insert, Finset.filter_singleton]
    simp only [nonstraightPattern, straightPattern, hsw, hse, hnw, hne,
      h00, h10, h01, h11, Fin.isValue, ne_eq, exists_and_left, Prod.exists,
      Fin.exists_fin_two, not_true_eq_false, false_and, and_false, zero_ne_one,
      not_false_eq_true, true_and, false_or, one_ne_zero, or_false] ; decide

theorem finiteQuadrantGerm_properVertex_iff
    {D : Set Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D)
    (hDpolygonal : IsLocallyAxisParallelPolygonal D)
    (x : Plane) :
    IsProperVertex D x ↔
      (finiteQuadrantGerm D x).card = 1 ∨
      (finiteQuadrantGerm D x).card = 3 ∨
      ∃ q r : Fin 2 × Fin 2,
        q ∈ finiteQuadrantGerm D x ∧
        r ∈ finiteQuadrantGerm D x ∧
        q.1 ≠ r.1 ∧ q.2 ≠ r.2 ∧
        finiteQuadrantGerm D x = ({q, r} : Finset (Fin 2 × Fin 2)) := by
  obtain ⟨ρ, hρ, p, hg, hchar⟩ :=
    exists_quadrantPattern_germ hDopen hDregular hDpolygonal x
  rw [properVertex_iff_nonstraightPattern hDopen hDregular hρ p hg]
  apply germ_target_iff_nonstraight
  intro q
  calc
    q ∈ finiteQuadrantGerm D x ↔
        SetOccupiesQuadrant D x (pairQuadrant q) :=
      finiteQuadrantGerm_mem_iff_occupies q
    _ ↔ p (pairQuadrant q) = true := (hchar _).symm

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open MeasureTheory Set Filter
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

/- Literal append fragment for SimultaneousColumns.lean; intentionally import-free. -/

private theorem target19_fullCarrier_closed
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D) :
    IsClosed (deformedCenterCarrier P.fullCenters) := by
  rw [show deformedCenterCarrier P.fullCenters =
      ⋃ t : deformedCenterCarrier P.fullCenters, {t.1} by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨P.fullCenters t, ⟨t, rfl⟩⟩, Set.mem_singleton _⟩
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨t, rfl⟩ := hz
      exact t.2]
  exact P.full_locallyFinite.isClosed_iUnion (fun _ => isClosed_singleton)

private noncomputable def target19_fullCarrierTiling
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D) :
    TilingSpace D.deformedRegion Set.univ :=
  { centres := ⟨deformedCenterCarrier P.fullCenters, target19_fullCarrier_closed P⟩
    tilesOn := P.full_tilesOn }

private theorem target19_translation_mem_univ (u : Plane) :
    u ∈ aePeriodGroup (Set.univ : Set Plane) := by
  simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup, AddAction.aestabilizer]

/-- Corrected subsequence-indexed orbit limit with its complete horizontal
column in the limit tiling. Append inside namespace Tiling.AxisParallel.Structure. -/
theorem orbitLimit_hasHorizontalColumn
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (O : HorizontalColumnOrderData C H phi) :
    Nonempty (HorizontalColumnOrbitLimitData C H phi D P O) := by
  let deformedSource := target19_fullCarrierTiling P
  have hsource_centres : (deformedSource.centres : Set Plane) =
      deformedCenterCarrier P.fullCenters := rfl
  let rawTranslations : ℕ → aePeriodGroup (Set.univ : Set Plane) := fun n =>
    ⟨P.fullCenters ⟨H.anchor, H.anchor_mem_context⟩ -
      P.fullCenters ⟨H.movingCentre n, H.movingCentre_mem_context n⟩,
      target19_translation_mem_univ _⟩
  have htiles : ∀ n, TilesOn D.deformedRegion
      ((TilingSpace.translate (rawTranslations n) deformedSource).centres : Set Plane)
      Set.univ := fun n => (TilingSpace.translate (rawTranslations n) deformedSource).tilesOn
  obtain ⟨subsequence, L, hsub, hLtiles, hLclosed, hconv, _hmem⟩ :=
    exists_tilesOn_locallyFellSubsequence
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence rawTranslations deformedSource)) htiles
  let limit : TilingSpace D.deformedRegion Set.univ :=
    { centres := ⟨L, hLclosed⟩, tilesOn := hLtiles }
  let translations : ℕ → aePeriodGroup (Set.univ : Set Plane) :=
    fun n => rawTranslations (subsequence n)
  have hconv' : LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence translations deformedSource))
      (limit.centres : Set Plane) := by
    change LocallyFellConverges
      (fun n => TilingSpace.centresSequence
        (TilingSpace.translateSequence rawTranslations deformedSource) (subsequence n)) L
    exact hconv
  have hrow_eventual : ∀ s : ↥H.fibre, ∀ᶠ n : ℕ in atTop,
      O.image s ∈
        ((TilingSpace.translate (translations n) deformedSource).centres : Set Plane) := by
    intro s
    have hpull := H.persistent_pullback s.1 s.2
    have hpull' := hpull.filter_mono hsub.tendsto_atTop
    filter_upwards [hpull'] with n hn
    let t : C.centres := ⟨s.1 - (H.translations (subsequence n) : Plane), hn⟩
    let xt := O.coordinateLift s
    let xa := C.centrePoint H.anchor H.anchor_mem_context
    let xm := C.centrePoint (H.movingCentre (subsequence n))
      (H.movingCentre_mem_context (subsequence n))
    let xsub : {z : Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} :=
      ⟨(xa : Plane) - (xm : Plane),
        C.coordinateSpace.sub_mem xa.2.1 xm.2.1,
        C.coordinateSpace.sub_mem xa.2.2 xm.2.2⟩
    let xxsub : {z : Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} :=
      ⟨(xt : Plane) - (xsub : Plane),
        C.coordinateSpace.sub_mem xt.2.1 xsub.2.1,
        C.coordinateSpace.sub_mem xt.2.2 xsub.2.2⟩
    have hpoint : C.centrePoint t.1 t.2 = xxsub := by
      apply Subtype.ext
      change (t : Plane) = (xt : Plane) - ((xa : Plane) - (xm : Plane))
      dsimp [t, xxsub, xsub, xt, xa, xm]
      rw [H.translations_eq, O.coordinateLift_coe]
      simp [ApproximationContext.centrePoint, sub_eq_add_neg]
    have hxs := mapPoint_sub_local phi xt xsub
    have hxa := mapPoint_sub_local phi xa xm
    have himage : O.image s =
        (P.fullCenters ⟨H.anchor, H.anchor_mem_context⟩ -
          P.fullCenters ⟨H.movingCentre (subsequence n),
            H.movingCentre_mem_context (subsequence n)⟩) + P.fullCenters t := by
      rw [O.image_apply, P.fullCenters_apply, P.fullCenters_apply, P.fullCenters_apply]
      rw [hpoint, hxs, hxa]
      ring
    change O.image s ∈
      (fun x => x + (translations n : Plane)) '' (deformedSource.centres : Set Plane)
    refine ⟨P.fullCenters t, ⟨t, rfl⟩, ?_⟩
    rw [himage]
    simp [translations, rawTranslations, add_comm]
  have hrow_subset : Set.range O.image ⊆ (limit.centres : Set Plane) := by
    rintro z ⟨s, rfl⟩
    by_contra hz
    have hdisj : Disjoint (limit.centres : Set Plane) ({O.image s} : Set Plane) := by
      rw [Set.disjoint_singleton_right]
      exact hz
    have hev := Tiling.AxisParallel.Continuous.locallyFellConverges_eventually_disjoint_compact
      hconv' (isCompact_singleton : IsCompact ({O.image s} : Set Plane)) hdisj
    obtain ⟨n, hn, hmem⟩ := (hev.and (hrow_eventual s)).exists
    exact Set.disjoint_left.mp hn hmem (Set.mem_singleton _)
  have hlimit_hull : limit ∈ orbitHull deformedSource := by
    have htl : Filter.Tendsto
        (fun n => TilingSpace.translate (translations n) deformedSource)
        atTop (nhds limit) := by
      apply ((locallyFell_metrizable D.deformedRegion Set.univ).2 _ limit).mpr
      exact hconv'
    apply isClosed_closure.mem_of_tendsto htl
    exact Filter.Eventually.of_forall (fun n => subset_closure (AddAction.mem_orbit _ _))
  let row := coordinateSwap '' Set.range O.image
  have hrowColumn := imageRow_isCenterColumn_swap H D O
  have hrow_subset_swap : row ⊆
      (coordinateSwap '' (limit.centres : Set Plane)) :=
    Set.image_mono hrow_subset
  have hlimitSwapTiles :
      TilesOn D.deformedRegion.coordinateSwap
        (coordinateSwap '' (limit.centres : Set Plane)) Set.univ := by
    simpa using tilesOn_coordinateSwap limit.tilesOn
  have hanchor_row :
      coordinateSwap (O.image ⟨H.anchor, H.anchor_mem_fibre⟩) ∈ row :=
    ⟨O.image ⟨H.anchor, H.anchor_mem_fibre⟩,
      ⟨⟨H.anchor, H.anchor_mem_fibre⟩, rfl⟩, rfl⟩
  obtain ⟨horizontalColumn, hcolumn, _hanchor, hcentres⟩ :=
    Tiling.AxisParallel.Continuous.completeColumn_eq_verticalPlateThrough
      hlimitSwapTiles hrowColumn hrow_subset_swap hanchor_row
  have hsupport :=
    (VerticalPlate.support_isVerticalSlab hlimitSwapTiles horizontalColumn).2
  refine ⟨{
    deformedSource := deformedSource
    deformedSource_centres := hsource_centres
    subsequence := subsequence
    subsequence_strictMono := hsub
    translations := translations
    translations_eq := ?_
    limit := limit
    limit_mem_hull := hlimit_hull
    converges := hconv'
    rowImage_subset := hrow_subset
    rowImage_eventuallyMem := hrow_eventual
    horizontalColumn := horizontalColumn
    horizontalColumn_isColumn := hcolumn
    horizontalColumn_centres := hcentres
    horizontalColumn_support := hsupport
  }⟩
  intro n
  rfl



open Filter
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private theorem image_translation_eq_vadd_local (v : Plane) (S : Set Plane) :
    positiveSimilarity 1 v '' S = v +ᵥ S := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [positiveSimilarity, Set.mem_vadd_set_iff_neg_vadd_mem]
  · intro hz
    refine ⟨-v + z, ?_, ?_⟩
    · simpa [Set.mem_vadd_set_iff_neg_vadd_mem] using hz
    · simp [positiveSimilarity]

private theorem source_verticalColumn_exists_local
    {C : ApproximationContext}
    (hTile : TilesOn C.region C.centres Set.univ)
    (hNonempty : C.centres.Nonempty)
    (hNontrivial :
      ¬ ∃ Q : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres) :
    ∃ Q : VerticalPlate C.region C.centres, IsVerticalColumn Q := by
  obtain ⟨c, hc⟩ := hNonempty
  let Q₀ : VerticalPlate C.region C.centres :=
    VerticalPlate.ofCentre (K := C.region) ⟨c, hc⟩
  by_cases hQ₀ : IsVerticalColumn Q₀
  · exact ⟨Q₀, hQ₀⟩
  · have hAtMost
        (P Q : VerticalPlate C.region C.centres)
        (hPnoncolumn : ¬ IsVerticalColumn P)
        (hQnoncolumn : ¬ IsVerticalColumn Q) : P = Q := by
      by_contra hPQ
      obtain ⟨M, hM, hDense⟩ :=
        componentBoundarySet_relativelyDense_of_two_noncolumnPlates hTile
          ⟨P, Q, hPQ, hPnoncolumn, hQnoncolumn⟩
      exact hInfinite (finiteHorizontalComplexity_of_relativelyDenseBoundaries
        hTile hNontrivial ⟨M, hM, hDense⟩)
    by_contra hNoColumn
    apply hNontrivial
    refine ⟨Q₀, hQ₀, ?_⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact t.property
    · intro z hz
      let Qz : VerticalPlate C.region C.centres :=
        VerticalPlate.ofCentre (K := C.region) ⟨z, hz⟩
      by_cases hQz : IsVerticalColumn Qz
      · exact (hNoColumn ⟨Qz, hQz⟩).elim
      · have hEq : Qz = Q₀ := hAtMost Qz Q₀ hQz hQ₀
        have hzQz : z ∈ Qz.centres := by
          exact VerticalPlate.mem_centres_ofCentre ⟨z, hz⟩
        rw [hEq] at hzQz
        exact hzQz

private noncomputable def translatedVerticalPlate_local
    {K : Region} {T : Set Plane} (v : Plane)
    (Q : VerticalPlate K T) : VerticalPlate K (positiveSimilarity 1 v '' T) :=
  verticalPlate_positiveSimilarityEquiv (K := K) (R := K) (T := T)
    (s := 1) (r := 0) (by norm_num) (by ext z; simp [positiveSimilarity]) v Q

private theorem translatedVerticalPlate_local_centres
    {K : Region} {T : Set Plane} (v : Plane)
    (Q : VerticalPlate K T) :
    (translatedVerticalPlate_local v Q).centres =
      positiveSimilarity 1 v '' Q.centres := by
  exact verticalPlate_positiveSimilarityEquiv_centres_image
    (K := K) (R := K) (T := T)
    (s := 1) (r := 0) (by norm_num) (by ext z; simp [positiveSimilarity]) v Q

private theorem translatedVerticalPlate_local_column
    {K : Region} {T : Set Plane} (v : Plane)
    (Q : VerticalPlate K T) (hQ : IsVerticalColumn Q) :
    IsVerticalColumn (translatedVerticalPlate_local v Q) := by
  exact (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
    (K := K) (R := K) (T := T)
    (s := 1) (r := 0) (by norm_num) (by ext z; simp [positiveSimilarity]) v Q).mp hQ

private theorem translatedVerticalPlate_anchored_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {T : Set Plane}
    (v : Plane) (Q : VerticalPlate D.deformedRegion T)
    (hQcolumn : IsVerticalColumn Q) (a : Plane) (ha : a ∈ Q.centres) :
    ∃ A : AnchoredDeformedColumn
        (C := C) (D := D) (positiveSimilarity 1 v '' T),
      A.plate = translatedVerticalPlate_local v Q ∧
      A.anchor = positiveSimilarity 1 v a ∧
      A.normalized = -a +ᵥ Q.centres := by
  let R := translatedVerticalPlate_local v Q
  let b : Plane := positiveSimilarity 1 v a
  have hRcentres : R.centres = positiveSimilarity 1 v '' Q.centres :=
    translatedVerticalPlate_local_centres v Q
  have hb : b ∈ R.centres := by
    rw [hRcentres]
    exact ⟨a, ha, rfl⟩
  have hRcolumn : IsVerticalColumn R :=
    translatedVerticalPlate_local_column v Q hQcolumn
  have hnorm : -b +ᵥ R.centres = -a +ᵥ Q.centres := by
    rw [hRcentres, image_translation_eq_vadd_local]
    ext z
    constructor
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [b, positiveSimilarity, vadd_eq_add]
      ; ring
    · rintro ⟨x, hx, rfl⟩
      refine ⟨v + x, ⟨x, hx, ?_⟩, ?_⟩
      · simp
      · simp [b, positiveSimilarity, vadd_eq_add]
        ; ring
  refine ⟨{
    plate := R
    isColumn := hRcolumn
    anchor := b
    anchor_mem := hb
    normalized := -a +ᵥ Q.centres
    normalized_eq := hnorm.symm
    zero_mem := ?_ }, rfl, rfl, rfl⟩
  exact ⟨a, ha, by simp [vadd_eq_add]⟩

private theorem source_verticalColumn_transport_prefix
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (hNontrivial :
      ¬ ∃ Q : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres) :
    ∃ Q : VerticalPlate C.region C.centres,
      IsVerticalColumn Q ∧
      ∃ A : Set (VerticalPlate D.deformedRegion
          (deformedCenterCarrier P.fullCenters)),
        A.Nonempty ∧
        (∀ R ∈ A, IsVerticalColumn R) ∧
        deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Plane) ∈ Q.centres} =
          ⋃ R : A, R.1.centres := by
  have hQtile : TilesOn C.region C.centres Set.univ := P.source_tilesOn
  obtain ⟨Q, hQcolumn⟩ := source_verticalColumn_exists_local
    hQtile ⟨H.anchor, H.anchor_mem_context⟩ hNontrivial hInfinite
  obtain ⟨A, hAne, hAcolumn, hAunion⟩ :=
    deformation_originalColumn_hasColumn P Q hQcolumn
  exact ⟨Q, hQcolumn, A, hAne, hAcolumn, hAunion⟩

private theorem translated_orbit_centres_eq_positiveSimilarity_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    {H : PersistentHorizontalFibreData C source}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    {P : TwoStageDeformationSupportTransport C phi D}
    {O : HorizontalColumnOrderData C H phi}
    (L : HorizontalColumnOrbitLimitData C H phi D P O)
    (n : ℕ) :
    ((TilingSpace.translate (L.translations n) L.deformedSource).centres : Set Plane) =
      positiveSimilarity 1 (L.translations n : Plane) ''
        deformedCenterCarrier P.fullCenters := by
  change (fun x : Plane ↦ x + (L.translations n : Plane)) ''
      (L.deformedSource.centres : Set Plane) = _
  rw [L.deformedSource_centres]
  have himage :
      (fun x : Plane ↦ x + (L.translations n : Plane)) ''
          deformedCenterCarrier P.fullCenters =
        (L.translations n : Plane) +ᵥ deformedCenterCarrier P.fullCenters := by
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
  rw [himage, image_translation_eq_vadd_local]

private theorem translated_transport_anchored_column_exists
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    (hNontrivial :
      ¬ ∃ Q : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres)
    (v : Plane) :
    ∃ Q : VerticalPlate C.region C.centres, IsVerticalColumn Q ∧
      ∃ A : Set (VerticalPlate D.deformedRegion
          (deformedCenterCarrier P.fullCenters)),
        A.Nonempty ∧
        (∀ R ∈ A, IsVerticalColumn R) ∧
        ∃ R ∈ A, ∃ B : AnchoredDeformedColumn
          (C := C) (D := D)
          (positiveSimilarity 1 v '' deformedCenterCarrier P.fullCenters),
          B.plate = translatedVerticalPlate_local v R ∧
          IsVerticalColumn B.plate := by
  obtain ⟨Q, hQ, A, hAne, hAcol, _hAunion⟩ :=
    source_verticalColumn_transport_prefix H P hNontrivial hInfinite
  have hAne' := hAne
  obtain ⟨R, hR⟩ := hAne'
  obtain ⟨a, ha⟩ := R.nonempty_supp
  let R0 : VerticalPlate D.deformedRegion
      (deformedCenterCarrier P.fullCenters) := R
  have ha' : (a : Plane) ∈ R0.centres := ⟨a, ha, rfl⟩
  obtain ⟨B, hBplate, _hBanchor, _hBnorm⟩ :=
    translatedVerticalPlate_anchored_local v R0 (hAcol R hR) a ha'
  exact ⟨Q, hQ, A, hAne, hAcol, R, hR, B, hBplate, B.isColumn⟩


private theorem deformedRegion_relativelyRational_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi) :
    Tiling.RationalPolygonal.IsRelativelyRational
      D.deformedRegion.toPolygonalRegion := by
  obtain ⟨v, hv, w, hw, hmax, hdiam⟩ :=
    IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
  refine ⟨v, hv, ?_⟩
  intro z hz
  obtain ⟨vx, vy, hvx, hvy⟩ := D.rational_vertices v hv
  obtain ⟨zx, zy, hzx, hzy⟩ := D.rational_vertices z hz
  refine ⟨zx - vx, zy - vy, ?_, ?_⟩
  · rw [Complex.sub_re, hvx, hzx]
    norm_num
  · rw [Complex.sub_im, hvy, hzy]
    norm_num

private theorem translated_column_axes_bound_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (U : TilingSpace D.deformedRegion Set.univ)
    (B : AnchoredDeformedColumn (C := C) (phi := phi) (D := D)
      (U.centres : Set Plane)) :
    ∃ beta R : ℝ, 0 < beta ∧ 0 < R ∧
      ∀ x : ℝ, ∃ a ∈ verticalColumnCentres D.deformedRegion
          (U.centres : Set Plane), |a.re - x| ≤ R := by
  have hCne : (verticalColumnCentres D.deformedRegion
      (U.centres : Set Plane)).Nonempty := by
    refine ⟨B.anchor, ?_⟩
    rw [verticalColumnCentres_eq]
    exact Set.mem_iUnion.mpr ⟨⟨B.plate, B.isColumn⟩, B.anchor_mem⟩
  obtain ⟨beta, R, hbeta, hR, _hperiod, hbound⟩ :=
    deformedColumnAxes_relativelyDense U.tilesOn
      (deformedRegion_relativelyRational_local D) hCne
  exact ⟨beta, R, hbeta, hR, hbound⟩


private theorem vadd_vadd_set_local20 (a b : ℝ) (S : Set ℝ) :
    a +ᵥ (b +ᵥ S) = (a + b) +ᵥ S := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro hx <;> convert hx using 1 <;> ring

private theorem preimage_add_left_local20 (u : ℝ) (S : Set ℝ) :
    (fun x : ℝ ↦ -u + x) ⁻¹' S = u +ᵥ S := by
  ext x
  simp only [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]

private theorem lineTiles_translate_local20
    {B L : Set ℝ} (hTile : LineTiles B L) (u : ℝ) :
    LineTiles B (u +ᵥ L) := by
  change LineTilesOn B (u +ᵥ L) Set.univ
  refine ⟨hTile.1, MeasurableSet.univ, ?_, ?_, ?_⟩
  · have heq : u +ᵥ L = (fun l : ℝ ↦ u + l) '' L := by
      ext x
      simp [Set.mem_vadd_set_iff_neg_vadd_mem, add_comm]
    rw [heq]
    exact hTile.2.2.1.image _
  · intro l hl m hm hlm
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    obtain ⟨m₀, hm₀, rfl⟩ := hm
    have hlm₀ : l₀ ≠ m₀ := by
      intro heq
      exact hlm (by simp [heq])
    have hd := hTile.2.2.2.1 hl₀ hm₀ hlm₀
    have hd' := hd.preimage
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u))
    rw [preimage_add_left_local20, preimage_add_left_local20] at hd'
    simpa [vadd_vadd_set_local20, add_comm] using hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u)).ae
      hTile.2.2.2.2
    filter_upwards [hpull] with x hx
    simp only [Set.mem_univ, true_iff]
    obtain ⟨l, hl⟩ := hx.mp (by simp)
    refine ⟨⟨u + l.1, ⟨l.1, l.2, rfl⟩⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hl ⊢
    simpa [vadd_eq_add, add_assoc, add_comm] using hl



private theorem lineTiles_imag_bound_of_ball_local
    {B : Set ℝ} {L : Set ℝ} {R₀ : ℝ}
    (hR₀ : ∀ b ∈ B, |b| ≤ R₀) (hline : LineTiles B L) :
    ∀ u : ℝ, ∃ y ∈ u +ᵥ L, |y| ≤ 1 + |R₀| := by
  intro u
  have hae : ∀ᵐ x : ℝ ∂volume,
      ∃ l : L, ∃ b ∈ B, x = (l : ℝ) + b := by
    filter_upwards [hline.2.2.2.2] with x hx
    obtain ⟨l, hl⟩ := hx.mp (Set.mem_univ x)
    obtain ⟨b, hb, hxb⟩ := hl
    exact ⟨l, b, hb, hxb.symm⟩
  obtain ⟨x, hx, hxI⟩ :=
    (volume.dense_of_ae hae).exists_mem_open isOpen_Ioo
      (show (Set.Ioo (-u - 1 : ℝ) (-u + 1)).Nonempty from
        ⟨-u, by constructor <;> linarith⟩)
  obtain ⟨l, b, hb, hxb⟩ := hx
  refine ⟨u + l, ⟨l, l.property, rfl⟩, ?_⟩
  have hbabs : |b| ≤ R₀ := hR₀ b hb
  have hbabs' : |b| ≤ |R₀| := hbabs.trans (le_abs_self R₀)
  have huxabs : |u + x| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hxI.1, hxI.2]
  have hl_eq : (l : ℝ) = x - b := by linarith [hxb]
  rw [hl_eq]
  calc
    |u + (x - b)| ≤ |u + x| + |b| := by
      rw [show u + (x - b) = (u + x) - b by ring]
      exact abs_sub _ _
    _ ≤ 1 + |R₀| := by linarith


private theorem anchored_imag_choice_uniform_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} :
    ∃ R : ℝ, 0 < R ∧
      ∀ {T : Set Plane} (_hTile : TilesOn D.deformedRegion T Set.univ),
        ∀ B : AnchoredDeformedColumn (C := C) (phi := phi) (D := D) T,
          ∀ u : ℝ, ∃ y ∈ u +ᵥ Complex.im '' B.normalized, |y| ≤ R := by
  obtain ⟨F⟩ := fixedGenericVerticalSliceData_exists D
  let Bslice := F.slice
  have hBfinite : IsFiniteIntervalRegion Bslice := F.presentation.isFiniteIntervalRegion
  obtain ⟨R₀, hR₀⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp
      (IntervalPresentation.ofIsFiniteIntervalRegion hBfinite).isBounded
  let R : ℝ := 1 + |R₀|
  have hR : 0 < R := by
    dsimp [R]
    positivity
  refine ⟨R, hR, ?_⟩
  intro T hTile B
  have hnormline : LineTiles Bslice (Complex.im '' B.normalized) := by
    obtain ⟨c, hc⟩ := B.isColumn
    have hColumn : IsCenterColumn Axis.vertical D.deformedRegion B.plate.centres :=
      VerticalPlate.isCenterColumn_of_isVerticalColumn hTile B.plate B.isColumn
    let Y : Set ℝ := Complex.im '' B.plate.centres
    have hY : Y.Nonempty := ⟨B.anchor.im, ⟨B.anchor, B.anchor_mem, rfl⟩⟩
    have hshape : B.plate.centres =
        {z : Plane | z.re = c ∧ z.im ∈ Y} := by
      ext z
      constructor
      · intro hz
        exact ⟨hc hz, ⟨z, hz, rfl⟩⟩
      · rintro ⟨hzre, ⟨w, hw, hwim⟩⟩
        have hzw : z = w := by
          apply Complex.ext
          · exact hzre.trans (hc hw).symm
          · exact hwim.symm
        simpa [hzw] using hw
    have hColumn' : IsCenterColumn Axis.vertical D.deformedRegion
        {z : Plane | z.re = c ∧ z.im ∈ Y} := by
      simpa [hshape] using hColumn
    have hline : LineTiles Bslice Y := by
      simpa [Bslice, F.slice_eq] using F.completeColumn_lineTiles hY hColumn'
    rw [B.normalized_eq]
    have himage_eq : Complex.im '' (-B.anchor +ᵥ B.plate.centres) =
        (-B.anchor.im) +ᵥ Y := by
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨w.im, ⟨w, hw, rfl⟩, ?_⟩
        simp [vadd_eq_add]
      · rintro ⟨y₀, ⟨w, hw, rfl⟩, rfl⟩
        refine ⟨-B.anchor + w, ⟨w, hw, rfl⟩, ?_⟩
        simp [vadd_eq_add]
    rw [himage_eq]
    exact lineTiles_translate_local20 hline (-B.anchor.im)
  exact lineTiles_imag_bound_of_ball_local (fun b hb => by
    have hb' := hR₀ hb
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hb')
    hnormline

private theorem bounded_anchor_subsequence_local
    (z : ℕ → Plane) {R : ℝ} (_hR : 0 ≤ R)
    (hz : ∀ n, ‖z n‖ ≤ R) :
    ∃ z₀ : Plane, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (𝓝 z₀) := by
  have hzball : ∀ n, z n ∈ Metric.closedBall (0 : Plane) R := by
    intro n
    simpa [Metric.mem_closedBall, dist_zero_right] using hz n
  obtain ⟨z₀, _hz₀, φ, hφ, hlim⟩ :=
    (ProperSpace.isCompact_closedBall (0 : Plane) R).isSeqCompact
      hzball
  exact ⟨z₀, φ, hφ, hlim⟩

private theorem finite_range_constant_subsequence_local
    {α : Type} (f : ℕ → α) (hfinite : (Set.range f).Finite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = f (φ 0) := by
  classical
  let _ := hfinite.fintype
  let g : ℕ → Set.range f := fun n ↦ ⟨f n, ⟨n, rfl⟩⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  have hy' : ({n | g n = y} : Set ℕ).Infinite :=
    Set.infinite_coe_iff.mp hy
  let φ : ℕ → ℕ := Nat.nth (fun n ↦ g n = y)
  have hφ : StrictMono φ := Nat.nth_strictMono hy'
  have hmem (n : ℕ) : g (φ n) = y :=
    Nat.nth_mem n (fun hf ↦ (hy' hf).elim)
  refine ⟨φ, hφ, fun n ↦ ?_⟩
  exact congrArg Subtype.val ((hmem n).trans (hmem 0).symm)

private theorem bounded_constant_normalized_subsequence_local
    {alpha : Type} (z : ℕ → Plane) (N : ℕ → alpha) {R : ℝ}
    (_hR : 0 ≤ R) (hz : ∀ n, ‖z n‖ ≤ R)
    (hNfinite : (Set.range N).Finite) :
    ∃ z₀ : Plane, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (z ∘ φ) atTop (𝓝 z₀) ∧
      ∀ n, N (φ n) = N (φ 0) := by
  obtain ⟨z₀, ψ, hψ, hlim⟩ := bounded_anchor_subsequence_local z _hR hz
  have hNsub : Set.range (N ∘ ψ) ⊆ Set.range N := by
    rintro x ⟨n, rfl⟩
    exact ⟨ψ n, rfl⟩
  obtain ⟨χ, hχ, hN⟩ :=
    finite_range_constant_subsequence_local (N ∘ ψ) (hNfinite.subset hNsub)
  refine ⟨z₀, ψ ∘ χ, hψ.comp hχ, ?_, ?_⟩
  · simpa only [Function.comp_assoc] using hlim.comp hχ.tendsto_atTop
  · intro n
    exact hN n

private theorem anchored_normalized_vadd_plate_centres_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {T : Set Plane}
    (B : AnchoredDeformedColumn (C := C) (phi := phi) (D := D) T)
    (a : Plane) :
    a +ᵥ B.normalized = (a - B.anchor) +ᵥ B.plate.centres := by
  rw [B.normalized_eq]
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp [vadd_eq_add]
    ring
  · rintro ⟨u, hu, rfl⟩
    refine ⟨-B.anchor + u, ⟨u, hu, rfl⟩, ?_⟩
    simp [vadd_eq_add]
    ring


private theorem vadd_centerColumn_cross_local
    {K : Region} {U T : Set Plane}
    (hTileU : TilesOn K U Set.univ)
    (hTileT : TilesOn K T Set.univ)
    (B : VerticalPlate K U) (hBcolumn : IsVerticalColumn B)
    (v : Plane) (hsub : v +ᵥ B.centres ⊆ T) :
    IsCenterColumn Axis.vertical K (v +ᵥ B.centres) := by
  have hBcenter := VerticalPlate.isCenterColumn_of_isVerticalColumn hTileU B hBcolumn
  have hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (v +ᵥ B.centres)) := by
    apply (isPacking_iff_openCarrier_disjoint K (v +ᵥ B.centres)).mpr
    intro s hs t ht hst
    exact (isPacking_iff_openCarrier_disjoint K T).mp hTileT.2.1
      (hsub hs) (hsub ht) hst
  have hne : (v +ᵥ B.centres).Nonempty := by
    obtain ⟨z, hz⟩ := hBcenter.2.1
    exact ⟨v + z, ⟨z, hz, rfl⟩⟩
  obtain ⟨c, hc⟩ := hBcenter.2.2.1
  refine ⟨hpack, hne, ⟨v.re + c, ?_⟩, ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    simpa [Axis.transverseCoord, vadd_eq_add] using hc w hw
  · rw [regularSupport_vadd]
    intro a
    have hInv := hBcenter.2.2.2 a
    calc
      ((a : ℂ) * Complex.I) +ᵥ (v +ᵥ regularSupport K B.centres) =
          (((a : ℂ) * Complex.I) + v) +ᵥ regularSupport K B.centres :=
        vadd_vadd _ _ _
      _ = (v + (a : ℂ) * Complex.I) +ᵥ regularSupport K B.centres := by
        rw [add_comm]
      _ = v +ᵥ (((a : ℂ) * Complex.I) +ᵥ regularSupport K B.centres) := by
        rw [vadd_vadd]
      _ = v +ᵥ regularSupport K B.centres := congrArg (fun S : Set Plane ↦ v +ᵥ S) hInv

private theorem package_anchored_limit_column_cross_local
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi} {U T : Set Plane}
    (hTileU : TilesOn D.deformedRegion U Set.univ)
    (hTileT : TilesOn D.deformedRegion T Set.univ)
    (B : AnchoredDeformedColumn (C := C) (phi := phi) (D := D) U)
    (a : Plane) (hmap : a +ᵥ B.normalized ⊆ T) :
    ∃ Q : VerticalPlate D.deformedRegion T,
      a +ᵥ B.normalized = Q.centres ∧ IsVerticalColumn Q := by
  let v : Plane := a - B.anchor
  have hvset : v +ᵥ B.plate.centres = a +ᵥ B.normalized := by
    symm
    exact anchored_normalized_vadd_plate_centres_local B a
  have hmap' : v +ᵥ B.plate.centres ⊆ T := by
    rw [hvset]
    exact hmap
  have hCcolumn := vadd_centerColumn_cross_local hTileU hTileT B.plate B.isColumn v hmap'
  have hanchor : v + B.anchor ∈ v +ᵥ B.plate.centres :=
    ⟨B.anchor, B.anchor_mem, rfl⟩
  obtain ⟨Q, hQcolumn, _hQanchor, hQ⟩ :=
    Tiling.AxisParallel.Continuous.completeColumn_eq_verticalPlateThrough
      hTileT hCcolumn hmap' hanchor
  refine ⟨Q, ?_, hQcolumn⟩
  rw [hQ, hvset]

private theorem translated_anchor_exists_bounded_local
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    (P : TwoStageDeformationSupportTransport C phi D)
    {O : HorizontalColumnOrderData C H phi}
    (L : HorizontalColumnOrbitLimitData C H phi D P O)
    (hNontrivial :
      ¬ ∃ Q : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres) :
    ∃ R Ri : ℝ, 0 < R ∧ 0 < Ri ∧
      ∀ n : ℕ, ∃ B : AnchoredDeformedColumn
          (C := C) (phi := phi) (D := D)
        ((TilingSpace.translate (L.translations n) L.deformedSource).centres : Set Plane),
        IsVerticalColumn B.plate ∧ |B.anchor.re| ≤ R ∧ |B.anchor.im| ≤ Ri ∧
          ∃ B₀ : AnchoredDeformedColumn (C := C) (phi := phi) (D := D)
              (positiveSimilarity 1 (0 : Plane) '' (L.deformedSource.centres : Set Plane)),
            B.normalized = B₀.normalized := by
  obtain ⟨Q, hQ, A, hAne, hAcol, R0, hR0, B0, hB0, hB0col⟩ :=
    translated_transport_anchored_column_exists H P hNontrivial hInfinite 0
  have hbaseeq :
      positiveSimilarity 1 (0 : Plane) '' deformedCenterCarrier P.fullCenters =
        (L.deformedSource.centres : Set Plane) := by
    rw [L.deformedSource_centres]
    ext z
    simp [positiveSimilarity]
  let Bbase : AnchoredDeformedColumn (C := C) (phi := phi) (D := D)
      (L.deformedSource.centres : Set Plane) := hbaseeq ▸ B0
  have hTileBaseU : TilesOn D.deformedRegion
      (positiveSimilarity 1 (0 : Plane) '' (L.deformedSource.centres : Set Plane))
      Set.univ := by
    have hcarrier : D.deformedRegion.openCarrier =
        positiveSimilarity 1 (0 : Plane) '' D.deformedRegion.openCarrier := by
      ext z
      simp [positiveSimilarity]
    have h := (tilesOn_positiveSimilarity_iff
      (K := D.deformedRegion) (R := D.deformedRegion)
      (s := 1) (r := 0) (c := 0) one_pos hcarrier).mpr
      L.deformedSource.tilesOn
    have himageuniv : positiveSimilarity 1 (0 : Plane) ''
        (Set.univ : Set Plane) = Set.univ := by
      ext z
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨z, trivial, by simp [positiveSimilarity]⟩
    simpa [positiveSimilarity, himageuniv] using h
  obtain ⟨Ri, hRi, himag⟩ :=
    anchored_imag_choice_uniform_local (C := C) (phi := phi) (D := D)
  obtain ⟨beta, R, hbeta, hR, haxes⟩ :=
    translated_column_axes_bound_local L.deformedSource Bbase
  refine ⟨R, Ri, hR, hRi, ?_⟩
  intro n
  let vn : Plane := (L.translations n : Plane)
  obtain ⟨a, ha, hdist⟩ := haxes (-vn.re)
  obtain ⟨S, haS⟩ : ∃ S :
      {P : VerticalPlate D.deformedRegion
          (L.deformedSource.centres : Set Plane) // IsVerticalColumn P},
      a ∈ S.1.centres := by
    rw [verticalColumnCentres_eq] at ha
    exact Set.mem_iUnion.mp ha
  obtain ⟨BbaseS, hBbaseplate, hBbaseanchor, hBbasenorm⟩ :=
    translatedVerticalPlate_anchored_local (0 : Plane) S.1 S.2 a haS
  obtain ⟨y, hy, hybound⟩ := himag hTileBaseU BbaseS (vn.im + a.im)
  rcases hy with ⟨q, ⟨w, hw, rfl⟩, rfl⟩
  rw [BbaseS.normalized_eq] at hw
  rcases hw with ⟨zraw, hzraw, hzr⟩
  have hzimage : zraw ∈ (translatedVerticalPlate_local (0 : Plane) S.1).centres := by
    rw [← hBbaseplate]
    exact hzraw
  rw [translatedVerticalPlate_local_centres] at hzimage
  obtain ⟨z0, hz0, hzmap⟩ := hzimage
  have hzbound : |vn.im + z0.im| ≤ Ri := by
    rw [← hzr] at hybound
    have hzraw_eq : zraw = z0 := by
      simpa [positiveSimilarity] using hzmap.symm
    rw [hzraw_eq, hBbaseanchor] at hybound
    convert hybound using 1
    simp [positiveSimilarity, vadd_eq_add, add_comm, add_left_comm, add_assoc]
    ring_nf
  obtain ⟨B, hBplate, hBanchor, hBnorm⟩ :=
    translatedVerticalPlate_anchored_local vn S.1 S.2 z0 hz0
  obtain ⟨B₀, hB₀plate, hB₀anchor, hB₀norm⟩ :=
    translatedVerticalPlate_anchored_local (0 : Plane) S.1 S.2 z0 hz0
  have heq := translated_orbit_centres_eq_positiveSimilarity_local L n
  have hcarrier_n :
      positiveSimilarity 1 vn '' (L.deformedSource.centres : Set Plane) =
        positiveSimilarity 1 (L.translations n : Plane) ''
          deformedCenterCarrier P.fullCenters := by
    rw [← hbaseeq]
    rw [image_translation_eq_vadd_local, image_translation_eq_vadd_local]
    simp only [image_translation_eq_vadd_local]
    simp [vn]
  have heq' :
      positiveSimilarity 1 vn '' (L.deformedSource.centres : Set Plane) =
        ((TilingSpace.translate (L.translations n) L.deformedSource).centres : Set Plane) :=
    hcarrier_n.trans heq.symm
  rw [← heq']
  refine ⟨B, B.isColumn, ?_, ?_, ?_⟩
  · rw [hBanchor]
    have hreal : (positiveSimilarity 1 vn z0).re = vn.re + z0.re := by
      simp [positiveSimilarity]
      ring
    rw [hreal]
    obtain ⟨c, hc⟩ := S.2
    have hzre := hc hz0
    have hare := hc haS
    change z0.re = c at hzre
    change a.re = c at hare
    have hdist' : |vn.re + a.re| ≤ R := by
      simpa [sub_eq_add_neg, add_comm] using hdist
    simpa [hzre, hare] using hdist'
  · rw [hBanchor]
    have him : (positiveSimilarity 1 vn z0).im = vn.im + z0.im := by
      simp [positiveSimilarity]
      ring
    rw [him]
    simpa [add_comm] using hzbound
  · exact ⟨B₀, hBnorm.trans hB₀norm.symm⟩

theorem orbitLimit_hasVerticalColumn
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (hNontrivial :
      ¬ ∃ Q : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    {D : CoordinateDeformation C phi}
    {P : TwoStageDeformationSupportTransport C phi D}
    {O : HorizontalColumnOrderData C H phi}
    (L : HorizontalColumnOrbitLimitData C H phi D P O) :
    ∃ Q : VerticalPlate D.deformedRegion (L.limit.centres : Set Plane),
      IsVerticalColumn Q := by
  obtain ⟨R, Ri, hR, hRi, hB⟩ :=
    translated_anchor_exists_bounded_local H P L hNontrivial hInfinite
  let Bseq : ∀ n : ℕ, AnchoredDeformedColumn (C := C) (phi := phi)
      (D := D) ((TilingSpace.translate (L.translations n) L.deformedSource).centres : Set Plane) :=
    fun n => Classical.choose (hB n)
  have hBseq (n : ℕ) := Classical.choose_spec (hB n)
  let anchor : ℕ → Plane := fun n => (Bseq n).anchor
  let Nseq : ℕ → Set Plane := fun n => (Bseq n).normalized
  have hnorm : ∀ n, ‖anchor n‖ ≤ R + Ri := by
    intro n
    calc
      ‖anchor n‖ ≤ |(anchor n).re| + |(anchor n).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ R + Ri := add_le_add (hBseq n).2.1 (hBseq n).2.2.1
  have hTileBase : TilesOn D.deformedRegion
      (positiveSimilarity 1 (0 : Plane) '' (L.deformedSource.centres : Set Plane))
      Set.univ := by
    have hcarrier : D.deformedRegion.openCarrier =
        positiveSimilarity 1 (0 : Plane) '' D.deformedRegion.openCarrier := by
      ext z
      simp [positiveSimilarity]
    have h := (tilesOn_positiveSimilarity_iff
      (K := D.deformedRegion) (R := D.deformedRegion)
      (s := 1) (r := 0) (c := 0) one_pos hcarrier).mpr
      L.deformedSource.tilesOn
    have himageuniv : positiveSimilarity 1 (0 : Plane) ''
        (Set.univ : Set Plane) = Set.univ := by
      ext z
      constructor
      · intro _
        trivial
      · intro _
        exact ⟨z, trivial, by simp [positiveSimilarity]⟩
    simpa [positiveSimilarity, himageuniv] using h
  have hFamilyFinite := normalizedDeformedColumns_finite hTileBase
  have hNfinite : (Set.range Nseq).Finite := by
    apply hFamilyFinite.subset
    rintro N ⟨n, rfl⟩
    obtain ⟨B₀, hB₀⟩ := (hBseq n).2.2.2
    exact ⟨B₀, hB₀⟩
  let Ts : ℕ → TilingSpace D.deformedRegion Set.univ :=
    fun n => TilingSpace.translate (L.translations n) L.deformedSource
  have hsubset : ∀ n, anchor n +ᵥ Nseq n ⊆ (Ts n).centres := by
    intro n z hz
    rcases hz with ⟨w, hw, rfl⟩
    change w ∈ (Bseq n).normalized at hw
    rw [(Bseq n).normalized_eq] at hw
    rcases hw with ⟨u, hu, rfl⟩
    rcases hu with ⟨t, ht, rfl⟩
    rcases t.property with ⟨s, hs, hst⟩
    refine ⟨s, hs, ?_⟩
    simp [anchor, vadd_eq_add, hst]
  have hconv : LocallyFellConverges
      (TilingSpace.centresSequence Ts) (L.limit.centres : Set Plane) := by
    change LocallyFellConverges
      (TilingSpace.centresSequence
        (TilingSpace.translateSequence L.translations L.deformedSource))
      (L.limit.centres : Set Plane)
    exact L.converges
  obtain ⟨limitAnchor, ψ, hψ, hlim, hNconst⟩ :=
    bounded_constant_normalized_subsequence_local anchor Nseq
      (by positivity) hnorm hNfinite
  have hconvSub := locallyFellConverges_comp_strictMono_adapter ψ hψ hconv
  have hsubSub : ∀ n, anchor (ψ n) +ᵥ Nseq (ψ 0) ⊆
      (Ts (ψ n)).centres := by
    intro n
    rw [← hNconst n]
    exact hsubset (ψ n)
  have hlimitSubset := translatedNormalized_subset_ambientLimit_adapter
    (fun n => Ts (ψ n)) L.limit (Nseq (ψ 0)) (fun n => anchor (ψ n))
    limitAnchor hsubSub hlim hconvSub
  let Bstar := Bseq (ψ 0)
  have hmap : limitAnchor +ᵥ Bstar.normalized ⊆ (L.limit.centres : Set Plane) := by
    simpa [Bstar, Nseq] using hlimitSubset
  obtain ⟨Q, _hQ, hQcolumn⟩ := package_anchored_limit_column_cross_local
    (Ts (ψ 0)).tilesOn L.limit.tilesOn Bstar limitAnchor hmap
  exact ⟨Q, hQcolumn⟩

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open MeasureTheory Set Filter
open Tiling
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

/-- Construct a single deformed orbit limit carrying both column directions. -/
theorem exists_orbitLimit_withSimultaneousColumns
    {C : ApproximationContext} {source : TilingSpace C.region Set.univ}
    (H : PersistentHorizontalFibreData C source)
    (hNontrivial : ¬ ∃ Q : VerticalPlate C.region C.centres,
      ¬ IsVerticalColumn Q ∧ Q.centres = C.centres)
    (hInfinite : ¬ HasFiniteHorizontalComplexity C.centres)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C phi)
    (P : TwoStageDeformationSupportTransport C phi D) :
    ∃ O : HorizontalColumnOrderData C H phi,
      Nonempty (SimultaneousColumnsLimitData C H phi D P O) := by
  obtain ⟨O⟩ := horizontalColumn_globalOrder H phi D
  obtain ⟨L⟩ := orbitLimit_hasHorizontalColumn H P O
  obtain ⟨Q, hQ⟩ := orbitLimit_hasVerticalColumn H hNontrivial hInfinite L
  refine ⟨O, ⟨{
    horizontal := L
    verticalColumn := Q
    verticalColumn_isColumn := hQ
    verticalColumn_support := ?_ }⟩⟩
  exact (VerticalPlate.support_isVerticalSlab L.limit.tilesOn Q).2

end Tiling.AxisParallel.Structure
