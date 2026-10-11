import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Terminal.PeriodicCarrierContinuousSlabs

/-!
# Terminal region decomposition

This module defines the orientation-aware terminal certificates and establishes the generic
finite-local-complexity and regular-support lemmas used to assemble their pieces.
-/

open Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

/-- Minimality of a selected plate in the vertical direction, and also horizontally when its
base is the full line. -/
structure IsPropagationIrreducible
    (K : Tiling.AxisParallel.Region) (T S : Set Tiling.Plane)
    (base : Set ℝ) : Prop where
  vertical : ∀ Q : Set Tiling.Plane,
    Q.Nonempty → Q ⊆ S →
    (∃ Y : Set ℝ, Y = interior (closure Y) ∧
      Tiling.AxisParallel.regularSupport K Q = Complex.re ⁻¹' Y) →
    Q = S
  horizontal_of_full : base = Set.univ → ∀ Q : Set Tiling.Plane,
    Q.Nonempty → Q ⊆ S →
    (∃ Y : Set ℝ, Y = interior (closure Y) ∧
      Tiling.AxisParallel.regularSupport K Q = Complex.im ⁻¹' Y) →
    Q = S

/-- One noncolumn terminal plate, retaining both its original and selected orientation. -/
structure TerminalRegion
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) where
  orientation : Tiling.AxisParallel.Axis
  centres : Set Tiling.Plane
  centres_nonempty : centres.Nonempty
  centres_subset : centres ⊆ T
  selectedRegion : Tiling.AxisParallel.Region
  selectedRegion_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedRegion = K
  selectedRegion_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedRegion = K.coordinateSwap
  selectedAmbientCentres : Set Tiling.Plane
  selectedAmbientCentres_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedAmbientCentres = T
  selectedAmbientCentres_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedAmbientCentres = Tiling.AxisParallel.coordinateSwap '' T
  selectedCentres : Set Tiling.Plane
  selectedCentres_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedCentres = centres
  selectedCentres_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedCentres = Tiling.AxisParallel.coordinateSwap '' centres
  plate : Tiling.AxisParallel.Continuous.VerticalPlate
    selectedRegion selectedAmbientCentres
  selectedCentres_eq_plate : selectedCentres = plate.centres
  plate_noncolumn : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn plate
  base : Set ℝ
  base_open : IsOpen base
  base_regular : interior (closure base) = base
  base_nonnull : MeasureTheory.volume base ≠ 0
  support_eq : Tiling.AxisParallel.regularSupport selectedRegion
    selectedCentres = Complex.re ⁻¹' base
  tiles : Tiling.AxisParallel.TilesOn selectedRegion selectedCentres
    (Complex.re ⁻¹' base)
  flc : Tiling.AxisParallel.HasFLC centres
  selected_flc : Tiling.AxisParallel.HasFLC selectedCentres
  supportPeriod : ℝ
  supportPeriod_pos : 0 < supportPeriod
  support_periodic : supportPeriod +ᵥ base = base
  propagationIrreducible : IsPropagationIrreducible
    selectedRegion selectedAmbientCentres selectedCentres base

/-- A finite terminal-region partition and the remaining aggregate column family. -/
structure TerminalRegionDecomposition
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) where
  orientation : Tiling.AxisParallel.Axis
  selectedRegion : Tiling.AxisParallel.Region
  selectedRegion_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedRegion = K
  selectedRegion_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedRegion = K.coordinateSwap
  selectedCentres : Set Tiling.Plane
  selectedCentres_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedCentres = T
  selectedCentres_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedCentres = Tiling.AxisParallel.coordinateSwap '' T
  selectedCarrier : PeriodicVerticalCarrier
  selectedCarrier_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical → selectedCarrier = X
  selectedCarrier_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      X.base = Set.univ ∧ selectedCarrier.base = Set.univ ∧
        selectedCarrier.carrier = Set.univ
  selected_tiles : Tiling.AxisParallel.TilesOn
    selectedRegion selectedCentres selectedCarrier.carrier
  selected_flc : Tiling.AxisParallel.HasFLC selectedCentres
  slabs : PeriodicCarrierSlabDecomposition
    selectedRegion selectedCentres selectedCarrier
  region : Fin slabs.numberOfNonColumnPlates → TerminalRegion K T
  region_orientation : ∀ i, (region i).orientation = orientation
  region_selectedRegion : ∀ i, (region i).selectedRegion = selectedRegion
  region_selectedAmbientCentres : ∀ i,
    (region i).selectedAmbientCentres = selectedCentres
  region_selectedCentres : ∀ i,
    (region i).selectedCentres = (slabs.nonColumnPlate i).centres
  region_period : ∀ i,
    (region i).supportPeriod = slabs.commonSupportPeriod
  columnCentres : Set Tiling.Plane
  selectedColumnCentres : Set Tiling.Plane
  selectedColumnCentres_vertical :
    orientation = Tiling.AxisParallel.Axis.vertical →
      selectedColumnCentres = columnCentres
  selectedColumnCentres_horizontal :
    orientation = Tiling.AxisParallel.Axis.horizontal →
      selectedColumnCentres = Tiling.AxisParallel.coordinateSwap '' columnCentres
  selectedColumnCentres_eq_slabs :
    selectedColumnCentres = slabs.columnCentres
  column_flc : Tiling.AxisParallel.HasFLC columnCentres
  selectedColumn_flc : Tiling.AxisParallel.HasFLC selectedColumnCentres
  parts_pairwise :
    Set.PairwiseDisjoint Set.univ (fun i ↦ (region i).centres)
  column_region_disjoint : ∀ i, Disjoint columnCentres (region i).centres
  parts_union : columnCentres ∪ (⋃ i, (region i).centres) = T
  fullBase_only_bothTrivial : ∀ i, (region i).base = Set.univ →
    slabs.numberOfNonColumnPlates = 1 ∧
      columnCentres = ∅ ∧ (region i).centres = T

/-- Finite local complexity passes to arbitrary subsets. -/
theorem _root_.Tiling.AxisParallel.HasFLC.subset
    {S T : Set Tiling.Plane}
    (hT : Tiling.AxisParallel.HasFLC T) (hST : S ⊆ T) :
    Tiling.AxisParallel.HasFLC S := by
  refine ⟨?_, ?_⟩
  · intro Q hQ
    apply (hT.1 Q hQ).subset
    rintro x ⟨hxS, hxQ⟩
    exact ⟨hST hxS, hxQ⟩
  · intro R hR
    apply (hT.2 R hR).subset
    rintro x ⟨hxDiff, hxBall⟩
    obtain ⟨s, hs, t, ht, rfl⟩ := hxDiff
    exact ⟨⟨s, hST hs, t, hST ht, rfl⟩, hxBall⟩

private theorem tilesOn_regularSupport_of_subset
    {K : Tiling.AxisParallel.Region} {S T E : Set Tiling.Plane}
    (hST : S ⊆ T) (hTile : Tiling.AxisParallel.TilesOn K T E) :
    Tiling.AxisParallel.TilesOn K S
      (Tiling.AxisParallel.regularSupport K S) := by
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    intro s hs t ht hst
    exact hTile.2.1 (hST hs) (hST ht) hst
  refine ⟨hTile.1.mono hST, hpacking, ?_⟩
  filter_upwards [Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking] with x hx
  exact (Iff.of_eq hx.symm).trans (by
    change x ∈ (⋃ s : S, (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
      ∃ s : S, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier
    exact Set.mem_iUnion)

/-- Disjoint centre subfamilies remain disjoint after regularization and tile their own supports. -/
theorem regularSupport_disjointSubfamilies
    {I : Type*} [Countable I]
    {K : Tiling.AxisParallel.Region} {T E : Set Tiling.Plane}
    (S : I → Set Tiling.Plane)
    (hparts : Set.PairwiseDisjoint Set.univ S)
    (hsub : ∀ i, S i ⊆ T)
    (hTile : Tiling.AxisParallel.TilesOn K T E) :
    Set.PairwiseDisjoint Set.univ
        (fun i ↦ Tiling.AxisParallel.regularSupport K (S i)) ∧
      (∀ i, Tiling.AxisParallel.TilesOn K (S i)
        (Tiling.AxisParallel.regularSupport K (S i))) ∧
      Tiling.AxisParallel.regularSupport K (⋃ i, S i) =
        interior (closure
          (⋃ i, Tiling.AxisParallel.regularSupport K (S i))) := by
  have hsubUnion : (⋃ i, S i) ⊆ T := by
    exact Set.iUnion_subset hsub
  have hUnionTile := tilesOn_regularSupport_of_subset hsubUnion hTile
  have hdisjoint :=
    (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
      S hparts rfl hUnionTile).1
  exact ⟨hdisjoint, fun i ↦ tilesOn_regularSupport_of_subset (hsub i) hTile,
    regularSupport_iUnion S⟩

/-- The arbitrary-union regular-support identity specialized to a finite family. -/
theorem finiteAggregateSupport
    {n : ℕ} {K : Tiling.AxisParallel.Region}
    (S : Fin n → Set Tiling.Plane) :
    Tiling.AxisParallel.regularSupport K (⋃ i, S i) =
      interior (closure
        (⋃ i, Tiling.AxisParallel.regularSupport K (S i))) :=
  regularSupport_iUnion S

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

private noncomputable def coordinateSwapIsometry_t12 :
    Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := Tiling.AxisParallel.coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem hasFLC_coordinateSwap_to_original_t12
    (S : Set Tiling.Plane) :
    Tiling.AxisParallel.HasFLC
        (Tiling.AxisParallel.coordinateSwap '' S) →
      Tiling.AxisParallel.HasFLC S := by
  intro h
  constructor
  · intro Q hQ
    have hQ' : Bornology.IsBounded
        (Tiling.AxisParallel.coordinateSwap '' Q) :=
      coordinateSwapIsometry_t12.lipschitz.isBounded_image hQ
    have hfinite := h.1 (Tiling.AxisParallel.coordinateSwap '' Q) hQ'
    refine Set.Finite.of_finite_image (s := S ∩ Q)
      (f := Tiling.AxisParallel.coordinateSwap) ?_
      Tiling.AxisParallel.coordinateSwap.injective.injOn
    rw [Set.image_inter Tiling.AxisParallel.coordinateSwap.injective]
    exact hfinite
  · intro R hR
    let A : Set Tiling.Plane :=
      (S - S) ∩ Metric.closedBall 0 R
    refine Set.Finite.of_finite_image (s := A)
      (f := Tiling.AxisParallel.coordinateSwap) ?_
      Tiling.AxisParallel.coordinateSwap.injective.injOn
    apply (h.2 R hR).subset
    rintro d ⟨d₀, ⟨hd, hdR⟩, rfl⟩
    rcases hd with ⟨b, hb, a, ha, rfl⟩
    refine ⟨⟨Tiling.AxisParallel.coordinateSwap b,
        ⟨b, hb, rfl⟩,
      Tiling.AxisParallel.coordinateSwap a, ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · simp only [map_sub]
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hnorm : ‖Tiling.AxisParallel.coordinateSwap (b - a)‖ = ‖b - a‖ := by
        change ‖coordinateSwapIsometry_t12 (b - a)‖ = ‖b - a‖
        exact coordinateSwapIsometry_t12.norm_map _
      rw [hnorm]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hdR

private theorem hasFLC_coordinateSwap :
    ∀ {T : Set Tiling.Plane},
      Tiling.AxisParallel.HasFLC T →
        Tiling.AxisParallel.HasFLC
          (Tiling.AxisParallel.coordinateSwap '' T) := by
  intro T h
  have h' := hasFLC_coordinateSwap_to_original_t12
      (Tiling.AxisParallel.coordinateSwap '' T)
      (by
        simpa [Set.image_image,
          Tiling.AxisParallel.coordinateSwap_apply_apply] using h)
  simpa [Set.image_image,
    Tiling.AxisParallel.coordinateSwap_apply_apply] using h'

private theorem properCarrier_nonColumnBase_ne_univ
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (D : PeriodicCarrierSlabDecomposition K T X) :
    X.base ≠ Set.univ → ∀ i, (D.nonColumnPlate i).base ≠ Set.univ := by
  intro hX i hbase
  apply hX
  apply Set.eq_univ_of_forall
  intro x
  let P := D.nonColumnPlate i
  have hcarrierOpen : IsOpen X.carrier :=
    X.base_open.preimage Complex.continuous_re
  have hcarrierRegular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      X.base_regular]
  have hsourceSupport :
      Tiling.AxisParallel.regularSupport K T = X.carrier :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      hcarrierOpen hcarrierRegular D.source_tiles
  have hopenUnion : Tiling.AxisParallel.openUnion K T ⊆ X.carrier := by
    rw [← hsourceSupport]
    have hopen : IsOpen (Tiling.AxisParallel.openUnion K T) := by
      apply isOpen_iUnion
      intro t
      exact isOpen_interior.vadd t.1
    exact hopen.subset_interior_closure
  have hPsubset : P.centres ⊆ T := by
    rintro p ⟨q, _hq, rfl⟩
    exact q.2
  have hPopen : Tiling.AxisParallel.openUnion K P.centres ⊆
      Tiling.AxisParallel.openUnion K T := by
    intro z hz
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier, Set.mem_iUnion] at hz ⊢
    obtain ⟨p, hp⟩ := hz
    refine ⟨⟨p.1, hPsubset p.2⟩, ?_⟩
    exact hp
  have hPsupport : P.support ⊆ X.carrier := by
    change Tiling.AxisParallel.regularSupport K P.centres ⊆ X.carrier
    rw [← hcarrierRegular]
    exact interior_mono (closure_mono (hPopen.trans hopenUnion))
  have hxbase : x ∈ P.base := by
    rw [hbase]
    trivial
  change x ∈ Complex.re '' P.support at hxbase
  rcases hxbase with ⟨z, hz, rfl⟩
  exact hPsupport hz

theorem nontrivialPlanePlate_hasProperBase
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (hTile : Tiling.AxisParallel.TilesOn K T Set.univ)
    (hNoFull : ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T)
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    (hPnotcol : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P) :
    P.base ≠ Set.univ := by
  intro hbase
  obtain ⟨_hbaseRegular, hsupport⟩ :=
    Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hPsupport : P.support = Set.univ := by
    rw [hsupport, hbase]
    exact Set.preimage_univ
  have hcentres : P.centres = T :=
    Tiling.AxisParallel.Continuous.plate_centres_eq_of_support_eq_univ hTile P hPsupport
  exact hNoFull ⟨P, hPnotcol, hcentres⟩

private theorem properPlate_propagationIrreducible
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    (hminimal :
      Tiling.AxisParallel.Continuous.IsMinimalVerticalSlabSubfamily
        K T P.centres)
    (_hPnotcol : ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P)
    (hproper : P.base ≠ Set.univ) :
    IsPropagationIrreducible K T P.centres P.base := by
  refine ⟨?_, ?_⟩
  · intro Q hQnonempty hQsub hQslab
    exact hminimal.2.2.2 Q hQnonempty hQsub hQslab
  · intro hfull _Q _hQnonempty _hQsub _hQslab
    exact (hproper hfull).elim

private theorem plate_base_nonempty_local
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T) :
    P.base.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  rw [P.base_eq]
  refine ⟨(t.1 + u).re, ⟨t.1 + u, ?_, rfl⟩⟩
  rw [Tiling.AxisParallel.Continuous.VerticalPlate.support_eq_regularSupport]
  unfold Tiling.AxisParallel.regularSupport
  have hopen : IsOpen (Tiling.AxisParallel.openUnion K P.centres) := by
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1
  apply hopen.subset_interior_closure
  rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion,
    ← Region.openCarrier, Set.mem_iUnion]
  refine ⟨⟨t.1, ⟨t, ht, rfl⟩⟩, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hu' : u ∈ K.openCarrier := by
    rw [← K.openCarrier_regularOpen.2,
      show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
    exact hu
  simpa only [vadd_eq_add, neg_add_cancel_left] using hu'

private theorem plate_base_periodic_local
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (P : Tiling.AxisParallel.Continuous.VerticalPlate K T)
    {beta : ℝ}
    (hsupport : P.support = Complex.re ⁻¹' P.base)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℂ))) :
    beta +ᵥ P.base = P.base := by
  ext x
  have hperiod' : Tiling.RationalPolygonal.SetPeriodicBy
      (Complex.re ⁻¹' P.base) ((beta : ℂ)) := by
    rw [← hsupport]
    exact hperiod
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm,
    add_left_comm, add_assoc, Tiling.RationalPolygonal.SetPeriodicBy,
    Complex.add_re] using (hperiod' ((x - beta : ℝ) : ℂ)).symm

private theorem columnCentres_subset_local
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane} :
    Tiling.AxisParallel.Continuous.verticalColumnCentres K T ⊆ T := by
  intro z hz
  change z ∈ ⋃ P : {P : Tiling.AxisParallel.Continuous.VerticalPlate K T //
    Tiling.AxisParallel.Continuous.IsVerticalColumn P}, P.1.centres at hz
  simp only [Set.mem_iUnion] at hz
  obtain ⟨P, t, ht, rfl⟩ := hz
  exact t.2

private def verticalTerminalRegion
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K T X)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ)
    (i : Fin D.numberOfNonColumnPlates) : TerminalRegion K T := by
  let P := D.nonColumnPlate i
  have hslab := (relativePlateGraph_minimality X D.source_tiles).1
  have hminimal := (relativePlateGraph_minimality X D.source_tiles).2.1
  have hPslab := hslab P
  have hPminimal := hminimal P
  have hsub : P.centres ⊆ T := hPminimal.2.1
  have htile := tilesOn_regularSupport_of_subset hsub D.source_tiles
  have hbaseOpen : IsOpen P.base := by
    rw [hPslab.1]
    exact isOpen_interior
  have hbaseNonempty : P.base.Nonempty := plate_base_nonempty_local P
  have hbaseNeZero : MeasureTheory.volume P.base ≠ 0 :=
    hbaseOpen.measure_ne_zero MeasureTheory.volume hbaseNonempty
  have hprop := properPlate_propagationIrreducible P hPminimal
    (D.nonColumnPlate_noncolumn i) (hproper i)
  refine {
    orientation := Axis.vertical
    centres := P.centres
    centres_nonempty := hPminimal.1
    centres_subset := hsub
    selectedRegion := K
    selectedRegion_vertical := by intro; rfl
    selectedRegion_horizontal := by intro h; cases h
    selectedAmbientCentres := T
    selectedAmbientCentres_vertical := by intro; rfl
    selectedAmbientCentres_horizontal := by intro h; cases h
    selectedCentres := P.centres
    selectedCentres_vertical := by intro; rfl
    selectedCentres_horizontal := by intro h; cases h
    plate := P
    selectedCentres_eq_plate := rfl
    plate_noncolumn := D.nonColumnPlate_noncolumn i
    base := P.base
    base_open := hbaseOpen
    base_regular := hPslab.1.symm
    base_nonnull := hbaseNeZero
    support_eq := hPslab.2
    tiles := by
      change Tiling.AxisParallel.TilesOn K P.centres P.support at htile
      rw [hPslab.2] at htile
      simpa only [P] using htile
    flc := hFLC.subset hsub
    selected_flc := hFLC.subset hsub
    supportPeriod := D.commonSupportPeriod
    supportPeriod_pos := D.commonSupportPeriod_pos
    support_periodic := plate_base_periodic_local P hPslab.2
      (D.nonColumnSupport_periodic i)
    propagationIrreducible := hprop }

private theorem verticalRegion_fields
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K T X)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ)
    (i : Fin D.numberOfNonColumnPlates) :
    (verticalTerminalRegion hFLC D hproper i).orientation = Axis.vertical ∧
    (verticalTerminalRegion hFLC D hproper i).selectedRegion = K ∧
    (verticalTerminalRegion hFLC D hproper i).selectedAmbientCentres = T ∧
    (verticalTerminalRegion hFLC D hproper i).selectedCentres =
      (D.nonColumnPlate i).centres ∧
    (verticalTerminalRegion hFLC D hproper i).supportPeriod = D.commonSupportPeriod := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private theorem verticalColumn_region_disjoint
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K T X)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ) :
    ∀ i, Disjoint D.columnCentres
      (verticalTerminalRegion hFLC D hproper i).centres := by
  intro i
  change Disjoint D.columnCentres (D.nonColumnPlate i).centres
  exact D.column_nonColumn_disjoint i

private theorem verticalSlabs_to_terminalDecomposition
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K T X)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ) :
    ∃ R : TerminalRegionDecomposition K T X,
      R.orientation = Axis.vertical ∧
      R.slabs.numberOfNonColumnPlates = D.numberOfNonColumnPlates ∧
      R.columnCentres = D.columnCentres := by
  let region : Fin D.numberOfNonColumnPlates → TerminalRegion K T :=
    fun i ↦ verticalTerminalRegion hFLC D hproper i
  let R : TerminalRegionDecomposition K T X := {
    orientation := Axis.vertical
    selectedRegion := K
    selectedRegion_vertical := by intro; rfl
    selectedRegion_horizontal := by intro h; cases h
    selectedCentres := T
    selectedCentres_vertical := by intro; rfl
    selectedCentres_horizontal := by intro h; cases h
    selectedCarrier := X
    selectedCarrier_vertical := by intro; rfl
    selectedCarrier_horizontal := by intro h; cases h
    selected_tiles := D.source_tiles
    selected_flc := hFLC
    slabs := D
    region := region
    region_orientation := by
      intro i
      exact (verticalRegion_fields hFLC D hproper i).1
    region_selectedRegion := by
      intro i
      exact (verticalRegion_fields hFLC D hproper i).2.1
    region_selectedAmbientCentres := by
      intro i
      exact (verticalRegion_fields hFLC D hproper i).2.2.1
    region_selectedCentres := by
      intro i
      exact (verticalRegion_fields hFLC D hproper i).2.2.2.1
    region_period := by
      intro i
      exact (verticalRegion_fields hFLC D hproper i).2.2.2.2
    columnCentres := D.columnCentres
    selectedColumnCentres := D.columnCentres
    selectedColumnCentres_vertical := by intro; rfl
    selectedColumnCentres_horizontal := by intro h; cases h
    selectedColumnCentres_eq_slabs := rfl
    column_flc := hFLC.subset (by
      rw [D.columnCentres_eq]
      exact columnCentres_subset_local)
    selectedColumn_flc := hFLC.subset (by
      rw [D.columnCentres_eq]
      exact columnCentres_subset_local)
    parts_pairwise := by
      intro i _ j _ hij
      change Disjoint (region i).centres (region j).centres
      change Disjoint (D.nonColumnPlate i).centres (D.nonColumnPlate j).centres
      exact D.nonColumnCentres_pairwise (by simp) (by simp) hij
    column_region_disjoint := by
      intro i
      exact verticalColumn_region_disjoint hFLC D hproper i
    parts_union := by
      have hEq : (⋃ i, (region i).centres) =
          ⋃ i, (D.nonColumnPlate i).centres := by
        apply Set.iUnion_congr
        intro i
        rfl
      rw [hEq]
      exact D.centres_partition
    fullBase_only_bothTrivial := by
      intro i hi
      change (D.nonColumnPlate i).base = Set.univ at hi
      exact (hproper i hi).elim }
  refine ⟨R, ?_⟩
  exact ⟨rfl, rfl, rfl⟩

private theorem swap_subset_original_local
    {T S : Set Tiling.Plane}
    (hS : S ⊆ Tiling.AxisParallel.coordinateSwap '' T) :
    Tiling.AxisParallel.coordinateSwap '' S ⊆ T := by
  rintro z ⟨y, hy, rfl⟩
  obtain ⟨t, ht, rfl⟩ := hS hy
  simpa only [Tiling.AxisParallel.coordinateSwap_apply_apply] using ht

private theorem swap_disjoint_image_local
    {A B : Set Tiling.Plane} (h : Disjoint A B) :
    Disjoint (Tiling.AxisParallel.coordinateSwap '' A)
      (Tiling.AxisParallel.coordinateSwap '' B) := by
  rw [Set.disjoint_left]
  rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
  have hab : a = b := Tiling.AxisParallel.coordinateSwap.injective
    (haz.trans hbz.symm)
  exact Set.disjoint_left.mp h ha (hab ▸ hb)

private theorem swap_iUnion_image_local
    {ι : Type*} (A : ι → Set Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap '' (⋃ i, A i) =
      ⋃ i, Tiling.AxisParallel.coordinateSwap '' A i := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨i, hai⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨i, ⟨a, hai, rfl⟩⟩
  · intro hz
    obtain ⟨i, a, hai, hza⟩ := Set.mem_iUnion.mp hz
    exact ⟨a, Set.mem_iUnion.mpr ⟨i, hai⟩, hza⟩

private def horizontalTerminalRegion
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {Xswap : PeriodicVerticalCarrier}
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' T) Xswap)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ)
    (i : Fin D.numberOfNonColumnPlates) : TerminalRegion K T := by
  let P := D.nonColumnPlate i
  have hslab := (relativePlateGraph_minimality Xswap D.source_tiles).1 P
  have hminimal := (relativePlateGraph_minimality Xswap D.source_tiles).2.1 P
  have hsub : P.centres ⊆ Tiling.AxisParallel.coordinateSwap '' T := hminimal.2.1
  have hcentres : Tiling.AxisParallel.coordinateSwap '' P.centres ⊆ T :=
    swap_subset_original_local hsub
  have htile := tilesOn_regularSupport_of_subset hsub D.source_tiles
  have hbaseOpen : IsOpen P.base := by rw [hslab.1]; exact isOpen_interior
  have hbaseNe : P.base.Nonempty := plate_base_nonempty_local P
  have hbaseZero : MeasureTheory.volume P.base ≠ 0 :=
    hbaseOpen.measure_ne_zero MeasureTheory.volume hbaseNe
  have hprop := properPlate_propagationIrreducible P hminimal
    (D.nonColumnPlate_noncolumn i) (hproper i)
  have hswapFLC := hasFLC_coordinateSwap hFLC
  refine {
    orientation := Axis.horizontal
    centres := Tiling.AxisParallel.coordinateSwap '' P.centres
    centres_nonempty := hminimal.1.image Tiling.AxisParallel.coordinateSwap
    centres_subset := hcentres
    selectedRegion := K.coordinateSwap
    selectedRegion_vertical := by intro h; cases h
    selectedRegion_horizontal := by intro; rfl
    selectedAmbientCentres := Tiling.AxisParallel.coordinateSwap '' T
    selectedAmbientCentres_vertical := by intro h; cases h
    selectedAmbientCentres_horizontal := by intro; rfl
    selectedCentres := P.centres
    selectedCentres_vertical := by intro h; cases h
    selectedCentres_horizontal := by
      intro
      exact (IntrinsicVertices.coordinateSwap_image_image P.centres).symm
    plate := P
    selectedCentres_eq_plate := rfl
    plate_noncolumn := D.nonColumnPlate_noncolumn i
    base := P.base
    base_open := hbaseOpen
    base_regular := hslab.1.symm
    base_nonnull := hbaseZero
    support_eq := hslab.2
    tiles := by
      change Tiling.AxisParallel.TilesOn K.coordinateSwap P.centres P.support at htile
      rw [hslab.2] at htile
      simpa only [P] using htile
    flc := hFLC.subset hcentres
    selected_flc := hswapFLC.subset hsub
    supportPeriod := D.commonSupportPeriod
    supportPeriod_pos := D.commonSupportPeriod_pos
    support_periodic := plate_base_periodic_local P hslab.2
      (D.nonColumnSupport_periodic i)
    propagationIrreducible := hprop }

private theorem horizontalSlabs_to_terminalDecomposition
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (X Xswap : PeriodicVerticalCarrier)
    (hPlane : X.base = Set.univ)
    (hSwapPlane : Xswap.base = Set.univ ∧ Xswap.carrier = Set.univ)
    (hFLC : Tiling.AxisParallel.HasFLC T)
    (D : PeriodicCarrierSlabDecomposition K.coordinateSwap
      (Tiling.AxisParallel.coordinateSwap '' T) Xswap)
    (hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ) :
    ∃ R : TerminalRegionDecomposition K T X,
      R.orientation = Axis.horizontal ∧
      R.slabs.numberOfNonColumnPlates = D.numberOfNonColumnPlates ∧
      R.selectedColumnCentres = D.columnCentres := by
  let region : Fin D.numberOfNonColumnPlates → TerminalRegion K T :=
    fun i ↦ horizontalTerminalRegion hFLC D hproper i
  let originalColumn := Tiling.AxisParallel.coordinateSwap '' D.columnCentres
  have hDcol : D.columnCentres ⊆ Tiling.AxisParallel.coordinateSwap '' T := by
    rw [D.columnCentres_eq]
    exact columnCentres_subset_local
  have hOrigCol : originalColumn ⊆ T := swap_subset_original_local hDcol
  let R : TerminalRegionDecomposition K T X := {
    orientation := Axis.horizontal
    selectedRegion := K.coordinateSwap
    selectedRegion_vertical := by intro h; cases h
    selectedRegion_horizontal := by intro; rfl
    selectedCentres := Tiling.AxisParallel.coordinateSwap '' T
    selectedCentres_vertical := by intro h; cases h
    selectedCentres_horizontal := by intro; rfl
    selectedCarrier := Xswap
    selectedCarrier_vertical := by intro h; cases h
    selectedCarrier_horizontal := by intro; exact ⟨hPlane, hSwapPlane.1, hSwapPlane.2⟩
    selected_tiles := D.source_tiles
    selected_flc := hasFLC_coordinateSwap hFLC
    slabs := D
    region := region
    region_orientation := by intro i; rfl
    region_selectedRegion := by intro i; rfl
    region_selectedAmbientCentres := by intro i; rfl
    region_selectedCentres := by intro i; rfl
    region_period := by intro i; rfl
    columnCentres := originalColumn
    selectedColumnCentres := D.columnCentres
    selectedColumnCentres_vertical := by intro h; cases h
    selectedColumnCentres_horizontal := by
      intro
      exact (IntrinsicVertices.coordinateSwap_image_image D.columnCentres).symm
    selectedColumnCentres_eq_slabs := rfl
    column_flc := hFLC.subset hOrigCol
    selectedColumn_flc := (hasFLC_coordinateSwap hFLC).subset hDcol
    parts_pairwise := by
      intro i _ j _ hij
      change Disjoint (region i).centres (region j).centres
      change Disjoint (Tiling.AxisParallel.coordinateSwap ''
        (D.nonColumnPlate i).centres)
        (Tiling.AxisParallel.coordinateSwap ''
          (D.nonColumnPlate j).centres)
      exact swap_disjoint_image_local
        (D.nonColumnCentres_pairwise (by simp) (by simp) hij)
    column_region_disjoint := by
      intro i
      change Disjoint (Tiling.AxisParallel.coordinateSwap '' D.columnCentres)
        (Tiling.AxisParallel.coordinateSwap '' (D.nonColumnPlate i).centres)
      exact swap_disjoint_image_local (D.column_nonColumn_disjoint i)
    parts_union := by
      rw [show (⋃ i, (region i).centres) =
          Tiling.AxisParallel.coordinateSwap ''
            (⋃ i, (D.nonColumnPlate i).centres) by
        rw [swap_iUnion_image_local]
        rfl, ← Set.image_union]
      rw [D.centres_partition]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        obtain ⟨t, ht, rfl⟩ := hw
        simpa only [Tiling.AxisParallel.coordinateSwap_apply_apply] using ht
      · intro hz
        exact ⟨Tiling.AxisParallel.coordinateSwap z,
          ⟨z, hz, rfl⟩,
          Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
    fullBase_only_bothTrivial := by
      intro i hi
      change (D.nonColumnPlate i).base = Set.univ at hi
      exact (hproper i hi).elim }
  refine ⟨R, ?_⟩
  exact ⟨rfl, rfl, rfl⟩


open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous

private theorem coordinateSwap_image_preimage_im
    (Y : Set ℝ) :
    coordinateSwap '' (Complex.im ⁻¹' Y) = Complex.re ⁻¹' Y := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    refine ⟨coordinateSwap z, ?_, ?_⟩
    · exact hz
    · exact coordinateSwap_apply_apply z

private theorem bothTrivial_propagation
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hP : VerticalPlate K T)
    (hPcentres : hP.centres = T)
    (hSwap : VerticalPlate K.coordinateSwap (coordinateSwap '' T))
    (hSwapCentres : hSwap.centres = coordinateSwap '' T) :
    IsPropagationIrreducible K T hP.centres Set.univ := by
  have hminimal : IsMinimalVerticalSlabSubfamily K T hP.centres :=
    VerticalPlate.minimal hTile hP
  have hSwapTile :
      TilesOn K.coordinateSwap (coordinateSwap '' T) Set.univ := by
    have hswapUniv : coordinateSwap '' (Set.univ : Set Tiling.Plane) = Set.univ :=
      Set.image_univ.trans coordinateSwap.surjective.range_eq
    simpa [hswapUniv] using
      (tilesOn_coordinateSwap hTile)
  have hSwapMinimal :
      IsMinimalVerticalSlabSubfamily K.coordinateSwap
        (coordinateSwap '' T) (coordinateSwap '' T) := by
    simpa [hSwapCentres] using VerticalPlate.minimal hSwapTile hSwap
  refine ⟨?_, ?_⟩
  · intro Q hQnonempty hQsub hQslab
    exact hminimal.2.2.2 Q hQnonempty hQsub hQslab
  · intro _hfull Q hQnonempty hQsub hQslab
    obtain ⟨Y, hYregular, hQsupport⟩ := hQslab
    have hSwapQsupport :
        regularSupport K.coordinateSwap (coordinateSwap '' Q) =
          Complex.re ⁻¹' Y := by
      rw [regularSupport_coordinateSwap, hQsupport,
        coordinateSwap_image_preimage_im]
    have hQsubT : Q ⊆ T := by
      simpa only [hPcentres] using hQsub
    have hSwapQeq : coordinateSwap '' Q = coordinateSwap '' T :=
      hSwapMinimal.2.2.2 (coordinateSwap '' Q)
        (hQnonempty.image coordinateSwap)
        (Set.image_mono hQsubT)
        ⟨Y, hYregular, hSwapQsupport⟩
    have hQeqT : Q = T := by
      apply Set.Subset.antisymm
      · intro z hz
        have hz' : coordinateSwap z ∈ coordinateSwap '' Q :=
          ⟨z, hz, rfl⟩
        rw [hSwapQeq] at hz'
        obtain ⟨t, ht, hzt⟩ := hz'
        have hzt' : z = t := coordinateSwap.injective hzt.symm
        simpa [hzt'] using ht
      · intro z hz
        have hz' : coordinateSwap z ∈ coordinateSwap '' T :=
          ⟨z, hz, rfl⟩
        rw [← hSwapQeq] at hz'
        obtain ⟨t, ht, hzt⟩ := hz'
        have hzt' : z = t := coordinateSwap.injective hzt.symm
        simpa [hzt'] using ht
    rw [hPcentres]
    exact hQeqT

theorem bothTrivialPlaneCase
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hFLC : HasFLC T)
    (hOriginal : ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hSwapped : ∃ P : VerticalPlate K.coordinateSwap (coordinateSwap '' T),
      ¬ IsVerticalColumn P ∧ P.centres = coordinateSwap '' T) :
    ∃ R : TerminalRegion K T,
      R.orientation = Axis.vertical ∧ R.centres = T ∧ R.base = Set.univ := by
  obtain ⟨P, hPnoncolumn, hPcentres⟩ := hOriginal
  obtain ⟨Pswap, _hPswapNoncolumn, hPswapCentres⟩ := hSwapped
  have hPsupport : P.support = Set.univ := by
    rw [P.support_eq_regularSupport, hPcentres,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile]
  have hPslab : P.support = Complex.re ⁻¹' P.base := by
    exact (VerticalPlate.support_isVerticalSlab hTile P).2
  have hPbase : P.base = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hxSupport : (x : Tiling.Plane) ∈ P.support := by
      rw [hPsupport]
      trivial
    have hxBase : (x : Tiling.Plane) ∈ Complex.re ⁻¹' P.base := by
      rw [← hPslab]
      exact hxSupport
    simpa using hxBase
  have hPprop : IsPropagationIrreducible K T P.centres Set.univ :=
    bothTrivial_propagation hTile P hPcentres Pswap hPswapCentres
  have hPtiles : TilesOn K P.centres (Complex.re ⁻¹' Set.univ) := by
    simpa [Set.preimage_univ, hPcentres] using hTile
  have hPbaseNonnull : MeasureTheory.volume (Set.univ : Set ℝ) ≠ 0 := by
    simp
  let R : TerminalRegion K T := {
    orientation := Axis.vertical
    centres := T
    centres_nonempty := by
      rw [← hPcentres]
      exact P.nonempty_supp.image (fun q => q.1)
    centres_subset := Subset.rfl
    selectedRegion := K
    selectedRegion_vertical := by intro; rfl
    selectedRegion_horizontal := by intro h; cases h
    selectedAmbientCentres := T
    selectedAmbientCentres_vertical := by intro; rfl
    selectedAmbientCentres_horizontal := by intro h; cases h
    selectedCentres := T
    selectedCentres_vertical := by intro; rfl
    selectedCentres_horizontal := by intro h; cases h
    plate := P
    selectedCentres_eq_plate := hPcentres.symm
    plate_noncolumn := hPnoncolumn
    base := Set.univ
    base_open := isOpen_univ
    base_regular := by simp
    base_nonnull := hPbaseNonnull
    support_eq := by
      rw [← hPcentres, ← P.support_eq_regularSupport]
      rw [hPsupport]
      simp
    tiles := by simpa [Set.preimage_univ] using hTile
    flc := hFLC
    selected_flc := hFLC
    supportPeriod := 1
    supportPeriod_pos := by norm_num
    support_periodic := by simp
    propagationIrreducible := by
      simpa only [hPcentres] using hPprop }
  refine ⟨R, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl

private theorem plate_eq_of_full_centres
    {K : Region} {T : Set Tiling.Plane}
    {P : VerticalPlate K T} (hPcentres : P.centres = T)
    (Q : VerticalPlate K T) : P = Q := by
  obtain ⟨q, hq⟩ := Q.nonempty_supp
  have hqT : q.1 ∈ T := q.2
  have hqP : q.1 ∈ P.centres := by
    rw [hPcentres]
    exact hqT
  obtain ⟨p, hp, hpq⟩ := hqP
  have hqp : q = p := Subtype.ext hpq.symm
  have hqPcomp : q ∈ P.supp := by
    rw [hqp]
    exact hp
  have hQeq : (verticalPlateGraph K T).connectedComponentMk q = Q :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff Q q).mp hq
  have hPeq : (verticalPlateGraph K T).connectedComponentMk q = P :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff P q).mp hqPcomp
  exact hPeq.symm.trans hQeq

private theorem bothTrivialPlane_decomposition
    {K : Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hX : X.base = Set.univ)
    (hTile : TilesOn K T X.carrier)
    (hFLC : HasFLC T)
    (hOriginal : ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hSwapped : ∃ P : VerticalPlate K.coordinateSwap (coordinateSwap '' T),
      ¬ IsVerticalColumn P ∧ P.centres = coordinateSwap '' T) :
    ∃ D : TerminalRegionDecomposition K T X,
      D.orientation = Axis.vertical ∧
      D.slabs.numberOfNonColumnPlates = 1 ∧
      D.columnCentres = ∅ ∧
      ∀ i, (D.region i).centres = T ∧ (D.region i).base = Set.univ := by
  have hTilePlane : TilesOn K T Set.univ := by
    simpa [PeriodicVerticalCarrier.carrier, hX] using hTile
  obtain ⟨P, hPnoncolumn, hPcentres⟩ := hOriginal
  have hPsupport : P.support = Set.univ := by
    rw [P.support_eq_regularSupport, hPcentres,
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTilePlane]
  obtain ⟨R, hRorientation, hRcentres, hRbase⟩ :=
    bothTrivialPlaneCase hTilePlane hFLC ⟨P, hPnoncolumn, hPcentres⟩ hSwapped
  have hRplateMinimal :
      IsMinimalVerticalSlabSubfamily K T P.centres := by
    exact VerticalPlate.minimal hTilePlane P
  have hRplateEq : ∀ Q : VerticalPlate K T, P = Q := by
    intro Q
    exact plate_eq_of_full_centres hPcentres Q
  have hColumnEmpty : Continuous.verticalColumnCentres K T = ∅ := by
    ext z
    constructor
    · intro hz
      rw [Continuous.verticalColumnCentres, Set.mem_iUnion] at hz
      obtain ⟨Q, _hQz⟩ := hz
      have hPQ : P = Q.1 := plate_eq_of_full_centres hPcentres Q.1
      exact (hPnoncolumn (hPQ ▸ Q.2)).elim
    · intro hz
      exact hz.elim
  have hregEmpty : regularSupport K (∅ : Set Tiling.Plane) = ∅ := by
    simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
  have iUnion_fin_one (A : Set Tiling.Plane) :
      (⋃ _ : Fin 1, A) = A := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact hi
    · intro hx
      exact Set.mem_iUnion.mpr ⟨0, hx⟩
  have iUnion_fin_one_univ :
      (⋃ _ : Fin 1, (Set.univ : Set Tiling.Plane)) = Set.univ :=
    iUnion_fin_one Set.univ
  let slabs : PeriodicCarrierSlabDecomposition K T X := {
    source_tiles := hTile
    numberOfNonColumnPlates := 1
    nonColumnPlate := fun _ => P
    nonColumnPlate_noncolumn := fun _ => hPnoncolumn
    nonColumnPlate_injective := by
      intro i j _
      exact Subsingleton.elim _ _
    nonColumnPlate_complete := by
      intro Q hQ
      refine ⟨0, ?_⟩
      exact hRplateEq Q
    columnCentres := ∅
    columnCentres_eq := by
      exact hColumnEmpty.symm
    centres_partition := by
      change ∅ ∪ ⋃ _ : Fin 1, P.centres = T
      rw [iUnion_fin_one, empty_union, hPcentres]
    nonColumnCentres_pairwise := by
      intro i _ j _ hij
      exact (hij (Subsingleton.elim _ _)).elim
    column_nonColumn_disjoint := by simp
    commonSupportPeriod := R.supportPeriod
    commonSupportPeriod_pos := R.supportPeriod_pos
    nonColumnSupport_periodic := by
      intro i
      rw [hPsupport]
      intro z
      simp
    columnBase := ∅
    columnBase_regular := by simp
    columnSupport_eq := by
      rw [hregEmpty]
      simp
    columnSupport_periodic := by
      rw [hregEmpty]
      intro z
      simp
    nonColumnSupports_pairwise := by
      intro i _ j _ hij
      exact (hij (Subsingleton.elim _ _)).elim
    column_nonColumnSupport_disjoint := by
      rw [hregEmpty]
      simp
    supports_cover := by
      rw [hregEmpty]
      change interior (closure (∅ ∪ ⋃ _ : Fin 1, P.support)) = X.carrier
      rw [iUnion_fin_one, hPsupport]
      simp [PeriodicVerticalCarrier.carrier, hX]
    nonColumn_minimal := by
      intro i
      simpa only [show (fun _ : Fin 1 => P.centres) i = P.centres by rfl]
        using hRplateMinimal
    columnAxes := ∅
    columnFibre := fun _ => ∅
    columnCentres_formula := by simp
    columnInterface := by
      intro h
      rcases h with ⟨x, hx⟩
      exact hx.elim
    }
  let D : TerminalRegionDecomposition K T X := {
    orientation := Axis.vertical
    selectedRegion := K
    selectedRegion_vertical := by intro; rfl
    selectedRegion_horizontal := by intro h; cases h
    selectedCentres := T
    selectedCentres_vertical := by intro; rfl
    selectedCentres_horizontal := by intro h; cases h
    selectedCarrier := X
    selectedCarrier_vertical := by intro; rfl
    selectedCarrier_horizontal := by intro h; cases h
    selected_tiles := hTile
    selected_flc := hFLC
    slabs := slabs
    region := fun _ => R
    region_orientation := by intro; exact hRorientation
    region_selectedRegion := by intro; exact R.selectedRegion_vertical hRorientation
    region_selectedAmbientCentres := by intro; exact R.selectedAmbientCentres_vertical hRorientation
    region_selectedCentres := by
      intro i
      exact (R.selectedCentres_vertical hRorientation).trans
        (hRcentres.trans hPcentres.symm)
    region_period := by intro; rfl
    columnCentres := ∅
    selectedColumnCentres := ∅
    selectedColumnCentres_vertical := by intro; rfl
    selectedColumnCentres_horizontal := by intro h; cases h
    selectedColumnCentres_eq_slabs := rfl
    column_flc := hFLC.subset (Set.empty_subset T)
    selectedColumn_flc := hFLC.subset (Set.empty_subset T)
    parts_pairwise := by
      intro i _ j _ hij
      exact (hij (Subsingleton.elim _ _)).elim
    column_region_disjoint := by simp
    parts_union := by
      change ∅ ∪ ⋃ _ : Fin 1, R.centres = T
      rw [iUnion_fin_one, empty_union, hRcentres]
    fullBase_only_bothTrivial := by
      intro i hi
      exact ⟨rfl, rfl, hRcentres⟩ }
  refine ⟨D, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · intro i
    exact ⟨hRcentres, hRbase⟩


private theorem terminalOrientation_fourCases
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (_hTile : Tiling.AxisParallel.TilesOn K T X.carrier) :
    X.base ≠ Set.univ ∨
    (X.base = Set.univ ∧
      ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) ∨
    (X.base = Set.univ ∧
      (∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) ∧
      ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate
          K.coordinateSwap (Tiling.AxisParallel.coordinateSwap '' T),
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
          P.centres = Tiling.AxisParallel.coordinateSwap '' T) ∨
    (X.base = Set.univ ∧
      (∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T) ∧
      (∃ P : Tiling.AxisParallel.Continuous.VerticalPlate
          K.coordinateSwap (Tiling.AxisParallel.coordinateSwap '' T),
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
          P.centres = Tiling.AxisParallel.coordinateSwap '' T)) := by
  by_cases hX : X.base = Set.univ
  · by_cases hP : ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧ P.centres = T
    · by_cases hPswap : ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate
          K.coordinateSwap (Tiling.AxisParallel.coordinateSwap '' T),
          ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
            P.centres = Tiling.AxisParallel.coordinateSwap '' T
      · exact Or.inr (Or.inr (Or.inr ⟨hX, hP, hPswap⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨hX, hP, hPswap⟩))
    · exact Or.inr (Or.inl ⟨hX, hP⟩)
  · exact Or.inl hX


end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

/-- Every periodic carrier admits its orientation-aware terminal decomposition. -/
theorem exists_terminalRegionDecomposition
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    (X : PeriodicVerticalCarrier)
    (hTile : Tiling.AxisParallel.TilesOn K T X.carrier)
    (hFLC : Tiling.AxisParallel.HasFLC T) :
    Nonempty (TerminalRegionDecomposition K T X) := by
  classical
  rcases terminalOrientation_fourCases X hTile with
    hProper | ⟨hWhole, hNoFull⟩ | ⟨hWhole, hFull, hNoSwapFull⟩ |
    ⟨hWhole, hFull, hSwapFull⟩
  · let D := Classical.choice
      (exists_periodicCarrierSlabDecomposition X hTile (Or.inl hProper))
    have hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ :=
      properCarrier_nonColumnBase_ne_univ D hProper
    obtain ⟨R, _, _, _⟩ :=
      verticalSlabs_to_terminalDecomposition X hFLC D hproper
    exact ⟨R⟩
  · have hTilePlane : Tiling.AxisParallel.TilesOn K T Set.univ := by
      simpa [PeriodicVerticalCarrier.carrier, hWhole] using hTile
    let D := Classical.choice
      (exists_periodicCarrierSlabDecomposition X hTile (Or.inr hFLC))
    have hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ := by
      intro i
      exact nontrivialPlanePlate_hasProperBase hTilePlane hNoFull (D.nonColumnPlate i)
        (D.nonColumnPlate_noncolumn i)
    obtain ⟨R, _, _, _⟩ :=
      verticalSlabs_to_terminalDecomposition X hFLC D hproper
    exact ⟨R⟩
  · have hTilePlane : Tiling.AxisParallel.TilesOn K T Set.univ := by
      simpa [PeriodicVerticalCarrier.carrier, hWhole] using hTile
    have hSwapTile :
        Tiling.AxisParallel.TilesOn K.coordinateSwap
          (Tiling.AxisParallel.coordinateSwap '' T) Set.univ := by
      have hswapUniv :
          Tiling.AxisParallel.coordinateSwap '' (Set.univ : Set Tiling.Plane) = Set.univ :=
        Set.image_univ.trans Tiling.AxisParallel.coordinateSwap.surjective.range_eq
      simpa [hswapUniv] using
        Tiling.AxisParallel.tilesOn_coordinateSwap hTilePlane
    let Xswap : PeriodicVerticalCarrier := {
      base := Set.univ
      base_open := isOpen_univ
      base_regular := by simp
      base_nonnull := by simp
      period := 1
      period_pos := by norm_num
      base_periodic := by simp }
    have hFLCswap : Tiling.AxisParallel.HasFLC
        (Tiling.AxisParallel.coordinateSwap '' T) :=
      hasFLC_coordinateSwap hFLC
    let D := Classical.choice
      (exists_periodicCarrierSlabDecomposition Xswap hSwapTile (Or.inr hFLCswap))
    have hproper : ∀ i, (D.nonColumnPlate i).base ≠ Set.univ := by
      intro i
      exact nontrivialPlanePlate_hasProperBase hSwapTile hNoSwapFull
        (D.nonColumnPlate i) (D.nonColumnPlate_noncolumn i)
    obtain ⟨R, _, _, _⟩ :=
      horizontalSlabs_to_terminalDecomposition X Xswap hWhole
        ⟨rfl, by simp [Xswap, PeriodicVerticalCarrier.carrier]⟩ hFLC D hproper
    exact ⟨R⟩
  · obtain ⟨D, _, _, _, _⟩ :=
      bothTrivialPlane_decomposition X hWhole hTile hFLC hFull hSwapFull
    exact ⟨D⟩

end Tiling.AxisParallel.Terminal
