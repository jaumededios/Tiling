import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Foundations.LatticeOrbitRepresentatives
import Tiling.AxisParallel.OneDimensional.FiniteInterval.EndpointCoding
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.OneDimensional.PeriodicPointEnumeration
import Tiling.AxisParallel.Terminal.AssemblyCore
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/- Exact19 authorized additive imports: the lower lattice-orbit and endpoint-coding APIs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open MeasureTheory
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

/-!
# Simultaneous rationalization of finitely many slabs

This module starts the simultaneous construction with its native finite partition datum and the
generic-section lemma.  The eventual rationalization uses one approximation for the whole finite
family rather than one map per slab.
-/

open Set
open scoped Pointwise

/-- A finite literal partition of a periodic carrier into tiled vertical slabs. -/
structure FiniteSlabPartition
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane) where
  carrierBase : Set ℝ
  carrierBase_open : IsOpen carrierBase
  carrierBase_regular : interior (closure carrierBase) = carrierBase
  carrierBase_nonnull : MeasureTheory.volume carrierBase ≠ 0
  source_tiles : Tiling.AxisParallel.TilesOn K S (Complex.re ⁻¹' carrierBase)
  numberOfParts : ℕ
  numberOfParts_pos : 0 < numberOfParts
  partCentres : Fin numberOfParts → Set Tiling.Plane
  partCentres_nonempty : ∀ i, (partCentres i).Nonempty
  partCentres_pairwise :
    Set.PairwiseDisjoint Set.univ partCentres
  partCentres_union : (⋃ i, partCentres i) = S
  partBase : Fin numberOfParts → Set ℝ
  partBase_open : ∀ i, IsOpen (partBase i)
  partBase_regular : ∀ i, interior (closure (partBase i)) = partBase i
  partBase_ae_disjoint :
    Set.PairwiseDisjoint Set.univ
      (fun i ↦ MeasureTheory.volume.restrict (partBase i))
  partBase_ae_partition :
    MeasureTheory.volume.restrict carrierBase =
      ∑ i, MeasureTheory.volume.restrict (partBase i)
  part_tiles : ∀ i,
    Tiling.AxisParallel.TilesOn K (partCentres i)
      (Complex.re ⁻¹' partBase i)
  commonPeriod : ℝ
  commonPeriod_pos : 0 < commonPeriod
  carrierBase_periodic : commonPeriod +ᵥ carrierBase = carrierBase
  verticalPeriod : Fin numberOfParts → ℝ
  verticalPeriod_pos : ∀ i, 0 < verticalPeriod i
  shear : Fin numberOfParts → ℝ
  part_vertical_period : ∀ i,
    verticalPeriodVector (verticalPeriod i) ∈
      Tiling.AxisParallel.periodGroup (partCentres i)
  part_skew_period : ∀ i,
    skewPeriodVector commonPeriod (shear i) ∈
      Tiling.AxisParallel.periodGroup (partCentres i)

/-- Carrier and labelled-slab boundary coordinates. -/
def slabBoundarySet
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) : Set ℝ :=
  frontier P.carrierBase ∪ ⋃ i, frontier (P.partBase i)

/-- One first-coordinate rationalization shared by every member of a finite slab partition. -/
structure SlabRationalization
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane)
    (P : FiniteSlabPartition K S) where
  tileAnchor : Tiling.Plane
  tileAnchor_mem : tileAnchor ∈ K.vertices
  centreAnchor : Tiling.Plane
  centreAnchor_mem : centreAnchor ∈ S
  context : Tiling.AxisParallel.Approximation.ApproximationContext
  context_region : context.region.openCarrier = (-tileAnchor) +ᵥ K.openCarrier
  context_centres : context.centres = (-centreAnchor) +ᵥ S
  context_target : context.target =
    (-(tileAnchor + centreAnchor)) +ᵥ (Complex.re ⁻¹' P.carrierBase)
  context_tiles : Tiling.AxisParallel.TilesOn
    context.region context.centres context.target
  normalizedCarrierBase : Set ℝ
  normalizedCarrierBase_eq : normalizedCarrierBase =
    (-((tileAnchor + centreAnchor).re)) +ᵥ P.carrierBase
  normalizedPartCentres : Fin P.numberOfParts → Set Tiling.Plane
  normalizedPartCentres_eq : ∀ i,
    normalizedPartCentres i = (-centreAnchor) +ᵥ P.partCentres i
  normalizedPartBase : Fin P.numberOfParts → Set ℝ
  normalizedPartBase_eq : ∀ i, normalizedPartBase i =
    (-((tileAnchor + centreAnchor).re)) +ᵥ P.partBase i
  normalized_part_tiles : ∀ i,
    Tiling.AxisParallel.TilesOn context.region (normalizedPartCentres i)
      (Complex.re ⁻¹' normalizedPartBase i)
  commonPeriod_mem : P.commonPeriod ∈ context.coordinateSpace
  normalizedBoundary_mem : ∀ x ∈ slabBoundarySet P,
    x - (tileAnchor + centreAnchor).re ∈ context.coordinateSpace
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  phi : context.coordinateSpace →ₗ[ℚ] ℚ
  approximation :
    Tiling.AxisParallel.Approximation.IsEpsilonApproximation context epsilon phi
  good : Tiling.AxisParallel.Approximation.IsGoodApproximation context phi
  deformation :
    Tiling.AxisParallel.Approximation.CoordinateDeformation context phi
  centreEmbedding : ↥context.centres ↪ Tiling.Plane
  centreEmbedding_apply : ∀ t : ↥context.centres,
    centreEmbedding t = Tiling.AxisParallel.Approximation.mapFirstPoint phi
      (context.centrePoint t.1 t.2)
  deformedCentres : Set Tiling.Plane
  deformedCentres_eq : deformedCentres =
    Tiling.AxisParallel.Approximation.deformedCenterCarrier centreEmbedding
  deformedPartCentres : Fin P.numberOfParts → Set Tiling.Plane
  deformedPartCentres_eq : ∀ i, deformedPartCentres i =
    Tiling.AxisParallel.Approximation.deformedCenterCarrierOn centreEmbedding
      {t : ↥context.centres | (t : Tiling.Plane) ∈ normalizedPartCentres i}
  deformedPartCentres_nonempty : ∀ i, (deformedPartCentres i).Nonempty
  deformedPartCentres_pairwise :
    Set.PairwiseDisjoint Set.univ deformedPartCentres
  deformedPartCentres_union : (⋃ i, deformedPartCentres i) = deformedCentres
  deformedCarrierBase : Set ℝ
  deformedCarrierBase_open : IsOpen deformedCarrierBase
  deformedCarrierBase_regular :
    interior (closure deformedCarrierBase) = deformedCarrierBase
  deformedCarrierBase_nonnull : MeasureTheory.volume deformedCarrierBase ≠ 0
  deformedPartBase : Fin P.numberOfParts → Set ℝ
  deformedPartBase_open : ∀ i, IsOpen (deformedPartBase i)
  deformedPartBase_regular : ∀ i,
    interior (closure (deformedPartBase i)) = deformedPartBase i
  deformedPartBase_nonnull : ∀ i,
    MeasureTheory.volume (deformedPartBase i) ≠ 0
  deformedPartBase_ae_disjoint :
    Set.PairwiseDisjoint Set.univ
      (fun i ↦ MeasureTheory.volume.restrict (deformedPartBase i))
  deformedPartBase_ae_partition :
    MeasureTheory.volume.restrict deformedCarrierBase =
      ∑ i, MeasureTheory.volume.restrict (deformedPartBase i)
  deformed_tiles : Tiling.AxisParallel.TilesOn deformation.firstRegion
    deformedCentres (Complex.re ⁻¹' deformedCarrierBase)
  deformed_support : Tiling.AxisParallel.regularSupport deformation.firstRegion
    deformedCentres = Complex.re ⁻¹' deformedCarrierBase
  deformed_part_tiles : ∀ i,
    Tiling.AxisParallel.TilesOn deformation.firstRegion
      (deformedPartCentres i) (Complex.re ⁻¹' deformedPartBase i)
  deformed_part_support : ∀ i,
    Tiling.AxisParallel.regularSupport deformation.firstRegion
      (deformedPartCentres i) = Complex.re ⁻¹' deformedPartBase i
  rationalHorizontalPeriod : ℚ
  rationalHorizontalPeriod_pos : 0 < rationalHorizontalPeriod
  rationalHorizontalPeriod_eq :
    (rationalHorizontalPeriod : ℝ) =
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨P.commonPeriod, commonPeriod_mem⟩
  deformedCarrierBase_periodic :
    (rationalHorizontalPeriod : ℝ) +ᵥ deformedCarrierBase =
      deformedCarrierBase
  deformedPartBase_periodic : ∀ i,
    (rationalHorizontalPeriod : ℝ) +ᵥ deformedPartBase i =
      deformedPartBase i
  deformed_part_vertical_period : ∀ i,
    verticalPeriodVector (P.verticalPeriod i) ∈
      Tiling.AxisParallel.periodGroup (deformedPartCentres i)
  deformed_part_skew_period : ∀ i,
    skewPeriodVector (rationalHorizontalPeriod : ℝ) (P.shear i) ∈
      Tiling.AxisParallel.periodGroup (deformedPartCentres i)
  rationalMass : Fin P.numberOfParts → ℚ
  rationalMass_pos : ∀ i, 0 < rationalMass i
  rationalMass_eq : ∀ i,
    (MeasureTheory.volume
      (deformedPartBase i ∩ Set.Ico 0 (rationalHorizontalPeriod : ℝ))).toReal =
        (rationalMass i : ℝ)
  carrier_frontier_transport :
    frontier deformedCarrierBase =
      deformation.firstHomeomorph '' frontier normalizedCarrierBase
  part_frontier_transport : ∀ i,
    frontier (deformedPartBase i) =
      deformation.firstHomeomorph '' frontier (normalizedPartBase i)
  deformed_first_coordinates_rational :
    (∀ v ∈ deformation.firstRegion.vertices,
      ∃ q : ℚ, v.re = (q : ℝ)) ∧
    ∀ t ∈ deformedCentres, ∃ q : ℚ, t.re = (q : ℝ)

/-- The slab boundary set unfolds to the carrier boundary and all labelled boundaries. -/
theorem slabBoundarySet_eq
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) :
    slabBoundarySet P = frontier P.carrierBase ∪
      ⋃ i, frontier (P.partBase i) :=
  rfl

private theorem locallyFinite_openCarrier_translates
    {K : Tiling.AxisParallel.Region} {S E Q : Set Tiling.Plane}
    (hTiles : Tiling.AxisParallel.TilesOn K S E) (hQ : Q ⊆ S) :
    LocallyFinite (fun q : ↥Q ↦ q.1 +ᵥ K.openCarrier) := by
  let A := K.polygonalProtoTiling S
  let e : ↥Q ↪ A.placements :=
    ⟨fun q ↦ ⟨((q.1, ())), hQ q.2⟩, fun q r h ↦ by
      apply Subtype.ext
      exact congrArg (fun i : A.placements ↦ i.1.1) h⟩
  have hsupport : LocallyFinite (fun q : ↥Q ↦ q.1 +ᵥ K.support) := by
    have heq (q : ↥Q) :
        Tiling.placedTile A.prototiles (e q).1 = q.1 +ᵥ K.support := rfl
    have hlocal : LocallyFinite
        ((fun i : A.placements ↦ Tiling.placedTile A.prototiles i.1) ∘ e) :=
      (A.locallyFinite_placedTile hTiles.2.1).comp_injective e.injective
    rw [show ((fun i : A.placements ↦ Tiling.placedTile A.prototiles i.1) ∘ e) =
        (fun q : ↥Q ↦ q.1 +ᵥ K.support) by
      funext q
      exact heq q] at hlocal
    exact hlocal
  exact hsupport.subset fun q ↦ by
    exact Set.vadd_set_mono interior_subset

/-- Points added by regularizing a placement subfamily lie on one of its tile boundaries. -/
theorem locallyFiniteUnion_support
    {K : Tiling.AxisParallel.Region} {S E Q : Set Tiling.Plane}
    (hTiles : Tiling.AxisParallel.TilesOn K S E) (hQ : Q ⊆ S) :
    Tiling.AxisParallel.regularSupport K Q \ Tiling.AxisParallel.openUnion K Q ⊆
      ⋃ q : ↥Q, frontier (q.1 +ᵥ K.openCarrier) := by
  have hlocal := locallyFinite_openCarrier_translates hTiles hQ
  intro x hx
  have hxclosure : x ∈ closure (Tiling.AxisParallel.openUnion K Q) :=
    interior_subset hx.1
  rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, hlocal.closure_iUnion] at hxclosure
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxclosure
  rw [Set.mem_iUnion]
  refine ⟨q, ?_⟩
  have hopenq : IsOpen (q.1 +ᵥ K.openCarrier) :=
    (Homeomorph.addLeft q.1).isOpenMap _ (K.openCarrier_regularOpen).1
  rw [hopenq.frontier_eq]
  exact ⟨hxq, fun hxqopen ↦ hx.2 (Set.mem_iUnion.mpr ⟨q, hxqopen⟩)⟩

/-- The boundary of a regularized placement subfamily lies on its tile boundaries. -/
theorem regularSupportBoundary_subset_tileBoundaries
    {K : Tiling.AxisParallel.Region} {S E Q : Set Tiling.Plane}
    (hTiles : Tiling.AxisParallel.TilesOn K S E) (hQ : Q ⊆ S) :
    frontier (Tiling.AxisParallel.regularSupport K Q) ⊆
      ⋃ q : ↥Q, frontier (q.1 +ᵥ K.openCarrier) := by
  have hlocal := locallyFinite_openCarrier_translates hTiles hQ
  intro x hx
  have hxclosure : x ∈ closure (Tiling.AxisParallel.openUnion K Q) := by
    have hxregularClosure := frontier_subset_closure hx
    rw [Tiling.AxisParallel.regularSupport] at hxregularClosure
    simpa only [closure_closure] using
      closure_mono interior_subset hxregularClosure
  have hxnotOpenUnion : x ∉ Tiling.AxisParallel.openUnion K Q := by
    intro hxopen
    have hopenUnion : IsOpen (Tiling.AxisParallel.openUnion K Q) := by
      rw [Tiling.AxisParallel.openUnion]
      exact isOpen_iUnion fun q ↦
        (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
          (K.openCarrier_regularOpen).1
    have hxregular : x ∈ Tiling.AxisParallel.regularSupport K Q := by
      exact interior_maximal subset_closure
        hopenUnion hxopen
    have hx' := hx
    rw [(Tiling.AxisParallel.regularSupport_isRegularOpen K Q).1.frontier_eq] at hx'
    exact hx'.2 hxregular
  rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, hlocal.closure_iUnion] at hxclosure
  obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxclosure
  rw [Set.mem_iUnion]
  refine ⟨q, ?_⟩
  have hopenq : IsOpen (q.1 +ᵥ K.openCarrier) :=
    (Homeomorph.addLeft q.1).isOpenMap _ (K.openCarrier_regularOpen).1
  rw [hopenq.frontier_eq]
  exact ⟨hxq, fun hxqopen ↦
    hxnotOpenUnion (Set.mem_iUnion.mpr ⟨q, hxqopen⟩)⟩

/-- The labelled bases form a literal nonnull partition and inherit the common horizontal
period from the skew periods of their centre families. -/
theorem slabBases_literalAndCommonPeriodic
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) :
    (∀ i, P.partBase i ⊆ P.carrierBase) ∧
    (∀ i j, i ≠ j → Disjoint (P.partBase i) (P.partBase j)) ∧
    (∀ i, P.commonPeriod +ᵥ P.partBase i = P.partBase i) ∧
    ∀ i, MeasureTheory.volume (P.partBase i) ≠ 0 := by
  have hslabOpen (B : Set ℝ) (hB : IsOpen B) :
      IsOpen (Complex.re ⁻¹' B) :=
    hB.preimage Complex.continuous_re
  have hslabRegular (B : Set ℝ) (hB : interior (closure B) = B) :
      interior (closure (Complex.re ⁻¹' B)) = Complex.re ⁻¹' B := by
    calc
      interior (closure (Complex.re ⁻¹' B)) =
          interior (Complex.re ⁻¹' closure B) := by
            rw [Complex.closure_preimage_re]
      _ = Complex.re ⁻¹' interior (closure B) :=
        Complex.interior_preimage_re _
      _ = Complex.re ⁻¹' B := congrArg (Complex.re ⁻¹' ·) hB
  have hcarrierSupport : Tiling.AxisParallel.regularSupport K S =
      Complex.re ⁻¹' P.carrierBase :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      (hslabOpen P.carrierBase P.carrierBase_open)
      (hslabRegular P.carrierBase P.carrierBase_regular) P.source_tiles
  have hpartSupport (i : Fin P.numberOfParts) :
      Tiling.AxisParallel.regularSupport K (P.partCentres i) =
        Complex.re ⁻¹' P.partBase i :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      (hslabOpen (P.partBase i) (P.partBase_open i))
      (hslabRegular (P.partBase i) (P.partBase_regular i)) (P.part_tiles i)
  have hpartSubset (i : Fin P.numberOfParts) : P.partCentres i ⊆ S := by
    intro s hs
    apply (Set.ext_iff.mp P.partCentres_union s).mp
    exact Set.mem_iUnion.mpr ⟨i, hs⟩
  have hsupportMono {A B : Set Tiling.Plane} (hAB : A ⊆ B) :
      Tiling.AxisParallel.regularSupport K A ⊆
        Tiling.AxisParallel.regularSupport K B := by
    apply interior_mono
    apply closure_mono
    rw [Tiling.Polygonal.openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier]
    rintro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨a, hxa⟩ := hx
    exact ⟨⟨a.1, hAB a.2⟩, hxa⟩
  have hbaseSubset (i : Fin P.numberOfParts) :
      P.partBase i ⊆ P.carrierBase := by
    intro x hx
    have hz : (x : ℂ) ∈ Tiling.AxisParallel.regularSupport K (P.partCentres i) := by
      rw [hpartSupport i]
      exact hx
    have hz' := hsupportMono (hpartSubset i) hz
    rw [hcarrierSupport] at hz'
    exact hz'
  have hsupportDisjoint :=
    (Tiling.AxisParallel.regularSupport_pairwiseDisjoint P.partCentres
      P.partCentres_pairwise P.partCentres_union P.source_tiles).1
  have hbaseDisjoint (i j : Fin P.numberOfParts) (hij : i ≠ j) :
      Disjoint (P.partBase i) (P.partBase j) := by
    have hd := hsupportDisjoint (Set.mem_univ i) (Set.mem_univ j) hij
    change Disjoint
      (Tiling.AxisParallel.regularSupport K (P.partCentres i))
      (Tiling.AxisParallel.regularSupport K (P.partCentres j)) at hd
    rw [hpartSupport i, hpartSupport j] at hd
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hzi : (x : ℂ) ∈ Complex.re ⁻¹' P.partBase i := hxi
    have hzj : (x : ℂ) ∈ Complex.re ⁻¹' P.partBase j := hxj
    exact Set.disjoint_left.mp hd hzi hzj
  have hbasePeriod (i : Fin P.numberOfParts) :
      P.commonPeriod +ᵥ P.partBase i = P.partBase i := by
    let u := skewPeriodVector P.commonPeriod (P.shear i)
    have huCentres : u +ᵥ P.partCentres i = P.partCentres i :=
      (Tiling.AxisParallel.periodGroup_isAddSubgroup (P.partCentres i) u).mp
        (P.part_skew_period i)
    have huSupport : u +ᵥ Tiling.AxisParallel.regularSupport K (P.partCentres i) =
        Tiling.AxisParallel.regularSupport K (P.partCentres i) := by
      rw [← Tiling.AxisParallel.regularSupport_vadd, huCentres]
    rw [hpartSupport i] at huSupport
    ext x
    have hx := Set.ext_iff.mp huSupport (x : ℂ)
    simpa [u, skewPeriodVector, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add] using hx
  have hbaseNonnull (i : Fin P.numberOfParts) :
      MeasureTheory.volume (P.partBase i) ≠ 0 := by
    obtain ⟨s, hs⟩ := P.partCentres_nonempty i
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hxOpenUnion : s + x ∈
        Tiling.AxisParallel.openUnion K (P.partCentres i) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨s, hs⟩, ⟨x, hx, rfl⟩⟩
    have hopenUnion :
        IsOpen (Tiling.AxisParallel.openUnion K (P.partCentres i)) := by
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
      exact isOpen_iUnion fun t ↦
        (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _
          (K.openCarrier_regularOpen).1
    have hxSupport : s + x ∈
        Tiling.AxisParallel.regularSupport K (P.partCentres i) := by
      exact interior_maximal subset_closure hopenUnion hxOpenUnion
    rw [hpartSupport i] at hxSupport
    exact (P.partBase_open i).measure_ne_zero MeasureTheory.volume
      ⟨(s + x).re, hxSupport⟩
  exact ⟨hbaseSubset, hbaseDisjoint, hbasePeriod, hbaseNonnull⟩

/-- A countable family of translated finite vertex sets misses some height in every
nonempty open interval. -/
theorem exists_genericHeight_forEndpoints
    {K : Tiling.AxisParallel.Region} {S E : Set Tiling.Plane}
    (hTiles : Tiling.AxisParallel.TilesOn K S E) :
    ∃ y ∈ Set.Ioo (0 : ℝ) 1, ∀ s ∈ S, ∀ v ∈ K.vertices,
      (v + s).im ≠ y := by
  classical
  let _ : Countable S := hTiles.1.to_subtype
  let bad : Set ℝ := Set.range fun p : S × {v // v ∈ K.vertexFinset} ↦
    (p.2.1 + p.1.1).im
  have hbad : bad.Countable := Set.countable_range _
  have hnotSubset : ¬ Set.Ioo (0 : ℝ) 1 ⊆ bad := by
    intro hsubset
    have hcountable : (Set.Ioo (0 : ℝ) 1).Countable := hbad.mono hsubset
    have := Cardinal.Real.Ioo_countable_iff.mp hcountable
    norm_num at this
  obtain ⟨y, hy, hyBad⟩ := Set.not_subset.mp hnotSubset
  refine ⟨y, hy, ?_⟩
  intro s hs v hv heq
  apply hyBad
  have hvfin : v ∈ K.vertexFinset := by
    change v ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset]
    exact hv
  let sv : S × {w // w ∈ K.vertexFinset} :=
    (⟨s, hs⟩, ⟨v, hvfin⟩)
  exact ⟨sv, by simp only [sv, heq]⟩

/-- The mass of a measurable periodic set in one half-open period cell is independent of the
chosen cell. -/
theorem periodCellMeasure_translationInvariant
    {Y : Set ℝ} {b : ℝ}
    (hY : MeasurableSet Y) (hb : 0 < b) (hperiod : b +ᵥ Y = Y)
    (a : ℝ) :
    (MeasureTheory.volume (Y ∩ Set.Ico a (a + b))).toReal =
      (MeasureTheory.volume (Y ∩ Set.Ico 0 b)).toReal := by
  have hbPeriod : b ∈ Tiling.AxisParallel.periodGroup Y :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup Y b).mpr hperiod
  have hmultiple : AddSubgroup.zmultiples b ≤ Tiling.AxisParallel.periodGroup Y :=
    AddSubgroup.zmultiples_le.mpr hbPeriod
  have hinvariant (g : AddSubgroup.zmultiples b) :
      (fun x : ℝ ↦ g.1 +ᵥ x) ⁻¹' Y = Y := by
    have hgSet : g.1 +ᵥ Y = Y :=
      (Tiling.AxisParallel.periodGroup_isAddSubgroup Y g.1).mp
        (hmultiple g.2)
    ext x
    have hx := Set.ext_iff.mp hgSet (g.1 + x)
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hx.symm
  have hIoc :
      MeasureTheory.volume (Y ∩ Set.Ioc a (a + b)) =
        MeasureTheory.volume (Y ∩ Set.Ioc 0 b) := by
    convert
      (isAddFundamentalDomain_Ioc hb a MeasureTheory.volume).measure_set_eq
        (isAddFundamentalDomain_Ioc hb (0 : ℝ) MeasureTheory.volume) hY hinvariant using 1
    simp
  have hleft :
      MeasureTheory.volume (Y ∩ Set.Ico a (a + b)) =
        MeasureTheory.volume (Y ∩ Set.Ioc a (a + b)) := by
    apply MeasureTheory.measure_congr
    exact Filter.EventuallyEq.inter Filter.EventuallyEq.rfl
      MeasureTheory.Ico_ae_eq_Ioc
  have hright :
      MeasureTheory.volume (Y ∩ Set.Ico 0 b) =
        MeasureTheory.volume (Y ∩ Set.Ioc 0 b) := by
    apply MeasureTheory.measure_congr
    exact Filter.EventuallyEq.inter Filter.EventuallyEq.rfl
      MeasureTheory.Ico_ae_eq_Ioc
  rw [hleft, hright, hIoc]


open Tiling.AxisParallel.Terminal

/- Frozen skeleton sha256:
e2437df654b96b7790804f050307082621f80884d8af79c397de48b8f74aacaf
-/

private theorem slabBoundary_periodicFinite :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      (P : FiniteSlabPartition K S),
    P.commonPeriod +ᵥ slabBoundarySet P = slabBoundarySet P ∧
    (slabBoundarySet P ∩ Ico 0 P.commonPeriod).Finite := by
  intro K S P
  have hbase := Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P
  have hcarrierPeriod :
      P.commonPeriod +ᵥ frontier P.carrierBase = frontier P.carrierBase :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic
      P.carrierBase_periodic
  have hpartPeriod (i : Fin P.numberOfParts) :
      P.commonPeriod +ᵥ frontier (P.partBase i) = frontier (P.partBase i) :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic
      (hbase.2.2.1 i)
  have hcarrierMem (x : ℝ) :
      (-P.commonPeriod +ᵥ x ∈ frontier P.carrierBase) ↔
        x ∈ frontier P.carrierBase := by
    constructor
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier P.carrierBase := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa only [neg_add_cancel] using hx
      simpa only [hcarrierPeriod] using hx'
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier P.carrierBase := by
        simpa only [hcarrierPeriod] using hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa only [neg_add_cancel] using hx'
  have hpartMem (i : Fin P.numberOfParts) (x : ℝ) :
      (-P.commonPeriod +ᵥ x ∈ frontier (P.partBase i)) ↔
        x ∈ frontier (P.partBase i) := by
    constructor
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier (P.partBase i) := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa only [neg_add_cancel] using hx
      simpa only [hpartPeriod i] using hx'
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier (P.partBase i) := by
        simpa only [hpartPeriod i] using hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa only [neg_add_cancel] using hx'
  constructor
  · rw [slabBoundarySet]
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (hx | ⟨i, hx⟩)
      · left
        exact hcarrierMem x |>.mp hx
      · right
        refine ⟨i, ?_⟩
        exact hpartMem i x |>.mp hx
    · rintro (hx | ⟨i, hx⟩)
      · left
        exact hcarrierMem x |>.mpr hx
      · right
        refine ⟨i, ?_⟩
        exact hpartMem i x |>.mpr hx
  · have hcarrierFinite :
        (frontier P.carrierBase ∩ Ico 0 P.commonPeriod).Finite := by
      have h := P.source_tiles.verticalCylinder_frontier_locallyFinite
        P.carrierBase_open P.carrierBase_regular (Icc 0 P.commonPeriod)
        isCompact_Icc
      have hIcc : (Icc 0 P.commonPeriod ∩ frontier P.carrierBase).Finite := by
        simpa only [inter_comm] using h
      apply hIcc.subset
      intro x hx
      exact ⟨⟨hx.2.1, hx.2.2.le⟩, hx.1⟩
    have hpartFinite (i : Fin P.numberOfParts) :
        (frontier (P.partBase i) ∩ Ico 0 P.commonPeriod).Finite := by
      have h := (P.part_tiles i).verticalCylinder_frontier_locallyFinite
        (P.partBase_open i) (P.partBase_regular i) (Icc 0 P.commonPeriod)
        isCompact_Icc
      have hIcc :
          (Icc 0 P.commonPeriod ∩ frontier (P.partBase i)).Finite := by
        simpa only [inter_comm] using h
      apply hIcc.subset
      intro x hx
      exact ⟨⟨hx.2.1, hx.2.2.le⟩, hx.1⟩
    have hall :
        ((frontier P.carrierBase ∩ Ico 0 P.commonPeriod) ∪
          (⋃ i, (frontier (P.partBase i) ∩ Ico 0 P.commonPeriod))).Finite :=
        (hcarrierFinite.union (Set.finite_iUnion hpartFinite))
    simpa only [slabBoundarySet, union_inter_distrib_right, iUnion_inter] using hall

private theorem boundarylessSlabPartition_oneColour :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      (P : FiniteSlabPartition K S),
    slabBoundarySet P = ∅ →
      P.carrierBase = Set.univ ∧ P.numberOfParts = 1 ∧
      ∀ i, P.partBase i = Set.univ := by
  intro K S P hboundary
  have hcarrierFront : frontier P.carrierBase = ∅ := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ slabBoundarySet P := by
        rw [slabBoundarySet]
        exact Or.inl hx
      rw [hboundary] at hx'
      simp at hx'
    · intro hx
      simp at hx
  have hpartFront (i : Fin P.numberOfParts) : frontier (P.partBase i) = ∅ := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ slabBoundarySet P := by
        rw [slabBoundarySet]
        exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)
      rw [hboundary] at hx'
      simp at hx'
    · intro hx
      simp at hx
  have hcarrierUniv : P.carrierBase = Set.univ := by
    rcases frontier_eq_empty_iff.mp hcarrierFront with h | h
    · exfalso
      have hn := P.carrierBase_nonnull
      rw [h] at hn
      simp at hn
    · exact h
  have hpartUniv (i : Fin P.numberOfParts) : P.partBase i = Set.univ := by
    rcases frontier_eq_empty_iff.mp (hpartFront i) with h | h
    · exfalso
      have hnonnull := (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).2.2.2 i
      rw [h] at hnonnull
      simp at hnonnull
    · exact h
  have hnumber_le : P.numberOfParts ≤ 1 := by
    by_contra hle
    have htwo : 2 ≤ P.numberOfParts := by omega
    let i0 : Fin P.numberOfParts := ⟨0, by omega⟩
    let i1 : Fin P.numberOfParts := ⟨1, by omega⟩
    have hdis :=
      (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).2.1
        i0 i1 (by simp [i0, i1])
    rw [hpartUniv i0, hpartUniv i1] at hdis
    have hzero : (0 : ℝ) ∈ (Set.univ : Set ℝ) := by simp
    have hnot : (0 : ℝ) ∉ (Set.univ : Set ℝ) :=
      (Set.disjoint_left.mp hdis) hzero
    exact hnot hzero
  have hnumber_pos : 1 ≤ P.numberOfParts := P.numberOfParts_pos
  refine ⟨hcarrierUniv, ?_, ?_⟩
  · omega
  · intro i
    exact hpartUniv i

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private structure NormalizedSlabData
    {K : Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) where
  tileAnchor : Tiling.Plane
  tileAnchor_mem : tileAnchor ∈ K.vertices
  centreAnchor : Tiling.Plane
  centreAnchor_mem : centreAnchor ∈ S
  context : ApproximationContext
  context_region : context.region.openCarrier = (-tileAnchor) +ᵥ K.openCarrier
  context_centres : context.centres = (-centreAnchor) +ᵥ S
  context_target : context.target =
    (-(tileAnchor + centreAnchor)) +ᵥ (Complex.re ⁻¹' P.carrierBase)
  context_tiles : TilesOn context.region context.centres context.target
  normalizedCarrierBase : Set ℝ
  normalizedCarrierBase_eq : normalizedCarrierBase =
    (-((tileAnchor + centreAnchor).re)) +ᵥ P.carrierBase
  normalizedPartCentres : Fin P.numberOfParts → Set Tiling.Plane
  normalizedPartCentres_eq : ∀ i,
    normalizedPartCentres i = (-centreAnchor) +ᵥ P.partCentres i
  normalizedPartBase : Fin P.numberOfParts → Set ℝ
  normalizedPartBase_eq : ∀ i, normalizedPartBase i =
    (-((tileAnchor + centreAnchor).re)) +ᵥ P.partBase i
  normalized_part_tiles : ∀ i,
    TilesOn context.region (normalizedPartCentres i)
      (Complex.re ⁻¹' normalizedPartBase i)
  commonPeriod_mem : P.commonPeriod ∈ context.coordinateSpace
  normalizedBoundary_mem : ∀ x ∈ slabBoundarySet P,
    x - (tileAnchor + centreAnchor).re ∈ context.coordinateSpace

private structure PeriodicTranslatedVertexHomeomorph
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
    (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ) where
  homeomorph : ℝ ≃ₜ ℝ
  strictMono : StrictMono homeomorph
  translatedVertex_agreement :
    ∀ (v : N.context.region.vertices) (s : N.context.centres),
      homeomorph ((v.1 + (s.1 : Tiling.Plane)).re) =
        (mapFirstPoint phi (N.context.vertexPoint v.1 v.2) +
          mapFirstPoint phi (N.context.centrePoint s.1 s.2)).re
  period_equivariant : ∀ x : ℝ,
    homeomorph (x + P.commonPeriod) = homeomorph x +
      mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩

/- The public lower APIs actually available to this lane. -/
/- Exact smaller dependencies that are discharged by the current public APIs. -/
/- A02 can be rebuilt with a prescribed first map once agreement on the
   unshifted intrinsic vertex levels is supplied.  This is the exact smaller
   constructor reached before the translated-vertex transport step. -/
private theorem prescribedFirstCoordinateDeformation
    {C : ApproximationContext} {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hphi : IsGoodApproximation C phi)
    (hx : ℝ ≃ₜ ℝ) (hhx : StrictMono hx)
    (hxv : ∀ (v : Tiling.Plane) (hv : v ∈ C.region.vertices),
      hx v.re = (mapFirstPoint phi (C.vertexPoint v hv)).re) :
    ∃ D : CoordinateDeformation C phi, D.firstHomeomorph = hx := by
  classical
  obtain ⟨hy, hhy, hyv⟩ :=
    exists_increasingCoordinateExtension C phi hphi .vertical
  let H₁ := coordinateProductHomeomorph hx (Homeomorph.refl ℝ)
  let H := coordinateProductHomeomorph hx hy
  obtain ⟨K₁, _, hK₁open, _⟩ :=
    exists_coordinateProductImageRegion C.region hx (Homeomorph.refl ℝ)
      hhx strictMono_id
  obtain ⟨K, _, hKopen, hKvertices⟩ :=
    exists_coordinateProductImageRegion C.region hx hy hhx hhy
  have hH₁ (z : Tiling.Plane) : H₁ z = hx z.re + z.im * Complex.I := by
    change coordinateProductHomeomorph hx (Homeomorph.refl ℝ) z = _
    rw [coordinateProductHomeomorph_apply]
    rfl
  have hH (z : Tiling.Plane) : H z = hx z.re + hy z.im * Complex.I :=
    coordinateProductHomeomorph_apply hx hy z
  have hagree₁ (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      H₁ v = mapFirstPoint phi (C.vertexPoint v hv) := by
    rw [hH₁]
    apply Complex.ext
    · simp [hxv v hv]
    · simp [mapFirstPoint, ApproximationContext.vertexPoint]
  have hagree (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      H v = mapPoint phi (C.vertexPoint v hv) := by
    rw [hH]
    apply Complex.ext
    · simp [hxv v hv, mapPoint, mapFirstPoint, ApproximationContext.vertexPoint]
    · simpa [Tiling.AxisParallel.Axis.coord, mapPoint, mapScalar,
        ApproximationContext.vertexPoint] using hyv v hv
  have hcomp : ConnectedComponents ↥C.region.openCarrier ≃
      ConnectedComponents ↥K.openCarrier := by
    let e := Classical.choice (connectedComponents_equiv_image H C.region.openCarrier)
    rw [hKopen]
    exact e
  have hcompc : ConnectedComponents ↥(C.region.openCarrier)ᶜ ≃
      ConnectedComponents ↥(K.openCarrier)ᶜ := by
    let e := Classical.choice (connectedComponents_equiv_image H (C.region.openCarrier)ᶜ)
    have heq : H '' (C.region.openCarrier)ᶜ = (H '' C.region.openCarrier)ᶜ :=
      H.image_compl _
    rw [hKopen]
    rw [← heq]
    exact e
  refine ⟨{
    source_good := hphi
    firstHomeomorph := hx
    firstHomeomorph_strictMono := hhx
    secondHomeomorph := hy
    secondHomeomorph_strictMono := hhy
    firstPlanarHomeomorph := H₁
    firstPlanarHomeomorph_apply := hH₁
    planarHomeomorph := H
    planarHomeomorph_apply := hH
    firstRegion := K₁
    deformedRegion := K
    firstRegion_openCarrier := hK₁open
    deformedRegion_openCarrier := hKopen
    first_vertex_agreement := hagree₁
    vertex_agreement := hagree
    vertices_image := hKvertices
    componentEquiv := hcomp
    complementComponentEquiv := hcompc
    rational_vertices := ?_ }, rfl⟩
  intro w hw
  rw [hKvertices] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [hagree v hv]
  refine ⟨phi ⟨v.re, C.vertex_re_mem v hv⟩,
    phi ⟨v.im, C.vertex_im_mem v hv⟩, ?_, ?_⟩
  · simp [mapPoint, mapScalar, ApproximationContext.vertexPoint]
  · simp [mapPoint, mapScalar, ApproximationContext.vertexPoint]

/- Exact frozen A02-prescribed-homeomorph target, with the translated-vertex
   adapter reduced to the normalized zero centre. -/
private theorem coordinateDeformation_with_firstHomeomorph :
    ∀ {K : Region} {S : Set Tiling.Plane}
          {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
          (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ),
        IsGoodApproximation N.context phi →
        ∀ (H : PeriodicTranslatedVertexHomeomorph N phi),
          ∃ D : CoordinateDeformation N.context phi,
            D.firstHomeomorph = H.homeomorph := by
  intro K S P N phi hphi H
  have hzero : (0 : Tiling.Plane) ∈ N.context.centres := by
    rw [N.context_centres]
    refine Set.mem_vadd_set.mpr ⟨N.centreAnchor, N.centreAnchor_mem, ?_⟩
    simp
  let s₀ : N.context.centres := ⟨0, hzero⟩
  have hxv : ∀ (v : Tiling.Plane) (hv : v ∈ N.context.region.vertices),
      H.homeomorph v.re =
        (mapFirstPoint phi (N.context.vertexPoint v hv)).re := by
    intro v hv
    have h := H.translatedVertex_agreement ⟨v, hv⟩ s₀
    have hp0 : mapScalar phi
        (⟨(0 : ℝ), N.context.coordinateSpace.zero_mem⟩) = 0 := by
      have hz : (⟨(0 : ℝ), N.context.coordinateSpace.zero_mem⟩ :
          N.context.coordinateSpace) = 0 := by
        apply Subtype.ext
        simp
      change (phi (⟨(0 : ℝ), N.context.coordinateSpace.zero_mem⟩) : ℝ) = 0
      rw [hz, map_zero]
      norm_num
    have hzeroMap :
        mapFirstPoint phi (N.context.centrePoint (0 : Tiling.Plane) hzero) = 0 := by
      change (mapScalar phi ⟨(0 : ℝ), _⟩ : ℂ) + (0 : ℂ) * Complex.I = 0
      rw [hp0]
      simp
    rw [hzeroMap] at h
    simpa [s₀, mapFirstPoint, ApproximationContext.centrePoint,
      mapScalar, add_zero] using h
  exact prescribedFirstCoordinateDeformation hphi H.homeomorph H.strictMono hxv

private theorem normalized_carrier_target_eq
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P) :
    N.context.target = {z : Tiling.Plane | z.re ∈ N.normalizedCarrierBase} := by
  rw [N.context_target, N.normalizedCarrierBase_eq]
  ext z
  simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    Complex.add_re]

private theorem normalized_part_centres_subset_context
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
    (i : Fin P.numberOfParts) :
    N.normalizedPartCentres i ⊆ N.context.centres := by
  rw [N.normalizedPartCentres_eq i, N.context_centres]
  intro z hz
  obtain ⟨t, ht, rfl⟩ := Set.mem_vadd_set.mp hz
  apply Set.mem_vadd_set.mpr
  refine ⟨t, ?_, rfl⟩
  rw [← P.partCentres_union]
  exact Set.mem_iUnion.mpr ⟨i, ht⟩

private theorem normalized_carrier_open
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P) :
    IsOpen N.normalizedCarrierBase := by
  rw [N.normalizedCarrierBase_eq]
  exact P.carrierBase_open.vadd _

private theorem normalized_carrier_regular
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P) :
    interior (closure N.normalizedCarrierBase) = N.normalizedCarrierBase := by
  rw [N.normalizedCarrierBase_eq, closure_vadd, interior_vadd,
    P.carrierBase_regular]

private theorem normalized_part_open
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
    (i : Fin P.numberOfParts) : IsOpen (N.normalizedPartBase i) := by
  rw [N.normalizedPartBase_eq i]
  exact (P.partBase_open i).vadd _

private theorem normalized_part_regular
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
    (i : Fin P.numberOfParts) :
    interior (closure (N.normalizedPartBase i)) = N.normalizedPartBase i := by
  rw [N.normalizedPartBase_eq i, closure_vadd, interior_vadd,
    P.partBase_regular i]

private theorem support_mem_of_cylinder_frontier_for_subset
    (C : ApproximationContext) (T : Set Tiling.Plane) (X : Set ℝ)
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (hTile : TilesOn C.region T {z : Tiling.Plane | z.re ∈ X})
    (x q : ℝ) (hx : x ∈ frontier X) :
    ∃ t : ↥T,
      (Complex.mk x q : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support := by
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport C.region T =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hxf : (Complex.mk x q : Tiling.Plane) ∈
      frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
    rw [frontier_verticalCylinder]
    simpa using hx
  have hcloseEq : closure (regularSupport C.region T) =
      closure (openUnion C.region T) := by
    rw [regularSupport]
    apply le_antisymm
    · exact closure_minimal
        (interior_subset : interior (closure (openUnion C.region T)) ⊆
          closure (openUnion C.region T)) isClosed_closure
    · have hopen : IsOpen (openUnion C.region T) := by
        rw [openUnion]
        exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _
      exact closure_mono (interior_maximal subset_closure hopen)
  have hxclosure : (Complex.mk x q : Tiling.Plane) ∈
      closure (openUnion C.region T) := by
    rw [← hcloseEq, hsupport]
    exact frontier_subset_closure hxf
  rw [closure_openUnion_eq_iUnion_support hTile.2.1] at hxclosure
  exact Set.mem_iUnion.mp hxclosure

private theorem boundaryCoordinateWitness_for_subset
    (C : ApproximationContext) (T : Set Tiling.Plane) (X : Set ℝ)
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (hTile : TilesOn C.region T {z : Tiling.Plane | z.re ∈ X}) :
    ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ C.region.vertices)
      (t : Tiling.Plane) (_ht : t ∈ T), x = (v + t).re := by
  intro x hx
  let levels : Set ℝ := Set.range fun p : ↥T × ↥C.region.vertices =>
    ((p.1 : Tiling.Plane) + p.2.1).im
  have hlevels : levels.Countable := by
    have hT : T.Countable := (IsPacking.locallyFinite_centres hTile.2.1).2
    have hV : C.region.vertices.Countable := by
      rw [← C.region.coe_vertexFinset]
      exact C.region.vertexFinset.finite_toSet.countable
    let _ : Countable ↥T := hT.to_subtype
    let _ : Countable ↥C.region.vertices := hV.to_subtype
    exact Set.countable_range _
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ levels).Nonempty := by
    by_contra hne
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ levels := by
      intro q hq
      by_contra hqbad
      exact hne ⟨q, hq, hqbad⟩
    have hzero : volume (Set.Ioo (0 : ℝ) 1) = 0 :=
      measure_mono_null hsub (hlevels.measure_zero volume)
    exact (isOpen_Ioo.measure_ne_zero volume ⟨(1 / 2 : ℝ), by norm_num⟩) hzero
  obtain ⟨q, hqIoo, hqbad⟩ := hdiff
  obtain ⟨t, hzt⟩ := support_mem_of_cylinder_frontier_for_subset
    C T X hXopen hXregular hTile x q hx
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport C.region T =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hfront : (Complex.mk x q : Tiling.Plane) ∈
      frontier ((t : Tiling.Plane) +ᵥ C.region.support) := by
    rw [frontier]
    refine ⟨subset_closure hzt, ?_⟩
    intro hzint
    have hzopen : (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ C.region.openCarrier := by
      change (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ interior C.region.support
      simpa only [interior_vadd] using hzint
    have hzunion : (Complex.mk x q : Tiling.Plane) ∈
        openUnion C.region T := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨t, hzopen⟩
    have hopenSub : openUnion C.region T ⊆ regularSupport C.region T := by
      rw [regularSupport]
      exact interior_maximal subset_closure (by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
        exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _)
    have hztarget : (Complex.mk x q : Tiling.Plane) ∈
        ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      rw [← hsupport]
      exact hopenSub hzunion
    have hxin : x ∈ X := by simpa using hztarget
    have hxint : x ∈ interior X :=
      mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hxin)
    exact (Set.disjoint_left.1 disjoint_interior_frontier hxint hx)
  have hsource : (Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane) ∈
      frontier C.region.support := by
    have hvaddfront : frontier ((t : Tiling.Plane) +ᵥ C.region.support) =
        (t : Tiling.Plane) +ᵥ frontier C.region.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    rw [hvaddfront] at hfront
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hfront
  have hgrid := Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid
    C.region hsource
  change ((∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).re = v.re) ∨
    ∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).im = v.im) at hgrid
  obtain hgrid | hgrid := hgrid
  · obtain ⟨v, hv, hvr⟩ := hgrid
    refine ⟨v, hv, t.1, t.2, ?_⟩
    have hvr' : x - (t : Tiling.Plane).re = v.re := by
      simpa only [Complex.sub_re] using hvr
    rw [Complex.add_re]
    linarith
  · obtain ⟨v, hv, hvi⟩ := hgrid
    have hvi' : q - (t : Tiling.Plane).im = v.im := by
      simpa only [Complex.sub_im] using hvi
    have hqbad' : q = ((t : Tiling.Plane) + v).im := by
      rw [Complex.add_im]
      linarith
    exact (hqbad ⟨⟨t, ⟨v, hv⟩⟩, hqbad'.symm⟩).elim

private theorem normalizedBoundary_isTranslatedVertexLevel :
    ∀ {K : Region} {S : Set Tiling.Plane}
          {P : FiniteSlabPartition K S} (N : NormalizedSlabData P),
        ∀ x ∈ slabBoundarySet P,
          ∃ (v : N.context.region.vertices) (s : N.context.centres),
            x - (N.tileAnchor + N.centreAnchor).re =
              (v.1 + (s.1 : Tiling.Plane)).re := by
  intro K S P N x hx
  have hanchor : (N.tileAnchor + N.centreAnchor).re =
      N.tileAnchor.re + N.centreAnchor.re := by rfl
  rw [slabBoundarySet_eq P] at hx
  rcases hx with hxCarrier | hxParts
  · have hxNorm : x - (N.tileAnchor + N.centreAnchor).re ∈
        frontier N.normalizedCarrierBase := by
      rw [N.normalizedCarrierBase_eq]
      change _ ∈ frontier ((Homeomorph.addLeft _) '' _)
      rw [← Homeomorph.image_frontier]
      simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd]
      refine Set.mem_vadd_set.mpr ⟨x, hxCarrier, ?_⟩
      simp [hanchor]
      ring
    have htarget := normalized_carrier_target_eq N
    have htiles :
        TilesOn N.context.region N.context.centres
          {z : Tiling.Plane | z.re ∈ N.normalizedCarrierBase} := by
      simpa [htarget] using N.context_tiles
    obtain ⟨v, hv, t, ht, hvt⟩ := boundaryCoordinateWitness_for_subset
      N.context N.context.centres N.normalizedCarrierBase
      (normalized_carrier_open N)
      (normalized_carrier_regular N)
      htiles _ hxNorm
    exact ⟨⟨v, hv⟩, ⟨t, ht⟩, hvt⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxParts
    have hxNorm : x - (N.tileAnchor + N.centreAnchor).re ∈
        frontier (N.normalizedPartBase i) := by
      rw [N.normalizedPartBase_eq i]
      change _ ∈ frontier ((Homeomorph.addLeft _) '' _)
      rw [← Homeomorph.image_frontier]
      simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd]
      refine Set.mem_vadd_set.mpr ⟨x, hi, ?_⟩
      simp [hanchor]
      ring
    obtain ⟨v, hv, t, ht, hvt⟩ := boundaryCoordinateWitness_for_subset
      N.context (N.normalizedPartCentres i) (N.normalizedPartBase i)
      (normalized_part_open N i)
      (normalized_part_regular N i)
      (N.normalized_part_tiles i) _ hxNorm
    have htContext : (t : Tiling.Plane) ∈ N.context.centres :=
      normalized_part_centres_subset_context N i ht
    exact ⟨⟨v, hv⟩, ⟨t, htContext⟩, hvt⟩

private theorem placedTile_firstHomeomorph_image :
    ∀ {K : Region} {S : Set Tiling.Plane}
          {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
          (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ)
          (H : PeriodicTranslatedVertexHomeomorph N phi)
          (D : CoordinateDeformation N.context phi),
        D.firstHomeomorph = H.homeomorph →
        ∀ s : N.context.centres,
          D.firstPlanarHomeomorph ''
              ((s.1 : Tiling.Plane) +ᵥ N.context.region.openCarrier) =
            mapFirstPoint phi (N.context.centrePoint s.1 s.2) +ᵥ
              D.firstRegion.openCarrier := by
  intro K S P N phi H D hDH s
  let c := mapFirstPoint phi (N.context.centrePoint s.1 s.2)
  let hx₁ : ℝ ≃ₜ ℝ :=
    (Homeomorph.addRight s.1.re).trans
      (H.homeomorph.trans (Homeomorph.addRight (-c.re)))
  have hhx₁ : StrictMono hx₁ := by
    intro x y hxy
    change H.homeomorph (x + s.1.re) + -c.re <
      H.homeomorph (y + s.1.re) + -c.re
    simpa [add_comm] using
      add_lt_add_right (H.strictMono (add_lt_add_right hxy s.1.re)) (-c.re)
  have hxagree : ∀ v ∈ N.context.region.vertices,
      hx₁ v.re = D.firstHomeomorph v.re := by
    intro v hv
    have htranslated := H.translatedVertex_agreement ⟨v, hv⟩ s
    have hDvertex := congrArg Complex.re (D.first_vertex_agreement v hv)
    rw [D.firstPlanarHomeomorph_apply] at hDvertex
    rw [hDH] at hDvertex
    change H.homeomorph (v.re + s.1.re) + -c.re = D.firstHomeomorph v.re
    have him : c.im = s.1.im := by
      simp [c, mapFirstPoint, ApproximationContext.centrePoint]
    have hre : H.homeomorph (v.re + s.1.re) =
        (mapFirstPoint phi (N.context.vertexPoint v hv)).re + c.re := by
      simpa [c, Complex.add_re] using htranslated
    have hDv : H.homeomorph v.re =
        (mapFirstPoint phi (N.context.vertexPoint v hv)).re := by
      simpa using hDvertex
    rw [hre]
    rw [hDH, hDv]
    simp
  have himages :
      coordinateProductHomeomorph hx₁ (Homeomorph.refl ℝ) ''
          N.context.region.openCarrier =
        coordinateProductHomeomorph D.firstHomeomorph (Homeomorph.refl ℝ) ''
          N.context.region.openCarrier := by
    apply coordinateProductImage_openCarrier_unique N.context.region
      hx₁ (Homeomorph.refl ℝ) D.firstHomeomorph (Homeomorph.refl ℝ)
      hhx₁ strictMono_id D.firstHomeomorph_strictMono strictMono_id
    · exact hxagree
    · simp
  have hplaced (u : Tiling.Plane) :
      D.firstPlanarHomeomorph ((s.1 : Tiling.Plane) + u) =
        c + coordinateProductHomeomorph hx₁ (Homeomorph.refl ℝ) u := by
    apply Complex.ext
    · simp [D.firstPlanarHomeomorph_apply, coordinateProductHomeomorph_apply,
        hx₁, c, hDH, add_comm, add_left_comm]
    · simp [D.firstPlanarHomeomorph_apply, coordinateProductHomeomorph_apply,
        c, mapFirstPoint, ApproximationContext.centrePoint]
  have hfirst (u : Tiling.Plane) :
      D.firstPlanarHomeomorph u =
        coordinateProductHomeomorph D.firstHomeomorph (Homeomorph.refl ℝ) u := by
    rw [D.firstPlanarHomeomorph_apply,
      coordinateProductHomeomorph_apply]
    simp
  calc
    D.firstPlanarHomeomorph ''
          ((s.1 : Tiling.Plane) +ᵥ N.context.region.openCarrier) =
        c +ᵥ (coordinateProductHomeomorph hx₁ (Homeomorph.refl ℝ) ''
          N.context.region.openCarrier) := by
            ext z
            constructor
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
              exact Set.mem_vadd_set.mpr ⟨_, ⟨u, hu, rfl⟩, (hplaced u).symm⟩
            · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
              exact ⟨_, Set.mem_vadd_set.mpr ⟨u, hu, rfl⟩, hplaced u⟩
    _ = c +ᵥ (coordinateProductHomeomorph D.firstHomeomorph
          (Homeomorph.refl ℝ) '' N.context.region.openCarrier) := by rw [himages]
    _ = c +ᵥ D.firstRegion.openCarrier := by
      rw [D.firstRegion_openCarrier]
      rw [show coordinateProductHomeomorph D.firstHomeomorph
          (Homeomorph.refl ℝ) = D.firstPlanarHomeomorph by
        apply Homeomorph.ext
        intro u
        exact (hfirst u).symm]

private structure TwoBlockSlabInput
    (K : Tiling.AxisParallel.Region)
    (SNonColumn SColumn S : Set Tiling.Plane)
    (XNonColumn XColumn X : Set ℝ)
    (alpha alphaColumn beta betaColumn z w B : ℝ)
    (n nColumn : ℕ) : Prop where
  carrier_open : IsOpen X
  carrier_regular : interior (closure X) = X
  carrier_nonnull : MeasureTheory.volume X ≠ 0
  nonColumn_open : IsOpen XNonColumn
  nonColumn_regular : interior (closure XNonColumn) = XNonColumn
  column_open : IsOpen XColumn
  column_regular : interior (closure XColumn) = XColumn
  centres_disjoint : Disjoint SNonColumn SColumn
  centres_union : SNonColumn ∪ SColumn = S
  nonColumn_nonempty : SNonColumn.Nonempty
  column_nonempty : SColumn.Nonempty
  bases_ae_disjoint : Disjoint
    (MeasureTheory.volume.restrict XNonColumn)
    (MeasureTheory.volume.restrict XColumn)
  bases_ae_partition : MeasureTheory.volume.restrict X =
    MeasureTheory.volume.restrict XNonColumn +
      MeasureTheory.volume.restrict XColumn
  tiles : Tiling.AxisParallel.TilesOn K S (Complex.re ⁻¹' X)
  nonColumn_tiles : Tiling.AxisParallel.TilesOn K SNonColumn
    (Complex.re ⁻¹' XNonColumn)
  column_tiles : Tiling.AxisParallel.TilesOn K SColumn
    (Complex.re ⁻¹' XColumn)
  alpha_pos : 0 < alpha
  alphaColumn_pos : 0 < alphaColumn
  beta_pos : 0 < beta
  betaColumn_pos : 0 < betaColumn
  nonColumn_vertical : verticalPeriodVector alpha ∈
    Tiling.AxisParallel.periodGroup SNonColumn
  nonColumn_skew : skewPeriodVector beta z ∈
    Tiling.AxisParallel.periodGroup SNonColumn
  column_vertical : verticalPeriodVector alphaColumn ∈
    Tiling.AxisParallel.periodGroup SColumn
  column_skew : skewPeriodVector betaColumn w ∈
    Tiling.AxisParallel.periodGroup SColumn
  nonColumnMultiplier_pos : 0 < n
  columnMultiplier_pos : 0 < nColumn
  nonColumn_common : (n : ℝ) * beta = B
  column_common : (nColumn : ℝ) * betaColumn = B

/- Frozen skeleton sha256:
e2437df654b96b7790804f050307082621f80884d8af79c397de48b8f74aacaf
-/

private theorem twoBlockFiniteSlabPartition_exists :
    ∀ {K : Tiling.AxisParallel.Region}
          {SNonColumn SColumn S : Set Tiling.Plane}
          {XNonColumn XColumn X : Set ℝ}
          {alpha alphaColumn beta betaColumn z w B : ℝ}
          {n nColumn : ℕ}
          (_I : TwoBlockSlabInput K SNonColumn SColumn S
            XNonColumn XColumn X alpha alphaColumn beta betaColumn z w B n nColumn),
        ∃ (P : FiniteSlabPartition K S)
            (iNonColumn iColumn : Fin P.numberOfParts),
          iNonColumn ≠ iColumn ∧
          (∀ i, i = iNonColumn ∨ i = iColumn) ∧
          P.carrierBase = X ∧ P.commonPeriod = B ∧
          P.partCentres iNonColumn = SNonColumn ∧
          P.partCentres iColumn = SColumn ∧
          P.partBase iNonColumn = XNonColumn ∧
          P.partBase iColumn = XColumn ∧
          P.verticalPeriod iNonColumn = alpha ∧
          P.verticalPeriod iColumn = alphaColumn ∧
          P.shear iNonColumn = (n : ℝ) * z ∧
          P.shear iColumn = (nColumn : ℝ) * w := by
  intro K SNonColumn SColumn S XNonColumn XColumn X
    alpha alphaColumn beta betaColumn z w B n nColumn I
  let centres : Fin 2 → Set Tiling.Plane :=
    Fin.cases SNonColumn (fun _ ↦ SColumn)
  let bases : Fin 2 → Set ℝ :=
    Fin.cases XNonColumn (fun _ ↦ XColumn)
  let verticals : Fin 2 → ℝ :=
    Fin.cases alpha (fun _ ↦ alphaColumn)
  let shears : Fin 2 → ℝ :=
    Fin.cases ((n : ℝ) * z) (fun _ ↦ (nColumn : ℝ) * w)
  have hBpos : 0 < B := by
    rw [← I.nonColumn_common]
    exact mul_pos (by exact_mod_cast I.nonColumnMultiplier_pos) I.beta_pos
  have fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, hj⟩
    · exact Or.inl rfl
    · right
      simpa using hj.trans (congrArg Fin.succ (Subsingleton.elim j 0))
  have hcentres_union : (⋃ i : Fin 2, centres i) = S := by
    ext s
    constructor
    · intro hs
      rw [Set.mem_iUnion] at hs
      obtain ⟨i, hi⟩ := hs
      rcases fin2_cases i with rfl | rfl
      · rw [← I.centres_union]
        exact Or.inl hi
      · rw [← I.centres_union]
        exact Or.inr hi
    · intro hs
      rw [← I.centres_union] at hs
      rcases hs with hs | hs
      · exact Set.mem_iUnion.mpr ⟨0, hs⟩
      · exact Set.mem_iUnion.mpr ⟨1, hs⟩
  have hcentres_pairwise : Set.PairwiseDisjoint Set.univ centres := by
    intro i _ j _ hij
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
    · exact (hij rfl).elim
    · change Disjoint SNonColumn SColumn
      exact I.centres_disjoint
    · change Disjoint SColumn SNonColumn
      exact I.centres_disjoint.symm
    · exact (hij rfl).elim
  have hbases_pairwise : Set.PairwiseDisjoint Set.univ
      (fun i ↦ MeasureTheory.volume.restrict (bases i)) := by
    intro i _ j _ hij
    rcases fin2_cases i with rfl | rfl <;> rcases fin2_cases j with rfl | rfl
    · exact (hij rfl).elim
    · change Disjoint (MeasureTheory.volume.restrict XNonColumn)
        (MeasureTheory.volume.restrict XColumn)
      exact I.bases_ae_disjoint
    · change Disjoint (MeasureTheory.volume.restrict XColumn)
        (MeasureTheory.volume.restrict XNonColumn)
      exact I.bases_ae_disjoint.symm
    · exact (hij rfl).elim
  have hbases_partition : MeasureTheory.volume.restrict X =
      ∑ i : Fin 2, MeasureTheory.volume.restrict (bases i) := by
    rw [Fin.sum_univ_two]
    change MeasureTheory.volume.restrict X =
      MeasureTheory.volume.restrict XNonColumn +
        MeasureTheory.volume.restrict XColumn
    exact I.bases_ae_partition
  have hnonColumnPeriod :
      skewPeriodVector B ((n : ℝ) * z) ∈
        Tiling.AxisParallel.periodGroup SNonColumn := by
    have hm := AddSubgroup.nsmul_mem
      (Tiling.AxisParallel.periodGroup SNonColumn) I.nonColumn_skew n
    rw [← I.nonColumn_common]
    convert hm using 1
    simp [skewPeriodVector, nsmul_eq_mul]
    ring
  have hcolumnPeriod :
      skewPeriodVector B ((nColumn : ℝ) * w) ∈
        Tiling.AxisParallel.periodGroup SColumn := by
    have hm := AddSubgroup.nsmul_mem
      (Tiling.AxisParallel.periodGroup SColumn) I.column_skew nColumn
    rw [← I.column_common]
    convert hm using 1
    simp [skewPeriodVector, nsmul_eq_mul]
    ring
  have hpart_centres_period (i : Fin 2) :
      skewPeriodVector B (shears i) ∈
        Tiling.AxisParallel.periodGroup (centres i) := by
    rcases fin2_cases i with rfl | rfl
    · exact hnonColumnPeriod
    · exact hcolumnPeriod
  have hslabOpen (Y : Set ℝ) (hY : IsOpen Y) :
      IsOpen (Complex.re ⁻¹' Y) := hY.preimage Complex.continuous_re
  have hslabRegular (Y : Set ℝ) (hY : interior (closure Y) = Y) :
      interior (closure (Complex.re ⁻¹' Y)) = Complex.re ⁻¹' Y := by
    calc
      interior (closure (Complex.re ⁻¹' Y)) =
          interior (Complex.re ⁻¹' closure Y) := by
            rw [Complex.closure_preimage_re]
      _ = Complex.re ⁻¹' interior (closure Y) := Complex.interior_preimage_re _
      _ = Complex.re ⁻¹' Y := congrArg (Complex.re ⁻¹' ·) hY
  have hnonSupport :
      Tiling.AxisParallel.regularSupport K SNonColumn = Complex.re ⁻¹' XNonColumn :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      (hslabOpen XNonColumn I.nonColumn_open)
      (hslabRegular XNonColumn I.nonColumn_regular) I.nonColumn_tiles
  have hcolumnSupport :
      Tiling.AxisParallel.regularSupport K SColumn = Complex.re ⁻¹' XColumn :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      (hslabOpen XColumn I.column_open)
      (hslabRegular XColumn I.column_regular) I.column_tiles
  have hcarrierSupport :
      Tiling.AxisParallel.regularSupport K S = Complex.re ⁻¹' X :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      (hslabOpen X I.carrier_open) (hslabRegular X I.carrier_regular) I.tiles
  have hnonBasePeriod : B +ᵥ XNonColumn = XNonColumn := by
    have hsupp :
        skewPeriodVector B ((n : ℝ) * z) +ᵥ
            Tiling.AxisParallel.regularSupport K SNonColumn =
          Tiling.AxisParallel.regularSupport K SNonColumn := by
      calc
        _ = Tiling.AxisParallel.regularSupport K
              (skewPeriodVector B ((n : ℝ) * z) +ᵥ SNonColumn) :=
          (Tiling.AxisParallel.regularSupport_vadd K SNonColumn _).symm
        _ = _ := by
          rw [(Tiling.AxisParallel.periodGroup_isAddSubgroup SNonColumn _).mp
            hnonColumnPeriod]
    rw [hnonSupport] at hsupp
    ext x
    have hx := Set.ext_iff.mp hsupp (x : ℂ)
    simpa [skewPeriodVector, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx
  have hcolumnBasePeriod : B +ᵥ XColumn = XColumn := by
    have hsupp :
        skewPeriodVector B ((nColumn : ℝ) * w) +ᵥ
            Tiling.AxisParallel.regularSupport K SColumn =
          Tiling.AxisParallel.regularSupport K SColumn := by
      calc
        _ = Tiling.AxisParallel.regularSupport K
              (skewPeriodVector B ((nColumn : ℝ) * w) +ᵥ SColumn) :=
          (Tiling.AxisParallel.regularSupport_vadd K SColumn _).symm
        _ = _ := by
          rw [(Tiling.AxisParallel.periodGroup_isAddSubgroup SColumn _).mp
            hcolumnPeriod]
    rw [hcolumnSupport] at hsupp
    ext x
    have hx := Set.ext_iff.mp hsupp (x : ℂ)
    simpa [skewPeriodVector, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx
  have hsupport_union :
      (⋃ i : Fin 2, Tiling.AxisParallel.regularSupport K (centres i)) =
        Complex.re ⁻¹' (XNonColumn ∪ XColumn) := by
    ext x
    rw [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rcases fin2_cases i with rfl | rfl
      · change x ∈ Tiling.AxisParallel.regularSupport K SNonColumn at hi
        rw [hnonSupport] at hi
        exact Set.mem_union_left _ hi
      · change x ∈ Tiling.AxisParallel.regularSupport K SColumn at hi
        rw [hcolumnSupport] at hi
        exact Set.mem_union_right _ hi
    · intro hx
      rcases hx with hx | hx
      · refine ⟨0, ?_⟩
        change x ∈ Tiling.AxisParallel.regularSupport K SNonColumn
        rw [hnonSupport]
        exact hx
      · refine ⟨1, ?_⟩
        change x ∈ Tiling.AxisParallel.regularSupport K SColumn
        rw [hcolumnSupport]
        exact hx
  have hregularized_union :
      X = interior (closure (XNonColumn ∪ XColumn)) := by
    have hreg := Tiling.AxisParallel.regularSupport_iUnion K centres
    rw [hcentres_union, hcarrierSupport, hsupport_union] at hreg
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re] at hreg
    ext x
    have hx := Set.ext_iff.mp hreg (x : ℂ)
    exact hx
  have hbasePeriod : B +ᵥ X = X := by
    rw [hregularized_union]
    rw [← interior_vadd, ← closure_vadd]
    have hUperiod : B +ᵥ (XNonColumn ∪ XColumn) = XNonColumn ∪ XColumn := by
      calc
        B +ᵥ (XNonColumn ∪ XColumn) =
            (B +ᵥ XNonColumn) ∪ (B +ᵥ XColumn) := by
          ext x
          simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
        _ = XNonColumn ∪ XColumn := by
          rw [hnonBasePeriod, hcolumnBasePeriod]
    rw [hUperiod]
  have hcarrierPeriod : B +ᵥ X = X := by
    exact hbasePeriod
  let P : FiniteSlabPartition K S :=
    { carrierBase := X
      carrierBase_open := I.carrier_open
      carrierBase_regular := I.carrier_regular
      carrierBase_nonnull := I.carrier_nonnull
      source_tiles := I.tiles
      numberOfParts := 2
      numberOfParts_pos := by decide
      partCentres := centres
      partCentres_nonempty := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.nonColumn_nonempty
        · exact I.column_nonempty
      partCentres_pairwise := hcentres_pairwise
      partCentres_union := hcentres_union
      partBase := bases
      partBase_open := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.nonColumn_open
        · exact I.column_open
      partBase_regular := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.nonColumn_regular
        · exact I.column_regular
      partBase_ae_disjoint := hbases_pairwise
      partBase_ae_partition := hbases_partition
      part_tiles := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.nonColumn_tiles
        · exact I.column_tiles
      commonPeriod := B
      commonPeriod_pos := hBpos
      carrierBase_periodic := hcarrierPeriod
      verticalPeriod := verticals
      verticalPeriod_pos := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.alpha_pos
        · exact I.alphaColumn_pos
      shear := shears
      part_vertical_period := by
        intro i
        rcases fin2_cases i with rfl | rfl
        · exact I.nonColumn_vertical
        · exact I.column_vertical
      part_skew_period := hpart_centres_period }
  have hne : (0 : Fin P.numberOfParts) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  have hall : ∀ i : Fin P.numberOfParts, i = 0 ∨ i = 1 := by
    intro i
    exact fin2_cases i
  have houtputs :
      P.partCentres 0 = SNonColumn ∧
      P.partCentres 1 = SColumn ∧
      P.partBase 0 = XNonColumn ∧
      P.partBase 1 = XColumn ∧
      P.verticalPeriod 0 = alpha ∧
      P.verticalPeriod 1 = alphaColumn ∧
      P.shear 0 = (n : ℝ) * z ∧
      P.shear 1 = (nColumn : ℝ) * w := by
    constructor
    · rfl
    constructor
    · change SColumn = SColumn
      rfl
    constructor
    · rfl
    constructor
    · change XColumn = XColumn
      rfl
    constructor
    · rfl
    constructor
    · change alphaColumn = alphaColumn
      rfl
    constructor
    · rfl
    · change (nColumn : ℝ) * w = (nColumn : ℝ) * w
      rfl
  exact ⟨P, 0, 1, hne, hall, rfl, rfl, houtputs⟩

private theorem twoBlockRationalization_toMixedDatum :
    ∀ {K : Tiling.AxisParallel.Region}
          {SNonColumn SColumn S : Set Tiling.Plane}
          {XNonColumn XColumn X : Set ℝ}
          {alpha alphaColumn beta betaColumn z w B : ℝ}
          {n nColumn : ℕ}
          (_I : TwoBlockSlabInput K SNonColumn SColumn S
            XNonColumn XColumn X alpha alphaColumn beta betaColumn z w B n nColumn)
          (P : FiniteSlabPartition K S)
          (iNonColumn iColumn : Fin P.numberOfParts),
        iNonColumn ≠ iColumn →
        (∀ i, i = iNonColumn ∨ i = iColumn) →
        P.carrierBase = X → P.commonPeriod = B →
        P.partCentres iNonColumn = SNonColumn →
        P.partCentres iColumn = SColumn →
        P.partBase iNonColumn = XNonColumn →
        P.partBase iColumn = XColumn →
        P.verticalPeriod iNonColumn = alpha →
        P.verticalPeriod iColumn = alphaColumn →
        P.shear iNonColumn = (n : ℝ) * z →
        P.shear iColumn = (nColumn : ℝ) * w →
        SlabRationalization K S P →
          ∃ D : MixedRationalizationDatum alpha alphaColumn B,
            D.nonColumnShear = (n : ℝ) * z ∧
            D.columnShear = (nColumn : ℝ) * w := by
  intro K SNonColumn SColumn S XNonColumn XColumn X
    alpha alphaColumn beta betaColumn z w B n nColumn I P iNonColumn iColumn
    hne hAll hCarrier hCommon hNCentres hCCentres hNBase hCBase
    hNVertical hCVertical hNShear hCShear R
  have hBpos : 0 < B := by
    rw [← I.nonColumn_common]
    exact mul_pos (by exact_mod_cast I.nonColumnMultiplier_pos) I.beta_pos
  have hqpos : 0 < (R.rationalHorizontalPeriod : ℝ) := by
    exact_mod_cast R.rationalHorizontalPeriod_pos
  refine ⟨
    { deformedRegion := R.deformation.firstRegion
      nonColumnCentres := R.deformedPartCentres iNonColumn
      columnCentres := R.deformedPartCentres iColumn
      nonColumnBase := R.deformedPartBase iNonColumn
      columnBase := R.deformedPartBase iColumn
      nonColumnBase_measurable := (R.deformedPartBase_open iNonColumn).measurableSet
      columnBase_measurable := (R.deformedPartBase_open iColumn).measurableSet
      rationalHorizontalPeriod := (R.rationalHorizontalPeriod : ℝ)
      nonColumnShear := P.shear iNonColumn
      columnShear := P.shear iColumn
      sourceCommonPeriod_pos := hBpos
      rationalHorizontalPeriod_pos := hqpos
      nonColumnTiles := R.deformed_part_tiles iNonColumn
      columnTiles := R.deformed_part_tiles iColumn
      nonColumnVerticalPeriod := by
        simpa [hNVertical] using R.deformed_part_vertical_period iNonColumn
      nonColumnHorizontalPeriod := R.deformed_part_skew_period iNonColumn
      columnVerticalPeriod := by
        simpa [hCVertical] using R.deformed_part_vertical_period iColumn
      columnHorizontalPeriod := R.deformed_part_skew_period iColumn
      nonColumnMass := R.rationalMass iNonColumn
      columnMass := R.rationalMass iColumn
      nonColumnMass_pos := R.rationalMass_pos iNonColumn
      columnMass_pos := R.rationalMass_pos iColumn
      nonColumnMass_eq := R.rationalMass_eq iNonColumn
      columnMass_eq := R.rationalMass_eq iColumn },
    ?_, ?_⟩
  · exact hNShear
  · exact hCShear

private theorem locallyFiniteSet_isolated (F : Set ℝ)
    (hlocal : ∀ a b : ℝ, (F ∩ Icc a b).Finite) {x : ℝ} (hx : x ∈ F) :
    ∃ a b : ℝ, a < x ∧ x < b ∧ Ioo a b ∩ F = {x} := by
  let G := (F ∩ Icc (x - 1) (x + 1)) \ {x}
  have hGfinite : G.Finite :=
    (hlocal (x - 1) (x + 1)).sdiff
  have hxG : x ∉ G := by simp [G]
  have hnhds : Gᶜ ∈ 𝓝 x := hGfinite.isClosed.isOpen_compl.mem_nhds hxG
  obtain ⟨a, b, ⟨hax, hxb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  refine ⟨max a (x - 1), min b (x + 1), max_lt hax (by linarith),
    lt_min hxb (by linarith), ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hyF⟩
    have hyab : y ∈ Ioo a b :=
      ⟨lt_of_le_of_lt (le_max_left _ _) hy.1,
        lt_of_lt_of_le hy.2 (min_le_left _ _)⟩
    have hyIcc : y ∈ Icc (x - 1) (x + 1) :=
      ⟨(le_max_right _ _).trans hy.1.le, hy.2.le.trans (min_le_right _ _)⟩
    have hynG : y ∉ G := hab hyab
    have : y = x := by
      by_contra hyx
      exact hynG ⟨⟨hyF, hyIcc⟩, by simpa only [mem_singleton_iff]⟩
    simpa only [mem_singleton_iff]
  · intro hy
    have hyx : y = x := by simpa only [mem_singleton_iff] using hy
    subst y
    exact ⟨⟨max_lt hax (by linarith), lt_min hxb (by linarith)⟩, hx⟩

/-- The no-crossing case of the same-frontier dichotomy. -/
private theorem regularOpen_dichotomy_of_frontier_eq_empty
    (X Y : Set ℝ) (hFX : frontier X = ∅) (hFY : frontier Y = ∅) :
    Y = X ∨ Y = interior Xᶜ := by
  rcases frontier_eq_empty_iff.mp hFX with rfl | rfl <;>
    rcases frontier_eq_empty_iff.mp hFY with rfl | rfl <;> simp

/-- A frontier-free real interval lies wholly in one chamber of an open set. -/
private theorem openSet_Ioo_chamberChoice (X : Set ℝ) (hXopen : IsOpen X)
    {a b : ℝ} (havoid : Ioo a b ∩ frontier X = ∅) :
    Ioo a b ⊆ X ∨ Ioo a b ⊆ interior Xᶜ := by
  apply isPreconnected_Ioo.subset_or_subset hXopen isOpen_interior
    (disjoint_of_subset_right interior_subset disjoint_compl_right)
  intro y hy
  have hyfrontier : y ∉ frontier X := by
    intro hyF
    have : y ∈ Ioo a b ∩ frontier X := ⟨hy, hyF⟩
    rw [havoid] at this
    exact this
  have hycompl : y ∈ (frontier X)ᶜ := hyfrontier
  rw [compl_frontier_eq_union_interior, hXopen.interior_eq] at hycompl
  exact hycompl

/-- At an isolated frontier point, a regular-open subset of the line occupies exactly one of the
two adjacent chambers.  This is the local induction step for the finite-crossing argument. -/
private theorem regularOpen_isolatedFrontier_toggle
    (X : Set ℝ) (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    {a x b : ℝ} (hax : a < x) (hxb : x < b) (hx : x ∈ frontier X)
    (hleft : Ioo a x ∩ frontier X = ∅)
    (hright : Ioo x b ∩ frontier X = ∅) :
    (Ioo a x ⊆ X ∧ Ioo x b ⊆ interior Xᶜ) ∨
      (Ioo a x ⊆ interior Xᶜ ∧ Ioo x b ⊆ X) := by
  rcases openSet_Ioo_chamberChoice X hXopen hleft with hLX | hLC
  · rcases openSet_Ioo_chamberChoice X hXopen hright with hRX | hRC
    · exfalso
      have hnear : Ioo a b ⊆ closure X := by
        intro y hy
        rcases lt_trichotomy y x with hyx | rfl | hxy
        · exact subset_closure (hLX ⟨hy.1, hyx⟩)
        · exact frontier_subset_closure hx
        · exact subset_closure (hRX ⟨hxy, hy.2⟩)
      have hxint : x ∈ interior (closure X) :=
        mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Ioo_mem_nhds hax hxb) hnear)
      rw [hXregular] at hxint
      exact (hXopen.frontier_eq ▸ hx).2 hxint
    · exact Or.inl ⟨hLX, hRC⟩
  · rcases openSet_Ioo_chamberChoice X hXopen hright with hRX | hRC
    · exact Or.inr ⟨hLC, hRX⟩
    · exfalso
      have hxnot : x ∉ X := by
        rw [hXopen.frontier_eq] at hx
        exact hx.2
      have hnear : Ioo a b ⊆ Xᶜ := by
        intro y hy
        rcases lt_trichotomy y x with hyx | rfl | hxy
        · exact interior_subset (hLC ⟨hy.1, hyx⟩)
        · exact hxnot
        · exact interior_subset (hRC ⟨hxy, hy.2⟩)
      have hxint : x ∈ interior Xᶜ :=
        mem_interior_iff_mem_nhds.mpr
          (Filter.mem_of_superset (Ioo_mem_nhds hax hxb) hnear)
      exact (frontier_compl X ▸ hx) |>.2 hxint

private theorem regularOpen_eq_or_regularComplement_of_sameLocallyFiniteFrontier :
    ∀ (X Y : Set ℝ),
      IsOpen X → interior (closure X) = X →
      IsOpen Y → interior (closure Y) = Y →
      frontier X = frontier Y →
      (∀ a b : ℝ, (frontier X ∩ Icc a b).Finite) →
        Y = X ∨ Y = interior Xᶜ := by
  intro X Y hXopen hXreg hYopen hYreg hfront hlocal
  classical
  by_cases hF : frontier X = ∅
  · exact regularOpen_dichotomy_of_frontier_eq_empty X Y hF (hfront ▸ hF)
  let A : Set ℝ := (X ∩ Y) ∪ (interior Xᶜ ∩ interior Yᶜ)
  let B : Set ℝ := (X ∩ interior Yᶜ) ∪ (interior Xᶜ ∩ Y)
  have hAopen : IsOpen A :=
    (hXopen.inter hYopen).union (isOpen_interior.inter isOpen_interior)
  have hBopen : IsOpen B :=
    (hXopen.inter isOpen_interior).union (isOpen_interior.inter hYopen)
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z (⟨hzX, hzY⟩ | ⟨hzXc, hzYc⟩)
      (⟨hzX', hzYc'⟩ | ⟨hzXc', hzY'⟩)
    · exact (interior_subset hzYc') hzY
    · exact (interior_subset hzXc') hzX
    · exact (interior_subset hzXc) hzX'
    · exact (interior_subset hzYc) hzY'
  have hcover : (frontier X)ᶜ ⊆ A ∪ B := by
    intro z hz
    have hxside : z ∈ X ∨ z ∈ interior Xᶜ := by
      have hz' : z ∈ interior X ∪ interior Xᶜ := by
        simpa only [compl_frontier_eq_union_interior] using hz
      rw [hXopen.interior_eq] at hz'
      exact hz'
    have hyside : z ∈ Y ∨ z ∈ interior Yᶜ := by
      have hzY : z ∉ frontier Y := by
        intro hzFY
        exact hz (hfront.symm ▸ hzFY)
      have hz' : z ∈ interior Y ∪ interior Yᶜ := by
        rw [← compl_frontier_eq_union_interior]
        exact hzY
      rw [hYopen.interior_eq] at hz'
      exact hz'
    rcases hxside with hzX | hzXc <;> rcases hyside with hzY | hzYc
    · exact Or.inl (Or.inl ⟨hzX, hzY⟩)
    · exact Or.inr (Or.inl ⟨hzX, hzYc⟩)
    · exact Or.inr (Or.inr ⟨hzXc, hzY⟩)
    · exact Or.inl (Or.inr ⟨hzXc, hzYc⟩)
  have hfrontChoice (x : ℝ) (hx : x ∈ frontier X) :
      (x ∈ closure A ∧ x ∉ closure B) ∨
        (x ∈ closure B ∧ x ∉ closure A) := by
    obtain ⟨a, b, hax, hxb, hiso⟩ := locallyFiniteSet_isolated (frontier X) hlocal hx
    have hleft : Ioo a x ∩ frontier X = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hz, hzF⟩
      have hzsing : z ∈ ({x} : Set ℝ) := by
        rw [← hiso]
        exact ⟨⟨hz.1, hz.2.trans hxb⟩, hzF⟩
      exact hz.2.ne (by simpa only [Set.mem_singleton_iff] using hzsing)
    have hright : Ioo x b ∩ frontier X = ∅ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hz, hzF⟩
      have hzsing : z ∈ ({x} : Set ℝ) := by
        rw [← hiso]
        exact ⟨⟨hax.trans hz.1, hz.2⟩, hzF⟩
      exact hz.1.ne' (by simpa only [Set.mem_singleton_iff] using hzsing)
    have hleftY : Ioo a x ∩ frontier Y = ∅ := by simpa only [← hfront] using hleft
    have hrightY : Ioo x b ∩ frontier Y = ∅ := by simpa only [← hfront] using hright
    have hxY : x ∈ frontier Y := hfront ▸ hx
    rcases regularOpen_isolatedFrontier_toggle X hXopen hXreg hax hxb hx hleft hright with
      hX | hX <;>
    rcases regularOpen_isolatedFrontier_toggle Y hYopen hYreg hax hxb hxY hleftY hrightY with
      hY | hY
    · left
      have hIA : Ioo a x ⊆ A := fun z hz ↦ Or.inl ⟨hX.1 hz, hY.1 hz⟩
      have hxA : x ∈ closure A := by
        apply closure_mono hIA
        rw [closure_Ioo hax.ne]
        exact ⟨hax.le, le_rfl⟩
      refine ⟨hxA, ?_⟩
      have hd : Disjoint (Ioo a b) B := by
        rw [Set.disjoint_left]
        intro z hzI hzB
        rcases lt_trichotomy z x with hzx | rfl | hxz
        · rcases hzB with hzB | hzB
          · exact (interior_subset hzB.2) (hY.1 ⟨hzI.1, hzx⟩)
          · exact (interior_subset hzB.1) (hX.1 ⟨hzI.1, hzx⟩)
        · have hxnotX : z ∉ X := (hXopen.frontier_eq ▸ hx).2
          have hxnotY : z ∉ Y := (hYopen.frontier_eq ▸ hxY).2
          rcases hzB with hzB | hzB
          · exact hxnotX hzB.1
          · exact hxnotY hzB.2
        · rcases hzB with hzB | hzB
          · exact (interior_subset (hX.2 ⟨hxz, hzI.2⟩)) hzB.1
          · exact (interior_subset (hY.2 ⟨hxz, hzI.2⟩)) hzB.2
      exact Set.disjoint_left.mp (hd.closure_right isOpen_Ioo) ⟨hax, hxb⟩
    · right
      have hIB : Ioo a x ⊆ B := fun z hz ↦ Or.inl ⟨hX.1 hz, hY.1 hz⟩
      have hxB : x ∈ closure B := by
        apply closure_mono hIB
        rw [closure_Ioo hax.ne]
        exact ⟨hax.le, le_rfl⟩
      refine ⟨hxB, ?_⟩
      have hd : Disjoint (Ioo a b) A := by
        rw [Set.disjoint_left]
        intro z hzI hzA
        rcases lt_trichotomy z x with hzx | rfl | hxz
        · rcases hzA with hzA | hzA
          · exact (interior_subset (hY.1 ⟨hzI.1, hzx⟩)) hzA.2
          · exact (interior_subset hzA.1) (hX.1 ⟨hzI.1, hzx⟩)
        · have hxnotX : z ∉ X := (hXopen.frontier_eq ▸ hx).2
          have hxnotXi : z ∉ interior Xᶜ := by
            rw [frontier_eq_inter_compl_interior] at hx
            exact hx.2
          rcases hzA with hzA | hzA
          · exact hxnotX hzA.1
          · exact hxnotXi hzA.1
        · rcases hzA with hzA | hzA
          · exact (interior_subset (hX.2 ⟨hxz, hzI.2⟩)) hzA.1
          · exact (interior_subset hzA.2) (hY.2 ⟨hxz, hzI.2⟩)
      exact Set.disjoint_left.mp (hd.closure_right isOpen_Ioo) ⟨hax, hxb⟩
    · right
      have hIB : Ioo a x ⊆ B := fun z hz ↦ Or.inr ⟨hX.1 hz, hY.1 hz⟩
      have hxB : x ∈ closure B := by
        apply closure_mono hIB
        rw [closure_Ioo hax.ne]
        exact ⟨hax.le, le_rfl⟩
      refine ⟨hxB, ?_⟩
      have hd : Disjoint (Ioo a b) A := by
        rw [Set.disjoint_left]
        intro z hzI hzA
        rcases lt_trichotomy z x with hzx | rfl | hxz
        · rcases hzA with hzA | hzA
          · exact (interior_subset (hX.1 ⟨hzI.1, hzx⟩)) hzA.1
          · exact (interior_subset hzA.2) (hY.1 ⟨hzI.1, hzx⟩)
        · have hxnotX : z ∉ X := (hXopen.frontier_eq ▸ hx).2
          have hxnotXi : z ∉ interior Xᶜ := by
            rw [frontier_eq_inter_compl_interior] at hx
            exact hx.2
          rcases hzA with hzA | hzA
          · exact hxnotX hzA.1
          · exact hxnotXi hzA.1
        · rcases hzA with hzA | hzA
          · exact (interior_subset (hY.2 ⟨hxz, hzI.2⟩)) hzA.2
          · exact (interior_subset hzA.1) (hX.2 ⟨hxz, hzI.2⟩)
      exact Set.disjoint_left.mp (hd.closure_right isOpen_Ioo) ⟨hax, hxb⟩
    · left
      have hIA : Ioo a x ⊆ A := fun z hz ↦ Or.inr ⟨hX.1 hz, hY.1 hz⟩
      have hxA : x ∈ closure A := by
        apply closure_mono hIA
        rw [closure_Ioo hax.ne]
        exact ⟨hax.le, le_rfl⟩
      refine ⟨hxA, ?_⟩
      have hd : Disjoint (Ioo a b) B := by
        rw [Set.disjoint_left]
        intro z hzI hzB
        rcases lt_trichotomy z x with hzx | rfl | hxz
        · rcases hzB with hzB | hzB
          · exact (interior_subset (hX.1 ⟨hzI.1, hzx⟩)) hzB.1
          · exact (interior_subset (hY.1 ⟨hzI.1, hzx⟩)) hzB.2
        · have hxnotX : z ∉ X := (hXopen.frontier_eq ▸ hx).2
          have hxnotY : z ∉ Y := (hYopen.frontier_eq ▸ hxY).2
          rcases hzB with hzB | hzB
          · exact hxnotX hzB.1
          · exact hxnotY hzB.2
        · rcases hzB with hzB | hzB
          · exact (interior_subset hzB.2) (hY.2 ⟨hxz, hzI.2⟩)
          · exact (interior_subset hzB.1) (hX.2 ⟨hxz, hzI.2⟩)
      exact Set.disjoint_left.mp (hd.closure_right isOpen_Ioo) ⟨hax, hxb⟩
  have hclosuresDisjoint : Disjoint (closure A) (closure B) := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    by_cases hzF : z ∈ frontier X
    · rcases hfrontChoice z hzF with h | h
      · exact h.2 hzB
      · exact h.2 hzA
    · rcases hcover hzF with hz | hz
      · exact Set.disjoint_left.mp (hAB.closure_right hAopen) hz hzB
      · exact Set.disjoint_left.mp (hAB.closure_left hBopen) hzA hz
  have hclosuresCover : (Set.univ : Set ℝ) ⊆ closure A ∪ closure B := by
    intro z _
    by_cases hzF : z ∈ frontier X
    · rcases hfrontChoice z hzF with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · rcases hcover hzF with hz | hz
      · exact Or.inl (subset_closure hz)
      · exact Or.inr (subset_closure hz)
  have hempty : closure A = ∅ ∨ closure B = ∅ := by
    by_contra h
    push Not at h
    have hAn : (closure A).Nonempty := h.1
    have hBn : (closure B).Nonempty := h.2
    have hpre : IsPreconnected (Set.univ : Set ℝ) := isPreconnected_univ
    have hi := isPreconnected_closed_iff.mp hpre
      (closure A) (closure B) isClosed_closure isClosed_closure hclosuresCover
      (by simpa only [Set.univ_inter] using hAn) (by simpa only [Set.univ_inter] using hBn)
    rw [hclosuresDisjoint.inter_eq, Set.univ_inter] at hi
    exact Set.not_nonempty_empty hi
  rcases hempty with hAe | hBe
  · right
    have hYXc : Y ⊆ Xᶜ := by
      intro z hzY hzX
      have hzA : z ∈ A := Or.inl ⟨hzX, hzY⟩
      simpa only [hAe, Set.mem_empty_iff_false] using subset_closure hzA
    have hYint : Y ⊆ interior Xᶜ := interior_maximal hYXc hYopen
    apply Set.Subset.antisymm_iff.mpr
    constructor
    · exact hYint
    · intro z hzXc
      have hznotYc : z ∉ interior Yᶜ := by
        intro hzYc
        have hzA : z ∈ A := Or.inr ⟨hzXc, hzYc⟩
        simpa only [hAe, Set.mem_empty_iff_false] using subset_closure hzA
      have hznotFY : z ∉ frontier Y := by
        intro hzFY
        have hzFX : z ∈ frontier X := hfront.symm ▸ hzFY
        rw [frontier_eq_inter_compl_interior] at hzFX
        exact hzFX.2 hzXc
      have : z ∈ Y ∨ z ∈ interior Yᶜ := by
        have : z ∈ interior Y ∪ interior Yᶜ := by
          rw [← compl_frontier_eq_union_interior]
          exact hznotFY
        rw [hYopen.interior_eq] at this
        exact this
      exact this.resolve_right hznotYc
  · left
    ext z
    constructor
    · intro hzY
      have hznotFX : z ∉ frontier X := by
        intro hzFX
        have hzFY : z ∈ frontier Y := hfront ▸ hzFX
        rw [hYopen.frontier_eq] at hzFY
        exact hzFY.2 hzY
      rcases hcover hznotFX with hzA | hzB
      · rcases hzA with hzA | hzA
        · exact hzA.1
        · exact False.elim ((interior_subset hzA.2) hzY)
      · have : z ∈ closure B := subset_closure hzB
        rw [hBe] at this
        exact this.elim
    · intro hzX
      have hznotFX : z ∉ frontier X := by
        rw [hXopen.frontier_eq]
        exact fun h ↦ h.2 hzX
      rcases hcover hznotFX with hzA | hzB
      · rcases hzA with hzA | hzA
        · exact hzA.2
        · exact False.elim ((interior_subset hzA.1) hzX)
      · have : z ∈ closure B := subset_closure hzB
        rw [hBe] at this
        exact this.elim

/- Frozen skeleton sha256:
e2437df654b96b7790804f050307082621f80884d8af79c397de48b8f74aacaf
-/

private theorem openUnion_subset_regularSupport
    (K : Tiling.AxisParallel.Region) (S : Set Tiling.Plane) :
    Tiling.AxisParallel.openUnion K S ⊆
      Tiling.AxisParallel.regularSupport K S := by
  apply interior_maximal subset_closure
  rw [Tiling.AxisParallel.openUnion]
  exact isOpen_iUnion fun t ↦
    (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ K.openCarrier_regularOpen.1

private theorem slabRationalization_anchorColour :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (R : SlabRationalization K S P),
    ∃ i₀ : Fin P.numberOfParts,
      0 ∈ R.normalizedPartCentres i₀ ∧
      ((R.deformation.firstHomeomorph '' R.normalizedPartBase i₀) ∩
        R.deformedPartBase i₀).Nonempty ∧
      ((R.deformation.firstHomeomorph '' R.normalizedCarrierBase) ∩
        R.deformedCarrierBase).Nonempty := by
  intro K S P R
  have hcUnion : R.centreAnchor ∈ ⋃ i, P.partCentres i := by
    rw [P.partCentres_union]
    exact R.centreAnchor_mem
  obtain ⟨i₀, hci₀⟩ := Set.mem_iUnion.mp hcUnion
  have hzeroPart : (0 : Tiling.Plane) ∈ R.normalizedPartCentres i₀ := by
    rw [R.normalizedPartCentres_eq i₀, Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using hci₀
  let t₀ : ↥R.context.centres := ⟨0, R.context.zero_mem_centres⟩
  have ht₀part : (t₀ : Tiling.Plane) ∈ R.normalizedPartCentres i₀ := hzeroPart
  have hcentreImage : R.centreEmbedding t₀ = 0 := by
    rw [R.centreEmbedding_apply]
    let z₀ : {z : Tiling.Plane // z.re ∈ R.context.coordinateSpace ∧
        z.im ∈ R.context.coordinateSpace} := ⟨0, by simp⟩
    have harg : R.context.centrePoint t₀.1 t₀.2 = z₀ := by
      apply Subtype.ext
      simp [t₀, z₀, Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint]
    rw [harg]
    have hzre : (⟨z₀.1.re, z₀.2.1⟩ : R.context.coordinateSpace) = 0 := by
      apply Subtype.ext
      simp [z₀]
    unfold Tiling.AxisParallel.Approximation.mapFirstPoint
      Tiling.AxisParallel.Approximation.mapScalar
    rw [hzre, R.phi.map_zero]
    simp [z₀]
  obtain ⟨x, hx⟩ := R.context.region.isPolygonal.interior_nonempty
    R.context.region.nonempty
  change x ∈ R.context.region.openCarrier at hx
  have hxSourceOpen : x ∈ Tiling.AxisParallel.openUnion R.context.region
      (R.normalizedPartCentres i₀) := by
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨0, hzeroPart⟩, by simpa only [zero_vadd] using hx⟩
  have hxSourceSupport : x ∈ Tiling.AxisParallel.regularSupport R.context.region
      (R.normalizedPartCentres i₀) :=
    openUnion_subset_regularSupport _ _ hxSourceOpen
  have hxBase : x.re ∈ R.normalizedPartBase i₀ := by
    have hbaseOpen : IsOpen (R.normalizedPartBase i₀) := by
      rw [R.normalizedPartBase_eq i₀]
      exact (Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))).isOpenMap _
        (P.partBase_open i₀)
    have hbaseRegular : interior (closure (R.normalizedPartBase i₀)) =
        R.normalizedPartBase i₀ := by
      rw [R.normalizedPartBase_eq i₀]
      let H := Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))
      change interior (closure (H '' P.partBase i₀)) = H '' P.partBase i₀
      rw [← H.image_closure, ← H.image_interior, P.partBase_regular i₀]
    have hcylOpen : IsOpen (Complex.re ⁻¹' R.normalizedPartBase i₀) :=
      hbaseOpen.preimage Complex.continuous_re
    have hcylRegular : interior (closure (Complex.re ⁻¹' R.normalizedPartBase i₀)) =
        Complex.re ⁻¹' R.normalizedPartBase i₀ := by
      rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hbaseRegular]
    have hsupp := Tiling.AxisParallel.regularSupport_eq_of_tilesOn
      hcylOpen hcylRegular (R.normalized_part_tiles i₀)
    rw [hsupp] at hxSourceSupport
    exact hxSourceSupport
  let y := R.deformation.firstPlanarHomeomorph x
  have hyOpen : y ∈ R.deformation.firstRegion.openCarrier := by
    rw [R.deformation.firstRegion_openCarrier]
    exact ⟨x, hx, rfl⟩
  have hzeroDeformedPart : (0 : Tiling.Plane) ∈ R.deformedPartCentres i₀ := by
    rw [R.deformedPartCentres_eq i₀,
      Tiling.AxisParallel.Approximation.deformedCenterCarrierOn]
    exact ⟨t₀, ht₀part, hcentreImage⟩
  have hzeroDeformed : (0 : Tiling.Plane) ∈ R.deformedCentres := by
    rw [R.deformedCentres_eq, Tiling.AxisParallel.Approximation.deformedCenterCarrier]
    exact ⟨t₀, hcentreImage⟩
  have hyPartOpenUnion : y ∈ Tiling.AxisParallel.openUnion R.deformation.firstRegion
      (R.deformedPartCentres i₀) := by
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨0, hzeroDeformedPart⟩, by simpa only [zero_vadd] using hyOpen⟩
  have hyFullOpenUnion : y ∈ Tiling.AxisParallel.openUnion R.deformation.firstRegion
      R.deformedCentres := by
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨0, hzeroDeformed⟩, by simpa only [zero_vadd] using hyOpen⟩
  have hyPartSupport := openUnion_subset_regularSupport _ _ hyPartOpenUnion
  have hyFullSupport := openUnion_subset_regularSupport _ _ hyFullOpenUnion
  rw [R.deformed_part_support i₀] at hyPartSupport
  rw [R.deformed_support] at hyFullSupport
  have hyre : y.re = R.deformation.firstHomeomorph x.re := by
    change (R.deformation.firstPlanarHomeomorph x).re = _
    rw [R.deformation.firstPlanarHomeomorph_apply]
    simp
  have hxCarrier : x.re ∈ R.normalizedCarrierBase := by
    have hsubset := (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).1 i₀
    rw [R.normalizedCarrierBase_eq, Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [R.normalizedPartBase_eq i₀, Set.mem_vadd_set_iff_neg_vadd_mem] at hxBase
    exact hsubset hxBase
  refine ⟨i₀, hzeroPart, ?_, ?_⟩
  · refine ⟨y.re, ⟨?_, hyPartSupport⟩⟩
    exact ⟨x.re, hxBase, hyre.symm⟩
  · refine ⟨y.re, ⟨?_, hyFullSupport⟩⟩
    exact ⟨x.re, hxCarrier, hyre.symm⟩

/- Frozen skeleton sha256:
e2437df654b96b7790804f050307082621f80884d8af79c397de48b8f74aacaf
-/

private theorem homeomorph_image_frontier_locallyFinite
    (H : ℝ ≃ₜ ℝ) (X : Set ℝ)
    (hlocal : ∀ C : Set ℝ, IsCompact C → (C ∩ frontier X).Finite) :
    ∀ a b : ℝ, (frontier (H '' X) ∩ Icc a b).Finite := by
  intro a b
  have hcompact : IsCompact (H ⁻¹' Icc a b) :=
    H.isCompact_preimage.mpr isCompact_Icc
  have hfinite : (frontier X ∩ H ⁻¹' Icc a b).Finite := by
    simpa only [inter_comm] using hlocal (H ⁻¹' Icc a b) hcompact
  have himage := hfinite.image H
  rw [Set.image_inter_preimage, H.image_frontier] at himage
  exact himage

private theorem slabRationalization_mappedFrontiers_locallyFinite :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (R : SlabRationalization K S P),
    (∀ a b : ℝ,
      (frontier (R.deformation.firstHomeomorph '' R.normalizedCarrierBase) ∩
        Icc a b).Finite) ∧
    ∀ i, ∀ a b : ℝ,
      (frontier (R.deformation.firstHomeomorph '' R.normalizedPartBase i) ∩
        Icc a b).Finite := by
  intro K S P R
  have hcarrierOpen : IsOpen R.normalizedCarrierBase := by
    rw [R.normalizedCarrierBase_eq]
    exact (Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))).isOpenMap _
      P.carrierBase_open
  have hcarrierRegular : interior (closure R.normalizedCarrierBase) =
      R.normalizedCarrierBase := by
    rw [R.normalizedCarrierBase_eq]
    let H := Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))
    change interior (closure (H '' P.carrierBase)) = H '' P.carrierBase
    rw [← H.image_closure, ← H.image_interior, P.carrierBase_regular]
  have hcontextTarget : R.context.target =
      Complex.re ⁻¹' R.normalizedCarrierBase := by
    rw [R.context_target, R.normalizedCarrierBase_eq]
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  have hcarrierTiles : Tiling.AxisParallel.TilesOn R.context.region R.context.centres
      (Complex.re ⁻¹' R.normalizedCarrierBase) := by
    rw [← hcontextTarget]
    exact R.context_tiles
  constructor
  · apply homeomorph_image_frontier_locallyFinite
    intro C hC
    exact hcarrierTiles.verticalCylinder_frontier_locallyFinite
      hcarrierOpen hcarrierRegular C hC
  · intro i
    have hpartOpen : IsOpen (R.normalizedPartBase i) := by
      rw [R.normalizedPartBase_eq i]
      exact (Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))).isOpenMap _
        (P.partBase_open i)
    have hpartRegular : interior (closure (R.normalizedPartBase i)) =
        R.normalizedPartBase i := by
      rw [R.normalizedPartBase_eq i]
      let H := Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))
      change interior (closure (H '' P.partBase i)) = H '' P.partBase i
      rw [← H.image_closure, ← H.image_interior, P.partBase_regular i]
    apply homeomorph_image_frontier_locallyFinite
    intro C hC
    exact (R.normalized_part_tiles i).verticalCylinder_frontier_locallyFinite
      hpartOpen hpartRegular C hC

/- Frozen skeleton sha256:
e2437df654b96b7790804f050307082621f80884d8af79c397de48b8f74aacaf
-/

private theorem slabRationalization_allBaseImages :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (R : SlabRationalization K S P),
    R.deformedCarrierBase =
        R.deformation.firstHomeomorph '' R.normalizedCarrierBase ∧
      ∀ i, R.deformedPartBase i =
        R.deformation.firstHomeomorph '' R.normalizedPartBase i := by
  intro K S P R
  let H := R.deformation.firstHomeomorph
  have hlocal := slabRationalization_mappedFrontiers_locallyFinite R
  have hopenCarrier : IsOpen (H '' R.normalizedCarrierBase) :=
    H.isOpenMap _ (by
      rw [R.normalizedCarrierBase_eq]
      exact (Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))).isOpenMap _
        P.carrierBase_open)
  have hregCarrier : interior (closure (H '' R.normalizedCarrierBase)) =
      H '' R.normalizedCarrierBase := by
    rw [← H.image_closure, ← H.image_interior]
    congr 1
    rw [R.normalizedCarrierBase_eq]
    let T := Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))
    change interior (closure (T '' P.carrierBase)) = T '' P.carrierBase
    rw [← T.image_closure, ← T.image_interior, P.carrierBase_regular]
  have hcarrierFront : frontier (H '' R.normalizedCarrierBase) =
      frontier R.deformedCarrierBase := by
    calc
      frontier (H '' R.normalizedCarrierBase) = H '' frontier R.normalizedCarrierBase :=
        (H.image_frontier _).symm
      _ = frontier R.deformedCarrierBase := by
        simpa only [H] using R.carrier_frontier_transport.symm
  have hcarrierChoice :=
    regularOpen_eq_or_regularComplement_of_sameLocallyFiniteFrontier
      (H '' R.normalizedCarrierBase) R.deformedCarrierBase
      hopenCarrier hregCarrier R.deformedCarrierBase_open R.deformedCarrierBase_regular
      hcarrierFront (hlocal.1)
  obtain ⟨i₀, _, hanchorPart, hanchorCarrier⟩ :=
    slabRationalization_anchorColour R
  have hcarrierEq : R.deformedCarrierBase = H '' R.normalizedCarrierBase := by
    rcases hcarrierChoice with h | h
    · exact h
    · exfalso
      obtain ⟨x, hxX, hxY⟩ := hanchorCarrier
      rw [h] at hxY
      exact (interior_subset hxY) hxX
  have hopenPart (i : Fin P.numberOfParts) :
      IsOpen (H '' R.normalizedPartBase i) :=
    H.isOpenMap _ (by
      rw [R.normalizedPartBase_eq i]
      exact (Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))).isOpenMap _
        (P.partBase_open i))
  have hregPart (i : Fin P.numberOfParts) :
      interior (closure (H '' R.normalizedPartBase i)) =
        H '' R.normalizedPartBase i := by
    rw [← H.image_closure, ← H.image_interior]
    congr 1
    rw [R.normalizedPartBase_eq i]
    let T := Homeomorph.addLeft (-((R.tileAnchor + R.centreAnchor).re))
    change interior (closure (T '' P.partBase i)) = T '' P.partBase i
    rw [← T.image_closure, ← T.image_interior, P.partBase_regular i]
  have hchoice (i : Fin P.numberOfParts) :
      R.deformedPartBase i = H '' R.normalizedPartBase i ∨
        R.deformedPartBase i = interior (H '' R.normalizedPartBase i)ᶜ := by
    apply regularOpen_eq_or_regularComplement_of_sameLocallyFiniteFrontier
      (H '' R.normalizedPartBase i) (R.deformedPartBase i)
      (hopenPart i) (hregPart i) (R.deformedPartBase_open i)
      (R.deformedPartBase_regular i)
    · calc
        frontier (H '' R.normalizedPartBase i) =
            H '' frontier (R.normalizedPartBase i) := (H.image_frontier _).symm
        _ = frontier (R.deformedPartBase i) := by
          simpa only [H] using (R.part_frontier_transport i).symm
    · exact hlocal.2 i
  have hi₀ : R.deformedPartBase i₀ = H '' R.normalizedPartBase i₀ := by
    rcases hchoice i₀ with h | h
    · exact h
    · exfalso
      obtain ⟨x, hxX, hxY⟩ := hanchorPart
      rw [h] at hxY
      exact (interior_subset hxY) hxX
  have hsourceDisjoint (i j : Fin P.numberOfParts) (hij : i ≠ j) :
      Disjoint (H '' R.normalizedPartBase i) (H '' R.normalizedPartBase j) := by
    have hd := (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).2.1 i j hij
    rw [Set.disjoint_left]
    rintro x ⟨xi, hxi, rfl⟩ ⟨xj, hxj, heq⟩
    apply Set.disjoint_left.mp hd
    · rw [R.normalizedPartBase_eq i, Set.mem_vadd_set_iff_neg_vadd_mem] at hxi
      exact hxi
    · rw [R.normalizedPartBase_eq j, Set.mem_vadd_set_iff_neg_vadd_mem] at hxj
      have : xi = xj := H.injective heq.symm
      simpa only [this] using hxj
  have htargetDisjoint (i j : Fin P.numberOfParts) (hij : i ≠ j) :
      Disjoint (R.deformedPartBase i) (R.deformedPartBase j) := by
    have hd := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
      R.deformedPartCentres R.deformedPartCentres_pairwise
      R.deformedPartCentres_union R.deformed_tiles).1
      (Set.mem_univ i) (Set.mem_univ j) hij
    change Disjoint
      (Tiling.AxisParallel.regularSupport R.deformation.firstRegion
        (R.deformedPartCentres i))
      (Tiling.AxisParallel.regularSupport R.deformation.firstRegion
        (R.deformedPartCentres j)) at hd
    rw [R.deformed_part_support i, R.deformed_part_support j] at hd
    rw [Set.disjoint_left]
    intro x hxi hxj
    exact Set.disjoint_left.mp hd (show (x : ℂ) ∈ Complex.re ⁻¹' R.deformedPartBase i from hxi)
      (show (x : ℂ) ∈ Complex.re ⁻¹' R.deformedPartBase j from hxj)
  refine ⟨hcarrierEq, fun j ↦ ?_⟩
  by_cases hj : j = i₀
  · simpa only [hj] using hi₀
  rcases hchoice j with h | h
  · exact h
  · exfalso
    obtain ⟨x, hxX, _⟩ := hanchorPart
    have hxComp : x ∈ interior (H '' R.normalizedPartBase j)ᶜ := by
      apply interior_maximal
      · intro z hz
        exact Set.disjoint_left.mp (hsourceDisjoint i₀ j (Ne.symm hj)) hz
      · exact hopenPart i₀
      exact hxX
    have hxTargetJ : x ∈ R.deformedPartBase j := by simpa only [h] using hxComp
    have hxTargetI : x ∈ R.deformedPartBase i₀ := by simpa only [hi₀] using hxX
    exact Set.disjoint_left.mp (htargetDisjoint i₀ j (Ne.symm hj)) hxTargetI hxTargetJ

theorem rationalMap_preservesCyclicSupportCode :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (R : SlabRationalization K S P),
    ∀ a ∈ slabBoundarySet P, ∀ b ∈ slabBoundarySet P,
      a < b → Ioo a b ∩ slabBoundarySet P = ∅ →
      ((Ioo a b ⊆ P.carrierBase ↔
        Ioo
          (R.deformation.firstHomeomorph
            (a - (R.tileAnchor + R.centreAnchor).re))
          (R.deformation.firstHomeomorph
            (b - (R.tileAnchor + R.centreAnchor).re)) ⊆
            R.deformedCarrierBase) ∧
      ∀ i, Ioo a b ⊆ P.partBase i ↔
        Ioo
          (R.deformation.firstHomeomorph
            (a - (R.tileAnchor + R.centreAnchor).re))
          (R.deformation.firstHomeomorph
            (b - (R.tileAnchor + R.centreAnchor).re)) ⊆
              R.deformedPartBase i) := by
  intro K S P R a _ b _ _ _
  let H := R.deformation.firstHomeomorph
  let c := (R.tileAnchor + R.centreAnchor).re
  have himages := slabRationalization_allBaseImages R
  have hIoo : H '' Ioo (a - c) (b - c) = Ioo (H (a - c)) (H (b - c)) :=
    H.continuous.image_Ioo_of_strictMono R.deformation.firstHomeomorph_strictMono
  have hnormalize (B : Set ℝ) :
      Ioo a b ⊆ B ↔ Ioo (a - c) (b - c) ⊆ (-c) +ᵥ B := by
    constructor
    · intro h x hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change - -c + x ∈ B
      have hc : - -c + x = x + c := by ring
      rw [hc]
      apply h
      constructor <;> linarith [hx.1, hx.2]
    · intro h x hx
      have hy : x - c ∈ Ioo (a - c) (b - c) := by
        constructor <;> linarith [hx.1, hx.2]
      have := h hy
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at this
      change - -c + (x - c) ∈ B at this
      have heq : - -c + (x - c) = x := by ring
      rw [heq] at this
      exact this
  have himageSubset (X : Set ℝ) :
      Ioo (a - c) (b - c) ⊆ X ↔
        Ioo (H (a - c)) (H (b - c)) ⊆ H '' X := by
    rw [← hIoo]
    constructor
    · exact Set.image_mono
    · intro h x hx
      obtain ⟨y, hyX, hyEq⟩ := h ⟨x, hx, rfl⟩
      exact H.injective hyEq ▸ hyX
  constructor
  · rw [hnormalize P.carrierBase, ← R.normalizedCarrierBase_eq,
      himageSubset R.normalizedCarrierBase, ← himages.1]
  · intro i
    rw [hnormalize (P.partBase i), ← R.normalizedPartBase_eq i,
      himageSubset (R.normalizedPartBase i), ← himages.2 i]


private theorem openUnion_translate_normalization
    {K L : Region} {S Q : Set Tiling.Plane} {a b : Tiling.Plane}
    (hregion : L.openCarrier = a +ᵥ K.openCarrier)
    (hcentres : Q = b +ᵥ S) :
    openUnion L Q = (a + b) +ᵥ openUnion K S := by
  rw [hcentres]
  ext z
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  change (∃ q : b +ᵥ S,
      z ∈ (q : Tiling.Plane) +ᵥ L.openCarrier) ↔
    ∃ s : S, -(a + b) + z ∈
      (s : Tiling.Plane) +ᵥ K.openCarrier
  constructor
  · intro hz
    obtain ⟨q, hzq⟩ := hz
    obtain ⟨s, hs, hqs⟩ := Set.mem_vadd_set.mp q.2
    rw [← hqs] at hzq
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [hregion] at hzq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzq
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    convert hzq using 1
    simp only [vadd_eq_add]
    abel
  · intro hz
    obtain ⟨s, hz⟩ := hz
    let q : b +ᵥ S := ⟨b + s.1, by
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_cancel_left] using s.2⟩
    refine ⟨q, ?_⟩
    rw [hregion]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
    convert hz using 1
    simp only [q, vadd_eq_add]
    abel

private theorem regularSupport_translate_normalization
    {K L : Region} {S Q : Set Tiling.Plane} {a b : Tiling.Plane}
    (hregion : L.openCarrier = a +ᵥ K.openCarrier)
    (hcentres : Q = b +ᵥ S) :
    regularSupport L Q = (a + b) +ᵥ regularSupport K S := by
  rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
    Tiling.Polygonal.regularSupport, ← openUnion, ← openUnion,
    openUnion_translate_normalization hregion hcentres,
    closure_vadd, interior_vadd]

private theorem tilesOn_of_regularSupport_normalization
    {K : Region} {S D₀ Q D : Set Tiling.Plane}
    (hTiles : TilesOn K S D₀) (hQ : Q ⊆ S)
    (hSupport : regularSupport K Q = D) : TilesOn K Q D := by
  have hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Q) := by
    apply (isPacking_iff_openCarrier_disjoint K Q).2
    intro a ha b hb hab
    exact (isPacking_iff_openCarrier_disjoint K S).1 hTiles.2.1
      (hQ ha) (hQ hb) hab
  have hcount : Q.Countable := (IsPacking.locallyFinite_centres hpack).2
  have hae := openUnion_aeEq_regularSupport hpack
  refine ⟨hcount, hpack, ?_⟩
  filter_upwards [hae] with z hz
  have hz' : z ∈ D ↔ z ∈ regularSupport K Q := by
    exact Iff.of_eq (hSupport ▸ rfl)
  have hraw : z ∈ regularSupport K Q ↔
      ∃ s : Q, z ∈ (s : Tiling.Plane) +ᵥ K.openCarrier := by
    constructor
    · intro h
      exact Set.mem_iUnion.mp ((Iff.of_eq hz.symm).mp h)
    · rintro ⟨s, hs⟩
      apply (Iff.of_eq hz.symm).mpr
      exact Set.mem_iUnion.mpr ⟨s, hs⟩
  exact hz'.trans hraw

private theorem normalizedSlabData_exists :
    ∀ {K : Region} {S : Set Tiling.Plane}
      (P : FiniteSlabPartition K S), Nonempty (NormalizedSlabData P) := by
  intro K S P
  obtain ⟨v₀, hv₀, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  let i₀ : Fin P.numberOfParts := ⟨0, P.numberOfParts_pos⟩
  obtain ⟨t₀, ht₀⟩ := P.partCentres_nonempty i₀
  have ht₀S : t₀ ∈ S := by
    rw [← P.partCentres_union]
    exact Set.mem_iUnion.mpr ⟨i₀, ht₀⟩
  obtain ⟨C, hCregion, hCcentres, hCtarget, hCtiles⟩ :=
    normalizeApproximationContext K S (Complex.re ⁻¹' P.carrierBase)
      v₀ hv₀ t₀ ht₀S
  let carrier : Set ℝ := (-((v₀ + t₀).re)) +ᵥ P.carrierBase
  let partCentres : Fin P.numberOfParts → Set Tiling.Plane :=
    fun i ↦ (-t₀) +ᵥ P.partCentres i
  let partBase : Fin P.numberOfParts → Set ℝ :=
    fun i ↦ (-((v₀ + t₀).re)) +ᵥ P.partBase i
  have hpartSubset (i : Fin P.numberOfParts) :
      partCentres i ⊆ C.centres := by
    rw [hCcentres]
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Set.mem_vadd_set.mp hz
    apply Set.mem_vadd_set.mpr
    refine ⟨t, ?_, rfl⟩
    rw [← P.partCentres_union]
    exact Set.mem_iUnion.mpr ⟨i, ht⟩
  have hsourceSupport :
    regularSupport K S = Complex.re ⁻¹' P.carrierBase :=
    regularSupport_eq_of_tilesOn
      (P.carrierBase_open.preimage Complex.continuous_re)
      (by
        change interior (closure (Complex.re ⁻¹' P.carrierBase)) = _
        rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
          P.carrierBase_regular]) P.source_tiles
  have hcarrierSupport :
      regularSupport C.region C.centres = Complex.re ⁻¹' carrier := by
    have htrans := regularSupport_translate_normalization
      (K := K) (L := C.region) (S := S) (Q := C.centres)
      (a := -v₀) (b := -t₀) hCregion hCcentres
    rw [htrans, hsourceSupport]
    ext z
    simp [carrier, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      Complex.add_re, add_comm]
  have hcarrierTiles : TilesOn C.region C.centres (Complex.re ⁻¹' carrier) := by
    apply tilesOn_of_regularSupport_normalization (D₀ := C.target) (hCtiles.mp P.source_tiles)
      (by intro z hz; exact hz)
    exact hcarrierSupport
  have hpartSupport (i : Fin P.numberOfParts) :
      regularSupport C.region (partCentres i) = Complex.re ⁻¹' partBase i := by
    have hsource : regularSupport K (P.partCentres i) =
        Complex.re ⁻¹' P.partBase i :=
      regularSupport_eq_of_tilesOn
        ((P.partBase_open i).preimage Complex.continuous_re)
        (by
          change interior (closure (Complex.re ⁻¹' P.partBase i)) = _
          rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
            P.partBase_regular i]) (P.part_tiles i)
    have htrans := regularSupport_translate_normalization
      (K := K) (L := C.region) (S := P.partCentres i) (Q := partCentres i)
      (a := -v₀) (b := -t₀) hCregion rfl
    rw [htrans, hsource]
    ext z
    simp [partBase, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      Complex.add_re, add_comm]
  have hpartTiles (i : Fin P.numberOfParts) :
      TilesOn C.region (partCentres i) (Complex.re ⁻¹' partBase i) :=
    tilesOn_of_regularSupport_normalization (D₀ := C.target) (hCtiles.mp P.source_tiles)
      (hpartSubset i) (hpartSupport i)
  have hcommon : P.commonPeriod ∈ C.coordinateSpace := by
    let u := skewPeriodVector P.commonPeriod (P.shear i₀)
    have hu : u +ᵥ P.partCentres i₀ = P.partCentres i₀ :=
      (periodGroup_isAddSubgroup (P.partCentres i₀) u).mp
        (P.part_skew_period i₀)
    have htu : u + t₀ ∈ P.partCentres i₀ := by
      rw [← hu]
      exact Set.mem_vadd_set.mpr ⟨t₀, ht₀, rfl⟩
    let t₁ : Tiling.Plane := u + t₀
    have ht₁ : t₁ ∈ P.partCentres i₀ := by simpa [t₁] using htu
    have ht₁S : t₁ ∈ S := by
      rw [← P.partCentres_union]
      exact Set.mem_iUnion.mpr ⟨i₀, ht₁⟩
    have hc₀ : (0 : Tiling.Plane) ∈ C.centres := by
      rw [hCcentres]
      exact Set.mem_vadd_set.mpr ⟨t₀, ht₀S, by simp⟩
    have hc₁ : u ∈ C.centres := by
      rw [hCcentres]
      refine Set.mem_vadd_set.mpr ⟨t₁, ht₁S, ?_⟩
      simp only [t₁, u, vadd_eq_add]
      abel
    rw [C.coordinateSpace_eq_span]
    apply Submodule.subset_span
    refine ⟨Tiling.AxisParallel.Axis.horizontal, u, 0, ?_, ?_, ?_⟩
    · exact ⟨0, C.zero_mem_vertices, u, hc₁, by simp⟩
    · exact ⟨0, C.zero_mem_vertices, 0, hc₀, by simp⟩
    · simp [Tiling.AxisParallel.Axis.coord, u, skewPeriodVector]
  have hboundary : ∀ x ∈ slabBoundarySet P,
      x - (v₀ + t₀).re ∈ C.coordinateSpace := by
    intro x hx
    rw [slabBoundarySet_eq P] at hx
    rcases hx with hxCarrier | hxParts
    · have hxNorm : x - (v₀ + t₀).re ∈ frontier carrier := by
        simp only [carrier]
        change _ ∈ frontier ((Homeomorph.addLeft _) '' _)
        rw [← Homeomorph.image_frontier]
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd]
        refine Set.mem_vadd_set.mpr ⟨x, hxCarrier, ?_⟩
        simp [vadd_eq_add]
        ring
      obtain ⟨v, hv, t, ht, hvt⟩ := boundaryCoordinateWitness_for_subset
        C C.centres carrier
        (by exact P.carrierBase_open.vadd _)
        (by
          change interior (closure ((-((v₀ + t₀).re)) +ᵥ P.carrierBase)) = _
          rw [closure_vadd, interior_vadd, P.carrierBase_regular])
        hcarrierTiles _ hxNorm
      rw [hvt]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v hv)
        (C.centre_re_mem t ht)
    · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxParts
      have hxNorm : x - (v₀ + t₀).re ∈ frontier (partBase i) := by
        simp only [partBase]
        change _ ∈ frontier ((Homeomorph.addLeft _) '' _)
        rw [← Homeomorph.image_frontier]
        simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd]
        refine Set.mem_vadd_set.mpr ⟨x, hxi, ?_⟩
        simp [vadd_eq_add]
        ring
      obtain ⟨v, hv, t, ht, hvt⟩ := boundaryCoordinateWitness_for_subset
        C (partCentres i) (partBase i)
        (by exact (P.partBase_open i).vadd _)
        (by
          change interior (closure ((-((v₀ + t₀).re)) +ᵥ P.partBase i)) = _
          rw [closure_vadd, interior_vadd, P.partBase_regular i])
        (hpartTiles i) _ hxNorm
      have htC : t ∈ C.centres := hpartSubset i ht
      rw [hvt]
      exact C.coordinateSpace.add_mem (C.vertex_re_mem v hv)
        (C.centre_re_mem t htC)
  refine ⟨{
    tileAnchor := v₀
    tileAnchor_mem := hv₀
    centreAnchor := t₀
    centreAnchor_mem := ht₀S
    context := C
    context_region := hCregion
    context_centres := hCcentres
    context_target := hCtarget
    context_tiles := hCtiles.mp P.source_tiles
    normalizedCarrierBase := carrier
    normalizedCarrierBase_eq := rfl
    normalizedPartCentres := partCentres
    normalizedPartCentres_eq := fun _ ↦ rfl
    normalizedPartBase := partBase
    normalizedPartBase_eq := fun _ ↦ rfl
    normalized_part_tiles := hpartTiles
    commonPeriod_mem := hcommon
    normalizedBoundary_mem := hboundary }⟩

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
structure PeriodicSlabCode
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) where
  numberOfBoundaryPoints : ℕ
  numberOfBoundaryPoints_pos : 0 < numberOfBoundaryPoints
  boundary : ℤ → ℝ
  boundary_strictMono : StrictMono boundary
  boundary_range : Set.range boundary = slabBoundarySet P
  boundary_period : ∀ j : ℤ,
    boundary (j + Int.ofNat numberOfBoundaryPoints) =
      boundary j + P.commonPeriod
  label : ℤ → Option (Fin P.numberOfParts)
  label_part_iff : ∀ (j : ℤ) (i : Fin P.numberOfParts),
    label j = some i ↔ Ioo (boundary j) (boundary (j + 1)) ⊆ P.partBase i
  label_outside_iff : ∀ j : ℤ,
    label j = none ↔ Ioo (boundary j) (boundary (j + 1)) ⊆ P.carrierBaseᶜ
  label_periodic : ∀ j : ℤ,
    label (j + Int.ofNat numberOfBoundaryPoints) = label j

private theorem frontier_subset_slabBoundary
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) :
    frontier P.carrierBase ⊆ slabBoundarySet P := by
  intro x hx
  rw [slabBoundarySet]
  exact Or.inl hx

private theorem part_frontier_subset_slabBoundary
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) (i : Fin P.numberOfParts) :
    frontier (P.partBase i) ⊆ slabBoundarySet P := by
  intro x hx
  rw [slabBoundarySet]
  exact Or.inr (Set.mem_iUnion.mpr ⟨i, hx⟩)

private theorem bounded_frontier_finite
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) (Q : Set ℝ)
    (hQ : Bornology.IsBounded Q) :
    (frontier P.carrierBase ∩ Q).Finite := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hQ
  have hclosed := P.source_tiles.verticalCylinder_frontier_locallyFinite
    P.carrierBase_open P.carrierBase_regular (Set.Icc (-R) R)
    isCompact_Icc
  apply hclosed.subset
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : ℝ) R := hR hx.2
  have hxIcc : x ∈ Set.Icc (-R) R := by
    simpa [Metric.mem_closedBall, Real.norm_eq_abs, abs_le] using hxball
  exact ⟨hxIcc, hx.1⟩

private theorem bounded_part_frontier_finite
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) (i : Fin P.numberOfParts)
    (Q : Set ℝ) (hQ : Bornology.IsBounded Q) :
    (frontier (P.partBase i) ∩ Q).Finite := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hQ
  have hclosed := (P.part_tiles i).verticalCylinder_frontier_locallyFinite
    (P.partBase_open i) (P.partBase_regular i) (Set.Icc (-R) R)
    isCompact_Icc
  apply hclosed.subset
  intro x hx
  have hxball : x ∈ Metric.closedBall (0 : ℝ) R := hR hx.2
  have hxIcc : x ∈ Set.Icc (-R) R := by
    simpa [Metric.mem_closedBall, Real.norm_eq_abs, abs_le] using hxball
  exact ⟨hxIcc, hx.1⟩

private theorem slabBoundary_bounded_finite
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (slabBoundarySet P ∩ Q).Finite := by
  intro Q hQ
  have hc := bounded_frontier_finite P Q hQ
  have hp (i : Fin P.numberOfParts) := bounded_part_frontier_finite P i Q hQ
  have hall :
      ((frontier P.carrierBase ∩ Q) ∪
        (⋃ i, frontier (P.partBase i) ∩ Q)).Finite :=
    hc.union (Set.finite_iUnion hp)
  simpa only [slabBoundarySet, union_inter_distrib_right, iUnion_inter] using hall

private theorem slabBoundary_periodic
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    (P : FiniteSlabPartition K S) :
    P.commonPeriod +ᵥ slabBoundarySet P = slabBoundarySet P := by
  have hbase := Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P
  have hc : P.commonPeriod +ᵥ frontier P.carrierBase = frontier P.carrierBase :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic
      P.carrierBase_periodic
  have hp (i : Fin P.numberOfParts) :
      P.commonPeriod +ᵥ frontier (P.partBase i) = frontier (P.partBase i) :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic
      (hbase.2.2.1 i)
  rw [slabBoundarySet]
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_union, Set.mem_iUnion]
  have hcm (x : ℝ) :
      (-P.commonPeriod +ᵥ x ∈ frontier P.carrierBase) ↔
        x ∈ frontier P.carrierBase := by
    constructor
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier P.carrierBase := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa only [neg_add_cancel] using hx
      simpa only [hc] using hx'
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier P.carrierBase := by
        simpa only [hc] using hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa only [neg_add_cancel] using hx'
  have hpm (i : Fin P.numberOfParts) (x : ℝ) :
      (-P.commonPeriod +ᵥ x ∈ frontier (P.partBase i)) ↔
        x ∈ frontier (P.partBase i) := by
    constructor
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier (P.partBase i) := by
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa only [neg_add_cancel] using hx
      simpa only [hp i] using hx'
    · intro hx
      have hx' : x ∈ P.commonPeriod +ᵥ frontier (P.partBase i) := by
        simpa only [hp i] using hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa only [neg_add_cancel] using hx'
  constructor
  · rintro (hx | ⟨i, hx⟩)
    · exact Or.inl (hcm x |>.mp hx)
    · exact Or.inr ⟨i, hpm i x |>.mp hx⟩
  · rintro (hx | ⟨i, hx⟩)
    · exact Or.inl (hcm x |>.mpr hx)
    · exact Or.inr ⟨i, hpm i x |>.mpr hx⟩

private theorem interval_disjoint_boundary
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S}
    {E : Tiling.AxisParallel.OneDimensional.PeriodicIntEnumeration
      (slabBoundarySet P) P.commonPeriod}
    (j : ℤ) :
    Disjoint (Ioo (E.point j) (E.point (j + 1))) (slabBoundarySet P) := by
  rw [Set.disjoint_left]
  intro x hxI hxE
  obtain ⟨k, hk⟩ := E.point_range.symm ▸ hxE
  have hleft : E.point j < E.point k := by simpa [hk] using hxI.1
  have hright : E.point k < E.point (j + 1) := by simpa [hk] using hxI.2
  have hjk : j < k := by
    by_contra hnot
    have hle : k ≤ j := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact (not_lt_of_ge (E.point_strictMono.monotone hlt.le)) hleft
    · exact (lt_irrefl _ hleft)
  have hsucc : j + 1 ≤ k := by omega
  exact (not_lt_of_ge (E.point_strictMono.monotone hsucc)) hright

private theorem interval_part_or_outside
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S}
    {E : Tiling.AxisParallel.OneDimensional.PeriodicIntEnumeration
      (slabBoundarySet P) P.commonPeriod}
    (j : ℤ) :
    (∃ i : Fin P.numberOfParts,
      Ioo (E.point j) (E.point (j + 1)) ⊆ P.partBase i) ∨
      Ioo (E.point j) (E.point (j + 1)) ⊆ P.carrierBaseᶜ := by
  let I := Ioo (E.point j) (E.point (j + 1))
  have hbase := Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P
  have hcarrierFront : Disjoint I (frontier P.carrierBase) := by
    apply Set.disjoint_of_subset_right (frontier_subset_slabBoundary P)
    exact interval_disjoint_boundary j
  have hcarrier :=
    Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hcarrierFront
  rcases hcarrier with hcarrier | hout
  · have hcarrier' : I ⊆ P.carrierBase := by
      simpa only [I, P.carrierBase_open.interior_eq] using hcarrier
    by_contra hnone
    have hnone' : ¬ ∃ i : Fin P.numberOfParts, I ⊆ P.partBase i := by
      intro h
      exact hnone (Or.inl h)
    have hpartChoice (i : Fin P.numberOfParts) :
        I ⊆ (P.partBase i)ᶜ := by
      have hfront : Disjoint I (frontier (P.partBase i)) := by
        apply Set.disjoint_of_subset_right (part_frontier_subset_slabBoundary P i)
        exact interval_disjoint_boundary j
      rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
          isPreconnected_Ioo hfront with hi | hi
      · exfalso
        exact hnone' ⟨i, by simpa only [I, P.partBase_open i |>.interior_eq] using hi⟩
      · exact hi.trans interior_subset
    have hIpos : 0 < MeasureTheory.volume I := by
      rw [Real.volume_Ioo]
      have hj : j < j + 1 := by omega
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (E.point_strictMono hj))
    have hmeasure :=
      congrArg (fun μ : MeasureTheory.Measure ℝ => μ I) P.partBase_ae_partition
    have hI : MeasurableSet I := by
      dsimp [I]
      exact measurableSet_Ioo
    have hleft : MeasureTheory.volume I = MeasureTheory.volume (I ∩ P.carrierBase) := by
      rw [inter_eq_left.mpr hcarrier']
    have hright :
        (∑ i, MeasureTheory.volume (I ∩ P.partBase i)) = 0 := by
      rw [Finset.sum_eq_zero]
      intro i hi
      have hempty : I ∩ P.partBase i = ∅ := by
        ext x
        constructor
        · intro hx
          exact (hpartChoice i hx.1) hx.2
        · intro hx
          simp at hx
      rw [hempty]
      exact measure_empty
    simp only [Measure.coe_finsetSum, Finset.sum_apply] at hmeasure
    simp_rw [Measure.restrict_apply hI] at hmeasure
    rw [hright] at hmeasure
    exact hIpos.ne' (hleft.trans hmeasure)
  · exact Or.inr (hout.trans interior_subset)

private theorem part_interval_unique
    {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S}
    {E : Tiling.AxisParallel.OneDimensional.PeriodicIntEnumeration
      (slabBoundarySet P) P.commonPeriod}
    {j : ℤ} {i k : Fin P.numberOfParts}
    (hi : Ioo (E.point j) (E.point (j + 1)) ⊆ P.partBase i)
    (hk : Ioo (E.point j) (E.point (j + 1)) ⊆ P.partBase k) :
    i = k := by
  by_contra hik
  have hd :=
    (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).2.1 i k hik
  have hj : j < j + 1 := by omega
  obtain ⟨x, hx⟩ := nonempty_Ioo.mpr (E.point_strictMono hj)
  exact Set.disjoint_left.mp hd (hi hx) (hk hx)

private theorem periodicSlabCode_exists :
    ∀ {K : Tiling.AxisParallel.Region} {S : Set Tiling.Plane}
      (P : FiniteSlabPartition K S),
    (slabBoundarySet P).Nonempty → Nonempty (PeriodicSlabCode P) := by
  intro K S P hE
  let E := slabBoundarySet P
  let p := P.commonPeriod
  classical
  have hp : 0 < p := P.commonPeriod_pos
  have hperiod : p +ᵥ E = E := by
    exact slabBoundary_periodic P
  have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite := by
    intro Q hQ
    exact slabBoundary_bounded_finite P Q hQ
  obtain ⟨enum⟩ :=
    Tiling.AxisParallel.OneDimensional.periodicIntEnumeration_exists E p hp hE hlocal
      hperiod
  let n := enum.count
  have hn : 0 < n := enum.count_pos
  let q : ℤ := Int.ofNat n
  have hboundary_shift (j : ℤ) :
      enum.point (j + q) = enum.point j + p := by
    exact enum.point_period j
  have hinterval_shift (j : ℤ) (x : ℝ) :
      x ∈ Ioo (enum.point j) (enum.point (j + 1)) ↔
        x + p ∈ Ioo (enum.point (j + q)) (enum.point (j + q + 1)) := by
    have h0 := hboundary_shift j
    have h1 : enum.point (j + q + 1) = enum.point (j + 1) + p := by
      have ht := hboundary_shift (j + 1)
      convert ht using 1
      ring_nf
    rw [h0, h1]
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  have hperiod_mem (B : Set ℝ) (hB : p +ᵥ B = B) (x : ℝ) :
      x ∈ B ↔ x + p ∈ B := by
    constructor
    · intro hx
      have hx' : p + x ∈ p +ᵥ B := ⟨x, hx, rfl⟩
      rw [hB] at hx'
      simpa [add_comm] using hx'
    · intro hx
      have hx' : x + p ∈ p +ᵥ B := by simpa [hB] using hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa [sub_eq_add_neg, add_assoc] using hx'
  have hpart_period (i : Fin P.numberOfParts) :
      p +ᵥ P.partBase i = P.partBase i := by
    simpa [p] using
      (Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P).2.2.1 i
  have hshiftPart (j : ℤ) (i : Fin P.numberOfParts)
      (hi : Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i) :
      Ioo (enum.point (j + q)) (enum.point (j + q + 1)) ⊆ P.partBase i := by
    intro x hx
    have hxm : x - p ∈ Ioo (enum.point j) (enum.point (j + 1)) := by
      apply (hinterval_shift j (x - p)).mpr
      simpa [sub_add_cancel] using hx
    simpa [sub_add_cancel] using
      (hperiod_mem (P.partBase i) (hpart_period i) (x - p)).mp (hi hxm)
  have hshiftPart_back (j : ℤ) (i : Fin P.numberOfParts)
      (hi : Ioo (enum.point (j + q)) (enum.point (j + q + 1)) ⊆ P.partBase i) :
      Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i := by
    intro x hx
    have hxp : x + p ∈ Ioo (enum.point (j + q)) (enum.point (j + q + 1)) :=
      (hinterval_shift j x).mp hx
    exact (hperiod_mem (P.partBase i) (hpart_period i) x).mpr
      (hi hxp)
  have hExists (j : ℤ) :
      (∃ i : Fin P.numberOfParts,
        Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i) ↔
      (∃ i : Fin P.numberOfParts,
        Ioo (enum.point (j + q)) (enum.point (j + q + 1)) ⊆ P.partBase i) := by
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, hshiftPart j i hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, hshiftPart_back j i hi⟩
  let label : ℤ → Option (Fin P.numberOfParts) := fun j ↦
    if h : ∃ i : Fin P.numberOfParts,
        Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i then
      some (Classical.choose h)
    else none
  have hlabel_part (j : ℤ) (i : Fin P.numberOfParts) :
      label j = some i ↔
        Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i := by
    constructor
    · intro hj
      by_cases h : ∃ k : Fin P.numberOfParts,
          Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase k
      · dsimp [label] at hj
        rw [dif_pos h] at hj
        have hchoose := Classical.choose_spec h
        have heq : Classical.choose h = i := Option.some.inj hj
        simpa [heq] using hchoose
      · dsimp [label] at hj
        rw [dif_neg h] at hj
        simp at hj
    · intro hi
      have h : ∃ k : Fin P.numberOfParts,
          Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase k := ⟨i, hi⟩
      dsimp [label]
      rw [dif_pos h]
      congr 1
      exact (part_interval_unique (P := P) (E := enum) (j := j) hi
        (Classical.choose_spec h)).symm
  have hlabel_none (j : ℤ) :
      label j = none ↔
        ¬ ∃ i : Fin P.numberOfParts,
          Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i := by
    dsimp [label]
    by_cases h : ∃ i : Fin P.numberOfParts,
        Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i <;>
      simp [h]
  have hlabel_outside (j : ℤ) :
      label j = none ↔
        Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.carrierBaseᶜ := by
    have hbase := Tiling.AxisParallel.Terminal.slabBases_literalAndCommonPeriodic P
    constructor
    · intro hj
      rcases interval_part_or_outside j with hpart | hout
      · obtain ⟨i, hi⟩ := hpart
        have hsome : label j = some i := (hlabel_part j i).mpr hi
        exact False.elim (by rw [hsome] at hj; simp at hj)
      · exact hout
    · intro hout
      apply hlabel_none j |>.2
      intro hpart
      obtain ⟨i, hi⟩ := hpart
      have hne : (Ioo (enum.point j) (enum.point (j + 1))).Nonempty :=
        nonempty_Ioo.mpr (enum.point_strictMono (by omega))
      obtain ⟨x, hx⟩ := hne
      exact hout hx (hbase.1 i (hi hx))
  have hlabel_period (j : ℤ) : label (j + q) = label j := by
    by_cases hjnone : label j = none
    · have hnone : ¬ ∃ i : Fin P.numberOfParts,
          Ioo (enum.point j) (enum.point (j + 1)) ⊆ P.partBase i :=
        (hlabel_none j).mp hjnone
      have hnoneShift : ¬ ∃ i : Fin P.numberOfParts,
          Ioo (enum.point (j + q)) (enum.point (j + q + 1)) ⊆ P.partBase i := by
        intro h
        exact hnone ((hExists j).mpr h)
      have hjnoneShift : label (j + q) = none := (hlabel_none (j + q)).mpr hnoneShift
      simp [hjnone, hjnoneShift]
    · cases hj : label j with
      | none => exact False.elim (hjnone hj)
      | some i =>
        have hi := (hlabel_part j i).mp hj
        have hiShift := hshiftPart j i hi
        have hshiftSome : label (j + q) ≠ none := by
          intro hnone
          have hnone' := (hlabel_none (j + q)).mp hnone
          exact hnone' ⟨i, hiShift⟩
        cases hs : label (j + q) with
        | none => exact False.elim (hshiftSome hs)
        | some k =>
          have hk := (hlabel_part (j + q) k).mp hs
          have hki := part_interval_unique hk hiShift
          simp [hki]
  refine ⟨⟨n, hn, enum.point, enum.point_strictMono, ?_, ?_, label, ?_, ?_, ?_⟩⟩
  · simpa [E] using enum.point_range
  · simpa [n, q] using enum.point_period
  · intro j i
    simpa [E, n, q] using hlabel_part j i
  · intro j
    simpa [E, n, q] using hlabel_outside j
  · intro j
    simpa [n, q] using hlabel_period j
end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Function
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private theorem periodGroup_vadd_iff_local {S : Set Plane} (a u : Plane) :
    u ∈ periodGroup (a +ᵥ S) ↔ u ∈ periodGroup S := by
  change u +ᵥ (a +ᵥ S) = a +ᵥ S ↔ u +ᵥ S = S
  rw [vadd_vadd]
  constructor
  · intro h
    have h' : a +ᵥ (u +ᵥ S) = a +ᵥ S := by
      calc
        a +ᵥ (u +ᵥ S) = (a + u) +ᵥ S := by rw [vadd_vadd]
        _ = (u + a) +ᵥ S := by rw [add_comm]
        _ = a +ᵥ S := h
    exact vadd_left_cancel a h'
  · intro h
    calc
      (u + a) +ᵥ S = (a + u) +ᵥ S := by rw [add_comm]
      _ = a +ᵥ (u +ᵥ S) := by rw [vadd_vadd]
      _ = a +ᵥ S := by rw [h]

private noncomputable def triangularLatticeLocal
    (alpha beta shear : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    PlanarLattice where
  basis := ![verticalPeriodVector alpha, skewPeriodVector beta shear]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro s t s' t' h
    have hre := congrArg Complex.re h
    have ht : t = t' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at hre
      exact hre.resolve_right hbeta.ne'
    subst t'
    have him := congrArg Complex.im h
    have hs : s = s' := by
      norm_num [verticalPeriodVector, skewPeriodVector] at him
      exact him.resolve_right halpha.ne'
    exact ⟨hs, rfl⟩

private theorem triangularLatticeLocal_toAddSubgroup
    (alpha beta shear : ℝ) (halpha : 0 < alpha) (hbeta : 0 < beta) :
    (triangularLatticeLocal alpha beta shear halpha hbeta).toAddSubgroup =
      triangularPeriodSubgroup alpha beta shear := by
  apply le_antisymm
  · rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
      AddSubgroup.closure_le]
    rintro x ⟨i, rfl⟩
    change ![verticalPeriodVector alpha, skewPeriodVector beta shear] i ∈
      triangularPeriodSubgroup alpha beta shear
    fin_cases i
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  · intro x hx
    rcases hx with ⟨m, n, rfl⟩
    apply add_mem
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) m
      exact ⟨0, by simp [triangularLatticeLocal]⟩
    · apply AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure ?_) n
      exact ⟨1, by simp [triangularLatticeLocal]⟩

private theorem normalizedPartCentres_finiteOrbitRepresentatives
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    ∃ R : Finset Plane,
      (R : Set Plane) ⊆ N.normalizedPartCentres i ∧
      QuotientAddGroup.mk'
          (triangularLatticeLocal (P.verticalPeriod i) P.commonPeriod (P.shear i)
            (P.verticalPeriod_pos i) P.commonPeriod_pos).toAddSubgroup '' (R : Set Plane) =
        QuotientAddGroup.mk'
          (triangularLatticeLocal (P.verticalPeriod i) P.commonPeriod (P.shear i)
            (P.verticalPeriod_pos i) P.commonPeriod_pos).toAddSubgroup ''
          N.normalizedPartCentres i ∧
      Set.InjOn (QuotientAddGroup.mk'
          (triangularLatticeLocal (P.verticalPeriod i) P.commonPeriod (P.shear i)
            (P.verticalPeriod_pos i) P.commonPeriod_pos).toAddSubgroup) (R : Set Plane) := by
  let L := triangularLatticeLocal (P.verticalPeriod i) P.commonPeriod (P.shear i)
    (P.verticalPeriod_pos i) P.commonPeriod_pos
  have hlocal : ∀ Q : Set Plane, Bornology.IsBounded Q →
      (N.normalizedPartCentres i ∩ Q).Finite := by
    exact (IsPacking.locallyFinite_centres (N.normalized_part_tiles i).2.1).1
  have hv : verticalPeriodVector (P.verticalPeriod i) ∈
      periodGroup (N.normalizedPartCentres i) := by
    rw [N.normalizedPartCentres_eq i]
    apply (periodGroup_vadd_iff_local (-N.centreAnchor)
      (verticalPeriodVector (P.verticalPeriod i))).2
    exact P.part_vertical_period i
  have hs : skewPeriodVector P.commonPeriod (P.shear i) ∈
      periodGroup (N.normalizedPartCentres i) := by
    rw [N.normalizedPartCentres_eq i]
    apply (periodGroup_vadd_iff_local (-N.centreAnchor)
      (skewPeriodVector P.commonPeriod (P.shear i))).2
    exact P.part_skew_period i
  have hperiod : L.toAddSubgroup ≤ periodGroup (N.normalizedPartCentres i) := by
    rw [triangularLatticeLocal_toAddSubgroup _ _ _ (P.verticalPeriod_pos i)
      P.commonPeriod_pos]
    intro x hx
    rcases hx with ⟨m, n, rfl⟩
    exact add_mem (AddSubgroup.zsmul_mem _ hv m) (AddSubgroup.zsmul_mem _ hs n)
  simpa only [L] using
    Tiling.AxisParallel.exists_finiteOrbitRepresentatives_of_planarLattice L hlocal hperiod

private theorem normalizedPartCentres_representation
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    ∃ R : Finset Plane,
      (R : Set Plane) ⊆ N.normalizedPartCentres i ∧
      ∀ s ∈ N.normalizedPartCentres i, ∃ r,
        r ∈ (R : Set Plane) ∧ ∃ n : ℤ,
          s.re = r.re + (n : ℝ) * P.commonPeriod := by
  obtain ⟨R, hRsub, hRquot, _hRinj⟩ :=
    normalizedPartCentres_finiteOrbitRepresentatives N i
  let L := triangularLatticeLocal (P.verticalPeriod i) P.commonPeriod (P.shear i)
    (P.verticalPeriod_pos i) P.commonPeriod_pos
  refine ⟨R, hRsub, ?_⟩
  intro s hs
  have hsmem :
      QuotientAddGroup.mk' L.toAddSubgroup s ∈
        QuotientAddGroup.mk' L.toAddSubgroup '' N.normalizedPartCentres i :=
    ⟨s, hs, rfl⟩
  rw [← hRquot] at hsmem
  obtain ⟨r, hr, hquot⟩ := hsmem
  have hdiff : -r + s ∈ L.toAddSubgroup := by
    obtain ⟨z, hz, hrel⟩ := (QuotientAddGroup.mk'_eq_mk' _).mp hquot
    rw [← hrel]
    simpa using hz
  rw [triangularLatticeLocal_toAddSubgroup _ _ _ (P.verticalPeriod_pos i)
    P.commonPeriod_pos] at hdiff
  obtain ⟨m, n, hdiff_eq⟩ := hdiff
  have hrel' : s = r + (m • verticalPeriodVector (P.verticalPeriod i) +
      n • skewPeriodVector P.commonPeriod (P.shear i)) := by
    apply sub_eq_zero.mp
    rw [← hdiff_eq]
    abel
  have hre := congrArg Complex.re hrel'
  refine ⟨r, hr, n, ?_⟩
  simpa [verticalPeriodVector, skewPeriodVector, Complex.add_re] using hre

private theorem translatedVertexLevel_residue_finite
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    ∃ F : Finset ℝ, ∀ (v : N.context.region.vertices)
      (s : N.normalizedPartCentres i), ∃ f, f ∈ (F : Set ℝ) ∧ ∃ n : ℤ,
        (v.1 + (s.1 : Plane)).re = f + (n : ℝ) * P.commonPeriod := by
  obtain ⟨R, hRsub, hrepr⟩ := normalizedPartCentres_representation N i
  let V := N.context.region.vertexFinset
  let F : Finset ℝ := (V.product R).image fun vr ↦ (vr.1 + vr.2).re
  refine ⟨F, ?_⟩
  intro v s
  have hvV : (v.1 : Plane) ∈ (V : Set Plane) := by
    rw [N.context.region.coe_vertexFinset]
    exact v.2
  have hvs : ∃ r, r ∈ (R : Set Plane) ∧ ∃ n : ℤ,
      s.1.re = r.re + (n : ℝ) * P.commonPeriod := hrepr s.1 s.2
  obtain ⟨r, hr, n, hsr⟩ := hvs
  have hmem : (v.1, r) ∈ V.product R := by
    exact Finset.mem_product.mpr ⟨hvV, hr⟩
  refine ⟨(v.1 + r).re, ?_, n, ?_⟩
  · exact Finset.mem_image.mpr ⟨(v.1, r), hmem, rfl⟩
  · calc
      (v.1 + (s.1 : Plane)).re = v.1.re + s.1.re := by
        simp only [Complex.add_re]
      _ = v.1.re + (r.re + (n : ℝ) * P.commonPeriod) := by rw [hsr]
      _ = (v.1.re + r.re) + (n : ℝ) * P.commonPeriod := by ring
      _ = (v.1 + r).re + (n : ℝ) * P.commonPeriod := by
        rw [Complex.add_re]

private theorem normalizedPartCentres_iUnion_eq_contextCentres
  {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    (⋃ i, N.normalizedPartCentres i) = N.context.centres := by
  rw [N.context_centres]
  ext x
  constructor
  · intro hx
    rw [Set.mem_iUnion] at hx
    obtain ⟨i, hi⟩ := hx
    rw [N.normalizedPartCentres_eq i] at hi
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hi
    have hyS : y ∈ S := by
      rw [← P.partCentres_union]
      exact Set.mem_iUnion.mpr ⟨i, hy⟩
    exact Set.mem_vadd_set.mpr ⟨y, hyS, hxy⟩
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hx
    have hyParts : y ∈ ⋃ i, P.partCentres i := by
      rw [P.partCentres_union]
      exact hy
    rw [Set.mem_iUnion] at hyParts
    obtain ⟨i, hi⟩ := hyParts
    rw [Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [N.normalizedPartCentres_eq i]
    exact Set.mem_vadd_set.mpr ⟨y, hi, hxy⟩

private def translatedVertexLevelsLocal
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) : Set ℝ :=
  {x | ∃ v : N.context.region.vertices, ∃ s : N.context.centres,
    x = (v.1 + (s.1 : Plane)).re}

private theorem translatedVertexLevelsLocal_periodic
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    P.commonPeriod +ᵥ translatedVertexLevelsLocal N =
      translatedVertexLevelsLocal N := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨v, s, rfl⟩ := hy
    have hsUnion : s.1 ∈ ⋃ i, N.normalizedPartCentres i := by
      rw [normalizedPartCentres_iUnion_eq_contextCentres N]
      exact s.2
    rw [Set.mem_iUnion] at hsUnion
    obtain ⟨i, hsi⟩ := hsUnion
    have hperiod : skewPeriodVector P.commonPeriod (P.shear i) ∈
        periodGroup (N.normalizedPartCentres i) := by
      rw [N.normalizedPartCentres_eq i]
      apply (periodGroup_vadd_iff_local (-N.centreAnchor)
        (skewPeriodVector P.commonPeriod (P.shear i))).2
      exact P.part_skew_period i
    have hshift : (s.1 : Plane) + skewPeriodVector P.commonPeriod (P.shear i) ∈
        N.normalizedPartCentres i := by
      have heq := (periodGroup_isAddSubgroup _ _).mp hperiod
      apply heq ▸ Set.mem_vadd_set.mpr ⟨s.1, hsi, ?_⟩
      simp [vadd_eq_add, add_comm]
    refine ⟨v, ⟨s.1 + skewPeriodVector P.commonPeriod (P.shear i), ?_⟩, ?_⟩
    · have hU : (s.1 : Plane) + skewPeriodVector P.commonPeriod (P.shear i) ∈
          ⋃ j, N.normalizedPartCentres j := Set.mem_iUnion.mpr ⟨i, hshift⟩
      exact (congrArg (fun T : Set Plane ↦
        (s.1 : Plane) + skewPeriodVector P.commonPeriod (P.shear i) ∈ T)
        (normalizedPartCentres_iUnion_eq_contextCentres N)).mp hU
    · rw [← hxy]
      change P.commonPeriod + (v.1 + (s.1 : Plane)).re =
        (v.1 + (s.1 + skewPeriodVector P.commonPeriod (P.shear i))).re
      rw [Complex.add_re, Complex.add_re]
      simp [skewPeriodVector]
      ring
  · intro hx
    have hminus : -P.commonPeriod +ᵥ translatedVertexLevelsLocal N ⊆
        translatedVertexLevelsLocal N := by
      intro z hz
      obtain ⟨y, hy, hzy⟩ := hz
      obtain ⟨v, s, rfl⟩ := hy
      have hsUnion : s.1 ∈ ⋃ i, N.normalizedPartCentres i := by
        rw [normalizedPartCentres_iUnion_eq_contextCentres N]
        exact s.2
      rw [Set.mem_iUnion] at hsUnion
      obtain ⟨i, hsi⟩ := hsUnion
      have hperiod : skewPeriodVector P.commonPeriod (P.shear i) ∈
          periodGroup (N.normalizedPartCentres i) := by
        rw [N.normalizedPartCentres_eq i]
        apply (periodGroup_vadd_iff_local (-N.centreAnchor)
          (skewPeriodVector P.commonPeriod (P.shear i))).2
        exact P.part_skew_period i
      have hshift : (s.1 : Plane) - skewPeriodVector P.commonPeriod (P.shear i) ∈
          N.normalizedPartCentres i := by
        have hneg := (periodGroup_isAddSubgroup _ _).mp hperiod
        have hneg' := (periodGroup_isAddSubgroup _ _).mp (neg_mem hperiod)
        apply hneg' ▸ Set.mem_vadd_set.mpr ⟨s.1, hsi, ?_⟩
        simp [vadd_eq_add, sub_eq_add_neg, add_comm]
      refine ⟨v, ⟨s.1 - skewPeriodVector P.commonPeriod (P.shear i), ?_⟩, ?_⟩
      · have hU : (s.1 : Plane) - skewPeriodVector P.commonPeriod (P.shear i) ∈
            ⋃ j, N.normalizedPartCentres j := Set.mem_iUnion.mpr ⟨i, hshift⟩
        exact (congrArg (fun T : Set Plane ↦
          (s.1 : Plane) - skewPeriodVector P.commonPeriod (P.shear i) ∈ T)
          (normalizedPartCentres_iUnion_eq_contextCentres N)).mp hU
      · rw [← hzy]
        change -P.commonPeriod + (v.1 + (s.1 : Plane)).re =
          (v.1 + (s.1 - skewPeriodVector P.commonPeriod (P.shear i))).re
        rw [Complex.add_re, Complex.add_re]
        simp [skewPeriodVector]
        linarith
    have hinput : x - P.commonPeriod ∈
        -P.commonPeriod +ᵥ translatedVertexLevelsLocal N := by
      refine ⟨x, hx, ?_⟩
      dsimp
      rw [sub_eq_add_neg, add_comm]
    have hz := hminus hinput
    refine ⟨x - P.commonPeriod, hz, ?_⟩
    dsimp
    rw [sub_eq_add_neg]
    ring

private theorem translatedVertexLevelsLocal_residue_finite
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    ∃ F : Finset ℝ, ∀ x ∈ translatedVertexLevelsLocal N,
      ∃ f, f ∈ (F : Set ℝ) ∧ ∃ n : ℤ,
        x = f + (n : ℝ) * P.commonPeriod := by
  classical
  let Fs : Fin P.numberOfParts → Finset ℝ := fun i ↦
    Classical.choose (translatedVertexLevel_residue_finite N i)
  have hFs (i : Fin P.numberOfParts) :
      ∀ (v : N.context.region.vertices) (s : N.normalizedPartCentres i),
        ∃ f, f ∈ (Fs i : Set ℝ) ∧ ∃ n : ℤ,
          (v.1 + (s.1 : Plane)).re = f + (n : ℝ) * P.commonPeriod :=
    fun v s ↦ Classical.choose_spec (translatedVertexLevel_residue_finite N i) v s
  let F : Finset ℝ := Finset.univ.biUnion Fs
  refine ⟨F, ?_⟩
  intro x hx
  obtain ⟨v, s, rfl⟩ := hx
  have hsUnion : s.1 ∈ ⋃ i, N.normalizedPartCentres i := by
    rw [normalizedPartCentres_iUnion_eq_contextCentres N]
    exact s.2
  rw [Set.mem_iUnion] at hsUnion
  obtain ⟨i, hsi⟩ := hsUnion
  obtain ⟨f, hf, n, hlevel⟩ := hFs i v ⟨s.1, hsi⟩
  refine ⟨f, ?_, n, hlevel⟩
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hf⟩

private theorem finite_arithmetic_translates_inter_bounded
    {F : Finset ℝ} {p : ℝ} (hp : 0 < p)
    (Q : Set ℝ) (hQ : Bornology.IsBounded Q) :
    ({x : ℝ | ∃ f ∈ (F : Set ℝ), ∃ n : ℤ,
      x = f + (n : ℝ) * p} ∩ Q).Finite := by
  classical
  obtain ⟨R, hQR⟩ := hQ.subset_closedBall (0 : ℝ)
  let A : ℝ → Set ℤ := fun f ↦
    {n | f + (n : ℝ) * p ∈ Q}
  have hAfin (f : ℝ) : (A f).Finite := by
    have hAsub : A f ⊆ Set.Icc
        (Int.ceil ((-R - f) / p)) (Int.floor ((R - f) / p)) := by
      intro n hn
      have hball : f + (n : ℝ) * p ∈ Metric.closedBall (0 : ℝ) R :=
        hQR hn
      have habs : |f + (n : ℝ) * p| ≤ R := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hball
      have hlow : (-R - f) / p ≤ (n : ℝ) := by
        apply (div_le_iff₀ hp).2
        linarith [((abs_le.mp habs).1)]
      have hupp : (n : ℝ) ≤ (R - f) / p := by
        apply (le_div_iff₀ hp).2
        linarith [((abs_le.mp habs).2)]
      exact ⟨(Int.ceil_le).2 hlow, (Int.le_floor).2 hupp⟩
    exact (Set.finite_Icc _ _).subset hAsub
  let B : Finset ℝ := F.biUnion fun f ↦
    (Finset.Icc (Int.ceil ((-R - f) / p)) (Int.floor ((R - f) / p))).image
      (fun n : ℤ ↦ f + (n : ℝ) * p)
  exact B.finite_toSet.subset (by
    rintro x ⟨⟨f, hf, n, rfl⟩, hxQ⟩
    have hball : f + (n : ℝ) * p ∈ Metric.closedBall (0 : ℝ) R := hQR hxQ
    have habs : |f + (n : ℝ) * p| ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hball
    have hlow : (-R - f) / p ≤ (n : ℝ) := by
      apply (div_le_iff₀ hp).2
      linarith [((abs_le.mp habs).1)]
    have hupp : (n : ℝ) ≤ (R - f) / p := by
      apply (le_div_iff₀ hp).2
      linarith [((abs_le.mp habs).2)]
    have hnIcc : n ∈ Finset.Icc
        (Int.ceil ((-R - f) / p)) (Int.floor ((R - f) / p)) :=
      by
        simp only [Finset.mem_Icc]
        exact ⟨(Int.ceil_le).2 hlow, (Int.le_floor).2 hupp⟩
    exact Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_image.mpr ⟨n, hnIcc, rfl⟩⟩)

private theorem translatedVertexLevelsLocal_locallyFinite
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (translatedVertexLevelsLocal N ∩ Q).Finite := by
  intro Q hQ
  have hres := translatedVertexLevelsLocal_residue_finite N
  obtain ⟨F, hF⟩ := hres
  exact (finite_arithmetic_translates_inter_bounded P.commonPeriod_pos Q hQ).subset (by
      intro x hx
      obtain ⟨f, hf, n, hxn⟩ := hF x hx.1
      exact ⟨⟨f, hf, n, hxn⟩, hx.2⟩)

private theorem translatedVertexLevelsLocal_nonempty
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    (translatedVertexLevelsLocal N).Nonempty := by
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair N.context.region
  have hs : N.context.centres.Nonempty := by
    rw [N.context_centres]
    refine ⟨0, ?_⟩
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using N.centreAnchor_mem
  obtain ⟨s, hs⟩ := hs
  exact ⟨(v + (s : Plane)).re, ⟨⟨v, hv⟩, ⟨s, hs⟩, rfl⟩⟩

private theorem translatedVertexLevelsLocal_enumeration
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    Nonempty (PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod) :=
  periodicIntEnumeration_exists (translatedVertexLevelsLocal N) P.commonPeriod
    P.commonPeriod_pos (translatedVertexLevelsLocal_nonempty N)
    (translatedVertexLevelsLocal_locallyFinite N)
    (translatedVertexLevelsLocal_periodic N)

private theorem periodicEnumeration_point_intShift
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    (j q : ℤ) :
    E.point (j + q * Int.ofNat E.count) =
      E.point j + (q : ℝ) * P.commonPeriod := by
  refine Int.induction_on q ?_ ?_ ?_
  · simp
  · intro q ih
    rw [show j + (q + 1) * Int.ofNat E.count =
      (j + q * Int.ofNat E.count) + Int.ofNat E.count by ring]
    rw [E.point_period, ih]
    push_cast
    ring
  · intro q ih
    have hp := E.point_period
      (j + (- (q : ℤ) - 1) * Int.ofNat E.count)
    rw [show (j + (- (q : ℤ) - 1) * Int.ofNat E.count) +
      Int.ofNat E.count = j + (- (q : ℤ)) * Int.ofNat E.count by ring] at hp
    have hqcast : ((-(q : ℤ) : ℤ) : ℝ) = -(q : ℝ) := by norm_num
    have hqcast2 : (((-(q : ℤ) - 1 : ℤ) : ℝ)) = -(q : ℝ) - 1 := by
      norm_num
    calc
      E.point (j + (- (q : ℤ) - 1) * Int.ofNat E.count) =
          E.point (j + (- (q : ℤ)) * Int.ofNat E.count) -
            P.commonPeriod := by linarith [hp]
      _ = (E.point j + (-(q : ℝ)) * P.commonPeriod) -
            P.commonPeriod := by rw [ih, hqcast]
      _ = E.point j + ((- (q : ℤ) - 1 : ℤ) : ℝ) *
            P.commonPeriod := by
        rw [hqcast2]
        ring

private theorem translatedVertexLevelsLocal_point_mem_coordinateSpace
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    (j : ℤ) : E.point j ∈ N.context.coordinateSpace := by
  have hrange : E.point j ∈ Set.range E.point := ⟨j, rfl⟩
  have hlevel : E.point j ∈ translatedVertexLevelsLocal N :=
    Eq.mp (congrArg (fun T : Set ℝ ↦ E.point j ∈ T) E.point_range) hrange
  obtain ⟨v, s, hvs⟩ := hlevel
  rw [hvs]
  exact N.context.coordinateSpace.add_mem
    (N.context.vertex_re_mem v.1 v.2) (N.context.centre_re_mem s.1 s.2)

private theorem periodicEnumeration_mappedPoint_intShift
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    (φ : N.context.coordinateSpace →ₗ[ℚ] ℚ) (j q : ℤ) :
    mapScalar φ
        ⟨E.point (j + q * Int.ofNat E.count),
          translatedVertexLevelsLocal_point_mem_coordinateSpace N E
            (j + q * Int.ofNat E.count)⟩ =
      mapScalar φ
          ⟨E.point j,
            translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩ +
        (q : ℝ) * mapScalar φ ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by
  let a : N.context.coordinateSpace :=
    ⟨E.point j, translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩
  let p : N.context.coordinateSpace := ⟨P.commonPeriod, N.commonPeriod_mem⟩
  have hcoord :
      (⟨E.point (j + q * Int.ofNat E.count),
        translatedVertexLevelsLocal_point_mem_coordinateSpace N E
          (j + q * Int.ofNat E.count)⟩ : N.context.coordinateSpace) =
        a + q • p := by
    apply Subtype.ext
    dsimp [a, p]
    change E.point (j + q * Int.ofNat E.count) =
      E.point j + q • P.commonPeriod
    simpa [smul_eq_mul] using periodicEnumeration_point_intShift E j q
  rw [hcoord]
  change ((φ (a + q • p) : ℚ) : ℝ) =
    ((φ a : ℚ) : ℝ) + (q : ℝ) * ((φ p : ℚ) : ℝ)
  rw [map_add, map_zsmul]
  norm_num

private def translatedVertexGapFinset
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod) :
    Finset N.context.coordinateSpace :=
  Finset.univ.image fun i : Fin E.count ↦
    ⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
      N.context.coordinateSpace.sub_mem
        (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
          (Int.ofNat i + 1))
        (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
          (Int.ofNat i))⟩

private theorem translatedVertexGapFinset_mem
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    {z : N.context.coordinateSpace} (hz : z ∈ translatedVertexGapFinset E) :
    ∃ i : Fin E.count,
      z.1 = E.point (Int.ofNat i + 1) - E.point (Int.ofNat i) := by
  simp only [translatedVertexGapFinset, Finset.mem_image, Finset.mem_univ, true_and] at hz
  obtain ⟨i, hi⟩ := hz
  exact ⟨i, (congrArg Subtype.val hi).symm⟩

private theorem translatedVertexGapFinset_source_pos
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    {z : N.context.coordinateSpace} (hz : z ∈ translatedVertexGapFinset E) :
    0 < (z : ℝ) := by
  obtain ⟨i, hi⟩ := translatedVertexGapFinset_mem E hz
  rw [hi]
  apply sub_pos.mpr
  apply E.point_strictMono
  omega

private theorem translatedVertexPeriod_and_gaps_mapped_pos_threshold
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (φ : N.context.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation N.context ε φ →
      0 < mapScalar φ ⟨P.commonPeriod, N.commonPeriod_mem⟩ ∧
      ∀ z ∈ translatedVertexGapFinset E, 0 < mapScalar φ z := by
  let periodZ : N.context.coordinateSpace :=
    ⟨P.commonPeriod, N.commonPeriod_mem⟩
  let Z : Finset N.context.coordinateSpace :=
    insert periodZ (translatedVertexGapFinset E)
  obtain ⟨ε, hε, hsign⟩ := approximation_preservesSign_finset N.context Z
  refine ⟨ε, hε, ?_⟩
  intro φ hφ
  have hperiodSign : Real.sign (mapScalar φ periodZ) = 1 := by
    rw [hsign φ hφ periodZ (Finset.mem_insert_self periodZ
      (translatedVertexGapFinset E))]
    exact Real.sign_of_pos P.commonPeriod_pos
  have hperiodPos : 0 < mapScalar φ periodZ := by
    by_contra hnot
    have hle : mapScalar φ periodZ ≤ 0 := le_of_not_gt hnot
    rcases lt_or_eq_of_le hle with hneg | hzero
    · rw [Real.sign_of_neg hneg] at hperiodSign
      norm_num at hperiodSign
    · rw [hzero, Real.sign_zero] at hperiodSign
      norm_num at hperiodSign
  refine ⟨hperiodPos, ?_⟩
  intro z hz
  have hsignpos : Real.sign (mapScalar φ z) = 1 := by
    rw [hsign φ hφ z (Finset.mem_insert_of_mem hz), Real.sign_of_pos
      (translatedVertexGapFinset_source_pos E hz)]
  by_contra hnot
  have hle : mapScalar φ z ≤ 0 := le_of_not_gt hnot
  rcases lt_or_eq_of_le hle with hneg | hzero
  · rw [Real.sign_of_neg hneg] at hsignpos
    norm_num at hsignpos
  · rw [hzero, Real.sign_zero] at hsignpos
    norm_num at hsignpos

private theorem translatedVertexGap_map_eq_sub
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    (φ : N.context.coordinateSpace →ₗ[ℚ] ℚ)
    (i : Fin E.count) :
    mapScalar φ
        ⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
          N.context.coordinateSpace.sub_mem
            (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
              (Int.ofNat i + 1))
            (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
              (Int.ofNat i))⟩ =
      mapScalar φ
        ⟨E.point (Int.ofNat i + 1),
          translatedVertexLevelsLocal_point_mem_coordinateSpace N E
            (Int.ofNat i + 1)⟩ -
      mapScalar φ
        ⟨E.point (Int.ofNat i),
          translatedVertexLevelsLocal_point_mem_coordinateSpace N E
            (Int.ofNat i)⟩ := by
  let a : N.context.coordinateSpace :=
    ⟨E.point (Int.ofNat i + 1),
      translatedVertexLevelsLocal_point_mem_coordinateSpace N E
        (Int.ofNat i + 1)⟩
  let b : N.context.coordinateSpace :=
    ⟨E.point (Int.ofNat i),
      translatedVertexLevelsLocal_point_mem_coordinateSpace N E
        (Int.ofNat i)⟩
  have hab :
      (⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
        N.context.coordinateSpace.sub_mem
          (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
            (Int.ofNat i + 1))
          (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
            (Int.ofNat i))⟩ :
        N.context.coordinateSpace) = a - b := by
    apply Subtype.ext
    rfl
  rw [hab]
  change ((φ (a - b) : ℚ) : ℝ) =
    ((φ a : ℚ) : ℝ) - ((φ b : ℚ) : ℝ)
  rw [map_sub]
  norm_num

private theorem translatedVertexMappedOrder_of_all_successor_steps
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod)
    (φ : N.context.coordinateSpace →ₗ[ℚ] ℚ)
    (hstep : ∀ j : ℤ,
      mapScalar φ
          ⟨E.point j,
            translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩ <
      mapScalar φ
          ⟨E.point (j + 1),
            translatedVertexLevelsLocal_point_mem_coordinateSpace N E (j + 1)⟩) :
    StrictMono (fun j : ℤ ↦
      mapScalar φ
        ⟨E.point j,
          translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩) :=
  strictMono_int_of_lt_succ hstep

private theorem translatedVertexMappedOrder_of_periodic_cycle
    {K : Region} {S : Set Plane} {P : FiniteSlabPartition K S}
    {N : NormalizedSlabData P}
    (E : PeriodicIntEnumeration (translatedVertexLevelsLocal N) P.commonPeriod) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (φ : N.context.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation N.context ε φ →
      StrictMono (fun j : ℤ ↦
        mapScalar φ
          ⟨E.point j,
            translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩) := by
  obtain ⟨ε, hε, hgood⟩ :=
    translatedVertexPeriod_and_gaps_mapped_pos_threshold E
  refine ⟨ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨hperiod, hgap⟩ := hgood φ hφ
  let n : ℤ := Int.ofNat E.count
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast E.count_pos
  let y : ℤ → ℝ := fun j ↦
    mapScalar φ
      ⟨E.point j,
        translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩
  let a : ℝ := mapScalar φ ⟨P.commonPeriod, N.commonPeriod_mem⟩
  have hperiod' (j : ℤ) : y (j + n) = y j + a := by
    simpa [y, a, n] using periodicEnumeration_mappedPoint_intShift E φ j 1
  let d : ℤ → ℝ := fun j ↦ y (j + 1) - y j
  have hdperiod (j : ℤ) : d (j + n) = d j := by
    dsimp [d]
    rw [show (j + n) + 1 = (j + 1) + n by ring,
      hperiod' (j + 1), hperiod' j]
    ring
  have hdshift (q j : ℤ) : d (j + q * n) = d j := by
    induction q using Int.induction_on with
    | zero => simp
    | @succ q ih =>
        rw [show j + (q + 1) * n = (j + q * n) + n by ring,
          hdperiod (j + q * n)]
        exact ih
    | @pred q ih =>
        rw [← hdperiod (j + (-(q : ℤ) - 1) * n)]
        convert ih using 1
        ring_nf
  have hsucc : ∀ j : ℤ, y j < y (j + 1) := by
    intro j
    let r : ℤ := j % n
    let q : ℤ := j / n
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg _ (ne_of_gt hn)
    have hrn : r < n := by
      dsimp [r]
      exact Int.emod_lt_of_pos _ hn
    let i : Fin E.count :=
      ⟨r.toNat, by
        have : r.toNat < n.toNat := (Int.toNat_lt hr0).2 hrn
        simpa [n] using this⟩
    have hir : (i : ℤ) = r := by
      change (r.toNat : ℤ) = r
      exact Int.toNat_of_nonneg hr0
    have hj : j = (i : ℤ) + q * n := by
      have hdecomp : r + n * q = j := by
        exact Int.emod_add_mul_ediv j n
      rw [← hdecomp, ← hir]
      ring
    have hdj : d j = d (i : ℤ) := by
      rw [hj, hdshift]
    have hfund' : 0 < d (i : ℤ) := by
      change 0 < y (Int.ofNat i + 1) - y (Int.ofNat i)
      let z : N.context.coordinateSpace :=
        ⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
          N.context.coordinateSpace.sub_mem
            (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
              (Int.ofNat i + 1))
            (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
              (Int.ofNat i))⟩
      have hz : z ∈ translatedVertexGapFinset E := by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      have hzpos : 0 < mapScalar φ z := hgap z hz
      have hmap := translatedVertexGap_map_eq_sub E φ i
      dsimp [z] at hzpos
      have hmap' : mapScalar φ
              ⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
                N.context.coordinateSpace.sub_mem
                  (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                    (Int.ofNat i + 1))
                  (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                    (Int.ofNat i))⟩ =
            mapScalar φ
              ⟨E.point (Int.ofNat i + 1),
                translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                  (Int.ofNat i + 1)⟩ -
              mapScalar φ
                ⟨E.point (Int.ofNat i),
                  translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                    (Int.ofNat i)⟩ := by
        simpa using hmap
      have hzpos' : 0 < mapScalar φ
          ⟨E.point (Int.ofNat i + 1) - E.point (Int.ofNat i),
            N.context.coordinateSpace.sub_mem
              (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                (Int.ofNat i + 1))
              (translatedVertexLevelsLocal_point_mem_coordinateSpace N E
                (Int.ofNat i))⟩ := by
        simpa using hzpos
      rw [hmap'] at hzpos'
      simpa [y] using hzpos'
    have hdpos : 0 < d j := by simpa [hdj] using hfund'
    exact sub_pos.mp hdpos
  exact translatedVertexMappedOrder_of_all_successor_steps E φ (by
    simpa [y] using hsucc)

private theorem translatedVertex_globalOrderThreshold :
    ∀ {K : Region} {S : Set Plane}
      {P : FiniteSlabPartition K S} (N : NormalizedSlabData P),
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation N.context epsilon phi →
        ∀ (v w : N.context.region.vertices) (s t : N.context.centres),
          ((v.1 + (s.1 : Plane)).re <
              (w.1 + (t.1 : Plane)).re ↔
            mapScalar phi ⟨(v.1 + (s.1 : Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem v.1 v.2)
                (N.context.centre_re_mem s.1 s.2)⟩ <
            mapScalar phi ⟨(w.1 + (t.1 : Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem w.1 w.2)
                (N.context.centre_re_mem t.1 t.2)⟩) := by
  intro K S P N
  obtain ⟨E⟩ := translatedVertexLevelsLocal_enumeration N
  obtain ⟨ε, hε, hmono⟩ := translatedVertexMappedOrder_of_periodic_cycle E
  refine ⟨ε, hε, ?_⟩
  intro φ hφ v w s t
  have hxlevel :
      (v.1 + (s.1 : Plane)).re ∈ translatedVertexLevelsLocal N := by
    exact ⟨v, s, rfl⟩
  have hylevel :
      (w.1 + (t.1 : Plane)).re ∈ translatedVertexLevelsLocal N := by
    exact ⟨w, t, rfl⟩
  have hxrange :
      (v.1 + (s.1 : Plane)).re ∈ Set.range E.point := by
    rw [E.point_range]
    exact hxlevel
  have hyrange :
      (w.1 + (t.1 : Plane)).re ∈ Set.range E.point := by
    rw [E.point_range]
    exact hylevel
  obtain ⟨j, hj⟩ := hxrange
  obtain ⟨k, hk⟩ := hyrange
  let ex : N.context.coordinateSpace :=
    ⟨E.point j, translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩
  let ey : N.context.coordinateSpace :=
    ⟨E.point k, translatedVertexLevelsLocal_point_mem_coordinateSpace N E k⟩
  let hx : N.context.coordinateSpace :=
    ⟨(v.1 + (s.1 : Plane)).re,
      N.context.coordinateSpace.add_mem
        (N.context.vertex_re_mem v.1 v.2)
        (N.context.centre_re_mem s.1 s.2)⟩
  let hy : N.context.coordinateSpace :=
    ⟨(w.1 + (t.1 : Plane)).re,
      N.context.coordinateSpace.add_mem
        (N.context.vertex_re_mem w.1 w.2)
        (N.context.centre_re_mem t.1 t.2)⟩
  have hex : ex = hx := by
    apply Subtype.ext
    exact hj
  have hey : ey = hy := by
    apply Subtype.ext
    exact hk
  have hsource :
      (v.1 + (s.1 : Plane)).re < (w.1 + (t.1 : Plane)).re ↔
        E.point j < E.point k := by
    rw [hj, hk]
  have hmap :
      mapScalar φ hx < mapScalar φ hy ↔
        mapScalar φ ex < mapScalar φ ey := by
    rw [← hex, ← hey]
  have hbridge :
      mapScalar φ ex < mapScalar φ ey ↔ j < k := by
    simpa [ex, ey] using (hmono φ hφ).lt_iff_lt
  exact hsource.trans ((E.point_strictMono.lt_iff_lt).trans
    (hbridge.symm.trans hmap.symm))

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private structure ExactFirstCoordinateSlabTransport
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ)
    (H : PeriodicTranslatedVertexHomeomorph N phi)
    (D : CoordinateDeformation N.context phi) where
  firstHomeomorph_eq : D.firstHomeomorph = H.homeomorph
  centreEmbedding : ↥N.context.centres ↪ Tiling.Plane
  centreEmbedding_apply : ∀ t, centreEmbedding t =
    mapFirstPoint phi (N.context.centrePoint t.1 t.2)
  deformedCentres : Set Tiling.Plane
  deformedCentres_eq : deformedCentres = deformedCenterCarrier centreEmbedding
  deformedPartCentres : Fin P.numberOfParts → Set Tiling.Plane
  deformedPartCentres_eq : ∀ i, deformedPartCentres i =
    deformedCenterCarrierOn centreEmbedding
      {t : ↥N.context.centres | (t : Tiling.Plane) ∈ N.normalizedPartCentres i}
  mappedCarrierBase : Set ℝ
  mappedCarrierBase_eq : mappedCarrierBase = H.homeomorph '' N.normalizedCarrierBase
  mappedPartBase : Fin P.numberOfParts → Set ℝ
  mappedPartBase_eq : ∀ i, mappedPartBase i =
    H.homeomorph '' N.normalizedPartBase i
  full_openUnion_image : D.firstPlanarHomeomorph ''
    openUnion N.context.region N.context.centres =
      openUnion D.firstRegion deformedCentres
  part_openUnion_image : ∀ i, D.firstPlanarHomeomorph ''
    openUnion N.context.region (N.normalizedPartCentres i) =
      openUnion D.firstRegion (deformedPartCentres i)
  full_support_image : regularSupport D.firstRegion deformedCentres =
    D.firstPlanarHomeomorph '' regularSupport N.context.region N.context.centres
  part_support_image : ∀ i,
    regularSupport D.firstRegion (deformedPartCentres i) =
      D.firstPlanarHomeomorph ''
        regularSupport N.context.region (N.normalizedPartCentres i)
  full_support_cylinder : regularSupport D.firstRegion deformedCentres =
    Complex.re ⁻¹' mappedCarrierBase
  part_support_cylinder : ∀ i,
    regularSupport D.firstRegion (deformedPartCentres i) =
      Complex.re ⁻¹' mappedPartBase i
  full_packing : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
    (D.firstRegion.toPolygonalRegion.placements deformedCentres)
  part_packing : ∀ i,
    Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
      (D.firstRegion.toPolygonalRegion.placements (deformedPartCentres i))
  full_tiles : TilesOn D.firstRegion deformedCentres
    (Complex.re ⁻¹' mappedCarrierBase)
  part_tiles : ∀ i, TilesOn D.firstRegion (deformedPartCentres i)
    (Complex.re ⁻¹' mappedPartBase i)

private structure SharedSlabApproximation
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} (N : NormalizedSlabData P) where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  phi : N.context.coordinateSpace →ₗ[ℚ] ℚ
  approximation : IsEpsilonApproximation N.context epsilon phi
  good : IsGoodApproximation N.context phi
  deformation : CoordinateDeformation N.context phi
  firstHomeomorph_translatedVertex_agreement :
    ∀ (v : N.context.region.vertices) (s : N.context.centres),
      deformation.firstHomeomorph ((v.1 + (s.1 : Tiling.Plane)).re) =
        (mapFirstPoint phi (N.context.vertexPoint v.1 v.2) +
          mapFirstPoint phi (N.context.centrePoint s.1 s.2)).re
  firstHomeomorph_period_equivariant : ∀ x : ℝ,
    deformation.firstHomeomorph (x + P.commonPeriod) =
      deformation.firstHomeomorph x +
        mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩
  rationalHorizontalPeriod : ℚ
  rationalHorizontalPeriod_pos : 0 < rationalHorizontalPeriod
  rationalHorizontalPeriod_eq :
    (rationalHorizontalPeriod : ℝ) =
      mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩
  boundary_agreement : ∀ (x : ℝ) (hx : x ∈ slabBoundarySet P),
    deformation.firstHomeomorph (x - (N.tileAnchor + N.centreAnchor).re) =
      mapScalar phi ⟨x - (N.tileAnchor + N.centreAnchor).re,
        N.normalizedBoundary_mem x hx⟩
  boundary_order : ∀ a ∈ slabBoundarySet P, ∀ b ∈ slabBoundarySet P,
    a < b →
      deformation.firstHomeomorph (a - (N.tileAnchor + N.centreAnchor).re) <
        deformation.firstHomeomorph (b - (N.tileAnchor + N.centreAnchor).re)
  translatedVertex_order :
    ∀ (v w : N.context.region.vertices) (s t : N.context.centres),
      ((v.1 + (s.1 : Tiling.Plane)).re <
          (w.1 + (t.1 : Tiling.Plane)).re ↔
        mapScalar phi
            ⟨(v.1 + (s.1 : Tiling.Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem v.1 v.2)
                (N.context.centre_re_mem s.1 s.2)⟩ <
          mapScalar phi
            ⟨(w.1 + (t.1 : Tiling.Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem w.1 w.2)
                (N.context.centre_re_mem t.1 t.2)⟩)

private structure FirstCoordinateSlabTransport
    {K : Region} {S : Set Tiling.Plane}
    {P : FiniteSlabPartition K S} {N : NormalizedSlabData P}
    (A : SharedSlabApproximation N) where
  centreEmbedding : ↥N.context.centres ↪ Tiling.Plane
  centreEmbedding_apply : ∀ t : ↥N.context.centres,
    centreEmbedding t = mapFirstPoint A.phi
      (N.context.centrePoint t.1 t.2)
  deformedCentres : Set Tiling.Plane
  deformedCentres_eq : deformedCentres = deformedCenterCarrier centreEmbedding
  deformedPartCentres : Fin P.numberOfParts → Set Tiling.Plane
  deformedPartCentres_eq : ∀ i,
    deformedPartCentres i = deformedCenterCarrierOn centreEmbedding
      {t : ↥N.context.centres |
        (t : Tiling.Plane) ∈ N.normalizedPartCentres i}
  deformedPartCentres_nonempty : ∀ i, (deformedPartCentres i).Nonempty
  deformedPartCentres_pairwise :
    Set.PairwiseDisjoint Set.univ deformedPartCentres
  deformedPartCentres_union : (⋃ i, deformedPartCentres i) = deformedCentres
  deformedCarrierBase : Set ℝ
  deformedCarrierBase_open : IsOpen deformedCarrierBase
  deformedCarrierBase_regular :
    interior (closure deformedCarrierBase) = deformedCarrierBase
  deformedCarrierBase_nonnull : volume deformedCarrierBase ≠ 0
  deformedPartBase : Fin P.numberOfParts → Set ℝ
  deformedPartBase_open : ∀ i, IsOpen (deformedPartBase i)
  deformedPartBase_regular : ∀ i,
    interior (closure (deformedPartBase i)) = deformedPartBase i
  deformedPartBase_nonnull : ∀ i, volume (deformedPartBase i) ≠ 0
  deformedPartBase_ae_disjoint :
    Set.PairwiseDisjoint Set.univ
      (fun i ↦ volume.restrict (deformedPartBase i))
  deformedPartBase_ae_partition :
    volume.restrict deformedCarrierBase =
      ∑ i, volume.restrict (deformedPartBase i)
  deformed_tiles : TilesOn A.deformation.firstRegion
    deformedCentres (Complex.re ⁻¹' deformedCarrierBase)
  deformed_support : regularSupport A.deformation.firstRegion
    deformedCentres = Complex.re ⁻¹' deformedCarrierBase
  deformed_part_tiles : ∀ i,
    TilesOn A.deformation.firstRegion (deformedPartCentres i)
      (Complex.re ⁻¹' deformedPartBase i)
  deformed_part_support : ∀ i,
    regularSupport A.deformation.firstRegion (deformedPartCentres i) =
      Complex.re ⁻¹' deformedPartBase i
  deformedCarrierBase_periodic :
    (A.rationalHorizontalPeriod : ℝ) +ᵥ deformedCarrierBase =
      deformedCarrierBase
  deformedPartBase_periodic : ∀ i,
    (A.rationalHorizontalPeriod : ℝ) +ᵥ deformedPartBase i =
      deformedPartBase i
  deformed_part_vertical_period : ∀ i,
    verticalPeriodVector (P.verticalPeriod i) ∈
      periodGroup (deformedPartCentres i)
  deformed_part_skew_period : ∀ i,
    skewPeriodVector (A.rationalHorizontalPeriod : ℝ) (P.shear i) ∈
      periodGroup (deformedPartCentres i)
  carrier_frontier_transport :
    frontier deformedCarrierBase =
      A.deformation.firstHomeomorph '' frontier N.normalizedCarrierBase
  part_frontier_transport : ∀ i,
    frontier (deformedPartBase i) =
      A.deformation.firstHomeomorph '' frontier (N.normalizedPartBase i)
  deformed_first_coordinates_rational :
    (∀ v ∈ A.deformation.firstRegion.vertices,
      ∃ q : ℚ, v.re = (q : ℝ)) ∧
    ∀ t ∈ deformedCentres, ∃ q : ℚ, t.re = (q : ℝ)

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private theorem regularSupport_image_of_openUnion_image
    (K L : Region) (S T : Set Tiling.Plane)
    (h : Tiling.Plane ≃ₜ Tiling.Plane)
    (hopen : h '' openUnion K S = openUnion L T) :
    regularSupport L T = h '' regularSupport K S := by
  rw [regularSupport, regularSupport, Tiling.Polygonal.regularSupport,
    Tiling.Polygonal.regularSupport, ← openUnion, ← openUnion, ← hopen]
  rw [← h.image_closure, ← h.image_interior]

/- Coverage is recovered from packing and the exact regular support.  In
particular, this does not assert that a general homeomorphism preserves null
sets. -/

private theorem tilesOn_of_countable_packing_regularSupport
    (K : Region) (S D : Set Tiling.Plane)
    (hcount : S.Countable)
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S))
    (hsupport : regularSupport K S = D) :
    TilesOn K S D := by
  refine ⟨hcount, hpacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpacking] with x hx
  constructor
  · intro hD
    have hr : x ∈ regularSupport K S := by simpa [hsupport] using hD
    have hu : x ∈ openUnion K S := by
      change openUnion K S x
      exact Eq.mp hx.symm hr
    rwa [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hu
  · intro hu
    have hu' : x ∈ openUnion K S := by
      rwa [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    have hr : x ∈ regularSupport K S := by
      change regularSupport K S x
      exact Eq.mp hx hu'
    simpa [hsupport] using hr

/- The mapped first-coordinate cylinder is exactly the planar image of the
source cylinder. -/

private theorem coordinateCylinder_image
    (hx : ℝ ≃ₜ ℝ) (X : Set ℝ) :
    Tiling.AxisParallel.Approximation.coordinateProductHomeomorph
          hx (Homeomorph.refl ℝ) '' (Complex.re ⁻¹' X) =
      Complex.re ⁻¹' (hx '' X) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Tiling.AxisParallel.Approximation.coordinateProductHomeomorph_apply]
    exact ⟨w.re, hw, by simp⟩
  · rintro ⟨x, hxX, hzx⟩
    refine ⟨⟨x, z.im⟩, hxX, ?_⟩
    rw [Tiling.AxisParallel.Approximation.coordinateProductHomeomorph_apply]
    apply Complex.ext
    · simpa using hzx
    · simp

/- Exact proof-private copies of the frozen inputs used by the constructor. -/

private theorem centreEmbedding_exists
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ)
    (H : PeriodicTranslatedVertexHomeomorph N phi) :
    ∃ E : ↥N.context.centres ↪ Tiling.Plane,
      ∀ t, E t = mapFirstPoint phi (N.context.centrePoint t.1 t.2) := by
  let f : ↥N.context.centres → Tiling.Plane := fun t ↦
    mapFirstPoint phi (N.context.centrePoint t.1 t.2)
  have hf : Function.Injective f := by
    intro s t hst
    dsimp [f] at hst
    let v : N.context.region.vertices :=
      ⟨0, N.context.zero_mem_vertices⟩
    have him : s.1.im = t.1.im := by
      have h := congrArg Complex.im hst
      simpa [f, mapFirstPoint, ApproximationContext.centrePoint] using h
    have hH : H.homeomorph ((v.1 + (s.1 : Tiling.Plane)).re) =
        H.homeomorph ((v.1 + (t.1 : Tiling.Plane)).re) := by
      rw [H.translatedVertex_agreement v s,
        H.translatedVertex_agreement v t, hst]
    have hre : s.1.re = t.1.re := by
      have := H.homeomorph.injective hH
      simpa [v] using this
    apply Subtype.ext
    apply Complex.ext <;> assumption
  exact ⟨⟨f, hf⟩, fun _ ↦ rfl⟩

private theorem normalizedCarrier_sourceSupport
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    regularSupport N.context.region N.context.centres =
      Complex.re ⁻¹' N.normalizedCarrierBase := by
  apply regularSupport_eq_of_tilesOn
  · rw [N.normalizedCarrierBase_eq]
    exact (P.carrierBase_open.vadd _).preimage Complex.continuous_re
  · rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      N.normalizedCarrierBase_eq, closure_vadd, interior_vadd,
      P.carrierBase_regular]
  · have htarget : N.context.target = Complex.re ⁻¹' N.normalizedCarrierBase := by
      rw [normalized_carrier_target_eq N]
      rfl
    rw [← htarget]
    exact N.context_tiles

private theorem normalizedPart_sourceSupport
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    regularSupport N.context.region (N.normalizedPartCentres i) =
      Complex.re ⁻¹' N.normalizedPartBase i := by
  apply regularSupport_eq_of_tilesOn
  · rw [N.normalizedPartBase_eq]
    exact ((P.partBase_open i).vadd _).preimage Complex.continuous_re
  · rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      N.normalizedPartBase_eq, closure_vadd, interior_vadd,
      P.partBase_regular]
  · exact N.normalized_part_tiles i

private theorem openUnion_image_of_placedTile_images
    {K L : Region} {C : Set Tiling.Plane}
    (h : Tiling.Plane ≃ₜ Tiling.Plane)
    (E : ↥C ↪ Tiling.Plane)
    (A : Set Tiling.Plane) (hA : A ⊆ C)
    (hplaced : ∀ s : ↥C,
      h '' ((s.1 : Tiling.Plane) +ᵥ K.openCarrier) =
        E s +ᵥ L.openCarrier) :
    h '' openUnion K A =
      openUnion L (deformedCenterCarrierOn E
        {s : ↥C | (s : Tiling.Plane) ∈ A}) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hw
    obtain ⟨s, hws⟩ := hw
    let sC : C := ⟨s.1, hA s.2⟩
    have himage : h w ∈ E sC +ᵥ L.openCarrier := by
      rw [← hplaced sC]
      exact ⟨w, hws, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨E sC, ⟨sC, ?_, rfl⟩⟩, himage⟩
    exact s.2
  · rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    rintro ⟨e, he⟩
    obtain ⟨s, hsA, hse⟩ := e.2
    rw [← hse] at he
    rw [← hplaced s] at he
    obtain ⟨w, hw, rfl⟩ := he
    refine ⟨w, ?_, rfl⟩
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s.1, hsA⟩, hw⟩

private theorem packing_of_placedTile_images
    {K L : Region} {C : Set Tiling.Plane}
    (h : Tiling.Plane ≃ₜ Tiling.Plane)
    (E : ↥C ↪ Tiling.Plane)
    (A : Set Tiling.Plane) (_hA : A ⊆ C)
    (hsource : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A))
    (hplaced : ∀ s : ↥C,
      h '' ((s.1 : Tiling.Plane) +ᵥ K.openCarrier) =
        E s +ᵥ L.openCarrier) :
    Tiling.IsPacking L.toPolygonalRegion.prototileFamily
      (L.toPolygonalRegion.placements
        (deformedCenterCarrierOn E {s : ↥C | (s : Tiling.Plane) ∈ A})) := by
  apply (isPacking_iff_openCarrier_disjoint L _).mpr
  intro a ha b hb hab
  obtain ⟨s, hsA, hsa⟩ := ha
  obtain ⟨t, htA, htb⟩ := hb
  subst a
  subst b
  have hst : s ≠ t := by
    intro h
    apply hab
    exact congrArg E h
  have hsourceDisjoint :=
    (isPacking_iff_openCarrier_disjoint K A).mp hsource hsA htA
      (fun h ↦ hst (Subtype.ext h))
  change Disjoint (E s +ᵥ L.openCarrier) (E t +ᵥ L.openCarrier)
  rw [← hplaced s, ← hplaced t]
  rw [Set.disjoint_left]
  rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have : x = y := h.injective hxy.symm
  exact Set.disjoint_left.mp hsourceDisjoint hx (this ▸ hy)

private theorem exactFirstCoordinateSlabTransport_exists :
    ∀ {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
      (N : NormalizedSlabData P)
      (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ)
      (H : PeriodicTranslatedVertexHomeomorph N phi)
      (D : CoordinateDeformation N.context phi),
    D.firstHomeomorph = H.homeomorph →
      Nonempty (ExactFirstCoordinateSlabTransport N phi H D) := by
  intro K S P N phi H D hDH
  obtain ⟨E, hE⟩ := centreEmbedding_exists N phi H
  let dC : Set Tiling.Plane := deformedCenterCarrier E
  let dP : Fin P.numberOfParts → Set Tiling.Plane := fun i ↦
    deformedCenterCarrierOn E
      {t : ↥N.context.centres | (t : Tiling.Plane) ∈ N.normalizedPartCentres i}
  let mC : Set ℝ := H.homeomorph '' N.normalizedCarrierBase
  let mP : Fin P.numberOfParts → Set ℝ := fun i ↦
    H.homeomorph '' N.normalizedPartBase i
  have hplaced (s : N.context.centres) :
      D.firstPlanarHomeomorph ''
          ((s.1 : Tiling.Plane) +ᵥ N.context.region.openCarrier) =
        E s +ᵥ D.firstRegion.openCarrier := by
    rw [hE]
    exact placedTile_firstHomeomorph_image N phi H D hDH s
  have hopenFull : D.firstPlanarHomeomorph ''
      openUnion N.context.region N.context.centres =
        openUnion D.firstRegion dC := by
    simpa [dC, deformedCenterCarrier, deformedCenterCarrierOn] using
      openUnion_image_of_placedTile_images D.firstPlanarHomeomorph E
        N.context.centres (fun _ h ↦ h) hplaced
  have hopenPart (i : Fin P.numberOfParts) : D.firstPlanarHomeomorph ''
      openUnion N.context.region (N.normalizedPartCentres i) =
        openUnion D.firstRegion (dP i) := by
    exact openUnion_image_of_placedTile_images D.firstPlanarHomeomorph E
      (N.normalizedPartCentres i) (normalized_part_centres_subset_context N i) hplaced
  have hsuppFull : regularSupport D.firstRegion dC =
      D.firstPlanarHomeomorph '' regularSupport N.context.region N.context.centres :=
    regularSupport_image_of_openUnion_image N.context.region D.firstRegion
      N.context.centres dC D.firstPlanarHomeomorph hopenFull
  have hsuppPart (i : Fin P.numberOfParts) :
      regularSupport D.firstRegion (dP i) =
        D.firstPlanarHomeomorph ''
          regularSupport N.context.region (N.normalizedPartCentres i) :=
    regularSupport_image_of_openUnion_image N.context.region D.firstRegion
      (N.normalizedPartCentres i) (dP i) D.firstPlanarHomeomorph (hopenPart i)
  have hfirst : D.firstPlanarHomeomorph =
      coordinateProductHomeomorph D.firstHomeomorph (Homeomorph.refl ℝ) := by
    apply Homeomorph.ext
    intro z
    rw [D.firstPlanarHomeomorph_apply, coordinateProductHomeomorph_apply]
    simp
  have hcylFull : regularSupport D.firstRegion dC = Complex.re ⁻¹' mC := by
    rw [hsuppFull, normalizedCarrier_sourceSupport N, hfirst, hDH]
    exact coordinateCylinder_image H.homeomorph N.normalizedCarrierBase
  have hcylPart (i : Fin P.numberOfParts) :
      regularSupport D.firstRegion (dP i) = Complex.re ⁻¹' mP i := by
    rw [hsuppPart i, normalizedPart_sourceSupport N i, hfirst, hDH]
    exact coordinateCylinder_image H.homeomorph (N.normalizedPartBase i)
  have hpackFull : Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
      (D.firstRegion.toPolygonalRegion.placements dC) := by
    simpa [dC, deformedCenterCarrier, deformedCenterCarrierOn] using
      packing_of_placedTile_images D.firstPlanarHomeomorph E N.context.centres
        (fun _ h ↦ h) N.context_tiles.2.1 hplaced
  have hpackPart (i : Fin P.numberOfParts) :
      Tiling.IsPacking D.firstRegion.toPolygonalRegion.prototileFamily
        (D.firstRegion.toPolygonalRegion.placements (dP i)) :=
    packing_of_placedTile_images D.firstPlanarHomeomorph E
      (N.normalizedPartCentres i) (normalized_part_centres_subset_context N i)
      (N.normalized_part_tiles i).2.1 hplaced
  let _ : Countable ↥N.context.centres := N.context_tiles.1.to_subtype
  have hcountFull : dC.Countable := by
    exact Set.countable_range E
  have hcountPart (i : Fin P.numberOfParts) : (dP i).Countable := by
    exact hcountFull.mono (Set.image_subset_range E _)
  have htilesFull : TilesOn D.firstRegion dC (Complex.re ⁻¹' mC) :=
    tilesOn_of_countable_packing_regularSupport D.firstRegion dC
      (Complex.re ⁻¹' mC) hcountFull hpackFull hcylFull
  have htilesPart (i : Fin P.numberOfParts) :
      TilesOn D.firstRegion (dP i) (Complex.re ⁻¹' mP i) :=
    tilesOn_of_countable_packing_regularSupport D.firstRegion (dP i)
      (Complex.re ⁻¹' mP i) (hcountPart i) (hpackPart i) (hcylPart i)
  exact ⟨{
    firstHomeomorph_eq := hDH
    centreEmbedding := E
    centreEmbedding_apply := hE
    deformedCentres := dC
    deformedCentres_eq := rfl
    deformedPartCentres := dP
    deformedPartCentres_eq := fun _ ↦ rfl
    mappedCarrierBase := mC
    mappedCarrierBase_eq := rfl
    mappedPartBase := mP
    mappedPartBase_eq := fun _ ↦ rfl
    full_openUnion_image := hopenFull
    part_openUnion_image := hopenPart
    full_support_image := hsuppFull
    part_support_image := hsuppPart
    full_support_cylinder := hcylFull
    part_support_cylinder := hcylPart
    full_packing := hpackFull
    part_packing := hpackPart
    full_tiles := htilesFull
    part_tiles := htilesPart }⟩
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private theorem sharedSlabApproximation_of_periodicHomeomorph :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
      {epsilon : ℝ} (_hepsilon : 0 < epsilon)
      (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation N.context epsilon phi →
    IsGoodApproximation N.context phi →
    ∀ (H : PeriodicTranslatedVertexHomeomorph N phi)
      (D : CoordinateDeformation N.context phi),
      D.firstHomeomorph = H.homeomorph →
        ∃ A : SharedSlabApproximation N,
          A.epsilon = epsilon ∧ A.phi = phi ∧ HEq A.deformation D ∧
            A.deformation.firstHomeomorph = H.homeomorph := by
  intro K S P N epsilon hepsilon phi happrox hgood H D hDH
  have hperiod : 0 < mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by
    have h := H.strictMono (show (0 : ℝ) < P.commonPeriod from P.commonPeriod_pos)
    have heq := H.period_equivariant 0
    simp only [zero_add] at heq
    linarith
  have hboundary :
      ∀ (x : ℝ) (hx : x ∈ slabBoundarySet P),
        D.firstHomeomorph (x - (N.tileAnchor + N.centreAnchor).re) =
          mapScalar phi ⟨x - (N.tileAnchor + N.centreAnchor).re,
            N.normalizedBoundary_mem x hx⟩ := by
    intro x hx
    obtain ⟨v, s, hs⟩ := normalizedBoundary_isTranslatedVertexLevel N x hx
    have hcoord :
        (⟨x - (N.tileAnchor + N.centreAnchor).re,
          N.normalizedBoundary_mem x hx⟩ : N.context.coordinateSpace) =
          ⟨(v.1 + (s.1 : Tiling.Plane)).re,
            N.context.coordinateSpace.add_mem
              (N.context.vertex_re_mem v.1 v.2)
              (N.context.centre_re_mem s.1 s.2)⟩ := by
      apply Subtype.ext
      exact hs
    calc
      D.firstHomeomorph (x - (N.tileAnchor + N.centreAnchor).re) =
          H.homeomorph ((v.1 + (s.1 : Tiling.Plane)).re) := by
            rw [hDH, hs]
      _ = mapScalar phi
          ⟨(v.1 + (s.1 : Tiling.Plane)).re,
            N.context.coordinateSpace.add_mem
              (N.context.vertex_re_mem v.1 v.2)
              (N.context.centre_re_mem s.1 s.2)⟩ := by
            rw [H.translatedVertex_agreement v s]
            simp only [mapFirstPoint, mapScalar, ApproximationContext.vertexPoint,
              ApproximationContext.centrePoint, Complex.add_re]
            have heq :
                (⟨v.1.re + s.1.re,
                  N.context.coordinateSpace.add_mem
                    (N.context.vertex_re_mem v.1 v.2)
                    (N.context.centre_re_mem s.1 s.2)⟩ : N.context.coordinateSpace) =
                  ⟨v.1.re, N.context.vertex_re_mem v.1 v.2⟩ +
                    ⟨s.1.re, N.context.centre_re_mem s.1 s.2⟩ := by
              apply Subtype.ext
              rfl
            symm
            rw [heq, map_add]
            norm_num
      _ = mapScalar phi
          ⟨x - (N.tileAnchor + N.centreAnchor).re,
            N.normalizedBoundary_mem x hx⟩ := by
            exact congrArg (mapScalar phi) hcoord.symm
  have horder :
      ∀ a ∈ slabBoundarySet P, ∀ b ∈ slabBoundarySet P, a < b →
        D.firstHomeomorph (a - (N.tileAnchor + N.centreAnchor).re) <
          D.firstHomeomorph (b - (N.tileAnchor + N.centreAnchor).re) := by
    intro a ha b hb hab
    rw [hDH]
    apply H.strictMono
    linarith
  let A : SharedSlabApproximation N := {
    epsilon := epsilon
    epsilon_pos := hepsilon
    phi := phi
    approximation := happrox
    good := hgood
    deformation := D
    firstHomeomorph_translatedVertex_agreement := by
      intro v s
      rw [hDH]
      exact H.translatedVertex_agreement v s
    firstHomeomorph_period_equivariant := by
      intro x
      rw [hDH]
      exact H.period_equivariant x
    rationalHorizontalPeriod := phi ⟨P.commonPeriod, N.commonPeriod_mem⟩
    rationalHorizontalPeriod_pos := by
      have hq : (0 : ℝ) < (phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ : ℝ) := hperiod
      exact_mod_cast hq
    rationalHorizontalPeriod_eq := rfl
    boundary_agreement := hboundary
    boundary_order := horder
    translatedVertex_order := by
      intro v w s t
      have hv := H.translatedVertex_agreement v s
      have hw := H.translatedVertex_agreement w t
      have hv' : mapScalar phi
          ⟨(v.1 + (s.1 : Tiling.Plane)).re,
            N.context.coordinateSpace.add_mem
              (N.context.vertex_re_mem v.1 v.2)
              (N.context.centre_re_mem s.1 s.2)⟩ =
          H.homeomorph ((v.1 + (s.1 : Tiling.Plane)).re) := by
        rw [H.translatedVertex_agreement v s]
        simp only [mapFirstPoint, mapScalar, ApproximationContext.vertexPoint,
          ApproximationContext.centrePoint, Complex.add_re]
        have heq :
            (⟨v.1.re + s.1.re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem v.1 v.2)
                (N.context.centre_re_mem s.1 s.2)⟩ : N.context.coordinateSpace) =
              ⟨v.1.re, N.context.vertex_re_mem v.1 v.2⟩ +
                ⟨s.1.re, N.context.centre_re_mem s.1 s.2⟩ := by
          apply Subtype.ext
          rfl
        rw [heq, map_add]
        norm_num
      have hw' : mapScalar phi
          ⟨(w.1 + (t.1 : Tiling.Plane)).re,
            N.context.coordinateSpace.add_mem
              (N.context.vertex_re_mem w.1 w.2)
              (N.context.centre_re_mem t.1 t.2)⟩ =
          H.homeomorph ((w.1 + (t.1 : Tiling.Plane)).re) := by
        rw [H.translatedVertex_agreement w t]
        simp only [mapFirstPoint, mapScalar, ApproximationContext.vertexPoint,
          ApproximationContext.centrePoint, Complex.add_re]
        have heq :
            (⟨w.1.re + t.1.re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem w.1 w.2)
                (N.context.centre_re_mem t.1 t.2)⟩ : N.context.coordinateSpace) =
              ⟨w.1.re, N.context.vertex_re_mem w.1 w.2⟩ +
                ⟨t.1.re, N.context.centre_re_mem t.1 t.2⟩ := by
          apply Subtype.ext
          rfl
        rw [heq, map_add]
        norm_num
      rw [hv', hw']
      exact (H.strictMono.lt_iff_lt).symm }
  refine ⟨A, rfl, rfl, HEq.rfl, ?_⟩
  exact hDH
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional
open Function
open Tiling.AxisParallel.OneDimensional.FiniteInterval

private theorem boundaryCoordinateWitness_for_mass
    (C : ApproximationContext) (T : Set Tiling.Plane) (X : Set ℝ)
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (hTile : TilesOn C.region T {z : Tiling.Plane | z.re ∈ X}) :
    ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ C.region.vertices)
      (t : Tiling.Plane) (_ht : t ∈ T), x = (v + t).re := by
  intro x hx
  let levels : Set ℝ := Set.range fun p : ↥T × ↥C.region.vertices =>
    ((p.1 : Tiling.Plane) + p.2.1).im
  have hlevels : levels.Countable := by
    have hT : T.Countable := (IsPacking.locallyFinite_centres hTile.2.1).2
    have hV : C.region.vertices.Countable := by
      rw [← C.region.coe_vertexFinset]
      exact C.region.vertexFinset.finite_toSet.countable
    let _ : Countable ↥T := hT.to_subtype
    let _ : Countable ↥C.region.vertices := hV.to_subtype
    exact Set.countable_range _
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ levels).Nonempty := by
    by_contra hne
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ levels := by
      intro q hq
      by_contra hqbad
      exact hne ⟨q, hq, hqbad⟩
    have hzero : volume (Set.Ioo (0 : ℝ) 1) = 0 :=
      measure_mono_null hsub (hlevels.measure_zero volume)
    exact (isOpen_Ioo.measure_ne_zero volume ⟨(1 / 2 : ℝ), by norm_num⟩) hzero
  obtain ⟨q, hqIoo, hqbad⟩ := hdiff
  obtain ⟨t, hzt⟩ := support_mem_of_cylinder_frontier_for_subset
    C T X hXopen hXregular hTile x q hx
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport C.region T =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hfront : (Complex.mk x q : Tiling.Plane) ∈
      frontier ((t : Tiling.Plane) +ᵥ C.region.support) := by
    rw [frontier]
    refine ⟨subset_closure hzt, ?_⟩
    intro hzint
    have hzopen : (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ C.region.openCarrier := by
      change (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ interior C.region.support
      simpa only [interior_vadd] using hzint
    have hzunion : (Complex.mk x q : Tiling.Plane) ∈ openUnion C.region T := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨t, hzopen⟩
    have hopenSub : openUnion C.region T ⊆ regularSupport C.region T := by
      rw [regularSupport]
      exact interior_maximal subset_closure (by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
        exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _)
    have hztarget : (Complex.mk x q : Tiling.Plane) ∈
        ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      rw [← hsupport]
      exact hopenSub hzunion
    have hxin : x ∈ X := by simpa using hztarget
    have hxint : x ∈ interior X :=
      mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hxin)
    exact (Set.disjoint_left.1 disjoint_interior_frontier hxint hx)
  have hsource : (Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane) ∈
      frontier C.region.support := by
    have hvaddfront : frontier ((t : Tiling.Plane) +ᵥ C.region.support) =
        (t : Tiling.Plane) +ᵥ frontier C.region.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    rw [hvaddfront] at hfront
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hfront
  have hgrid := IntrinsicVertices.frontier_subset_vertexCoordinateGrid C.region hsource
  change ((∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).re = v.re) ∨
    ∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).im = v.im) at hgrid
  obtain hgrid | hgrid := hgrid
  · obtain ⟨v, hv, hvr⟩ := hgrid
    refine ⟨v, hv, t.1, t.2, ?_⟩
    have hvr' : x - (t : Tiling.Plane).re = v.re := by
      simpa only [Complex.sub_re] using hvr
    rw [Complex.add_re]
    linarith
  · obtain ⟨v, hv, hvi⟩ := hgrid
    have hvi' : q - (t : Tiling.Plane).im = v.im := by
      simpa only [Complex.sub_im] using hvi
    have hqbad' : q = ((t : Tiling.Plane) + v).im := by
      rw [Complex.add_im]
      linarith
    exact (hqbad ⟨⟨t, ⟨v, hv⟩⟩, hqbad'.symm⟩).elim

private theorem boundaryCoordinateWitness_region_for_mass
    (K : Region) (T : Set Tiling.Plane) (X : Set ℝ)
    (hXopen : IsOpen X) (hXregular : interior (closure X) = X)
    (hTile : TilesOn K T {z : Tiling.Plane | z.re ∈ X}) :
    ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ K.vertices)
      (t : Tiling.Plane) (_ht : t ∈ T), x = (v + t).re := by
  intro x hx
  let levels : Set ℝ := Set.range fun p : ↥T × ↥K.vertices =>
    ((p.1 : Tiling.Plane) + p.2.1).im
  have hlevels : levels.Countable := by
    have hT : T.Countable := (IsPacking.locallyFinite_centres hTile.2.1).2
    have hV : K.vertices.Countable := by
      rw [← K.coe_vertexFinset]
      exact K.vertexFinset.finite_toSet.countable
    let _ : Countable ↥T := hT.to_subtype
    let _ : Countable ↥K.vertices := hV.to_subtype
    exact Set.countable_range _
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ levels).Nonempty := by
    by_contra hne
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ levels := by
      intro q hq
      by_contra hqbad
      exact hne ⟨q, hq, hqbad⟩
    have hzero : volume (Set.Ioo (0 : ℝ) 1) = 0 :=
      measure_mono_null hsub (hlevels.measure_zero volume)
    exact (isOpen_Ioo.measure_ne_zero volume ⟨(1 / 2 : ℝ), by norm_num⟩) hzero
  obtain ⟨q, hqIoo, hqbad⟩ := hdiff
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport K T =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  obtain ⟨t, hzt⟩ := by
    have hxf : (Complex.mk x q : Tiling.Plane) ∈
        frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      rw [frontier_verticalCylinder]
      simpa using hx
    have hcloseEq : closure (regularSupport K T) =
        closure (openUnion K T) := by
      rw [regularSupport]
      apply le_antisymm
      · exact closure_minimal
          (interior_subset : interior (closure (openUnion K T)) ⊆
            closure (openUnion K T)) isClosed_closure
      · have hopen : IsOpen (openUnion K T) := by
          rw [openUnion]
          exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen K).1.vadd _
        exact closure_mono (interior_maximal subset_closure hopen)
    have hxclosure : (Complex.mk x q : Tiling.Plane) ∈
        closure (openUnion K T) := by
      rw [← hcloseEq, hsupport]
      exact frontier_subset_closure hxf
    rw [closure_openUnion_eq_iUnion_support hTile.2.1] at hxclosure
    exact Set.mem_iUnion.mp hxclosure
  have hfront : (Complex.mk x q : Tiling.Plane) ∈
      frontier ((t : Tiling.Plane) +ᵥ K.support) := by
    rw [frontier]
    refine ⟨subset_closure hzt, ?_⟩
    intro hzint
    have hzopen : (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ K.openCarrier := by
      change (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ interior K.support
      simpa only [interior_vadd] using hzint
    have hzunion : (Complex.mk x q : Tiling.Plane) ∈ openUnion K T := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨t, hzopen⟩
    have hopenSub : openUnion K T ⊆ regularSupport K T := by
      rw [regularSupport]
      exact interior_maximal subset_closure (by
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
        exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen K).1.vadd _)
    have hztarget : (Complex.mk x q : Tiling.Plane) ∈
        ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      rw [← hsupport]
      exact hopenSub hzunion
    have hxin : x ∈ X := by simpa using hztarget
    have hxint : x ∈ interior X :=
      mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hxin)
    exact (Set.disjoint_left.1 disjoint_interior_frontier hxint hx)
  have hsource : (Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane) ∈
      frontier K.support := by
    have hvaddfront : frontier ((t : Tiling.Plane) +ᵥ K.support) =
        (t : Tiling.Plane) +ᵥ frontier K.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    rw [hvaddfront] at hfront
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hfront
  have hgrid := IntrinsicVertices.frontier_subset_vertexCoordinateGrid K hsource
  change ((∃ v ∈ K.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).re = v.re) ∨
    ∃ v ∈ K.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).im = v.im) at hgrid
  obtain hgrid | hgrid := hgrid
  · obtain ⟨v, hv, hvr⟩ := hgrid
    refine ⟨v, hv, t.1, t.2, ?_⟩
    have hvr' : x - (t : Tiling.Plane).re = v.re := by
      simpa only [Complex.sub_re] using hvr
    rw [Complex.add_re]
    linarith
  · obtain ⟨v, hv, hvi⟩ := hgrid
    have hvi' : q - (t : Tiling.Plane).im = v.im := by
      simpa only [Complex.sub_im] using hvi
    have hqbad' : q = ((t : Tiling.Plane) + v).im := by
      rw [Complex.add_im]
      linarith
    exact (hqbad ⟨⟨t, ⟨v, hv⟩⟩, hqbad'.symm⟩).elim

private theorem endpointChain_cover_for_mass
    {E : Set ℝ} {x y : ℝ} (C :
      Tiling.AxisParallel.OneDimensional.FiniteInterval.EndpointChain E x y)
    {z : ℝ} (hzE : z ∉ E) (hzx : x < z) (hzy : z < y) :
    ∃ i : Fin C.length, z ∈ Ioo (C.point i.castSucc) (C.point i.succ) := by
  classical
  let S : Set (Fin (C.length + 1)) := {j | C.point j ≤ z}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := by
    refine ⟨0, ?_⟩
    change C.point 0 ≤ z
    rw [C.first]
    exact le_of_lt hzx
  obtain ⟨j, hjS, hjmax⟩ := hSfinite.exists_maximal hSnonempty
  change C.point j ≤ z at hjS
  have hjlast : j ≠ Fin.last C.length := by
    intro hlast
    have : y ≤ z := by simpa [hlast, C.last] using hjS
    exact (not_le_of_gt hzy) this
  let i : Fin C.length := ⟨j.val, by
    have hle : j.val ≤ C.length := Nat.le_of_lt_succ j.isLt
    by_contra hnot
    have heq : j.val = C.length := Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
    apply hjlast
    apply Fin.ext
    exact heq⟩
  have hji : i.castSucc = j := by rfl
  have hleft : C.point i.castSucc < z := by
    exact lt_of_le_of_ne hjS (by
      intro hzEq
      apply hzE
      have hpointE := (C.consecutive i).1
      rw [← hzEq]
      exact hpointE)
  have hright : z < C.point i.succ := by
    by_contra hnot
    have hle : C.point i.succ ≤ z := le_of_not_gt hnot
    have hsuccS : i.succ ∈ S := hle
    have hji_lt : j < i.succ := by
      change j.val < i.val + 1
      simp only [i]
      omega
    have hmaxle := hjmax hsuccS hji_lt.le
    exact (not_le_of_gt hji_lt) hmaxle
  exact ⟨i, ⟨hleft, hright⟩⟩

private theorem periodic_mem_of_vadd_eq_mass {X : Set ℝ} {p : ℝ}
    (h : p +ᵥ X = X) : Function.Periodic (fun x : ℝ => x ∈ X) p := by
  intro x
  apply propext
  constructor
  · intro hx
    have hx' : p + x ∈ X := by simpa [add_comm] using hx
    rw [← h] at hx'
    obtain ⟨y, hy, hay⟩ := hx'
    have : y = x := by simpa using hay
    simpa [this] using hy
  · intro hx
    have hx' : p + x ∈ p +ᵥ X := ⟨x, hx, rfl⟩
    rw [h] at hx'
    simpa [add_comm] using hx'

private theorem rational_periodic_open_mass
    {X : Set ℝ} {p : ℝ}
    (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (hXnonnull : volume X ≠ 0)
    (hXperiod : p +ᵥ X = X)
    (hp : 0 < p)
    (hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q → (frontier X ∩ Q).Finite)
    (hboundary : ∀ x ∈ frontier X, ∃ q : ℚ, x = (q : ℝ))
    (hprat : ∃ q : ℚ, p = (q : ℝ)) :
    ∃ m : ℚ, 0 < m ∧
      (volume (X ∩ Ico 0 p)).toReal = (m : ℝ) := by
  classical
  by_cases hXuniv : X = Set.univ
  · obtain ⟨q, hq⟩ := hprat
    refine ⟨q, ?_, ?_⟩
    · have hqpos : (0 : ℝ) < (q : ℝ) := by simpa [← hq] using hp
      exact_mod_cast hqpos
    · rw [hXuniv]
      simp only [univ_inter]
      rw [Real.volume_Ico]
      rw [show p - 0 = p by ring, ENNReal.toReal_ofReal hp.le]
      exact hq
  have hXne : X.Nonempty := by
    by_contra hne
    have : X = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [this] at hXnonnull
    exact hXnonnull measure_empty
  have hfrontne : (frontier X).Nonempty :=
    frontier_nonempty_of_nonempty_proper_regularOpen
      hXne hXopen hXregular hXuniv
  obtain ⟨x, hx⟩ := hfrontne
  have hxshift : x + p ∈ frontier X := by
    rw [← Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic hXperiod]
    exact Set.mem_vadd_set.mpr ⟨x, hx, by simp [vadd_eq_add, add_comm]⟩
  have hfrontlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (frontier X ∩ Q).Finite := hlocal
  obtain ⟨C⟩ := Tiling.AxisParallel.OneDimensional.FiniteInterval.endpointChain_nonempty
    hfrontlocal hx hxshift (by linarith)
  have hCmono : StrictMono C.point := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    exact (C.consecutive i).2.2.1
  have hCxy : C.point (0 : Fin (C.length + 1)) <
      C.point (Fin.last C.length) := by
    rw [C.first, C.last]
    exact lt_add_of_pos_right x hp
  have hpoint_mem (j : Fin (C.length + 1)) : C.point j ∈ frontier X := by
    by_cases hjlast : j = Fin.last C.length
    · simpa [hjlast, C.last] using hxshift
    · have hj : j.val < C.length := by
        exact lt_of_le_of_ne (Nat.le_of_lt_succ j.isLt)
          (by intro h; apply hjlast; exact Fin.ext h)
      exact (C.consecutive ⟨j.val, hj⟩).1
  let good : Fin C.length → Prop := fun i ↦
    Ioo (C.point i.castSucc) (C.point i.succ) ⊆ X
  have hgood_or (i : Fin C.length) :
      good i ∨ Ioo (C.point i.castSucc) (C.point i.succ) ⊆ Xᶜ := by
    dsimp [good]
    have hdis : Disjoint (Ioo (C.point i.castSucc) (C.point i.succ)) (frontier X) := by
      rw [Set.disjoint_left]
      intro z hz hzf
      exact (Set.disjoint_left.mp (C.consecutive i).2.2.2) hzf hz
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hdis with h | h
    · exact Or.inl (h.trans interior_subset)
    · exact Or.inr (h.trans interior_subset)
  let qpoint : Fin (C.length + 1) → ℚ := fun j =>
    Classical.choose (hboundary (C.point j) (hpoint_mem j))
  have hqpoint (j : Fin (C.length + 1)) : C.point j = (qpoint j : ℝ) :=
    Classical.choose_spec (hboundary (C.point j) (hpoint_mem j))
  let mass : ℚ := ∑ i : Fin C.length,
    if good i then qpoint i.succ - qpoint i.castSucc else 0
  have hmass_eq_sum :
      (mass : ℝ) = ∑ i : Fin C.length,
        if good i then C.point i.succ - C.point i.castSucc else 0 := by
    dsimp [mass]
    push_cast
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs with hiGood
    · rw [Rat.cast_sub, hqpoint i.succ, hqpoint i.castSucc]
    · simp
  have hXcell_ae : Filter.EventuallyEq (ae volume)
      (Set.inter X (Ico (C.point 0) (C.point (Fin.last C.length)) : Set ℝ))
      (⋃ i : Fin C.length, if good i then
        Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := by
    have hrange : (Set.range C.point).Finite := Set.finite_range C.point
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hrange.measure_zero volume)] with z hz
    have hznot : z ∉ Set.range C.point := by
      intro hzr
      exact hz hzr
    apply propext
    constructor
    · rintro ⟨hzX, hzcell⟩
      have hzleft : C.point 0 < z := by
        rw [C.first]
        exact lt_of_le_of_ne (by simpa [C.first] using hzcell.1) (by
          intro heq
          apply hznot
          exact ⟨0, by simpa [C.first] using heq⟩)
      have hzright : z < C.point (Fin.last C.length) := by
        exact lt_of_le_of_ne hzcell.2.le (by
          intro heq
          apply hznot
          exact ⟨Fin.last C.length, heq.symm⟩)
      have hzrightx : z < x + p := by simpa [C.last] using hzright
      have hzleftx : x < z := by simpa [C.first] using hzleft
      have hznotfront : z ∉ frontier X := by
        intro hzf
        exact (Set.disjoint_left.1 disjoint_interior_frontier
          (mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hzX)) hzf)
      obtain ⟨i, hzi⟩ := endpointChain_cover_for_mass C hznotfront hzleftx hzrightx
      have hgoodi : good i := by
        rcases hgood_or i with hi | hi
        · exact hi
        · exfalso
          exact hi hzi hzX
      exact Set.mem_iUnion.mpr ⟨i, by simp [hgoodi, hzi]⟩
    · intro hzU
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hzU
      by_cases hgi : good i
      · rw [if_pos hgi] at hzi
        have hleft : C.point 0 ≤ C.point i.castSucc :=
          hCmono.monotone (Fin.zero_le _)
        have hright : C.point i.succ ≤ C.point (Fin.last C.length) :=
          hCmono.monotone (Fin.le_last _)
        exact ⟨hgi hzi, ⟨hleft.trans (le_of_lt hzi.1),
          lt_of_lt_of_le hzi.2 hright⟩⟩
      · rw [if_neg hgi] at hzi
        exact hzi.elim
  have hUmeas : MeasurableSet
      (⋃ i : Fin C.length, if good i then
        Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := by
    exact MeasurableSet.iUnion fun i ↦ by
      split_ifs with hi
      · exact measurableSet_Ioo
      · exact MeasurableSet.empty
  have hUdisj : Pairwise (Disjoint on fun i : Fin C.length ↦
      if good i then Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := by
    intro i j hij
    change Disjoint (if good i then Ioo (C.point i.castSucc) (C.point i.succ) else ∅)
      (if good j then Ioo (C.point j.castSucc) (C.point j.succ) else ∅)
    split_ifs with hi hj
    · rw [Set.disjoint_left]
      intro z hzi hzj
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hidx : i.succ ≤ j.castSucc := by
          apply Fin.mk_le_mk.mpr
          exact Nat.succ_le_of_lt (by exact_mod_cast hlt)
        have hleft : C.point i.succ ≤ C.point j.castSucc := hCmono.monotone hidx
        exact (not_lt_of_ge hleft) (lt_trans hzj.1 hzi.2)
      · have hidx : j.succ ≤ i.castSucc := by
          apply Fin.mk_le_mk.mpr
          exact Nat.succ_le_of_lt (by exact_mod_cast hgt)
        have hleft : C.point j.succ ≤ C.point i.castSucc := hCmono.monotone hidx
        exact (not_lt_of_ge hleft) (lt_trans hzi.1 hzj.2)
    · exact Set.disjoint_left.2 (by simp)
    · exact Set.disjoint_left.2 (by simp)
    · exact Set.disjoint_left.2 (by simp)
  have hUmeas_i (i : Fin C.length) : MeasurableSet
      (if good i then Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := by
    split_ifs with hi
    · exact measurableSet_Ioo
    · exact MeasurableSet.empty
  have hUmeasure :
      volume (⋃ i : Fin C.length, if good i then
        Ioo (C.point i.castSucc) (C.point i.succ) else ∅) =
        ∑ i : Fin C.length, volume (if good i then
          Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := by
    rw [measure_iUnion hUdisj hUmeas_i]
    simp only [tsum_fintype]
  have hcellmeasure :
      volume (X ∩ Ico (C.point 0) (C.point (Fin.last C.length))) =
        ∑ i : Fin C.length, if good i then
          volume (Ioo (C.point i.castSucc) (C.point i.succ)) else 0 := by
    calc
      volume (X ∩ Ico (C.point 0) (C.point (Fin.last C.length))) =
          volume (⋃ i : Fin C.length, if good i then
            Ioo (C.point i.castSucc) (C.point i.succ) else ∅) :=
        measure_congr hXcell_ae
      _ = ∑ i : Fin C.length, volume (if good i then
          Ioo (C.point i.castSucc) (C.point i.succ) else ∅) := hUmeasure
      _ = ∑ i : Fin C.length, if good i then
          volume (Ioo (C.point i.castSucc) (C.point i.succ)) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        split_ifs <;> simp
  have hcellreal :
      (volume (X ∩ Ico (C.point 0) (C.point (Fin.last C.length)))).toReal =
        (mass : ℝ) := by
    rw [hcellmeasure, ENNReal.toReal_sum]
    · apply Eq.trans ?_ hmass_eq_sum.symm
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs with h
      · rw [Real.volume_Ioo, ENNReal.toReal_ofReal]
        exact (sub_pos.mpr (C.consecutive i).2.2.1).le
      · simp
    · intro i hi
      split_ifs with h
      · rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      · simp
  have htranslate := Tiling.AxisParallel.Terminal.periodCellMeasure_translationInvariant
    hXopen.measurableSet hp hXperiod (C.point 0)
  have horigin :
      (volume (X ∩ Ico 0 p)).toReal =
        (volume (X ∩ Ico (C.point 0) (C.point 0 + p))).toReal := by
    symm
    exact htranslate
  have hCperiod : C.point (Fin.last C.length) = C.point 0 + p := by
    rw [C.first, C.last]
  have hcellreal' :
      (volume (X ∩ Ico (C.point 0) (C.point 0 + p))).toReal = (mass : ℝ) := by
    simpa [hCperiod] using hcellreal
  refine ⟨mass, ?_, horigin.trans hcellreal'⟩
  have hmasspos : 0 < mass := by
    obtain ⟨z, hzX⟩ := hXne
    let n : ℤ := Int.floor ((z - C.point 0) / p)
    let z' : ℝ := z - (n : ℝ) * p
    have hz'X : z' ∈ X := by
      have hfun := (periodic_mem_of_vadd_eq_mass hXperiod).zsmul (-n)
      have := (hfun z).mpr hzX
      simpa [z', n, zsmul_eq_mul, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc] using this
    have hz'left : C.point 0 ≤ z' := by
      have hfloor := Int.floor_le ((z - C.point 0) / p)
      have := (le_div_iff₀ hp).mp hfloor
      dsimp [z']
      linarith
    have hz'right : z' < C.point 0 + p := by
      have hfloor := Int.lt_floor_add_one ((z - C.point 0) / p)
      have := (div_lt_iff₀ hp).mp hfloor
      dsimp [z']
      linarith
    have hz'left' : C.point 0 < z' := by
      exact lt_of_le_of_ne hz'left (by
        intro heq
        have : z' ∈ frontier X := by
          simpa [heq] using hpoint_mem 0
        exact (Set.disjoint_left.1 disjoint_interior_frontier
          (mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hz'X)) this)
        )
    have hz'right' : z' < C.point (Fin.last C.length) := by simpa [hCperiod] using hz'right
    have hznotfront : z' ∉ frontier X := by
      intro hzf
      exact (Set.disjoint_left.1 disjoint_interior_frontier
        (mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hz'X)) hzf)
    have hz'rightx : z' < x + p := by
      simpa [C.last] using hz'right'
    have hz'leftx : x < z' := by simpa [C.first] using hz'left'
    obtain ⟨i, hzi⟩ := endpointChain_cover_for_mass C hznotfront hz'leftx hz'rightx
    have hgi : good i := by
      rcases hgood_or i with hi | hi
      · exact hi
      · exfalso
        exact hi hzi hz'X
    have hterm : 0 < qpoint i.succ - qpoint i.castSucc := by
      have hreal : 0 < (qpoint i.succ : ℝ) - (qpoint i.castSucc : ℝ) := by
        rw [← hqpoint i.succ, ← hqpoint i.castSucc]
        exact sub_pos.mpr (C.consecutive i).2.2.1
      exact_mod_cast hreal
    have hsumpos : 0 < ∑ i : Fin C.length,
        if good i then qpoint i.succ - qpoint i.castSucc else 0 := by
      apply lt_of_lt_of_le hterm
      have hsingle := Finset.single_le_sum
        (s := Finset.univ)
        (f := fun j : Fin C.length ↦
          if good j then qpoint j.succ - qpoint j.castSucc else 0)
        (fun j _ ↦ by
          by_cases hj : good j
          · have hreal : 0 ≤ (qpoint j.succ : ℝ) - (qpoint j.castSucc : ℝ) := by
              rw [← hqpoint j.succ, ← hqpoint j.castSucc]
              exact (sub_pos.mpr (C.consecutive j).2.2.1).le
            have : 0 ≤ qpoint j.succ - qpoint j.castSucc := by exact_mod_cast hreal
            simpa [hj] using this
          · simp [hj]) (Finset.mem_univ i)
      simpa [hgi] using hsingle
    simpa [mass] using hsumpos
  exact hmasspos

private theorem rationalPeriodCellMasses :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} {N : NormalizedSlabData P}
      {A : SharedSlabApproximation N} (D : FirstCoordinateSlabTransport A),
    ∃ mass : Fin P.numberOfParts → ℚ,
      (∀ i, 0 < mass i) ∧
      ∀ i,
        (volume (D.deformedPartBase i ∩
          Ico 0 (A.rationalHorizontalPeriod : ℝ))).toReal =
            (mass i : ℝ) := by
  intro K S P N A D
  have hpartSubset (i : Fin P.numberOfParts) :
      D.deformedPartCentres i ⊆ D.deformedCentres := by
    intro t ht
    rw [← D.deformedPartCentres_union]
    exact Set.mem_iUnion.mpr ⟨i, ht⟩
  have hmass : ∀ i : Fin P.numberOfParts, ∃ m : ℚ, 0 < m ∧
      (volume (D.deformedPartBase i ∩
        Ico 0 (A.rationalHorizontalPeriod : ℝ))).toReal = (m : ℝ) := by
    intro i
    have hlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
        (frontier (D.deformedPartBase i) ∩ Q).Finite := by
      intro Q hQ
      obtain ⟨R, hQR⟩ := hQ.subset_closedBall 0
      have hfin := (D.deformed_part_tiles i).verticalCylinder_frontier_locallyFinite
        (D.deformedPartBase_open i) (D.deformedPartBase_regular i)
        (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
      apply hfin.subset
      intro x hx
      exact ⟨hQR hx.2, hx.1⟩
    have hboundary : ∀ x ∈ frontier (D.deformedPartBase i), ∃ q : ℚ, x = (q : ℝ) := by
      intro x hx
      obtain ⟨v, hv, t, ht, hvt⟩ := boundaryCoordinateWitness_region_for_mass
        A.deformation.firstRegion (D.deformedPartCentres i)
        (D.deformedPartBase i) (D.deformedPartBase_open i)
        (D.deformedPartBase_regular i) (D.deformed_part_tiles i) x hx
      obtain ⟨qv, hqv⟩ := D.deformed_first_coordinates_rational.1 v hv
      obtain ⟨qt, hqt⟩ := D.deformed_first_coordinates_rational.2 t
        (hpartSubset i ht)
      refine ⟨qv + qt, ?_⟩
      rw [hvt, Complex.add_re, hqv, hqt]
      push_cast
      rfl
    exact rational_periodic_open_mass
      (D.deformedPartBase_open i) (D.deformedPartBase_regular i)
      (D.deformedPartBase_nonnull i) (D.deformedPartBase_periodic i)
      (by exact_mod_cast A.rationalHorizontalPeriod_pos) hlocal hboundary
      ⟨A.rationalHorizontalPeriod, rfl⟩
  choose mass hmass_pos hmass_eq using hmass
  exact ⟨mass, hmass_pos, hmass_eq⟩

private theorem slabRationalization_of_sharedTransport :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S}
      (N : NormalizedSlabData P) (A : SharedSlabApproximation N)
      (D : FirstCoordinateSlabTransport A)
      (mass : Fin P.numberOfParts → ℚ),
    (∀ i, 0 < mass i) →
    (∀ i,
      (volume (D.deformedPartBase i ∩
        Ico 0 (A.rationalHorizontalPeriod : ℝ))).toReal =
          (mass i : ℝ)) →
      Nonempty (SlabRationalization K S P) := by
  intro K S P N A D mass hmass hmass_eq
  refine ⟨{
    tileAnchor := N.tileAnchor
    tileAnchor_mem := N.tileAnchor_mem
    centreAnchor := N.centreAnchor
    centreAnchor_mem := N.centreAnchor_mem
    context := N.context
    context_region := N.context_region
    context_centres := N.context_centres
    context_target := N.context_target
    context_tiles := N.context_tiles
    normalizedCarrierBase := N.normalizedCarrierBase
    normalizedCarrierBase_eq := N.normalizedCarrierBase_eq
    normalizedPartCentres := N.normalizedPartCentres
    normalizedPartCentres_eq := N.normalizedPartCentres_eq
    normalizedPartBase := N.normalizedPartBase
    normalizedPartBase_eq := N.normalizedPartBase_eq
    normalized_part_tiles := N.normalized_part_tiles
    commonPeriod_mem := N.commonPeriod_mem
    normalizedBoundary_mem := N.normalizedBoundary_mem
    epsilon := A.epsilon
    epsilon_pos := A.epsilon_pos
    phi := A.phi
    approximation := A.approximation
    good := A.good
    deformation := A.deformation
    centreEmbedding := D.centreEmbedding
    centreEmbedding_apply := D.centreEmbedding_apply
    deformedCentres := D.deformedCentres
    deformedCentres_eq := D.deformedCentres_eq
    deformedPartCentres := D.deformedPartCentres
    deformedPartCentres_eq := D.deformedPartCentres_eq
    deformedPartCentres_nonempty := D.deformedPartCentres_nonempty
    deformedPartCentres_pairwise := D.deformedPartCentres_pairwise
    deformedPartCentres_union := D.deformedPartCentres_union
    deformedCarrierBase := D.deformedCarrierBase
    deformedCarrierBase_open := D.deformedCarrierBase_open
    deformedCarrierBase_regular := D.deformedCarrierBase_regular
    deformedCarrierBase_nonnull := D.deformedCarrierBase_nonnull
    deformedPartBase := D.deformedPartBase
    deformedPartBase_open := D.deformedPartBase_open
    deformedPartBase_regular := D.deformedPartBase_regular
    deformedPartBase_nonnull := D.deformedPartBase_nonnull
    deformedPartBase_ae_disjoint := D.deformedPartBase_ae_disjoint
    deformedPartBase_ae_partition := D.deformedPartBase_ae_partition
    deformed_tiles := D.deformed_tiles
    deformed_support := D.deformed_support
    deformed_part_tiles := D.deformed_part_tiles
    deformed_part_support := D.deformed_part_support
    rationalHorizontalPeriod := A.rationalHorizontalPeriod
    rationalHorizontalPeriod_pos := A.rationalHorizontalPeriod_pos
    rationalHorizontalPeriod_eq := A.rationalHorizontalPeriod_eq
    deformedCarrierBase_periodic := D.deformedCarrierBase_periodic
    deformedPartBase_periodic := D.deformedPartBase_periodic
    deformed_part_vertical_period := D.deformed_part_vertical_period
    deformed_part_skew_period := D.deformed_part_skew_period
    rationalMass := mass
    rationalMass_pos := hmass
    rationalMass_eq := hmass_eq
    carrier_frontier_transport := D.carrier_frontier_transport
    part_frontier_transport := D.part_frontier_transport
    deformed_first_coordinates_rational := D.deformed_first_coordinates_rational }⟩
end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private theorem periodicTranslatedVertexHomeomorph_exists :
    ∀ {K : Region} {S : Set Plane}
      {P : FiniteSlabPartition K S} (N : NormalizedSlabData P)
      (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ),
    IsGoodApproximation N.context phi →
    (0 < mapScalar phi
      ⟨P.commonPeriod, N.commonPeriod_mem⟩) →
    (∀ (v w : N.context.region.vertices) (s t : N.context.centres),
      ((v.1 + (s.1 : Plane)).re <
          (w.1 + (t.1 : Plane)).re ↔
        mapScalar phi
            ⟨(v.1 + (s.1 : Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem v.1 v.2)
                (N.context.centre_re_mem s.1 s.2)⟩ <
          mapScalar phi
            ⟨(w.1 + (t.1 : Plane)).re,
              N.context.coordinateSpace.add_mem
                (N.context.vertex_re_mem w.1 w.2)
                (N.context.centre_re_mem t.1 t.2)⟩)) →
      Nonempty (PeriodicTranslatedVertexHomeomorph N phi) := by
  intro K S P N phi hgood hperiod horder
  obtain ⟨E⟩ := translatedVertexLevelsLocal_enumeration N
  let y : ℤ → ℝ := fun j ↦
    mapScalar phi
      ⟨E.point j,
        translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩
  have hystrict : StrictMono y := by
    apply strictMono_int_of_lt_succ
    intro j
    have hxlevel : E.point j ∈ translatedVertexLevelsLocal N := by
      have hr : E.point j ∈ Set.range E.point := Set.mem_range_self j
      rw [E.point_range] at hr
      exact hr
    have hylevel : E.point (j + 1) ∈ translatedVertexLevelsLocal N := by
      have hr : E.point (j + 1) ∈ Set.range E.point :=
        Set.mem_range_self (j + 1)
      rw [E.point_range] at hr
      exact hr
    obtain ⟨v, s, hv⟩ := hxlevel
    obtain ⟨w, t, hw⟩ := hylevel
    have hsrc :
        (v.1 + (s.1 : Plane)).re < (w.1 + (t.1 : Plane)).re := by
      rw [← hv, ← hw]
      apply E.point_strictMono
      omega
    have hmap := (horder v w s t).mp hsrc
    simpa [y, hv, hw] using hmap
  have hxs : ∀ j : ℤ,
      E.point (j + Int.ofNat E.count) = E.point j + P.commonPeriod :=
    fun j ↦ E.point_period j
  have hys : ∀ j : ℤ,
      y (j + Int.ofNat E.count) = y j +
        mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by
    intro j
    simpa [y] using periodicEnumeration_mappedPoint_intShift E phi j 1
  have hxc : ∀ z : ℝ, ∃ j : ℤ,
      E.point j ≤ z ∧ z < E.point (j + 1) := by
    exact periodic_strictMono_cofinal (n := E.count)
      (p := P.commonPeriod) E.count_pos P.commonPeriod_pos E.point_strictMono hxs
  have hyc : ∀ z : ℝ, ∃ j : ℤ,
      y j ≤ z ∧ z < y (j + 1) := by
    exact periodic_strictMono_cofinal (n := E.count)
      (p := mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩)
      E.count_pos hperiod hystrict hys
  obtain ⟨H, hHmono, hHknots, hHperiod⟩ :=
    exists_periodic_strictMonoHomeomorph_extension E.count P.commonPeriod
      (mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩)
      E.point y E.count_pos P.commonPeriod_pos hperiod E.point_strictMono
      hystrict hxs hys hxc hyc
  refine ⟨⟨H, hHmono, ?_, ?_⟩⟩
  · intro v s
    have hlevel : (v.1 + (s.1 : Plane)).re ∈ translatedVertexLevelsLocal N :=
      ⟨v, s, rfl⟩
    have hrange : (v.1 + (s.1 : Plane)).re ∈ Set.range E.point := by
      rw [E.point_range]
      exact hlevel
    obtain ⟨j, hj⟩ := hrange
    have hkn := hHknots j
    have hcoord :
        (⟨E.point j, translatedVertexLevelsLocal_point_mem_coordinateSpace N E j⟩ :
          N.context.coordinateSpace) =
        ⟨(v.1 + (s.1 : Plane)).re,
          N.context.coordinateSpace.add_mem
            (N.context.vertex_re_mem v.1 v.2)
            (N.context.centre_re_mem s.1 s.2)⟩ := by
      apply Subtype.ext
      exact hj
    rw [← hj, hHknots j]
    dsimp [y]
    rw [hcoord]
    have hsum :
        (⟨(v.1 + (s.1 : Plane)).re,
          N.context.coordinateSpace.add_mem
            (N.context.vertex_re_mem v.1 v.2)
            (N.context.centre_re_mem s.1 s.2)⟩ : N.context.coordinateSpace) =
        (⟨v.1.re, N.context.vertex_re_mem v.1 v.2⟩ : N.context.coordinateSpace) +
          ⟨s.1.re, N.context.centre_re_mem s.1 s.2⟩ := by
      apply Subtype.ext
      simp [Complex.add_re]
    rw [hsum]
    have hvmap :
        (mapFirstPoint phi (N.context.vertexPoint v.1 v.2)).re =
          mapScalar phi
            (⟨v.1.re, N.context.vertex_re_mem v.1 v.2⟩ :
              N.context.coordinateSpace) := by
      simp only [mapFirstPoint, ApproximationContext.vertexPoint,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul, sub_self,
        add_zero]
    have hsmap :
        (mapFirstPoint phi (N.context.centrePoint s.1 s.2)).re =
          mapScalar phi
            (⟨s.1.re, N.context.centre_re_mem s.1 s.2⟩ :
              N.context.coordinateSpace) := by
      simp only [mapFirstPoint, ApproximationContext.centrePoint,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul, sub_self,
        add_zero]
    rw [hvmap, hsmap]
    unfold mapScalar
    rw [map_add]
    norm_num
  · intro x
    exact hHperiod x
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
private theorem sharedSlabApproximation_exists :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} (N : NormalizedSlabData P),
    Nonempty (SharedSlabApproximation N) := by
  intro K S P N
  obtain ⟨εorder, hεorder, horderThreshold⟩ :=
    translatedVertex_globalOrderThreshold N
  obtain ⟨εgood, hεgood, hgoodThreshold⟩ :=
    isGoodApproximation_of_sufficientlyFine N.context
  let period : N.context.coordinateSpace :=
    ⟨P.commonPeriod, N.commonPeriod_mem⟩
  let periodAlphabet : Finset N.context.coordinateSpace := {period}
  obtain ⟨εperiod, hεperiod, hperiodSign⟩ :=
    approximation_preservesSign_finset N.context periodAlphabet
  let ε : ℝ := min εorder (min εgood εperiod)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεorder (lt_min hεgood hεperiod)
  obtain ⟨φ, hφ⟩ := exists_epsilonApproximation N.context ε hε
  have hφorder : IsEpsilonApproximation N.context εorder φ := by
    refine ⟨lt_of_lt_of_le hφ.epsilon_pos (min_le_left _ _),
      hφ.fixesRational, ?_⟩
    intro j
    exact lt_of_lt_of_le (hφ.basis_close j) (min_le_left _ _)
  have hφgood : IsEpsilonApproximation N.context εgood φ := by
    refine ⟨lt_of_lt_of_le hφ.epsilon_pos
        (le_trans (min_le_right _ _) (min_le_left _ _)),
      hφ.fixesRational, ?_⟩
    intro j
    exact lt_of_lt_of_le (hφ.basis_close j)
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hφperiod : IsEpsilonApproximation N.context εperiod φ := by
    refine ⟨lt_of_lt_of_le hφ.epsilon_pos
        (le_trans (min_le_right _ _) (min_le_right _ _)),
      hφ.fixesRational, ?_⟩
    intro j
    exact lt_of_lt_of_le (hφ.basis_close j)
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hgood : IsGoodApproximation N.context φ := hgoodThreshold φ hφgood
  have horder := horderThreshold φ hφorder
  have hperiod : 0 < mapScalar φ period := by
    have hs := hperiodSign φ hφperiod period (by simp [periodAlphabet])
    have hs' : Real.sign (mapScalar φ period) = 1 := by
      have hsrc : Real.sign ((period : N.context.coordinateSpace) : ℝ) = 1 := by
        change Real.sign P.commonPeriod = 1
        exact Real.sign_of_pos P.commonPeriod_pos
      exact hs.trans hsrc
    have hne : mapScalar φ period ≠ 0 := by
      intro hz
      rw [hz, Real.sign_zero] at hs'
      norm_num at hs'
    rcases lt_or_gt_of_ne hne with hn | hp
    · rw [Real.sign_of_neg hn] at hs'
      norm_num at hs'
    · exact hp
  obtain ⟨H⟩ := periodicTranslatedVertexHomeomorph_exists N φ hgood hperiod horder
  obtain ⟨D, hDH⟩ := coordinateDeformation_with_firstHomeomorph N φ hgood H
  obtain ⟨A, _hεA, _hφA, _hDA, _hHA⟩ :=
    sharedSlabApproximation_of_periodicHomeomorph N hε φ hφ hgood H D hDH
  exact ⟨A⟩
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
private theorem periodGroup_mapFirstPoint
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (A : SharedSlabApproximation N)
    (E : ↥N.context.centres ↪ Tiling.Plane)
    (hE : ∀ t, E t = mapFirstPoint A.phi (N.context.centrePoint t.1 t.2))
    (i : Fin P.numberOfParts)
    (u v : Tiling.Plane)
    (hu : u ∈ periodGroup (N.normalizedPartCentres i))
    (hshift : ∀ (t : ↥N.context.centres)
      (_ht : (t : Tiling.Plane) ∈ N.normalizedPartCentres i),
      ∃ htu : t.1 + u ∈ N.context.centres,
        mapFirstPoint A.phi (N.context.centrePoint (t.1 + u) htu) =
          mapFirstPoint A.phi (N.context.centrePoint t.1 t.2) + v) :
    v ∈ periodGroup (deformedCenterCarrierOn E
      {t : ↥N.context.centres | (t : Tiling.Plane) ∈ N.normalizedPartCentres i}) := by
  have hset : u +ᵥ N.normalizedPartCentres i = N.normalizedPartCentres i :=
    (periodGroup_isAddSubgroup _ _).mp hu
  have hneg : -u ∈ periodGroup (N.normalizedPartCentres i) := neg_mem hu
  have hsetneg : (-u) +ᵥ N.normalizedPartCentres i = N.normalizedPartCentres i :=
    (periodGroup_isAddSubgroup _ _).mp hneg
  ext z
  constructor
  · rintro ⟨z₀, ⟨t, ht, rfl⟩, rfl⟩
    obtain ⟨htu, hmap⟩ := hshift t ht
    refine ⟨⟨t.1 + u, htu⟩, ?_, ?_⟩
    · rw [← hset]
      exact Set.mem_vadd_set.mpr ⟨t.1, ht, by simp [add_comm]⟩
    · rw [hE, hE]
      simpa [vadd_eq_add, add_comm] using hmap
  · rintro ⟨y, hy, rfl⟩
    have htm : y.1 - u ∈ N.normalizedPartCentres i := by
      have hmem : -u + y.1 ∈ N.normalizedPartCentres i := by
        rw [← hsetneg]
        exact Set.mem_vadd_set.mpr ⟨y.1, hy, rfl⟩
      simpa [sub_eq_add_neg, add_comm] using hmem
    have htu : y.1 - u ∈ N.context.centres :=
      normalized_part_centres_subset_context N i htm
    obtain ⟨htu', hmap⟩ := hshift ⟨y.1 - u, htu⟩ htm
    refine ⟨E ⟨y.1 - u, htu⟩, ?_, ?_⟩
    · exact ⟨⟨y.1 - u, htu⟩, htm, rfl⟩
    · have hcoord : (y.1 - u : Tiling.Plane) + u = y.1 := by
        apply Complex.ext <;> simp
      change v +ᵥ E ⟨y.1 - u, htu⟩ = E y
      rw [vadd_eq_add, hE, hE]
      have hmap' :
          mapFirstPoint A.phi (N.context.centrePoint y.1 y.2) =
            mapFirstPoint A.phi
              (N.context.centrePoint (⟨y.1 - u, htu⟩ : ↥N.context.centres).1
                (⟨y.1 - u, htu⟩ : ↥N.context.centres).2) + v := by
        simpa [hcoord] using hmap
      simpa [add_comm] using hmap'.symm

private theorem firstCoordinate_geometry_fields
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (A : SharedSlabApproximation N)
    (H : PeriodicTranslatedVertexHomeomorph N A.phi)
    (hH : A.deformation.firstHomeomorph = H.homeomorph)
    (E : ExactFirstCoordinateSlabTransport N A.phi H A.deformation) :
    (∀ i, verticalPeriodVector (P.verticalPeriod i) ∈
      periodGroup (E.deformedPartCentres i)) ∧
    (∀ i, skewPeriodVector (A.rationalHorizontalPeriod : ℝ) (P.shear i) ∈
      periodGroup (E.deformedPartCentres i)) ∧
    frontier E.mappedCarrierBase =
      A.deformation.firstHomeomorph '' frontier N.normalizedCarrierBase ∧
    (∀ i, frontier (E.mappedPartBase i) =
      A.deformation.firstHomeomorph '' frontier (N.normalizedPartBase i)) ∧
    ((∀ v ∈ A.deformation.firstRegion.vertices,
        ∃ q : ℚ, v.re = (q : ℝ)) ∧
      ∀ t ∈ E.deformedCentres,
        ∃ q : ℚ, t.re = (q : ℝ)) := by
  have hperiod (i : Fin P.numberOfParts) (u : Tiling.Plane) (hu : u ∈
      periodGroup (P.partCentres i)) :
      u ∈ periodGroup (N.normalizedPartCentres i) := by
    rw [N.normalizedPartCentres_eq i]
    exact (periodGroup_vadd_iff_local (-N.centreAnchor) u).mpr hu
  have hvertical (i : Fin P.numberOfParts) :
      verticalPeriodVector (P.verticalPeriod i) ∈
        periodGroup (deformedCenterCarrierOn E.centreEmbedding
          {t : ↥N.context.centres |
            (t : Tiling.Plane) ∈ N.normalizedPartCentres i}) := by
    let u : Tiling.Plane := verticalPeriodVector (P.verticalPeriod i)
    have hu : u ∈ periodGroup (N.normalizedPartCentres i) :=
      hperiod i u (P.part_vertical_period i)
    apply periodGroup_mapFirstPoint N A E.centreEmbedding E.centreEmbedding_apply i u u
      hu
    intro t ht
    have hset := (periodGroup_isAddSubgroup _ _).mp hu
    have hmem : t.1 + u ∈ N.normalizedPartCentres i := by
      rw [← hset]
      exact Set.mem_vadd_set.mpr ⟨t.1, ht, by simp [add_comm]⟩
    have htu : t.1 + u ∈ N.context.centres :=
      normalized_part_centres_subset_context N i hmem
    refine ⟨htu, ?_⟩
    apply Complex.ext <;>
      simp [u, mapFirstPoint, ApproximationContext.centrePoint,
        verticalPeriodVector]
  have hskew (i : Fin P.numberOfParts) :
      skewPeriodVector (A.rationalHorizontalPeriod : ℝ) (P.shear i) ∈
        periodGroup (deformedCenterCarrierOn E.centreEmbedding
          {t : ↥N.context.centres |
            (t : Tiling.Plane) ∈ N.normalizedPartCentres i}) := by
    let u : Tiling.Plane := skewPeriodVector P.commonPeriod (P.shear i)
    let v : Tiling.Plane :=
      skewPeriodVector (A.rationalHorizontalPeriod : ℝ) (P.shear i)
    have hu : u ∈ periodGroup (N.normalizedPartCentres i) :=
      hperiod i u (P.part_skew_period i)
    apply periodGroup_mapFirstPoint N A E.centreEmbedding E.centreEmbedding_apply i u v hu
    intro t ht
    have hset := (periodGroup_isAddSubgroup _ _).mp hu
    have hmem : t.1 + u ∈ N.normalizedPartCentres i := by
      rw [← hset]
      exact Set.mem_vadd_set.mpr ⟨t.1, ht, by simp [add_comm]⟩
    have htu : t.1 + u ∈ N.context.centres :=
      normalized_part_centres_subset_context N i hmem
    refine ⟨htu, ?_⟩
    have harg :
        (⟨(t.1 + u).re, N.context.centre_re_mem (t.1 + u) htu⟩ :
          N.context.coordinateSpace) =
        (⟨t.1.re, N.context.centre_re_mem t.1 t.2⟩ :
          N.context.coordinateSpace) +
          (⟨P.commonPeriod, N.commonPeriod_mem⟩ : N.context.coordinateSpace) := by
      apply Subtype.ext
      simp [u, skewPeriodVector]
    have hre : mapScalar A.phi
          ⟨(t.1 + u).re, N.context.centre_re_mem (t.1 + u) htu⟩ =
        mapScalar A.phi ⟨t.1.re, N.context.centre_re_mem t.1 t.2⟩ +
          mapScalar A.phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by
      rw [harg, mapScalar, map_add]
      push_cast
      rfl
    have hre' : mapScalar A.phi
          ⟨t.1.re + P.commonPeriod,
            N.context.coordinateSpace.add_mem
              (N.context.centre_re_mem t.1 t.2) N.commonPeriod_mem⟩ =
        mapScalar A.phi ⟨t.1.re, N.context.centre_re_mem t.1 t.2⟩ +
          mapScalar A.phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by
      convert hre using 1
      all_goals simp [u, skewPeriodVector]
    apply Complex.ext
    · simp [mapFirstPoint, ApproximationContext.centrePoint, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, add_zero, hre', u, v, skewPeriodVector,
        A.rationalHorizontalPeriod_eq]
    · simp [u, v, mapFirstPoint, ApproximationContext.centrePoint,
        skewPeriodVector]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [E.deformedPartCentres_eq] using hvertical i
  · intro i
    simpa only [E.deformedPartCentres_eq] using hskew i
  · rw [E.mappedCarrierBase_eq, hH]
    exact (H.homeomorph.image_frontier _).symm
  · intro i
    rw [E.mappedPartBase_eq, hH]
    exact (H.homeomorph.image_frontier _).symm
  · constructor
    · intro v hv
      rw [Tiling.AxisParallel.Approximation.firstRegion_vertices_image A.deformation] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      have hvertex := congrArg Complex.re
        (A.deformation.first_vertex_agreement w hw)
      refine ⟨A.phi ⟨w.re, N.context.vertex_re_mem w hw⟩, ?_⟩
      simpa [A.deformation.firstPlanarHomeomorph_apply,
        mapFirstPoint, ApproximationContext.vertexPoint,
        mapScalar] using hvertex
    · intro t ht
      rw [E.deformedCentres_eq] at ht
      obtain ⟨s, rfl⟩ := ht
      rw [E.centreEmbedding_apply]
      refine ⟨A.phi ⟨s.1.re, N.context.centre_re_mem s.1 s.2⟩, ?_⟩
      simp [mapFirstPoint, ApproximationContext.centrePoint, mapScalar]

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
private theorem normalized_periodic
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    P.commonPeriod +ᵥ N.normalizedPartBase i = N.normalizedPartBase i := by
  rw [N.normalizedPartBase_eq i]
  have hperiod := slabBases_literalAndCommonPeriodic P |>.2.2.1 i
  calc
    P.commonPeriod +ᵥ (-((N.tileAnchor + N.centreAnchor).re) +ᵥ P.partBase i) =
        -((N.tileAnchor + N.centreAnchor).re) +ᵥ
          (P.commonPeriod +ᵥ P.partBase i) := by
            ext x
            simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
            ring_nf
    _ = -((N.tileAnchor + N.centreAnchor).re) +ᵥ P.partBase i := by rw [hperiod]

private theorem normalized_carrier_periodic
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    P.commonPeriod +ᵥ N.normalizedCarrierBase = N.normalizedCarrierBase := by
  rw [N.normalizedCarrierBase_eq]
  calc
    P.commonPeriod +ᵥ (-((N.tileAnchor + N.centreAnchor).re) +ᵥ P.carrierBase) =
        -((N.tileAnchor + N.centreAnchor).re) +ᵥ
          (P.commonPeriod +ᵥ P.carrierBase) := by
            ext x
            simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
            ring_nf
    _ = -((N.tileAnchor + N.centreAnchor).re) +ᵥ P.carrierBase := by
      rw [P.carrierBase_periodic]

private theorem mapped_periodic
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (phi : N.context.coordinateSpace →ₗ[ℚ] ℚ)
    (H : PeriodicTranslatedVertexHomeomorph N phi)
    (X : Set ℝ) (hX : P.commonPeriod +ᵥ X = X) :
    mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ +ᵥ H.homeomorph '' X =
      H.homeomorph '' X := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, hy⟩
    have hz' : z + P.commonPeriod ∈ X := by
      rw [← hX]
      exact ⟨z, hz, by simp [vadd_eq_add, add_comm]⟩
    refine ⟨z + P.commonPeriod, hz', ?_⟩
    rw [H.period_equivariant]
    simpa [vadd_eq_add, add_comm] using hy
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - P.commonPeriod ∈ X := by
      rw [← hX, Set.mem_vadd_set_iff_neg_vadd_mem] at hz
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hz
    refine ⟨H.homeomorph (z - P.commonPeriod), ⟨z - P.commonPeriod, hz', rfl⟩, ?_⟩
    have hp := H.period_equivariant (z - P.commonPeriod)
    calc
      mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ +
          H.homeomorph (z - P.commonPeriod) =
          H.homeomorph (z - P.commonPeriod) +
            mapScalar phi ⟨P.commonPeriod, N.commonPeriod_mem⟩ := by ring
      _ = H.homeomorph ((z - P.commonPeriod) + P.commonPeriod) := hp.symm
      _ = H.homeomorph z := by congr 1; ring

private theorem diff_measure_zero
    {n : ℕ} (C : Set ℝ) (B : Fin n → Set ℝ)
    (hC : MeasurableSet C)
    (hBopen : ∀ i, IsOpen (B i))
    (hpartition : volume.restrict C = ∑ i, volume.restrict (B i)) :
    volume (C \ ⋃ i, B i) = 0 := by
  let D : Set ℝ := C \ ⋃ i, B i
  have hD : MeasurableSet D := hC.diff (isOpen_iUnion hBopen).measurableSet
  have hDC : D ⊆ C := fun x hx => hx.1
  have hzero : (∑ i, volume.restrict (B i)) D = 0 := by
    simp only [Measure.coe_finsetSum, Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Measure.restrict_apply hD]
    have hDB : D ∩ B i = ∅ := by
      ext x
      constructor
      · rintro ⟨hxD, hxB⟩
        exact hxD.2 (Set.mem_iUnion.mpr ⟨i, hxB⟩)
      · intro hx
        exact False.elim hx
    rw [hDB, measure_empty]
  rw [show volume D = volume.restrict C D by
    rw [Measure.restrict_apply hD, Set.inter_eq_left.mpr hDC], hpartition, hzero]

private theorem diff_subset_iUnion_frontier
    {n : ℕ} (C : Set ℝ) (B : Fin n → Set ℝ)
    (hCopen : IsOpen C) (hBopen : ∀ i, IsOpen (B i))
    (hnull : volume (C \ ⋃ i, B i) = 0) :
    C \ ⋃ i, B i ⊆ ⋃ i, frontier (B i) := by
  intro x hx
  by_contra hnot
  have hnot_i (i : Fin n) : x ∉ frontier (B i) := by
    intro hxi
    exact hnot (Set.mem_iUnion.mpr ⟨i, hxi⟩)
  have hnot_closure (i : Fin n) : x ∉ closure (B i) := by
    intro hxi
    apply hnot_i i
    rw [frontier, (hBopen i).interior_eq]
    exact ⟨hxi, fun hxin ↦ hx.2 (Set.mem_iUnion.mpr ⟨i, hxin⟩)⟩
  let U : Set ℝ := C ∩ ⋂ i, (closure (B i))ᶜ
  have hUopen : IsOpen U := by
    exact hCopen.inter (isOpen_iInter_of_finite fun i ↦ isOpen_compl_iff.mpr isClosed_closure)
  have hxU : x ∈ U := by
    refine ⟨hx.1, ?_⟩
    exact mem_iInter.2 hnot_closure
  have hUsub : U ⊆ C \ ⋃ i, B i := by
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro hyU
    obtain ⟨i, hyi⟩ := Set.mem_iUnion.mp hyU
    exact (Set.mem_iInter.mp hy.2 i) (subset_closure hyi)
  have hUzero : volume U = 0 := measure_mono_null hUsub hnull
  exact (hUopen.measure_ne_zero volume ⟨x, hxU⟩) hUzero

private theorem partition_of_diff_zero
    {n : ℕ} (C : Set ℝ) (B : Fin n → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hsubset : ∀ i, B i ⊆ C)
    (hdisjoint : Set.PairwiseDisjoint Set.univ B)
    (hnull : volume (C \ ⋃ i, B i) = 0) :
    volume.restrict C = ∑ i, volume.restrict (B i) := by
  let U : Set ℝ := ⋃ i, B i
  have hUC : U ⊆ C := by
    intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact hsubset i hxi
  have hae : C =ᵐ[volume] U := by
    apply ae_eq_set.mpr
    refine ⟨hnull, ?_⟩
    rw [sdiff_eq_empty.mpr hUC]
    exact measure_empty
  rw [Measure.restrict_congr_set hae,
    Measure.restrict_iUnion
      (fun i j hij ↦ hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hB,
    Measure.sum_fintype]

private theorem image_diff_subset_frontiers
    {n : ℕ} (H : ℝ ≃ₜ ℝ) (C : Set ℝ) (B : Fin n → Set ℝ)
    (hsource : C \ ⋃ i, B i ⊆ ⋃ i, frontier (B i)) :
    H '' C \ ⋃ i, H '' B i ⊆ ⋃ i, frontier (H '' B i) := by
  intro y hy
  obtain ⟨x, hxC, rfl⟩ := hy.1
  have hxnot : x ∉ ⋃ i, B i := by
    intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    apply hy.2
    exact Set.mem_iUnion.mpr ⟨i, ⟨x, hxi, rfl⟩⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hsource ⟨hxC, hxnot⟩)
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [← H.image_frontier]
  exact ⟨x, hxi, rfl⟩

private theorem normalized_part_subset
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    N.normalizedPartBase i ⊆ N.normalizedCarrierBase := by
  rw [N.normalizedPartBase_eq i, N.normalizedCarrierBase_eq]
  obtain ⟨hsubset, _, _, _⟩ := slabBases_literalAndCommonPeriodic P
  intro x hx
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx ⊢
  exact hsubset i (by simpa using hx)

private theorem normalized_base_open_regular
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) :
    IsOpen N.normalizedCarrierBase ∧
      interior (closure N.normalizedCarrierBase) = N.normalizedCarrierBase := by
  constructor
  · rw [N.normalizedCarrierBase_eq]
    exact (Homeomorph.addLeft (-((N.tileAnchor + N.centreAnchor).re))).isOpenMap _
      P.carrierBase_open
  · rw [N.normalizedCarrierBase_eq]
    let T := Homeomorph.addLeft (-((N.tileAnchor + N.centreAnchor).re))
    change interior (closure (T '' P.carrierBase)) = T '' P.carrierBase
    rw [← T.image_closure, ← T.image_interior, P.carrierBase_regular]

private theorem normalized_part_open_regular
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) (i : Fin P.numberOfParts) :
    IsOpen (N.normalizedPartBase i) ∧
      interior (closure (N.normalizedPartBase i)) = N.normalizedPartBase i := by
  constructor
  · rw [N.normalizedPartBase_eq i]
    exact (Homeomorph.addLeft (-((N.tileAnchor + N.centreAnchor).re))).isOpenMap _
      (P.partBase_open i)
  · rw [N.normalizedPartBase_eq i]
    let T := Homeomorph.addLeft (-((N.tileAnchor + N.centreAnchor).re))
    change interior (closure (T '' P.partBase i)) = T '' P.partBase i
    rw [← T.image_closure, ← T.image_interior, P.partBase_regular i]

private theorem mapped_frontier_countable_of_tiles
    {K : Region} {S : Set Tiling.Plane}
    (H : ℝ ≃ₜ ℝ) (X : Set ℝ) (hopen : IsOpen X)
    (hregular : interior (closure X) = X)
    (hTile : TilesOn K S (Complex.re ⁻¹' X)) :
    (frontier (H '' X)).Countable := by
  apply Tiling.AxisParallel.Foundations.countable_of_locallyFinite_inter
  intro Q hQ
  obtain ⟨R, hQR⟩ := hQ.subset_closedBall 0
  have hfront := homeomorph_image_frontier_locallyFinite H X
    (fun C hC ↦ hTile.verticalCylinder_frontier_locallyFinite hopen hregular C hC)
      (-R) R
  apply hfront.subset
  intro x hx
  refine ⟨hx.1, ?_⟩
  have hxball := hQR hx.2
  rw [Metric.mem_closedBall, Real.dist_eq] at hxball
  exact abs_le.mp (by simpa using hxball)

private theorem normalized_part_disjoint
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P) {i j : Fin P.numberOfParts} (hij : i ≠ j) :
    Disjoint (N.normalizedPartBase i) (N.normalizedPartBase j) := by
  rw [N.normalizedPartBase_eq i, N.normalizedPartBase_eq j]
  have hdis := (slabBases_literalAndCommonPeriodic P).2.1 i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  apply Set.disjoint_left.mp hdis
  · exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hxi
  · exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hxj

private theorem mapped_base_measure_fields
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (A : SharedSlabApproximation N)
    (H : PeriodicTranslatedVertexHomeomorph N A.phi)
    (hH : A.deformation.firstHomeomorph = H.homeomorph)
    (E : ExactFirstCoordinateSlabTransport N A.phi H A.deformation) :
    Set.PairwiseDisjoint Set.univ
        (fun i ↦ volume.restrict (E.mappedPartBase i)) ∧
      volume.restrict E.mappedCarrierBase =
        ∑ i, volume.restrict (E.mappedPartBase i) := by
  have hsourceNull :
      volume (P.carrierBase \ ⋃ i, P.partBase i) = 0 :=
    diff_measure_zero P.carrierBase P.partBase P.carrierBase_open.measurableSet
      (fun i ↦ P.partBase_open i) P.partBase_ae_partition
  have hnormDiff :
      N.normalizedCarrierBase \ ⋃ i, N.normalizedPartBase i =
        (-((N.tileAnchor + N.centreAnchor).re)) +ᵥ
          (P.carrierBase \ ⋃ i, P.partBase i) := by
    rw [N.normalizedCarrierBase_eq]
    simp_rw [N.normalizedPartBase_eq]
    ext x
    simp only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
  have hnormNull :
      volume (N.normalizedCarrierBase \ ⋃ i, N.normalizedPartBase i) = 0 := by
    rw [hnormDiff, MeasureTheory.measure_vadd]
    exact hsourceNull
  obtain ⟨hCopen, hCreg⟩ := normalized_base_open_regular N
  have hBopen (i : Fin P.numberOfParts) : IsOpen (N.normalizedPartBase i) :=
    (normalized_part_open_regular N i).1
  have hBreg (i : Fin P.numberOfParts) :
      interior (closure (N.normalizedPartBase i)) = N.normalizedPartBase i :=
    (normalized_part_open_regular N i).2
  have hsourceFront :
      N.normalizedCarrierBase \ ⋃ i, N.normalizedPartBase i ⊆
        ⋃ i, frontier (N.normalizedPartBase i) :=
    diff_subset_iUnion_frontier N.normalizedCarrierBase N.normalizedPartBase
      hCopen hBopen hnormNull
  have hmappedDiff :
      E.mappedCarrierBase \ ⋃ i, E.mappedPartBase i ⊆
        ⋃ i, frontier (E.mappedPartBase i) := by
    rw [E.mappedCarrierBase_eq]
    simp_rw [E.mappedPartBase_eq]
    rw [← hH]
    exact image_diff_subset_frontiers A.deformation.firstHomeomorph _ _ hsourceFront
  have hmappedFrontCount (i : Fin P.numberOfParts) :
      (frontier (E.mappedPartBase i)).Countable := by
    rw [E.mappedPartBase_eq i, ← hH]
    exact mapped_frontier_countable_of_tiles A.deformation.firstHomeomorph
      (N.normalizedPartBase i) (hBopen i) (hBreg i)
        (N.normalized_part_tiles i)
  have hfrontNull : volume (⋃ i, frontier (E.mappedPartBase i)) = 0 :=
    measure_iUnion_null fun i ↦ (hmappedFrontCount i).measure_zero volume
  have hmappedNull :
      volume (E.mappedCarrierBase \ ⋃ i, E.mappedPartBase i) = 0 :=
    measure_mono_null hmappedDiff hfrontNull
  have hmappedSubset (i : Fin P.numberOfParts) :
      E.mappedPartBase i ⊆ E.mappedCarrierBase := by
    rw [E.mappedPartBase_eq i, E.mappedCarrierBase_eq]
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x, normalized_part_subset N i hx, rfl⟩
  have hmappedOpen (i : Fin P.numberOfParts) : IsOpen (E.mappedPartBase i) := by
    rw [E.mappedPartBase_eq i]
    exact H.homeomorph.isOpenMap _ (hBopen i)
  have hmappedMeas (i : Fin P.numberOfParts) :
      MeasurableSet (E.mappedPartBase i) := (hmappedOpen i).measurableSet
  have hmappedDisjoint :
      Set.PairwiseDisjoint Set.univ E.mappedPartBase := by
    intro i hi j hj hij
    change Disjoint (E.mappedPartBase i) (E.mappedPartBase j)
    rw [E.mappedPartBase_eq i, E.mappedPartBase_eq j]
    rw [Set.disjoint_left]
    rintro y ⟨x, hxi, rfl⟩ ⟨z, hxj, hyz⟩
    have hxz : x = z := H.homeomorph.injective hyz.symm
    exact Set.disjoint_left.mp (normalized_part_disjoint N hij) hxi (hxz ▸ hxj)
  refine ⟨?_, ?_⟩
  · intro i hi j hj hij
    have hset := hmappedDisjoint hi hj hij
    have hleft :
        (volume.restrict (E.mappedPartBase i)) (E.mappedPartBase j) = 0 := by
      rw [Measure.restrict_apply (hmappedMeas j)]
      rw [Set.inter_comm, Set.disjoint_iff_inter_eq_empty.mp hset, measure_empty]
    have hright :
        (volume.restrict (E.mappedPartBase j)) (E.mappedPartBase j)ᶜ = 0 := by
      rw [Measure.restrict_apply (hmappedMeas j).compl]
      rw [Set.compl_inter_self, measure_empty]
    exact (Measure.MutuallySingular.mk hleft hright (by simp)).disjoint
  · exact partition_of_diff_zero _ _
      hmappedMeas
      hmappedSubset hmappedDisjoint hmappedNull

private theorem mappedCarrierBase_periodic
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (A : SharedSlabApproximation N)
    (H : PeriodicTranslatedVertexHomeomorph N A.phi)
    (E : ExactFirstCoordinateSlabTransport N A.phi H A.deformation) :
    (A.rationalHorizontalPeriod : ℝ) +ᵥ E.mappedCarrierBase =
      E.mappedCarrierBase := by
  rw [E.mappedCarrierBase_eq, A.rationalHorizontalPeriod_eq]
  exact mapped_periodic N A.phi H _ (normalized_carrier_periodic N)

private theorem mappedPartBase_periodic
    {K : Region} {S : Set Tiling.Plane} {P : FiniteSlabPartition K S}
    (N : NormalizedSlabData P)
    (A : SharedSlabApproximation N)
    (H : PeriodicTranslatedVertexHomeomorph N A.phi)
    (E : ExactFirstCoordinateSlabTransport N A.phi H A.deformation)
    (i : Fin P.numberOfParts) :
    (A.rationalHorizontalPeriod : ℝ) +ᵥ E.mappedPartBase i =
      E.mappedPartBase i := by
  rw [E.mappedPartBase_eq i, A.rationalHorizontalPeriod_eq]
  exact mapped_periodic N A.phi H _ (normalized_periodic N i)
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
private theorem base_nonempty_of_support
    {C : Region} {T : Set Tiling.Plane} {X : Set ℝ}
    (hT : T.Nonempty)
    (hSupport : regularSupport C T = Complex.re ⁻¹' X) : X.Nonempty := by
  have hopen : IsOpen (openUnion C T) := by
    rw [openUnion]
    exact isOpen_iUnion fun t ↦ (Region.openCarrier_regularOpen C).1.vadd t.1
  have hcarrier : C.openCarrier.Nonempty :=
    C.isPolygonal.interior_nonempty C.nonempty
  obtain ⟨t, ht⟩ := hT
  obtain ⟨z, hz⟩ := hcarrier
  have hzU : t +ᵥ z ∈ openUnion C T := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨t, ht⟩, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩⟩
  have hzR : t +ᵥ z ∈ regularSupport C T := by
    change t +ᵥ z ∈ interior (closure (openUnion C T))
    exact hopen.subset_interior_closure hzU
  rw [hSupport] at hzR
  exact ⟨(t +ᵥ z).re, hzR⟩
private theorem firstCoordinateSlabTransport_of_exact :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} {N : NormalizedSlabData P}
      (A : SharedSlabApproximation N)
      (H : PeriodicTranslatedVertexHomeomorph N A.phi)
      (_hH : A.deformation.firstHomeomorph = H.homeomorph)
      (_E : ExactFirstCoordinateSlabTransport N A.phi H A.deformation),
    Nonempty (FirstCoordinateSlabTransport A) := by
  intro K S P N A H hH E
  have hpartCentresNonempty (i : Fin P.numberOfParts) :
      (N.normalizedPartCentres i).Nonempty := by
    rw [N.normalizedPartCentres_eq i]
    obtain ⟨s, hs⟩ := P.partCentres_nonempty i
    exact ⟨-N.centreAnchor + s, Set.mem_vadd_set.mpr ⟨s, hs, rfl⟩⟩
  have hctxCentresNonempty : N.context.centres.Nonempty := by
    rw [N.context_centres]
    exact ⟨-N.centreAnchor + N.centreAnchor,
      Set.mem_vadd_set.mpr ⟨N.centreAnchor, N.centreAnchor_mem, rfl⟩⟩
  have hpartNonempty (i : Fin P.numberOfParts) :
      (E.deformedPartCentres i).Nonempty := by
    rw [E.deformedPartCentres_eq i]
    obtain ⟨s, hs⟩ := hpartCentresNonempty i
    have hctx : s ∈ N.context.centres := normalized_part_centres_subset_context N i hs
    refine ⟨E.centreEmbedding ⟨s, hctx⟩, ?_⟩
    exact ⟨⟨s, hctx⟩, hs, rfl⟩
  have hpartPairwise :
      Set.PairwiseDisjoint Set.univ E.deformedPartCentres := by
    intro i hi j hj hij
    change Disjoint (E.deformedPartCentres i) (E.deformedPartCentres j)
    rw [E.deformedPartCentres_eq i, E.deformedPartCentres_eq j]
    rw [Set.disjoint_left]
    rintro z ⟨x, hxi, rfl⟩ ⟨y, hxj, hxy⟩
    have hxy' : y = x := E.centreEmbedding.injective hxy
    subst y
    apply Set.disjoint_left.mp
      (show Disjoint (N.normalizedPartCentres i) (N.normalizedPartCentres j) from ?_)
      hxi hxj
    rw [N.normalizedPartCentres_eq i, N.normalizedPartCentres_eq j]
    rw [Set.disjoint_left]
    intro w hwi hwj
    apply Set.disjoint_left.mp (P.partCentres_pairwise hi hj hij)
    · exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hwi
    · exact Set.mem_vadd_set_iff_neg_vadd_mem.mp hwj
  have hpartUnion :
      (⋃ i, E.deformedPartCentres i) = E.deformedCentres := by
    rw [E.deformedCentres_eq]
    ext z
    constructor
    · intro hz
      obtain ⟨i, hzi⟩ := Set.mem_iUnion.mp hz
      rw [E.deformedPartCentres_eq i] at hzi
      obtain ⟨t, ht, rfl⟩ := hzi
      exact ⟨t, rfl⟩
    · rintro ⟨t, rfl⟩
      have hparts : (⋃ i, N.normalizedPartCentres i) = N.context.centres := by
        rw [N.context_centres]
        ext x
        constructor
        · intro hx
          obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
          rw [N.normalizedPartCentres_eq i,
            Set.mem_vadd_set_iff_neg_vadd_mem] at hxi
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          let U : Set Tiling.Plane := ⋃ i, P.partCentres i
          have hU : U = S := P.partCentres_union
          have hUmem : -(-N.centreAnchor) +ᵥ x ∈ U := by
            exact Set.mem_iUnion.mpr ⟨i, hxi⟩
          exact (Set.ext_iff.mp hU) _ |>.mp hUmem
        · intro hx
          have hxS : -(-N.centreAnchor) + x ∈ S :=
            Set.mem_vadd_set_iff_neg_vadd_mem.mp hx
          have hxS' : -(-N.centreAnchor) + x ∈
              (⋃ i, P.partCentres i) := by
            let U : Set Tiling.Plane := ⋃ i, P.partCentres i
            have hU : U = S := P.partCentres_union
            exact (Set.ext_iff.mp hU) _ |>.mpr hxS
          obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxS'
          refine Set.mem_iUnion.mpr ⟨i, ?_⟩
          rw [N.normalizedPartCentres_eq i,
            Set.mem_vadd_set_iff_neg_vadd_mem]
          exact hxi
      have htparts : t.1 ∈ ⋃ i, N.normalizedPartCentres i := by
        rw [hparts]
        exact t.2
      obtain ⟨i, hti⟩ := Set.mem_iUnion.mp htparts
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [E.deformedPartCentres_eq i]
      exact ⟨t, hti, rfl⟩
  have hcarrierOpen : IsOpen (E.mappedCarrierBase) := by
    rw [E.mappedCarrierBase_eq]
    obtain ⟨hopen, _⟩ := normalized_base_open_regular N
    exact H.homeomorph.isOpenMap _ hopen
  have hcarrierRegular :
      interior (closure E.mappedCarrierBase) = E.mappedCarrierBase := by
    rw [E.mappedCarrierBase_eq]
    obtain ⟨_, hreg⟩ := normalized_base_open_regular N
    rw [← H.homeomorph.image_closure, ← H.homeomorph.image_interior, hreg]
  have hcarrierNonempty : E.mappedCarrierBase.Nonempty := by
    rw [E.mappedCarrierBase_eq]
    have hbase := base_nonempty_of_support hctxCentresNonempty
      (normalizedCarrier_sourceSupport N)
    obtain ⟨r, hr⟩ := hbase
    exact ⟨H.homeomorph r, ⟨r, hr, rfl⟩⟩
  have hcarrierNonnull : volume E.mappedCarrierBase ≠ 0 :=
    hcarrierOpen.measure_ne_zero volume hcarrierNonempty
  have hpartOpen (i : Fin P.numberOfParts) : IsOpen (E.mappedPartBase i) := by
    rw [E.mappedPartBase_eq i]
    exact H.homeomorph.isOpenMap _ (normalized_part_open_regular N i).1
  have hpartRegular (i : Fin P.numberOfParts) :
      interior (closure (E.mappedPartBase i)) = E.mappedPartBase i := by
    rw [E.mappedPartBase_eq i]
    rw [← H.homeomorph.image_closure, ← H.homeomorph.image_interior,
      (normalized_part_open_regular N i).2]
  have hpartNonnull (i : Fin P.numberOfParts) :
      volume (E.mappedPartBase i) ≠ 0 := by
    apply (hpartOpen i).measure_ne_zero volume
    rw [E.mappedPartBase_eq i]
    obtain ⟨r, hr⟩ := base_nonempty_of_support (hpartCentresNonempty i)
      (normalizedPart_sourceSupport N i)
    exact ⟨H.homeomorph r, ⟨r, hr, rfl⟩⟩
  have hgeom := firstCoordinate_geometry_fields N A H hH E
  have hmeasure := mapped_base_measure_fields N A H hH E
  exact ⟨{
    centreEmbedding := E.centreEmbedding
    centreEmbedding_apply := E.centreEmbedding_apply
    deformedCentres := E.deformedCentres
    deformedCentres_eq := E.deformedCentres_eq
    deformedPartCentres := E.deformedPartCentres
    deformedPartCentres_eq := E.deformedPartCentres_eq
    deformedPartCentres_nonempty := hpartNonempty
    deformedPartCentres_pairwise := hpartPairwise
    deformedPartCentres_union := hpartUnion
    deformedCarrierBase := E.mappedCarrierBase
    deformedCarrierBase_open := hcarrierOpen
    deformedCarrierBase_regular := hcarrierRegular
    deformedCarrierBase_nonnull := hcarrierNonnull
    deformedPartBase := E.mappedPartBase
    deformedPartBase_open := hpartOpen
    deformedPartBase_regular := hpartRegular
    deformedPartBase_nonnull := hpartNonnull
    deformedPartBase_ae_disjoint := hmeasure.1
    deformedPartBase_ae_partition := hmeasure.2
    deformed_tiles := E.full_tiles
    deformed_support := E.full_support_cylinder
    deformed_part_tiles := E.part_tiles
    deformed_part_support := E.part_support_cylinder
    deformedCarrierBase_periodic := mappedCarrierBase_periodic N A H E
    deformedPartBase_periodic := mappedPartBase_periodic N A H E
    deformed_part_vertical_period := hgeom.1
    deformed_part_skew_period := hgeom.2.1
    carrier_frontier_transport := hgeom.2.2.1
    part_frontier_transport := hgeom.2.2.2.1
    deformed_first_coordinates_rational := hgeom.2.2.2.2 }⟩
end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
private theorem firstCoordinateSlabTransport_exists :
    ∀ {K : Region} {S : Set Tiling.Plane}
      {P : FiniteSlabPartition K S} {N : NormalizedSlabData P}
      (A : SharedSlabApproximation N),
    Nonempty (FirstCoordinateSlabTransport A) := by
  intro K S P N A
  let H : PeriodicTranslatedVertexHomeomorph N A.phi := {
    homeomorph := A.deformation.firstHomeomorph
    strictMono := A.deformation.firstHomeomorph_strictMono
    translatedVertex_agreement := A.firstHomeomorph_translatedVertex_agreement
    period_equivariant := A.firstHomeomorph_period_equivariant }
  obtain ⟨E⟩ := exactFirstCoordinateSlabTransport_exists
    N A.phi H A.deformation rfl
  exact firstCoordinateSlabTransport_of_exact A H rfl E

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation

theorem exists_simultaneousSlabRationalization :
    ∀ {K : Region} {S : Set Plane}
      (P : FiniteSlabPartition K S),
    Nonempty (SlabRationalization K S P) := by
  intro K S P
  obtain ⟨N⟩ := normalizedSlabData_exists P
  obtain ⟨A⟩ := sharedSlabApproximation_exists N
  obtain ⟨D⟩ := firstCoordinateSlabTransport_exists A
  obtain ⟨mass, hmass, hmass_eq⟩ := rationalPeriodCellMasses D
  exact slabRationalization_of_sharedTransport N A D mass hmass hmass_eq

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation

/-- Rationalize two labelled blocks through one shared finite-partition construction. -/
theorem exists_twoBlockMixedRationalizationDatum :
    ∀ {K : Tiling.AxisParallel.Region}
      {SNonColumn SColumn S : Set Tiling.Plane}
      {XNonColumn XColumn X : Set ℝ},
    IsOpen X → interior (closure X) = X →
    MeasureTheory.volume X ≠ 0 →
    IsOpen XNonColumn → interior (closure XNonColumn) = XNonColumn →
    IsOpen XColumn → interior (closure XColumn) = XColumn →
    (Disjoint SNonColumn SColumn ∧ SNonColumn ∪ SColumn = S) →
    (SNonColumn.Nonempty ∧ SColumn.Nonempty) →
    Disjoint (MeasureTheory.volume.restrict XNonColumn)
      (MeasureTheory.volume.restrict XColumn) →
    MeasureTheory.volume.restrict X =
      MeasureTheory.volume.restrict XNonColumn +
        MeasureTheory.volume.restrict XColumn →
    Tiling.AxisParallel.TilesOn K S (Complex.re ⁻¹' X) →
    Tiling.AxisParallel.TilesOn K SNonColumn (Complex.re ⁻¹' XNonColumn) →
    Tiling.AxisParallel.TilesOn K SColumn (Complex.re ⁻¹' XColumn) →
    ∀ {alpha alphaColumn beta betaColumn z w B : ℝ},
      0 < alpha → 0 < alphaColumn → 0 < beta → 0 < betaColumn →
      verticalPeriodVector alpha ∈ Tiling.AxisParallel.periodGroup SNonColumn →
      skewPeriodVector beta z ∈ Tiling.AxisParallel.periodGroup SNonColumn →
      verticalPeriodVector alphaColumn ∈ Tiling.AxisParallel.periodGroup SColumn →
      skewPeriodVector betaColumn w ∈ Tiling.AxisParallel.periodGroup SColumn →
      ∀ {n nColumn : ℕ}, 0 < n → 0 < nColumn →
      ((n : ℝ) * beta = B ∧ (nColumn : ℝ) * betaColumn = B) →
        ∃ D : MixedRationalizationDatum alpha alphaColumn B,
          D.nonColumnShear = (n : ℝ) * z ∧
          D.columnShear = (nColumn : ℝ) * w := by
  intro K SNonColumn SColumn S XNonColumn XColumn X
    hXopen hXregular hXnonnull hNCopen hNCregular hCopen hCregular
    hCentres hNonempty hBasesDisjoint hBasesPartition hTiles hNCTiles hCTiles
    alpha alphaColumn beta betaColumn z w B hAlpha hAlphaColumn hBeta hBetaColumn
    hNCVertical hNCSkew hCVertical hCSkew n nColumn hn hnColumn hCommon
  let I : TwoBlockSlabInput K SNonColumn SColumn S
      XNonColumn XColumn X alpha alphaColumn beta betaColumn z w B n nColumn :=
    { carrier_open := hXopen
      carrier_regular := hXregular
      carrier_nonnull := hXnonnull
      nonColumn_open := hNCopen
      nonColumn_regular := hNCregular
      column_open := hCopen
      column_regular := hCregular
      centres_disjoint := hCentres.1
      centres_union := hCentres.2
      nonColumn_nonempty := hNonempty.1
      column_nonempty := hNonempty.2
      bases_ae_disjoint := hBasesDisjoint
      bases_ae_partition := hBasesPartition
      tiles := hTiles
      nonColumn_tiles := hNCTiles
      column_tiles := hCTiles
      alpha_pos := hAlpha
      alphaColumn_pos := hAlphaColumn
      beta_pos := hBeta
      betaColumn_pos := hBetaColumn
      nonColumn_vertical := hNCVertical
      nonColumn_skew := hNCSkew
      column_vertical := hCVertical
      column_skew := hCSkew
      nonColumnMultiplier_pos := hn
      columnMultiplier_pos := hnColumn
      nonColumn_common := hCommon.1
      column_common := hCommon.2 }
  obtain ⟨P, iNonColumn, iColumn, hne, hAll, hCarrier, hPeriod,
      hNCentres, hCCentres, hNBase, hCBase, hNVertical, hCVertical,
      hNShear, hCShear⟩ := twoBlockFiniteSlabPartition_exists I
  obtain ⟨R⟩ := exists_simultaneousSlabRationalization P
  exact twoBlockRationalization_toMixedDatum I P iNonColumn iColumn hne hAll hCarrier hPeriod
    hNCentres hCCentres hNBase hCBase hNVertical hCVertical hNShear hCShear R

end Tiling.AxisParallel.Terminal
