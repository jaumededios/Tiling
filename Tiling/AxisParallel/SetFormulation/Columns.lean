import Tiling.AxisParallel.SetFormulation.Basic
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Structure.PlateThickness

/-!
# Semantic columns and earthquake components

This module identifies invariant line fibres and minimal
invariant subfamilies with the production contact components. All bridges use
the open carrier of an existing production region.
-/

set_option autoImplicit false

open MeasureTheory Set Submodule
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.SetFormulation.Columns

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous

/-- The set formulation and structured regions regularize the same open union. -/
theorem coveredRegion_openCarrier (K : Region) (S : Set Plane) :
    coveredRegion K.openCarrier S = regularSupport K S := by
  apply congrArg interior
  apply congrArg closure
  change S +ᵥ K.openCarrier = ⋃ s : S, (s : Plane) +ᵥ K.openCarrier
  ext z
  simp only [Set.mem_vadd_set, Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht, u, hu, rfl⟩
    exact ⟨⟨t, ht⟩, u, hu, rfl⟩
  · rintro ⟨t, u, hu, rfl⟩
    exact ⟨t, t.2, u, hu, rfl⟩

/-- The imaginary-axis line through t is the fibre of its real coordinate. -/
theorem lineFibre_vertical (T : Set Plane) (t : Plane) :
    lineFibre Complex.I T t = T ∩ {z | z.re = t.re} := by
  ext z
  simp only [lineFibre, Set.mem_inter_iff, Set.mem_vadd_set]
  constructor
  · rintro ⟨hz, w, hw, rfl⟩
    refine ⟨hz, ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [Complex.add_re]
  · rintro ⟨hz, hreal⟩
    change z.re = t.re at hreal
    refine ⟨hz, z - t, ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨z.im - t.im, ?_⟩
      apply Complex.ext <;> simp [hreal]
    · simp [vadd_eq_add]

/-- Vector invariance along I is the production vertical-invariance predicate. -/
theorem invariant_vertical_iff (D : Set Plane) :
    IsInvariantAlong D Complex.I ↔ ∀ a : ℝ, ((a : ℂ) * Complex.I) +ᵥ D = D := by
  simp only [IsInvariantAlong, IsPeriod, Complex.real_smul]

/-- Invariance of a regularized support is equivalent to regular slab support. -/
theorem invariant_iff_verticalSlab (K : Region) (S : Set Plane) :
    IsInvariantAlong (coveredRegion K.openCarrier S) Complex.I ↔
      ∃ X : Set ℝ, X = interior (closure X) ∧
        regularSupport K S = Complex.re ⁻¹' X := by
  rw [coveredRegion_openCarrier, invariant_vertical_iff]
  constructor
  · intro h
    obtain ⟨X, hX⟩ := (verticalInvariant_iff_product (regularSupport K S)).mp h
    refine ⟨X, ?_, hX⟩
    have hr := (regularSupport_isRegularOpen K S).2
    rw [hX] at hr
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X at hr
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re] at hr
    exact ((Set.preimage_injective.mpr Complex.re_surjective) hr).symm
  · rintro ⟨X, _, hX⟩
    exact (verticalInvariant_iff_product (regularSupport K S)).mpr ⟨X, hX⟩

/-- Semantic inclusion-minimal invariant families are exactly minimal slab families. -/
theorem component_iff_minimalSlab (K : Region) (T S : Set Plane) :
    IsEarthquakeComponent K.openCarrier Complex.I T S ↔
      IsMinimalVerticalSlabSubfamily K T S := by
  simp only [IsEarthquakeComponent, IsMinimalVerticalSlabSubfamily,
    invariant_iff_verticalSlab]

private theorem plate_centres_nonempty {K : Region} {T : Set Plane}
    (P : VerticalPlate K T) : P.centres.Nonempty := by
  obtain ⟨p, hp⟩ := P.nonempty_supp
  exact ⟨p, p, hp, rfl⟩

private theorem plate_centres_subset {K : Region} {T : Set Plane}
    (P : VerticalPlate K T) : P.centres ⊆ T := by
  rintro _ ⟨p, _, rfl⟩
  exact p.2

private theorem packing_subfamily {K : Region} {T E A : Set Plane}
    (hTile : TilesOn K T E) (hA : A ⊆ T) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements A) := by
  apply (isPacking_iff_openCarrier_disjoint K A).mpr
  intro s hs t ht hst
  exact (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1 (hA hs) (hA ht) hst

private theorem centre_tile_subset_support (K : Region) {A : Set Plane}
    {t : Plane} (ht : t ∈ A) : t +ᵥ K.openCarrier ⊆ regularSupport K A := by
  have hopen : IsOpen (openUnion K A) :=
    isOpen_iUnion fun s : A => K.openCarrier_regularOpen.1.vadd (s : Plane)
  apply Set.Subset.trans _ hopen.subset_interior_closure
  exact Set.subset_iUnion_of_subset ⟨t, ht⟩ Set.Subset.rfl

/-- A centre-subfamily is determined by its regularized support within a packing. -/
theorem centres_subset_of_support_subset {K : Region} {T E A B : Set Plane}
    (hTile : TilesOn K T E) (hA : A ⊆ T) (hB : B ⊆ T)
    (hsupport : regularSupport K A ⊆ regularSupport K B) : A ⊆ B := by
  intro t htA
  by_contra htB
  have hdisjoint : Disjoint (t +ᵥ K.openCarrier) (openUnion K B) := by
    change Disjoint (t +ᵥ K.openCarrier) (⋃ b : B, (b : Plane) +ᵥ K.openCarrier)
    apply Set.disjoint_iUnion_right.mpr
    intro b
    apply (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1 (hA htA) (hB b.2)
    intro htb
    exact htB (htb.symm ▸ b.2)
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have htuA : t + u ∈ regularSupport K A :=
    centre_tile_subset_support K htA ⟨u, hu, rfl⟩
  have htuB : t + u ∈ closure (openUnion K B) := interior_subset (hsupport htuA)
  exact Set.disjoint_left.mp
    (hdisjoint.closure_right (K.openCarrier_regularOpen.1.vadd t)) ⟨u, hu, rfl⟩ htuB

private theorem centerColumn_of_invariant {K : Region} {T E C : Set Plane}
    (hTile : TilesOn K T E) (hCT : C ⊆ T) (hCnonempty : C.Nonempty)
    (x : ℝ) (hcoord : ∀ z ∈ C, z.re = x)
    (hinvariant : IsInvariantAlong (coveredRegion K.openCarrier C) Complex.I) :
    IsCenterColumn Axis.vertical K C := by
  refine ⟨packing_subfamily hTile hCT, hCnonempty, ⟨x, hcoord⟩, ?_⟩
  rw [coveredRegion_openCarrier, invariant_vertical_iff] at hinvariant
  exact hinvariant

private theorem centerColumn_support_at {K : Region} {C : Set Plane}
    (hC : IsCenterColumn Axis.vertical K C)
    (x : ℝ) (hcoord : ∀ z ∈ C, z.re = x) :
    regularSupport K C = Complex.re ⁻¹'
      interior (closure (x +ᵥ (Complex.re '' K.openCarrier))) := by
  obtain ⟨a, hne, ha, hs⟩ := centerColumn_regularSupport hC
  obtain ⟨z, hz⟩ := hne
  have hax : a = x := (ha z hz).symm.trans (hcoord z hz)
  change regularSupport K C =
    {z : Plane | z.re ∈ interior (closure (x +ᵥ (Complex.re '' K.openCarrier)))}
  simpa only [Axis.transverseCoord, hax] using hs

/-- A complete line fibre is inclusion-minimal among invariant subfamilies. -/
theorem complete_lineFibre_minimal {K : Region} {T E : Set Plane}
    (hTile : TilesOn K T E) {t : Plane} (ht : t ∈ T)
    (hinvariant : IsInvariantAlong
      (coveredRegion K.openCarrier (lineFibre Complex.I T t)) Complex.I) :
    IsEarthquakeComponent K.openCarrier Complex.I T (lineFibre Complex.I T t) := by
  let C := lineFibre Complex.I T t
  have hCT : C ⊆ T := Set.inter_subset_left
  have htC : t ∈ C := by
    change t ∈ lineFibre Complex.I T t
    rw [lineFibre_vertical]
    exact ⟨ht, rfl⟩
  have hcoord : ∀ z ∈ C, z.re = t.re := by
    intro z hz
    change z ∈ lineFibre Complex.I T t at hz
    rw [lineFibre_vertical] at hz
    exact hz.2
  have hC := centerColumn_of_invariant hTile hCT ⟨t, htC⟩ t.re hcoord hinvariant
  have hsC := centerColumn_support_at hC t.re hcoord
  refine ⟨⟨t, htC⟩, hCT, hinvariant, ?_⟩
  intro R hRne hRC hRinv
  have hcoordR : ∀ z ∈ R, z.re = t.re := fun z hz => hcoord z (hRC hz)
  have hR := centerColumn_of_invariant hTile (hRC.trans hCT) hRne t.re hcoordR hRinv
  have hsR := centerColumn_support_at hR t.re hcoordR
  apply Set.Subset.antisymm hRC
  apply centres_subset_of_support_subset hTile hCT (hRC.trans hCT)
  rw [hsC, hsR]

/-- A graph column with slab support is the entire line fibre through each centre. -/
theorem column_plate_eq_lineFibre {K : Region} {T E : Set Plane}
    (hTile : TilesOn K T E) (P : VerticalPlate K T)
    (hPslab : P.base = interior (closure P.base) ∧
      P.support = Complex.re ⁻¹' P.base)
    (hPcolumn : IsVerticalColumn P) {t : Plane} (htP : t ∈ P.centres) :
    P.centres = lineFibre Complex.I T t := by
  obtain ⟨x, hx⟩ := hPcolumn
  have htx : t.re = x := hx htP
  have hPcoord : ∀ z ∈ P.centres, z.re = x := fun z hz => hx hz
  have hPInv : IsInvariantAlong (coveredRegion K.openCarrier P.centres) Complex.I := by
    apply (invariant_iff_verticalSlab K P.centres).mpr
    exact ⟨P.base, hPslab.1, hPslab.2⟩
  have hP := centerColumn_of_invariant hTile (plate_centres_subset P)
    (plate_centres_nonempty P) x hPcoord hPInv
  have hPsupport := centerColumn_support_at hP x hPcoord
  have hFsub : lineFibre Complex.I T t ⊆ T := Set.inter_subset_left
  have hFsupport : regularSupport K (lineFibre Complex.I T t) ⊆ regularSupport K P.centres := by
    have hraw : openUnion K (lineFibre Complex.I T t) ⊆ regularSupport K P.centres := by
      intro z hz
      rw [openUnion, Tiling.Polygonal.openUnion, Set.mem_iUnion] at hz
      obtain ⟨q, u, hu, rfl⟩ := hz
      have hqx : (q : Plane).re = x :=
        ((Set.ext_iff.mp (lineFibre_vertical T t) q.1).mp q.2).2.trans htx
      rw [hPsupport]
      apply (Complex.isOpenMap_re K.openCarrier K.openCarrier_regularOpen.1).vadd x
        |>.subset_interior_closure
      exact ⟨u.re, ⟨u, hu, rfl⟩, by simp [Complex.add_re, hqx]⟩
    change interior (closure (openUnion K (lineFibre Complex.I T t))) ⊆ _
    rw [← (regularSupport_isRegularOpen K P.centres).2]
    exact interior_mono (closure_mono hraw)
  apply Set.Subset.antisymm
  · intro z hz
    rw [lineFibre_vertical]
    exact ⟨plate_centres_subset P hz, (hPcoord z hz).trans htx.symm⟩
  · exact centres_subset_of_support_subset hTile hFsub (plate_centres_subset P) hFsupport

private theorem cylinder_plate_facts {K : Region} {T : Set Plane} {X : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' X)) (hX : IsRegularOpen X) :
    (∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧ P.support = Complex.re ⁻¹' P.base) ∧
    Set.range (@VerticalPlate.centres K T) =
      {S | IsMinimalVerticalSlabSubfamily K T S} := by
  have hboundary := hTile.verticalCylinder_frontier_locallyFinite
    (isRegularOpen_isOpen hX) hX
  have hplates := relativeCarrier_verticalPlates hTile rfl hX.symm
    (fun a b => by simpa only [Set.inter_comm] using hboundary _ isCompact_Icc)
  exact ⟨hplates.1, hplates.2.2.1⟩

/-- Semantic components are exactly the graph-plate centre sets on a regular cylinder. -/
theorem components_eq_range_relative {K : Region} {T : Set Plane} {X : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' X)) (hX : IsRegularOpen X) :
    {S | IsEarthquakeComponent K.openCarrier Complex.I T S} =
      Set.range (@VerticalPlate.centres K T) := by
  rw [(cylinder_plate_facts hTile hX).2]
  ext S
  exact component_iff_minimalSlab K T S

/-- The canonical complete-fibre column part equals the union of graph columns. -/
theorem columnPart_eq_verticalColumnCentres_relative
    {K : Region} {T : Set Plane} {X : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' X)) (hX : IsRegularOpen X) :
    columnPart K.openCarrier Complex.I T = verticalColumnCentres K T := by
  have hplates := cylinder_plate_facts hTile hX
  ext t
  constructor
  · rintro ⟨ht, hInv⟩
    have hminimal := (component_iff_minimalSlab K T _).mp
      (complete_lineFibre_minimal hTile ht hInv)
    have hF : lineFibre Complex.I T t ∈ Set.range (@VerticalPlate.centres K T) :=
      hplates.2.symm ▸ hminimal
    obtain ⟨P, hP⟩ := hF
    have hcol : IsVerticalColumn P := by
      refine ⟨t.re, ?_⟩
      rw [hP, lineFibre_vertical]
      exact Set.inter_subset_right
    rw [verticalColumnCentres, Set.mem_iUnion]
    refine ⟨⟨P, hcol⟩, ?_⟩
    rw [hP, lineFibre_vertical]
    exact ⟨ht, rfl⟩
  · intro ht
    rw [verticalColumnCentres, Set.mem_iUnion] at ht
    obtain ⟨P, htP⟩ := ht
    refine ⟨plate_centres_subset P.1 htP, ?_⟩
    rw [← column_plate_eq_lineFibre hTile P.1 (hplates.1 P.1) P.2 htP]
    apply (invariant_iff_verticalSlab K P.1.centres).mpr
    exact ⟨P.1.base, (hplates.1 P.1).1, (hplates.1 P.1).2⟩

/-- Semantic noncolumn plates correspond exactly to noncolumn graph plates. -/
theorem tectonicPlates_eq_nonColumn_relative
    {K : Region} {T : Set Plane} {X : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' X)) (hX : IsRegularOpen X) :
    tectonicPlates K.openCarrier Complex.I T =
      (@VerticalPlate.centres K T) '' nonColumnVerticalPlates K T := by
  have hcomponents := components_eq_range_relative hTile hX
  have hcolumns := columnPart_eq_verticalColumnCentres_relative hTile hX
  ext S
  constructor
  · rintro ⟨hS, hSoutside⟩
    have hSr : S ∈ Set.range (@VerticalPlate.centres K T) := hcomponents ▸ hS
    obtain ⟨P, rfl⟩ := hSr
    refine ⟨P, ?_, rfl⟩
    intro hPcolumn
    obtain ⟨t, ht⟩ := plate_centres_nonempty P
    have htcolumn : t ∈ columnPart K.openCarrier Complex.I T := by
      rw [hcolumns, verticalColumnCentres, Set.mem_iUnion]
      exact ⟨⟨P, hPcolumn⟩, ht⟩
    exact (hSoutside ht).2 htcolumn
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(Set.ext_iff.mp hcomponents P.centres).mpr ⟨P, rfl⟩, ?_⟩
    intro t htP
    refine ⟨plate_centres_subset P htP, ?_⟩
    intro htcol
    rw [hcolumns, verticalColumnCentres, Set.mem_iUnion] at htcol
    obtain ⟨Q, htQ⟩ := htcol
    have hPQ : P ≠ Q.1 := fun heq => hP (heq ▸ Q.2)
    exact Set.disjoint_left.mp (verticalPlateCentres_pairwiseDisjoint K T
      (Set.mem_univ P) (Set.mem_univ Q.1) hPQ) htP htQ

/-- The canonical earthquake decomposition is a partition, also on regular cylinders. -/
theorem vertical_decomposition_relative
    {K : Region} {T : Set Plane} {X : Set ℝ}
    (hTile : TilesOn K T (Complex.re ⁻¹' X)) (hX : IsRegularOpen X) :
    columnPart K.openCarrier Complex.I T ∪
        ⋃₀ tectonicPlates K.openCarrier Complex.I T = T ∧
      Disjoint (columnPart K.openCarrier Complex.I T)
        (⋃₀ tectonicPlates K.openCarrier Complex.I T) ∧
      (tectonicPlates K.openCarrier Complex.I T).Pairwise Disjoint := by
  have hcolumns := columnPart_eq_verticalColumnCentres_relative hTile hX
  have htectonic := tectonicPlates_eq_nonColumn_relative hTile hX
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · rintro t (ht | ht)
      · exact ht.1
      · obtain ⟨S, hS, htS⟩ := ht
        exact hS.1.2.1 htS
    · intro t ht
      have htUnion : t ∈ ⋃ P : VerticalPlate K T, P.centres :=
        (iUnion_verticalPlateCentres K T).symm ▸ ht
      obtain ⟨P, htP⟩ := Set.mem_iUnion.mp htUnion
      by_cases hPcolumn : IsVerticalColumn P
      · left
        rw [hcolumns, verticalColumnCentres, Set.mem_iUnion]
        exact ⟨⟨P, hPcolumn⟩, htP⟩
      · right
        exact ⟨P.centres, htectonic.symm ▸
          (show P.centres ∈ (@VerticalPlate.centres K T) ''
            nonColumnVerticalPlates K T from ⟨P, hPcolumn, rfl⟩), htP⟩
  · apply Set.disjoint_left.mpr
    rintro t htcol ⟨S, hS, htS⟩
    exact (hS.2 htS).2 htcol
  · intro S hS R hR hSR
    rw [htectonic] at hS hR
    obtain ⟨P, _, rfl⟩ := hS
    obtain ⟨Q, _, rfl⟩ := hR
    exact verticalPlateCentres_pairwiseDisjoint K T
      (Set.mem_univ P) (Set.mem_univ Q) (fun heq => hSR (congrArg VerticalPlate.centres heq))

/-- Whole-plane specialization of the canonical column bridge. -/
theorem columnPart_eq_verticalColumnCentres {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    columnPart K.openCarrier Complex.I T = verticalColumnCentres K T := by
  apply columnPart_eq_verticalColumnCentres_relative (X := Set.univ)
  · simpa using hTile
  · simp [IsRegularOpen]

/-- Whole-plane specialization of the semantic plate bridge. -/
theorem tectonicPlates_eq_nonColumn {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    tectonicPlates K.openCarrier Complex.I T =
      (@VerticalPlate.centres K T) '' nonColumnVerticalPlates K T := by
  apply tectonicPlates_eq_nonColumn_relative (X := Set.univ)
  · simpa using hTile
  · simp [IsRegularOpen]

/-- Whole-plane specialization of the canonical vertical decomposition. -/
theorem vertical_decomposition {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    columnPart K.openCarrier Complex.I T ∪
        ⋃₀ tectonicPlates K.openCarrier Complex.I T = T ∧
      Disjoint (columnPart K.openCarrier Complex.I T)
        (⋃₀ tectonicPlates K.openCarrier Complex.I T) ∧
      (tectonicPlates K.openCarrier Complex.I T).Pairwise Disjoint := by
  apply vertical_decomposition_relative (X := Set.univ)
  · simpa using hTile
  · simp [IsRegularOpen]

/-- Coordinate swap commutes with covered regions. -/
theorem coveredRegion_coordinateSwap (K : Region) (S : Set Plane) :
    coveredRegion K.coordinateSwap.openCarrier (coordinateSwap '' S) =
      coordinateSwap '' coveredRegion K.openCarrier S := by
  rw [coveredRegion_openCarrier, coveredRegion_openCarrier, regularSupport_coordinateSwap]

/-- Invariance is preserved and reflected by the real-linear coordinate swap. -/
theorem invariant_coordinateSwap (D : Set Plane) (v : Plane) :
    IsInvariantAlong D v ↔
      IsInvariantAlong (coordinateSwap '' D) (coordinateSwap v) := by
  constructor
  · intro h r
    change (r • coordinateSwap v) +ᵥ (coordinateSwap '' D) = coordinateSwap '' D
    rw [← coordinateSwap.map_smul, ← coordinateSwap_image_vadd]
    exact congrArg (Set.image coordinateSwap) (h r)
  · intro h r
    apply coordinateSwap.injective.image_injective
    rw [coordinateSwap_image_vadd, coordinateSwap.map_smul]
    exact h r

/-- Invariant supports transport with both tile and direction under coordinate swap. -/
theorem coveredRegion_invariant_coordinateSwap (K : Region) (S : Set Plane) (v : Plane) :
    IsInvariantAlong (coveredRegion K.openCarrier S) v ↔
      IsInvariantAlong (coveredRegion K.coordinateSwap.openCarrier (coordinateSwap '' S))
        (coordinateSwap v) := by
  rw [coveredRegion_coordinateSwap]
  exact invariant_coordinateSwap _ _

private theorem coordinateSwap_image_image (S : Set Plane) :
    coordinateSwap '' (coordinateSwap '' S) = S := by
  simp [Set.image_image]

private theorem coordinateSwap_one : coordinateSwap (1 : Plane) = Complex.I := by
  apply Complex.ext <;> simp

private theorem component_coordinateSwap_forward (K : Region) (T S : Set Plane)
    (v : Plane) (hS : IsEarthquakeComponent K.openCarrier v T S) :
    IsEarthquakeComponent K.coordinateSwap.openCarrier (coordinateSwap v)
      (coordinateSwap '' T) (coordinateSwap '' S) := by
  refine ⟨hS.1.image _, Set.image_mono hS.2.1,
    (coveredRegion_invariant_coordinateSwap K S v).mp hS.2.2.1, ?_⟩
  intro R hRnonempty hRsub hRinv
  have hRsubOriginal : coordinateSwap '' R ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨s, hs, hsz⟩ := hRsub hz
    simpa only [← hsz, coordinateSwap_apply_apply] using hs
  have hRinvOriginal : IsInvariantAlong (coveredRegion K.openCarrier (coordinateSwap '' R)) v := by
    have h :=
      (coveredRegion_invariant_coordinateSwap K.coordinateSwap R (coordinateSwap v)).mp hRinv
    simpa only [Region.coordinateSwap_involutive, coordinateSwap_apply_apply] using h
  have hEq := hS.2.2.2 (coordinateSwap '' R) (hRnonempty.image _)
    hRsubOriginal hRinvOriginal
  have hImageEq := congrArg (Set.image coordinateSwap) hEq
  simpa only [coordinateSwap_image_image] using hImageEq

/-- Minimal invariant subfamilies transport exactly under coordinate swap. -/
theorem component_coordinateSwap (K : Region) (T S : Set Plane) (v : Plane) :
    IsEarthquakeComponent K.openCarrier v T S ↔
      IsEarthquakeComponent K.coordinateSwap.openCarrier (coordinateSwap v)
        (coordinateSwap '' T) (coordinateSwap '' S) := by
  constructor
  · exact component_coordinateSwap_forward K T S v
  · intro h
    have hback := component_coordinateSwap_forward K.coordinateSwap
      (coordinateSwap '' T) (coordinateSwap '' S) (coordinateSwap v) h
    simpa only [Region.coordinateSwap_involutive, coordinateSwap_image_image,
      coordinateSwap_apply_apply] using hback

/-- The real-axis line through t is the fibre of its imaginary coordinate. -/
theorem lineFibre_horizontal (T : Set Plane) (t : Plane) :
    lineFibre (1 : Plane) T t = T ∩ {z | z.im = t.im} := by
  ext z
  simp only [lineFibre, Set.mem_inter_iff, Set.mem_vadd_set]
  constructor
  · rintro ⟨hz, w, hw, rfl⟩
    refine ⟨hz, ?_⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    simp [Complex.add_im]
  · rintro ⟨hz, himag⟩
    change z.im = t.im at himag
    refine ⟨hz, z - t, ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨z.re - t.re, ?_⟩
      apply Complex.ext <;> simp [himag]
    · simp [vadd_eq_add]

/-- Coordinate swap sends horizontal fibres to vertical fibres. -/
theorem lineFibre_coordinateSwap_horizontal (T : Set Plane) (t : Plane) :
    lineFibre Complex.I (coordinateSwap '' T) (coordinateSwap t) =
      coordinateSwap '' lineFibre (1 : Plane) T t := by
  rw [lineFibre_vertical, lineFibre_horizontal]
  ext z
  constructor
  · rintro ⟨⟨s, hs, rfl⟩, hcoord⟩
    exact ⟨s, ⟨hs, hcoord⟩, rfl⟩
  · rintro ⟨s, ⟨hs, hcoord⟩, rfl⟩
    exact ⟨⟨s, hs, rfl⟩, hcoord⟩

/-- The canonical horizontal column part becomes the vertical column part after swap. -/
theorem columnPart_coordinateSwap_horizontal (K : Region) (T : Set Plane) :
    columnPart K.coordinateSwap.openCarrier Complex.I (coordinateSwap '' T) =
      coordinateSwap '' columnPart K.openCarrier (1 : Plane) T := by
  ext z
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hInv⟩
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    rw [lineFibre_coordinateSwap_horizontal] at hInv
    apply (coveredRegion_invariant_coordinateSwap K (lineFibre (1 : Plane) T t) 1).mpr
    simpa only [coordinateSwap_one] using hInv
  · rintro ⟨t, ⟨ht, hInv⟩, rfl⟩
    refine ⟨⟨t, ht, rfl⟩, ?_⟩
    rw [lineFibre_coordinateSwap_horizontal]
    have h := (coveredRegion_invariant_coordinateSwap K (lineFibre (1 : Plane) T t) 1).mp hInv
    simpa only [coordinateSwap_one] using h

/-- Membership in horizontal tectonic plates is equivalent to swapped vertical membership. -/
theorem tectonic_mem_coordinateSwap_horizontal (K : Region) (T S : Set Plane) :
    S ∈ tectonicPlates K.openCarrier (1 : Plane) T ↔
      coordinateSwap '' S ∈
        tectonicPlates K.coordinateSwap.openCarrier Complex.I (coordinateSwap '' T) := by
  change (IsEarthquakeComponent K.openCarrier 1 T S ∧
    S ⊆ T \ columnPart K.openCarrier 1 T) ↔ _
  change _ ↔ (IsEarthquakeComponent K.coordinateSwap.openCarrier Complex.I
    (coordinateSwap '' T) (coordinateSwap '' S) ∧
      coordinateSwap '' S ⊆ coordinateSwap '' T \
        columnPart K.coordinateSwap.openCarrier Complex.I (coordinateSwap '' T))
  rw [columnPart_coordinateSwap_horizontal, ← Set.image_sdiff coordinateSwap.injective,
    Set.image_subset_image_iff coordinateSwap.injective]
  have hcomponent := component_coordinateSwap K T S 1
  simpa only [coordinateSwap_one] using and_congr hcomponent Iff.rfl

/-- Horizontal tectonic families transport to vertical tectonic families under swap. -/
theorem tectonicPlates_coordinateSwap_horizontal (K : Region) (T : Set Plane) :
    tectonicPlates K.coordinateSwap.openCarrier Complex.I (coordinateSwap '' T) =
      (Set.image coordinateSwap) '' tectonicPlates K.openCarrier (1 : Plane) T := by
  ext S
  constructor
  · intro hS
    refine ⟨coordinateSwap '' S, ?_, coordinateSwap_image_image S⟩
    apply (tectonic_mem_coordinateSwap_horizontal K T (coordinateSwap '' S)).mpr
    simpa only [coordinateSwap_image_image] using hS
  · rintro ⟨R, hR, rfl⟩
    exact (tectonic_mem_coordinateSwap_horizontal K T R).mp hR

/-- Horizontal earthquake decomposition follows by interchanging coordinates. -/
theorem horizontal_decomposition {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    columnPart K.openCarrier (1 : Plane) T ∪
        ⋃₀ tectonicPlates K.openCarrier (1 : Plane) T = T ∧
      Disjoint (columnPart K.openCarrier (1 : Plane) T)
        (⋃₀ tectonicPlates K.openCarrier (1 : Plane) T) ∧
      (tectonicPlates K.openCarrier (1 : Plane) T).Pairwise Disjoint := by
  have hTileSwap : TilesOn K.coordinateSwap (coordinateSwap '' T) Set.univ := by
    simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using
      tilesOn_coordinateSwap hTile
  have hD := vertical_decomposition hTileSwap
  have hcolumns := columnPart_coordinateSwap_horizontal K T
  have htectonic := tectonicPlates_coordinateSwap_horizontal K T
  refine ⟨?_, ?_, ?_⟩
  · apply coordinateSwap.injective.image_injective
    rw [Set.image_union, Set.image_sUnion, ← hcolumns, ← htectonic]
    exact hD.1
  · apply Disjoint.of_image (f := coordinateSwap)
    rw [Set.image_sUnion, ← hcolumns, ← htectonic]
    exact hD.2.1
  · intro S hS R hR hSR
    apply Disjoint.of_image (f := coordinateSwap)
    have hSswap := (tectonic_mem_coordinateSwap_horizontal K T S).mp hS
    have hRswap := (tectonic_mem_coordinateSwap_horizontal K T R).mp hR
    exact hD.2.2 hSswap hRswap
      (fun heq => hSR (coordinateSwap.injective.image_injective heq))

/-- Only finitely many semantic vertical plates fail to be columns. -/
theorem vertical_tectonicPlates_finite {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    (tectonicPlates K.openCarrier Complex.I T).Finite := by
  rw [tectonicPlates_eq_nonColumn hTile]
  exact (Tiling.AxisParallel.Structure.noncolumnVerticalPlates_finite hTile).1.image _

/-- The finiteness conclusion also holds for the horizontal direction. -/
theorem horizontal_tectonicPlates_finite {K : Region} {T : Set Plane}
    (hTile : TilesOn K T Set.univ) :
    (tectonicPlates K.openCarrier (1 : Plane) T).Finite := by
  have hTileSwap : TilesOn K.coordinateSwap (coordinateSwap '' T) Set.univ := by
    simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using
      tilesOn_coordinateSwap hTile
  have hfinite := vertical_tectonicPlates_finite hTileSwap
  rw [tectonicPlates_coordinateSwap_horizontal] at hfinite
  exact hfinite.of_finite_image coordinateSwap.injective.image_injective.injOn

end Tiling.AxisParallel.SetFormulation.Columns
