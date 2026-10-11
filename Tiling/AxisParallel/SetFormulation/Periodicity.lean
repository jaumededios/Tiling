import Tiling.AxisParallel.SetFormulation.RegionBridge
import Tiling.AxisParallel.SetFormulation.PeriodicityBridge
import Tiling.AxisParallel.SetFormulation.FellMinimality
import Tiling.AxisParallel.SetFormulation.Columns
import Tiling.AxisParallel.Terminal.MainCorollaries
import Tiling.AxisParallel.Terminal.PeriodicCarrierContinuousSlabs

set_option autoImplicit false

open Set
open scoped Pointwise Topology

noncomputable section

open Tiling.Combinatorics.FiniteSetPartitions

namespace Tiling.AxisParallel.SetFormulation

private theorem real_period_membership {X : Set ℝ} {β : ℝ}
    (hperiod : β +ᵥ X = X) : ∀ x, x + β ∈ X ↔ x ∈ X := by
  intro x
  have hmem := congrArg (fun A : Set ℝ => β + x ∈ A) hperiod
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using hmem.symm

private def StructureAlong (Ω T : Set Plane) (v : Plane) : Prop :=
  ∃ P : Finpartition (T \ columnPart Ω v T),
    IsDoublyPeriodic (coveredRegion Ω (columnPart Ω v T)) ∧
      ∀ S ∈ P.parts, HasFiniteLocalComplexity S ∧
        IsDoublyPeriodic (coveredRegion Ω S) ∧ IsInvariantAlong (coveredRegion Ω S) v

private theorem structure_of_indexed (K : Tiling.AxisParallel.Region) (T C : Set Plane)
    {n : ℕ} (part : Fin n → Set Plane)
    (hC : C = columnPart K.openCarrier Complex.I T)
    (hcover : C ∪ (⋃ i, part i) = T)
    (hdis : Set.PairwiseDisjoint Set.univ part)
    (hCdis : ∀ i, Disjoint C (part i))
    (hCperiod : Tiling.AxisParallel.IsLatticePeriodic (Tiling.AxisParallel.regularSupport K C))
    (hFLC : ∀ i, Tiling.AxisParallel.HasFLC (part i))
    (hperiod : ∀ i, Tiling.AxisParallel.IsLatticePeriodic
      (Tiling.AxisParallel.regularSupport K (part i)))
    (hInv : ∀ i, IsInvariantAlong (Tiling.AxisParallel.regularSupport K (part i)) Complex.I) :
    StructureAlong K.openCarrier T Complex.I := by
  classical
  have hpartsCover : (⋃ i, part i) = T \ columnPart K.openCarrier Complex.I T := by
    rw [← hC, ← hcover]
    ext z
    constructor
    · intro hz
      refine ⟨Or.inr hz, ?_⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact fun hzC => Set.disjoint_left.mp (hCdis i) hzC hi
    · rintro ⟨hzC | hz, hnC⟩
      · exact (hnC hzC).elim
      · exact hz
  refine ⟨finpartitionOfIndexed part hdis hpartsCover, ?_, ?_⟩
  · rw [Columns.coveredRegion_openCarrier, ← hC]
    exact (isDoublyPeriodic_iff_isLatticePeriodic _).mpr hCperiod
  · intro S hS
    rw [finpartitionOfIndexed_parts] at hS
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    rw [Columns.coveredRegion_openCarrier]
    exact ⟨hasFiniteLocalComplexity_iff_hasFLC.mpr (hFLC i),
      (isDoublyPeriodic_iff_isLatticePeriodic _).mpr (hperiod i), hInv i⟩

private theorem cylinder_periodic {X : Set ℝ} {β : ℝ} (hβ : 0 < β)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy (Complex.re ⁻¹' X) (β : Plane)) :
    Tiling.AxisParallel.IsLatticePeriodic (Complex.re ⁻¹' X) := by
  apply (Tiling.AxisParallel.isLatticePeriodic_iff_doublyPeriodic _).mpr
  refine ⟨(β : Plane), Complex.I, ?_, hperiod, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · have hreal := congrArg Complex.re hg
      rcases (by simpa using hreal) with hzero | hzero
      · simpa using hzero
      · exact ((ne_of_gt hβ) hzero).elim
    · have himag := congrArg Complex.im hg
      simpa using himag
  · intro z
    simp [Complex.add_re]

private theorem cylinder_invariant (X : Set ℝ) :
    IsInvariantAlong (Complex.re ⁻¹' X) Complex.I := by
  rw [Columns.invariant_vertical_iff]
  exact (Tiling.AxisParallel.verticalInvariant_iff_product _).mpr ⟨X, rfl⟩

private theorem vertical_structure_flc (K : Tiling.AxisParallel.Region) (T : Set Plane)
    (hT : Tiling.AxisParallel.TilesOn K T univ) (hFLC : Tiling.AxisParallel.HasFLC T) :
    StructureAlong K.openCarrier T Complex.I := by
  let X : Tiling.AxisParallel.Terminal.PeriodicVerticalCarrier := {
    base := univ
    base_open := isOpen_univ
    base_regular := by simp
    base_nonnull := by simp
    period := 1
    period_pos := zero_lt_one
    base_periodic := by simp }
  have hTX : Tiling.AxisParallel.TilesOn K T X.carrier := by
    simpa [X, Tiling.AxisParallel.Terminal.PeriodicVerticalCarrier.carrier] using hT
  obtain ⟨D⟩ := Tiling.AxisParallel.Terminal.exists_periodicCarrierSlabDecomposition
    X hTX (Or.inr hFLC)
  apply structure_of_indexed K T D.columnCentres (fun i => (D.nonColumnPlate i).centres)
    (D.columnCentres_eq.trans (Columns.columnPart_eq_verticalColumnCentres hT).symm)
    D.centres_partition D.nonColumnCentres_pairwise D.column_nonColumn_disjoint
  · rw [D.columnSupport_eq]
    apply cylinder_periodic D.commonSupportPeriod_pos
    rw [← D.columnSupport_eq]
    exact D.columnSupport_periodic
  · intro i
    apply Tiling.Polygonal.HasFLC.mono hFLC
    rintro z ⟨q, _, rfl⟩
    exact q.2
  · intro i
    obtain ⟨_, hsupp⟩ :=
      Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab hT (D.nonColumnPlate i)
    change Tiling.AxisParallel.IsLatticePeriodic (D.nonColumnPlate i).support
    rw [hsupp]
    apply cylinder_periodic D.commonSupportPeriod_pos
    rw [← hsupp]
    exact D.nonColumnSupport_periodic i
  · intro i
    obtain ⟨_, hsupp⟩ :=
      Tiling.AxisParallel.Continuous.VerticalPlate.support_isVerticalSlab hT (D.nonColumnPlate i)
    change IsInvariantAlong (D.nonColumnPlate i).support Complex.I
    rw [hsupp]
    exact cylinder_invariant _

private theorem vertical_structure_nonflc
    {K : Tiling.AxisParallel.Region}
    {U : Tiling.AxisParallel.Topology.TilingSpace K univ}
    (D : Tiling.AxisParallel.Structure.MinimalTilingStructureData K U)
    (hFLC : ¬ Tiling.AxisParallel.HasFLC (D.selectedTiling.centres : Set Plane)) :
    StructureAlong D.selectedRegion.openCarrier
      (D.selectedTiling.centres : Set Plane) Complex.I := by
  apply structure_of_indexed D.selectedRegion D.selectedTiling.centres D.columnPart D.piece
    ((D.nonFLC_components hFLC).1.trans
      (Columns.columnPart_eq_verticalColumnCentres D.selectedTiling.tilesOn).symm)
    D.centres_partition D.pieces_pairwiseDisjoint D.column_disjoint_piece
    D.columnSupport_latticePeriodic D.piece_hasFLC D.pieceSupport_latticePeriodic
  intro i
  rw [D.pieceSupport_eq]
  exact cylinder_invariant _

private theorem doubly_periodic_swap_iff (A : Set Plane) :
    IsDoublyPeriodic (Tiling.AxisParallel.coordinateSwap '' A) ↔ IsDoublyPeriodic A := by
  constructor
  · intro h
    have hnative := Tiling.AxisParallel.coordinateSwap_latticePeriodic
      ((isDoublyPeriodic_iff_isLatticePeriodic _).mp h)
    rw [Tiling.AxisParallel.IntrinsicVertices.coordinateSwap_image_image] at hnative
    exact (isDoublyPeriodic_iff_isLatticePeriodic _).mpr hnative
  · intro h
    exact (isDoublyPeriodic_iff_isLatticePeriodic _).mpr
      (Tiling.AxisParallel.coordinateSwap_latticePeriodic
        ((isDoublyPeriodic_iff_isLatticePeriodic _).mp h))

private theorem structure_swap_horizontal (K : Tiling.AxisParallel.Region) (T : Set Plane)
    (hstructure : StructureAlong K.coordinateSwap.openCarrier
      (Tiling.AxisParallel.coordinateSwap '' T) Complex.I) :
    StructureAlong K.openCarrier T (1 : Plane) := by
  classical
  obtain ⟨P, hcolumn, hparts⟩ := hstructure
  let part := fun i : Fin P.parts.card =>
    Tiling.AxisParallel.coordinateSwap '' enumerate P.parts i
  have henum : (⋃ i, enumerate P.parts i) =
      (Tiling.AxisParallel.coordinateSwap '' T) \
        columnPart K.coordinateSwap.openCarrier Complex.I
          (Tiling.AxisParallel.coordinateSwap '' T) := by
    rw [iUnion_enumerate]
    simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
  have hcover : (⋃ i, part i) = T \ columnPart K.openCarrier (1 : Plane) T := by
    rw [show (⋃ i, part i) = Tiling.AxisParallel.coordinateSwap '' (⋃ i, enumerate P.parts i)
      from Set.image_iUnion.symm, henum]
    rw [Set.image_sdiff Tiling.AxisParallel.coordinateSwap.injective,
      Columns.columnPart_coordinateSwap_horizontal,
      Tiling.AxisParallel.IntrinsicVertices.coordinateSwap_image_image,
      Tiling.AxisParallel.IntrinsicVertices.coordinateSwap_image_image]
  have hdis : Set.PairwiseDisjoint Set.univ part := by
    intro i _ j _ hij
    have hd := P.disjoint (enumerate_mem P.parts i) (enumerate_mem P.parts j)
      (fun heq => hij (enumerate_injective P.parts heq))
    apply Set.disjoint_left.mpr
    rintro z ⟨a, ha, haz⟩ ⟨b, hb, hbz⟩
    have hab : a = b := Tiling.AxisParallel.coordinateSwap.injective (haz.trans hbz.symm)
    exact Set.disjoint_left.mp hd ha (hab.symm ▸ hb)
  refine ⟨finpartitionOfIndexed part hdis hcover, ?_, ?_⟩
  · rw [Columns.columnPart_coordinateSwap_horizontal,
      Columns.coveredRegion_coordinateSwap] at hcolumn
    exact (doubly_periodic_swap_iff _).mp hcolumn
  · intro S hS
    rw [finpartitionOfIndexed_parts] at hS
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    have hi := hparts (enumerate P.parts i) (enumerate_mem P.parts i)
    refine ⟨?_, ?_, ?_⟩
    · apply hasFiniteLocalComplexity_iff_hasFLC.mpr
      exact (Tiling.Polygonal.HasFLC.linearImage_iff Tiling.AxisParallel.coordinateSwap _).mpr
        (hasFiniteLocalComplexity_iff_hasFLC.mp hi.1)
    · have hcov := Columns.coveredRegion_coordinateSwap K.coordinateSwap (enumerate P.parts i)
      simp only [Tiling.AxisParallel.Region.coordinateSwap_involutive] at hcov
      change IsDoublyPeriodic
        (coveredRegion K.openCarrier (Tiling.AxisParallel.coordinateSwap '' enumerate P.parts i))
      rw [hcov]
      exact (doubly_periodic_swap_iff _).mpr hi.2.1
    · have hinv := (Columns.coveredRegion_invariant_coordinateSwap K.coordinateSwap
        (enumerate P.parts i) Complex.I).mp hi.2.2
      have hswapI : Tiling.AxisParallel.coordinateSwap Complex.I = (1 : Plane) := by
        apply Complex.ext <;> simp
      simpa only [Tiling.AxisParallel.Region.coordinateSwap_involutive, hswapI] using hinv

theorem flc_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : HasFiniteLocalComplexity T) : WeaklyPeriodic T := by
  have _ := hX
  apply (weaklyPeriodic_iff_production T).mpr
  exact Tiling.AxisParallel.Terminal.flcTiling_weaklyPeriodic
    (isRegularOpen_isOpen hXregular) hβ (real_period_membership hperiod)
    ((tilingOn_iff_native Ω hΩ _ T).mp hT)
    (hasFiniteLocalComplexity_iff_hasFLC.mp hFLC)

theorem periodic_tiling_of_flc
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X) :
    (∃ T, TilingOn (p₁ ⁻¹' X) Ω T ∧ HasFiniteLocalComplexity T) →
      ∃ S, TilingOn (p₁ ⁻¹' X) Ω S ∧ IsDoublyPeriodic S := by
  have _ := hX
  rintro ⟨T, hT, hFLC⟩
  obtain ⟨P⟩ := Tiling.AxisParallel.Terminal.exists_flcPeriodicReplacement
    (isRegularOpen_isOpen hXregular) hβ (real_period_membership hperiod)
    ((tilingOn_iff_native Ω hΩ _ T).mp hT)
    (hasFiniteLocalComplexity_iff_hasFLC.mp hFLC)
  exact ⟨P.centres, (tilingOn_iff_native Ω hΩ _ _).mpr P.tiles,
    (isDoublyPeriodic_iff_isLatticePeriodic _).mpr ⟨P.lattice, P.lattice_periods⟩⟩

theorem minimal_tiling_structure
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (T : Set Plane) (hT : Tiles Ω T) (hminimal : IsMinimal univ T) :
    ∃ v ∈ ({e₁, e₂} : Set Plane),
      ∃ P : Finpartition (T \ columnPart Ω v T),
        IsDoublyPeriodic (coveredRegion Ω (columnPart Ω v T)) ∧
        ∀ S ∈ P.parts,
          HasFiniteLocalComplexity S ∧
          IsDoublyPeriodic (coveredRegion Ω S) ∧ IsInvariantAlong (coveredRegion Ω S) v := by
  change ∃ v ∈ ({e₁, e₂} : Set Plane), StructureAlong Ω T v
  let K := regionOfTile Ω hΩ
  have hcarrier : K.openCarrier = Ω := regionOfTile_openCarrier Ω hΩ
  have hnative : Tiling.AxisParallel.TilesOn K T univ :=
    (tilingOn_iff_native Ω hΩ univ T).mp hT
  by_cases hFLC : Tiling.AxisParallel.HasFLC T
  · refine ⟨e₂, by simp, ?_⟩
    simpa only [hcarrier, e₂, Complex.I] using vertical_structure_flc K T hnative hFLC
  · let U : Tiling.AxisParallel.Topology.TilingSpace K univ := ⟨⟨T, hminimal.1⟩, hnative⟩
    have hUcentres : (U.centres : Set Plane) = T := rfl
    have hmin := (Fell.minimal_bridge isOpen_univ (by simp [IsRegularOpen]) U).mp hminimal
    obtain ⟨D⟩ := Tiling.AxisParallel.Structure.exists_minimalTilingStructureData U hmin
    have hselectedNonFLC : ¬ Tiling.AxisParallel.HasFLC
        (D.selectedTiling.centres : Set Plane) := by
      intro hf
      rcases D.orientation_spec with ⟨_, _, hcentres⟩ | ⟨_, _, hcentres⟩
      · rw [hcentres] at hf
        exact hFLC hf
      · rw [hcentres] at hf
        exact hFLC ((Tiling.Polygonal.HasFLC.linearImage_iff
          Tiling.AxisParallel.coordinateSwap _).mp hf)
    have hs := vertical_structure_nonflc D hselectedNonFLC
    rcases D.orientation_spec with ⟨_, hregion, hcentres⟩ | ⟨_, hregion, hcentres⟩
    · refine ⟨e₂, by simp, ?_⟩
      rw [hcentres, hregion] at hs
      simpa only [hcarrier, e₂, Complex.I, hUcentres] using hs
    · refine ⟨e₁, by simp, ?_⟩
      rw [hcentres, hregion] at hs
      have hone : (1 : Plane) = e₁ := by
        apply Complex.ext <;> simp
      simpa only [hcarrier, hone] using structure_swap_horizontal K T hs

theorem minimal_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (T : Set Plane) (hT : Tiles Ω T) (hminimal : IsMinimal univ T) :
    WeaklyPeriodic T := by
  let U : Tiling.AxisParallel.Topology.TilingSpace (regionOfTile Ω hΩ) univ :=
    ⟨⟨T, hminimal.1⟩, (tilingOn_iff_native Ω hΩ univ T).mp hT⟩
  have hmin := (Fell.minimal_bridge isOpen_univ (by simp [IsRegularOpen]) U).mp hminimal
  exact (weaklyPeriodic_iff_production T).mpr
    (Tiling.AxisParallel.Terminal.topologicallyMinimalTiling_weaklyPeriodic U hmin)

theorem quasi_periodic_tiling_with_common_period
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω) :
    (∃ T, Tiles Ω T) →
      ∃ S, Tiles Ω S ∧ QuasiPeriodic S ∧ ∃ p, p ≠ 0 ∧ IsPeriod S p := by
  rintro ⟨T, hT⟩
  obtain ⟨S, hS, hquasi, p, hp, hperiod⟩ :=
    Tiling.AxisParallel.Terminal.exists_quasiPeriodicTiling_commonPeriod
      (regionOfTile Ω hΩ) ⟨T, (tilingOn_iff_native Ω hΩ univ T).mp hT⟩
  exact ⟨S, (tilingOn_iff_native Ω hΩ univ S).mpr hS,
    (quasiPeriodic_iff_production S).mpr hquasi, p, hp,
    (isPeriod_iff_mem_periodGroup S p).mpr hperiod⟩

end Tiling.AxisParallel.SetFormulation
