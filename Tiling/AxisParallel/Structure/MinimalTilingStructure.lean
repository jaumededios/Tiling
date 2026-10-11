import Tiling.AxisParallel.Continuous.CoordinateSwapTilings
import Tiling.AxisParallel.Continuous.ContinuousSlabPeriodicity
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.Continuous.WeakTilingTopology
import Tiling.AxisParallel.Structure.HorizontalComplexityUnderWeakLimits
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Topology.HullCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Structure.PlateThickness
import Tiling.AxisParallel.Continuous.NontrivialEarthquakeLimit
import Tiling.AxisParallel.Structure.AlignedEarthquakeLimits
import Tiling.AxisParallel.Structure.FiniteHorizontalComplexityTrichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

/-- The finite periodic slab decomposition attached to a minimal tiling after choosing the
orientation with finite horizontal complexity. -/
structure MinimalTilingStructureData
    (K : Tiling.AxisParallel.Region)
    (T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ) where
  orientation : Tiling.AxisParallel.Axis
  selectedRegion : Tiling.AxisParallel.Region
  selectedTiling : Tiling.AxisParallel.Topology.TilingSpace selectedRegion Set.univ
  orientation_spec :
    (orientation = Tiling.AxisParallel.Axis.vertical ∧
      selectedRegion = K ∧
        (selectedTiling.centres : Set Tiling.Plane) =
          (T.centres : Set Tiling.Plane)) ∨
    (orientation = Tiling.AxisParallel.Axis.horizontal ∧
      selectedRegion = K.coordinateSwap ∧
      (selectedTiling.centres : Set Tiling.Plane) =
        Tiling.AxisParallel.coordinateSwap ''
          (T.centres : Set Tiling.Plane))
  selected_minimal : Tiling.AxisParallel.Topology.IsTopologicallyMinimal
    (Tiling.AxisParallel.Topology.orbitHull selectedTiling)
  numberOfPieces : ℕ
  columnPart : Set Tiling.Plane
  columnPlates : Set
    (Tiling.AxisParallel.Continuous.VerticalPlate
      selectedRegion (selectedTiling.centres : Set Tiling.Plane))
  columnPlates_areColumns : ∀ P ∈ columnPlates,
    Tiling.AxisParallel.Continuous.IsVerticalColumn P
  columnPlates_areComplete : ∀ P ∈ columnPlates,
    Tiling.AxisParallel.IsCenterColumn Tiling.AxisParallel.Axis.vertical
      selectedRegion P.centres
  columnPart_eq : columnPart = ⋃ P : ↑columnPlates, P.1.centres
  piece : Fin numberOfPieces → Set Tiling.Plane
  piece_nonempty : ∀ j, (piece j).Nonempty
  pieces_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ piece
  column_disjoint_piece : ∀ j, Disjoint columnPart (piece j)
  centres_partition :
    columnPart ∪ (⋃ j, piece j) =
      (selectedTiling.centres : Set Tiling.Plane)
  piece_hasFLC : ∀ j, Tiling.AxisParallel.HasFLC (piece j)
  finiteComplexity_normalForm :
    Tiling.AxisParallel.HasFLC
        (selectedTiling.centres : Set Tiling.Plane) →
      columnPart = ∅ ∧ numberOfPieces = 1 ∧
        ∃ j : Fin numberOfPieces,
          piece j = (selectedTiling.centres : Set Tiling.Plane)
  finiteHorizontalComplexity_of_nonFLC :
    ¬ Tiling.AxisParallel.HasFLC
        (selectedTiling.centres : Set Tiling.Plane) →
      Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity
        (selectedTiling.centres : Set Tiling.Plane)
  columnBase : Set ℝ
  base : Fin numberOfPieces → Set ℝ
  columnBase_open : IsOpen columnBase
  columnBase_regular : interior (closure columnBase) = columnBase
  columnBase_nonempty_iff : columnBase.Nonempty ↔ columnPart.Nonempty
  base_open : ∀ j, IsOpen (base j)
  base_regular : ∀ j, interior (closure (base j)) = base j
  base_nonempty : ∀ j, (base j).Nonempty
  columnSupport_eq :
    Tiling.AxisParallel.regularSupport selectedRegion columnPart =
      Complex.re ⁻¹' columnBase
  pieceSupport_eq : ∀ j,
    Tiling.AxisParallel.regularSupport selectedRegion (piece j) =
      Complex.re ⁻¹' (base j)
  column_tiles : Tiling.AxisParallel.TilesOn selectedRegion columnPart
    (Complex.re ⁻¹' columnBase)
  piece_tiles : ∀ j, Tiling.AxisParallel.TilesOn selectedRegion (piece j)
    (Complex.re ⁻¹' (base j))
  support_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ
    (fun j ↦ Tiling.AxisParallel.regularSupport selectedRegion (piece j))
  columnSupport_disjoint_piece : ∀ j,
    Disjoint
      (Tiling.AxisParallel.regularSupport selectedRegion columnPart)
      (Tiling.AxisParallel.regularSupport selectedRegion (piece j))
  supports_cover :
    (Tiling.AxisParallel.regularSupport selectedRegion columnPart ∪
      (⋃ j : Fin numberOfPieces,
        Tiling.AxisParallel.regularSupport selectedRegion (piece j)) :
          Set Tiling.Plane)
      =ᵐ[MeasureTheory.volume] Set.univ
  bases_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ base
  columnBase_disjoint_base : ∀ j, Disjoint columnBase (base j)
  bases_cover :
    (columnBase ∪ (⋃ j : Fin numberOfPieces, base j) : Set ℝ)
    =ᵐ[MeasureTheory.volume] Set.univ
  horizontalPeriod : ℝ
  horizontalPeriod_pos : 0 < horizontalPeriod
  columnSupport_periodic : Tiling.RationalPolygonal.SetPeriodicBy
    (Tiling.AxisParallel.regularSupport selectedRegion columnPart)
    ((horizontalPeriod : ℝ) : ℂ)
  pieceSupport_periodic : ∀ j, Tiling.RationalPolygonal.SetPeriodicBy
    (Tiling.AxisParallel.regularSupport selectedRegion (piece j))
    ((horizontalPeriod : ℝ) : ℂ)
  columnBase_periodic : ∀ x : ℝ,
    x + horizontalPeriod ∈ columnBase ↔ x ∈ columnBase
  base_periodic : ∀ j x,
    x + horizontalPeriod ∈ base j ↔ x ∈ base j
  columnSupport_latticePeriodic : Tiling.AxisParallel.IsLatticePeriodic
    (Tiling.AxisParallel.regularSupport selectedRegion columnPart)
  pieceSupport_latticePeriodic : ∀ j, Tiling.AxisParallel.IsLatticePeriodic
    (Tiling.AxisParallel.regularSupport selectedRegion (piece j))
  somePart_nonempty : columnPart.Nonempty ∨ Nonempty (Fin numberOfPieces)
  columnBase_proper_of_piece : Nonempty (Fin numberOfPieces) →
    columnBase ≠ Set.univ
  base_proper_of_multiple : ∀ j,
    (columnPart.Nonempty ∨ 2 ≤ numberOfPieces) → base j ≠ Set.univ
  nonFLC_nontrivial : ¬ Tiling.AxisParallel.HasFLC
      (selectedTiling.centres : Set Tiling.Plane) →
    ¬ ∃ P : Tiling.AxisParallel.Continuous.VerticalPlate
        selectedRegion (selectedTiling.centres : Set Tiling.Plane),
      ¬ Tiling.AxisParallel.Continuous.IsVerticalColumn P ∧
        P.centres = (selectedTiling.centres : Set Tiling.Plane)
  nonFLC_components : ¬ Tiling.AxisParallel.HasFLC
      (selectedTiling.centres : Set Tiling.Plane) →
    columnPart = Tiling.AxisParallel.Continuous.verticalColumnCentres
        selectedRegion (selectedTiling.centres : Set Tiling.Plane) ∧
      ∃ e : Fin numberOfPieces ≃
          ↑(Tiling.AxisParallel.Continuous.nonColumnVerticalPlates
            selectedRegion (selectedTiling.centres : Set Tiling.Plane)),
        ∀ j, piece j = (e j).1.centres

theorem exists_topologicallyMinimalOrbitPoint
    {K : Tiling.AxisParallel.Region}
    (T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ) :
    ∃ S : Tiling.AxisParallel.Topology.TilingSpace K Set.univ,
      S ∈ Tiling.AxisParallel.Topology.orbitHull T ∧
      Tiling.AxisParallel.Topology.IsTopologicallyMinimal
        (Tiling.AxisParallel.Topology.orbitHull S) := by
  obtain ⟨Y, hYHull, hYnonempty, _hYclosed, _hYinvariant, hYminimal⟩ :=
    Tiling.AxisParallel.Continuous.exists_minimalInvariantSubset T
  obtain ⟨S, hSY⟩ := hYnonempty
  refine ⟨S, hYHull hSY, ?_⟩
  rw [show Tiling.AxisParallel.Topology.orbitHull S = Y from
    hYminimal.2.2.2 S hSY]
  exact hYminimal

theorem MinimalTilingStructureData.allColumns_iff
    {K : Tiling.AxisParallel.Region}
    {T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    (D : Tiling.AxisParallel.Structure.MinimalTilingStructureData K T)
    (hNonFLC : ¬ Tiling.AxisParallel.HasFLC
      (D.selectedTiling.centres : Set Tiling.Plane)) :
    (D.selectedTiling.centres : Set Tiling.Plane) =
        Tiling.AxisParallel.Continuous.verticalColumnCentres
          D.selectedRegion
            (D.selectedTiling.centres : Set Tiling.Plane) ↔
      D.columnPart = (D.selectedTiling.centres : Set Tiling.Plane) ∧
        D.numberOfPieces = 0 := by
  have hcomponents := D.nonFLC_components hNonFLC
  constructor
  · intro hAll
    have hColumnPart : D.columnPart =
        (D.selectedTiling.centres : Set Tiling.Plane) :=
      hcomponents.1.trans hAll.symm
    refine ⟨hColumnPart, ?_⟩
    apply Nat.eq_zero_of_not_pos
    intro hpos
    let j : Fin D.numberOfPieces := ⟨0, hpos⟩
    obtain ⟨x, hxPiece⟩ := D.piece_nonempty j
    have hxCentres : x ∈ (D.selectedTiling.centres : Set Tiling.Plane) := by
      rw [← D.centres_partition]
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, hxPiece⟩)
    have hxColumn : x ∈ D.columnPart := by
      rw [hColumnPart]
      exact hxCentres
    exact Set.disjoint_left.mp (D.column_disjoint_piece j) hxColumn hxPiece
  · rintro ⟨hColumnPart, _⟩
    rw [← hcomponents.1, hColumnPart]

theorem MinimalTilingStructureData.noColumns_iff
    {K : Tiling.AxisParallel.Region}
    {T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    (D : Tiling.AxisParallel.Structure.MinimalTilingStructureData K T)
    (hNonFLC : ¬ Tiling.AxisParallel.HasFLC
      (D.selectedTiling.centres : Set Tiling.Plane)) :
    Tiling.AxisParallel.Continuous.verticalColumnCentres
        D.selectedRegion
          (D.selectedTiling.centres : Set Tiling.Plane) = ∅ ↔
      D.columnPart = ∅ := by
  rw [D.nonFLC_components hNonFLC |>.1]

theorem MinimalTilingStructureData.finiteComplexityBranch
    {K : Tiling.AxisParallel.Region}
    {T : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    (D : Tiling.AxisParallel.Structure.MinimalTilingStructureData K T)
    (hFLC : Tiling.AxisParallel.HasFLC
      (D.selectedTiling.centres : Set Tiling.Plane)) :
    D.columnPart = ∅ ∧ D.numberOfPieces = 1 ∧
      ∃ j : Fin D.numberOfPieces,
        D.piece j = (D.selectedTiling.centres : Set Tiling.Plane) :=
  D.finiteComplexity_normalForm hFLC

private structure OrientedNonFLCSelection (K : Region)
    (T : Topology.TilingSpace K Set.univ) where
  orientation : Axis
  selectedRegion : Region
  selectedTiling : Topology.TilingSpace selectedRegion Set.univ
  orientation_spec :
    (orientation = Axis.vertical ∧ selectedRegion = K ∧
      (selectedTiling.centres : Set Tiling.Plane) = (T.centres : Set Tiling.Plane)) ∨
    (orientation = Axis.horizontal ∧ selectedRegion = K.coordinateSwap ∧
      (selectedTiling.centres : Set Tiling.Plane) =
        coordinateSwap '' (T.centres : Set Tiling.Plane))
  selected_minimal : Topology.IsTopologicallyMinimal (Topology.orbitHull selectedTiling)
  selected_nonFLC : ¬ HasFLC (selectedTiling.centres : Set Tiling.Plane)
  finiteHorizontal : Continuous.HasFiniteHorizontalComplexity
    (selectedTiling.centres : Set Tiling.Plane)
  nontrivialVertical : ¬ ∃ P : Continuous.VerticalPlate selectedRegion
      (selectedTiling.centres : Set Tiling.Plane),
    ¬ Continuous.IsVerticalColumn P ∧ P.centres = (selectedTiling.centres : Set Tiling.Plane)

private structure NonColumnPlateIndexing {K : Region}
    (T : Topology.TilingSpace K Set.univ) where
  numberOfPieces : ℕ
  plate : Fin numberOfPieces → Continuous.VerticalPlate K (T.centres : Set Tiling.Plane)
  plate_nonColumn : ∀ j, ¬ Continuous.IsVerticalColumn (plate j)
  equiv : Fin numberOfPieces ≃
    ↑(Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane))
  plate_eq : ∀ j, plate j = (equiv j).1

private structure ComponentPeriodData {K : Region}
    (T : Topology.TilingSpace K Set.univ) where
  beta : ℝ
  beta_pos : 0 < beta
  column_periodic : Tiling.RationalPolygonal.SetPeriodicBy
    (regularSupport K (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)))
    ((beta : ℝ) : ℂ)
  plate_periodic : ∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
    ¬ Continuous.IsVerticalColumn P →
      Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ)

private structure VerticalComponentGeometry {K : Region}
    (T : Topology.TilingSpace K Set.univ) (I : NonColumnPlateIndexing T) where
  columnPart : Set Tiling.Plane
  columnPlates : Set (Continuous.VerticalPlate K (T.centres : Set Tiling.Plane))
  piece : Fin I.numberOfPieces → Set Tiling.Plane
  columnBase : Set ℝ
  base : Fin I.numberOfPieces → Set ℝ
  columnPlates_areColumns : ∀ P ∈ columnPlates, Continuous.IsVerticalColumn P
  columnPlates_areComplete : ∀ P ∈ columnPlates, IsCenterColumn Axis.vertical K P.centres
  columnPart_eq : columnPart = ⋃ P : ↑columnPlates, P.1.centres
  piece_eq : ∀ j, piece j = (I.plate j).centres
  piece_nonempty : ∀ j, (piece j).Nonempty
  pieces_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ piece
  column_disjoint_piece : ∀ j, Disjoint columnPart (piece j)
  centres_partition : columnPart ∪ (⋃ j, piece j) = (T.centres : Set Tiling.Plane)
  columnBase_open : IsOpen columnBase
  columnBase_regular : interior (closure columnBase) = columnBase
  columnBase_nonempty_iff : columnBase.Nonempty ↔ columnPart.Nonempty
  base_open : ∀ j, IsOpen (base j)
  base_regular : ∀ j, interior (closure (base j)) = base j
  base_nonempty : ∀ j, (base j).Nonempty
  columnSupport_eq : regularSupport K columnPart = Complex.re ⁻¹' columnBase
  pieceSupport_eq : ∀ j, regularSupport K (piece j) = Complex.re ⁻¹' (base j)
  column_tiles : TilesOn K columnPart (Complex.re ⁻¹' columnBase)
  piece_tiles : ∀ j, TilesOn K (piece j) (Complex.re ⁻¹' (base j))
  support_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ
    (fun j ↦ regularSupport K (piece j))
  columnSupport_disjoint_piece : ∀ j,
    Disjoint (regularSupport K columnPart) (regularSupport K (piece j))
  supports_cover :
    (regularSupport K columnPart ∪ ⋃ j, regularSupport K (piece j) : Set Tiling.Plane)
      =ᵐ[volume] Set.univ
  bases_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ base
  columnBase_disjoint_base : ∀ j, Disjoint columnBase (base j)
  bases_cover : (columnBase ∪ ⋃ j, base j : Set ℝ) =ᵐ[volume] Set.univ

private theorem exists_coordinateSwapTiling :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      ∃ S : TilingSpace K.coordinateSwap Set.univ,
        (S.centres : Set Tiling.Plane) = coordinateSwap ''
          (T.centres : Set Tiling.Plane) := by
  intro K T
  exact Tiling.AxisParallel.Continuous.exists_coordinateSwapTiling T

private theorem coordinateSwap_hullFacts :
    ∀ {K : Region} (T U : TilingSpace K Set.univ)
      (T' U' : TilingSpace K.coordinateSwap Set.univ),
      (T'.centres : Set Tiling.Plane) = coordinateSwap ''
          (T.centres : Set Tiling.Plane) →
      (U'.centres : Set Tiling.Plane) = coordinateSwap ''
          (U.centres : Set Tiling.Plane) →
      U ∈ orbitHull T →
      (U' ∈ orbitHull T') ∧
      (IsTopologicallyMinimal (orbitHull T) →
        IsTopologicallyMinimal (orbitHull T')) := by
  intro K T U T' U' hT' hU' hU
  refine ⟨(Tiling.AxisParallel.Continuous.coordinateSwap_orbitHull_iff hT' hU').mp hU, ?_⟩
  intro hminimal
  exact (Tiling.AxisParallel.Continuous.coordinateSwap_minimal_iff hT').mp hminimal

private theorem exists_translateSequence_to_minimalHullPoint :
    ∀ {K : Region} (T U : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      U ∈ orbitHull T →
      ∃ g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane),
        LocallyFellConverges
          (TilingSpace.centresSequence
            (TilingSpace.translateSequence g T))
          (U.centres : Set Tiling.Plane) := by
  intro K T U _hminimal hU
  change U ∈ closure (AddAction.orbit
    (aePeriodGroup (Set.univ : Set Tiling.Plane)) T) at hU
  obtain ⟨V, hVmem, hVlim⟩ := mem_closure_iff_seq_limit.mp hU
  choose g hg using hVmem
  refine ⟨g, ?_⟩
  have hseq : TilingSpace.translateSequence g T = V := by
    funext n
    exact hg n
  rw [← hseq] at hVlim
  exact (locallyFell_metrizable K Set.univ).2
    (TilingSpace.translateSequence g T) U |>.mp hVlim

private theorem finiteHorizontalComplexity_backToMinimalSource :
    ∀ {K : Region} (T U : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      U ∈ orbitHull T →
      HasFiniteHorizontalComplexity (U.centres : Set Tiling.Plane) →
      HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) := by
  intro K T U hminimal hU hUFLC
  have hHull : orbitHull U = orbitHull T :=
    hminimal.2.2.2 U hU
  have hUminimal : IsTopologicallyMinimal (orbitHull U) := by
    rw [hHull]
    exact hminimal
  have hTmem : T ∈ orbitHull U := by
    rw [hHull]
    exact subset_closure (AddAction.mem_orbit_self T)
  obtain ⟨g, hconv⟩ :=
    exists_translateSequence_to_minimalHullPoint U T hUminimal hTmem
  exact finiteHorizontalComplexity_of_translateLimit U T hUFLC g hconv


private def residueFloorIndex
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (beta : ℝ) : ℕ → ℤ :=
  fun n => Int.floor ((g n : Tiling.Plane).re / beta)

private def residueValue
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    (beta : ℝ) : ℕ → ℝ :=
  fun n => (g n : Tiling.Plane).re -
    (residueFloorIndex g beta n : ℝ) * beta

private theorem residueValue_mem_Icc
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ n, residueValue g beta n ∈ Set.Icc (0 : ℝ) beta := by
  intro n
  have hlo : (residueFloorIndex g beta n : ℝ) ≤
      (g n : Tiling.Plane).re / beta := by
    dsimp [residueFloorIndex]
    exact Int.floor_le _
  have hhi : (g n : Tiling.Plane).re / beta <
      (residueFloorIndex g beta n : ℝ) + 1 := by
    dsimp [residueFloorIndex]
    exact Int.lt_floor_add_one _
  have hlo' : (residueFloorIndex g beta n : ℝ) * beta ≤
      (g n : Tiling.Plane).re := (le_div_iff₀ hbeta).mp hlo
  have hhi' : (g n : Tiling.Plane).re <
      (residueFloorIndex g beta n : ℝ) * beta + beta := by
    have h := (div_lt_iff₀ hbeta).mp hhi
    simpa [add_mul, mul_add, add_comm, add_left_comm, add_assoc] using h
  constructor <;> dsimp [residueValue] <;> linarith

private theorem residue_subsequence_exists
    (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane))
    {beta : ℝ} (hbeta : 0 < beta) :
    ∃ alpha ∈ Set.Icc (0 : ℝ) beta, ∃ phi : ℕ → ℕ,
      StrictMono phi ∧
        Tendsto (residueValue g beta ∘ phi) atTop (nhds alpha) := by
  obtain ⟨alpha, halpha, phi, hphi, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) beta)).tendsto_subseq
      (residueValue_mem_Icc g hbeta)
  exact ⟨alpha, halpha, phi, hphi, hlim⟩

private theorem translate_action_tendsto_wip
    {K : Region} {q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {qlim : aePeriodGroup (Set.univ : Set Tiling.Plane)}
    {X : ℕ → TilingSpace K Set.univ} {U : TilingSpace K Set.univ}
    (hq : Tendsto q atTop (nhds qlim))
    (hX : Tendsto X atTop (nhds U)) :
    Tendsto (fun n => TilingSpace.translate (q n) (X n)) atTop
      (nhds (TilingSpace.translate qlim U)) := by
  have hpair : Tendsto (fun n => (q n, X n)) atTop (nhds (qlim, U)) :=
    by
      rw [nhds_prod_eq]
      exact hq.prodMk hX
  exact (translationAction_continuous K Set.univ).tendsto
    (qlim, U) |>.comp hpair

private theorem exists_alignedResidueLimit :
    ∀ {K : Region} (T U : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      U ∈ orbitHull T →
      ∀ {beta : ℝ}, 0 < beta →
      ∃ (alpha : ℝ) (V : TilingSpace K Set.univ)
        (g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane)),
        0 ≤ alpha ∧ alpha < beta ∧
        (V.centres : Set Tiling.Plane) = ((-alpha : ℝ) : ℂ) +ᵥ
          (U.centres : Set Tiling.Plane) ∧
        (∀ n, ∃ m : ℤ, (g n : Tiling.Plane).re = (m : ℝ) * beta) ∧
        LocallyFellConverges
          (TilingSpace.centresSequence
            (TilingSpace.translateSequence g T))
          (V.centres : Set Tiling.Plane) := by
  intro K T U hminimal hU beta hbeta
  obtain ⟨g₀, hconv₀⟩ :=
    exists_translateSequence_to_minimalHullPoint T U hminimal hU
  have hOld : Tendsto (TilingSpace.translateSequence g₀ T) atTop (nhds U) :=
    ((locallyFell_metrizable K Set.univ).2
      (TilingSpace.translateSequence g₀ T) U).mpr hconv₀
  obtain ⟨alpha, halpha, phi, hphi, hres⟩ :=
    residue_subsequence_exists g₀ hbeta
  have hOld' : Tendsto
      (TilingSpace.translateSequence (g₀ ∘ phi) T) atTop (nhds U) := by
    change Tendsto (TilingSpace.translateSequence g₀ T ∘ phi) atTop (nhds U)
    exact hOld.comp hphi.tendsto_atTop
  by_cases halt : alpha < beta
  · let q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨-((residueValue g₀ beta (phi n) : ℝ) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    let qlim : aePeriodGroup (Set.univ : Set Tiling.Plane) :=
      ⟨-alpha, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
    have hq : Tendsto q atTop (nhds qlim) := by
      rw [tendsto_subtype_rng]
      have hplane : Tendsto (fun n =>
          -((residueValue g₀ beta (phi n) : ℝ) : Tiling.Plane)) atTop
          (nhds (-((alpha : ℝ) : Tiling.Plane))) := by
        convert (Complex.continuous_ofReal.tendsto _).comp hres.neg using 1 <;>
          simp [Function.comp_def]
      simpa only [q, qlim] using hplane
    let V : TilingSpace K Set.univ := TilingSpace.translate qlim U
    let g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨(q n : Tiling.Plane) + (g₀ (phi n) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    have hlim := translate_action_tendsto_wip hq hOld'
    have hseq :
        TilingSpace.translateSequence g T =
          (fun n => TilingSpace.translate (q n)
            (TilingSpace.translateSequence (g₀ ∘ phi) T n)) := by
      funext n
      change TilingSpace.translate (g n) T =
        TilingSpace.translate (q n)
          (TilingSpace.translate (g₀ (phi n)) T)
      have hg : g n = q n + g₀ (phi n) := by
        apply Subtype.ext
        rfl
      rw [hg]
      exact add_vadd (q n) (g₀ (phi n)) T
    have hVcent : (V.centres : Set Tiling.Plane) =
        ((-alpha : ℝ) : ℂ) +ᵥ (U.centres : Set Tiling.Plane) := by
      ext z
      change z ∈ (fun x : Tiling.Plane => x + (qlim : Tiling.Plane)) ''
          (U.centres : Set Tiling.Plane) ↔ _
      rw [show (qlim : Tiling.Plane) = ((-alpha : ℝ) : ℂ) by
        simp [qlim]]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Set.mem_vadd_set.mpr ⟨x, hx, by
          simp [vadd_eq_add, add_comm]
          ⟩
      · intro hz
        rcases Set.mem_vadd_set.mp hz with ⟨x, hx, hxz⟩
        exact ⟨x, hx, by simpa [vadd_eq_add, add_comm] using hxz⟩
    have hconv : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T))
        (V.centres : Set Tiling.Plane) := by
      rw [hseq]
      exact ((locallyFell_metrizable K Set.univ).2 _ V).mp hlim
    refine ⟨alpha, V, g, halpha.1, halt, hVcent, ?_, hconv⟩
    intro n
    refine ⟨residueFloorIndex g₀ beta (phi n), ?_⟩
    dsimp [g, q, residueValue, residueFloorIndex]
    ring
  · have halpha_eq : alpha = beta :=
      le_antisymm halpha.2 (not_lt.mp halt)
    let q : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨((beta - residueValue g₀ beta (phi n) : ℝ) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    let qlim : aePeriodGroup (Set.univ : Set Tiling.Plane) :=
      ⟨0, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩
    have hq : Tendsto q atTop (nhds qlim) := by
      rw [tendsto_subtype_rng]
      dsimp [q, qlim]
      change Tendsto (fun n =>
        ((beta - residueValue g₀ beta (phi n) : ℝ) : Tiling.Plane)) atTop
        (nhds (0 : Tiling.Plane))
      have hreal : Tendsto
          (fun n => beta - residueValue g₀ beta (phi n)) atTop (nhds 0) := by
        have h := (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => beta) atTop (nhds beta)).sub hres
        simpa [halpha_eq] using h
      convert (Complex.continuous_ofReal.tendsto 0).comp hreal using 1 <;>
        simp [Function.comp_def]
    let V : TilingSpace K Set.univ := TilingSpace.translate qlim U
    let g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n =>
      ⟨(q n : Tiling.Plane) + (g₀ (phi n) : Tiling.Plane), by
        simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]
      ⟩
    have hlim := translate_action_tendsto_wip hq hOld'
    have hseq :
        TilingSpace.translateSequence g T =
          (fun n => TilingSpace.translate (q n)
            (TilingSpace.translateSequence (g₀ ∘ phi) T n)) := by
      funext n
      change TilingSpace.translate (g n) T =
        TilingSpace.translate (q n)
          (TilingSpace.translate (g₀ (phi n)) T)
      have hg : g n = q n + g₀ (phi n) := by
        apply Subtype.ext
        rfl
      rw [hg]
      exact add_vadd (q n) (g₀ (phi n)) T
    have hVcent : (V.centres : Set Tiling.Plane) =
        ((0 : ℝ) : ℂ) +ᵥ (U.centres : Set Tiling.Plane) := by
      ext z
      change z ∈ (fun x : Tiling.Plane => x + (qlim : Tiling.Plane)) ''
          (U.centres : Set Tiling.Plane) ↔ _
      dsimp [qlim]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact Set.mem_vadd_set.mpr ⟨x, hx, by simp [vadd_eq_add]
          ⟩
      · intro hz
        rcases Set.mem_vadd_set.mp hz with ⟨x, hx, hxz⟩
        exact ⟨x, hx, by simpa [vadd_eq_add] using hxz⟩
    have hconv : LocallyFellConverges
        (TilingSpace.centresSequence
          (TilingSpace.translateSequence g T))
        (V.centres : Set Tiling.Plane) := by
      rw [hseq]
      exact ((locallyFell_metrizable K Set.univ).2 _ V).mp hlim
    refine ⟨0, V, g, by norm_num, hbeta, ?_, ?_, hconv⟩
    · simpa using hVcent
    · intro n
      refine ⟨residueFloorIndex g₀ beta (phi n) + 1, ?_⟩
      dsimp [g, q, residueValue, residueFloorIndex]
      simp only [Int.cast_add, Int.cast_one]
      ring

private theorem nontrivialVertical_translation_iff :
    ∀ {K : Region} (T U : TilingSpace K Set.univ) (a : ℝ),
      (U.centres : Set Tiling.Plane) = ((a : ℝ) : ℂ) +ᵥ
        (T.centres : Set Tiling.Plane) →
      ((¬ ∃ P : VerticalPlate K (T.centres : Set Tiling.Plane),
          ¬ IsVerticalColumn P ∧
            P.centres = (T.centres : Set Tiling.Plane)) ↔
        ¬ ∃ P : VerticalPlate K (U.centres : Set Tiling.Plane),
          ¬ IsVerticalColumn P ∧
            P.centres = (U.centres : Set Tiling.Plane)) := by
  intro K T U a hU
  have hcarrier : K.openCarrier =
      positiveSimilarity 1 0 '' K.openCarrier := by
    ext z
    constructor
    · intro hz
      exact ⟨z, hz, by simp [positiveSimilarity]
        ⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [positiveSimilarity] using hz
  have hsim (c : Tiling.Plane) (S : Set Tiling.Plane) :
      positiveSimilarity 1 c '' S = c +ᵥ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact Set.mem_vadd_set.mpr ⟨w, hw, by
        simp [positiveSimilarity, vadd_eq_add, add_comm]
        ⟩
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hwz⟩
      refine ⟨w, hw, ?_⟩
      simpa [positiveSimilarity, vadd_eq_add, add_comm] using hwz
  have hforward : ∀ {A B : TilingSpace K Set.univ} (c : Tiling.Plane),
      (B.centres : Set Tiling.Plane) = c +ᵥ (A.centres : Set Tiling.Plane) →
      (¬ ∃ P : VerticalPlate K (A.centres : Set Tiling.Plane),
          ¬ IsVerticalColumn P ∧
            P.centres = (A.centres : Set Tiling.Plane)) →
      ¬ ∃ P : VerticalPlate K (B.centres : Set Tiling.Plane),
          ¬ IsVerticalColumn P ∧
            P.centres = (B.centres : Set Tiling.Plane) := by
    intro A B c hB hA hBexists
    have hBimage : positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane) =
        (B.centres : Set Tiling.Plane) := by
      rw [hsim c, hB]
    rw [← hBimage] at hBexists
    rcases hBexists with ⟨Q, hQnotcol, hQcent⟩
    let e₀ := verticalPlate_positiveSimilarityEquiv
      (K := K) (R := K)
      (T := positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane))
      (s := 1) (r := 0) one_pos hcarrier (-c) Q
    have he₀cent : e₀.centres =
        positiveSimilarity 1 (-c) '' Q.centres :=
      verticalPlate_positiveSimilarityEquiv_centres_image
        one_pos hcarrier (-c) Q
    have himage : positiveSimilarity 1 (-c) ''
        (positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane)) =
        (A.centres : Set Tiling.Plane) := by
      calc
        positiveSimilarity 1 (-c) ''
            (positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane)) =
            (-c) +ᵥ (c +ᵥ (A.centres : Set Tiling.Plane)) := by
          rw [hsim, hsim]
        _ = (A.centres : Set Tiling.Plane) := by
          rw [← add_vadd]
          simp
    have he₀cent' : e₀.centres =
        positiveSimilarity 1 (-c) ''
          (positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane)) := by
      simpa only [hQcent] using he₀cent
    have hPexists : ∃ P : VerticalPlate K (positiveSimilarity 1 (-c) ''
        (positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane))),
        ¬ IsVerticalColumn P ∧
          P.centres = positiveSimilarity 1 (-c) ''
            (positiveSimilarity 1 c '' (A.centres : Set Tiling.Plane)) := by
      refine ⟨e₀, ?_, ?_⟩
      · intro he₀col
        exact hQnotcol
          ((verticalPlate_positiveSimilarityEquiv_isVerticalColumn
            one_pos hcarrier (-c) Q).mpr he₀col)
      · exact he₀cent'
    rw [himage] at hPexists
    exact hA hPexists
  constructor
  · exact hforward ((a : ℝ) : ℂ) hU
  · apply hforward ((-a : ℝ) : ℂ)
    rw [hU, ← add_vadd]
    simp

private noncomputable def coordinateSwapIsometry_local :
    Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem hasFLC_coordinateSwap_to_original
    (S : Set Tiling.Plane) :
    HasFLC (coordinateSwap '' S) → HasFLC S := by
  intro h
  constructor
  · intro Q hQ
    have hQ' : Bornology.IsBounded (coordinateSwap '' Q) :=
      coordinateSwapIsometry_local.lipschitz.isBounded_image hQ
    have hfinite := h.1 (coordinateSwap '' Q) hQ'
    refine Set.Finite.of_finite_image (s := S ∩ Q) (f := coordinateSwap) ?_
      coordinateSwap.injective.injOn
    rw [Set.image_inter coordinateSwap.injective]
    exact hfinite
  · intro R hR
    let A : Set Tiling.Plane :=
      (S - S) ∩ Metric.closedBall 0 R
    refine Set.Finite.of_finite_image (s := A) (f := coordinateSwap) ?_
      coordinateSwap.injective.injOn
    apply (h.2 R hR).subset
    rintro d ⟨d₀, ⟨hd, hdR⟩, rfl⟩
    rcases hd with ⟨b, hb, a, ha, rfl⟩
    refine ⟨⟨coordinateSwap b, ⟨b, hb, rfl⟩,
      coordinateSwap a, ⟨a, ha, rfl⟩, ?_⟩, ?_⟩
    · simp only [map_sub]
    · rw [Metric.mem_closedBall, dist_zero_right]
      have hnorm : ‖coordinateSwap (b - a)‖ = ‖b - a‖ := by
        change ‖coordinateSwapIsometry_local (b - a)‖ = ‖b - a‖
        exact coordinateSwapIsometry_local.norm_map _
      rw [hnorm]
      simpa only [Metric.mem_closedBall, dist_zero_right] using hdR

private theorem hasFLC_coordinateSwap_iff :
    ∀ (S : Set Tiling.Plane), HasFLC (coordinateSwap '' S) ↔ HasFLC S := by
  intro S
  constructor
  · exact hasFLC_coordinateSwap_to_original S
  · intro h
    have h' := hasFLC_coordinateSwap_to_original (coordinateSwap '' S)
      (by simpa [Set.image_image, coordinateSwap_apply_apply] using h)
    simpa [Set.image_image, coordinateSwap_apply_apply] using h'

private theorem exists_nonColumnPlateIndexing :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      Nonempty (NonColumnPlateIndexing T) := by
  intro K T hFiniteHorizontal
  have hFinite := (noncolumnVerticalPlates_finite T.tilesOn).1
  let S : Set (Continuous.VerticalPlate K (T.centres : Set Tiling.Plane)) :=
    Continuous.nonColumnVerticalPlates K (T.centres : Set Tiling.Plane)
  let _ : Fintype S := hFinite.fintype
  let e : Fin S.ncard ≃ S :=
    (Finite.equivFinOfCardEq (Nat.card_coe_set_eq S)).symm
  refine ⟨{
    numberOfPieces := S.ncard
    plate := fun j ↦ (e j).1
    plate_nonColumn := fun j ↦ (e j).2
    equiv := e
    plate_eq := fun j ↦ rfl }⟩

private theorem tilesOn_regularSupport_of_subset
    {K : Region} {S T E : Set Tiling.Plane}
    (hST : S ⊆ T) (hTile : TilesOn K T E) :
    TilesOn K S (regularSupport K S) := by
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    intro s hs t ht hst
    exact hTile.2.1 (hST hs) (hST ht) hst
  refine ⟨hTile.1.mono hST, hpacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpacking] with x hx
  exact (Iff.of_eq hx.symm).trans (by
    change x ∈ (⋃ s : S, (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
      ∃ s : S, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier
    exact Set.mem_iUnion)

private theorem columnPart_eq_verticalColumnCentres
    {K : Region} {T : TilingSpace K Set.univ} :
    (⋃ P : {P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane) //
      Continuous.IsVerticalColumn P}, P.1.centres) =
      Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) := by
  rw [Continuous.verticalColumnCentres_eq]
  rfl

private theorem columnFamily_tiles
    {K : Region} {T : TilingSpace K Set.univ} :
    TilesOn K (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))
      (regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane))) := by
  apply tilesOn_regularSupport_of_subset
    (S := Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))
    (T := (T.centres : Set Tiling.Plane))
  · intro z hz
    rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hz
    obtain ⟨P, hP⟩ := hz
    obtain ⟨p, hp, rfl⟩ := hP
    exact p.2
  · exact T.tilesOn

private theorem centres_partition_local
    {K : Region} (T : TilingSpace K Set.univ)
    (I : NonColumnPlateIndexing T) :
    Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) ∪
        (⋃ j, (I.plate j).centres) = (T.centres : Set Tiling.Plane) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with hzColumn | hzPiece
    · rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hzColumn
      obtain ⟨P, hP⟩ := hzColumn
      obtain ⟨p, hp, rfl⟩ := hP
      exact p.2
    · rw [Set.mem_iUnion] at hzPiece
      obtain ⟨j, hj⟩ := hzPiece
      obtain ⟨p, hp, rfl⟩ := hj
      exact p.2
  · intro z hz
    let t : (T.centres : Set Tiling.Plane) := ⟨z, hz⟩
    let P := Continuous.VerticalPlate.ofCentre (K := K) t
    by_cases hColumn : Continuous.IsVerticalColumn P
    · left
      rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
      refine ⟨⟨P, hColumn⟩, ?_⟩
      exact Continuous.VerticalPlate.mem_centres_ofCentre t
    · right
      let j : Fin I.numberOfPieces := I.equiv.symm ⟨P, hColumn⟩
      rw [Set.mem_iUnion]
      refine ⟨j, ?_⟩
      rw [I.plate_eq j]
      rw [I.equiv.apply_symm_apply]
      exact Continuous.VerticalPlate.mem_centres_ofCentre t

private theorem verticalPlate_countable_local
    {K : Region} {S : Set Tiling.Plane}
    (hTile : TilesOn K S Set.univ) :
    Countable (Continuous.VerticalPlate K S) := by
  let _ : Countable S := hTile.1.to_subtype
  apply Function.Surjective.countable
    (f := fun t : S ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
  intro P
  obtain ⟨p, hp⟩ := P.nonempty_supp
  refine ⟨p, ?_⟩
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp

private theorem support_partition_local
    {K : Region} (T : TilingSpace K Set.univ)
    (I : NonColumnPlateIndexing T) :
    Set.PairwiseDisjoint Set.univ
      (fun j ↦ regularSupport K (I.plate j).centres) ∧
    (∀ j, Disjoint (regularSupport K
      (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)))
      (regularSupport K (I.plate j).centres)) ∧
      (regularSupport K (Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane)) ∪
        ⋃ j, regularSupport K (I.plate j).centres : Set Tiling.Plane)
      =ᵐ[volume] Set.univ := by
  let A : Sum Unit (Fin I.numberOfPieces) → Set Tiling.Plane
    | Sum.inl _ => Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)
    | Sum.inr j => (I.plate j).centres
  have hParts : Set.PairwiseDisjoint Set.univ A := by
    intro a _ b _ hab
    cases a with
    | inl u =>
        cases b with
        | inl v => exact False.elim (hab rfl)
        | inr j =>
            change Disjoint (Continuous.verticalColumnCentres K
              (T.centres : Set Tiling.Plane)) (I.plate j).centres
            rw [Continuous.verticalColumnCentres_eq]
            apply Set.disjoint_iUnion_left.2
            intro P
            apply (Continuous.verticalPlateCentres_pairwiseDisjoint K
              (T.centres : Set Tiling.Plane)) (Set.mem_univ _) (Set.mem_univ _)
            intro hEq
            have hColumn := P.2
            rw [hEq] at hColumn
            exact I.plate_nonColumn j hColumn
    | inr i =>
        cases b with
        | inl u =>
            change Disjoint (I.plate i).centres
              (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))
            rw [Continuous.verticalColumnCentres_eq]
            apply Set.disjoint_iUnion_right.2
            intro P
            apply (Continuous.verticalPlateCentres_pairwiseDisjoint K
              (T.centres : Set Tiling.Plane)) (Set.mem_univ _) (Set.mem_univ _)
            intro hEq
            exact I.plate_nonColumn i (hEq.symm ▸ P.2)
        | inr j =>
            change Disjoint (I.plate i).centres (I.plate j).centres
            apply (Continuous.verticalPlateCentres_pairwiseDisjoint K
              (T.centres : Set Tiling.Plane)) (Set.mem_univ _) (Set.mem_univ _)
            intro hEq
            apply hab
            exact congrArg Sum.inr (I.equiv.injective (Subtype.ext
              ((I.plate_eq i).symm.trans (hEq.trans (I.plate_eq j)))))
  have hUnion : (⋃ a, A a) = (T.centres : Set Tiling.Plane) := by
    rw [show (⋃ a, A a) =
      Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane) ∪
        ⋃ j, (I.plate j).centres by
      ext z
      simp [A]]
    exact centres_partition_local T I
  have hSupport : Set.PairwiseDisjoint Set.univ
      (fun q : Sum Unit (Fin I.numberOfPieces) ↦ regularSupport K (A q)) ∧
      (⋃ q : Sum Unit (Fin I.numberOfPieces), regularSupport K (A q))
        =ᵐ[volume] Set.univ :=
    regularSupport_pairwiseDisjoint A hParts hUnion T.tilesOn
  have hSupportPair : Set.PairwiseDisjoint Set.univ
      (fun q : Sum Unit (Fin I.numberOfPieces) ↦ regularSupport K (A q)) :=
    hSupport.1
  have hPiecePair : Set.PairwiseDisjoint Set.univ
      (fun j ↦ regularSupport K (I.plate j).centres) := by
    intro i _ j _ hij
    have hne : (Sum.inr i : Sum Unit (Fin I.numberOfPieces)) ≠
        (Sum.inr j : Sum Unit (Fin I.numberOfPieces)) := by
      intro h
      exact hij (Sum.inr.inj h)
    have hs := hSupportPair
      (show Sum.inr i ∈ (Set.univ : Set (Sum Unit (Fin I.numberOfPieces)))
        from Set.mem_univ _)
      (show Sum.inr j ∈ (Set.univ : Set (Sum Unit (Fin I.numberOfPieces)))
        from Set.mem_univ _) hne
    exact hs
  have hColumnPiece : ∀ j, Disjoint (regularSupport K
      (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)))
      (regularSupport K (I.plate j).centres) := by
    intro j
    have hs := hSupportPair
      (show (Sum.inl () : Sum Unit (Fin I.numberOfPieces)) ∈
        (Set.univ : Set (Sum Unit (Fin I.numberOfPieces)))
        from Set.mem_univ _)
      (show (Sum.inr j : Sum Unit (Fin I.numberOfPieces)) ∈
        (Set.univ : Set (Sum Unit (Fin I.numberOfPieces)))
        from Set.mem_univ _) (by simp)
    exact hs
  have hAUnion : (⋃ q : Sum Unit (Fin I.numberOfPieces), regularSupport K (A q)) =
      regularSupport K (Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane)) ∪
        ⋃ j, regularSupport K (I.plate j).centres := by
    ext z
    simp [A]
  rw [hAUnion] at hSupport
  exact ⟨hPiecePair, hColumnPiece, hSupport.2⟩

private theorem verticalColumnSupport_verticalInvariant_local
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (y : ℝ) :
    (((y : ℂ) * Complex.I) +ᵥ
        regularSupport K (Continuous.verticalColumnCentres K T)) =
      regularSupport K (Continuous.verticalColumnCentres K T) := by
  rw [Continuous.verticalColumnCentres_eq, regularSupport_iUnion]
  rw [← interior_vadd, ← closure_vadd]
  congr 2
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
  constructor
  · rintro ⟨P, hzP⟩
    refine ⟨P, ?_⟩
    have hinv := (Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
      hTile P.1 P.2).2.2.2 y
    have hmem := Set.ext_iff.mp hinv z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
    exact hmem.mp hzP
  · rintro ⟨P, hzP⟩
    refine ⟨P, ?_⟩
    have hinv := (Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
      hTile P.1 P.2).2.2.2 y
    have hmem := Set.ext_iff.mp hinv z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
    exact hmem.mpr hzP

private theorem verticalColumnSupport_isVerticalSlab_local
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K (Continuous.verticalColumnCentres K T) = Complex.re ⁻¹' X := by
  obtain ⟨X, hX⟩ := (verticalInvariant_iff_product
    (regularSupport K (Continuous.verticalColumnCentres K T))).mp
      (verticalColumnSupport_verticalInvariant_local hTile)
  have hreg := (regularSupport_isRegularOpen K
    (Continuous.verticalColumnCentres K T)).2
  change regularSupport K (Continuous.verticalColumnCentres K T) = Complex.re ⁻¹' X at hX
  rw [hX, Complex.closure_preimage_re, Complex.interior_preimage_re] at hreg
  refine ⟨X, ?_, hX⟩
  ext x
  have hx := Set.ext_iff.mp hreg (x : ℂ)
  simpa using hx.symm

private theorem verticalPlate_base_nonempty_local
    {K : Region} {T : Set Tiling.Plane}
    (P : Continuous.VerticalPlate K T) : P.base.Nonempty := by
  obtain ⟨t, htP⟩ := P.nonempty_supp
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨(t.1 + u).re, t.1 + u, ?_, rfl⟩
  change t.1 + u ∈ regularSupport K P.centres
  unfold regularSupport
  have hopen : IsOpen (openUnion K P.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1
  apply hopen.subset_interior_closure
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
  refine ⟨⟨t.1, ⟨t, htP, rfl⟩⟩, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hu' : u ∈ K.openCarrier := by
    rw [← K.openCarrier_regularOpen.2,
      show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
    exact hu
  simpa only [vadd_eq_add, neg_add_cancel_left] using hu'

private theorem regularSupport_nonempty_iff_local
    {K : Region} {S : Set Tiling.Plane} :
    (regularSupport K S).Nonempty ↔ S.Nonempty := by
  constructor
  · intro hS
    by_contra hEmpty
    have hEq : S = (∅ : Set Tiling.Plane) := Set.not_nonempty_iff_eq_empty.mp hEmpty
    rw [hEq, regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion] at hS
    simp at hS
  · rintro ⟨s, hs⟩
    obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
    refine ⟨s + u, ?_⟩
    unfold regularSupport
    have hopen : IsOpen (openUnion K S) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun t : S ↦ isOpen_interior.vadd t.1
    apply hopen.subset_interior_closure
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨s, hs⟩, ?_⟩
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have hu' : u ∈ K.openCarrier := by
      rw [← K.openCarrier_regularOpen.2,
        show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
      exact hu
    simpa only [vadd_eq_add, neg_add_cancel_left] using hu'

private theorem exists_verticalComponentGeometry :
    ∀ {K : Region} (T : TilingSpace K Set.univ)
      (I : NonColumnPlateIndexing T),
      Nonempty (VerticalComponentGeometry T I) := by
  intro K T I
  classical
  let columnPart : Set Tiling.Plane :=
    Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)
  let columnPlates : Set (Continuous.VerticalPlate K (T.centres : Set Tiling.Plane)) :=
    {P | Continuous.IsVerticalColumn P}
  let piece : Fin I.numberOfPieces → Set Tiling.Plane :=
    fun j ↦ (I.plate j).centres
  obtain ⟨columnBase, hcolumnBaseRegular, hcolumnSupport⟩ :=
    verticalColumnSupport_isVerticalSlab_local T.tilesOn
  refine ⟨{
    columnPart := columnPart
    columnPlates := columnPlates
    piece := piece
    columnBase := columnBase
    base := fun j ↦ (I.plate j).base
    columnPlates_areColumns := by
      intro P hP
      exact hP
    columnPlates_areComplete := by
      intro P hP
      exact Continuous.VerticalPlate.isCenterColumn_of_isVerticalColumn
        T.tilesOn P hP
    columnPart_eq := by
      dsimp [columnPart, columnPlates]
      rw [Continuous.verticalColumnCentres_eq]
    piece_eq := by
      intro j
      rfl
    piece_nonempty := by
      intro j
      dsimp [piece]
      obtain ⟨p, hp⟩ := (I.plate j).nonempty_supp
      exact ⟨p.1, ⟨p, hp, rfl⟩⟩
    pieces_pairwiseDisjoint := by
      intro i _ j _ hij
      apply (Continuous.verticalPlateCentres_pairwiseDisjoint K
        (T.centres : Set Tiling.Plane)) (Set.mem_univ _) (Set.mem_univ _)
      intro hEq
      apply hij
      exact I.equiv.injective (Subtype.ext
        ((I.plate_eq i).symm.trans (hEq.trans (I.plate_eq j))))
    column_disjoint_piece := by
      intro j
      rw [show columnPart = Continuous.verticalColumnCentres K
        (T.centres : Set Tiling.Plane) by rfl]
      rw [Continuous.verticalColumnCentres_eq]
      apply Set.disjoint_iUnion_left.2
      intro P
      apply (Continuous.verticalPlateCentres_pairwiseDisjoint K
        (T.centres : Set Tiling.Plane)) (Set.mem_univ _) (Set.mem_univ _)
      intro hEq
      have hColumn := P.2
      rw [hEq] at hColumn
      exact I.plate_nonColumn j hColumn
    centres_partition := by
      simpa [columnPart, piece] using centres_partition_local T I
    columnBase_open := by
      have hOpen := (regularSupport_isRegularOpen K
        (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane))).1
      rw [hcolumnSupport] at hOpen
      apply interior_eq_iff_isOpen.mp
      apply (Set.preimage_injective.mpr (by
        intro x
        exact ⟨(x : ℂ), Complex.ofReal_re x⟩))
      rw [← Complex.interior_preimage_re, hOpen.interior_eq]
    columnBase_regular := hcolumnBaseRegular.symm
    columnBase_nonempty_iff := by
      constructor
      · intro h
        obtain ⟨x, hx⟩ := h
        have hz : (x : ℂ) ∈ regularSupport K
            (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)) := by
          rw [hcolumnSupport]
          exact hx
        exact (regularSupport_nonempty_iff_local (K := K)).mp ⟨(x : ℂ), hz⟩
      · intro h
        obtain ⟨z, hz⟩ :=
          (regularSupport_nonempty_iff_local (K := K)
            (S := Continuous.verticalColumnCentres K
              (T.centres : Set Tiling.Plane))).mpr h
        have hz' : z ∈ Complex.re ⁻¹' columnBase := by
          rw [← hcolumnSupport]
          exact hz
        exact ⟨z.re, hz'⟩
    base_open := by
      intro j
      rw [(I.plate j).support_isVerticalSlab T.tilesOn |>.1]
      exact isOpen_interior
    base_regular := by
      intro j
      exact (I.plate j).support_isVerticalSlab T.tilesOn |>.1 |>.symm
    base_nonempty := by
      intro j
      exact verticalPlate_base_nonempty_local (I.plate j)
    columnSupport_eq := by
      simpa [columnPart] using hcolumnSupport
    pieceSupport_eq := by
      intro j
      dsimp [piece]
      exact (I.plate j).support_isVerticalSlab T.tilesOn |>.2
    column_tiles := by
      have hc := columnFamily_tiles (K := K) (T := T)
      rw [hcolumnSupport] at hc
      simpa [columnPart] using hc
    piece_tiles := by
      intro j
      have hsub : (I.plate j).centres ⊆ (T.centres : Set Tiling.Plane) := by
        intro z hz
        obtain ⟨p, hp, rfl⟩ := hz
        exact p.2
      have hp := tilesOn_regularSupport_of_subset
        (T := (T.centres : Set Tiling.Plane))
          hsub T.tilesOn
      have hsupport : regularSupport K (I.plate j).centres =
          Complex.re ⁻¹' (I.plate j).base := by
        simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
          (I.plate j).support_isVerticalSlab T.tilesOn |>.2
      rw [hsupport] at hp
      simpa [piece] using hp
    support_pairwiseDisjoint := by
      simpa [piece] using (support_partition_local T I).1
    columnSupport_disjoint_piece := by
      intro j
      simpa [columnPart, piece] using (support_partition_local T I).2.1 j
    supports_cover := by
      simpa [columnPart, piece] using (support_partition_local T I).2.2
    bases_pairwiseDisjoint := by
      intro i _ j _ hij
      change Disjoint ((I.plate i).base) ((I.plate j).base)
      rw [Set.disjoint_left]
      intro x hxi hxj
      have hsi : regularSupport K (I.plate i).centres =
          Complex.re ⁻¹' (I.plate i).base := by
        simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
          (I.plate i).support_isVerticalSlab T.tilesOn |>.2
      have hsj : regularSupport K (I.plate j).centres =
          Complex.re ⁻¹' (I.plate j).base := by
        simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
          (I.plate j).support_isVerticalSlab T.tilesOn |>.2
      have hzi : (x : ℂ) ∈ regularSupport K (piece i) := by
        rw [show piece i = (I.plate i).centres by rfl, hsi]
        exact hxi
      have hzj : (x : ℂ) ∈ regularSupport K (piece j) := by
        rw [show piece j = (I.plate j).centres by rfl, hsj]
        exact hxj
      exact Set.disjoint_left.1
        ((support_partition_local T I).1 (Set.mem_univ _) (Set.mem_univ _) hij)
        hzi hzj
    columnBase_disjoint_base := by
      intro j
      rw [Set.disjoint_left]
      intro x hxc hxj
      have hzc : (x : ℂ) ∈ regularSupport K columnPart := by
        rw [show columnPart = Continuous.verticalColumnCentres K
          (T.centres : Set Tiling.Plane) by rfl, hcolumnSupport]
        exact hxc
      have hzj : (x : ℂ) ∈ regularSupport K (piece j) := by
        have hsj : regularSupport K (I.plate j).centres =
            Complex.re ⁻¹' (I.plate j).base := by
          simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
            (I.plate j).support_isVerticalSlab T.tilesOn |>.2
        rw [show piece j = (I.plate j).centres by rfl, hsj]
        exact hxj
      exact Set.disjoint_left.1 ((support_partition_local T I).2.1 j)
        hzc (by simpa [piece] using hzj)
    bases_cover := by
      let D : Set Tiling.Plane :=
        regularSupport K columnPart ∪ ⋃ j, regularSupport K (piece j)
      let B : Set ℝ := columnBase ∪ ⋃ j, (I.plate j).base
      have hD : D =ᵐ[volume] Set.univ := by
        simpa [D] using (support_partition_local T I).2.2
      have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hD
      have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume,
          ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∈ D := by
        filter_upwards [hpull] with p hp
        have heq : ({ re := p.1, im := p.2 } : ℂ) =
            (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by
          apply Complex.ext <;> simp
        change (({ re := p.1, im := p.2 } : ℂ) ∈ D) =
          (({ re := p.1, im := p.2 } : ℂ) ∈ (Set.univ : Set Tiling.Plane)) at hp
        rw [heq] at hp
        exact (Iff.of_eq hp).mpr (Set.mem_univ _)
      have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod hprod
      filter_upwards [hslices] with x hx
      have hxB : x ∈ B := by
        obtain ⟨y, hy⟩ := hx.exists
        have hyD : ((x : ℂ) + (y : ℂ) * Complex.I) ∈ D := by
          simpa using hy
        rcases hyD with hyColumn | hyPiece
        · left
          have hy' : ((x : ℂ) + (y : ℂ) * Complex.I) ∈
              Complex.re ⁻¹' columnBase := by
            rw [← hcolumnSupport]
            exact hyColumn
          simpa using hy'
        · right
          obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hyPiece
          have hj' : ((x : ℂ) + (y : ℂ) * Complex.I) ∈
              Complex.re ⁻¹' (I.plate j).base := by
            have hsj : regularSupport K (I.plate j).centres =
                Complex.re ⁻¹' (I.plate j).base := by
              simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
                (I.plate j).support_isVerticalSlab T.tilesOn |>.2
            rw [← hsj]
            exact hj
          exact Set.mem_iUnion.mpr ⟨j, by simpa using hj'⟩
      apply propext
      exact ⟨(fun _ ↦ Set.mem_univ x), fun _ ↦ hxB⟩
      }⟩

private theorem exists_componentPeriodData :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      Nonempty (ComponentPeriodData T) := by
  intro K T hFHC
  obtain ⟨beta, hbeta, hperiod⟩ :=
    Continuous.continuousVerticalPlateSupport_periodic T.tilesOn hFHC
  refine ⟨{
    beta := beta
    beta_pos := hbeta
    column_periodic := hperiod.1
    plate_periodic := ?_ }⟩
  intro P hP
  exact hperiod.2 P hP

private theorem nonColumnPlate_base_proper :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      (¬ ∃ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P ∧
          P.centres = (T.centres : Set Tiling.Plane)) →
      ∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P → P.base ≠ Set.univ := by
  intro K T hNontrivial P hNoncolumn hFull
  let _ : Countable (T.centres : Set Tiling.Plane) := T.tilesOn.1.to_subtype
  let _ : Countable (Continuous.VerticalPlate K
      (T.centres : Set Tiling.Plane)) := by
    apply Function.Surjective.countable
      (f := fun t : (T.centres : Set Tiling.Plane) ↦
        Continuous.VerticalPlate.ofCentre (K := K) t)
    intro Q
    obtain ⟨q, hq⟩ := Q.nonempty_supp
    refine ⟨q, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff Q q).1 hq
  have hPair := (regularSupport_pairwiseDisjoint
    (fun Q : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane) ↦ Q.centres)
    (verticalPlateCentres_pairwiseDisjoint K (T.centres : Set Tiling.Plane))
    (iUnion_verticalPlateCentres K (T.centres : Set Tiling.Plane)) T.tilesOn).1
  obtain ⟨hPbase, hPsupport⟩ := P.support_isVerticalSlab T.tilesOn
  have hPfull : P.support = Set.univ := by
    rw [hPsupport, hFull]
    simp
  apply hNontrivial
  refine ⟨P, hNoncolumn, ?_⟩
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    exact q.2
  · intro x hx
    let t : (T.centres : Set Tiling.Plane) := ⟨x, hx⟩
    let Q := Continuous.VerticalPlate.ofCentre (K := K) t
    have hQeq : Q = P := by
      by_contra hneq
      have hdisj : Disjoint P.support Q.support := by
        have hPQ : P ≠ Q := by
          intro h
          exact hneq h.symm
        exact hPair (Set.mem_univ P) (Set.mem_univ Q) hPQ
      have hQempty : Q.support = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact Set.disjoint_left.1 hdisj
          (by rw [hPfull]; trivial) hz
      obtain ⟨q, hq⟩ := Q.nonempty_supp
      obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
      change c ∈ K.openCarrier at hc
      have hmem : (q : Tiling.Plane) + c ∈ Q.support := by
        change (q : Tiling.Plane) + c ∈ regularSupport K Q.centres
        rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion, mem_interior_iff_mem_nhds]
        have hopen : IsOpen (openUnion K Q.centres) := by
          rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
          exact isOpen_iUnion fun s ↦
            (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _
              K.openCarrier_regularOpen.1
        apply Filter.mem_of_superset (hopen.mem_nhds ?_) subset_closure
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨(q : Tiling.Plane), ⟨q, hq, rfl⟩⟩, by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [vadd_eq_add] using hc⟩
      rw [hQempty] at hmem
      exact hmem
    have hxt : x ∈ Q.centres := by
      exact VerticalPlate.mem_centres_ofCentre t
    rw [hQeq] at hxt
    exact hxt

private theorem cylinder_periodic_gives_base_periodic :
    ∀ {X : Set ℝ} {beta : ℝ},
      Tiling.RationalPolygonal.SetPeriodicBy
        (Complex.re ⁻¹' X) ((beta : ℝ) : ℂ) →
      ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X := by
  intro X beta hperiod x
  simpa [Tiling.RationalPolygonal.SetPeriodicBy, Complex.add_re] using
    hperiod (x : ℂ)

private theorem cylinder_twoPeriods_give_latticePeriodic :
    ∀ {X : Set ℝ} {beta : ℝ}, 0 < beta →
      Tiling.RationalPolygonal.SetPeriodicBy
        (Complex.re ⁻¹' X) ((beta : ℝ) : ℂ) →
      IsLatticePeriodic (Complex.re ⁻¹' X) := by
  intro X beta hbeta hperiod
  apply (isLatticePeriodic_iff_doublyPeriodic (Complex.re ⁻¹' X)).2
  refine ⟨((beta : ℝ) : ℂ), Complex.I, ?_, hperiod, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg i
    fin_cases i
    · have hreal := congrArg Complex.re hg
      rcases (by simpa using hreal) with hzero | hzero
      · simpa using hzero
      · exact False.elim ((ne_of_gt hbeta) hzero)
    · have himag := congrArg Complex.im hg
      simpa using himag
  · intro z
    simp [Complex.add_re]

private theorem finiteComplexity_branch :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      HasFLC (T.centres : Set Tiling.Plane) →
      Nonempty (MinimalTilingStructureData K T) := by
  intro K T hMinimal hFLC
  have hTnonempty : (T.centres : Set Tiling.Plane).Nonempty := by
    obtain ⟨x, hx⟩ := T.tilesOn.2.2.exists
    obtain ⟨s, hs⟩ := hx.mp (Set.mem_univ x)
    exact ⟨s.1, s.2⟩
  have hTsupport : regularSupport K (T.centres : Set Tiling.Plane) = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) T.tilesOn
  have hEmptyTiles : TilesOn K (∅ : Set Tiling.Plane)
      (Complex.re ⁻¹' (∅ : Set ℝ)) := by
    rw [tilesOn_iff_multiplicity]
    refine ⟨Set.countable_empty, ?_, ?_⟩
    · intro p hp q hq hpq
      exact False.elim (hp.elim)
    · filter_upwards with x
      simp
  have hEmptySupport : regularSupport K (∅ : Set Tiling.Plane) = ∅ := by
    simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
  have hEmptyLattice : IsLatticePeriodic (∅ : Set Tiling.Plane) := by
    simpa using (cylinder_twoPeriods_give_latticePeriodic
      (X := (∅ : Set ℝ)) (beta := (1 : ℝ)) zero_lt_one (by
        intro z
        simp))
  have hFullLattice : IsLatticePeriodic (Set.univ : Set Tiling.Plane) := by
    simpa using (cylinder_twoPeriods_give_latticePeriodic
      (X := (Set.univ : Set ℝ)) (beta := (1 : ℝ)) zero_lt_one (by
        intro z
        simp))
  refine ⟨{
    orientation := Axis.vertical
    selectedRegion := K
    selectedTiling := T
    orientation_spec := Or.inl ⟨rfl, rfl, rfl⟩
    selected_minimal := hMinimal
    numberOfPieces := 1
    columnPart := ∅
    columnPlates := ∅
    columnPlates_areColumns := by simp
    columnPlates_areComplete := by simp
    columnPart_eq := by simp
    piece := fun _ ↦ (T.centres : Set Tiling.Plane)
    piece_nonempty := by intro j; simpa using hTnonempty
    pieces_pairwiseDisjoint := by
      intro i _ j _ hij
      fin_cases i
      fin_cases j
      simp_all
    column_disjoint_piece := by simp
    centres_partition := by
      ext x
      simp [Set.mem_iUnion]
    piece_hasFLC := by intro j; simpa using hFLC
    finiteComplexity_normalForm := by
      intro _
      exact ⟨by simp, rfl, ⟨0, rfl⟩⟩
    finiteHorizontalComplexity_of_nonFLC := by
      intro h
      exact False.elim (h hFLC)
    columnBase := ∅
    base := fun _ ↦ Set.univ
    columnBase_open := isOpen_empty
    columnBase_regular := by simp
    columnBase_nonempty_iff := by simp
    base_open := by intro j; exact isOpen_univ
    base_regular := by intro j; simp
    base_nonempty := by intro j; exact Set.univ_nonempty
    columnSupport_eq := by simp [hEmptySupport]
    pieceSupport_eq := by
      intro j
      simp [hTsupport]
    column_tiles := by simpa using hEmptyTiles
    piece_tiles := by
      intro j
      simpa using T.tilesOn
    support_pairwiseDisjoint := by
      intro i _ j _ hij
      fin_cases i
      fin_cases j
      simp_all
    columnSupport_disjoint_piece := by simp [hEmptySupport]
    supports_cover := by
      rw [hEmptySupport]
      have hpieces :
          (⋃ j : Fin 1, regularSupport K (T.centres : Set Tiling.Plane)) =
            regularSupport K (T.centres : Set Tiling.Plane) := by
        ext x
        simp
      rw [hpieces, hTsupport]
      exact Filter.Eventually.of_forall (fun _ ↦ by simp)
    bases_pairwiseDisjoint := by
      intro i _ j _ hij
      fin_cases i
      fin_cases j
      simp_all
    columnBase_disjoint_base := by simp
    bases_cover := by
      have hpieces : (⋃ j : Fin 1, (Set.univ : Set ℝ)) = Set.univ := by
        ext x
        simp
      rw [hpieces]
      exact Filter.Eventually.of_forall (fun _ ↦ by simp)
    horizontalPeriod := 1
    horizontalPeriod_pos := zero_lt_one
    columnSupport_periodic := by
      intro x
      simp [hEmptySupport]
    pieceSupport_periodic := by
      intro j x
      simp [hTsupport]
    columnBase_periodic := by simp
    base_periodic := by intro j x; simp
    columnSupport_latticePeriodic := by simpa [hEmptySupport] using hEmptyLattice
    pieceSupport_latticePeriodic := by intro j; simpa [hTsupport] using hFullLattice
    somePart_nonempty := Or.inr ⟨0⟩
    columnBase_proper_of_piece := by
      intro _
      exact Set.empty_ne_univ
    base_proper_of_multiple := by
      intro j h
      rcases h with h | h
      · exact False.elim (not_nonempty_empty h)
      · norm_num at h
    nonFLC_nontrivial := by
      intro h
      exact False.elim (h hFLC)
    nonFLC_components := by
      intro h
      exact False.elim (h hFLC) }⟩

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

private theorem nontrivialVertical_backToMinimalSource :
    ∀ {K : Region} (T U : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      U ∈ orbitHull T →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      (¬ ∃ P : Continuous.VerticalPlate K (U.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P ∧
          P.centres = (U.centres : Set Tiling.Plane)) →
      ∀ {beta : ℝ}, 0 < beta →
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K
          (Continuous.verticalColumnCentres K (T.centres : Set Tiling.Plane)))
        ((beta : ℝ) : ℂ) →
      (∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P →
          Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ)) →
      ¬ ∃ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P ∧
          P.centres = (T.centres : Set Tiling.Plane) := by
  intro K T U hminimal hU hFHC hnontrivialU beta hbeta hcolumnPeriod hplatePeriod
  obtain ⟨alpha, V, g, hα0, hαβ, hVcent, haligned, hconv⟩ :=
    exists_alignedResidueLimit T U hminimal hU hbeta
  obtain ⟨D⟩ :=
    Tiling.AxisParallel.Structure.exists_alignedEarthquakeLimitData
      T V hminimal hFHC hbeta hcolumnPeriod hplatePeriod g haligned hconv
  have hnontrivialV :
      ¬ ∃ Q : Continuous.VerticalPlate K (V.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn Q ∧
          Q.centres = (V.centres : Set Tiling.Plane) := by
    exact (nontrivialVertical_translation_iff U V (-alpha) hVcent).mp
      hnontrivialU
  intro htrivialT
  exact hnontrivialV (D.trivialDecomposition_iff.mp htrivialT)

end Tiling.AxisParallel.Structure


open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Structure
open Tiling.AxisParallel.Topology

noncomputable section

namespace S11Remaining.Target14

open Tiling.AxisParallel

/-- One locally-Fell sequence has at most one limit. -/
private theorem locallyFellConverges_limit_subset
    {A B : ℕ → Set Tiling.Plane} {L M : Set Tiling.Plane}
    (hsub : ∀ n, A n ⊆ B n)
    (hA : LocallyFellConverges A L)
    (hB : LocallyFellConverges B M) : L ⊆ M := by
  intro x hxL
  by_contra hxM
  obtain ⟨hBclosed, hMclosed, hBfell⟩ := hB
  have hB' : LocallyFellConverges B M := ⟨hBclosed, hMclosed, hBfell⟩
  obtain ⟨epsilon, hepsilon, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_compl_iff.mpr hMclosed) x hxM
  let C : Set Tiling.Plane := Metric.closedBall x (epsilon / 2)
  have hCM : Disjoint M C := by
    rw [Set.disjoint_left]
    intro z hzM hzC
    change dist z x ≤ epsilon / 2 at hzC
    have hzMc : z ∈ Mᶜ := hball (by
      rw [Metric.mem_ball]
      exact lt_of_le_of_lt (by simpa [dist_comm] using hzC) (by linarith))
    exact hzMc hzM
  have havoid := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_disjoint_compact
    hB' (isCompact_closedBall x _) hCM
  have hhit := Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
    hA hxL (by linarith : 0 < epsilon / 2)
  obtain ⟨n, ⟨y, hyA, hyx⟩, hn⟩ := (hhit.and havoid).exists
  exact Set.disjoint_left.mp hn (hsub n hyA) (by exact le_of_lt hyx)

private theorem locallyFellConverges_eq_of_same_sequence
    {A : ℕ → Set Tiling.Plane} {L M : Set Tiling.Plane}
    (hL : LocallyFellConverges A L)
    (hM : LocallyFellConverges A M) : L = M := by
  apply Set.Subset.antisymm
  · exact locallyFellConverges_limit_subset (fun _ x hx => hx) hL hM
  · exact locallyFellConverges_limit_subset (fun _ x hx => hx) hM hL

/-- Coerce a carrier-period translation into the full-plane a.e.-period subgroup. -/
private def coeFullPlaneTranslation
    {X : Set ℝ} (u : aePeriodGroup {z : Tiling.Plane | z.re ∈ X}) :
    aePeriodGroup (Set.univ : Set Tiling.Plane) :=
  ⟨u.1, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩

private theorem localized_translate_centres_eq_vadd
    {K : Region} {X : Set ℝ}
    {U : Topology.TilingSpace K {z : Tiling.Plane | z.re ∈ X}}
    (lambda : ℕ → aePeriodGroup {z : Tiling.Plane | z.re ∈ X}) :
    (TilingSpace.centresSequence
      (TilingSpace.translateSequence lambda U)) =
      (fun n ↦ (lambda n : Tiling.Plane) +ᵥ (U.centres : Set Tiling.Plane)) := by
  funext n
  change (fun x : Tiling.Plane => x + (lambda n : Tiling.Plane)) ''
      (U.centres : Set Tiling.Plane) = _
  ext x
  simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm]

end S11Remaining.Target14


noncomputable section

namespace Tiling.AxisParallel.Continuous

/-!
The local obstruction used by S11 target14.  A split into two nonempty colours with
vertical regular-slab supports cannot live inside one vertical plate: C01 plate
minimality identifies the persistent colour with the whole plate.
-/
private theorem persistentTransientSplit_impossible_inside_verticalPlate
    {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    {U : Tiling.AxisParallel.Topology.TilingSpace K Set.univ}
    {T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X}}
    {S : Tiling.AxisParallel.Topology.TilingSpace K
      {z : Tiling.Plane | z.re ∈ X}}
    (Q : VerticalPlate K (U.centres : Set Tiling.Plane))
    (D : PersistentTransientSplit K X T S)
    (hcentres : (S.centres : Set Tiling.Plane) = Q.centres)
    (horientation : D.orientation = Tiling.AxisParallel.Axis.vertical)
    (hpne : D.persistent.Nonempty)
    (htne : D.transient.Nonempty) : False := by
  have hPeq : D.persistent = Q.centres := by
    apply (VerticalPlate.minimal U.tilesOn Q).2.2.2 D.persistent hpne
    · exact hcentres ▸ D.persistent_subset
    · exact ⟨D.persistentBase, D.persistentBase_regular.symm,
        D.persistentSupport_vertical horientation⟩
  obtain ⟨z, hz⟩ := htne
  have hzP : z ∈ D.persistent := by
    rw [hPeq, ← hcentres]
    exact D.transient_subset hz
  exact Set.disjoint_left.mp D.disjoint hzP hz

end Tiling.AxisParallel.Continuous

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

private noncomputable def s11RectangularLattice (beta : ℝ) (hbeta : 0 < beta) :
    PlanarLattice where
  basis := ![Complex.I, (beta : ℂ)]
  independent := by
    rw [LinearIndependent.pair_iffₛ]
    intro a b a' b' h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    norm_num at hre him
    have hb : b = b' := hre.resolve_right hbeta.ne'
    have ha : a = a' := him
    exact ⟨ha, hb⟩

private theorem s11RectangularLattice_le_aePeriodGroup
    {X : Set ℝ} {beta : ℝ} (hbeta : 0 < beta)
    (hopen : IsOpen X) (hregular : interior (closure X) = X)
    (hperiod : ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X) :
    (s11RectangularLattice beta hbeta).toAddSubgroup ≤
      aePeriodGroup (Complex.re ⁻¹' X) := by
  rw [aePeriodGroup_eq_periodGroup_of_regularOpen
    (hopen.preimage Complex.continuous_re) (by
      rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hregular])]
  rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
    AddSubgroup.closure_le]
  rintro z ⟨i, rfl⟩
  change (s11RectangularLattice beta hbeta).basis i +ᵥ
      (Complex.re ⁻¹' X) = Complex.re ⁻¹' X
  apply (Tiling.AxisParallel.setPeriodicBy_iff_vadd_eq _ _).mp
  fin_cases i
  · intro z
    simp [s11RectangularLattice]
  · intro z
    simpa [s11RectangularLattice, Complex.add_re] using hperiod z.re

private theorem s11RectangularLattice_re
    {beta : ℝ} (hbeta : 0 < beta) {z : Tiling.Plane}
    (hz : z ∈ (s11RectangularLattice beta hbeta).toAddSubgroup) :
    ∃ m : ℤ, z.re = (m : ℝ) * beta := by
  rw [PlanarLattice.toAddSubgroup] at hz
  refine AddSubgroup.closure_induction (p := fun z _ ↦
      ∃ m : ℤ, z.re = (m : ℝ) * beta) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨i, rfl⟩
    fin_cases i
    · refine ⟨0, ?_⟩
      norm_num [s11RectangularLattice]
    · refine ⟨1, ?_⟩
      norm_num [s11RectangularLattice]
  · exact ⟨0, by simp⟩
  · rintro a b _ _ ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    change a.re + b.re = _
    rw [hm, hn]
    push_cast
    ring
  · rintro a _ ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    change -a.re = _
    rw [hm]
    push_cast
    ring

private theorem locallyFellConverges_comp_strictMono_s11
    (A : ℕ → Set Tiling.Plane) (S : Set Tiling.Plane)
    (phi : ℕ → ℕ) (hphi : StrictMono phi)
    (hconv : LocallyFellConverges A S) :
    LocallyFellConverges (fun n ↦ A (phi n)) S := by
  rcases hconv with ⟨hA, hS, hconv⟩
  exact ⟨fun n ↦ hA (phi n), hS, hconv.comp hphi.tendsto_atTop⟩

private theorem nonColumnPlate_hasFLC :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      Continuous.HasFiniteHorizontalComplexity (T.centres : Set Tiling.Plane) →
      (¬ ∃ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P ∧
          P.centres = (T.centres : Set Tiling.Plane)) →
      ∀ P : Continuous.VerticalPlate K (T.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P → HasFLC P.centres := by
  intro K T hminimal hFHC hnontrivial P hP
  by_contra hPflc
  obtain ⟨H⟩ := exists_componentPeriodData T hFHC
  have hbaseProper := nonColumnPlate_base_proper T hnontrivial P hP
  obtain ⟨hbaseRegular, hsupport⟩ := P.support_isVerticalSlab T.tilesOn
  have hbaseOpen : IsOpen P.base := by
    rw [hbaseRegular]
    exact isOpen_interior
  have hbaseNonempty : P.base.Nonempty := verticalPlate_base_nonempty_local P
  have hbasePeriod : ∀ x : ℝ, x + H.beta ∈ P.base ↔ x ∈ P.base := by
    apply cylinder_periodic_gives_base_periodic
    rw [← hsupport]
    exact H.plate_periodic P hP
  have hPsub : P.centres ⊆ (T.centres : Set Tiling.Plane) := by
    rintro x ⟨q, hq, rfl⟩
    exact q.2
  have hPtilesSupport := tilesOn_regularSupport_of_subset hPsub T.tilesOn
  have hPtiles : TilesOn K P.centres (Complex.re ⁻¹' P.base) := by
    rw [← hsupport]
    exact hPtilesSupport
  have hPclosed : IsClosed P.centres := by
    obtain ⟨delta, hdelta, hsep⟩ := tilesOn_uniformlySeparated K
    apply Metric.isClosed_of_pairwise_le_dist hdelta
    intro x hx y hy hxy
    exact hsep Set.univ (T.centres : Set Tiling.Plane) T.tilesOn
      (hPsub hx) (hPsub hy) hxy
  let TP : TilingSpace K (Complex.re ⁻¹' P.base) :=
    ⟨⟨P.centres, hPclosed⟩, hPtiles⟩
  let Lambda := s11RectangularLattice H.beta H.beta_pos
  have hLambda : Lambda.toAddSubgroup ≤ aePeriodGroup (Complex.re ⁻¹' P.base) := by
    exact s11RectangularLattice_le_aePeriodGroup H.beta_pos hbaseOpen
      hbaseRegular.symm hbasePeriod
  obtain ⟨D0, lambda, gamma, Split, hlambda, hHull, hlocalConv, hpne, htne⟩ :=
    Continuous.exists_nontrivialEarthquakeOrbitLimit_latticeTranslations
      hbaseNonempty hbaseOpen hbaseRegular.symm H.beta_pos hbasePeriod TP hPflc
      Lambda hLambda
  let g : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) :=
    fun n ↦ S11Remaining.Target14.coeFullPlaneTranslation (lambda n)
  let A : ℕ → Set Tiling.Plane := fun n ↦
    ((TilingSpace.translateSequence g T n).centres : Set Tiling.Plane)
  have hATiles : ∀ n, TilesOn K (A n) Set.univ := by
    intro n
    exact (TilingSpace.translateSequence g T n).tilesOn
  obtain ⟨phi, L, hphi, hLTiles, hLclosed, hAmbient, _⟩ :=
    Continuous.exists_tilesOn_locallyFellSubsequence A hATiles
  let U : TilingSpace K Set.univ := ⟨⟨L, hLclosed⟩, hLTiles⟩
  let gsub : ℕ → aePeriodGroup (Set.univ : Set Tiling.Plane) := fun n ↦ g (phi n)
  have hAligned : ∀ n, ∃ m : ℤ,
      (gsub n : Tiling.Plane).re = (m : ℝ) * H.beta := by
    intro n
    exact s11RectangularLattice_re H.beta_pos (hlambda (phi n))
  have hAmbient' : LocallyFellConverges
      (TilingSpace.centresSequence (TilingSpace.translateSequence gsub T))
      (U.centres : Set Tiling.Plane) := by
    change LocallyFellConverges
      (fun n ↦ ((TilingSpace.translateSequence g T (phi n)).centres : Set Tiling.Plane)) L
    exact hAmbient
  obtain ⟨D⟩ := exists_alignedEarthquakeLimitData T U hminimal hFHC H.beta_pos
    H.column_periodic H.plate_periodic gsub hAligned hAmbient'
  let Pidx : ↑(Continuous.nonColumnVerticalPlates K
      (T.centres : Set Tiling.Plane)) := ⟨P, hP⟩
  let psi : ℕ → ℕ := fun n ↦ phi (D.subsequence n)
  have hpsi : StrictMono psi := hphi.comp D.subsequence_strictMono
  have hlocalConv' : LocallyFellConverges
      (fun n ↦ (lambda n : Tiling.Plane) +ᵥ P.centres)
      ((TilingSpace.translate gamma D0.limit).centres : Set Tiling.Plane) := by
    rw [S11Remaining.Target14.localized_translate_centres_eq_vadd
      (U := TP) lambda] at hlocalConv
    exact hlocalConv
  have hlocalSub : LocallyFellConverges
      (fun n ↦ (lambda (psi n) : Tiling.Plane) +ᵥ P.centres)
      ((TilingSpace.translate gamma D0.limit).centres : Set Tiling.Plane) := by
    exact locallyFellConverges_comp_strictMono_s11
      (fun n ↦ (lambda n : Tiling.Plane) +ᵥ P.centres)
      ((TilingSpace.translate gamma D0.limit).centres : Set Tiling.Plane)
      psi hpsi hlocalConv'
  have hcolour : LocallyFellConverges
      (fun n ↦ (lambda (psi n) : Tiling.Plane) +ᵥ P.centres)
      (D.nonColumnLimit Pidx) := by
    simpa [Pidx, gsub, g, psi,
      S11Remaining.Target14.coeFullPlaneTranslation] using D.nonColumn_converges Pidx
  have hlimitEq : (D.nonColumnLimit Pidx) =
      ((TilingSpace.translate gamma D0.limit).centres : Set Tiling.Plane) :=
    S11Remaining.Target14.locallyFellConverges_eq_of_same_sequence hcolour hlocalSub
  let Q : Continuous.VerticalPlate K (U.centres : Set Tiling.Plane) :=
    (D.plateEquiv Pidx).1
  have hcentres : ((TilingSpace.translate gamma D0.limit).centres : Set Tiling.Plane) =
      Q.centres := by
    rw [← hlimitEq, D.nonColumnLimit_eq]
  have horientation : Split.orientation = Axis.vertical := by
    cases hAxis : Split.orientation with
    | vertical => rfl
    | horizontal =>
        exfalso
        exact hbaseProper (Split.horizontal_requires_plane hAxis)
  exact Continuous.persistentTransientSplit_impossible_inside_verticalPlate
    Q Split hcentres horientation hpne htne

end Tiling.AxisParallel.Structure

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Topology

private theorem verticalComponentGeometry_columnPart_eq
    {K : Region} {T : TilingSpace K Set.univ}
    (I : NonColumnPlateIndexing T)
    (G : VerticalComponentGeometry T I) :
    G.columnPart = Continuous.verticalColumnCentres K
      (T.centres : Set Tiling.Plane) := by
  apply Set.Subset.antisymm
  · rw [G.columnPart_eq, Continuous.verticalColumnCentres_eq]
    intro x hx
    obtain ⟨P, hP⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨⟨P.1, G.columnPlates_areColumns P.1 P.2⟩, ?_⟩
    exact hP
  · intro x hx
    rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion] at hx
    obtain ⟨P, hP⟩ := hx
    have hxT : x ∈ (T.centres : Set Tiling.Plane) := by
      obtain ⟨p, hp, rfl⟩ := hP
      exact p.2
    rw [← G.centres_partition] at hxT
    rcases hxT with hxColumn | hxPiece
    · exact hxColumn
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hxPiece
      rw [G.piece_eq j] at hj
      have hneq : P.1 ≠ I.plate j := by
        intro heq
        have hcol : Continuous.IsVerticalColumn (I.plate j) := by
          rw [← heq]
          exact P.2
        exact I.plate_nonColumn j hcol
      exact False.elim (Set.disjoint_left.mp
        ((Continuous.verticalPlateCentres_pairwiseDisjoint K
          (T.centres : Set Tiling.Plane)) (Set.mem_univ _)
          (Set.mem_univ _) hneq) hP hj)

private theorem nonFLC_branch_given
    {K : Region} (T : TilingSpace K Set.univ)
    (D : OrientedNonFLCSelection K T)
    (I : NonColumnPlateIndexing D.selectedTiling)
    (G : VerticalComponentGeometry D.selectedTiling I)
    (H : ComponentPeriodData D.selectedTiling)
    (hPlateFLC : ∀ P : Continuous.VerticalPlate D.selectedRegion
        (D.selectedTiling.centres : Set Tiling.Plane),
        ¬ Continuous.IsVerticalColumn P → HasFLC P.centres) :
    Nonempty (MinimalTilingStructureData K T) := by
  classical
  have hColumnPart : G.columnPart = Continuous.verticalColumnCentres
      D.selectedRegion (D.selectedTiling.centres : Set Tiling.Plane) :=
    verticalComponentGeometry_columnPart_eq I G
  have hcolumnPeriod : Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport D.selectedRegion G.columnPart)
      ((H.beta : ℝ) : ℂ) := by
    rw [hColumnPart]
    exact H.column_periodic
  have hpiecePeriod : ∀ j,
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport D.selectedRegion (G.piece j))
        ((H.beta : ℝ) : ℂ) := by
    intro j
    rw [G.piece_eq j]
    simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
      H.plate_periodic (I.plate j) (I.plate_nonColumn j)
  have hcolumnBasePeriod : Tiling.RationalPolygonal.SetPeriodicBy
      (Complex.re ⁻¹' G.columnBase) ((H.beta : ℝ) : ℂ) := by
    rw [← G.columnSupport_eq, hColumnPart]
    exact H.column_periodic
  have hbasePeriod : ∀ j, Tiling.RationalPolygonal.SetPeriodicBy
      (Complex.re ⁻¹' (G.base j)) ((H.beta : ℝ) : ℂ) := by
    intro j
    rw [← G.pieceSupport_eq j]
    rw [G.piece_eq j]
    simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using
      H.plate_periodic (I.plate j) (I.plate_nonColumn j)
  have hTnonempty : (D.selectedTiling.centres : Set Tiling.Plane).Nonempty := by
    obtain ⟨x, hx⟩ := D.selectedTiling.tilesOn.2.2.exists
    obtain ⟨s, hs⟩ := hx.mp (Set.mem_univ x)
    exact ⟨s.1, s.2⟩
  have hSomePart : G.columnPart.Nonempty ∨ Nonempty (Fin I.numberOfPieces) := by
    by_cases hN : Nonempty (Fin I.numberOfPieces)
    · exact Or.inr hN
    · left
      obtain ⟨x, hx⟩ := hTnonempty
      rw [← G.centres_partition] at hx
      rcases hx with hxColumn | hxPieces
      · exact ⟨x, hxColumn⟩
      · obtain ⟨j, _⟩ := Set.mem_iUnion.mp hxPieces
        exact False.elim (hN ⟨j⟩)
  have hColumnBaseProper : ∀ (_ : Nonempty (Fin I.numberOfPieces)),
      G.columnBase ≠ Set.univ := by
    intro hN hEq
    obtain ⟨j⟩ := hN
    obtain ⟨x, hx⟩ := G.base_nonempty j
    have hxc : x ∈ G.columnBase := by rw [hEq]; exact Set.mem_univ _
    exact Set.disjoint_left.mp (G.columnBase_disjoint_base j) hxc hx
  have hBaseProper : ∀ j,
      (G.columnPart.Nonempty ∨ 2 ≤ I.numberOfPieces) →
        G.base j ≠ Set.univ := by
    intro j hCase hEq
    rcases hCase with hColumn | hTwo
    · obtain ⟨x, hx⟩ := (G.columnBase_nonempty_iff.mpr hColumn)
      have hxj : x ∈ G.base j := by rw [hEq]; exact Set.mem_univ _
      exact Set.disjoint_left.mp (G.columnBase_disjoint_base j) hx hxj
    · have hOne : 1 < I.numberOfPieces := lt_of_lt_of_le (by norm_num) hTwo
      let U : Finset (Fin I.numberOfPieces) := Finset.univ
      obtain ⟨k, _hk, hkj⟩ := Finset.exists_mem_ne
        (s := U) (by simpa [U] using hOne) j
      obtain ⟨x, hx⟩ := G.base_nonempty k
      have hxj : x ∈ G.base j := by rw [hEq]; exact Set.mem_univ _
      exact Set.disjoint_left.mp
        (G.bases_pairwiseDisjoint (Set.mem_univ _) (Set.mem_univ _) hkj)
        hx hxj
  refine ⟨{
    orientation := D.orientation
    selectedRegion := D.selectedRegion
    selectedTiling := D.selectedTiling
    orientation_spec := D.orientation_spec
    selected_minimal := D.selected_minimal
    numberOfPieces := I.numberOfPieces
    columnPart := G.columnPart
    columnPlates := G.columnPlates
    columnPlates_areColumns := G.columnPlates_areColumns
    columnPlates_areComplete := G.columnPlates_areComplete
    columnPart_eq := G.columnPart_eq
    piece := G.piece
    piece_nonempty := G.piece_nonempty
    pieces_pairwiseDisjoint := G.pieces_pairwiseDisjoint
    column_disjoint_piece := G.column_disjoint_piece
    centres_partition := G.centres_partition
    piece_hasFLC := by
      intro j
      rw [G.piece_eq j]
      exact hPlateFLC (I.plate j) (I.plate_nonColumn j)
    finiteComplexity_normalForm := by
      intro hFLC
      exact False.elim (D.selected_nonFLC hFLC)
    finiteHorizontalComplexity_of_nonFLC := by
      intro _
      exact D.finiteHorizontal
    columnBase := G.columnBase
    base := G.base
    columnBase_open := G.columnBase_open
    columnBase_regular := G.columnBase_regular
    columnBase_nonempty_iff := G.columnBase_nonempty_iff
    base_open := G.base_open
    base_regular := G.base_regular
    base_nonempty := G.base_nonempty
    columnSupport_eq := G.columnSupport_eq
    pieceSupport_eq := G.pieceSupport_eq
    column_tiles := G.column_tiles
    piece_tiles := G.piece_tiles
    support_pairwiseDisjoint := G.support_pairwiseDisjoint
    columnSupport_disjoint_piece := G.columnSupport_disjoint_piece
    supports_cover := G.supports_cover
    bases_pairwiseDisjoint := G.bases_pairwiseDisjoint
    columnBase_disjoint_base := G.columnBase_disjoint_base
    bases_cover := G.bases_cover
    horizontalPeriod := H.beta
    horizontalPeriod_pos := H.beta_pos
    columnSupport_periodic := hcolumnPeriod
    pieceSupport_periodic := hpiecePeriod
    columnBase_periodic := fun x ↦
      cylinder_periodic_gives_base_periodic hcolumnBasePeriod x
    base_periodic := fun j x ↦
      cylinder_periodic_gives_base_periodic (hbasePeriod j) x
    columnSupport_latticePeriodic := by
      rw [G.columnSupport_eq]
      exact cylinder_twoPeriods_give_latticePeriodic H.beta_pos hcolumnBasePeriod
    pieceSupport_latticePeriodic := by
      intro j
      rw [G.pieceSupport_eq j]
      exact cylinder_twoPeriods_give_latticePeriodic H.beta_pos (hbasePeriod j)
    somePart_nonempty := hSomePart
    columnBase_proper_of_piece := hColumnBaseProper
    base_proper_of_multiple := hBaseProper
    nonFLC_nontrivial := by
      intro _
      exact D.nontrivialVertical
    nonFLC_components := by
      intro _
      refine ⟨hColumnPart, I.equiv, ?_⟩
      intro j
      exact (G.piece_eq j).trans (congrArg (fun P : Continuous.VerticalPlate
        D.selectedRegion (D.selectedTiling.centres : Set Tiling.Plane) ↦ P.centres)
        (I.plate_eq j)) }⟩

/-- Choose the source orientation with finite horizontal complexity using the S08 hull limit. -/
private theorem exists_orientedNonFLCSelection :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      ¬ HasFLC (T.centres : Set Tiling.Plane) →
      Nonempty (OrientedNonFLCSelection K T) := by
  intro K T hminimal hnonFLC
  obtain ⟨D⟩ := exists_finiteHorizontalComplexityTrichotomy T hnonFLC
  cases hAxis : D.orientation with
  | vertical =>
      have hfinite : Continuous.HasFiniteHorizontalComplexity
          (T.centres : Set Tiling.Plane) :=
        finiteHorizontalComplexity_backToMinimalSource T D.limit hminimal
          D.limit_mem_hull (D.finiteHorizontal_original hAxis)
      obtain ⟨P⟩ := exists_componentPeriodData T hfinite
      have hnontrivial := nontrivialVertical_backToMinimalSource T D.limit
        hminimal D.limit_mem_hull hfinite (D.nontrivialVertical_original hAxis)
        P.beta_pos P.column_periodic P.plate_periodic
      exact ⟨{
        orientation := Axis.vertical
        selectedRegion := K
        selectedTiling := T
        orientation_spec := Or.inl ⟨rfl, rfl, rfl⟩
        selected_minimal := hminimal
        selected_nonFLC := hnonFLC
        finiteHorizontal := hfinite
        nontrivialVertical := hnontrivial }⟩
  | horizontal =>
      obtain ⟨Tσ, hTσ⟩ := exists_coordinateSwapTiling T
      obtain ⟨Uσ, hUσ⟩ := exists_coordinateSwapTiling D.limit
      obtain ⟨hHullσ, hMinimalσ⟩ := coordinateSwap_hullFacts T D.limit
        Tσ Uσ hTσ hUσ D.limit_mem_hull
      have hMinimalσ' : IsTopologicallyMinimal (orbitHull Tσ) := hMinimalσ hminimal
      have hfiniteUσ : Continuous.HasFiniteHorizontalComplexity
          (Uσ.centres : Set Tiling.Plane) := by
        rw [hUσ]
        exact D.finiteHorizontal_swapped hAxis
      have hnontrivialUσ : ¬ ∃ P : Continuous.VerticalPlate K.coordinateSwap
          (Uσ.centres : Set Tiling.Plane),
            ¬ Continuous.IsVerticalColumn P ∧
              P.centres = (Uσ.centres : Set Tiling.Plane) := by
        rw [hUσ]
        exact D.nontrivialVertical_swapped hAxis
      have hfiniteσ : Continuous.HasFiniteHorizontalComplexity
          (Tσ.centres : Set Tiling.Plane) :=
        finiteHorizontalComplexity_backToMinimalSource Tσ Uσ hMinimalσ'
          hHullσ hfiniteUσ
      obtain ⟨P⟩ := exists_componentPeriodData Tσ hfiniteσ
      have hnontrivialσ := nontrivialVertical_backToMinimalSource Tσ Uσ
        hMinimalσ' hHullσ hfiniteσ hnontrivialUσ P.beta_pos
        P.column_periodic P.plate_periodic
      have hnonFLCσ : ¬ HasFLC (Tσ.centres : Set Tiling.Plane) := by
        intro hFLCσ
        apply hnonFLC
        apply (hasFLC_coordinateSwap_iff (T.centres : Set Tiling.Plane)).mp
        simpa [hTσ] using hFLCσ
      exact ⟨{
        orientation := Axis.horizontal
        selectedRegion := K.coordinateSwap
        selectedTiling := Tσ
        orientation_spec := Or.inr ⟨rfl, rfl, hTσ⟩
        selected_minimal := hMinimalσ'
        selected_nonFLC := hnonFLCσ
        finiteHorizontal := hfiniteσ
        nontrivialVertical := hnontrivialσ }⟩


/-- Assemble the finite slab decomposition in the non-FLC branch. -/
private theorem nonFLC_branch :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      ¬ HasFLC (T.centres : Set Tiling.Plane) →
      Nonempty (MinimalTilingStructureData K T) := by
  intro K T hMinimal hNonFLC
  obtain ⟨D⟩ := exists_orientedNonFLCSelection T hMinimal hNonFLC
  obtain ⟨I⟩ := exists_nonColumnPlateIndexing D.selectedTiling D.finiteHorizontal
  obtain ⟨G⟩ := exists_verticalComponentGeometry D.selectedTiling I
  obtain ⟨H⟩ := exists_componentPeriodData D.selectedTiling D.finiteHorizontal
  exact nonFLC_branch_given T D I G H
    (nonColumnPlate_hasFLC D.selectedTiling
      D.selected_minimal D.finiteHorizontal D.nontrivialVertical)

/-- Every topologically minimal tiling admits the oriented finite periodic slab decomposition. -/
theorem exists_minimalTilingStructureData :
    ∀ {K : Region} (T : TilingSpace K Set.univ),
      IsTopologicallyMinimal (orbitHull T) →
      Nonempty (MinimalTilingStructureData K T) := by
  intro K T hMinimal
  by_cases hFLC : HasFLC (T.centres : Set Tiling.Plane)
  · exact finiteComplexity_branch T hMinimal hFLC
  · exact nonFLC_branch T hMinimal hFLC

end Tiling.AxisParallel.Structure
