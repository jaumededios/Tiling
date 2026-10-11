import Tiling.AxisParallel.Terminal.AssemblyCore
import Tiling.AxisParallel.Terminal.PeriodicReplacementCore

/-!
# Terminal periodic normal forms

This definition-only module contains the two certificate shapes produced by the terminal
classification: a whole-plane lattice replacement or a finite family of oriented periodic slabs.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

/-- A finite periodic-slab normal form, stated both in selected and original coordinates. -/
structure SlabCertificate (K : Tiling.AxisParallel.Region) where
  orientation : Bool
  selectedRegion : Tiling.AxisParallel.Region
  selectedRegion_eq : selectedRegion =
    if orientation then K.coordinateSwap else K
  numberOfPieces : ℕ
  atLeastTwoPieces : 2 ≤ numberOfPieces
  selectedCentres : Set Tiling.Plane
  selectedPiece : Fin numberOfPieces → Set Tiling.Plane
  selectedPiece_nonempty : ∀ j, (selectedPiece j).Nonempty
  selectedPiece_pairwiseDisjoint : Set.PairwiseDisjoint Set.univ selectedPiece
  selectedPieces_union : (⋃ j, selectedPiece j) = selectedCentres
  selected_tiles : Tiling.AxisParallel.TilesOn selectedRegion selectedCentres Set.univ
  base : Fin numberOfPieces → Set ℝ
  base_nonempty : ∀ j, (base j).Nonempty
  base_proper : ∀ j, base j ≠ Set.univ
  base_open : ∀ j, IsOpen (base j)
  base_regular : ∀ j, interior (closure (base j)) = base j
  base_periodic : ∀ j, ∃ b : ℝ, 0 < b ∧
    ∀ x : ℝ, x + b ∈ base j ↔ x ∈ base j
  piece_tiles : ∀ j,
    Tiling.AxisParallel.TilesOn selectedRegion (selectedPiece j)
      {z : Tiling.Plane | z.re ∈ base j}
  bases_pairwise_aeDisjoint : Set.Pairwise Set.univ
    (fun i j ↦ MeasureTheory.AEDisjoint MeasureTheory.volume (base i) (base j))
  bases_cover : (⋃ j, base j) =ᵐ[MeasureTheory.volume] Set.univ
  verticalPeriod : Fin numberOfPieces → ℝ
  horizontalPeriod : Fin numberOfPieces → ℝ
  shear : Fin numberOfPieces → ℝ
  verticalPeriod_pos : ∀ j, 0 < verticalPeriod j
  horizontalPeriod_pos : ∀ j, 0 < horizontalPeriod j
  individual_verticalPeriod : ∀ j,
    verticalPeriodVector (verticalPeriod j) ∈
      Tiling.AxisParallel.periodGroup (selectedPiece j)
  individual_skewPeriod : ∀ j,
    skewPeriodVector (horizontalPeriod j) (shear j) ∈
      Tiling.AxisParallel.periodGroup (selectedPiece j)
  vertical_commensurable : ∀ i j,
    ∃ q : ℚ, verticalPeriod i = (q : ℝ) * verticalPeriod j
  horizontal_commensurable : ∀ i j,
    ∃ q : ℚ, horizontalPeriod i = (q : ℝ) * horizontalPeriod j
  commonVerticalPeriod : ℝ
  commonHorizontalPeriod : ℝ
  commonVerticalPeriod_pos : 0 < commonVerticalPeriod
  commonHorizontalPeriod_pos : 0 < commonHorizontalPeriod
  verticalMultiplier : Fin numberOfPieces → ℕ
  horizontalMultiplier : Fin numberOfPieces → ℕ
  verticalMultiplier_pos : ∀ j, 0 < verticalMultiplier j
  horizontalMultiplier_pos : ∀ j, 0 < horizontalMultiplier j
  commonVerticalPeriod_eq : ∀ j,
    commonVerticalPeriod = verticalMultiplier j * verticalPeriod j
  commonHorizontalPeriod_eq : ∀ j,
    commonHorizontalPeriod = horizontalMultiplier j * horizontalPeriod j
  normalizedShear : Fin numberOfPieces → ℝ
  normalizedShear_nonnegative : ∀ j, 0 ≤ normalizedShear j
  normalizedShear_lt : ∀ j, normalizedShear j < commonVerticalPeriod
  common_verticalPeriod : ∀ j,
    verticalPeriodVector commonVerticalPeriod ∈
      Tiling.AxisParallel.periodGroup (selectedPiece j)
  common_skewPeriod : ∀ j,
    skewPeriodVector commonHorizontalPeriod (normalizedShear j) ∈
      Tiling.AxisParallel.periodGroup (selectedPiece j)
  selected_commonPeriod :
    verticalPeriodVector commonVerticalPeriod ∈
      Tiling.AxisParallel.periodGroup selectedCentres
  originalCentres : Set Tiling.Plane
  originalPiece : Fin numberOfPieces → Set Tiling.Plane
  originalCentres_eq : originalCentres =
    if orientation then
      Tiling.AxisParallel.coordinateSwap '' selectedCentres
    else selectedCentres
  originalPiece_eq : ∀ j,
    originalPiece j =
      if orientation then
        Tiling.AxisParallel.coordinateSwap '' selectedPiece j
      else selectedPiece j
  originalPieces_union : (⋃ j, originalPiece j) = originalCentres
  original_tiles : Tiling.AxisParallel.TilesOn K originalCentres Set.univ
  originalPiece_tiles : ∀ j,
    Tiling.AxisParallel.TilesOn K (originalPiece j)
      (if orientation then
        {z : Tiling.Plane | z.im ∈ base j}
      else {z : Tiling.Plane | z.re ∈ base j})
  original_verticalPeriod : ∀ j,
    (if orientation then
      Tiling.AxisParallel.coordinateSwap
        (verticalPeriodVector commonVerticalPeriod)
    else verticalPeriodVector commonVerticalPeriod) ∈
      Tiling.AxisParallel.periodGroup (originalPiece j)
  original_skewPeriod : ∀ j,
    (if orientation then
      Tiling.AxisParallel.coordinateSwap
        (skewPeriodVector commonHorizontalPeriod (normalizedShear j))
    else skewPeriodVector commonHorizontalPeriod (normalizedShear j)) ∈
      Tiling.AxisParallel.periodGroup (originalPiece j)
  original_commonPeriod :
    (if orientation then
      Tiling.AxisParallel.coordinateSwap
        (verticalPeriodVector commonVerticalPeriod)
    else verticalPeriodVector commonVerticalPeriod) ∈
      Tiling.AxisParallel.periodGroup originalCentres

/-- The two terminal alternatives for a periodic tiling certificate. -/
inductive PeriodicTilingNormalForm (K : Tiling.AxisParallel.Region)
  | wholePlaneLattice : PeriodicReplacement K Set.univ → PeriodicTilingNormalForm K
  | orientedSlabs : SlabCertificate K → PeriodicTilingNormalForm K

end Tiling.AxisParallel.Terminal
