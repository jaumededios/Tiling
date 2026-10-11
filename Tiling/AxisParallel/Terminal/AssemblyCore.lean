import Tiling.AxisParallel.Core
import Tiling.AxisParallel.OneDimensional.Core

/-!
# Common-period assembly data

This definition-only module contains the explicit triangular period subgroup and the records used by
the terminal common-period assembly theorem.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

/-- The vertical period vector of length `alpha`. -/
def verticalPeriodVector (alpha : ℝ) : Tiling.Plane :=
  (alpha : ℂ) * Complex.I

/-- A vector with horizontal displacement `beta` and vertical shear. -/
def skewPeriodVector (beta shear : ℝ) : Tiling.Plane :=
  (beta : ℂ) + (shear : ℂ) * Complex.I

/-- The integer span of a vertical vector and a skew horizontal vector. -/
def triangularPeriodSubgroup (alpha beta shear : ℝ) : AddSubgroup Tiling.Plane where
  carrier := {v | ∃ m n : ℤ,
    v = m • verticalPeriodVector alpha + n • skewPeriodVector beta shear}
  zero_mem' := ⟨0, 0, by simp⟩
  add_mem' := by
    rintro x y ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    refine ⟨m + m', n + n', ?_⟩
    simp only [add_smul]
    abel
  neg_mem' := by
    rintro x ⟨m, n, rfl⟩
    refine ⟨-m, -n, ?_⟩
    simp only [neg_smul, neg_add_rev]
    ac_rfl

/-- A planar lattice written in the normal form adapted to a vertical slab. -/
structure VerticalSlabLatticeForm (Lambda : Tiling.AxisParallel.PlanarLattice) where
  verticalPeriod : ℝ
  horizontalPeriod : ℝ
  shear : ℝ
  verticalPeriod_pos : 0 < verticalPeriod
  horizontalPeriod_pos : 0 < horizontalPeriod
  subgroup_eq :
    Lambda.toAddSubgroup =
      triangularPeriodSubgroup verticalPeriod horizontalPeriod shear

/-- The two periodic pieces and rational masses used to synchronize their vertical periods. -/
structure MixedRationalizationDatum
    (alpha alphaColumn sourceCommonPeriod : ℝ) where
  deformedRegion : Tiling.AxisParallel.Region
  nonColumnCentres : Set Tiling.Plane
  columnCentres : Set Tiling.Plane
  nonColumnBase : Set ℝ
  columnBase : Set ℝ
  nonColumnBase_measurable : MeasurableSet nonColumnBase
  columnBase_measurable : MeasurableSet columnBase
  rationalHorizontalPeriod : ℝ
  nonColumnShear : ℝ
  columnShear : ℝ
  sourceCommonPeriod_pos : 0 < sourceCommonPeriod
  rationalHorizontalPeriod_pos : 0 < rationalHorizontalPeriod
  nonColumnTiles : Tiling.AxisParallel.TilesOn deformedRegion nonColumnCentres
    {z : Tiling.Plane | z.re ∈ nonColumnBase}
  columnTiles : Tiling.AxisParallel.TilesOn deformedRegion columnCentres
    {z : Tiling.Plane | z.re ∈ columnBase}
  nonColumnVerticalPeriod :
    verticalPeriodVector alpha ∈
      Tiling.AxisParallel.periodGroup nonColumnCentres
  nonColumnHorizontalPeriod :
    skewPeriodVector rationalHorizontalPeriod nonColumnShear ∈
      Tiling.AxisParallel.periodGroup nonColumnCentres
  columnVerticalPeriod :
    verticalPeriodVector alphaColumn ∈
      Tiling.AxisParallel.periodGroup columnCentres
  columnHorizontalPeriod :
    skewPeriodVector rationalHorizontalPeriod columnShear ∈
      Tiling.AxisParallel.periodGroup columnCentres
  nonColumnMass : ℚ
  columnMass : ℚ
  nonColumnMass_pos : 0 < nonColumnMass
  columnMass_pos : 0 < columnMass
  nonColumnMass_eq :
    (MeasureTheory.volume
      (nonColumnBase ∩ Set.Ico 0 rationalHorizontalPeriod)).toReal =
        (nonColumnMass : ℝ)
  columnMass_eq :
    (MeasureTheory.volume
      (columnBase ∩ Set.Ico 0 rationalHorizontalPeriod)).toReal =
        (columnMass : ℝ)

/-- A column piece together with the family obtained by freely choosing its shear. -/
structure ColumnReplacementFamily (K : Tiling.AxisParallel.Region) where
  base : Set ℝ
  base_measurable : MeasurableSet base
  sourceCentres : Set Tiling.Plane
  source_nonempty : sourceCentres.Nonempty
  source_tiles : Tiling.AxisParallel.TilesOn K sourceCentres
    {z : Tiling.Plane | z.re ∈ base}
  verticalPeriod : ℝ
  axisPeriod : ℝ
  verticalPeriod_pos : 0 < verticalPeriod
  axisPeriod_pos : 0 < axisPeriod
  replacement : ℝ → Set Tiling.Plane
  replacement_tiles : ∀ shear : ℝ,
    Tiling.AxisParallel.TilesOn K (replacement shear)
      {z : Tiling.Plane | z.re ∈ base}
  replacement_verticalPeriod : ∀ shear : ℝ,
    verticalPeriodVector verticalPeriod ∈
      Tiling.AxisParallel.periodGroup (replacement shear)
  replacement_axisPeriod : ∀ shear : ℝ,
    skewPeriodVector axisPeriod shear ∈
      Tiling.AxisParallel.periodGroup (replacement shear)

/-- All finite pieces and compatibility data needed for the four assembly branches. -/
structure CommonPeriodAssemblyData
    (K : Tiling.AxisParallel.Region) (Y : Set ℝ) where
  target_measurable : MeasurableSet Y
  numberOfNonColumnPieces : ℕ
  nonColumnCentres : Fin numberOfNonColumnPieces → Set Tiling.Plane
  nonColumnBase : Fin numberOfNonColumnPieces → Set ℝ
  nonColumnBase_measurable : ∀ i, MeasurableSet (nonColumnBase i)
  nonColumn_nonempty : ∀ i, (nonColumnCentres i).Nonempty
  nonColumn_tiles : ∀ i,
    Tiling.AxisParallel.TilesOn K (nonColumnCentres i)
      {z : Tiling.Plane | z.re ∈ nonColumnBase i}
  nonColumnLattice : Fin numberOfNonColumnPieces →
    Tiling.AxisParallel.PlanarLattice
  nonColumn_periodic : ∀ i,
    (nonColumnLattice i).toAddSubgroup ≤
      Tiling.AxisParallel.periodGroup (nonColumnCentres i)
  commonNonColumnLattice : Option Tiling.AxisParallel.PlanarLattice
  commonNonColumnLattice_isSome_iff :
    commonNonColumnLattice ≠ none ↔ 0 < numberOfNonColumnPieces
  commonNonColumnLattice_le : ∀ Lambda,
    commonNonColumnLattice = some Lambda → ∀ i,
      Lambda.toAddSubgroup ≤ (nonColumnLattice i).toAddSubgroup
  column : Option (ColumnReplacementFamily K)
  bases_pairwise_aeDisjoint :
    (∀ i j, i ≠ j → MeasureTheory.AEDisjoint MeasureTheory.volume
      (nonColumnBase i) (nonColumnBase j)) ∧
    ∀ C, column = some C → ∀ i,
      MeasureTheory.AEDisjoint MeasureTheory.volume (nonColumnBase i) C.base
  bases_cover :
    Set.union
      (⋃ i : Fin numberOfNonColumnPieces, nonColumnBase i)
      {x : ℝ | ∃ C, column = some C ∧ x ∈ C.base} =ᵐ[MeasureTheory.volume] Y
  mixed_nonColumnBase_positive :
    0 < numberOfNonColumnPieces → column ≠ none →
      ∃ I : Set ℝ, Bornology.IsBounded I ∧
        0 < (MeasureTheory.volume
          ((⋃ i : Fin numberOfNonColumnPieces, nonColumnBase i) ∩ I)).toReal
  mixed_columnBase_positive :
    0 < numberOfNonColumnPieces → ∀ C, column = some C →
      ∃ I : Set ℝ, Bornology.IsBounded I ∧
        0 < (MeasureTheory.volume (C.base ∩ I)).toReal
  mixed_rationalization :
    ∀ Lambda C,
      commonNonColumnLattice = some Lambda → column = some C →
      ∀ F : VerticalSlabLatticeForm Lambda,
      ∀ B : ℝ, 0 < B →
      (∃ n : ℕ, 0 < n ∧ B = n * F.horizontalPeriod) →
      (∃ n : ℕ, 0 < n ∧ B = n * C.axisPeriod) →
      Nonempty (MixedRationalizationDatum F.verticalPeriod C.verticalPeriod B)

/-- A tiling of the target vertical set together with literal rank-two centre periods. -/
structure PeriodicAssembly
    (K : Tiling.AxisParallel.Region) (Y : Set ℝ) where
  centres : Set Tiling.Plane
  tiles : Tiling.AxisParallel.TilesOn K centres
    {z : Tiling.Plane | z.re ∈ Y}
  lattice : Tiling.AxisParallel.PlanarLattice
  lattice_periods : lattice.toAddSubgroup ≤
    Tiling.AxisParallel.periodGroup centres

end Tiling.AxisParallel.Terminal
