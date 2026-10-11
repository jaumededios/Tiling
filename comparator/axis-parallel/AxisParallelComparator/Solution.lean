import AxisParallelComparator.Definitions
import Tiling.AxisParallel.SetFormulation.Periodicity
import Tiling.AxisParallel.SetFormulation.Earthquakes
import Tiling.AxisParallel.SetFormulation.BoundaryBridge

set_option autoImplicit false
open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

namespace AxisParallelComparator

theorem IsAxisParallelTile.isRectangleTile {Ω : Set Plane}
    (hΩ : IsAxisParallelTile Ω) :
    Tiling.AxisParallel.SetFormulation.IsRectangleTile Ω := by
  obtain ⟨hne, hbounded, hregular, edges, hedge, hfront⟩ := hΩ
  exact Tiling.AxisParallel.SetFormulation.isRectangleTile_of_axis_parallel_boundary
    Ω hne hbounded hregular edges hedge hfront

theorem flc_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : HasFiniteLocalComplexity T) :
    WeaklyPeriodic T := by
  exact Tiling.AxisParallel.SetFormulation.flc_tiling_weakly_periodic
    Ω (hΩ.isRectangleTile) X hX hXregular β hβ hperiod T hT hFLC

theorem periodic_tiling_of_flc
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X) :
    (∃ T, TilingOn (p₁ ⁻¹' X) Ω T ∧ HasFiniteLocalComplexity T) →
      ∃ S, TilingOn (p₁ ⁻¹' X) Ω S ∧ IsDoublyPeriodic S := by
  exact Tiling.AxisParallel.SetFormulation.periodic_tiling_of_flc
    Ω (hΩ.isRectangleTile) X hX hXregular β hβ hperiod

theorem exists_minimal_tiling_in_hull
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      IsMinimal (p₁ ⁻¹' X) S := by
  exact Tiling.AxisParallel.SetFormulation.exists_minimal_tiling_in_hull
    Ω (hΩ.isRectangleTile) X hX hXregular β hβ hperiod T hT

theorem earthquake_decomposition
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    columnPart Ω v T ∪ ⋃₀ tectonicPlates Ω v T = T ∧
      Disjoint (columnPart Ω v T) (⋃₀ tectonicPlates Ω v T) ∧
      (tectonicPlates Ω v T).Pairwise Disjoint := by
  exact Tiling.AxisParallel.SetFormulation.earthquake_decomposition Ω (hΩ.isRectangleTile) T hT v hv

theorem minimal_tiling_structure
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hminimal : IsMinimal univ T) :
    ∃ v ∈ ({e₁, e₂} : Set Plane),
      ∃ P : Finpartition (T \ columnPart Ω v T),
        IsDoublyPeriodic (coveredRegion Ω (columnPart Ω v T)) ∧
        ∀ S ∈ P.parts,
          HasFiniteLocalComplexity S ∧
          IsDoublyPeriodic (coveredRegion Ω S) ∧ IsInvariantAlong (coveredRegion Ω S) v := by
  exact Tiling.AxisParallel.SetFormulation.minimal_tiling_structure
    Ω (hΩ.isRectangleTile) T hT hminimal

theorem minimal_tiling_weakly_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hminimal : IsMinimal univ T) :
    WeaklyPeriodic T := by
  exact Tiling.AxisParallel.SetFormulation.minimal_tiling_weakly_periodic
    Ω (hΩ.isRectangleTile) T hT hminimal

theorem quasi_periodic_tiling_with_common_period
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω) :
    (∃ T, Tiling Ω T) →
      ∃ S, Tiling Ω S ∧ QuasiPeriodic S ∧ ∃ p, p ≠ 0 ∧ IsPeriod S p := by
  exact Tiling.AxisParallel.SetFormulation.quasi_periodic_tiling_with_common_period
    Ω (hΩ.isRectangleTile)

theorem finitely_many_tectonic_plates
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    (tectonicPlates Ω v T).Finite := by
  exact Tiling.AxisParallel.SetFormulation.finitely_many_tectonic_plates
    Ω (hΩ.isRectangleTile) T hT v hv

theorem earthquake_slabs_periodic
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (hperiod : β₀ +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hcomplexity : HasFiniteLocalComplexity (p₁ '' T)) :
    ∃ β : ℝ, 0 < β ∧
      IsPeriod (coveredRegion Ω (columnPart Ω e₂ T)) (β • e₁) ∧
      ∀ P ∈ tectonicPlates Ω e₂ T, IsPeriod (coveredRegion Ω P) (β • e₁) := by
  exact Tiling.AxisParallel.SetFormulation.earthquake_slabs_periodic
    Ω (hΩ.isRectangleTile) X hX hXregular β₀ hβ₀ hperiod T hT hcomplexity

theorem proper_cylinder_finite_horizontal_complexity
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X) (hproper : X ≠ univ)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    HasFiniteLocalComplexity (p₁ '' T) := by
  exact Tiling.AxisParallel.SetFormulation.proper_cylinder_finite_horizontal_complexity
    Ω (hΩ.isRectangleTile) X hX hXregular hproper β hβ hperiod T hT

theorem non_flc_earthquake_limit
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
        (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit Ω S S₀ S₁ v := by
  exact Tiling.AxisParallel.SetFormulation.non_flc_earthquake_limit
    Ω (hΩ.isRectangleTile) X hX hXregular β hβ hperiod T hT hFLC

theorem non_flc_earthquake_limit_in_lattice
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : ¬ HasFiniteLocalComplexity T)
    (p q : Plane) (hpq : LinearIndependent ℝ ![p, q])
    (hp : IsPeriod (p₁ ⁻¹' X) p) (hq : IsPeriod (p₁ ⁻¹' X) q) :
    ∃ S ∈ orbitHullUnder (span ℤ {p, q} : Set Plane) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
        (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit Ω S S₀ S₁ v := by
  exact Tiling.AxisParallel.SetFormulation.non_flc_earthquake_limit_in_lattice
    Ω (hΩ.isRectangleTile) X hX hXregular β hβ hperiod T hT hFLC p q hpq hp hq

theorem non_flc_finite_horizontal_complexity_limit
    (Ω : Set Plane) (hΩ : IsAxisParallelTile Ω)
    (T : Set Plane) (hT : Tiling Ω T) (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull univ T,
      Tiling Ω S ∧
      ((HasFiniteLocalComplexity (p₁ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₂ S) ∨
       (HasFiniteLocalComplexity (p₂ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₁ S)) := by
  exact Tiling.AxisParallel.SetFormulation.non_flc_finite_horizontal_complexity_limit
    Ω (hΩ.isRectangleTile) T hT hFLC

end AxisParallelComparator
