import Tiling.RationalSlopes.ParametrizationLifting
import Tiling.Topology.TilingHull

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.RationalSlopes

open Tiling.RationalPolygonal (PolygonalRegion WeaklyPeriodic)
open Tiling.Polygonal

theorem minimal_flc_goodParametrization
    {K : PolygonalRegion} {T E : Set Plane} (hK : HasRationalSlopes K)
    (hFLC : HasFLC T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E)
    (hminimal : Tiling.Polygonal.Topology.IsMinimalTiling K T E) :
    Nonempty (GoodParametrization K T) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · exact empty_goodParametrization K
  have hdim {δ : Submodule ℝ Plane} (hb : HasBoundaryDirection K δ) :
      Module.finrank ℝ δ = 1 := by
    rcases hb with ⟨a, b, hab, _, rfl⟩
    exact finrank_span_singleton (sub_ne_zero.mpr hab.symm)
  by_cases hcol : ∃ δ : Submodule ℝ Plane,
      HasBoundaryDirection K δ ∧ IsUnionOfColumns K δ T
  · obtain ⟨δ, hb, hcolumns⟩ := hcol
    exact unionColumns_goodParametrization (hdim hb) htile hEopen hEregular hEper
      hcolumns
  have hδdense (δ : Submodule ℝ Plane) :
      ∃ R : ℝ, 0 < R ∧ (HasBoundaryDirection K δ → ∀ x : Plane,
        ∃ v ∈ fibreProperVertices K T δ, dist x v < R) := by
    by_cases hb : HasBoundaryDirection K δ
    · obtain ⟨R, hR, hdense⟩ := minimal_noncolumn_fibreCorners_relativeDense
        (hdim hb) hTne htile hEopen hEregular hEper hminimal
        (fun hc => hcol ⟨δ, hb, hc⟩)
      exact ⟨R, hR, fun _ => hdense⟩
    · exact ⟨1, zero_lt_one, fun hb' => (hb hb').elim⟩
  choose radius hpositive hdensity using hδdense
  obtain ⟨δ₀, hbound⟩ := Set.exists_upper_bound_image
    {δ : Submodule ℝ Plane | HasBoundaryDirection K δ} radius
    (boundaryDirections_finite K)
  apply flc_goodParametrization_of_fibreCornerDensity hK hTne hFLC htile
    hEopen hEregular hEper
  refine ⟨radius δ₀ + 1, by linarith [hpositive δ₀], ?_⟩
  intro δ hb x
  obtain ⟨v, hv, hdist⟩ := hdensity δ hb x
  refine ⟨v, hv, ?_⟩
  have hle := hbound δ hb
  linarith

theorem minimal_flc_weaklyPeriodic
    {K : PolygonalRegion} {T E : Set Plane} (hK : HasRationalSlopes K)
    (hFLC : HasFLC T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E)
    (hminimal : Tiling.Polygonal.Topology.IsMinimalTiling K T E) :
    WeaklyPeriodic T := by
  obtain ⟨G⟩ := minimal_flc_goodParametrization hK hFLC htile hEopen hEregular
    hEper hminimal
  exact G.weaklyPeriodic

theorem flc_exists_periodic_replacement
    {K : PolygonalRegion} {T E : Set Plane} (hK : HasRationalSlopes K)
    (hFLC : HasFLC T) (htile : TilesOn K T E)
    (hEopen : IsOpen E) (hEregular : interior (closure E) = E)
    (hEper : IsLatticePeriodic E) :
    ∃ S : Set Plane, TilesOn K S E ∧ IsLatticePeriodic S ∧
      periodGroup S ≤ periodGroup E := by
  let source : Tiling.Polygonal.Topology.TilingSpace K E :=
    ⟨⟨T, (packing_centres_locallyFinite htile.2.1).2.2⟩, htile⟩
  obtain ⟨U, hU, hminimal⟩ :=
    Tiling.Polygonal.Topology.exists_minimalTiling_in_hull source
  have hUFLC : HasFLC (U.centres : Set Plane) :=
    Tiling.Polygonal.Topology.hasFLC_of_mem_orbitHull hFLC hU
  have hUminimal : Tiling.Polygonal.Topology.IsMinimalTiling K
      (U.centres : Set Plane) E := ⟨U, rfl, hminimal⟩
  obtain ⟨G⟩ := minimal_flc_goodParametrization hK hUFLC U.tilesOn hEopen
    hEregular hEper hUminimal
  exact ⟨G.replacementCentres, G.periodic_replacement U.tilesOn hEopen hEregular⟩

end Tiling.RationalSlopes
