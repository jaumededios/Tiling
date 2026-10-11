import Tiling.AxisParallel.SetFormulation.RegionBridge
import Tiling.AxisParallel.SetFormulation.Columns
import Tiling.AxisParallel.SetFormulation.FellMinimality
import Tiling.AxisParallel.Terminal.PeriodicCarrierContinuousSlabs
import Tiling.AxisParallel.Continuous.NontrivialEarthquakeLimit
import Tiling.AxisParallel.Structure.FiniteHorizontalComplexityTrichotomy

/-!
# Minimality and earthquake structure for sets of translations

These proofs transport the native tiling-space and contact-component results
through the independent solution vocabulary.
-/

set_option autoImplicit false

open Bornology MeasureTheory Set Submodule TopologicalSpace
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.SetFormulation

private theorem e₁_eq_one : e₁ = (1 : Plane) := by
  apply Complex.ext <;> rfl

private theorem e₂_eq_I : e₂ = Complex.I := by
  apply Complex.ext <;> rfl

private theorem cylinder_regularOpen {X : Set ℝ} (hX : IsRegularOpen X) :
    IsRegularOpen (p₁ ⁻¹' X) := by
  change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
  rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hX]

private def periodicCarrier (X : Set ℝ) (hX : X.Nonempty)
    (hXregular : IsRegularOpen X) (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X) :
    Tiling.AxisParallel.Terminal.PeriodicVerticalCarrier where
  base := X
  base_open := isRegularOpen_isOpen hXregular
  base_regular := hXregular
  base_nonnull := (isRegularOpen_isOpen hXregular).measure_ne_zero volume hX
  period := β
  period_pos := hβ
  base_periodic := hperiod

private theorem native_support_period (K : Tiling.AxisParallel.Region)
    (S : Set Plane) (β : ℝ)
    (hperiod : Tiling.RationalPolygonal.SetPeriodicBy
      (Tiling.AxisParallel.regularSupport K S) (β : Plane)) :
    IsPeriod (coveredRegion K.openCarrier S) (β • e₁) := by
  have hvector : β • e₁ = (β : Plane) := by
    apply Complex.ext <;> simp [e₁]
  rw [Columns.coveredRegion_openCarrier, hvector, isPeriod_iff_membership]
  exact hperiod

theorem exists_minimal_tiling_in_hull
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (_hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (_hβ : 0 < β) (_hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      IsMinimal (p₁ ⁻¹' X) S := by
  let K := regionOfTile Ω hΩ
  have hNative : Tiling.AxisParallel.TilesOn K T (p₁ ⁻¹' X) :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  let U : Tiling.AxisParallel.Topology.TilingSpace K (p₁ ⁻¹' X) :=
    ⟨⟨T, Fell.tilesOn_centres_isClosed hNative⟩, hNative⟩
  obtain ⟨V, hHull, hMinimal⟩ := Fell.exists_minimal_hull_point
    (cylinder_regularOpen hXregular) U
  exact ⟨V.centres, hHull, (tilingOn_iff_native Ω hΩ _ _).mpr V.tilesOn, hMinimal⟩

theorem earthquake_decomposition
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (T : Set Plane) (hT : Tiles Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    columnPart Ω v T ∪ ⋃₀ tectonicPlates Ω v T = T ∧
      Disjoint (columnPart Ω v T) (⋃₀ tectonicPlates Ω v T) ∧
      (tectonicPlates Ω v T).Pairwise Disjoint := by
  have hNative := (tilingOn_iff_native Ω hΩ Set.univ T).mp hT
  rcases Set.mem_insert_iff.mp hv with hv | hv
  · subst v
    simpa only [regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.horizontal_decomposition hNative
  · have hv := Set.mem_singleton_iff.mp hv
    subst v
    simpa only [regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.vertical_decomposition hNative

theorem finitely_many_tectonic_plates
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (T : Set Plane) (hT : Tiles Ω T)
    (v : Plane) (hv : v ∈ ({e₁, e₂} : Set Plane)) :
    (tectonicPlates Ω v T).Finite := by
  have hNative := (tilingOn_iff_native Ω hΩ Set.univ T).mp hT
  rcases Set.mem_insert_iff.mp hv with hv | hv
  · subst v
    simpa only [regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.horizontal_tectonicPlates_finite hNative
  · have hv := Set.mem_singleton_iff.mp hv
    subst v
    simpa only [regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.vertical_tectonicPlates_finite hNative

theorem earthquake_slabs_periodic
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β₀ : ℝ) (hβ₀ : 0 < β₀) (hperiod : β₀ +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hcomplexity : HasFiniteLocalComplexity (p₁ '' T)) :
    ∃ β : ℝ, 0 < β ∧
      IsPeriod (coveredRegion Ω (columnPart Ω e₂ T)) (β • e₁) ∧
      ∀ P ∈ tectonicPlates Ω e₂ T, IsPeriod (coveredRegion Ω P) (β • e₁) := by
  let K := regionOfTile Ω hΩ
  let Y := periodicCarrier X hX hXregular β₀ hβ₀ hperiod
  have hNative : Tiling.AxisParallel.TilesOn K T Y.carrier :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  have hFHC : Tiling.AxisParallel.Continuous.HasFiniteHorizontalComplexity T :=
    hasFiniteLocalComplexity_iff_hasFLC.mp hcomplexity
  obtain ⟨β, hβ, hPlates, hColumns⟩ :=
    Tiling.AxisParallel.Terminal.continuousPeriodicCarrierPlate_periodic Y hNative hFHC
  have hColumnEq : columnPart Ω e₂ T =
      Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
    simpa only [K, regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.columnPart_eq_verticalColumnCentres_relative hNative hXregular
  have hPlateEq : tectonicPlates Ω e₂ T =
      (@Tiling.AxisParallel.Continuous.VerticalPlate.centres K T) ''
        Tiling.AxisParallel.Continuous.nonColumnVerticalPlates K T := by
    simpa only [K, regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      Columns.tectonicPlates_eq_nonColumn_relative hNative hXregular
  refine ⟨β, hβ, ?_, ?_⟩
  · rw [hColumnEq]
    simpa only [K, regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      native_support_period K _ β hColumns
  · intro P hP
    rw [hPlateEq] at hP
    obtain ⟨Q, hQ, rfl⟩ := hP
    simpa only [K, regionOfTile_openCarrier, e₁_eq_one, e₂_eq_I] using
      native_support_period K Q.centres β (hPlates Q hQ)

theorem proper_cylinder_finite_horizontal_complexity
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X) (hproper : X ≠ univ)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T) :
    HasFiniteLocalComplexity (p₁ '' T) := by
  let K := regionOfTile Ω hΩ
  let Y := periodicCarrier X hX hXregular β hβ hperiod
  have hNative : Tiling.AxisParallel.TilesOn K T Y.carrier :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  exact hasFiniteLocalComplexity_iff_hasFLC.mpr
    (Tiling.AxisParallel.Terminal.properCarrier_hasFiniteHorizontalComplexity Y hproper hNative)



private theorem base_period_membership {X : Set ℝ} {β : ℝ}
    (hperiod : β +ᵥ X = X) : ∀ x : ℝ, x + β ∈ X ↔ x ∈ X := by
  intro x
  have hmem := congrArg (fun S : Set ℝ => β + x ∈ S) hperiod
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, add_comm] using hmem.symm

private theorem split_adapter {K : Tiling.AxisParallel.Region} {X : Set ℝ}
    {U : ℕ → Tiling.AxisParallel.Topology.TilingSpace K (p₁ ⁻¹' X)}
    {S : Tiling.AxisParallel.Topology.TilingSpace K (p₁ ⁻¹' X)}
    (D : Tiling.AxisParallel.Continuous.PersistentTransientSplit K X U S)
    (hp : D.persistent.Nonempty) (ht : D.transient.Nonempty) :
    ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
      (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit K.openCarrier S.centres S₀ S₁ v := by
  cases ho : D.orientation with
  | vertical =>
    refine ⟨e₂, by simp, D.persistent, D.transient, fun _ => rfl,
      hp, ht, D.disjoint, D.union_eq, ?_, ?_⟩
    · rw [e₂_eq_I, Columns.invariant_iff_verticalSlab]
      exact ⟨D.persistentBase, D.persistentBase_regular.symm,
        D.persistentSupport_vertical ho⟩
    · rw [e₂_eq_I, Columns.invariant_iff_verticalSlab]
      exact ⟨D.transientBase, D.transientBase_regular.symm,
        D.transientSupport_vertical ho⟩
  | horizontal =>
    refine ⟨e₁, by simp, D.persistent, D.transient, ?_,
      hp, ht, D.disjoint, D.union_eq, ?_, ?_⟩
    · intro hproper
      exact (hproper (D.horizontal_requires_plane ho)).elim
    · rw [Columns.coveredRegion_openCarrier]
      have hinv := (Tiling.AxisParallel.horizontalInvariant_iff_product
        (Tiling.AxisParallel.regularSupport K D.persistent)).mpr
          ⟨D.persistentBase, D.persistentSupport_horizontal ho⟩
      simpa only [IsInvariantAlong, IsPeriod, e₁_eq_one, Complex.real_smul,
        mul_one] using hinv
    · rw [Columns.coveredRegion_openCarrier]
      have hinv := (Tiling.AxisParallel.horizontalInvariant_iff_product
        (Tiling.AxisParallel.regularSupport K D.transient)).mpr
          ⟨D.transientBase, D.transientSupport_horizontal ho⟩
      simpa only [IsInvariantAlong, IsPeriod, e₁_eq_one, Complex.real_smul,
        mul_one] using hinv

theorem non_flc_earthquake_limit
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (X : Set ℝ) (hX : X.Nonempty) (hXregular : IsRegularOpen X)
    (β : ℝ) (hβ : 0 < β) (hperiod : β +ᵥ X = X)
    (T : Set Plane) (hT : TilingOn (p₁ ⁻¹' X) Ω T)
    (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull (p₁ ⁻¹' X) T,
      TilingOn (p₁ ⁻¹' X) Ω S ∧
      ∃ v ∈ ({e₁, e₂} : Set Plane), ∃ S₀ S₁,
        (X ≠ univ → v = e₂) ∧ IsEarthquakeSplit Ω S S₀ S₁ v := by
  let K := regionOfTile Ω hΩ
  have hNative : Tiling.AxisParallel.TilesOn K T (p₁ ⁻¹' X) :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  let U : Tiling.AxisParallel.Topology.TilingSpace K (p₁ ⁻¹' X) :=
    ⟨⟨T, Fell.tilesOn_centres_isClosed hNative⟩, hNative⟩
  obtain ⟨D⟩ := Tiling.AxisParallel.Continuous.exists_nontrivialEarthquakeOrbitLimit
    hX (isRegularOpen_isOpen hXregular) hXregular hβ (base_period_membership hperiod)
    U (fun h => hFLC (hasFiniteLocalComplexity_iff_hasFLC.mpr h))
  have hHull := D.limit_mem_hull
  rw [Fell.production_hull_eq_preimage
    (isRegularOpen_isOpen (cylinder_regularOpen hXregular))
    (cylinder_regularOpen hXregular) U] at hHull
  refine ⟨D.limit.centres, hHull, (tilingOn_iff_native Ω hΩ _ _).mpr D.limit.tilesOn, ?_⟩
  simpa only [K, regionOfTile_openCarrier] using
    split_adapter D.split D.persistent_nonempty D.transient_nonempty

theorem non_flc_earthquake_limit_in_lattice
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
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
  let K := regionOfTile Ω hΩ
  have hNative : Tiling.AxisParallel.TilesOn K T (p₁ ⁻¹' X) :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  let U : Tiling.AxisParallel.Topology.TilingSpace K (p₁ ⁻¹' X) :=
    ⟨⟨T, Fell.tilesOn_centres_isClosed hNative⟩, hNative⟩
  let L : Tiling.AxisParallel.PlanarLattice := ⟨![p, q], hpq⟩
  have hRange : Set.range L.basis = ({p, q} : Set Plane) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [L]
    · intro hz
      rcases Set.mem_insert_iff.mp hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · exact ⟨1, (Set.mem_singleton_iff.mp hz).symm⟩
  have hLattice : L.toAddSubgroup = (span ℤ {p, q}).toAddSubgroup := by
    rw [Tiling.AxisParallel.PlanarLattice.toAddSubgroup,
      Tiling.Polygonal.PlanarLattice.toAddSubgroup, hRange,
      Submodule.span_int_eq_addSubgroupClosure]
  have hL : L.toAddSubgroup ≤ Tiling.AxisParallel.aePeriodGroup (p₁ ⁻¹' X) := by
    apply (AddSubgroup.closure_le _).mpr
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact (Fell.period_bridge
        (isRegularOpen_isOpen (cylinder_regularOpen hXregular))
        (cylinder_regularOpen hXregular) p).mpr hp
    · exact (Fell.period_bridge
        (isRegularOpen_isOpen (cylinder_regularOpen hXregular))
        (cylinder_regularOpen hXregular) q).mpr hq
  obtain ⟨D, lambda, gamma, D', hlambda, _hHull, hconv, hp', ht'⟩ :=
    Tiling.AxisParallel.Continuous.exists_nontrivialEarthquakeOrbitLimit_latticeTranslations
      hX (isRegularOpen_isOpen hXregular) hXregular hβ (base_period_membership hperiod)
      U (fun h => hFLC (hasFiniteLocalComplexity_iff_hasFLC.mpr h)) L hL
  let V := Tiling.AxisParallel.Topology.TilingSpace.translate gamma D.limit
  have hseq : Tiling.AxisParallel.Topology.TilingSpace.centresSequence
      (Tiling.AxisParallel.Topology.TilingSpace.translateSequence lambda U) =
        (fun n => (lambda n : Plane) +ᵥ T) := by
    funext n
    exact Fell.centres_translation (lambda n) U
  rw [hseq] at hconv
  have hHull := Fell.mem_orbitHullUnder_of_locallyFellConverges
    (G := (span ℤ {p, q} : Set Plane)) (T := T)
    (fun n => (lambda n : Plane))
    (fun n => by
      change (lambda n : Plane) ∈ (span ℤ {p, q}).toAddSubgroup
      rw [← hLattice]
      exact hlambda n) V.centres hconv
  refine ⟨V.centres, hHull, (tilingOn_iff_native Ω hΩ _ _).mpr V.tilesOn, ?_⟩
  simpa only [K, regionOfTile_openCarrier] using split_adapter D' hp' ht'

theorem non_flc_finite_horizontal_complexity_limit
    (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (T : Set Plane) (hT : Tiles Ω T) (hFLC : ¬ HasFiniteLocalComplexity T) :
    ∃ S ∈ orbitHull univ T,
      Tiles Ω S ∧
      ((HasFiniteLocalComplexity (p₁ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₂ S) ∨
       (HasFiniteLocalComplexity (p₂ '' S) ∧
          (S : Set Plane) ∉ tectonicPlates Ω e₁ S)) := by
  let K := regionOfTile Ω hΩ
  have hNative : Tiling.AxisParallel.TilesOn K T Set.univ :=
    (tilingOn_iff_native Ω hΩ _ T).mp hT
  let U : Tiling.AxisParallel.Topology.TilingSpace K Set.univ :=
    ⟨⟨T, Fell.tilesOn_centres_isClosed hNative⟩, hNative⟩
  obtain ⟨D⟩ := Tiling.AxisParallel.Structure.exists_finiteHorizontalComplexityTrichotomy
    U (fun h => hFLC (hasFiniteLocalComplexity_iff_hasFLC.mpr h))
  have hHull := D.limit_mem_hull
  rw [Fell.production_hull_eq_preimage isOpen_univ
    (by simp : interior (closure (Set.univ : Set Plane)) = Set.univ) U] at hHull
  refine ⟨D.limit.centres, hHull, (tilingOn_iff_native Ω hΩ _ _).mpr D.limit.tilesOn, ?_⟩
  cases ho : D.orientation with
  | vertical =>
    refine Or.inl ⟨hasFiniteLocalComplexity_iff_hasFLC.mpr
      (D.finiteHorizontal_original ho), ?_⟩
    intro hmem
    have hEq := Columns.tectonicPlates_eq_nonColumn D.limit.tilesOn
    have hmem' : (D.limit.centres : Set Plane) ∈
        tectonicPlates K.openCarrier Complex.I D.limit.centres := by
      simpa only [K, regionOfTile_openCarrier, e₂_eq_I] using hmem
    rw [hEq] at hmem'
    obtain ⟨P, hP, hPcentres⟩ := hmem'
    exact D.nontrivialVertical_original ho ⟨P, hP, hPcentres⟩
  | horizontal =>
    have hproj : Complex.re '' (Tiling.AxisParallel.coordinateSwap ''
        (D.limit.centres : Set Plane)) = p₂ '' (D.limit.centres : Set Plane) := by
      rw [Set.image_image]
      rfl
    have hFHC := D.finiteHorizontal_swapped ho
    change Tiling.AxisParallel.HasFLC (Complex.re ''
      (Tiling.AxisParallel.coordinateSwap '' (D.limit.centres : Set Plane))) at hFHC
    rw [hproj] at hFHC
    refine Or.inr ⟨hasFiniteLocalComplexity_iff_hasFLC.mpr hFHC, ?_⟩
    intro hmem
    have hmem' : (D.limit.centres : Set Plane) ∈
        tectonicPlates K.openCarrier 1 D.limit.centres := by
      simpa only [K, regionOfTile_openCarrier, e₁_eq_one] using hmem
    have hswap := (Columns.tectonic_mem_coordinateSwap_horizontal K
      D.limit.centres D.limit.centres).mp hmem'
    rw [Columns.tectonicPlates_eq_nonColumn (D.swapped_tilesOn ho)] at hswap
    obtain ⟨P, hP, hPcentres⟩ := hswap
    exact D.nontrivialVertical_swapped ho ⟨P, hP, hPcentres⟩

end Tiling.AxisParallel.SetFormulation
