import Tiling.AxisParallel.SetFormulation.Basic
import Tiling.AxisParallel.Continuous.WeakTilingTopology

/-!
# Ambient Fell hulls and fixed-carrier minimality

The hit-open/miss-compact topology agrees with the one-point
Vietoris topology used by the production tiling space. For regular-open
carriers, exact and essential periods agree, so their orbit hulls and
minimality predicates also agree.
-/

set_option autoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

namespace Tiling.AxisParallel.SetFormulation.Fell

noncomputable section

/-- Packing by a fixed tile forces the centre set to be closed. -/
theorem tilesOn_centres_isClosed {K : Tiling.AxisParallel.Region} {E T : Set Plane}
    (hT : Tiling.AxisParallel.TilesOn K T E) : IsClosed T := by
  obtain ⟨delta, hdelta, hsep⟩ :=
    Tiling.AxisParallel.Continuous.tilesOn_uniformlySeparated K
  exact Metric.isClosed_of_pairwise_le_dist hdelta (hsep E T hT)

private def compactifiedCentres (F : TopologicalSpace.Closeds Plane) :
    Set (OnePoint Plane) :=
  (((↑) : Plane → OnePoint Plane) '' (F : Set Plane)) ∪ {OnePoint.infty}

/-- Identification of hit-open/miss-compact Fell with one-point Vietoris.
This proof is adapted from the old Solution's valid `native_fell_topology`.
-/
theorem native_fell_topology :
    fellTopology = TopologicalSpace.induced compactifiedCentres
      (TopologicalSpace.vietoris (OnePoint Plane)) := by
  let : TopologicalSpace (Set (OnePoint Plane)) :=
    TopologicalSpace.vietoris (OnePoint Plane)
  let : TopologicalSpace (TopologicalSpace.Closeds Plane) := fellTopology
  apply le_antisymm
  · rw [TopologicalSpace.vietoris, induced_generateFrom_eq]
    apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    rintro _ ⟨U, hU, rfl⟩
    rcases hU with ⟨V, hV, rfl⟩ | ⟨V, hV, rfl⟩
    · by_cases hinfty : OnePoint.infty ∈ V
      · have hQ : IsCompact (((↑) : Plane → OnePoint Plane) ⁻¹' V)ᶜ :=
          ((OnePoint.isOpen_iff_of_mem hinfty).mp hV).2
        have heq : compactifiedCentres ⁻¹' V.powerset =
            {F : TopologicalSpace.Closeds Plane |
              Disjoint (F : Set Plane) (((↑) : Plane → OnePoint Plane) ⁻¹' V)ᶜ} := by
          ext F
          simp only [Set.mem_preimage, Set.mem_powerset_iff, Set.mem_ofPred_eq,
            compactifiedCentres, Set.union_subset_iff,
            Set.image_subset_iff, Set.singleton_subset_iff, hinfty, and_true,
            Set.disjoint_compl_right_iff_subset]
        rw [heq]
        exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inr ⟨_, hQ, rfl⟩)
      · have heq : compactifiedCentres ⁻¹' V.powerset = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro F hF
          exact hinfty (hF (Set.mem_union_right _ (Set.mem_singleton _)))
        rw [heq]
        exact @isOpen_empty _ fellTopology
    · by_cases hinfty : OnePoint.infty ∈ V
      · have heq : compactifiedCentres ⁻¹'
              {s : Set (OnePoint Plane) | (s ∩ V).Nonempty} = Set.univ := by
          ext F
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          exact ⟨OnePoint.infty,
            Set.mem_union_right _ (Set.mem_singleton _), hinfty⟩
        rw [heq]
        exact @isOpen_univ _ fellTopology
      · have hopen : IsOpen (((↑) : Plane → OnePoint Plane) ⁻¹' V) :=
          hV.preimage OnePoint.continuous_coe
        have heq : compactifiedCentres ⁻¹'
              {s : Set (OnePoint Plane) | (s ∩ V).Nonempty} =
            {F : TopologicalSpace.Closeds Plane |
              ((F : Set Plane) ∩ (((↑) : Plane → OnePoint Plane) ⁻¹' V)).Nonempty} := by
          ext F
          constructor
          · rintro ⟨z, hz, hzV⟩
            rcases hz with ⟨x, hx, rfl⟩ | hz
            · exact ⟨x, hx, hzV⟩
            · exact (hinfty (by simpa only [Set.mem_singleton_iff.mp hz] using hzV)).elim
          · rintro ⟨x, hx, hxV⟩
            exact ⟨(x : OnePoint Plane), Or.inl ⟨x, hx, rfl⟩, hxV⟩
        rw [heq]
        exact TopologicalSpace.isOpen_generateFrom_of_mem (Or.inl ⟨_, hopen, rfl⟩)
  · apply TopologicalSpace.le_generateFrom_iff_subset_isOpen.mpr
    rintro U (⟨V, hV, rfl⟩ | ⟨Q, hQ, rfl⟩)
    · apply isOpen_induced_iff.mpr
      refine ⟨{s : Set (OnePoint Plane) |
        (s ∩ (((↑) : Plane → OnePoint Plane) '' V)).Nonempty},
        TopologicalSpace.vietoris.isOpen_inter_nonempty_of_isOpen
          (OnePoint.isOpen_image_coe.mpr hV), ?_⟩
      ext F
      constructor
      · rintro ⟨z, hzF, x, hx, rfl⟩
        refine ⟨x, ?_, hx⟩
        simpa [compactifiedCentres] using hzF
      · rintro ⟨x, hx, hxV⟩
        exact ⟨(x : OnePoint Plane), Or.inl ⟨x, hx, rfl⟩, ⟨x, hxV, rfl⟩⟩
    · apply isOpen_induced_iff.mpr
      refine ⟨((((↑) : Plane → OnePoint Plane) '' Q)ᶜ).powerset,
        IsOpen.powerset_vietoris
          (OnePoint.isOpen_compl_image_coe.mpr ⟨hQ.isClosed, hQ⟩), ?_⟩
      ext F
      change ((((↑) : Plane → OnePoint Plane) '' (F : Set Plane)) ∪
        {OnePoint.infty} ⊆ (((↑) : Plane → OnePoint Plane) '' Q)ᶜ) ↔
        Disjoint (F : Set Plane) Q
      simp [Set.subset_def, Set.disjoint_left]
      aesop

local instance : TopologicalSpace (TopologicalSpace.Closeds Plane) := fellTopology

private def compactifyClosed (F : TopologicalSpace.Closeds Plane) :
    TopologicalSpace.NonemptyCompacts (OnePoint Plane) :=
  Tiling.Topology.fellCompactification (F : Set Plane) F.isClosed

private theorem compactifyClosed_inducing : Topology.IsInducing compactifyClosed := by
  constructor
  change fellTopology = TopologicalSpace.induced compactifyClosed
    (TopologicalSpace.induced
      ((↑) : TopologicalSpace.NonemptyCompacts (OnePoint Plane) → Set (OnePoint Plane))
      (TopologicalSpace.vietoris (OnePoint Plane)))
  simp only [induced_compose]
  exact native_fell_topology

private theorem compactifyClosed_embedding : Topology.IsEmbedding compactifyClosed where
  __ := compactifyClosed_inducing
  injective := by
    intro F G h
    apply TopologicalSpace.Closeds.ext
    ext x
    have hx := congrArg
      (fun C : TopologicalSpace.NonemptyCompacts (OnePoint Plane) =>
        (x : OnePoint Plane) ∈ (C : Set (OnePoint Plane))) h
    simpa [compactifyClosed, Tiling.Topology.fellCompactification] using hx

local instance : T2Space (TopologicalSpace.Closeds Plane) :=
  compactifyClosed_embedding.t2Space

/-- The production centre map is an embedding into the ambient Fell space. -/
theorem centres_embedding (K : Tiling.AxisParallel.Region) (E : Set Plane) :
    Topology.IsEmbedding
      (Tiling.AxisParallel.Topology.TilingSpace.centres (K := K) (E := E)) where
  eq_induced := by
    let : MetricSpace (OnePoint Plane) := by
      let e : OnePoint Plane ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
        onePointEquivSphereOfFinrankEq (ι := Fin 3) (V := Plane) (by
          norm_num [Plane, Complex.finrank_real_complex])
      exact e.isEmbedding.comapMetricSpace
    change TopologicalSpace.induced
      (fun T : Tiling.AxisParallel.Topology.TilingSpace K E =>
        Tiling.Topology.fellCompactification
          (T.centres : Set Plane) T.centres.isClosed)
      (TopologicalSpace.induced
        ((↑) : TopologicalSpace.NonemptyCompacts (OnePoint Plane) → Set (OnePoint Plane))
        (TopologicalSpace.vietoris (OnePoint Plane))) =
      TopologicalSpace.induced Tiling.AxisParallel.Topology.TilingSpace.centres fellTopology
    rw [native_fell_topology]
    simp only [induced_compose]
    rfl
  injective := by
    intro U V h
    cases U
    cases V
    cases h
    rfl

/-- In fact, the full fixed-carrier tiling space is a closed subspace of the
ambient Fell space: this follows from production's proved compactness. -/
theorem centres_closedEmbedding (K : Tiling.AxisParallel.Region)
    (E : Set Plane) :
    Topology.IsClosedEmbedding
      (Tiling.AxisParallel.Topology.TilingSpace.centres (K := K) (E := E)) where
  __ := centres_embedding K E
  isClosed_range := by
    have hcompact := (Tiling.AxisParallel.Continuous.tilingSpace_compact K E).image
      (centres_embedding K E).continuous
    simpa only [Set.image_univ] using hcompact.isClosed

/-- Literal periods agree with the production almost-everywhere periods on
regular-open carriers. -/
theorem period_bridge {E : Set Plane}
    (hopen : IsOpen E) (hregular : interior (closure E) = E) (p : Plane) :
    p ∈ Tiling.AxisParallel.aePeriodGroup E ↔ IsPeriod E p := by
  rw [Tiling.AxisParallel.aePeriodGroup_eq_periodGroup_of_regularOpen hopen hregular]
  rfl

theorem centres_translation {K : Tiling.AxisParallel.Region} {E : Set Plane}
    (p : Tiling.AxisParallel.aePeriodGroup E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    ((Tiling.AxisParallel.Topology.TilingSpace.translate p U).centres : Set Plane) =
      (p : Plane) +ᵥ (U.centres : Set Plane) := by
  change (fun x => x + (p : Plane)) '' (U.centres : Set Plane) = _
  ext x
  simp only [mem_image, mem_vadd_set, vadd_eq_add]
  constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, add_comm _ _⟩

theorem ambient_orbit_eq_image {K : Tiling.AxisParallel.Region} {E : Set Plane}
    (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    {S : TopologicalSpace.Closeds Plane |
      ∃ p ∈ {p : Plane | IsPeriod E p},
        (S : Set Plane) = p +ᵥ (U.centres : Set Plane)} =
    Tiling.AxisParallel.Topology.TilingSpace.centres ''
      AddAction.orbit (Tiling.AxisParallel.aePeriodGroup E) U := by
  ext S
  constructor
  · rintro ⟨p, hp, hS⟩
    let g : Tiling.AxisParallel.aePeriodGroup E := ⟨p, (period_bridge hopen hregular p).mpr hp⟩
    refine ⟨Tiling.AxisParallel.Topology.TilingSpace.translate g U,
      AddAction.mem_orbit_iff.mpr ⟨g, rfl⟩, ?_⟩
    apply TopologicalSpace.Closeds.ext
    exact (centres_translation g U).trans hS.symm
  · rintro ⟨V, hV, rfl⟩
    obtain ⟨g, rfl⟩ := AddAction.mem_orbit_iff.mp hV
    exact ⟨g, (period_bridge hopen hregular g).mp g.property, centres_translation g U⟩

/-- Closure in the fixed-carrier space is the pullback of ambient Fell closure.
This does not assume that arbitrary ambient closure points are tilings. -/
theorem production_hull_eq_preimage {K : Tiling.AxisParallel.Region}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    Tiling.AxisParallel.Topology.orbitHull U =
      Tiling.AxisParallel.Topology.TilingSpace.centres ⁻¹' orbitHull E (U.centres : Set Plane) := by
  rw [Tiling.AxisParallel.Topology.orbitHull,
    (centres_embedding K E).isInducing.closure_eq_preimage_closure_image,
    orbitHull, orbitHullUnder, ambient_orbit_eq_image hopen hregular]

/-- The image of the production hull is the full ambient Fell hull.
The reverse inclusion follows from compactness, rather than an assumed
closed-subspace statement. In particular, this proves that ambient hull points
of a production tiling still tile the fixed carrier. -/
theorem ambient_hull_eq_image {K : Tiling.AxisParallel.Region}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    orbitHull E (U.centres : Set Plane) =
      Tiling.AxisParallel.Topology.TilingSpace.centres ''
        Tiling.AxisParallel.Topology.orbitHull U := by
  have hc := (centres_embedding K E).continuous
  have hclosed : IsClosed
      (Tiling.AxisParallel.Topology.TilingSpace.centres ''
        Tiling.AxisParallel.Topology.orbitHull U) :=
    ((Tiling.AxisParallel.Continuous.orbitHull_compact U).1.image hc).isClosed
  apply Set.Subset.antisymm
  · rw [orbitHull, orbitHullUnder, ambient_orbit_eq_image hopen hregular]
    apply closure_minimal _ hclosed
    exact Set.image_mono subset_closure
  · change Tiling.AxisParallel.Topology.TilingSpace.centres '' _ ⊆ _
    rw [production_hull_eq_preimage hopen hregular]
    exact Set.image_preimage_subset _ _

/-- Ambient Fell closure does not introduce a non-tiling centre set. -/
theorem ambient_hull_points_tile {K : Tiling.AxisParallel.Region}
    {E : Set Plane} (hopen : IsOpen E) (hregular : interior (closure E) = E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E)
    {S : TopologicalSpace.Closeds Plane} (hS : S ∈ orbitHull E (U.centres : Set Plane)) :
    Tiling.AxisParallel.TilesOn K (S : Set Plane) E := by
  rw [ambient_hull_eq_image hopen hregular U] at hS
  obtain ⟨V, _, rfl⟩ := hS
  exact V.tilesOn

/-- Ambient centre-set minimality is equivalent to minimality of the
production orbit hull on the same regular-open carrier. -/
theorem minimal_bridge {K : Tiling.AxisParallel.Region} {E : Set Plane}
    (hopen : IsOpen E) (hregular : IsRegularOpen E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    IsMinimal E (U.centres : Set Plane) ↔
      Tiling.AxisParallel.Topology.IsTopologicallyMinimal
        (Tiling.AxisParallel.Topology.orbitHull U) := by
  constructor
  · rintro ⟨_hclosed, hminimal⟩
    obtain ⟨_, hnonempty, hinvariant⟩ :=
      Tiling.AxisParallel.Continuous.orbitHull_compact U
    refine ⟨hnonempty, isClosed_closure, hinvariant, ?_⟩
    intro V hV
    have hambient : V.centres ∈ orbitHull E (U.centres : Set Plane) := by
      rw [production_hull_eq_preimage hopen hregular U] at hV
      exact hV
    change Tiling.AxisParallel.Topology.orbitHull V =
      Tiling.AxisParallel.Topology.orbitHull U
    rw [production_hull_eq_preimage hopen hregular V,
      hminimal V.centres hambient]
    exact (production_hull_eq_preimage hopen hregular U).symm
  · intro hminimal
    refine ⟨U.centres.isClosed, ?_⟩
    intro S hS
    rw [ambient_hull_eq_image hopen hregular U] at hS
    obtain ⟨V, hV, rfl⟩ := hS
    have hVhull : Tiling.AxisParallel.Topology.orbitHull V =
        Tiling.AxisParallel.Topology.orbitHull U := hminimal.2.2.2 V hV
    rw [ambient_hull_eq_image hopen hregular V, hVhull,
      ← ambient_hull_eq_image hopen hregular U]

/-- A regular-open carrier alone supplies the openness used by the hull bridge. -/
theorem minimal_iff {K : Tiling.AxisParallel.Region} {E : Set Plane}
    (hregular : IsRegularOpen E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    IsMinimal E (U.centres : Set Plane) ↔
      Tiling.AxisParallel.Topology.IsTopologicallyMinimal
        (Tiling.AxisParallel.Topology.orbitHull U) :=
  minimal_bridge (isRegularOpen_isOpen hregular) hregular U

/-- Production local Fell convergence is precisely ambient Fell convergence. -/
theorem locallyFellConverges_iff_tendsto
    (A : ℕ → TopologicalSpace.Closeds Plane) (L : TopologicalSpace.Closeds Plane) :
    Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun n => (A n : Set Plane)) (L : Set Plane) ↔
      Filter.Tendsto A Filter.atTop (nhds L) := by
  constructor
  · rintro ⟨hA, hL, hconv⟩
    apply compactifyClosed_inducing.tendsto_nhds_iff.mpr
    exact hconv
  · intro hconv
    refine ⟨fun n => (A n).isClosed, L.isClosed, ?_⟩
    exact compactifyClosed_inducing.tendsto_nhds_iff.mp hconv

/-- A limit of translations in G belongs to the G-restricted translation hull. -/
theorem mem_orbitHullUnder_of_locallyFellConverges
    {G T : Set Plane} (g : ℕ → Plane) (hg : ∀ n, g n ∈ G)
    (L : TopologicalSpace.Closeds Plane)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges
      (fun n => g n +ᵥ T) (L : Set Plane)) : L ∈ orbitHullUnder G T := by
  obtain ⟨hA, hL, hconv⟩ := hconv
  let A : ℕ → TopologicalSpace.Closeds Plane := fun n => ⟨g n +ᵥ T, hA n⟩
  have hFell : Filter.Tendsto A Filter.atTop (nhds L) := by
    apply (locallyFellConverges_iff_tendsto A L).mp
    exact ⟨hA, hL, hconv⟩
  exact mem_closure_of_tendsto hFell
    (Filter.Eventually.of_forall fun n => ⟨g n, hg n, rfl⟩)

/-- Every production orbit hull contains an ambient-minimal centre configuration. -/
theorem exists_minimal_hull_point {K : Tiling.AxisParallel.Region} {E : Set Plane}
    (hregular : IsRegularOpen E)
    (U : Tiling.AxisParallel.Topology.TilingSpace K E) :
    ∃ V : Tiling.AxisParallel.Topology.TilingSpace K E,
      V.centres ∈ orbitHull E (U.centres : Set Plane) ∧
        IsMinimal E (V.centres : Set Plane) := by
  obtain ⟨Y, hYHull, hYnonempty, _, _, hYminimal⟩ :=
    Tiling.AxisParallel.Continuous.exists_minimalInvariantSubset U
  obtain ⟨V, hVY⟩ := hYnonempty
  have hVhull : Tiling.AxisParallel.Topology.orbitHull V = Y :=
    hYminimal.2.2.2 V hVY
  refine ⟨V, ?_, (minimal_iff hregular V).mpr ?_⟩
  · rw [ambient_hull_eq_image (isRegularOpen_isOpen hregular) hregular U]
    exact ⟨V, hYHull hVY, rfl⟩
  · rw [hVhull]
    exact hYminimal

end
end Tiling.AxisParallel.SetFormulation.Fell
