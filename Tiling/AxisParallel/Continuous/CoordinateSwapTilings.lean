import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Continuous.WeakTilingTopology

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.Topology

private def IsCoordinateSwapTiling {K : Region}
    (T : TilingSpace K Set.univ)
    (Tσ : TilingSpace K.coordinateSwap Set.univ) : Prop :=
  (Tσ.centres : Set Tiling.Plane) =
    coordinateSwap '' (T.centres : Set Tiling.Plane)

theorem exists_coordinateSwapTiling
    {K : Region} (T : TilingSpace K Set.univ) :
    ∃ Tσ : TilingSpace K.coordinateSwap Set.univ,
      (Tσ.centres : Set Tiling.Plane) =
        coordinateSwap '' (T.centres : Set Tiling.Plane) := by
  let c : TopologicalSpace.Closeds Tiling.Plane :=
    ⟨coordinateSwap '' (T.centres : Set Tiling.Plane),
      coordinateSwap.toHomeomorph.isClosed_image.mpr T.centres.isClosed⟩
  have htiles :
      TilesOn K.coordinateSwap
        (coordinateSwap '' (T.centres : Set Tiling.Plane)) Set.univ := by
    simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using
      (tilesOn_coordinateSwap (K := K) (S := (T.centres : Set Tiling.Plane))
        (D := Set.univ) T.tilesOn)
  refine ⟨{ centres := c, tilesOn := htiles }, ?_⟩
  rfl

private theorem coordinateSwapTiling_unique
    {K : Region} {T : TilingSpace K Set.univ}
    {Tσ Uσ : TilingSpace K.coordinateSwap Set.univ} :
    IsCoordinateSwapTiling T Tσ → IsCoordinateSwapTiling T Uσ → Tσ = Uσ := by
  intro hTσ hUσ
  cases Tσ with
  | mk cσ hσ =>
    cases Uσ with
    | mk cυ hυ =>
      congr 1
      apply TopologicalSpace.Closeds.ext
      exact hTσ.trans hUσ.symm

private def coordinateSwapTilingMap {K : Region}
    (T : TilingSpace K Set.univ) : TilingSpace K.coordinateSwap Set.univ where
  centres :=
    ⟨coordinateSwap '' (T.centres : Set Tiling.Plane),
      coordinateSwap.toHomeomorph.isClosed_image.mpr T.centres.isClosed⟩
  tilesOn := by
    change TilesOn K.coordinateSwap
      (coordinateSwap '' (T.centres : Set Tiling.Plane)) Set.univ
    simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using
      (tilesOn_coordinateSwap (K := K) (S := (T.centres : Set Tiling.Plane))
        (D := Set.univ) T.tilesOn)

private theorem coordinateSwap_fellCompactification
    {S : Set Tiling.Plane} (hS : IsClosed S) :
    Tiling.AxisParallel.Topology.fellCompactification
        (coordinateSwap '' S)
        (coordinateSwap.toHomeomorph.isClosed_image.mpr hS) =
      TopologicalSpace.NonemptyCompacts.map
        coordinateSwap.toHomeomorph.onePointCongr
        coordinateSwap.toHomeomorph.onePointCongr.continuous
        (Tiling.AxisParallel.Topology.fellCompactification S hS) := by
  apply TopologicalSpace.NonemptyCompacts.ext
  change
    ((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) ''
          (coordinateSwap '' S) ∪ {OnePoint.infty}) =
      (coordinateSwap.toHomeomorph.onePointCongr ''
        (((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) '' S) ∪
          {OnePoint.infty}))
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false, Homeomorph.onePointCongr]
      constructor
      · rintro ⟨y, ⟨t, ht, rfl⟩, hyx⟩
        refine ⟨(t : OnePoint Tiling.Plane), Or.inl ⟨t, ht, rfl⟩, ?_⟩
        exact hyx
      · rintro ⟨z, hz, hzx⟩
        rcases hz with ⟨t, ht, rfl⟩ | rfl
        · exact ⟨coordinateSwap t, ⟨t, ht, rfl⟩, hzx⟩
        · simp at hzx

private theorem coordinateSwapTilingMap_continuous {K : Region} :
    Continuous (coordinateSwapTilingMap :
      TilingSpace K Set.univ → TilingSpace K.coordinateSwap Set.univ) := by
  rw [continuous_iff_seqContinuous]
  intro U V hUV
  apply (locallyFell_metrizable K.coordinateSwap Set.univ).2
      (coordinateSwapTilingMap ∘ U) (coordinateSwapTilingMap V) |>.mpr
  obtain ⟨hUclosed, hVclosed, hFell⟩ :=
    (locallyFell_metrizable K Set.univ).2 U V |>.mp hUV
  let mapCompact := TopologicalSpace.NonemptyCompacts.map
    coordinateSwap.toHomeomorph.onePointCongr
    coordinateSwap.toHomeomorph.onePointCongr.continuous
  have hmap : Continuous mapCompact :=
    coordinateSwap.toHomeomorph.onePointCongr.continuous.nonemptyCompacts_map
  have hmapped := (hmap.tendsto
    (Tiling.AxisParallel.Topology.fellCompactification
      (V.centres : Set Tiling.Plane) hVclosed)).comp hFell
  refine ⟨fun n ↦ (coordinateSwapTilingMap (U n)).centres.isClosed,
    (coordinateSwapTilingMap V).centres.isClosed, ?_⟩
  convert hmapped using 1
  · funext n
    apply coordinateSwap_fellCompactification
  · congr 1
    apply coordinateSwap_fellCompactification

private theorem coordinateSwapTilingMap_translate
    {K : Region} (g : aePeriodGroup (Set.univ : Set Tiling.Plane))
    (T : TilingSpace K Set.univ) :
    coordinateSwapTilingMap (TilingSpace.translate g T) =
      TilingSpace.translate
        (⟨coordinateSwap g, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩ :
          aePeriodGroup (Set.univ : Set Tiling.Plane))
        (coordinateSwapTilingMap T) := by
  unfold coordinateSwapTilingMap TilingSpace.translate
  congr 1
  apply TopologicalSpace.Closeds.ext
  ext z
  change z ∈ coordinateSwap ''
      ((fun x : Tiling.Plane => x + (g : Tiling.Plane)) ''
        (T.centres : Set Tiling.Plane)) ↔
    z ∈ (fun x : Tiling.Plane => x + coordinateSwap (g : Tiling.Plane)) ''
      (coordinateSwap '' (T.centres : Set Tiling.Plane))
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨coordinateSwap x, ⟨x, hx, rfl⟩, coordinateSwap.map_add x g⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y + (g : Tiling.Plane), ⟨y, hy, rfl⟩,
      coordinateSwap.map_add y g⟩

private theorem coordinateSwap_mem_orbitHull
    {K : Region} {T S : TilingSpace K Set.univ}
    (hS : S ∈ orbitHull T) :
    coordinateSwapTilingMap S ∈
      orbitHull (coordinateSwapTilingMap T) := by
  let F : TilingSpace K Set.univ → TilingSpace K.coordinateSwap Set.univ :=
    coordinateSwapTilingMap
  let H : Set (TilingSpace K.coordinateSwap Set.univ) :=
    orbitHull (coordinateSwapTilingMap T)
  have hclosed : IsClosed (F ⁻¹' H) :=
    isClosed_closure.preimage coordinateSwapTilingMap_continuous
  have horbit : AddAction.orbit (aePeriodGroup (Set.univ : Set Tiling.Plane)) T ⊆
      F ⁻¹' H := by
    rintro V ⟨g, rfl⟩
    change coordinateSwapTilingMap (TilingSpace.translate g T) ∈ H
    rw [coordinateSwapTilingMap_translate]
    exact subset_closure (AddAction.mem_orbit (coordinateSwapTilingMap T)
      (⟨coordinateSwap g, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩ :
        aePeriodGroup (Set.univ : Set Tiling.Plane)))
  change F S ∈ H
  exact (closure_minimal horbit hclosed) hS

private theorem tilingSpace_eq_of_centres_eq
    {K : Region} {A B : TilingSpace K Set.univ}
    (h : (A.centres : Set Tiling.Plane) = (B.centres : Set Tiling.Plane)) :
    A = B := by
  cases A with
  | mk ca ha =>
    cases B with
    | mk cb hb =>
      congr 1
      exact TopologicalSpace.Closeds.ext h

private def coordinateSwapBackMap {K : Region}
    (Tσ : TilingSpace K.coordinateSwap Set.univ) :
    TilingSpace K Set.univ where
  centres :=
    ⟨coordinateSwap '' (Tσ.centres : Set Tiling.Plane),
      coordinateSwap.toHomeomorph.isClosed_image.mpr Tσ.centres.isClosed⟩
  tilesOn := by
    change TilesOn K
      (coordinateSwap '' (Tσ.centres : Set Tiling.Plane)) Set.univ
    have h := tilesOn_coordinateSwap (K := K.coordinateSwap)
      (S := (Tσ.centres : Set Tiling.Plane)) (D := Set.univ) Tσ.tilesOn
    have hK : K.coordinateSwap.coordinateSwap = K :=
      Region.coordinateSwap_involutive K
    have h' : TilesOn K.coordinateSwap.coordinateSwap
        (coordinateSwap '' (Tσ.centres : Set Tiling.Plane)) Set.univ := by
      simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using h
    simpa only [hK] using h'

private theorem coordinateSwapBackMap_continuous {K : Region} :
    Continuous (coordinateSwapBackMap :
      TilingSpace K.coordinateSwap Set.univ → TilingSpace K Set.univ) := by
  rw [continuous_iff_seqContinuous]
  intro U V hUV
  apply (locallyFell_metrizable K Set.univ).2
      (coordinateSwapBackMap ∘ U) (coordinateSwapBackMap V) |>.mpr
  obtain ⟨hUclosed, hVclosed, hFell⟩ :=
    (locallyFell_metrizable K.coordinateSwap Set.univ).2 U V |>.mp hUV
  let mapCompact := TopologicalSpace.NonemptyCompacts.map
    coordinateSwap.toHomeomorph.onePointCongr
    coordinateSwap.toHomeomorph.onePointCongr.continuous
  have hmap : Continuous mapCompact :=
    coordinateSwap.toHomeomorph.onePointCongr.continuous.nonemptyCompacts_map
  have hmapped := (hmap.tendsto
    (Tiling.AxisParallel.Topology.fellCompactification
      (V.centres : Set Tiling.Plane) hVclosed)).comp hFell
  refine ⟨fun n ↦ (coordinateSwapBackMap (U n)).centres.isClosed,
    (coordinateSwapBackMap V).centres.isClosed, ?_⟩
  convert hmapped using 1
  · funext n
    apply coordinateSwap_fellCompactification
  · congr 1
    apply coordinateSwap_fellCompactification

private theorem coordinateSwapTilingMap_back_eq {K : Region}
    (Tσ : TilingSpace K.coordinateSwap Set.univ) :
    coordinateSwapTilingMap (coordinateSwapBackMap Tσ) = Tσ := by
  apply tilingSpace_eq_of_centres_eq
  change coordinateSwap '' (coordinateSwap '' (Tσ.centres : Set Tiling.Plane)) =
    (Tσ.centres : Set Tiling.Plane)
  ext z
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hz
    exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩

private theorem coordinateSwapBackMap_translate
    {K : Region} (g : aePeriodGroup (Set.univ : Set Tiling.Plane))
    (Tσ : TilingSpace K.coordinateSwap Set.univ) :
    coordinateSwapBackMap (TilingSpace.translate g Tσ) =
      TilingSpace.translate
        (⟨coordinateSwap g, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩ :
          aePeriodGroup (Set.univ : Set Tiling.Plane))
        (coordinateSwapBackMap Tσ) := by
  unfold coordinateSwapBackMap TilingSpace.translate
  congr 1
  apply TopologicalSpace.Closeds.ext
  ext z
  change z ∈ coordinateSwap ''
      ((fun x : Tiling.Plane => x + (g : Tiling.Plane)) ''
        (Tσ.centres : Set Tiling.Plane)) ↔
    z ∈ (fun x : Tiling.Plane => x + coordinateSwap (g : Tiling.Plane)) ''
      (coordinateSwap '' (Tσ.centres : Set Tiling.Plane))
  constructor
  · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨coordinateSwap x, ⟨x, hx, rfl⟩, coordinateSwap.map_add x g⟩
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨y + (g : Tiling.Plane), ⟨y, hy, rfl⟩,
      coordinateSwap.map_add y g⟩

private theorem coordinateSwapBack_mem_orbitHull
    {K : Region} {Tσ Sσ : TilingSpace K.coordinateSwap Set.univ}
    (hSσ : Sσ ∈ orbitHull Tσ) :
    coordinateSwapBackMap Sσ ∈ orbitHull (coordinateSwapBackMap Tσ) := by
  let F : TilingSpace K.coordinateSwap Set.univ → TilingSpace K Set.univ :=
    coordinateSwapBackMap
  let H : Set (TilingSpace K Set.univ) := orbitHull (coordinateSwapBackMap Tσ)
  have hclosed : IsClosed (F ⁻¹' H) :=
    isClosed_closure.preimage coordinateSwapBackMap_continuous
  have horbit : AddAction.orbit
      (aePeriodGroup (Set.univ : Set Tiling.Plane)) Tσ ⊆ F ⁻¹' H := by
    rintro V ⟨g, rfl⟩
    change coordinateSwapBackMap (TilingSpace.translate g Tσ) ∈ H
    rw [coordinateSwapBackMap_translate]
    exact subset_closure (AddAction.mem_orbit (coordinateSwapBackMap Tσ)
      (⟨coordinateSwap g, by simp [aePeriodGroup, Tiling.Polygonal.aePeriodGroup]⟩ :
        aePeriodGroup (Set.univ : Set Tiling.Plane)))
  change F Sσ ∈ H
  exact (closure_minimal horbit hclosed) hSσ

theorem coordinateSwap_orbitHull_iff
    {K : Region}
    {T S : TilingSpace K Set.univ}
    {Tσ Sσ : TilingSpace K.coordinateSwap Set.univ}
    (hTσ : (Tσ.centres : Set Tiling.Plane) =
      coordinateSwap '' (T.centres : Set Tiling.Plane))
    (hSσ : (Sσ.centres : Set Tiling.Plane) =
      coordinateSwap '' (S.centres : Set Tiling.Plane)) :
    (S ∈ orbitHull T ↔ Sσ ∈ orbitHull Tσ) := by
  have hmapT : coordinateSwapTilingMap T = Tσ := by
    apply coordinateSwapTiling_unique (T := T)
    · rfl
    · exact hTσ
  have hmapS : coordinateSwapTilingMap S = Sσ := by
    apply coordinateSwapTiling_unique (T := S)
    · rfl
    · exact hSσ
  constructor
  · intro hS
    rw [← hmapS, ← hmapT]
    exact coordinateSwap_mem_orbitHull hS
  · intro hSσmem
    have hback := coordinateSwapBack_mem_orbitHull
      (K := K) (Tσ := Tσ) (Sσ := Sσ) hSσmem
    have hbackT : coordinateSwapBackMap Tσ = T := by
      apply tilingSpace_eq_of_centres_eq
      change coordinateSwap '' (Tσ.centres : Set Tiling.Plane) =
        (T.centres : Set Tiling.Plane)
      rw [hTσ]
      ext z
      constructor
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        simpa using hu
      · intro hz
        exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩
    have hbackS : coordinateSwapBackMap Sσ = S := by
      apply tilingSpace_eq_of_centres_eq
      change coordinateSwap '' (Sσ.centres : Set Tiling.Plane) =
        (S.centres : Set Tiling.Plane)
      rw [hSσ]
      ext z
      constructor
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
        simpa using hu
      · intro hz
        exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, coordinateSwap_apply_apply z⟩
    rw [hbackS, hbackT] at hback
    exact hback


private theorem orbitHull_isTopologicallyMinimal_iff
    {K : Region} {T : TilingSpace K Set.univ} :
    IsTopologicallyMinimal (orbitHull T) ↔
      ∀ S ∈ orbitHull T, orbitHull S = orbitHull T := by
  constructor
  · intro h S hS
    exact h.2.2.2 S hS
  · intro h
    refine ⟨(orbitHull_compact T).2.1, isClosed_closure, (orbitHull_compact T).2.2, ?_⟩
    intro S hS
    exact h S hS

theorem coordinateSwap_minimal_iff
    {K : Region} {T : TilingSpace K Set.univ}
    {Tσ : TilingSpace K.coordinateSwap Set.univ}
    (hTσ : (Tσ.centres : Set Tiling.Plane) =
      coordinateSwap '' (T.centres : Set Tiling.Plane)) :
    (IsTopologicallyMinimal (orbitHull T) ↔
      IsTopologicallyMinimal (orbitHull Tσ)) := by
  constructor
  · intro hT
    rw [orbitHull_isTopologicallyMinimal_iff] at hT ⊢
    refine fun Sσ hSσ ↦ ?_
    have hSmap : (coordinateSwapTilingMap
        (coordinateSwapBackMap Sσ)).centres =
        coordinateSwap '' ((coordinateSwapBackMap Sσ).centres : Set Tiling.Plane) := by
      rfl
    have hS : coordinateSwapBackMap Sσ ∈ orbitHull T := by
      apply (coordinateSwap_orbitHull_iff hTσ hSmap).mpr
      rw [coordinateSwapTilingMap_back_eq]
      exact hSσ
    have hHullS := hT (coordinateSwapBackMap Sσ) hS
    apply Set.ext
    intro Uσ
    have hUmap : (coordinateSwapTilingMap
        (coordinateSwapBackMap Uσ)).centres =
        coordinateSwap '' ((coordinateSwapBackMap Uσ).centres : Set Tiling.Plane) := by
      rfl
    constructor
    · intro hUSσ
      have hUS : coordinateSwapBackMap Uσ ∈
          orbitHull (coordinateSwapBackMap Sσ) := by
        apply (coordinateSwap_orbitHull_iff hSmap hUmap).mpr
        rw [coordinateSwapTilingMap_back_eq, coordinateSwapTilingMap_back_eq]
        exact hUSσ
      have hUT : coordinateSwapBackMap Uσ ∈ orbitHull T := by
        rw [hHullS] at hUS
        exact hUS
      have h := (coordinateSwap_orbitHull_iff hTσ hUmap).mp hUT
      rw [coordinateSwapTilingMap_back_eq] at h
      exact h
    · intro hUTσ
      have hUT : coordinateSwapBackMap Uσ ∈ orbitHull T := by
        apply (coordinateSwap_orbitHull_iff hTσ hUmap).mpr
        rw [coordinateSwapTilingMap_back_eq]
        exact hUTσ
      have hUS : coordinateSwapBackMap Uσ ∈
          orbitHull (coordinateSwapBackMap Sσ) := by
        rw [hHullS]
        exact hUT
      have h := (coordinateSwap_orbitHull_iff hSmap hUmap).mp hUS
      rw [coordinateSwapTilingMap_back_eq, coordinateSwapTilingMap_back_eq] at h
      exact h
  · intro hTσmin
    rw [orbitHull_isTopologicallyMinimal_iff] at hTσmin ⊢
    refine fun S hS ↦ ?_
    have hSmap : (coordinateSwapTilingMap S).centres =
        coordinateSwap '' (S.centres : Set Tiling.Plane) := by
      rfl
    have hSσ : coordinateSwapTilingMap S ∈ orbitHull Tσ := by
      apply (coordinateSwap_orbitHull_iff hTσ hSmap).mp
      exact hS
    have hHullSσ := hTσmin (coordinateSwapTilingMap S) hSσ
    apply Set.ext
    intro U
    have hUmap : (coordinateSwapTilingMap U).centres =
        coordinateSwap '' (U.centres : Set Tiling.Plane) := by
      rfl
    constructor
    · intro hUS
      have hUSσ : coordinateSwapTilingMap U ∈
          orbitHull (coordinateSwapTilingMap S) := by
        apply (coordinateSwap_orbitHull_iff hSmap hUmap).mp
        exact hUS
      have hUTσ : coordinateSwapTilingMap U ∈ orbitHull Tσ := by
        rw [hHullSσ] at hUSσ
        exact hUSσ
      exact (coordinateSwap_orbitHull_iff hTσ hUmap).mpr hUTσ
    · intro hUT
      have hUTσ : coordinateSwapTilingMap U ∈ orbitHull Tσ := by
        apply (coordinateSwap_orbitHull_iff hTσ hUmap).mp
        exact hUT
      have hUSσ : coordinateSwapTilingMap U ∈
          orbitHull (coordinateSwapTilingMap S) := by
        rw [hHullSσ]
        exact hUTσ
      exact (coordinateSwap_orbitHull_iff hSmap hUmap).mpr hUSσ

end Tiling.AxisParallel.Continuous
