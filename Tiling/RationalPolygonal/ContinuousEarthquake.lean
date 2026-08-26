import Tiling.RationalPolygonal.EarthquakeUniform
import Tiling.RationalPolygonal.Raster

set_option linter.style.header false

/-!
# Continuous plates and component shifts

This file retains the plate-to-translation-set correspondence which is deliberately forgotten by
the existential integer-reduction endpoint.  It is the continuous side of the compatibility step
in the proof of Theorem 1.2 of de Dios Pont--Grebík--Greenfeld--Madrid: each vertex-connected plate
is represented by its original translations, and shifting components translates precisely that
set of vectors.
-/

open Set
open scoped Pointwise

namespace Tiling.RationalPolygonal

namespace PolygonalRegion

/-- Translation vectors whose placements belong to one continuous vertex-connected plate. -/
def continuousPlateTranslations (K : PolygonalRegion) (T : Set Plane)
    (C : (K.polygonalProtoTiling T).Plate) : Set Plane :=
  {t | ∃ ht : t ∈ T,
    (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk
      (⟨(t, ()), ht⟩ : (K.polygonalProtoTiling T).placements) = C}

@[simp]
theorem mem_continuousPlateTranslations_iff
    {K : PolygonalRegion} {T : Set Plane}
    {C : (K.polygonalProtoTiling T).Plate} {t : Plane} :
    t ∈ K.continuousPlateTranslations T C ↔
      ∃ ht : t ∈ T,
        (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk
          (⟨(t, ()), ht⟩ : (K.polygonalProtoTiling T).placements) = C :=
  Iff.rfl

/-- Every placement translation belongs to the translation set of its own plate. -/
theorem mem_continuousPlateTranslations_mk
    {K : PolygonalRegion} {T : Set Plane}
    (i : (K.polygonalProtoTiling T).placements) :
    i.1.1 ∈ K.continuousPlateTranslations T
      ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i) := by
  refine ⟨i.2, ?_⟩
  congr 1

/-- The continuous plate translation sets partition the original translation set. -/
theorem iUnion_continuousPlateTranslations
    (K : PolygonalRegion) (T : Set Plane) :
    (⋃ C : (K.polygonalProtoTiling T).Plate,
      K.continuousPlateTranslations T C) = T := by
  ext t
  constructor
  · rintro ht
    obtain ⟨C, htC⟩ := Set.mem_iUnion.mp ht
    exact Classical.choose htC
  · intro ht
    let i : (K.polygonalProtoTiling T).placements := ⟨(t, ()), ht⟩
    exact Set.mem_iUnion.mpr
      ⟨(K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i,
        by simpa only [i] using K.mem_continuousPlateTranslations_mk i⟩

/-- Distinct continuous plates have disjoint translation sets. -/
theorem continuousPlateTranslations_pairwiseDisjoint
    (K : PolygonalRegion) (T : Set Plane) :
    Set.PairwiseDisjoint Set.univ
      (fun C : (K.polygonalProtoTiling T).Plate ↦
        K.continuousPlateTranslations T C) := by
  intro C _ D _ hCD
  change Disjoint (K.continuousPlateTranslations T C)
    (K.continuousPlateTranslations T D)
  rw [Set.disjoint_left]
  intro t htC htD
  obtain ⟨ht, hiC⟩ := htC
  obtain ⟨ht', hiD⟩ := htD
  apply hCD
  rw [← hiC, ← hiD]

/-- Carrier covered by translating a polygonal region along an arbitrary real translation set. -/
def translationCarrier (K : PolygonalRegion) (S : Set Plane) : Set Plane :=
  {x | ∃ y ∈ K.support, ∃ t ∈ S, x = y + t}

@[simp]
theorem mem_translationCarrier_iff
    {K : PolygonalRegion} {S : Set Plane} {x : Plane} :
    x ∈ K.translationCarrier S ↔
      ∃ y ∈ K.support, ∃ t ∈ S, x = y + t :=
  Iff.rfl

/-- The geometric carrier of a continuous plate is the carrier of its translation set. -/
theorem plateCarrier_eq_translationCarrier
    (K : PolygonalRegion) (T : Set Plane)
    (C : (K.polygonalProtoTiling T).Plate) :
    (K.polygonalProtoTiling T).plateCarrier C =
      K.translationCarrier (K.continuousPlateTranslations T C) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hiC, hxi⟩ :=
      (K.polygonalProtoTiling T).mem_plateCarrier_iff.mp hx
    change x ∈ i.1.1 +ᵥ K.support at hxi
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxi
    refine ⟨-i.1.1 +ᵥ x, hxi, i.1.1, ?_, ?_⟩
    · refine ⟨i.2, ?_⟩
      have hiCeq : (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i = C :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mp hiC
      rw [← hiCeq]
    · simp only [vadd_eq_add]
      abel
  · rintro ⟨y, hy, t, ⟨ht, hiC⟩, rfl⟩
    apply (K.polygonalProtoTiling T).mem_plateCarrier_iff.mpr
    let i : (K.polygonalProtoTiling T).placements := ⟨(t, ()), ht⟩
    refine ⟨i, ?_, ?_⟩
    · change i ∈ C.supp
      apply (SimpleGraph.ConnectedComponent.mem_supp_iff C i).mpr
      simpa only [i] using hiC
    · change y + t ∈ t +ᵥ K.support
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      convert hy using 1
      simp only [vadd_eq_add]
      abel

/-- Translation vectors of one old plate after applying its assigned component shift. -/
def shiftedContinuousPlateTranslations
    (K : PolygonalRegion) (T : Set Plane) (v : Plane)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ)
    (C : (K.polygonalProtoTiling T).Plate) : Set Plane :=
  shift C • v +ᵥ K.continuousPlateTranslations T C

/-- The translation set obtained by independently shifting every continuous plate. -/
def shiftedContinuousTranslations
    (K : PolygonalRegion) (T : Set Plane) (v : Plane)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) : Set Plane :=
  ⋃ C, K.shiftedContinuousPlateTranslations T v shift C

@[simp]
theorem mem_shiftedContinuousTranslations_iff
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    {shift : (K.polygonalProtoTiling T).Plate → ℝ} {t : Plane} :
    t ∈ K.shiftedContinuousTranslations T v shift ↔
      ∃ C, t ∈ K.shiftedContinuousPlateTranslations T v shift C := by
  simp only [shiftedContinuousTranslations, Set.mem_iUnion]

/-- The monotile placements of the shifted translation set are exactly the generic component
shift construction. -/
theorem placements_shiftedContinuousTranslations
    (K : PolygonalRegion) (T : Set Plane) (v : Plane)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) :
    K.placements (K.shiftedContinuousTranslations T v shift) =
      ((K.polygonalProtoTiling T).shiftComponents v shift).placements := by
  ext p
  constructor
  · intro hp
    obtain ⟨C, s, hsC, hsp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hsT, hiC⟩ := hsC
    let i : (K.polygonalProtoTiling T).placements := ⟨(s, ()), hsT⟩
    refine ⟨i, ?_⟩
    apply Prod.ext
    · change s + shift ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i) • v = p.1
      rw [show (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i = C by
        simpa only [i] using hiC]
      change shift C • v + s = p.1 at hsp
      simpa only [add_comm] using hsp
    · exact Subsingleton.elim _ _
  · rintro ⟨i, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i, ?_⟩
    change ((K.polygonalProtoTiling T).shiftedPlacement v shift i).1 ∈
      shift ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i) • v +ᵥ
        K.continuousPlateTranslations T
          ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    convert K.mem_continuousPlateTranslations_mk i using 1
    simp only [PolygonalProtoTiling.shiftedPlacement_translation, vadd_eq_add]
    module

/-- A component shift of a monotile tiling is represented by the corresponding shifted real
translation set. -/
theorem IsSlidingDirection.tiles_shiftedContinuousTranslations
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (hT : K.Tiles T)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) :
    K.Tiles (K.shiftedContinuousTranslations T v shift) := by
  change IsTiling K.prototileFamily
    (K.placements (K.shiftedContinuousTranslations T v shift))
  rw [K.placements_shiftedContinuousTranslations]
  simpa using
    (PolygonalProtoTiling.IsSlidingDirection.isTiling_shiftComponents
      (K.polygonalProtoTiling T) hv hT shift)

/-- A monotile tiling admits a component shift whose translation set is explicit and whose new
vertex-contact graph is connected.  The returned sliding certificate still refers to the old
plates, so downstream arguments can transport each plate separately. -/
theorem Tiles.exists_connected_shiftedContinuousTranslations
    {K : PolygonalRegion} {T : Set Plane} (hT : K.Tiles T) :
    ∃ (v : Plane)
        (_hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
        (shift : (K.polygonalProtoTiling T).Plate → ℝ),
      K.Tiles (K.shiftedContinuousTranslations T v shift) ∧
      (K.polygonalProtoTiling
        (K.shiftedContinuousTranslations T v shift)).vertexGraph.Connected := by
  obtain ⟨v, hv, shift, hshifted, hconnected⟩ :=
    (K.polygonalProtoTiling T).exists_connected_shift hT
  refine ⟨v, hv, shift, ?_, ?_⟩
  · change IsTiling K.prototileFamily
      (K.placements (K.shiftedContinuousTranslations T v shift))
    rw [K.placements_shiftedContinuousTranslations]
    simpa using hshifted
  have hplacements := K.placements_shiftedContinuousTranslations T v shift
  let B := K.polygonalProtoTiling (K.shiftedContinuousTranslations T v shift)
  let B' := (K.polygonalProtoTiling T).shiftComponents v shift
  let e : B.placements ≃ B'.placements := Equiv.setCongr hplacements
  let φ : B.vertexGraph ≃g B'.vertexGraph := {
    toEquiv := e
    map_rel_iff' := by
      intro i j
      have hei : (e i : Placement Plane Unit) = (i : Placement Plane Unit) := rfl
      have hej : (e j : Placement Plane Unit) = (j : Placement Plane Unit) := rfl
      have hvertex_i : B'.placedVertexSet (e i) = B.placedVertexSet i := by
        change (e i : Placement Plane Unit).1 +ᵥ
            vertexSet (K.prototileFamily (e i : Placement Plane Unit).2).support =
          (i : Placement Plane Unit).1 +ᵥ
            vertexSet (K.prototileFamily (i : Placement Plane Unit).2).support
        rw [hei]
      have hvertex_j : B'.placedVertexSet (e j) = B.placedVertexSet j := by
        change (e j : Placement Plane Unit).1 +ᵥ
            vertexSet (K.prototileFamily (e j : Placement Plane Unit).2).support =
          (j : Placement Plane Unit).1 +ᵥ
            vertexSet (K.prototileFamily (j : Placement Plane Unit).2).support
        rw [hej]
      rw [B.vertexGraph_adj, B'.vertexGraph_adj]
      constructor
      · rintro ⟨hij, hvertex⟩
        refine ⟨fun heq ↦ hij (congrArg e heq), ?_⟩
        simpa only [PolygonalProtoTiling.VertexConnected,
          hvertex_i, hvertex_j] using hvertex
      · rintro ⟨hij, hvertex⟩
        refine ⟨fun heq ↦ hij (e.injective heq), ?_⟩
        simpa only [PolygonalProtoTiling.VertexConnected,
          hvertex_i, hvertex_j] using hvertex
  }
  exact φ.connected_iff.mpr hconnected

end PolygonalRegion

end Tiling.RationalPolygonal
