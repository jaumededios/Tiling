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

open MeasureTheory Set
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

/-- Translating all placement vectors translates their geometric carrier by the same vector. -/
theorem translationCarrier_vadd
    (K : PolygonalRegion) (a : Plane) (S : Set Plane) :
    K.translationCarrier (a +ᵥ S) = a +ᵥ K.translationCarrier S := by
  ext x
  constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    obtain ⟨s, hs, rfl⟩ := ht
    refine ⟨y + s, ⟨y, hy, s, hs, rfl⟩, ?_⟩
    simp only [vadd_eq_add]
    abel
  · rintro ⟨z, ⟨y, hy, s, hs, rfl⟩, rfl⟩
    refine ⟨y, hy, a + s, ⟨s, hs, rfl⟩, ?_⟩
    simp only [vadd_eq_add]
    abel

/-- The carrier defined using lattice translations is the real translation carrier of their
embedded image. -/
theorem integerTranslationCarrier_eq_translationCarrier_image
    (K : PolygonalRegion) (S : Set IntegerPlane) :
    K.integerTranslationCarrier S = K.translationCarrier (integerPoint '' S) := by
  ext x
  constructor
  · rintro ⟨y, hy, t, ht, rfl⟩
    exact ⟨y, hy, integerPoint t, ⟨t, ht, rfl⟩, rfl⟩
  · rintro ⟨y, hy, _, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨y, hy, t, ht, rfl⟩

/-- A real period of an integer-translation carrier becomes the corresponding discrete period of
every raster signature carrier. -/
theorem signatureCarrier_periodic_of_integerTranslationCarrier
    (K : PolygonalRegion) {S : Set IntegerPlane} {w : IntegerPlane}
    (hperiod : SetPeriodicBy (K.integerTranslationCarrier S) (integerPoint w))
    (u : Plane) :
    DiscretePeriodicBy (discreteCarrier (K.signature u) S) w := by
  intro q
  rw [← K.mem_integerTranslationCarrier_iff_mem_discreteCarrier_signature S
      (u := u) (x := u + integerPoint (q + w)) (q := q + w) rfl,
    ← K.mem_integerTranslationCarrier_iff_mem_discreteCarrier_signature S
      (u := u) (x := u + integerPoint q) (q := q) rfl]
  simpa only [integerPoint_add, add_assoc] using hperiod (u + integerPoint q)

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

/-- For an integer-vertex polygonal monotile, the common real sliding line has a nonzero integer
direction.  In the one-plate case every direction stabilizes the unique carrier.  Otherwise two
applications of the contact-line vertex theorem produce distinct placed vertices in one plate;
their difference is both parallel to the sliding line and integral. -/
theorem Tiles.exists_integerSlidingDirection
    {K : PolygonalRegion} (hK : K.HasIntegerVertices)
    {T : Set Plane} (hT : K.Tiles T) :
    ∃ w : IntegerPlane, w ≠ 0 ∧
      (K.polygonalProtoTiling T).IsSlidingDirection (integerPoint w) := by
  classical
  let A := K.polygonalProtoTiling T
  by_cases hplates : Subsingleton A.Plate
  · let w : IntegerPlane := ![1, 0]
    have hw : w ≠ 0 := by
      intro hw
      have := congrArg (fun z : IntegerPlane ↦ z 0) hw
      norm_num [w] at this
    refine ⟨w, hw, ?_⟩
    refine ⟨fun hwzero ↦
      hw (integerPoint_injective (hwzero.trans integerPoint_zero.symm)), ?_⟩
    intro C r
    have hcarrier : A.plateCarrier C = Set.univ := by
      rw [← A.iUnion_plateCarrier_eq_univ hT]
      ext x
      constructor
      · intro hx
        exact Set.mem_iUnion.mpr ⟨C, hx⟩
      · intro hx
        obtain ⟨D, hxD⟩ := Set.mem_iUnion.mp hx
        simpa only [hplates.elim D C] using hxD
    rw [AddAction.mem_stabilizer_iff, hcarrier]
    simp
  · obtain ⟨v, hv⟩ := A.exists_isSlidingDirection hT
    obtain ⟨C, D, hCD, x, hxC, hxD⟩ :=
      A.exists_distinct_plate_carrier_contact hT hplates
    obtain ⟨i, t, ht, hi⟩ :=
      A.exists_placedVertex_on_invariant_contact_line hT hv hCD hxC hxD
    let x' : Plane := (t + 1) • v +ᵥ x
    have hx'C : x' ∈ A.plateCarrier C := by
      rw [← hv.vadd_plateCarrier C (t + 1)]
      exact ⟨x, hxC, rfl⟩
    have hx'D : x' ∈ A.plateCarrier D := by
      rw [← hv.vadd_plateCarrier D (t + 1)]
      exact ⟨x, hxD, rfl⟩
    obtain ⟨j, s, hs, hj⟩ :=
      A.exists_placedVertex_on_invariant_contact_line hT hv hCD hx'C hx'D
    let p : Plane := t • v +ᵥ x
    let p' : Plane := s • v +ᵥ x'
    let u : Plane := -i.1.1.1 +ᵥ p
    let u' : Plane := -j.1.1.1 +ᵥ p'
    have hu : u ∈ vertexSet K.support := by
      change p ∈ A.placedVertexSet (i : A.placements) at hi
      change p ∈ i.1.1.1 +ᵥ vertexSet K.support at hi
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hi
      exact hi
    have hu' : u' ∈ vertexSet K.support := by
      change p' ∈ A.placedVertexSet (j : A.placements) at hj
      change p' ∈ j.1.1.1 +ᵥ vertexSet K.support at hj
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hj
      exact hj
    have hiComp : A.vertexGraph.connectedComponentMk (i : A.placements) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C (i : A.placements)).mp i.2
    have hjComp : A.vertexGraph.connectedComponentMk (j : A.placements) = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C (j : A.placements)).mp j.2
    have hijPlate : A.SamePlate (i : A.placements) (j : A.placements) := by
      rw [A.samePlate_iff_component_eq]
      exact hiComp.trans hjComp.symm
    have htranslations : j.1.1.1 - i.1.1.1 ∈ integerLattice :=
      samePlate_translation_sub_mem_integerLattice hK hijPlate
    have hvertices : u' - u ∈ integerLattice :=
      AddSubgroup.sub_mem integerLattice (hK u' hu') (hK u hu)
    have hpint : p' - p ∈ integerLattice := by
      have hsum := AddSubgroup.add_mem integerLattice htranslations hvertices
      convert hsum using 1
      simp only [u, u', vadd_eq_add]
      abel
    have hpdiff : p' - p = (s + 1) • v := by
      simp only [p, p', x', vadd_eq_add, add_smul]
      module
    have hsone : s + 1 ≠ 0 := by linarith
    have hpne : p' - p ≠ 0 := by
      rw [hpdiff]
      exact smul_ne_zero hsone hv.ne_zero
    obtain ⟨w, hwpoint⟩ := mem_integerLattice_iff.mp hpint
    have hw : w ≠ 0 := by
      intro hw
      apply hpne
      rw [← hwpoint, hw, integerPoint_zero]
    refine ⟨w, hw, ?_⟩
    refine ⟨fun hwzero ↦
      hw (integerPoint_injective (hwzero.trans integerPoint_zero.symm)), ?_⟩
    intro E r
    have hwparallel : integerPoint w = (s + 1) • v := hwpoint.trans hpdiff
    rw [hwparallel, smul_smul]
    exact hv.invariant E (r * (s + 1))

/-- Translation vectors of one old plate after applying its assigned component shift. -/
def shiftedContinuousPlateTranslations
    (K : PolygonalRegion) (T : Set Plane) (v : Plane)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ)
    (C : (K.polygonalProtoTiling T).Plate) : Set Plane :=
  shift C • v +ᵥ K.continuousPlateTranslations T C

/-- Shifting one plate's translation vectors shifts its geometric carrier by the same amount. -/
theorem translationCarrier_shiftedContinuousPlateTranslations
    (K : PolygonalRegion) (T : Set Plane) (v : Plane)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ)
    (C : (K.polygonalProtoTiling T).Plate) :
    K.translationCarrier (K.shiftedContinuousPlateTranslations T v shift C) =
      shift C • v +ᵥ (K.polygonalProtoTiling T).plateCarrier C := by
  rw [shiftedContinuousPlateTranslations, K.translationCarrier_vadd,
    K.plateCarrier_eq_translationCarrier]

/-- A sliding certificate supplies the advertised period of each plate carrier. -/
theorem IsSlidingDirection.setPeriodicBy_plateCarrier
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (C : (K.polygonalProtoTiling T).Plate) :
    SetPeriodicBy ((K.polygonalProtoTiling T).plateCarrier C) v := by
  intro x
  have hcarrier := hv.vadd_plateCarrier C 1
  have hmem := congrArg (fun S : Set Plane ↦ x + v ∈ S) hcarrier
  simp only [one_smul, Set.mem_vadd_set_iff_neg_vadd_mem,
    vadd_eq_add] at hmem
  have hcancel : -v + (x + v) = x := by abel
  rw [hcancel] at hmem
  exact eq_iff_iff.mp hmem.symm

/-- Component shifting and a further common translation preserve the integer sliding period of
each old plate carrier. -/
theorem IsSlidingDirection.setPeriodicBy_translatedShiftedPlateCarrier
    {K : PolygonalRegion} {T : Set Plane} {v a : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ)
    (C : (K.polygonalProtoTiling T).Plate) :
    SetPeriodicBy
      (K.translationCarrier
        (a +ᵥ K.shiftedContinuousPlateTranslations T v shift C)) v := by
  rw [K.translationCarrier_vadd,
    K.translationCarrier_shiftedContinuousPlateTranslations]
  exact setPeriodicBy_vadd a
    (setPeriodicBy_vadd (shift C • v)
      (PolygonalRegion.IsSlidingDirection.setPeriodicBy_plateCarrier hv C))

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

/-- Component shifting is injective on all old monotile placements.  If two placements from
different plates were identified, the common shifted tile would have nonempty interior inside two
almost-everywhere disjoint invariant plate carriers. -/
theorem IsSlidingDirection.shiftedVertex_injective
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (hT : K.Tiles T)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) :
    Function.Injective
      ((K.polygonalProtoTiling T).shiftedVertex v shift) := by
  intro i j hij
  let A := K.polygonalProtoTiling T
  let C := A.vertexGraph.connectedComponentMk i
  let D := A.vertexGraph.connectedComponentMk j
  by_cases hCD : C = D
  · exact A.shiftedVertex_injective_of_component_eq v shift hCD hij
  have htileEq :
      placedTile A.prototiles (A.shiftedPlacement v shift i) =
        placedTile A.prototiles (A.shiftedPlacement v shift j) := by
    congr 1
    exact congrArg Subtype.val hij
  have htileNonempty :
      (placedTile A.prototiles (A.shiftedPlacement v shift i)).Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    refine ⟨(A.shiftedPlacement v shift i).1 + x, ?_⟩
    change (A.shiftedPlacement v shift i).1 + x ∈
      (A.shiftedPlacement v shift i).1 +ᵥ K.support
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hx
  have hinterior :
      (interior (placedTile A.prototiles
        (A.shiftedPlacement v shift i))).Nonempty :=
    (A.isPolygonal_placedTile (A.shiftedPlacement v shift i)).interior_nonempty
      htileNonempty
  obtain ⟨x, hx⟩ := hinterior
  have hsubsetC : placedTile A.prototiles (A.shiftedPlacement v shift i) ⊆
      A.plateCarrier C := by
    rw [A.placedTile_shiftedPlacement]
    intro y hy
    rw [← hv.vadd_plateCarrier C (shift C)]
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, A.placedTile_subset_plateCarrier i hz, rfl⟩
  have hsubsetD : placedTile A.prototiles (A.shiftedPlacement v shift i) ⊆
      A.plateCarrier D := by
    rw [htileEq, A.placedTile_shiftedPlacement]
    intro y hy
    rw [← hv.vadd_plateCarrier D (shift D)]
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, A.placedTile_subset_plateCarrier j hz, rfl⟩
  have hxC : x ∈ interior (A.plateCarrier C) := interior_mono hsubsetC hx
  have hxD : x ∈ interior (A.plateCarrier D) := interior_mono hsubsetD hx
  have hpositive : 0 < volume
      (interior (A.plateCarrier C) ∩ interior (A.plateCarrier D)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨x, hxC, hxD⟩
  have hzero : volume
      (interior (A.plateCarrier C) ∩ interior (A.plateCarrier D)) = 0 :=
    measure_mono_null (Set.inter_subset_inter interior_subset interior_subset)
      (A.plateCarrier_aedisjoint hT hCD).eq
  exact (ne_of_gt hpositive hzero).elim

/-- The shifted translation sets of distinct old plates remain disjoint. -/
theorem IsSlidingDirection.shiftedContinuousPlateTranslations_pairwiseDisjoint
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (hT : K.Tiles T)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) :
    Set.PairwiseDisjoint Set.univ
      (K.shiftedContinuousPlateTranslations T v shift) := by
  intro C _ D _ hCD
  change Disjoint (K.shiftedContinuousPlateTranslations T v shift C)
    (K.shiftedContinuousPlateTranslations T v shift D)
  rw [Set.disjoint_left]
  intro t htC htD
  obtain ⟨s, ⟨hsT, hsC⟩, hsEq⟩ := htC
  obtain ⟨r, ⟨hrT, hrD⟩, hrEq⟩ := htD
  let i : (K.polygonalProtoTiling T).placements := ⟨(s, ()), hsT⟩
  let j : (K.polygonalProtoTiling T).placements := ⟨(r, ()), hrT⟩
  have hshifted : (K.polygonalProtoTiling T).shiftedVertex v shift i =
      (K.polygonalProtoTiling T).shiftedVertex v shift j := by
    apply Subtype.ext
    apply Prod.ext
    · change s + shift ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i) • v =
        r + shift ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk j) • v
      rw [show (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i = C by
        simpa only [i] using hsC]
      rw [show (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk j = D by
        simpa only [j] using hrD]
      change shift C • v + s = t at hsEq
      change shift D • v + r = t at hrEq
      calc
        s + shift C • v = shift C • v + s := add_comm _ _
        _ = t := hsEq
        _ = shift D • v + r := hrEq.symm
        _ = r + shift D • v := add_comm _ _
    · exact Subsingleton.elim _ _
  have hij :=
    PolygonalRegion.IsSlidingDirection.shiftedVertex_injective hv hT shift hshifted
  have hcomponents :
      (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i =
        (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk j :=
    congrArg
      (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk hij
  apply hCD
  calc
    C = (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i := by
      simpa only [i] using hsC.symm
    _ = (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk j := hcomponents
    _ = D := by simpa only [j] using hrD

/-- A certified sliding direction admits an explicit component shift whose new vertex-contact
graph is connected.  The certificate still refers to the old plates, so downstream arguments can
transport each plate separately. -/
theorem IsSlidingDirection.exists_connected_shiftedContinuousTranslations
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (hT : K.Tiles T) :
    ∃ shift : (K.polygonalProtoTiling T).Plate → ℝ,
      K.Tiles (K.shiftedContinuousTranslations T v shift) ∧
      (K.polygonalProtoTiling
        (K.shiftedContinuousTranslations T v shift)).vertexGraph.Connected := by
  obtain ⟨shift, hshifted, hconnected⟩ :=
    PolygonalProtoTiling.IsSlidingDirection.exists_connected_component_shift
      (K.polygonalProtoTiling T) hv hT
  refine ⟨shift, ?_, ?_⟩
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

/-- A monotile tiling admits an explicit connected component shift. -/
theorem Tiles.exists_connected_shiftedContinuousTranslations
    {K : PolygonalRegion} {T : Set Plane} (hT : K.Tiles T) :
    ∃ (v : Plane)
        (_hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
        (shift : (K.polygonalProtoTiling T).Plate → ℝ),
      K.Tiles (K.shiftedContinuousTranslations T v shift) ∧
      (K.polygonalProtoTiling
        (K.shiftedContinuousTranslations T v shift)).vertexGraph.Connected := by
  obtain ⟨v, hv⟩ := (K.polygonalProtoTiling T).exists_isSlidingDirection hT
  obtain ⟨shift, htiles, hconnected⟩ :=
    PolygonalRegion.IsSlidingDirection.exists_connected_shiftedContinuousTranslations hv hT
  exact ⟨v, hv, shift, htiles, hconnected⟩

/-- Integer-vertex monotile tilings have a connected component shift along a nonzero integer
direction, while retaining the old continuous plate decomposition. -/
theorem Tiles.exists_integer_connected_shiftedContinuousTranslations
    {K : PolygonalRegion} (hK : K.HasIntegerVertices)
    {T : Set Plane} (hT : K.Tiles T) :
    ∃ (w : IntegerPlane) (_hw : w ≠ 0)
        (_hv : (K.polygonalProtoTiling T).IsSlidingDirection (integerPoint w))
        (shift : (K.polygonalProtoTiling T).Plate → ℝ),
      K.Tiles (K.shiftedContinuousTranslations T (integerPoint w) shift) ∧
      (K.polygonalProtoTiling
        (K.shiftedContinuousTranslations T (integerPoint w) shift)).vertexGraph.Connected := by
  obtain ⟨w, hw, hv⟩ := hT.exists_integerSlidingDirection hK
  obtain ⟨shift, htiles, hconnected⟩ :=
    PolygonalRegion.IsSlidingDirection.exists_connected_shiftedContinuousTranslations hv hT
  exact ⟨w, hw, hv, shift, htiles, hconnected⟩

end PolygonalRegion

end Tiling.RationalPolygonal
