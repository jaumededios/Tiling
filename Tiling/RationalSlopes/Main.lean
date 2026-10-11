import Tiling.RationalSlopes.MinimalStructure
import Tiling.RationalSlopes.FLCMain
import Tiling.RationalSlopes.SlicesAndColumns
import Tiling.Topology.TilingHull

set_option autoImplicit false
set_option linter.style.header false
open Function Filter MeasureTheory Set
open scoped Pointwise Topology
noncomputable section
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
open Tiling.Polygonal.Topology

namespace Tiling.RationalSlopes

private theorem packing_mono {K : PolygonalRegion} {S T : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T) :
    IsPacking K.prototileFamily (K.placements S) :=
  hp.mono (fun _ h => hST h)

private theorem part_subset {A : Set Plane}
    (d : Tiling.RationalPolygonal.WeakPeriodicDecomposition A)
    (i : Fin d.numberOfParts) : d.part i ⊆ A := by
  intro x hx
  rw [← d.iUnion_parts]
  exact mem_iUnion.mpr ⟨i, hx⟩

/-- Flatten the actual decompositions, retaining both levels of disjointness. -/
private theorem weaklyPeriodic_iUnion {ι : Type} [Fintype ι]
    (A : ι → Set Plane) (hA : ∀ i, Tiling.RationalPolygonal.WeaklyPeriodic (A i))
    (hdisj : PairwiseDisjoint univ A) :
    Tiling.RationalPolygonal.WeaklyPeriodic (⋃ i, A i) := by
  classical
  let d := fun i => Classical.choice (hA i)
  let J := Σ i, Fin (d i).numberOfParts
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hD : Pairwise (fun j k : J =>
      Disjoint ((d j.1).part j.2) ((d k.1).part k.2)) := by
    intro ⟨a, b⟩ ⟨c, f⟩ hne
    by_cases hac : a = c
    · subst c
      exact (d a).pairwiseDisjoint (mem_univ _) (mem_univ _)
        (fun hbf => hne (by cases hbf; rfl))
    · exact (hdisj (mem_univ _) (mem_univ _) hac).mono
        (part_subset _ _) (part_subset _ _)
  refine ⟨{
    numberOfParts := Fintype.card J
    part := fun j => (d (e j).1).part (e j).2
    period := fun j => (d (e j).1).period (e j).2
    period_ne_zero := fun j => (d (e j).1).period_ne_zero (e j).2
    periodic_part := fun j => (d (e j).1).periodic_part (e j).2
    pairwiseDisjoint := ?_
    iUnion_parts := ?_ }⟩
  · intro j _ k _ hjk
    exact hD (fun h => hjk (e.injective h))
  · ext x
    constructor
    · intro hx
      obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨(e j).1, part_subset _ _ hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [← (d i).iUnion_parts] at hi
      obtain ⟨j, hj⟩ := mem_iUnion.mp hi
      exact mem_iUnion.mpr ⟨e.symm ⟨i, j⟩, by
        rw [e.apply_symm_apply]
        exact hj⟩

private theorem singly_weaklyPeriodic {A : Set Plane} {q : Plane}
    (hq : q ≠ 0) (hp : q ∈ periodGroup A) :
    Tiling.RationalPolygonal.WeaklyPeriodic A := by
  refine ⟨{
    numberOfParts := 1
    part := fun _ => A
    period := fun _ => q
    period_ne_zero := fun _ => hq
    periodic_part := ?_
    pairwiseDisjoint := ?_
    iUnion_parts := by exact iUnion_const A }⟩
  · intro i x
    have heq : q +ᵥ A = A := hp
    constructor
    · intro hx
      have hx' : q + x ∈ q +ᵥ A := by rw [heq]; simpa [add_comm] using hx
      simpa [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx'
    · intro hx
      rw [← heq]
      exact mem_vadd_set.mpr ⟨x, hx, by simp [add_comm]⟩
  · intro i _ j _ hij
    exact (hij (Subsingleton.elim _ _)).elim

theorem minimal_wholePlane_weaklyPeriodic :
∀ (K : PolygonalRegion) (T : Set Plane), HasRationalSlopes K →
    TilesOn K T Set.univ → IsMinimalTiling K T Set.univ →
      Tiling.RationalPolygonal.WeaklyPeriodic T := by
  intro K T hK htile hmin
  obtain ⟨d⟩ := minimal_wholePlane_structure K T hK htile hmin
  have hpiece : ∀ j, Tiling.RationalPolygonal.WeaklyPeriodic (d.piece j) := by
    intro j
    obtain ⟨U, hU, _⟩ := d.piece_minimal j
    have ht : TilesOn K (d.piece j) (regularSupport K (d.piece j)) := by
      simpa [hU] using U.tilesOn
    obtain ⟨ho, hr⟩ := regularSupport_isRegularOpen K (d.piece j)
    exact minimal_flc_weaklyPeriodic hK (d.piece_hasFLC j) ht ho hr
      (d.piece_carrier_periodic j) (d.piece_minimal j)
  obtain ⟨q, _, hq, hp⟩ := unionColumns_singlyPeriodic d.direction_oneDim
    d.aggregate_isUnionColumns
  let A : Option (Fin d.numberOfPieces) → Set Plane :=
    fun i => i.elim d.columnAggregate d.piece
  have hA : ∀ i, Tiling.RationalPolygonal.WeaklyPeriodic (A i) := by
    intro i
    cases i with
    | none => exact singly_weaklyPeriodic hq hp
    | some j => exact hpiece j
  have hd : PairwiseDisjoint univ A := by
    intro i _ j _ hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact d.column_disjoint_piece j
    | some i =>
      cases j with
      | none => exact (d.column_disjoint_piece i).symm
      | some j =>
        exact d.pieces_pairwiseDisjoint (mem_univ _) (mem_univ _)
          (fun h => hij (congrArg Option.some h))
  have hu : (⋃ i, A i) = T := by
    calc
      (⋃ i, A i) = d.columnAggregate ∪ (⋃ j, d.piece j) := by
        ext x
        simp [A, Option.exists]
      _ = T := d.centres_partition
  simpa [hu] using weaklyPeriodic_iUnion A hA hd

private theorem openUnion_iUnion {ι : Type} (K : PolygonalRegion)
    (A : ι → Set Plane) : openUnion K (⋃ i, A i) = ⋃ i, openUnion K (A i) := by
  ext x
  simp only [openUnion, mem_iUnion, Subtype.exists, mem_iUnion]
  constructor
  · rintro ⟨s, ⟨i, hi⟩, hx⟩
    exact ⟨i, s, hi, hx⟩
  · rintro ⟨i, s, hi, hx⟩
    exact ⟨s, ⟨i, hi⟩, hx⟩

private theorem tile_subset_carrier {K : PolygonalRegion} {S D : Set Plane}
    (ho : IsOpen D) (hr : interior (closure D) = D) (ht : TilesOn K S D)
    {s : Plane} (hs : s ∈ S) : s +ᵥ K.openCarrier ⊆ D := by
  rw [← regularSupport_eq_of_tilesOn ho hr ht]
  apply subset_trans (subset_iUnion (fun t : S => (t : Plane) +ᵥ K.openCarrier) ⟨s, hs⟩)
  exact (isOpen_iUnion fun t : S =>
    (Homeomorph.addLeft (t : Plane)).isOpenMap _ isOpen_interior).subset_interior_closure

private theorem replacement_union {ι : Type} [Fintype ι]
    {K : PolygonalRegion} (A S : ι → Set Plane)
    (hA : TilesOn K (⋃ i, A i) univ)
    (hAd : PairwiseDisjoint univ A)
    (hS : ∀ i, TilesOn K (S i) (regularSupport K (A i)))
    (hper : ∀ i, IsLatticePeriodic (S i)) :
    TilesOn K (⋃ i, S i) univ ∧ IsQuasiPeriodic (⋃ i, S i) := by
  classical
  let D := fun i => regularSupport K (A i)
  have hAsub : ∀ i, A i ⊆ ⋃ i, A i := fun i => subset_iUnion A i
  have hpA : ∀ i, IsPacking K.prototileFamily (K.placements (A i)) :=
    fun i => packing_mono hA.2.1 (hAsub i)
  have hDt : ∀ i, TilesOn K (A i) (D i) :=
    fun i => tilesOn_regularSupport_of_packing (hpA i)
  have hDd : PairwiseDisjoint univ D := by
    intro i _ j _ hij
    exact regularSupport_disjoint_of_disjoint_subfamilies hA.2.1
      (hAsub i) (hAsub j) (hAd (mem_univ _) (mem_univ _) hij)
  have hsub : ∀ i, ∀ s ∈ S i, s +ᵥ K.openCarrier ⊆ D i := by
    intro i s hs
    obtain ⟨ho, hr⟩ := regularSupport_isRegularOpen K (A i)
    exact tile_subset_carrier ho hr (hS i) hs
  have hSd : PairwiseDisjoint univ S := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro s hsi hsj
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hsx : s + x ∈ s +ᵥ K.openCarrier :=
      mem_vadd_set.mpr ⟨x, hx, rfl⟩
    exact (disjoint_left.mp (hDd (mem_univ _) (mem_univ _) hij))
      (hsub i s hsi hsx) (hsub j s hsj hsx)
  have hpS : IsPacking K.prototileFamily (K.placements (⋃ i, S i)) := by
    apply (isPacking_iff_openCarrier_disjoint K _).mpr
    intro s hs t ht hst
    obtain ⟨i, hi⟩ := mem_iUnion.mp hs
    obtain ⟨j, hj⟩ := mem_iUnion.mp ht
    by_cases hij : i = j
    · subst j
      exact (isPacking_iff_openCarrier_disjoint K (S i)).mp (hS i).2.1 hi hj hst
    · exact (hDd (mem_univ _) (mem_univ _) hij).mono (hsub i s hi) (hsub j t hj)
  have htS : TilesOn K (⋃ i, S i) univ := by
    refine ⟨countable_iUnion (fun i => (hS i).1), hpS, ?_⟩
    have hsource : ∀ᵐ x ∂volume, ∀ i, x ∈ D i ↔ x ∈ openUnion K (A i) := by
      exact ae_all_iff.mpr (fun i => by
        simpa only [openUnion, mem_iUnion] using (hDt i).2.2)
    have htarget : ∀ᵐ x ∂volume, ∀ i, x ∈ D i ↔ x ∈ openUnion K (S i) := by
      exact ae_all_iff.mpr (fun i => by
        simpa only [openUnion, mem_iUnion] using (hS i).2.2)
    have hcover : ∀ᵐ x ∂volume, x ∈ univ ↔ x ∈ openUnion K (⋃ i, A i) := by
      simpa only [openUnion, mem_iUnion] using hA.2.2
    suffices h : ∀ᵐ x ∂volume, x ∈ univ ↔ x ∈ openUnion K (⋃ i, S i) by
      simpa only [openUnion, mem_iUnion] using h
    filter_upwards [hcover, hsource, htarget] with x hx hsrc htgt
    rw [openUnion_iUnion] at hx ⊢
    simp only [mem_iUnion] at hx ⊢
    exact hx.trans (exists_congr (fun i => (hsrc i).symm.trans (htgt i)))
  refine ⟨htS, ?_⟩
  let J := {i : ι // (S i).Nonempty}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, (fun j => S (e j).1),
    (fun j => ⟨(e j).2, hper (e j).1⟩), ?_, ?_⟩
  · intro j _ k _ hjk
    exact hSd (mem_univ _) (mem_univ _) (fun h => hjk (e.injective (Subtype.ext h)))
  · ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨(e j).1, hj⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      let j : J := ⟨i, ⟨x, hi⟩⟩
      exact mem_iUnion.mpr ⟨e.symm j, by simpa [j] using hi⟩

theorem exists_weaklyDoublyPeriodic_tiling :
∀ (K : PolygonalRegion) (T : Set Plane), HasRationalSlopes K →
    TilesOn K T Set.univ → ∃ S : Set Plane, TilesOn K S Set.univ ∧ IsQuasiPeriodic S := by
  intro K T hK htile
  have hclosed := (packing_centres_locallyFinite htile.2.1).2.2
  let t : TilingSpace K univ := ⟨⟨T, hclosed⟩, htile⟩
  obtain ⟨u, _, hu⟩ := exists_minimalTiling_in_hull t
  let U : Set Plane := u.centres
  have hUmin : IsMinimalTiling K U univ := ⟨u, rfl, hu⟩
  obtain ⟨d⟩ := minimal_wholePlane_structure K U hK u.tilesOn hUmin
  let A : Option (Fin d.numberOfPieces) → Set Plane :=
    fun i => i.elim d.columnAggregate d.piece
  have hunion : (⋃ i, A i) = U := by
    calc
      (⋃ i, A i) = d.columnAggregate ∪ (⋃ j, d.piece j) := by
        ext x
        simp [A, Option.exists]
      _ = U := d.centres_partition
  have hAd : PairwiseDisjoint univ A := by
    intro i _ j _ hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact d.column_disjoint_piece j
    | some i =>
      cases j with
      | none => exact (d.column_disjoint_piece i).symm
      | some j =>
        exact d.pieces_pairwiseDisjoint (mem_univ _) (mem_univ _)
          (fun h => hij (congrArg Option.some h))
  have hAtile : TilesOn K (⋃ i, A i) univ := by simpa [hunion] using u.tilesOn
  have hex : ∀ i, ∃ S : Set Plane,
      TilesOn K S (regularSupport K (A i)) ∧ IsLatticePeriodic S := by
    intro i
    have ht : TilesOn K (A i) (regularSupport K (A i)) :=
      tilesOn_regularSupport_of_packing
        (packing_mono hAtile.2.1 (subset_iUnion A i))
    obtain ⟨ho, hr⟩ := regularSupport_isRegularOpen K (A i)
    cases i with
    | none =>
      by_cases hempty : d.columnAggregate = ∅
      · refine ⟨∅, ?_, ?_⟩
        · simpa [A, hempty] using ht
        · obtain ⟨L, hL⟩ := d.aggregate_carrier_periodic
          refine ⟨L, ?_⟩
          intro q hq
          change q +ᵥ (∅ : Set Plane) = ∅
          simp
      · exact unionColumns_periodicReplacement d.direction_oneDim ht ho hr
          d.aggregate_carrier_periodic d.aggregate_isUnionColumns
    | some j =>
      obtain ⟨S, hS, hp, _⟩ := flc_exists_periodic_replacement hK
        (d.piece_hasFLC j) ht ho hr (d.piece_carrier_periodic j)
      exact ⟨S, hS, hp⟩
  choose S htS hper using hex
  exact ⟨⋃ i, S i, replacement_union A S hAtile hAd htS hper⟩



end Tiling.RationalSlopes
