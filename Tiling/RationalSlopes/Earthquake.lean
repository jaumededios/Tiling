import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.RationalSlopes.SlicesAndColumns
import Tiling.Geometry.PolygonalCarrier
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false
set_option linter.style.header false
open Function Filter MeasureTheory Set
open scoped Pointwise Topology
noncomputable section
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
open Tiling.RationalSlopes

namespace Tiling.RationalSlopes

def directionalSaturation (δ : Submodule ℝ Plane) (E : Set Plane) : Set Plane :=
  {x | ∃ y ∈ E, x - y ∈ δ}

def DirectionalOverlap (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (s t : Plane) : Prop :=
  ((s +ᵥ K.openCarrier) ∩ directionalSaturation δ (t +ᵥ K.openCarrier)).Nonempty

def earthquakeGraph (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : SimpleGraph T :=
  SimpleGraph.fromRel (fun s t => DirectionalOverlap K δ s.1 t.1)

abbrev EarthquakeComponent (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) := (earthquakeGraph K δ T).ConnectedComponent

def EarthquakeComponent.centres {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : Set Plane :=
  Subtype.val '' P.supp

def EarthquakeComponent.carrier {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : Set Plane :=
  regularSupport K P.centres

def noncolumnComponents (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Set (EarthquakeComponent K δ T) :=
  {P | ¬ IsCenterColumn K δ P.centres}

def columnPart (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) :
    Set Plane :=
  ⋃ P : {P : EarthquakeComponent K δ T // IsCenterColumn K δ P.centres}, P.1.centres

def IsIrreducibleDirectionalSubfamily (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T S : Set Plane) : Prop :=
  S.Nonempty ∧ S ⊆ T ∧ IsInvariantAlong (regularSupport K S) δ ∧
    ∀ U : Set Plane, U.Nonempty → U ⊆ S →
      IsInvariantAlong (regularSupport K U) δ → U = S

def HasDirectionalEarthquake (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) : Prop :=
  ∃ S : Set Plane, S.Nonempty ∧ S ⊆ T ∧ S ≠ T ∧
    IsInvariantAlong (regularSupport K S) δ

def HasNontrivialEarthquakeDecomposition (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) : Prop :=
  T = columnPart K δ T ∨
    ∃ P Q : EarthquakeComponent K δ T, P ≠ Q

def periodStepGroup (δ : Submodule ℝ Plane) (periodVec : Plane) : AddSubgroup Plane :=
  δ.toAddSubgroup ⊔ AddSubgroup.closure ({periodVec} : Set Plane)

def IsCommonCarrierPeriod (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (periodVec : Plane) : Prop :=
  periodVec ∉ δ ∧ periodVec ∈ periodGroup (regularSupport K (columnPart K δ T)) ∧
    ∀ P ∈ noncolumnComponents K δ T, periodVec ∈ periodGroup P.carrier

theorem directionalOverlap_comm :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (s t : Plane),
    DirectionalOverlap K δ s t ↔ DirectionalOverlap K δ t s
  := by
  intro K δ s t
  suffices h : ∀ s t : Plane, DirectionalOverlap K δ s t →
      DirectionalOverlap K δ t s from ⟨h s t, h t s⟩
  intro s t ⟨x, hxs, y, hyt, hxy⟩
  exact ⟨y, hyt, x, hxs, by simpa [neg_sub] using δ.neg_mem hxy⟩

private theorem component_centres_subset {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres ⊆ T := by
  rintro x ⟨s, _, rfl⟩
  exact s.property

private theorem component_centres_nonempty {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) : P.centres.Nonempty :=
  P.nonempty_supp.image Subtype.val

private theorem component_centres_disjoint {K : PolygonalRegion}
    {δ : Submodule ℝ Plane} {T : Set Plane}
    {P Q : EarthquakeComponent K δ T} (hPQ : P ≠ Q) : Disjoint P.centres Q.centres := by
  apply Set.disjoint_left.mpr
  rintro x ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
  have hst : t = s := Subtype.ext heq
  subst t
  exact hPQ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hs ht)

private theorem openUnion_open (K : PolygonalRegion) (S : Set Plane) :
    IsOpen (openUnion K S) :=
  isOpen_iUnion fun s => isOpen_interior.vadd (s : Plane)

private theorem openUnion_mono {K : PolygonalRegion} {A B : Set Plane}
    (hAB : A ⊆ B) : openUnion K A ⊆ openUnion K B := by
  intro x hx
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨⟨s, hAB s.property⟩, hs⟩

private theorem overlap_same_component {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {T : Set Plane} (P : EarthquakeComponent K δ T) {s t : T}
    (hs : s ∈ P.supp) (hov : DirectionalOverlap K δ s t) : t ∈ P.supp := by
  by_cases hst : s = t
  · simpa [← hst] using hs
  · exact P.mem_supp_of_adj_mem_supp hs ⟨hst, Or.inl hov⟩

private theorem component_openUnion_shift_subset_closure
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T : Set Plane}
    (hInv : IsInvariantAlong (regularSupport K T) δ)
    (P : EarthquakeComponent K δ T) {u : Plane} (hu : u ∈ δ) :
    u +ᵥ openUnion K P.centres ⊆ closure (openUnion K P.centres) := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨s, hys⟩ := Set.mem_iUnion.mp hy
  obtain ⟨sT, hsP, hsval⟩ := s.property
  have hyT : y ∈ regularSupport K T :=
    (openUnion_open K T).subset_interior_closure
      (openUnion_mono (component_centres_subset P) (Set.mem_iUnion.mpr ⟨s, hys⟩))
  have hxT : u +ᵥ y ∈ closure (openUnion K T) := by
    apply interior_subset
    change u +ᵥ y ∈ regularSupport K T
    rw [← hInv u hu]
    exact ⟨y, hyT, rfl⟩
  apply mem_closure_iff.mpr
  intro O hO hxO
  let V : Set Plane := O ∩ (u +ᵥ ((s : Plane) +ᵥ K.openCarrier))
  have hV : IsOpen V := hO.inter ((isOpen_interior.vadd (s : Plane)).vadd u)
  have hxV : u +ᵥ y ∈ V := ⟨hxO, ⟨y, hys, rfl⟩⟩
  obtain ⟨z, hzV, hzT⟩ := mem_closure_iff.mp hxT V hV hxV
  obtain ⟨t, hzt⟩ := Set.mem_iUnion.mp hzT
  obtain ⟨w, hws, hwz⟩ := hzV.2
  have hst : DirectionalOverlap K δ sT t := by
    refine ⟨w, ?_, z, hzt, ?_⟩
    · simpa [hsval] using hws
    · have hwz' : w - z = -u := by
        rw [← hwz]
        change w - (u + w) = -u
        abel
      rw [hwz']
      exact δ.neg_mem hu
  have htP := overlap_same_component P hsP hst
  exact ⟨z, hzV.1, Set.mem_iUnion.mpr ⟨⟨t, ⟨t, htP, rfl⟩⟩, hzt⟩⟩

private theorem invariant_subfamily_overlap_closed
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T)
    (hInv : IsInvariantAlong (regularSupport K S) δ) {s t : T}
    (hs : (s : Plane) ∈ S) (hov : DirectionalOverlap K δ s t) : (t : Plane) ∈ S := by
  by_contra ht
  obtain ⟨w, hws, z, hzt, hwz⟩ := hov
  have hwS : w ∈ regularSupport K S :=
    (openUnion_open K S).subset_interior_closure (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hws⟩)
  have hzS : z ∈ regularSupport K S := by
    rw [← hInv (z - w) (by simpa [neg_sub] using δ.neg_mem hwz)]
    exact ⟨w, hwS, by change z - w + w = z; abel⟩
  have hzt' : z ∈ regularSupport K ({(t : Plane)} : Set Plane) :=
    (openUnion_open K _).subset_interior_closure
      (Set.mem_iUnion.mpr ⟨⟨t, Set.mem_singleton _⟩, hzt⟩)
  have hd : Disjoint S ({(t : Plane)} : Set Plane) :=
    Set.disjoint_singleton_right.mpr ht
  exact Set.disjoint_left.mp (regularSupport_disjoint_of_disjoint_subfamilies hp hST
    (Set.singleton_subset_iff.mpr t.property) hd) hzS hzt'

private theorem invariant_subfamily_reachable_closed
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} {T S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T)
    (hInv : IsInvariantAlong (regularSupport K S) δ) {s t : T}
    (hr : (earthquakeGraph K δ T).Reachable s t) :
    (s : Plane) ∈ S → (t : Plane) ∈ S := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact id
  | cons hadj p ih =>
    intro hs
    obtain ⟨_, hov | hov⟩ := hadj
    · exact ih (invariant_subfamily_overlap_closed hp hST hInv hs hov)
    · exact ih (invariant_subfamily_overlap_closed hp hST hInv hs
        ((directionalOverlap_comm K δ _ _).mp hov))

theorem component_isInvariant :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
    IsInvariantAlong (regularSupport K T) δ →
      ∀ P : EarthquakeComponent K δ T, IsInvariantAlong P.carrier δ
  := by
  intro K δ T _ _ hInv P u hu
  have hsub : ∀ v ∈ δ, v +ᵥ P.carrier ⊆ P.carrier := by
    intro v hv
    change v +ᵥ interior (closure (openUnion K P.centres)) ⊆
      interior (closure (openUnion K P.centres))
    rw [← interior_vadd, ← closure_vadd]
    exact interior_mono ((closure_mono
      (component_openUnion_shift_subset_closure hInv P hv)).trans_eq closure_closure)
  apply Set.Subset.antisymm (hsub u hu)
  intro x hx
  have hneg : -u +ᵥ x ∈ P.carrier := hsub (-u) (δ.neg_mem hu) ⟨x, hx, rfl⟩
  exact ⟨-u +ᵥ x, hneg, by simp⟩

theorem invariantSubfamily_isUnionComponents :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
    IsInvariantAlong (regularSupport K T) δ → S ⊆ T →
    IsInvariantAlong (regularSupport K S) δ →
      ∀ P : EarthquakeComponent K δ T, Disjoint P.centres S ∨ P.centres ⊆ S
  := by
  intro K δ T S _ hp _ hST hInv P
  classical
  by_cases hd : Disjoint P.centres S
  · exact Or.inl hd
  · right
    obtain ⟨x, hxP, hxS⟩ := Set.not_disjoint_iff.mp hd
    obtain ⟨s, hsP, rfl⟩ := hxP
    rintro y ⟨t, htP, rfl⟩
    exact invariant_subfamily_reachable_closed hp hST hInv
      (P.reachable_of_mem_supp hsP htP) hxS

theorem irreducible_iff_component :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T S : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
    IsInvariantAlong (regularSupport K T) δ →
      (IsIrreducibleDirectionalSubfamily K δ T S ↔
        ∃ P : EarthquakeComponent K δ T, P.centres = S)
  := by
  intro K δ T S hδ hp hInv
  constructor
  · rintro ⟨hS, hST, hSI, hminimal⟩
    obtain ⟨s, hs⟩ := hS
    let P : EarthquakeComponent K δ T :=
      (earthquakeGraph K δ T).connectedComponentMk ⟨s, hST hs⟩
    have hsP : s ∈ P.centres := ⟨⟨s, hST hs⟩, rfl, rfl⟩
    have hPS : P.centres ⊆ S := by
      obtain hd | hPS := invariantSubfamily_isUnionComponents K δ T S hδ hp hInv hST hSI P
      · exact False.elim (Set.disjoint_left.mp hd hsP hs)
      · exact hPS
    exact ⟨P, hminimal P.centres (component_centres_nonempty P) hPS
      (component_isInvariant K δ T hδ hp hInv P)⟩
  · rintro ⟨P, rfl⟩
    refine ⟨component_centres_nonempty P, component_centres_subset P,
      component_isInvariant K δ T hδ hp hInv P, ?_⟩
    intro U hU hUP hUI
    obtain ⟨u, hu⟩ := hU
    obtain hd | hPU := invariantSubfamily_isUnionComponents K δ T U hδ hp hInv
      (hUP.trans (component_centres_subset P)) hUI P
    · exact False.elim (Set.disjoint_left.mp hd (hUP hu) hu)
    · exact Set.Subset.antisymm hUP hPU

private theorem line_supported_overlap {K : PolygonalRegion} {δ : Submodule ℝ Plane}
    {C : Set Plane} (hline : IsLineSupported C δ) {s t : Plane}
    (hs : s ∈ C) (ht : t ∈ C) : DirectionalOverlap K δ s t := by
  obtain ⟨a, ha⟩ := hline
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨s +ᵥ k, ⟨k, hk, rfl⟩, t +ᵥ k, ⟨k, hk, rfl⟩, ?_⟩
  have hdiff : s - t ∈ δ := by
    convert δ.sub_mem (ha s hs) (ha t ht) using 1
    abel
  simpa only [vadd_eq_add, add_sub_add_right_eq_sub] using hdiff

theorem column_isComponent :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T C : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
    C ⊆ T → IsCenterColumn K δ C →
      ∃ P : EarthquakeComponent K δ T, P.centres = C
  := by
  intro K δ T C _ hp hCT hC
  obtain ⟨_, hCne, hline, hInv⟩ := hC
  obtain ⟨s, hs⟩ := hCne
  let sT : T := ⟨s, hCT hs⟩
  let P : EarthquakeComponent K δ T := (earthquakeGraph K δ T).connectedComponentMk sT
  refine ⟨P, Set.Subset.antisymm ?_ ?_⟩
  · rintro t ⟨tT, htP, rfl⟩
    exact invariant_subfamily_reachable_closed hp hCT hInv
      (P.reachable_of_mem_supp (by rfl) htP) hs
  · intro t ht
    let tT : T := ⟨t, hCT ht⟩
    have htP : tT ∈ P.supp := overlap_same_component P (by rfl)
      (line_supported_overlap hline hs ht)
    exact ⟨tT, htP, rfl⟩

theorem columnPart_isUnionColumns :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
      IsUnionOfColumns K δ (columnPart K δ T)
  := by
  intro K δ T hδ hp t ht
  obtain ⟨P, htP⟩ := Set.mem_iUnion.mp ht
  have hCP : P.1.centres ⊆ columnPart K δ T :=
    fun x hx => Set.mem_iUnion.mpr ⟨P, hx⟩
  have hCT : columnPart K δ T ⊆ T := by
    intro x hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    exact component_centres_subset Q.1 hxQ
  have hmax := column_maximal_in_fibre hδ hp (component_centres_subset P.1) P.2 t htP
  have hfibre : lineFibre δ (columnPart K δ T) t = P.1.centres := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [← hmax]
      exact ⟨hCT hx.1, hx.2⟩
    · intro x hx
      have hxT : x ∈ lineFibre δ T t := hmax.symm ▸ hx
      exact ⟨hCP hx, hxT.2⟩
  rw [hfibre]
  exact P.2

theorem components_partition :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    (columnPart K δ T ∪
      ⋃ P : {P : EarthquakeComponent K δ T // P ∈ noncolumnComponents K δ T},
        P.1.centres) = T
  := by
  intro K δ T
  classical
  apply Set.Subset.antisymm
  · rintro x (hx | hx)
    · obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      exact component_centres_subset P.1 hx
    · obtain ⟨P, hx⟩ := Set.mem_iUnion.mp hx
      exact component_centres_subset P.1 hx
  · intro x hx
    let P : EarthquakeComponent K δ T := (earthquakeGraph K δ T).connectedComponentMk ⟨x, hx⟩
    have hxP : x ∈ P.centres := ⟨⟨x, hx⟩, rfl, rfl⟩
    by_cases hP : IsCenterColumn K δ P.centres
    · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hxP⟩)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hxP⟩)

theorem components_carriers_disjoint :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → IsPacking K.prototileFamily (K.placements T) →
      Set.PairwiseDisjoint Set.univ
        (fun P : EarthquakeComponent K δ T => P.carrier)
  := by
  intro K δ T _ hp P _ Q _ hPQ
  exact regularSupport_disjoint_of_disjoint_subfamilies hp
    (component_centres_subset P) (component_centres_subset Q)
    (component_centres_disjoint hPQ)

private theorem packing_subfamily {K : PolygonalRegion} {T S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T)) (hST : S ⊆ T) :
    IsPacking K.prototileFamily (K.placements S) := by
  apply (isPacking_iff_openCarrier_disjoint K S).mpr
  exact ((isPacking_iff_openCarrier_disjoint K T).mp hp).mono hST

private theorem frontier_support_covered {K : PolygonalRegion} {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) :
    frontier (regularSupport K S) ⊆ ⋃ s : S, (s : Plane) +ᵥ frontier K.support := by
  intro x hx
  have hxcl : x ∈ closure (openUnion K S) :=
    ((closure_mono interior_subset).trans_eq closure_closure) hx.1
  rw [closure_openUnion_eq_iUnion_support hp] at hxcl
  obtain ⟨s, k, hk, rfl⟩ := Set.mem_iUnion.mp hxcl
  apply Set.mem_iUnion.mpr
  refine ⟨s, k, ⟨subset_closure hk, ?_⟩, rfl⟩
  intro hkopen
  apply hx.2
  rw [(regularSupport_isRegularOpen K S).1.interior_eq]
  exact (openUnion_open K S).subset_interior_closure
    (Set.mem_iUnion.mpr ⟨s, ⟨k, hkopen, rfl⟩⟩)

private theorem line_edge_intersection_subsingleton
    {K : PolygonalRegion} {δ : Submodule ℝ Plane} (hδ : Module.finrank ℝ δ = 1)
    (hnb : ¬HasBoundaryDirection K δ) (a s p q : Plane)
    (hpq : p ≠ q) (hedge : segment ℝ p q ⊆ frontier K.support) :
    ((a +ᵥ (δ : Set Plane)) ∩ (s +ᵥ segment ℝ p q)).Subsingleton := by
  intro x hx y hy
  by_contra hxy
  obtain ⟨u, hu, hux⟩ := hx.1
  obtain ⟨v, hv, hvy⟩ := hy.1
  have hdiff : x - y ∈ δ := by
    rw [← hux, ← hvy]
    simpa only [vadd_eq_add, add_sub_add_left_eq_sub] using δ.sub_mem hu hv
  obtain ⟨z, hz, hzx⟩ := hx.2
  obtain ⟨w, hw, hwy⟩ := hy.2
  rw [segment_eq_image_lineMap] at hz hw
  obtain ⟨r, _, rfl⟩ := hz
  obtain ⟨t, _, rfl⟩ := hw
  have hrt : r ≠ t := by
    intro h
    exact hxy (by rw [← hzx, ← hwy, h])
  have heq : x - y = (r - t) • (q - p) := by
    rw [← hzx, ← hwy, AffineMap.lineMap_apply_module', AffineMap.lineMap_apply_module']
    simp only [vadd_eq_add, add_sub_add_left_eq_sub, add_sub_add_right_eq_sub, sub_smul]
  have hdmem : q - p ∈ δ := by
    have hh := δ.smul_mem (r - t)⁻¹ hdiff
    rw [heq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hrt), one_smul] at hh
    exact hh
  exact hnb ⟨p, q, hpq, hedge,
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hdmem (sub_ne_zero.mpr hpq.symm)⟩

theorem earthquake_direction_isBoundary :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    HasDirectionalEarthquake K δ T → HasBoundaryDirection K δ
  := by
  intro K δ T hδ htile hquake
  classical
  obtain ⟨S, hS, hST, hSne, hInv⟩ := hquake
  have hpS := packing_subfamily htile.2.1 hST
  obtain ⟨s, hs⟩ := hS
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hDne : (regularSupport K S).Nonempty :=
    ⟨s +ᵥ k, (openUnion_open K S).subset_interior_closure
      (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨k, hk, rfl⟩⟩)⟩
  have hproper : regularSupport K S ≠ Set.univ := by
    obtain ⟨t, htT, htS⟩ := Set.not_subset.mp (fun hTS => hSne (Set.Subset.antisymm hST hTS))
    have hd := regularSupport_disjoint_of_disjoint_subfamilies htile.2.1 hST
      (Set.singleton_subset_iff.mpr htT) (Set.disjoint_singleton_right.mpr htS)
    intro hfull
    have htk : t +ᵥ k ∈ regularSupport K ({t} : Set Plane) :=
      (openUnion_open K _).subset_interior_closure
        (Set.mem_iUnion.mpr ⟨⟨t, Set.mem_singleton t⟩, ⟨k, hk, rfl⟩⟩)
    exact Set.disjoint_left.mp hd (hfull.symm ▸ Set.mem_univ _) htk
  obtain ⟨a, ha⟩ := nonempty_frontier_iff.mpr ⟨hDne, hproper⟩
  have hline : a +ᵥ (δ : Set Plane) ⊆ frontier (regularSupport K S) := by
    rintro x ⟨u, hu, rfl⟩
    have hfront : u +ᵥ frontier (regularSupport K S) = frontier (regularSupport K S) := by
      calc
        u +ᵥ frontier (regularSupport K S) = frontier (u +ᵥ regularSupport K S) :=
          (Homeomorph.vadd u).image_frontier _
        _ = frontier (regularSupport K S) := by rw [hInv u hu]
    change a + u ∈ frontier (regularSupport K S)
    rw [add_comm a u]
    rw [← hfront]
    exact ⟨a, ha, rfl⟩
  by_contra hnb
  obtain ⟨F, hF, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let L : Set Plane := a +ᵥ (δ : Set Plane)
  have hSct : S.Countable := (packing_centres_locallyFinite hpS).2.1
  have hct : L.Countable := by
    apply Set.Countable.mono (s₂ := ⋃ s ∈ S, ⋃ e ∈ F,
      L ∩ (s +ᵥ segment ℝ e.1 e.2))
    · intro x hx
      obtain ⟨t, z, hz, hzx⟩ := Set.mem_iUnion.mp (frontier_support_covered hpS (hline hx))
      rw [hfront] at hz
      obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
      exact Set.mem_iUnion₂.mpr ⟨t, t.property,
        Set.mem_iUnion₂.mpr ⟨e, he, hx, ⟨z, hze, hzx⟩⟩⟩
    · apply hSct.biUnion
      intro t _
      apply F.finite_toSet.countable.biUnion
      intro e he
      exact (line_edge_intersection_subsingleton hδ hnb a t e.1 e.2
        (hF e he).1 (hF e he).2.2.2).countable
  have hpos : 0 < Module.finrank ℝ δ := by rw [hδ]; omega
  obtain ⟨e, he⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := δ)).mp hpos
  have he0 : (e : Plane) ≠ 0 := fun h => he (Subtype.ext h)
  let g : ℝ → Plane := fun r => a +ᵥ (r • (e : Plane))
  have hg : Function.Injective g := by
    intro r t h
    have hs : r • (e : Plane) = t • (e : Plane) := add_left_cancel h
    exact (smul_left_injective ℝ he0) hs
  have hpre : g ⁻¹' L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro r
    exact ⟨r • (e : Plane), δ.smul_mem r e.property, rfl⟩
  exact Set.not_countable_univ (hpre ▸ hct.preimage hg)

theorem shifts_preserveWholePlaneTiling :
∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
      ∀ f : EarthquakeComponent K δ T → Plane, (∀ P, f P ∈ δ) →
        TilesOn K (⋃ P : EarthquakeComponent K δ T, f P +ᵥ P.centres) Set.univ
  := by
  intro K δ T hδ htile f hf
  have hregT : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hInvT : IsInvariantAlong (regularSupport K T) δ := by
    rw [hregT]
    intro u _
    exact Set.vadd_set_univ
  have hInv : ∀ P : EarthquakeComponent K δ T, f P +ᵥ P.carrier = P.carrier :=
    fun P => component_isInvariant K δ T hδ htile.2.1 hInvT P (f P) (hf P)
  have hdisj := components_carriers_disjoint K δ T hδ htile.2.1
  have htileSub : ∀ (P : EarthquakeComponent K δ T) (s : Plane), s ∈ P.centres →
      f P +ᵥ (s +ᵥ K.openCarrier) ⊆ P.carrier := by
    intro P s hs x hx
    rw [← hInv P]
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, (openUnion_open K P.centres).subset_interior_closure
      (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hy⟩), rfl⟩
  have hpack : IsPacking K.prototileFamily
      (K.placements (⋃ P : EarthquakeComponent K δ T, f P +ᵥ P.centres)) := by
    apply (isPacking_iff_openCarrier_disjoint K _).mpr
    intro x hx y hy hxy
    obtain ⟨P, s, hs, rfl⟩ := Set.mem_iUnion.mp hx
    obtain ⟨Q, t, ht, rfl⟩ := Set.mem_iUnion.mp hy
    change Disjoint ((f P + s) +ᵥ K.openCarrier) ((f Q + t) +ᵥ K.openCarrier)
    rw [add_vadd, add_vadd]
    by_cases hPQ : P = Q
    · subst Q
      apply Set.disjoint_vadd_set.mpr
      apply (isPacking_iff_openCarrier_disjoint K T).mp htile.2.1
        (component_centres_subset P hs) (component_centres_subset P ht)
      intro hst
      exact hxy (congrArg (fun z : Plane => f P +ᵥ z) hst)
    · exact (hdisj (Set.mem_univ P) (Set.mem_univ Q) hPQ).mono
        (htileSub P s hs) (htileSub Q t ht)
  have hall : (⋃ P : EarthquakeComponent K δ T, P.centres) = T := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      exact component_centres_subset P hxP
    · intro x hx
      exact Set.mem_iUnion.mpr ⟨(earthquakeGraph K δ T).connectedComponentMk ⟨x, hx⟩,
        ⟨⟨x, hx⟩, rfl, rfl⟩⟩
  have hreg : regularSupport K
      (⋃ P : EarthquakeComponent K δ T, f P +ᵥ P.centres) = Set.univ := by
    rw [regularSupport_iUnion]
    have hcar : (fun P : EarthquakeComponent K δ T => regularSupport K (f P +ᵥ P.centres)) =
        (fun P : EarthquakeComponent K δ T => P.carrier) := by
      funext P
      rw [regularSupport_vadd]
      exact hInv P
    rw [hcar]
    change interior (closure (⋃ P : EarthquakeComponent K δ T,
      regularSupport K P.centres)) = Set.univ
    rw [← regularSupport_iUnion, hall, hregT]
  rw [← hreg]
  exact tilesOn_regularSupport_of_packing hpack

private theorem exists_nonzero_mem_of_finrank_one
    (δ : Submodule ℝ Plane) (hδ : Module.finrank ℝ δ = 1) :
    ∃ e : Plane, e ∈ δ ∧ e ≠ 0 := by
  have hpos : 0 < Module.finrank ℝ δ := by rw [hδ]; omega
  obtain ⟨e, he⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := δ)).mp hpos
  exact ⟨e.1, e.2, fun h => he (Subtype.ext h)⟩

private theorem determinant_ne_zero_of_not_mem_span
    (e q : Plane) (he : e ≠ 0) (hq : q ∉ Submodule.span ℝ ({e} : Set Plane)) :
    e.re * q.im - e.im * q.re ≠ 0 := by
  intro hdet
  by_cases hre : e.re = 0
  · have him : e.im ≠ 0 := by
      intro h
      apply he
      exact Complex.ext hre h
    have hqr : q.re = 0 := by
      have hp : e.im * q.re = 0 := by simpa [hre] using hdet
      exact (mul_eq_zero.mp hp).resolve_left him
    refine hq (Submodule.mem_span_singleton.mpr ⟨q.im / e.im, ?_⟩)
    apply Complex.ext
    · simp [hre, hqr]
    · simp [him]
  · let c : ℝ := q.re / e.re
    have hqi : q.im = c * e.im := by
      dsimp [c]
      field_simp [hre]
      nlinarith [hdet]
    refine hq (Submodule.mem_span_singleton.mpr ⟨c, ?_⟩)
    apply Complex.ext
    · simp [c]
      field_simp [hre]
    · simp [hqi]

private theorem linearIndependent_of_det_ne_zero (u v : Plane)
    (hd : u.re * v.im - u.im * v.re ≠ 0) : LinearIndependent ℝ ![u, v] := by
  rw [LinearIndependent.pair_iffₛ]
  intro s t s' t' h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im] at hr hi
  have hr' : (s - s') * u.re + (t - t') * v.re = 0 := by linear_combination hr
  have hi' : (s - s') * u.im + (t - t') * v.im = 0 := by linear_combination hi
  have h1 := congrArg (fun x : ℝ => x * v.im) hr'
  have h2 := congrArg (fun x : ℝ => x * v.re) hi'
  have h3 := congrArg (fun x : ℝ => x * u.im) hr'
  have h4 := congrArg (fun x : ℝ => x * u.re) hi'
  have hs : (s - s') * (u.re * v.im - u.im * v.re) = 0 := by
    nlinarith [h1, h2]
  have ht : (t - t') * (u.re * v.im - u.im * v.re) = 0 := by
    nlinarith [h3, h4]
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_right hd),
    sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_right hd)⟩


theorem periodStepGroup_containsLattice :
∀ (δ : Submodule ℝ Plane) (periodVec : Plane), Module.finrank ℝ δ = 1 → periodVec ∉ δ →
    ∃ L : PlanarLattice, L.toAddSubgroup ≤ periodStepGroup δ periodVec
  := by
  intro δ periodVec hδ hperiod
  obtain ⟨e, he, he0⟩ := exists_nonzero_mem_of_finrank_one δ hδ
  have hspan : δ = Submodule.span ℝ ({e} : Set Plane) := by
    apply eq_span_singleton_of_mem_of_finrank_eq_one hδ he
    exact he0
  have heGroup : e ∈ periodStepGroup δ periodVec :=
    (le_sup_left : δ.toAddSubgroup ≤ periodStepGroup δ periodVec) he
  have hpGroup : periodVec ∈ periodStepGroup δ periodVec := by
    exact (le_sup_right : AddSubgroup.closure ({periodVec} : Set Plane) ≤
      periodStepGroup δ periodVec) (AddSubgroup.subset_closure (by simp))
  have hdet := determinant_ne_zero_of_not_mem_span e periodVec he0 (by
    intro hpSpan
    exact hperiod (hspan ▸ hpSpan))
  refine ⟨⟨![e, periodVec], linearIndependent_of_det_ne_zero e periodVec hdet⟩, ?_⟩
  change AddSubgroup.closure (Set.range ![e, periodVec]) ≤ _
  rw [AddSubgroup.closure_le]
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact heGroup
  · exact hpGroup

theorem commensurableStepGroups_commonLattice :
∀ (δ : Submodule ℝ Plane) (periodVec μ : Plane), Module.finrank ℝ δ = 1 →
    periodVec ∉ δ → μ ∉ δ →
    (∃ m n : ℤ, m ≠ 0 ∧ n ≠ 0 ∧ m • periodVec - n • μ ∈ δ) →
      ∃ L : PlanarLattice, L.toAddSubgroup ≤ periodStepGroup δ periodVec ∧
        L.toAddSubgroup ≤ periodStepGroup δ μ
  := by
  intro δ periodVec μ hδ hp hμ hcomm
  obtain ⟨m, n, hm, hn, hdiff⟩ := hcomm
  obtain ⟨e, he, he0⟩ := exists_nonzero_mem_of_finrank_one δ hδ
  have hspan : δ = Submodule.span ℝ ({e} : Set Plane) := by
    apply eq_span_singleton_of_mem_of_finrank_eq_one hδ he
    exact he0
  let q : Plane := m • periodVec
  have hqnot : q ∉ δ := by
    intro hq
    have hp' : periodVec ∈ δ := by
      have hq' : (m : ℝ) • periodVec ∈ δ := by simpa [q, zsmul_eq_mul] using hq
      have hinv := δ.smul_mem ((m : ℝ)⁻¹) hq'
      have hm' : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
      simpa [smul_smul, hm, inv_mul_cancel₀ hm'] using hinv
    exact hp hp'
  have hq1 : q ∈ periodStepGroup δ periodVec := by
    change m • periodVec ∈ _
    have hgen : periodVec ∈ AddSubgroup.closure ({periodVec} : Set Plane) :=
      AddSubgroup.subset_closure (by simp)
    exact (le_sup_right : AddSubgroup.closure ({periodVec} : Set Plane) ≤
      periodStepGroup δ periodVec) (zsmul_mem hgen m)
  have hq2 : q ∈ periodStepGroup δ μ := by
    have hd : m • periodVec - n • μ ∈ δ.toAddSubgroup := hdiff
    have hnμ : n • μ ∈ AddSubgroup.closure ({μ} : Set Plane) := by
      exact zsmul_mem (AddSubgroup.subset_closure (by simp)) n
    have hsum : (m • periodVec - n • μ) + n • μ ∈ periodStepGroup δ μ :=
      (periodStepGroup δ μ).add_mem
        ((le_sup_left : δ.toAddSubgroup ≤ periodStepGroup δ μ) hd)
        ((le_sup_right : AddSubgroup.closure ({μ} : Set Plane) ≤
          periodStepGroup δ μ) hnμ)
    simpa [q, sub_add_cancel] using hsum
  have hdet := determinant_ne_zero_of_not_mem_span e q he0 (by
    intro hqSpan
    exact hqnot (hspan ▸ hqSpan))
  have hIndependent := linearIndependent_of_det_ne_zero e q hdet
  refine ⟨⟨![e, q], hIndependent⟩, ?_, ?_⟩
  · change AddSubgroup.closure (Set.range ![e, q]) ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact (le_sup_left : δ.toAddSubgroup ≤ periodStepGroup δ periodVec) he
    · exact hq1
  · change AddSubgroup.closure (Set.range ![e, q]) ≤ _
    rw [AddSubgroup.closure_le]
    rintro z ⟨i, rfl⟩
    fin_cases i
    · exact (le_sup_left : δ.toAddSubgroup ≤ periodStepGroup δ μ) he
    · exact hq2

end Tiling.RationalSlopes
