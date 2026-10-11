import Tiling.RationalPolygonal.Basic
import Tiling.Geometry.PackingTopology
import Tiling.Geometry.Periodicity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling.Polygonal

open Tiling.RationalPolygonal (PolygonalRegion)

def openUnion (K : PolygonalRegion) (S : Set Plane) : Set Plane :=
  ⋃ s : S, (s : Plane) +ᵥ K.openCarrier

def regularSupport (K : PolygonalRegion) (S : Set Plane) : Set Plane :=
  interior (closure (openUnion K S))

def TilesOn (K : PolygonalRegion) (S D : Set Plane) : Prop :=
  S.Countable ∧ IsPacking K.prototileFamily (K.placements S) ∧
    ∀ᵐ x ∂volume, (x ∈ D ↔ ∃ s : S, x ∈ ((s : Plane) +ᵥ K.openCarrier))

def IsProperVertex (D : Set Plane) (x : Plane) : Prop :=
  x ∈ frontier D ∧ ¬BoundaryLocallyStraightAt D x

def properVertices (D : Set Plane) : Set Plane := {x | IsProperVertex D x}

def SameGermAt (D : Set Plane) (x : Plane) (E : Set Plane) (y : Plane) : Prop :=
  D =ᶠ[𝓝 x] ((x - y) +ᵥ E)

private def genericProtoTiling (K : PolygonalRegion) (S : Set Plane) :
    PolygonalProtoTiling Unit where
  prototiles := K.prototileFamily
  placements := K.placements S
  isPolygonal _ := K.isPolygonal

private theorem finite_inter_of_bounded_of_pairwise_le_dist
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S Q : Set E} {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Pairwise fun x y ↦ delta ≤ dist x y)
    (hQ : Bornology.IsBounded Q) : (S ∩ Q).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hdelta hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · have hsep := hS htS hs hts
        simp only [Metric.mem_ball] at htball
        exfalso
        linarith
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  apply (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
  exact inter_subset_inter_right S hR

theorem regularSupport_vadd (K : PolygonalRegion) (S : Set Plane) (u : Plane) :
    regularSupport K (u +ᵥ S) = u +ᵥ regularSupport K S := by
  have hopen : openUnion K (u +ᵥ S) = u +ᵥ openUnion K S := by
    ext x
    constructor
    · rw [openUnion, Set.mem_iUnion]
      rintro ⟨s, hx⟩
      obtain ⟨t, ht, hst⟩ := s.2
      rw [← hst] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      refine ⟨t + k, ?_, by simp [vadd_eq_add, add_assoc]⟩
      rw [openUnion, Set.mem_iUnion]
      exact ⟨⟨t, ht⟩, k, hk, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rw [openUnion, Set.mem_iUnion] at hy ⊢
      obtain ⟨t, k, hk, rfl⟩ := hy
      exact ⟨⟨u + t, ⟨t, t.2, rfl⟩⟩, k, hk, by
        simp only [vadd_eq_add]
        abel⟩
  rw [regularSupport, regularSupport, hopen, closure_vadd, interior_vadd]

private theorem frontier_vadd_eq
    (u : Tiling.Plane) (D : Set Tiling.Plane) :
    frontier (u +ᵥ D) = u +ᵥ frontier D := by
  rw [frontier, closure_vadd, interior_vadd]
  ext z
  simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]

private theorem boundaryLocallyStraightAt_vadd_iff
    (u : Tiling.Plane) (D : Set Tiling.Plane) (x : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt (u +ᵥ D) (u + x) ↔
      Tiling.BoundaryLocallyStraightAt D x := by
  suffices ∀ (v : Tiling.Plane) (E : Set Tiling.Plane) (y : Tiling.Plane),
      Tiling.BoundaryLocallyStraightAt E y →
        Tiling.BoundaryLocallyStraightAt (v +ᵥ E) (v + y) by
    constructor
    · intro h
      have h' := this (-u) (u +ᵥ D) (u + x) h
      simpa only [neg_add_cancel_left, neg_vadd_vadd] using h'
    · exact this u D x
  intro v E y h
  obtain ⟨L, hyL, hdim, hlocal⟩ := h
  let L' : AffineSubspace ℝ Tiling.Plane := AffineSubspace.mk' (v + y) L.direction
  refine ⟨L', AffineSubspace.self_mem_mk' _ _, ?_, ?_⟩
  · dsimp only [L']
    rw [AffineSubspace.direction_mk']
    exact hdim
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨r, hr, fun z hz ↦ ?_⟩
    let z' : Tiling.Plane := z - v
    have hz' : dist z' y < r := by
      have hzEq : z' - y = z - (v + y) := by dsimp only [z']; abel
      simpa only [dist_eq_norm, hzEq] using hz
    have hsource := hball hz'
    rw [frontier_vadd_eq]
    change (z ∈ v +ᵥ frontier E) ↔ z ∈ L'
    have hfrontier : z ∈ v +ᵥ frontier E ↔ z' ∈ frontier E := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z' := by
          change v + w = z at hwz
          dsimp only [z']
          rw [← hwz]
          abel
        simpa only [this] using hw
      · intro hz'E
        refine ⟨z', hz'E, ?_⟩
        change v + z' = z
        dsimp only [z']
        abel
    rw [hfrontier, hsource]
    rw [show L = AffineSubspace.mk' y L.direction from
      (AffineSubspace.mk'_eq hyL).symm]
    simp only [L', AffineSubspace.mem_mk']
    change z' - y ∈ L.direction ↔ z - (v + y) ∈ L.direction
    have hzEq : z' - y = z - (v + y) := by
      dsimp only [z']
      abel
    rw [hzEq]

theorem properVertices_vadd (D : Set Plane) (u : Plane) :
    properVertices (u +ᵥ D) = u +ᵥ properVertices D := by
  ext x
  let y : Tiling.Plane := -u + x
  have hxy : u + y = x := by dsimp [y]; abel
  change IsProperVertex (u +ᵥ D) x ↔ x ∈ u +ᵥ properVertices D
  rw [mem_vadd_set_iff_neg_vadd_mem]
  change IsProperVertex (u +ᵥ D) x ↔ IsProperVertex D y
  change (x ∈ frontier (u +ᵥ D) ∧
      ¬Tiling.BoundaryLocallyStraightAt (u +ᵥ D) x) ↔
    y ∈ frontier D ∧ ¬Tiling.BoundaryLocallyStraightAt D y
  rw [frontier_vadd_eq]
  have hfrontier : x ∈ u +ᵥ frontier D ↔ y ∈ frontier D := by
    rw [mem_vadd_set_iff_neg_vadd_mem]
    rfl
  rw [hfrontier]
  have hstraight := boundaryLocallyStraightAt_vadd_iff u D y
  rw [hxy] at hstraight
  exact and_congr_right fun _ ↦ not_congr hstraight

private theorem interior_closure_iUnion_interior_closure
    {X : Type*} [TopologicalSpace X] {I : Type*}
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) :
    interior (closure (⋃ i, U i)) =
      interior (closure (⋃ i, interior (closure (U i)))) := by
  have hforward : (⋃ i, U i) ⊆ ⋃ i, interior (closure (U i)) := by
    apply Set.iUnion_mono
    intro i
    exact (hU i).subset_interior_closure
  have hbackward : (⋃ i, interior (closure (U i))) ⊆ closure (⋃ i, U i) := by
    apply Set.iUnion_subset
    intro i
    exact interior_subset.trans
      (closure_mono (Set.subset_iUnion U i))
  have hclosure : closure (⋃ i, U i) =
      closure (⋃ i, interior (closure (U i))) := by
    apply Set.Subset.antisymm
    · exact closure_mono hforward
    · exact closure_minimal hbackward isClosed_closure
  rw [hclosure]

private theorem openUnion_iUnion
    {I : Type*} (K : PolygonalRegion) (S : I → Set Tiling.Plane) :
    openUnion K (⋃ i, S i) = ⋃ i, openUnion K (S i) := by
  ext x
  simp only [openUnion, Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨i, hsi⟩ := Set.mem_iUnion.mp s.2
    exact ⟨i, ⟨⟨s.1, hsi⟩, hs⟩⟩
  · rintro ⟨i, s, hs⟩
    exact ⟨⟨s.1, Set.mem_iUnion.mpr ⟨i, s.2⟩⟩, hs⟩


theorem regularSupport_iUnion (K : PolygonalRegion) {ι : Type} (S : ι → Set Plane) :
    regularSupport K (⋃ i, S i) = interior (closure (⋃ i, regularSupport K (S i))) := by
  have hopen (i : ι) : IsOpen (openUnion K (S i)) := by
    apply isOpen_iUnion
    intro s
    change IsOpen ((Homeomorph.addLeft (s : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
  rw [regularSupport, openUnion_iUnion]
  exact interior_closure_iUnion_interior_closure
    (fun i ↦ openUnion K (S i)) hopen

theorem regularOpen_disjoint_complement
    {A B E : Set Plane} (hAopen : IsOpen A) (hAreg : interior (closure A) = A)
    (hBopen : IsOpen B) (hBreg : interior (closure B) = B)
    (hdisj : Disjoint A B) (hE : E = interior (closure (A ∪ B))) :
    A = E \ closure B ∧ B = E \ closure A := by
  have one {U V : Set Plane} (hU : IsOpen U) (hUreg : interior (closure U) = U)
      (hdis : Disjoint U V) :
      U = interior (closure (U ∪ V)) \ closure V := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨interior_mono (closure_mono subset_union_left)
        (hU.subset_interior_closure hx), disjoint_left.mp (hdis.closure_right hU) hx⟩
    · have hopen : IsOpen (interior (closure (U ∪ V)) \ closure V) :=
        isOpen_interior.sdiff isClosed_closure
      have hsub : interior (closure (U ∪ V)) \ closure V ⊆ closure U := by
        intro x hx
        have hcl := interior_subset hx.1
        rw [closure_union] at hcl
        exact hcl.resolve_right hx.2
      have hi := interior_mono hsub
      rw [hopen.interior_eq, hUreg] at hi
      exact hi
  subst E
  exact ⟨one hAopen hAreg hdisj, by simpa [union_comm] using one hBopen hBreg hdisj.symm⟩

/-- A direction actually represented by a nontrivial straight boundary segment. -/
def HasBoundaryDirection (K : PolygonalRegion) (δ : Submodule ℝ Plane) : Prop :=
  ∃ a b : Plane, a ≠ b ∧ segment ℝ a b ⊆ frontier K.support ∧
    δ = Submodule.span ℝ ({b - a} : Set Plane)

theorem tilesOn_univ_iff_tiles (K : PolygonalRegion) (S : Set Plane) :
    TilesOn K S univ ↔ K.Tiles S := by
  constructor
  · intro h
    refine {
      countable := K.placements_countable h.1
      isPacking := h.2.1
      isCover := ?_ }
    filter_upwards [h.2.2] with x hx
    obtain ⟨s, hs⟩ := hx.mp (Set.mem_univ x)
    rw [Set.mem_iUnion]
    refine ⟨⟨(s.1, ()), s.2⟩, ?_⟩
    change x ∈ s.1 +ᵥ K.support
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs ⊢
    exact interior_subset hs
  · intro h
    let P := genericProtoTiling K S
    let _ : Countable P.placements :=
      (K.placements_countable h.countable).to_subtype
    have hEq :
        (⋃ i : P.placements, interior (Tiling.placedTile P.prototiles i.1))
          =ᵐ[MeasureTheory.volume]
        (⋃ i : P.placements, Tiling.placedTile P.prototiles i.1) :=
      Filter.EventuallyEq.countable_iUnion fun i ↦
        (P.isPolygonal_placedTile i.1).interior_ae_eq
    refine ⟨h.countable, h.isPacking, ?_⟩
    filter_upwards [h.isCover, hEq] with x hx hxeq
    constructor
    · intro _
      have hxopen : x ∈ ⋃ i : P.placements,
          interior (Tiling.placedTile P.prototiles i.1) := hxeq.mpr hx
      rw [Set.mem_iUnion] at hxopen
      obtain ⟨i, hi⟩ := hxopen
      refine ⟨⟨i.1.1, i.2⟩, ?_⟩
      change x ∈ interior (i.1.1 +ᵥ K.support) at hi
      rw [interior_vadd] at hi
      exact hi
    · intro _
      exact Set.mem_univ x

theorem isPacking_iff_openCarrier_disjoint (K : PolygonalRegion) (S : Set Plane) :
    IsPacking K.prototileFamily (K.placements S) ↔
      S.Pairwise (fun s t => Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)) := by
  let P := genericProtoTiling K S
  constructor
  · intro hpacking s hs t ht hst
    let i : P.placements := ⟨(s, ()), hs⟩
    let j : P.placements := ⟨(t, ()), ht⟩
    have hij : i ≠ j := by
      intro hij
      exact hst (congrArg (fun q : P.placements ↦ q.1.1) hij)
    have hd := P.interior_placedTile_disjoint hpacking hij
    change Disjoint (interior (s +ᵥ K.support))
      (interior (t +ᵥ K.support)) at hd
    change Disjoint (s +ᵥ interior K.support) (t +ᵥ interior K.support)
    simpa only [interior_vadd] using hd
  · intro hdisjoint i hi j hj hij
    have hcent : i.1 ≠ j.1 := by
      intro hcent
      apply hij
      cases i
      cases j
      simp_all
    have hopenDisjoint := hdisjoint hi hj hcent
    let P := genericProtoTiling K S
    have hinterior : Disjoint
        (interior (Tiling.placedTile P.prototiles i))
        (interior (Tiling.placedTile P.prototiles j)) := by
      change Disjoint (i.1 +ᵥ interior K.support)
        (j.1 +ᵥ interior K.support) at hopenDisjoint
      change Disjoint (interior (i.1 +ᵥ K.support))
        (interior (j.1 +ᵥ K.support))
      simpa only [interior_vadd] using hopenDisjoint
    have hsubset :
        Tiling.placedTile P.prototiles i ∩ Tiling.placedTile P.prototiles j ⊆
          frontier (Tiling.placedTile P.prototiles i) ∪
            frontier (Tiling.placedTile P.prototiles j) := by
      rintro x ⟨hxi, hxj⟩
      by_cases hxi' : x ∈ interior (Tiling.placedTile P.prototiles i)
      · right
        apply (mem_frontier_iff_notMem_interior hxj).2
        intro hxj'
        exact Set.disjoint_left.1 hinterior hxi' hxj'
      · left
        exact (mem_frontier_iff_notMem_interior hxi).2 hxi'
    apply measure_mono_null hsubset
    rw [measure_union_null]
    · exact (P.isPolygonal_placedTile i).volume_frontier
    · exact (P.isPolygonal_placedTile j).volume_frontier

theorem exists_packingSeparation (K : PolygonalRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set Plane,
      IsPacking K.prototileFamily (K.placements S) →
        S.Pairwise (fun s t => δ ≤ dist s t) := by
  obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change c ∈ K.openCarrier at hc
  have hnhds : K.openCarrier ∈ 𝓝 c :=
    isOpen_interior.mem_nhds hc
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨r + r, add_pos hr hr, ?_⟩
  intro S hpacking s hs t ht hst
  have hdisjoint :=
    (isPacking_iff_openCarrier_disjoint K S).mp hpacking hs ht hst
  have ball_subset (a : Tiling.Plane) :
      Metric.ball (a + c) r ⊆ a +ᵥ K.openCarrier := by
    intro z hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    apply hball
    simpa [dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hz
  have hballs : Disjoint (Metric.ball (s + c) r) (Metric.ball (t + c) r) :=
    hdisjoint.mono (ball_subset s) (ball_subset t)
  have hdist := (disjoint_ball_ball_iff hr hr).mp hballs
  rw [show dist (s + c) (t + c) = dist s t by
    simp only [dist_eq_norm]
    congr 1
    abel] at hdist
  exact hdist

theorem packing_centres_locallyFinite
    {K : PolygonalRegion} {S : Set Plane}
    (hpacking : IsPacking K.prototileFamily (K.placements S)) :
    (∀ Q : Set Plane, Bornology.IsBounded Q → (S ∩ Q).Finite) ∧
      S.Countable ∧ IsClosed S := by
  obtain ⟨delta, hdelta, hsep⟩ := exists_packingSeparation K
  have hpairwise : S.Pairwise fun x y ↦ delta ≤ dist x y :=
    hsep S hpacking
  have hfinite : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (S ∩ Q).Finite := fun Q hQ ↦
    finite_inter_of_bounded_of_pairwise_le_dist hdelta hpairwise hQ
  refine ⟨hfinite, ?_, Metric.isClosed_of_pairwise_le_dist hdelta hpairwise⟩
  have hcover : S ⊆ ⋃ n : ℕ, S ∩ Metric.closedBall 0 n := by
    intro x hx
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt ‖x‖
    rw [Set.mem_iUnion]
    refine ⟨n, hx, ?_⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hn.le
  exact (Set.countable_iUnion fun n : ℕ ↦
    (hfinite (Metric.closedBall 0 (n : ℝ))
      Metric.isBounded_closedBall).countable).mono hcover

theorem regularSupport_isRegularOpen (K : PolygonalRegion) (S : Set Plane) :
    IsOpen (regularSupport K S) ∧
      interior (closure (regularSupport K S)) = regularSupport K S := by
  refine ⟨isOpen_interior, ?_⟩
  simp [regularSupport]

theorem closure_openUnion_eq_iUnion_support
    {K : PolygonalRegion} {S : Set Plane}
    (hpacking : IsPacking K.prototileFamily (K.placements S)) :
    closure (openUnion K S) = ⋃ s : S, (s : Plane) +ᵥ K.support := by
  let P := genericProtoTiling K S
  let toPlacement : S → P.placements := fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hst)
  have hloc : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.support) := by
    exact (P.locallyFinite_placedTile hpacking).comp_injective htoPlacement
  have hopen : LocallyFinite (fun s : S ↦ (s : Tiling.Plane) +ᵥ K.openCarrier) :=
    hloc.subset fun s => vadd_set_mono interior_subset
  rw [openUnion, hopen.closure_iUnion]
  apply iUnion_congr
  intro s
  rw [closure_vadd]
  rw [show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]

theorem openUnion_aeEq_regularSupport
    {K : PolygonalRegion} {S : Set Plane}
    (hpacking : IsPacking K.prototileFamily (K.placements S)) :
    openUnion K S =ᵐ[volume] regularSupport K S := by
  let P := genericProtoTiling K S
  let C : Set Tiling.Plane :=
    ⋃ i : P.placements, Tiling.placedTile P.prototiles i.1
  have hU : openUnion K S =
      ⋃ i : P.placements, interior (Tiling.placedTile P.prototiles i.1) := by
    ext x
    constructor
    · rw [openUnion, Set.mem_iUnion]
      rintro ⟨s, hs⟩
      rw [Set.mem_iUnion]
      refine ⟨⟨(s.1, ()), s.2⟩, ?_⟩
      change x ∈ interior (s.1 +ᵥ K.support)
      rw [interior_vadd]
      exact hs
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rw [openUnion, Set.mem_iUnion]
      refine ⟨⟨i.1.1, i.2⟩, ?_⟩
      change x ∈ interior (i.1.1 +ᵥ K.support) at hi
      rw [interior_vadd] at hi
      exact hi
  have hC : C = ⋃ s : S, (s : Tiling.Plane) +ᵥ K.support := by
    ext x
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨i.1.1, i.2⟩, hi⟩
    · rw [Set.mem_iUnion]
      rintro ⟨s, hs⟩
      rw [Set.mem_iUnion]
      exact ⟨⟨(s.1, ()), s.2⟩, hs⟩
  have hclosure : closure (openUnion K S) = C := by
    exact (closure_openUnion_eq_iUnion_support hpacking).trans hC.symm
  have hUC : openUnion K S ⊆ C := by
    rw [hU]
    exact iUnion_mono fun i ↦ interior_subset
  have hSCountable := (packing_centres_locallyFinite hpacking).2.1
  let _ : Countable P.placements :=
    (K.placements_countable hSCountable).to_subtype
  have hAE : openUnion K S =ᵐ[MeasureTheory.volume] C := by
    rw [hU]
    exact Filter.EventuallyEq.countable_iUnion fun i ↦
      (P.isPolygonal_placedTile i.1).interior_ae_eq
  have hUInterior : openUnion K S ⊆ interior C := by
    have hUOpen : IsOpen (openUnion K S) := by
      rw [hU]
      exact isOpen_iUnion fun _ ↦ isOpen_interior
    rw [← hUOpen.interior_eq]
    exact interior_mono hUC
  rw [regularSupport, hclosure]
  filter_upwards [hAE] with x hx
  apply propext
  constructor
  · intro hxU
    exact hUInterior hxU
  · intro hxint
    rw [hx]
    exact (interior_subset : interior C ⊆ C) hxint

theorem regularSupport_disjoint_of_disjoint_subfamilies
    {K : PolygonalRegion} {T A B : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements T))
    (hAT : A ⊆ T) (hBT : B ⊆ T) (hdisj : Disjoint A B) :
    Disjoint (regularSupport K A) (regularSupport K B) := by
  have hpackA : IsPacking K.prototileFamily (K.placements A) :=
    fun _ hs _ ht hst => hp (hAT hs) (hAT ht) hst
  have hpackB : IsPacking K.prototileFamily (K.placements B) :=
    fun _ hs _ ht hst => hp (hBT hs) (hBT ht) hst
  have hopenDisjoint : Disjoint (openUnion K A) (openUnion K B) := by
    rw [disjoint_left]
    intro x hxA hxB
    obtain ⟨s, hs⟩ := mem_iUnion.mp hxA
    obtain ⟨t, ht⟩ := mem_iUnion.mp hxB
    have hst : (s : Plane) ≠ (t : Plane) := by
      intro heq
      exact disjoint_left.mp hdisj s.2 (heq.symm ▸ t.2)
    exact disjoint_left.mp ((isPacking_iff_openCarrier_disjoint K T).mp hp
      (hAT s.2) (hBT t.2) hst) hs ht
  have hzero : volume (regularSupport K A ∩ regularSupport K B) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [openUnion_aeEq_regularSupport hpackA,
      openUnion_aeEq_regularSupport hpackB] with x hxA hxB
    intro hx
    exact disjoint_left.mp hopenDisjoint (Eq.mpr hxA hx.1) (Eq.mpr hxB hx.2)
  rw [disjoint_left]
  intro x hxA hxB
  exact ((regularSupport_isRegularOpen K A).1.inter
    (regularSupport_isRegularOpen K B).1).measure_ne_zero volume ⟨x, hxA, hxB⟩ hzero

theorem tilesOn_regularSupport_of_packing
    {K : PolygonalRegion} {S : Set Plane}
    (hpacking : IsPacking K.prototileFamily (K.placements S)) :
    TilesOn K S (regularSupport K S) := by
  refine ⟨(packing_centres_locallyFinite hpacking).2.1, hpacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpacking] with x hx
  change (x ∈ openUnion K S) = (x ∈ regularSupport K S) at hx
  rw [← hx]
  exact mem_iUnion

theorem properVertexProvenance
    {K : PolygonalRegion} {S : Set Plane}
    (hpacking : IsPacking K.prototileFamily (K.placements S)) :
    ∀ x ∈ properVertices (regularSupport K S),
      ∃ v ∈ vertexSet K.support, ∃ s ∈ S, x = v + s := by
  intro x hx
  let A := genericProtoTiling K S
  have hpack : Tiling.IsPacking A.prototiles A.placements := by
    intro i hi j hj hij
    apply hpacking
    · exact hi
    · exact hj
    · exact hij
  have hcarrier : A.placementCarrier Set.univ =
      closure (openUnion K S) := by
    rw [Tiling.PolygonalProtoTiling.placementCarrier]
    rw [closure_openUnion_eq_iUnion_support hpack]
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      rw [Set.mem_iUnion]
      exact ⟨⟨i.1.1.1, i.1.2⟩, hi⟩
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rw [Set.mem_iUnion]
      let i : A.placements := ⟨((s : Tiling.Plane), ()), s.2⟩
      refine ⟨⟨i, trivial⟩, ?_⟩
      exact hs
  have hfrontier_eq :
      frontier (A.placementCarrier Set.univ) =
        frontier (regularSupport K S) := by
    rw [regularSupport, ← hcarrier]
    simp [frontier, A.placementCarrier_closure_interior hpack Set.univ,
      (A.placementCarrier_isClosed hpack Set.univ).closure_eq]
  have hxfrontier : x ∈ frontier (A.placementCarrier Set.univ) := by
    rw [hfrontier_eq]
    exact hx.1
  have hxnotstraight : ¬Tiling.BoundaryLocallyStraightAt
      (A.placementCarrier Set.univ) x := by
    intro hstraight
    apply hx.2
    simpa only [Tiling.BoundaryLocallyStraightAt, hfrontier_eq] using hstraight
  obtain ⟨i, hiQ, hxi⟩ :=
    A.exists_vertex_of_not_boundaryLocallyStraightAt hpack Set.univ
      hxfrontier hxnotstraight
  have hcenterS : i.1.1 ∈ S := i.2
  have hplaced : x ∈ i.1.1 +ᵥ vertexSet K.support := by
    exact hxi
  obtain ⟨v, hv, hvx⟩ := Set.mem_vadd_set.mp hplaced
  refine ⟨v, hv, i.1.1, hcenterS, ?_⟩
  simpa [vadd_eq_add, add_comm] using hvx.symm

theorem frontier_eventuallyEq_of_eventuallyEq
    {D E : Set Plane} {x : Plane} (hDE : D =ᶠ[𝓝 x] E) :
    frontier D =ᶠ[𝓝 x] frontier E := by
  have hnhds : ∀ᶠ y in 𝓝 x, D =ᶠ[𝓝 y] E := hDE.eventually_nhds
  filter_upwards [hnhds] with y hy
  apply propext
  have closureIff (A B : Set Tiling.Plane)
      (hAB : A =ᶠ[nhds y] B) :
      y ∈ closure A ↔ y ∈ closure B := by
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    constructor
    · intro hA
      exact (hA.and_eventually hAB).mono fun z hz ↦ Eq.mp hz.2 hz.1
    · intro hB
      exact (hB.and_eventually hAB).mono fun z hz ↦ Eq.mpr hz.2 hz.1
  have hyCompl : Dᶜ =ᶠ[nhds y] Eᶜ :=
    hy.mono fun z hz ↦ congrArg Not hz
  change y ∈ frontier D ↔ y ∈ frontier E
  rw [frontier_eq_closure_inter_closure,
    frontier_eq_closure_inter_closure, mem_inter_iff, mem_inter_iff,
    closureIff D E hy, closureIff Dᶜ Eᶜ hyCompl]

theorem isProperVertex_iff_of_eventuallyEq
    {D E : Set Plane} {x : Plane} (hDE : D =ᶠ[𝓝 x] E) :
    IsProperVertex D x ↔ IsProperVertex E x := by
  have hfront := frontier_eventuallyEq_of_eventuallyEq hDE
  have hfrontx : x ∈ frontier D ↔ x ∈ frontier E :=
    Iff.of_eq hfront.self_of_nhds
  have hstraight :
      Tiling.BoundaryLocallyStraightAt D x ↔
        Tiling.BoundaryLocallyStraightAt E x := by
    constructor
    · rintro ⟨L, hxL, hdim, hline⟩
      refine ⟨L, hxL, hdim, ?_⟩
      filter_upwards [hfront, hline] with y hyfront hyline
      exact (Iff.of_eq hyfront).symm.trans hyline
    · rintro ⟨L, hxL, hdim, hline⟩
      refine ⟨L, hxL, hdim, ?_⟩
      filter_upwards [hfront, hline] with y hyfront hyline
      exact (Iff.of_eq hyfront).trans hyline
  exact and_congr hfrontx (not_congr hstraight)

theorem regularOpen_eq_of_aeEq {D E : Set Plane}
    (hDopen : IsOpen D) (hDreg : interior (closure D) = D)
    (hEopen : IsOpen E) (hEreg : interior (closure E) = E)
    (hDE : D =ᵐ[volume] E) : D = E := by
  have closure_mono_of_ae {A B : Set Tiling.Plane}
      (hA : IsOpen A) (hB : IsOpen B)
      (hAB : A =ᵐ[MeasureTheory.volume] B) : A ⊆ closure B := by
    intro x hxA
    by_contra hxB
    let W := A ∩ (closure B)ᶜ
    have hWopen : IsOpen W := hA.inter isClosed_closure.isOpen_compl
    have hxW : x ∈ W := ⟨hxA, hxB⟩
    have hWzero : MeasureTheory.volume W = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (hAB.mono fun y hy hyW ↦ by
        have hyB : y ∈ B := Eq.mp hy hyW.1
        exact hyW.2 (subset_closure hyB))
    exact hWopen.measure_ne_zero MeasureTheory.volume ⟨x, hxW⟩ hWzero
  have hclosure : closure D = closure E := Set.Subset.antisymm
    (closure_minimal (closure_mono_of_ae hDopen hEopen hDE) isClosed_closure)
    (closure_minimal (closure_mono_of_ae hEopen hDopen hDE.symm) isClosed_closure)
  calc
    D = interior (closure D) := hDreg.symm
    _ = interior (closure E) := congrArg interior hclosure
    _ = E := hEreg

theorem regularSupport_eq_of_tilesOn
    {K : PolygonalRegion} {S D : Set Plane}
    (hopen : IsOpen D) (hregular : interior (closure D) = D)
    (htile : TilesOn K S D) : regularSupport K S = D := by
  have hAE : regularSupport K S =ᵐ[volume] D := by
    filter_upwards [openUnion_aeEq_regularSupport htile.2.1, htile.2.2] with x hx hu
    apply propext
    change (x ∈ openUnion K S) = (x ∈ regularSupport K S) at hx
    change x ∈ regularSupport K S ↔ x ∈ D
    rw [← hx]
    simpa only [openUnion, mem_iUnion] using hu.symm
  obtain ⟨hsopen, hsreg⟩ := regularSupport_isRegularOpen K S
  exact regularOpen_eq_of_aeEq hsopen hsreg hopen hregular hAE

theorem aePeriodGroup_eq_periodGroup_of_regularOpen
    {S : Set Plane} (hopen : IsOpen S) (hregular : interior (closure S) = S) :
    aePeriodGroup S = periodGroup S := by
  ext u
  change (u +ᵥ S =ᵐ[MeasureTheory.volume] S) ↔ u +ᵥ S = S
  constructor
  · intro hu
    apply regularOpen_eq_of_aeEq (hopen.vadd u) _ hopen hregular hu
    rw [closure_vadd, interior_vadd, hregular]
  · intro hu
    rw [hu]
    exact Filter.EventuallyEq.rfl

theorem isClosed_periodGroup_of_regularOpen {S : Set Plane}
    (hopen : IsOpen S) (hregular : interior (closure S) = S) :
    IsClosed (periodGroup S : Set Plane) := by
  have _hopen := hopen
  apply isClosed_of_closure_subset
  intro u hu
  have hfix {v : Plane} (hv : v ∈ periodGroup S) :
      v +ᵥ closure S = closure S := by
    change v +ᵥ S = S at hv
    rw [← closure_vadd, hv]
  have hmap (x : Plane) (hx : x ∈ closure S) :
      u + x ∈ closure S ∧ -u + x ∈ closure S := by
    constructor
    · have hf : Continuous (fun v : Plane => v + x) := continuous_id.add continuous_const
      apply closure_minimal (t := closure S) ?_ isClosed_closure
        (image_closure_subset_closure_image hf ⟨u, hu, rfl⟩)
      rintro y ⟨v, hv, rfl⟩
      rw [← hfix hv]
      exact ⟨x, hx, rfl⟩
    · have hf : Continuous (fun v : Plane => -v + x) := continuous_id.neg.add continuous_const
      apply closure_minimal (t := closure S) ?_ isClosed_closure
        (image_closure_subset_closure_image hf ⟨u, hu, rfl⟩)
      rintro y ⟨v, hv, rfl⟩
      rw [← hfix ((periodGroup S).neg_mem hv)]
      exact ⟨x, hx, rfl⟩
  have hc : u +ᵥ closure S = closure S := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      exact (hmap x hx).1
    · intro x hx
      exact ⟨-u + x, (hmap x hx).2, by simp [vadd_eq_add]⟩
  change u +ᵥ S = S
  rw [← hregular, ← interior_vadd, hc]

theorem tilesOn_translate {K : PolygonalRegion} {S D : Set Plane}
    (htile : TilesOn K S D) (u : Plane) :
    TilesOn K (u +ᵥ S) (u +ᵥ D) := by
  refine ⟨?_, ?_, ?_⟩
  · have hset : u +ᵥ S = (fun s : Tiling.Plane ↦ u + s) '' S := by
      ext x
      constructor
      · intro hx
        exact ⟨-u + x, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hx,
          by simp⟩
      · rintro ⟨s, hs, rfl⟩
        simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
          neg_add_cancel_left] using hs
    rw [hset]
    exact htile.1.image _
  · intro i hi j hj hij
    let i₀ : Tiling.Placement Tiling.Plane Unit := (-u + i.1, ())
    let j₀ : Tiling.Placement Tiling.Plane Unit := (-u + j.1, ())
    have hi₀ : i₀ ∈ K.placements S := by
      change -u + i.1 ∈ S
      change i.1 ∈ u +ᵥ S at hi
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hi
    have hj₀ : j₀ ∈ K.placements S := by
      change -u + j.1 ∈ S
      change j.1 ∈ u +ᵥ S at hj
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hj
    have hij₀ : i₀ ≠ j₀ := by
      intro heq
      apply hij
      apply Prod.ext
      · have heq' := congrArg Prod.fst heq
        dsimp only [i₀, j₀] at heq'
        have := congrArg (fun z : Tiling.Plane ↦ u + z) heq'
        simpa only [add_assoc, add_neg_cancel_left] using this
      · exact Subsingleton.elim _ _
    have hd := htile.2.1 hi₀ hj₀ hij₀
    have hd' := Tiling.aedisjoint_vadd u hd
    have hiTile : u +ᵥ ((-u + i.1) +ᵥ K.support) = i.1 +ᵥ K.support := by
      rw [vadd_vadd]
      congr 1
      abel
    have hjTile : u +ᵥ ((-u + j.1) +ᵥ K.support) = j.1 +ᵥ K.support := by
      rw [vadd_vadd]
      congr 1
      abel
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (i.1 +ᵥ K.support) (j.1 +ᵥ K.support)
    rw [← hiTile, ← hjTile]
    exact hd'
  · have hpull :=
      (MeasureTheory.quasiMeasurePreserving_add_left MeasureTheory.volume (-u)).ae htile.2.2
    filter_upwards [hpull] with x hx
    have htarget : x ∈ u +ᵥ D ↔ -u + x ∈ D := by
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have hunion :
        (∃ s : u +ᵥ S, x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) ↔
          ∃ s : S, -u + x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
      constructor
      · rintro ⟨s, hsx⟩
        let s₀ : S := ⟨-u + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using s.2⟩
        refine ⟨s₀, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        convert hsx using 1
        all_goals simp only [s₀, vadd_eq_add]
        all_goals abel
      · rintro ⟨s, hsx⟩
        let s' : u +ᵥ S := ⟨u + s.1, by
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_cancel_left] using s.2⟩
        refine ⟨s', ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsx ⊢
        convert hsx using 1
        all_goals simp only [s', vadd_eq_add]
        all_goals abel
    exact htarget.trans (hx.trans hunion.symm)

def affineMap (A : Plane ≃L[ℝ] Plane) (a : Plane) (x : Plane) : Plane := a + A x

private theorem affineMap_injective (A : Plane ≃L[ℝ] Plane) (a : Plane) :
    Injective (affineMap A a) := by
  intro x y h
  exact A.injective (add_left_cancel h)

private theorem affineMap_vadd (A : Plane ≃L[ℝ] Plane) (a u : Plane) (S : Set Plane) :
    affineMap A a '' (u +ᵥ S) = A u +ᵥ (affineMap A a '' S) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨affineMap A a z, ⟨z, hz, rfl⟩, by
      simp [affineMap, map_add, vadd_eq_add, add_left_comm]⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨u + z, ⟨z, hz, rfl⟩, by
      simp [affineMap, map_add, vadd_eq_add, add_left_comm]⟩

private theorem affineMap_inverse (A : Plane ≃L[ℝ] Plane) (a : Plane) (S : Set Plane) :
    affineMap A.symm (-A.symm a) '' (affineMap A a '' S) = S := by
  rw [image_image]
  have hfun : affineMap A.symm (-A.symm a) ∘ affineMap A a = id := by
    funext x
    simp [affineMap]
  change (affineMap A.symm (-A.symm a) ∘ affineMap A a) '' S = S
  rw [hfun, image_id]

theorem volume_affineImage_eq_zero_iff (A : Plane ≃L[ℝ] Plane)
    (a : Plane) (s : Set Plane) :
    volume (affineMap A a '' s) = 0 ↔ volume s = 0 := by
  have h := MeasureTheory.Measure.addHaar_image_continuousLinearEquiv
    (μ := volume) A s
  change volume ((fun x : Plane => a + A x) '' s) = 0 ↔ volume s = 0
  rw [show (fun x : Plane => a + A x) = (fun y : Plane => a + y) ∘ A by rfl,
    Set.image_comp, image_add_left, measure_preimage_add, h]
  have hdet : ENNReal.ofReal |LinearMap.det (A : Plane →ₗ[ℝ] Plane)| ≠ 0 := by
    rw [ENNReal.ofReal_ne_zero_iff]
    apply abs_pos.mpr
    intro hzero
    have hmul := LinearEquiv.det_mul_det_symm A.toLinearEquiv
    rw [hzero, zero_mul] at hmul
    norm_num at hmul
  simp [hdet]

private theorem det_realPlane_formula (A : Plane ≃L[ℝ] Plane) :
    LinearMap.det (A : Plane →ₗ[ℝ] Plane) =
      (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, LinearEquiv.coe_coe,
    Complex.coe_basisOneI_repr]
  simp

private theorem det_realPlane_ne_zero (A : Plane ≃L[ℝ] Plane) :
    LinearMap.det (A : Plane →ₗ[ℝ] Plane) ≠ 0 := by
  intro hzero
  have hmul := LinearEquiv.det_mul_det_symm A.toLinearEquiv
  rw [hzero, zero_mul] at hmul
  norm_num at hmul

private theorem twiceSignedArea_linearImage (A : Plane ≃L[ℝ] Plane)
    (p q r : Plane) :
    Tiling.twiceSignedArea (A p) (A q) (A r) =
      LinearMap.det (A : Plane →ₗ[ℝ] Plane) * Tiling.twiceSignedArea p q r := by
  have hA (z : Plane) : A z = z.re • A 1 + z.im • A Complex.I := by
    have hz : z = z.re • (1 : Plane) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    calc
      A z = A (z.re • (1 : Plane) + z.im • Complex.I) := congrArg A hz
      _ = z.re • A 1 + z.im • A Complex.I := by rw [map_add, map_smul, map_smul]
  have hq : A q - A p = (q.re - p.re) • A 1 + (q.im - p.im) • A Complex.I := by
    calc
      A q - A p = A (q - p) := (map_sub A q p).symm
      _ = (q.re - p.re) • A 1 + (q.im - p.im) • A Complex.I := by
        rw [hA]
        simp
  have hr : A r - A p = (r.re - p.re) • A 1 + (r.im - p.im) • A Complex.I := by
    calc
      A r - A p = A (r - p) := (map_sub A r p).symm
      _ = (r.re - p.re) • A 1 + (r.im - p.im) • A Complex.I := by
        rw [hA]
        simp
  have hqre : (A q).re - (A p).re =
      (q.re - p.re) * (A 1).re + (q.im - p.im) * (A Complex.I).re := by
    simpa only [Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul] using
      congrArg Complex.re hq
  have hqim : (A q).im - (A p).im =
      (q.re - p.re) * (A 1).im + (q.im - p.im) * (A Complex.I).im := by
    simpa only [Complex.sub_im, Complex.add_im, Complex.smul_im, smul_eq_mul] using
      congrArg Complex.im hq
  have hrre : (A r).re - (A p).re =
      (r.re - p.re) * (A 1).re + (r.im - p.im) * (A Complex.I).re := by
    simpa only [Complex.sub_re, Complex.add_re, Complex.smul_re, smul_eq_mul] using
      congrArg Complex.re hr
  have hrim : (A r).im - (A p).im =
      (r.re - p.re) * (A 1).im + (r.im - p.im) * (A Complex.I).im := by
    simpa only [Complex.sub_im, Complex.add_im, Complex.smul_im, smul_eq_mul] using
      congrArg Complex.im hr
  rw [Tiling.twiceSignedArea, Tiling.twiceSignedArea]
  rw [hqre, hqim, hrre, hrim]
  rw [det_realPlane_formula]
  ring

private noncomputable def mappedTriangulation {s : Set Plane}
    (T : Tiling.Triangulation s) (A : Plane ≃L[ℝ] Plane) (a : Plane) :
    Tiling.Triangulation (affineMap A a '' s) := by
  classical
  let f : Plane →ᵃ[ℝ] Plane := AffineEquiv.ofLinearEquiv A.toLinearEquiv 0 a
  let pieces : Finset (Set Plane) := T.pieces.image (affineMap A a '' ·)
  refine {
    pieces := pieces
    isTriangle := ?_
    pairwiseAEDisjoint := ?_
    sUnion_eq := ?_ }
  · intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨p, q, r, harea, rfl⟩ := T.isTriangle u hu
    refine ⟨affineMap A a p, affineMap A a q, affineMap A a r, ?_, ?_⟩
    · have hshift : Tiling.twiceSignedArea (affineMap A a p) (affineMap A a q)
          (affineMap A a r) =
          Tiling.twiceSignedArea (A p) (A q) (A r) := by
        simp [affineMap, Tiling.twiceSignedArea, Complex.add_re, Complex.add_im]
      rw [hshift, twiceSignedArea_linearImage]
      change LinearMap.det (A : Plane →ₗ[ℝ] Plane) * Tiling.twiceSignedArea p q r ≠ 0
      exact mul_ne_zero (det_realPlane_ne_zero A) harea
    · let f : Plane →ᵃ[ℝ] Plane := AffineEquiv.ofLinearEquiv A.toLinearEquiv 0 a
      have hf (x : Plane) : affineMap A a x = f x := by
        simp [f, affineMap, AffineEquiv.ofLinearEquiv_apply, vsub_eq_sub, add_comm]
      calc
        (fun x : Plane => affineMap A a x) '' convexHull ℝ {p, q, r} =
            (f : Plane → Plane) '' convexHull ℝ {p, q, r} := by
          congr 1
          funext x
          exact hf x
        _ = convexHull ℝ ((f : Plane → Plane) '' {p, q, r}) :=
          f.image_convexHull _
        _ = convexHull ℝ {affineMap A a p, affineMap A a q, affineMap A a r} := by
          simp only [image_insert_eq, image_singleton]
          simp_rw [← hf]
  · rw [Finset.coe_image]
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ huv
    have huv' : u ≠ v := by
      intro h
      exact huv (by simp [h])
    have hd := T.pairwiseAEDisjoint hu hv huv'
    rw [MeasureTheory.AEDisjoint]
    rw [← Set.image_inter (f := fun x : Plane => affineMap A a x) (by
      intro x y hxy
      dsimp [affineMap] at hxy
      exact A.injective (add_left_cancel hxy))]
    exact (volume_affineImage_eq_zero_iff A a (u ∩ v)).2 hd.eq
  · calc
      ⋃₀ (pieces : Set (Set Plane)) =
          affineMap A a '' ⋃₀ (T.pieces : Set (Set Plane)) := by
        ext z
        simp only [Set.mem_sUnion, Finset.mem_coe, Set.mem_image]
        aesop
      _ = affineMap A a '' s := congrArg (affineMap A a '' ·) T.sUnion_eq

private theorem affineMap_ae_iff (A : Plane ≃L[ℝ] Plane) (a : Plane) (p : Plane → Prop) :
    (∀ᵐ x ∂volume, p (affineMap A a x)) ↔ ∀ᵐ y ∂volume, p y := by
  rw [ae_iff, ae_iff, ← volume_affineImage_eq_zero_iff A a]
  change volume (affineMap A a '' (affineMap A a ⁻¹' {y | ¬p y})) = 0 ↔ _
  let h : Plane ≃ₜ Plane := A.toHomeomorph.trans (Homeomorph.addLeft a)
  change volume (h '' (h ⁻¹' {y | ¬p y})) = 0 ↔ _
  rw [image_preimage_eq _ h.surjective]

theorem isPolygonal_affineImage {s : Set Plane} (hs : IsPolygonal s)
    (A : Plane ≃L[ℝ] Plane) (a : Plane) :
    IsPolygonal (affineMap A a '' s) := by
  obtain ⟨T⟩ := hs
  exact ⟨mappedTriangulation T A a⟩

def affineImage (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane) (a : Plane) :
    PolygonalRegion where
  support := affineMap A a '' K.support
  isPolygonal := isPolygonal_affineImage K.isPolygonal A a
  nonempty := K.nonempty.image (affineMap A a)

theorem affineImage_openCarrier (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane)
    (a : Plane) :
    (affineImage K A a).openCarrier = affineMap A a '' K.openCarrier := by
  let h : Plane ≃ₜ Plane := A.toHomeomorph.trans (Homeomorph.addLeft a)
  exact (h.image_interior K.support).symm

private theorem extremePoints_vadd (a : Plane) (s : Set Plane) :
    (a +ᵥ s).extremePoints ℝ = a +ᵥ s.extremePoints ℝ := by
  ext x
  rw [mem_extremePoints_iff_left, mem_vadd_set_iff_neg_vadd_mem,
    mem_vadd_set_iff_neg_vadd_mem, mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hxs, hxext⟩
    refine ⟨hxs, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hseg
    have hseg' : x ∈ openSegment ℝ (a +ᵥ y₁) (a +ᵥ y₂) := by
      rw [← vadd_openSegment ℝ]
      exact ⟨-a +ᵥ x, hseg, by simp⟩
    have heq := hxext (a +ᵥ y₁)
      (by simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hy₁)
      (a +ᵥ y₂)
      (by simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hy₂) hseg'
    exact vadd_left_cancel a (heq.trans (vadd_neg_vadd a x).symm)
  · rintro ⟨hxs, hxext⟩
    refine ⟨hxs, ?_⟩
    intro z₁ hz₁ z₂ hz₂ hseg
    have hz₁' : -a +ᵥ z₁ ∈ s := by
      simpa only [mem_vadd_set_iff_neg_vadd_mem] using hz₁
    have hz₂' : -a +ᵥ z₂ ∈ s := by
      simpa only [mem_vadd_set_iff_neg_vadd_mem] using hz₂
    have hseg' : -a +ᵥ x ∈ openSegment ℝ (-a +ᵥ z₁) (-a +ᵥ z₂) := by
      rw [← vadd_openSegment ℝ]
      exact ⟨x, hseg, by simp⟩
    have heq := hxext (-a +ᵥ z₁) hz₁' (-a +ᵥ z₂) hz₂' hseg'
    exact vadd_left_cancel (-a) heq

private theorem affineMap_image (A : Plane ≃L[ℝ] Plane) (a : Plane) (s : Set Plane) :
    affineMap A a '' s = a +ᵥ (A '' s) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨A y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩

private theorem extremePoints_affineImage (A : Plane ≃L[ℝ] Plane) (a : Plane)
    (s : Set Plane) :
    (affineMap A a '' s).extremePoints ℝ = affineMap A a '' s.extremePoints ℝ := by
  rw [affineMap_image, extremePoints_vadd, ← image_extremePoints A, affineMap_image]

theorem vertexSet_affineImage (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane)
    (a : Plane) :
    vertexSet (affineImage K A a).support = affineMap A a '' vertexSet K.support := by
  have forward (B : Plane ≃L[ℝ] Plane) (b : Plane) (s : Set Plane) :
      vertexSet (affineMap B b '' s) ⊆ affineMap B b '' vertexSet s := by
    intro x hx
    let h : Plane ≃ₜ Plane := B.toHomeomorph.trans (Homeomorph.addLeft b)
    obtain ⟨y, rfl⟩ := h.surjective x
    refine ⟨y, ?_, rfl⟩
    change ∀ T : Triangulation s, ∃ t ∈ T.pieces, y ∈ t.extremePoints ℝ
    intro T
    obtain ⟨t, ht, hxt⟩ := hx (mappedTriangulation T B b)
    simp only [mappedTriangulation, Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨u, hu, ?_⟩
    rw [extremePoints_affineImage] at hxt
    exact (affineMap_injective B b).mem_set_image.mp hxt
  apply Subset.antisymm
  · exact forward A a K.support
  · rintro x ⟨y, hy, rfl⟩
    have hi := forward A.symm (-A.symm a) (affineMap A a '' K.support)
    rw [affineMap_inverse] at hi
    obtain ⟨z, hz, heq⟩ := hi hy
    have hpoint : affineMap A a y = z := by
      rw [← heq]
      simp [affineMap]
    rwa [hpoint]

theorem boundaryLocallyStraightAt_affineImage_iff
    (A : Plane ≃L[ℝ] Plane) (a : Plane) (D : Set Plane) (x : Plane) :
    BoundaryLocallyStraightAt (affineMap A a '' D) (affineMap A a x) ↔
      BoundaryLocallyStraightAt D x := by
  have forward (B : Plane ≃L[ℝ] Plane) (b : Plane) (E : Set Plane) (y : Plane)
      (hs : BoundaryLocallyStraightAt E y) :
      BoundaryLocallyStraightAt (affineMap B b '' E) (affineMap B b y) := by
    obtain ⟨L, hy, hdim, hlocal⟩ := hs
    let f : Plane ≃ᵃ[ℝ] Plane :=
      B.toLinearEquiv.toAffineEquiv.trans (AffineEquiv.constVAdd ℝ Plane b)
    let h : Plane ≃ₜ Plane := B.toHomeomorph.trans (Homeomorph.addLeft b)
    refine ⟨L.map f.toAffineMap, AffineSubspace.mem_map_of_mem f.toAffineMap hy, ?_, ?_⟩
    · rw [AffineSubspace.map_direction]
      change Module.finrank ℝ (L.direction.map B.toLinearMap) = 1
      rw [B.toLinearEquiv.finrank_map_eq, hdim]
    · have ht : Tendsto h.symm (𝓝 (h y)) (𝓝 y) := by
        simpa only [h.symm_apply_apply] using h.symm.continuous.tendsto (h y)
      have hevent := ht.eventually hlocal
      filter_upwards [hevent] with z hz
      have hzfront : z ∈ frontier (affineMap B b '' E) ↔ h.symm z ∈ frontier E := by
        change z ∈ frontier (h '' E) ↔ h.symm z ∈ frontier E
        rw [← h.image_frontier, h.image_eq_preimage_symm]
        rfl
      have hzL : z ∈ L.map f.toAffineMap ↔ h.symm z ∈ L := by
        change z ∈ f '' (L : Set Plane) ↔ h.symm z ∈ L
        change z ∈ h '' (L : Set Plane) ↔ h.symm z ∈ L
        rw [h.image_eq_preimage_symm]
        rfl
      exact hzfront.trans (hz.trans hzL.symm)
  constructor
  · intro hs
    have hi := forward A.symm (-A.symm a) _ _ hs
    rw [affineMap_inverse] at hi
    simpa [affineMap] using hi
  · exact forward A a D x

private theorem polygonalRegion_eq_of_support_eq {K L : PolygonalRegion}
    (h : K.support = L.support) : K = L := by
  cases K
  cases L
  simpa only [PolygonalRegion.mk.injEq] using h

theorem tilesOn_affineImage_iff
    (K : PolygonalRegion) (A : Plane ≃L[ℝ] Plane) (a : Plane) (S D : Set Plane) :
    TilesOn (affineImage K A a) (A '' S) (affineMap A a '' D) ↔
      TilesOn K S D := by
  have tileOpen (L : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (b v : Plane) :
      B v +ᵥ (affineImage L B b).openCarrier =
        affineMap B b '' (v +ᵥ L.openCarrier) := by
    rw [affineImage_openCarrier, affineMap_vadd]
  have forward (L : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (b : Plane)
      (T E : Set Plane) (hT : TilesOn L T E) :
      TilesOn (affineImage L B b) (B '' T) (affineMap B b '' E) := by
    refine ⟨hT.1.image B, ?_, ?_⟩
    · apply (isPacking_iff_openCarrier_disjoint _ _).mpr
      rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hvw
      rw [tileOpen, tileOpen]
      apply disjoint_image_of_injective (affineMap_injective B b)
      exact (isPacking_iff_openCarrier_disjoint L T).mp hT.2.1 hv hw
        (fun h => hvw (congrArg B h))
    · apply (affineMap_ae_iff B b _).mp
      filter_upwards [hT.2.2] with x hx
      rw [(affineMap_injective B b).mem_set_image]
      have hunion :
          (∃ t : B '' T, affineMap B b x ∈
            (t : Plane) +ᵥ (affineImage L B b).openCarrier) ↔
          ∃ v : T, x ∈ (v : Plane) +ᵥ L.openCarrier := by
        constructor
        · rintro ⟨t, ht⟩
          obtain ⟨v, hv, heq⟩ := t.2
          have ht' : affineMap B b x ∈ B v +ᵥ (affineImage L B b).openCarrier :=
            heq.symm ▸ ht
          rw [tileOpen, (affineMap_injective B b).mem_set_image] at ht'
          exact ⟨⟨v, hv⟩, ht'⟩
        · rintro ⟨v, hv⟩
          refine ⟨⟨B v, ⟨v, v.2, rfl⟩⟩, ?_⟩
          change affineMap B b x ∈ B v +ᵥ (affineImage L B b).openCarrier
          rw [tileOpen, (affineMap_injective B b).mem_set_image]
          exact hv
      exact hx.trans hunion.symm
  constructor
  · intro h
    have hi := forward (affineImage K A a) A.symm (-A.symm a)
      (A '' S) (affineMap A a '' D) h
    have hk : affineImage (affineImage K A a) A.symm (-A.symm a) = K := by
      have hs : (affineImage (affineImage K A a) A.symm (-A.symm a)).support =
          K.support := affineMap_inverse A a K.support
      exact polygonalRegion_eq_of_support_eq hs
    rw [hk, affineMap_inverse] at hi
    simpa only [image_image, A.symm_apply_apply, image_id'] using hi
  · exact forward K A a S D

theorem HasFLC.linearImage_iff (A : Plane ≃L[ℝ] Plane) (S : Set Plane) :
    HasFLC (A '' S) ↔ HasFLC S := by
  have forward (B : Plane ≃L[ℝ] Plane) {T : Set Plane} (hT : HasFLC T) :
      HasFLC (B '' T) := by
    have localImage {U : Set Plane}
        (hU : ∀ Q : Set Plane, Bornology.IsBounded Q → (U ∩ Q).Finite) :
        ∀ Q : Set Plane, Bornology.IsBounded Q → ((B '' U) ∩ Q).Finite := by
      intro Q hQ
      have hf := hU (B.symm '' Q) (B.symm.lipschitz.isBounded_image hQ)
      apply (hf.image B).subset
      rintro x ⟨⟨y, hy, rfl⟩, hQy⟩
      exact ⟨y, ⟨hy, ⟨B y, hQy, B.symm_apply_apply y⟩⟩, rfl⟩
    refine ⟨localImage hT.1, ?_⟩
    have hdiff : ∀ Q : Set Plane, Bornology.IsBounded Q → ((T - T) ∩ Q).Finite := by
      intro Q hQ
      obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : Plane)
      exact (hT.2 (max R 1) (lt_of_lt_of_le zero_lt_one (le_max_right R 1))).subset
        (inter_subset_inter_right _ (hR.trans (Metric.closedBall_subset_closedBall
          (le_max_left R 1))))
    have heq : B '' (T - T) = (B '' T) - (B '' T) := by
      ext x
      constructor
      · rintro ⟨y, ⟨v, hv, w, hw, rfl⟩, rfl⟩
        exact ⟨B v, ⟨v, hv, rfl⟩, B w, ⟨w, hw, rfl⟩, (map_sub B v w).symm⟩
      · rintro ⟨y, ⟨v, hv, rfl⟩, z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨v - w, ⟨v, hv, w, hw, rfl⟩, map_sub B v w⟩
    intro R _
    rw [← heq]
    exact localImage hdiff _ Metric.isBounded_closedBall
  constructor
  · intro h
    have := forward A.symm h
    simpa only [image_image, A.symm_apply_apply, image_id'] using this
  · exact forward A

theorem periodGroup_affineImage (A : Plane ≃L[ℝ] Plane) (a : Plane)
    (S : Set Plane) :
    periodGroup (affineMap A a '' S) =
      (periodGroup S).map A.toLinearEquiv.toAddEquiv.toAddMonoidHom := by
  ext u
  obtain ⟨v, rfl⟩ := A.surjective u
  change (A v +ᵥ (affineMap A a '' S) = affineMap A a '' S) ↔
    ∃ w, w ∈ periodGroup S ∧ A w = A v
  rw [← affineMap_vadd]
  constructor
  · intro h
    exact ⟨v, (affineMap_injective A a).image_injective h, rfl⟩
  · rintro ⟨w, hw, h⟩
    have := A.injective h
    subst w
    change v +ᵥ S = S at hw
    rw [hw]

theorem isLatticePeriodic_affineImage_iff (A : Plane ≃L[ℝ] Plane) (a : Plane)
    (S : Set Plane) :
    IsLatticePeriodic (affineMap A a '' S) ↔ IsLatticePeriodic S := by
  have forward (B : Plane ≃L[ℝ] Plane) (b : Plane) {T : Set Plane}
      (hT : IsLatticePeriodic T) : IsLatticePeriodic (affineMap B b '' T) := by
    obtain ⟨L, hL⟩ := hT
    let M : PlanarLattice := ⟨B ∘ L.basis,
      L.independent.map' B.toLinearMap (LinearMap.ker_eq_bot.mpr B.injective)⟩
    refine ⟨M, ?_⟩
    have hm : M.toAddSubgroup = L.toAddSubgroup.map
        B.toLinearEquiv.toAddEquiv.toAddMonoidHom := by
      unfold PlanarLattice.toAddSubgroup
      rw [AddMonoidHom.map_closure, ← range_comp]
      rfl
    rw [hm, periodGroup_affineImage]
    rintro x ⟨y, hy, rfl⟩
    exact ⟨y, hL hy, rfl⟩
  constructor
  · intro h
    have := forward A.symm (-A.symm a) h
    rwa [affineMap_inverse] at this
  · exact forward A a

theorem weaklyPeriodic_affineImage_iff (A : Plane ≃L[ℝ] Plane) (a : Plane)
    (S : Set Plane) :
    Tiling.RationalPolygonal.WeaklyPeriodic (affineMap A a '' S) ↔
      Tiling.RationalPolygonal.WeaklyPeriodic S := by
  have forward (B : Plane ≃L[ℝ] Plane) (b : Plane) {T : Set Plane}
      (hT : Tiling.RationalPolygonal.WeaklyPeriodic T) :
      Tiling.RationalPolygonal.WeaklyPeriodic (affineMap B b '' T) := by
    obtain ⟨D⟩ := hT
    refine ⟨{
      numberOfParts := D.numberOfParts
      part := fun i => affineMap B b '' D.part i
      period := fun i => B (D.period i)
      period_ne_zero := fun i hz => D.period_ne_zero i (B.injective (by simpa using hz))
      periodic_part := ?_
      pairwiseDisjoint := ?_
      iUnion_parts := ?_ }⟩
    · intro i x
      obtain ⟨y, rfl⟩ := (Homeomorph.addLeft b).surjective x
      obtain ⟨z, rfl⟩ := B.surjective y
      have hmem (w : Plane) : affineMap B b w ∈ affineMap B b '' D.part i ↔
          w ∈ D.part i := (affineMap_injective B b).mem_set_image
      change b + B z + B (D.period i) ∈ affineMap B b '' D.part i ↔
        b + B z ∈ affineMap B b '' D.part i
      rw [show b + B z + B (D.period i) = affineMap B b (z + D.period i) by
        simp [affineMap, map_add, add_assoc]]
      exact (hmem _).trans ((D.periodic_part i z).trans (hmem _).symm)
    · intro i _ j _ hij
      change Disjoint (affineMap B b '' D.part i) (affineMap B b '' D.part j)
      rw [disjoint_left]
      rintro x ⟨y, hy, rfl⟩ ⟨z, hz, heq⟩
      have heq' := affineMap_injective B b heq
      subst z
      exact disjoint_left.mp (D.pairwiseDisjoint (mem_univ i) (mem_univ j) hij) hy hz
    · rw [← image_iUnion, D.iUnion_parts]
  constructor
  · intro h
    have := forward A.symm (-A.symm a) h
    rwa [affineMap_inverse] at this
  · exact forward A a

end Tiling.Polygonal

-- Exact owner/dependency axiom audit.

/-! Independently reviewed supplemental lemmas (outside frozen362). -/
open Tiling
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal

namespace Tiling.Polygonal

/-- A frontier point of the regularized carrier of a polygonal packing belongs
to the translated frontier of one of its placed tiles. -/
theorem exists_tile_frontier_of_mem_frontier_regularSupport (K : PolygonalRegion)
    {S : Set Plane}
    (hp : IsPacking K.prototileFamily (K.placements S)) {x : Plane}
    (hx : x ∈ frontier (regularSupport K S)) :
    ∃ s ∈ S, x - s ∈ frontier K.support := by
  have hop : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro t
    exact (Homeomorph.addLeft (t : Plane)).isOpenMap _ isOpen_interior
  have hsub : openUnion K S ⊆ regularSupport K S :=
    interior_maximal subset_closure hop
  have hxcl := frontier_subset_closure hx
  change x ∈ closure (interior (closure (openUnion K S))) at hxcl
  have hxcl' := closure_mono (s := interior (closure (openUnion K S)))
    (t := closure (openUnion K S)) interior_subset hxcl
  rw [closure_closure, closure_openUnion_eq_iUnion_support hp] at hxcl'
  obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hxcl'
  have hxnot : x ∉ regularSupport K S := by
    exact fun h => Set.disjoint_left.mp disjoint_interior_frontier
      (by simpa only [regularSupport, interior_interior] using h) hx
  have hxs : x - (s : Plane) ∈ K.support := by
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg, add_comm] using hs
  refine ⟨s, s.2, K.isPolygonal.isClosed.frontier_eq ▸ ⟨hxs, ?_⟩⟩
  intro hi
  apply hxnot
  apply hsub
  apply Set.mem_iUnion.mpr
  refine ⟨s, ?_⟩
  refine ⟨x - (s : Plane), hi, ?_⟩
  simp [vadd_eq_add]

private theorem frontierLevel_segmentTwoPoints (π : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    {a b x y : Plane} (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b)
    (hπx : π x = c) (hπy : π y = c) (hxy : x ≠ y) : π a = c ∧ π b = c := by
  rw [segment_eq_image ℝ] at hx hy
  obtain ⟨s, _, rfl⟩ := hx
  obtain ⟨t, _, rfl⟩ := hy
  have hst : s ≠ t := by
    intro he
    exact hxy (by rw [he])
  simp only [map_add, map_smul, smul_eq_mul] at hπx hπy
  have he : (s - t) * (π b - π a) = 0 := by nlinarith
  have hab : π b = π a := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hst))
  rw [hab] at hπx
  have ha : π a = c := by nlinarith
  exact ⟨ha, hab.trans ha⟩

private theorem frontierLevel_segmentFinite (π : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (a b : Plane) (h : ¬ (π a = c ∧ π b = c)) :
    (segment ℝ a b ∩ {x | π x = c}).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  by_contra hxy
  exact h (frontierLevel_segmentTwoPoints π c hx.1 hy.1 hx.2 hy.2 hxy)

private theorem frontierLevel_finiteCoverCoincident (π : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (F : Finset (Plane × Plane)) {C : Set Plane} (hC : C.Infinite)
    (hlevel : C ⊆ {x | π x = c})
    (hcover : C ⊆ ⋃ e ∈ F, segment ℝ e.1 e.2) :
    ∃ e ∈ F, π e.1 = c ∧ π e.2 = c := by
  classical
  by_contra h
  push Not at h
  have hf : (⋃ e ∈ F, segment ℝ e.1 e.2 ∩ {x | π x = c}).Finite :=
    F.finite_toSet.biUnion fun e he => frontierLevel_segmentFinite π c e.1 e.2
      (by intro hh; exact h e he hh.1 hh.2)
  apply hC
  apply hf.subset
  intro x hx
  have hh := hcover hx
  simp only [Set.mem_iUnion] at hh
  obtain ⟨e, heF, hseg⟩ := hh
  exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨heF, ⟨hseg, hlevel hx⟩⟩⟩

/-- Every full frontier level of a polygonal packing has a translated intrinsic vertex
at that level whose placement centre is uniformly close to the chosen base point.

The nonzero kernel vector supplies an infinite compact tangent interval. Local finiteness
reduces its tile-boundary cover to finitely many translated intrinsic segments, one of
which must coincide with the level. No finite-local-complexity or decoration is needed. -/
theorem frontierLevel_has_intrinsicVertex_of_supportBound
    (K : PolygonalRegion) (S : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →ₗ[ℝ] ℝ) (e : Plane) (he : e ≠ 0) (hπe : π e = 0)
    (B : ℝ) (hbound : ∀ z ∈ K.support, ‖z‖ ≤ B) :
    ∀ x : Plane,
      ({y | π y = π x} ⊆ frontier (regularSupport K S)) →
        ∃ v q : Plane, v ∈ vertexSet K.support ∧ q ∈ S ∧
          π (v + q) = π x ∧ dist q x ≤ B + ‖e‖ + 1 := by
  classical
  obtain ⟨F, hF, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let R : ℝ := B + ‖e‖ + 1
  intro x hline
  let Q : Set Plane := S ∩ Metric.closedBall x R
  have hQ : Q.Finite := (packing_centres_locallyFinite hp).1 _ Metric.isBounded_closedBall
  let H : Finset (Plane × Plane) :=
    (hQ.toFinset ×ˢ F).image (fun q => (q.1 + q.2.1, q.1 + q.2.2))
  let C : Set Plane := (fun t : ℝ => x + t • e) '' Set.Icc 0 1
  have hinj : Function.Injective (fun t : ℝ => x + t • e) := by
    intro s t hst
    exact smul_left_injective ℝ he (add_left_cancel hst)
  have hC : C.Infinite :=
    Set.Icc_infinite (show (0 : ℝ) < 1 by norm_num) |>.image hinj.injOn
  have hlevel : C ⊆ {y | π y = π x} := by
    rintro y ⟨t, ht, rfl⟩
    change π (x + t • e) = π x
    simp only [map_add, map_smul, hπe, smul_zero, add_zero]
  have hcover : C ⊆ ⋃ q ∈ H, segment ℝ q.1 q.2 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := hy
    have hdist : dist (x + t • e) x ≤ ‖e‖ := by
      simp only [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg e) ht.2
    obtain ⟨s, hs, hsb⟩ := exists_tile_frontier_of_mem_frontier_regularSupport K hp
      (hline (hlevel ⟨t, ht, rfl⟩))
    have hsbSupport := K.isPolygonal.isClosed.frontier_subset hsb
    have hdistys : dist (x + t • e) s ≤ B := by
      simpa only [dist_eq_norm] using hbound _ hsbSupport
    have hsQ : s ∈ Q := by
      refine ⟨hs, ?_⟩
      change dist s x ≤ R
      have hd := dist_triangle s (x + t • e) x
      rw [dist_comm s (x + t • e)] at hd
      dsimp [R]
      linarith
    rw [hfront] at hsb
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hsb
    obtain ⟨hqF, hseg⟩ := Set.mem_iUnion.mp hq
    have hqH : (s + q.1, s + q.2) ∈ H := by
      exact Finset.mem_image.mpr ⟨(s, q), Finset.mem_product.mpr
        ⟨hQ.mem_toFinset.mpr hsQ, hqF⟩, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(s + q.1, s + q.2), Set.mem_iUnion.mpr ⟨hqH, ?_⟩⟩
    have hh := (mem_segment_translate ℝ s).mpr hseg
    simpa only [add_sub_cancel] using hh
  obtain ⟨q, hqH, hqπ⟩ := frontierLevel_finiteCoverCoincident π (π x) H hC hlevel hcover
  obtain ⟨⟨s, p⟩, hpH, rfl⟩ := Finset.mem_image.mp hqH
  obtain ⟨hsQ, hpF⟩ := Finset.mem_product.mp hpH
  have hs := hQ.mem_toFinset.mp hsQ
  have hpV := (hF p hpF).2.1
  have hpSupport : p.1 ∈ K.support := K.isPolygonal.isClosed.frontier_subset
    ((hF p hpF).2.2.2 (left_mem_segment ℝ p.1 p.2))
  refine ⟨p.1, s, hpV, hs.1, ?_, ?_⟩
  · simpa only [add_comm] using hqπ.1
  · exact Metric.mem_closedBall.mp hs.2

theorem frontierLevel_has_bounded_intrinsicVertex
    (K : PolygonalRegion) (S : Set Plane)
    (hp : IsPacking K.prototileFamily (K.placements S))
    (π : Plane →ₗ[ℝ] ℝ) (e : Plane) (he : e ≠ 0) (hπe : π e = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Plane,
      ({y | π y = π x} ⊆ frontier (regularSupport K S)) →
        ∃ v q : Plane, v ∈ vertexSet K.support ∧ q ∈ S ∧
          π (v + q) = π x ∧ dist q x ≤ C := by
  obtain ⟨B, hB, hbound⟩ := K.isPolygonal.isCompact.isBounded.exists_pos_norm_le
  exact ⟨B + ‖e‖ + 1, by positivity,
    frontierLevel_has_intrinsicVertex_of_supportBound K S hp π e he hπe B hbound⟩

end Tiling.Polygonal
