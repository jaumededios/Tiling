import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Tiling.Geometry.Sliding

set_option linter.style.header false

/-!
# Connected polygonal tilings

This file formalizes the merging step inspired by Lemma 2.7 of *Periodicity and decidability of
translational tilings by rational polygonal sets* (arXiv:2408.02151).  Once the plate carriers are
known to be invariant along a common direction, a connected graph of possible vertex alignments
supplies compatible shifts which merge all plates.

The finite-family statement is a genuine extension of the published monotile lemma.  The generic
offset-potential construction and the lift from connected plates to connected placement vertices
are proved here.  Carrier contact is realized by alignable placed vertices using the local planar
geometry developed in the preceding modules.
-/

open Filter MeasureTheory Set
open scoped Pointwise

namespace Tiling

universe u v

namespace PolygonalProtoTiling

variable {P : Type u} (A : PolygonalProtoTiling P)

/-- A relative displacement `r` aligns a vertex from plate `C` with a vertex from plate `D` along
the direction `v`. -/
private def AlignsAlong (v : Plane) (C D : A.Plate) (r : ℝ) : Prop :=
  ∃ i : C, ∃ j : D,
    ((r • v +ᵥ A.placedVertexSet (i : A.placements)) ∩
      A.placedVertexSet (j : A.placements)).Nonempty

private theorem alignsAlong_symm {v : Plane} {C D : A.Plate} {r : ℝ}
    (h : A.AlignsAlong v C D r) : A.AlignsAlong v D C (-r) := by
  obtain ⟨i, j, x, hxi, hxj⟩ := h
  refine ⟨j, i, ⟨-(r • v) +ᵥ x, ?_, ?_⟩⟩
  · rw [mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_smul, neg_neg, vadd_vadd, add_neg_cancel, zero_vadd] using hxj
  · exact (mem_vadd_set_iff_neg_vadd_mem.mp hxi)

/-- Plates are adjacent when some relative displacement aligns a pair of their vertices. -/
private def alignmentGraph (v : Plane) : SimpleGraph A.Plate :=
  SimpleGraph.fromRel fun C D ↦ ∃ r : ℝ, A.AlignsAlong v C D r

/-- The graph whose edges record nonempty intersections of distinct plate carriers. -/
private def carrierContactGraph : SimpleGraph A.Plate :=
  SimpleGraph.intersectionGraph A.plateCarrier

/-- The plate-carrier contact graph is connected. -/
private theorem carrierContactGraph_connected [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    A.carrierContactGraph.Connected :=
  SimpleGraph.connected_intersectionGraph A.plateCarrier
    (A.locallyFinite_plateCarrier hA.isPacking)
    (A.plateCarrier_isClosed hA.isPacking)
    A.plateCarrier_nonempty
    (A.iUnion_plateCarrier_eq_univ hA)

private theorem not_mem_interior_left_of_mem_right_of_aedisjoint
    {s t : Set Plane} (htregular : closure (interior t) = t)
    (had : AEDisjoint volume s t) {x : Plane} (hxt : x ∈ t) :
    x ∉ interior s := by
  intro hxs
  rw [← htregular] at hxt
  obtain ⟨y, hyt, hys⟩ := mem_closure_iff.mp hxt (interior s) isOpen_interior hxs
  have hne : volume (interior s ∩ interior t) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero volume ⟨y, hyt, hys⟩
  exact hne (measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset) had)

/-- A boundary line of an invariant plate contains a placed vertex of that plate.  The proof takes a
finite set of tiles covering a compact interval of the line, then looks at the right endpoint of the
connected component of its parameter preimage. -/
private theorem exists_placedVertex_on_invariant_contact_line [Finite P] {v : Plane}
    (hA : IsTiling A.prototiles A.placements) (hv : A.IsSlidingDirection v)
    {C D : A.Plate} (hCD : C ≠ D) {x : Plane}
    (hxC : x ∈ A.plateCarrier C) (hxD : x ∈ A.plateCarrier D) :
    ∃ (i : C) (t : ℝ), t • v +ᵥ x ∈ A.placedVertexSet (i : A.placements) := by
  classical
  let φ : ℝ → Plane := fun t ↦ t • v +ᵥ x
  have hφ : Continuous φ := by
    fun_prop
  have hlineC (t : ℝ) : φ t ∈ A.plateCarrier C := by
    rw [show φ t = t • v +ᵥ x from rfl, ← hv.vadd_plateCarrier C t,
      Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_vadd_vadd] using hxC
  have hlineD (t : ℝ) : φ t ∈ A.plateCarrier D := by
    rw [show φ t = t • v +ᵥ x from rfl, ← hv.vadd_plateCarrier D t,
      Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [neg_vadd_vadd] using hxD
  let segment : Set Plane := φ '' Set.Icc (0 : ℝ) 1
  have hsegment_compact : IsCompact segment :=
    isCompact_Icc.image hφ
  let S : Set A.placements :=
    {i | i ∈ C ∧ (placedTile A.prototiles i.1 ∩ segment).Nonempty}
  have hSfinite : S.Finite := by
    apply ((A.locallyFinite_placedTile hA.isPacking).finite_nonempty_inter_compact
      hsegment_compact).subset
    intro i hi
    exact hi.2
  have hsegment_subset : segment ⊆ A.placementCarrier S := by
    rintro y ⟨t, ht, rfl⟩
    obtain ⟨i, hiC, hi⟩ := A.mem_plateCarrier_iff.mp (hlineC t)
    apply A.mem_placementCarrier_iff.mpr
    refine ⟨i, ⟨hiC, ?_⟩, hi⟩
    exact ⟨φ t, hi, ⟨t, ht, rfl⟩⟩
  have hSsub : S ⊆ (C : Set A.placements) := fun _ hi ↦ hi.1
  have hcarrierS_subset : A.placementCarrier S ⊆ A.plateCarrier C := by
    intro y hy
    obtain ⟨i, hiS, hyi⟩ := A.mem_placementCarrier_iff.mp hy
    exact A.mem_plateCarrier_iff.mpr ⟨i, hSsub hiS, hyi⟩
  have hcarrierS_closed : IsClosed (A.placementCarrier S) :=
    A.placementCarrier_isClosed hA.isPacking S
  have hcarrierS_bounded : Bornology.IsBounded (A.placementCarrier S) := by
    rw [placementCarrier, Set.iUnion_subtype]
    exact (Bornology.isBounded_biUnion hSfinite).2 fun i hi ↦
      (A.isPolygonal_placedTile i.1).isBounded
  let F : Set ℝ := φ ⁻¹' A.placementCarrier S
  have hFclosed : IsClosed F := hcarrierS_closed.preimage hφ
  have hzeroF : (0 : ℝ) ∈ F := by
    apply hsegment_subset
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hF_bddAbove : BddAbove F := by
    obtain ⟨R, hR⟩ := hcarrierS_bounded.subset_closedBall x
    refine ⟨R / ‖v‖, fun t ht ↦ ?_⟩
    have hdist := hR ht
    rw [Metric.mem_closedBall] at hdist
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv.ne_zero
    have habs : |t| * ‖v‖ ≤ R := by
      simpa [F, φ, dist_eq_norm, norm_smul, Real.norm_eq_abs, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hdist
    have ht_le_abs : t ≤ |t| := le_abs_self t
    apply (le_div_iff₀ hvnorm).2
    exact (mul_le_mul_of_nonneg_right ht_le_abs hvnorm.le).trans habs
  let J : Set ℝ := connectedComponentIn F 0
  have hzeroJ : (0 : ℝ) ∈ J := mem_connectedComponentIn hzeroF
  have honeJ : (1 : ℝ) ∈ J := by
    have hsub : Set.Icc (0 : ℝ) 1 ⊆ connectedComponentIn F 0 :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr zero_le_one) fun t ht ↦ hsegment_subset ⟨t, ht, rfl⟩
    exact hsub (right_mem_Icc.mpr zero_le_one)
  have hJclosed : IsClosed J := by
    dsimp only [J]
    rw [connectedComponentIn_eq_image hzeroF]
    exact hFclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hJ_bddAbove : BddAbove J := hF_bddAbove.mono (connectedComponentIn_subset F 0)
  have hJnonempty : J.Nonempty := ⟨0, hzeroJ⟩
  let b : ℝ := sSup J
  have hbGreatest : IsGreatest J b := hJclosed.isGreatest_csSup hJnonempty hJ_bddAbove
  have hbJ : b ∈ J := hbGreatest.1
  have hone_le_b : (1 : ℝ) ≤ b := hbGreatest.2 honeJ
  have hbpos : 0 < b := zero_lt_one.trans_le hone_le_b
  have hline_not_interior_C (t : ℝ) : φ t ∉ interior (A.plateCarrier C) := by
    exact not_mem_interior_left_of_mem_right_of_aedisjoint
      (A.plateCarrier_closure_interior hA.isPacking D)
      (A.plateCarrier_aedisjoint hA hCD) (hlineD t)
  have hfrontier_of_mem_J {t : ℝ} (ht : t ∈ J) :
      φ t ∈ frontier (A.placementCarrier S) := by
    have htF : t ∈ F := connectedComponentIn_subset F 0 ht
    rw [frontier, hcarrierS_closed.closure_eq]
    exact ⟨htF, fun htint ↦ hline_not_interior_C t
      (interior_mono hcarrierS_subset htint)⟩
  have hbfrontier : φ b ∈ frontier (A.placementCarrier S) :=
    hfrontier_of_mem_J hbJ
  have hbnotstraight : ¬BoundaryLocallyStraightAt (A.placementCarrier S) (φ b) := by
    rintro ⟨L, hbL, _, hlocal⟩
    have hparam :
        {t : ℝ | φ t ∈ frontier (A.placementCarrier S) ↔ φ t ∈ (L : Set Plane)} ∈
          nhds b := by
      exact hφ.continuousAt.preimage_mem_nhds hlocal
    obtain ⟨l, u, ⟨hlb, hbu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hparam
    obtain ⟨t₁, ht₁l, ht₁b⟩ := exists_between (max_lt hlb hbpos)
    have ht₁nonneg : 0 ≤ t₁ := (le_max_right l 0).trans ht₁l.le
    have ht₁J : t₁ ∈ J :=
      isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ⟨ht₁nonneg, ht₁b.le⟩
    have ht₁frontier := hfrontier_of_mem_J ht₁J
    have ht₁L : φ t₁ ∈ L := (hlu ⟨(le_max_left l 0).trans_lt ht₁l, ht₁b.trans hbu⟩) |>.mp
      ht₁frontier
    obtain ⟨t₂, hbt₂, ht₂u⟩ := exists_between hbu
    have lineMap_eq (t : ℝ) :
        AffineMap.lineMap (φ b) (φ t₁) ((t - b) / (t₁ - b)) = φ t := by
      have ht₁bne : t₁ - b ≠ 0 := sub_ne_zero.mpr ht₁b.ne
      simp only [AffineMap.lineMap_apply, φ, vsub_eq_sub, vadd_eq_add]
      rw [add_sub_add_right_eq_sub, ← sub_smul, smul_smul,
        div_mul_cancel₀ (t - b) ht₁bne, sub_smul]
      abel
    have ht₂L : φ t₂ ∈ L := by
      rw [← lineMap_eq t₂]
      exact AffineMap.lineMap_mem _ hbL ht₁L
    have hintervalF : Set.Icc b t₂ ⊆ F := by
      intro t ht
      have htL : φ t ∈ L := by
        rw [← lineMap_eq t]
        exact AffineMap.lineMap_mem _ hbL ht₁L
      have htlocal : t ∈ Set.Ioo l u := ⟨hlb.trans_le ht.1, ht.2.trans_lt ht₂u⟩
      have htfrontier : φ t ∈ frontier (A.placementCarrier S) := (hlu htlocal).mpr htL
      change φ t ∈ A.placementCarrier S
      rw [← hcarrierS_closed.closure_eq]
      exact frontier_subset_closure htfrontier
    have ht₂_component_b : t₂ ∈ connectedComponentIn F b := by
      exact isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hbt₂.le) hintervalF (right_mem_Icc.mpr hbt₂.le)
    have hcomponents : J = connectedComponentIn F b := connectedComponentIn_eq hbJ
    have ht₂J : t₂ ∈ J := hcomponents.symm ▸ ht₂_component_b
    exact (not_lt_of_ge (hbGreatest.2 ht₂J)) hbt₂
  obtain ⟨i, _, hiS, _, hvertex, _⟩ :=
    A.exists_vertices_across_of_not_boundaryLocallyStraightAt hA S hbfrontier hbnotstraight
  exact ⟨⟨i, hSsub hiS⟩, b, hvertex⟩

/-- A contact of two invariant plate carriers can be realized by aligning tile vertices along the
sliding direction.

This is the supporting-line geometric input to the merging proof. -/
private theorem alignsAlong_of_carrierContact [Finite P] {v : Plane}
    (hA : IsTiling A.prototiles A.placements) (hv : A.IsSlidingDirection v)
    {C D : A.Plate} (hCD : A.carrierContactGraph.Adj C D) :
    ∃ r : ℝ, A.AlignsAlong v C D r := by
  rw [carrierContactGraph, SimpleGraph.intersectionGraph_adj] at hCD
  obtain ⟨hCDne, x, hxC, hxD⟩ := hCD
  obtain ⟨i, tC, hi⟩ :=
    A.exists_placedVertex_on_invariant_contact_line hA hv hCDne hxC hxD
  obtain ⟨j, tD, hj⟩ :=
    A.exists_placedVertex_on_invariant_contact_line hA hv hCDne.symm hxD hxC
  refine ⟨tD - tC, i, j, ⟨tD • v +ᵥ x, ?_, hj⟩⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  convert hi using 1
  simp only [sub_smul, vadd_eq_add]
  abel

/-- The planar carrier-contact argument makes the alignment graph connected.

The topological intersection-graph step is generic and proved separately; only realization of a
carrier contact by alignable vertices is planar geometry. -/
private theorem alignmentGraph_connected [Finite P] {v : Plane}
    (hA : IsTiling A.prototiles A.placements) (hv : A.IsSlidingDirection v) :
    (A.alignmentGraph v).Connected := by
  apply (A.carrierContactGraph_connected hA).mono
  intro C D hCD
  obtain ⟨r, hr⟩ := A.alignsAlong_of_carrierContact hA hv hCD
  rw [alignmentGraph, SimpleGraph.fromRel_adj]
  exact ⟨hCD.ne, Or.inl ⟨r, hr⟩⟩

/-- A connected symmetric offset relation admits a potential whose realized-offset graph is
connected. -/
private theorem exists_potential_connected {V : Type u} {Γ : Type v} [AddCommGroup Γ]
    (R : V → V → Γ → Prop)
    (hR_symm : ∀ ⦃x y d⦄, R x y d → R y x (-d))
    (hG : (SimpleGraph.fromRel fun x y ↦ ∃ d, R x y d).Connected) :
    ∃ f : V → Γ,
      (SimpleGraph.fromRel fun x y ↦ R x y (f x - f y)).Connected := by
  classical
  let G := SimpleGraph.fromRel fun x y ↦ ∃ d, R x y d
  let root : V := Classical.choice hG.nonempty
  let walk : (x : V) → G.Walk root x := fun x ↦
    Classical.choose ((hG root x).exists_walk_length_eq_dist)
  have walk_length (x : V) : (walk x).length = G.dist root x :=
    Classical.choose_spec ((hG root x).exists_walk_length_eq_dist)
  let parent (x : V) : V := if x = root then root else (walk x).penultimate
  have parent_eq (x : V) (hx : x ≠ root) :
      parent x = (walk x).penultimate := by
    simp [parent, hx]
  have walk_not_nil (x : V) (hx : x ≠ root) : ¬(walk x).Nil :=
    SimpleGraph.Walk.not_nil_of_ne hx.symm
  have parent_adj (x : V) (hx : x ≠ root) : G.Adj (parent x) x := by
    rw [parent_eq x hx]
    exact (walk x).adj_penultimate (walk_not_nil x hx)
  have parent_dist_lt (x : V) (hx : x ≠ root) :
      G.dist root (parent x) < G.dist root x := by
    calc
      G.dist root (parent x) ≤ (walk x).dropLast.length := by
        rw [parent_eq x hx]
        exact G.dist_le _
      _ = (walk x).length - 1 := (walk x).length_dropLast
      _ < (walk x).length := Nat.sub_lt (by
        rw [walk_length]
        exact (hG root x).pos_dist_of_ne hx.symm) zero_lt_one
      _ = G.dist root x := walk_length x
  have edge_has_offset ⦃x y : V⦄ (hxy : G.Adj x y) : ∃ d, R x y d := by
    rw [show G = SimpleGraph.fromRel (fun x y ↦ ∃ d, R x y d) from rfl,
      SimpleGraph.fromRel_adj] at hxy
    rcases hxy.2 with h | h
    · exact h
    · rcases h with ⟨d, hd⟩
      exact ⟨-d, hR_symm hd⟩
  let offset (x : V) : Γ := if hx : x = root then 0 else
    Classical.choose (edge_has_offset (parent_adj x hx))
  have offset_spec (x : V) (hx : x ≠ root) :
      R (parent x) x (offset x) := by
    simp only [offset, dif_neg hx]
    exact Classical.choose_spec (edge_has_offset (parent_adj x hx))
  let f : V → Γ :=
    WellFounded.fix (measure fun x ↦ G.dist root x).wf fun x rec ↦
      if hx : x = root then 0
      else rec (parent x) (parent_dist_lt x hx) - offset x
  have f_eq (x : V) (hx : x ≠ root) :
      f x = f (parent x) - offset x := by
    dsimp only [f]
    rw [WellFounded.fix_eq]
    simp [hx]
  refine ⟨f, (SimpleGraph.connected_iff_exists_forall_reachable _).2
    ⟨root, fun x ↦ ?_⟩⟩
  induction x using (measure fun x ↦ G.dist root x).wf.induction with
  | h x ih =>
      by_cases hx : x = root
      · subst x
        exact SimpleGraph.Reachable.refl root
      · have hp :
            (SimpleGraph.fromRel fun x y ↦ R x y (f x - f y)).Adj (parent x) x := by
          rw [SimpleGraph.fromRel_adj]
          refine ⟨(parent_adj x hx).ne, Or.inl ?_⟩
          rw [f_eq x hx]
          simpa using offset_spec x hx
        exact (ih (parent x) (parent_dist_lt x hx)).trans hp.reachable

private theorem reachable_shiftedVertex_of_alignsAlong {v : Plane}
    (shift : A.Plate → ℝ) {C D : A.Plate}
    (h : A.AlignsAlong v C D (shift C - shift D)) :
    ∃ i : C, ∃ j : D,
      (A.shiftComponents v shift).vertexGraph.Reachable
        (A.shiftedVertex v shift (i : A.placements))
        (A.shiftedVertex v shift (j : A.placements)) := by
  obtain ⟨i, j, x, hxi, hxj⟩ := h
  refine ⟨i, j, ?_⟩
  by_cases hij : A.shiftedVertex v shift (i : A.placements) =
      A.shiftedVertex v shift (j : A.placements)
  · rw [hij]
  · apply SimpleGraph.Adj.reachable
    rw [(A.shiftComponents v shift).vertexGraph_adj]
    refine ⟨hij, ?_⟩
    rw [VertexConnected, A.placedVertexSet_shiftedVertex,
      A.placedVertexSet_shiftedVertex, i.2, j.2]
    refine ⟨shift D • v +ᵥ x, ?_, ?_⟩
    · rw [mem_vadd_set_iff_neg_vadd_mem]
      have hxbase : -((shift C - shift D) • v) +ᵥ x ∈
          A.placedVertexSet (i : A.placements) := by
        simpa only [mem_vadd_set_iff_neg_vadd_mem] using hxi
      convert hxbase using 1
      simp only [vadd_eq_add, sub_smul]
      abel
    · simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hxj

private theorem connected_shiftedGraph_of_realized_connected {v : Plane}
    (shift : A.Plate → ℝ)
    (hrealized :
      (SimpleGraph.fromRel fun C D ↦
        A.AlignsAlong v C D (shift C - shift D)).Connected) :
    (A.shiftComponents v shift).vertexGraph.Connected := by
  classical
  let B := A.shiftComponents v shift
  let f := A.shiftedVertexHom v shift
  let H := SimpleGraph.fromRel fun C D ↦ A.AlignsAlong v C D (shift C - shift D)
  let rep (C : A.Plate) : A.placements := Classical.choose C.nonempty_supp
  have rep_mem (C : A.Plate) : A.vertexGraph.connectedComponentMk (rep C) = C :=
    Classical.choose_spec C.nonempty_supp
  let q (C : A.Plate) : B.vertexGraph.ConnectedComponent :=
    B.vertexGraph.connectedComponentMk (f (rep C))
  have same_old_plate {i j : A.placements}
      (hij : A.vertexGraph.connectedComponentMk i =
        A.vertexGraph.connectedComponentMk j) :
      B.vertexGraph.connectedComponentMk (f i) =
        B.vertexGraph.connectedComponentMk (f j) := by
    apply SimpleGraph.ConnectedComponent.sound
    exact (SimpleGraph.ConnectedComponent.exact hij).map f
  have q_eq_of_direct_alignment {C D : A.Plate}
      (hCD : A.AlignsAlong v C D (shift C - shift D)) : q C = q D := by
    obtain ⟨i, j, hij⟩ := A.reachable_shiftedVertex_of_alignsAlong shift hCD
    calc
      q C = B.vertexGraph.connectedComponentMk (f (i : A.placements)) :=
        same_old_plate (rep_mem C |>.trans i.2.symm)
      _ = B.vertexGraph.connectedComponentMk (f (j : A.placements)) :=
        SimpleGraph.ConnectedComponent.sound hij
      _ = q D := (same_old_plate (rep_mem D |>.trans j.2.symm)).symm
  have q_eq_of_adj {C D : A.Plate} (hCD : H.Adj C D) : q C = q D := by
    rw [show H = SimpleGraph.fromRel
      (fun C D ↦ A.AlignsAlong v C D (shift C - shift D)) from rfl,
      SimpleGraph.fromRel_adj] at hCD
    rcases hCD.2 with h | h
    · exact q_eq_of_direct_alignment h
    · exact (q_eq_of_direct_alignment h).symm
  have q_eq_of_reachable {C D : A.Plate} (hCD : H.Reachable C D) : q C = q D := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at hCD
    induction hCD with
    | refl => rfl
    | tail _ hlast ih => exact ih.trans (q_eq_of_adj hlast)
  have hH : H.Connected := hrealized
  let C₀ : A.Plate := Classical.choice hH.nonempty
  let _ : Nonempty B.placements := ⟨f (rep C₀)⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨i, rfl⟩ := A.shiftedVertex_surjective v shift x
  obtain ⟨j, rfl⟩ := A.shiftedVertex_surjective v shift y
  apply SimpleGraph.ConnectedComponent.exact
  calc
    B.vertexGraph.connectedComponentMk (f i) = q (A.vertexGraph.connectedComponentMk i) :=
      (same_old_plate ((rep_mem _).trans rfl)).symm
    _ = q (A.vertexGraph.connectedComponentMk j) :=
      q_eq_of_reachable (hH _ _)
    _ = B.vertexGraph.connectedComponentMk (f j) :=
      same_old_plate ((rep_mem _).trans rfl)

/-- **Merge components by sliding.**  A sliding-direction certificate admits a component shift
whose placement graph is connected. -/
theorem IsSlidingDirection.exists_connected_component_shift [Finite P] {v : Plane}
    (hv : A.IsSlidingDirection v) (hA : IsTiling A.prototiles A.placements) :
    ∃ shift : A.Plate → ℝ,
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements ∧
      (A.shiftComponents v shift).vertexGraph.Connected := by
  obtain ⟨shift, hrealized⟩ := exists_potential_connected (A.AlignsAlong v)
    (fun _ _ _ h ↦ A.alignsAlong_symm h) (A.alignmentGraph_connected hA hv)
  exact ⟨shift, IsSlidingDirection.isTiling_shiftComponents A hv hA shift,
    A.connected_shiftedGraph_of_realized_connected shift hrealized⟩

/-- A connected component shift, retaining its reusable sliding-direction certificate. -/
theorem exists_connected_shift [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ (v : Plane) (_hv : A.IsSlidingDirection v) (shift : A.Plate → ℝ),
      IsTiling (A.shiftComponents v shift).prototiles
        (A.shiftComponents v shift).placements ∧
      (A.shiftComponents v shift).vertexGraph.Connected := by
  obtain ⟨v, hv⟩ := A.exists_isSlidingDirection hA
  obtain ⟨shift, htiling, hconnected⟩ :=
    IsSlidingDirection.exists_connected_component_shift A hv hA
  exact ⟨v, hv, shift, htiling, hconnected⟩

/-- A finite polygonal prototile family which admits a tiling admits one whose vertex-contact graph
is connected. -/
theorem exists_connected_tiling [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    ∃ S : ProtoTiling Plane P,
      IsTiling A.prototiles S ∧ (A.withPlacements S).vertexGraph.Connected := by
  obtain ⟨v, _, shift, htiling, hconnected⟩ := A.exists_connected_shift hA
  exact ⟨(A.shiftComponents v shift).placements, by simpa using htiling,
    by simpa [shiftComponents] using hconnected⟩

end PolygonalProtoTiling

end Tiling
