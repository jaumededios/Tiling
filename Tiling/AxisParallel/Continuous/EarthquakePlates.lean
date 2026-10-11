/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Continuous earthquake plates

The proper-horizontal-contact component decomposition, its literal regular-open slab supports,
minimality, intrinsic characterization, and column formula. The relative-cylinder construction
and independent vertical shifts preserve the ambient a.e. tiling.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise symmDiff Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

theorem horizontalProperContact_comm
    (K : Region) (s t : Tiling.Plane) :
    HorizontalProperContact K s t ↔ HorizontalProperContact K t s := by
  constructor <;> rintro ⟨a, b, hab, hh, hseg⟩
  · refine ⟨a, b, hab, hh, ?_⟩
    simpa only [inter_comm, union_comm] using hseg
  · refine ⟨a, b, hab, hh, ?_⟩
    simpa only [inter_comm, union_comm] using hseg

theorem horizontalProperContact_iff
    (K : Region) (s t : Tiling.Plane) :
    HorizontalProperContact K s t ↔
      ∃ a b : Tiling.Plane,
        a ≠ b ∧ a.im = b.im ∧
        openSegment ℝ a b ⊆
          (frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)) \
            ((s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices)) :=
  Iff.rfl

theorem horizontalProperContact_edgeConnected
    {K : Region} {T : Set Tiling.Plane}
    (i j : (K.polygonalProtoTiling T).placements)
    (hContact : HorizontalProperContact K i.1.1 j.1.1) :
    (K.polygonalProtoTiling T).EdgeConnected i j := by
  rcases i with ⟨⟨s, ⟨⟩⟩, hs⟩
  rcases j with ⟨⟨t, ⟨⟩⟩, ht⟩
  rcases hContact with ⟨a, b, hab, hh, hseg⟩
  refine ⟨a, b, hab, ?_⟩
  change openSegment ℝ a b ⊆
    (frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)) \
      ((s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices))
  exact hseg

theorem VerticalPlate_eq_connectedComponent
    (K : Region) (T : Set Tiling.Plane) :
    VerticalPlate K T = (verticalPlateGraph K T).ConnectedComponent :=
  rfl

theorem verticalPlateGraph_adj_iff
    {K : Region} {T : Set Tiling.Plane} (s t : T) :
    (verticalPlateGraph K T).Adj s t ↔
      s ≠ t ∧ HorizontalProperContact K s t := by
  rw [verticalPlateGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hst, hContact | hContact⟩
    · exact ⟨hst, hContact⟩
    · exact ⟨hst, (horizontalProperContact_comm K t s).mp hContact⟩
  · rintro ⟨hst, hContact⟩
    exact ⟨hst, Or.inl hContact⟩

theorem iUnion_verticalPlateCentres
    (K : Region) (T : Set Tiling.Plane) :
    (⋃ P : VerticalPlate K T, P.centres) = T := by
  change (⋃ P : VerticalPlate K T, Subtype.val '' P.supp) = T
  ext t
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨_, s, _, rfl⟩
    exact s.2
  · intro ht
    let t' : T := ⟨t, ht⟩
    rw [Set.mem_iUnion]
    refine ⟨VerticalPlate.ofCentre (K := K) t', t', ?_, rfl⟩
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem

theorem VerticalPlate.mem_centres_ofCentre
    {K : Region} {T : Set Tiling.Plane} (t : T) :
    (t : Tiling.Plane) ∈ (VerticalPlate.ofCentre (K := K) t).centres := by
  exact ⟨t, SimpleGraph.ConnectedComponent.connectedComponentMk_mem, rfl⟩

theorem VerticalPlate.support_eq_regularSupport
    {K : Region} {T : Set Tiling.Plane}
    (P : VerticalPlate K T) :
    P.support = regularSupport K P.centres :=
  rfl

theorem VerticalPlate.base_eq
    {K : Region} {T : Set Tiling.Plane}
    (P : VerticalPlate K T) :
    P.base = Complex.re '' P.support :=
  rfl

theorem isVerticalColumn_iff
    {K : Region} {T : Set Tiling.Plane}
    (P : VerticalPlate K T) :
    IsVerticalColumn P ↔
      ∃ x : ℝ, P.centres ⊆ {z : Tiling.Plane | z.re = x} :=
  Iff.rfl

theorem verticalColumnCentres_eq
    (K : Region) (T : Set Tiling.Plane) :
    verticalColumnCentres K T =
      ⋃ P : {P : VerticalPlate K T | IsVerticalColumn P},
        P.1.centres :=
  rfl

theorem nonColumnVerticalPlates_eq
    (K : Region) (T : Set Tiling.Plane) :
    nonColumnVerticalPlates K T =
      {P : VerticalPlate K T | ¬ IsVerticalColumn P} :=
  rfl

theorem isMinimalVerticalSlabSubfamily_iff
    (K : Region) (T S : Set Tiling.Plane) :
    IsMinimalVerticalSlabSubfamily K T S ↔
      S.Nonempty ∧ S ⊆ T ∧
      (∃ X : Set ℝ,
        X = interior (closure X) ∧
          regularSupport K S = Complex.re ⁻¹' X) ∧
      ∀ Q : Set Tiling.Plane,
        Q.Nonempty → Q ⊆ S →
        (∃ X : Set ℝ,
          X = interior (closure X) ∧
            regularSupport K Q = Complex.re ⁻¹' X) →
        Q = S :=
  Iff.rfl

theorem shiftVerticalPlates_eq
    (K : Region) (T : Set Tiling.Plane)
    (shift : VerticalPlate K T → ℝ) :
    shiftVerticalPlates K T shift =
      ⋃ P : VerticalPlate K T,
        ((((shift P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) :=
  rfl

theorem verticalPlateCentres_pairwiseDisjoint
    (K : Region) (T : Set Tiling.Plane) :
    Set.PairwiseDisjoint Set.univ
      (@VerticalPlate.centres K T) := by
  intro P _ Q _ hPQ
  change Disjoint P.centres Q.centres
  rw [Set.disjoint_left]
  intro t htP htQ
  rcases htP with ⟨p, hp, hpt⟩
  rcases htQ with ⟨q, hq, hqt⟩
  have hpq : p = q := Subtype.ext (hpt.trans hqt.symm)
  subst q
  exact hPQ (SimpleGraph.ConnectedComponent.eq_of_common_vertex hp hq)

private theorem placedSupport_subset_closure_regularSupport
    (K : Region) {A : Set Tiling.Plane} {s : Tiling.Plane} (hs : s ∈ A) :
    s +ᵥ K.support ⊆ closure (regularSupport K A) := by
  rw [K.isPolygonal.closure_interior.symm, ← closure_vadd s (interior K.support)]
  apply closure_mono
  intro z hz
  rw [regularSupport]
  apply (isOpen_iUnion fun i : A ↦ isOpen_interior.vadd (i : Tiling.Plane)).subset_interior_closure
  change z ∈ ⋃ i : A, (i : Tiling.Plane) +ᵥ K.openCarrier
  exact Set.mem_iUnion_of_mem ⟨s, hs⟩ hz

private theorem no_crossing_contact
    (K : Region) {A B : Set Tiling.Plane} {Y0 Y1 : Set ℝ}
    (hreg0 : interior (closure Y0) = Y0)
    (hreg1 : interior (closure Y1) = Y1)
    (hdisj : Disjoint (regularSupport K A) (regularSupport K B))
    (hA : regularSupport K A = {z : Tiling.Plane | z.re ∈ Y0})
    (hB : regularSupport K B = {z : Tiling.Plane | z.re ∈ Y1})
    {s t : Tiling.Plane} (hs : s ∈ A) (ht : t ∈ B) :
    ¬ HorizontalProperContact K s t := by
  rintro ⟨a, b, hab, him, hseg⟩
  have hre : a.re ≠ b.re := by
    intro hre
    apply hab
    apply Complex.ext hre him
  let J : Set ℝ := openSegment ℝ a.re b.re
  have hJopen : IsOpen J := by
    change IsOpen (openSegment ℝ a.re b.re)
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · rw [openSegment_eq_Ioo hlt]
      exact isOpen_Ioo
    · rw [openSegment_symm, openSegment_eq_Ioo hgt]
      exact isOpen_Ioo
  have hJ0 : J ⊆ closure Y0 := by
    intro q hq
    dsimp [J] at hq
    rw [openSegment_eq_image] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    have hz := hseg (lineMap_mem_openSegment ℝ a b hu)
    have hzsupport := frontier_subset_closure hz.1.1
    rw [(K.isPolygonal.isClosed.vadd s).closure_eq] at hzsupport
    have hzcl := placedSupport_subset_closure_regularSupport K hs hzsupport
    rw [hA] at hzcl
    change (AffineMap.lineMap a b u) ∈ closure (Complex.re ⁻¹' Y0) at hzcl
    rw [Complex.closure_preimage_re] at hzcl
    change (1 - u) * a.re + u * b.re ∈ closure Y0
    rw [show (1 - u) * a.re + u * b.re = u * (b.re - a.re) + a.re by ring]
    change (u • (b - a) + a).re ∈ closure Y0 at hzcl
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] using hzcl
  have hJ1 : J ⊆ closure Y1 := by
    intro q hq
    dsimp [J] at hq
    rw [openSegment_eq_image] at hq
    obtain ⟨u, hu, rfl⟩ := hq
    have hz := hseg (lineMap_mem_openSegment ℝ a b hu)
    have hzsupport := frontier_subset_closure hz.1.2
    rw [(K.isPolygonal.isClosed.vadd t).closure_eq] at hzsupport
    have hzcl := placedSupport_subset_closure_regularSupport K ht hzsupport
    rw [hB] at hzcl
    change (AffineMap.lineMap a b u) ∈ closure (Complex.re ⁻¹' Y1) at hzcl
    rw [Complex.closure_preimage_re] at hzcl
    change (1 - u) * a.re + u * b.re ∈ closure Y1
    rw [show (1 - u) * a.re + u * b.re = u * (b.re - a.re) + a.re by ring]
    change (u • (b - a) + a).re ∈ closure Y1 at hzcl
    simpa only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add,
      Complex.add_re, Complex.sub_re, Complex.smul_re, smul_eq_mul] using hzcl
  have hmJ : midpoint ℝ a.re b.re ∈ J := midpoint_mem_openSegment _ _
  have hm0 : midpoint ℝ a.re b.re ∈ Y0 := by
    rw [← hreg0]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hJopen.mem_nhds hmJ) hJ0)
  have hm1 : midpoint ℝ a.re b.re ∈ Y1 := by
    rw [← hreg1]
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (hJopen.mem_nhds hmJ) hJ1)
  have hz0 : ((midpoint ℝ a.re b.re : ℝ) : ℂ) ∈ regularSupport K A := by
    simpa [hA] using hm0
  have hz1 : ((midpoint ℝ a.re b.re : ℝ) : ℂ) ∈ regularSupport K B := by
    simpa [hB] using hm1
  exact Set.disjoint_left.1 hdisj hz0 hz1

/-- Every proper-horizontal-contact plate lies wholly in one side of a partition whose regular
supports are disjoint regular vertical slabs. -/
theorem verticalPlates_saturated_of_slabPartition
    (K : Region) {T A B : Set Tiling.Plane} {Y0 Y1 : Set ℝ}
    (hUnion : A ∪ B = T)
    (hSupportDisjoint : Disjoint (regularSupport K A) (regularSupport K B))
    (hY0regular : interior (closure Y0) = Y0)
    (hY1regular : interior (closure Y1) = Y1)
    (hSupportA : regularSupport K A = {z : Tiling.Plane | z.re ∈ Y0})
    (hSupportB : regularSupport K B = {z : Tiling.Plane | z.re ∈ Y1}) :
    (∀ P : VerticalPlate K T,
      (P.centres ∩ A).Nonempty → P.centres ⊆ A) ∧
    (∀ P : VerticalPlate K T,
      (P.centres ∩ B).Nonempty → P.centres ⊆ B) := by
  have hedgeA {u v : T} (huv : (verticalPlateGraph K T).Adj u v)
      (hu : (u : Tiling.Plane) ∈ A) : (v : Tiling.Plane) ∈ A := by
    have hvT : (v : Tiling.Plane) ∈ T := v.2
    have hvAB : (v : Tiling.Plane) ∈ A ∪ B := hUnion.symm ▸ hvT
    rcases hvAB with hvA | hvB
    · exact hvA
    · exact (no_crossing_contact K hY0regular hY1regular hSupportDisjoint
        hSupportA hSupportB hu hvB
        ((verticalPlateGraph_adj_iff u v).mp huv).2).elim
  have hedgeB {u v : T} (huv : (verticalPlateGraph K T).Adj u v)
      (hu : (u : Tiling.Plane) ∈ B) : (v : Tiling.Plane) ∈ B := by
    have hvT : (v : Tiling.Plane) ∈ T := v.2
    have hvAB : (v : Tiling.Plane) ∈ A ∪ B := hUnion.symm ▸ hvT
    rcases hvAB with hvA | hvB
    · exact (no_crossing_contact K hY0regular hY1regular hSupportDisjoint
        hSupportA hSupportB hvA hu
        ((horizontalProperContact_comm K u v).mp
          ((verticalPlateGraph_adj_iff u v).mp huv).2)).elim
    · exact hvB
  have walkA {u v : T} (w : (verticalPlateGraph K T).Walk u v) :
      (u : Tiling.Plane) ∈ A → (v : Tiling.Plane) ∈ A := by
    induction w with
    | nil => exact fun h ↦ h
    | cons hadj _ ih => exact fun h ↦ ih (hedgeA hadj h)
  have walkB {u v : T} (w : (verticalPlateGraph K T).Walk u v) :
      (u : Tiling.Plane) ∈ B → (v : Tiling.Plane) ∈ B := by
    induction w with
    | nil => exact fun h ↦ h
    | cons hadj _ ih => exact fun h ↦ ih (hedgeB hadj h)
  constructor
  · intro P hPA z hzP
    obtain ⟨p, hpP, hpA⟩ := hPA
    obtain ⟨p', hp'P, rfl⟩ := hpP
    obtain ⟨z', hz'P, rfl⟩ := hzP
    obtain ⟨w⟩ := P.reachable_of_mem_supp hp'P hz'P
    exact walkA w hpA
  · intro P hPB z hzP
    obtain ⟨p, hpP, hpB⟩ := hPB
    obtain ⟨p', hp'P, rfl⟩ := hpP
    obtain ⟨z', hz'P, rfl⟩ := hzP
    obtain ⟨w⟩ := P.reachable_of_mem_supp hp'P hz'P
    exact walkB w hpB

private theorem segment_inter_frontier_of_mem_notMem
    {D : Set Tiling.Plane} {u v : Tiling.Plane}
    (hu : u ∈ D) (hv : v ∉ D) :
    ∃ q ∈ segment ℝ u v, q ∈ frontier D := by
  by_contra h
  push Not at h
  have hdisj : Disjoint (segment ℝ u v) (frontier D) := by
    exact Set.disjoint_left.2 fun q hq hqf => h q hq hqf
  have hinside : segment ℝ u v ⊆ interior D :=
    Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
      (convex_segment u v).isPreconnected hdisj (left_mem_segment ℝ u v) hu
  exact hv (interior_subset (hinside (right_mem_segment ℝ u v)))

private theorem horizontal_frontier_of_left_quadrants_mismatch
    {D : Set Tiling.Plane} {z : Tiling.Plane} {r : ℝ} (hr : 0 < r)
    (hcross : ∀ w ∈ Metric.ball z r, w ∈ frontier D →
      w.re = z.re ∨ w.im = z.im)
    (hmismatch :
      ((Metric.ball z r ∩ {w | w.re < z.re} ∩ {w | z.im < w.im}) ⊆ D ∧
        (Metric.ball z r ∩ {w | w.re < z.re} ∩ {w | w.im < z.im}) ⊆ Dᶜ) ∨
      ((Metric.ball z r ∩ {w | w.re < z.re} ∩ {w | z.im < w.im}) ⊆ Dᶜ ∧
        (Metric.ball z r ∩ {w | w.re < z.re} ∩ {w | w.im < z.im}) ⊆ D)) :
    ∃ a b : Tiling.Plane, a ≠ b ∧ a.im = b.im ∧
      openSegment ℝ a b ⊆ frontier D := by
  let d : ℝ := r / 4
  have hd : 0 < d := div_pos hr (by norm_num)
  let a : Tiling.Plane := z - (d : ℂ)
  let b : Tiling.Plane := z
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hab
    have hre := congrArg Complex.re hab
    simp [a, b] at hre
    linarith
  · simp [a, b]
  intro p hp
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have haBall : a ∈ Metric.closedBall z d := by
    rw [Metric.mem_closedBall]
    simp [a, d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hbBall : b ∈ Metric.closedBall z d := by simp [b, hd.le]
  have hpBallClosed : p ∈ Metric.closedBall z d :=
    (convex_closedBall z d).segment_subset haBall hbBall hpseg
  have hpdist : dist p z ≤ d := Metric.mem_closedBall.mp hpBallClosed
  have hpcoords : z.re - d < p.re ∧ p.re < z.re ∧ p.im = z.im := by
    rw [openSegment_eq_image] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    rcases hc with ⟨hc0, hc1⟩
    dsimp [a, b]
    constructor
    · simp only [Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.sub_re]
      nlinarith
    · constructor
      · simp only [Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_re]
        nlinarith
      · simp only [Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.sub_im]
        ring
  let up : Tiling.Plane := p + (d : ℂ) * Complex.I
  let down : Tiling.Plane := p - (d : ℂ) * Complex.I
  have hdistUp : dist up p = d := by
    rw [dist_eq_norm]
    have heq : up - p = (d : ℂ) * Complex.I := by simp [up]
    rw [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hd]
  have hdistDown : dist down p = d := by
    rw [dist_eq_norm]
    have heq : down - p = -(d : ℂ) * Complex.I := by simp [down]
    rw [heq, show -(d : ℂ) * Complex.I = -((d : ℂ) * Complex.I) by ring,
      norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hd]
  have hupBall : up ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist up z ≤ dist up p + dist p z := dist_triangle _ _ _
      _ ≤ d + d := by rw [hdistUp]; linarith
      _ < r := by dsimp [d]; linarith
  have hdownBall : down ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist down z ≤ dist down p + dist p z := dist_triangle _ _ _
      _ ≤ d + d := by rw [hdistDown]; linarith
      _ < r := by dsimp [d]; linarith
  have hupLeft : up.re < z.re := by simpa [up] using hpcoords.2.1
  have hdownLeft : down.re < z.re := by simpa [down] using hpcoords.2.1
  have hupAbove : z.im < up.im := by simp [up, hpcoords.2.2, hd]
  have hdownBelow : down.im < z.im := by simp [down, hpcoords.2.2, hd]
  have hfront : ∃ q ∈ segment ℝ up down, q ∈ frontier D := by
    rcases hmismatch with ⟨hupIn, hdownOut⟩ | ⟨hupOut, hdownIn⟩
    · exact segment_inter_frontier_of_mem_notMem
        (hupIn ⟨⟨hupBall, hupLeft⟩, hupAbove⟩)
        (hdownOut ⟨⟨hdownBall, hdownLeft⟩, hdownBelow⟩)
    · obtain ⟨q, hq, hqf⟩ := segment_inter_frontier_of_mem_notMem
        (hdownIn ⟨⟨hdownBall, hdownLeft⟩, hdownBelow⟩)
        (hupOut ⟨⟨hupBall, hupLeft⟩, hupAbove⟩)
      exact ⟨q, by simpa [segment_symm] using hq, hqf⟩
  obtain ⟨q, hqseg, hqfront⟩ := hfront
  have hqBall : q ∈ Metric.ball z r := by
    exact (convex_ball z r).segment_subset hupBall hdownBall hqseg
  have hqre : q.re = p.re := by
    rw [segment_eq_image] at hqseg
    obtain ⟨c, _hc, rfl⟩ := hqseg
    simp [up, down]
    ring
  have hqim : q.im = z.im := by
    rcases hcross q hqBall hqfront with hre | him
    · exfalso
      rw [hqre] at hre
      exact ne_of_lt hpcoords.2.1 hre
    · exact him
  have hqp : q = p := Complex.ext hqre (hqim.trans hpcoords.2.2.symm)
  simpa [hqp] using hqfront

private theorem horizontal_frontier_of_right_quadrants_mismatch
    {D : Set Tiling.Plane} {z : Tiling.Plane} {r : ℝ} (hr : 0 < r)
    (hcross : ∀ w ∈ Metric.ball z r, w ∈ frontier D →
      w.re = z.re ∨ w.im = z.im)
    (hmismatch :
      ((Metric.ball z r ∩ {w | z.re < w.re} ∩ {w | z.im < w.im}) ⊆ D ∧
        (Metric.ball z r ∩ {w | z.re < w.re} ∩ {w | w.im < z.im}) ⊆ Dᶜ) ∨
      ((Metric.ball z r ∩ {w | z.re < w.re} ∩ {w | z.im < w.im}) ⊆ Dᶜ ∧
        (Metric.ball z r ∩ {w | z.re < w.re} ∩ {w | w.im < z.im}) ⊆ D)) :
    ∃ a b : Tiling.Plane, a ≠ b ∧ a.im = b.im ∧
      openSegment ℝ a b ⊆ frontier D := by
  let d : ℝ := r / 4
  have hd : 0 < d := div_pos hr (by norm_num)
  let a : Tiling.Plane := z + (d : ℂ)
  let b : Tiling.Plane := z
  refine ⟨a, b, ?_, ?_, ?_⟩
  · intro hab
    have hre := congrArg Complex.re hab
    simp [a, b] at hre
    linarith
  · simp [a, b]
  intro p hp
  have hpseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  have haBall : a ∈ Metric.closedBall z d := by
    rw [Metric.mem_closedBall]
    simp [a, d, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hbBall : b ∈ Metric.closedBall z d := by simp [b, hd.le]
  have hpBallClosed : p ∈ Metric.closedBall z d :=
    (convex_closedBall z d).segment_subset haBall hbBall hpseg
  have hpdist : dist p z ≤ d := Metric.mem_closedBall.mp hpBallClosed
  have hpcoords : z.re < p.re ∧ p.re < z.re + d ∧ p.im = z.im := by
    rw [openSegment_eq_image] at hp
    obtain ⟨c, hc, rfl⟩ := hp
    rcases hc with ⟨hc0, hc1⟩
    dsimp [a, b]
    constructor
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.add_re]
      nlinarith
    · constructor
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re]
        nlinarith
      · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_im]
        ring
  let up : Tiling.Plane := p + (d : ℂ) * Complex.I
  let down : Tiling.Plane := p - (d : ℂ) * Complex.I
  have hdistUp : dist up p = d := by
    rw [dist_eq_norm]
    have heq : up - p = (d : ℂ) * Complex.I := by simp [up]
    rw [heq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hd]
  have hdistDown : dist down p = d := by
    rw [dist_eq_norm]
    have heq : down - p = -(d : ℂ) * Complex.I := by simp [down]
    rw [heq, show -(d : ℂ) * Complex.I = -((d : ℂ) * Complex.I) by ring,
      norm_neg, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos hd]
  have hupBall : up ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist up z ≤ dist up p + dist p z := dist_triangle _ _ _
      _ ≤ d + d := by rw [hdistUp]; linarith
      _ < r := by dsimp [d]; linarith
  have hdownBall : down ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist down z ≤ dist down p + dist p z := dist_triangle _ _ _
      _ ≤ d + d := by rw [hdistDown]; linarith
      _ < r := by dsimp [d]; linarith
  have hupRight : z.re < up.re := by simpa [up] using hpcoords.1
  have hdownRight : z.re < down.re := by simpa [down] using hpcoords.1
  have hupAbove : z.im < up.im := by simp [up, hpcoords.2.2, hd]
  have hdownBelow : down.im < z.im := by simp [down, hpcoords.2.2, hd]
  have hfront : ∃ q ∈ segment ℝ up down, q ∈ frontier D := by
    rcases hmismatch with ⟨hupIn, hdownOut⟩ | ⟨hupOut, hdownIn⟩
    · exact segment_inter_frontier_of_mem_notMem
        (hupIn ⟨⟨hupBall, hupRight⟩, hupAbove⟩)
        (hdownOut ⟨⟨hdownBall, hdownRight⟩, hdownBelow⟩)
    · obtain ⟨q, hq, hqf⟩ := segment_inter_frontier_of_mem_notMem
        (hdownIn ⟨⟨hdownBall, hdownRight⟩, hdownBelow⟩)
        (hupOut ⟨⟨hupBall, hupRight⟩, hupAbove⟩)
      exact ⟨q, by simpa [segment_symm] using hq, hqf⟩
  obtain ⟨q, hqseg, hqfront⟩ := hfront
  have hqBall : q ∈ Metric.ball z r :=
    (convex_ball z r).segment_subset hupBall hdownBall hqseg
  have hqre : q.re = p.re := by
    rw [segment_eq_image] at hqseg
    obtain ⟨c, _hc, rfl⟩ := hqseg
    simp [up, down]
    ring
  have hqim : q.im = z.im := by
    rcases hcross q hqBall hqfront with hre | him
    · rw [hqre] at hre
      exfalso
      linarith [hpcoords.1]
    · exact him
  have hqp : q = p := Complex.ext hqre (hqim.trans hpcoords.2.2.symm)
  simpa [hqp] using hqfront

private theorem halfBall_subset_closure_openQuadrants
    (z : Tiling.Plane) {r : ℝ} (hr : 0 < r) :
    Metric.ball z (r / 2) ⊆ closure
      ((Metric.ball z r ∩ {w : Tiling.Plane | w.re < z.re} ∩ {w | z.im < w.im}) ∪
       (Metric.ball z r ∩ {w : Tiling.Plane | w.re < z.re} ∩ {w | w.im < z.im}) ∪
       (Metric.ball z r ∩ {w : Tiling.Plane | z.re < w.re} ∩ {w | z.im < w.im}) ∪
       (Metric.ball z r ∩ {w : Tiling.Plane | z.re < w.re} ∩ {w | w.im < z.im})) := by
  intro w hw
  rw [mem_closure_iff]
  intro o hopen hwo
  obtain ⟨ε, hε, hεo⟩ := Metric.isOpen_iff.mp hopen w hwo
  let m : ℝ := r / 2 - dist w z
  have hm : 0 < m := by
    rw [Metric.mem_ball] at hw
    dsimp [m]
    linarith
  let δ : ℝ := min ε m / 4
  have hδ : 0 < δ := div_pos (lt_min hε hm) (by norm_num)
  let sx : ℝ := if w.re < z.re then -δ else δ
  let sy : ℝ := if w.im < z.im then -δ else δ
  let q : Tiling.Plane := w + (sx : ℂ) + (sy : ℂ) * Complex.I
  have hsxabs : |sx| = δ := by
    dsimp [sx]
    split <;> simp [abs_of_pos hδ]
  have hsyabs : |sy| = δ := by
    dsimp [sy]
    split <;> simp [abs_of_pos hδ]
  have hqw : dist q w ≤ δ + δ := by
    calc
      dist q w ≤ dist q (w + (sx : ℂ)) + dist (w + (sx : ℂ)) w :=
        dist_triangle _ _ _
      _ = ‖(sy : ℂ) * Complex.I‖ + ‖(sx : ℂ)‖ := by
        simp [q, dist_eq_norm]
      _ = δ + δ := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, hsxabs, hsyabs]
  have hδeps : δ + δ < ε := by
    dsimp [δ]
    have := min_le_left ε m
    linarith
  have hδm : δ + δ < m := by
    dsimp [δ]
    have := min_le_right ε m
    linarith
  have hqo : q ∈ o := hεo (by
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt hqw hδeps)
  have hqBall : q ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist q z ≤ dist q w + dist w z := dist_triangle _ _ _
      _ < m + dist w z := by linarith
      _ = r / 2 := by dsimp [m]; ring
      _ < r := by linarith
  have hqre : q.re < z.re ∨ z.re < q.re := by
    dsimp [q, sx]
    split_ifs with h
    · left
      simp only [Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    · right
      simp only [Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      have : z.re ≤ w.re := le_of_not_gt h
      linarith
  have hqim : q.im < z.im ∨ z.im < q.im := by
    dsimp [q, sy]
    split_ifs with h
    · left
      simp only [Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      linarith
    · right
      simp only [Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      have : z.im ≤ w.im := le_of_not_gt h
      linarith
  refine ⟨q, hqo, ?_⟩
  rcases hqre with hqLeft | hqRight <;> rcases hqim with hqBelow | hqAbove
  · exact Or.inl (Or.inl (Or.inr ⟨⟨hqBall, hqLeft⟩, hqBelow⟩))
  · exact Or.inl (Or.inl (Or.inl ⟨⟨hqBall, hqLeft⟩, hqAbove⟩))
  · exact Or.inr ⟨⟨hqBall, hqRight⟩, hqBelow⟩
  · exact Or.inl (Or.inr ⟨⟨hqBall, hqRight⟩, hqAbove⟩)


theorem localBoundaryCross_noHorizontal_verticalGerm
    {D : Set Tiling.Plane} (hreg : D = interior (closure D))
    (hcross : ∀ z ∈ frontier D, ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ Metric.ball z r,
        w ∈ frontier D → w.re = z.re ∨ w.im = z.im)
    (hNoHorizontal : ∀ a b : Tiling.Plane, a ≠ b → a.im = b.im →
      ¬ openSegment ℝ a b ⊆ frontier D)
    {z : Tiling.Plane} (hz : z ∈ frontier D) :
    ∃ r : ℝ, 0 < r ∧
      {w : Tiling.Plane | w.re = z.re ∧ dist w z < r} ⊆ frontier D := by
  obtain ⟨r, hr, hcrossBall⟩ := hcross z hz
  let LT := Metric.ball z r ∩ {w : Tiling.Plane | w.re < z.re} ∩
    {w : Tiling.Plane | z.im < w.im}
  let LB := Metric.ball z r ∩ {w : Tiling.Plane | w.re < z.re} ∩
    {w : Tiling.Plane | w.im < z.im}
  let RT := Metric.ball z r ∩ {w : Tiling.Plane | z.re < w.re} ∩
    {w : Tiling.Plane | z.im < w.im}
  let RB := Metric.ball z r ∩ {w : Tiling.Plane | z.re < w.re} ∩
    {w : Tiling.Plane | w.im < z.im}
  have quadrant_cases (Q : Set Tiling.Plane) (hQpre : IsPreconnected Q)
      (hQball : Q ⊆ Metric.ball z r)
      (hQoff : ∀ w ∈ Q, w.re ≠ z.re ∧ w.im ≠ z.im) :
      Q ⊆ interior D ∨ Q ⊆ interior Dᶜ := by
    apply Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      hQpre
    rw [Set.disjoint_left]
    intro w hwQ hwf
    rcases hcrossBall w (hQball hwQ) hwf with hre | him
    · exact (hQoff w hwQ).1 hre
    · exact (hQoff w hwQ).2 him
  have hLTpre : IsPreconnected LT := by
    exact (((convex_ball z r).inter
      (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear z.re)).inter
      (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear z.im)).isPreconnected
  have hLBpre : IsPreconnected LB := by
    exact (((convex_ball z r).inter
      (convex_halfSpace_lt Complex.reCLM.toLinearMap.isLinear z.re)).inter
      (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear z.im)).isPreconnected
  have hRTpre : IsPreconnected RT := by
    exact (((convex_ball z r).inter
      (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear z.re)).inter
      (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear z.im)).isPreconnected
  have hRBpre : IsPreconnected RB := by
    exact (((convex_ball z r).inter
      (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear z.re)).inter
      (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear z.im)).isPreconnected
  have hLT := quadrant_cases LT hLTpre (fun w hw => hw.1.1) (fun w hw =>
    ⟨ne_of_lt hw.1.2, ne_of_gt hw.2⟩)
  have hLB := quadrant_cases LB hLBpre (fun w hw => hw.1.1) (fun w hw =>
    ⟨ne_of_lt hw.1.2, ne_of_lt hw.2⟩)
  have hRT := quadrant_cases RT hRTpre (fun w hw => hw.1.1) (fun w hw =>
    ⟨ne_of_gt hw.1.2, ne_of_gt hw.2⟩)
  have hRB := quadrant_cases RB hRBpre (fun w hw => hw.1.1) (fun w hw =>
    ⟨ne_of_gt hw.1.2, ne_of_lt hw.2⟩)
  have hleft :
      (LT ⊆ interior D ∧ LB ⊆ interior D) ∨
      (LT ⊆ interior Dᶜ ∧ LB ⊆ interior Dᶜ) := by
    rcases hLT with hLTin | hLTout <;> rcases hLB with hLBin | hLBout
    · exact Or.inl ⟨hLTin, hLBin⟩
    · exfalso
      obtain ⟨a, b, hab, hh, hedge⟩ :=
        horizontal_frontier_of_left_quadrants_mismatch hr hcrossBall
          (Or.inl ⟨hLTin.trans interior_subset, hLBout.trans interior_subset⟩)
      exact hNoHorizontal a b hab hh hedge
    · exfalso
      obtain ⟨a, b, hab, hh, hedge⟩ :=
        horizontal_frontier_of_left_quadrants_mismatch hr hcrossBall
          (Or.inr ⟨hLTout.trans interior_subset, hLBin.trans interior_subset⟩)
      exact hNoHorizontal a b hab hh hedge
    · exact Or.inr ⟨hLTout, hLBout⟩
  have hright :
      (RT ⊆ interior D ∧ RB ⊆ interior D) ∨
      (RT ⊆ interior Dᶜ ∧ RB ⊆ interior Dᶜ) := by
    rcases hRT with hRTin | hRTout <;> rcases hRB with hRBin | hRBout
    · exact Or.inl ⟨hRTin, hRBin⟩
    · exfalso
      obtain ⟨a, b, hab, hh, hedge⟩ :=
        horizontal_frontier_of_right_quadrants_mismatch hr hcrossBall
          (Or.inl ⟨hRTin.trans interior_subset, hRBout.trans interior_subset⟩)
      exact hNoHorizontal a b hab hh hedge
    · exfalso
      obtain ⟨a, b, hab, hh, hedge⟩ :=
        horizontal_frontier_of_right_quadrants_mismatch hr hcrossBall
          (Or.inr ⟨hRTout.trans interior_subset, hRBin.trans interior_subset⟩)
      exact hNoHorizontal a b hab hh hedge
    · exact Or.inr ⟨hRTout, hRBout⟩
  have hDopen : IsOpen D := by rw [hreg]; exact isOpen_interior
  have hopposite :
      ((LT ⊆ interior D ∧ LB ⊆ interior D) ∧
        (RT ⊆ interior Dᶜ ∧ RB ⊆ interior Dᶜ)) ∨
      ((LT ⊆ interior Dᶜ ∧ LB ⊆ interior Dᶜ) ∧
        (RT ⊆ interior D ∧ RB ⊆ interior D)) := by
    rcases hleft with hleftIn | hleftOut <;>
      rcases hright with hrightIn | hrightOut
    · exfalso
      have hunion : LT ∪ LB ∪ RT ∪ RB ⊆ D := by
        intro w hw
        rcases hw with ((hw | hw) | hw) | hw
        · exact interior_subset (hleftIn.1 hw)
        · exact interior_subset (hleftIn.2 hw)
        · exact interior_subset (hrightIn.1 hw)
        · exact interior_subset (hrightIn.2 hw)
      have hballClosure : Metric.ball z (r / 2) ⊆ closure D :=
        (halfBall_subset_closure_openQuadrants z hr).trans (closure_mono hunion)
      have hzInterior : z ∈ interior (closure D) :=
        interior_maximal hballClosure Metric.isOpen_ball
          (Metric.mem_ball_self (half_pos hr))
      have hzD : z ∈ D := by rw [hreg]; exact hzInterior
      exact Set.disjoint_left.1 disjoint_interior_frontier
        (by rwa [hDopen.interior_eq]) hz
    · exact Or.inl ⟨hleftIn, hrightOut⟩
    · exact Or.inr ⟨hleftOut, hrightIn⟩
    · exfalso
      have hunion : LT ∪ LB ∪ RT ∪ RB ⊆ Dᶜ := by
        intro w hw
        rcases hw with ((hw | hw) | hw) | hw
        · exact interior_subset (hleftOut.1 hw)
        · exact interior_subset (hleftOut.2 hw)
        · exact interior_subset (hrightOut.1 hw)
        · exact interior_subset (hrightOut.2 hw)
      have hcomplClosed : IsClosed Dᶜ := hDopen.isClosed_compl
      have hballCompl : Metric.ball z (r / 2) ⊆ Dᶜ :=
        (halfBall_subset_closure_openQuadrants z hr).trans
          (show closure (LT ∪ LB ∪ RT ∪ RB) ⊆ Dᶜ from
            closure_minimal hunion hcomplClosed)
      have hzComplInterior : z ∈ interior Dᶜ :=
        interior_maximal hballCompl Metric.isOpen_ball
          (Metric.mem_ball_self (half_pos hr))
      have hzComplFrontier : z ∈ frontier Dᶜ := by simpa using hz
      exact Set.disjoint_left.1 disjoint_interior_frontier hzComplInterior hzComplFrontier
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro w hw
  rcases hw with ⟨hwre, hwdist⟩
  by_cases hwz : w = z
  · simpa [hwz] using hz
  have hwim : w.im ≠ z.im := by
    intro him
    apply hwz
    exact Complex.ext hwre him
  let e : ℝ := (r - dist w z) / 2
  have he : 0 < e := div_pos (sub_pos.mpr (lt_trans hwdist (half_lt_self hr))) (by norm_num)
  let l : Tiling.Plane := w - (e : ℂ)
  let u : Tiling.Plane := w + (e : ℂ)
  have hdistL : dist l w = e := by
    rw [dist_eq_norm]
    simp [l, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hdistU : dist u w = e := by
    rw [dist_eq_norm]
    simp [u, Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
  have hlBall : l ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist l z ≤ dist l w + dist w z := dist_triangle _ _ _
      _ = e + dist w z := by rw [hdistL]
      _ < r := by dsimp [e]; linarith
  have huBall : u ∈ Metric.ball z r := by
    rw [Metric.mem_ball]
    calc
      dist u z ≤ dist u w + dist w z := dist_triangle _ _ _
      _ = e + dist w z := by rw [hdistU]
      _ < r := by dsimp [e]; linarith
  have hlLeft : l.re < z.re := by simp [l, hwre, he]
  have huRight : z.re < u.re := by simp [u, hwre, he]
  have hlim : l.im = w.im := by simp [l]
  have huim : u.im = w.im := by simp [u]
  have hcrossing : ∃ q ∈ segment ℝ l u, q ∈ frontier D := by
    rcases hopposite with ⟨hleftIn, hrightOut⟩ | ⟨hleftOut, hrightIn⟩
    · by_cases him : z.im < w.im
      · exact segment_inter_frontier_of_mem_notMem
          (interior_subset (hleftIn.1 ⟨⟨hlBall, hlLeft⟩, by simpa [hlim]⟩))
          (interior_subset (hrightOut.1 ⟨⟨huBall, huRight⟩, by simpa [huim]⟩))
      · have him' : w.im < z.im := lt_of_le_of_ne (le_of_not_gt him) hwim
        exact segment_inter_frontier_of_mem_notMem
          (interior_subset (hleftIn.2 ⟨⟨hlBall, hlLeft⟩, by simpa [hlim]⟩))
          (interior_subset (hrightOut.2 ⟨⟨huBall, huRight⟩, by simpa [huim]⟩))
    · by_cases him : z.im < w.im
      · obtain ⟨q, hq, hqf⟩ := segment_inter_frontier_of_mem_notMem
          (interior_subset (hrightIn.1 ⟨⟨huBall, huRight⟩, by simpa [huim]⟩))
          (interior_subset (hleftOut.1 ⟨⟨hlBall, hlLeft⟩, by simpa [hlim]⟩))
        exact ⟨q, by simpa [segment_symm] using hq, hqf⟩
      · have him' : w.im < z.im := lt_of_le_of_ne (le_of_not_gt him) hwim
        obtain ⟨q, hq, hqf⟩ := segment_inter_frontier_of_mem_notMem
          (interior_subset (hrightIn.2 ⟨⟨huBall, huRight⟩, by simpa [huim]⟩))
          (interior_subset (hleftOut.2 ⟨⟨hlBall, hlLeft⟩, by simpa [hlim]⟩))
        exact ⟨q, by simpa [segment_symm] using hq, hqf⟩
  obtain ⟨q, hqseg, hqfront⟩ := hcrossing
  have hqBall : q ∈ Metric.ball z r :=
    (convex_ball z r).segment_subset hlBall huBall hqseg
  have hqim : q.im = w.im := by
    rw [segment_eq_image] at hqseg
    obtain ⟨c, _hc, rfl⟩ := hqseg
    simp [l, u]
    ring
  have hqre : q.re = z.re := by
    rcases hcrossBall q hqBall hqfront with hre | him
    · exact hre
    · exfalso
      rw [hqim] at him
      exact hwim him
  have hqw : q = w := Complex.ext (hqre.trans hwre.symm) hqim
  simpa [hqw] using hqfront

theorem locallyPolygonal_has_localBoundaryCross
    {D : Set Tiling.Plane}
    (hpoly : IsLocallyAxisParallelPolygonal D) {z : Tiling.Plane}
    (_hz : z ∈ frontier D) :
    ∃ r : ℝ, 0 < r ∧ ∀ w ∈ Metric.ball z r,
      w ∈ frontier D → w.re = z.re ∨ w.im = z.im := by
  exact Tiling.AxisParallel.exists_ball_frontier_subset_axisCross hpoly z

theorem verticalGerms_extend_to_lines
    {D : Set Tiling.Plane}
    (hgerm : ∀ z ∈ frontier D, ∃ r : ℝ, 0 < r ∧
      {w : Tiling.Plane | w.re = z.re ∧ dist w z < r} ⊆ frontier D)
    {z : Tiling.Plane} (hz : z ∈ frontier D) :
    {w : Tiling.Plane | w.re = z.re} ⊆ frontier D := by
  let line : ℝ → Tiling.Plane := fun y => (z.re : ℂ) + (y : ℂ) * Complex.I
  let Y : Set ℝ := line ⁻¹' frontier D
  have hYclosed : IsClosed Y := isClosed_frontier.preimage (by fun_prop)
  have hYopen : IsOpen Y := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨r, hr, hsub⟩ := hgerm (line y) hy
    refine Filter.mem_of_superset (Metric.ball_mem_nhds y hr) ?_
    intro u hu
    apply hsub
    constructor
    · simp [line]
    · have hdist : dist (line u) (line y) = dist u y := by
        rw [dist_eq_norm, dist_eq_norm]
        have heq : line u - line y =
            ((u - y : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [line]
        rw [heq, norm_mul]
        rw [Complex.norm_I, mul_one, Complex.norm_real]
      rwa [hdist]
  have hYuniv : Y = Set.univ := by
    rcases isClopen_iff.mp ⟨hYclosed, hYopen⟩ with hYempty | hYuniv
    · exfalso
      have : z.im ∈ Y := by simpa [Y, line] using hz
      simp [hYempty] at this
    · exact hYuniv
  intro w hw
  have hwline : line w.im = w := by
    apply Complex.ext
    · simpa [line] using hw.symm
    · simp [line]
  rw [← hwline]
  have : w.im ∈ Y := by rw [hYuniv]; trivial
  exact this

theorem regularOpen_of_vertical_frontier_is_cylinder
    {D : Set Tiling.Plane} (hreg : D = interior (closure D))
    (hvertical : ∀ z ∈ frontier D,
      {w : Tiling.Plane | w.re = z.re} ⊆ frontier D) :
    ∃ X : Set ℝ, X = interior (closure X) ∧ D = Complex.re ⁻¹' X := by
  have hDopen : IsOpen D := by
    rw [hreg]
    exact isOpen_interior
  have same_line_mem {u w : Tiling.Plane} (hu : u ∈ D) (huw : w.re = u.re) : w ∈ D := by
    have hsegRe : ∀ q ∈ segment ℝ u w, q.re = u.re := by
      intro q hq
      rw [segment_eq_image] at hq
      obtain ⟨c, _hc, rfl⟩ := hq
      simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      rw [huw]
      ring
    have hdisj : Disjoint (segment ℝ u w) (frontier D) := by
      rw [Set.disjoint_left]
      intro q hq hqfront
      have huFrontier : u ∈ frontier D := hvertical q hqfront (hsegRe q hq).symm
      have huInterior : u ∈ interior D := by rwa [hDopen.interior_eq]
      exact Set.disjoint_left.1 disjoint_interior_frontier huInterior huFrontier
    have hinside : segment ℝ u w ⊆ interior D :=
      Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
        (convex_segment u w).isPreconnected hdisj (left_mem_segment ℝ u w) hu
    exact interior_subset (hinside (right_mem_segment ℝ u w))
  let X : Set ℝ := {x | (x : ℂ) ∈ D}
  have hproduct : D = Complex.re ⁻¹' X := by
    ext w
    constructor
    · intro hw
      change (w.re : ℂ) ∈ D
      exact same_line_mem hw (by simp)
    · intro hw
      change (w.re : ℂ) ∈ D at hw
      exact same_line_mem hw (by simp)
  refine ⟨X, ?_, hproduct⟩
  have hpreimage : Complex.re ⁻¹' X =
      interior (closure (Complex.re ⁻¹' X)) := hproduct ▸ hreg
  rw [Complex.closure_preimage_re, Complex.interior_preimage_re] at hpreimage
  have hreSurj : Function.Surjective Complex.re := by
    intro x
    exact ⟨(x : ℂ), by simp⟩
  exact (Set.preimage_injective.mpr hreSurj) hpreimage

theorem difference_aeEq_regularizedDifference
    {U V : Set Tiling.Plane}
    (_hUopen : IsOpen U) (_hVopen : IsOpen V)
    (hUfrontier : volume (frontier U) = 0)
    (hVfrontier : volume (frontier V) = 0) :
    U \ V =ᵐ[volume] interior (closure (U \ V)) := by
  have hfront : volume (frontier (U \ V)) = 0 := by
    apply measure_mono_null (frontier_inter_subset U Vᶜ)
    apply measure_union_null
    · exact measure_mono_null inter_subset_left hUfrontier
    · apply measure_mono_null inter_subset_right
      simpa using hVfrontier
  have hfrontClosure : volume (frontier (closure (U \ V))) = 0 :=
    measure_mono_null frontier_closure_subset hfront
  exact (closure_ae_eq_of_null_frontier hfront).symm.trans
    (interior_ae_eq_of_null_frontier hfrontClosure).symm

theorem regularSupport_sdiff_aeEq
    {K : Region} {T E P Q : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hPT : P ⊆ T) (hQP : Q ⊆ P) :
    regularSupport K (P \ Q) =ᵐ[volume]
      regularSupport K P \ regularSupport K Q := by
  have hdisj := (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
  have packing_sub {A : Set Tiling.Plane} (hAT : A ⊆ T) :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements A) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K A).mpr
    intro a ha b hb hab
    exact hdisj (hAT ha) (hAT hb) hab
  have hQT : Q ⊆ T := hQP.trans hPT
  have hdiffT : P \ Q ⊆ T := (sdiff_subset.trans hPT)
  have hopen : openUnion K (P \ Q) = openUnion K P \ openUnion K Q := by
    ext x
    constructor
    · intro hx
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hx
      obtain ⟨p, hp⟩ := hx
      refine ⟨?_, ?_⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨p, p.2.1⟩, hp⟩
      · intro hxQ
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxQ
        obtain ⟨q, hq⟩ := hxQ
        have hpq : (p : Tiling.Plane) ≠ (q : Tiling.Plane) := by
          intro heq
          apply p.2.2
          simp [heq, q.2]
        exact Set.disjoint_left.1 (hdisj (hPT p.2.1) (hQT q.2) hpq) hp hq
    · rintro ⟨hxP, hxnotQ⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxP ⊢
      obtain ⟨p, hp⟩ := hxP
      have hpnotQ : (p : Tiling.Plane) ∉ Q := by
        intro hpQ
        apply hxnotQ
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨⟨p, hpQ⟩, hp⟩
      exact ⟨⟨p, p.2, hpnotQ⟩, hp⟩
  have hPQ := Tiling.AxisParallel.openUnion_aeEq_regularSupport
    (packing_sub hdiffT)
  have hP := Tiling.AxisParallel.openUnion_aeEq_regularSupport
    (packing_sub hPT)
  have hQ := Tiling.AxisParallel.openUnion_aeEq_regularSupport
    (packing_sub hQT)
  exact hPQ.symm.trans ((Filter.EventuallyEq.of_eq hopen).trans
    (MeasureTheory.ae_eq_set_sdiff hP hQ))

private theorem volume_verticalLine (a : ℝ) :
    volume {z : Tiling.Plane | z.re = a} = 0 := by
  have hset : {z : ℂ | z.re = a} =
      Complex.measurableEquivRealProd ⁻¹' ({a} ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, zero_mul]
  · exact ((MeasurableSet.singleton a).prod MeasurableSet.univ).nullMeasurableSet

private theorem volume_horizontalLine (b : ℝ) :
    volume {z : Tiling.Plane | z.im = b} = 0 := by
  have hset : {z : ℂ | z.im = b} =
      Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ {b}) := by
    ext z
    simp [Complex.measurableEquivRealProd]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]
  · exact (MeasurableSet.univ.prod (MeasurableSet.singleton b)).nullMeasurableSet

theorem regularSupport_frontier_null
    {K : Region} {S : Set Tiling.Plane}
    (hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    volume (frontier (regularSupport K S)) = 0 := by
  let D := regularSupport K S
  have hlocal : ∀ x : Tiling.Plane,
      ∃ r > 0, frontier D ∩ Metric.ball x r ⊆
        {z | z.re = x.re} ∪ {z | z.im = x.im} := by
    intro x
    obtain ⟨r, hr, hx⟩ :=
      Tiling.AxisParallel.regularSupport_localBoundaryCross hpacking x
    refine ⟨r, hr, ?_⟩
    rintro z ⟨hzfront, hzball⟩
    exact hx z hzball hzfront
  choose r hr hcross using hlocal
  obtain ⟨A, hAcount, -, hcover⟩ :=
    isLindelof_univ.elim_nhds_subcover
      (fun x : Tiling.Plane ↦ Metric.ball x (r x))
      (fun x _ ↦ Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (hr x)))
  have hfrontCover : frontier D ⊆
      ⋃ x ∈ A, frontier D ∩ Metric.ball x (r x) := by
    intro z hz
    obtain ⟨x, hx⟩ := Set.mem_iUnion.1 (hcover (Set.mem_univ z))
    obtain ⟨hxA, hzball⟩ := Set.mem_iUnion.1 hx
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxA, hz, hzball⟩⟩
  apply measure_mono_null hfrontCover
  rw [measure_biUnion_null_iff hAcount]
  intro x hx
  apply measure_mono_null (hcross x)
  exact measure_union_null (volume_verticalLine x.re) (volume_horizontalLine x.im)

theorem finiteClosedCover_contains_subsegment
    {a b : Tiling.Plane} (hab : a ≠ b)
    {F : Finset (Set Tiling.Plane)}
    (hclosed : ∀ C ∈ F, IsClosed C)
    (hcover : openSegment ℝ a b ⊆ ⋃ C ∈ F, C) :
    ∃ C ∈ F, ∃ a' b' : Tiling.Plane,
      a' ≠ b' ∧ openSegment ℝ a' b' ⊆ openSegment ℝ a b ∩ C := by
  let I := Bool ⊕ {C : Set Tiling.Plane // C ∈ F}
  let A : I → Set ℝ
    | Sum.inl false => Iic 0
    | Sum.inl true => Ici 1
    | Sum.inr C => AffineMap.lineMap a b ⁻¹' C.1
  have hAclosed : ∀ i, IsClosed (A i) := by
    rintro (i | C)
    · cases i
      · exact isClosed_Iic
      · exact isClosed_Ici
    · apply (hclosed C.1 C.2).preimage
      fun_prop
  have hAcover : ⋃ i, A i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    by_cases ht0 : t ≤ 0
    · exact Set.mem_iUnion.2 ⟨Sum.inl false, ht0⟩
    by_cases ht1 : 1 ≤ t
    · exact Set.mem_iUnion.2 ⟨Sum.inl true, ht1⟩
    have ht : t ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_not_ge ht0, lt_of_not_ge ht1⟩
    have hm := hcover (lineMap_mem_openSegment (𝕜 := ℝ) a b ht)
    simp only [Set.mem_iUnion] at hm
    obtain ⟨C, hm⟩ := hm
    obtain ⟨hCF, hmC⟩ := hm
    exact Set.mem_iUnion.2 ⟨Sum.inr ⟨C, hCF⟩, hmC⟩
  have hdense : Dense (⋃ i, interior (A i)) :=
    dense_iUnion_interior_of_closed hAclosed hAcover
  obtain ⟨t, htUnion, ht⟩ := hdense.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.2 (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 htUnion
  rcases i with i | C
  · cases i with
    | false =>
        change t ∈ interior (Iic 0) at hi
        have : t ≤ 0 := by
          exact (interior_subset : interior (Iic (0 : ℝ)) ⊆ Iic 0) hi
        exact (not_lt_of_ge this ht.1).elim
    | true =>
        change t ∈ interior (Ici 1) at hi
        have : 1 ≤ t := by
          exact (interior_subset : interior (Ici (1 : ℝ)) ⊆ Ici 1) hi
        exact (not_lt_of_ge this ht.2).elim
  · have hnhds : A (Sum.inr C) ∩ Ioo (0 : ℝ) 1 ∈ nhds t :=
      Filter.inter_mem (mem_interior_iff_mem_nhds.1 hi)
        (isOpen_Ioo.mem_nhds ht)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
    let c := t - ε / 2
    let d := t + ε / 2
    have hε2 : 0 < ε / 2 := half_pos hε
    have hcball : c ∈ Metric.ball t ε := by
      simp only [Metric.mem_ball, Real.dist_eq]
      dsimp [c]
      rw [abs_of_nonpos] <;> linarith
    have hdball : d ∈ Metric.ball t ε := by
      simp only [Metric.mem_ball, Real.dist_eq, d]
      rw [add_sub_cancel_left, abs_of_nonneg]
      · linarith
      · linarith
    have hc : c ∈ A (Sum.inr C) ∩ Ioo (0 : ℝ) 1 := hball hcball
    have hd : d ∈ A (Sum.inr C) ∩ Ioo (0 : ℝ) 1 := hball hdball
    have hcd : c < d := by dsimp [c, d]; linarith
    refine ⟨C.1, C.2, AffineMap.lineMap a b c,
      AffineMap.lineMap a b d, ?_, ?_⟩
    · intro heq
      exact (ne_of_lt hcd) ((AffineMap.lineMap_injective ℝ hab) heq)
    · rw [← image_openSegment ℝ (AffineMap.lineMap a b) c d]
      rintro z ⟨u, hu, rfl⟩
      rw [openSegment_eq_Ioo hcd] at hu
      have huball : u ∈ Metric.ball t ε := by
        rw [Real.ball_eq_Ioo]
        dsimp [c, d] at hu ⊢
        have hhalf : ε / 2 < ε := half_lt_self hε
        exact ⟨(sub_lt_sub_left hhalf t).trans hu.1,
          hu.2.trans (by simpa [add_comm] using add_lt_add_left hhalf t)⟩
      have hu' := hball huball
      exact ⟨lineMap_mem_openSegment (𝕜 := ℝ) a b hu'.2, hu'.1⟩

private theorem exists_subsegment_avoiding_finite
    {a b : Tiling.Plane} (hab : a ≠ b) (hh : a.im = b.im)
    {V : Set Tiling.Plane} (hV : V.Finite) :
    ∃ a' b' : Tiling.Plane, a' ≠ b' ∧ a'.im = b'.im ∧
      openSegment ℝ a' b' ⊆ openSegment ℝ a b \ V := by
  let f : ℝ → Tiling.Plane := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have hpre : (f ⁻¹' V).Finite := hV.preimage hf.injOn
  have hdiff : (Ioo (0 : ℝ) 1 \ f ⁻¹' V).Nonempty :=
    ((Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).sdiff hpre).nonempty
  obtain ⟨u, huI, huV⟩ := hdiff
  have hopen : Ioo (0 : ℝ) 1 \ f ⁻¹' V ∈ nhds u :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds huI)
      (hpre.isClosed.isOpen_compl.mem_nhds huV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hopen
  let c := u - ε / 2
  let d := u + ε / 2
  have hε2 : 0 < ε / 2 := half_pos hε
  have hcball : c ∈ Metric.ball u ε := by
    simp only [Metric.mem_ball, Real.dist_eq]
    dsimp [c]
    rw [abs_of_nonpos] <;> linarith
  have hdball : d ∈ Metric.ball u ε := by
    simp only [Metric.mem_ball, Real.dist_eq, d]
    rw [add_sub_cancel_left, abs_of_nonneg] <;> linarith
  have hc := hball hcball
  have hd := hball hdball
  have hcd : c < d := by dsimp [c, d]; linarith
  refine ⟨AffineMap.lineMap a b c, AffineMap.lineMap a b d, ?_, ?_, ?_⟩
  · intro heq
    exact (ne_of_lt hcd) (hf heq)
  · simp [AffineMap.lineMap_apply, hh]
  · rw [← image_openSegment ℝ (AffineMap.lineMap a b) c d]
    rintro z ⟨t, ht, rfl⟩
    rw [openSegment_eq_Ioo hcd] at ht
    have htball : t ∈ Metric.ball u ε := by
      rw [Real.ball_eq_Ioo]
      dsimp [c, d] at ht ⊢
      have hhalf : ε / 2 < ε := half_lt_self hε
      exact ⟨(sub_lt_sub_left hhalf u).trans ht.1,
        ht.2.trans (by simpa [add_comm] using add_lt_add_left hhalf u)⟩
    have ht' := hball htball
    exact ⟨lineMap_mem_openSegment (𝕜 := ℝ) a b ht'.1, ht'.2⟩

theorem horizontalEdge_closureOverlap_gives_properContact
    {K : Region} {s t a b : Tiling.Plane} (hab : a ≠ b)
    (hh : a.im = b.im)
    (hpackingPair : volume ((s +ᵥ K.support) ∩ (t +ᵥ K.support)) = 0)
    (hedge : openSegment ℝ a b ⊆
      frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices))
    (hclosure : openSegment ℝ a b ⊆ t +ᵥ K.support) :
    HorizontalProperContact K s t := by
  have htfront : openSegment ℝ a b ⊆ frontier (t +ᵥ K.support) := by
    intro p hp
    have hpSupport : p ∈ t +ᵥ K.support := hclosure hp
    have hpNotInterior : p ∉ interior (t +ᵥ K.support) := by
      intro hpIntT
      have hpClosureS : p ∈ closure (interior (s +ᵥ K.support)) := by
        rw [interior_vadd, closure_vadd, K.isPolygonal.closure_interior]
        simpa only [(K.isPolygonal.vadd s).isClosed.closure_eq] using
          (frontier_subset_closure (hedge hp).1)
      have hmeet :
          (interior (t +ᵥ K.support) ∩ interior (s +ᵥ K.support)).Nonempty :=
        (mem_closure_iff.1 hpClosureS) _ isOpen_interior hpIntT
      have hpos : 0 < volume
          (interior (t +ᵥ K.support) ∩ interior (s +ᵥ K.support)) :=
        (isOpen_interior.inter isOpen_interior).measure_pos volume hmeet
      have hmono : interior (t +ᵥ K.support) ∩ interior (s +ᵥ K.support) ⊆
          (s +ᵥ K.support) ∩ (t +ᵥ K.support) := by
        rintro x ⟨hxt, hxs⟩
        exact ⟨interior_subset hxs, interior_subset hxt⟩
      have : 0 < volume ((s +ᵥ K.support) ∩ (t +ᵥ K.support)) :=
        hpos.trans_le (measure_mono hmono)
      simp only [hpackingPair, lt_self_iff_false] at this
    rw [frontier, (K.isPolygonal.vadd t).isClosed.closure_eq]
    exact ⟨hpSupport, hpNotInterior⟩
  have hvertices : (t +ᵥ K.vertices).Finite := by
    simpa only [Region.vertices, singleton_vadd] using
      (Set.finite_singleton t).vadd K.isPolygonal.vertexSet_finite
  obtain ⟨a', b', hab', hh', hsub⟩ :=
    exists_subsegment_avoiding_finite hab hh hvertices
  refine ⟨a', b', hab', hh', ?_⟩
  · intro p hp
    have hp' := hsub hp
    refine ⟨⟨(hedge hp'.1).1, htfront hp'.1⟩, ?_⟩
    intro hpv
    exact hpv.elim (hedge hp'.1).2 hp'.2

theorem horizontalSupportBoundary_containsTileEdge
    {K : Region} {T E S : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hST : S ⊆ T)
    {a b : Tiling.Plane} (hab : a ≠ b) (hh : a.im = b.im)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S)) :
    ∃ s ∈ S, ∃ a' b' : Tiling.Plane,
      a' ≠ b' ∧ a'.im = b'.im ∧
      openSegment ℝ a' b' ⊆ openSegment ℝ a b ∧
      openSegment ℝ a' b' ⊆
        frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices) := by
  have hpackingS : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K S).mpr
    exact fun s hs t ht hst ↦
      (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hST hs) (hST ht) hst
  let P := K.polygonalProtoTiling S
  let f : S → Set Tiling.Plane := fun s ↦ (s : Tiling.Plane) +ᵥ K.support
  let placementOf : S → P.placements := fun s ↦ ⟨((s : Tiling.Plane), ()), s.2⟩
  have hinj : Function.Injective placementOf := by
    intro s t h
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) h)
  have hlocal : LocallyFinite f := by
    have h := (P.locallyFinite_placedTile hpackingS).comp_injective hinj
    change LocallyFinite f at h
    exact h
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  let G : Finset S :=
    (hlocal.finite_nonempty_inter_compact hcompact).toFinset
  let F : Finset (Set Tiling.Plane) := G.image fun s ↦ frontier (f s)
  have hpoint {p : Tiling.Plane} (hp : p ∈ openSegment ℝ a b) :
      ∃ s : S, s ∈ G ∧ p ∈ frontier (f s) := by
    have hpfront := hBoundary hp
    have hpclosure : p ∈ closure (openUnion K S) := by
      have hp' := frontier_interior_subset hpfront
      simpa only [closure_closure] using frontier_subset_closure hp'
    rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support hpackingS] at hpclosure
    obtain ⟨s, hps⟩ := Set.mem_iUnion.1 hpclosure
    have hpnotint : p ∉ interior (f s) := by
      intro hpint
      have hpreg : p ∈ regularSupport K S := by
        apply interior_mono ?_ hpint
        rw [Tiling.AxisParallel.closure_openUnion_eq_iUnion_support hpackingS]
        exact subset_iUnion (fun q : S ↦ (q : Tiling.Plane) +ᵥ K.support) s
      rw [frontier] at hpfront
      apply hpfront.2
      change p ∈ interior (interior (closure (openUnion K S)))
      simpa only [regularSupport, Tiling.Polygonal.regularSupport, interior_interior] using hpreg
    have hpfronts : p ∈ frontier (f s) := by
      rw [frontier, (K.isPolygonal.vadd s.1).isClosed.closure_eq]
      exact ⟨hps, hpnotint⟩
    refine ⟨s, ?_, hpfronts⟩
    change s ∈ (hlocal.finite_nonempty_inter_compact hcompact).toFinset
    rw [Set.Finite.mem_toFinset]
    exact ⟨p, hps, openSegment_subset_segment ℝ a b hp⟩
  have hFclosed : ∀ C ∈ F, IsClosed C := by
    intro C hC
    simp only [F, Finset.mem_image] at hC
    obtain ⟨s, -, rfl⟩ := hC
    exact isClosed_frontier
  have hFcover : openSegment ℝ a b ⊆ ⋃ C ∈ F, C := by
    intro p hp
    obtain ⟨s, hsG, hps⟩ := hpoint hp
    rw [Set.mem_iUnion]
    refine ⟨frontier (f s), ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_image.2 ⟨s, hsG, rfl⟩, hps⟩
  obtain ⟨C, hCF, c, d, hcd, hsub⟩ :=
    finiteClosedCover_contains_subsegment hab hFclosed hFcover
  obtain ⟨s, hsG, hsC⟩ := Finset.mem_image.1 hCF
  subst C
  have hsS : (s : Tiling.Plane) ∈ S := s.2
  have hvertices : ((s : Tiling.Plane) +ᵥ K.vertices).Finite := by
    simpa only [Region.vertices, singleton_vadd] using
      (Set.finite_singleton (s : Tiling.Plane)).vadd K.isPolygonal.vertexSet_finite
  have hcdhor : c.im = d.im := by
    have hc := hsub (midpoint_mem_openSegment (𝕜 := ℝ) c d) |>.1
    have hthird : AffineMap.lineMap c d (1 / 3 : ℝ) ∈ openSegment ℝ c d :=
      lineMap_mem_openSegment (𝕜 := ℝ) c d (by norm_num)
    have hd := hsub hthird |>.1
    have segment_im {z : Tiling.Plane} (hz : z ∈ segment ℝ a b) : z.im = a.im := by
      rw [segment_eq_image] at hz
      obtain ⟨q, -, rfl⟩ := hz
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [hh]
      ring
    have hcim := segment_im (openSegment_subset_segment ℝ a b hc)
    have hdim := segment_im (openSegment_subset_segment ℝ a b hd)
    norm_num [midpoint, AffineMap.lineMap_apply] at hcim hdim
    linarith
  obtain ⟨a', b', hab', hh', hav⟩ :=
    exists_subsegment_avoiding_finite hcd hcdhor hvertices
  refine ⟨s, hsS, a', b', hab', hh', ?_, ?_⟩
  · intro p hp
    exact (hsub (hav hp).1).1
  · intro p hp
    have hp' := hav hp
    exact ⟨hsub hp'.1 |>.2, hp'.2⟩

theorem boundarySegment_coveredBy_outsideTileClosures
    {K : Region} {T S : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (_hST : S ⊆ T)
    {a b : Tiling.Plane} (_hab : a ≠ b)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S)) :
    openSegment ℝ a b ⊆
      ⋃ t : {t : Tiling.Plane // t ∈ T \ S},
        closure ((t : Tiling.Plane) +ᵥ K.openCarrier) := by
  have hdense : Dense (openUnion K T) := by
    apply (volume : Measure Tiling.Plane).dense_of_ae
    filter_upwards [hTile.2.2] with x hx
    change x ∈ ⋃ s : T, (s : Tiling.Plane) +ᵥ K.openCarrier
    rw [Set.mem_iUnion]
    exact hx.mp (Set.mem_univ x)
  let P := K.polygonalProtoTiling T
  let fT : T → Set Tiling.Plane := fun t ↦ (t : Tiling.Plane) +ᵥ K.support
  let placementOf : T → P.placements := fun t ↦ ⟨((t : Tiling.Plane), ()), t.2⟩
  have hinj : Function.Injective placementOf := by
    intro s t h
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) h)
  have hlocalT : LocallyFinite fT := by
    have h := (P.locallyFinite_placedTile hTile.2.1).comp_injective hinj
    change LocallyFinite fT at h
    exact h
  let R := {t : Tiling.Plane // t ∈ T \ S}
  let toT : R → T := fun t ↦ ⟨t.1, t.2.1⟩
  have htoT : Function.Injective toT := fun s t h ↦
    Subtype.ext (congrArg (fun u : T ↦ (u : Tiling.Plane)) h)
  have hlocalR : LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) := by
    have h := hlocalT.comp_injective htoT
    change LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) at h
    exact h
  have hclosedR : IsClosed (⋃ t : R, (t : Tiling.Plane) +ᵥ K.support) :=
    hlocalR.isClosed_iUnion fun t ↦ (K.isPolygonal.vadd t.1).isClosed
  intro z hzseg
  have hzfront := hBoundary hzseg
  have hzExteriorClosure :
      z ∈ closure ((closure (regularSupport K S))ᶜ) := by
    rw [mem_closure_iff]
    intro U hU hzU
    by_contra hmeet
    rw [Set.not_nonempty_iff_eq_empty] at hmeet
    have hUsub : U ⊆ closure (regularSupport K S) := by
      intro x hx
      by_contra hxcl
      have : x ∈ U ∩ (closure (regularSupport K S))ᶜ := ⟨hx, hxcl⟩
      rw [hmeet] at this
      exact this
    have hzint : z ∈ interior (closure (regularSupport K S)) :=
      mem_interior_iff_mem_nhds.2 (mem_nhds_iff.2 ⟨U, hUsub, hU, hzU⟩)
    have hregular : interior (closure (regularSupport K S)) = regularSupport K S := by
      rw [regularSupport, Tiling.Polygonal.regularSupport]
      exact interior_closure_idem
    have hzreg : z ∈ regularSupport K S := hregular ▸ hzint
    rw [frontier] at hzfront
    apply hzfront.2
    change z ∈ interior (interior (closure (openUnion K S)))
    simpa only [interior_interior, regularSupport, Tiling.Polygonal.regularSupport] using hzreg
  by_contra hzUnion
  simp only [Set.mem_iUnion, not_exists] at hzUnion
  have hzCompl : z ∈ (⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro t hzt
    apply hzUnion t
    rw [closure_vadd, Region.openCarrier,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
      K.isPolygonal.closure_interior]
    exact hzt
  have hopenCompl : IsOpen ((⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ) :=
    hclosedR.isOpen_compl
  have hmeetExterior := mem_closure_iff.1 hzExteriorClosure _ hopenCompl hzCompl
  obtain ⟨y, hyCompl, hyExterior⟩ := hmeetExterior
  have hopenMeet : IsOpen
      ((⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ ∩
        (closure (regularSupport K S))ᶜ) :=
    hopenCompl.inter isClosed_closure.isOpen_compl
  obtain ⟨x, hxTile, hxOpen⟩ := hdense.exists_mem_open hopenMeet
    ⟨y, hyCompl, hyExterior⟩
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxTile
  obtain ⟨t, hxt⟩ := hxTile
  have htNotS : (t : Tiling.Plane) ∉ S := by
    intro htS
    apply hxOpen.2
    apply subset_closure
    apply interior_maximal subset_closure
    · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun q ↦
        (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
          K.openCarrier_regularOpen.1
    rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨(t : Tiling.Plane), htS⟩, hxt⟩
  have hxSupport : x ∈ (t : Tiling.Plane) +ᵥ K.support := by
    rw [Region.openCarrier,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier] at hxt
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt ⊢
    exact interior_subset hxt
  exact hxOpen.1 (Set.mem_iUnion.2
    ⟨(⟨t.1, t.2, htNotS⟩ : R), hxSupport⟩)

private theorem horizontal_point_mem_openSegment_iff
    {a b : Tiling.Plane} (_hab : a ≠ b) (hh : a.im = b.im) (x : ℝ) :
    ((x : ℂ) + a.im * Complex.I) ∈ openSegment ℝ a b ↔
      x ∈ openSegment ℝ a.re b.re := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor <;> rintro ⟨u, hu, h⟩
  · refine ⟨u, hu, ?_⟩
    have := congrArg Complex.re h
    simpa using this
  · refine ⟨u, hu, ?_⟩
    apply Complex.ext
    · simpa using congrArg id h
    · simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        Complex.smul_im, smul_eq_mul]
      rw [hh]
      ring

private theorem localBoundaryCross_vadd_proof
    {D : Set Tiling.Plane} (hD : Tiling.IsAxisParallel D)
    (u x : Tiling.Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier (u +ᵥ D) →
      z.re = x.re ∨ z.im = x.im := by
  obtain ⟨r, hr, hball⟩ := hD.localBoundaryCross (x - u)
  refine ⟨r, hr, fun z hz hzfront ↦ ?_⟩
  have hzdist : z - u ∈ Metric.ball (x - u) r := by
    simpa only [Metric.mem_ball, dist_eq_norm, sub_sub_sub_cancel_right] using hz
  have hzsource : z - u ∈ frontier D := by
    rw [frontier, closure_vadd, interior_vadd] at hzfront
    rw [frontier]
    simpa only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hzfront
  rcases hball (z - u) hzdist hzsource with h | h
  · left
    simpa only [Complex.sub_re] using sub_left_inj.mp h
  · right
    simpa only [Complex.sub_im] using sub_left_inj.mp h

theorem positive_edge_overlap_gives_properContact
    {K : Region} {s t a b : Tiling.Plane} (hab : a ≠ b)
    (hh : a.im = b.im)
    (hedge : openSegment ℝ a b ⊆
      frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices))
    (hpositive : 0 < volume
      {x : ℝ | x ∈ openSegment ℝ a.re b.re ∧
        ((x : ℂ) + a.im * Complex.I) ∈
          frontier (t +ᵥ K.support) \ (t +ᵥ K.vertices)}) :
    HorizontalProperContact K s t := by
  let A : Set ℝ := {x : ℝ | x ∈ openSegment ℝ a.re b.re ∧
    ((x : ℂ) + a.im * Complex.I) ∈
      frontier (t +ᵥ K.support) \ (t +ᵥ K.vertices)}
  obtain ⟨V₀, H₀, hVH₀⟩ := K.isAxisParallel.exists_finite_boundary_axisLines
  let V := V₀.image fun y ↦ t.re + y
  let H := H₀.image fun y ↦ t.im + y
  have hVH (w : Tiling.Plane) (hw : w ∈ frontier (t +ᵥ K.support)) :
      w.re ∈ V ∨ w.im ∈ H := by
    have hw' : w - t ∈ frontier K.support := by
      rw [frontier, closure_vadd, interior_vadd] at hw
      rw [frontier]
      simpa only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hw
    rcases hVH₀ (w - t) hw' with hre | him
    · left
      apply Finset.mem_image.2
      exact ⟨(w - t).re, hre, by simp⟩
    · right
      apply Finset.mem_image.2
      exact ⟨(w - t).im, him, by simp⟩
  have hnotSub : ¬ A ⊆ (V : Set ℝ) := by
    intro hsub
    have hle : (volume : Measure ℝ) A ≤ volume (V : Set ℝ) := measure_mono hsub
    have hzero : volume (V : Set ℝ) = 0 := V.measure_zero volume
    have : ¬ 0 < volume A := by simpa only [hzero] using not_lt_of_ge hle
    exact this hpositive
  obtain ⟨x, hxA, hxV⟩ := Set.not_subset.1 hnotSub
  let z : Tiling.Plane := (x : ℂ) + a.im * Complex.I
  have hzfront : z ∈ frontier (t +ᵥ K.support) := hxA.2.1
  have hznotvertex : z ∉ Tiling.vertexSet (t +ᵥ K.support) := by
    simpa only [Region.vertices, Tiling.vertexSet_vadd] using hxA.2.2
  obtain ⟨L, hzL, hdim, hlocal⟩ :=
    (K.isPolygonal.vadd t).boundaryLocallyStraightAt_of_not_mem_vertexSet
      hzfront hznotvertex
  obtain ⟨v, hv, r₁, hr₁, hline⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hzL hdim hlocal
  obtain ⟨r₂, hr₂, hcross⟩ := localBoundaryCross_vadd_proof K.isAxisParallel t z
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let δ := r / (2 * ‖v‖)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hδ : 0 < δ := div_pos hr (mul_pos zero_lt_two hvnorm)
  let q := z + δ • v
  have hqball : q ∈ Metric.ball z r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [q, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    dsimp [δ]
    field_simp
    linarith
  have hqline : q ∈ Tiling.affineLine z v := by
    rw [Tiling.mem_affineLine_iff_exists_smul hv]
    exact ⟨δ, rfl⟩
  have hqfront : q ∈ frontier (t +ᵥ K.support) :=
    (hline q (Metric.ball_subset_ball (min_le_left _ _) hqball)).2 hqline
  have haxis := hcross q (Metric.ball_subset_ball (min_le_right _ _) hqball) hqfront
  have hvaxis : v.re = 0 ∨ v.im = 0 := by
    rcases haxis with hre | him
    · left
      simp only [q, Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
      exact (mul_eq_zero.mp (by linarith : δ * v.re = 0)).resolve_left hδ.ne'
    · right
      simp only [q, Complex.add_im, Complex.smul_im, smul_eq_mul] at him
      exact (mul_eq_zero.mp (by linarith : δ * v.im = 0)).resolve_left hδ.ne'
  have hvim : v.im = 0 := by
    rcases hvaxis with hvre | hvim
    · have hvimne : v.im ≠ 0 := by
        intro hvim
        apply hv
        exact Complex.ext hvre hvim
      let g : ℝ → ℝ := fun u ↦ (z + u • v).im
      have hginj : Function.Injective g := by
        intro u w huw
        simp only [g, Complex.add_im, Complex.smul_im, smul_eq_mul] at huw
        apply mul_right_cancel₀ hvimne
        linarith
      have hpre : (g ⁻¹' (H : Set ℝ)).Finite := H.finite_toSet.preimage hginj.injOn
      let e := r / ‖v‖
      have he : 0 < e := div_pos hr hvnorm
      have hmany := (Set.Ioo_infinite (neg_lt_self he)).sdiff hpre
      obtain ⟨u, huI, huH⟩ := hmany.nonempty
      let w := z + u • v
      have hwball : w ∈ Metric.ball z r := by
        rw [Metric.mem_ball, dist_eq_norm]
        simp only [w, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        have huabs : |u| < e := (abs_lt.2 huI)
        dsimp [e] at huabs
        calc
          |u| * ‖v‖ < (r / ‖v‖) * ‖v‖ := mul_lt_mul_of_pos_right huabs hvnorm
          _ = r := div_mul_cancel₀ r hvnorm.ne'
      have hwline : w ∈ Tiling.affineLine z v := by
        rw [Tiling.mem_affineLine_iff_exists_smul hv]
        exact ⟨u, rfl⟩
      have hwfront : w ∈ frontier (t +ᵥ K.support) :=
        (hline w (Metric.ball_subset_ball (min_le_left _ _) hwball)).2 hwline
      rcases hVH w hwfront with hwV | hwH
      · exfalso
        apply hxV
        simpa [w, z, hvre] using hwV
      · exfalso
        exact huH hwH
    · exact hvim
  have habre : a.re ≠ b.re := by
    intro hre
    exact hab (Complex.ext hre hh)
  have hopenReal : IsOpen (openSegment ℝ a.re b.re) := by
    rw [openSegment_eq_Ioo' habre]
    exact isOpen_Ioo
  obtain ⟨ρ, hρ, hρball⟩ := Metric.mem_nhds_iff.1
    (hopenReal.mem_nhds hxA.1)
  let W := (s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices)
  have hWfinite : W.Finite := by
    apply Set.Finite.union
    · simpa only [W, Region.vertices, singleton_vadd] using
        (Set.finite_singleton s).vadd K.isPolygonal.vertexSet_finite
    · simpa only [W, Region.vertices, singleton_vadd] using
        (Set.finite_singleton t).vadd K.isPolygonal.vertexSet_finite
  have hzseg : z ∈ openSegment ℝ a b :=
    (horizontal_point_mem_openSegment_iff hab hh x).2 hxA.1
  have hzW : z ∉ W := fun hzmem ↦ hzmem.elim (hedge hzseg).2 hxA.2.2
  obtain ⟨ν, hν, hνball⟩ := Metric.mem_nhds_iff.1
    (hWfinite.isClosed.isOpen_compl.mem_nhds hzW)
  let e := min (min (r / 2) (ρ / 2)) (ν / 2)
  have he : 0 < e := lt_min (lt_min (half_pos hr) (half_pos hρ)) (half_pos hν)
  have her : e < r :=
    (min_le_left _ _).trans (min_le_left _ _) |>.trans_lt (half_lt_self hr)
  have heρ : e < ρ := (min_le_left _ _ |>.trans (min_le_right _ _)).trans_lt
    (half_lt_self hρ)
  have heν : e < ν := (min_le_right _ _).trans_lt (half_lt_self hν)
  let c : Tiling.Plane := z - (e : ℂ)
  let d : Tiling.Plane := z + (e : ℂ)
  refine ⟨c, d, ?_, ?_, ?_⟩
  · intro hcd
    have := congrArg Complex.re hcd
    simp [c, d] at this
    linarith
  · simp [c, d]
  · intro p hp
    rw [openSegment_eq_image] at hp
    obtain ⟨u, hu, rfl⟩ := hp
    have hpform : (1 - u) • c + u • d =
        z + (((2 * u - 1) * e : ℝ) : ℂ) := by
      simp only [c, d, Complex.ofReal_mul, Complex.ofReal_sub,
        Complex.ofReal_one, Complex.real_smul]
      push_cast
      ring
    have hpball : (1 - u) • c + u • d ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [hpform, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rcases hu with ⟨hu0, hu1⟩
      have huabs : |2 * u - 1| < 1 := (abs_lt.2 ⟨by linarith, by linarith⟩)
      rw [abs_mul, abs_of_pos he]
      exact (mul_lt_of_lt_one_left he huabs).trans her
    have hpline : (1 - u) • c + u • d ∈ Tiling.affineLine z v := by
      rw [Tiling.mem_affineLine_iff_exists_smul hv]
      refine ⟨(((2 * u - 1) * e) / v.re), ?_⟩
      apply Complex.ext
      · have hvrene : v.re ≠ 0 := by
          intro h
          exact hv (Complex.ext h hvim)
        simp only [c, d, Complex.smul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.add_re, smul_eq_mul]
        field_simp
        ring
      · simp [c, d, hvim]
        ring
    have hpfrontT : (1 - u) • c + u • d ∈ frontier (t +ᵥ K.support) :=
      (hline _ (Metric.ball_subset_ball (min_le_left _ _) hpball)).2 hpline
    have hpfrontS : (1 - u) • c + u • d ∈ frontier (s +ᵥ K.support) := by
      apply (hedge ?_).1
      rw [show (1 - u) • c + u • d =
          ((((1 - u) • c + u • d).re : ℂ) + a.im * Complex.I) by
        rw [hpform]
        apply Complex.ext <;> simp [z]]
      apply (horizontal_point_mem_openSegment_iff hab hh _).2
      apply hρball
      rw [Metric.mem_ball, Real.dist_eq]
      rw [hpform]
      simp only [Complex.add_re, Complex.ofReal_re, z, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
        sub_zero]
      rcases hu with ⟨hu0, hu1⟩
      have huabs : |2 * u - 1| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
      have hsmall : |(2 * u - 1) * e| < ρ := by
        rw [abs_mul, abs_of_pos he]
        exact (mul_lt_of_lt_one_left he huabs).trans heρ
      ring_nf
      convert hsmall using 1
      congr 1
      ring
    refine ⟨⟨hpfrontS, hpfrontT⟩, ?_⟩
    have hpν : (1 - u) • c + u • d ∈ Metric.ball z ν := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [hpform, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
      rcases hu with ⟨hu0, hu1⟩
      have huabs : |2 * u - 1| < 1 := abs_lt.2 ⟨by linarith, by linarith⟩
      rw [abs_mul, abs_of_pos he]
      exact (mul_lt_of_lt_one_left he huabs).trans heν
    exact hνball hpν

theorem regularSupport_sdiff_of_packing
    {K : Region} {T E P Q : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hPT : P ⊆ T) (hQP : Q ⊆ P) :
    regularSupport K (P \ Q) =
      interior (closure (regularSupport K P \ regularSupport K Q)) := by
  let U := regularSupport K (P \ Q)
  let V := interior (closure (regularSupport K P \ regularSupport K Q))
  have hUopen : IsOpen U := isOpen_interior
  have hUregular : interior (closure U) = U := by
    dsimp only [U, regularSupport]
    exact interior_closure_idem
  have hVopen : IsOpen V := isOpen_interior
  have hVregular : interior (closure V) = V := by
    dsimp only [V]
    exact interior_closure_idem
  have hpackingP : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P).mpr
    exact fun p hp q hq hpq ↦
      (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hPT hp) (hPT hq) hpq
  have hpackingQ : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements Q) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K Q).mpr
    exact fun p hp q hq hpq ↦
      (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hPT (hQP hp)) (hPT (hQP hq)) hpq
  apply Tiling.AxisParallel.regularOpen_eq_of_aeEq hUopen hUregular hVopen hVregular
  exact (regularSupport_sdiff_aeEq hTile hPT hQP).trans
    (difference_aeEq_regularizedDifference isOpen_interior isOpen_interior
      (regularSupport_frontier_null hpackingP)
      (regularSupport_frontier_null hpackingQ))

theorem boundary_withoutHorizontalSegment_isVerticalInvariant
    {D : Set Tiling.Plane}
    (hDregular : D = interior (closure D))
    (hDpolygonal : IsLocallyAxisParallelPolygonal D)
    (hNoHorizontal : ∀ a b : Tiling.Plane,
      a ≠ b → a.im = b.im → ¬ openSegment ℝ a b ⊆ frontier D) :
    ∃ X : Set ℝ, X = interior (closure X) ∧ D = Complex.re ⁻¹' X := by
  have hcross : ∀ z ∈ frontier D, ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ Metric.ball z r, w ∈ frontier D →
        w.re = z.re ∨ w.im = z.im := by
    intro z hz
    exact locallyPolygonal_has_localBoundaryCross hDpolygonal hz
  have hgerm : ∀ z ∈ frontier D, ∃ r : ℝ, 0 < r ∧
      {w : Tiling.Plane | w.re = z.re ∧ dist w z < r} ⊆ frontier D := by
    intro z hz
    exact localBoundaryCross_noHorizontal_verticalGerm
      hDregular hcross hNoHorizontal hz
  have hvertical : ∀ z ∈ frontier D,
      {w : Tiling.Plane | w.re = z.re} ⊆ frontier D := by
    intro z hz
    exact verticalGerms_extend_to_lines hgerm hz
  exact regularOpen_of_vertical_frontier_is_cylinder hDregular hvertical

theorem exposedHorizontalEdge_hasOppositeTile
    {K : Region} {T S : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hST : S ⊆ T)
    {s : Tiling.Plane} (hs : s ∈ S) {a b : Tiling.Plane}
    (hab : a ≠ b) (hHorizontal : a.im = b.im)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S))
    (hTileEdge : openSegment ℝ a b ⊆
      frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices)) :
    ∃ t ∈ T \ S, HorizontalProperContact K s t := by
  let P := K.polygonalProtoTiling T
  let fT : T → Set Tiling.Plane := fun t ↦ (t : Tiling.Plane) +ᵥ K.support
  let placementOf : T → P.placements := fun t ↦ ⟨((t : Tiling.Plane), ()), t.2⟩
  have hinj : Function.Injective placementOf := by
    intro u v h
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) h)
  have hlocalT : LocallyFinite fT := by
    have h := (P.locallyFinite_placedTile hTile.2.1).comp_injective hinj
    change LocallyFinite fT at h
    exact h
  let R := {t : Tiling.Plane // t ∈ T \ S}
  let toT : R → T := fun t ↦ ⟨t.1, t.2.1⟩
  have htoT : Function.Injective toT := fun u v h ↦
    Subtype.ext (congrArg (fun q : T ↦ (q : Tiling.Plane)) h)
  have hlocalR : LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) := by
    have h := hlocalT.comp_injective htoT
    change LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) at h
    exact h
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  let G : Finset R := (hlocalR.finite_nonempty_inter_compact hcompact).toFinset
  let F : Finset (Set Tiling.Plane) :=
    G.image fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support
  have houtside := boundarySegment_coveredBy_outsideTileClosures
    hTile hST hab hBoundary
  have hcover : openSegment ℝ a b ⊆ ⋃ C ∈ F, C := by
    intro x hx
    have hx' := houtside hx
    rw [Set.mem_iUnion] at hx'
    obtain ⟨t, hxt⟩ := hx'
    have hxt' : x ∈ (t : Tiling.Plane) +ᵥ K.support := by
      rw [closure_vadd, Region.openCarrier,
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
        K.isPolygonal.closure_interior] at hxt
      exact hxt
    have htG : t ∈ G := by
      change t ∈ (hlocalR.finite_nonempty_inter_compact hcompact).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hxt', openSegment_subset_segment ℝ a b hx⟩
    rw [Set.mem_iUnion]
    refine ⟨(t : Tiling.Plane) +ᵥ K.support, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_image.2 ⟨t, htG, rfl⟩, hxt'⟩
  have hclosed : ∀ C ∈ F, IsClosed C := by
    intro C hC
    obtain ⟨t : R, -, rfl⟩ := Finset.mem_image.1 hC
    exact (K.isPolygonal.vadd t.1).isClosed
  obtain ⟨C, hCF, c, d, hcd, hsub⟩ :=
    finiteClosedCover_contains_subsegment hab hclosed hcover
  obtain ⟨t : R, htG, htC⟩ := Finset.mem_image.1 hCF
  subst C
  have hcdHorizontal : c.im = d.im := by
    have segment_im {z : Tiling.Plane} (hz : z ∈ segment ℝ a b) : z.im = a.im := by
      rw [segment_eq_image] at hz
      obtain ⟨q, -, rfl⟩ := hz
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [hHorizontal]
      ring
    have hc := hsub (midpoint_mem_openSegment (𝕜 := ℝ) c d) |>.1
    have hthird : AffineMap.lineMap c d (1 / 3 : ℝ) ∈ openSegment ℝ c d :=
      lineMap_mem_openSegment (𝕜 := ℝ) c d (by norm_num)
    have hd := hsub hthird |>.1
    have hcim := segment_im (openSegment_subset_segment ℝ a b hc)
    have hdim := segment_im (openSegment_subset_segment ℝ a b hd)
    norm_num [midpoint, AffineMap.lineMap_apply] at hcim hdim
    linarith
  have hsT : s ∈ T := hST hs
  have hst : s ≠ (t : Tiling.Plane) := by
    intro heq
    exact t.2.2 (heq ▸ hs)
  have hpackingPair : volume
      ((s +ᵥ K.support) ∩ ((t : Tiling.Plane) +ᵥ K.support)) = 0 := by
    have hp := hTile.2.1
      (show ((s, ()) : Tiling.Placement Tiling.Plane Unit) ∈
        K.toPolygonalRegion.placements T by exact hsT)
      (show (((t : Tiling.Plane), ()) : Tiling.Placement Tiling.Plane Unit) ∈
        K.toPolygonalRegion.placements T by exact t.2.1)
      (by intro h; exact hst (congrArg Prod.fst h))
    exact hp
  refine ⟨t, t.2, horizontalEdge_closureOverlap_gives_properContact
    hcd hcdHorizontal hpackingPair ?_ ?_⟩
  · exact hsub.trans (inter_subset_left.trans hTileEdge)
  · exact hsub.trans inter_subset_right

theorem VerticalPlate.support_isVerticalSlab
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (P : VerticalPlate K T) :
    P.base = interior (closure P.base) ∧
      P.support = Complex.re ⁻¹' P.base := by
  have hcentres : P.centres ⊆ T := by
    rintro s ⟨q, hqP, rfl⟩
    exact q.2
  have hpackingP : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    exact fun s hs t ht hst ↦
      (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hcentres hs) (hcentres ht) hst
  have hNoHorizontal : ∀ a b : Tiling.Plane,
      a ≠ b → a.im = b.im →
        ¬ openSegment ℝ a b ⊆ frontier P.support := by
    intro a b hab hh hseg
    obtain ⟨s, hsP, c, d, hcd, hcdhor, hcdsub, hTileEdge⟩ :=
      horizontalSupportBoundary_containsTileEdge hTile hcentres hab hh hseg
    obtain ⟨t, htOutside, hcontact⟩ :=
      exposedHorizontalEdge_hasOppositeTile hTile hcentres hsP
        hcd hcdhor (hcdsub.trans hseg) hTileEdge
    obtain ⟨sT, hsSupp, hsEq⟩ := hsP
    subst s
    let tT : T := ⟨t, htOutside.1⟩
    have hadj : (verticalPlateGraph K T).Adj sT tT := by
      rw [verticalPlateGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl hcontact⟩
      intro heq
      apply htOutside.2
      have hval : (sT : Tiling.Plane) = (tT : Tiling.Plane) :=
        congrArg Subtype.val heq
      change (sT : Tiling.Plane) = t at hval
      exact hval ▸ (show (sT : Tiling.Plane) ∈ P.centres from ⟨sT, hsSupp, rfl⟩)
    have hmkS : (verticalPlateGraph K T).connectedComponentMk sT = P :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P sT).1 hsSupp
    have hmkEq :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have htSupp : tT ∈ P.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P tT).2 (hmkEq.symm.trans hmkS)
    apply htOutside.2
    exact ⟨tT, htSupp, rfl⟩
  have hregular : P.support = interior (closure P.support) := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_closure_idem.symm
  have hcross : ∀ z ∈ frontier P.support, ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ Metric.ball z r, w ∈ frontier P.support →
        w.re = z.re ∨ w.im = z.im := by
    intro z _hz
    exact Tiling.AxisParallel.regularSupport_localBoundaryCross hpackingP z
  have hgerm : ∀ z ∈ frontier P.support, ∃ r : ℝ, 0 < r ∧
      {w : Tiling.Plane | w.re = z.re ∧ dist w z < r} ⊆ frontier P.support := by
    intro z hz
    exact localBoundaryCross_noHorizontal_verticalGerm
      hregular hcross hNoHorizontal hz
  have hvertical : ∀ z ∈ frontier P.support,
      {w : Tiling.Plane | w.re = z.re} ⊆ frontier P.support := by
    intro z hz
    exact verticalGerms_extend_to_lines hgerm hz
  obtain ⟨X, hXregular, hsupport⟩ :=
    regularOpen_of_vertical_frontier_is_cylinder hregular hvertical
  have hbase : P.base = X := by
    ext x
    constructor
    · rintro ⟨z, hzP, rfl⟩
      exact (show z ∈ Complex.re ⁻¹' X by simpa only [← hsupport] using hzP)
    · intro hx
      refine ⟨(x : ℂ), ?_, by simp⟩
      rw [hsupport]
      exact hx
  constructor
  · rw [hbase]
    exact hXregular
  · rw [hbase]
    exact hsupport


theorem verticalSlab_sdiff
    {K : Region} {T E P Q : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hPT : P ⊆ T) (hQP : Q ⊆ P)
    (hP : ∃ X : Set ℝ,
      X = interior (closure X) ∧ regularSupport K P = Complex.re ⁻¹' X)
    (hQ : ∃ X : Set ℝ,
      X = interior (closure X) ∧ regularSupport K Q = Complex.re ⁻¹' X) :
    ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K (P \ Q) = Complex.re ⁻¹' X := by
  obtain ⟨XP, hXPreg, hPsupport⟩ := hP
  obtain ⟨XQ, hXQreg, hQsupport⟩ := hQ
  let X := interior (closure (XP \ XQ))
  refine ⟨X, ?_, ?_⟩
  · dsimp only [X]
    exact interior_closure_idem.symm
  · rw [regularSupport_sdiff_of_packing hTile hPT hQP,
      hPsupport, hQsupport, ← Set.preimage_sdiff,
      Complex.closure_preimage_re, Complex.interior_preimage_re]

private theorem wholeSupport_eq_univ
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    regularSupport K T = Set.univ := by
  exact Tiling.AxisParallel.regularSupport_eq_of_tilesOn isOpen_univ
    (by simp) hTile

theorem VerticalPlate.minimal
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (P : VerticalPlate K T) :
    IsMinimalVerticalSlabSubfamily K T P.centres := by
  have hPnonempty : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  have hPsub : P.centres ⊆ T := by
    rintro p ⟨q, -, rfl⟩
    exact q.2
  obtain ⟨hPreg, hPsupport⟩ := VerticalPlate.support_isVerticalSlab hTile P
  refine ⟨hPnonempty, hPsub, ⟨P.base, hPreg, hPsupport⟩, ?_⟩
  intro Q hQnonempty hQP hQslab
  obtain ⟨XQ, hXQreg, hQsupport⟩ := hQslab
  have hTslab : ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K T = Complex.re ⁻¹' X := by
    refine ⟨Set.univ, by simp, ?_⟩
    rw [wholeSupport_eq_univ hTile]
    simp
  obtain ⟨XB, hXBreg, hBsupport⟩ := verticalSlab_sdiff
    hTile (Subset.refl T) (hQP.trans hPsub) hTslab
    ⟨XQ, hXQreg, hQsupport⟩
  let parts : Bool → Set Tiling.Plane
    | false => Q
    | true => T \ Q
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.2 fun _ hxQ hxB ↦ hxB.2 hxQ
    · exact Set.disjoint_left.2 fun _ hxB hxQ ↦ hxB.2 hxQ
    · exact (hij rfl).elim
  have hunion : (⋃ i, parts i) = T := by
    ext x
    constructor
    · simp only [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      cases i
      · exact (hQP.trans hPsub) hi
      · exact hi.1
    · intro hxT
      by_cases hxQ : x ∈ Q
      · exact Set.mem_iUnion.2 ⟨false, hxQ⟩
      · exact Set.mem_iUnion.2 ⟨true, hxT, hxQ⟩
  have hdisj := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
    parts hparts hunion hTile).1
  have hQBdisj : Disjoint (regularSupport K Q) (regularSupport K (T \ Q)) := by
    have := hdisj (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K Q) (regularSupport K (T \ Q)) at this
    exact this
  have hsat := verticalPlates_saturated_of_slabPartition K
    (show Q ∪ (T \ Q) = T by
      ext x
      constructor
      · rintro (hxQ | hxB)
        · exact (hQP.trans hPsub) hxQ
        · exact hxB.1
      · intro hxT
        by_cases hxQ : x ∈ Q
        · exact Or.inl hxQ
        · exact Or.inr ⟨hxT, hxQ⟩)
    hQBdisj hXQreg.symm hXBreg.symm hQsupport hBsupport
  have hmeet : (P.centres ∩ Q).Nonempty := by
    obtain ⟨q, hqQ⟩ := hQnonempty
    exact ⟨q, hQP hqQ, hqQ⟩
  exact Set.Subset.antisymm hQP (hsat.1 P hmeet)

theorem verticalPlates_intrinsic
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) :
    Set.range (@VerticalPlate.centres K T) =
      {S : Set Tiling.Plane | IsMinimalVerticalSlabSubfamily K T S} := by
  ext S
  constructor
  · rintro ⟨P, rfl⟩
    exact VerticalPlate.minimal hTile P
  · intro hSminimal
    rw [Set.mem_ofPred_eq] at hSminimal
    obtain ⟨hSnonempty, hSsub, ⟨XS, hXSreg, hSsupport⟩, hSmin⟩ := hSminimal
    obtain ⟨s, hsS⟩ := hSnonempty
    let sT : T := ⟨s, hSsub hsS⟩
    let P : VerticalPlate K T := VerticalPlate.ofCentre sT
    have hTslab : ∃ X : Set ℝ, X = interior (closure X) ∧
        regularSupport K T = Complex.re ⁻¹' X :=
      ⟨Set.univ, by simp, by rw [wholeSupport_eq_univ hTile]; simp⟩
    obtain ⟨XB, hXBreg, hBsupport⟩ := verticalSlab_sdiff
      hTile (Subset.refl T) hSsub hTslab ⟨XS, hXSreg, hSsupport⟩
    let parts : Bool → Set Tiling.Plane
      | false => S
      | true => T \ S
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact Set.disjoint_left.2 fun _ hxS hxB ↦ hxB.2 hxS
      · exact Set.disjoint_left.2 fun _ hxB hxS ↦ hxB.2 hxS
      · exact (hij rfl).elim
    have hunion : (⋃ i, parts i) = T := by
      ext x
      constructor
      · simp only [Set.mem_iUnion]
        rintro ⟨i, hi⟩
        cases i
        · exact hSsub hi
        · exact hi.1
      · intro hxT
        by_cases hxS : x ∈ S
        · exact Set.mem_iUnion.2 ⟨false, hxS⟩
        · exact Set.mem_iUnion.2 ⟨true, hxT, hxS⟩
    have hpair := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
      parts hparts hunion hTile).1
    have hdisj : Disjoint (regularSupport K S) (regularSupport K (T \ S)) := by
      have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
      change Disjoint (regularSupport K S) (regularSupport K (T \ S)) at h
      exact h
    have hsat := verticalPlates_saturated_of_slabPartition K
      (show S ∪ (T \ S) = T by
        ext x
        constructor
        · rintro (hxS | hxB)
          · exact hSsub hxS
          · exact hxB.1
        · intro hxT
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hxT, hxS⟩)
      hdisj hXSreg.symm hXBreg.symm hSsupport hBsupport
    have hsP : s ∈ P.centres := by
      refine ⟨sT, ?_, rfl⟩
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P sT).2 rfl
    have hPsubS : P.centres ⊆ S :=
      hsat.1 P ⟨s, hsP, hsS⟩
    have hPnonempty : P.centres.Nonempty := ⟨s, hsP⟩
    obtain ⟨hPreg, hPsupport⟩ := VerticalPlate.support_isVerticalSlab hTile P
    have hPeq : P.centres = S := hSmin P.centres hPnonempty hPsubS
      ⟨P.base, hPreg, hPsupport⟩
    exact ⟨P, hPeq⟩

theorem verticalColumn_regularSupport
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (P : VerticalPlate K T)
    (_hPcolumn : IsVerticalColumn P) {x : ℝ}
    (hx : P.centres ⊆ {z : Tiling.Plane | z.re = x}) :
    P.base = interior (closure ((Complex.re '' K.openCarrier) + {x})) ∧
      P.support = Complex.re ⁻¹' P.base := by
  let A : Set ℝ := (Complex.re '' K.openCarrier) + {x}
  have hPnonempty : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  have hproj : Complex.re '' openUnion K P.centres = A := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
      refine ⟨(z - (s : Tiling.Plane)).re, ?_, x, Set.mem_singleton x, ?_⟩
      · refine ⟨z - (s : Tiling.Plane), ?_, rfl⟩
        simpa only [vadd_eq_add, neg_add_eq_sub] using hs
      · have hsx := hx s.2
        simp only [Set.mem_ofPred_eq] at hsx
        simp only [Complex.sub_re]
        linarith
    · rintro ⟨u, ⟨k, hk, rfl⟩, v, hv, rfl⟩
      rw [Set.mem_singleton_iff] at hv
      subst v
      obtain ⟨s, hsP⟩ := hPnonempty
      refine ⟨s + k, ?_, ?_⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        refine ⟨⟨s, hsP⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa using hk
      · have hsx := hx hsP
        simp only [Set.mem_ofPred_eq] at hsx
        simp [hsx, add_comm]
  have hopenUnion : IsOpen (openUnion K P.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  have hrawSupport : openUnion K P.centres ⊆ P.support := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_maximal subset_closure hopenUnion
  have hsupportClosure : P.support ⊆ closure (openUnion K P.centres) := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_subset
  have hA_base : A ⊆ P.base := by
    rw [← hproj]
    exact Set.image_mono hrawSupport
  have hbase_closureA : P.base ⊆ closure A := by
    rintro y ⟨z, hzP, rfl⟩
    have hzcl := hsupportClosure hzP
    have hmap : Set.MapsTo Complex.re (openUnion K P.centres) A := by
      intro w hw
      rw [← hproj]
      exact ⟨w, hw, rfl⟩
    exact hmap.closure Complex.continuous_re hzcl
  obtain ⟨hbaseRegular, hsupport⟩ := VerticalPlate.support_isVerticalSlab hTile P
  have hbaseOpen : IsOpen P.base := by
    rw [hbaseRegular]
    exact isOpen_interior
  have hbaseEq : P.base = interior (closure A) := by
    apply Set.Subset.antisymm
    · exact interior_maximal hbase_closureA hbaseOpen
    · rw [hbaseRegular]
      exact interior_mono (closure_mono hA_base)
  exact ⟨hbaseEq, hsupport⟩

theorem boundarySegment_coveredBy_outsideTileClosures_relative
    {K : Region} {T S E : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hEopen : IsOpen E) (_hST : S ⊆ T)
    {a b : Tiling.Plane} (_hab : a ≠ b)
    (hSegmentE : openSegment ℝ a b ⊆ E)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S)) :
    openSegment ℝ a b ⊆
      ⋃ t : {t : Tiling.Plane // t ∈ T \ S},
        closure ((t : Tiling.Plane) +ᵥ K.openCarrier) := by
  have hdense : Dense (openUnion K T ∪ Eᶜ) := by
    apply (volume : Measure Tiling.Plane).dense_of_ae
    filter_upwards [hTile.2.2] with x hx
    by_cases hxE : x ∈ E
    · left
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      exact hx.mp hxE
    · exact Or.inr hxE
  let P := K.polygonalProtoTiling T
  let fT : T → Set Tiling.Plane := fun t ↦ (t : Tiling.Plane) +ᵥ K.support
  let placementOf : T → P.placements := fun t ↦ ⟨((t : Tiling.Plane), ()), t.2⟩
  have hinj : Function.Injective placementOf := by
    intro s t h
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) h)
  have hlocalT : LocallyFinite fT := by
    have h := (P.locallyFinite_placedTile hTile.2.1).comp_injective hinj
    change LocallyFinite fT at h
    exact h
  let R := {t : Tiling.Plane // t ∈ T \ S}
  let toT : R → T := fun t ↦ ⟨t.1, t.2.1⟩
  have htoT : Function.Injective toT := fun s t h ↦
    Subtype.ext (congrArg (fun u : T ↦ (u : Tiling.Plane)) h)
  have hlocalR : LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) := by
    have h := hlocalT.comp_injective htoT
    change LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) at h
    exact h
  have hclosedR : IsClosed (⋃ t : R, (t : Tiling.Plane) +ᵥ K.support) :=
    hlocalR.isClosed_iUnion fun t ↦ (K.isPolygonal.vadd t.1).isClosed
  intro z hzseg
  have hzfront := hBoundary hzseg
  have hzExteriorClosure : z ∈ closure ((closure (regularSupport K S))ᶜ) := by
    rw [mem_closure_iff]
    intro U hU hzU
    by_contra hmeet
    rw [Set.not_nonempty_iff_eq_empty] at hmeet
    have hUsub : U ⊆ closure (regularSupport K S) := by
      intro x hx
      by_contra hxcl
      have : x ∈ U ∩ (closure (regularSupport K S))ᶜ := ⟨hx, hxcl⟩
      rw [hmeet] at this
      exact this
    have hzint : z ∈ interior (closure (regularSupport K S)) :=
      mem_interior_iff_mem_nhds.2 (mem_nhds_iff.2 ⟨U, hUsub, hU, hzU⟩)
    have hregular : interior (closure (regularSupport K S)) = regularSupport K S := by
      rw [regularSupport, Tiling.Polygonal.regularSupport]
      exact interior_closure_idem
    have hzreg : z ∈ regularSupport K S := hregular ▸ hzint
    rw [frontier] at hzfront
    apply hzfront.2
    change z ∈ interior (interior (closure (openUnion K S)))
    simpa only [interior_interior, regularSupport, Tiling.Polygonal.regularSupport] using hzreg
  by_contra hzUnion
  simp only [Set.mem_iUnion, not_exists] at hzUnion
  have hzCompl : z ∈ (⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro t hzt
    apply hzUnion t
    rw [closure_vadd, Region.openCarrier,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
      K.isPolygonal.closure_interior]
    exact hzt
  have hopenCompl : IsOpen ((⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ) :=
    hclosedR.isOpen_compl
  have hnear :
      ((⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ ∩ E) ∈ nhds z :=
    Filter.inter_mem (hopenCompl.mem_nhds hzCompl)
      (hEopen.mem_nhds (hSegmentE hzseg))
  have hmeetExterior :=
    mem_closure_iff.1 hzExteriorClosure _
      (hopenCompl.inter hEopen) ⟨hzCompl, hSegmentE hzseg⟩
  obtain ⟨y, ⟨hyCompl, hyE⟩, hyExterior⟩ := hmeetExterior
  have hopenMeet : IsOpen
      (((⋃ t : R, (t : Tiling.Plane) +ᵥ K.support)ᶜ ∩ E) ∩
        (closure (regularSupport K S))ᶜ) :=
    (hopenCompl.inter hEopen).inter isClosed_closure.isOpen_compl
  obtain ⟨x, hxDense, hxOpen⟩ := hdense.exists_mem_open hopenMeet
    ⟨y, ⟨hyCompl, hyE⟩, hyExterior⟩
  have hxTile : x ∈ openUnion K T :=
    hxDense.resolve_right (fun hxEc ↦ hxEc hxOpen.1.2)
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxTile
  obtain ⟨t, hxt⟩ := hxTile
  have htNotS : (t : Tiling.Plane) ∉ S := by
    intro htS
    apply hxOpen.2
    apply subset_closure
    apply interior_maximal subset_closure
    · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun q ↦
        (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
          K.openCarrier_regularOpen.1
    rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨(t : Tiling.Plane), htS⟩, hxt⟩
  have hxSupport : x ∈ (t : Tiling.Plane) +ᵥ K.support := by
    rw [Region.openCarrier,
      Tiling.RationalPolygonal.PolygonalRegion.openCarrier] at hxt
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt ⊢
    exact interior_subset hxt
  exact hxOpen.1.1 (Set.mem_iUnion.2
    ⟨(⟨t.1, t.2, htNotS⟩ : R), hxSupport⟩)

theorem exposedHorizontalEdge_hasOppositeTile_relative
    {K : Region} {T S E : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hEopen : IsOpen E) (hST : S ⊆ T)
    {s : Tiling.Plane} (hs : s ∈ S) {a b : Tiling.Plane}
    (hab : a ≠ b) (hHorizontal : a.im = b.im)
    (hSegmentE : openSegment ℝ a b ⊆ E)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S))
    (hTileEdge : openSegment ℝ a b ⊆
      frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices)) :
    ∃ t ∈ T \ S, HorizontalProperContact K s t := by
  let P := K.polygonalProtoTiling T
  let fT : T → Set Tiling.Plane := fun t ↦ (t : Tiling.Plane) +ᵥ K.support
  let placementOf : T → P.placements := fun t ↦ ⟨((t : Tiling.Plane), ()), t.2⟩
  have hinj : Function.Injective placementOf := by
    intro u v h
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) h)
  have hlocalT : LocallyFinite fT := by
    have h := (P.locallyFinite_placedTile hTile.2.1).comp_injective hinj
    change LocallyFinite fT at h
    exact h
  let R := {t : Tiling.Plane // t ∈ T \ S}
  let toT : R → T := fun t ↦ ⟨t.1, t.2.1⟩
  have htoT : Function.Injective toT := fun u v h ↦
    Subtype.ext (congrArg (fun q : T ↦ (q : Tiling.Plane)) h)
  have hlocalR : LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) := by
    have h := hlocalT.comp_injective htoT
    change LocallyFinite (fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support) at h
    exact h
  have hcompact : IsCompact (segment ℝ a b) := by
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image (by fun_prop)
  let G : Finset R := (hlocalR.finite_nonempty_inter_compact hcompact).toFinset
  let F : Finset (Set Tiling.Plane) :=
    G.image fun t : R ↦ (t : Tiling.Plane) +ᵥ K.support
  have houtside := boundarySegment_coveredBy_outsideTileClosures_relative
    hTile hEopen hST hab hSegmentE hBoundary
  have hcover : openSegment ℝ a b ⊆ ⋃ C ∈ F, C := by
    intro x hx
    have hx' := houtside hx
    rw [Set.mem_iUnion] at hx'
    obtain ⟨t, hxt⟩ := hx'
    have hxt' : x ∈ (t : Tiling.Plane) +ᵥ K.support := by
      rw [closure_vadd, Region.openCarrier,
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
        K.isPolygonal.closure_interior] at hxt
      exact hxt
    have htG : t ∈ G := by
      change t ∈ (hlocalR.finite_nonempty_inter_compact hcompact).toFinset
      rw [Set.Finite.mem_toFinset]
      exact ⟨x, hxt', openSegment_subset_segment ℝ a b hx⟩
    rw [Set.mem_iUnion]
    refine ⟨(t : Tiling.Plane) +ᵥ K.support, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨Finset.mem_image.2 ⟨t, htG, rfl⟩, hxt'⟩
  have hclosed : ∀ C ∈ F, IsClosed C := by
    intro C hC
    obtain ⟨t : R, -, rfl⟩ := Finset.mem_image.1 hC
    exact (K.isPolygonal.vadd t.1).isClosed
  obtain ⟨C, hCF, c, d, hcd, hsub⟩ :=
    finiteClosedCover_contains_subsegment hab hclosed hcover
  obtain ⟨t : R, -, rfl⟩ := Finset.mem_image.1 hCF
  have hcdHorizontal : c.im = d.im := by
    have segment_im {z : Tiling.Plane} (hz : z ∈ segment ℝ a b) : z.im = a.im := by
      rw [segment_eq_image] at hz
      obtain ⟨q, -, rfl⟩ := hz
      simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
      rw [hHorizontal]
      ring
    have hc := hsub (midpoint_mem_openSegment (𝕜 := ℝ) c d) |>.1
    have hthird : AffineMap.lineMap c d (1 / 3 : ℝ) ∈ openSegment ℝ c d :=
      lineMap_mem_openSegment (𝕜 := ℝ) c d (by norm_num)
    have hd := hsub hthird |>.1
    have hcim := segment_im (openSegment_subset_segment ℝ a b hc)
    have hdim := segment_im (openSegment_subset_segment ℝ a b hd)
    norm_num [midpoint, AffineMap.lineMap_apply] at hcim hdim
    linarith
  have hst : s ≠ (t : Tiling.Plane) := by
    intro heq
    exact t.2.2 (heq ▸ hs)
  have hpackingPair : volume
      ((s +ᵥ K.support) ∩ ((t : Tiling.Plane) +ᵥ K.support)) = 0 := by
    have hp := hTile.2.1
      (show ((s, ()) : Tiling.Placement Tiling.Plane Unit) ∈
        K.toPolygonalRegion.placements T by exact hST hs)
      (show (((t : Tiling.Plane), ()) : Tiling.Placement Tiling.Plane Unit) ∈
        K.toPolygonalRegion.placements T by exact t.2.1)
      (by intro h; exact hst (congrArg Prod.fst h))
    exact hp
  refine ⟨t, t.2, horizontalEdge_closureOverlap_gives_properContact
    hcd hcdHorizontal hpackingPair ?_ ?_⟩
  · exact hsub.trans (inter_subset_left.trans hTileEdge)
  · exact hsub.trans inter_subset_right

private theorem relativePlate_support_isVerticalSlab
    {K : Region} {T E : Set Tiling.Plane} {X₀ : Set ℝ}
    (hTile : TilesOn K T E) (hE : E = Complex.re ⁻¹' X₀)
    (hX₀regular : X₀ = interior (closure X₀))
    (hX₀boundary : ∀ a b : ℝ, (frontier X₀ ∩ Set.Icc a b).Finite)
    (P : VerticalPlate K T) :
    P.base = interior (closure P.base) ∧
      P.support = Complex.re ⁻¹' P.base := by
  have hXopen : IsOpen X₀ := by rw [hX₀regular]; exact isOpen_interior
  have hEopen : IsOpen E := hE.symm ▸ hXopen.preimage Complex.continuous_re
  have hEregular : interior (closure E) = E := by
    rw [hE, Complex.closure_preimage_re, Complex.interior_preimage_re,
      ← hX₀regular]
  have hsupportT : regularSupport K T = E :=
    Tiling.AxisParallel.regularSupport_eq_of_tilesOn hEopen hEregular hTile
  have hcentres : P.centres ⊆ T := by
    rintro s ⟨q, -, rfl⟩
    exact q.2
  have hpackingP : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    exact fun s hs t ht hst ↦
      (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hcentres hs) (hcentres ht) hst
  have hNoHorizontal : ∀ a b : Tiling.Plane,
      a ≠ b → a.im = b.im →
        ¬ openSegment ℝ a b ⊆ frontier P.support := by
    intro a b hab hh hseg
    obtain ⟨s, hsP, c, d, hcd, hcdhor, hcdsub, hTileEdge⟩ :=
      horizontalSupportBoundary_containsTileEdge hTile hcentres hab hh hseg
    let F : Set ℝ := frontier X₀ ∩ Set.Icc (min c.re d.re) (max c.re d.re)
    let V : Set Tiling.Plane :=
      (fun y : ℝ ↦ (y : ℂ) + c.im * Complex.I) '' F
    have hVfinite : V.Finite :=
      (hX₀boundary (min c.re d.re) (max c.re d.re)).image _
    obtain ⟨c', d', hcd', hcd'hor, hcd'avoid⟩ :=
      exists_subsegment_avoiding_finite hcd hcdhor hVfinite
    have hcd'sub : openSegment ℝ c' d' ⊆ openSegment ℝ c d :=
      hcd'avoid.trans inter_subset_left
    have hsegmentE : openSegment ℝ c' d' ⊆ E := by
      intro z hz
      have hzcd := hcd'sub hz
      have hzsupport : z ∈ s +ᵥ K.support := by
        have := frontier_subset_closure (hTileEdge hzcd).1
        simpa only [(K.isPolygonal.vadd s).isClosed.closure_eq] using this
      have hzclosure : z ∈ closure E := by
        have hopenTile : s +ᵥ K.openCarrier ⊆ regularSupport K T := by
          intro w hw
          apply interior_maximal subset_closure
          · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
            exact isOpen_iUnion fun q ↦
              (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
                K.openCarrier_regularOpen.1
          rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
          exact ⟨⟨s, hcentres hsP⟩, hw⟩
        have hzreg : z ∈ closure (regularSupport K T) := by
          rw [← K.isPolygonal.closure_interior, ← closure_vadd] at hzsupport
          exact closure_mono hopenTile hzsupport
        simpa only [hsupportT] using hzreg
      have hzim : z.im = c.im := by
        have hzseg := openSegment_subset_segment ℝ c d hzcd
        rw [segment_eq_image] at hzseg
        obtain ⟨q, -, rfl⟩ := hzseg
        simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
        rw [hcdhor]
        ring
      have hzreSegment : z.re ∈ segment ℝ c.re d.re := by
        have hzseg := openSegment_subset_segment ℝ c d hzcd
        rw [segment_eq_image] at hzseg ⊢
        obtain ⟨q, hq, rfl⟩ := hzseg
        refine ⟨q, hq, ?_⟩
        simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
      have hzIcc : z.re ∈ Set.Icc (min c.re d.re) (max c.re d.re) := by
        rw [segment_eq_uIcc, Set.mem_uIcc] at hzreSegment
        rcases hzreSegment with hzre | hzre
        · exact ⟨(min_le_left _ _).trans hzre.1,
            hzre.2.trans (le_max_right _ _)⟩
        · exact ⟨(min_le_right _ _).trans hzre.1,
            hzre.2.trans (le_max_left _ _)⟩
      have hznotfront : z.re ∉ frontier X₀ := by
        intro hzfront
        apply (hcd'avoid hz).2
        refine ⟨z.re, ⟨hzfront, hzIcc⟩, ?_⟩
        apply Complex.ext <;> simp [hzim]
      have hzclX : z.re ∈ closure X₀ := by
        rw [hE, Complex.closure_preimage_re] at hzclosure
        exact hzclosure
      have hzintX : z.re ∈ interior X₀ := by
        rw [frontier] at hznotfront
        exact Classical.byContradiction fun hznotint ↦ hznotfront ⟨hzclX, hznotint⟩
      rw [hE]
      change z.re ∈ X₀
      exact interior_subset hzintX
    obtain ⟨t, htOutside, hcontact⟩ :=
      exposedHorizontalEdge_hasOppositeTile_relative hTile hEopen hcentres hsP
        hcd' hcd'hor hsegmentE (hcd'sub.trans (hcdsub.trans hseg))
        (hcd'sub.trans hTileEdge)
    obtain ⟨sT, hsSupp, hsEq⟩ := hsP
    subst s
    let tT : T := ⟨t, htOutside.1⟩
    have hadj : (verticalPlateGraph K T).Adj sT tT := by
      rw [verticalPlateGraph, SimpleGraph.fromRel_adj]
      refine ⟨?_, Or.inl hcontact⟩
      intro heq
      apply htOutside.2
      have hval : (sT : Tiling.Plane) = (tT : Tiling.Plane) :=
        congrArg Subtype.val heq
      change (sT : Tiling.Plane) = t at hval
      exact hval ▸ (show (sT : Tiling.Plane) ∈ P.centres from ⟨sT, hsSupp, rfl⟩)
    have hmkS : (verticalPlateGraph K T).connectedComponentMk sT = P :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P sT).1 hsSupp
    have hmkEq :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have htSupp : tT ∈ P.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P tT).2 (hmkEq.symm.trans hmkS)
    exact htOutside.2 ⟨tT, htSupp, rfl⟩
  have hregular : P.support = interior (closure P.support) := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_closure_idem.symm
  have hcross : ∀ z ∈ frontier P.support, ∃ r : ℝ, 0 < r ∧
      ∀ w ∈ Metric.ball z r, w ∈ frontier P.support →
        w.re = z.re ∨ w.im = z.im := by
    intro z _
    exact Tiling.AxisParallel.regularSupport_localBoundaryCross hpackingP z
  have hgerm : ∀ z ∈ frontier P.support, ∃ r : ℝ, 0 < r ∧
      {w : Tiling.Plane | w.re = z.re ∧ dist w z < r} ⊆ frontier P.support := by
    intro z hz
    exact localBoundaryCross_noHorizontal_verticalGerm
      hregular hcross hNoHorizontal hz
  have hvertical : ∀ z ∈ frontier P.support,
      {w : Tiling.Plane | w.re = z.re} ⊆ frontier P.support := by
    intro z hz
    exact verticalGerms_extend_to_lines hgerm hz
  obtain ⟨X, hXregular, hsupport⟩ :=
    regularOpen_of_vertical_frontier_is_cylinder hregular hvertical
  have hbase : P.base = X := by
    ext x
    constructor
    · rintro ⟨z, hzP, rfl⟩
      exact (show z ∈ Complex.re ⁻¹' X by simpa only [← hsupport] using hzP)
    · intro hx
      refine ⟨(x : ℂ), ?_, by simp⟩
      rw [hsupport]
      exact hx
  constructor
  · rw [hbase]
    exact hXregular
  · rw [hbase]
    exact hsupport

private theorem minimal_relative
    {K : Region} {T E : Set Tiling.Plane} {X₀ : Set ℝ}
    (hTile : TilesOn K T E) (hE : E = Complex.re ⁻¹' X₀)
    (hX₀regular : X₀ = interior (closure X₀))
    (hPlateSlab : ∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base)
    (P : VerticalPlate K T) :
    IsMinimalVerticalSlabSubfamily K T P.centres := by
  have hPnonempty : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  have hPsub : P.centres ⊆ T := by
    rintro p ⟨q, -, rfl⟩
    exact q.2
  obtain ⟨hPreg, hPsupport⟩ := hPlateSlab P
  refine ⟨hPnonempty, hPsub, ⟨P.base, hPreg, hPsupport⟩, ?_⟩
  intro Q hQnonempty hQP hQslab
  obtain ⟨XQ, hXQreg, hQsupport⟩ := hQslab
  have hEopen : IsOpen E := by
    rw [hE, hX₀regular]
    exact isOpen_interior.preimage Complex.continuous_re
  have hEregular : interior (closure E) = E := by
    rw [hE, Complex.closure_preimage_re, Complex.interior_preimage_re,
      ← hX₀regular]
  have hTsupport : regularSupport K T = Complex.re ⁻¹' X₀ := by
    rw [← hE]
    exact Tiling.AxisParallel.regularSupport_eq_of_tilesOn hEopen hEregular hTile
  obtain ⟨XB, hXBreg, hBsupport⟩ := verticalSlab_sdiff
    hTile (Subset.refl T) (hQP.trans hPsub)
      ⟨X₀, hX₀regular, hTsupport⟩ ⟨XQ, hXQreg, hQsupport⟩
  let parts : Bool → Set Tiling.Plane
    | false => Q
    | true => T \ Q
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.2 fun _ hxQ hxB ↦ hxB.2 hxQ
    · exact Set.disjoint_left.2 fun _ hxB hxQ ↦ hxB.2 hxQ
    · exact (hij rfl).elim
  have hunion : (⋃ i, parts i) = T := by
    ext x
    constructor
    · simp only [Set.mem_iUnion]
      rintro ⟨i, hi⟩
      cases i
      · exact (hQP.trans hPsub) hi
      · exact hi.1
    · intro hxT
      by_cases hxQ : x ∈ Q
      · exact Set.mem_iUnion.2 ⟨false, hxQ⟩
      · exact Set.mem_iUnion.2 ⟨true, hxT, hxQ⟩
  have hdisj := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
    parts hparts hunion hTile).1
  have hQBdisj : Disjoint (regularSupport K Q) (regularSupport K (T \ Q)) := by
    have h := hdisj (Set.mem_univ false) (Set.mem_univ true) (by decide)
    change Disjoint (regularSupport K Q) (regularSupport K (T \ Q)) at h
    exact h
  have hsat := verticalPlates_saturated_of_slabPartition K
    (show Q ∪ (T \ Q) = T by
      ext x
      constructor
      · rintro (hxQ | hxB)
        · exact (hQP.trans hPsub) hxQ
        · exact hxB.1
      · intro hxT
        by_cases hxQ : x ∈ Q
        · exact Or.inl hxQ
        · exact Or.inr ⟨hxT, hxQ⟩)
    hQBdisj hXQreg.symm hXBreg.symm hQsupport hBsupport
  have hmeet : (P.centres ∩ Q).Nonempty := by
    obtain ⟨q, hqQ⟩ := hQnonempty
    exact ⟨q, hQP hqQ, hqQ⟩
  exact Set.Subset.antisymm hQP (hsat.1 P hmeet)


theorem verticalPlates_intrinsic_relative
    {K : Region} {T E : Set Tiling.Plane} {X₀ : Set ℝ}
    (hTile : TilesOn K T E) (hE : E = Complex.re ⁻¹' X₀)
    (hX₀regular : X₀ = interior (closure X₀))
    (hPlateSlab : ∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base) :
    Set.range (@VerticalPlate.centres K T) =
      {S : Set Tiling.Plane | IsMinimalVerticalSlabSubfamily K T S} := by
  ext S
  constructor
  · rintro ⟨P, rfl⟩
    exact minimal_relative hTile hE hX₀regular hPlateSlab P
  · intro hSminimal
    rw [Set.mem_ofPred_eq] at hSminimal
    obtain ⟨hSnonempty, hSsub, ⟨XS, hXSreg, hSsupport⟩, hSmin⟩ := hSminimal
    obtain ⟨s, hsS⟩ := hSnonempty
    let sT : T := ⟨s, hSsub hsS⟩
    let P : VerticalPlate K T := VerticalPlate.ofCentre sT
    have hEopen : IsOpen E := by
      rw [hE, hX₀regular]
      exact isOpen_interior.preimage Complex.continuous_re
    have hEregular : interior (closure E) = E := by
      rw [hE, Complex.closure_preimage_re, Complex.interior_preimage_re,
        ← hX₀regular]
    have hTsupport : regularSupport K T = Complex.re ⁻¹' X₀ := by
      rw [← hE]
      exact Tiling.AxisParallel.regularSupport_eq_of_tilesOn hEopen hEregular hTile
    obtain ⟨XB, hXBreg, hBsupport⟩ := verticalSlab_sdiff
      hTile (Subset.refl T) hSsub ⟨X₀, hX₀regular, hTsupport⟩
        ⟨XS, hXSreg, hSsupport⟩
    let parts : Bool → Set Tiling.Plane
      | false => S
      | true => T \ S
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact Set.disjoint_left.2 fun _ hxS hxB ↦ hxB.2 hxS
      · exact Set.disjoint_left.2 fun _ hxB hxS ↦ hxB.2 hxS
      · exact (hij rfl).elim
    have hunion : (⋃ i, parts i) = T := by
      ext x
      constructor
      · simp only [Set.mem_iUnion]
        rintro ⟨i, hi⟩
        cases i
        · exact hSsub hi
        · exact hi.1
      · intro hxT
        by_cases hxS : x ∈ S
        · exact Set.mem_iUnion.2 ⟨false, hxS⟩
        · exact Set.mem_iUnion.2 ⟨true, hxT, hxS⟩
    have hpair := (Tiling.AxisParallel.regularSupport_pairwiseDisjoint
      parts hparts hunion hTile).1
    have hdisj : Disjoint (regularSupport K S) (regularSupport K (T \ S)) := by
      have h := hpair (Set.mem_univ false) (Set.mem_univ true) (by decide)
      change Disjoint (regularSupport K S) (regularSupport K (T \ S)) at h
      exact h
    have hsat := verticalPlates_saturated_of_slabPartition K
      (show S ∪ (T \ S) = T by
        ext x
        constructor
        · rintro (hxS | hxB)
          · exact hSsub hxS
          · exact hxB.1
        · intro hxT
          by_cases hxS : x ∈ S
          · exact Or.inl hxS
          · exact Or.inr ⟨hxT, hxS⟩)
      hdisj hXSreg.symm hXBreg.symm hSsupport hBsupport
    have hsP : s ∈ P.centres := by
      refine ⟨sT, ?_, rfl⟩
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff P sT).2 rfl
    have hPsubS : P.centres ⊆ S := hsat.1 P ⟨s, hsP, hsS⟩
    have hPeq : P.centres = S := hSmin P.centres ⟨s, hsP⟩ hPsubS
      ⟨P.base, (hPlateSlab P).1, (hPlateSlab P).2⟩
    exact ⟨P, hPeq⟩

theorem verticalColumn_regularSupport_of_slab
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T)
    (hPslab : P.base = interior (closure P.base) ∧
      P.support = Complex.re ⁻¹' P.base)
    (_hPcolumn : IsVerticalColumn P) {x : ℝ}
    (hx : P.centres ⊆ {z : Tiling.Plane | z.re = x}) :
    P.base = interior (closure ((Complex.re '' K.openCarrier) + {x})) ∧
      P.support = Complex.re ⁻¹' P.base := by
  let A : Set ℝ := (Complex.re '' K.openCarrier) + {x}
  have hPnonempty : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  have hproj : Complex.re '' openUnion K P.centres = A := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hs
      refine ⟨(z - (s : Tiling.Plane)).re, ?_, x, Set.mem_singleton x, ?_⟩
      · refine ⟨z - (s : Tiling.Plane), ?_, rfl⟩
        simpa only [vadd_eq_add, neg_add_eq_sub] using hs
      · have hsx := hx s.2
        simp only [Set.mem_ofPred_eq] at hsx
        simp only [Complex.sub_re]
        linarith
    · rintro ⟨u, ⟨k, hk, rfl⟩, v, hv, rfl⟩
      rw [Set.mem_singleton_iff] at hv
      subst v
      obtain ⟨s, hsP⟩ := hPnonempty
      refine ⟨s + k, ?_, ?_⟩
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        refine ⟨⟨s, hsP⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa using hk
      · have hsx := hx hsP
        simp only [Set.mem_ofPred_eq] at hsx
        simp [hsx, add_comm]
  have hopenUnion : IsOpen (openUnion K P.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
        K.openCarrier_regularOpen.1
  have hrawSupport : openUnion K P.centres ⊆ P.support := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_maximal subset_closure hopenUnion
  have hsupportClosure : P.support ⊆ closure (openUnion K P.centres) := by
    dsimp only [VerticalPlate.support, regularSupport]
    exact interior_subset
  have hA_base : A ⊆ P.base := by
    rw [← hproj]
    exact Set.image_mono hrawSupport
  have hbase_closureA : P.base ⊆ closure A := by
    rintro y ⟨z, hzP, rfl⟩
    have hzcl := hsupportClosure hzP
    have hmap : Set.MapsTo Complex.re (openUnion K P.centres) A := by
      intro w hw
      rw [← hproj]
      exact ⟨w, hw, rfl⟩
    exact hmap.closure Complex.continuous_re hzcl
  have hbaseOpen : IsOpen P.base := by
    rw [hPslab.1]
    exact isOpen_interior
  have hbaseEq : P.base = interior (closure A) := by
    apply Set.Subset.antisymm
    · exact interior_maximal hbase_closureA hbaseOpen
    · rw [hPslab.1]
      exact interior_mono (closure_mono hA_base)
  exact ⟨hbaseEq, hPslab.2⟩

theorem relativeCarrier_verticalPlates
    {K : Region} {T E : Set Tiling.Plane} {X₀ : Set ℝ}
    (hTile : TilesOn K T E) (hE : E = Complex.re ⁻¹' X₀)
    (hX₀regular : X₀ = interior (closure X₀))
    (hX₀boundary : ∀ a b : ℝ,
      (frontier X₀ ∩ Set.Icc a b).Finite) :
    (∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base) ∧
    (∀ P : VerticalPlate K T,
      IsMinimalVerticalSlabSubfamily K T P.centres) ∧
    Set.range (@VerticalPlate.centres K T) =
      {S : Set Tiling.Plane | IsMinimalVerticalSlabSubfamily K T S} ∧
    ∀ P : VerticalPlate K T, IsVerticalColumn P → ∀ x : ℝ,
      P.centres ⊆ {z : Tiling.Plane | z.re = x} →
      P.base = interior (closure ((Complex.re '' K.openCarrier) + {x})) ∧
        P.support = Complex.re ⁻¹' P.base := by
  have hslab : ∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base := fun P ↦
    relativePlate_support_isVerticalSlab hTile hE hX₀regular hX₀boundary P
  refine ⟨hslab, fun P ↦ minimal_relative hTile hE hX₀regular hslab P,
    verticalPlates_intrinsic_relative hTile hE hX₀regular hslab, ?_⟩
  intro P hPcolumn x hx
  exact verticalColumn_regularSupport_of_slab P (hslab P) hPcolumn hx

theorem tilesOn_shiftVerticalPlates
    {K : Region} {T E : Set Tiling.Plane} {X₀ : Set ℝ}
    (hTile : TilesOn K T E) (hE : E = Complex.re ⁻¹' X₀)
    (hX₀regular : X₀ = interior (closure X₀))
    (hX₀boundary : ∀ a b : ℝ,
      (frontier X₀ ∩ Set.Icc a b).Finite)
    (shift : VerticalPlate K T → ℝ) :
    TilesOn K (shiftVerticalPlates K T shift) E := by
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨p, hp⟩ := P.nonempty_supp
    refine ⟨p, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp
  have hslab := (relativeCarrier_verticalPlates
    hTile hE hX₀regular hX₀boundary).1
  have hcentres (P : VerticalPlate K T) : P.centres ⊆ T := by
    rintro s ⟨q, -, rfl⟩
    exact q.2
  have hplateTile (P : VerticalPlate K T) : TilesOn K P.centres P.support := by
    have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements P.centres) := by
      apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
        K P.centres).mpr
      exact fun s hs t ht hst ↦
        (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
          (hcentres P hs) (hcentres P ht) hst
    refine ⟨hTile.1.mono (hcentres P), hpacking, ?_⟩
    have hae := Tiling.AxisParallel.openUnion_aeEq_regularSupport hpacking
    filter_upwards [hae] with x hx
    have hunion : (∃ s : P.centres,
        x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) ↔
        x ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    change x ∈ P.support ↔ ∃ s : P.centres, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier
    rw [hunion]
    exact iff_of_eq hx.symm
  let gamma (P : VerticalPlate K T) : Tiling.Plane :=
    ((shift P : ℝ) : ℂ) * Complex.I
  have hsupportInv (P : VerticalPlate K T) : gamma P +ᵥ P.support = P.support := by
    rw [(hslab P).2]
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage,
      vadd_eq_add, gamma]
    simp
  have hshiftTile (P : VerticalPlate K T) :
      TilesOn K (gamma P +ᵥ P.centres) P.support := by
    have h := Tiling.AxisParallel.tilesOn_translate (hplateTile P) (gamma P)
    rwa [hsupportInv] at h
  have hpartition := Tiling.AxisParallel.regularSupport_pairwiseDisjoint
    (@VerticalPlate.centres K T)
      (verticalPlateCentres_pairwiseDisjoint K T)
      (iUnion_verticalPlateCentres K T) hTile
  have hsupportDisjoint := hpartition.1
  have htileSubset (P : VerticalPlate K T) (s : Tiling.Plane)
      (hs : s ∈ gamma P +ᵥ P.centres) :
      s +ᵥ K.openCarrier ⊆ P.support := by
    have hreg : regularSupport K (gamma P +ᵥ P.centres) = P.support := by
      have hPopen : IsOpen P.support := by
        rw [(hslab P).2]
        have hbaseOpen : IsOpen P.base := by
          rw [(hslab P).1]
          exact isOpen_interior
        exact hbaseOpen.preimage Complex.continuous_re
      have hPreg : interior (closure P.support) = P.support := by
        rw [(hslab P).2, Complex.closure_preimage_re,
          Complex.interior_preimage_re, ← (hslab P).1]
      exact Tiling.AxisParallel.regularSupport_eq_of_tilesOn
        hPopen hPreg (hshiftTile P)
    intro x hx
    rw [← hreg]
    apply interior_maximal subset_closure
    · rw [Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun q ↦
        (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _
          K.openCarrier_regularOpen.1
    rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s, hs⟩, hx⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [shiftVerticalPlates_eq]
    exact Set.countable_iUnion fun P ↦ (hshiftTile P).1
  · apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
      K (shiftVerticalPlates K T shift)).mpr
    intro s hs t ht hst
    rw [shiftVerticalPlates_eq, Set.mem_iUnion] at hs ht
    obtain ⟨P, hsP⟩ := hs
    obtain ⟨Q, htQ⟩ := ht
    by_cases hPQ : P = Q
    · subst Q
      exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint
        K (gamma P +ᵥ P.centres)).mp (hshiftTile P).2.1 hsP htQ hst
    · apply Set.disjoint_left.2
      intro x hxs hxt
      have hxP := htileSubset P s hsP hxs
      have hxQ := htileSubset Q t htQ hxt
      exact Set.disjoint_left.1
        (hsupportDisjoint (Set.mem_univ P) (Set.mem_univ Q) hPQ) hxP hxQ
  · have hraw (P : VerticalPlate K T) :
        openUnion K (gamma P +ᵥ P.centres) =ᵐ[volume] P.support :=
      Tiling.AxisParallel.openUnion_aeEq_regularSupport (hshiftTile P).2.1 |>.trans
        (Filter.Eventually.of_forall fun x ↦ by
          have hPopen : IsOpen P.support := by
            rw [(hslab P).2]
            have hbaseOpen : IsOpen P.base := by
              rw [(hslab P).1]
              exact isOpen_interior
            exact hbaseOpen.preimage Complex.continuous_re
          have hPreg : interior (closure P.support) = P.support := by
            rw [(hslab P).2, Complex.closure_preimage_re,
              Complex.interior_preimage_re, ← (hslab P).1]
          exact congrFun (Tiling.AxisParallel.regularSupport_eq_of_tilesOn
            hPopen hPreg (hshiftTile P)) x)
    have hrawUnion : (⋃ P : VerticalPlate K T,
        openUnion K (gamma P +ᵥ P.centres)) =ᵐ[volume]
        ⋃ P : VerticalPlate K T, P.support :=
      Filter.EventuallyEq.countable_iUnion hraw
    have hopenEq : openUnion K (shiftVerticalPlates K T shift) =
        ⋃ P : VerticalPlate K T, openUnion K (gamma P +ᵥ P.centres) := by
      ext x
      constructor
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        rintro ⟨s, hxs⟩
        have hsunion := s.2
        change s.1 ∈ ⋃ P : VerticalPlate K T, gamma P +ᵥ P.centres at hsunion
        rw [Set.mem_iUnion] at hsunion
        obtain ⟨P, hsP⟩ := hsunion
        rw [Set.mem_iUnion]
        exact ⟨P, Set.mem_iUnion.2 ⟨⟨s.1, hsP⟩, hxs⟩⟩
      · rw [Set.mem_iUnion]
        rintro ⟨P, hxP⟩
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hxP
        obtain ⟨s, hxs⟩ := hxP
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        refine ⟨⟨s.1, ?_⟩, hxs⟩
        change s.1 ∈ ⋃ P : VerticalPlate K T, gamma P +ᵥ P.centres
        rw [Set.mem_iUnion]
        exact ⟨P, s.2⟩
    filter_upwards [hrawUnion, hpartition.2] with x hxraw hxcover
    have hxcover' : (x ∈ ⋃ P : VerticalPlate K T, P.support) = (x ∈ E) := by
      change ((⋃ P : VerticalPlate K T, P.support) x) = E x
      simpa only [VerticalPlate.support_eq_regularSupport] using hxcover
    have hgoal : (x ∈ E ↔ x ∈ openUnion K (shiftVerticalPlates K T shift)) := by
      rw [hopenEq]
      exact iff_of_eq (hxcover'.symm.trans hxraw.symm)
    simpa only [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier.eq_def, Set.mem_iUnion] using hgoal

/-- A graph plate which is a column in the C01 sense is a complete centre column. -/
theorem VerticalPlate.isCenterColumn_of_isVerticalColumn
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T)
    (hcolumn : IsVerticalColumn P) :
    IsCenterColumn Axis.vertical K P.centres := by
  have hcentres : P.centres ⊆ T := by
    rintro s ⟨t, _ht, rfl⟩
    exact t.2
  have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K P.centres).mpr
    intro s hs t ht hst
    exact (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      (hcentres hs) (hcentres ht) hst
  have hnonempty : P.centres.Nonempty := by
    obtain ⟨p, hp⟩ := P.nonempty_supp
    exact ⟨p, p, hp, rfl⟩
  obtain ⟨c, hc⟩ := hcolumn
  obtain ⟨_hbase, hsupport⟩ := P.support_isVerticalSlab hTile
  refine ⟨hpacking, hnonempty, ⟨c, ?_⟩, ?_⟩
  · intro z hz
    exact hc hz
  · intro a
    rw [← P.support_eq_regularSupport, hsupport]
    ext z
    simp only [Set.mem_vadd_set, Set.mem_preimage]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hz
      refine ⟨z - (a : Tiling.Plane) * Complex.I, ?_, ?_⟩
      · simpa using hz
      · simp [vadd_eq_add]

theorem plate_centres_eq_of_support_eq_univ
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (P : VerticalPlate K T) (hfull : P.support = Set.univ) : P.centres = T := by
  have hsub : P.centres ⊆ T := by
    rintro _ ⟨t, _ht, rfl⟩
    exact t.2
  apply Set.Subset.antisymm hsub
  intro t htT
  by_contra htP
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have htuint : t + u ∈ interior (closure (openUnion K P.centres)) := by
    change t + u ∈ P.support
    rw [hfull]
    trivial
  have hopenTile : IsOpen (t +ᵥ K.openCarrier) := isOpen_interior.vadd t
  have hmeet : ((t +ᵥ K.openCarrier) ∩ openUnion K P.centres).Nonempty := by
    apply mem_closure_iff.mp (interior_subset htuint)
    · exact hopenTile
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      have hu' : u ∈ K.openCarrier := by
        rw [← K.openCarrier_regularOpen.2,
          show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
        exact hu
      simpa only [vadd_eq_add, neg_add_cancel_left] using hu'
  obtain ⟨q, hqtile, hqraw⟩ := hmeet
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hqraw
  obtain ⟨s, hqs⟩ := hqraw
  have hst : (s : Tiling.Plane) ≠ t := by
    intro heq
    exact htP (heq ▸ s.2)
  have hdis := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
    (hsub s.2) htT hst
  exact Set.disjoint_left.mp hdis hqs hqtile

/-- A complete vertical centre column in a plane tiling is exactly the vertical plate
through any one of its centres. -/
theorem completeColumn_eq_verticalPlateThrough
    {K : Region} {S L : Set Tiling.Plane}
    (hTile : TilesOn K S Set.univ)
    (hL : IsCenterColumn Axis.vertical K L)
    (hsub : L ⊆ S) {c : Tiling.Plane} (hc : c ∈ L) :
    ∃ P : VerticalPlate K S,
      IsVerticalColumn P ∧ c ∈ P.centres ∧ P.centres = L := by
  classical
  obtain ⟨a, _, halign, hsupport⟩ := centerColumn_regularSupport hL
  let X : Set ℝ := interior (closure (a +ᵥ (Complex.re '' K.openCarrier)))
  have hLs : regularSupport K L = Complex.re ⁻¹' X := by
    change regularSupport K L = {z : Tiling.Plane | z.re ∈ X}
    simpa [X, Axis.transverseCoord] using hsupport
  have hSs : regularSupport K S = Complex.re ⁻¹' (Set.univ : Set ℝ) := by
    rw [regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile]
    simp
  obtain ⟨Y, hY, hSY⟩ := verticalSlab_sdiff hTile (Subset.refl S) hsub
    ⟨univ, by simp, hSs⟩ ⟨X, by dsimp [X]; exact interior_closure_idem.symm, hLs⟩
  let parts : Bool → Set Tiling.Plane | true => L | false => S \ L
  have hparts : Set.PairwiseDisjoint Set.univ parts := by
    intro i _ j _ hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact Set.disjoint_left.mpr (fun _ hz hzL => hz.2 hzL)
    · exact Set.disjoint_left.mpr (fun _ hzL hz => hz.2 hzL)
    · exact (hij rfl).elim
  have hunion : (⋃ b, parts b) = S := by
    ext z
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨b, hb⟩
      cases b
      · exact hb.1
      · exact hsub hb
    · intro hz
      by_cases hzL : z ∈ L
      · exact ⟨true, hzL⟩
      · exact ⟨false, hz, hzL⟩
  have hpairs := regularSupport_pairwiseDisjoint parts hparts hunion hTile
  have hdis : Disjoint (regularSupport K L) (regularSupport K (S \ L)) := by
    have h := hpairs.1 (show true ∈ (Set.univ : Set Bool) by trivial)
      (show false ∈ (Set.univ : Set Bool) by trivial) (by decide)
    change Disjoint (regularSupport K (parts true))
      (regularSupport K (parts false)) at h
    simpa only [parts] using h
  have hUnion : L ∪ (S \ L) = S := by
    ext z
    simp only [Set.mem_union, Set.mem_sdiff]
    constructor
    · rintro (hz | hz)
      · exact hsub hz
      · exact hz.1
    · intro hz
      by_cases hzL : z ∈ L
      · exact Or.inl hzL
      · exact Or.inr ⟨hz, hzL⟩
  have hsat := (verticalPlates_saturated_of_slabPartition K hUnion hdis
    interior_closure_idem hY.symm hLs hSY).1
  let P : VerticalPlate K S := VerticalPlate.ofCentre ⟨c, hsub hc⟩
  have hcP : c ∈ P.centres := VerticalPlate.mem_centres_ofCentre ⟨c, hsub hc⟩
  have hPsub : P.centres ⊆ L := hsat P ⟨c, hcP, hc⟩
  have hcol (Q : VerticalPlate K S) (hQ : Q.centres ⊆ L) :
      IsVerticalColumn Q := by
    refine ⟨a, fun z hz => ?_⟩
    simpa [Axis.transverseCoord] using halign z (hQ hz)
  have heq (Q : VerticalPlate K S) (hQ : Q.centres ⊆ L) : Q = P := by
    have haxisQ : Q.centres ⊆ {z : Tiling.Plane | z.re = a} := by
      intro z hz
      simpa [Axis.transverseCoord] using halign z (hQ hz)
    have haxisP : P.centres ⊆ {z : Tiling.Plane | z.re = a} := by
      intro z hz
      simpa [Axis.transverseCoord] using halign z (hPsub hz)
    have hQs := verticalColumn_regularSupport hTile Q (hcol Q hQ) haxisQ
    have hPs := verticalColumn_regularSupport hTile P (hcol P hPsub) haxisP
    have hbase : Q.base = P.base := hQs.1.trans hPs.1.symm
    have hsupp : Q.support = P.support := by rw [hQs.2, hPs.2, hbase]
    by_contra hne
    let _ : Countable S := hTile.1.to_subtype
    let _ : Countable (VerticalPlate K S) := by
      apply Function.Surjective.countable
        (f := fun t : S => VerticalPlate.ofCentre (K := K) t)
      intro R
      obtain ⟨r, hr⟩ := R.nonempty_supp
      exact ⟨r, (SimpleGraph.ConnectedComponent.mem_supp_iff R r).mp hr⟩
    have hPair := regularSupport_pairwiseDisjoint (@VerticalPlate.centres K S)
      (verticalPlateCentres_pairwiseDisjoint K S) (iUnion_verticalPlateCentres K S) hTile
    have hQP := hPair.1 (show Q ∈ (univ : Set (VerticalPlate K S)) by simp)
      (show P ∈ (univ : Set (VerticalPlate K S)) by simp) hne
    change Disjoint Q.support P.support at hQP
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hzP : c + k ∈ P.support := by
      rw [P.support_eq_regularSupport, regularSupport]
      apply (isOpen_iUnion
        (fun q : P.centres => K.openCarrier_regularOpen.1.vadd q.1)).subset_interior_closure
      exact Set.mem_iUnion.mpr ⟨⟨c, hcP⟩, Set.mem_vadd_set.mpr ⟨k, hk, rfl⟩⟩
    have hzQ : c + k ∈ Q.support := hsupp.symm ▸ hzP
    exact Set.disjoint_left.mp hQP hzQ hzP
  refine ⟨P, hcol P hPsub, hcP, Set.Subset.antisymm hPsub ?_⟩
  intro x hx
  let Q : VerticalPlate K S := VerticalPlate.ofCentre ⟨x, hsub hx⟩
  have hxQ : x ∈ Q.centres := VerticalPlate.mem_centres_ofCentre ⟨x, hsub hx⟩
  have hQsub : Q.centres ⊆ L := hsat Q ⟨x, hxQ, hx⟩
  exact heq Q hQsub ▸ hxQ


end Tiling.AxisParallel.Continuous
