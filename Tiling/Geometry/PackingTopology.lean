import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.MetricSpace.Bounded
import Tiling.Geometry.LocalLine
import Tiling.Geometry.Plate
import Tiling.Geometry.PolygonalTopology

set_option linter.style.header false

/-!
# Topology forced by a finite polygonal packing

Interior balls give physical anchors for placed tiles.  Packing separates these anchors, while
bounded supports turn that separation into local finiteness.  This file then derives closed and
regular-closed carriers, exact coverage from almost-everywhere coverage, and the local boundary
property of a plate, including the proper-boundary vertex extraction from local planar geometry.
-/

open Filter MeasureTheory Set
open scoped Pointwise Topology

namespace Tiling

namespace PolygonalProtoTiling

universe u

variable {P : Type u} (A : PolygonalProtoTiling P)

private theorem finite_label_meets_ball
    (hpacking : IsPacking A.prototiles A.placements)
    (p : P) (c : Plane) {r R : ℝ} (hr : 0 < r)
    (hball : Metric.ball c r ⊆ (A.prototiles p).support)
    (hsupport : (A.prototiles p).support ⊆ Metric.closedBall c R)
    (x : Plane) :
    {i : A.placements | i.1.2 = p ∧
      (placedTile A.prototiles i.1 ∩ Metric.ball x 1).Nonempty}.Finite := by
  let H : Set A.placements :=
    {i | i.1.2 = p ∧ (placedTile A.prototiles i.1 ∩ Metric.ball x 1).Nonempty}
  let anchor : A.placements → Plane := fun i ↦ i.1.1 + c
  have ball_subset_placed (i : A.placements) (hi : i ∈ H) :
      Metric.ball (anchor i) r ⊆ placedTile A.prototiles i.1 := by
    intro z hz
    rw [placedTile, mem_vadd_set_iff_neg_vadd_mem]
    apply hi.1.symm ▸ hball
    simpa [anchor, dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hz
  have placed_subset_closedBall (i : A.placements) (hi : i ∈ H) :
      placedTile A.prototiles i.1 ⊆ Metric.closedBall (anchor i) R := by
    intro z hz
    rw [placedTile, mem_vadd_set_iff_neg_vadd_mem] at hz
    rw [hi.1] at hz
    have hz' := hsupport hz
    simpa [anchor, dist_eq_norm_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hz'
  have anchor_dist {i j : A.placements} (hi : i ∈ H) (hj : j ∈ H) (hij : i ≠ j) :
      r + r ≤ dist (anchor i) (anchor j) := by
    apply (disjoint_ball_ball_iff hr hr).mp
    by_contra hdisj
    have hnonempty :
        (Metric.ball (anchor i) r ∩ Metric.ball (anchor j) r).Nonempty :=
      Set.not_disjoint_iff.mp hdisj
    have hne : volume (Metric.ball (anchor i) r ∩ Metric.ball (anchor j) r) ≠ 0 :=
      (Metric.isOpen_ball.inter Metric.isOpen_ball).measure_ne_zero volume hnonempty
    exact hne ((hpacking i.2 j.2 (fun h ↦ hij (Subtype.ext h))).mono
      (ball_subset_placed i hi) (ball_subset_placed j hj))
  have hsep : (anchor '' H).Pairwise fun a b ↦ r + r ≤ dist a b := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩ hne
    exact anchor_dist hi hj (fun hij ↦ hne (congrArg anchor hij))
  have hclosed : IsClosed (anchor '' H) :=
    Metric.isClosed_of_pairwise_le_dist (add_pos hr hr) hsep
  have hdiscrete : IsDiscrete (anchor '' H) := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro a ha
    refine ⟨Metric.ball a r, Metric.isOpen_ball, ?_⟩
    ext b
    constructor
    · rintro ⟨hba, hb⟩
      by_cases hab : b = a
      · simp [hab]
      · have hd := hsep hb ha hab
        simp only [Metric.mem_ball] at hba
        rw [dist_comm] at hba
        change r + r ≤ dist b a at hd
        rw [dist_comm b a] at hd
        exfalso
        linarith
    · rintro rfl
      exact ⟨Metric.mem_ball_self hr, ha⟩
  have himage_bounded : Bornology.IsBounded (anchor '' H) := by
    apply (Metric.isBounded_closedBall (x := x) (r := R + 1)).subset
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨y, hyplaced, hyball⟩ := hi.2
    have hyclosed := placed_subset_closedBall i hi hyplaced
    rw [Metric.mem_closedBall] at hyclosed ⊢
    rw [Metric.mem_ball] at hyball
    calc
      dist (anchor i) x ≤ dist (anchor i) y + dist y x := dist_triangle _ _ _
      _ ≤ R + 1 := add_le_add (by simpa [dist_comm] using hyclosed) hyball.le
  have himage_finite : (anchor '' H).Finite :=
    (Metric.isCompact_of_isClosed_isBounded hclosed himage_bounded).finite hdiscrete
  have hinj : Set.InjOn anchor H := by
    intro i hi j hj hij
    by_contra hne
    have hd := anchor_dist hi hj hne
    rw [hij, dist_self] at hd
    linarith
  exact himage_finite.of_finite_image hinj

private theorem locallyFinite_placedTile_of_uniform_geometry [Finite P]
    (hpacking : IsPacking A.prototiles A.placements)
    (center : P → Plane) (radius bound : P → ℝ)
    (hradius : ∀ p, 0 < radius p)
    (hball : ∀ p, Metric.ball (center p) (radius p) ⊆ (A.prototiles p).support)
    (hsupport : ∀ p, (A.prototiles p).support ⊆
      Metric.closedBall (center p) (bound p)) :
    LocallyFinite fun i : A.placements ↦ placedTile A.prototiles i.1 := by
  intro x
  refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x one_pos, ?_⟩
  let S : P → Set A.placements := fun p ↦
    {i | i.1.2 = p ∧ (placedTile A.prototiles i.1 ∩ Metric.ball x 1).Nonempty}
  have hS (p : P) : (S p).Finite := by
    apply finite_label_meets_ball A hpacking p (center p) (hradius p)
      (hball p) (hsupport p) x
  apply (Set.finite_iUnion hS).subset
  intro i hi
  rw [Set.mem_iUnion]
  exact ⟨i.1.2, rfl, hi⟩

/-- Placed supports in a packing by a finite polygonal family form a locally finite family. -/
theorem locallyFinite_placedTile [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) :
    LocallyFinite fun i : A.placements ↦ placedTile A.prototiles i.1 := by
  have hinterior : ∀ p, (interior (A.prototiles p).support).Nonempty := fun p ↦
    (A.isPolygonal p).interior_nonempty (A.prototiles p).nonempty_support
  choose center hcenter using hinterior
  have hnhds (p : P) : (A.prototiles p).support ∈ 𝓝 (center p) :=
    mem_interior_iff_mem_nhds.mp (hcenter p)
  choose radius hradius hball using fun p ↦ Metric.mem_nhds_iff.mp (hnhds p)
  choose bound hbound using fun p ↦ (A.isPolygonal p).isBounded.subset_closedBall (center p)
  exact A.locallyFinite_placedTile_of_uniform_geometry hpacking center radius bound
    hradius hball hbound

/-- Every placed polygonal support is closed. -/
theorem isClosed_placedTile (i : Placement Plane P) :
    IsClosed (placedTile A.prototiles i) := by
  rw [placedTile]
  simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] using
    ((Homeomorph.addLeft i.1).isClosed_image.mpr (A.isPolygonal i.2).isClosed)

/-- Every placed polygonal support is the closure of its interior. -/
theorem closure_interior_placedTile (i : Placement Plane P) :
    closure (interior (placedTile A.prototiles i)) = placedTile A.prototiles i := by
  rw [placedTile, interior_vadd, closure_vadd, (A.isPolygonal i.2).closure_interior]

/-- The interiors of two distinct placed supports in a packing are disjoint. -/
theorem interior_placedTile_disjoint
    (hpacking : IsPacking A.prototiles A.placements)
    {i j : A.placements} (hij : i ≠ j) :
    Disjoint (interior (placedTile A.prototiles i.1))
      (interior (placedTile A.prototiles j.1)) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  have hne :
      volume (interior (placedTile A.prototiles i.1) ∩
        interior (placedTile A.prototiles j.1)) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero volume ⟨x, hxi, hxj⟩
  exact hne (measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset)
    (hpacking i.2 j.2 fun h ↦ hij (Subtype.ext h)))

/-- The carrier of any placement subfamily is closed. -/
theorem placementCarrier_isClosed [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) (S : Set A.placements) :
    IsClosed (A.placementCarrier S) := by
  rw [placementCarrier]
  exact ((A.locallyFinite_placedTile hpacking).comp_injective
    Subtype.val_injective).isClosed_iUnion fun i ↦ A.isClosed_placedTile i.1.1

/-- The carrier of any placement subfamily is the closure of its interior. -/
theorem placementCarrier_closure_interior [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) (S : Set A.placements) :
    closure (interior (A.placementCarrier S)) = A.placementCarrier S := by
  rw [placementCarrier]
  exact ((A.locallyFinite_placedTile hpacking).comp_injective
    Subtype.val_injective).closure_interior_iUnion_eq fun i ↦
      A.closure_interior_placedTile i.1.1

/-- An almost-everywhere polygonal tiling covers the plane exactly by its closed supports. -/
theorem iUnion_placedTile_eq_univ [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    (⋃ i : A.placements, placedTile A.prototiles i.1) = Set.univ := by
  let U : Set Plane := ⋃ i : A.placements, placedTile A.prototiles i.1
  have hclosed : IsClosed U :=
    (A.locallyFinite_placedTile hA.isPacking).isClosed_iUnion fun i ↦
      A.isClosed_placedTile i.1
  have hcover : ∀ᵐ x, x ∈ U := by
    filter_upwards [hA.isCover] with x hx
    exact hx
  apply (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp
  filter_upwards [hcover] with x hx
  change (x ∈ U) = (x ∈ (Set.univ : Set Plane))
  simp [hx]

/-- Plate carriers themselves form a locally finite family. -/
theorem locallyFinite_plateCarrier [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) :
    LocallyFinite fun C : A.Plate ↦ A.plateCarrier C := by
  intro x
  obtain ⟨t, htx, ht⟩ := A.locallyFinite_placedTile hpacking x
  refine ⟨t, htx, (ht.image fun i ↦ A.vertexGraph.connectedComponentMk i).subset ?_⟩
  intro C hC
  obtain ⟨y, hyC, hyt⟩ := hC
  obtain ⟨i, hiC, hyi⟩ := A.mem_plateCarrier_iff.mp hyC
  exact ⟨i, ⟨y, hyi, hyt⟩, hiC⟩

/-- Every plate carrier is closed in a finite-family packing. -/
theorem plateCarrier_isClosed [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) (C : A.Plate) :
    IsClosed (A.plateCarrier C) :=
  A.placementCarrier_isClosed hpacking C

/-- Every plate carrier is the closure of its interior in a finite-family packing. -/
theorem plateCarrier_closure_interior [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) (C : A.Plate) :
    closure (interior (A.plateCarrier C)) = A.plateCarrier C :=
  A.placementCarrier_closure_interior hpacking C

/-- Plate carriers cover the plane exactly. -/
theorem iUnion_plateCarrier_eq_univ [Finite P]
    (hA : IsTiling A.prototiles A.placements) :
    (⋃ C : A.Plate, A.plateCarrier C) = Set.univ := by
  rw [← A.iUnion_placedTile_eq_univ hA]
  apply Set.Subset.antisymm
  · intro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨C, hxC⟩ := hx
    obtain ⟨i, _, hxi⟩ := A.mem_plateCarrier_iff.mp hxC
    exact ⟨i, hxi⟩
  · intro x hx
    rw [Set.mem_iUnion] at hx ⊢
    obtain ⟨i, hxi⟩ := hx
    exact ⟨A.vertexGraph.connectedComponentMk i,
      A.placedTile_subset_plateCarrier i hxi⟩

/-- Carriers of disjoint placement subfamilies are almost-everywhere disjoint. -/
theorem placementCarrier_aedisjoint (hA : IsTiling A.prototiles A.placements)
    {S R : Set A.placements} (hSR : Disjoint S R) :
    AEDisjoint volume (A.placementCarrier S) (A.placementCarrier R) := by
  let _ : Countable A.placements := hA.countable.to_subtype
  rw [placementCarrier, AEDisjoint.iUnion_left_iff]
  intro i
  rw [placementCarrier, AEDisjoint.iUnion_right_iff]
  intro j
  apply hA.isPacking i.1.2 j.1.2
  intro hij
  apply Set.disjoint_left.1 hSR i.2
  have hsub : (i.1 : A.placements) = j.1 := Subtype.ext hij
  simpa only [hsub] using j.2

/-- Carriers of different plates are almost-everywhere disjoint. -/
theorem plateCarrier_aedisjoint (hA : IsTiling A.prototiles A.placements)
    {C D : A.Plate} (hCD : C ≠ D) :
    AEDisjoint volume (A.plateCarrier C) (A.plateCarrier D) := by
  apply A.placementCarrier_aedisjoint hA
  rw [Set.disjoint_left]
  intro i hiC hiD
  exact hCD (hiC.symm.trans hiD)

private theorem disjoint_regular_left_interior_of_aedisjoint
    {s t : Set Plane} (hregular : closure (interior s) = s)
    (had : AEDisjoint volume s t) : Disjoint s (interior t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  rw [← hregular] at hxs
  obtain ⟨y, hyt, hys⟩ := mem_closure_iff.mp hxs (interior t) isOpen_interior hxt
  have hne : volume (interior s ∩ interior t) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero volume ⟨y, hys, hyt⟩
  exact hne (measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset) had)

private theorem exists_small_lineMap (x z : Plane) {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    ∃ δ : ℝ, 0 < δ ∧
      (AffineMap.lineMap x z) δ ∈ Metric.ball x r ∩ Metric.ball x q ∧
      (AffineMap.lineMap x z) (-δ) ∈ Metric.ball x r ∩ Metric.ball x q := by
  let ρ := min r q
  have hρ : 0 < ρ := lt_min hr hq
  let n := ‖z - x‖
  have hn : 0 ≤ n := norm_nonneg _
  let δ := ρ / (2 * (n + 1))
  have hden : 0 < 2 * (n + 1) := by positivity
  have hδ : 0 < δ := div_pos hρ hden
  have hδn : δ * n < ρ := by
    change (ρ / (2 * (n + 1))) * n < ρ
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hdist_pos : dist ((AffineMap.lineMap x z) δ) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  have hdist_neg : dist ((AffineMap.lineMap x z) (-δ)) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  refine ⟨δ, hδ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_right _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_right _ _)

private theorem locallyStraight_lines_eq_of_aedisjoint
    {s t : Set Plane} {x : Plane}
    (hsregular : closure (interior s) = s)
    (htregular : closure (interior t) = t)
    (had : AEDisjoint volume s t)
    (hxt : x ∈ frontier t)
    {Ls Lt : AffineSubspace ℝ Plane}
    (hxLs : x ∈ Ls) (hLsdim : Module.finrank ℝ Ls.direction = 1)
    (hsline : ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ (Ls : Set Plane)))
    (hxLt : x ∈ Lt) (hLtdim : Module.finrank ℝ Lt.direction = 1)
    (htline : ∀ᶠ y in 𝓝 x, (y ∈ frontier t ↔ y ∈ (Lt : Set Plane))) :
    Ls = Lt := by
  obtain ⟨rs, hrs, hsball⟩ := Metric.eventually_nhds_iff.mp hsline
  obtain ⟨rt, hrt, htball⟩ := Metric.eventually_nhds_iff.mp htline
  obtain ⟨ψt, hψt⟩ :=
    Tiling.AffineSubspace.exists_levelSet_coordinate Lt x hxLt hLtdim
  have htboundary (y : Plane) (hy : y ∈ Metric.ball x rt) :
      y ∈ frontier t ↔ ψt y = ψt x :=
    (htball hy).trans (hψt y)
  have htclass := Tiling.local_levelSet_dichotomy ψt hrt htregular hxt htboundary
  dsimp only at htclass
  by_contra hne
  have hz : ∃ z, z ∈ Ls ∧ z ∉ Lt := by
    by_contra h
    push Not at h
    have hle : Ls ≤ Lt := fun z hz ↦ h z hz
    have hdir : Ls.direction = Lt.direction :=
      Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
        (hLsdim.trans hLtdim.symm)
    exact hne
      (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨x, hxLs⟩ hle)
  obtain ⟨z, hzLs, hzLt⟩ := hz
  have hzψ : ψt z ≠ ψt x := fun h ↦ hzLt ((hψt z).2 h)
  obtain ⟨δ, hδ, hyposBalls, hynegBalls⟩ := exists_small_lineMap x z hrs hrt
  let ypos := (AffineMap.lineMap x z) δ
  let yneg := (AffineMap.lineMap x z) (-δ)
  have hyposLs : ypos ∈ Ls := AffineMap.lineMap_mem δ hxLs hzLs
  have hynegLs : yneg ∈ Ls := AffineMap.lineMap_mem (-δ) hxLs hzLs
  have hψline (r : ℝ) :
      ψt ((AffineMap.lineMap x z) r) = ψt x + r * (ψt z - ψt x) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [map_add, map_smul, map_sub]
    ring
  have hsclosed : IsClosed s := by rw [← hsregular]; exact isClosed_closure
  have hdisj : Disjoint s (interior t) :=
    disjoint_regular_left_interior_of_aedisjoint hsregular had
  have contradict (y : Plane) (hyball : y ∈ Metric.ball x rs)
      (hyLs : y ∈ Ls) (hyt : y ∈ interior t) : False := by
    apply Set.disjoint_left.1 hdisj (hsclosed.frontier_subset ((hsball hyball).2 hyLs)) hyt
  rcases htclass with htpos | htneg
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hynegPos : ψt x < ψt yneg := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htpos.1 ⟨hynegBalls.2, hynegPos⟩)
    · have hyposPos : ψt x < ψt ypos := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htpos.1 ⟨hyposBalls.2, hyposPos⟩)
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hyposNeg : ψt ypos < ψt x := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htneg.2 ⟨hyposBalls.2, hyposNeg⟩)
    · have hynegNeg : ψt yneg < ψt x := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htneg.2 ⟨hynegBalls.2, hynegNeg⟩)

private theorem union_mem_nhds_of_regular_of_aedisjoint_of_locallyStraight
    {s t : Set Plane} {x : Plane}
    (hsregular : closure (interior s) = s)
    (htregular : closure (interior t) = t)
    (had : AEDisjoint volume s t)
    (hxs : x ∈ frontier s) (hxt : x ∈ frontier t)
    (hsstraight : BoundaryLocallyStraightAt s x)
    (htstraight : BoundaryLocallyStraightAt t x) :
    s ∪ t ∈ 𝓝 x := by
  obtain ⟨Ls, hxLs, hLsdim, hsline⟩ := hsstraight
  obtain ⟨Lt, hxLt, hLtdim, htline⟩ := htstraight
  have hlines : Ls = Lt :=
    locallyStraight_lines_eq_of_aedisjoint hsregular htregular had hxt
      hxLs hLsdim hsline hxLt hLtdim htline
  subst Lt
  obtain ⟨rs, hrs, hsball⟩ := Metric.eventually_nhds_iff.mp hsline
  obtain ⟨rt, hrt, htball⟩ := Metric.eventually_nhds_iff.mp htline
  obtain ⟨ψ, hψ⟩ :=
    Tiling.AffineSubspace.exists_levelSet_coordinate Ls x hxLs hLsdim
  have hsboundary (y : Plane) (hy : y ∈ Metric.ball x rs) :
      y ∈ frontier s ↔ ψ y = ψ x :=
    (hsball hy).trans (hψ y)
  have htboundary (y : Plane) (hy : y ∈ Metric.ball x rt) :
      y ∈ frontier t ↔ ψ y = ψ x :=
    (htball hy).trans (hψ y)
  have hsclass := Tiling.local_levelSet_dichotomy ψ hrs hsregular hxs hsboundary
  have htclass := Tiling.local_levelSet_dichotomy ψ hrt htregular hxt htboundary
  dsimp only at hsclass htclass
  let ρ := min rs rt
  have hρ : 0 < ρ := lt_min hrs hrt
  have hρs : ρ ≤ rs := min_le_left _ _
  have hρt : ρ ≤ rt := min_le_right _ _
  have hsclosed : IsClosed s := by rw [← hsregular]; exact isClosed_closure
  have hxsin : x ∈ closure (interior s) := by
    rw [hsregular]
    exact hsclosed.frontier_subset hxs
  obtain ⟨u, huball, huin⟩ :=
    mem_closure_iff.mp hxsin (Metric.ball x ρ) Metric.isOpen_ball
      (Metric.mem_ball_self hρ)
  have huballs : u ∈ Metric.ball x rs :=
    Metric.ball_subset_ball hρs huball
  have huballt : u ∈ Metric.ball x rt :=
    Metric.ball_subset_ball hρt huball
  have huψ : ψ u ≠ ψ x := by
    intro heq
    exact Set.disjoint_left.1 disjoint_interior_frontier huin
      ((hsboundary u huballs).2 heq)
  have hdisj : Disjoint s (interior t) :=
    disjoint_regular_left_interior_of_aedisjoint hsregular had
  have orientations :
      ((Metric.ball x rs ∩ {y | ψ x < ψ y} ⊆ interior s ∧
          Metric.ball x rs ∩ {y | ψ y < ψ x} ⊆ interior sᶜ) ∧
        (Metric.ball x rt ∩ {y | ψ x < ψ y} ⊆ interior tᶜ ∧
          Metric.ball x rt ∩ {y | ψ y < ψ x} ⊆ interior t)) ∨
      ((Metric.ball x rs ∩ {y | ψ x < ψ y} ⊆ interior sᶜ ∧
          Metric.ball x rs ∩ {y | ψ y < ψ x} ⊆ interior s) ∧
        (Metric.ball x rt ∩ {y | ψ x < ψ y} ⊆ interior t ∧
          Metric.ball x rt ∩ {y | ψ y < ψ x} ⊆ interior tᶜ)) := by
    rcases hsclass with hspos | hsneg <;> rcases htclass with htpos | htneg
    · exfalso
      rcases lt_or_gt_of_ne huψ with huneg | hupos
      · exact (interior_subset (hspos.2 ⟨huballs, huneg⟩))
          (interior_subset huin)
      · exact Set.disjoint_left.1 hdisj (interior_subset huin)
          (htpos.1 ⟨huballt, hupos⟩)
    · exact Or.inl ⟨hspos, htneg⟩
    · exact Or.inr ⟨hsneg, htpos⟩
    · exfalso
      rcases lt_or_gt_of_ne huψ with huneg | hupos
      · exact Set.disjoint_left.1 hdisj (interior_subset huin)
          (htneg.2 ⟨huballt, huneg⟩)
      · exact (interior_subset (hsneg.1 ⟨huballs, hupos⟩))
          (interior_subset huin)
  apply mem_of_superset (Metric.ball_mem_nhds x hρ)
  intro y hyball
  have hyballs : y ∈ Metric.ball x rs := Metric.ball_subset_ball hρs hyball
  have hyballt : y ∈ Metric.ball x rt := Metric.ball_subset_ball hρt hyball
  rcases lt_trichotomy (ψ y) (ψ x) with hyneg | hyeq | hypos
  · rcases orientations with h | h
    · exact Or.inr (interior_subset (h.2.2 ⟨hyballt, hyneg⟩))
    · exact Or.inl (interior_subset (h.1.2 ⟨hyballs, hyneg⟩))
  · exact Or.inl (hsclosed.frontier_subset ((hsboundary y hyballs).2 hyeq))
  · rcases orientations with h | h
    · exact Or.inl (interior_subset (h.1.1 ⟨hyballs, hypos⟩))
    · exact Or.inr (interior_subset (h.2.1 ⟨hyballt, hypos⟩))

private theorem frontier_eventuallyEq_of_eventuallyEq_of_isClosed
    {X : Type*} [TopologicalSpace X] {s t : Set X} {x : X}
    (hs : IsClosed s) (ht : IsClosed t) (hst : s =ᶠ[𝓝 x] t) :
    frontier s =ᶠ[𝓝 x] frontier t := by
  have hst_nhds : ∀ᶠ y in 𝓝 x, s =ᶠ[𝓝 y] t := hst.eventually_nhds
  filter_upwards [hst, hst_nhds] with y hy hynhds
  rw [hs.frontier_eq, ht.frontier_eq]
  ext
  constructor
  · rintro ⟨hys, hyint⟩
    refine ⟨?_, ?_⟩
    · change s y at hys
      change t y
      exact Eq.mp hy hys
    · exact fun hytint ↦ hyint ((hynhds.mem_interior_iff).2 hytint)
  · rintro ⟨hyt, hyint⟩
    refine ⟨?_, ?_⟩
    · change t y at hyt
      change s y
      exact Eq.mpr hy hyt
    · exact fun hysint ↦ hyint ((hynhds.mem_interior_iff).1 hysint)

/-- A placement-subfamily carrier and its complement carrier have the same frontier. -/
theorem frontier_placementCarrier_compl [Finite P]
    (hA : IsTiling A.prototiles A.placements) (S : Set A.placements) :
    frontier (A.placementCarrier S) = frontier (A.placementCarrier Sᶜ) := by
  let C := A.placementCarrier S
  let D := A.placementCarrier Sᶜ
  have hCregular : closure (interior C) = C :=
    A.placementCarrier_closure_interior hA.isPacking S
  have hDregular : closure (interior D) = D :=
    A.placementCarrier_closure_interior hA.isPacking Sᶜ
  have hAD : AEDisjoint volume C D :=
    A.placementCarrier_aedisjoint hA disjoint_compl_right
  have hcover : C ∪ D = Set.univ := by
    rw [← A.iUnion_placedTile_eq_univ hA]
    ext x
    simp only [C, D, A.mem_placementCarrier_iff, mem_union, mem_iUnion]
    constructor
    · rintro (⟨i, _, hxi⟩ | ⟨i, _, hxi⟩)
      · exact ⟨i, hxi⟩
      · exact ⟨i, hxi⟩
    · rintro ⟨i, hxi⟩
      by_cases hi : i ∈ S
      · exact Or.inl ⟨i, hi, hxi⟩
      · exact Or.inr ⟨i, hi, hxi⟩
  have hCcompl : Cᶜ = interior D := by
    apply subset_antisymm
    · apply interior_maximal
      · intro x hx
        have hx' : x ∈ C ∪ D := by rw [hcover]; exact mem_univ x
        exact hx'.resolve_left hx
      · exact (A.placementCarrier_isClosed hA.isPacking S).isOpen_compl
    · exact (disjoint_regular_left_interior_of_aedisjoint hCregular hAD).subset_compl_left
  have hDcompl : Dᶜ = interior C := by
    apply subset_antisymm
    · apply interior_maximal
      · intro x hx
        have hx' : x ∈ C ∪ D := by rw [hcover]; exact mem_univ x
        exact hx'.resolve_right hx
      · exact (A.placementCarrier_isClosed hA.isPacking Sᶜ).isOpen_compl
    · exact Disjoint.subset_compl_left
        (disjoint_regular_left_interior_of_aedisjoint hDregular hAD.symm)
  rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure,
    (A.placementCarrier_isClosed hA.isPacking S).closure_eq,
    (A.placementCarrier_isClosed hA.isPacking Sᶜ).closure_eq,
    hCcompl, hDcompl, hCregular, hDregular, inter_comm]

/-- A placed support is polygonal. -/
theorem isPolygonal_placedTile (i : Placement Plane P) :
    IsPolygonal (placedTile A.prototiles i) := by
  simpa [placedTile] using (A.isPolygonal i.2).vadd i.1

/-- The intrinsic vertices of a placed support are its translated support vertices. -/
theorem vertexSet_placedTile (i : Placement Plane P) :
    vertexSet (placedTile A.prototiles i) =
      i.1 +ᵥ vertexSet (A.prototiles i.2).support := by
  simp [placedTile, vertexSet_vadd]

/-- Subtype-facing form of `vertexSet_placedTile`. -/
@[simp]
theorem vertexSet_placedTile' (i : A.placements) :
    vertexSet (placedTile A.prototiles i.1) = A.placedVertexSet i := by
  simp only [A.vertexSet_placedTile i.1, placedVertexSet]

/-- A placed support is locally straight at every frontier point outside its placed vertex set. -/
theorem placedTile_boundaryLocallyStraightAt_of_not_mem_placedVertexSet
    (i : A.placements) {x : Plane} (hx : x ∈ frontier (placedTile A.prototiles i.1))
    (hxv : x ∉ A.placedVertexSet i) :
    BoundaryLocallyStraightAt (placedTile A.prototiles i.1) x := by
  apply (A.isPolygonal_placedTile i.1).boundaryLocallyStraightAt_of_not_mem_vertexSet hx
  simpa only [A.vertexSet_placedTile'] using hxv

/-- If each tile boundary is locally straight away from its vertices, a proper boundary point of
a placement-subfamily carrier contains a vertex of one of its tiles. -/
theorem exists_vertex_of_local_tile_geometry [Finite P]
    (hlocal : ∀ (i : A.placements) {y : Plane},
      y ∈ frontier (placedTile A.prototiles i.1) →
      y ∉ A.placedVertexSet i →
      BoundaryLocallyStraightAt (placedTile A.prototiles i.1) y)
    (hpacking : IsPacking A.prototiles A.placements) (S : Set A.placements) {x : Plane}
    (hx : x ∈ frontier (A.placementCarrier S))
    (hproper : ¬BoundaryLocallyStraightAt (A.placementCarrier S) x) :
    ∃ i : A.placements, i ∈ S ∧ x ∈ A.placedVertexSet i := by
  have find_vertex (R : Set A.placements)
      (hxR : x ∈ frontier (A.placementCarrier R))
      (hproperR : ¬BoundaryLocallyStraightAt (A.placementCarrier R) x) :
      ∃ i : A.placements, i ∈ R ∧ x ∈ A.placedVertexSet i := by
    by_contra hnone
    push Not at hnone
    have hRclosed : IsClosed (A.placementCarrier R) :=
      A.placementCarrier_isClosed hpacking R
    have hxRmem : x ∈ A.placementCarrier R := hRclosed.frontier_subset hxR
    obtain ⟨i, hiR, hxi⟩ := A.mem_placementCarrier_iff.mp hxRmem
    have tile_subset_carrier {k : A.placements} (hkR : k ∈ R) :
        placedTile A.prototiles k.1 ⊆ A.placementCarrier R := by
      intro y hy
      exact A.mem_placementCarrier_iff.mpr ⟨k, hkR, hy⟩
    have tile_frontier {k : A.placements} (hkR : k ∈ R)
        (hxk : x ∈ placedTile A.prototiles k.1) :
        x ∈ frontier (placedTile A.prototiles k.1) := by
      rw [(A.isClosed_placedTile k.1).frontier_eq]
      refine ⟨hxk, ?_⟩
      intro hxint
      exact Set.disjoint_left.1 disjoint_interior_frontier
        (interior_mono (tile_subset_carrier hkR) hxint) hxR
    have hxiFrontier : x ∈ frontier (placedTile A.prototiles i.1) :=
      tile_frontier hiR hxi
    have hiStraight := hlocal i hxiFrontier (hnone i hiR)
    have unique_incident (k : A.placements) (hkR : k ∈ R)
        (hxk : x ∈ placedTile A.prototiles k.1) : k = i := by
      by_contra hki
      have hxkFrontier : x ∈ frontier (placedTile A.prototiles k.1) :=
        tile_frontier hkR hxk
      have hkStraight := hlocal k hxkFrontier (hnone k hkR)
      have hik : i ≠ k := Ne.symm hki
      have haed : AEDisjoint volume (placedTile A.prototiles i.1)
          (placedTile A.prototiles k.1) :=
        hpacking i.2 k.2 (fun h ↦ hik (Subtype.ext h))
      have hunion :
          placedTile A.prototiles i.1 ∪ placedTile A.prototiles k.1 ∈ 𝓝 x :=
        union_mem_nhds_of_regular_of_aedisjoint_of_locallyStraight
          (A.closure_interior_placedTile i.1)
          (A.closure_interior_placedTile k.1) haed hxiFrontier hxkFrontier
          hiStraight hkStraight
      have hcarrier : A.placementCarrier R ∈ 𝓝 x :=
        mem_of_superset hunion (union_subset
          (tile_subset_carrier hiR) (tile_subset_carrier hkR))
      have hxint : x ∈ interior (A.placementCarrier R) :=
        mem_interior_iff_mem_nhds.mpr hcarrier
      exact Set.disjoint_left.1 disjoint_interior_frontier hxint hxR
    have hfinite : LocallyFinite fun k : R ↦ placedTile A.prototiles k.1.1 :=
      (A.locallyFinite_placedTile hpacking).comp_injective Subtype.val_injective
    have hevent := hfinite.eventually_subset
      (fun k : R ↦ A.isClosed_placedTile k.1.1) x
    have hcarrier_tile :
        A.placementCarrier R =ᶠ[𝓝 x] placedTile A.prototiles i.1 := by
      filter_upwards [hevent] with y hy
      apply propext
      constructor
      · intro hycarrier
        obtain ⟨k, hkR, hyk⟩ := A.mem_placementCarrier_iff.mp hycarrier
        have hxk : x ∈ placedTile A.prototiles k.1 :=
          hy (a := ⟨k, hkR⟩)
            (show y ∈ placedTile A.prototiles (⟨k, hkR⟩ : R).1.1 from hyk)
        have hki : k = i := unique_incident k hkR hxk
        change placedTile A.prototiles k.1 y at hyk
        change placedTile A.prototiles i.1 y
        simpa only [hki] using hyk
      · intro hyi
        exact A.mem_placementCarrier_iff.mpr ⟨i, hiR, hyi⟩
    have hfrontier := frontier_eventuallyEq_of_eventuallyEq_of_isClosed
      hRclosed (A.isClosed_placedTile i.1) hcarrier_tile
    obtain ⟨L, hxL, hLdim, htileLine⟩ := hiStraight
    apply hproperR
    refine ⟨L, hxL, hLdim, ?_⟩
    filter_upwards [hfrontier, htileLine] with y hyfront hyline
    constructor
    · intro hy
      exact hyline.1 (Eq.mp hyfront hy)
    · intro hy
      exact Eq.mpr hyfront (hyline.2 hy)
  exact find_vertex S hx hproper

/-- A proper boundary point of a placement-subfamily carrier contains a vertex of one of its
tiles. -/
theorem exists_vertex_of_not_boundaryLocallyStraightAt [Finite P]
    (hpacking : IsPacking A.prototiles A.placements) (S : Set A.placements) {x : Plane}
    (hx : x ∈ frontier (A.placementCarrier S))
    (hproper : ¬BoundaryLocallyStraightAt (A.placementCarrier S) x) :
    ∃ i : A.placements, i ∈ S ∧ x ∈ A.placedVertexSet i := by
  exact A.exists_vertex_of_local_tile_geometry
    (fun i _ hxfrontier hxvertex ↦
      A.placedTile_boundaryLocallyStraightAt_of_not_mem_placedVertexSet
        i hxfrontier hxvertex)
    hpacking S hx hproper

/-- If each tile boundary is locally straight away from its vertices, a proper boundary point of
a placement-subfamily carrier supplies a common vertex on both sides.

This is the local planar-combinatorial input to the plate argument. -/
theorem exists_vertices_across_of_local_tile_geometry [Finite P]
    (hlocal : ∀ (i : A.placements) {y : Plane},
      y ∈ frontier (placedTile A.prototiles i.1) →
      y ∉ A.placedVertexSet i →
      BoundaryLocallyStraightAt (placedTile A.prototiles i.1) y)
    (hA : IsTiling A.prototiles A.placements) (S : Set A.placements) {x : Plane}
    (hx : x ∈ frontier (A.placementCarrier S))
    (hproper : ¬BoundaryLocallyStraightAt (A.placementCarrier S) x) :
    ∃ i j : A.placements,
      i ∈ S ∧ j ∉ S ∧ x ∈ A.placedVertexSet i ∧ x ∈ A.placedVertexSet j := by
  obtain ⟨i, hiS, hxi⟩ :=
    A.exists_vertex_of_local_tile_geometry hlocal hA.isPacking S hx hproper
  have hxcompl : x ∈ frontier (A.placementCarrier Sᶜ) := by
    rw [← A.frontier_placementCarrier_compl hA S]
    exact hx
  have hproperCompl : ¬BoundaryLocallyStraightAt (A.placementCarrier Sᶜ) x := by
    rintro ⟨L, hxL, hLdim, hline⟩
    apply hproper
    refine ⟨L, hxL, hLdim, ?_⟩
    filter_upwards [hline] with y hy
    rw [A.frontier_placementCarrier_compl hA S]
    exact hy
  obtain ⟨j, hjS, hxj⟩ :=
    A.exists_vertex_of_local_tile_geometry hlocal hA.isPacking Sᶜ hxcompl hproperCompl
  exact ⟨i, j, hiS, hjS, hxi, hxj⟩

/-- At a proper boundary point of a placement-subfamily carrier, incident tiles from both sides
supply a common intrinsic vertex. -/
theorem exists_vertices_across_of_not_boundaryLocallyStraightAt [Finite P]
    (hA : IsTiling A.prototiles A.placements) (S : Set A.placements) {x : Plane}
    (hx : x ∈ frontier (A.placementCarrier S))
    (hproper : ¬BoundaryLocallyStraightAt (A.placementCarrier S) x) :
    ∃ i j : A.placements,
      i ∈ S ∧ j ∉ S ∧ x ∈ A.placedVertexSet i ∧ x ∈ A.placedVertexSet j := by
  exact A.exists_vertices_across_of_local_tile_geometry
    (fun i _ hxfrontier hxvertex ↦
      A.placedTile_boundaryLocallyStraightAt_of_not_mem_placedVertexSet
        i hxfrontier hxvertex)
    hA S hx hproper

/-- Every point of a plate-carrier frontier is locally straight. -/
theorem plateCarrier_boundaryLocallyStraightAt [Finite P]
    (hA : IsTiling A.prototiles A.placements) (C : A.Plate) {x : Plane}
    (hx : x ∈ frontier (A.plateCarrier C)) :
    BoundaryLocallyStraightAt (A.plateCarrier C) x := by
  by_contra hproper
  obtain ⟨i, j, hiC, hjC, hxi, hxj⟩ :=
    A.exists_vertices_across_of_not_boundaryLocallyStraightAt hA C hx hproper
  have hij : i ≠ j := fun h ↦ hjC (h ▸ hiC)
  have hadj : A.vertexGraph.Adj i j := by
    rw [A.vertexGraph_adj]
    exact ⟨hij, ⟨x, hxi, hxj⟩⟩
  apply hjC
  calc
    A.vertexGraph.connectedComponentMk j = A.vertexGraph.connectedComponentMk i :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
    _ = C := hiC

end PolygonalProtoTiling

end Tiling
