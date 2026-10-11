import Tiling.AxisParallel.SetFormulation.Basic
import Tiling.AxisParallel.Foundations.FiniteRectangles
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

set_option autoImplicit false

open Bornology MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.SetFormulation

theorem rectangle_eq_orderedBox (a b : Plane) :
    rectangle a b = Tiling.AxisParallel.FiniteRectangles.orderedBox a b := rfl

theorem IsRectangleTile.nonempty {Ω : Set Plane} (hΩ : IsRectangleTile Ω) :
    Ω.Nonempty := hΩ.1

theorem IsRectangleTile.isOpen {Ω : Set Plane} (hΩ : IsRectangleTile Ω) :
    IsOpen Ω := by
  obtain ⟨F, rfl⟩ := hΩ.2
  exact isOpen_interior

theorem IsRectangleTile.isRegularOpen {Ω : Set Plane} (hΩ : IsRectangleTile Ω) :
    IsRegularOpen Ω := by
  obtain ⟨F, rfl⟩ := hΩ.2
  simp only [rectangle_eq_orderedBox]
  exact Tiling.AxisParallel.FiniteRectangles.interior_isRegularOpen_of_isClosed
    (Tiling.AxisParallel.FiniteRectangles.finite_boxes_union_isClosed F)

theorem IsRectangleTile.isBounded {Ω : Set Plane} (hΩ : IsRectangleTile Ω) :
    IsBounded Ω := by
  obtain ⟨F, rfl⟩ := hΩ.2
  simp only [rectangle_eq_orderedBox]
  exact (Tiling.AxisParallel.FiniteRectangles.finite_boxes_union_isBounded F).subset interior_subset

theorem IsRectangleTile.frontier_axisLines {Ω : Set Plane}
    (hΩ : IsRectangleTile Ω) :
    ∃ s t : Finset ℝ, ∀ z ∈ frontier Ω, z.re ∈ s ∨ z.im ∈ t := by
  obtain ⟨F, rfl⟩ := hΩ.2
  simp only [rectangle_eq_orderedBox]
  exact Tiling.AxisParallel.FiniteRectangles.finite_boxes_carrier_axisLines F

theorem IsRectangleTile.isAxisParallel_closure {Ω : Set Plane}
    (hΩ : IsRectangleTile Ω) : Tiling.IsAxisParallel (closure Ω) := by
  obtain ⟨s, t, hfront⟩ := hΩ.frontier_axisLines
  exact Tiling.AxisParallel.FiniteRectangles.rectangulation_of_grid
    hΩ.isOpen hΩ.isBounded s t hfront

def regionOfTile (Ω : Set Plane) (hΩ : IsRectangleTile Ω) :
    Tiling.AxisParallel.Region where
  support := closure Ω
  isPolygonal := Tiling.AxisParallel.IntrinsicVertices.isPolygonal_of_isAxisParallel
    hΩ.isAxisParallel_closure
  nonempty := hΩ.nonempty.mono subset_closure
  isAxisParallel := hΩ.isAxisParallel_closure

@[simp] theorem regionOfTile_support (Ω : Set Plane) (hΩ : IsRectangleTile Ω) :
    (regionOfTile Ω hΩ).support = closure Ω := rfl

@[simp] theorem regionOfTile_openCarrier (Ω : Set Plane) (hΩ : IsRectangleTile Ω) :
    (regionOfTile Ω hΩ).openCarrier = Ω := hΩ.isRegularOpen

theorem region_rectangle_presentation (K : Tiling.AxisParallel.Region) :
    ∃ F : Finset (Plane × Plane), K.support = ⋃ r ∈ F, rectangle r.1 r.2 :=
  Tiling.AxisParallel.FiniteRectangles.region_rectangle_presentation K

theorem isAxisParallelTile_openCarrier (K : Tiling.AxisParallel.Region) :
    IsRectangleTile K.openCarrier := by
  obtain ⟨F, hF⟩ := region_rectangle_presentation K
  exact ⟨K.isPolygonal.interior_nonempty K.nonempty, F,
    congrArg interior hF⟩

theorem packing_openCarrier_iff (K : Tiling.AxisParallel.Region) (T : Set Plane) :
    Packing K.openCarrier T ↔
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements T) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  constructor
  · intro h s hs t ht hst
    apply Set.disjoint_iff_inter_eq_empty.mpr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    have hopen := ((K.openCarrier_regularOpen).1.vadd s).inter
      ((K.openCarrier_regularOpen).1.vadd t)
    exact hopen.measure_ne_zero volume hne (h hs ht hst)
  · intro h s hs t ht hst
    change volume ((s +ᵥ K.openCarrier) ∩ (t +ᵥ K.openCarrier)) = 0
    rw [Set.disjoint_iff_inter_eq_empty.mp (h hs ht hst), measure_empty]

theorem tilingOn_openCarrier_iff (K : Tiling.AxisParallel.Region) (E T : Set Plane) :
    TilingOn E K.openCarrier T ↔ Tiling.AxisParallel.TilesOn K T E := by
  rw [Tiling.AxisParallel.tilesOn_iff_multiplicity]
  constructor
  · rintro ⟨hc, hp, he⟩
    refine ⟨hc, (packing_openCarrier_iff K T).mp hp, ?_⟩
    filter_upwards [he] with z hz
    change (z ∈ E) = (z ∈ T +ᵥ K.openCarrier) at hz
    rw [hz]
    constructor
    · rintro ⟨t, ht, u, hu, rfl⟩
      exact ⟨⟨t, ht⟩, u, hu, rfl⟩
    · rintro ⟨t, u, hu, rfl⟩
      exact ⟨t, t.2, u, hu, rfl⟩
  · rintro ⟨hc, hp, he⟩
    refine ⟨hc, (packing_openCarrier_iff K T).mpr hp, ?_⟩
    filter_upwards [he] with z hz
    apply propext
    change z ∈ E ↔ z ∈ T +ᵥ K.openCarrier
    rw [hz]
    constructor
    · rintro ⟨t, u, hu, rfl⟩
      exact ⟨t, t.2, u, hu, rfl⟩
    · rintro ⟨t, ht, u, hu, rfl⟩
      exact ⟨⟨t, ht⟩, u, hu, rfl⟩

theorem tilingOn_iff_native (Ω : Set Plane) (hΩ : IsRectangleTile Ω)
    (E T : Set Plane) :
    TilingOn E Ω T ↔ Tiling.AxisParallel.TilesOn (regionOfTile Ω hΩ) T E := by
  simpa using tilingOn_openCarrier_iff (regionOfTile Ω hΩ) E T

private theorem close_vertex_edge (K : Tiling.AxisParallel.Region)
    (axis : Tiling.AxisParallel.Axis) {v : Plane} (hv : v ∈ K.vertices)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ frontier K.openCarrier ∩ Metric.ball v ε,
      axis.coord z ≠ axis.coord v := by
  obtain ⟨w, hne, halign, hseg⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.intrinsicVertex_incident_axisEdge K axis ⟨v, hv⟩
  have hvcl : v ∈ closure (openSegment ℝ v w.1) := by
    rw [closure_openSegment]
    exact left_mem_segment ℝ _ _
  obtain ⟨z, hzball, hzseg⟩ := mem_closure_iff.mp hvcl
    (Metric.ball v ε) Metric.isOpen_ball (Metric.mem_ball_self hε)
  have hzfront : z ∈ frontier K.openCarrier := by
    rw [K.frontier_openCarrier_eq_frontier_support]
    exact (hseg hzseg).1
  have hzv : z ≠ v := by
    intro heq
    rw [heq] at hzseg
    exact hne (left_mem_openSegment_iff.mp hzseg).symm
  refine ⟨z, ⟨hzfront, hzball⟩, ?_⟩
  cases axis with
  | horizontal =>
    have him : z.im = v.im :=
      (convex_hyperplane Complex.imLm.isLinear v.im).segment_subset
        rfl halign (openSegment_subset_segment ℝ _ _ hzseg)
    exact fun hre => hzv (Complex.ext hre him)
  | vertical =>
    have hre : z.re = v.re :=
      (convex_hyperplane Complex.reLm.isLinear v.re).segment_subset
        rfl halign (openSegment_subset_segment ℝ _ _ hzseg)
    exact fun him => hzv (Complex.ext hre him)

theorem vertices_openCarrier_eq (K : Tiling.AxisParallel.Region) :
    vertices K.openCarrier = K.vertices := by
  ext v
  constructor
  · rintro ⟨hvfront, hvε⟩
    by_contra hv
    have hvfront' : v ∈ frontier K.support :=
      K.frontier_openCarrier_eq_frontier_support ▸ hvfront
    obtain ⟨L, hvL, hdim, hlocal⟩ :=
      K.isPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hvfront' hv
    obtain ⟨d, hd, r, hr, hline⟩ :=
      Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hvL hdim hlocal
    obtain ⟨q, hq, hcross⟩ := K.isAxisParallel.localBoundaryCross v
    obtain ⟨⟨a, ⟨hafront, haball⟩, hare⟩, ⟨b, ⟨hbfront, hbball⟩, hbim⟩⟩ :=
      hvε (min r q) (lt_min hr hq)
    have har := Metric.ball_subset_ball (min_le_left r q) haball
    have haq := Metric.ball_subset_ball (min_le_right r q) haball
    have hbr := Metric.ball_subset_ball (min_le_left r q) hbball
    have hbq := Metric.ball_subset_ball (min_le_right r q) hbball
    have hafront' : a ∈ frontier K.support :=
      K.frontier_openCarrier_eq_frontier_support ▸ hafront
    have hbfront' : b ∈ frontier K.support :=
      K.frontier_openCarrier_eq_frontier_support ▸ hbfront
    have haim := (hcross a haq hafront').resolve_left hare
    have hbre := (hcross b hbq hbfront').resolve_right hbim
    have haL := Tiling.mem_affineLine.mp ((hline a har).mp hafront')
    have hbL := Tiling.mem_affineLine.mp ((hline b hbr).mp hbfront')
    have hdmul : d.im * (a.re - v.re) = 0 := by
      dsimp [Tiling.signedSide, Tiling.planarCross] at haL
      rw [haim] at haL
      linarith
    have hdimmul : d.re * (b.im - v.im) = 0 := by
      dsimp [Tiling.signedSide, Tiling.planarCross] at hbL
      rw [hbre] at hbL
      linarith
    have hdimzero : d.im = 0 :=
      (mul_eq_zero.mp hdmul).resolve_right (sub_ne_zero.mpr hare)
    have hdrezero : d.re = 0 :=
      (mul_eq_zero.mp hdimmul).resolve_right (sub_ne_zero.mpr hbim)
    exact hd (Complex.ext hdrezero hdimzero)
  · intro hv
    refine ⟨Tiling.AxisParallel.IntrinsicVertices.region_vertices_subset_frontier K hv, ?_⟩
    intro ε hε
    exact ⟨close_vertex_edge K .horizontal hv hε, close_vertex_edge K .vertical hv hε⟩

theorem vertices_eq_native (Ω : Set Plane) (hΩ : IsRectangleTile Ω) :
    vertices Ω = (regionOfTile Ω hΩ).vertices := by
  simpa using vertices_openCarrier_eq (regionOfTile Ω hΩ)

end Tiling.AxisParallel.SetFormulation
