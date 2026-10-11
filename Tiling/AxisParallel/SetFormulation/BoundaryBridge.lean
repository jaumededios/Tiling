import Tiling.AxisParallel.SetFormulation.RegionBridge

/-!
# Intrinsic finite axis-parallel boundaries give rectangle presentations

A boundary consisting of finitely many axis-parallel segments lies on a finite
coordinate grid. Rectangulation of that grid recovers the regular-open tile.
Degenerate boundary segments are permitted.
-/

set_option autoImplicit false
open Bornology Set
open scoped Pointwise Topology

namespace Tiling.AxisParallel.SetFormulation

theorem isRectangleTile_of_axis_parallel_boundary
    (Ω : Set Plane) (hne : Ω.Nonempty) (hbounded : IsBounded Ω)
    (hregular : IsRegularOpen Ω) (edges : Finset (Plane × Plane))
    (hedge : ∀ e ∈ edges, p₁ e.1 = p₁ e.2 ∨ p₂ e.1 = p₂ e.2)
    (hfront : frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2) :
    IsRectangleTile Ω := by
  classical
  let s := edges.image fun e => e.1.re
  let t := edges.image fun e => e.1.im
  have hlines : ∀ z ∈ frontier Ω, z.re ∈ s ∨ z.im ∈ t := by
    intro z hz
    rw [hfront] at hz
    obtain ⟨e, hz⟩ := mem_iUnion.mp hz
    obtain ⟨he, hz⟩ := mem_iUnion.mp hz
    rcases hedge e he with hre | him
    · have hzre : z.re = e.1.re :=
        (convex_hyperplane Complex.reLm.isLinear e.1.re).segment_subset
          rfl hre.symm hz
      exact Or.inl (Finset.mem_image.mpr ⟨e, he, hzre.symm⟩)
    · have hzim : z.im = e.1.im :=
        (convex_hyperplane Complex.imLm.isLinear e.1.im).segment_subset
          rfl him.symm hz
      exact Or.inr (Finset.mem_image.mpr ⟨e, he, hzim.symm⟩)
  have hopen : IsOpen Ω := hregular ▸ isOpen_interior
  have haxis := Tiling.AxisParallel.FiniteRectangles.rectangulation_of_grid
    hopen hbounded s t hlines
  let K : Tiling.AxisParallel.Region := {
    support := closure Ω
    isPolygonal := Tiling.AxisParallel.IntrinsicVertices.isPolygonal_of_isAxisParallel haxis
    nonempty := hne.mono subset_closure
    isAxisParallel := haxis }
  obtain ⟨F, hF⟩ := Tiling.AxisParallel.FiniteRectangles.region_rectangle_presentation K
  exact ⟨hne, F, hregular.symm.trans (congrArg interior hF)⟩

end Tiling.AxisParallel.SetFormulation
