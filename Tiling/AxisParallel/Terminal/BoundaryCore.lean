import Tiling.AxisParallel.Core

/-!
# Boundary-code core definitions and local cone transport laws

This module records the four local Boolean quadrants at a proper vertex, labelled complete boundary
lines, their translation action, strict-distance linkedness, and local cone transport laws.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

/-- A local cone is the set of Boolean-labelled open quadrants which lie locally in the region. -/
abbrev LocalCone : Type := Set (Bool × Bool)

/-- Whether `z` lies in the open quadrant at `x` selected by the two Boolean signs. -/
private def liesInQuadrant (x z : Tiling.Plane) (q : Bool × Bool) : Prop :=
  (if q.1 then x.re < z.re else z.re < x.re) ∧
    (if q.2 then x.im < z.im else z.im < x.im)

/-- The Boolean sign quadrants which, near a proper vertex, lie inside the region. -/
noncomputable def localCone
    (F : Set Tiling.Plane) (x : Tiling.Plane)
    (_hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F)
    (_hx : Tiling.AxisParallel.IsProperVertex F x) : LocalCone :=
  {q | ∃ r : ℝ, 0 < r ∧
    ∀ z : Tiling.Plane, z ∈ Metric.ball x r → liesInQuadrant x z q → z ∈ F}

/-- A complete boundary line, including both its orientation and its locally-inside side. -/
structure CompleteBoundaryLine where
  axis : Tiling.AxisParallel.Axis
  level : ℝ
  insideOnPositiveSide : Bool

/-- The underlying affine coordinate line of a labelled complete boundary line. -/
def CompleteBoundaryLine.carrier (L : CompleteBoundaryLine) : Set Tiling.Plane :=
  {z | L.axis.transverseCoord z = L.level}

/-- Translate a labelled complete boundary line, preserving its locally-inside side. -/
def CompleteBoundaryLine.vadd
    (L : CompleteBoundaryLine) (a : Tiling.Plane) : CompleteBoundaryLine where
  axis := L.axis
  level := L.level + L.axis.transverseCoord a
  insideOnPositiveSide := L.insideOnPositiveSide

/-- The complete coordinate lines in the boundary, labelled by the side locally inside `F`. -/
noncomputable def completeBoundaryLines
    (F : Set Tiling.Plane)
    (_hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F) :
    Set CompleteBoundaryLine :=
  {L | L.carrier ⊆ frontier F ∧
    ∀ x ∈ L.carrier, ∃ r : ℝ, 0 < r ∧
      ∀ z : Tiling.Plane, z ∈ Metric.ball x r →
        (z ∈ F ↔
          if L.insideOnPositiveSide then
            L.level < L.axis.transverseCoord z
          else
            L.axis.transverseCoord z < L.level)}

/-- Proper-vertex germs together with all labelled complete boundary lines. -/
structure BoundaryCode where
  properVertexSet : Set Tiling.Plane
  cone : properVertexSet → LocalCone
  completeLines : Set CompleteBoundaryLine

/-- The ordinary set-theoretic graph of the subtype-indexed cone function. -/
def BoundaryCode.coneGraph (B : BoundaryCode) : Set (Tiling.Plane × LocalCone) :=
  {(x, C) | ∃ hx : x ∈ B.properVertexSet, C = B.cone ⟨x, hx⟩}

/-- The boundary code of a locally axis-parallel polygonal region. -/
noncomputable def boundaryCode
    (F : Set Tiling.Plane)
    (hF : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F) : BoundaryCode where
  properVertexSet := Tiling.AxisParallel.properVertices F
  cone := fun x => localCone F x hF x.property
  completeLines := completeBoundaryLines F hF

/-- Translate a boundary code. -/
def BoundaryCode.vadd (B : BoundaryCode) (a : Tiling.Plane) : BoundaryCode where
  properVertexSet := a +ᵥ B.properVertexSet
  cone := fun x =>
    B.cone ⟨x.1 - a, by
      rcases x.property with ⟨y, hy, hxy⟩
      rw [← hxy]
      simpa only [vadd_eq_add, add_sub_cancel_left] using hy⟩
  completeLines := (fun L => L.vadd a) '' B.completeLines

/-- Nonempty connectedness of the graph joining distinct points at strict distance less than `r`. -/
def Linked (r : ℝ) (S : Set Tiling.Plane) : Prop :=
  S.Nonempty ∧
    ∀ x ∈ S, ∀ y ∈ S,
      Relation.ReflTransGen
        (fun u v : Tiling.Plane => u ∈ S ∧ v ∈ S ∧ dist u v < r) x y

end Tiling.AxisParallel.Terminal

open Filter Set Topology
open scoped Pointwise
namespace Tiling.AxisParallel.Terminal

/-- A local Boolean cone depends only on the offset membership germ at its anchor. -/
theorem localCone_eq_of_eventually_mem_iff_offset
    {F₀ F₁ : Set Tiling.Plane} {x y : Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hx : Tiling.AxisParallel.IsProperVertex F₀ x)
    (hy : Tiling.AxisParallel.IsProperVertex F₁ y)
    (h : ∀ᶠ d in 𝓝 (0 : Tiling.Plane), (x + d ∈ F₀ ↔ y + d ∈ F₁)) :
    localCone F₀ x hF₀ hx = localCone F₁ y hF₁ hy := by
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp h
  ext q
  change (∃ r : ℝ, 0 < r ∧ ∀ z : Tiling.Plane,
      z ∈ Metric.ball x r →
      ((if q.1 then x.re < z.re else z.re < x.re) ∧
        (if q.2 then x.im < z.im else z.im < x.im)) → z ∈ F₀) ↔
    (∃ r : ℝ, 0 < r ∧ ∀ z : Tiling.Plane,
      z ∈ Metric.ball y r →
      ((if q.1 then y.re < z.re else z.re < y.re) ∧
        (if q.2 then y.im < z.im else z.im < y.im)) → z ∈ F₁)
  have quadrant (u v z : Tiling.Plane) :
      ((if q.1 then u.re < (u + (z - v)).re else (u + (z - v)).re < u.re) ∧
        (if q.2 then u.im < (u + (z - v)).im else (u + (z - v)).im < u.im)) ↔
      ((if q.1 then v.re < z.re else z.re < v.re) ∧
        (if q.2 then v.im < z.im else z.im < v.im)) := by
    rcases q with ⟨b₁, b₂⟩
    cases b₁ <;> cases b₂ <;>
      simp only [Bool.false_eq_true, ↓reduceIte, Complex.add_re, Complex.add_im,
        Complex.sub_re, Complex.sub_im] <;>
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;>
      constructor <;> linarith
  constructor
  · rintro ⟨r, hr, hcone⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    intro z hz hq
    have hzR : z ∈ Metric.ball y r :=
      Metric.ball_subset_ball (min_le_left r s) hz
    have hzS : z ∈ Metric.ball y s :=
      Metric.ball_subset_ball (min_le_right r s) hz
    have hdS : z - y ∈ Metric.ball (0 : Tiling.Plane) s := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hzS
    have hxR : x + (z - y) ∈ Metric.ball x r := by
      have hdist : dist (x + (z - y)) x = dist z y := by
        simp only [dist_eq_norm]
        congr 1
        abel
      simpa only [Metric.mem_ball, hdist] using hzR
    have hxQ := (quadrant x y z).2 hq
    have hxy := hball hdS
    have hyz : y + (z - y) = z := by abel
    simpa only [hyz] using hxy.mp (hcone (x + (z - y)) hxR hxQ)
  · rintro ⟨r, hr, hcone⟩
    refine ⟨min r s, lt_min hr hs, ?_⟩
    intro z hz hq
    have hzR : z ∈ Metric.ball x r :=
      Metric.ball_subset_ball (min_le_left r s) hz
    have hzS : z ∈ Metric.ball x s :=
      Metric.ball_subset_ball (min_le_right r s) hz
    have hdS : z - x ∈ Metric.ball (0 : Tiling.Plane) s := by
      simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hzS
    have hyR : y + (z - x) ∈ Metric.ball y r := by
      have hdist : dist (y + (z - x)) y = dist z x := by
        simp only [dist_eq_norm]
        congr 1
        abel
      simpa only [Metric.mem_ball, hdist] using hzR
    have hyQ := (quadrant y x z).2 hq
    have hxy := hball hdS
    have hxz : x + (z - x) = z := by abel
    simpa only [hxz] using hxy.mpr (hcone (y + (z - x)) hyR hyQ)

/-- Exact translated supports have equal cones at translated proper vertices. -/
theorem localCone_eq_of_vadd_eq
    {F₀ F₁ : Set Tiling.Plane} {a x : Tiling.Plane}
    (hF₀ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₀)
    (hF₁ : Tiling.AxisParallel.IsLocallyAxisParallelPolygonal F₁)
    (hx : Tiling.AxisParallel.IsProperVertex F₀ x)
    (hy : Tiling.AxisParallel.IsProperVertex F₁ (a + x))
    (htrans : F₁ = a +ᵥ F₀) :
    localCone F₀ x hF₀ hx = localCone F₁ (a + x) hF₁ hy := by
  apply localCone_eq_of_eventually_mem_iff_offset hF₀ hF₁ hx hy
  apply Filter.Eventually.of_forall
  intro d
  rw [htrans, mem_vadd_set_iff_neg_vadd_mem]
  change x + d ∈ F₀ ↔ -a + (a + x + d) ∈ F₀
  have hax : -a + (a + x + d) = x + d := by abel
  rw [hax]


end Tiling.AxisParallel.Terminal
