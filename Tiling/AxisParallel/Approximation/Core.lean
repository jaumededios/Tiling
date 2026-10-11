import Tiling.AxisParallel.Core
import Mathlib.Data.Real.Sign
import Mathlib.LinearAlgebra.Basis.Basic

open Set

namespace Tiling.AxisParallel.Approximation

noncomputable section

/-- The normalized geometric and linear-algebraic data used by rational approximations. -/
structure ApproximationContext where
  region : Tiling.AxisParallel.Region
  centres : Set Tiling.Plane
  target : Set Tiling.Plane
  zero_mem_vertices : 0 ∈ region.vertices
  zero_mem_centres : 0 ∈ centres
  coordinateSpace : Submodule ℚ ℝ
  basisIndex : Type*
  basis : Module.Basis basisIndex ℚ coordinateSpace
  coordinateSpace_eq_span :
    coordinateSpace = Submodule.span ℚ
      {r : ℝ | ∃ (axis : Tiling.AxisParallel.Axis) (a b : Tiling.Plane),
        (∃ v ∈ region.vertices, ∃ t ∈ centres, a = v + t) ∧
        (∃ v ∈ region.vertices, ∃ t ∈ centres, b = v + t) ∧
        r = Tiling.AxisParallel.Axis.coord axis (a - b)}
  vertex_re_mem : ∀ v ∈ region.vertices, v.re ∈ coordinateSpace
  vertex_im_mem : ∀ v ∈ region.vertices, v.im ∈ coordinateSpace
  centre_re_mem : ∀ t ∈ centres, t.re ∈ coordinateSpace
  centre_im_mem : ∀ t ∈ centres, t.im ∈ coordinateSpace

/-- A rational linear map which fixes rational scalars and is close on the chosen basis. -/
structure IsEpsilonApproximation (C : ApproximationContext) (ε : ℝ)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) : Prop where
  epsilon_pos : 0 < ε
  fixesRational : ∀ (q : ℚ) (hq : (q : ℝ) ∈ C.coordinateSpace),
    φ ⟨(q : ℝ), hq⟩ = q
  basis_close : ∀ j : C.basisIndex,
    |((φ (C.basis j) : ℚ) : ℝ) - ((C.basis j : C.coordinateSpace) : ℝ)| < ε

theorem IsEpsilonApproximation.of_le
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    {ε δ : ℝ} (hφ : IsEpsilonApproximation C ε φ) (hεδ : ε ≤ δ) :
    IsEpsilonApproximation C δ φ where
  epsilon_pos := lt_of_lt_of_le hφ.epsilon_pos hεδ
  fixesRational := hφ.fixesRational
  basis_close j := lt_of_lt_of_le (hφ.basis_close j) hεδ

/-- Regard a controlled vertex as a point whose two coordinates lie in the coordinate space. -/
def ApproximationContext.vertexPoint (C : ApproximationContext)
    (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
    {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} :=
  ⟨v, C.vertex_re_mem v hv, C.vertex_im_mem v hv⟩

/-- Regard a controlled centre as a point whose two coordinates lie in the coordinate space. -/
def ApproximationContext.centrePoint (C : ApproximationContext)
    (t : Tiling.Plane) (ht : t ∈ C.centres) :
    {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace} :=
  ⟨t, C.centre_re_mem t ht, C.centre_im_mem t ht⟩

/-- Evaluate a rational approximation and coerce its rational value back to `ℝ`. -/
def mapScalar {C : ApproximationContext} (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x : C.coordinateSpace) : ℝ :=
  φ x

/-- The image of a set of controlled scalars. -/
def mapScalarSet {C : ApproximationContext} (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (S : Set C.coordinateSpace) : Set ℝ :=
  mapScalar φ '' S

/-- Deform only the first coordinate of a controlled point. -/
def mapFirstPoint {C : ApproximationContext} (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    Tiling.Plane :=
  (mapScalar φ ⟨x.1.re, x.2.1⟩ : ℂ) + (x.1.im : ℂ) * Complex.I

/-- Deform both coordinates of a controlled point by the same rational linear map. -/
def mapPoint {C : ApproximationContext} (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (x : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}) :
    Tiling.Plane :=
  (mapScalar φ ⟨x.1.re, x.2.1⟩ : ℂ) +
    (mapScalar φ ⟨x.1.im, x.2.2⟩ : ℂ) * Complex.I

/-- The order-preservation condition required to deform an axis-parallel polygon. -/
structure IsGoodApproximation (C : ApproximationContext)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) : Prop where
  preservesVertexCoordinateSign :
    ∀ (axis : Tiling.AxisParallel.Axis) (v w : Tiling.Plane)
      (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices),
      Real.sign (Tiling.AxisParallel.Axis.coord axis
        (mapPoint φ (C.vertexPoint v hv) - mapPoint φ (C.vertexPoint w hw))) =
      Real.sign (Tiling.AxisParallel.Axis.coord axis (v - w))

end

end Tiling.AxisParallel.Approximation
