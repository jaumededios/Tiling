import Tiling.AxisParallel.Approximation.Core
import Tiling.Geometry.PolygonalTopology
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace Tiling.AxisParallel.Approximation

/-- The literal range of an indexed injective deformation of centres. -/
def deformedCenterCarrier {ι : Type*} (D : ι ↪ Tiling.Plane) : Set Tiling.Plane :=
  Set.range D

/-- An injective indexed centre map identifies its index type with its literal range. -/
noncomputable def deformedCenterEquivCarrier {ι : Type*}
    (D : ι ↪ Tiling.Plane) : ι ≃ ↥(deformedCenterCarrier D) :=
  Equiv.ofInjective D D.injective

/-- The image of a selected subfamily under an indexed centre deformation. -/
def deformedCenterCarrierOn {ι : Type*}
    (D : ι ↪ Tiling.Plane) (J : Set ι) : Set Tiling.Plane :=
  D '' J

/-- The singleton family indexed by the literal deformed centre carrier. -/
def deformedCenterSingletonFamily {ι : Type*} (D : ι ↪ Tiling.Plane) :
    ↥(deformedCenterCarrier D) → Set Tiling.Plane :=
  fun t ↦ {t.1}

/-- A coordinatewise homeomorphic deformation realizing a good rational approximation. -/
structure CoordinateDeformation (C : ApproximationContext)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) where
  source_good : IsGoodApproximation C φ
  firstHomeomorph : ℝ ≃ₜ ℝ
  firstHomeomorph_strictMono : StrictMono firstHomeomorph
  secondHomeomorph : ℝ ≃ₜ ℝ
  secondHomeomorph_strictMono : StrictMono secondHomeomorph
  firstPlanarHomeomorph : Tiling.Plane ≃ₜ Tiling.Plane
  firstPlanarHomeomorph_apply : ∀ z : Tiling.Plane,
    firstPlanarHomeomorph z = firstHomeomorph z.re + z.im * Complex.I
  planarHomeomorph : Tiling.Plane ≃ₜ Tiling.Plane
  planarHomeomorph_apply : ∀ z : Tiling.Plane,
    planarHomeomorph z = firstHomeomorph z.re + secondHomeomorph z.im * Complex.I
  firstRegion : Tiling.AxisParallel.Region
  deformedRegion : Tiling.AxisParallel.Region
  firstRegion_openCarrier :
    firstRegion.openCarrier = firstPlanarHomeomorph '' C.region.openCarrier
  deformedRegion_openCarrier :
    deformedRegion.openCarrier = planarHomeomorph '' C.region.openCarrier
  first_vertex_agreement :
    ∀ (v : Tiling.Plane) (hv : v ∈ C.region.vertices),
      firstPlanarHomeomorph v = mapFirstPoint φ (C.vertexPoint v hv)
  vertex_agreement :
    ∀ (v : Tiling.Plane) (hv : v ∈ C.region.vertices),
      planarHomeomorph v = mapPoint φ (C.vertexPoint v hv)
  vertices_image :
    deformedRegion.vertices = planarHomeomorph '' C.region.vertices
  componentEquiv :
    ConnectedComponents ↥C.region.openCarrier ≃
      ConnectedComponents ↥deformedRegion.openCarrier
  complementComponentEquiv :
    ConnectedComponents ↥(C.region.openCarrier)ᶜ ≃
      ConnectedComponents ↥(deformedRegion.openCarrier)ᶜ
  rational_vertices :
    ∀ v ∈ deformedRegion.vertices, Tiling.IsRationalPoint v

end Tiling.AxisParallel.Approximation
