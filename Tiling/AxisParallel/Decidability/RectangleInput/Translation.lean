import Tiling.AxisParallel.Decidability.RectangleInput.Geometry
import Tiling.Geometry.PolygonalTopology

set_option autoImplicit false

open Set
open scoped Pointwise

noncomputable section

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

theorem rectangle_vadd (a p q : Plane) :
    a +ᵥ rectangle p q = rectangle (a + p) (a + q) := by
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, rectangle, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_Icc, vadd_eq_add, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, p₁, p₂]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;>
    constructor <;> constructor <;> linarith

def translatedRectangles (R : List (Plane × Plane)) (a : Plane) : List (Plane × Plane) :=
  R.map fun r => (a + r.1, a + r.2)

theorem realizesRectangles_vadd {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (a : Plane) :
    RectanglePresentation (translatedRectangles R a) (a +ᵥ Ω) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨z, hz⟩ := hR.1
    exact ⟨a + z, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩⟩
  · rw [hR.2, ← interior_vadd]
    congr 1
    rw [Set.vadd_set_iUnion]
    simp only [Set.vadd_set_iUnion]
    ext z
    simp only [translatedRectangles, List.mem_map, Set.mem_iUnion,
      exists_prop, exists_exists_and_eq_and, rectangle_vadd]

def translatedRegion {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (a : Plane) : Tiling.AxisParallel.Region :=
  regionOfTile (a +ᵥ Ω) (RectanglePresentation.isAxisParallelTile (realizesRectangles_vadd hR a))

@[simp] theorem translatedRegion_openCarrier {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (a : Plane) :
    (translatedRegion hR a).openCarrier = a +ᵥ Ω :=
  regionOfTile_openCarrier _ _

theorem translatedRegion_support {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (a : Plane) :
    (translatedRegion hR a).support =
      a +ᵥ (regionOfTile Ω (RectanglePresentation.isAxisParallelTile hR)).support :=
  closure_vadd a Ω

theorem translatedRegion_vertices {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) (a : Plane) :
    (translatedRegion hR a).vertices = a +ᵥ vertices Ω := by
  rw [(translatedRegion hR a).vertices_eq_vertexSet, translatedRegion_support,
    Tiling.vertexSet_vadd, ← (regionOfTile Ω
      (RectanglePresentation.isAxisParallelTile hR)).vertices_eq_vertexSet,
    ← vertices_eq_native Ω (RectanglePresentation.isAxisParallelTile hR)]

end Tiling.AxisParallel.Decidability.RectangleInput
