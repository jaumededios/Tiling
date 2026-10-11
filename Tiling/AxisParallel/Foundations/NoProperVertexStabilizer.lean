import Tiling.AxisParallel.Core
import Tiling.Geometry.Sliding

/-!
# Shared stabilizer direction for proper-vertex-free supports

This lower module extracts the regular-open stabilizer argument from the
continuous slab development so terminal consumers can use it without importing
the continuous layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Set
open MeasureTheory
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel

/-- A regular-open planar set without proper vertices is invariant along a nonzero direction. -/
theorem exists_stabilizerDirection_of_noProperVertices
    {D : Set Tiling.Plane} (hDopen : IsOpen D)
    (hDregular : interior (closure D) = D)
    (hDvertices : properVertices D = ∅) :
    ∃ v : Tiling.Plane, v ≠ 0 ∧ ∀ r : ℝ,
      r • v ∈ AddAction.stabilizer Tiling.Plane D := by
  by_cases hDempty : D = ∅
  · refine ⟨1, one_ne_zero, ?_⟩
    intro r
    rw [AddAction.mem_stabilizer_iff, hDempty]
    simp
  have hDnonempty : D.Nonempty := Set.nonempty_iff_ne_empty.mpr hDempty
  have hFrontierClosure : frontier (closure D) = frontier D := by
    rw [frontier, closure_closure, hDregular]
    symm
    rw [frontier, hDopen.interior_eq]
  have hstraight : ∀ x, x ∈ frontier (closure D) →
      Tiling.BoundaryLocallyStraightAt (closure D) x := by
    intro x hx
    have hxD : x ∈ frontier D := hFrontierClosure ▸ hx
    have hxStraight : Tiling.BoundaryLocallyStraightAt D x := by
      by_contra hxNotStraight
      have hxProper : x ∈ properVertices D :=
        ⟨hxD, hxNotStraight⟩
      rw [hDvertices] at hxProper
      exact hxProper.elim
    rcases hxStraight with ⟨L, hxL, hLdim, hlocal⟩
    refine ⟨L, hxL, hLdim, ?_⟩
    simpa only [hFrontierClosure] using hlocal
  have hClosedRegular : closure (interior (closure D)) = closure D := by
    rw [hDregular]
  obtain ⟨v, hv, hinvariant⟩ := Tiling.exists_common_stabilizer_direction
    (fun _ : Unit ↦ closure D)
    (fun _ ↦ hDnonempty.mono subset_closure)
    (fun _ ↦ hClosedRegular)
    (fun {_ _} hij ↦ (hij (Subsingleton.elim _ _)).elim)
    (fun _ ↦ hstraight)
  refine ⟨v, hv, ?_⟩
  intro r
  rw [AddAction.mem_stabilizer_iff]
  calc
    r • v +ᵥ D = r • v +ᵥ interior (closure D) := by rw [hDregular]
    _ = interior (r • v +ᵥ closure D) := by rw [interior_vadd]
    _ = interior (closure D) := by
      rw [AddAction.mem_stabilizer_iff.mp (hinvariant Unit.unit r)]
    _ = D := hDregular

end Tiling.AxisParallel
