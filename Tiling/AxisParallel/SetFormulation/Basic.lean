import Tiling.AxisParallel.SetFormulation.Definitions
import Tiling.Geometry.FiniteLocalComplexity

/-!
# Set formulations of packing, tiling, and periodicity

This module connects predicates on sets to their structured
counterparts. It imports no challenge statements.
-/

set_option autoImplicit false

open Bornology Set
open scoped Pointwise

namespace Tiling.AxisParallel.SetFormulation

theorem isRegularOpen_isOpen {X : Type*} [TopologicalSpace X]
    {U : Set X} (hU : IsRegularOpen U) : IsOpen U := by
  rw [← hU]
  exact isOpen_interior

theorem isPeriod_iff_mem_periodGroup (A : Set Plane) (p : Plane) :
    IsPeriod A p ↔ p ∈ Tiling.Polygonal.periodGroup A := by
  exact AddAction.mem_stabilizer_iff.symm

theorem isPeriod_iff_membership (A : Set Plane) (p : Plane) :
    IsPeriod A p ↔ ∀ x, x + p ∈ A ↔ x ∈ A := by
  constructor
  · intro hp x
    have hmem := congrArg (fun S : Set Plane => p + x ∈ S) hp
    simpa [IsPeriod, Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm] using hmem.symm
  · intro hp
    apply Set.ext
    intro x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add] using (hp (-p + x)).symm

theorem hasFiniteLocalComplexity_iff_hasFLC
    {V : Type*} [NormedAddCommGroup V] {T : Set V} :
    HasFiniteLocalComplexity T ↔ Tiling.Polygonal.HasFLC T :=
  Tiling.Polygonal.hasFLC_iff_finite_differences_on_bounded.symm

theorem hasFiniteLocalComplexity_mono
    {V : Type*} [NormedAddCommGroup V] {S T : Set V}
    (hT : HasFiniteLocalComplexity T) (hST : S ⊆ T) :
  HasFiniteLocalComplexity S := by
  intro B hB
  exact (hT B hB).subset
    (inter_subset_inter_left B (Set.sub_subset_sub hST hST))

end Tiling.AxisParallel.SetFormulation
