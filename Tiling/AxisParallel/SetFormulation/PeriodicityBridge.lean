import Tiling.AxisParallel.SetFormulation.Basic
import Tiling.Combinatorics.Finpartition
import Tiling.Geometry.Periodicity
import Tiling.RationalPolygonal.Basic

/-!
# Periodicity and finite partitions

The indexed weak-periodicity witness may include empty or repeated pieces.
These equivalences express weak periodicity using `Finpartition`.
-/

set_option autoImplicit false

open Set
open scoped Pointwise

noncomputable section

open Tiling.Combinatorics.FiniteSetPartitions

namespace Tiling.AxisParallel.SetFormulation

/-- Two independent exact periods generate a planar lattice of periods. -/
theorem isDoublyPeriodic_iff_isLatticePeriodic (A : Set Plane) :
    IsDoublyPeriodic A ↔ Tiling.Polygonal.IsLatticePeriodic A := by
  constructor
  · rintro ⟨p, q, hind, hp, hq⟩
    let L : Tiling.Polygonal.PlanarLattice := ⟨![p, q], hind⟩
    refine ⟨L, ?_⟩
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact (isPeriod_iff_mem_periodGroup A p).mp hp
    · exact (isPeriod_iff_mem_periodGroup A q).mp hq
  · rintro ⟨L, hL⟩
    have hbasis : ![L.basis 0, L.basis 1] = L.basis := by
      ext i
      fin_cases i <;> rfl
    refine ⟨L.basis 0, L.basis 1, hbasis.symm ▸ L.independent, ?_, ?_⟩
    · exact (isPeriod_iff_mem_periodGroup A _).mpr
        (hL (AddSubgroup.subset_closure (Set.mem_range_self 0)))
    · exact (isPeriod_iff_mem_periodGroup A _).mpr
        (hL (AddSubgroup.subset_closure (Set.mem_range_self 1)))

theorem isPeriod_iff_setPeriodicBy (A : Set Plane) (p : Plane) :
    IsPeriod A p ↔ Tiling.RationalPolygonal.SetPeriodicBy A p := by
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

theorem weaklyPeriodic_iff_production (A : Set Plane) :
    WeaklyPeriodic A ↔ Tiling.RationalPolygonal.WeaklyPeriodic A := by
  rw [WeaklyPeriodic]
  constructor
  · rintro ⟨P, hperiod⟩
    classical
    let part : Fin P.parts.card → Set Plane := enumerate P.parts
    have hmem : ∀ i, part i ∈ P.parts := fun i => enumerate_mem P.parts i
    have hnonempty : ∀ i, (part i).Nonempty := fun i =>
      finpartitionParts_nonempty P (part i) (hmem i)
    have hdis : Set.PairwiseDisjoint Set.univ part := by
      intro i _ j _ hij
      exact P.disjoint (hmem i) (hmem j) (fun heq => hij (enumerate_injective P.parts heq))
    have hcover : (⋃ i, part i) = A := by
      rw [iUnion_enumerate]
      simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
    choose period hne hp using fun i => hperiod (part i) (hmem i)
    refine ⟨⟨P.parts.card, part, period, hne, ?_, hdis, hcover⟩⟩
    intro i
    exact (isPeriod_iff_setPeriodicBy (part i) (period i)).mp (hp i)
  · rintro ⟨D⟩
    refine ⟨finpartitionOfIndexed D.part D.pairwiseDisjoint D.iUnion_parts, ?_⟩
    intro S hS
    classical
    have hS' : S ∈ nonemptyPieces D.part := by
      rw [← finpartitionOfIndexed_parts D.part D.pairwiseDisjoint D.iUnion_parts]
      exact hS
    obtain ⟨⟨i, hi⟩, _⟩ := (mem_nonemptyPieces D.part S).mp hS'
    subst S
    exact ⟨D.period i, D.period_ne_zero i,
      (isPeriod_iff_setPeriodicBy (D.part i) (D.period i)).mpr (D.periodic_part i)⟩

theorem quasiPeriodic_iff_production (A : Set Plane) :
    QuasiPeriodic A ↔ Tiling.Polygonal.IsQuasiPeriodic A := by
  rw [QuasiPeriodic]
  constructor
  · rintro ⟨P, hperiod⟩
    classical
    let part : Fin P.parts.card → Set Plane := enumerate P.parts
    have hmem : ∀ i, part i ∈ P.parts := fun i => enumerate_mem P.parts i
    have hnonempty : ∀ i, (part i).Nonempty := fun i =>
      finpartitionParts_nonempty P (part i) (hmem i)
    have hdis : Set.PairwiseDisjoint Set.univ part := by
      intro i _ j _ hij
      exact P.disjoint (hmem i) (hmem j) (fun heq => hij (enumerate_injective P.parts heq))
    have hcover : (⋃ i, part i) = A := by
      rw [iUnion_enumerate]
      simpa only [Finset.sup_id_set_eq_sUnion] using P.sup_parts
    refine ⟨P.parts.card, part, ?_, hdis, hcover⟩
    intro i
    exact ⟨hnonempty i,
      (isDoublyPeriodic_iff_isLatticePeriodic _).mp (hperiod (part i) (hmem i))⟩
  · rintro ⟨n, part, hperiod, hdis, hcover⟩
    refine ⟨finpartitionOfIndexed part hdis hcover, ?_⟩
    intro S hS
    classical
    have hS' : S ∈ nonemptyPieces part := by
      rw [← finpartitionOfIndexed_parts part hdis hcover]
      exact hS
    obtain ⟨⟨i, hi⟩, _⟩ := (mem_nonemptyPieces part S).mp hS'
    subst S
    exact (isDoublyPeriodic_iff_isLatticePeriodic _).mpr (hperiod i).2

end Tiling.AxisParallel.SetFormulation
