import Mathlib.Order.Partition.Finpartition
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Card

/-!
# Finite partitions from indexed set covers

An indexed disjoint cover may contain empty or repeated sets. The construction
keeps exactly the distinct nonempty members and provides their enumeration.
-/

set_option autoImplicit false

open Set

noncomputable section

namespace Tiling.Combinatorics.FiniteSetPartitions

variable {α : Type*}

/-- Enumerate each member of a finite set exactly once. -/
def enumerate (parts : Finset (Set α)) : Fin parts.card → Set α :=
  fun i => (parts.equivFin.symm i : Set α)

theorem enumerate_mem (parts : Finset (Set α)) (i : Fin parts.card) :
    enumerate parts i ∈ parts :=
  (parts.equivFin.symm i).property

theorem enumerate_injective (parts : Finset (Set α)) :
    Function.Injective (enumerate parts) := by
  intro i j h
  exact parts.equivFin.symm.injective (Subtype.ext h)

theorem iUnion_enumerate (parts : Finset (Set α)) :
    (⋃ i, enumerate parts i) = ⋃₀ parts := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    exact Set.mem_sUnion.mpr ⟨enumerate parts i, enumerate_mem parts i, hx⟩
  · rintro ⟨S, hS, hx⟩
    apply Set.mem_iUnion.mpr
    refine ⟨parts.equivFin ⟨S, hS⟩, ?_⟩
    simpa [enumerate] using hx

/-- Keep the distinct nonempty members of an indexed family. -/
def nonemptyPieces {n : ℕ} (part : Fin n → Set α) : Finset (Set α) := by
  classical
  exact (Finset.univ.image part).filter Set.Nonempty

theorem mem_nonemptyPieces {n : ℕ} (part : Fin n → Set α) (S : Set α) :
    S ∈ nonemptyPieces part ↔ (∃ i, part i = S) ∧ S.Nonempty := by
  classical
  simp [nonemptyPieces]

theorem sUnion_nonemptyPieces {n : ℕ} (part : Fin n → Set α) :
    ⋃₀ (nonemptyPieces part) = ⋃ i, part i := by
  classical
  ext x
  constructor
  · rintro ⟨S, hS, hx⟩
    obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  · intro hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_sUnion.mpr ⟨part i,
      (mem_nonemptyPieces part (part i)).mpr ⟨⟨i, rfl⟩, ⟨x, hxi⟩⟩, hxi⟩

theorem pairwiseDisjoint_nonemptyPieces {n : ℕ} (part : Fin n → Set α)
    (hdis : Set.PairwiseDisjoint Set.univ part) :
    (nonemptyPieces part : Set (Set α)).PairwiseDisjoint id := by
  classical
  intro S hS U hU hne
  obtain ⟨⟨i, rfl⟩, _⟩ := (mem_nonemptyPieces part S).mp hS
  obtain ⟨⟨j, rfl⟩, _⟩ := (mem_nonemptyPieces part U).mp hU
  exact hdis (Set.mem_univ _) (Set.mem_univ _) (fun hij => hne (congrArg part hij))

theorem sup_nonemptyPieces {A : Set α} {n : ℕ} (part : Fin n → Set α)
    (hcover : (⋃ i, part i) = A) :
    (nonemptyPieces part).sup id = A := by
  classical
  calc
    (nonemptyPieces part).sup id = ⋃₀ (nonemptyPieces part) :=
      Finset.sup_id_set_eq_sUnion _
    _ = ⋃ i, part i := sUnion_nonemptyPieces part
    _ = A := hcover

/-- An indexed disjoint cover gives a canonical finite partition. -/
def finpartitionOfIndexed {A : Set α} {n : ℕ} (part : Fin n → Set α)
    (hdis : Set.PairwiseDisjoint Set.univ part) (hcover : (⋃ i, part i) = A) :
    Finpartition A := by
  classical
  exact (Finpartition.ofPairwiseDisjoint (nonemptyPieces part)
    (pairwiseDisjoint_nonemptyPieces part hdis)).copy (sup_nonemptyPieces part hcover)

theorem finpartitionOfIndexed_parts {A : Set α} {n : ℕ}
    (part : Fin n → Set α) (hdis : Set.PairwiseDisjoint Set.univ part)
    (hcover : (⋃ i, part i) = A) :
    (finpartitionOfIndexed part hdis hcover).parts = nonemptyPieces part := by
  classical
  simp [finpartitionOfIndexed, Finpartition.ofPairwiseDisjoint,
    Finset.erase_eq_of_notMem, mem_nonemptyPieces]

theorem finpartitionParts_nonempty {A : Set α} (P : Finpartition A)
    (S : Set α) (hS : S ∈ P.parts) : S.Nonempty := by
  exact Set.nonempty_iff_ne_empty.mpr (P.ne_bot hS)

end Tiling.Combinatorics.FiniteSetPartitions
