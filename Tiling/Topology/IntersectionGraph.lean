import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyFinite

set_option linter.style.header false

/-!
# Intersection graphs of locally finite closed covers

The intersection graph of a locally finite nonempty closed cover of a connected space is
connected.  This topological lemma is independent of tilings; plate carriers are its first
consumer.
-/

open Set

namespace LocallyFinite

universe u v

variable {X : Type u} {ι : Type v} [TopologicalSpace X] {f : ι → Set X}

/-- A locally finite union of regular-closed sets is regular closed. -/
theorem closure_interior_iUnion_eq (hlocal : LocallyFinite f)
    (hregular : ∀ i, closure (interior (f i)) = f i) :
    closure (interior (⋃ i, f i)) = ⋃ i, f i := by
  have hclosed : ∀ i, IsClosed (f i) := fun i ↦ by
    rw [← hregular i]
    exact isClosed_closure
  apply subset_antisymm
  · exact closure_minimal interior_subset (hlocal.isClosed_iUnion hclosed)
  · rw [iUnion_subset_iff]
    intro i
    rw [← hregular i]
    exact closure_mono (interior_mono (subset_iUnion f i))

end LocallyFinite

namespace SimpleGraph

universe u v

variable {X : Type u} {ι : Type v}

/-- The graph whose distinct indices are adjacent when their sets intersect. -/
def intersectionGraph (s : ι → Set X) : SimpleGraph ι :=
  SimpleGraph.fromRel fun i j ↦ (s i ∩ s j).Nonempty

/-- Adjacency in an intersection graph is distinctness together with nonempty intersection. -/
@[simp]
theorem intersectionGraph_adj (s : ι → Set X) (i j : ι) :
    (intersectionGraph s).Adj i j ↔ i ≠ j ∧ (s i ∩ s j).Nonempty := by
  rw [intersectionGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hij, hij' | hji'⟩
    · exact ⟨hij, hij'⟩
    · exact ⟨hij, by simpa [inter_comm] using hji'⟩
  · rintro ⟨hij, hnonempty⟩
    exact ⟨hij, Or.inl hnonempty⟩

variable [TopologicalSpace X]

/-- The intersection graph of a locally finite family of nonempty closed sets covering a connected
space is connected. -/
theorem connected_intersectionGraph [ConnectedSpace X]
    (s : ι → Set X) (hs : _root_.LocallyFinite s)
    (hsc : ∀ i, IsClosed (s i)) (hsn : ∀ i, (s i).Nonempty)
    (hcover : ⋃ i, s i = Set.univ) :
    (intersectionGraph s).Connected := by
  classical
  let G := intersectionGraph s
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  have hx : x ∈ ⋃ i, s i := by rw [hcover]; exact mem_univ x
  simp only [mem_iUnion] at hx
  obtain ⟨root, _⟩ := hx
  rw [connected_iff_exists_forall_reachable]
  refine ⟨root, fun j ↦ ?_⟩
  by_contra hj
  let I : Set ι := {i | G.Reachable root i}
  let U : Set X := ⋃ i : I, s i
  let W : Set X := ⋃ i : {i // i ∉ I}, s i
  have hUclosed : IsClosed U := by
    exact (hs.comp_injective Subtype.val_injective).isClosed_iUnion fun i ↦ hsc i
  have hWclosed : IsClosed W := by
    exact (hs.comp_injective Subtype.val_injective).isClosed_iUnion fun i ↦ hsc i
  have hUW : U ∪ W = Set.univ := by
    rw [← hcover]
    apply subset_antisymm
    · intro y hy
      rcases hy with hy | hy
      · simp only [U, mem_iUnion] at hy
        obtain ⟨i, hyi⟩ := hy
        exact mem_iUnion_of_mem i.1 hyi
      · simp only [W, mem_iUnion] at hy
        obtain ⟨i, hyi⟩ := hy
        exact mem_iUnion_of_mem i.1 hyi
    · intro y hy
      simp only [mem_iUnion] at hy
      obtain ⟨i, hyi⟩ := hy
      by_cases hi : i ∈ I
      · left
        exact mem_iUnion_of_mem ⟨i, hi⟩ hyi
      · right
        exact mem_iUnion_of_mem ⟨i, hi⟩ hyi
  have hdisj : Disjoint U W := by
    rw [Set.disjoint_left]
    intro y hyU hyW
    simp only [U, mem_iUnion] at hyU
    simp only [W, mem_iUnion] at hyW
    obtain ⟨i, hyi⟩ := hyU
    obtain ⟨k, hyk⟩ := hyW
    have hik : i.1 ≠ k.1 := by
      intro h
      apply k.2
      rw [← h]
      exact i.2
    have hadj : G.Adj i.1 k.1 := by
      rw [show G = intersectionGraph s from rfl, intersectionGraph_adj]
      exact ⟨hik, ⟨y, hyi, hyk⟩⟩
    exact k.2 (i.2.trans hadj.reachable)
  have hcompl : Uᶜ = W := by
    ext y
    constructor
    · intro hy
      have hy' : y ∈ U ∪ W := by rw [hUW]; exact mem_univ y
      rcases hy' with hyU | hyW
      · exact (hy hyU).elim
      · exact hyW
    · intro hyW hyU
      exact Set.disjoint_left.1 hdisj hyU hyW
  have hUopen : IsOpen U := by
    rw [← compl_compl U, hcompl]
    exact hWclosed.isOpen_compl
  have hUne : U.Nonempty := by
    obtain ⟨y, hy⟩ := hsn root
    exact ⟨y, mem_iUnion_of_mem ⟨root, Reachable.refl root⟩ hy⟩
  have hUuniv : U = Set.univ :=
    (show IsClopen U from ⟨hUclosed, hUopen⟩).eq_univ hUne
  obtain ⟨y, hy⟩ := hsn j
  have hyW : y ∈ W := mem_iUnion_of_mem ⟨j, hj⟩ hy
  have hyU : y ∈ U := by rw [hUuniv]; exact mem_univ y
  exact Set.disjoint_left.1 hdisj hyU hyW

end SimpleGraph
