import Tiling.Geometry.Periodicity

/-!
# Finite local complexity from bounded difference sets

Finiteness of the differences in every bounded set already forces local
finiteness of the original set; no properness assumption is needed.
-/

set_option autoImplicit false

open Bornology Set
open scoped Pointwise

namespace Tiling.Polygonal

theorem locallyFinite_of_finite_differences
    {V : Type*} [NormedAddCommGroup V] {T : Set V}
    (hT : ∀ B : Set V, IsBounded B → ((T - T) ∩ B).Finite) (B : Set V) (hB : IsBounded B) :
    (T ∩ B).Finite := by
  classical
  by_cases hnonempty : T.Nonempty
  · obtain ⟨t, ht⟩ := hnonempty
    have hfinite := hT ((-t) +ᵥ B) (hB.vadd (-t))
    apply (hfinite.image fun d : V => d + t).subset
    rintro x ⟨hxT, hxB⟩
    refine ⟨x - t, ⟨⟨x, hxT, t, ht, rfl⟩, ?_⟩, sub_add_cancel x t⟩
    refine ⟨x, hxB, ?_⟩
    change -t + x = x - t
    abel
  · rw [Set.not_nonempty_iff_eq_empty.mp hnonempty, Set.empty_inter]
    exact Set.finite_empty

theorem hasFLC_iff_finite_differences_on_bounded
    {V : Type*} [NormedAddCommGroup V] {T : Set V} :
    HasFLC T ↔ ∀ B : Set V, IsBounded B → ((T - T) ∩ B).Finite := by
  constructor
  · exact HasFLC.differences_locallyFinite
  · intro hT
    exact ⟨locallyFinite_of_finite_differences hT,
      fun R _ => hT _ Metric.isBounded_closedBall⟩

end Tiling.Polygonal
