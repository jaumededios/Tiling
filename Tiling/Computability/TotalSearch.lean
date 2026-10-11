import Mathlib.Computability.RE

/-!
# Totalized search over a bounded partial certificate oracle

This module isolates the generic computability step used by effective
certificate searches. The validity test controls whether a search is run;
on valid inputs, an eventual successful bounded query guarantees that the
partial `rfindOpt` search terminates.
-/

set_option autoImplicit false

namespace Tiling.Computability

variable {α : Type*} [Primcodable α]

/-- A valid input eventually has a successful bounded query. -/
def BoundedSearchHalts (valid : α → Bool) (bounded : α → ℕ → Option Bool) : Prop :=
  ∀ a, valid a = true → ∃ n b, bounded a n = some b

/-- The partial search, totalized by returning `false` on invalid inputs. -/
def totalSearchPart (valid : α → Bool) (bounded : α → ℕ → Option Bool) : α →. Bool :=
  fun a => if valid a then Nat.rfindOpt (bounded a) else Part.some false

/-- The first successful result on valid inputs, and `false` on invalid inputs. -/
noncomputable def totalSearch (valid : α → Bool) (bounded : α → ℕ → Option Bool)
    (halts : BoundedSearchHalts valid bounded) (a : α) : Bool := by
  by_cases hv : valid a = true
  · exact (Nat.rfindOpt (bounded a)).get (Nat.rfindOpt_dom.mpr (by
      obtain ⟨n, b, hb⟩ := halts a hv
      exact ⟨n, b, by rw [hb]; simp⟩))
  · exact false

/- Every totalized successful result comes from a bounded query. -/
omit [Primcodable α] in
theorem totalSearch_mem_rfindOpt (valid : α → Bool) (bounded : α → ℕ → Option Bool)
    (halts : BoundedSearchHalts valid bounded) (a : α) (hv : valid a = true) :
    totalSearch valid bounded halts a ∈ Nat.rfindOpt (bounded a) := by
  simp only [totalSearch, dif_pos hv]
  exact Part.get_mem _

omit [Primcodable α] in
/-- On a valid input, the chosen result is witnessed by a bounded stage. -/
theorem totalSearch_sound (valid : α → Bool) (bounded : α → ℕ → Option Bool)
    (halts : BoundedSearchHalts valid bounded) (a : α) (hv : valid a = true) :
    ∃ n, totalSearch valid bounded halts a ∈ bounded a n :=
  Nat.rfindOpt_spec (totalSearch_mem_rfindOpt valid bounded halts a hv)

/-- Bounded totalization preserves the computability of the validity test and oracle. -/
theorem computable_totalSearch (valid : α → Bool) (bounded : α → ℕ → Option Bool)
    (hvalid : Computable valid) (hbounded : Computable₂ bounded)
    (halts : BoundedSearchHalts valid bounded) :
    Computable (totalSearch valid bounded halts) := by
  have hsearch : Partrec fun a : α => Nat.rfindOpt (bounded a) :=
    Partrec.rfindOpt hbounded
  have hdefault : Partrec fun _ : α => Part.some false := Partrec.const' (Part.some false)
  have hpartial : Partrec (totalSearchPart valid bounded) :=
    (Partrec.cond hvalid hsearch hdefault).of_eq fun a => by
      simp [totalSearchPart]
  apply Partrec.of_eq_tot hpartial
  intro a
  by_cases hv : valid a = true
  · have hm := totalSearch_mem_rfindOpt valid bounded halts a hv
    simpa [totalSearchPart, totalSearch, hv] using hm
  · simp [totalSearchPart, totalSearch, hv]

end Tiling.Computability
