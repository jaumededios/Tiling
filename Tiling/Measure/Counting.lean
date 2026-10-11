import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Count

set_option linter.style.header false

/-!
# Canonical counting measures for integer lattices

For this project, `ℤ` carries counting measure as its canonical `volume`.  The canonical measure on
`Fin n → ℤ` is then obtained from Mathlib's finite-product `MeasureSpace` instance.  We prove that
this product measure is equal to counting measure on the product.

Mathlib does not currently install the base `MeasureSpace ℤ` instance globally.  Keeping it and
the associated bridge instances in this small module isolates that project-level choice and the
declarations that may later be proposed for Mathlib.
-/

open MeasureTheory

namespace Tiling

noncomputable section

/-- Counting measure as the canonical measure on `ℤ`. -/
noncomputable instance instMeasureSpaceInt : MeasureSpace ℤ :=
  ⟨Measure.count⟩

/-- The canonical measure on `ℤ` inherits sigma-finiteness from counting measure. -/
instance instSigmaFiniteIntVolume : SigmaFinite (volume : Measure ℤ) := by
  change SigmaFinite (Measure.count : Measure ℤ)
  infer_instance

/-- The canonical measure on `ℤ` inherits translation invariance from counting measure. -/
instance instIsAddLeftInvariantIntVolume :
    (volume : Measure ℤ).IsAddLeftInvariant := by
  change (Measure.count : Measure ℤ).IsAddLeftInvariant
  infer_instance

/-- A finite product of counting measures is counting measure on the product. -/
theorem Measure.pi_count {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)] [∀ i, MeasurableSingletonClass (α i)]
    [∀ i, Countable (α i)] :
    Measure.pi (fun i ↦ (Measure.count : Measure (α i))) =
      (Measure.count : Measure (∀ i, α i)) := by
  apply Measure.ext_of_singleton
  intro f
  rw [Measure.pi_singleton]
  simp

/-- The product `volume` on the integer lattice `Fin n → ℤ` is counting measure. -/
theorem volume_piFin_int_eq_count (n : ℕ) :
    (volume : Measure (Fin n → ℤ)) = Measure.count := by
  change Measure.pi (fun _ : Fin n ↦ (Measure.count : Measure ℤ)) = Measure.count
  exact Measure.pi_count

end

end Tiling
