import Tiling.AxisParallel.Decidability.Search.Frontend
import Tiling.AxisParallel.Decidability.RectangleInput.LocalBound
import Tiling.AxisParallel.Decidability.Oracle.Prefix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput

abbrev RuntimeInput := TableInput × List Bool

def gridSchedule (count : ℕ) : List Query := comparisonQueries (2 * count)

def boundSchedule (input : TableInput) : List Query := LocalBound.queries (packedRegion input)

/-- The second finite prefix records local-bound comparisons before certificate replay. -/
def afterGrid (body : RuntimeInput → List Bool → Bool ⊕ Query) (count : ℕ)
    (gridHistory suffix : List Bool) : Bool ⊕ Query :=
  OraclePrefix.prefixProgram boundSchedule
    (fun input boundHistory history => body (input, boundHistory) history)
    (count, gridHistory) suffix

/-- The uniform rectangle input performs both finite query prefixes before search. -/
def withPrefixes (body : RuntimeInput → List Bool → Bool ⊕ Query) : OracleCode :=
  OraclePrefix.prefixProgram gridSchedule (afterGrid body)

/-- The proof-layer input obtained from the actual corner oracle's finite answers. -/
def oracleInput (count : ℕ) (answer : Query → Bool) : RuntimeInput :=
  let input : TableInput := (count, comparisonHistory (2 * count) answer)
  (input, LocalBound.history (packedRegion input) answer)

theorem gridSchedule_computable : Computable gridSchedule :=
  comparisonQueries_primrec.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id)

theorem boundSchedule_computable : Computable boundSchedule :=
  LocalBound.queries_primrec.to_comp.comp packedRegion_primrec.to_comp

/-- Both prefix phases are effective uniformly in any effective certificate replay body. -/
theorem withPrefixes_computable {body : RuntimeInput → List Bool → Bool ⊕ Query}
    (hb : Computable₂ body) : Computable₂ (withPrefixes body) := by
  have hinner : Computable₂ (OraclePrefix.prefixProgram boundSchedule
      (fun input boundHistory history => body (input, boundHistory) history)) :=
    OraclePrefix.prefixProgram_computable boundSchedule_computable
      (hb.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))
  exact OraclePrefix.prefixProgram_computable gridSchedule_computable
    (hinner.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd))

/-- After both finite prefixes, replay is exactly the supplied search body. -/
theorem run_withPrefixes (body : RuntimeInput → List Bool → Bool ⊕ Query)
    (count : ℕ) (answer : Query → Bool) (fuel : ℕ) :
    run (withPrefixes body count) answer
      ((gridSchedule count).length +
        (boundSchedule (oracleInput count answer).1).length + fuel) [] =
      run (body (oracleInput count answer)) answer fuel [] := by
  rw [Nat.add_assoc]
  rw [withPrefixes, OraclePrefix.run_from_empty_after_schedule]
  change run (OraclePrefix.prefixProgram boundSchedule
    (fun input boundHistory history => body (input, boundHistory) history)
    (count, comparisonHistory (2 * count) answer)) answer
    ((boundSchedule (count, comparisonHistory (2 * count) answer)).length + fuel) [] = _
  rw [OraclePrefix.run_from_empty_after_schedule]
  rfl

/-- Every answer from the uniform program comes from its actual post-prefix search. -/
theorem run_withPrefixes_answer (body : RuntimeInput → List Bool → Bool ⊕ Query)
    (count : ℕ) (answer : Query → Bool) (fuel : ℕ) (b : Bool)
    (h : run (withPrefixes body count) answer fuel [] = some b) :
    ∃ bodyFuel, run (body (oracleInput count answer)) answer bodyFuel [] = some b := by
  obtain ⟨gridFuel, hgrid⟩ := OraclePrefix.run_answer_after_schedule
    gridSchedule (afterGrid body) count answer fuel b h
  exact OraclePrefix.run_answer_after_schedule boundSchedule
    (fun input boundHistory history => body (input, boundHistory) history)
    (count, comparisonHistory (2 * count) answer) answer gridFuel b hgrid

/-- Finite search completeness and soundness transfer through both query prefixes. -/
theorem withPrefixes_correct (body : RuntimeInput → List Bool → Bool ⊕ Query)
    (count : ℕ) (answer : Query → Bool) (P : Bool → Prop)
    (hc : ∃ fuel b, run (body (oracleInput count answer)) answer fuel [] = some b)
    (hs : ∀ fuel b, run (body (oracleInput count answer)) answer fuel [] = some b → P b) :
    (∃ fuel b, run (withPrefixes body count) answer fuel [] = some b) ∧
      ∀ fuel b, run (withPrefixes body count) answer fuel [] = some b → P b := by
  constructor
  · obtain ⟨fuel, b, hf⟩ := hc
    exact ⟨_, b, (run_withPrefixes body count answer fuel).trans hf⟩
  · intro fuel b hf
    obtain ⟨bodyFuel, hb⟩ := run_withPrefixes_answer body count answer fuel b hf
    exact hs bodyFuel b hb

end Tiling.AxisParallel.Decidability.OracleDecision
