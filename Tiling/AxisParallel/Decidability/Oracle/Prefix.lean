import Tiling.AxisParallel.Decidability.Oracle.Execution
import Mathlib.Computability.Partrec

/-!
# Oracle programs with a finite query prefix

Run a fixed finite query schedule before handing the complete answer prefix and
the remaining history to a body program.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OraclePrefix

open Tiling.AxisParallel.Decidability

def defaultQuery : Query := (0, [], [])

def prefixStep (queries : List Query) (body : List Bool → List Bool → Bool ⊕ Query)
    (history : List Bool) : Bool ⊕ Query :=
  if history.length < queries.length then
    .inr (queries.getD history.length defaultQuery)
  else
    body (history.take queries.length) (history.drop queries.length)

def prefixProgram {α : Type*} (schedule : α → List Query)
    (body : α → List Bool → List Bool → Bool ⊕ Query)
    (input : α) (history : List Bool) : Bool ⊕ Query :=
  prefixStep (schedule input) (body input) history

theorem prefixProgram_computable {α : Type*} [Primcodable α]
    {schedule : α → List Query}
    {body : α → List Bool → List Bool → Bool ⊕ Query}
    (hschedule : Computable schedule)
    (hbody : Computable (fun x : α × (List Bool × List Bool) => body x.1 x.2.1 x.2.2)) :
    Computable₂ (prefixProgram schedule body) := by
  have hqueries : Computable (fun x : α × List Bool => schedule x.1) :=
    hschedule.comp Computable.fst
  have hqueryLength : Computable (fun x : α × List Bool => (schedule x.1).length) :=
    Computable.comp Computable.list_length hqueries
  have hhistoryLength : Computable (fun x : α × List Bool => x.2.length) :=
    Computable.comp Computable.list_length Computable.snd
  have hmore : Computable (fun x : α × List Bool => decide (x.2.length < (schedule x.1).length)) :=
    (Primrec.nat_lt.decide.to_comp).comp hhistoryLength hqueryLength
  have hindexQuery : Computable (fun x : α × List Bool =>
      (schedule x.1).getD x.2.length defaultQuery) :=
    (Primrec.list_getD defaultQuery).to_comp.comp hqueries hhistoryLength
  have htake : Computable (fun x : α × List Bool => x.2.take (schedule x.1).length) :=
    Computable₂.comp Primrec.list_take.to_comp hqueryLength Computable.snd
  have hdrop : Computable (fun x : α × List Bool => x.2.drop (schedule x.1).length) :=
    Computable₂.comp Primrec.list_drop.to_comp hqueryLength Computable.snd
  have hbodyInput : Computable (fun x : α × List Bool =>
      (x.1, (x.2.take (schedule x.1).length, x.2.drop (schedule x.1).length))) :=
    Computable.fst.pair (htake.pair hdrop)
  have hbodyResult : Computable (fun x : α × List Bool =>
      body x.1 (x.2.take (schedule x.1).length) (x.2.drop (schedule x.1).length)) :=
    hbody.comp hbodyInput
  refine (Computable.cond hmore (Computable.sumInr.comp hindexQuery) hbodyResult).to₂.of_eq ?_
  intro x
  rcases x with ⟨input, history⟩
  by_cases h : history.length < (schedule input).length
  · simp [prefixProgram, prefixStep, h]
  · simp [prefixProgram, prefixStep, h]

theorem prefixProgram_eq_body_of_length {α : Type*}
    (schedule : α → List Query) (body : α → List Bool → List Bool → Bool ⊕ Query)
    (input : α) (history : List Bool)
    (h : (schedule input).length ≤ history.length) :
    prefixProgram schedule body input history =
      body input (history.take (schedule input).length) (history.drop (schedule input).length) := by
  simp [prefixProgram, prefixStep, Nat.not_lt.mpr h]

private theorem run_congr {s t : List Bool → Bool ⊕ Query}
    (hstep : ∀ history, s history = t history) (answer : Query → Bool)
    (fuel : ℕ) (history : List Bool) :
    run s answer fuel history = run t answer fuel history := by
  induction fuel generalizing history with
  | zero => rfl
  | succ fuel ih =>
      rw [run, run, hstep history]
      split
      · rfl
      · rename_i query
        exact ih _

theorem run_after_complete_prefix {α : Type*}
    (schedule : α → List Query) (body : α → List Bool → List Bool → Bool ⊕ Query)
    (input : α) (answer : Query → Bool) (frozen suffix : List Bool)
    (hfrozen : frozen.length = (schedule input).length) (fuel : ℕ) :
    run (prefixProgram schedule body input) answer fuel (frozen ++ suffix) =
      run (body input frozen) answer fuel suffix := by
  induction fuel generalizing suffix with
  | zero => rfl
  | succ fuel ih =>
      rw [run, run]
      have hlen : (schedule input).length ≤ (frozen ++ suffix).length := by
        rw [List.length_append, hfrozen]
        omega
      rw [prefixProgram_eq_body_of_length schedule body input (frozen ++ suffix) hlen]
      have htake : (frozen ++ suffix).take (schedule input).length = frozen := by
        rw [← hfrozen]
        exact List.take_left
      have hdrop : (frozen ++ suffix).drop (schedule input).length = suffix := by
        rw [← hfrozen]
        exact List.drop_left
      rw [htake, hdrop]
      cases hbody : body input frozen suffix with
      | inl b => rfl
      | inr q =>
          simpa [List.append_assoc] using ih (suffix ++ [answer q])

private theorem run_after_scheduled_queries (queries : List Query)
    (body : List Bool → List Bool → Bool ⊕ Query) (answer : Query → Bool) :
    ∀ history remaining fuel,
      history.length + remaining = queries.length →
      history = (queries.take history.length).map answer →
      run (prefixStep queries body) answer (remaining + fuel) history =
        run (body (queries.map answer)) answer fuel [] := by
  intro history remaining
  induction remaining generalizing history with
  | zero =>
      intro fuel hlength hhistory
      have hhistory' : history = queries.map answer := by
        calc
          history = (queries.take history.length).map answer := hhistory
          _ = queries.map answer := by
            have hlen : history.length = queries.length := by omega
            rw [hlen]
            simp
      subst history
      have hcomplete :=
        run_after_complete_prefix (fun _ : Unit => queries) (fun _ => body) () answer
          (queries.map answer) [] (by simp) fuel
      have hcomplete' :
          run (prefixProgram (fun _ : Unit => queries) (fun _ => body) ()) answer fuel
            (queries.map answer) =
          run (body (queries.map answer)) answer fuel [] := by
        simpa using hcomplete
      have hsteps : ∀ history, prefixStep queries body history =
          prefixProgram (fun _ : Unit => queries) (fun _ => body) () history :=
        fun _ => rfl
      have hrun := run_congr hsteps answer fuel (queries.map answer)
      simpa using hrun.trans hcomplete'
  | succ remaining ih =>
      intro fuel hlength hhistory
      have hlt : history.length < queries.length := by omega
      have hquery : queries.getD history.length defaultQuery = queries[history.length] :=
        List.getD_eq_getElem _ _ hlt
      let q := queries[history.length]
      have hhistoryNext : history ++ [answer q] =
          (queries.take (history.length + 1)).map answer := by
        rw [hhistory, List.take_add_one, List.map_append]
        simp [q, List.getElem?_eq_getElem hlt,
          min_eq_left (Nat.le_of_lt hlt)]
      have hlengthNext : (history ++ [answer q]).length + remaining = queries.length := by
        simp only [List.length_append, List.length_singleton]
        omega
      rw [show Nat.succ remaining + fuel = Nat.succ (remaining + fuel) by omega]
      rw [run, prefixStep, if_pos hlt, hquery]
      have hstep :
          run (prefixStep queries body) answer (remaining + fuel)
            (history ++ [answer (queries[history.length])]) =
          run (body (queries.map answer)) answer fuel [] :=
        ih (history ++ [answer (queries[history.length])]) fuel hlengthNext ?_
      · exact hstep
      · simpa using hhistoryNext

theorem run_from_empty_after_schedule {α : Type*}
    (schedule : α → List Query) (body : α → List Bool → List Bool → Bool ⊕ Query)
    (input : α) (answer : Query → Bool) (fuel : ℕ) :
    run (prefixProgram schedule body input) answer ((schedule input).length + fuel) [] =
      run (body input ((schedule input).map answer)) answer fuel [] := by
  let queries := schedule input
  have h := run_after_scheduled_queries queries (body input) answer [] queries.length fuel
    (by simp) (by simp)
  change run (prefixStep queries (body input)) answer (queries.length + fuel) [] = _
  simpa [queries] using h

private theorem run_none_before_schedule_finishes (queries : List Query)
    (body : List Bool → List Bool → Bool ⊕ Query) (answer : Query → Bool) :
    ∀ fuel history, history.length + fuel < queries.length →
      run (prefixStep queries body) answer fuel history = none := by
  intro fuel
  induction fuel with
  | zero =>
      intro history _
      rfl
  | succ fuel ih =>
      intro history hlt
      have hquery : history.length < queries.length := by omega
      rw [run, prefixStep, if_pos hquery]
      change run (prefixStep queries body) answer fuel
        (history ++ [answer (queries.getD history.length defaultQuery)]) = none
      apply ih
      simp only [List.length_append, List.length_singleton]
      omega

theorem run_answer_after_schedule {α : Type*}
    (schedule : α → List Query) (body : α → List Bool → List Bool → Bool ⊕ Query)
    (input : α) (answer : Query → Bool) (fuel : ℕ) (b : Bool)
    (h : run (prefixProgram schedule body input) answer fuel [] = some b) :
    ∃ bodyFuel,
      run (body input ((schedule input).map answer)) answer bodyFuel [] = some b := by
  by_cases hlong : (schedule input).length ≤ fuel
  · obtain ⟨bodyFuel, rfl⟩ := Nat.exists_eq_add_of_le hlong
    exact ⟨bodyFuel, by simpa [run_from_empty_after_schedule] using h⟩
  · have hnone := run_none_before_schedule_finishes (schedule input) (body input) answer
      fuel [] (by simpa using Nat.not_le.mp hlong)
    rw [show prefixProgram schedule body input =
      prefixStep (schedule input) (body input) by rfl, hnone] at h
    cases h

end Tiling.AxisParallel.Decidability.OraclePrefix
