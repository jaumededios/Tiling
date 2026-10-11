import Tiling.AxisParallel.Decidability.Oracle.Execution
import Mathlib.Computability.Partrec

/-!
# Computability of bounded oracle execution

A computable history-step program and computable query answers give a computable
bounded simulation. Both may depend on the same encoded input. Execution is
iterated through finite data rather than a function-valued recursion state.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleRun

private abbrev State := Bool ⊕ List Bool

private def advance {α : Type*} (program : α → List Bool → Bool ⊕ Query)
    (answer : α → Query → Bool) (input : α) : State → State
  | .inl b => .inl b
  | .inr history =>
    match program input history with
    | .inl b => .inl b
    | .inr q => .inr (history ++ [answer input q])

private def trace {α : Type*} (program : α → List Bool → Bool ⊕ Query)
    (answer : α → Query → Bool) (input : α) (initial : List Bool) : ℕ → State
  | 0 => .inr initial
  | n + 1 => advance program answer input (trace program answer input initial n)

private def result : State → Option Bool
  | .inl b => some b
  | .inr _ => none

private theorem advance_computable {α : Type*} [Primcodable α]
    {program : α → List Bool → Bool ⊕ Query} {answer : α → Query → Bool}
    (hprogram : Computable₂ program) (hanswer : Computable₂ answer) :
    Computable₂ (advance program answer) := by
  have hhistory : Computable₂ (fun x : α × State => fun history : List Bool =>
      match program x.1 history with
      | .inl b => Sum.inl b
      | .inr q => Sum.inr (history ++ [answer x.1 q])) := by
    refine (Computable.sumCasesOn
      (hprogram.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.sumInl.comp Computable.snd).to₂
      (Computable.sumInr.comp (Computable.list_concat.comp
        (Computable.snd.comp Computable.fst)
        (hanswer.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
          Computable.snd))).to₂).of_eq ?_
    intro x
    dsimp only
    cases program x.1.1 x.2 <;> rfl
  refine (Computable.sumCasesOn Computable.snd
    (Computable.sumInl.comp Computable.snd).to₂ hhistory).of_eq ?_
  intro x
  cases x.2 <;> rfl

private theorem trace_computable {α : Type*} [Primcodable α]
    {program : α → List Bool → Bool ⊕ Query} {answer : α → Query → Bool}
    (hprogram : Computable₂ program) (hanswer : Computable₂ answer) :
    Computable (fun x : α × ℕ × List Bool => trace program answer x.1 x.2.2 x.2.1) := by
  have hrec := Computable.nat_rec
    (Computable.fst.comp Computable.snd : Computable (fun x : α × ℕ × List Bool => x.2.1))
    (Computable.sumInr.comp (Computable.snd.comp Computable.snd))
    ((advance_computable hprogram hanswer).comp
      (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.snd)).to₂
  refine hrec.of_eq ?_
  intro x
  induction x.2.1 with
  | zero => rfl
  | succ n ih => simp only [trace, ih]

private theorem result_computable : Computable result := by
  refine (Computable.sumCasesOn Computable.id
    (Computable.option_some.comp Computable.snd).to₂ (Computable.const none).to₂).of_eq ?_
  intro state
  cases state <;> rfl

private theorem trace_eq_iterate {α : Type*} (program : α → List Bool → Bool ⊕ Query)
    (answer : α → Query → Bool) (input : α) (history : List Bool) (fuel : ℕ) :
    trace program answer input history fuel =
      (advance program answer input)^[fuel] (.inr history) := by
  induction fuel with
  | zero => rfl
  | succ n ih => rw [trace, ih, Function.iterate_succ_apply']

private theorem iterate_result_eq_run {α : Type*}
    (program : α → List Bool → Bool ⊕ Query) (answer : α → Query → Bool)
    (input : α) (fuel : ℕ) : ∀ history,
    result ((advance program answer input)^[fuel] (.inr history)) =
      run (program input) (answer input) fuel history := by
  induction fuel with
  | zero => intro history; rfl
  | succ n ih =>
      intro history
      rw [Function.iterate_succ_apply]
      cases h : program input history with
      | inl b =>
          have hfixed : advance program answer input (.inl b) = .inl b := rfl
          simp only [advance, h, Function.iterate_fixed hfixed, result, run]
      | inr q =>
          simpa only [advance, h, run] using ih (history ++ [answer input q])

/-- The existing bounded `run` is computable uniformly in encoded inputs, fuel,
and the initial Boolean history. This theorem does not assume that the program halts. -/
theorem run_computable {α : Type*} [Primcodable α]
    {program : α → List Bool → Bool ⊕ Query} {answer : α → Query → Bool}
    (hprogram : Computable₂ program) (hanswer : Computable₂ answer) :
    Computable (fun x : α × ℕ × List Bool => run (program x.1) (answer x.1) x.2.1 x.2.2) := by
  refine (result_computable.comp (trace_computable hprogram hanswer)).of_eq ?_
  intro x
  rw [trace_eq_iterate]
  exact iterate_result_eq_run program answer x.1 x.2.1 x.2.2

/-- Bounded execution from empty history is computable in input and fuel. -/
theorem run_from_empty_computable {α : Type*} [Primcodable α]
    {program : α → List Bool → Bool ⊕ Query} {answer : α → Query → Bool}
    (hprogram : Computable₂ program) (hanswer : Computable₂ answer) :
    Computable₂ (fun input fuel => run (program input) (answer input) fuel []) :=
  (run_computable hprogram hanswer).comp
    (Computable.fst.pair (Computable.snd.pair (Computable.const [])))

end Tiling.AxisParallel.Decidability.OracleRun
