import Tiling.AxisParallel.Decidability.Oracle.Execution
import Mathlib.Computability.Partrec

/-!
# Replay of finite oracle stages

A packed tree stores its two children explicitly. At an unsuccessful stage leaf
replay asks a dummy query before proceeding to the next stage. Consequently every
stage transition consumes a history bit, including for malformed stage data.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleReplay

abbrev Node := Option Bool ⊕ (Query × ℕ × ℕ)
abbrev Code := List Node
abbrev State := ℕ × ℕ

/-- The ignored query at an unsuccessful stage leaf. -/
def tick : Query := (0, [], [])

/-- The postorder root; an empty code is an unsuccessful stage. -/
def root (code : Code) : ℕ := code.length - 1

def node (code : Code) (index : ℕ) : Node := code.getD index (.inl none)

/-- Query children must precede their parent in the packed list. -/
def WellFormed (code : Code) : Prop :=
  ∀ index q left right, node code index = .inr (q, left, right) →
    left < index ∧ right < index

private def nodeAdvance (x : State × Bool × ℕ) : Node → State
  | .inl none => (x.1.1 + 1, x.2.2)
  | .inl (some _) => x.1
  | .inr (_, left, right) => (x.1.1, cond x.2.1 right left)

private def nodeOutput : Node → Bool ⊕ Query
  | .inl none => .inr tick
  | .inl (some b) => .inl b
  | .inr (q, _, _) => .inr q

private theorem nodeAdvance_primrec : Primrec₂ nodeAdvance := by
  have hleaf : Primrec₂ (fun x : State × Bool × ℕ => fun o : Option Bool =>
      match o with
      | none => (x.1.1 + 1, x.2.2)
      | some _ => x.1) := by
    refine (Primrec.option_casesOn Primrec.snd
      ((Primrec.nat_add.comp
        (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 1)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).to₂).of_eq ?_
    intro x
    cases x.2 <;> rfl
  have hquery : Primrec₂ (fun x : State × Bool × ℕ =>
      fun y : Query × ℕ × ℕ => (x.1.1, cond x.2.1 y.2.2 y.2.1)) :=
    (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.cond (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  refine (Primrec.sumCasesOn Primrec.snd
    (hleaf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (hquery.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).of_eq ?_
  intro x
  cases x.2 with
  | inl o => cases o <;> rfl
  | inr q => rfl

private theorem nodeOutput_primrec : Primrec nodeOutput := by
  have hleaf : Primrec₂ (fun _ : Node => fun o : Option Bool =>
      match o with
      | none => Sum.inr tick
      | some b => Sum.inl b) := by
    refine (Primrec.option_casesOn Primrec.snd (Primrec.const (.inr tick))
      (Primrec.sumInl.comp Primrec.snd).to₂).of_eq ?_
    intro x
    cases x.2 <;> rfl
  refine (Primrec.sumCasesOn Primrec.id hleaf
    (Primrec.sumInr.comp (Primrec.fst.comp Primrec.snd)).to₂).of_eq ?_
  intro x
  cases x with
  | inl o => cases o <;> rfl
  | inr q => rfl

/-- Replaying one supplied bit is total for all codes and histories. -/
def advance {α : Type*} (stages : α → ℕ → Code) (input : α)
    (state : State) (bit : Bool) : State :=
  nodeAdvance (state, bit, root (stages input (state.1 + 1)))
    (node (stages input state.1) state.2)

def initial {α : Type*} (stages : α → ℕ → Code) (input : α) : State :=
  (0, root (stages input 0))

def replay {α : Type*} (stages : α → ℕ → Code) (input : α)
    (history : List Bool) : State :=
  history.foldl (advance stages input) (initial stages input)

/-- A successful leaf answers; every other state issues a query. -/
def step {α : Type*} (stages : α → ℕ → Code) (input : α)
    (history : List Bool) : Bool ⊕ Query :=
  let state := replay stages input history
  nodeOutput (node (stages input state.1) state.2)

private theorem root_primrec : Primrec root :=
  Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)

private theorem node_primrec : Primrec₂ node := Primrec.list_getD (Sum.inl none : Node)

private theorem initial_computable {α : Type*} [Primcodable α]
    {stages : α → ℕ → Code} (h : Computable₂ stages) : Computable (initial stages) :=
  (Computable.const 0).pair (root_primrec.to_comp.comp
    (h.comp Computable.id (Computable.const 0)))

private theorem advance_computable {α : Type*} [Primcodable α]
    {stages : α → ℕ → Code} (h : Computable₂ stages) :
    Computable (fun x : α × State × Bool => advance stages x.1 x.2.1 x.2.2) := by
  have hstage : Computable (fun x : α × State × Bool => x.2.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.snd)
  have hindex : Computable (fun x : α × State × Bool => x.2.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.snd)
  exact nodeAdvance_primrec.to_comp.comp
    ((Computable.fst.comp Computable.snd).pair
      ((Computable.snd.comp Computable.snd).pair
        (root_primrec.to_comp.comp (h.comp Computable.fst
          (Primrec.nat_add.to_comp.comp hstage (Computable.const 1))))))
    (node_primrec.to_comp.comp (h.comp Computable.fst hstage) hindex)

private def replayBounded {α : Type*} (stages : α → ℕ → Code)
    (input : α) (history : List Bool) : ℕ → State
  | 0 => initial stages input
  | n + 1 => advance stages input (replayBounded stages input history n)
      (history.getD n false)

private theorem replayBounded_computable {α : Type*} [Primcodable α]
    {stages : α → ℕ → Code} (h : Computable₂ stages) :
    Computable (fun x : α × List Bool × ℕ => replayBounded stages x.1 x.2.1 x.2.2) := by
  have hrec := Computable.nat_rec
    (Computable.snd.comp Computable.snd :
      Computable (fun x : α × List Bool × ℕ => x.2.2))
    ((initial_computable h).comp Computable.fst)
    ((advance_computable h).comp
      ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.snd).pair
          ((Primrec.list_getD false).to_comp.comp
            (Computable.fst.comp (Computable.snd.comp Computable.fst))
            (Computable.fst.comp Computable.snd))))).to₂
  refine hrec.of_eq ?_
  intro x
  induction x.2.2 with
  | zero => rfl
  | succ n ih => simp only [replayBounded, ih]

private theorem replayBounded_eq_fold {α : Type*} (stages : α → ℕ → Code)
    (input : α) (history : List Bool) :
    replayBounded stages input history history.length = replay stages input history := by
  have general : ∀ n, n ≤ history.length → replayBounded stages input history n =
      (history.take n).foldl (advance stages input) (initial stages input) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [replayBounded, ih (by omega)]
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      congr 1
      exact List.getD_eq_getElem _ _ _
  simpa only [List.take_length, replay] using general history.length (by rfl)

/-- Computability is uniform in the encoded input and arbitrary Boolean history. -/
theorem step_computable {α : Type*} [Primcodable α]
    {stages : α → ℕ → Code} (h : Computable₂ stages) : Computable₂ (step stages) := by
  have hr : Computable₂ (replay stages) := by
    refine ((replayBounded_computable h).comp
      (Computable.fst.pair (Computable.snd.pair
        (Computable.list_length.comp Computable.snd)))).of_eq ?_
    intro x
    exact replayBounded_eq_fold stages x.1 x.2
  exact nodeOutput_primrec.to_comp.comp
    (node_primrec.to_comp.comp
      (h.comp Computable.fst (Computable.fst.comp hr)) (Computable.snd.comp hr))



/-- An oracle-consistent path within one packed stage. -/
inductive Path (answer : Query → Bool) (code : Code) : ℕ → ℕ → Prop
  | refl (index : ℕ) : Path answer code index index
  | query {start index q left right}
      (path : Path answer code start index)
      (hnode : node code index = .inr (q, left, right)) :
      Path answer code start (cond (answer q) right left)

/-- An answer reached by a finite oracle path in a stage. -/
def StageAnswer (answer : Query → Bool) (code : Code) (b : Bool) : Prop :=
  ∃ index, Path answer code (root code) index ∧ node code index = .inl (some b)

private def observation : Node → Option Bool
  | .inl o => o
  | .inr _ => none

private def machineNext {α : Type*} (stages : α → ℕ → Code) (input : α)
    (answer : Query → Bool) (state : State) : State :=
  match node (stages input state.1) state.2 with
  | .inl none => (state.1 + 1, root (stages input (state.1 + 1)))
  | .inl (some _) => state
  | .inr (q, left, right) => (state.1, cond (answer q) right left)

private def machineResult {α : Type*} (stages : α → ℕ → Code)
    (input : α) (state : State) : Option Bool :=
  observation (node (stages input state.1) state.2)

private theorem replay_append {α : Type*} (stages : α → ℕ → Code)
    (input : α) (history : List Bool) (bit : Bool) :
    replay stages input (history ++ [bit]) = advance stages input
      (replay stages input history) bit := by
  simp only [replay, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem run_eq_machine {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (fuel : ℕ) : ∀ history,
    run (step stages input) answer (fuel + 1) history =
      machineResult stages input
        ((machineNext stages input answer)^[fuel] (replay stages input history)) := by
  induction fuel with
  | zero =>
    intro history
    simp only [Function.iterate_zero, id_eq, run, step, machineResult]
    cases hn : node (stages input (replay stages input history).1)
      (replay stages input history).2 with
    | inl o => cases o <;> rfl
    | inr q => rfl
  | succ n ih =>
    intro history
    cases hn : node (stages input (replay stages input history).1)
      (replay stages input history).2 with
    | inl o =>
      cases o with
      | none =>
        have hnext : machineNext stages input answer (replay stages input history) =
            replay stages input (history ++ [answer tick]) := by
          rw [replay_append]
          simp only [machineNext, advance, hn, nodeAdvance]
        simpa only [run, step, hn, nodeOutput, Function.iterate_succ_apply,
          hnext] using ih (history ++ [answer tick])
      | some b =>
        have hfixed : machineNext stages input answer (replay stages input history) =
            replay stages input history := by simp only [machineNext, hn]
        simp only [run, step, hn, nodeOutput, Function.iterate_fixed hfixed,
          machineResult, observation]
    | inr q =>
      rcases q with ⟨q, left, right⟩
      have hnext : machineNext stages input answer (replay stages input history) =
          replay stages input (history ++ [answer q]) := by
        rw [replay_append]
        simp only [machineNext, advance, hn, nodeAdvance]
      simpa only [run, step, hn, nodeOutput, Function.iterate_succ_apply,
        hnext] using ih (history ++ [answer q])

private theorem reachable_next {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (state : State)
    (hp : Path answer (stages input state.1) (root (stages input state.1)) state.2) :
    let next := machineNext stages input answer state
    Path answer (stages input next.1) (root (stages input next.1)) next.2 := by
  cases hn : node (stages input state.1) state.2 with
  | inl o =>
    cases o with
    | none => simpa only [machineNext, hn] using
        (Path.refl (answer := answer) (code := stages input (state.1 + 1))
          (root (stages input (state.1 + 1))))
    | some b => simpa only [machineNext, hn] using hp
  | inr q =>
    rcases q with ⟨q, left, right⟩
    simpa only [machineNext, hn] using Path.query hp hn

private theorem reachable_iterate {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (fuel : ℕ) :
    let state := (machineNext stages input answer)^[fuel] (initial stages input)
    Path answer (stages input state.1) (root (stages input state.1)) state.2 := by
  induction fuel with
  | zero => exact Path.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact reachable_next stages input answer _ ih

/-- Every returned answer is witnessed by a finite path in a generated stage.
No wellformedness or correctness assumption on the stage data is needed. -/
theorem run_answer_from_stage {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (fuel : ℕ) (b : Bool)
    (h : run (step stages input) answer fuel [] = some b) :
    ∃ stage, StageAnswer answer (stages input stage) b := by
  cases fuel with
  | zero => simp [run] at h
  | succ n =>
    rw [run_eq_machine] at h
    let state := (machineNext stages input answer)^[n] (initial stages input)
    have hp := reachable_iterate stages input answer n
    refine ⟨state.1, state.2, hp, ?_⟩
    change observation (node (stages input state.1) state.2) = some b at h
    cases hn : node (stages input state.1) state.2 with
    | inl o =>
      rw [hn] at h
      exact congrArg Sum.inl h
    | inr q => simp [hn, observation] at h



private theorem path_machine_reaches {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (stage start index : ℕ)
    (hp : Path answer (stages input stage) start index) :
    ∃ fuel, (machineNext stages input answer)^[fuel] (stage, start) = (stage, index) := by
  induction hp with
  | refl => exact ⟨0, rfl⟩
  | @query index q left right path hn ih =>
    obtain ⟨fuel, hfuel⟩ := ih
    refine ⟨fuel + 1, ?_⟩
    rw [Function.iterate_succ_apply', hfuel]
    simp only [machineNext, hn]

private theorem stage_reaches_leaf {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (stage : ℕ)
    (hw : WellFormed (stages input stage)) (index : ℕ) :
    ∃ fuel index' outcome,
      (machineNext stages input answer)^[fuel] (stage, index) = (stage, index') ∧
      node (stages input stage) index' = .inl outcome := by
  induction index using Nat.strong_induction_on with
  | h index ih =>
    cases hn : node (stages input stage) index with
    | inl o => exact ⟨0, index, o, rfl, hn⟩
    | inr q =>
      rcases q with ⟨q, left, right⟩
      have hless : cond (answer q) right left < index := by
        obtain ⟨hl, hr⟩ := hw index q left right hn
        cases answer q <;> assumption
      obtain ⟨fuel, index', outcome, hfuel, hleaf⟩ := ih _ hless
      refine ⟨fuel + 1, index', outcome, ?_, hleaf⟩
      rw [Function.iterate_succ_apply]
      simpa only [machineNext, hn] using hfuel

private theorem stage_reached_or_answer {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (hw : ∀ stage, WellFormed (stages input stage))
    (stage : ℕ) :
    (∃ fuel b, machineResult stages input
        ((machineNext stages input answer)^[fuel] (initial stages input)) = some b) ∨
      ∃ fuel, (machineNext stages input answer)^[fuel] (initial stages input) =
        (stage, root (stages input stage)) := by
  induction stage with
  | zero => exact Or.inr ⟨0, rfl⟩
  | succ stage ih =>
    rcases ih with hanswer | ⟨fuel, hfuel⟩
    · exact Or.inl hanswer
    · obtain ⟨fuel', index, outcome, hstate, hleaf⟩ :=
        stage_reaches_leaf stages input answer stage (hw stage) (root (stages input stage))
      have hcombined : (machineNext stages input answer)^[fuel' + fuel]
          (initial stages input) = (stage, index) := by
        rw [Function.iterate_add_apply, hfuel]
        exact hstate
      cases outcome with
      | none =>
        refine Or.inr ⟨fuel' + fuel + 1, ?_⟩
        rw [Function.iterate_succ_apply', hcombined]
        simp only [machineNext, hleaf]
      | some b =>
        refine Or.inl ⟨fuel' + fuel, b, ?_⟩
        rw [hcombined]
        simp only [machineResult, hleaf, observation]

/-- If a finite stage has an answer, replay eventually answers. Postorder children
ensure that each earlier stage reaches a leaf after finitely many queries. -/
theorem run_eventually_answers {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (hw : ∀ stage, WellFormed (stages input stage))
    (hsuccess : ∃ stage b, StageAnswer answer (stages input stage) b) :
    ∃ fuel b, run (step stages input) answer fuel [] = some b := by
  obtain ⟨stage, b, index, hp, hn⟩ := hsuccess
  rcases stage_reached_or_answer stages input answer hw stage with
    ⟨fuel, b', hb'⟩ | ⟨fuel, hfuel⟩
  · refine ⟨fuel + 1, b', ?_⟩
    simpa only [run_eq_machine, replay, List.foldl_nil] using hb'
  · obtain ⟨fuel', hpath⟩ := path_machine_reaches stages input answer stage _ _ hp
    refine ⟨fuel' + fuel + 1, b, ?_⟩
    rw [run_eq_machine]
    change machineResult stages input ((machineNext stages input answer)^[fuel' + fuel]
      (initial stages input)) = some b
    rw [Function.iterate_add_apply, hfuel, hpath]
    simp only [machineResult, hn, observation]

/-- A convenient semantic packaging of replay: finite stage completeness gives
halting, and every generated stage answer gives the returned-answer specification. -/
theorem run_correct {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (P : Bool → Prop)
    (hw : ∀ stage, WellFormed (stages input stage))
    (hcomplete : ∃ stage b, StageAnswer answer (stages input stage) b)
    (hsound : ∀ stage b, StageAnswer answer (stages input stage) b → P b) :
    (∃ fuel b, run (step stages input) answer fuel [] = some b) ∧
      ∀ fuel b, run (step stages input) answer fuel [] = some b → P b := by
  refine ⟨run_eventually_answers stages input answer hw hcomplete, ?_⟩
  intro fuel b h
  obtain ⟨stage, hstage⟩ := run_answer_from_stage stages input answer fuel b h
  exact hsound stage b hstage



/-- A bounded evaluator for compiler correctness. Fuel exhaustion returns `none`. -/
def evalFuel (answer : Query → Bool) (code : Code) : ℕ → ℕ → Option Bool
  | 0, _ => none
  | fuel + 1, index =>
    match node code index with
    | .inl o => o
    | .inr (q, left, right) => evalFuel answer code fuel (cond (answer q) right left)

/-- Oracle paths compose within a stage. -/
theorem Path.trans {answer : Query → Bool} {code : Code} {start middle finish : ℕ}
    (first : Path answer code start middle) (second : Path answer code middle finish) :
    Path answer code start finish := by
  induction second with
  | refl => exact first
  | query path hn ih => exact Path.query ih hn

private theorem evalFuel_some_path (answer : Query → Bool) (code : Code) (fuel index : ℕ)
    (b : Bool) (h : evalFuel answer code fuel index = some b) :
    ∃ finish, Path answer code index finish ∧ node code finish = .inl (some b) := by
  induction fuel generalizing index with
  | zero => simp [evalFuel] at h
  | succ fuel ih =>
    cases hn : node code index with
    | inl o =>
      rw [evalFuel, hn] at h
      exact ⟨index, Path.refl index, hn.trans (congrArg Sum.inl h)⟩
    | inr q =>
      rcases q with ⟨q, left, right⟩
      rw [evalFuel, hn] at h
      obtain ⟨finish, hp, hfinish⟩ := ih _ h
      exact ⟨finish, (Path.query (Path.refl index) hn).trans hp, hfinish⟩

private theorem path_evalFuel_exists (answer : Query → Bool) (code : Code)
    {start finish : ℕ} (hp : Path answer code start finish) :
    ∀ fuel b, evalFuel answer code fuel finish = some b →
      ∃ fuel', evalFuel answer code fuel' start = some b := by
  induction hp with
  | refl => intro fuel b h; exact ⟨fuel, h⟩
  | query path hn ih =>
    intro fuel b h
    apply ih (fuel + 1) b
    simpa only [evalFuel, hn] using h

/-- A stage answer is exactly success of its bounded evaluator for some finite fuel.
The equivalence also holds for malformed codes; postorder wellformedness is only
needed to guarantee that unsuccessful stages reach a leaf. -/
theorem stageAnswer_iff_evalFuel (answer : Query → Bool) (code : Code) (b : Bool) :
    StageAnswer answer code b ↔
      ∃ fuel, evalFuel answer code fuel (root code) = some b := by
  constructor
  · rintro ⟨finish, hp, hn⟩
    apply path_evalFuel_exists answer code hp 1 b
    simp only [evalFuel, hn]
  · rintro ⟨fuel, h⟩
    exact evalFuel_some_path answer code fuel (root code) b h



/-- Compiler-facing correctness: completeness and soundness may be stated directly
in terms of bounded packed-stage evaluation. -/
theorem run_correct_of_evalFuel {α : Type*} (stages : α → ℕ → Code)
    (input : α) (answer : Query → Bool) (P : Bool → Prop)
    (hw : ∀ stage, WellFormed (stages input stage))
    (hcomplete : ∃ stage fuel b,
      evalFuel answer (stages input stage) fuel (root (stages input stage)) = some b)
    (hsound : ∀ stage fuel b,
      evalFuel answer (stages input stage) fuel (root (stages input stage)) = some b → P b) :
    (∃ fuel b, run (step stages input) answer fuel [] = some b) ∧
      ∀ fuel b, run (step stages input) answer fuel [] = some b → P b := by
  apply run_correct stages input answer P hw
  · obtain ⟨stage, fuel, b, h⟩ := hcomplete
    exact ⟨stage, b, (stageAnswer_iff_evalFuel answer _ b).mpr ⟨fuel, h⟩⟩
  · intro stage b h
    obtain ⟨fuel, hfuel⟩ := (stageAnswer_iff_evalFuel answer _ b).mp h
    exact hsound stage fuel b hfuel

end Tiling.AxisParallel.Decidability.OracleReplay
