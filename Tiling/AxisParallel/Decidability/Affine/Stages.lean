import Tiling.AxisParallel.Decidability.Affine.Trees

/-! Oracle-search stages compiled from finite certificate formulas. A false formula
is an unsuccessful stage; a true formula returns the certificate's chosen answer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.Affine.Trees

open OracleReplay

def labelNode (result : Bool) : Node → Node
  | .inl none => .inl none
  | .inl (some b) => .inl (if b then some result else none)
  | .inr q => .inr q

def labelCode (result : Bool) (code : Tree) : Tree := code.map (labelNode result)

/-- Verify a certificate formula, returning `result` only when the formula is true. -/
def certificateTree (transport : PackedQuery → Query) (result : Bool) (code : Code) : Tree :=
  labelCode result (treeOfFormula transport code)

private theorem labelNode_primrec : Primrec₂ labelNode := by
  have hleaf : Primrec₂ (fun result : Bool => fun o : Option Bool =>
      match o with
      | none => (Sum.inl none : Node)
      | some b => Sum.inl (if b then some result else none)) := by
    have hsome : Primrec (fun x : (Bool × Option Bool) × Bool => some x.1.1) :=
      Primrec.option_some.comp (Primrec.fst.comp Primrec.fst)
    refine (Primrec.option_casesOn Primrec.snd (Primrec.const (.inl none))
      (Primrec.sumInl.comp (Primrec.cond Primrec.snd
        hsome (Primrec.const none))).to₂).of_eq ?_
    intro x
    cases x.2 with
    | none => rfl
    | some b => cases b <;> rfl
  refine (Primrec.sumCasesOn Primrec.snd
    (hleaf.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
    (Primrec.sumInr.comp Primrec.snd).to₂).of_eq ?_
  intro x
  cases x.2 with
  | inl o => cases o <;> rfl
  | inr q => rfl

private theorem labelCode_primrec : Primrec₂ labelCode :=
  Primrec.list_map Primrec.snd
    (labelNode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

private theorem node_labelCode (result : Bool) (code : Tree) (index : ℕ) :
    node (labelCode result code) index = labelNode result (node code index) := by
  exact List.getD_map code (.inl none) (labelNode result)

private theorem labelCode_wellFormed (result : Bool) (code : Tree) (h : WellFormed code) :
    WellFormed (labelCode result code) := by
  intro index q left right hn
  rw [node_labelCode] at hn
  cases he : node code index with
  | inl o =>
    cases o with
    | none => simp [he, labelNode] at hn
    | some b => cases b <;> simp [he, labelNode] at hn
  | inr qq =>
    simp only [he, labelNode, Sum.inr.injEq] at hn
    exact h index q left right (by rw [he, hn])

private theorem evalFuel_labelCode (result : Bool) (answer : Query → Bool)
    (code : Tree) (fuel index : ℕ) :
    evalFuel answer (labelCode result code) fuel index =
      (evalFuel answer code fuel index).bind (fun b => if b then some result else none) := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
    simp only [evalFuel, node_labelCode]
    cases hn : node code index with
    | inl o => cases o with
      | none => rfl
      | some b => cases b <;> rfl
    | inr qq => exact ih _

private theorem labelCode_stageAnswer (result : Bool) (answer : Query → Bool)
    (code : Tree) (b : Bool) :
    StageAnswer answer (labelCode result code) b ↔ StageAnswer answer code true ∧ result = b := by
  rw [stageAnswer_iff_evalFuel, stageAnswer_iff_evalFuel]
  have hroot : root (labelCode result code) = root code := by simp [root, labelCode]
  constructor
  · rintro ⟨fuel, hf⟩
    rw [hroot, evalFuel_labelCode] at hf
    cases he : evalFuel answer code fuel (root code) with
    | none => simp [he] at hf
    | some value =>
      cases value with
      | false => simp [he] at hf
      | true => exact ⟨⟨fuel, he⟩, by simpa only [he, Option.bind_some, ↓reduceIte,
          Option.some.injEq] using hf⟩
  · rintro ⟨⟨fuel, hf⟩, rfl⟩
    refine ⟨fuel, ?_⟩
    rw [hroot, evalFuel_labelCode, hf]
    rfl

/-- Every certificate-search stage is finite and has only backwards child references. -/
theorem certificateTree_wellFormed (transport : PackedQuery → Query) (result : Bool)
    (code : Code) : WellFormed (certificateTree transport result code) :=
  labelCode_wellFormed result _ (treeOfFormula_wellFormed transport code)

/-- The stage returns its designated answer exactly when its finite formula is true. -/
theorem certificateTree_stageAnswer (transport : PackedQuery → Query) (answer : Query → Bool)
    (result : Bool) (code : Code) (b : Bool) :
    StageAnswer answer (certificateTree transport result code) b ↔
      decidePackedFormula (answer ∘ transport) code = true ∧ result = b := by
  rw [certificateTree, labelCode_stageAnswer, treeOfFormula_stageAnswer]

/-- Certificate-tree generation is computable uniformly in the query transport. -/
theorem certificateTree_computable {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} (ht : Computable₂ transport) :
    Computable (fun x : α × Bool × Code => certificateTree (transport x.1) x.2.1 x.2.2) :=
  labelCode_primrec.to_comp.comp (Computable.fst.comp Computable.snd)
    ((treeOfFormula_computable ht).comp (Computable.fst.pair
      (Computable.snd.comp Computable.snd)))

/-- Formula truth and the designated result exactly characterize successful native stages. -/
theorem certificateTree_native_correct
    {C : Tiling.AxisParallel.Terminal.Executable.RegionCode}
    (R : Tiling.AxisParallel.Terminal.Executable.Realization C)
    (O : Tiling.AxisParallel.Terminal.Executable.CorrectOracle C R)
    (transport : PackedQuery → Query) (answer : Query → Bool)
    (hanswer : ∀ q, answer (transport (Native.packQuery q)) = O.toOracle.answer q)
    (f : Tiling.AxisParallel.Terminal.Executable.Formula C 0 0) (result b : Bool) :
    StageAnswer answer (certificateTree transport result (Native.packFormula f)) b ↔
      Tiling.AxisParallel.Terminal.Executable.Formula.Holds R f Fin.elim0 Fin.elim0 ∧
        result = b := by
  rw [certificateTree_stageAnswer, Native.decidePackedFormula_correct R O
    (answer ∘ transport) hanswer]

/-- Assemble a sequence of certificate-search stages from packed formula generators. -/
def certificateStages {α : Type*} (transport : α → PackedQuery → Query)
    (results : α → ℕ → Bool) (formulas : α → ℕ → Code) (input : α) (stage : ℕ) : Tree :=
  certificateTree (transport input) (results input stage) (formulas input stage)

/-- Effective finite stage generation from effective formula and result generators. -/
theorem certificateStages_computable {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} {results : α → ℕ → Bool}
    {formulas : α → ℕ → Code} (ht : Computable₂ transport)
    (hr : Computable₂ results) (hf : Computable₂ formulas) :
    Computable₂ (certificateStages transport results formulas) :=
  (certificateTree_computable ht).comp (Computable.fst.pair (hr.pair hf))

/-- The history-only replay program is computable on every input and history. -/
theorem certificateSearch_computable {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} {results : α → ℕ → Bool}
    {formulas : α → ℕ → Code} (ht : Computable₂ transport)
    (hr : Computable₂ results) (hf : Computable₂ formulas) :
    Computable₂ (OracleReplay.step (certificateStages transport results formulas)) :=
  OracleReplay.step_computable (certificateStages_computable ht hr hf)

/-- A true finite certificate gives eventual replay termination, and certificate
soundness specifies every returned answer. No uniform bound on certificate stage is needed. -/
theorem certificateSearch_correct {α : Type*}
    (transport : α → PackedQuery → Query) (results : α → ℕ → Bool)
    (formulas : α → ℕ → Code) (input : α) (answer : Query → Bool) (P : Bool → Prop)
    (hcomplete : ∃ stage,
      decidePackedFormula (answer ∘ transport input) (formulas input stage) = true)
    (hsound : ∀ stage,
      decidePackedFormula (answer ∘ transport input) (formulas input stage) = true →
        P (results input stage)) :
    (∃ fuel b, run (OracleReplay.step (certificateStages transport results formulas) input)
      answer fuel [] = some b) ∧
    ∀ fuel b, run (OracleReplay.step (certificateStages transport results formulas) input)
      answer fuel [] = some b → P b := by
  apply OracleReplay.run_correct
    (certificateStages transport results formulas) input answer P
  · intro stage
    exact certificateTree_wellFormed _ _ _
  · obtain ⟨stage, hstage⟩ := hcomplete
    exact ⟨stage, results input stage,
      (certificateTree_stageAnswer _ _ _ _ _).mpr ⟨hstage, rfl⟩⟩
  · intro stage b hb
    obtain ⟨hformula, hresult⟩ := (certificateTree_stageAnswer _ _ _ _ _).mp hb
    rw [← hresult]
    exact hsound stage hformula

end Tiling.AxisParallel.Decidability.Affine.Trees
