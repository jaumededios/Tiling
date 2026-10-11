import Tiling.AxisParallel.Decidability.Search.Prefix

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput
open Tiling.AxisParallel.Decidability.Affine
open Affine.Trees

abbrev PositiveProducer := CertificateFormulas.RegionInput → ℕ → Code
abbrev NegativeProducer := CertificateFormulas.RegionInput → LocalBound.Bounds → ℕ → Code

def runtimeBounds (input : RuntimeInput) : Option LocalBound.Bounds :=
  LocalBound.build (packedRegion input.1) input.2

def runtimeTransport (input : RuntimeInput) (q : PackedQuery) : Query := transport input.1 q

def stageResult (_input : RuntimeInput) (stage : ℕ) : Bool := decide (stage % 2 = 0)

def negativeAt (negative : NegativeProducer) (input : RuntimeInput) (stage : ℕ) : Code :=
  match runtimeBounds input with
  | none => CertificateFormulas.falsity
  | some bounds => negative (formulaRegion input.1) bounds stage

/-- Alternate positive and negative certificate indices without any bound on the search. -/
def stageFormula (positive : PositiveProducer) (negative : NegativeProducer)
    (input : RuntimeInput) (stage : ℕ) : Code :=
  if stageResult input stage then positive (formulaRegion input.1) (stage / 2)
  else negativeAt negative input (stage / 2)

def searchBody (positive : PositiveProducer) (negative : NegativeProducer)
    (input : RuntimeInput) (history : List Bool) : Bool ⊕ Query :=
  OracleReplay.step (certificateStages runtimeTransport stageResult
    (stageFormula positive negative)) input history

/-- A single history program, taking only the rectangle count, implements the decision search. -/
def decisionProgram (positive : PositiveProducer) (negative : NegativeProducer) : OracleCode :=
  withPrefixes (searchBody positive negative)

theorem runtimeBounds_computable : Computable runtimeBounds :=
  LocalBound.build_primrec.to_comp.comp
    (packedRegion_primrec.to_comp.comp Computable.fst) Computable.snd

theorem runtimeTransport_computable : Computable₂ runtimeTransport :=
  transport_computable.comp (Computable.fst.comp Computable.fst) Computable.snd

theorem stageResult_computable : Computable₂ stageResult :=
  (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2))
    (Primrec.const 0)).decide.to_comp

private theorem optionalNegative_computable {α : Type*} [Primcodable α]
    {negative : NegativeProducer} {region : α → CertificateFormulas.RegionInput}
    {bounds : α → Option LocalBound.Bounds} {stage : α → ℕ}
    (hn : Computable (fun x : CertificateFormulas.RegionInput ×
      LocalBound.Bounds × ℕ => negative x.1 x.2.1 x.2.2))
    (hr : Computable region) (hb : Computable bounds) (hs : Computable stage) :
    Computable (fun x => match bounds x with
      | none => CertificateFormulas.falsity
      | some b => negative (region x) b (stage x)) := by
  have hsome : Computable₂ (fun x : α => fun b : LocalBound.Bounds =>
      negative (region x) b (stage x)) :=
    hn.comp ((hr.comp Computable.fst).pair (Computable.snd.pair (hs.comp Computable.fst)))
  refine (Computable.option_casesOn hb
    (Computable.const CertificateFormulas.falsity) hsome).of_eq ?_
  intro x
  cases bounds x <;> rfl

theorem negativeAt_computable {negative : NegativeProducer}
    (hn : Computable (fun x : CertificateFormulas.RegionInput ×
      LocalBound.Bounds × ℕ => negative x.1 x.2.1 x.2.2)) : Computable₂ (negativeAt negative) :=
  optionalNegative_computable hn
    (formulaRegion_computable.comp (Computable.fst.comp Computable.fst))
    (runtimeBounds_computable.comp Computable.fst) Computable.snd

theorem stageFormula_computable {positive : PositiveProducer} {negative : NegativeProducer}
    (hp : Computable₂ positive)
    (hn : Computable (fun x : CertificateFormulas.RegionInput ×
      LocalBound.Bounds × ℕ => negative x.1 x.2.1 x.2.2)) :
    Computable₂ (stageFormula positive negative) := by
  have hindex : Computable (fun x : RuntimeInput × ℕ => x.2 / 2) :=
    Primrec.nat_div.to_comp.comp Computable.snd (Computable.const 2)
  have hpositive := hp.comp
    (formulaRegion_computable.comp (Computable.fst.comp Computable.fst)) hindex
  have hnegative := (negativeAt_computable hn).comp Computable.fst hindex
  refine (Computable.cond stageResult_computable hpositive hnegative).of_eq ?_
  intro x
  cases hs : stageResult x.1 x.2 <;> simp only [stageFormula, hs, Bool.false_eq_true,
    ↓reduceIte] <;> rfl

theorem decisionProgram_computable {positive : PositiveProducer} {negative : NegativeProducer}
    (hp : Computable₂ positive)
    (hn : Computable (fun x : CertificateFormulas.RegionInput ×
      LocalBound.Bounds × ℕ => negative x.1 x.2.1 x.2.2)) :
    Computable₂ (decisionProgram positive negative) :=
  withPrefixes_computable (certificateSearch_computable runtimeTransport_computable
    stageResult_computable (stageFormula_computable hp hn))

/-- Semantic specification of a positive packed stage after the finite query prefixes. -/
def positiveValue (positive : PositiveProducer) (count : ℕ)
    (answer : Query → Bool) (stage : ℕ) : Bool :=
  let input := oracleInput count answer
  decidePackedFormula (answer ∘ runtimeTransport input) (positive (formulaRegion input.1) stage)

/-- Semantic specification of a negative packed stage after the finite query prefixes. -/
def negativeValue (negative : NegativeProducer) (count : ℕ)
    (answer : Query → Bool) (stage : ℕ) : Bool :=
  let input := oracleInput count answer
  decidePackedFormula (answer ∘ runtimeTransport input) (negativeAt negative input stage)

/-- The integration needs only certificate completeness and soundness. The executable
program itself depends solely on its two effective finite formula producers. -/
theorem decisionProgram_correct (positive : PositiveProducer) (negative : NegativeProducer)
    (count : ℕ) (answer : Query → Bool) (Q : Prop)
    (hps : ∀ stage, positiveValue positive count answer stage = true → Q)
    (hns : ∀ stage, negativeValue negative count answer stage = true → ¬Q)
    (hpc : Q → ∃ stage, positiveValue positive count answer stage = true)
    (hnc : ¬Q → ∃ stage, negativeValue negative count answer stage = true) :
    (∃ fuel b, run (decisionProgram positive negative count) answer fuel [] = some b) ∧
      ∀ fuel b, run (decisionProgram positive negative count) answer fuel [] = some b →
        (b = true ↔ Q) := by
  apply withPrefixes_correct (searchBody positive negative) count answer (fun b => b = true ↔ Q)
  · apply (certificateSearch_correct runtimeTransport stageResult
      (stageFormula positive negative) (oracleInput count answer) answer
      (fun b => b = true ↔ Q) ?_ ?_).1
    · by_cases hQ : Q
      · obtain ⟨stage, hs⟩ := hpc hQ
        refine ⟨2 * stage, ?_⟩
        simpa [stageFormula, stageResult, positiveValue] using hs
      · obtain ⟨stage, hs⟩ := hnc hQ
        refine ⟨2 * stage + 1, ?_⟩
        have hdiv : (2 * stage + 1) / 2 = stage := by omega
        simpa [stageFormula, stageResult, negativeValue, hdiv] using hs
    · intro stage hs
      by_cases he : stage % 2 = 0
      · have hQ := hps (stage / 2) (by
          simpa [stageFormula, stageResult, he, positiveValue] using hs)
        simp [stageResult, he, hQ]
      · have hQ := hns (stage / 2) (by
          simpa [stageFormula, stageResult, he, negativeValue] using hs)
        simp [stageResult, he, hQ]
  · intro fuel b hf
    obtain ⟨stage, hstage⟩ := OracleReplay.run_answer_from_stage
      (certificateStages runtimeTransport stageResult (stageFormula positive negative))
      (oracleInput count answer) answer fuel b hf
    obtain ⟨hformula, hresult⟩ := (certificateTree_stageAnswer _ _ _ _ _).mp hstage
    rw [← hresult]
    by_cases he : stage % 2 = 0
    · have hQ := hps (stage / 2) (by
        simpa [stageFormula, stageResult, he, positiveValue] using hformula)
      simp [stageResult, he, hQ]
    · have hQ := hns (stage / 2) (by
        simpa [stageFormula, stageResult, he, negativeValue] using hformula)
      simp [stageResult, he, hQ]

end Tiling.AxisParallel.Decidability.OracleDecision
