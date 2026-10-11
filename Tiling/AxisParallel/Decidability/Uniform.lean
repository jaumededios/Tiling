import Tiling.AxisParallel.Decidability.Search.Positive
import Tiling.AxisParallel.Decidability.Search.Negative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability

/-- The concrete rectangle-count decision program with finite query preprocessing,
finite Fourier–Motzkin verification, and positive/negative certificate replay. -/
def uniformDecisionProgram : OracleCode :=
  OracleDecision.decisionProgram CertificateFormulas.positiveFormula
    NegativeFormulas.negativeFormula

theorem uniformDecisionProgram_computable : Computable₂ uniformDecisionProgram :=
  OracleDecision.decisionProgram_computable CertificateFormulas.positiveFormula_computable
    NegativeFormulas.negativeFormula_computable

/-- The concrete search terminates and decides tileability for every correct comparison provider. -/
theorem uniformDecisionProgram_correct {R : List (Plane × Plane)} {Ω : Set Plane}
    (hR : RectanglePresentation R Ω) {answer : Query → Bool}
    (hanswer : CorrectOracle (cornerList R) answer) :
    (∃ fuel b, run (uniformDecisionProgram R.length) answer fuel [] = some b) ∧
      ∀ fuel b, run (uniformDecisionProgram R.length) answer fuel [] = some b →
        (b = true ↔ ∃ T, Tiles Ω T) := by
  exact OracleDecision.decisionProgram_correct_of_native
    CertificateFormulas.positiveFormula NegativeFormulas.negativeFormula
    hR hanswer
    (OracleDecision.positiveValue_eq_native hR hanswer)
    (OracleDecision.negativeValue_eq_native hR hanswer)

/-- One computable search works for every finite input and correct comparison provider. -/
theorem uniform_oracle_relative_decision_bounded :
    ∃ program : OracleCode, Computable₂ program ∧
      ∀ R Ω, RectanglePresentation R Ω → ∀ answer, CorrectOracle (cornerList R) answer →
        (∃ fuel b, run (program R.length) answer fuel [] = some b) ∧
        ∀ fuel b, run (program R.length) answer fuel [] = some b →
          (b = true ↔ ∃ T, Tiles Ω T) := by
  exact ⟨uniformDecisionProgram, uniformDecisionProgram_computable,
    fun _R _Ω hR _answer hanswer => uniformDecisionProgram_correct hR hanswer⟩

end Tiling.AxisParallel.Decidability
