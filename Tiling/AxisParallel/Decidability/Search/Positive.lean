import Tiling.AxisParallel.Decidability.Search.Correctness
import Tiling.AxisParallel.Decidability.Certificates.FormulaPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput
open Tiling.AxisParallel.Decidability.Affine
open Tiling.AxisParallel.Terminal.Executable

/-- The effective positive stages agree exactly with the production search stages. -/
theorem positiveValue_eq_native {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : RectanglePresentation R Ω)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer) (stage : ℕ) :
    positiveValue CertificateFormulas.positiveFormula R.length answer stage =
      Tiling.AxisParallel.Terminal.positiveStage _ (frontendOracle hR hanswer).toOracle stage := by
  let input : TableInput := (R.length, comparisonHistory (2 * R.length) answer)
  have hgrid : TableCorrect (cornerList R) input.2 := comparisonHistory_rectangles_correct hanswer
  have hinput : 0 < (vertexLabels input).length := vertexLabels_nonempty hR hgrid
  let C := inputCode input hinput
  let ON := oracle hR hgrid hinput hanswer
  have hquery : ∀ q, (answer ∘ transport input) (Native.packQuery q) = ON.toOracle.answer q := by
    intro q
    rw [Function.comp_apply, transport_packQuery]
    rfl
  change decidePackedFormula (answer ∘ transport input)
    (CertificateFormulas.positiveFormula (formulaRegion input) stage) =
      Tiling.AxisParallel.Terminal.positiveStage C ON.toOracle stage
  rw [formulaRegion_eq_encodeRegion input hinput]
  cases hc : wellFormedPositiveStage stage with
  | none =>
    rw [CertificateFormulas.Native.positiveFormula_none _ stage hc]
    simp only [Tiling.AxisParallel.Terminal.positiveStage,
      PositiveVerification.verifyPositiveStage, hc]
    rfl
  | some c =>
    have hw : c.wellFormed = true := (Option.filter_eq_some_iff.mp hc).2
    rw [CertificateFormulas.Native.positiveFormula_eq_pack C stage c hc,
      Native.decidePackedFormula_eq_decideFormula ON.toOracle (answer ∘ transport input) hquery]
    simp only [Tiling.AxisParallel.Terminal.positiveStage,
      PositiveVerification.verifyPositiveStage, hc, PositiveVerification.verifyPositive,
      hw, Bool.true_and]

end Tiling.AxisParallel.Decidability.OracleDecision
