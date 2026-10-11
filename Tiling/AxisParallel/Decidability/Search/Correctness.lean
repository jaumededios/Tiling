import Tiling.AxisParallel.Decidability.Search.Runtime
import Tiling.AxisParallel.Terminal.DecidabilityCertificates
import Tiling.AxisParallel.Terminal.PositiveCertificateCompleteness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput
open Tiling.AxisParallel.Terminal.Executable

/-- Correct native oracle for the region recovered by the uniform finite-query frontend. -/
def frontendOracle {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : RectanglePresentation R Ω)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer) :
    Tiling.AxisParallel.Terminal.Executable.CorrectOracle
      (inputCode (R.length, comparisonHistory (2 * R.length) answer)
        (vertexLabels_nonempty hR (comparisonHistory_rectangles_correct hanswer)))
      (realizationOfOracle hR hanswer) :=
  oracle hR (comparisonHistory_rectangles_correct hanswer)
    (vertexLabels_nonempty hR (comparisonHistory_rectangles_correct hanswer)) hanswer

/-- The final integration transfers production certificate soundness and completeness
through actual packed-stage equalities and the two finite query prefixes. -/
theorem decisionProgram_correct_of_native (positive : PositiveProducer)
    (negative : NegativeProducer) {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : RectanglePresentation R Ω)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer)
    (hp : ∀ stage, positiveValue positive R.length answer stage =
      Tiling.AxisParallel.Terminal.positiveStage _ (frontendOracle hR hanswer).toOracle stage)
    (hn : ∀ stage, negativeValue negative R.length answer stage =
      Tiling.AxisParallel.Terminal.negativeStage _ (frontendOracle hR hanswer).toOracle stage) :
    (∃ fuel b, run (decisionProgram positive negative R.length) answer fuel [] = some b) ∧
      ∀ fuel b, run (decisionProgram positive negative R.length) answer fuel [] = some b →
        (b = true ↔ ∃ T, Tiles Ω T) := by
  let RN := realizationOfOracle hR hanswer
  let ON := frontendOracle hR hanswer
  have ht : PositiveVerification.realizationPlaneTileable RN ↔ ∃ T, Tiles Ω T :=
    realizationOfOracle_tileable_iff hR hanswer
  apply decisionProgram_correct positive negative R.length answer (∃ T, Tiles Ω T)
  · intro stage hs
    apply ht.mp
    apply PositiveVerification.verifyPositiveStage_sound RN ON stage
    exact (hp stage).symm.trans hs
  · intro stage hs htile
    apply Tiling.AxisParallel.Terminal.negativeStage_sound RN ON stage
      ((hn stage).symm.trans hs)
    exact ht.mpr htile
  · intro htile
    obtain ⟨stage, hs⟩ :=
      Tiling.AxisParallel.Terminal.PositiveCertificateCompleteness.positiveStage_complete
        RN ON (ht.mpr htile)
    exact ⟨stage, (hp stage).trans hs⟩
  · intro hnotile
    obtain ⟨stage, hs⟩ := Tiling.AxisParallel.Terminal.negativeStage_complete RN ON
      (fun htile => hnotile (ht.mp htile))
    exact ⟨stage, (hn stage).trans hs⟩

end Tiling.AxisParallel.Decidability.OracleDecision
