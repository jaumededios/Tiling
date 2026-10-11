import Tiling.AxisParallel.Decidability.Search.Correctness
import Tiling.AxisParallel.Decidability.Certificates.NegativeStages
import Tiling.AxisParallel.Decidability.RectangleInput.LocalBoundSemantics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.OracleDecision

open RectangleInput
open Tiling.AxisParallel.Decidability.Affine
open Tiling.AxisParallel.Terminal.Executable

/-- The effective negative stages agree exactly with the production search stages. -/
theorem negativeValue_eq_native {R : List (Plane × Plane)} {Ω : Set Plane}
    {answer : Tiling.AxisParallel.Decidability.Query → Bool}
    (hR : RectanglePresentation R Ω)
    (hanswer : Tiling.AxisParallel.Decidability.CorrectOracle (cornerList R) answer) (stage : ℕ) :
    negativeValue NegativeFormulas.negativeFormula R.length answer stage =
      Tiling.AxisParallel.Terminal.negativeStage _ (frontendOracle hR hanswer).toOracle stage := by
  let input : TableInput := (R.length, comparisonHistory (2 * R.length) answer)
  have hgrid : TableCorrect (cornerList R) input.2 := comparisonHistory_rectangles_correct hanswer
  have hinput : 0 < (vertexLabels input).length := vertexLabels_nonempty hR hgrid
  let C := inputCode input hinput
  let RN := realization hR hgrid hinput
  let ON := oracle hR hgrid hinput hanswer
  have hc : 0 < C.cellCount := by
    simpa only [C, inputCode, regionCode, packedRegion, List.length_map] using
      coarseCells_nonempty hR hgrid
  have hex : ∃ B : LocalCoverSearch.LocalBoundCode C,
      LocalCoverSearch.buildLocalBound C ON.toOracle = some B := by
    simp only [LocalCoverSearch.buildLocalBound, dif_pos hc]
    exact ⟨_, rfl⟩
  obtain ⟨B, hB⟩ := hex
  have hbounds : runtimeBounds (oracleInput R.length answer) =
      some (NegativeFormulas.Native.encodeBound B) := by
    change LocalBound.build (packedRegion input)
      (LocalBound.history (packedRegion input) answer) = _
    rw [LocalBound.build_eq_native hR hgrid hinput hanswer, hB]
    rfl
  change decidePackedFormula (answer ∘ transport input)
    (negativeAt NegativeFormulas.negativeFormula (oracleInput R.length answer) stage) =
      Tiling.AxisParallel.Terminal.negativeStage C ON.toOracle stage
  rw [negativeAt, hbounds]
  change decidePackedFormula (answer ∘ transport input)
    (NegativeFormulas.negativeFormula (formulaRegion input)
      (NegativeFormulas.Native.encodeBound B) stage) = _
  rw [formulaRegion_eq_encodeRegion input hinput,
    NegativeFormulas.Native.negativeFormula_eq_pack C B stage]
  have hquery : ∀ q, (answer ∘ transport input) (Native.packQuery q) = ON.toOracle.answer q := by
    intro q
    rw [Function.comp_apply, transport_packQuery]
    rfl
  rw [Native.decidePackedFormula_eq_decideFormula ON.toOracle (answer ∘ transport input) hquery]
  exact NegativeFormulas.Native.stageFormula_correct RN ON B stage hB

end Tiling.AxisParallel.Decidability.OracleDecision
