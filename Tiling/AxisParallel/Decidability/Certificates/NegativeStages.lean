import Tiling.AxisParallel.Decidability.Certificates.NegativeFormulasComputability
import Tiling.AxisParallel.Decidability.Certificates.NegativeFormulasCorrespondence
import Tiling.AxisParallel.Terminal.DecidabilityCertificates

/-! A single finite formula for each negative-certificate stage. -/

set_option autoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.NegativeFormulas.Native

open Tiling.AxisParallel.Terminal.Executable

/-- The conjunction tested by the production negative verifier. -/
def certificateFormula (C : RegionCode) (B : LocalCoverSearch.LocalBoundCode C)
    (c : RawNegativeCode) : Formula C 0 0 :=
  if c.wellFormed then
    .conjunction (LocalCoverSearch.positiveSubdivisionFormula C B c)
      (LocalCoverSearch.listAnd
        ((List.range (c.horizontalSubdivisions * c.verticalSubdivisions + 1)).map
          fun m => Formula.negation (LocalCoverSearch.localCoverFormula C B c.boxIndex m)))
  else .falsity

private theorem listAnd_holds {C : RegionCode} (R : Realization C)
    {h v : ℕ} (fs : List (Formula C h v)) (x : Fin h → ℝ) (y : Fin v → ℝ) :
    (LocalCoverSearch.listAnd fs).Holds R x y ↔ ∀ f ∈ fs, f.Holds R x y := by
  induction fs with
  | nil => simp [LocalCoverSearch.listAnd, Formula.Holds]
  | cons f fs ih =>
      change (f.Holds R x y ∧ (LocalCoverSearch.listAnd fs).Holds R x y) ↔ _
      simp only [ih, List.forall_mem_cons]

theorem certificateFormula_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalCoverSearch.LocalBoundCode C) (c : RawNegativeCode) :
    AffineCompiler.decideFormula O.toOracle (certificateFormula C B c) =
      LocalCoverSearch.negativeVerifier AffineCompiler.decideFormula O.toOracle B c := by
  apply Bool.eq_iff_iff.mpr
  rw [AffineCompiler.decideFormula_correct]
  have hwell : LocalCoverSearch.subdivisionWellFormed c = c.wellFormed := rfl
  by_cases hc : c.wellFormed = true
  · simp only [certificateFormula, if_pos hc, Formula.Holds, listAnd_holds,
      List.forall_mem_map, List.mem_range]
    simp only [LocalCoverSearch.negativeVerifier, LocalCoverSearch.checkSubdivision,
      hwell, hc,
      Bool.true_and, Bool.and_eq_true, LocalCoverSearch.allLocalCardinalitiesFail,
      List.all_eq_true, List.mem_range, LocalCoverSearch.localCardinalityBound,
      LocalCoverSearch.checkLocalCover, Bool.not_eq_true_eq_eq_false,
      Bool.eq_false_iff, ne_eq, AffineCompiler.decideFormula_correct]
  · simp only [certificateFormula, if_neg hc, Formula.Holds]
    have hfalse : c.wellFormed = false := Bool.eq_false_iff.mpr hc
    simp only [LocalCoverSearch.negativeVerifier, LocalCoverSearch.checkSubdivision,
      hwell, hfalse,
      Bool.false_and, Bool.false_eq_true]

def stageFormula (C : RegionCode) (B : LocalCoverSearch.LocalBoundCode C)
    (stage : ℕ) : Formula C 0 0 :=
  match wellFormedNegativeStage stage with
  | none => .falsity
  | some c => certificateFormula C B c

theorem stageFormula_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalCoverSearch.LocalBoundCode C) (stage : ℕ)
    (hB : LocalCoverSearch.buildLocalBound C O.toOracle = some B) :
    AffineCompiler.decideFormula O.toOracle (stageFormula C B stage) =
      Tiling.AxisParallel.Terminal.negativeStage C O.toOracle stage := by
  rw [Tiling.AxisParallel.Terminal.negativeStage, hB]
  cases hstage : wellFormedNegativeStage stage with
  | none =>
      simp only [stageFormula, hstage]
      apply Bool.eq_false_iff.mpr
      rw [ne_eq, AffineCompiler.decideFormula_correct]
      exact id
  | some c =>
      simpa only [stageFormula, hstage] using certificateFormula_correct R O B c

open Affine.Native CertificateFormulas.Native

theorem negativeCertificateFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (c : RawNegativeCode) :
    negativeCertificateFormula (encodeRegion C) (encodeBound B) c =
      packFormula (certificateFormula C B c) := by
  by_cases hc : c.wellFormed = true
  · simp only [negativeCertificateFormula, certificateFormula, if_pos hc,
      packFormula_conjunction, positiveSubdivisionFormula_eq_pack, pack_listAnd,
      List.map_map, Function.comp_def, packFormula_negation, localCoverFormula_eq_pack]
  · simp only [negativeCertificateFormula, certificateFormula, if_neg hc, packFormula_falsity]

theorem negativeFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (stage : ℕ) :
    negativeFormula (encodeRegion C) (encodeBound B) stage =
      packFormula (stageFormula C B stage) := by
  unfold negativeFormula stageFormula
  cases wellFormedNegativeStage stage with
  | none => rfl
  | some c => exact negativeCertificateFormula_eq_pack C B c

end Tiling.AxisParallel.Decidability.NegativeFormulas.Native
