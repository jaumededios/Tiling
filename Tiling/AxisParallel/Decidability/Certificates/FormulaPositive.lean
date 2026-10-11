import Tiling.AxisParallel.Decidability.Certificates.FormulaTriangularCorrespondence
import Tiling.AxisParallel.Decidability.Certificates.FormulaLatticeCorrespondence

/-! The total, computable positive-certificate enumeration stage. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine
open PositiveCoding
open CertificateCoding
open Tiling.AxisParallel.Terminal.Executable

def positiveCertificate (region : RegionInput) : RawPositiveCode → Code
  | .triangular c => orientClosed c.orientation (Triangular.triangularSlabFormula region c)
  | .lattice c => latticeCertificate region c

def positiveFormula (region : RegionInput) (stage : ℕ) : Code :=
  match wellFormedPositiveStage stage with
  | none => falsity
  | some c => positiveCertificate region c

theorem positiveCertificate_computable : Computable₂ positiveCertificate := by
  have ht : Computable (fun p : RegionInput × RawTriangularCode =>
      orientClosed p.2.orientation (Triangular.triangularSlabFormula p.1 p.2)) :=
    orientClosed_primrec.to_comp.comp
      (rawTriangular_orientation_primrec.to_comp.comp Computable.snd)
      (Triangular.c_triangularSlabFormula Prod.fst Prod.snd Computable.fst Computable.snd)
  exact rawPositive_casesOn_computable₂ ht latticeCertificate_computable

theorem positiveFormula_computable : Computable₂ positiveFormula := by
  have hs : Computable (fun p : RegionInput × ℕ => wellFormedPositiveStage p.2) :=
    wellFormedPositiveStage_computable.comp Computable.snd
  refine (Computable.option_casesOn hs (Computable.const falsity)
    (positiveCertificate_computable.comp
      (Computable.fst.comp Computable.fst) Computable.snd).to₂).of_eq ?_
  intro p
  unfold positiveFormula
  cases wellFormedPositiveStage p.2 <;> rfl

namespace Native

theorem positiveCertificate_eq_pack (C : RegionCode) (c : RawPositiveCode) :
    positiveCertificate (encodeRegion C) c =
      Affine.Native.packFormula (PositiveVerification.positiveCertificateFormula
        C c) := by
  cases c with
  | triangular c =>
    change orientClosed c.orientation (Triangular.triangularSlabFormula (encodeRegion C) c) = _
    rw [triangularSlab_eq_pack, orientClosed_eq_pack]
    rfl
  | lattice c => exact latticeCertificate_eq_pack C c

theorem positiveFormula_eq_pack (C : RegionCode) (stage : ℕ) (c : RawPositiveCode)
    (hc : wellFormedPositiveStage stage = some c) :
    positiveFormula (encodeRegion C) stage =
      Affine.Native.packFormula (PositiveVerification.positiveCertificateFormula
        C c) := by
  simp only [positiveFormula, hc, positiveCertificate_eq_pack]

theorem positiveFormula_none (region : RegionInput) (stage : ℕ)
    (hc : wellFormedPositiveStage stage = none) : positiveFormula region stage = falsity := by
  simp only [positiveFormula, hc]

end Native
end Tiling.AxisParallel.Decidability.CertificateFormulas
