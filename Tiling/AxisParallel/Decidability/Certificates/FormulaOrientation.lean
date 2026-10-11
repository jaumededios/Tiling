import Tiling.AxisParallel.Decidability.Affine.FormulaPacking
import Tiling.AxisParallel.Terminal.PositiveCertificateVerification

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine

/-- Swap coordinate sorts and quantifiers, preserving all unused instruction data. -/
def swapInstruction (i : Instruction) : Instruction :=
  (if i.1 = 6 then 7 else if i.1 = 7 then 6 else i.1,
    if i.1 = 2 then (!i.2.1.1, i.2.1.2) else i.2.1, i.2.2)

def swapCode (code : Code) : Code := code.map swapInstruction

def orientClosed (vertical : Bool) (code : Code) : Code :=
  if vertical then swapCode code else code

theorem swapInstruction_primrec : Primrec swapInstruction := by
  have htag : Primrec (fun i : Instruction => i.1) := Primrec.fst
  have hatom : Primrec (fun i : Instruction => i.2.1) := Primrec.fst.comp Primrec.snd
  have hnot : Primrec (fun i : Instruction => !(i.2.1.1)) :=
    (Primrec.dom_bool _).comp (Primrec.fst.comp hatom)
  exact (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) (Primrec.const 7)
    (Primrec.ite (Primrec.eq.comp htag (Primrec.const 7)) (Primrec.const 6) htag)).pair
    ((Primrec.ite (Primrec.eq.comp htag (Primrec.const 2))
      (hnot.pair (Primrec.snd.comp hatom)) hatom).pair (Primrec.snd.comp Primrec.snd))

theorem swapCode_primrec : Primrec swapCode :=
  Primrec.list_map Primrec.id (swapInstruction_primrec.comp Primrec.snd).to₂

theorem orientClosed_primrec : Primrec₂ orientClosed := by
  refine (Primrec.cond Primrec.fst (swapCode_primrec.comp Primrec.snd) Primrec.snd).of_eq ?_
  intro x
  cases x.1 <;> rfl

namespace Native

open Tiling.AxisParallel.Terminal.Executable
open Affine.Native

@[simp] theorem compilationTrace_length_coordinateSwap {C : RegionCode} {h v : ℕ}
    (f : Formula C h v) :
    (compilationTrace (PositiveVerification.Formula.coordinateSwap f)).length =
      (compilationTrace f).length := by
  induction f <;> simp [compilationTrace, PositiveVerification.Formula.coordinateSwap, *]

/-- Swapping the finite code exactly implements native coordinate exchange. -/
theorem packFormulaAt_coordinateSwap {C : RegionCode} {h v : ℕ} (f : Formula C h v)
    (offset : ℕ) :
    packFormulaAt offset (PositiveVerification.Formula.coordinateSwap f) =
      swapCode (packFormulaAt offset f) := by
  induction f generalizing offset <;>
    simp [PositiveVerification.Formula.coordinateSwap, packFormulaAt, swapCode,
      swapInstruction, *]

@[simp] theorem packFormula_coordinateSwap {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    packFormula (PositiveVerification.Formula.coordinateSwap f) = swapCode (packFormula f) :=
  packFormulaAt_coordinateSwap f 0

@[simp] theorem orientClosed_eq_pack {C : RegionCode} (vertical : Bool) (f : Formula C 0 0) :
    orientClosed vertical (packFormula f) =
      packFormula (PositiveVerification.Formula.orientClosed vertical f) := by
  cases vertical <;> simp [orientClosed, PositiveVerification.Formula.orientClosed]

end Native

end Tiling.AxisParallel.Decidability.CertificateFormulas
