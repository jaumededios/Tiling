import Tiling.AxisParallel.Decidability.Affine.Correspondence
import Tiling.AxisParallel.Decidability.Certificates.FormulaRuntime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.Affine.Native

open Tiling.AxisParallel.Terminal.Executable
open CertificateFormulas

/-- Moving a native formula's code shifts precisely its actual child references. -/
theorem shiftCode_packFormulaAt {C : RegionCode} {h v : ℕ} (f : Formula C h v)
    (offset delta : ℕ) :
    shiftCode delta (packFormulaAt offset f) = packFormulaAt (delta + offset) f := by
  induction f generalizing offset with
  | truth => rfl
  | falsity => rfl
  | horizontalLe a b => rfl
  | horizontalLt a b => rfl
  | verticalLe a b => rfl
  | verticalLt a b => rfl
  | conjunction p q ihp ihq =>
    have hp := compilationTrace_length_pos p
    have hq := compilationTrace_length_pos q
    simp only [packFormulaAt, shiftCode, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map (shiftInstruction delta) (packFormulaAt offset p) =
      packFormulaAt (delta + offset) p from ihp offset]
    rw [show List.map (shiftInstruction delta)
        (packFormulaAt (offset + (compilationTrace p).length) q) =
      packFormulaAt (delta + offset + (compilationTrace p).length) q by
        simpa only [shiftCode, Nat.add_assoc] using ihq (offset + (compilationTrace p).length)]
    simp only [shiftInstruction]
    dsimp
    congr <;> omega
  | disjunction p q ihp ihq =>
    have hp := compilationTrace_length_pos p
    have hq := compilationTrace_length_pos q
    simp only [packFormulaAt, shiftCode, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map (shiftInstruction delta) (packFormulaAt offset p) =
      packFormulaAt (delta + offset) p from ihp offset]
    rw [show List.map (shiftInstruction delta)
        (packFormulaAt (offset + (compilationTrace p).length) q) =
      packFormulaAt (delta + offset + (compilationTrace p).length) q by
        simpa only [shiftCode, Nat.add_assoc] using ihq (offset + (compilationTrace p).length)]
    simp only [shiftInstruction]
    dsimp
    congr <;> omega
  | negation p ih =>
    have hp := compilationTrace_length_pos p
    simp only [packFormulaAt, shiftCode, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map (shiftInstruction delta) (packFormulaAt offset p) =
      packFormulaAt (delta + offset) p from ih offset]
    simp only [shiftInstruction]
    dsimp
    congr
    omega
  | existsHorizontal p ih =>
    have hp := compilationTrace_length_pos p
    simp only [packFormulaAt, shiftCode, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map (shiftInstruction delta) (packFormulaAt offset p) =
      packFormulaAt (delta + offset) p from ih offset]
    simp only [shiftInstruction]
    dsimp
    congr
    omega
  | existsVertical p ih =>
    have hp := compilationTrace_length_pos p
    simp only [packFormulaAt, shiftCode, List.map_append, List.map_cons, List.map_nil]
    rw [show List.map (shiftInstruction delta) (packFormulaAt offset p) =
      packFormulaAt (delta + offset) p from ih offset]
    simp only [shiftInstruction]
    dsimp
    congr
    omega

/-- Formula constructors may rebase a packed subtree by shifting its code. -/
theorem packFormulaAt_eq_shiftCode {C : RegionCode} {h v : ℕ} (f : Formula C h v)
    (offset : ℕ) : packFormulaAt offset f = shiftCode offset (packFormula f) := by
  simpa only [packFormula, Nat.add_zero] using (shiftCode_packFormulaAt f 0 offset).symm

@[simp] theorem packFormula_truth {C : RegionCode} {h v : ℕ} :
    packFormula (Formula.truth : Formula C h v) = truth := rfl

@[simp] theorem packFormula_falsity {C : RegionCode} {h v : ℕ} :
    packFormula (Formula.falsity : Formula C h v) = falsity := rfl

@[simp] theorem packFormula_horizontalLe {C : RegionCode} {h v : ℕ}
    (a b : AffineExpr C h) :
    packFormula (Formula.horizontalLe a b : Formula C h v) =
      atomCode false false
        (exprSub (packExpr (AffineCompiler.LinearExpr.ofAffine a))
          (packExpr (AffineCompiler.LinearExpr.ofAffine b))) := by
  simp only [packFormula, packFormulaAt, atomCode, packAtom, packExpr_sub]
  rfl

@[simp] theorem packFormula_horizontalLt {C : RegionCode} {h v : ℕ}
    (a b : AffineExpr C h) :
    packFormula (Formula.horizontalLt a b : Formula C h v) =
      atomCode false true
        (exprSub (packExpr (AffineCompiler.LinearExpr.ofAffine a))
          (packExpr (AffineCompiler.LinearExpr.ofAffine b))) := by
  simp only [packFormula, packFormulaAt, atomCode, packAtom, packExpr_sub]
  rfl

@[simp] theorem packFormula_verticalLe {C : RegionCode} {h v : ℕ}
    (a b : AffineExpr C v) :
    packFormula (Formula.verticalLe a b : Formula C h v) =
      atomCode true false
        (exprSub (packExpr (AffineCompiler.LinearExpr.ofAffine a))
          (packExpr (AffineCompiler.LinearExpr.ofAffine b))) := by
  simp only [packFormula, packFormulaAt, atomCode, packAtom, packExpr_sub]
  rfl

@[simp] theorem packFormula_verticalLt {C : RegionCode} {h v : ℕ}
    (a b : AffineExpr C v) :
    packFormula (Formula.verticalLt a b : Formula C h v) =
      atomCode true true
        (exprSub (packExpr (AffineCompiler.LinearExpr.ofAffine a))
          (packExpr (AffineCompiler.LinearExpr.ofAffine b))) := by
  simp only [packFormula, packFormulaAt, atomCode, packAtom, packExpr_sub]
  rfl

@[simp] theorem packFormula_conjunction {C : RegionCode} {h v : ℕ}
    (p q : Formula C h v) :
    packFormula (.conjunction p q) = conjunction (packFormula p) (packFormula q) := by
  simp only [packFormula, packFormulaAt, conjunction, binary, packFormulaAt_length,
    Nat.zero_add]
  rw [packFormulaAt_eq_shiftCode q]
  rfl

@[simp] theorem packFormula_disjunction {C : RegionCode} {h v : ℕ}
    (p q : Formula C h v) :
    packFormula (.disjunction p q) = disjunction (packFormula p) (packFormula q) := by
  simp only [packFormula, packFormulaAt, disjunction, binary, packFormulaAt_length,
    Nat.zero_add]
  rw [packFormulaAt_eq_shiftCode q]
  rfl

@[simp] theorem packFormula_negation {C : RegionCode} {h v : ℕ} (p : Formula C h v) :
    packFormula (.negation p) = negation (packFormula p) := by
  simp only [packFormula, packFormulaAt, negation, unary, packFormulaAt_length,
    Nat.zero_add]
  rfl

@[simp] theorem packFormula_existsHorizontal {C : RegionCode} {h v : ℕ}
    (p : Formula C (h + 1) v) :
    packFormula (.existsHorizontal p) = existsHorizontal (packFormula p) := by
  simp only [packFormula, packFormulaAt, existsHorizontal, unary, packFormulaAt_length,
    Nat.zero_add]
  rfl

@[simp] theorem packFormula_existsVertical {C : RegionCode} {h v : ℕ}
    (p : Formula C h (v + 1)) :
    packFormula (.existsVertical p) = existsVertical (packFormula p) := by
  simp only [packFormula, packFormulaAt, existsVertical, unary, packFormulaAt_length,
    Nat.zero_add]
  rfl

end Tiling.AxisParallel.Decidability.Affine.Native
