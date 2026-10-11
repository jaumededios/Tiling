import Tiling.AxisParallel.Decidability.Certificates.FormulaRuntime
import Tiling.AxisParallel.Decidability.Affine.Computability
import Tiling.AxisParallel.Decidability.Affine.Correspondence

/-! Affine arrays and atomic comparisons used by the certificate generators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine
open PositiveCoding
open Tiling.Computability.List (list_replicate_primrec)

abbrev Cell := (ℕ × ℕ) × (ℕ × ℕ)
abbrev RegionInput := ℕ × List Cell

def basisArray (count index : ℕ) (value : ℚ) : List ℚ :=
  (List.range count).map fun j => if j = index then value else 0

def affineZero (variableCount inputs : ℕ) : Expr :=
  (List.replicate variableCount 0, List.replicate inputs 0)

def affineVariable (variableCount inputs index : ℕ) : Expr :=
  (basisArray variableCount index 1, List.replicate inputs 0)

def affineInput (variableCount : ℕ) (coefficients : List ℚ) : Expr :=
  (List.replicate variableCount 0, coefficients)

def cellSelector (region : RegionInput) (side index : ℕ) : ℕ :=
  let cell := region.2.getD index ((0, 0), (0, 0))
  (if side = 0 then cell.1.1 else if side = 1 then cell.1.2
    else if side = 2 then cell.2.1 else cell.2.2) % region.1

def cellInput (region : RegionInput) (variableCount side index : ℕ) : Expr :=
  affineInput variableCount (basisArray region.1 (cellSelector region side index) 1)

def comparison (vertical strict : Bool) (left right : Expr) : Code :=
  atomCode vertical strict (exprSub left right)

def horizontalLe (left right : Expr) : Code := comparison false false left right
def horizontalLt (left right : Expr) : Code := comparison false true left right
def verticalLe (left right : Expr) : Code := comparison true false left right
def verticalLt (left right : Expr) : Code := comparison true true left right

theorem basisArray_primrec : Primrec (fun p : ℕ × ℕ × ℚ =>
    basisArray p.1 p.2.1 p.2.2) :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.ite
      (Primrec.eq.comp Primrec.snd (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 0)).to₂

theorem affineZero_primrec : Primrec₂ affineZero :=
  (list_replicate_primrec.comp Primrec.fst (Primrec.const (0 : ℚ))).pair
    (list_replicate_primrec.comp Primrec.snd (Primrec.const (0 : ℚ)))

theorem affineVariable_primrec : Primrec (fun p : ℕ × ℕ × ℕ =>
    affineVariable p.1 p.2.1 p.2.2) :=
  (basisArray_primrec.comp (Primrec.fst.pair
    ((Primrec.snd.comp Primrec.snd).pair (Primrec.const 1)))).pair
      (list_replicate_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.const (0 : ℚ)))

theorem affineInput_primrec : Primrec₂ affineInput :=
  (list_replicate_primrec.comp Primrec.fst (Primrec.const (0 : ℚ))).pair Primrec.snd

theorem cellSelector_primrec : Primrec (fun p : RegionInput × ℕ × ℕ =>
    cellSelector p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : RegionInput × ℕ × ℕ =>
      p.1.2.getD p.2.2 ((0, 0), (0, 0))) :=
    (Primrec.list_getD ((0, 0), (0, 0))).comp
      (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun p : RegionInput × ℕ × ℕ => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  exact Primrec.nat_mod.comp
    (Primrec.ite (Primrec.eq.comp hs (Primrec.const 0)) (Primrec.fst.comp (Primrec.fst.comp hc))
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const 1))
        (Primrec.snd.comp (Primrec.fst.comp hc))
        (Primrec.ite (Primrec.eq.comp hs (Primrec.const 2))
          (Primrec.fst.comp (Primrec.snd.comp hc)) (Primrec.snd.comp (Primrec.snd.comp hc)))))
    (Primrec.fst.comp Primrec.fst)

theorem cellInput_primrec : Primrec (fun p : RegionInput × ℕ × ℕ × ℕ =>
    cellInput p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  affineInput_primrec.comp (Primrec.fst.comp Primrec.snd)
    (basisArray_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((cellSelector_primrec.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.const 1))))

theorem comparison_computable : Computable (fun p : Bool × Bool × Expr × Expr =>
    comparison p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hp : Computable (fun p : Bool × Bool × Expr × Expr =>
      (p.1, p.2.1, exprSub p.2.2.1 p.2.2.2)) := Computable.fst.pair
    ((Computable.fst.comp Computable.snd).pair
      (exprSub_computable.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))
        (Computable.snd.comp (Computable.snd.comp Computable.snd))))
  have h := atomCode_primrec.to_comp.comp hp
  exact h.of_eq (fun _ => rfl)

theorem horizontalLe_computable : Computable₂ horizontalLe := by
  have hp : Computable (fun p : Expr × Expr => (false, false, p)) :=
    (Computable.const false).pair ((Computable.const false).pair Computable.id)
  exact (comparison_computable.comp hp).of_eq (fun _ => rfl)

theorem horizontalLt_computable : Computable₂ horizontalLt := by
  have hp : Computable (fun p : Expr × Expr => (false, true, p)) :=
    (Computable.const false).pair ((Computable.const true).pair Computable.id)
  exact (comparison_computable.comp hp).of_eq (fun _ => rfl)

theorem verticalLe_computable : Computable₂ verticalLe := by
  have hp : Computable (fun p : Expr × Expr => (true, false, p)) :=
    (Computable.const true).pair ((Computable.const false).pair Computable.id)
  exact (comparison_computable.comp hp).of_eq (fun _ => rfl)

theorem verticalLt_computable : Computable₂ verticalLt := by
  have hp : Computable (fun p : Expr × Expr => (true, true, p)) :=
    (Computable.const true).pair ((Computable.const true).pair Computable.id)
  exact (comparison_computable.comp hp).of_eq (fun _ => rfl)

namespace Native

open Tiling.AxisParallel.Terminal.Executable

def encodeRegion (C : RegionCode) : RegionInput :=
  (C.vertexCount, List.ofFn fun e =>
    (((C.leftVertex e).val, (C.rightVertex e).val),
      ((C.bottomVertex e).val, (C.topVertex e).val)))

@[simp] theorem encodeRegion_vertexCount (C : RegionCode) :
    (encodeRegion C).1 = C.vertexCount := rfl

@[simp] theorem encodeRegion_cellCount (C : RegionCode) :
    (encodeRegion C).2.length = C.cellCount := by simp [encodeRegion]

def packAffine {C : RegionCode} {n : ℕ} (a : AffineExpr C n) : Expr :=
  Affine.Native.packExpr (AffineCompiler.LinearExpr.ofAffine a)

theorem basisArray_eq_ofFn {n : ℕ} (index : ℕ) (value : ℚ) :
    basisArray n index value = List.ofFn (fun j : Fin n => if j.val = index then value else 0) := by
  apply List.ext_getElem
  · simp [basisArray]
  · intro j hj hj'
    simp [basisArray]

theorem affineVariable_eq_pack {C : RegionCode} (n index : ℕ) :
    affineVariable n C.vertexCount index =
      packAffine (⟨fun j => if j.val = index then 1 else 0, Coeff.zero C⟩ : AffineExpr C n) := by
  simp [affineVariable, basisArray_eq_ofFn, packAffine,
    Affine.Native.packExpr, AffineCompiler.LinearExpr.ofAffine, Coeff.zero]

theorem affineInput_eq_pack {C : RegionCode} {n : ℕ} (a : Coeff C) :
    affineInput n (List.ofFn (fun j => (a j : ℚ))) =
      packAffine (⟨fun _ => 0, a⟩ : AffineExpr C n) := by
  simp [affineInput, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine]

theorem affineZero_eq_pack {C : RegionCode} (n : ℕ) :
    affineZero n C.vertexCount =
      packAffine (⟨fun _ => 0, Coeff.zero C⟩ : AffineExpr C n) := by
  simp [affineZero, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine, Coeff.zero]

theorem cellSelector_encodeRegion (C : RegionCode) (e : Fin C.cellCount) :
    cellSelector (encodeRegion C) 0 e = C.leftVertex e ∧
    cellSelector (encodeRegion C) 1 e = C.rightVertex e ∧
    cellSelector (encodeRegion C) 2 e = C.bottomVertex e ∧
    cellSelector (encodeRegion C) 3 e = C.topVertex e := by
  simp [cellSelector, encodeRegion, Nat.mod_eq_of_lt]

theorem cellInput_left_eq_pack (C : RegionCode) (n : ℕ) (e : Fin C.cellCount) :
    cellInput (encodeRegion C) n 0 e =
      packAffine (⟨fun _ => 0, Coeff.cellLeft e⟩ : AffineExpr C n) := by
  rw [cellInput, (cellSelector_encodeRegion C e).1, basisArray_eq_ofFn]
  simp [affineInput, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine, Coeff.cellLeft, Coeff.single, Fin.ext_iff, encodeRegion]

theorem cellInput_right_eq_pack (C : RegionCode) (n : ℕ) (e : Fin C.cellCount) :
    cellInput (encodeRegion C) n 1 e =
      packAffine (⟨fun _ => 0, Coeff.cellRight e⟩ : AffineExpr C n) := by
  rw [cellInput, (cellSelector_encodeRegion C e).2.1, basisArray_eq_ofFn]
  simp [affineInput, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine, Coeff.cellRight, Coeff.single, Fin.ext_iff, encodeRegion]

theorem cellInput_bottom_eq_pack (C : RegionCode) (n : ℕ) (e : Fin C.cellCount) :
    cellInput (encodeRegion C) n 2 e =
      packAffine (⟨fun _ => 0, Coeff.cellBottom e⟩ : AffineExpr C n) := by
  rw [cellInput, (cellSelector_encodeRegion C e).2.2.1, basisArray_eq_ofFn]
  simp [affineInput, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine, Coeff.cellBottom, Coeff.single, Fin.ext_iff, encodeRegion]

theorem cellInput_top_eq_pack (C : RegionCode) (n : ℕ) (e : Fin C.cellCount) :
    cellInput (encodeRegion C) n 3 e =
      packAffine (⟨fun _ => 0, Coeff.cellTop e⟩ : AffineExpr C n) := by
  rw [cellInput, (cellSelector_encodeRegion C e).2.2.2, basisArray_eq_ofFn]
  simp [affineInput, packAffine, Affine.Native.packExpr,
    AffineCompiler.LinearExpr.ofAffine, Coeff.cellTop, Coeff.single, Fin.ext_iff, encodeRegion]

theorem packAffine_add {C : RegionCode} {n : ℕ} (a b : AffineExpr C n) :
    exprAdd (packAffine a) (packAffine b) = packAffine
      (⟨fun i => a.variableCoefficient i + b.variableCoefficient i,
        fun i => a.inputConstant i + b.inputConstant i⟩ : AffineExpr C n) := by
  simp only [packAffine, Affine.Native.packExpr_add]
  simp [Affine.Native.packExpr, AffineCompiler.LinearExpr.add,
    AffineCompiler.LinearExpr.ofAffine]

theorem packAffine_neg {C : RegionCode} {n : ℕ} (a : AffineExpr C n) :
    exprNeg (packAffine a) = packAffine
      (⟨fun i => -a.variableCoefficient i, fun i => -a.inputConstant i⟩ : AffineExpr C n) := by
  simp only [packAffine, Affine.Native.packExpr_neg]
  simp [Affine.Native.packExpr, AffineCompiler.LinearExpr.neg,
    AffineCompiler.LinearExpr.ofAffine]

theorem packAffine_intScale {C : RegionCode} {n : ℕ} (z : ℤ) (a : AffineExpr C n) :
    exprScale (z : ℚ) (packAffine a) = packAffine
      (⟨fun i => (z : ℚ) * a.variableCoefficient i,
        fun i => z * a.inputConstant i⟩ : AffineExpr C n) := by
  simp only [packAffine, Affine.Native.packExpr_scale]
  simp [Affine.Native.packExpr, AffineCompiler.LinearExpr.scale,
    AffineCompiler.LinearExpr.ofAffine]

theorem packAffine_scale_zero {C : RegionCode} {n : ℕ} (q : ℚ) (a : AffineExpr C n)
    (ha : a.inputConstant = Coeff.zero C) :
    exprScale q (packAffine a) = packAffine
      (⟨fun i => q * a.variableCoefficient i,
        fun i => q.num * a.inputConstant i⟩ : AffineExpr C n) := by
  simp only [packAffine, Affine.Native.packExpr_scale]
  simp [Affine.Native.packExpr, AffineCompiler.LinearExpr.scale,
    AffineCompiler.LinearExpr.ofAffine, ha, Coeff.zero]

theorem horizontalLe_eq_pack {C : RegionCode} {h v : ℕ} (a b : AffineExpr C h) :
    horizontalLe (packAffine a) (packAffine b) =
      Affine.Native.packFormula (Formula.horizontalLe (v := v) a b) := by
  simp [horizontalLe, comparison, atomCode, packAffine,
    Affine.Native.packFormula, Affine.Native.packFormulaAt,
    Affine.Native.packAtom]

theorem horizontalLt_eq_pack {C : RegionCode} {h v : ℕ} (a b : AffineExpr C h) :
    horizontalLt (packAffine a) (packAffine b) =
      Affine.Native.packFormula (Formula.horizontalLt (v := v) a b) := by
  simp [horizontalLt, comparison, atomCode, packAffine,
    Affine.Native.packFormula, Affine.Native.packFormulaAt,
    Affine.Native.packAtom]

theorem verticalLe_eq_pack {C : RegionCode} {h v : ℕ} (a b : AffineExpr C v) :
    verticalLe (packAffine a) (packAffine b) =
      Affine.Native.packFormula (Formula.verticalLe (h := h) a b) := by
  simp [verticalLe, comparison, atomCode, packAffine,
    Affine.Native.packFormula, Affine.Native.packFormulaAt,
    Affine.Native.packAtom]

theorem verticalLt_eq_pack {C : RegionCode} {h v : ℕ} (a b : AffineExpr C v) :
    verticalLt (packAffine a) (packAffine b) =
      Affine.Native.packFormula (Formula.verticalLt (h := h) a b) := by
  simp [verticalLt, comparison, atomCode, packAffine,
    Affine.Native.packFormula, Affine.Native.packFormulaAt,
    Affine.Native.packAtom]

end Native

end Tiling.AxisParallel.Decidability.CertificateFormulas
