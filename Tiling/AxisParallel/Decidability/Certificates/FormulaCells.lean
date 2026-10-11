import Tiling.AxisParallel.Decidability.Certificates.FormulaComputability
import Tiling.AxisParallel.Decidability.Affine.FormulaPacking
import Tiling.AxisParallel.Terminal.PositiveCertificateVerification

/-! Packed cell macros and their exact native formula correspondence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine

def horizontalEq (a b : Expr) : Code := conjunction (horizontalLe a b) (horizontalLe b a)
def verticalEq (a b : Expr) : Code := conjunction (verticalLe a b) (verticalLe b a)
def forallHorizontal (p : Code) : Code := negation (existsHorizontal (negation p))
def forallVertical (p : Code) : Code := negation (existsVertical (negation p))
def close (h v : ℕ) (p : Code) : Code := closeVertical v (closeHorizontal h p)

def selectedInput (region : RegionInput) (epsilon : Bool) (n side e : ℕ) : Expr :=
  cellInput region n
    (if epsilon then if side = 0 then 2 else if side = 1 then 3
      else if side = 2 then 0 else 1 else side) e

def openCell (region : RegionInput) (epsilon : Bool) (h v e : ℕ)
    (cx x cy y : Expr) : Code :=
  andList [horizontalLt (exprAdd cx (selectedInput region epsilon h 0 e)) x,
    horizontalLt x (exprAdd cx (selectedInput region epsilon h 1 e)),
    verticalLt (exprAdd cy (selectedInput region epsilon v 2 e)) y,
    verticalLt y (exprAdd cy (selectedInput region epsilon v 3 e))]

def closedCell (region : RegionInput) (epsilon : Bool) (h v e : ℕ)
    (cx x cy y : Expr) : Code :=
  andList [horizontalLe (exprAdd cx (selectedInput region epsilon h 0 e)) x,
    horizontalLe x (exprAdd cx (selectedInput region epsilon h 1 e)),
    verticalLe (exprAdd cy (selectedInput region epsilon v 2 e)) y,
    verticalLe y (exprAdd cy (selectedInput region epsilon v 3 e))]

def sameCentre (cx cx' cy cy' : Expr) : Code :=
  conjunction (horizontalEq cx cx') (verticalEq cy cy')

def cellNonoverlap (region : RegionInput) (epsilon : Bool) (h v e e' : ℕ)
    (cx cx' cy cy' : Expr) : Code :=
  orList [horizontalLe (exprAdd cx (selectedInput region epsilon h 1 e))
      (exprAdd cx' (selectedInput region epsilon h 0 e')),
    horizontalLe (exprAdd cx' (selectedInput region epsilon h 1 e'))
      (exprAdd cx (selectedInput region epsilon h 0 e)),
    verticalLe (exprAdd cy (selectedInput region epsilon v 3 e))
      (exprAdd cy' (selectedInput region epsilon v 2 e')),
    verticalLe (exprAdd cy' (selectedInput region epsilon v 3 e'))
      (exprAdd cy (selectedInput region epsilon v 2 e))]

@[fun_prop] theorem c_horizontalEq {α : Type*} [Primcodable α]
    (a b : α → Expr) (ha : Computable a) (hb : Computable b) :
    Computable (fun x => horizontalEq (a x) (b x)) := by
  unfold horizontalEq
  fun_prop

@[fun_prop] theorem c_verticalEq {α : Type*} [Primcodable α]
    (a b : α → Expr) (ha : Computable a) (hb : Computable b) :
    Computable (fun x => verticalEq (a x) (b x)) := by
  unfold verticalEq
  fun_prop

@[fun_prop] theorem c_forallHorizontal {α : Type*} [Primcodable α]
    (p : α → Code) (hp : Computable p) : Computable (fun x => forallHorizontal (p x)) := by
  unfold forallHorizontal
  fun_prop

@[fun_prop] theorem c_forallVertical {α : Type*} [Primcodable α]
    (p : α → Code) (hp : Computable p) : Computable (fun x => forallVertical (p x)) := by
  unfold forallVertical
  fun_prop

@[fun_prop] theorem c_close {α : Type*} [Primcodable α]
    (h v : α → ℕ) (p : α → Code) (hh : Computable h) (hv : Computable v)
    (hp : Computable p) : Computable (fun x => close (h x) (v x) (p x)) := by
  unfold close
  fun_prop

@[fun_prop] theorem c_selectedInput {α : Type*} [Primcodable α]
    (r : α → RegionInput) (s : α → Bool) (n side e : α → ℕ)
    (hr : Computable r) (hs : Computable s) (hn : Computable n)
    (hside : Computable side) (he : Computable e) :
    Computable (fun x => selectedInput (r x) (s x) (n x) (side x) (e x)) := by
  unfold selectedInput
  fun_prop

@[fun_prop] theorem c_openCell {α : Type*} [Primcodable α]
    (r : α → RegionInput) (s : α → Bool) (h v e : α → ℕ) (cx x cy y : α → Expr)
    (hr : Computable r) (hs : Computable s) (hh : Computable h) (hv : Computable v)
    (he : Computable e) (hcx : Computable cx) (hx : Computable x)
    (hcy : Computable cy) (hy : Computable y) :
    Computable (fun a => openCell (r a) (s a) (h a) (v a) (e a) (cx a) (x a) (cy a) (y a)) := by
  unfold openCell
  fun_prop

@[fun_prop] theorem c_closedCell {α : Type*} [Primcodable α]
    (r : α → RegionInput) (s : α → Bool) (h v e : α → ℕ) (cx x cy y : α → Expr)
    (hr : Computable r) (hs : Computable s) (hh : Computable h) (hv : Computable v)
    (he : Computable e) (hcx : Computable cx) (hx : Computable x)
    (hcy : Computable cy) (hy : Computable y) :
    Computable (fun a => closedCell (r a) (s a) (h a) (v a) (e a) (cx a) (x a) (cy a) (y a)) := by
  unfold closedCell
  fun_prop

@[fun_prop] theorem c_sameCentre {α : Type*} [Primcodable α]
    (cx cx' cy cy' : α → Expr) (hcx : Computable cx) (hcx' : Computable cx')
    (hcy : Computable cy) (hcy' : Computable cy') :
    Computable (fun a => sameCentre (cx a) (cx' a) (cy a) (cy' a)) := by
  unfold sameCentre
  fun_prop

@[fun_prop] theorem c_cellNonoverlap {α : Type*} [Primcodable α]
    (r : α → RegionInput) (s : α → Bool) (h v e e' : α → ℕ) (cx cx' cy cy' : α → Expr)
    (hr : Computable r) (hs : Computable s) (hh : Computable h) (hv : Computable v)
    (he : Computable e) (he' : Computable e') (hcx : Computable cx) (hcx' : Computable cx')
    (hcy : Computable cy) (hcy' : Computable cy') :
    Computable (fun a => cellNonoverlap (r a) (s a) (h a) (v a) (e a) (e' a)
      (cx a) (cx' a) (cy a) (cy' a)) := by
  unfold cellNonoverlap
  fun_prop

namespace Native

open Tiling.AxisParallel.Terminal.Executable

@[simp] theorem pack_andList {C : RegionCode} {h v : ℕ} (fs : List (Formula C h v)) :
    Affine.Native.packFormula (PositiveVerification.Formula.andList fs) = andList
      (fs.map Affine.Native.packFormula) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [PositiveVerification.Formula.andList,
    Affine.Native.packFormula_conjunction, ih,
      List.map_cons, andList, List.foldr_cons]

@[simp] theorem pack_orList {C : RegionCode} {h v : ℕ} (fs : List (Formula C h v)) :
    Affine.Native.packFormula (PositiveVerification.Formula.orList fs) = orList
      (fs.map Affine.Native.packFormula) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp only [PositiveVerification.Formula.orList,
    Affine.Native.packFormula_disjunction, ih,
      List.map_cons, orList, List.foldr_cons]

@[simp] theorem pack_closeHorizontal {C : RegionCode} {v : ℕ} (h : ℕ) (f : Formula C h v) :
    Affine.Native.packFormula (PositiveVerification.Formula.closeHorizontal h f)
      = closeHorizontal h (Affine.Native.packFormula f) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [PositiveVerification.Formula.closeHorizontal, ih,
      Affine.Native.packFormula_existsHorizontal,
      closeHorizontal, Function.iterate_succ_apply]

@[simp] theorem pack_closeVertical {C : RegionCode} (v : ℕ) (f : Formula C 0 v) :
    Affine.Native.packFormula (PositiveVerification.Formula.closeVertical v f) =
      closeVertical v (Affine.Native.packFormula f) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    simp only [PositiveVerification.Formula.closeVertical, ih,
      Affine.Native.packFormula_existsVertical,
      closeVertical, Function.iterate_succ_apply]

@[simp] theorem pack_close {C : RegionCode} {h v : ℕ} (f : Formula C h v) :
    Affine.Native.packFormula (PositiveVerification.Formula.close f) = close h v
      (Affine.Native.packFormula f) := by
  simp only [PositiveVerification.Formula.close, pack_closeHorizontal, pack_closeVertical, close]

@[simp] theorem pack_implication {C : RegionCode} {h v : ℕ} (p q : Formula C h v) :
    Affine.Native.packFormula (PositiveVerification.Formula.implication p q) =
      implication (Affine.Native.packFormula p)
      (Affine.Native.packFormula q) := by
  simp only [PositiveVerification.Formula.implication,
    Affine.Native.packFormula_disjunction,
    Affine.Native.packFormula_negation,
    implication]

@[simp] theorem pack_forallHorizontal {C : RegionCode} {h v : ℕ} (f : Formula C (h + 1) v) :
    Affine.Native.packFormula (PositiveVerification.Formula.forallHorizontal f) =
      forallHorizontal (Affine.Native.packFormula f) := by
  simp only [PositiveVerification.Formula.forallHorizontal,
    Affine.Native.packFormula_negation,
    Affine.Native.packFormula_existsHorizontal,
    forallHorizontal]

@[simp] theorem pack_forallVertical {C : RegionCode} {h v : ℕ} (f : Formula C h (v + 1)) :
    Affine.Native.packFormula (PositiveVerification.Formula.forallVertical f) =
      forallVertical (Affine.Native.packFormula f) := by
  simp only [PositiveVerification.Formula.forallVertical,
    Affine.Native.packFormula_negation,
    Affine.Native.packFormula_existsVertical,
    forallVertical]

@[simp] theorem pack_zero (C : RegionCode) (n : ℕ) :
    packAffine (PositiveVerification.Expr.zero C n) = affineZero n C.vertexCount :=
      (affineZero_eq_pack n).symm

@[simp] theorem pack_var (C : RegionCode) (n index : ℕ) :
    packAffine (PositiveVerification.Expr.var C n index) = affineVariable n C.vertexCount index :=
  (affineVariable_eq_pack n index).symm

@[simp] theorem pack_input {C : RegionCode} (n : ℕ) (a : Coeff C) :
    packAffine (PositiveVerification.Expr.input n a) = affineInput n (List.ofFn (fun i => (a i :
      ℚ))) :=
  (affineInput_eq_pack a).symm

@[simp] theorem pack_add {C : RegionCode} {n : ℕ} (a b : AffineExpr C n) :
    packAffine (PositiveVerification.Expr.add a b) = exprAdd (packAffine a) (packAffine b) :=
  (packAffine_add a b).symm

@[simp] theorem pack_neg {C : RegionCode} {n : ℕ} (a : AffineExpr C n) :
    packAffine (PositiveVerification.Expr.neg a) = exprNeg (packAffine a) := (packAffine_neg a).symm

@[simp] theorem pack_sub {C : RegionCode} {n : ℕ} (a b : AffineExpr C n) :
    packAffine (PositiveVerification.Expr.sub a b) = exprSub (packAffine a) (packAffine b) := by
  simp only [PositiveVerification.Expr.sub, pack_add, pack_neg, exprSub]

@[simp] theorem pack_intScale {C : RegionCode} {n : ℕ} (z : ℤ) (a : AffineExpr C n) :
    packAffine (PositiveVerification.Expr.scale (z : ℚ) a) = exprScale (z : ℚ) (packAffine a) := by
  simpa only [PositiveVerification.Expr.scale, Rat.num_intCast] using (packAffine_intScale z a).symm

@[simp] theorem pack_scale_zero {C : RegionCode} {n : ℕ} (q : ℚ) (a : AffineExpr C n)
    (ha : a.inputConstant = Coeff.zero C) :
    packAffine (PositiveVerification.Expr.scale q a) = exprScale q (packAffine a) :=
  (packAffine_scale_zero q a ha).symm

@[simp] theorem pack_horizontalLe {C : RegionCode} {h v : ℕ} (a b : AffineExpr C h) :
    Affine.Native.packFormula (.horizontalLe a b : Formula C h v) = horizontalLe
      (packAffine a) (packAffine b) :=
  (horizontalLe_eq_pack a b).symm

@[simp] theorem pack_horizontalLt {C : RegionCode} {h v : ℕ} (a b : AffineExpr C h) :
    Affine.Native.packFormula (.horizontalLt a b : Formula C h v) = horizontalLt
      (packAffine a) (packAffine b) :=
  (horizontalLt_eq_pack a b).symm

@[simp] theorem pack_verticalLe {C : RegionCode} {h v : ℕ} (a b : AffineExpr C v) :
    Affine.Native.packFormula (.verticalLe a b : Formula C h v) = verticalLe
      (packAffine a) (packAffine b) :=
  (verticalLe_eq_pack a b).symm

@[simp] theorem pack_verticalLt {C : RegionCode} {h v : ℕ} (a b : AffineExpr C v) :
    Affine.Native.packFormula (.verticalLt a b : Formula C h v) = verticalLt
      (packAffine a) (packAffine b) :=
  (verticalLt_eq_pack a b).symm

@[simp] theorem pack_selectedLeft (C : RegionCode) (epsilon : Bool) (n : ℕ)
    (e : Fin C.cellCount) :
    packAffine (PositiveVerification.Expr.input n
      (PositiveVerification.selectedCellLeft C epsilon e)) =
      selectedInput (encodeRegion C) epsilon n 0 e := by
  cases epsilon
  · exact (cellInput_left_eq_pack C n e).symm
  · exact (cellInput_bottom_eq_pack C n e).symm

@[simp] theorem pack_selectedRight (C : RegionCode) (epsilon : Bool) (n : ℕ)
    (e : Fin C.cellCount) :
    packAffine (PositiveVerification.Expr.input n
      (PositiveVerification.selectedCellRight C epsilon e)) =
      selectedInput (encodeRegion C) epsilon n 1 e := by
  cases epsilon
  · exact (cellInput_right_eq_pack C n e).symm
  · exact (cellInput_top_eq_pack C n e).symm

@[simp] theorem pack_selectedBottom (C : RegionCode) (epsilon : Bool) (n : ℕ)
    (e : Fin C.cellCount) :
    packAffine (PositiveVerification.Expr.input n
      (PositiveVerification.selectedCellBottom C epsilon e)) =
      selectedInput (encodeRegion C) epsilon n 2 e := by
  cases epsilon
  · exact (cellInput_bottom_eq_pack C n e).symm
  · exact (cellInput_left_eq_pack C n e).symm

@[simp] theorem pack_selectedTop (C : RegionCode) (epsilon : Bool) (n : ℕ)
    (e : Fin C.cellCount) :
    packAffine (PositiveVerification.Expr.input n
      (PositiveVerification.selectedCellTop C epsilon e)) =
      selectedInput (encodeRegion C) epsilon n 3 e := by
  cases epsilon
  · exact (cellInput_top_eq_pack C n e).symm
  · exact (cellInput_right_eq_pack C n e).symm

@[simp] theorem pack_horizontalEq {C : RegionCode} {h v : ℕ} (a b : AffineExpr C h) :
    Affine.Native.packFormula
      (PositiveVerification.Formula.horizontalEq a b : Formula C h v) =
      horizontalEq (packAffine a) (packAffine b) := by
  simp only [PositiveVerification.Formula.horizontalEq,
    Affine.Native.packFormula_conjunction, pack_horizontalLe, horizontalEq]

@[simp] theorem pack_verticalEq {C : RegionCode} {h v : ℕ} (a b : AffineExpr C v) :
    Affine.Native.packFormula
      (PositiveVerification.Formula.verticalEq a b : Formula C h v) =
      verticalEq (packAffine a) (packAffine b) := by
  simp only [PositiveVerification.Formula.verticalEq,
    Affine.Native.packFormula_conjunction, pack_verticalLe, verticalEq]

@[simp] theorem pack_sameCentre {C : RegionCode} {h v : ℕ}
    (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v) :
    Affine.Native.packFormula
      (PositiveVerification.sameCentreFormula cx cx' cy cy') =
      sameCentre (packAffine cx) (packAffine cx') (packAffine cy) (packAffine cy') := by
  simp only [PositiveVerification.sameCentreFormula,
    Affine.Native.packFormula_conjunction, pack_horizontalEq,
    pack_verticalEq, sameCentre]

@[simp] theorem pack_openCell {C : RegionCode} {h v : ℕ} (epsilon : Bool)
    (e : Fin C.cellCount) (cx x : AffineExpr C h) (cy y : AffineExpr C v) :
    Affine.Native.packFormula
      (PositiveVerification.openCellFormula epsilon e cx x cy y) =
      openCell (encodeRegion C) epsilon h v e
        (packAffine cx) (packAffine x) (packAffine cy) (packAffine y) := by
  simp only [PositiveVerification.openCellFormula, pack_andList, List.map_cons,
    List.map_nil, pack_horizontalLt, pack_verticalLt, pack_add,
    pack_selectedLeft, pack_selectedRight, pack_selectedBottom, pack_selectedTop, openCell]

@[simp] theorem pack_closedCell {C : RegionCode} {h v : ℕ} (epsilon : Bool)
    (e : Fin C.cellCount) (cx x : AffineExpr C h) (cy y : AffineExpr C v) :
    Affine.Native.packFormula
      (PositiveVerification.closedCellFormula epsilon e cx x cy y) =
      closedCell (encodeRegion C) epsilon h v e
        (packAffine cx) (packAffine x) (packAffine cy) (packAffine y) := by
  simp only [PositiveVerification.closedCellFormula, pack_andList, List.map_cons,
    List.map_nil, pack_horizontalLe, pack_verticalLe, pack_add,
    pack_selectedLeft, pack_selectedRight, pack_selectedBottom, pack_selectedTop, closedCell]

@[simp] theorem pack_cellNonoverlap {C : RegionCode} {h v : ℕ} (epsilon : Bool)
    (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v) :
    Affine.Native.packFormula
      (PositiveVerification.cellNonoverlapFormula epsilon e e' cx cx' cy cy') =
      cellNonoverlap (encodeRegion C) epsilon h v e e'
        (packAffine cx) (packAffine cx') (packAffine cy) (packAffine cy') := by
  simp only [PositiveVerification.cellNonoverlapFormula, pack_orList, List.map_cons,
    List.map_nil, pack_horizontalLe, pack_verticalLe, pack_add,
    pack_selectedLeft, pack_selectedRight, pack_selectedBottom, pack_selectedTop, cellNonoverlap]

end Native
end Tiling.AxisParallel.Decidability.CertificateFormulas
