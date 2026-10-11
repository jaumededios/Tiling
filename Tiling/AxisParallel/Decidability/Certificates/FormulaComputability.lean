import Tiling.AxisParallel.Decidability.Certificates.FormulaExpressions
import Tiling.Computability.FunProp

/-! Compositional computability rules for finite certificate syntax. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine
open PositiveCoding
open CertificateCoding
open Tiling.AxisParallel.Terminal.Executable



@[fun_prop] theorem c_affineZero {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => affineZero (f0 x) (f1 x)) :=
  affineZero_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_affineVariable {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (f2 : α → ℕ)
    (h0 : Computable f0)
    (h1 : Computable f1)
    (h2 : Computable f2) :
    Computable (fun x => affineVariable (f0 x) (f1 x) (f2 x)) :=
  affineVariable_primrec.to_comp.comp (h0.pair (h1.pair (h2)))

@[fun_prop] theorem c_affineInput {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → List ℚ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => affineInput (f0 x) (f1 x)) :=
  affineInput_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_basisArray {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (f2 : α → ℚ)
    (h0 : Computable f0)
    (h1 : Computable f1)
    (h2 : Computable f2) :
    Computable (fun x => basisArray (f0 x) (f1 x) (f2 x)) :=
  basisArray_primrec.to_comp.comp (h0.pair (h1.pair (h2)))

@[fun_prop] theorem c_cellInput {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → ℕ) (f2 : α → ℕ) (f3 : α → ℕ)
    (h0 : Computable f0)
    (h1 : Computable f1)
    (h2 : Computable f2)
    (h3 : Computable f3) :
    Computable (fun x => cellInput (f0 x) (f1 x) (f2 x) (f3 x)) :=
  cellInput_primrec.to_comp.comp (h0.pair (h1.pair (h2.pair (h3))))

@[fun_prop] theorem c_exprAdd {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => exprAdd (f0 x) (f1 x)) :=
  exprAdd_computable.comp h0 h1

@[fun_prop] theorem c_exprSub {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => exprSub (f0 x) (f1 x)) :=
  exprSub_computable.comp h0 h1

@[fun_prop] theorem c_exprScale {α : Type*} [Primcodable α]
    (f0 : α → ℚ) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => exprScale (f0 x) (f1 x)) :=
  exprScale_computable.comp h0 h1

@[fun_prop] theorem c_exprNeg {α : Type*} [Primcodable α]
    (f0 : α → Expr) (h0 : Computable f0) :
    Computable (fun x => exprNeg (f0 x)) :=
  exprNeg_computable.comp h0

@[fun_prop] theorem c_horizontalLe {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => horizontalLe (f0 x) (f1 x)) :=
  horizontalLe_computable.comp h0 h1

@[fun_prop] theorem c_horizontalLt {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => horizontalLt (f0 x) (f1 x)) :=
  horizontalLt_computable.comp h0 h1

@[fun_prop] theorem c_verticalLe {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => verticalLe (f0 x) (f1 x)) :=
  verticalLe_computable.comp h0 h1

@[fun_prop] theorem c_verticalLt {α : Type*} [Primcodable α]
    (f0 : α → Expr) (f1 : α → Expr) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => verticalLt (f0 x) (f1 x)) :=
  verticalLt_computable.comp h0 h1

@[fun_prop] theorem c_conjunction {α : Type*} [Primcodable α]
    (f0 : α → Code) (f1 : α → Code) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => conjunction (f0 x) (f1 x)) :=
  conjunction_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_disjunction {α : Type*} [Primcodable α]
    (f0 : α → Code) (f1 : α → Code) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => disjunction (f0 x) (f1 x)) :=
  disjunction_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_implication {α : Type*} [Primcodable α]
    (f0 : α → Code) (f1 : α → Code) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => implication (f0 x) (f1 x)) :=
  implication_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_negation {α : Type*} [Primcodable α]
    (f0 : α → Code) (h0 : Computable f0) :
    Computable (fun x => negation (f0 x)) :=
  negation_primrec.to_comp.comp h0

@[fun_prop] theorem c_existsHorizontal {α : Type*} [Primcodable α]
    (f0 : α → Code) (h0 : Computable f0) :
    Computable (fun x => existsHorizontal (f0 x)) :=
  existsHorizontal_primrec.to_comp.comp h0

@[fun_prop] theorem c_existsVertical {α : Type*} [Primcodable α]
    (f0 : α → Code) (h0 : Computable f0) :
    Computable (fun x => existsVertical (f0 x)) :=
  existsVertical_primrec.to_comp.comp h0

@[fun_prop] theorem c_andList {α : Type*} [Primcodable α]
    (f0 : α → List Code) (h0 : Computable f0) :
    Computable (fun x => andList (f0 x)) :=
  andList_primrec.to_comp.comp h0

@[fun_prop] theorem c_orList {α : Type*} [Primcodable α]
    (f0 : α → List Code) (h0 : Computable f0) :
    Computable (fun x => orList (f0 x)) :=
  orList_primrec.to_comp.comp h0

@[fun_prop] theorem c_closeHorizontal {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → Code) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => closeHorizontal (f0 x) (f1 x)) :=
  closeHorizontal_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_closeVertical {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → Code) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => closeVertical (f0 x) (f1 x)) :=
  closeVertical_primrec.to_comp.comp h0 h1

@[fun_prop] theorem c_pieceIntervals {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularPieceCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularPieceCode.intervalCount (f0 x)) :=
  rawPiece_intervalCount_primrec.to_comp.comp h0

@[fun_prop] theorem c_pieceRepresentatives {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularPieceCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularPieceCode.representativeCount (f0 x)) :=
  rawPiece_representativeCount_primrec.to_comp.comp h0

@[fun_prop] theorem c_triangularPieces {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularCode.pieces (f0 x)) :=
  rawTriangular_pieces_primrec.to_comp.comp h0

@[fun_prop] theorem c_triangularRadius {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularCode.checkingRadius (f0 x)) :=
  rawTriangular_checkingRadius_primrec.to_comp.comp h0

@[fun_prop] theorem c_triangularOrientation {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularCode.orientation (f0 x)) :=
  rawTriangular_orientation_primrec.to_comp.comp h0

@[fun_prop] theorem c_triangularWellFormed {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (h0 : Computable f0) :
    Computable (fun x => RawTriangularCode.wellFormed (f0 x)) :=
  rawTriangular_wellFormed_computable.comp h0

end Tiling.AxisParallel.Decidability.CertificateFormulas
