import Tiling.AxisParallel.Decidability.Certificates.FormulaExpressions
import Tiling.AxisParallel.Decidability.Affine.FormulaPacking
import Tiling.AxisParallel.Terminal.LocalCoverSearch

/-!
# Finite formulas for negative certificates

These functions build the local packing and covering formulas from finite arrays.
The four bounds are horizontal diameter, vertical diameter, horizontal cell width,
and vertical cell width, each expressed as an integer combination of vertices.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.NegativeFormulas

open CertificateFormulas
open Tiling.AxisParallel.Decidability.Affine

abbrev Bounds := List ℤ × List ℤ × List ℤ × List ℤ

def constantExpr (m : ℕ) (coefficients : List ℤ) : Expr :=
  affineInput m (coefficients.map fun z : ℤ => (z : ℚ))

def variableExpr (region : RegionInput) (m i : ℕ) : Expr :=
  affineVariable m region.1 i

def translatedExpr (region : RegionInput) (m i side cell : ℕ) : Expr :=
  (basisArray m i 1, basisArray region.1 (cellSelector region side cell) 1)

def distinctCentres (region : RegionInput) (m i j : ℕ) : Code :=
  orList [horizontalLt (variableExpr region m i) (variableExpr region m j),
    horizontalLt (variableExpr region m j) (variableExpr region m i),
    verticalLt (variableExpr region m i) (variableExpr region m j),
    verticalLt (variableExpr region m j) (variableExpr region m i)]

def cellPairSeparated (region : RegionInput) (m i j a b : ℕ) : Code :=
  orList [horizontalLe (translatedExpr region m i 1 a) (translatedExpr region m j 0 b),
    horizontalLe (translatedExpr region m j 1 b) (translatedExpr region m i 0 a),
    verticalLe (translatedExpr region m i 3 a) (translatedExpr region m j 2 b),
    verticalLe (translatedExpr region m j 3 b) (translatedExpr region m i 2 a)]

def cellPairsSeparated (region : RegionInput) (m i j : ℕ) : Code :=
  andList ((List.range region.2.length).flatMap fun a =>
    (List.range region.2.length).map fun b => cellPairSeparated region m i j a b)

def centrePairPacking (region : RegionInput) (m i j : ℕ) : Code :=
  if i = j then truth else
    conjunction (distinctCentres region m i j) (cellPairsSeparated region m i j)

def packingFormula (region : RegionInput) (m : ℕ) : Code :=
  andList ((List.range m).flatMap fun i =>
    (List.range m).map fun j => centrePairPacking region m i j)

def withinBoundHorizontal (region : RegionInput) (m N : ℕ)
    (bound : List ℤ) (i : ℕ) : Code :=
  let b := exprScale (N : ℚ) (constantExpr m bound)
  conjunction (horizontalLe (exprNeg b) (variableExpr region m i))
    (horizontalLe (variableExpr region m i) b)

def withinBoundVertical (region : RegionInput) (m N : ℕ)
    (bound : List ℤ) (i : ℕ) : Code :=
  let b := exprScale (N : ℚ) (constantExpr m bound)
  conjunction (verticalLe (exprNeg b) (variableExpr region m i))
    (verticalLe (variableExpr region m i) b)

def relevanceFormula (region : RegionInput) (bounds : Bounds) (N m : ℕ) : Code :=
  andList ((List.range m).map fun i => conjunction
    (withinBoundHorizontal region m (N + 1) bounds.1 i)
    (withinBoundVertical region m (N + 1) bounds.2.1 i))

def outsideClosedCell (region : RegionInput) (m i a : ℕ) : Code :=
  negation (andList [
    horizontalLe (translatedExpr region (m + 1) (i + 1) 0 a) (variableExpr region (m + 1) 0),
    horizontalLe (variableExpr region (m + 1) 0) (translatedExpr region (m + 1) (i + 1) 1 a),
    verticalLe (translatedExpr region (m + 1) (i + 1) 2 a) (variableExpr region (m + 1) 0),
    verticalLe (variableExpr region (m + 1) 0) (translatedExpr region (m + 1) (i + 1) 3 a)])

def uncoveredPointBody (region : RegionInput) (bounds : Bounds) (N m : ℕ) : Code :=
  let h := exprScale (N : ℚ) (constantExpr (m + 1) bounds.1)
  let v := exprScale (N : ℚ) (constantExpr (m + 1) bounds.2.1)
  let x := variableExpr region (m + 1) 0
  andList ([horizontalLt (exprNeg h) x, horizontalLt x h,
    verticalLt (exprNeg v) x, verticalLt x v] ++
    (List.range m).flatMap fun i =>
      (List.range region.2.length).map fun a => outsideClosedCell region m i a)

def coverageFormula (region : RegionInput) (bounds : Bounds) (N m : ℕ) : Code :=
  negation (existsHorizontal (existsVertical (uncoveredPointBody region bounds N m)))

def localCoverFormula (region : RegionInput) (bounds : Bounds) (N m : ℕ) : Code :=
  closeVertical m (closeHorizontal m
    (andList [packingFormula region m, relevanceFormula region bounds N m,
      coverageFormula region bounds N m]))

def positiveSubdivisionFormula (bounds : Bounds) (N horizontal vertical : ℕ) : Code :=
  conjunction
    (horizontalLt (exprScale ((2 * (N + 1) : ℕ) : ℚ) (constantExpr 0 bounds.1))
      (exprScale (horizontal : ℚ) (constantExpr 0 bounds.2.2.1)))
    (verticalLt (exprScale ((2 * (N + 1) : ℕ) : ℚ) (constantExpr 0 bounds.2.1))
      (exprScale (vertical : ℚ) (constantExpr 0 bounds.2.2.2)))

def negativeCertificateFormula (region : RegionInput) (bounds : Bounds)
    (code : Tiling.AxisParallel.Terminal.Executable.RawNegativeCode) : Code :=
  if code.wellFormed then
    conjunction
      (positiveSubdivisionFormula bounds code.boxIndex
        code.horizontalSubdivisions code.verticalSubdivisions)
      (andList ((List.range (code.horizontalSubdivisions * code.verticalSubdivisions + 1)).map
        fun m => negation (localCoverFormula region bounds code.boxIndex m)))
  else falsity

def negativeFormula (region : RegionInput) (bounds : Bounds) (stage : ℕ) : Code :=
  match Tiling.AxisParallel.Terminal.Executable.wellFormedNegativeStage stage with
  | none => falsity
  | some code => negativeCertificateFormula region bounds code

end Tiling.AxisParallel.Decidability.NegativeFormulas
