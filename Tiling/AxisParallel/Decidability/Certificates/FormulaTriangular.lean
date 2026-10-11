import Tiling.AxisParallel.Decidability.Certificates.FormulaCells

/-! Effective finite triangular-slab certificate formulas. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas.Triangular

open Tiling.AxisParallel.Decidability.Affine
open Tiling.AxisParallel.Terminal.Executable

instance : Inhabited RawTriangularPieceCode := ⟨⟨0, 0⟩⟩

abbrev Index := ℕ × ℕ
abbrev FiniteIndex := ℕ × ℕ × ℕ

def triangularPieceCount (c : RawTriangularCode) : ℕ := c.pieces.length
def triangularPiece (c : RawTriangularCode) (j : ℕ) : RawTriangularPieceCode :=
  c.pieces.getD j ⟨0, 0⟩
def triangularIntervalIndices (c : RawTriangularCode) : List Index :=
  (List.range (triangularPieceCount c)).flatMap fun j =>
    (List.range (triangularPiece c j).intervalCount).map fun ell => (j, ell)
def triangularRepresentativeIndices (c : RawTriangularCode) : List Index :=
  (List.range (triangularPieceCount c)).flatMap fun j =>
    (List.range (triangularPiece c j).representativeCount).map fun r => (j, r)
def triangularTotalIntervalCount (c : RawTriangularCode) : ℕ :=
  (c.pieces.map RawTriangularPieceCode.intervalCount).sum
def triangularTotalRepresentativeCount (c : RawTriangularCode) : ℕ :=
  (c.pieces.map RawTriangularPieceCode.representativeCount).sum
def triangularIntervalOrdinal (c : RawTriangularCode) (i : Index) : ℕ :=
  ((c.pieces.take i.1).map RawTriangularPieceCode.intervalCount).sum + i.2
def triangularRepresentativeOrdinal (c : RawTriangularCode) (i : Index) : ℕ :=
  ((c.pieces.take i.1).map RawTriangularPieceCode.representativeCount).sum + i.2
def triangularHorizontalVariableCount (c : RawTriangularCode) : ℕ :=
  1 + 2 * triangularTotalIntervalCount c + triangularTotalRepresentativeCount c
def triangularVerticalVariableCount (c : RawTriangularCode) : ℕ :=
  1 + triangularPieceCount c + triangularTotalRepresentativeCount c
def triangularBetaId : ℕ := 0
def triangularIntervalLeftId (c : RawTriangularCode) (i : Index) : ℕ :=
  1 + 2 * triangularIntervalOrdinal c i
def triangularIntervalRightId (c : RawTriangularCode) (i : Index) : ℕ :=
  2 + 2 * triangularIntervalOrdinal c i
def triangularRepresentativeXId (c : RawTriangularCode) (i : Index) : ℕ :=
  1 + 2 * triangularTotalIntervalCount c + triangularRepresentativeOrdinal c i
def triangularAlphaId : ℕ := 0
def triangularShearId (j : ℕ) : ℕ := 1 + j
def triangularRepresentativeYId (c : RawTriangularCode) (i : Index) : ℕ :=
  1 + triangularPieceCount c + triangularRepresentativeOrdinal c i
def centeredInteger (radius i : ℕ) : ℤ := Int.ofNat i - Int.ofNat radius

def triangularFiniteIndices (c : RawTriangularCode) (j : ℕ) : List FiniteIndex :=
  (List.range (triangularPiece c j).representativeCount).flatMap fun r =>
    (List.range (2 * (c.checkingRadius + 1) + 1)).flatMap fun n =>
      (List.range (2 * (2 * c.checkingRadius + 3) + 1)).map fun k => (r, n, k)

def triH (region : RegionInput) (code : RawTriangularCode) (shift id : ℕ) : Expr :=
  affineVariable (triangularHorizontalVariableCount code + shift) region.1 (id + shift)
def triV (region : RegionInput) (code : RawTriangularCode) (shift id : ℕ) : Expr :=
  affineVariable (triangularVerticalVariableCount code + shift) region.1 (id + shift)
def triangularCentreX (region : RegionInput) (code : RawTriangularCode) (shift j : ℕ)
    (i : FiniteIndex) : Expr :=
  let rep : Index := (j, i.1)
  exprAdd (triH region code shift (triangularRepresentativeXId code rep))
    (exprScale (centeredInteger (code.checkingRadius + 1) i.2.1 : ℚ)
      (triH region code shift triangularBetaId))
def triangularCentreY (region : RegionInput) (code : RawTriangularCode) (shift j : ℕ)
    (i : FiniteIndex) : Expr :=
  let rep : Index := (j, i.1)
  exprAdd
    (exprAdd (triV region code shift (triangularRepresentativeYId code rep))
      (exprScale (centeredInteger (code.checkingRadius + 1) i.2.1 : ℚ)
        (triV region code shift (triangularShearId j))))
    (exprScale (centeredInteger (2 * code.checkingRadius + 3) i.2.2 : ℚ)
      (triV region code shift triangularAlphaId))

def triangularBaseOpenFormula (region : RegionInput) (code : RawTriangularCode)
    (shift j : ℕ) (x : Expr) : Code :=
  let intervalIds := List.range (triangularPiece code j).intervalCount
  orList (intervalIds.flatMap fun ell =>
    ([-1, 0, 1] : List ℤ).map fun q =>
      let idx : Index := (j, ell)
      let left := exprAdd (triH region code shift (triangularIntervalLeftId code idx))
        (exprScale (q : ℚ) (triH region code shift triangularBetaId))
      let right := exprAdd (triH region code shift (triangularIntervalRightId code idx))
        (exprScale (q : ℚ) (triH region code shift triangularBetaId))
      conjunction (horizontalLt left x) (horizontalLt x right))

def triangularBaseClosedFormula (region : RegionInput) (code : RawTriangularCode)
    (shift j : ℕ) (x : Expr) : Code :=
  let intervalIds := List.range (triangularPiece code j).intervalCount
  orList (intervalIds.flatMap fun ell =>
    ([-1, 0, 1] : List ℤ).map fun q =>
      let idx : Index := (j, ell)
      let left := exprAdd (triH region code shift (triangularIntervalLeftId code idx))
        (exprScale (q : ℚ) (triH region code shift triangularBetaId))
      let right := exprAdd (triH region code shift (triangularIntervalRightId code idx))
        (exprScale (q : ℚ) (triH region code shift triangularBetaId))
      conjunction (horizontalLe left x) (horizontalLe x right))

def diameterInput (region : RegionInput) (n a b : ℕ) : Expr :=
  exprSub (affineInput n (basisArray region.1 a 1))
    (affineInput n (basisArray region.1 b 1))

def triangularBody (region : RegionInput) (code : RawTriangularCode) : Code :=
  let h := triangularHorizontalVariableCount code
  let v := triangularVerticalVariableCount code
  let zeroH := affineZero h region.1
  let zeroV := affineZero v region.1
  let beta := triH region code 0 triangularBetaId
  let alpha := triV region code 0 triangularAlphaId
  let pieces := List.range (triangularPieceCount code)
  let intervals := triangularIntervalIndices code
  let reps := triangularRepresentativeIndices code
  let vertices := List.range region.1
  let cells := List.range region.2.length
  let positivity : Code :=
    conjunction (horizontalLt zeroH beta) (verticalLt zeroV alpha)
  let shearChecks := pieces.map fun j => andList
    [verticalLe zeroV (triV region code 0 (triangularShearId j)),
     verticalLt (triV region code 0 (triangularShearId j)) alpha]
  let intervalChecks := intervals.map fun i =>
    let a := triH region code 0 (triangularIntervalLeftId code i)
    let b := triH region code 0 (triangularIntervalRightId code i)
    andList [horizontalLe zeroH a, horizontalLt a b, horizontalLe b beta]
  let intervalDisjoint := intervals.flatMap fun i => intervals.map fun i' =>
    if i = i' then truth else disjunction
      (horizontalLe (triH region code 0 (triangularIntervalRightId code i))
        (triH region code 0 (triangularIntervalLeftId code i')))
      (horizontalLe (triH region code 0 (triangularIntervalRightId code i'))
        (triH region code 0 (triangularIntervalLeftId code i)))
  let partitionCoverage : Code := forallHorizontal
    (let x := affineVariable (h + 1) region.1 0
     let beta' := triH region code 1 triangularBetaId
     implication
       (andList [horizontalLt (affineZero (h + 1) region.1) x, horizontalLt x beta'])
       (orList (intervals.map fun i =>
         let a := triH region code 1 (triangularIntervalLeftId code i)
         let b := triH region code 1 (triangularIntervalRightId code i)
         conjunction (horizontalLe a x) (horizontalLe x b))))
  let representativeChecks := reps.map fun i => andList
    [horizontalLe zeroH (triH region code 0 (triangularRepresentativeXId code i)),
     horizontalLt (triH region code 0 (triangularRepresentativeXId code i)) beta,
     verticalLe zeroV (triV region code 0 (triangularRepresentativeYId code i)),
     verticalLt (triV region code 0 (triangularRepresentativeYId code i)) alpha]
  let diameterChecks := andList
    ((vertices.flatMap fun a => vertices.map fun b =>
      let d := diameterInput region h a b
      andList
        [horizontalLt d (exprScale (Int.ofNat code.checkingRadius) beta),
         horizontalLt (exprNeg d) (exprScale (Int.ofNat code.checkingRadius) beta)]) ++
     (vertices.flatMap fun a => vertices.map fun b =>
      let d := diameterInput region v a b
      andList
        [verticalLt d (exprScale (Int.ofNat code.checkingRadius) alpha),
         verticalLt (exprNeg d) (exprScale (Int.ofNat code.checkingRadius) alpha)]))
  let packingChecks := andList (pieces.flatMap fun j =>
    let indices := triangularFiniteIndices code j
    indices.flatMap fun i => indices.map fun i' =>
      if i = i' then truth else
        let cx := triangularCentreX region code 0 j i
        let cy := triangularCentreY region code 0 j i
        let cx' := triangularCentreX region code 0 j i'
        let cy' := triangularCentreY region code 0 j i'
        disjunction (sameCentre cx cx' cy cy')
          (andList (cells.flatMap fun e => cells.map fun e' =>
            cellNonoverlap region code.orientation h v e e' cx cx' cy cy')))
  let leakageChecks := andList (pieces.map fun j => forallHorizontal
    (forallVertical
      (let x := affineVariable (h + 1) region.1 0
       let y := affineVariable (v + 1) region.1 0
       let beta' := triH region code 1 triangularBetaId
       let alpha' := triV region code 1 triangularAlphaId
       let hit := orList ((triangularFiniteIndices code j).flatMap fun i =>
         cells.map fun e => openCell region code.orientation (h + 1) (v + 1) e
           (triangularCentreX region code 1 j i) x (triangularCentreY region code 1 j i) y)
       implication
         (andList
           [horizontalLt (affineZero (h + 1) region.1) x, horizontalLt x beta',
            verticalLt (affineZero (v + 1) region.1) y, verticalLt y alpha', hit])
         (triangularBaseClosedFormula region code 1 j x))))
  let coverageChecks := andList (pieces.map fun j => forallHorizontal
    (forallVertical
      (let x := affineVariable (h + 1) region.1 0
       let y := affineVariable (v + 1) region.1 0
       let beta' := triH region code 1 triangularBetaId
       let alpha' := triV region code 1 triangularAlphaId
       let covered := orList ((triangularFiniteIndices code j).flatMap fun i =>
         cells.map fun e => closedCell region code.orientation (h + 1) (v + 1) e
           (triangularCentreX region code 1 j i) x (triangularCentreY region code 1 j i) y)
       implication
         (andList
           [horizontalLt (affineZero (h + 1) region.1) x, horizontalLt x beta',
            verticalLt (affineZero (v + 1) region.1) y, verticalLt y alpha',
            triangularBaseOpenFormula region code 1 j x])
         covered)))
  andList
    ([positivity, partitionCoverage, diameterChecks, packingChecks, leakageChecks,
        coverageChecks] ++
      shearChecks ++ intervalChecks ++ intervalDisjoint ++ representativeChecks)

def triangularSlabFormula (region : RegionInput) (code : RawTriangularCode) : Code :=
  if code.wellFormed then close (triangularHorizontalVariableCount code)
    (triangularVerticalVariableCount code) (triangularBody region code) else falsity

@[fun_prop] theorem c_triangularPieceCount {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularPieceCount (f0 x)) := by
  unfold triangularPieceCount
  fun_prop

@[fun_prop] theorem c_triangularPiece {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularPiece (f0 x) (f1 x)) := by
  unfold triangularPiece
  fun_prop

@[fun_prop] theorem c_triangularIntervalIndices {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularIntervalIndices (f0 x)) := by
  unfold triangularIntervalIndices
  fun_prop

@[fun_prop] theorem c_triangularRepresentativeIndices {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularRepresentativeIndices (f0 x)) := by
  unfold triangularRepresentativeIndices
  fun_prop

@[fun_prop] theorem c_triangularTotalIntervalCount {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularTotalIntervalCount (f0 x)) := by
  unfold triangularTotalIntervalCount
  fun_prop

@[fun_prop] theorem c_triangularTotalRepresentativeCount {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularTotalRepresentativeCount (f0 x)) := by
  unfold triangularTotalRepresentativeCount
  fun_prop

@[fun_prop] theorem c_triangularIntervalOrdinal {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularIntervalOrdinal (f0 x) (f1 x)) := by
  unfold triangularIntervalOrdinal
  fun_prop

@[fun_prop] theorem c_triangularRepresentativeOrdinal {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularRepresentativeOrdinal (f0 x) (f1 x)) := by
  unfold triangularRepresentativeOrdinal
  fun_prop

@[fun_prop] theorem c_triangularHorizontalVariableCount {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularHorizontalVariableCount (f0 x)) := by
  unfold triangularHorizontalVariableCount
  fun_prop

@[fun_prop] theorem c_triangularVerticalVariableCount {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode)
    (h0 : Computable f0) :
    Computable (fun x => triangularVerticalVariableCount (f0 x)) := by
  unfold triangularVerticalVariableCount
  fun_prop

@[fun_prop] theorem c_triangularIntervalLeftId {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularIntervalLeftId (f0 x) (f1 x)) := by
  unfold triangularIntervalLeftId
  fun_prop

@[fun_prop] theorem c_triangularIntervalRightId {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularIntervalRightId (f0 x) (f1 x)) := by
  unfold triangularIntervalRightId
  fun_prop

@[fun_prop] theorem c_triangularRepresentativeXId {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularRepresentativeXId (f0 x) (f1 x)) := by
  unfold triangularRepresentativeXId
  fun_prop

@[fun_prop] theorem c_triangularShearId {α : Type*} [Primcodable α]
    (f0 : α → ℕ)
    (h0 : Computable f0) :
    Computable (fun x => triangularShearId (f0 x)) := by
  unfold triangularShearId
  fun_prop

@[fun_prop] theorem c_triangularRepresentativeYId {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → Index)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularRepresentativeYId (f0 x) (f1 x)) := by
  unfold triangularRepresentativeYId
  fun_prop

@[fun_prop] theorem c_centeredInteger {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => centeredInteger (f0 x) (f1 x)) := by
  unfold centeredInteger
  fun_prop

@[fun_prop] theorem c_triangularFiniteIndices {α : Type*} [Primcodable α]
    (f0 : α → RawTriangularCode) (f1 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularFiniteIndices (f0 x) (f1 x)) := by
  unfold triangularFiniteIndices
  fun_prop

@[fun_prop] theorem c_triH {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) :
    Computable (fun x => triH (f0 x) (f1 x) (f2 x) (f3 x)) := by
  unfold triH
  fun_prop

@[fun_prop] theorem c_triV {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) :
    Computable (fun x => triV (f0 x) (f1 x) (f2 x) (f3 x)) := by
  unfold triV
  fun_prop

@[fun_prop] theorem c_triangularCentreX {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ) (f4 : α →
      FiniteIndex)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) (h4 :
      Computable f4) :
    Computable (fun x => triangularCentreX (f0 x) (f1 x) (f2 x) (f3 x) (f4 x)) := by
  unfold triangularCentreX
  fun_prop

@[fun_prop] theorem c_triangularCentreY {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ) (f4 : α →
      FiniteIndex)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) (h4 :
      Computable f4) :
    Computable (fun x => triangularCentreY (f0 x) (f1 x) (f2 x) (f3 x) (f4 x)) := by
  unfold triangularCentreY
  fun_prop

@[fun_prop] theorem c_triangularBaseOpenFormula {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ) (f4 : α → Expr)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) (h4 :
      Computable f4) :
    Computable (fun x => triangularBaseOpenFormula (f0 x) (f1 x) (f2 x) (f3 x) (f4 x)) := by
  unfold triangularBaseOpenFormula
  fun_prop

@[fun_prop] theorem c_triangularBaseClosedFormula {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode) (f2 : α → ℕ) (f3 : α → ℕ) (f4 : α → Expr)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) (h4 :
      Computable f4) :
    Computable (fun x => triangularBaseClosedFormula (f0 x) (f1 x) (f2 x) (f3 x) (f4 x)) := by
  unfold triangularBaseClosedFormula
  fun_prop

@[fun_prop] theorem c_diameterInput {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → ℕ) (f2 : α → ℕ) (f3 : α → ℕ)
    (h0 : Computable f0) (h1 : Computable f1) (h2 : Computable f2) (h3 : Computable f3) :
    Computable (fun x => diameterInput (f0 x) (f1 x) (f2 x) (f3 x)) := by
  unfold diameterInput
  fun_prop

@[fun_prop] theorem c_triangularBody {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularBody (f0 x) (f1 x)) := by
  dsimp only [triangularBody]
  fun_prop

@[fun_prop] theorem c_triangularSlabFormula {α : Type*} [Primcodable α]
    (f0 : α → RegionInput) (f1 : α → RawTriangularCode)
    (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => triangularSlabFormula (f0 x) (f1 x)) := by
  unfold triangularSlabFormula
  fun_prop

end Tiling.AxisParallel.Decidability.CertificateFormulas.Triangular
