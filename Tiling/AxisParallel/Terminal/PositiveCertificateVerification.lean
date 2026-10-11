import Tiling.AxisParallel.Terminal.ExecutableInput
import Tiling.AxisParallel.Terminal.ExecutableInputSemantics
import Tiling.AxisParallel.Terminal.CertificateCoding
import Tiling.AxisParallel.Terminal.AffineCompilerCorrectness
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Tiling.AxisParallel.Terminal.AffineCompiler
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Terminal.CommonPeriodAssembly

/-!
# T17 positive-certificate verification: complete statement packet

This Stage-1 file materializes the two finite formulas and the executable positive verifier.
Everything before `Semantic contracts` is runtime data: it contains no `Real`, no geometric set,
and no proof-bearing certificate.  The real witnesses occur only in the semantics and obligations.

Eventual owner: `Tiling/AxisParallel/Terminal/PositiveCertificateVerification.lean`.
-/

open scoped BigOperators Pointwise
open Set

namespace Tiling.AxisParallel.Terminal.Executable.PositiveVerification

/-! ## Formula and affine-expression combinators -/

namespace Expr

def zero (C : RegionCode) (n : Nat) : AffineExpr C n :=
  ⟨fun _ => 0, Coeff.zero C⟩

def var (C : RegionCode) (n id : Nat) : AffineExpr C n :=
  ⟨fun i => if i.val = id then 1 else 0, Coeff.zero C⟩

def input {C : RegionCode} (n : Nat) (a : Coeff C) : AffineExpr C n :=
  ⟨fun _ => 0, a⟩

def add {C : RegionCode} {n : Nat} (a b : AffineExpr C n) : AffineExpr C n :=
  ⟨fun i => a.variableCoefficient i + b.variableCoefficient i,
    Coeff.add a.inputConstant b.inputConstant⟩

def neg {C : RegionCode} {n : Nat} (a : AffineExpr C n) : AffineExpr C n :=
  ⟨fun i => -a.variableCoefficient i, Coeff.neg a.inputConstant⟩

def sub {C : RegionCode} {n : Nat} (a b : AffineExpr C n) : AffineExpr C n :=
  add a (neg b)

/-- Scale a constant-free variable expression.  Every call below has zero `inputConstant`; input
coefficients enter later through `input` and are never rationally scaled. -/
def scale {C : RegionCode} {n : Nat} (q : Rat) (a : AffineExpr C n) : AffineExpr C n :=
  ⟨fun i => q * a.variableCoefficient i,
    fun i => q.num * a.inputConstant i⟩

end Expr

namespace Formula

def andList {C : RegionCode} {h v : Nat} : List (Formula C h v) → Formula C h v
  | [] => .truth
  | p :: ps => .conjunction p (andList ps)

def orList {C : RegionCode} {h v : Nat} : List (Formula C h v) → Formula C h v
  | [] => .falsity
  | p :: ps => .disjunction p (orList ps)

def implication {C : RegionCode} {h v : Nat} (p q : Formula C h v) : Formula C h v :=
  .disjunction (.negation p) q

def horizontalEq {C : RegionCode} {h v : Nat} (a b : AffineExpr C h) : Formula C h v :=
  .conjunction (.horizontalLe a b) (.horizontalLe b a)

def verticalEq {C : RegionCode} {h v : Nat} (a b : AffineExpr C v) : Formula C h v :=
  .conjunction (.verticalLe a b) (.verticalLe b a)

def forallHorizontal {C : RegionCode} {h v : Nat}
    (p : Formula C (h + 1) v) : Formula C h v :=
  .negation (.existsHorizontal (.negation p))

def forallVertical {C : RegionCode} {h v : Nat}
    (p : Formula C h (v + 1)) : Formula C h v :=
  .negation (.existsVertical (.negation p))

def closeHorizontal {C : RegionCode} {v : Nat} :
    (h : Nat) → Formula C h v → Formula C 0 v
  | 0, p => p
  | h + 1, p => closeHorizontal h (.existsHorizontal p)

def closeVertical {C : RegionCode} :
    (v : Nat) → Formula C 0 v → Formula C 0 0
  | 0, p => p
  | v + 1, p => closeVertical v (.existsVertical p)

def close {C : RegionCode} {h v : Nat} (p : Formula C h v) : Formula C 0 0 :=
  closeVertical v (closeHorizontal h p)

/-- Exchange the two coordinate sorts, their variable blocks, and their quantifiers. -/
def coordinateSwap {C : RegionCode} : {h v : Nat} → Formula C h v → Formula C v h
  | _, _, .truth => .truth
  | _, _, .falsity => .falsity
  | _, _, .horizontalLe a b => .verticalLe a b
  | _, _, .horizontalLt a b => .verticalLt a b
  | _, _, .verticalLe a b => .horizontalLe a b
  | _, _, .verticalLt a b => .horizontalLt a b
  | _, _, .conjunction p q => .conjunction (coordinateSwap p) (coordinateSwap q)
  | _, _, .disjunction p q => .disjunction (coordinateSwap p) (coordinateSwap q)
  | _, _, .negation p => .negation (coordinateSwap p)
  | _, _, .existsHorizontal p => .existsVertical (coordinateSwap p)
  | _, _, .existsVertical p => .existsHorizontal (coordinateSwap p)

def orientClosed {C : RegionCode} (epsilon : Bool) (p : Formula C 0 0) : Formula C 0 0 :=
  if epsilon then coordinateSwap p else p

end Formula

/-! ## Finite indices and exact variable identifiers -/

def triangularPieceCount (c : RawTriangularCode) : Nat := c.pieces.length

def triangularPiece (c : RawTriangularCode) (j : Fin (triangularPieceCount c)) :
    RawTriangularPieceCode := c.pieces.get j

abbrev TriangularIntervalIndex (c : RawTriangularCode) :=
  (j : Fin (triangularPieceCount c)) × Fin (triangularPiece c j).intervalCount

abbrev TriangularRepresentativeIndex (c : RawTriangularCode) :=
  (j : Fin (triangularPieceCount c)) × Fin (triangularPiece c j).representativeCount

def triangularIntervalIndices (c : RawTriangularCode) : List (TriangularIntervalIndex c) :=
  (List.ofFn fun j : Fin (triangularPieceCount c) => j).flatMap fun j =>
    List.ofFn fun ell : Fin (triangularPiece c j).intervalCount => ⟨j, ell⟩

def triangularRepresentativeIndices (c : RawTriangularCode) :
    List (TriangularRepresentativeIndex c) :=
  (List.ofFn fun j : Fin (triangularPieceCount c) => j).flatMap fun j =>
    List.ofFn fun r : Fin (triangularPiece c j).representativeCount => ⟨j, r⟩

def triangularTotalIntervalCount (c : RawTriangularCode) : Nat :=
  (c.pieces.map RawTriangularPieceCode.intervalCount).sum

def triangularTotalRepresentativeCount (c : RawTriangularCode) : Nat :=
  (c.pieces.map RawTriangularPieceCode.representativeCount).sum

def triangularIntervalOrdinal (c : RawTriangularCode)
    (i : TriangularIntervalIndex c) : Nat :=
  ((c.pieces.take i.1.val).map RawTriangularPieceCode.intervalCount).sum + i.2.val

def triangularRepresentativeOrdinal (c : RawTriangularCode)
    (i : TriangularRepresentativeIndex c) : Nat :=
  ((c.pieces.take i.1.val).map RawTriangularPieceCode.representativeCount).sum + i.2.val

def triangularHorizontalVariableCount (c : RawTriangularCode) : Nat :=
  1 + 2 * triangularTotalIntervalCount c + triangularTotalRepresentativeCount c

def triangularVerticalVariableCount (c : RawTriangularCode) : Nat :=
  1 + triangularPieceCount c + triangularTotalRepresentativeCount c

def triangularBetaId : Nat := 0
def triangularIntervalLeftId (c : RawTriangularCode)
    (i : TriangularIntervalIndex c) : Nat :=
  1 + 2 * triangularIntervalOrdinal c i
def triangularIntervalRightId (c : RawTriangularCode)
    (i : TriangularIntervalIndex c) : Nat :=
  2 + 2 * triangularIntervalOrdinal c i
def triangularRepresentativeXId (c : RawTriangularCode)
    (i : TriangularRepresentativeIndex c) : Nat :=
  1 + 2 * triangularTotalIntervalCount c + triangularRepresentativeOrdinal c i

def triangularAlphaId : Nat := 0
def triangularShearId (j : Nat) : Nat := 1 + j
def triangularRepresentativeYId (c : RawTriangularCode)
    (i : TriangularRepresentativeIndex c) : Nat :=
  1 + triangularPieceCount c + triangularRepresentativeOrdinal c i

/-- The integer represented by position `i` in the closed interval `[-radius,radius]`. -/
def centeredInteger {radius : Nat} (i : Fin (2 * radius + 1)) : Int :=
  Int.ofNat i.val - Int.ofNat radius

abbrev TriangularFirstIndex (c : RawTriangularCode) := Fin (2 * (c.checkingRadius + 1) + 1)
abbrev TriangularSecondIndex (c : RawTriangularCode) :=
  Fin (2 * (2 * c.checkingRadius + 3) + 1)

abbrev TriangularFiniteIndex (c : RawTriangularCode) (j : Fin (triangularPieceCount c)) :=
  Fin (triangularPiece c j).representativeCount × TriangularFirstIndex c × TriangularSecondIndex c

def triangularFiniteIndices (c : RawTriangularCode) (j : Fin (triangularPieceCount c)) :
    List (TriangularFiniteIndex c j) :=
  (List.ofFn fun r : Fin (triangularPiece c j).representativeCount => r).flatMap fun r =>
    (List.ofFn fun n : TriangularFirstIndex c => n).flatMap fun n =>
      List.ofFn fun k : TriangularSecondIndex c => (r, n, k)

abbrev LatticeBoundedInteger (radius : Nat) := Fin (2 * radius + 1)
abbrev LatticeFiniteIndex (c : RawLatticeCode) :=
  Fin c.representativeCount × LatticeBoundedInteger c.firstIndexBound ×
    LatticeBoundedInteger c.secondIndexBound

def latticeFiniteIndices (c : RawLatticeCode) : List (LatticeFiniteIndex c) :=
  ((List.ofFn fun r : Fin c.representativeCount => r).flatMap fun r =>
    (List.ofFn fun n : LatticeBoundedInteger c.firstIndexBound => n).flatMap fun n =>
      List.ofFn fun m : LatticeBoundedInteger c.secondIndexBound => (r, n, m)).filter
        fun i => decide ((centeredInteger i.2.1).natAbs < c.firstIndexBound ∧
          (centeredInteger i.2.2).natAbs < c.secondIndexBound)

def latticeHorizontalVariableCount (c : RawLatticeCode) : Nat := 4 + c.representativeCount
def latticeVerticalVariableCount (c : RawLatticeCode) : Nat := 3 + c.representativeCount

def latticeFirstPeriodXId : Nat := 0
def latticeSecondPeriodXId : Nat := 1
def latticeRepresentativeXId (r : Nat) : Nat := 2 + r
def latticeHorizontalBoundId (c : RawLatticeCode) : Nat := 2 + c.representativeCount
def latticeFirstPeriodAbsoluteXBoundId (c : RawLatticeCode) : Nat :=
  3 + c.representativeCount

def latticeFirstPeriodYId : Nat := 0
def latticeSecondPeriodYId : Nat := 1
def latticeRepresentativeYId (r : Nat) : Nat := 2 + r
def latticeVerticalBoundId (c : RawLatticeCode) : Nat := 2 + c.representativeCount

/-! ## Oriented cell macros -/

def selectedCellLeft (C : RegionCode) (epsilon : Bool) (e : Fin C.cellCount) : Coeff C :=
  if epsilon then Coeff.cellBottom e else Coeff.cellLeft e

def selectedCellRight (C : RegionCode) (epsilon : Bool) (e : Fin C.cellCount) : Coeff C :=
  if epsilon then Coeff.cellTop e else Coeff.cellRight e

def selectedCellBottom (C : RegionCode) (epsilon : Bool) (e : Fin C.cellCount) : Coeff C :=
  if epsilon then Coeff.cellLeft e else Coeff.cellBottom e

def selectedCellTop (C : RegionCode) (epsilon : Bool) (e : Fin C.cellCount) : Coeff C :=
  if epsilon then Coeff.cellRight e else Coeff.cellTop e

def openCellFormula {C : RegionCode} {h v : Nat} (epsilon : Bool) (e : Fin C.cellCount)
    (cx x : AffineExpr C h) (cy y : AffineExpr C v) : Formula C h v :=
  Formula.andList
    [.horizontalLt (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x,
     .horizontalLt x (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))),
     .verticalLt (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y,
     .verticalLt y (Expr.add cy (Expr.input v (selectedCellTop C epsilon e)))]

def closedCellFormula {C : RegionCode} {h v : Nat} (epsilon : Bool) (e : Fin C.cellCount)
    (cx x : AffineExpr C h) (cy y : AffineExpr C v) : Formula C h v :=
  Formula.andList
    [.horizontalLe (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x,
     .horizontalLe x (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))),
     .verticalLe (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y,
     .verticalLe y (Expr.add cy (Expr.input v (selectedCellTop C epsilon e)))]

def sameCentreFormula {C : RegionCode} {h v : Nat}
    (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v) : Formula C h v :=
  .conjunction (Formula.horizontalEq cx cx') (Formula.verticalEq cy cy')

def cellNonoverlapFormula {C : RegionCode} {h v : Nat} (epsilon : Bool)
    (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v) :
    Formula C h v :=
  Formula.orList
    [.horizontalLe (Expr.add cx (Expr.input h (selectedCellRight C epsilon e)))
        (Expr.add cx' (Expr.input h (selectedCellLeft C epsilon e'))),
     .horizontalLe (Expr.add cx' (Expr.input h (selectedCellRight C epsilon e')))
        (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))),
     .verticalLe (Expr.add cy (Expr.input v (selectedCellTop C epsilon e)))
        (Expr.add cy' (Expr.input v (selectedCellBottom C epsilon e'))),
     .verticalLe (Expr.add cy' (Expr.input v (selectedCellTop C epsilon e')))
        (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e)))]

/-! ## The triangular-slab formula -/

def triH (C : RegionCode) (code : RawTriangularCode) (shift id : Nat) :
    AffineExpr C (triangularHorizontalVariableCount code + shift) :=
  Expr.var C _ (id + shift)

def triV (C : RegionCode) (code : RawTriangularCode) (shift id : Nat) :
    AffineExpr C (triangularVerticalVariableCount code + shift) :=
  Expr.var C _ (id + shift)

def triangularCentreX (C : RegionCode) (code : RawTriangularCode) (shift : Nat)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j) :
    AffineExpr C (triangularHorizontalVariableCount code + shift) :=
  let rep : TriangularRepresentativeIndex code := ⟨j, i.1⟩
  Expr.add (triH C code shift (triangularRepresentativeXId code rep))
    (Expr.scale (centeredInteger i.2.1) (triH C code shift triangularBetaId))

def triangularCentreY (C : RegionCode) (code : RawTriangularCode) (shift : Nat)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j) :
    AffineExpr C (triangularVerticalVariableCount code + shift) :=
  let rep : TriangularRepresentativeIndex code := ⟨j, i.1⟩
  Expr.add
    (Expr.add (triV C code shift (triangularRepresentativeYId code rep))
      (Expr.scale (centeredInteger i.2.1) (triV C code shift (triangularShearId j.val))))
    (Expr.scale (centeredInteger i.2.2) (triV C code shift triangularAlphaId))

def triangularBaseOpenFormula {v : Nat} (C : RegionCode) (code : RawTriangularCode)
    (shift : Nat) (j : Fin (triangularPieceCount code))
    (x : AffineExpr C (triangularHorizontalVariableCount code + shift)) :
    Formula C (triangularHorizontalVariableCount code + shift) v :=
  let intervalIds :=
    List.ofFn fun ell : Fin (triangularPiece code j).intervalCount => ell
  Formula.orList (intervalIds.flatMap fun ell =>
    ([-1, 0, 1] : List Int).map fun q =>
      let idx : TriangularIntervalIndex code := ⟨j, ell⟩
      let left := Expr.add (triH C code shift (triangularIntervalLeftId code idx))
        (Expr.scale q (triH C code shift triangularBetaId))
      let right := Expr.add (triH C code shift (triangularIntervalRightId code idx))
        (Expr.scale q (triH C code shift triangularBetaId))
      .conjunction (.horizontalLt left x) (.horizontalLt x right))

def triangularBaseClosedFormula {v : Nat} (C : RegionCode) (code : RawTriangularCode)
    (shift : Nat) (j : Fin (triangularPieceCount code))
    (x : AffineExpr C (triangularHorizontalVariableCount code + shift)) :
    Formula C (triangularHorizontalVariableCount code + shift) v :=
  let intervalIds :=
    List.ofFn fun ell : Fin (triangularPiece code j).intervalCount => ell
  Formula.orList (intervalIds.flatMap fun ell =>
    ([-1, 0, 1] : List Int).map fun q =>
      let idx : TriangularIntervalIndex code := ⟨j, ell⟩
      let left := Expr.add (triH C code shift (triangularIntervalLeftId code idx))
        (Expr.scale q (triH C code shift triangularBetaId))
      let right := Expr.add (triH C code shift (triangularIntervalRightId code idx))
        (Expr.scale q (triH C code shift triangularBetaId))
      .conjunction (.horizontalLe left x) (.horizontalLe x right))

def triangularBody (C : RegionCode) (code : RawTriangularCode) :
    Formula C (triangularHorizontalVariableCount code) (triangularVerticalVariableCount code) :=
  let h := triangularHorizontalVariableCount code
  let v := triangularVerticalVariableCount code
  let zeroH := Expr.zero C h
  let zeroV := Expr.zero C v
  let beta := triH C code 0 triangularBetaId
  let alpha := triV C code 0 triangularAlphaId
  let pieces := List.ofFn fun j : Fin (triangularPieceCount code) => j
  let intervals := triangularIntervalIndices code
  let reps := triangularRepresentativeIndices code
  let vertices := List.ofFn fun i : Fin C.vertexCount => i
  let cells := List.ofFn fun e : Fin C.cellCount => e
  let positivity : Formula C h v :=
    .conjunction (.horizontalLt zeroH beta) (.verticalLt zeroV alpha)
  let shearChecks := pieces.map fun j => Formula.andList
    [.verticalLe zeroV (triV C code 0 (triangularShearId j.val)),
     .verticalLt (triV C code 0 (triangularShearId j.val)) alpha]
  let intervalChecks := intervals.map fun i =>
    let a := triH C code 0 (triangularIntervalLeftId code i)
    let b := triH C code 0 (triangularIntervalRightId code i)
    Formula.andList [.horizontalLe zeroH a, .horizontalLt a b, .horizontalLe b beta]
  let intervalDisjoint := intervals.flatMap fun i => intervals.map fun i' =>
    if i = i' then Formula.truth else Formula.disjunction
      (.horizontalLe (triH C code 0 (triangularIntervalRightId code i))
        (triH C code 0 (triangularIntervalLeftId code i')))
      (.horizontalLe (triH C code 0 (triangularIntervalRightId code i'))
        (triH C code 0 (triangularIntervalLeftId code i)))
  let partitionCoverage : Formula C h v := Formula.forallHorizontal
    (let x := Expr.var C (h + 1) 0
     let beta' := triH C code 1 triangularBetaId
     Formula.implication
       (Formula.andList [.horizontalLt (Expr.zero C (h + 1)) x, .horizontalLt x beta'])
       (Formula.orList (intervals.map fun i =>
         let a := triH C code 1 (triangularIntervalLeftId code i)
         let b := triH C code 1 (triangularIntervalRightId code i)
         .conjunction (.horizontalLe a x) (.horizontalLe x b))))
  let representativeChecks := reps.map fun i => Formula.andList
    [.horizontalLe zeroH (triH C code 0 (triangularRepresentativeXId code i)),
     .horizontalLt (triH C code 0 (triangularRepresentativeXId code i)) beta,
     .verticalLe zeroV (triV C code 0 (triangularRepresentativeYId code i)),
     .verticalLt (triV C code 0 (triangularRepresentativeYId code i)) alpha]
  let diameterChecks := Formula.andList
    ((vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input h (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      Formula.andList
        [.horizontalLt d (Expr.scale (Int.ofNat code.checkingRadius) beta),
         .horizontalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius) beta)]) ++
     (vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input v (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      Formula.andList
        [.verticalLt d (Expr.scale (Int.ofNat code.checkingRadius) alpha),
         .verticalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius) alpha)]))
  let packingChecks := Formula.andList (pieces.flatMap fun j =>
    let indices := triangularFiniteIndices code j
    indices.flatMap fun i => indices.map fun i' =>
      if i = i' then Formula.truth else
        let cx := triangularCentreX C code 0 j i
        let cy := triangularCentreY C code 0 j i
        let cx' := triangularCentreX C code 0 j i'
        let cy' := triangularCentreY C code 0 j i'
        Formula.disjunction (sameCentreFormula cx cx' cy cy')
          (Formula.andList (cells.flatMap fun e => cells.map fun e' =>
            cellNonoverlapFormula code.orientation e e' cx cx' cy cy')))
  let leakageChecks := Formula.andList (pieces.map fun j => Formula.forallHorizontal
    (Formula.forallVertical
      (let x := Expr.var C (h + 1) 0
       let y := Expr.var C (v + 1) 0
       let beta' := triH C code 1 triangularBetaId
       let alpha' := triV C code 1 triangularAlphaId
       let hit := Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
         cells.map fun e => openCellFormula code.orientation e
           (triangularCentreX C code 1 j i) x (triangularCentreY C code 1 j i) y)
       Formula.implication
         (Formula.andList
           [.horizontalLt (Expr.zero C (h + 1)) x, .horizontalLt x beta',
            .verticalLt (Expr.zero C (v + 1)) y, .verticalLt y alpha', hit])
         (triangularBaseClosedFormula C code 1 j x))))
  let coverageChecks := Formula.andList (pieces.map fun j => Formula.forallHorizontal
    (Formula.forallVertical
      (let x := Expr.var C (h + 1) 0
       let y := Expr.var C (v + 1) 0
       let beta' := triH C code 1 triangularBetaId
       let alpha' := triV C code 1 triangularAlphaId
       let covered := Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
         cells.map fun e => closedCellFormula code.orientation e
           (triangularCentreX C code 1 j i) x (triangularCentreY C code 1 j i) y)
       Formula.implication
         (Formula.andList
           [.horizontalLt (Expr.zero C (h + 1)) x, .horizontalLt x beta',
            .verticalLt (Expr.zero C (v + 1)) y, .verticalLt y alpha',
            triangularBaseOpenFormula C code 1 j x])
         covered)))
  Formula.andList
    ([positivity, partitionCoverage, diameterChecks, packingChecks, leakageChecks,
        coverageChecks] ++
      shearChecks ++ intervalChecks ++ intervalDisjoint ++ representativeChecks)

def triangularSlabFormula (C : RegionCode) (code : RawTriangularCode) : Formula C 0 0 :=
  if code.wellFormed then Formula.close (triangularBody C code) else .falsity

/-! ## The general-lattice formula -/

def latH (C : RegionCode) (code : RawLatticeCode) (shift id : Nat) :
    AffineExpr C (latticeHorizontalVariableCount code + shift) := Expr.var C _ (id + shift)

def latV (C : RegionCode) (code : RawLatticeCode) (shift id : Nat) :
    AffineExpr C (latticeVerticalVariableCount code + shift) := Expr.var C _ (id + shift)

def latticeCentreX (C : RegionCode) (code : RawLatticeCode) (shift : Nat)
    (i : LatticeFiniteIndex code) : AffineExpr C (latticeHorizontalVariableCount code + shift) :=
  Expr.add
    (Expr.add (latH C code shift (latticeRepresentativeXId i.1.val))
      (Expr.scale (centeredInteger i.2.1) (latH C code shift latticeFirstPeriodXId)))
    (Expr.scale (centeredInteger i.2.2) (latH C code shift latticeSecondPeriodXId))

def latticeCentreY (C : RegionCode) (code : RawLatticeCode) (shift : Nat)
    (i : LatticeFiniteIndex code) : AffineExpr C (latticeVerticalVariableCount code + shift) :=
  Expr.add
    (Expr.add (latV C code shift (latticeRepresentativeYId i.1.val))
      (Expr.scale (centeredInteger i.2.1) (latV C code shift latticeFirstPeriodYId)))
    (Expr.scale (centeredInteger i.2.2) (latV C code shift latticeSecondPeriodYId))

def latticeBody (C : RegionCode) (code : RawLatticeCode) :
    Formula C (latticeHorizontalVariableCount code) (latticeVerticalVariableCount code) :=
  let h := latticeHorizontalVariableCount code
  let v := latticeVerticalVariableCount code
  let zeroH := Expr.zero C h
  let zeroV := Expr.zero C v
  let ux := latH C code 0 latticeFirstPeriodXId
  let vx := latH C code 0 latticeSecondPeriodXId
  let uy := latV C code 0 latticeFirstPeriodYId
  let vy := latV C code 0 latticeSecondPeriodYId
  let hx := latH C code 0 (latticeHorizontalBoundId code)
  let hy := latV C code 0 (latticeVerticalBoundId code)
  let uxBound := latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)
  let q : Rat := code.rationalSeparator
  let ax := Expr.sub ux (Expr.scale q vx)
  let ay := Expr.sub (Expr.scale q vy) uy
  let reps := List.ofFn fun r : Fin code.representativeCount => r
  let vertices := List.ofFn fun i : Fin C.vertexCount => i
  let cells := List.ofFn fun e : Fin C.cellCount => e
  let indices := latticeFiniteIndices code
  let rankChecks := Formula.andList
    [.horizontalLt zeroH vx, .verticalLt zeroV vy,
     .horizontalLt zeroH ax, .verticalLt zeroV ay,
     .horizontalLt zeroH hx, .verticalLt zeroV hy]
  let periodBounds := Formula.andList
    ([1, -1].flatMap fun s : Int => [1, -1].map fun t : Int => Formula.andList
      [.horizontalLe (Expr.add (Expr.scale s ux) (Expr.scale t vx)) hx,
       .verticalLe (Expr.add (Expr.scale s uy) (Expr.scale t vy)) hy])
  let representativeBounds := Formula.andList (reps.map fun r => Formula.andList
    [.horizontalLe (Expr.neg hx) (latH C code 0 (latticeRepresentativeXId r.val)),
     .horizontalLe (latH C code 0 (latticeRepresentativeXId r.val)) hx,
     .verticalLe (Expr.neg hy) (latV C code 0 (latticeRepresentativeYId r.val)),
     .verticalLe (latV C code 0 (latticeRepresentativeYId r.val)) hy])
  let firstIndexBounds := Formula.andList
    ((vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input h (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      let lhsPos := Expr.add (Expr.scale 2 hx) d
      let lhsNeg := Expr.add (Expr.scale 2 hx) (Expr.neg d)
      let rhs := Expr.scale (Int.ofNat code.firstIndexBound) ax
      Formula.andList [.horizontalLt lhsPos rhs, .horizontalLt lhsNeg rhs]) ++
     (vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input v (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      let lhsPos := Expr.add (Expr.scale 2 hy) d
      let lhsNeg := Expr.add (Expr.scale 2 hy) (Expr.neg d)
      let rhs := Expr.scale (Int.ofNat code.firstIndexBound) ay
      Formula.andList [.verticalLt lhsPos rhs, .verticalLt lhsNeg rhs]))
  let uxBounds := Formula.andList
    [.horizontalLe zeroH uxBound, .horizontalLe ux uxBound, .horizontalLe (Expr.neg ux) uxBound]
  let secondIndexBounds := Formula.andList (vertices.flatMap fun a => vertices.map fun b =>
    let d := Expr.input h (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
    let common := Expr.add (Expr.scale 2 hx)
      (Expr.scale (Int.ofNat code.firstIndexBound) uxBound)
    let rhs := Expr.scale (Int.ofNat code.secondIndexBound) vx
    Formula.andList
      [.horizontalLt (Expr.add common d) rhs, .horizontalLt (Expr.add common (Expr.neg d)) rhs])
  let packingChecks := Formula.andList (indices.flatMap fun i => indices.map fun i' =>
    if i = i' then Formula.truth else
      let cx := latticeCentreX C code 0 i
      let cy := latticeCentreY C code 0 i
      let cx' := latticeCentreX C code 0 i'
      let cy' := latticeCentreY C code 0 i'
      Formula.disjunction (sameCentreFormula cx cx' cy cy')
        (Formula.andList (cells.flatMap fun e => cells.map fun e' =>
          cellNonoverlapFormula false e e' cx cx' cy cy')))
  let coverageCheck : Formula C h v := Formula.forallHorizontal (Formula.forallVertical
    (let x := Expr.var C (h + 1) 0
     let y := Expr.var C (v + 1) 0
     let hx' := latH C code 1 (latticeHorizontalBoundId code)
     let hy' := latV C code 1 (latticeVerticalBoundId code)
     Formula.implication
       (Formula.andList
         [.horizontalLt (Expr.neg hx') x, .horizontalLt x hx',
          .verticalLt (Expr.neg hy') y, .verticalLt y hy'])
       (Formula.orList (indices.flatMap fun i => cells.map fun e =>
         closedCellFormula false e (latticeCentreX C code 1 i) x
           (latticeCentreY C code 1 i) y))))
  Formula.andList
    [rankChecks, periodBounds, representativeBounds, firstIndexBounds, uxBounds,
      secondIndexBounds, packingChecks, coverageCheck]

def latticeCertificateFormula (C : RegionCode) (code : RawLatticeCode) : Formula C 0 0 :=
  if code.wellFormed then Formula.close (latticeBody C code) else .falsity

def positiveCertificateFormula (C : RegionCode) : RawPositiveCode → Formula C 0 0
  | .triangular code => Formula.orientClosed code.orientation (triangularSlabFormula C code)
  | .lattice code => latticeCertificateFormula C code

/-- Runtime verifier: only finite code, affine syntax, and the Boolean coordinate oracle occur. -/
def verifyPositive (C : RegionCode) (O : Oracle C) (code : RawPositiveCode) : Bool :=
  code.wellFormed &&
    AffineCompiler.decideFormula O (positiveCertificateFormula C code)

/-- An unused or malformed enumeration stage returns `false`; it cannot block later stages. -/
def verifyPositiveStage (C : RegionCode) (O : Oracle C) (stage : Nat) : Bool :=
  match wellFormedPositiveStage stage with
  | none => false
  | some code => verifyPositive C O code

/-- A finite query tree implementing the positive verifier. -/
def verifyPositiveProgram (C : RegionCode) (code : RawPositiveCode) :
    Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool :=
  if code.wellFormed then
    AffineCompiler.decideFormulaProgram (positiveCertificateFormula C code)
  else .pure false

/-! ## Semantic contracts -/

private def selectedAxis (epsilon : Bool) (s : CoordSort) : Tiling.AxisParallel.Axis :=
  if epsilon then s.axis.swap else s.axis

private def evalAffineInOrientation {C : RegionCode} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) {n : Nat} (A : AffineExpr C n) (x : Fin n → Real) : Real :=
  (∑ i, (A.variableCoefficient i : Real) * x i) +
    ∑ i, (A.inputConstant i : Real) * (selectedAxis epsilon s).coord (R.vertex i)

private def formulaHoldsInOrientation {C : RegionCode} (R : Realization C) (epsilon : Bool) :
    {h v : Nat} → Formula C h v → (Fin h → Real) → (Fin v → Real) → Prop
  | _, _, .truth, _, _ => True
  | _, _, .falsity, _, _ => False
  | _, _, .horizontalLe A B, x, _ =>
      evalAffineInOrientation R epsilon .horizontal A x ≤
        evalAffineInOrientation R epsilon .horizontal B x
  | _, _, .horizontalLt A B, x, _ =>
      evalAffineInOrientation R epsilon .horizontal A x <
        evalAffineInOrientation R epsilon .horizontal B x
  | _, _, .verticalLe A B, _, y =>
      evalAffineInOrientation R epsilon .vertical A y ≤
        evalAffineInOrientation R epsilon .vertical B y
  | _, _, .verticalLt A B, _, y =>
      evalAffineInOrientation R epsilon .vertical A y <
        evalAffineInOrientation R epsilon .vertical B y
  | _, _, .conjunction p q, x, y => formulaHoldsInOrientation R epsilon p x y ∧
      formulaHoldsInOrientation R epsilon q x y
  | _, _, .disjunction p q, x, y => formulaHoldsInOrientation R epsilon p x y ∨
      formulaHoldsInOrientation R epsilon q x y
  | _, _, .negation p, x, y => ¬formulaHoldsInOrientation R epsilon p x y
  | _, _, .existsHorizontal p, x, y =>
      ∃ t, formulaHoldsInOrientation R epsilon p (Fin.cons t x) y
  | _, _, .existsVertical p, x, y =>
      ∃ t, formulaHoldsInOrientation R epsilon p x (Fin.cons t y)

structure TriangularRawParameters (code : RawTriangularCode) where
  alpha : Real
  beta : Real
  shear : Fin (triangularPieceCount code) → Real
  intervalLeft : (i : TriangularIntervalIndex code) → Real
  intervalRight : (i : TriangularIntervalIndex code) → Real
  representativeX : (i : TriangularRepresentativeIndex code) → Real
  representativeY : (i : TriangularRepresentativeIndex code) → Real

private def triangularSemanticCentre (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (r : Fin (triangularPiece code j).representativeCount) (n k : Int) :
    Tiling.Plane :=
  let i : TriangularRepresentativeIndex code := ⟨j, r⟩
  (X.representativeX i + n * X.beta) +
    (X.representativeY i + n * X.shear j + k * X.alpha) * Complex.I

private def triangularCentreSet (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) : Set Tiling.Plane :=
  {p | ∃ r n k, p = triangularSemanticCentre code X j r n k}

private def triangularBaseSet (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) : Set Real :=
  ⋃ q : Int, ⋃ ell : Fin (triangularPiece code j).intervalCount,
    Set.Ioo (X.intervalLeft ⟨j, ell⟩ + q * X.beta)
      (X.intervalRight ⟨j, ell⟩ + q * X.beta)

private def triangularOpenFundamentalBox (code : RawTriangularCode)
    (X : TriangularRawParameters code) : Set Tiling.Plane :=
  {p | 0 < p.re ∧ p.re < X.beta ∧ 0 < p.im ∧ p.im < X.alpha}

private def triangularPieceFirstPeriod (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) : Tiling.Plane :=
  X.beta + X.shear j * Complex.I

private def triangularPieceSecondPeriod (code : RawTriangularCode)
    (X : TriangularRawParameters code) : Tiling.Plane := X.alpha * Complex.I

private def triangularPieceTarget (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) : Set Tiling.Plane :=
  {p | p.re ∈ triangularBaseSet code X j}

def selectedCoordinate (epsilon : Bool) (s : CoordSort) (p : Tiling.Plane) : Real :=
  (selectedAxis epsilon s).coord p

private def semanticOpenCell {C : RegionCode} (R : Realization C) (epsilon : Bool)
    (e : Fin C.cellCount) (centre point : Tiling.Plane) : Prop :=
  centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) < point.re ∧
  point.re < centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
  centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) < point.im ∧
  point.im < centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))

private def semanticClosedCell {C : RegionCode} (R : Realization C) (epsilon : Bool)
    (e : Fin C.cellCount) (centre point : Tiling.Plane) : Prop :=
  centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ≤ point.re ∧
  point.re ≤ centre.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
  centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) ≤ point.im ∧
  point.im ≤ centre.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e))

private def semanticCellsNonoverlap {C : RegionCode} (R : Realization C) (epsilon : Bool)
    (e e' : Fin C.cellCount) (c c' : Tiling.Plane) : Prop :=
  c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ≤
    c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e' else C.leftVertex e')) ∨
  c'.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.topVertex e' else C.rightVertex e')) ≤
    c.re + selectedCoordinate epsilon .horizontal
      (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ∨
  c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) ≤
    c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e' else C.bottomVertex e')) ∨
  c'.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.rightVertex e' else C.topVertex e')) ≤
    c.im + selectedCoordinate epsilon .vertical
      (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e))

structure TriangularChecks {C : RegionCode} (R : Realization C) (code : RawTriangularCode)
    (X : TriangularRawParameters code) : Prop where
  periods_pos : 0 < X.alpha ∧ 0 < X.beta
  shear_normalized : ∀ j, 0 ≤ X.shear j ∧ X.shear j < X.alpha
  intervals_normalized : ∀ i,
    0 ≤ X.intervalLeft i ∧ X.intervalLeft i < X.intervalRight i ∧
      X.intervalRight i ≤ X.beta
  interval_interiors_disjoint : ∀ i i', i ≠ i' →
    X.intervalRight i ≤ X.intervalLeft i' ∨ X.intervalRight i' ≤ X.intervalLeft i
  base_period_covered : ∀ x, 0 < x → x < X.beta →
    ∃ i, X.intervalLeft i ≤ x ∧ x ≤ X.intervalRight i
  representatives_normalized : ∀ i,
    (0 ≤ X.representativeX i ∧ X.representativeX i < X.beta) ∧
    (0 ≤ X.representativeY i ∧ X.representativeY i < X.alpha)
  vertex_diameter_bounds :
    (∀ a b, |selectedCoordinate code.orientation .horizontal (R.vertex a) -
        selectedCoordinate code.orientation .horizontal (R.vertex b)| <
          code.checkingRadius * X.beta) ∧
    (∀ a b, |selectedCoordinate code.orientation .vertical (R.vertex a) -
        selectedCoordinate code.orientation .vertical (R.vertex b)| <
          code.checkingRadius * X.alpha)
  finite_packing : ∀ j (i i' : TriangularFiniteIndex code j), i ≠ i' →
    triangularSemanticCentre code X j i.1 (centeredInteger i.2.1) (centeredInteger i.2.2) =
      triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1) (centeredInteger i'.2.2) ∨
    ∀ e e', semanticCellsNonoverlap R code.orientation e e'
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1) (centeredInteger i.2.2))
      (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1) (centeredInteger i'.2.2))
  no_leakage : ∀ j p, 0 < p.re → p.re < X.beta → 0 < p.im → p.im < X.alpha →
    (∃ i ∈ triangularFiniteIndices code j, ∃ e,
      semanticOpenCell R code.orientation e
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1) (centeredInteger i.2.2)) p) →
    ∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
      X.intervalLeft ⟨j, ell⟩ + q * X.beta ≤ p.re ∧
      p.re ≤ X.intervalRight ⟨j, ell⟩ + q * X.beta
  finite_coverage : ∀ j p, 0 < p.re → p.re < X.beta → 0 < p.im → p.im < X.alpha →
    (∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
      X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
      p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta) →
    ∃ i ∈ triangularFiniteIndices code j, ∃ e,
      semanticClosedCell R code.orientation e
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1) (centeredInteger i.2.2)) p

structure LatticeRawParameters (code : RawLatticeCode) where
  firstPeriod : Tiling.Plane
  secondPeriod : Tiling.Plane
  representative : Fin code.representativeCount → Tiling.Plane
  horizontalBound : Real
  verticalBound : Real
  firstPeriodAbsoluteXBound : Real

private def latticeSemanticCentre (code : RawLatticeCode) (X : LatticeRawParameters code)
    (r : Fin code.representativeCount) (n m : Int) : Tiling.Plane :=
  X.representative r + n • X.firstPeriod + m • X.secondPeriod

def latticeCentreSet (code : RawLatticeCode) (X : LatticeRawParameters code) : Set Tiling.Plane :=
  {p | ∃ r n m, p = latticeSemanticCentre code X r n m}

private def latticeFundamentalParallelogram
    (code : RawLatticeCode) (X : LatticeRawParameters code) : Set Tiling.Plane :=
  {p | ∃ s t : Real, 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧
    p = s • X.firstPeriod + t • X.secondPeriod}

private def latticeOpenCheckingBox (code : RawLatticeCode) (X : LatticeRawParameters code) :
    Set Tiling.Plane :=
  {p | -X.horizontalBound < p.re ∧ p.re < X.horizontalBound ∧
    -X.verticalBound < p.im ∧ p.im < X.verticalBound}

private def latticeClosedCheckingBox (code : RawLatticeCode) (X : LatticeRawParameters code) :
    Set Tiling.Plane :=
  {p | |p.re| ≤ X.horizontalBound ∧ |p.im| ≤ X.verticalBound}

structure LatticeChecks {C : RegionCode} (R : Realization C) (code : RawLatticeCode)
    (X : LatticeRawParameters code) : Prop where
  separated_periods :
    0 < X.secondPeriod.re ∧ 0 < X.secondPeriod.im ∧
    0 < X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re ∧
    0 < code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im
  checking_bounds_pos : 0 < X.horizontalBound ∧ 0 < X.verticalBound
  period_signed_bounds : ∀ sx ∈ ([-1, 1] : List Int), ∀ sy ∈ ([-1, 1] : List Int),
    sx * X.firstPeriod.re + sy * X.secondPeriod.re ≤ X.horizontalBound ∧
    sx * X.firstPeriod.im + sy * X.secondPeriod.im ≤ X.verticalBound
  representatives_bounded : ∀ r,
    |(X.representative r).re| ≤ X.horizontalBound ∧
    |(X.representative r).im| ≤ X.verticalBound
  first_index_bounds :
    (∀ a b, 2 * X.horizontalBound + |(R.vertex a).re - (R.vertex b).re| <
      code.firstIndexBound *
        (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re)) ∧
    (∀ a b, 2 * X.verticalBound + |(R.vertex a).im - (R.vertex b).im| <
      code.firstIndexBound *
        (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im))
  first_period_x_bound : 0 ≤ X.firstPeriodAbsoluteXBound ∧
    X.firstPeriod.re ≤ X.firstPeriodAbsoluteXBound ∧
    -X.firstPeriod.re ≤ X.firstPeriodAbsoluteXBound
  second_index_bound : ∀ a b,
    2 * X.horizontalBound + |(R.vertex a).re - (R.vertex b).re| +
      code.firstIndexBound * X.firstPeriodAbsoluteXBound <
        code.secondIndexBound * X.secondPeriod.re
  finite_packing : ∀ (i i' : LatticeFiniteIndex code),
    i ∈ latticeFiniteIndices code → i' ∈ latticeFiniteIndices code → i ≠ i' →
    latticeSemanticCentre code X i.1 (centeredInteger i.2.1) (centeredInteger i.2.2) =
      latticeSemanticCentre code X i'.1 (centeredInteger i'.2.1) (centeredInteger i'.2.2) ∨
    ∀ e e', semanticCellsNonoverlap R false e e'
      (latticeSemanticCentre code X i.1 (centeredInteger i.2.1) (centeredInteger i.2.2))
      (latticeSemanticCentre code X i'.1 (centeredInteger i'.2.1) (centeredInteger i'.2.2))
  finite_coverage : ∀ p ∈ latticeOpenCheckingBox code X,
    ∃ i ∈ latticeFiniteIndices code, ∃ e,
      semanticClosedCell R false e
        (latticeSemanticCentre code X i.1 (centeredInteger i.2.1) (centeredInteger i.2.2)) p

private noncomputable def selectedRegion {C : RegionCode} (R : Realization C) (epsilon : Bool) :
    Tiling.AxisParallel.Region := if epsilon then R.region.coordinateSwap else R.region

def realizationPlaneTileable {C : RegionCode} (R : Realization C) : Prop :=
  ∃ S : Set Tiling.Plane, Tiling.AxisParallel.TilesOn R.region S Set.univ

end Tiling.AxisParallel.Terminal.Executable.PositiveVerification
namespace Tiling.AxisParallel.Terminal.Executable.PositiveVerification

open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.AffineCompiler
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification
private theorem test_mapped_sum_take_get_lt : ∀ (pieces : List RawTriangularPieceCode)
    (f : RawTriangularPieceCode → Nat) (j : Fin pieces.length) (n : Nat),
    n < f (pieces.get j) →
      (pieces.take j.val |>.map f).sum + n < (pieces.map f).sum := by
  intro pieces
  induction pieces with
  | nil => intro f j; exact Fin.elim0 j
  | cons a as ih =>
      intro f j n hn
      revert hn
      refine Fin.cases ?_ ?_ j
      · intro hn
        change n < f a at hn
        simp at ⊢
        omega
      · intro k hn
        change n < f (as.get k) at hn
        simp at ⊢
        have htail := ih f k n hn
        simp only [List.map_take] at htail
        omega

private theorem triangular_interval_ordinal_lt : ∀ code i,
    triangularIntervalOrdinal code i < triangularTotalIntervalCount code := by
  intro code i
  unfold triangularIntervalOrdinal triangularTotalIntervalCount
  apply test_mapped_sum_take_get_lt
  exact i.2.isLt

private theorem triangular_representative_ordinal_lt : ∀ code i,
    triangularRepresentativeOrdinal code i < triangularTotalRepresentativeCount code := by
  intro code i
  unfold triangularRepresentativeOrdinal triangularTotalRepresentativeCount
  apply test_mapped_sum_take_get_lt
  exact i.2.isLt

private theorem test_mapped_ordinal_lt_of_lt :
    ∀ (pieces : List RawTriangularPieceCode) (f : RawTriangularPieceCode → Nat)
      (j k : Fin pieces.length) (n m : Nat),
      n < f (pieces.get j) → m < f (pieces.get k) → j < k →
      (pieces.take j.val |>.map f).sum + n <
        (pieces.take k.val |>.map f).sum + m := by
  intro pieces
  induction pieces with
  | nil => intro f j; exact Fin.elim0 j
  | cons a as ih =>
      intro f j k n m hn hm hjk
      revert hn hm hjk
      refine Fin.cases ?_ ?_ j
      · intro hn hm hjk
        revert hm hjk
        refine Fin.cases ?_ ?_ k
        · intro hm hjk
          omega
        · intro l hm hjk
          change n < f a at hn
          change m < f (as.get l) at hm
          change (0 : Nat) < (Fin.succ l).val at hjk
          simp at ⊢
          omega
      · intro l hn hm hjk
        revert hm hjk
        refine Fin.cases ?_ ?_ k
        · intro hm hjk
          change n < f (as.get l) at hn
          change m < f a at hm
          change (Fin.succ l).val < (0 : Nat) at hjk
          omega
        · intro q hm hjk
          change n < f (as.get l) at hn
          change m < f (as.get q) at hm
          have hjk' : l < q := Nat.lt_of_succ_lt_succ hjk
          simp [List.map_take] at ⊢
          have htail := ih f l q n m hn hm hjk'
          simp only [List.map_take] at htail
          omega

private theorem triangular_interval_ordinal_injective : ∀ code,
    Function.Injective (triangularIntervalOrdinal code) := by
  intro code i i' h
  rcases i with ⟨j, n⟩
  rcases i' with ⟨j', n'⟩
  unfold triangularIntervalOrdinal at h
  have hnot : ¬ j < j' := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt code.pieces
      RawTriangularPieceCode.intervalCount j j' n.val n'.val n.isLt n'.isLt hij
    exact (Nat.ne_of_lt hord) h
  have hnot' : ¬ j' < j := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt code.pieces
      RawTriangularPieceCode.intervalCount j' j n'.val n.val n'.isLt n.isLt hij
    exact (Nat.ne_of_lt hord) h.symm
  have hfirst : j = j' := by
    apply Fin.ext
    omega
  cases hfirst
  simp at h
  congr
  apply Fin.ext
  omega

private theorem triangular_representative_ordinal_injective : ∀ code,
    Function.Injective (triangularRepresentativeOrdinal code) := by
  intro code i i' h
  rcases i with ⟨j, n⟩
  rcases i' with ⟨j', n'⟩
  unfold triangularRepresentativeOrdinal at h
  have hnot : ¬ j < j' := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt code.pieces
      RawTriangularPieceCode.representativeCount j j' n.val n'.val n.isLt n'.isLt hij
    exact (Nat.ne_of_lt hord) h
  have hnot' : ¬ j' < j := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt code.pieces
      RawTriangularPieceCode.representativeCount j' j n'.val n.val n'.isLt n.isLt hij
    exact (Nat.ne_of_lt hord) h.symm
  have hfirst : j = j' := by
    apply Fin.ext
    omega
  cases hfirst
  simp at h
  congr
  apply Fin.ext
  omega

private theorem triangular_variable_ids_lt : ∀ code,
    triangularBetaId < triangularHorizontalVariableCount code ∧
    (∀ i, triangularIntervalLeftId code i < triangularHorizontalVariableCount code ∧
      triangularIntervalRightId code i < triangularHorizontalVariableCount code) ∧
    (∀ i, triangularRepresentativeXId code i < triangularHorizontalVariableCount code) ∧
    triangularAlphaId < triangularVerticalVariableCount code ∧
    (∀ j : Fin (triangularPieceCount code),
      triangularShearId j.val < triangularVerticalVariableCount code) ∧
    (∀ i, triangularRepresentativeYId code i < triangularVerticalVariableCount code) := by
  intro code
  have hinterval : ∀ i, triangularIntervalOrdinal code i < triangularTotalIntervalCount code :=
    triangular_interval_ordinal_lt code
  have hrep : ∀ i, triangularRepresentativeOrdinal code i <
      triangularTotalRepresentativeCount code :=
    triangular_representative_ordinal_lt code
  unfold triangularBetaId triangularHorizontalVariableCount triangularIntervalLeftId
    triangularIntervalRightId triangularRepresentativeXId triangularAlphaId
    triangularVerticalVariableCount triangularShearId triangularRepresentativeYId
  constructor
  · omega
  constructor
  · intro i
    have hi := hinterval i
    constructor <;> omega
  constructor
  · intro i
    have hi := hrep i
    omega
  constructor
  · omega
  constructor
  · intro j
    omega
  · intro i
    have hi := hrep i
    omega

private theorem lattice_variable_ids_lt : ∀ code,
    latticeFirstPeriodXId < latticeHorizontalVariableCount code ∧
    latticeSecondPeriodXId < latticeHorizontalVariableCount code ∧
    (∀ r : Fin code.representativeCount,
      latticeRepresentativeXId r.val < latticeHorizontalVariableCount code) ∧
    latticeHorizontalBoundId code < latticeHorizontalVariableCount code ∧
    latticeFirstPeriodAbsoluteXBoundId code < latticeHorizontalVariableCount code ∧
    latticeFirstPeriodYId < latticeVerticalVariableCount code ∧
    latticeSecondPeriodYId < latticeVerticalVariableCount code ∧
    (∀ r : Fin code.representativeCount,
      latticeRepresentativeYId r.val < latticeVerticalVariableCount code) ∧
    latticeVerticalBoundId code < latticeVerticalVariableCount code := by
  intro code
  unfold latticeFirstPeriodXId latticeSecondPeriodXId latticeRepresentativeXId
    latticeHorizontalBoundId latticeFirstPeriodAbsoluteXBoundId latticeFirstPeriodYId
    latticeSecondPeriodYId latticeRepresentativeYId latticeVerticalBoundId
    latticeHorizontalVariableCount latticeVerticalVariableCount
  constructor
  · omega
  constructor
  · omega
  constructor
  · intro r
    omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · intro r
    omega
  · omega


private theorem centeredInteger_closed_bounds : ∀ radius (i : Fin (2 * radius + 1)),
    (centeredInteger i).natAbs ≤ radius := by
  intro radius i
  change (Int.ofNat i.val - Int.ofNat radius).natAbs ≤ radius
  have hi : i.val < 2 * radius + 1 := i.isLt
  have hi' : i.val ≤ 2 * radius := by omega
  have h := Lean.Omega.Int.natAbs_dichotomy
    (a := (Int.ofNat i.val - Int.ofNat radius))
  rcases h with ⟨hpos, _⟩ | ⟨hneg, _⟩
  · have hcast :
        ((Int.ofNat i.val - Int.ofNat radius).natAbs : Int) ≤ Int.ofNat radius := by
      have hri : (i.val : Int) - (radius : Int) ≤ (radius : Int) := by omega
      calc
        ((Int.ofNat i.val - Int.ofNat radius).natAbs : Int) =
            Int.ofNat i.val - Int.ofNat radius := Int.natAbs_of_nonneg hpos
        _ ≤ Int.ofNat radius := hri
    exact Int.ofNat_le.mp hcast
  · have hcast :
        ((Int.ofNat i.val - Int.ofNat radius).natAbs : Int) ≤ Int.ofNat radius := by
      have hri : -((i.val : Int) - (radius : Int)) ≤ (radius : Int) := by omega
      calc
        ((Int.ofNat i.val - Int.ofNat radius).natAbs : Int) =
            -(Int.ofNat i.val - Int.ofNat radius) :=
          Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
        _ ≤ Int.ofNat radius := hri
    exact Int.ofNat_le.mp hcast

private theorem centeredInteger_closed_complete : ∀ radius (n : Int), n.natAbs ≤ radius →
    ∃ i : Fin (2 * radius + 1), centeredInteger i = n := by
  intro radius n hn
  by_cases hnonneg : 0 ≤ n
  · have hi : n.natAbs + radius < 2 * radius + 1 := by omega
    refine ⟨⟨n.natAbs + radius, hi⟩, ?_⟩
    change (Int.ofNat (n.natAbs + radius) - Int.ofNat radius) = n
    have hadd : Int.ofNat (n.natAbs + radius) =
        Int.ofNat n.natAbs + Int.ofNat radius := Int.natCast_add _ _
    rw [hadd]
    have hnat : Int.ofNat n.natAbs = n := Int.natAbs_of_nonneg hnonneg
    rw [hnat]
    omega
  · have hneg : n < 0 := Int.lt_of_not_ge hnonneg
    have hi : radius - n.natAbs < 2 * radius + 1 := by omega
    refine ⟨⟨radius - n.natAbs, hi⟩, ?_⟩
    change (Int.ofNat (radius - n.natAbs) - Int.ofNat radius) = n
    have hsub : Int.ofNat (radius - n.natAbs) =
        Int.ofNat radius - Int.ofNat n.natAbs := Int.ofNat_sub hn
    rw [hsub]
    have hnat : Int.ofNat n.natAbs = -n :=
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hneg)
    rw [hnat]
    omega

private theorem triangular_index_enumeration_complete : ∀ code j r n k,
    n.natAbs ≤ code.checkingRadius + 1 →
    k.natAbs ≤ 2 * code.checkingRadius + 3 →
    ∃ i ∈ triangularFiniteIndices code j,
      i.1 = r ∧ centeredInteger i.2.1 = n ∧ centeredInteger i.2.2 = k := by
  intro code j r n k hn hk
  obtain ⟨nidx, hnidx⟩ :=
    centeredInteger_closed_complete (code.checkingRadius + 1) n hn
  obtain ⟨kidx, hkidx⟩ :=
    centeredInteger_closed_complete (2 * code.checkingRadius + 3) k hk
  let i : TriangularFiniteIndex code j := (r, nidx, kidx)
  refine ⟨i, ?_, rfl, hnidx, hkidx⟩
  simp only [triangularFiniteIndices]
  apply List.mem_flatMap.mpr
  refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨nidx, List.mem_ofFn.mpr ⟨nidx, rfl⟩, ?_⟩
  apply List.mem_ofFn.mpr
  exact ⟨kidx, rfl⟩

private theorem lattice_index_enumeration_complete : ∀ code r n m,
    n.natAbs < code.firstIndexBound → m.natAbs < code.secondIndexBound →
    ∃ i ∈ latticeFiniteIndices code,
      i.1 = r ∧ centeredInteger i.2.1 = n ∧ centeredInteger i.2.2 = m := by
  intro code r n m hn hm
  obtain ⟨nidx, hnidx⟩ :=
    centeredInteger_closed_complete code.firstIndexBound n (by omega)
  obtain ⟨midx, hmid⟩ :=
    centeredInteger_closed_complete code.secondIndexBound m (by omega)
  let i : LatticeFiniteIndex code := (r, nidx, midx)
  refine ⟨i, ?_, rfl, hnidx, hmid⟩
  simp only [latticeFiniteIndices, List.mem_filter]
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨nidx, List.mem_ofFn.mpr ⟨nidx, rfl⟩, ?_⟩
    apply List.mem_ofFn.mpr
    exact ⟨midx, rfl⟩
  · dsimp [i]
    simp [hnidx, hmid, hn, hm]


private theorem formula_coordinateSwap_holds : ∀ {C h v} (R : Realization C)
    (f : Formula C h v) x y,
    (Formula.coordinateSwap f).Holds R y x ↔
      formulaHoldsInOrientation R true f x y := by
  intro C h v R f
  induction f with
  | truth => intro x y; rfl
  | falsity => intro x y; rfl
  | horizontalLe A B => intro x y; rfl
  | horizontalLt A B => intro x y; rfl
  | verticalLe A B => intro x y; rfl
  | verticalLt A B => intro x y; rfl
  | conjunction p q ihp ihq =>
      intro x y
      simp only [Formula.coordinateSwap, Formula.Holds, formulaHoldsInOrientation,
        ihp, ihq]
  | disjunction p q ihp ihq =>
      intro x y
      simp only [Formula.coordinateSwap, Formula.Holds, formulaHoldsInOrientation,
        ihp, ihq]
  | negation p ih =>
      intro x y
      simp only [Formula.coordinateSwap, Formula.Holds, formulaHoldsInOrientation, ih]
  | existsHorizontal p ih =>
      intro x y
      simp only [Formula.coordinateSwap, Formula.Holds, formulaHoldsInOrientation]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih (Fin.cons t x) y).mp ht⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih (Fin.cons t x) y).mpr ht⟩
  | existsVertical p ih =>
      intro x y
      simp only [Formula.coordinateSwap, Formula.Holds, formulaHoldsInOrientation]
      constructor
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih x (Fin.cons t y)).mp ht⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, (ih x (Fin.cons t y)).mpr ht⟩

private theorem orientClosed_holds : ∀ {C} (R : Realization C) epsilon (f : Formula C 0 0),
    (Formula.orientClosed epsilon f).Holds R Fin.elim0 Fin.elim0 ↔
      formulaHoldsInOrientation R epsilon f Fin.elim0 Fin.elim0 := by
  intro C R epsilon f
  cases epsilon
  · have hfalse : ∀ {h v} (f : Formula C h v) x y,
        f.Holds R x y ↔ formulaHoldsInOrientation R false f x y := by
      intro h v f
      induction f with
      | truth => intro x y; rfl
      | falsity => intro x y; rfl
      | horizontalLe A B => intro x y; rfl
      | horizontalLt A B => intro x y; rfl
      | verticalLe A B => intro x y; rfl
      | verticalLt A B => intro x y; rfl
      | conjunction p q ihp ihq =>
          intro x y
          simp only [Formula.Holds, formulaHoldsInOrientation, ihp, ihq]
      | disjunction p q ihp ihq =>
          intro x y
          simp only [Formula.Holds, formulaHoldsInOrientation, ihp, ihq]
      | negation p ih =>
          intro x y
          simp only [Formula.Holds, formulaHoldsInOrientation, ih]
      | existsHorizontal p ih =>
          intro x y
          simp only [Formula.Holds, formulaHoldsInOrientation]
          exact exists_congr fun t => ih (Fin.cons t x) y
      | existsVertical p ih =>
          intro x y
          simp only [Formula.Holds, formulaHoldsInOrientation]
          exact exists_congr fun t => ih x (Fin.cons t y)
    simpa only [Formula.orientClosed, Bool.false_eq_true, ↓reduceIte] using
      (hfalse f Fin.elim0 Fin.elim0)
  · simpa only [Formula.orientClosed, Bool.false_eq_true, ↓reduceIte] using
      (formula_coordinateSwap_holds R f Fin.elim0 Fin.elim0)

theorem verifyPositiveProgram_evaluate : ∀ (C : RegionCode) (O : Oracle C) code,
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
      (verifyPositiveProgram C code) = verifyPositive C O code := by
  intro C O code
  by_cases h : code.wellFormed
  · simp only [verifyPositiveProgram, h, ↓reduceIte]
    rw [AffineCompiler.decideFormulaProgram_evaluate]
    simp only [verifyPositive, h, Bool.true_and]
  · simp only [verifyPositiveProgram, h, Bool.false_eq_true, ↓reduceIte,
      OracleProgram.evaluate, verifyPositive, Bool.false_and]


end Tiling.AxisParallel.Terminal.Executable.PositiveVerification
namespace Tiling.AxisParallel.Terminal.Executable.PositiveVerification

open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Terminal.Executable.AffineCompiler
open Tiling.AxisParallel.Terminal.Executable.PositiveVerification

private theorem triangular_piece_periodic : ∀ (code : RawTriangularCode)
      (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
      (p : Tiling.Plane) (n k : Int),
    p ∈ triangularCentreSet code X j ↔
      p + n • triangularPieceFirstPeriod code X j +
        k • triangularPieceSecondPeriod code X ∈ triangularCentreSet code X j := by
  intro code X j p n k
  constructor
  · rintro ⟨r, a, b, rfl⟩
    refine ⟨r, a + n, b + k, ?_⟩
    simp [triangularSemanticCentre, triangularPieceFirstPeriod,
      triangularPieceSecondPeriod]
    ring
  · rintro ⟨r, a, b, h⟩
    refine ⟨r, a - n, b - k, ?_⟩
    calc
      p = (p + n • triangularPieceFirstPeriod code X j +
        k • triangularPieceSecondPeriod code X) -
          n • triangularPieceFirstPeriod code X j -
          k • triangularPieceSecondPeriod code X := by abel
      _ = triangularSemanticCentre code X j r a b -
          n • triangularPieceFirstPeriod code X j -
          k • triangularPieceSecondPeriod code X := by rw [h]
      _ = triangularSemanticCentre code X j r (a - n) (b - k) := by
        simp [triangularSemanticCentre, triangularPieceFirstPeriod,
          triangularPieceSecondPeriod]
        ring

private theorem triangular_target_periodic : ∀ (code : RawTriangularCode)
      (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
      (p : Tiling.Plane) (n k : Int),
    p ∈ triangularPieceTarget code X j ↔
      p + n • triangularPieceFirstPeriod code X j +
        k • triangularPieceSecondPeriod code X ∈ triangularPieceTarget code X j := by
  intro code X j p n k
  constructor
  · intro hp
    have hshift :
        (p + n • triangularPieceFirstPeriod code X j +
          k • triangularPieceSecondPeriod code X).re =
          p.re + (n : ℝ) * X.beta := by
      simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod]
    simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion] at hp ⊢
    rcases hp with ⟨q, ell, hleft, hright⟩
    refine ⟨q + n, ell, ?_, ?_⟩
    · rw [hshift]
      change X.intervalLeft ⟨j, ell⟩ + ((q + n : Int) : ℝ) * X.beta <
        p.re + (n : ℝ) * X.beta
      convert add_lt_add_right hleft ((n : ℝ) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
    · rw [hshift]
      change p.re + (n : ℝ) * X.beta <
        X.intervalRight ⟨j, ell⟩ + ((q + n : Int) : ℝ) * X.beta
      convert add_lt_add_right hright ((n : ℝ) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
  · intro hp
    have hshift :
        (p + n • triangularPieceFirstPeriod code X j +
          k • triangularPieceSecondPeriod code X).re =
          p.re + (n : ℝ) * X.beta := by
      simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod]
    simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion] at hp ⊢
    rcases hp with ⟨q, ell, hleft, hright⟩
    rw [hshift] at hleft hright
    refine ⟨q - n, ell, ?_, ?_⟩
    · change X.intervalLeft ⟨j, ell⟩ + ((q - n : Int) : ℝ) * X.beta < p.re
      convert sub_lt_sub_right hleft ((n : ℝ) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
    · change p.re <
        X.intervalRight ⟨j, ell⟩ + ((q - n : Int) : ℝ) * X.beta
      convert sub_lt_sub_right hright ((n : ℝ) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)

private theorem lattice_rank_two : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X →
    X.firstPeriod.re * X.secondPeriod.im - X.firstPeriod.im * X.secondPeriod.re > 0 := by
  intro C R code X hX
  rcases hX.separated_periods with ⟨hvx, hvy, hax, hay⟩
  have hdet :
      X.firstPeriod.re * X.secondPeriod.im - X.firstPeriod.im * X.secondPeriod.re =
        (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) *
            X.secondPeriod.im +
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) *
            X.secondPeriod.re := by
    ring
  rw [hdet]
  nlinarith [mul_pos hax hvy, mul_pos hay hvx]

private theorem abs_add_le_of_four_bounds {x y B : Real}
    (hpp : x + y ≤ B) (hpn : x - y ≤ B) (hnp : -x + y ≤ B) (hnn : -x - y ≤ B) :
    |x| + |y| ≤ B := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hx, abs_of_nonneg hy]
    linarith
  · rw [abs_of_nonneg hx, abs_of_nonpos (le_of_not_ge hy)]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge hx), abs_of_nonneg hy]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge hx), abs_of_nonpos (le_of_not_ge hy)]
    linarith

private theorem abs_add_triangle (x y : Real) : |x + y| ≤ |x| + |y| := by
  by_cases hx : 0 ≤ x <;> by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg (add_nonneg hx hy), abs_of_nonneg hx, abs_of_nonneg hy]
  · by_cases hxy : 0 ≤ x + y
    · rw [abs_of_nonneg hxy, abs_of_nonneg hx, abs_of_nonpos (le_of_not_ge hy)]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hxy), abs_of_nonneg hx,
        abs_of_nonpos (le_of_not_ge hy)]
      linarith
  · by_cases hxy : 0 ≤ x + y
    · rw [abs_of_nonneg hxy, abs_of_nonpos (le_of_not_ge hx), abs_of_nonneg hy]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hxy), abs_of_nonpos (le_of_not_ge hx),
        abs_of_nonneg hy]
      linarith
  · by_cases hxy : 0 ≤ x + y
    · rw [abs_of_nonneg hxy, abs_of_nonpos (le_of_not_ge hx),
        abs_of_nonpos (le_of_not_ge hy)]
      linarith
    · rw [abs_of_nonpos (le_of_not_ge hxy), abs_of_nonpos (le_of_not_ge hx),
        abs_of_nonpos (le_of_not_ge hy)]
      linarith

private theorem lattice_parallelogram_subset_closedBox : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X →
      latticeFundamentalParallelogram code X ⊆ latticeClosedCheckingBox code X := by
  intro C R code X hX p hp
  change ∃ s t : Real, 0 ≤ s ∧ s < 1 ∧ 0 ≤ t ∧ t < 1 ∧
    p = s • X.firstPeriod + t • X.secondPeriod at hp
  rcases hp with ⟨s, t, hs0, hs1, ht0, ht1, rfl⟩
  change |(s • X.firstPeriod + t • X.secondPeriod).re| ≤ X.horizontalBound ∧
    |(s • X.firstPeriod + t • X.secondPeriod).im| ≤ X.verticalBound
  have hppx := hX.period_signed_bounds (1 : Int) (by simp) (1 : Int) (by simp)
  have hpnx := hX.period_signed_bounds (1 : Int) (by simp) (-1 : Int) (by simp)
  have hnpx := hX.period_signed_bounds (-1 : Int) (by simp) (1 : Int) (by simp)
  have hnnx := hX.period_signed_bounds (-1 : Int) (by simp) (-1 : Int) (by simp)
  have hppy := hppx.2
  have hpny := hpnx.2
  have hnpy := hnpx.2
  have hnny := hnnx.2
  have hppx' := hppx.1
  have hpnx' := hpnx.1
  have hnpx' := hnpx.1
  have hnnx' := hnnx.1
  norm_num at hppx' hpnx' hnpx' hnnx' hppy hpny hnpy hnny
  have hpnx'' : X.firstPeriod.re - X.secondPeriod.re ≤ X.horizontalBound := by
    linarith [hpnx']
  have hnpx'' : -X.firstPeriod.re + X.secondPeriod.re ≤ X.horizontalBound := by
    linarith [hnpx']
  have hnnx'' : -X.firstPeriod.re - X.secondPeriod.re ≤ X.horizontalBound := by
    linarith [hnnx']
  have hpny'' : X.firstPeriod.im - X.secondPeriod.im ≤ X.verticalBound := by
    linarith [hpny]
  have hnpy'' : -X.firstPeriod.im + X.secondPeriod.im ≤ X.verticalBound := by
    linarith [hnpy]
  have hnny'' : -X.firstPeriod.im - X.secondPeriod.im ≤ X.verticalBound := by
    linarith [hnny]
  have hsumx : |X.firstPeriod.re| + |X.secondPeriod.re| ≤ X.horizontalBound :=
    abs_add_le_of_four_bounds hppx' hpnx'' hnpx'' hnnx''
  have hsumy : |X.firstPeriod.im| + |X.secondPeriod.im| ≤ X.verticalBound :=
    abs_add_le_of_four_bounds hppy hpny'' hnpy'' hnny''
  have hrex : |s * X.firstPeriod.re + t * X.secondPeriod.re| ≤ X.horizontalBound := by
    calc
          |s * X.firstPeriod.re + t * X.secondPeriod.re| ≤
          |s * X.firstPeriod.re| + |t * X.secondPeriod.re| := abs_add_triangle _ _
      _ = s * |X.firstPeriod.re| + t * |X.secondPeriod.re| := by
        rw [abs_mul, abs_of_nonneg hs0, abs_mul, abs_of_nonneg ht0]
      _ ≤ |X.firstPeriod.re| + |X.secondPeriod.re| := by
        nlinarith [abs_nonneg X.firstPeriod.re, abs_nonneg X.secondPeriod.re]
      _ ≤ X.horizontalBound := hsumx
  have hrey : |s * X.firstPeriod.im + t * X.secondPeriod.im| ≤ X.verticalBound := by
    calc
          |s * X.firstPeriod.im + t * X.secondPeriod.im| ≤
          |s * X.firstPeriod.im| + |t * X.secondPeriod.im| := abs_add_triangle _ _
      _ = s * |X.firstPeriod.im| + t * |X.secondPeriod.im| := by
        rw [abs_mul, abs_of_nonneg hs0, abs_mul, abs_of_nonneg ht0]
      _ ≤ |X.firstPeriod.im| + |X.secondPeriod.im| := by
        nlinarith [abs_nonneg X.firstPeriod.im, abs_nonneg X.secondPeriod.im]
      _ ≤ X.verticalBound := hsumy
  simpa only [Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
    smul_eq_mul] using And.intro hrex hrey

private theorem volume_re_eq_zero_local (a : Real) :
    MeasureTheory.volume {z : Tiling.Plane | z.re = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.re = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_re continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : z + (ε / 2 : ℝ) ∈ H := interior_subset hw
    have hzH : z.re = a := hzmem
    have hwH : (z + (ε / 2 : ℝ)).re = a := hwmem
    simp only [Complex.add_re, Complex.ofReal_re] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change MeasureTheory.volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.reLm.isLinear a).addHaar_frontier MeasureTheory.volume

private theorem volume_im_eq_zero_local (a : Real) :
    MeasureTheory.volume {z : Tiling.Plane | z.im = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.im = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_im continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) * Complex.I ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : z + (ε / 2 : ℝ) * Complex.I ∈ H := interior_subset hw
    have hzH : z.im = a := hzmem
    have hwH : (z + (ε / 2 : ℝ) * Complex.I).im = a := hwmem
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change MeasureTheory.volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.imLm.isLinear a).addHaar_frontier MeasureTheory.volume

private theorem lattice_parallelogram_outside_openBox_null : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X → MeasureTheory.volume
      (latticeFundamentalParallelogram code X \ latticeOpenCheckingBox code X) = 0 := by
  intro C R code X hX
  refine MeasureTheory.measure_mono_null
    (s := latticeFundamentalParallelogram code X \ latticeOpenCheckingBox code X)
    (t := ({p : Tiling.Plane | p.re = X.horizontalBound} ∪
      {p : Tiling.Plane | p.re = -X.horizontalBound} ∪
      {p : Tiling.Plane | p.im = X.verticalBound} ∪
      {p : Tiling.Plane | p.im = -X.verticalBound})) ?_ ?_
  · intro p hp
    rcases hp with ⟨hpP, hpF⟩
    have hbox := lattice_parallelogram_subset_closedBox R code X hX hpP
    change |p.re| ≤ X.horizontalBound ∧ |p.im| ≤ X.verticalBound at hbox
    have hx := abs_le.mp hbox.1
    have hy := abs_le.mp hbox.2
    change ¬(-X.horizontalBound < p.re ∧ p.re < X.horizontalBound ∧
      -X.verticalBound < p.im ∧ p.im < X.verticalBound) at hpF
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hboundary
    have hxr : p.re ≠ X.horizontalBound := by
      intro h
      exact hboundary (Or.inl (Or.inl (Or.inl h)))
    have hxl : p.re ≠ -X.horizontalBound := by
      intro h
      exact hboundary (Or.inl (Or.inl (Or.inr h)))
    have hyr : p.im ≠ X.verticalBound := by
      intro h
      exact hboundary (Or.inl (Or.inr h))
    have hyl : p.im ≠ -X.verticalBound := by
      intro h
      exact hboundary (Or.inr h)
    have hopenx : -X.horizontalBound < p.re ∧ p.re < X.horizontalBound :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩
    have hopeny : -X.verticalBound < p.im ∧ p.im < X.verticalBound :=
      ⟨lt_of_le_of_ne hy.1 (Ne.symm hyl), lt_of_le_of_ne hy.2 hyr⟩
    exact hpF ⟨hopenx.1, hopenx.2, hopeny.1, hopeny.2⟩
  · apply MeasureTheory.measure_union_null
    · apply MeasureTheory.measure_union_null
      · apply MeasureTheory.measure_union_null
        · exact volume_re_eq_zero_local _
        · exact volume_re_eq_zero_local _
      · exact volume_im_eq_zero_local _
    · exact volume_im_eq_zero_local _



private theorem rectangle_boundary_null (left right bottom top : Real) :
    MeasureTheory.volume
      ({p : Tiling.Plane | left ≤ p.re ∧ p.re ≤ right ∧ bottom ≤ p.im ∧ p.im ≤ top} \
        {p : Tiling.Plane | left < p.re ∧ p.re < right ∧ bottom < p.im ∧ p.im < top}) = 0 := by
  refine MeasureTheory.measure_mono_null
    (s := {p : Tiling.Plane | left ≤ p.re ∧ p.re ≤ right ∧ bottom ≤ p.im ∧ p.im ≤ top} \
      {p : Tiling.Plane | left < p.re ∧ p.re < right ∧ bottom < p.im ∧ p.im < top})
    (t := ({p : Tiling.Plane | p.re = left} ∪ {p : Tiling.Plane | p.re = right} ∪
      {p : Tiling.Plane | p.im = bottom} ∪ {p : Tiling.Plane | p.im = top})) ?_ ?_
  · intro p hp
    rcases hp with ⟨hclosed, hopen⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hboundary
    have hleft : p.re ≠ left := by
      intro h
      exact hboundary (Or.inl (Or.inl (Or.inl h)))
    have hright : p.re ≠ right := by
      intro h
      exact hboundary (Or.inl (Or.inl (Or.inr h)))
    have hbottom : p.im ≠ bottom := by
      intro h
      exact hboundary (Or.inl (Or.inr h))
    have htop : p.im ≠ top := by
      intro h
      exact hboundary (Or.inr h)
    rcases hclosed with ⟨hleftLe, hrightLe, hbottomLe, htopLe⟩
    have hopen' : left < p.re ∧ p.re < right ∧ bottom < p.im ∧ p.im < top := by
      exact ⟨lt_of_le_of_ne hleftLe (Ne.symm hleft),
        lt_of_le_of_ne hrightLe hright,
        lt_of_le_of_ne hbottomLe (Ne.symm hbottom),
        lt_of_le_of_ne htopLe htop⟩
    exact hopen hopen'
  · apply MeasureTheory.measure_union_null
    · apply MeasureTheory.measure_union_null
      · apply MeasureTheory.measure_union_null
        · exact volume_re_eq_zero_local _
        · exact volume_re_eq_zero_local _
      · exact volume_im_eq_zero_local _
    · exact volume_im_eq_zero_local _

private theorem semantic_cell_boundary_null : ∀ {C} (R : Realization C) epsilon e centre,
    MeasureTheory.volume
      ({p | semanticClosedCell R epsilon e centre p} \
        {p | semanticOpenCell R epsilon e centre p}) = 0 := by
  intro C R epsilon e centre
  simpa only [semanticClosedCell, semanticOpenCell] using
    rectangle_boundary_null
      (centre.re + selectedCoordinate epsilon .horizontal
        (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)))
      (centre.re + selectedCoordinate epsilon .horizontal
        (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)))
      (centre.im + selectedCoordinate epsilon .vertical
        (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)))
      (centre.im + selectedCoordinate epsilon .vertical
        (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)))

private theorem selected_presentation_ae_false : ∀ {C} (R : Realization C),
    (⋃ e, {p | semanticOpenCell R false e 0 p}) =ᵐ[MeasureTheory.volume]
      R.region.openCarrier := by
  intro C R
  simpa [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
    Tiling.AxisParallel.Axis.coord] using R.presentation_correct

private theorem semanticOpenCell_vadd {C} (R : Realization C) (e : Fin C.cellCount)
    (centre : Tiling.Plane) :
    {p | semanticOpenCell R false e centre p} =
      centre +ᵥ {p | semanticOpenCell R false e 0 p} := by
  ext p
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_ofPred_eq]
  simp [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
    Tiling.AxisParallel.Axis.coord, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im]

private theorem finite_closed_cells_cover_open_cells_ae : ∀ {C} (R : Realization C)
    (centres : Finset Tiling.Plane) (box : Set Tiling.Plane),
    (∀ p ∈ box, ∃ c ∈ centres, ∃ e, semanticClosedCell R false e c p) →
    MeasureTheory.volume
      (box \ Tiling.AxisParallel.openUnion R.region (centres : Set Tiling.Plane)) = 0 := by
  intro C R centres box hcover
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R false e 0 p}
  let B : Set Tiling.Plane :=
    ⋃ c : (centres : Set Tiling.Plane), ⋃ e : Fin C.cellCount,
      ({p | semanticClosedCell R false e c p} \
        {p | semanticOpenCell R false e c p})
  have hB : MeasureTheory.volume B = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro c
    apply MeasureTheory.measure_iUnion_null
    intro e
    exact semantic_cell_boundary_null R false e c
  have hOAE :
      (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O) =ᵐ[MeasureTheory.volume]
        Tiling.AxisParallel.openUnion R.region (centres : Set Tiling.Plane) := by
    have hpres := selected_presentation_ae_false R
    apply Filter.EventuallyEq.iUnion
    intro c
    exact (MeasureTheory.vadd_set_ae_eq (c : Tiling.Plane)).mpr hpres
  have hboxO : MeasureTheory.volume
      (box \ (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O)) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hB
    intro p hp
    rcases hp with ⟨hpbox, hpnot⟩
    obtain ⟨c, hc, e, hce⟩ := hcover p hpbox
    let c' : (centres : Set Tiling.Plane) := ⟨c, hc⟩
    by_contra hpB
    have hclosed :
        c.re + selectedCoordinate false .horizontal (R.vertex (C.leftVertex e)) ≤ p.re ∧
        p.re ≤ c.re + selectedCoordinate false .horizontal (R.vertex (C.rightVertex e)) ∧
        c.im + selectedCoordinate false .vertical (R.vertex (C.bottomVertex e)) ≤ p.im ∧
        p.im ≤ c.im + selectedCoordinate false .vertical (R.vertex (C.topVertex e)) := by
      simpa [semanticClosedCell] using hce
    rcases hclosed with ⟨hleft, hright, hbottom, htop⟩
    have hleftne : p.re ≠ c.re +
        selectedCoordinate false .horizontal (R.vertex (C.leftVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' :
            c.re + selectedCoordinate false .horizontal (R.vertex (C.leftVertex e)) < p.re := by
          simpa [semanticOpenCell, c'] using hopen.1
        exact (ne_of_lt hopen') heq.symm⟩⟩
    have hrightne : p.re ≠ c.re +
        selectedCoordinate false .horizontal (R.vertex (C.rightVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : p.re <
            c.re + selectedCoordinate false .horizontal (R.vertex (C.rightVertex e)) := by
          simpa [semanticOpenCell, c'] using hopen.2.1
        exact (ne_of_lt hopen') heq⟩⟩
    have hbottomne : p.im ≠ c.im +
        selectedCoordinate false .vertical (R.vertex (C.bottomVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' :
            c.im + selectedCoordinate false .vertical (R.vertex (C.bottomVertex e)) < p.im := by
          simpa [semanticOpenCell, c'] using hopen.2.2.1
        exact (ne_of_lt hopen') heq.symm⟩⟩
    have htopne : p.im ≠ c.im +
        selectedCoordinate false .vertical (R.vertex (C.topVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : p.im <
            c.im + selectedCoordinate false .vertical (R.vertex (C.topVertex e)) := by
          simpa [semanticOpenCell, c'] using hopen.2.2.2
        exact (ne_of_lt hopen') heq⟩⟩
    have hopen : semanticOpenCell R false e c p := by
      simpa [semanticOpenCell] using
        (show c.re + selectedCoordinate false .horizontal (R.vertex (C.leftVertex e)) < p.re ∧
          p.re < c.re + selectedCoordinate false .horizontal (R.vertex (C.rightVertex e)) ∧
          c.im + selectedCoordinate false .vertical (R.vertex (C.bottomVertex e)) < p.im ∧
          p.im < c.im + selectedCoordinate false .vertical (R.vertex (C.topVertex e)) from
          ⟨lt_of_le_of_ne hleft (Ne.symm hleftne), lt_of_le_of_ne hright hrightne,
            lt_of_le_of_ne hbottom (Ne.symm hbottomne), lt_of_le_of_ne htop htopne⟩)
    apply hpnot
    have hshift0 : p ∈ c +ᵥ {q | semanticOpenCell R false e 0 q} := by
      rw [← semanticOpenCell_vadd R e c]
      exact hopen
    have hshift : p ∈ c' +ᵥ {q | semanticOpenCell R false e 0 q} := by
      change p ∈ c +ᵥ {q | semanticOpenCell R false e 0 q}
      exact hshift0
    have hsub : {q | semanticOpenCell R false e 0 q} ⊆ O := by
      intro q hq
      exact Set.mem_iUnion.mpr ⟨e, hq⟩
    rcases Set.mem_vadd_set.mp hshift with ⟨q, hq, hqeq⟩
    exact Set.mem_iUnion.mpr ⟨c', Set.mem_vadd_set.mpr ⟨q, hsub hq, hqeq⟩⟩
  obtain ⟨hleftAE, hrightAE⟩ := MeasureTheory.ae_eq_set.mp hOAE
  apply MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hboxO hleftAE)
  intro p hp
  rcases hp with ⟨hpbox, hpnot⟩
  by_cases hpO : p ∈ (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O)
  · exact Or.inr ⟨hpO, hpnot⟩
  · exact Or.inl ⟨hpbox, hpO⟩
private theorem triangular_shear_lower_bound (rad : Nat) (alpha shear : ℝ) (n : Int)
    (hα : 0 < alpha) (hslo : 0 ≤ shear) (hshi : shear < alpha)
    (hnlo : -((rad + 1 : Nat) : ℝ) ≤ (n : ℝ)) :
    -((rad + 1 : Nat) : ℝ) * alpha ≤ (n : ℝ) * shear := by
  by_cases hn0 : 0 ≤ n
  · have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast hn0
    have hprod : 0 ≤ (n : ℝ) * shear := mul_nonneg hnR hslo
    nlinarith [hprod, hα]
  · have hnR : (n : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_lt (Int.lt_of_not_ge hn0))
    have hmul1 := mul_le_mul_of_nonneg_right hnlo hslo
    have hmul2 := mul_le_mul_of_nonneg_left (le_of_lt hshi)
      (by positivity : 0 ≤ (rad : ℝ) + 1)
    nlinarith [hmul1, hmul2]

private theorem triangular_shear_upper_bound (rad : Nat) (alpha shear : ℝ) (n : Int)
    (hα : 0 < alpha) (hslo : 0 ≤ shear) (hshi : shear < alpha)
    (hnhi : (n : ℝ) ≤ ((rad + 1 : Nat) : ℝ)) :
    (n : ℝ) * shear ≤ ((rad + 1 : Nat) : ℝ) * alpha := by
  by_cases hn0 : 0 ≤ n
  · have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast hn0
    have hmul1 := mul_le_mul_of_nonneg_right hnhi hα.le
    have hmul2 := mul_le_mul_of_nonneg_left (le_of_lt hshi) hnR
    nlinarith [hmul1, hmul2]
  · have hnR : (n : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_lt (Int.lt_of_not_ge hn0))
    have hprod : (n : ℝ) * shear ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnR hslo
    nlinarith [hprod, hα]

private theorem triangular_k_upper_bound (rad : Nat) (alpha y shearTerm : ℝ) (k : Int)
    (hα : 0 < alpha) (hy : 0 ≤ y)
    (hns : -((rad : ℝ) + 1) * alpha ≤ shearTerm)
    (hcy : y + shearTerm + (k : ℝ) * alpha < ((rad : ℝ) + 1) * alpha) :
    k < 2 * rad + 3 := by
  by_contra hnot
  have hge : (2 * rad + 3 : Int) ≤ k := by omega
  have hgeR : ((2 * rad + 3 : Int) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hge
  norm_num [Nat.cast_add, Nat.cast_mul] at hgeR hns hcy
  have hmul := mul_le_mul_of_nonneg_right hgeR hα.le
  nlinarith [hy, hns, hmul, hα]

private theorem triangular_k_lower_bound (rad : Nat) (alpha y shearTerm : ℝ) (k : Int)
    (hα : 0 < alpha) (hy : y < alpha)
    (hns : shearTerm ≤ ((rad : ℝ) + 1) * alpha)
    (hcy : -(rad : ℝ) * alpha < y + shearTerm + (k : ℝ) * alpha) :
    -(2 * rad + 3 : Nat) < k := by
  by_contra hnot
  have hle : k ≤ (-(2 * rad + 3 : Nat) : Int) := by omega
  have hleR : (k : ℝ) ≤ (-(2 * rad + 3 : Nat) : Int) := by exact_mod_cast hle
  norm_num [Nat.cast_add, Nat.cast_mul] at hleR hns hcy
  have hmul := mul_le_mul_of_nonneg_right hleR hα.le
  nlinarith [hy, hns, hmul, hα]

-- The coordinate-case arithmetic combines integer casts with the shear bounds.
private theorem triangular_cell_neighbour_bounds_local :
    ∀ {C} (R : Realization C) code X,
      TriangularChecks R code X → ∀ j r n k e p,
      semanticOpenCell R code.orientation e
        (triangularSemanticCentre code X j r n k) p →
      p ∈ triangularOpenFundamentalBox code X →
      n.natAbs ≤ code.checkingRadius + 1 ∧
        k.natAbs ≤ 2 * code.checkingRadius + 3 := by
  intro C R code X hX j r n k e p hcell hpbox
  let rad : Nat := code.checkingRadius
  have hβ : 0 < X.beta := hX.periods_pos.2
  have hα : 0 < X.alpha := hX.periods_pos.1
  have hrep := hX.representatives_normalized ⟨j, r⟩
  have hshear := hX.shear_normalized j
  have hzero (s : CoordSort) :
      selectedCoordinate code.orientation s (0 : Tiling.Plane) = 0 := by
    cases code.orientation <;> cases s <;> rfl
  have hpbox' : 0 < p.re ∧ p.re < X.beta ∧ 0 < p.im ∧ p.im < X.alpha := by
    simpa [triangularOpenFundamentalBox] using hpbox
  have hleftAbs :
      |selectedCoordinate code.orientation .horizontal
          (R.vertex (if code.orientation then C.bottomVertex e else C.leftVertex e))| <
        (rad : ℝ) * X.beta := by
    have h := hX.vertex_diameter_bounds.1 C.originVertex
      (if code.orientation then C.bottomVertex e else C.leftVertex e)
    rw [R.origin_eq_zero] at h
    rw [hzero .horizontal, zero_sub, abs_neg] at h
    simpa [rad, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using h
  have hrightAbs :
      |selectedCoordinate code.orientation .horizontal
          (R.vertex (if code.orientation then C.topVertex e else C.rightVertex e))| <
        (rad : ℝ) * X.beta := by
    have h := hX.vertex_diameter_bounds.1 C.originVertex
      (if code.orientation then C.topVertex e else C.rightVertex e)
    rw [R.origin_eq_zero] at h
    rw [hzero .horizontal, zero_sub, abs_neg] at h
    simpa [rad, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using h
  have hbottomAbs :
      |selectedCoordinate code.orientation .vertical
          (R.vertex (if code.orientation then C.leftVertex e else C.bottomVertex e))| <
        (rad : ℝ) * X.alpha := by
    have h := hX.vertex_diameter_bounds.2 C.originVertex
      (if code.orientation then C.leftVertex e else C.bottomVertex e)
    rw [R.origin_eq_zero] at h
    rw [hzero .vertical, zero_sub, abs_neg] at h
    simpa [rad, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using h
  have htopAbs :
      |selectedCoordinate code.orientation .vertical
          (R.vertex (if code.orientation then C.rightVertex e else C.topVertex e))| <
        (rad : ℝ) * X.alpha := by
    have h := hX.vertex_diameter_bounds.2 C.originVertex
      (if code.orientation then C.rightVertex e else C.topVertex e)
    rw [R.origin_eq_zero] at h
    rw [hzero .vertical, zero_sub, abs_neg] at h
    simpa [rad, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using h
  have hcell' := hcell
  simp only [semanticOpenCell] at hcell'
  have hleft := abs_lt.mp hleftAbs
  have hright := abs_lt.mp hrightAbs
  have hbottom := abs_lt.mp hbottomAbs
  have htop := abs_lt.mp htopAbs
  have hcxlow : -(rad : ℝ) * X.beta <
      (triangularSemanticCentre code X j r n k).re := by
    nlinarith [hcell'.2.1, hright.1, hpbox'.1]
  have hcxhigh : (triangularSemanticCentre code X j r n k).re <
      ((rad : ℝ) + 1) * X.beta := by
    nlinarith [hcell'.1, hleft.1, hpbox'.2.1]
  have hcylo : -(rad : ℝ) * X.alpha <
      (triangularSemanticCentre code X j r n k).im := by
    nlinarith [hcell'.2.2.1, htop.1, hpbox'.2.2.1]
  have hcyhi : (triangularSemanticCentre code X j r n k).im <
      ((rad : ℝ) + 1) * X.alpha := by
    nlinarith [hcell'.2.2.2, hbottom.1, hpbox'.2.2.2]
  have hcx :
      (triangularSemanticCentre code X j r n k).re =
        X.representativeX ⟨j, r⟩ + (n : ℝ) * X.beta := by
    simp [triangularSemanticCentre, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcy :
      (triangularSemanticCentre code X j r n k).im =
        X.representativeY ⟨j, r⟩ + (n : ℝ) * X.shear j + (k : ℝ) * X.alpha := by
    simp [triangularSemanticCentre, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hnupper : n < (rad + 1 : Nat) := by
    by_contra hnot
    have hge : (rad + 1 : Int) ≤ n := by omega
    have hgeR : ((rad + 1 : Int) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hge
    norm_num at hgeR
    have hmul := mul_le_mul_of_nonneg_right hgeR hβ.le
    rw [hcx] at hcxhigh
    nlinarith [hrep.1.1, hmul]
  have hnlower : (-(rad + 1 : Nat) : Int) < n := by
    by_contra hnot
    have hle : n ≤ (-(rad + 1 : Nat) : Int) := by omega
    have hleR : (n : ℝ) ≤ (-(rad + 1 : Nat) : Int) := by exact_mod_cast hle
    norm_num at hleR
    have hmul := mul_le_mul_of_nonneg_right hleR hβ.le
    rw [hcx] at hcxlow
    nlinarith [hrep.1.2, hmul]
  have hnabs : n.natAbs ≤ rad + 1 := by
    by_cases hn0 : 0 ≤ n
    · have hle : n ≤ (rad + 1 : Int) := by omega
      have hcast : (n.natAbs : Int) = n := Int.natAbs_of_nonneg hn0
      have hcast' : (n.natAbs : Int) ≤ (rad + 1 : Int) := by simpa [hcast] using hle
      exact_mod_cast hcast'
    · have hnneg : n < 0 := Int.lt_of_not_ge hn0
      have hle : -n ≤ (rad + 1 : Int) := by omega
      have hcast : (n.natAbs : Int) = -n :=
        Int.ofNat_natAbs_of_nonpos hnneg.le
      have hcast' : (n.natAbs : Int) ≤ (rad + 1 : Int) := by simpa [hcast] using hle
      exact_mod_cast hcast'
  have hnloR : (-(rad + 1 : Nat) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show (-(rad + 1 : Nat) : Int) ≤ n by omega)
  have hnhiR : (n : ℝ) ≤ (rad + 1 : Nat) := by
    exact_mod_cast (show n ≤ (rad + 1 : Int) by omega)
  have hnslo : -((rad : ℝ) + 1) * X.alpha ≤ (n : ℝ) * X.shear j := by
    simpa [Nat.cast_add] using triangular_shear_lower_bound rad X.alpha
      (X.shear j) n hα hshear.1 hshear.2 hnloR
  have hnshi : (n : ℝ) * X.shear j ≤ ((rad : ℝ) + 1) * X.alpha := by
    simpa [Nat.cast_add] using triangular_shear_upper_bound rad X.alpha
      (X.shear j) n hα hshear.1 hshear.2 hnhiR
  have hkupper : k < (2 * rad + 3 : Nat) := by
    rw [hcy] at hcyhi
    exact triangular_k_upper_bound rad X.alpha
      (X.representativeY ⟨j, r⟩) ((n : ℝ) * X.shear j) k hα
      hrep.2.1 hnslo hcyhi
  have hklower : (-(2 * rad + 3 : Nat) : Int) < k := by
    rw [hcy] at hcylo
    exact triangular_k_lower_bound rad X.alpha
      (X.representativeY ⟨j, r⟩) ((n : ℝ) * X.shear j) k hα
      hrep.2.2 hnshi hcylo
  have hkabs : k.natAbs ≤ 2 * rad + 3 := by
    by_cases hk0 : 0 ≤ k
    · have hle : k ≤ (2 * rad + 3 : Int) := by omega
      have hcast : (k.natAbs : Int) = k := Int.natAbs_of_nonneg hk0
      have hcast' : (k.natAbs : Int) ≤ (2 * rad + 3 : Int) := by simpa [hcast] using hle
      exact_mod_cast hcast'
    · have hkneg : k < 0 := Int.lt_of_not_ge hk0
      have hle : -k ≤ (2 * rad + 3 : Int) := by omega
      have hcast : (k.natAbs : Int) = -k :=
        Int.ofNat_natAbs_of_nonpos hkneg.le
      have hcast' : (k.natAbs : Int) ≤ (2 * rad + 3 : Int) := by simpa [hcast] using hle
      exact_mod_cast hcast'
  exact ⟨by simpa [rad] using hnabs, by simpa [rad] using hkabs⟩

private noncomputable def coordinateSwapIsometry_local : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := Tiling.AxisParallel.coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem coordinateSwap_image_eq_preimage_local (s : Set Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap '' s =
      Tiling.AxisParallel.coordinateSwap ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨Tiling.AxisParallel.coordinateSwap z, hz,
      Tiling.AxisParallel.coordinateSwap_apply_apply z⟩


private theorem semanticOpenCell_true_image_false_local {C} (R : Realization C)
    (e : Fin C.cellCount) :
    {p | semanticOpenCell R true e 0 p} =
      Tiling.AxisParallel.coordinateSwap ''
        {p | semanticOpenCell R false e 0 p} := by
  ext p
  constructor
  · intro hp
    refine ⟨Tiling.AxisParallel.coordinateSwap p, ?_,
      Tiling.AxisParallel.coordinateSwap_apply_apply p⟩
    change (0 : Tiling.Plane).re + selectedCoordinate false .horizontal
          (R.vertex (C.leftVertex e)) < (Tiling.AxisParallel.coordinateSwap p).re ∧
        (Tiling.AxisParallel.coordinateSwap p).re <
          (0 : Tiling.Plane).re + selectedCoordinate false .horizontal
            (R.vertex (C.rightVertex e)) ∧
        (0 : Tiling.Plane).im + selectedCoordinate false .vertical
            (R.vertex (C.bottomVertex e)) <
          (Tiling.AxisParallel.coordinateSwap p).im ∧
        (Tiling.AxisParallel.coordinateSwap p).im <
          (0 : Tiling.Plane).im + selectedCoordinate false .vertical
            (R.vertex (C.topVertex e))
    simpa [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord, Tiling.AxisParallel.Axis.swap,
      and_assoc, and_left_comm, and_comm] using hp
  · rintro ⟨q, hq, rfl⟩
    change (0 : Tiling.Plane).re + selectedCoordinate true .horizontal
          (R.vertex (C.bottomVertex e)) < (Tiling.AxisParallel.coordinateSwap q).re ∧
        (Tiling.AxisParallel.coordinateSwap q).re <
          (0 : Tiling.Plane).re + selectedCoordinate true .horizontal
            (R.vertex (C.topVertex e)) ∧
        (0 : Tiling.Plane).im + selectedCoordinate true .vertical
            (R.vertex (C.leftVertex e)) <
          (Tiling.AxisParallel.coordinateSwap q).im ∧
        (Tiling.AxisParallel.coordinateSwap q).im <
          (0 : Tiling.Plane).im + selectedCoordinate true .vertical
            (R.vertex (C.rightVertex e))
    simpa [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord, Tiling.AxisParallel.Axis.swap,
      and_assoc, and_left_comm, and_comm] using hq

private theorem selected_presentation_ae : ∀ {C} (R : Realization C) epsilon,
    (⋃ e, {p | semanticOpenCell R epsilon e 0 p}) =ᵐ[MeasureTheory.volume]
      (selectedRegion R epsilon).openCarrier := by
  intro C R epsilon
  cases epsilon with
  | false => simpa [selectedRegion] using selected_presentation_ae_false R
  | true =>
      have hcells :
          (⋃ e, {p | semanticOpenCell R true e 0 p}) =
            Tiling.AxisParallel.coordinateSwap ''
              (⋃ e, {p | semanticOpenCell R false e 0 p}) := by
        rw [Set.image_iUnion]
        apply Set.iUnion_congr
        intro e
        exact semanticOpenCell_true_image_false_local R e
      have hfalse := selected_presentation_ae_false R
      have hswap :=
        coordinateSwapIsometry_local.measurePreserving.quasiMeasurePreserving.ae hfalse
      have himage :
          Tiling.AxisParallel.coordinateSwap ''
              (⋃ e, {p | semanticOpenCell R false e 0 p}) =ᵐ[MeasureTheory.volume]
            Tiling.AxisParallel.coordinateSwap '' R.region.openCarrier := by
        rw [coordinateSwap_image_eq_preimage_local,
          coordinateSwap_image_eq_preimage_local]
        filter_upwards [hswap] with x hx
        change (⋃ e, {p | semanticOpenCell R false e 0 p})
            (Tiling.AxisParallel.coordinateSwap x) =
          R.region.openCarrier (Tiling.AxisParallel.coordinateSwap x) at hx
        exact hx
      rw [hcells]
      change Tiling.AxisParallel.coordinateSwap ''
          (⋃ e, {p | semanticOpenCell R false e 0 p}) =ᵐ[MeasureTheory.volume]
        (R.region.coordinateSwap).openCarrier
      apply himage.trans
      filter_upwards [] with x
      rw [Tiling.AxisParallel.coordinateSwap_openCarrier]

private theorem semanticOpenCell_vadd_local {C} (R : Realization C) (epsilon : Bool)
    (e : Fin C.cellCount) (centre : Tiling.Plane) :
    {p | semanticOpenCell R epsilon e centre p} =
      centre +ᵥ {p | semanticOpenCell R epsilon e 0 p} := by
  ext p
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  simp only [Set.mem_ofPred_eq]
  simp [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
    Tiling.AxisParallel.Axis.coord, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im]

private theorem finite_closed_cells_cover_open_cells_ae_local : ∀ {C} (R : Realization C)
    (epsilon : Bool) (centres : Finset Tiling.Plane) (box : Set Tiling.Plane),
    (∀ p ∈ box, ∃ c ∈ centres, ∃ e, semanticClosedCell R epsilon e c p) →
    MeasureTheory.volume
      (box \ Tiling.AxisParallel.openUnion (selectedRegion R epsilon)
        (centres : Set Tiling.Plane)) = 0 := by
  intro C R epsilon centres box hcover
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R epsilon e 0 p}
  let B : Set Tiling.Plane :=
    ⋃ c : (centres : Set Tiling.Plane), ⋃ e : Fin C.cellCount,
      ({p | semanticClosedCell R epsilon e c p} \
        {p | semanticOpenCell R epsilon e c p})
  have hB : MeasureTheory.volume B = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro c
    apply MeasureTheory.measure_iUnion_null
    intro e
    exact semantic_cell_boundary_null R epsilon e c
  have hOAE :
      (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O) =ᵐ[MeasureTheory.volume]
        Tiling.AxisParallel.openUnion (selectedRegion R epsilon)
          (centres : Set Tiling.Plane) := by
    have hpres := selected_presentation_ae R epsilon
    apply Filter.EventuallyEq.iUnion
    intro c
    exact (MeasureTheory.vadd_set_ae_eq (c : Tiling.Plane)).mpr hpres
  have hboxO : MeasureTheory.volume
      (box \ (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O)) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hB
    intro p hp
    rcases hp with ⟨hpbox, hpnot⟩
    obtain ⟨c, hc, e, hce⟩ := hcover p hpbox
    let c' : (centres : Set Tiling.Plane) := ⟨c, hc⟩
    by_contra hpB
    have hclosed :
        c.re + selectedCoordinate epsilon .horizontal
            (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) ≤ p.re ∧
        p.re ≤ c.re + selectedCoordinate epsilon .horizontal
            (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
        c.im + selectedCoordinate epsilon .vertical
            (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) ≤ p.im ∧
        p.im ≤ c.im + selectedCoordinate epsilon .vertical
            (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) := by
      simpa [semanticClosedCell] using hce
    rcases hclosed with ⟨hleft, hright, hbottom, htop⟩
    have hleftne : p.re ≠ c.re + selectedCoordinate epsilon .horizontal
        (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : c.re + selectedCoordinate epsilon .horizontal
            (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) < p.re := by
          simpa [semanticOpenCell, c'] using hopen.1
        exact (ne_of_lt hopen') heq.symm⟩⟩
    have hrightne : p.re ≠ c.re + selectedCoordinate epsilon .horizontal
        (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : p.re < c.re + selectedCoordinate epsilon .horizontal
            (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) := by
          simpa [semanticOpenCell, c'] using hopen.2.1
        exact (ne_of_lt hopen') heq⟩⟩
    have hbottomne : p.im ≠ c.im + selectedCoordinate epsilon .vertical
        (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : c.im + selectedCoordinate epsilon .vertical
            (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) < p.im := by
          simpa [semanticOpenCell, c'] using hopen.2.2.1
        exact (ne_of_lt hopen') heq.symm⟩⟩
    have htopne : p.im ≠ c.im + selectedCoordinate epsilon .vertical
        (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) := by
      intro heq
      apply hpB
      exact Set.mem_iUnion.mpr ⟨c', Set.mem_iUnion.mpr ⟨e, by
        refine ⟨by simpa [c'] using hce, ?_⟩
        intro hopen
        have hopen' : p.im < c.im + selectedCoordinate epsilon .vertical
            (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) := by
          simpa [semanticOpenCell, c'] using hopen.2.2.2
        exact (ne_of_lt hopen') heq⟩⟩
    have hopen : semanticOpenCell R epsilon e c p := by
      simpa [semanticOpenCell] using
        (show c.re + selectedCoordinate epsilon .horizontal
              (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) < p.re ∧
          p.re < c.re + selectedCoordinate epsilon .horizontal
              (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) ∧
          c.im + selectedCoordinate epsilon .vertical
              (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) < p.im ∧
          p.im < c.im + selectedCoordinate epsilon .vertical
              (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) from
          ⟨lt_of_le_of_ne hleft (Ne.symm hleftne), lt_of_le_of_ne hright hrightne,
            lt_of_le_of_ne hbottom (Ne.symm hbottomne), lt_of_le_of_ne htop htopne⟩)
    apply hpnot
    have hshift0 : p ∈ c +ᵥ {q | semanticOpenCell R epsilon e 0 q} := by
      rw [← semanticOpenCell_vadd_local R epsilon e c]
      exact hopen
    have hshift : p ∈ c' +ᵥ {q | semanticOpenCell R epsilon e 0 q} := by
      change p ∈ c +ᵥ {q | semanticOpenCell R epsilon e 0 q}
      exact hshift0
    have hsub : {q | semanticOpenCell R epsilon e 0 q} ⊆ O := by
      intro q hq
      exact Set.mem_iUnion.mpr ⟨e, hq⟩
    rcases Set.mem_vadd_set.mp hshift with ⟨q, hq, hqeq⟩
    exact Set.mem_iUnion.mpr ⟨c', Set.mem_vadd_set.mpr ⟨q, hsub hq, hqeq⟩⟩
  obtain ⟨hleftAE, hrightAE⟩ := MeasureTheory.ae_eq_set.mp hOAE
  apply MeasureTheory.measure_mono_null ?_
    (MeasureTheory.measure_union_null hboxO hleftAE)
  intro p hp
  rcases hp with ⟨hpbox, hpnot⟩
  by_cases hpO : p ∈ (⋃ c : (centres : Set Tiling.Plane), c +ᵥ O)
  · exact Or.inr ⟨hpO, hpnot⟩
  · exact Or.inl ⟨hpbox, hpO⟩

private theorem triangular_piece_local_ae_identity : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → ∀ j,
    MeasureTheory.volume
      ((triangularOpenFundamentalBox code X ∩
          Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
            (triangularCentreSet code X j)) \
        triangularPieceTarget code X j) = 0 ∧
    MeasureTheory.volume
      ((triangularOpenFundamentalBox code X ∩ triangularPieceTarget code X j) \
        Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
          (triangularCentreSet code X j)) = 0 := by
  intro C R code X hX j
  classical
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R code.orientation e 0 p}
  have hcount : (triangularCentreSet code X j).Countable := by
    have hrange : Set.Countable (Set.range (fun z :
        (Fin (triangularPiece code j).representativeCount × Int × Int) =>
          triangularSemanticCentre code X j z.1 z.2.1 z.2.2)) :=
      Set.countable_range _
    apply hrange.mono
    intro p hp
    rcases hp with ⟨r, n, k, rfl⟩
    exact ⟨(r, n, k), rfl⟩
  let _hScount : Countable (triangularCentreSet code X j) := hcount.to_subtype
  have hOAE :
      (⋃ c : (triangularCentreSet code X j), (c : Tiling.Plane) +ᵥ O) =ᵐ[MeasureTheory.volume]
        Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
          (triangularCentreSet code X j) := by
    have hpres := selected_presentation_ae R code.orientation
    apply Filter.EventuallyEq.countable_iUnion
    intro c
    exact (MeasureTheory.vadd_set_ae_eq (c : Tiling.Plane)).mpr hpres
  obtain ⟨hsemantic, hopen⟩ := MeasureTheory.ae_eq_set.mp hOAE
  let B : Set Tiling.Plane :=
    ⋃ q : Int, ⋃ ell : Fin (triangularPiece code j).intervalCount,
      ({p : Tiling.Plane | p.re = X.intervalLeft ⟨j, ell⟩ + q * X.beta} ∪
        {p : Tiling.Plane | p.re = X.intervalRight ⟨j, ell⟩ + q * X.beta})
  have hB : MeasureTheory.volume B = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro q
    apply MeasureTheory.measure_iUnion_null
    intro ell
    apply MeasureTheory.measure_union_null
    · exact volume_re_eq_zero_local _
    · exact volume_re_eq_zero_local _
  have hfirst : MeasureTheory.volume
      ((triangularOpenFundamentalBox code X ∩
          Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
            (triangularCentreSet code X j)) \
        triangularPieceTarget code X j) = 0 := by
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hB hopen)
    intro p hp
    rcases hp with ⟨⟨hpbox, hpopen⟩, hpnot⟩
    by_cases hpsem : p ∈
      (⋃ c : (triangularCentreSet code X j), (c : Tiling.Plane) +ᵥ O)
    · rcases Set.mem_iUnion.mp hpsem with ⟨c, hcp⟩
      rcases Set.mem_vadd_set.mp hcp with ⟨q0, hq0, hpq⟩
      rcases Set.mem_iUnion.mp hq0 with ⟨e, hqe⟩
      rcases c.property with ⟨r, n, k, hc⟩
      have hcell : semanticOpenCell R code.orientation e
          (triangularSemanticCentre code X j r n k) p := by
        change p ∈ {p | semanticOpenCell R code.orientation e
          (triangularSemanticCentre code X j r n k) p}
        rw [semanticOpenCell_vadd_local R code.orientation e
          (triangularSemanticCentre code X j r n k)]
        exact ⟨q0, hqe, by simpa [hc] using hpq⟩
      have hbounds := triangular_cell_neighbour_bounds_local R code X hX j r n k e p
        hcell hpbox
      obtain ⟨i, hi, hir, hin, hik⟩ := triangular_index_enumeration_complete
        code j r n k hbounds.1 hbounds.2
      have hfinite : ∃ i ∈ triangularFiniteIndices code j, ∃ e,
          semanticOpenCell R code.orientation e
            (triangularSemanticCentre code X j i.1
              (centeredInteger i.2.1) (centeredInteger i.2.2)) p := by
        refine ⟨i, hi, e, ?_⟩
        simpa [hir, hin, hik] using hcell
      obtain ⟨ell, q, hq, hleft, hright⟩ := hX.no_leakage j p
        hpbox.1 hpbox.2.1 hpbox.2.2.1 hpbox.2.2.2 hfinite
      have hstrict : ¬ (X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
          p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta) := by
        intro hs
        apply hpnot
        simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion]
        exact ⟨q, ell, hs.1, hs.2⟩
      have hpB : p ∈ B := by
        apply Set.mem_iUnion.mpr
        refine ⟨q, Set.mem_iUnion.mpr ⟨ell, ?_⟩⟩
        by_cases hleftEq : p.re = X.intervalLeft ⟨j, ell⟩ + q * X.beta
        · exact Or.inl hleftEq
        · have hleftLt : X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re :=
            lt_of_le_of_ne hleft (Ne.symm hleftEq)
          have hrightEq : p.re = X.intervalRight ⟨j, ell⟩ + q * X.beta := by
            by_contra hrightNe
            exact hstrict ⟨hleftLt, lt_of_le_of_ne hright hrightNe⟩
          exact Or.inr hrightEq
      exact Or.inl hpB
    · exact Or.inr ⟨hpopen, hpsem⟩
  let centres : Finset Tiling.Plane :=
    (triangularFiniteIndices code j).toFinset.image
      (fun i => triangularSemanticCentre code X j i.1
        (centeredInteger i.2.1) (centeredInteger i.2.2))
  have hcover : ∀ p ∈ triangularOpenFundamentalBox code X ∩
      triangularPieceTarget code X j, ∃ c ∈ centres, ∃ e,
        semanticClosedCell R code.orientation e c p := by
    intro p hp
    rcases hp with ⟨hpbox, hptarget⟩
    have hpt : ∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
        X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
        p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta := by
      simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion] at hptarget
      rcases hptarget with ⟨q, ell, hleft, hright⟩
      have hβ := hX.periods_pos.2
      have hqle : q ≤ 0 := by
        by_contra hnot
        have hqge : (1 : Int) ≤ q := by omega
        have hqgeR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqge
        have hmul := mul_le_mul_of_nonneg_right hqgeR hβ.le
        have hnorm := hX.intervals_normalized ⟨j, ell⟩
        rcases hnorm with ⟨hL0, hLR, hRβ⟩
        norm_num at hmul
        nlinarith [hpbox.2.1]
      have hqge : (-1 : Int) ≤ q := by
        by_contra hnot
        have hqle' : q ≤ (-2 : Int) := by omega
        have hqleR : (q : ℝ) ≤ (-2 : ℝ) := by exact_mod_cast hqle'
        have hmul := mul_le_mul_of_nonneg_right hqleR hβ.le
        have hnorm := hX.intervals_normalized ⟨j, ell⟩
        rcases hnorm with ⟨hL0, hLR, hRβ⟩
        nlinarith [hpbox.1]
      refine ⟨ell, q, ?_, hleft, hright⟩
      simp only [List.mem_cons]
      omega
    obtain ⟨i, hi, e, hclosed⟩ := hX.finite_coverage j p
      hpbox.1 hpbox.2.1 hpbox.2.2.1 hpbox.2.2.2 hpt
    refine ⟨triangularSemanticCentre code X j i.1
      (centeredInteger i.2.1) (centeredInteger i.2.2), ?_, e, hclosed⟩
    exact Finset.mem_image.mpr ⟨i, by simpa using hi, rfl⟩
  have hfinite := finite_closed_cells_cover_open_cells_ae_local R code.orientation centres
    (triangularOpenFundamentalBox code X ∩ triangularPieceTarget code X j) hcover
  have hsecond : MeasureTheory.volume
      ((triangularOpenFundamentalBox code X ∩ triangularPieceTarget code X j) \
        Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
          (triangularCentreSet code X j)) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hfinite
    intro p hp
    rcases hp with ⟨hpbox, hpnot⟩
    refine ⟨hpbox, ?_⟩
    intro hpfinite
    apply hpnot
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hpfinite ⊢
    rcases hpfinite with ⟨c, hcp⟩
    have hcp' : (c : Tiling.Plane) ∈ centres := Finset.mem_coe.mp c.property
    rcases Finset.mem_image.mp hcp' with ⟨i, hi, hic⟩
    refine ⟨⟨triangularSemanticCentre code X j i.1
      (centeredInteger i.2.1) (centeredInteger i.2.2), ?_⟩, ?_⟩
    · exact ⟨i.1, centeredInteger i.2.1, centeredInteger i.2.2, rfl⟩
    simpa [hic] using hcp
  exact ⟨hfirst, hsecond⟩

private theorem int_natAbs_le_of_abs_mul_lt_local (z : Int) (radius : Nat) (β : Real)
    (hβ : 0 < β) (h : |(z : Real) * β| < ((radius : Real) + 1) * β) :
    z.natAbs ≤ radius + 1 := by
  have habs := abs_lt.mp h
  have hzupper : z ≤ (radius + 1 : Int) := by
    by_contra hnot
    have hzge : (radius + 2 : Int) ≤ z := by omega
    have hzgeR : ((radius + 2 : Int) : Real) ≤ (z : Real) := by exact_mod_cast hzge
    norm_num at hzgeR
    nlinarith
  have hzlower : (-(radius + 1 : Nat) : Int) ≤ z := by
    by_contra hnot
    have hzle : z ≤ (-(radius + 2 : Nat) : Int) := by omega
    have hzleR : (z : Real) ≤ (-(radius + 2 : Nat) : Int) := by exact_mod_cast hzle
    norm_num at hzleR
    nlinarith
  by_cases hz0 : 0 ≤ z
  · have hcast : (z.natAbs : Int) = z := Int.natAbs_of_nonneg hz0
    have hcast' : (z.natAbs : Int) ≤ (radius + 1 : Int) := by simpa [hcast] using hzupper
    exact_mod_cast hcast'
  · have hzneg : z < 0 := Int.lt_of_not_ge hz0
    have hle : -z ≤ (radius + 1 : Int) := by omega
    have hcast : (z.natAbs : Int) = -z := Int.ofNat_natAbs_of_nonpos hzneg.le
    have hcast' : (z.natAbs : Int) ≤ (radius + 1 : Int) := by simpa [hcast] using hle
    exact_mod_cast hcast'

private theorem triangular_overlap_reduction : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → ∀ j r r' n n' k k',
    MeasureTheory.volume
      (((triangularSemanticCentre code X j r n k) +ᵥ
          (selectedRegion R code.orientation).openCarrier) ∩
       ((triangularSemanticCentre code X j r' n' k') +ᵥ
          (selectedRegion R code.orientation).openCarrier)) ≠ 0 →
    ∃ a b : Int,
      (n - a).natAbs ≤ code.checkingRadius + 1 ∧
      (n' - a).natAbs ≤ code.checkingRadius + 1 ∧
      (k - b).natAbs ≤ 2 * code.checkingRadius + 3 ∧
      (k' - b).natAbs ≤ 2 * code.checkingRadius + 3 := by
  intro C R code X hX j r r' n n' k k' hvol
  let c := triangularSemanticCentre code X j r n k
  let c' := triangularSemanticCentre code X j r' n' k'
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R code.orientation e 0 p}
  have hcellAE (d : Tiling.Plane) :
      (d +ᵥ O) =ᵐ[MeasureTheory.volume]
        d +ᵥ (selectedRegion R code.orientation).openCarrier := by
    have hpres := selected_presentation_ae R code.orientation
    apply (MeasureTheory.vadd_set_ae_eq d).mpr
    simpa [O] using hpres
  let A : Set Tiling.Plane :=
    (c +ᵥ (selectedRegion R code.orientation).openCarrier) ∩
      (c' +ᵥ (selectedRegion R code.orientation).openCarrier)
  have hAe : Set.inter (c +ᵥ O) (c' +ᵥ O) =ᵐ[MeasureTheory.volume] A := by
    exact (hcellAE c).inter (hcellAE c')
  obtain ⟨hsemA, hAsem⟩ := MeasureTheory.ae_eq_set.mp hAe
  have hsem_ne : MeasureTheory.volume (Set.inter (c +ᵥ O) (c' +ᵥ O)) ≠ 0 := by
    intro hzero
    apply hvol
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hAsem hzero)
    intro p hp
    by_cases hpsem : p ∈ Set.inter (c +ᵥ O) (c' +ᵥ O)
    · exact Or.inr hpsem
    · exact Or.inl ⟨hp, hpsem⟩
  obtain ⟨p, hp⟩ := MeasureTheory.nonempty_of_measure_ne_zero hsem_ne
  rcases hp with ⟨hp1, hp2⟩
  rcases Set.mem_vadd_set.mp hp1 with ⟨q1, hq1, hpq1⟩
  rcases Set.mem_iUnion.mp hq1 with ⟨e, he⟩
  rcases Set.mem_vadd_set.mp hp2 with ⟨q2, hq2, hpq2⟩
  rcases Set.mem_iUnion.mp hq2 with ⟨e', he'⟩
  have hcell1 : semanticOpenCell R code.orientation e c p := by
    change p ∈ {p | semanticOpenCell R code.orientation e c p}
    rw [semanticOpenCell_vadd_local R code.orientation e c]
    exact ⟨q1, he, hpq1⟩
  have hcell2 : semanticOpenCell R code.orientation e' c' p := by
    change p ∈ {p | semanticOpenCell R code.orientation e' c' p}
    rw [semanticOpenCell_vadd_local R code.orientation e' c']
    exact ⟨q2, he', hpq2⟩
  have hdx : |c.re - c'.re| < (code.checkingRadius : Real) * X.beta := by
    have hv12 := abs_lt.mp (hX.vertex_diameter_bounds.1
      (if code.orientation then C.bottomVertex e else C.leftVertex e)
      (if code.orientation then C.topVertex e' else C.rightVertex e'))
    have hv21 := abs_lt.mp (hX.vertex_diameter_bounds.1
      (if code.orientation then C.bottomVertex e' else C.leftVertex e')
      (if code.orientation then C.topVertex e else C.rightVertex e))
    rw [abs_lt]
    constructor <;> nlinarith [hcell1.1, hcell1.2.1, hcell2.1, hcell2.2.1]
  have hdy : |c.im - c'.im| < (code.checkingRadius : Real) * X.alpha := by
    have hv12 := abs_lt.mp (hX.vertex_diameter_bounds.2
      (if code.orientation then C.leftVertex e else C.bottomVertex e)
      (if code.orientation then C.rightVertex e' else C.topVertex e'))
    have hv21 := abs_lt.mp (hX.vertex_diameter_bounds.2
      (if code.orientation then C.leftVertex e' else C.bottomVertex e')
      (if code.orientation then C.rightVertex e else C.topVertex e))
    rw [abs_lt]
    constructor <;> nlinarith [hcell1.2.2.1, hcell1.2.2.2, hcell2.2.2.1, hcell2.2.2.2]
  have hcx : c.re = X.representativeX ⟨j, r⟩ + (n : Real) * X.beta := by
    simp [c, triangularSemanticCentre, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcx' : c'.re = X.representativeX ⟨j, r'⟩ + (n' : Real) * X.beta := by
    simp [c', triangularSemanticCentre, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcy : c.im = X.representativeY ⟨j, r⟩ + (n : Real) * X.shear j +
      (k : Real) * X.alpha := by
    simp [c, triangularSemanticCentre, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hcy' : c'.im = X.representativeY ⟨j, r'⟩ + (n' : Real) * X.shear j +
      (k' : Real) * X.alpha := by
    simp [c', triangularSemanticCentre, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hrepX : |X.representativeX ⟨j, r⟩ - X.representativeX ⟨j, r'⟩| < X.beta := by
    rw [abs_lt]
    rcases hX.representatives_normalized ⟨j, r⟩ with ⟨hr0, hr1⟩
    rcases hX.representatives_normalized ⟨j, r'⟩ with ⟨hr'0, hr'1⟩
    constructor <;> nlinarith
  have hrepY : |X.representativeY ⟨j, r⟩ - X.representativeY ⟨j, r'⟩| < X.alpha := by
    rw [abs_lt]
    rcases hX.representatives_normalized ⟨j, r⟩ with ⟨_, hr0, hr1⟩
    rcases hX.representatives_normalized ⟨j, r'⟩ with ⟨_, hr'0, hr'1⟩
    constructor <;> nlinarith
  have hndiff : |((n - n' : Int) : Real) * X.beta| <
      ((code.checkingRadius : Real) + 1) * X.beta := by
    have hdx' := abs_lt.mp hdx
    have hrepX' := abs_lt.mp hrepX
    rw [hcx, hcx'] at hdx'
    have hzcast : ((n - n' : Int) : Real) * X.beta =
        (n : Real) * X.beta - (n' : Real) * X.beta := by
      push_cast
      ring
    rw [hzcast, abs_lt]
    constructor <;> nlinarith
  have hnabs := int_natAbs_le_of_abs_mul_lt_local (n - n') code.checkingRadius
    X.beta hX.periods_pos.2 hndiff
  have hzloR : -((code.checkingRadius : Real) + 1) ≤ ((n - n' : Int) : Real) := by
    have h := (abs_lt.mp hndiff).1
    nlinarith [hX.periods_pos.2]
  have hzhiR : ((n - n' : Int) : Real) ≤ (code.checkingRadius : Real) + 1 := by
    have h := (abs_lt.mp hndiff).2
    nlinarith [hX.periods_pos.2]
  have hshearLo : -((code.checkingRadius : Real) + 1) * X.alpha ≤
      ((n - n' : Int) : Real) * X.shear j := by
    by_cases hz : 0 ≤ ((n - n' : Int) : Real)
    · have hnonneg : 0 ≤ ((n - n' : Int) : Real) * X.shear j :=
        mul_nonneg hz (hX.shear_normalized j).1
      nlinarith [hX.periods_pos.1]
    · have hz0 : ((n - n' : Int) : Real) ≤ 0 := le_of_not_ge hz
      have hmul1 := mul_le_mul_of_nonneg_right hzloR hX.periods_pos.1.le
      have hmul2 := mul_le_mul_of_nonpos_left (le_of_lt (hX.shear_normalized j).2) hz0
      nlinarith
  have hshearHi : ((n - n' : Int) : Real) * X.shear j ≤
      ((code.checkingRadius : Real) + 1) * X.alpha := by
    by_cases hz : 0 ≤ ((n - n' : Int) : Real)
    · have hmul1 := mul_le_mul_of_nonneg_right hzhiR hX.periods_pos.1.le
      have hmul2 := mul_le_mul_of_nonneg_left (le_of_lt (hX.shear_normalized j).2) hz
      nlinarith
    · have hz0 : ((n - n' : Int) : Real) ≤ 0 := le_of_not_ge hz
      have hnonpos : ((n - n' : Int) : Real) * X.shear j ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hz0 (hX.shear_normalized j).1
      nlinarith [hX.periods_pos.1]
  have hkdifference : |((k - k' : Int) : Real) * X.alpha| <
      ((2 * code.checkingRadius + 3 : Nat) : Real) * X.alpha := by
    have hdy' := abs_lt.mp hdy
    have hrepY' := abs_lt.mp hrepY
    rw [hcy, hcy'] at hdy'
    have hzshear : ((n - n' : Int) : Real) * X.shear j =
        (n : Real) * X.shear j - (n' : Real) * X.shear j := by
      push_cast
      ring
    have hzcast : ((k - k' : Int) : Real) * X.alpha =
        (k : Real) * X.alpha - (k' : Real) * X.alpha := by
      push_cast
      ring
    have hrad : ((2 * code.checkingRadius + 3 : Nat) : Real) =
        2 * (code.checkingRadius : Real) + 3 := by
      push_cast
      ring
    rw [hzcast, abs_lt]
    rw [hrad]
    constructor <;> nlinarith [hdy'.1, hdy'.2, hrepY'.1, hrepY'.2, hzshear]
  have hkdifference' : |((k - k' : Int) : Real) * X.alpha| <
      (((2 * code.checkingRadius + 2 : Nat) : Real) + 1) * X.alpha := by
    convert hkdifference using 1
    push_cast
    ring
  have hkabs := int_natAbs_le_of_abs_mul_lt_local (k - k')
    (2 * code.checkingRadius + 2) X.alpha hX.periods_pos.1 hkdifference'
  refine ⟨n', k', ?_, ?_, ?_, ?_⟩
  · simpa using hnabs
  · omega
  · simpa using hkabs
  · omega

private theorem triangular_target_periodic_local : ∀ (code : RawTriangularCode)
      (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
      (p : Tiling.Plane) (n k : Int),
    p ∈ triangularPieceTarget code X j ↔
      p + n • triangularPieceFirstPeriod code X j +
        k • triangularPieceSecondPeriod code X ∈ triangularPieceTarget code X j := by
  intro code X j p n k
  constructor
  · intro hp
    have hshift :
        (p + n • triangularPieceFirstPeriod code X j +
          k • triangularPieceSecondPeriod code X).re =
          p.re + (n : Real) * X.beta := by
      simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod]
    simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion] at hp ⊢
    rcases hp with ⟨q, ell, hleft, hright⟩
    refine ⟨q + n, ell, ?_, ?_⟩
    · rw [hshift]
      change X.intervalLeft ⟨j, ell⟩ + ((q + n : Int) : Real) * X.beta <
        p.re + (n : Real) * X.beta
      convert add_lt_add_right hleft ((n : Real) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
    · rw [hshift]
      change p.re + (n : Real) * X.beta <
        X.intervalRight ⟨j, ell⟩ + ((q + n : Int) : Real) * X.beta
      convert add_lt_add_right hright ((n : Real) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
  · intro hp
    have hshift :
        (p + n • triangularPieceFirstPeriod code X j +
          k • triangularPieceSecondPeriod code X).re =
          p.re + (n : Real) * X.beta := by
      simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod]
    simp only [triangularPieceTarget, triangularBaseSet, Set.mem_iUnion] at hp ⊢
    rcases hp with ⟨q, ell, hleft, hright⟩
    rw [hshift] at hleft hright
    refine ⟨q - n, ell, ?_, ?_⟩
    · change X.intervalLeft ⟨j, ell⟩ + ((q - n : Int) : Real) * X.beta < p.re
      convert sub_lt_sub_right hleft ((n : Real) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)
    · change p.re <
        X.intervalRight ⟨j, ell⟩ + ((q - n : Int) : Real) * X.beta
      convert sub_lt_sub_right hright ((n : Real) * X.beta) using 1 <;>
        first | rfl | (push_cast; ring)

private def triangularHalfOpenFundamentalBox (code : RawTriangularCode)
    (X : TriangularRawParameters code) : Set Tiling.Plane :=
  {p | 0 ≤ p.re ∧ p.re < X.beta ∧ 0 ≤ p.im ∧ p.im < X.alpha}

private theorem triangular_halfOpen_translate_cover_local : ∀ {C} (R : Realization C)
    code X, TriangularChecks R code X → ∀ j p,
    ∃ a b : Int,
      p ∈ (a • triangularPieceFirstPeriod code X j +
        b • triangularPieceSecondPeriod code X) +ᵥ
        triangularHalfOpenFundamentalBox code X := by
  intro C R code X hX j p
  let a : Int := ⌊p.re / X.beta⌋
  let b : Int := ⌊(p.im - (a : Real) * X.shear j) / X.alpha⌋
  have hβ : 0 < X.beta := hX.periods_pos.2
  have hα : 0 < X.alpha := hX.periods_pos.1
  have ha0 : (a : Real) ≤ p.re / X.beta := by
    dsimp [a]
    exact Int.floor_le _
  have ha1 : p.re / X.beta < (a : Real) + 1 := by
    dsimp [a]
    exact Int.lt_floor_add_one _
  have hb0 : (b : Real) ≤ (p.im - (a : Real) * X.shear j) / X.alpha := by
    dsimp [b]
    exact Int.floor_le _
  have hb1 : (p.im - (a : Real) * X.shear j) / X.alpha < (b : Real) + 1 := by
    dsimp [b]
    exact Int.lt_floor_add_one _
  have ha0' : (a : Real) * X.beta ≤ p.re := by
    exact (le_div_iff₀ hβ).mp ha0
  have ha1' : p.re < ((a : Real) + 1) * X.beta := by
    exact (div_lt_iff₀ hβ).mp ha1
  have hb0' : (b : Real) * X.alpha ≤ p.im - (a : Real) * X.shear j := by
    exact (le_div_iff₀ hα).mp hb0
  have hb1' : p.im - (a : Real) * X.shear j < ((b : Real) + 1) * X.alpha := by
    exact (div_lt_iff₀ hα).mp hb1
  let d := a • triangularPieceFirstPeriod code X j +
    b • triangularPieceSecondPeriod code X
  let q := p - d
  refine ⟨a, b, ?_⟩
  refine Set.mem_vadd_set.mpr ⟨q, ?_, ?_⟩
  · change 0 ≤ q.re ∧ q.re < X.beta ∧ 0 ≤ q.im ∧ q.im < X.alpha
    dsimp [q, d]
    simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod]
    constructor
    · nlinarith [ha0']
    constructor
    · nlinarith [ha1']
    constructor
    · nlinarith [hb0']
    · nlinarith [hb1']
  · dsimp [q, d]
    simp only [sub_eq_add_neg]
    abel_nf

private theorem triangular_halfOpen_translate_unique_local : ∀ {C} (R : Realization C)
    code X, TriangularChecks R code X → ∀ j (a b a' b' : Int) p,
    p ∈ (a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X) +ᵥ
        triangularHalfOpenFundamentalBox code X →
    p ∈ (a' • triangularPieceFirstPeriod code X j +
      b' • triangularPieceSecondPeriod code X) +ᵥ
        triangularHalfOpenFundamentalBox code X →
    a = a' ∧ b = b' := by
  intro C R code X hX j a b a' b' p hp hp'
  have hβ : 0 < X.beta := hX.periods_pos.2
  have hα : 0 < X.alpha := hX.periods_pos.1
  rcases Set.mem_vadd_set.mp hp with ⟨q, hq, hpq⟩
  rcases Set.mem_vadd_set.mp hp' with ⟨q', hq', hpq'⟩
  have hqre : (a : Real) * X.beta ≤ p.re ∧ p.re < ((a : Real) + 1) * X.beta := by
    have h := hq
    simp only [triangularHalfOpenFundamentalBox, Set.mem_ofPred_eq] at h
    have heq := congrArg Complex.re hpq.symm
    simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod,
      Complex.add_re] at heq
    constructor <;> nlinarith [h.1, h.2.1]
  have hqre' : (a' : Real) * X.beta ≤ p.re ∧ p.re < ((a' : Real) + 1) * X.beta := by
    have h := hq'
    simp only [triangularHalfOpenFundamentalBox, Set.mem_ofPred_eq] at h
    have heq := congrArg Complex.re hpq'.symm
    simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod,
      Complex.add_re] at heq
    constructor <;> nlinarith [h.1, h.2.1]
  have hab : a = a' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : (a : Real) + 1 ≤ (a' : Real) := by
        exact_mod_cast (show a + 1 ≤ a' by omega)
      nlinarith [hqre.2, hqre'.1]
    · have hstep : (a' : Real) + 1 ≤ (a : Real) := by
        exact_mod_cast (show a' + 1 ≤ a by omega)
      nlinarith [hqre'.2, hqre.1]
  have hqim : (b : Real) * X.alpha ≤
      p.im - (a : Real) * X.shear j ∧
      p.im - (a : Real) * X.shear j < ((b : Real) + 1) * X.alpha := by
    have h := hq
    simp only [triangularHalfOpenFundamentalBox, Set.mem_ofPred_eq] at h
    have heq := congrArg Complex.im hpq.symm
    simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod,
      Complex.add_im] at heq
    constructor <;> nlinarith [h.2.2.1, h.2.2.2]
  have hqim' : (b' : Real) * X.alpha ≤
      p.im - (a' : Real) * X.shear j ∧
      p.im - (a' : Real) * X.shear j < ((b' : Real) + 1) * X.alpha := by
    have h := hq'
    simp only [triangularHalfOpenFundamentalBox, Set.mem_ofPred_eq] at h
    have heq := congrArg Complex.im hpq'.symm
    simp [triangularPieceFirstPeriod, triangularPieceSecondPeriod,
      Complex.add_im] at heq
    constructor <;> nlinarith [h.2.2.1, h.2.2.2]
  have hbc : b = b' := by
    subst hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hstep : (b : Real) + 1 ≤ (b' : Real) := by
        exact_mod_cast (show b + 1 ≤ b' by omega)
      nlinarith [hqim.2, hqim'.1]
    · have hstep : (b' : Real) + 1 ≤ (b : Real) := by
        exact_mod_cast (show b' + 1 ≤ b by omega)
      nlinarith [hqim'.2, hqim.1]
  exact ⟨hab, hbc⟩

private theorem triangular_centreSet_add_period_local
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) (v : Tiling.Plane) (a b : Int)
    (hv : v = a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X) :
    v +ᵥ triangularCentreSet code X j ⊆ triangularCentreSet code X j := by
  intro p hp
  rcases Set.mem_vadd_set.mp hp with ⟨q, hq, rfl⟩
  rcases hq with ⟨r, n, k, hq⟩
  refine ⟨r, n + a, k + b, ?_⟩
  rw [hv, vadd_eq_add, hq]
  simp [triangularSemanticCentre, triangularPieceFirstPeriod,
    triangularPieceSecondPeriod]
  ring

private theorem triangular_openUnion_period_iff {C : RegionCode}
    (R : Realization C) (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
    (v : Tiling.Plane) (a b : Int)
    (hv : v = a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X) (p : Tiling.Plane) :
    p ∈ Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
        (triangularCentreSet code X j) ↔
      v + p ∈ Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
        (triangularCentreSet code X j) := by
  constructor
  · intro hp
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hp ⊢
    obtain ⟨c, hc⟩ := hp
    let c' : (triangularCentreSet code X j) :=
      ⟨v + c, triangular_centreSet_add_period_local code X j v a b hv
        ⟨c, c.property, rfl⟩⟩
    refine ⟨c', ?_⟩
    rcases Set.mem_vadd_set.mp hc with ⟨z, hz, hzc⟩
    refine Set.mem_vadd_set.mpr ⟨z, hz, ?_⟩
    dsimp [c']
    rw [vadd_eq_add] at hzc
    rw [add_assoc, hzc]
  · intro hp
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hp ⊢
    obtain ⟨c, hc⟩ := hp
    let c' : (triangularCentreSet code X j) :=
      ⟨-v + c, triangular_centreSet_add_period_local code X j (-v) (-a) (-b) (by
        rw [hv]
        module) ⟨c, c.property, rfl⟩⟩
    refine ⟨c', ?_⟩
    rcases Set.mem_vadd_set.mp hc with ⟨z, hz, hzc⟩
    refine Set.mem_vadd_set.mpr ⟨z, hz, ?_⟩
    dsimp [c']
    rw [vadd_eq_add] at hzc
    rw [add_assoc, hzc]
    abel

private theorem triangular_halfOpen_outside_open_null_local : ∀ {C}
    (R : Realization C) code X, TriangularChecks R code X →
    MeasureTheory.volume
      (triangularHalfOpenFundamentalBox code X \
        triangularOpenFundamentalBox code X) = 0 := by
  intro C R code X hX
  apply MeasureTheory.measure_mono_null ?_
    (rectangle_boundary_null 0 X.beta 0 X.alpha)
  intro p hp
  rcases hp with ⟨hpH, hpO⟩
  refine ⟨?_, ?_⟩
  · simp only [triangularHalfOpenFundamentalBox, Set.mem_ofPred_eq] at hpH
    exact ⟨hpH.1, hpH.2.1.le, hpH.2.2.1, hpH.2.2.2.le⟩
  · simpa only [triangularOpenFundamentalBox, Set.mem_ofPred_eq] using hpO

private theorem triangular_target_period_iff {C : RegionCode}
    (_R : Realization C) (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code))
    (v : Tiling.Plane) (a b : Int)
    (hv : v = a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X) (p : Tiling.Plane) :
    p ∈ triangularPieceTarget code X j ↔
      v + p ∈ triangularPieceTarget code X j := by
  have h := triangular_target_periodic_local code X j p a b
  simpa [hv, add_comm, add_left_comm, add_assoc] using h

private theorem triangular_piece_global_ae_identity_local : ∀ {C} (R : Realization C)
    code X, TriangularChecks R code X → ∀ j,
    MeasureTheory.volume
      ((Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
          (triangularCentreSet code X j)) \
        triangularPieceTarget code X j) = 0 ∧
    MeasureTheory.volume
      (triangularPieceTarget code X j \
        Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
          (triangularCentreSet code X j)) = 0 := by
  intro C R code X hX j
  classical
  let H : Set Tiling.Plane := triangularHalfOpenFundamentalBox code X
  let O : Set Tiling.Plane := triangularOpenFundamentalBox code X
  let U : Set Tiling.Plane :=
    Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
      (triangularCentreSet code X j)
  let T : Set Tiling.Plane := triangularPieceTarget code X j
  have hlocal := triangular_piece_local_ae_identity R code X hX j
  have hboundary := triangular_halfOpen_outside_open_null_local R code X hX
  have hcover : Set.univ ⊆ ⋃ a : Int, ⋃ b : Int,
      (a • triangularPieceFirstPeriod code X j +
        b • triangularPieceSecondPeriod code X) +ᵥ H := by
    intro p hp
    obtain ⟨a, b, hab⟩ := triangular_halfOpen_translate_cover_local R code X hX j p
    exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, hab⟩⟩
  have hnull₁ : ∀ a b : Int, MeasureTheory.volume
      ((((a • triangularPieceFirstPeriod code X j +
        b • triangularPieceSecondPeriod code X) +ᵥ H) ∩ U) \ T) = 0 := by
    intro a b
    let d : Tiling.Plane := a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X
    let A : Set Tiling.Plane := (O ∩ U) \ T
    let B : Set Tiling.Plane := H \ O
    have hzero : MeasureTheory.volume (d +ᵥ (A ∪ B)) = 0 := by
      rw [MeasureTheory.measure_vadd]
      exact MeasureTheory.measure_union_null hlocal.1 hboundary
    apply MeasureTheory.measure_mono_null ?_ hzero
    intro p hp
    rcases hp with ⟨⟨hpShift, hpU⟩, hpTnot⟩
    rcases Set.mem_vadd_set.mp hpShift with ⟨q, hq, hpq⟩
    have hpqD : d + q = p := by
      dsimp [d]
      simpa [vadd_eq_add] using hpq
    have hperU := triangular_openUnion_period_iff R code X j d a b rfl q
    have hqU : q ∈ U := by
      apply hperU.mpr
      rw [hpqD]
      exact hpU
    refine Set.mem_vadd_set.mpr ⟨q, ?_, hpq⟩
    by_cases hqO : q ∈ O
    · left
      refine ⟨⟨hqO, hqU⟩, ?_⟩
      intro hqT
      apply hpTnot
      have hper := triangular_target_period_iff R code X j d a b rfl q
      have hdT := hper.mp hqT
      rw [hpqD] at hdT
      exact hdT
    · right
      exact ⟨hq, hqO⟩
  have hnull₂ : ∀ a b : Int, MeasureTheory.volume
      ((((a • triangularPieceFirstPeriod code X j +
        b • triangularPieceSecondPeriod code X) +ᵥ H) ∩ T) \ U) = 0 := by
    intro a b
    let d : Tiling.Plane := a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X
    let A : Set Tiling.Plane := (O ∩ T) \ U
    let B : Set Tiling.Plane := H \ O
    have hzero : MeasureTheory.volume (d +ᵥ (A ∪ B)) = 0 := by
      rw [MeasureTheory.measure_vadd]
      exact MeasureTheory.measure_union_null hlocal.2 hboundary
    apply MeasureTheory.measure_mono_null ?_ hzero
    intro p hp
    rcases hp with ⟨⟨hpShift, hpT⟩, hpUnot⟩
    rcases Set.mem_vadd_set.mp hpShift with ⟨q, hq, hpq⟩
    have hpqD : d + q = p := by
      dsimp [d]
      simpa [vadd_eq_add] using hpq
    have hperT := triangular_target_period_iff R code X j d a b rfl q
    have hqT : q ∈ T := by
      apply hperT.mpr
      rw [hpqD]
      exact hpT
    refine Set.mem_vadd_set.mpr ⟨q, ?_, hpq⟩
    by_cases hqO : q ∈ O
    · left
      refine ⟨⟨hqO, hqT⟩, ?_⟩
      intro hqU
      apply hpUnot
      have hper := triangular_openUnion_period_iff R code X j d a b rfl q
      have hdU := hper.mp hqU
      rw [hpqD] at hdU
      exact hdU
    · right
      exact ⟨hq, hqO⟩
  have htrans₁ : MeasureTheory.volume
      (⋃ a : Int, ⋃ b : Int,
        ((((a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X) +ᵥ H) ∩ U) \ T)) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro a
    apply MeasureTheory.measure_iUnion_null
    intro b
    exact hnull₁ a b
  have htrans₂ : MeasureTheory.volume
      (⋃ a : Int, ⋃ b : Int,
        ((((a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X) +ᵥ H) ∩ T) \ U)) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro a
    apply MeasureTheory.measure_iUnion_null
    intro b
    exact hnull₂ a b
  constructor
  · apply MeasureTheory.measure_mono_null ?_ htrans₁
    intro p hp
    have hpcover := hcover (Set.mem_univ p)
    rcases Set.mem_iUnion.mp hpcover with ⟨a, ha⟩
    rcases Set.mem_iUnion.mp ha with ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ?_⟩⟩
    exact ⟨⟨hb, hp.1⟩, hp.2⟩
  · apply MeasureTheory.measure_mono_null ?_ htrans₂
    intro p hp
    have hpcover := hcover (Set.mem_univ p)
    rcases Set.mem_iUnion.mp hpcover with ⟨a, ha⟩
    rcases Set.mem_iUnion.mp ha with ⟨b, hb⟩
    refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ?_⟩⟩
    exact ⟨⟨hb, hp.1⟩, hp.2⟩

private theorem exists_common_semantic_open_cells_of_measure_ne_zero_local :
    ∀ {C} (R : Realization C) epsilon (c c' : Tiling.Plane),
    MeasureTheory.volume
      ((c +ᵥ (selectedRegion R epsilon).openCarrier) ∩
        (c' +ᵥ (selectedRegion R epsilon).openCarrier)) ≠ 0 →
    ∃ p e e', p ∈ (c +ᵥ (selectedRegion R epsilon).openCarrier) ∩
          (c' +ᵥ (selectedRegion R epsilon).openCarrier) ∧
      semanticOpenCell R epsilon e c p ∧ semanticOpenCell R epsilon e' c' p := by
  intro C R epsilon c c' hA
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R epsilon e 0 p}
  let U : Set Tiling.Plane := c +ᵥ O
  let U' : Set Tiling.Plane := c' +ᵥ O
  let K : Set Tiling.Plane := c +ᵥ (selectedRegion R epsilon).openCarrier
  let K' : Set Tiling.Plane := c' +ᵥ (selectedRegion R epsilon).openCarrier
  have hU : U =ᵐ[MeasureTheory.volume] K := by
    apply (MeasureTheory.vadd_set_ae_eq c).mpr
    simpa [O] using selected_presentation_ae R epsilon
  have hU' : U' =ᵐ[MeasureTheory.volume] K' := by
    apply (MeasureTheory.vadd_set_ae_eq c').mpr
    simpa [O] using selected_presentation_ae R epsilon
  obtain ⟨hUK, hKU⟩ := MeasureTheory.ae_eq_set.mp hU
  obtain ⟨hUK', hK'U'⟩ := MeasureTheory.ae_eq_set.mp hU'
  have hbad : MeasureTheory.volume ((K ∩ K') \ (U ∩ U')) = 0 := by
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hKU hK'U')
    rintro p ⟨⟨hpK, hpK'⟩, hpnot⟩
    by_cases hpU : p ∈ U
    · right
      exact ⟨hpK', fun hpU' => hpnot ⟨hpU, hpU'⟩⟩
    · left
      exact ⟨hpK, hpU⟩
  have hgood : MeasureTheory.volume ((K ∩ K') ∩ (U ∩ U')) ≠ 0 := by
    by_contra hz
    apply hA
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hbad hz)
    intro p hp
    by_cases hpU : p ∈ U ∩ U'
    · exact Or.inr ⟨hp, hpU⟩
    · exact Or.inl ⟨hp, hpU⟩
  obtain ⟨p, hp⟩ := MeasureTheory.nonempty_of_measure_ne_zero hgood
  rcases hp with ⟨⟨hpK, hpK'⟩, ⟨hpU, hpU'⟩⟩
  rcases Set.mem_vadd_set.mp hpU with ⟨z, hz, hpz⟩
  rcases Set.mem_iUnion.mp hz with ⟨e, he⟩
  rcases Set.mem_vadd_set.mp hpU' with ⟨z', hz', hpz'⟩
  rcases Set.mem_iUnion.mp hz' with ⟨e', he'⟩
  refine ⟨p, e, e', ⟨hpK, hpK'⟩, ?_, ?_⟩
  · change p ∈ {p | semanticOpenCell R epsilon e c p}
    rw [semanticOpenCell_vadd_local R epsilon e c]
    exact ⟨z, he, hpz⟩
  · change p ∈ {p | semanticOpenCell R epsilon e' c' p}
    rw [semanticOpenCell_vadd_local R epsilon e' c']
    exact ⟨z', he', hpz'⟩

private theorem triangular_semantic_centre_shift_local : ∀ {code} (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code)) r (n k a b : Int),
    triangularSemanticCentre code X j r n k =
      triangularSemanticCentre code X j r (n - a) (k - b) +
        a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X := by
  intro code X j r n k a b
  simp [triangularSemanticCentre, triangularPieceFirstPeriod,
    triangularPieceSecondPeriod]
  ring

private theorem triangular_semantic_open_cell_translate_local :
    ∀ {C} (R : Realization C) epsilon code X j r n k (a b : Int)
      (p : Tiling.Plane) (e : Fin C.cellCount),
    semanticOpenCell R epsilon e
      (triangularSemanticCentre code X j r n k) p →
    semanticOpenCell R epsilon e
      (triangularSemanticCentre code X j r (n - a) (k - b))
      ((-(a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X)) +ᵥ p) := by
  intro C R epsilon code X j r n k a b p e hcell
  change p ∈ {p | semanticOpenCell R epsilon e
    (triangularSemanticCentre code X j r n k) p} at hcell
  change ((-(a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X)) +ᵥ p) ∈
    {p | semanticOpenCell R epsilon e
      (triangularSemanticCentre code X j r (n - a) (k - b)) p}
  rw [semanticOpenCell_vadd_local R epsilon e
    (triangularSemanticCentre code X j r n k)] at hcell
  rw [semanticOpenCell_vadd_local R epsilon e
    (triangularSemanticCentre code X j r (n - a) (k - b))]
  rcases hcell with ⟨q, hq, hpq⟩
  refine ⟨q, hq, ?_⟩
  change triangularSemanticCentre code X j r n k + q = p at hpq
  change (triangularSemanticCentre code X j r (n - a) (k - b)) + q =
    (-(a • triangularPieceFirstPeriod code X j +
      b • triangularPieceSecondPeriod code X)) + p
  rw [← hpq]
  rw [triangular_semantic_centre_shift_local X j r n k a b]
  abel

private theorem triangular_piece_global_packing : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → ∀ j,
    Tiling.IsPacking (selectedRegion R code.orientation).toPolygonalRegion.prototileFamily
      ((selectedRegion R code.orientation).toPolygonalRegion.placements
        (triangularCentreSet code X j)) := by
  intro C R code X hX j
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  intro c hc c' hc' hcc'
  by_contra hnd
  obtain ⟨p, hp⟩ := Set.not_disjoint_iff.mp hnd
  have hvol : MeasureTheory.volume
      ((c +ᵥ (selectedRegion R code.orientation).openCarrier) ∩
        (c' +ᵥ (selectedRegion R code.orientation).openCarrier)) ≠ 0 := by
    exact (((selectedRegion R code.orientation).openCarrier_regularOpen.1.vadd c).inter
      ((selectedRegion R code.orientation).openCarrier_regularOpen.1.vadd c')).measure_ne_zero
      MeasureTheory.volume ⟨p, hp.1, hp.2⟩
  rcases hc with ⟨r, n, k, rfl⟩
  rcases hc' with ⟨r', n', k', rfl⟩
  obtain ⟨a, b, ha, ha', hb, hb'⟩ :=
    triangular_overlap_reduction R code X hX j r r' n n' k k' hvol
  obtain ⟨i, hi, hir, hin, hik⟩ := triangular_index_enumeration_complete
    code j r (n - a) (k - b) ha hb
  obtain ⟨i', hi', hir', hin', hik'⟩ := triangular_index_enumeration_complete
    code j r' (n' - a) (k' - b) ha' hb'
  have hne : i ≠ i' := by
    intro heq
    apply hcc'
    have heq' : triangularSemanticCentre code X j r (n - a) (k - b) =
        triangularSemanticCentre code X j r' (n' - a) (k' - b) := by
      calc
        triangularSemanticCentre code X j r (n - a) (k - b) =
            triangularSemanticCentre code X j i.1
              (centeredInteger i.2.1) (centeredInteger i.2.2) := by
          rw [hir, hin, hik]
        _ = triangularSemanticCentre code X j i'.1
              (centeredInteger i'.2.1) (centeredInteger i'.2.2) := by
          exact congrArg (fun (z : TriangularFiniteIndex code j) =>
            triangularSemanticCentre code X j z.1
              (centeredInteger z.2.1) (centeredInteger z.2.2)) heq
        _ = triangularSemanticCentre code X j r' (n' - a) (k' - b) := by
          rw [hir', hin', hik']
    calc
      triangularSemanticCentre code X j r n k =
          triangularSemanticCentre code X j r (n - a) (k - b) +
            a • triangularPieceFirstPeriod code X j +
              b • triangularPieceSecondPeriod code X :=
        triangular_semantic_centre_shift_local X j r n k a b
      _ = triangularSemanticCentre code X j r' (n' - a) (k' - b) +
            a • triangularPieceFirstPeriod code X j +
              b • triangularPieceSecondPeriod code X := by rw [heq']
      _ = triangularSemanticCentre code X j r' n' k' := by
        rw [triangular_semantic_centre_shift_local X j r' n' k' a b]
  rcases hX.finite_packing j i i' hne with heq | hnonoverlap
  · apply hcc'
    have heq' : triangularSemanticCentre code X j r (n - a) (k - b) =
        triangularSemanticCentre code X j r' (n' - a) (k' - b) := by
      calc
        triangularSemanticCentre code X j r (n - a) (k - b) =
            triangularSemanticCentre code X j i.1
              (centeredInteger i.2.1) (centeredInteger i.2.2) := by
          rw [hir, hin, hik]
        _ = triangularSemanticCentre code X j i'.1
              (centeredInteger i'.2.1) (centeredInteger i'.2.2) := by
          exact heq
        _ = triangularSemanticCentre code X j r' (n' - a) (k' - b) := by
          rw [hir', hin', hik']
    calc
      triangularSemanticCentre code X j r n k =
          triangularSemanticCentre code X j r (n - a) (k - b) +
            a • triangularPieceFirstPeriod code X j +
              b • triangularPieceSecondPeriod code X := by
        exact triangular_semantic_centre_shift_local X j r n k a b
      _ = triangularSemanticCentre code X j r' (n' - a) (k' - b) +
            a • triangularPieceFirstPeriod code X j +
              b • triangularPieceSecondPeriod code X := by rw [heq']
      _ = triangularSemanticCentre code X j r' n' k' := by
        rw [triangular_semantic_centre_shift_local X j r' n' k' a b]
  · obtain ⟨q, e, e', hq, hqe, hqe'⟩ :=
      exists_common_semantic_open_cells_of_measure_ne_zero_local R code.orientation
        (triangularSemanticCentre code X j r n k)
        (triangularSemanticCentre code X j r' n' k') hvol
    have hqe1 := triangular_semantic_open_cell_translate_local R code.orientation
      code X j r n k a b q e hqe
    have hqe2 := triangular_semantic_open_cell_translate_local R code.orientation
      code X j r' n' k' a b q e' hqe'
    have hqe1' : semanticOpenCell R code.orientation e
        (triangularSemanticCentre code X j i.1
          (centeredInteger i.2.1) (centeredInteger i.2.2))
        ((-(a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X)) +ᵥ q) := by
      simpa only [hir, hin, hik] using hqe1
    have hqe2' : semanticOpenCell R code.orientation e'
        (triangularSemanticCentre code X j i'.1
          (centeredInteger i'.2.1) (centeredInteger i'.2.2))
        ((-(a • triangularPieceFirstPeriod code X j +
          b • triangularPieceSecondPeriod code X)) +ᵥ q) := by
      simpa only [hir', hin', hik'] using hqe2
    have hno := hnonoverlap e e'
    simp only [semanticCellsNonoverlap] at hno
    simp only [semanticOpenCell] at hqe1' hqe2'
    rcases hno with hno | hno | hno | hno <;>
      nlinarith [hqe1'.1, hqe1'.2.1, hqe1'.2.2.1, hqe1'.2.2.2,
        hqe2'.1, hqe2'.2.1, hqe2'.2.2.1, hqe2'.2.2.2]


private theorem triangular_piece_tiles_selected : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → ∀ j,
    Tiling.AxisParallel.TilesOn (selectedRegion R code.orientation)
      (triangularCentreSet code X j)
      {p | p.re ∈ triangularBaseSet code X j} := by
  intro C R code X hX j
  classical
  have hcount : (triangularCentreSet code X j).Countable := by
    have hrange : Set.Countable (Set.range (fun z :
        (Fin (triangularPiece code j).representativeCount × Int × Int) =>
          triangularSemanticCentre code X j z.1 z.2.1 z.2.2)) :=
      Set.countable_range _
    apply hrange.mono
    intro p hp
    rcases hp with ⟨r, n, k, rfl⟩
    exact ⟨(r, n, k), rfl⟩
  have hpack := triangular_piece_global_packing R code X hX j
  have hglobal := triangular_piece_global_ae_identity_local R code X hX j
  refine ⟨hcount, hpack, ?_⟩
  have hleft := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hglobal.1
  have hright := MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hglobal.2
  filter_upwards [hleft, hright] with p hpU hpT
  have heq : p ∈ Tiling.AxisParallel.openUnion (selectedRegion R code.orientation)
      (triangularCentreSet code X j) ↔ p ∈ triangularPieceTarget code X j := by
    constructor
    · intro hp
      by_contra hnot
      exact hpU ⟨hp, hnot⟩
    · intro hp
      by_contra hnot
      exact hpT ⟨hp, hnot⟩
  simpa only [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion,
    triangularPieceTarget, Set.mem_ofPred_eq] using heq.symm

private theorem triangular_bases_pairwise_ae_disjoint : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → Set.Pairwise Set.univ fun i j =>
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (triangularBaseSet code X i) (triangularBaseSet code X j) := by
  intro C R code X hX i _ j _ hij
  apply Disjoint.aedisjoint
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [triangularBaseSet, Set.mem_iUnion] at hxi hxj
  rcases hxi with ⟨q, ell, hx⟩
  rcases hxj with ⟨q', ell', hy⟩
  have hi := hX.intervals_normalized ⟨i, ell⟩
  have hj := hX.intervals_normalized ⟨j, ell'⟩
  have hidx : (⟨i, ell⟩ : TriangularIntervalIndex code) ≠ ⟨j, ell'⟩ := by
    intro heq
    apply hij
    exact congrArg (fun z => z.1) heq
  have hsep := hX.interval_interiors_disjoint ⟨i, ell⟩ ⟨j, ell'⟩ hidx
  have hβ : 0 < X.beta := hX.periods_pos.2
  rcases lt_trichotomy q q' with hqq | rfl | hqq
  · have hqcast : (q : ℝ) + 1 ≤ (q' : ℝ) := by
      exact_mod_cast (show q + 1 ≤ q' by omega)
    have hmul : ((q : ℝ) + 1) * X.beta ≤ (q' : ℝ) * X.beta :=
      mul_le_mul_of_nonneg_right hqcast hβ.le
    have hbound : X.intervalRight ⟨i, ell⟩ + (q : ℝ) * X.beta ≤
        X.intervalLeft ⟨j, ell'⟩ + (q' : ℝ) * X.beta := by
      nlinarith [hi.1, hi.2.2, hj.1, hmul]
    exact (not_lt_of_ge hbound) (lt_trans hy.1 hx.2)
  · rcases hsep with hsep | hsep
    · have hbound : X.intervalRight ⟨i, ell⟩ + (q : ℝ) * X.beta ≤
          X.intervalLeft ⟨j, ell'⟩ + (q : ℝ) * X.beta := by
        simpa [add_comm] using add_le_add_right hsep ((q : ℝ) * X.beta)
      exact (not_lt_of_ge hbound) (lt_trans hy.1 hx.2)
    · have hbound : X.intervalRight ⟨j, ell'⟩ + (q : ℝ) * X.beta ≤
          X.intervalLeft ⟨i, ell⟩ + (q : ℝ) * X.beta := by
        simpa [add_comm] using add_le_add_right hsep ((q : ℝ) * X.beta)
      exact (not_lt_of_ge hbound) (lt_trans hx.1 hy.2)
  · have hqcast : (q' : ℝ) + 1 ≤ (q : ℝ) := by
      exact_mod_cast (show q' + 1 ≤ q by omega)
    have hmul : ((q' : ℝ) + 1) * X.beta ≤ (q : ℝ) * X.beta :=
      mul_le_mul_of_nonneg_right hqcast hβ.le
    have hbound : X.intervalRight ⟨j, ell'⟩ + (q' : ℝ) * X.beta ≤
        X.intervalLeft ⟨i, ell⟩ + (q : ℝ) * X.beta := by
      nlinarith [hj.1, hj.2.2, hi.1, hmul]
    exact (not_lt_of_ge hbound) (lt_trans hx.1 hy.2)

private theorem triangular_bases_cover : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X →
      (⋃ j, triangularBaseSet code X j) =ᵐ[MeasureTheory.volume] Set.univ := by
  intro C R code X hX
  let boundary : Set ℝ := Set.range
    (fun z : Int × Option (TriangularIntervalIndex code × Bool) =>
      match z.2 with
      | none => (z.1 : ℝ) * X.beta
      | some ib =>
          if ib.2 then X.intervalRight ib.1 + (z.1 : ℝ) * X.beta
          else X.intervalLeft ib.1 + (z.1 : ℝ) * X.beta)
  have hboundary : boundary.Countable := Set.countable_range _
  filter_upwards [hboundary.ae_notMem MeasureTheory.volume] with x hx
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    let q : Int := Int.floor (x / X.beta)
    let r : ℝ := x - (q : ℝ) * X.beta
    have hβ : 0 < X.beta := hX.periods_pos.2
    have hqle : (q : ℝ) ≤ x / X.beta := by
      dsimp [q]
      exact Int.floor_le _
    have hqgt : x / X.beta < (q : ℝ) + 1 := by
      dsimp [q]
      exact Int.lt_floor_add_one _
    have hqle' : (q : ℝ) * X.beta ≤ x :=
      (le_div_iff₀ hβ).mp hqle
    have hqgt' : x < ((q : ℝ) + 1) * X.beta :=
      (div_lt_iff₀ hβ).mp hqgt
    have hr0 : 0 ≤ r := by
      dsimp [r]
      linarith
    have hrβ : r < X.beta := by
      dsimp [r]
      linarith
    have hxeq : x = r + (q : ℝ) * X.beta := by
      dsimp [r]
      ring
    by_cases hrpos : 0 < r
    · obtain ⟨i, hLi, hRi⟩ := hX.base_period_covered r hrpos hrβ
      have hLstrict : X.intervalLeft i < r := by
        by_contra hnot
        have heq : X.intervalLeft i = r :=
          le_antisymm hLi (le_of_not_gt hnot)
        apply hx
        refine ⟨(q, some (i, false)), ?_⟩
        change X.intervalLeft i + (q : ℝ) * X.beta = x
        calc
          X.intervalLeft i + (q : ℝ) * X.beta =
              r + (q : ℝ) * X.beta := by rw [heq]
          _ = x := hxeq.symm
      have hRstrict : r < X.intervalRight i := by
        by_contra hnot
        have heq : X.intervalRight i = r :=
          le_antisymm (le_of_not_gt hnot) hRi
        apply hx
        refine ⟨(q, some (i, true)), ?_⟩
        change X.intervalRight i + (q : ℝ) * X.beta = x
        calc
          X.intervalRight i + (q : ℝ) * X.beta =
              r + (q : ℝ) * X.beta := by rw [heq]
          _ = x := hxeq.symm
      change x ∈ ⋃ j, ⋃ q : Int, ⋃ ell : Fin (triangularPiece code j).intervalCount,
        Set.Ioo (X.intervalLeft ⟨j, ell⟩ + (q : ℝ) * X.beta)
          (X.intervalRight ⟨j, ell⟩ + (q : ℝ) * X.beta)
      refine Set.mem_iUnion.2 ⟨i.1, ?_⟩
      refine Set.mem_iUnion.2 ⟨q, ?_⟩
      refine Set.mem_iUnion.2 ⟨i.2, ?_⟩
      constructor
      · rw [hxeq]
        simpa [add_comm] using add_lt_add_right hLstrict ((q : ℝ) * X.beta)
      · rw [hxeq]
        simpa [add_comm] using add_lt_add_right hRstrict ((q : ℝ) * X.beta)
    · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) hr0
      exfalso
      apply hx
      refine ⟨(q, none), ?_⟩
      change (q : ℝ) * X.beta = x
      rw [hxeq, hrzero]
      ring

private theorem region_eq_of_support_eq_local {K L : Tiling.AxisParallel.Region}
    (h : K.support = L.support) : K = L := by
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      simp only [Tiling.AxisParallel.Region.mk.injEq]
      cases K with
      | mk Ks Kp Kn =>
        cases L with
        | mk Ls Lp Ln =>
          simpa only [Tiling.RationalPolygonal.PolygonalRegion.mk.injEq] using h

private theorem coordinateSwap_tilesOn_pullback : ∀ {C} (R : Realization C) (S : Set Tiling.Plane),
    Tiling.AxisParallel.TilesOn R.region.coordinateSwap S Set.univ →
    Tiling.AxisParallel.TilesOn R.region
      (Tiling.AxisParallel.coordinateSwap '' S) Set.univ := by
  intro C R S hTile
  have hSwap := Tiling.AxisParallel.tilesOn_coordinateSwap hTile
  have hRegion : R.region.coordinateSwap.coordinateSwap = R.region := by
    apply region_eq_of_support_eq_local
    ext z
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      simpa using hu
    · intro hz
      exact ⟨Tiling.AxisParallel.coordinateSwap z,
        ⟨z, hz, rfl⟩, Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
  rw [hRegion] at hSwap
  simpa using hSwap

private theorem triangular_union_tiles_selected : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X →
    Tiling.AxisParallel.TilesOn (selectedRegion R code.orientation)
      (⋃ j, triangularCentreSet code X j) Set.univ := by
  intro C R code X hX
  classical
  let K := selectedRegion R code.orientation
  have htile : ∀ j : Fin (triangularPieceCount code),
      Tiling.AxisParallel.TilesOn K (triangularCentreSet code X j)
        {p | p.re ∈ triangularBaseSet code X j} := by
    intro j
    exact triangular_piece_tiles_selected R code X hX j
  have hdisjoint : ∀ i j : Fin (triangularPieceCount code), i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume
        (triangularBaseSet code X i) (triangularBaseSet code X j) := by
    intro i j hij
    exact triangular_bases_pairwise_ae_disjoint R code X hX
      (Set.mem_univ i) (Set.mem_univ j) hij
  have hcover : (⋃ j : Fin (triangularPieceCount code),
      triangularBaseSet code X j) =ᵐ[MeasureTheory.volume] Set.univ :=
    triangular_bases_cover R code X hX
  exact Tiling.AxisParallel.Terminal.tilesOn_finite_iUnion_of_aePartition
    (K := K) htile hdisjoint hcover
theorem triangularChecks_sound : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → realizationPlaneTileable R := by
  intro C R code X hX
  let S : Set Tiling.Plane := ⋃ j, triangularCentreSet code X j
  have htile := triangular_union_tiles_selected R code X hX
  cases h : code.orientation with
  | false =>
      refine ⟨S, ?_⟩
      simpa [S, selectedRegion, h] using htile
  | true =>
      refine ⟨Tiling.AxisParallel.coordinateSwap '' S, ?_⟩
      apply coordinateSwap_tilesOn_pullback R S
      simpa [S, selectedRegion, h] using htile


private theorem triangular_neighbour_bounds : ∀ {C} (R : Realization C) code X,
    TriangularChecks R code X → ∀ j r n k,
    MeasureTheory.volume
      (((triangularSemanticCentre code X j r n k) +ᵥ
          (selectedRegion R code.orientation).openCarrier) ∩
        triangularOpenFundamentalBox code X) ≠ 0 →
    n.natAbs ≤ code.checkingRadius + 1 ∧ k.natAbs ≤ 2 * code.checkingRadius + 3 := by
  intro C R code X hX j r n k hvol
  let O : Set Tiling.Plane :=
    ⋃ e, {p | semanticOpenCell R code.orientation e 0 p}
  let A : Set Tiling.Plane :=
    ((triangularSemanticCentre code X j r n k) +ᵥ O) ∩
      triangularOpenFundamentalBox code X
  have hpres := selected_presentation_ae R code.orientation
  have hAae :
      A =ᵐ[MeasureTheory.volume]
        Set.inter ((triangularSemanticCentre code X j r n k) +ᵥ
            (selectedRegion R code.orientation).openCarrier)
          (triangularOpenFundamentalBox code X) := by
    exact ((MeasureTheory.vadd_set_ae_eq
      (triangularSemanticCentre code X j r n k)).mpr hpres).inter
      Filter.EventuallyEq.rfl
  have hAnonempty : A.Nonempty := by
    by_contra hempty
    have hEq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have hzero : MeasureTheory.volume A = 0 := by
      rw [hEq, MeasureTheory.measure_empty]
    have hmeasure := MeasureTheory.measure_congr hAae
    exact hvol (hmeasure ▸ hzero)
  rcases hAnonempty with ⟨p, hp⟩
  rcases hp with ⟨hpA, hpbox⟩
  rcases Set.mem_vadd_set.mp hpA with ⟨q, hq, hpq⟩
  rcases Set.mem_iUnion.mp hq with ⟨e, hqe⟩
  have hcell : semanticOpenCell R code.orientation e
      (triangularSemanticCentre code X j r n k) p := by
    have hpv : p ∈ (triangularSemanticCentre code X j r n k) +ᵥ
        {q | semanticOpenCell R code.orientation e 0 q} :=
      Set.mem_vadd_set.mpr ⟨q, hqe, hpq⟩
    rw [← semanticOpenCell_vadd_local R code.orientation e
      (triangularSemanticCentre code X j r n k)] at hpv
    exact hpv
  exact triangular_cell_neighbour_bounds_local R code X hX j r n k e p hcell hpbox

private theorem semantic_open_cell_exists_of_measure_ne_zero : ∀ {C} (R : Realization C)
    (centre : Tiling.Plane) (box : Set Tiling.Plane),
    MeasureTheory.volume ((centre +ᵥ R.region.openCarrier) ∩ box) ≠ 0 →
    ∃ p e, p ∈ (centre +ᵥ R.region.openCarrier) ∩ box ∧
      semanticOpenCell R false e centre p := by
  intro C R centre box hA
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R false e 0 p}
  let U : Set Tiling.Plane := centre +ᵥ O
  let K : Set Tiling.Plane := centre +ᵥ R.region.openCarrier
  have hU : U =ᵐ[MeasureTheory.volume] K := by
    apply (MeasureTheory.vadd_set_ae_eq centre).mpr
    exact selected_presentation_ae_false R
  obtain ⟨hUK, hKU⟩ := MeasureTheory.ae_eq_set.mp hU
  have hAne : (K ∩ box).Nonempty := by
    by_contra hn
    have he : K ∩ box = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    exact hA (he ▸ MeasureTheory.measure_empty)
  have hKU' : MeasureTheory.volume ((K ∩ box) \ U) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hKU
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  obtain ⟨p, hp⟩ := hAne
  have hAU : ∃ q, q ∈ K ∩ box ∧ q ∈ U := by
    by_contra hn
    have hsub : K ∩ box ⊆ K \ U := by
      intro q hq
      refine ⟨hq.1, ?_⟩
      intro hqU
      exact hn ⟨q, hq, hqU⟩
    have hz : MeasureTheory.volume (K ∩ box) = 0 :=
      MeasureTheory.measure_mono_null hsub hKU
    exact hA hz
  obtain ⟨q, hq, hqU⟩ := hAU
  rcases Set.mem_vadd_set.mp hqU with ⟨z, hz, hqz⟩
  rcases Set.mem_iUnion.mp hz with ⟨e, hze⟩
  refine ⟨q, e, hq, ?_⟩
  change q ∈ {p | semanticOpenCell R false e centre p}
  rw [semanticOpenCell_vadd R e centre]
  exact ⟨z, hze, hqz⟩

end Tiling.AxisParallel.Terminal.Executable.PositiveVerification

namespace Tiling.AxisParallel.Terminal.Executable.PositiveVerification


private theorem lattice_neighbour_bounds : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X → ∀ r n m,
    MeasureTheory.volume
      (((latticeSemanticCentre code X r n m) +ᵥ R.region.openCarrier) ∩
        latticeOpenCheckingBox code X) ≠ 0 →
      n.natAbs < code.firstIndexBound ∧ m.natAbs < code.secondIndexBound := by
  intro C R code X hX r n m hvol
  obtain ⟨p, e, hp, hcell⟩ :=
    semantic_open_cell_exists_of_measure_ne_zero R
      (latticeSemanticCentre code X r n m) (latticeOpenCheckingBox code X) hvol
  have hcell' :
      (latticeSemanticCentre code X r n m).re +
          (R.vertex (C.leftVertex e)).re < p.re ∧
        p.re < (latticeSemanticCentre code X r n m).re +
          (R.vertex (C.rightVertex e)).re ∧
        (latticeSemanticCentre code X r n m).im +
          (R.vertex (C.bottomVertex e)).im < p.im ∧
        p.im < (latticeSemanticCentre code X r n m).im +
          (R.vertex (C.topVertex e)).im := by
    simpa [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using hcell
  have hpbox :
      -X.horizontalBound < p.re ∧ p.re < X.horizontalBound ∧
        -X.verticalBound < p.im ∧ p.im < X.verticalBound := by
    simpa [latticeOpenCheckingBox] using hp.2
  let w : Tiling.Plane := n • X.firstPeriod + m • X.secondPeriod
  have hwre : w.re = (n : Real) * X.firstPeriod.re +
      (m : Real) * X.secondPeriod.re := by
    simp [w, Complex.add_re]
  have hwim : w.im = (n : Real) * X.firstPeriod.im +
      (m : Real) * X.secondPeriod.im := by
    simp [w, Complex.add_im]
  have hcentre : latticeSemanticCentre code X r n m =
      X.representative r + w := by
    dsimp [latticeSemanticCentre, w]
    module
  rw [hcentre] at hcell'
  have hwx_upper : w.re < 2 * X.horizontalBound +
      |(R.vertex (C.leftVertex e)).re - (R.vertex C.originVertex).re| := by
    have hrep := (hX.representatives_bounded r).1
    have hcellL := hcell'.1
    simp only [Complex.add_re] at hcellL
    have hrepL : -(X.horizontalBound) ≤ (X.representative r).re := by
      exact (abs_le.mp hrep).1
    have habsL : -(R.vertex (C.leftVertex e)).re ≤
        |(R.vertex (C.leftVertex e)).re| := neg_le_abs _
    have hleft : |(R.vertex (C.leftVertex e)).re -
        (R.vertex C.originVertex).re| = |(R.vertex (C.leftVertex e)).re| := by
      simp [R.origin_eq_zero]
    rw [hleft]
    nlinarith
  have hwx_lower : -(2 * X.horizontalBound +
      |(R.vertex (C.rightVertex e)).re - (R.vertex C.originVertex).re|) < w.re := by
    have hrep := (hX.representatives_bounded r).1
    have hcellR := hcell'.2.1
    simp only [Complex.add_re] at hcellR
    have hrepU : (X.representative r).re ≤ X.horizontalBound := by
      exact le_trans (le_abs_self _) hrep
    have habsR : (R.vertex (C.rightVertex e)).re ≤
        |(R.vertex (C.rightVertex e)).re| := le_abs_self _
    have hright : |(R.vertex (C.rightVertex e)).re -
        (R.vertex C.originVertex).re| = |(R.vertex (C.rightVertex e)).re| := by
      simp [R.origin_eq_zero]
    rw [hright]
    nlinarith
  have hwy_upper : w.im < 2 * X.verticalBound +
      |(R.vertex (C.bottomVertex e)).im - (R.vertex C.originVertex).im| := by
    have hrep := (hX.representatives_bounded r).2
    have hcellB := hcell'.2.2.1
    simp only [Complex.add_im] at hcellB
    have hrepL : -(X.verticalBound) ≤ (X.representative r).im := by
      exact (abs_le.mp hrep).1
    have habsB : -(R.vertex (C.bottomVertex e)).im ≤
        |(R.vertex (C.bottomVertex e)).im| := neg_le_abs _
    have hbottom : |(R.vertex (C.bottomVertex e)).im -
        (R.vertex C.originVertex).im| = |(R.vertex (C.bottomVertex e)).im| := by
      simp [R.origin_eq_zero]
    rw [hbottom]
    nlinarith
  have hwy_lower : -(2 * X.verticalBound +
      |(R.vertex (C.topVertex e)).im - (R.vertex C.originVertex).im|) < w.im := by
    have hrep := (hX.representatives_bounded r).2
    have hcellT := hcell'.2.2.2
    simp only [Complex.add_im] at hcellT
    have hrepU : (X.representative r).im ≤ X.verticalBound := by
      exact le_trans (le_abs_self _) hrep
    have habsT : (R.vertex (C.topVertex e)).im ≤
        |(R.vertex (C.topVertex e)).im| := le_abs_self _
    have htop : |(R.vertex (C.topVertex e)).im -
        (R.vertex C.originVertex).im| = |(R.vertex (C.topVertex e)).im| := by
      simp [R.origin_eq_zero]
    rw [htop]
    nlinarith
  have hidentx : w.re = ((n : Real) * code.rationalSeparator + (m : Real)) *
      X.secondPeriod.re + (n : Real) *
        (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) := by
    rw [hwre]
    ring
  have hidenty : w.im = ((n : Real) * code.rationalSeparator + (m : Real)) *
      X.secondPeriod.im - (n : Real) *
        (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) := by
    rw [hwim]
    ring
  have hLx_left := hX.first_index_bounds.1
    (C.leftVertex e) C.originVertex
  have hLx_right := hX.first_index_bounds.1
    (C.rightVertex e) C.originVertex
  have hLy_bottom := hX.first_index_bounds.2
    (C.bottomVertex e) C.originVertex
  have hLy_top := hX.first_index_bounds.2
    (C.topVertex e) C.originVertex
  have hqvx := hX.separated_periods.1
  have hqvy := hX.separated_periods.2.1
  have hax := hX.separated_periods.2.2.1
  have hay := hX.separated_periods.2.2.2
  have hn_upper : (n : Real) < (code.firstIndexBound : Real) := by
    by_contra hn
    have hnge : (code.firstIndexBound : Real) ≤ (n : Real) := le_of_not_gt hn
    by_cases hh : 0 ≤ (n : Real) * code.rationalSeparator + (m : Real)
    · have hna : (code.firstIndexBound : Real) *
          (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) ≤
          (n : Real) *
          (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) :=
        mul_le_mul_of_nonneg_right hnge (le_of_lt hax)
      have hhv : 0 ≤ ((n : Real) * code.rationalSeparator + (m : Real)) *
          X.secondPeriod.re := mul_nonneg hh (le_of_lt hqvx)
      linarith [hLx_left, hwx_upper, hidentx, hna, hhv]
    · have hh' : (n : Real) * code.rationalSeparator + (m : Real) ≤ 0 :=
        (lt_of_not_ge hh).le
      have hnb : (code.firstIndexBound : Real) *
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) ≤
          (n : Real) *
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) :=
        mul_le_mul_of_nonneg_right hnge (le_of_lt hay)
      have hhv : ((n : Real) * code.rationalSeparator + (m : Real)) *
          X.secondPeriod.im ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh'
          (le_of_lt hqvy)
      linarith [hLy_top, hwy_lower, hidenty, hnb, hhv]
  have hn_lower : -(code.firstIndexBound : Real) < (n : Real) := by
    by_contra hn
    have hnle : (n : Real) ≤ -(code.firstIndexBound : Real) := le_of_not_gt hn
    by_cases hh : 0 ≤ (n : Real) * code.rationalSeparator + (m : Real)
    · have hnb : (code.firstIndexBound : Real) *
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) ≤
          -(n : Real) *
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hay)
        linarith
      have hhv : 0 ≤ ((n : Real) * code.rationalSeparator + (m : Real)) *
          X.secondPeriod.im := mul_nonneg hh (le_of_lt hqvy)
      linarith [hLy_bottom, hwy_upper, hidenty, hnb, hhv]
    · have hh' : (n : Real) * code.rationalSeparator + (m : Real) ≤ 0 :=
        (lt_of_not_ge hh).le
      have hna : (code.firstIndexBound : Real) *
          (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) ≤
          -(n : Real) *
          (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hax)
        linarith
      have hhv : ((n : Real) * code.rationalSeparator + (m : Real)) *
          X.secondPeriod.re ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hh'
          (le_of_lt hqvx)
      linarith [hLx_right, hwx_lower, hidentx, hna, hhv]
  have hn_upper_int : n < (code.firstIndexBound : Int) := by
    exact_mod_cast hn_upper
  have hn_lower_int : -(code.firstIndexBound : Int) < n := by
    exact_mod_cast hn_lower
  have hn_nat : n.natAbs < code.firstIndexBound := by
    omega
  have hLpos : 0 < (code.firstIndexBound : Real) := by
    have hM : 0 < 2 * X.horizontalBound +
        |(R.vertex (C.leftVertex e)).re - (R.vertex C.originVertex).re| := by
      nlinarith [hX.checking_bounds_pos.1,
        abs_nonneg ((R.vertex (C.leftVertex e)).re - (R.vertex C.originVertex).re)]
    by_contra hL
    have hL' : (code.firstIndexBound : Real) ≤ 0 := le_of_not_gt hL
    have hp' : (code.firstIndexBound : Real) *
        (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hL' (le_of_lt hax)
    nlinarith [hLx_left, hM, hp']
  have hnabs : |(n : Real)| ≤ (code.firstIndexBound : Real) := by
    apply abs_le.mpr
    exact ⟨hn_lower.le, hn_upper.le⟩
  have huxabs : |X.firstPeriod.re| ≤ X.firstPeriodAbsoluteXBound := by
    apply abs_le.mpr
    have hlow := neg_le_neg hX.first_period_x_bound.2.2
    exact ⟨by simpa using hlow, hX.first_period_x_bound.2.1⟩
  have hnuabs : |(n : Real) * X.firstPeriod.re| ≤
      (code.firstIndexBound : Real) * X.firstPeriodAbsoluteXBound := by
    rw [abs_mul]
    calc
      |(n : Real)| * |X.firstPeriod.re| ≤
          (code.firstIndexBound : Real) * |X.firstPeriod.re| :=
        mul_le_mul_of_nonneg_right hnabs (abs_nonneg _)
      _ ≤ (code.firstIndexBound : Real) * X.firstPeriodAbsoluteXBound :=
        mul_le_mul_of_nonneg_left huxabs hLpos.le
  have hmv_upper : (m : Real) * X.secondPeriod.re <
      (code.secondIndexBound : Real) * X.secondPeriod.re := by
    have hsecond := hX.second_index_bound
      (C.leftVertex e) C.originVertex
    have hmvre : (m : Real) * X.secondPeriod.re =
        w.re - (n : Real) * X.firstPeriod.re := by
      rw [hwre]
      ring
    rw [hmvre]
    have hle : w.re - (n : Real) * X.firstPeriod.re ≤
        w.re + |(n : Real) * X.firstPeriod.re| := by
      linarith [neg_le_abs ((n : Real) * X.firstPeriod.re)]
    linarith [hsecond, hnuabs, hwx_upper, hle]
  have hmv_lower : -(code.secondIndexBound : Real) * X.secondPeriod.re <
      (m : Real) * X.secondPeriod.re := by
    have hsecond := hX.second_index_bound
      (C.rightVertex e) C.originVertex
    have hmvre : (m : Real) * X.secondPeriod.re =
        w.re - (n : Real) * X.firstPeriod.re := by
      rw [hwre]
      ring
    rw [hmvre]
    have hle : -|(n : Real) * X.firstPeriod.re| ≤
        -(n : Real) * X.firstPeriod.re := by
      have htmp : (n : Real) * X.firstPeriod.re ≤
          |(n : Real) * X.firstPeriod.re| := le_abs_self _
      simpa [neg_mul] using (neg_le_neg htmp)
    linarith [hsecond, hnuabs, hwx_lower, hle]
  have hm_upper : (m : Real) < (code.secondIndexBound : Real) := by
    exact lt_of_mul_lt_mul_right hmv_upper hqvx.le
  have hm_lower : -(code.secondIndexBound : Real) < (m : Real) := by
    exact lt_of_mul_lt_mul_right hmv_lower hqvx.le
  have hm_upper_int : m < (code.secondIndexBound : Int) := by
    exact_mod_cast hm_upper
  have hm_lower_int : -(code.secondIndexBound : Int) < m := by
    exact_mod_cast hm_lower
  have hm_nat : m.natAbs < code.secondIndexBound := by
    omega
  exact ⟨hn_nat, hm_nat⟩

private theorem real_two_period_combo_le {s t u v H : Real}
    (hH : 0 ≤ H) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu : u ≤ H) (hv : v ≤ H) (huv : u + v ≤ H) :
    s * u + t * v ≤ H := by
  by_cases hst : s + t ≤ 1
  · have hsu := mul_le_mul_of_nonneg_left hu hs0
    have htv := mul_le_mul_of_nonneg_left hv ht0
    have hsum : (s + t) * H ≤ H := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hst hH
    nlinarith
  · have hst' : 0 ≤ s + t - 1 := by linarith
    have h1 := mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr ht1)
    have h2 := mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr hs1)
    have h3 := mul_le_mul_of_nonneg_left huv hst'
    nlinarith

private theorem lattice_parallelogram_subset_closedBox_local : ∀ {C} (R : Realization C)
    (code : RawLatticeCode) (X : LatticeRawParameters code),
    LatticeChecks R code X →
      latticeFundamentalParallelogram code X ⊆ latticeClosedCheckingBox code X := by
  intro C R code X hX p hp
  rcases hp with ⟨s, t, hs0, hs1, ht0, ht1, rfl⟩
  have hm1 : (1 : Int) ∈ ([-1, 1] : List Int) := by norm_num
  have hmm1 : (-1 : Int) ∈ ([-1, 1] : List Int) := by norm_num
  have hux : X.firstPeriod.re ≤ X.horizontalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 1 hm1).1
    have hm := (hX.period_signed_bounds 1 hm1 (-1) hmm1).1
    norm_num at hp hm ⊢
    by_cases hv : 0 ≤ X.secondPeriod.re <;> linarith
  have hvx : X.secondPeriod.re ≤ X.horizontalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 1 hm1).1
    have hm := (hX.period_signed_bounds (-1) hmm1 1 hm1).1
    norm_num at hp hm ⊢
    by_cases hu : 0 ≤ X.firstPeriod.re <;> linarith
  have huvx : X.firstPeriod.re + X.secondPeriod.re ≤ X.horizontalBound := by
    have h := (hX.period_signed_bounds 1 hm1 1 hm1).1
    norm_num at h ⊢
    exact h
  have hnux : -X.firstPeriod.re ≤ X.horizontalBound := by
    have hp := (hX.period_signed_bounds (-1) hmm1 1 hm1).1
    have hm := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).1
    norm_num at hp hm ⊢
    by_cases hv : 0 ≤ X.secondPeriod.re <;> linarith
  have hnvx : -X.secondPeriod.re ≤ X.horizontalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 (-1) hmm1).1
    have hm := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).1
    norm_num at hp hm ⊢
    by_cases hu : 0 ≤ X.firstPeriod.re <;> linarith
  have hnuvx : -X.firstPeriod.re - X.secondPeriod.re ≤ X.horizontalBound := by
    have h := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).1
    norm_num at h ⊢
    exact h
  have hyu : X.firstPeriod.im ≤ X.verticalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 1 hm1).2
    have hm := (hX.period_signed_bounds 1 hm1 (-1) hmm1).2
    norm_num at hp hm ⊢
    by_cases hv : 0 ≤ X.secondPeriod.im <;> linarith
  have hyv : X.secondPeriod.im ≤ X.verticalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 1 hm1).2
    have hm := (hX.period_signed_bounds (-1) hmm1 1 hm1).2
    norm_num at hp hm ⊢
    by_cases hu : 0 ≤ X.firstPeriod.im <;> linarith
  have hyuv : X.firstPeriod.im + X.secondPeriod.im ≤ X.verticalBound := by
    have h := (hX.period_signed_bounds 1 hm1 1 hm1).2
    norm_num at h ⊢
    exact h
  have hnyu : -X.firstPeriod.im ≤ X.verticalBound := by
    have hp := (hX.period_signed_bounds (-1) hmm1 1 hm1).2
    have hm := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).2
    norm_num at hp hm ⊢
    by_cases hv : 0 ≤ X.secondPeriod.im <;> linarith
  have hnyv : -X.secondPeriod.im ≤ X.verticalBound := by
    have hp := (hX.period_signed_bounds 1 hm1 (-1) hmm1).2
    have hm := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).2
    norm_num at hp hm ⊢
    by_cases hu : 0 ≤ X.firstPeriod.im <;> linarith
  have hnyuv : -X.firstPeriod.im - X.secondPeriod.im ≤ X.verticalBound := by
    have h := (hX.period_signed_bounds (-1) hmm1 (-1) hmm1).2
    norm_num at h ⊢
    exact h
  have hx := real_two_period_combo_le (le_of_lt hX.checking_bounds_pos.1)
    hs0 hs1.le ht0 ht1.le hux hvx huvx
  have hnx := real_two_period_combo_le (le_of_lt hX.checking_bounds_pos.1)
    hs0 hs1.le ht0 ht1.le hnux hnvx hnuvx
  have hy := real_two_period_combo_le (le_of_lt hX.checking_bounds_pos.2)
    hs0 hs1.le ht0 ht1.le hyu hyv hyuv
  have hny := real_two_period_combo_le (le_of_lt hX.checking_bounds_pos.2)
    hs0 hs1.le ht0 ht1.le hnyu hnyv hnyuv
  have hre : (s • X.firstPeriod + t • X.secondPeriod).re =
      s * X.firstPeriod.re + t * X.secondPeriod.re := by simp [Complex.add_re]
  have him : (s • X.firstPeriod + t • X.secondPeriod).im =
      s * X.firstPeriod.im + t * X.secondPeriod.im := by simp [Complex.add_im]
  change |(s • X.firstPeriod + t • X.secondPeriod).re| ≤ X.horizontalBound ∧
    |(s • X.firstPeriod + t • X.secondPeriod).im| ≤ X.verticalBound
  rw [hre, him]
  constructor <;> apply abs_le.mpr
  · exact ⟨by linarith [hnx], hx⟩
  · exact ⟨by linarith [hny], hy⟩



private theorem rectangle_boundary_null_local (left right bottom top : Real) :
    MeasureTheory.volume
      ({p : Tiling.Plane | left ≤ p.re ∧ p.re ≤ right ∧ bottom ≤ p.im ∧ p.im ≤ top} \
        {p : Tiling.Plane | left < p.re ∧ p.re < right ∧ bottom < p.im ∧ p.im < top}) = 0 := by
  refine MeasureTheory.measure_mono_null (s :=
      ({p : Tiling.Plane | left ≤ p.re ∧ p.re ≤ right ∧ bottom ≤ p.im ∧ p.im ≤ top} \
        {p : Tiling.Plane | left < p.re ∧ p.re < right ∧ bottom < p.im ∧ p.im < top}))
    (t := ({p : Tiling.Plane | p.re = left} ∪ {p : Tiling.Plane | p.re = right} ∪
      {p : Tiling.Plane | p.im = bottom} ∪ {p : Tiling.Plane | p.im = top})) ?_ ?_
  · intro p hp
    rcases hp with ⟨hclosed, hopen⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq]
    by_contra hboundary
    have hleft : p.re ≠ left := by intro h; exact hboundary (Or.inl (Or.inl (Or.inl h)))
    have hright : p.re ≠ right := by intro h; exact hboundary (Or.inl (Or.inl (Or.inr h)))
    have hbottom : p.im ≠ bottom := by intro h; exact hboundary (Or.inl (Or.inr h))
    have htop : p.im ≠ top := by intro h; exact hboundary (Or.inr h)
    rcases hclosed with ⟨hl, hr, hb, ht⟩
    exact hopen ⟨lt_of_le_of_ne hl (Ne.symm hleft), lt_of_le_of_ne hr hright,
      lt_of_le_of_ne hb (Ne.symm hbottom), lt_of_le_of_ne ht htop⟩
  · apply MeasureTheory.measure_union_null
    · apply MeasureTheory.measure_union_null
      · apply MeasureTheory.measure_union_null
        · exact volume_re_eq_zero_local _
        · exact volume_re_eq_zero_local _
      · exact volume_im_eq_zero_local _
    · exact volume_im_eq_zero_local _

private theorem lattice_parallelogram_translates_cover : ∀ {C} (R : Realization C)
    (code : RawLatticeCode) (X : LatticeRawParameters code),
    LatticeChecks R code X →
    Set.univ ⊆ ⋃ n : Int, ⋃ m : Int,
      (n • X.firstPeriod + m • X.secondPeriod) +ᵥ
        latticeFundamentalParallelogram code X := by
  intro C R code X hX p hp
  rcases hX.separated_periods with ⟨hvx, hvy, hux, huy⟩
  let det : Real := X.firstPeriod.re * X.secondPeriod.im -
    X.firstPeriod.im * X.secondPeriod.re
  have hdet_eq : det =
      (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) *
          X.secondPeriod.im +
        (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) *
          X.secondPeriod.re := by
    dsimp [det]
    ring
  have hdet : 0 < det := by
    rw [hdet_eq]
    positivity
  let s : Real := (p.re * X.secondPeriod.im - p.im * X.secondPeriod.re) / det
  let t : Real := (X.firstPeriod.re * p.im - X.firstPeriod.im * p.re) / det
  have hp_decomp : p = s • X.firstPeriod + t • X.secondPeriod := by
    apply Complex.ext
    · dsimp [s, t]
      field_simp [hdet.ne']
      norm_num [Complex.mul_re, Complex.mul_im]
      field_simp [hdet.ne']
      ring
    · dsimp [s, t]
      field_simp [hdet.ne']
      norm_num [Complex.mul_re, Complex.mul_im]
      field_simp [hdet.ne']
      ring
  let n : Int := Int.floor s
  let m : Int := Int.floor t
  let s₀ : Real := s - n
  let t₀ : Real := t - m
  have hs₀ : 0 ≤ s₀ := by
    dsimp [s₀]
    have h := Int.floor_le s
    linarith
  have hs₁ : s₀ < 1 := by
    dsimp [s₀]
    have h := Int.lt_floor_add_one s
    linarith
  have ht₀ : 0 ≤ t₀ := by
    dsimp [t₀]
    have h := Int.floor_le t
    linarith
  have ht₁ : t₀ < 1 := by
    dsimp [t₀]
    have h := Int.lt_floor_add_one t
    linarith
  let z : Tiling.Plane := s₀ • X.firstPeriod + t₀ • X.secondPeriod
  have hz : z ∈ latticeFundamentalParallelogram code X := by
    refine ⟨s₀, t₀, hs₀, hs₁, ht₀, ht₁, ?_⟩
    rfl
  refine Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨m, ?_⟩⟩
  refine ⟨z, hz, ?_⟩
  change (n • X.firstPeriod + m • X.secondPeriod) +ᵥ z = p
  rw [vadd_eq_add]
  change (n • X.firstPeriod + m • X.secondPeriod) +
      (s₀ • X.firstPeriod + t₀ • X.secondPeriod) = p
  rw [hp_decomp]
  dsimp [s₀, t₀]
  rw [← Int.cast_smul_eq_zsmul Real n X.firstPeriod,
    ← Int.cast_smul_eq_zsmul Real m X.secondPeriod]
  change (((n : Real) • X.firstPeriod + (m : Real) • X.secondPeriod) +
      ((s - (n : Real)) • X.firstPeriod + (t - (m : Real)) • X.secondPeriod)) =
    s • X.firstPeriod + t • X.secondPeriod
  module

end Tiling.AxisParallel.Terminal.Executable.PositiveVerification


namespace Tiling.AxisParallel.Terminal.Executable.PositiveVerification


private theorem lattice_parallelogram_outside_openBox_null_local : ∀ {C}
    (R : Realization C) code X, LatticeChecks R code X →
    MeasureTheory.volume (latticeFundamentalParallelogram code X \
      latticeOpenCheckingBox code X) = 0 := by
  intro C R code X hX
  apply MeasureTheory.measure_mono_null ?_
    (rectangle_boundary_null_local (-X.horizontalBound) X.horizontalBound
      (-X.verticalBound) X.verticalBound)
  intro p hp
  constructor
  · have hclosed := lattice_parallelogram_subset_closedBox_local R code X hX hp.1
    change |p.re| ≤ X.horizontalBound ∧ |p.im| ≤ X.verticalBound at hclosed
    exact ⟨(abs_le.mp hclosed.1).1, (abs_le.mp hclosed.1).2,
      (abs_le.mp hclosed.2).1, (abs_le.mp hclosed.2).2⟩
  · exact hp.2

private theorem exists_lattice_translate_box_intersection : ∀ {C}
    (R : Realization C) code X, LatticeChecks R code X →
    ∀ S : Set Tiling.Plane, MeasureTheory.volume S ≠ 0 →
    ∃ a b : Int,
      MeasureTheory.volume
        (S ∩ ((a • X.firstPeriod + b • X.secondPeriod) +ᵥ
          latticeOpenCheckingBox code X)) ≠ 0 := by
  intro C R code X hX S hS
  let P := latticeFundamentalParallelogram code X
  let B := latticeOpenCheckingBox code X
  let shifts : Set Tiling.Plane := ⋃ a : Int, ⋃ b : Int,
    (a • X.firstPeriod + b • X.secondPeriod) +ᵥ B
  have hcover : Set.univ ⊆ ⋃ a : Int, ⋃ b : Int,
      (a • X.firstPeriod + b • X.secondPeriod) +ᵥ P :=
    lattice_parallelogram_translates_cover R code X hX
  have hbad : MeasureTheory.volume (S \ shifts) = 0 := by
    have hnull : ∀ a b : Int, MeasureTheory.volume
        (((a • X.firstPeriod + b • X.secondPeriod) +ᵥ P) \
          ((a • X.firstPeriod + b • X.secondPeriod) +ᵥ B)) = 0 := by
      intro a b
      let d : Tiling.Plane := a • X.firstPeriod + b • X.secondPeriod
      have hnull' := lattice_parallelogram_outside_openBox_null_local R code X hX
      apply MeasureTheory.measure_mono_null ?_
        (by
          have hzero : MeasureTheory.volume (d +ᵥ (P \ B)) = 0 := by
            rw [MeasureTheory.measure_vadd]
            exact hnull'
          exact hzero)
      intro p hp
      rcases Set.mem_vadd_set.mp hp.1 with ⟨z, hz, hpz⟩
      refine ⟨z, ?_, ?_⟩
      · refine ⟨hz, ?_⟩
        intro hzB
        apply hp.2
        apply Set.mem_vadd_set.mpr
        exact ⟨z, hzB, by simpa [d] using hpz⟩
      · simpa [d] using hpz
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_iUnion_null (fun a : Int =>
        MeasureTheory.measure_iUnion_null (hnull a)))
    · intro p hp
      rcases Set.mem_iUnion.mp (hcover (Set.mem_univ p)) with ⟨a, ha⟩
      rcases Set.mem_iUnion.mp ha with ⟨b, hb⟩
      refine Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ⟨hb, ?_⟩⟩⟩
      intro hpbox
      exact hp.2 (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, hpbox⟩⟩)
  have hgood : MeasureTheory.volume (S ∩ shifts) ≠ 0 := by
    by_contra hz
    apply hS
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hbad hz)
    intro p hp
    by_cases hps : p ∈ shifts
    · exact Or.inr ⟨hp, hps⟩
    · exact Or.inl ⟨hp, hps⟩
  by_contra hz
  push Not at hz
  apply hgood
  apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_iUnion_null (fun a : Int =>
      MeasureTheory.measure_iUnion_null (fun b : Int => hz a b)))
  intro p hp
  rcases Set.mem_iUnion.mp hp.2 with ⟨a, ha⟩
  rcases Set.mem_iUnion.mp ha with ⟨b, hb⟩
  exact Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨b, ⟨hp.1, hb⟩⟩⟩

private theorem vadd_inter_translate (d : Tiling.Plane) (A B : Set Tiling.Plane) :
    (-d) +ᵥ (A ∩ (d +ᵥ B)) = ((-d) +ᵥ A) ∩ B := by
  ext p
  constructor
  · rintro ⟨z, hz, hpz⟩
    rcases hz with ⟨hzA, hzB⟩
    rcases Set.mem_vadd_set.mp hzB with ⟨y, hyB, hzy⟩
    have hpy : p = y := by
      change -d + z = p at hpz
      change d + y = z at hzy
      rw [← hpz, ← hzy]
      module
    exact ⟨⟨z, hzA, hpz⟩, by rw [hpy]; exact hyB⟩
  · rintro ⟨hpA, hpB⟩
    rcases Set.mem_vadd_set.mp hpA with ⟨z, hzA, hpz⟩
    have hzp : z = d + p := by
      change -d + z = p at hpz
      rw [← hpz]
      module
    refine Set.mem_vadd_set.mpr ⟨z, ⟨hzA, ?_⟩, hpz⟩
    exact Set.mem_vadd_set.mpr ⟨p, hpB, hzp.symm⟩

private theorem vadd_inter (d : Tiling.Plane) (A B : Set Tiling.Plane) :
    d +ᵥ (A ∩ B) = (d +ᵥ A) ∩ (d +ᵥ B) := by
  ext p
  constructor
  · rintro ⟨z, ⟨hzA, hzB⟩, hpz⟩
    exact ⟨⟨z, hzA, hpz⟩, ⟨z, hzB, hpz⟩⟩
  · rintro ⟨⟨z, hzA, hpz⟩, ⟨z', hzB, hpz'⟩⟩
    have hzz' : z = z' := by
      change d +ᵥ z = p at hpz
      change d +ᵥ z' = p at hpz'
      exact add_left_cancel (a := d) (hpz.trans hpz'.symm)
    subst z'
    exact ⟨z, ⟨hzA, hzB⟩, hpz⟩

private theorem lattice_overlap_reduction : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X → ∀ r r' n n' m m',
    MeasureTheory.volume
      (((latticeSemanticCentre code X r n m) +ᵥ R.region.openCarrier) ∩
        ((latticeSemanticCentre code X r' n' m') +ᵥ R.region.openCarrier)) ≠ 0 →
    ∃ a b : Int,
      (n - a).natAbs < code.firstIndexBound ∧
      (n' - a).natAbs < code.firstIndexBound ∧
      (m - b).natAbs < code.secondIndexBound ∧
      (m' - b).natAbs < code.secondIndexBound := by
  intro C R code X hX r r' n n' m m' hvol
  let c := latticeSemanticCentre code X r n m
  let c' := latticeSemanticCentre code X r' n' m'
  let A := (c +ᵥ R.region.openCarrier) ∩ (c' +ᵥ R.region.openCarrier)
  have hA : MeasureTheory.volume A ≠ 0 := by simpa [A, c, c'] using hvol
  obtain ⟨a, b, hab⟩ := exists_lattice_translate_box_intersection R code X hX A hA
  let d : Tiling.Plane := a • X.firstPeriod + b • X.secondPeriod
  have hshift : MeasureTheory.volume (((-d) +ᵥ A) ∩ latticeOpenCheckingBox code X) ≠ 0 := by
    rw [← vadd_inter_translate d A]
    simpa [d] using hab
  let c₁ := latticeSemanticCentre code X r (n - a) (m - b)
  let c₂ := latticeSemanticCentre code X r' (n' - a) (m' - b)
  have hc₁ : -d + c = c₁ := by
    dsimp [d, c, c₁, latticeSemanticCentre]
    module
  have hc₂ : -d + c' = c₂ := by
    dsimp [d, c', c₂, latticeSemanticCentre]
    module
  have hsets : (-d) +ᵥ A = (c₁ +ᵥ R.region.openCarrier) ∩
      (c₂ +ᵥ R.region.openCarrier) := by
    dsimp [A]
    rw [vadd_inter, vadd_vadd, vadd_vadd, hc₁, hc₂]
  rw [hsets] at hshift
  have hshift1 : MeasureTheory.volume
      ((c₁ +ᵥ R.region.openCarrier) ∩ latticeOpenCheckingBox code X) ≠ 0 := by
    by_contra hz
    apply hshift
    apply MeasureTheory.measure_mono_null ?_ hz
    intro p hp
    exact ⟨hp.1.1, hp.2⟩
  have hshift2 : MeasureTheory.volume
      ((c₂ +ᵥ R.region.openCarrier) ∩ latticeOpenCheckingBox code X) ≠ 0 := by
    by_contra hz
    apply hshift
    apply MeasureTheory.measure_mono_null ?_ hz
    intro p hp
    exact ⟨hp.1.2, hp.2⟩
  have h1 := lattice_neighbour_bounds R code X hX r (n - a) (m - b) hshift1
  have h2 := lattice_neighbour_bounds R code X hX r' (n' - a) (m' - b) hshift2
  exact ⟨a, b, h1.1, h2.1, h1.2, h2.2⟩

private theorem mem_latticeFiniteIndices (code : RawLatticeCode)
    (i : LatticeFiniteIndex code)
    (hi : (centeredInteger i.2.1).natAbs < code.firstIndexBound ∧
      (centeredInteger i.2.2).natAbs < code.secondIndexBound) :
    i ∈ latticeFiniteIndices code := by
  rcases i with ⟨r, n, m⟩
  unfold latticeFiniteIndices
  apply List.mem_filter.mpr
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨n, List.mem_ofFn.mpr ⟨n, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨m, rfl⟩
  · simpa using hi

private theorem latticeFiniteIndex_complete : ∀ code r n m,
    n.natAbs < code.firstIndexBound → m.natAbs < code.secondIndexBound →
    ∃ i ∈ latticeFiniteIndices code,
      i.1 = r ∧ centeredInteger i.2.1 = n ∧ centeredInteger i.2.2 = m := by
  intro code r n m hn hm
  obtain ⟨nidx, hnidx⟩ :=
    centeredInteger_closed_complete code.firstIndexBound n (by omega)
  obtain ⟨midx, hmid⟩ :=
    centeredInteger_closed_complete code.secondIndexBound m (by omega)
  let i : LatticeFiniteIndex code := (r, nidx, midx)
  refine ⟨i, ?_, rfl, hnidx, hmid⟩
  simp only [latticeFiniteIndices, List.mem_filter]
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨nidx, List.mem_ofFn.mpr ⟨nidx, rfl⟩, ?_⟩
    exact List.mem_ofFn.mpr ⟨midx, rfl⟩
  · dsimp [i]
    simp [hnidx, hmid, hn, hm]

private theorem exists_common_semantic_open_cells_of_measure_ne_zero :
    ∀ {C} (R : Realization C) (c c' : Tiling.Plane),
    MeasureTheory.volume
      ((c +ᵥ R.region.openCarrier) ∩ (c' +ᵥ R.region.openCarrier)) ≠ 0 →
    ∃ p e e', p ∈ (c +ᵥ R.region.openCarrier) ∩
          (c' +ᵥ R.region.openCarrier) ∧
      semanticOpenCell R false e c p ∧ semanticOpenCell R false e' c' p := by
  intro C R c c' hA
  let O : Set Tiling.Plane := ⋃ e, {p | semanticOpenCell R false e 0 p}
  let U : Set Tiling.Plane := c +ᵥ O
  let U' : Set Tiling.Plane := c' +ᵥ O
  let K : Set Tiling.Plane := c +ᵥ R.region.openCarrier
  let K' : Set Tiling.Plane := c' +ᵥ R.region.openCarrier
  have hU : U =ᵐ[MeasureTheory.volume] K := by
    apply (MeasureTheory.vadd_set_ae_eq c).mpr
    exact selected_presentation_ae_false R
  have hU' : U' =ᵐ[MeasureTheory.volume] K' := by
    apply (MeasureTheory.vadd_set_ae_eq c').mpr
    exact selected_presentation_ae_false R
  obtain ⟨hUK, hKU⟩ := MeasureTheory.ae_eq_set.mp hU
  obtain ⟨hUK', hK'U'⟩ := MeasureTheory.ae_eq_set.mp hU'
  have hbad : MeasureTheory.volume ((K ∩ K') \ (U ∩ U')) = 0 := by
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hKU hK'U')
    rintro p ⟨⟨hpK, hpK'⟩, hpnot⟩
    by_cases hpU : p ∈ U
    · right
      exact ⟨hpK', fun hpU' => hpnot ⟨hpU, hpU'⟩⟩
    · left
      exact ⟨hpK, hpU⟩
  have hgood : MeasureTheory.volume ((K ∩ K') ∩ (U ∩ U')) ≠ 0 := by
    by_contra hz
    apply hA
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null hbad hz)
    intro p hp
    by_cases hpU : p ∈ U ∩ U'
    · exact Or.inr ⟨hp, hpU⟩
    · exact Or.inl ⟨hp, hpU⟩
  obtain ⟨p, hp⟩ := MeasureTheory.nonempty_of_measure_ne_zero hgood
  rcases hp with ⟨⟨hpK, hpK'⟩, ⟨hpU, hpU'⟩⟩
  rcases Set.mem_vadd_set.mp hpU with ⟨z, hz, hpz⟩
  rcases Set.mem_iUnion.mp hz with ⟨e, hze⟩
  rcases Set.mem_vadd_set.mp hpU' with ⟨z', hz', hpz'⟩
  rcases Set.mem_iUnion.mp hz' with ⟨e', hze'⟩
  refine ⟨p, e, e', ⟨hpK, hpK'⟩, ?_, ?_⟩
  · change p ∈ {p | semanticOpenCell R false e c p}
    rw [semanticOpenCell_vadd R e c]
    exact ⟨z, hze, hpz⟩
  · change p ∈ {p | semanticOpenCell R false e' c' p}
    rw [semanticOpenCell_vadd R e' c']
    exact ⟨z', hze', hpz'⟩

private theorem lattice_checks_global_packing : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X →
    Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
      (R.region.toPolygonalRegion.placements (latticeCentreSet code X)) := by
  intro C R code X hX
  unfold Tiling.IsPacking
  intro i hi j hj hij
  change i.1 ∈ latticeCentreSet code X at hi
  change j.1 ∈ latticeCentreSet code X at hj
  rcases hi with ⟨r, n, m, hci⟩
  rcases hj with ⟨r', n', m', hcj⟩
  change MeasureTheory.AEDisjoint MeasureTheory.volume
    (i.1 +ᵥ R.region.toPolygonalRegion.support)
    (j.1 +ᵥ R.region.toPolygonalRegion.support)
  rw [hci, hcj]
  have hcc' : latticeSemanticCentre code X r n m ≠
      latticeSemanticCentre code X r' n' m' := by
    intro heq
    apply hij
    cases i
    cases j
    simp_all
  have hdisj_open : Disjoint
      ((latticeSemanticCentre code X r n m) +ᵥ R.region.openCarrier)
      ((latticeSemanticCentre code X r' n' m') +ᵥ R.region.openCarrier) := by
    by_contra hnd
    obtain ⟨p, hp⟩ := Set.not_disjoint_iff.mp hnd
    have hvol : MeasureTheory.volume
        ((latticeSemanticCentre code X r n m +ᵥ R.region.openCarrier) ∩
          (latticeSemanticCentre code X r' n' m' +ᵥ R.region.openCarrier)) ≠ 0 := by
      have hopen : IsOpen (latticeSemanticCentre code X r n m +ᵥ R.region.openCarrier) := by
        exact isOpen_interior.vadd _
      have hopen' : IsOpen (latticeSemanticCentre code X r' n' m' +ᵥ R.region.openCarrier) := by
        exact isOpen_interior.vadd _
      exact (hopen.inter hopen').measure_ne_zero MeasureTheory.volume
        ⟨p, hp.1, hp.2⟩
    obtain ⟨a, b, ha, ha', hb, hb'⟩ :=
      lattice_overlap_reduction R code X hX r r' n n' m m' hvol
    obtain ⟨i₀, hi₀, hir, hin, him⟩ :=
      latticeFiniteIndex_complete code r (n - a) (m - b) ha hb
    obtain ⟨i₁, hi₁, hir', hin', him'⟩ :=
      latticeFiniteIndex_complete code r' (n' - a) (m' - b) ha' hb'
    let d : Tiling.Plane := a • X.firstPeriod + b • X.secondPeriod
    let c₀ := latticeSemanticCentre code X r n m
    let c₁ := latticeSemanticCentre code X r' n' m'
    let c₂ := latticeSemanticCentre code X r (n - a) (m - b)
    let c₃ := latticeSemanticCentre code X r' (n' - a) (m' - b)
    have hc₂ : -d + c₀ = c₂ := by
      dsimp [d, c₀, c₂, latticeSemanticCentre]
      module
    have hc₃ : -d + c₁ = c₃ := by
      dsimp [d, c₁, c₃, latticeSemanticCentre]
      module
    have hvolShift : MeasureTheory.volume
        ((c₂ +ᵥ R.region.openCarrier) ∩ (c₃ +ᵥ R.region.openCarrier)) ≠ 0 := by
      have hshift : MeasureTheory.volume
          ((-d) +ᵥ ((c₀ +ᵥ R.region.openCarrier) ∩
            (c₁ +ᵥ R.region.openCarrier))) ≠ 0 := by
        rw [MeasureTheory.measure_vadd]
        exact hvol
      rw [vadd_inter, vadd_vadd, vadd_vadd, hc₂, hc₃] at hshift
      exact hshift
    have hne : i₀ ≠ i₁ := by
      intro heq
      have hshiftEq : c₂ = c₃ := by
        simpa only [hir, hir', hin, hin', him, him'] using congrArg
          (fun k => latticeSemanticCentre code X k.1
            (centeredInteger k.2.1) (centeredInteger k.2.2)) heq
      have horigEq : c₀ = c₁ := by
        calc
          c₀ = d + c₂ := by
            dsimp [d, c₀, c₂, latticeSemanticCentre]
            module
          _ = d + c₃ := by rw [hshiftEq]
          _ = c₁ := by
            dsimp [d, c₁, c₃, latticeSemanticCentre]
            module
      apply hcc'
      exact horigEq
    rcases hX.finite_packing i₀ i₁ hi₀ hi₁ hne with heq | hnonoverlap
    · apply hcc'
      have hshiftEq : c₂ = c₃ := by
        simpa only [hir, hir', hin, hin', him, him'] using heq
      calc
        c₀ = d + c₂ := by
          dsimp [d, c₀, c₂, latticeSemanticCentre]
          module
        _ = d + c₃ := by rw [hshiftEq]
        _ = c₁ := by
          dsimp [d, c₁, c₃, latticeSemanticCentre]
          module
    · rcases exists_common_semantic_open_cells_of_measure_ne_zero R c₂ c₃ hvolShift with
        ⟨q, e, e', hq, hqe, hqe'⟩
      have hqe'' : semanticOpenCell R false e
          (latticeSemanticCentre code X i₀.1
            (centeredInteger i₀.2.1) (centeredInteger i₀.2.2)) q := by
        simpa only [hir, hin, him] using hqe
      have hqe''' : semanticOpenCell R false e'
          (latticeSemanticCentre code X i₁.1
            (centeredInteger i₁.2.1) (centeredInteger i₁.2.2)) q := by
        simpa only [hir', hin', him'] using hqe'
      have hn := hnonoverlap e e'
      simp only [semanticCellsNonoverlap, selectedCoordinate, selectedAxis, CoordSort.axis,
        Tiling.AxisParallel.Axis.coord] at hn
      have hqec := hqe''
      have hqec' := hqe'''
      simp only [semanticOpenCell, selectedCoordinate, selectedAxis, CoordSort.axis,
        Tiling.AxisParallel.Axis.coord] at hqec hqec'
      rcases hn with hn | hn | hn | hn <;> linarith
  exact hdisj_open.aedisjoint.congr
    ((MeasureTheory.vadd_set_ae_eq _).mpr
      R.region.toPolygonalRegion.openCarrier_ae_eq.symm)
    ((MeasureTheory.vadd_set_ae_eq _).mpr
      R.region.toPolygonalRegion.openCarrier_ae_eq.symm)



private theorem latticeCentreSet_add_period
    (code : RawLatticeCode) (X : LatticeRawParameters code)
    (v : Tiling.Plane) (n m : Int)
    (hv : v = n • X.firstPeriod + m • X.secondPeriod) :
    v +ᵥ latticeCentreSet code X ⊆ latticeCentreSet code X := by
  intro p hp
  rcases Set.mem_vadd_set.mp hp with ⟨q, hq, rfl⟩
  change ∃ r n' m', q = latticeSemanticCentre code X r n' m' at hq
  rcases hq with ⟨r, n', m', rfl⟩
  refine ⟨r, n + n', m + m', ?_⟩
  rw [hv, vadd_eq_add]
  simp only [latticeSemanticCentre]
  module

private theorem openUnion_period_iff {C : RegionCode}
    (R : Realization C) (code : RawLatticeCode) (X : LatticeRawParameters code)
    (v : Tiling.Plane) (n m : Int)
    (hv : v = n • X.firstPeriod + m • X.secondPeriod) (p : Tiling.Plane) :
    p ∈ Tiling.AxisParallel.openUnion R.region (latticeCentreSet code X) ↔
      v + p ∈ Tiling.AxisParallel.openUnion R.region (latticeCentreSet code X) := by
  constructor
  · intro hp
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hp ⊢
    obtain ⟨c, hc⟩ := hp
    let c' : (latticeCentreSet code X) :=
      ⟨v + c, latticeCentreSet_add_period code X v n m hv
        (a := v + (c : Tiling.Plane)) ⟨c, c.property, rfl⟩⟩
    refine ⟨c', ?_⟩
    rcases Set.mem_vadd_set.mp hc with ⟨z, hz, hzc⟩
    refine Set.mem_vadd_set.mpr ⟨z, hz, ?_⟩
    dsimp [c']
    rw [vadd_eq_add] at hzc
    rw [add_assoc, hzc]
  · intro hp
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hp ⊢
    obtain ⟨c, hc⟩ := hp
    let c' : (latticeCentreSet code X) :=
      ⟨-v + c, latticeCentreSet_add_period code X (-v) (-n) (-m) (by
        rw [hv]
        module) (a := -v + (c : Tiling.Plane)) ⟨c, c.property, rfl⟩⟩
    refine ⟨c', ?_⟩
    rcases Set.mem_vadd_set.mp hc with ⟨z, hz, hzc⟩
    refine Set.mem_vadd_set.mpr ⟨z, hz, ?_⟩
    dsimp [c']
    rw [vadd_eq_add] at hzc
    rw [add_assoc, hzc]
    abel

private theorem lattice_checks_global_coverage : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X → MeasureTheory.volume
      (Set.univ \ Tiling.AxisParallel.openUnion R.region (latticeCentreSet code X)) = 0 := by
  intro C R code X hX
  let P : Set Tiling.Plane := latticeFundamentalParallelogram code X
  let G : Set Tiling.Plane :=
    Tiling.AxisParallel.openUnion R.region (latticeCentreSet code X)
  let centres : Finset Tiling.Plane :=
    ((latticeFiniteIndices code).toFinset).image
      (fun i ↦ latticeSemanticCentre code X i.1
        (centeredInteger i.2.1) (centeredInteger i.2.2))
  have hcover : ∀ p ∈ latticeOpenCheckingBox code X,
      ∃ c ∈ centres, ∃ e, semanticClosedCell R false e c p := by
    intro p hp
    rcases hX.finite_coverage p hp with ⟨i, hi, e, he⟩
    refine ⟨latticeSemanticCentre code X i.1
      (centeredInteger i.2.1) (centeredInteger i.2.2), ?_, e, he⟩
    apply Finset.mem_image.mpr
    refine ⟨i, ?_, rfl⟩
    simpa using hi
  have hfinite : MeasureTheory.volume
      (latticeOpenCheckingBox code X \
        Tiling.AxisParallel.openUnion R.region (centres : Set Tiling.Plane)) = 0 :=
    finite_closed_cells_cover_open_cells_ae R centres (latticeOpenCheckingBox code X) hcover
  have hcentres :
      Tiling.AxisParallel.openUnion R.region (centres : Set Tiling.Plane) ⊆ G := by
    intro p hp
    change p ∈ Tiling.AxisParallel.openUnion R.region (centres : Set Tiling.Plane) at hp
    change p ∈ Tiling.AxisParallel.openUnion R.region (latticeCentreSet code X)
    rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hp ⊢
    obtain ⟨c, hc⟩ := hp
    obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp c.property
    refine ⟨⟨(c : Tiling.Plane), ?_⟩, ?_⟩
    · change ∃ r n m, (c : Tiling.Plane) = latticeSemanticCentre code X r n m
      exact ⟨i.1, centeredInteger i.2.1, centeredInteger i.2.2, hci.symm⟩
    · exact hc
  have hbox : MeasureTheory.volume
      (latticeOpenCheckingBox code X \ G) = 0 := by
    apply MeasureTheory.measure_mono_null ?_ hfinite
    intro p hp
    exact ⟨hp.1, fun hpG => hp.2 (hcentres hpG)⟩
  have houtside : MeasureTheory.volume (P \ latticeOpenCheckingBox code X) = 0 :=
    lattice_parallelogram_outside_openBox_null_local R code X hX
  have hP : MeasureTheory.volume (P \ G) = 0 := by
    apply MeasureTheory.measure_mono_null ?_
      (MeasureTheory.measure_union_null houtside hbox)
    intro p hp
    rcases hp with ⟨hpP, hpG⟩
    by_cases hpbox : p ∈ latticeOpenCheckingBox code X
    · exact Or.inr ⟨hpbox, hpG⟩
    · exact Or.inl ⟨hpP, hpbox⟩
  have hPae : P \ G =ᵐ[MeasureTheory.volume] (∅ : Set Tiling.Plane) := by
    filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hP] with p hp
    change (p ∈ P \ G) = (p ∈ (∅ : Set Tiling.Plane))
    simp only [Set.mem_empty_iff_false]
    exact propext ⟨fun h => (hp h).elim, fun h => h.elim⟩
  have htranslate : ∀ n m : Int,
      MeasureTheory.volume
        (((n • X.firstPeriod + m • X.secondPeriod) +ᵥ P) \ G) = 0 := by
    intro n m
    let v : Tiling.Plane := n • X.firstPeriod + m • X.secondPeriod
    have hzero : MeasureTheory.volume (v +ᵥ (P \ G)) = 0 := by
      apply MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr
      have hae := (MeasureTheory.vadd_set_ae_eq v).mpr hPae
      filter_upwards [hae] with p hp
      intro hmem
      have hempty : p ∈ v +ᵥ (∅ : Set Tiling.Plane) := hp.mp hmem
      simp at hempty
    apply MeasureTheory.measure_mono_null ?_ hzero
    intro p hp
    rcases Set.mem_vadd_set.mp hp.1 with ⟨q, hq, rfl⟩
    refine Set.mem_vadd_set.mpr ⟨q, ⟨hq, ?_⟩, rfl⟩
    intro hqG
    exact hp.2 ((openUnion_period_iff R code X v n m rfl q).mp hqG)
  have htranslates : MeasureTheory.volume
      (⋃ n : Int, ⋃ m : Int,
        ((n • X.firstPeriod + m • X.secondPeriod) +ᵥ P) \ G) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro n
    apply MeasureTheory.measure_iUnion_null
    intro m
    exact htranslate n m
  have hPcover : Set.univ ⊆ ⋃ n : Int, ⋃ m : Int,
      (n • X.firstPeriod + m • X.secondPeriod) +ᵥ P := by
    exact lattice_parallelogram_translates_cover R code X hX
  apply MeasureTheory.measure_mono_null ?_ htranslates
  intro p hp
  have hpcover := hPcover hp.1
  rw [Set.mem_iUnion] at hpcover
  obtain ⟨n, hn⟩ := hpcover
  rw [Set.mem_iUnion] at hn
  obtain ⟨m, hm⟩ := hn
  rw [Set.mem_iUnion]
  refine ⟨n, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨m, ?_⟩
  exact ⟨hm, hp.2⟩

theorem latticeChecks_sound : ∀ {C} (R : Realization C) code X,
    LatticeChecks R code X → realizationPlaneTileable R := by
  intro C R code X hX
  let f : (Fin code.representativeCount × Int × Int) → Tiling.Plane :=
    fun q => latticeSemanticCentre code X q.1 q.2.1 q.2.2
  have hcentre : latticeCentreSet code X = Set.range f := by
    ext p
    constructor
    · rintro ⟨r, n, m, rfl⟩
      exact ⟨(r, n, m), rfl⟩
    · rintro ⟨⟨r, n, m⟩, rfl⟩
      exact ⟨r, n, m, rfl⟩
  have hcount : (latticeCentreSet code X).Countable := by
    rw [hcentre]
    exact Set.countable_range f
  refine ⟨latticeCentreSet code X, ?_⟩
  refine ⟨hcount, lattice_checks_global_packing R code X hX, ?_⟩
  have hzero := lattice_checks_global_coverage R code X hX
  filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hzero] with p hp
  constructor
  · intro _
    by_contra hpG
    have hpnot : p ∉ Tiling.AxisParallel.openUnion R.region
        (latticeCentreSet code X) := by
      intro hpopen
      rw [Tiling.AxisParallel.openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hpopen
      obtain ⟨s, hs⟩ := hpopen
      exact hpG ⟨s, hs⟩
    exact hp ⟨Set.mem_univ p, hpnot⟩
  · intro _
    trivial


private def triangularPartitionFormula (C : RegionCode) (code : RawTriangularCode) :
    Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) :=
  let intervals := triangularIntervalIndices code
  Formula.forallHorizontal
    (Formula.implication
      (Formula.andList
        [.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
            (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
         .horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (triH C code 1 triangularBetaId)])
      (Formula.orList
        (intervals.map fun i =>
          (Formula.horizontalLe (triH C code 1 (triangularIntervalLeftId code i))
              (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
            (Formula.horizontalLe (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
              (triH C code 1 (triangularIntervalRightId code i))))))

private theorem formulaHolds_closeHorizontal : ∀ {C v} (R : Realization C) epsilon
    (h : Nat) (p : Formula C h v) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.closeHorizontal h p) Fin.elim0 y ↔
      ∃ x : Fin h → Real, formulaHoldsInOrientation R epsilon p x y := by
  intro C v R epsilon h
  induction h with
  | zero =>
      intro p y
      simp only [Formula.closeHorizontal]
      constructor
      · intro hp
        exact ⟨Fin.elim0, hp⟩
      · rintro ⟨x, hx⟩
        have hzero : x = (Fin.elim0 : Fin 0 → Real) := Subsingleton.elim _ _
        simpa only [hzero] using hx
  | succ h ih =>
      intro p y
      rw [Formula.closeHorizontal]
      rw [ih]
      simp only [formulaHoldsInOrientation]
      constructor
      · rintro ⟨x, t, ht⟩
        exact ⟨Fin.cons t x, ht⟩
      · rintro ⟨x, hx⟩
        let z : Fin (h + 1) → Real := Fin.cons (x 0) (fun i => x i.succ)
        have hz : z = x := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [z]
          · simp [z]
        exact ⟨fun i => x i.succ, x 0, by simpa [z, hz] using hx⟩

private theorem formulaHolds_closeVertical : ∀ {C} (R : Realization C) epsilon
    (v : Nat) (p : Formula C 0 v),
    formulaHoldsInOrientation R epsilon (Formula.closeVertical v p) Fin.elim0 Fin.elim0 ↔
      ∃ y : Fin v → Real, formulaHoldsInOrientation R epsilon p Fin.elim0 y := by
  intro C R epsilon v
  induction v with
  | zero =>
      intro p
      simp only [Formula.closeVertical]
      constructor
      · intro hp
        exact ⟨Fin.elim0, hp⟩
      · rintro ⟨y, hy⟩
        have hzero : y = (Fin.elim0 : Fin 0 → Real) := Subsingleton.elim _ _
        simpa only [hzero] using hy
  | succ v ih =>
      intro p
      rw [Formula.closeVertical]
      rw [ih]
      simp only [formulaHoldsInOrientation]
      constructor
      · rintro ⟨y, t, ht⟩
        exact ⟨Fin.cons t y, ht⟩
      · rintro ⟨y, hy⟩
        let z : Fin (v + 1) → Real := Fin.cons (y 0) (fun i => y i.succ)
        have hz : z = y := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · simp [z]
          · simp [z]
        exact ⟨fun i => y i.succ, y 0, by simpa [z, hz] using hy⟩

private theorem formulaHolds_andList : ∀ {C h v} (R : Realization C) epsilon
    (ps : List (Formula C h v)) (x : Fin h → Real) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.andList ps) x y ↔
      ∀ p ∈ ps, formulaHoldsInOrientation R epsilon p x y := by
  intro C h v R epsilon ps
  induction ps with
  | nil => simp [Formula.andList, formulaHoldsInOrientation]
  | cons p ps ih =>
      intro x y
      simp only [Formula.andList, formulaHoldsInOrientation, ih, List.mem_cons]
      constructor
      · rintro ⟨hp, hs⟩ q hq
        cases hq with
        | inl hq => simpa [hq] using hp
        | inr hq => exact hs q hq
      · intro hs
        exact ⟨hs p (by simp), fun q hq => hs q (by simp [hq])⟩

private theorem formulaHolds_orList : ∀ {C h v} (R : Realization C) epsilon
    (ps : List (Formula C h v)) (x : Fin h → Real) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.orList ps) x y ↔
      ∃ p ∈ ps, formulaHoldsInOrientation R epsilon p x y := by
  intro C h v R epsilon ps
  induction ps with
  | nil => simp [Formula.orList, formulaHoldsInOrientation]
  | cons p ps ih =>
      intro x y
      simp only [Formula.orList, formulaHoldsInOrientation, ih, List.mem_cons]
      constructor
      · intro hs
        cases hs with
        | inl hp => exact ⟨p, by simp, hp⟩
        | inr hs => rcases hs with ⟨q, hq, hqv⟩; exact ⟨q, by simp [hq], hqv⟩
      · rintro ⟨q, hq, hqv⟩
        cases hq with
        | inl hq => exact Or.inl (by simpa [hq] using hqv)
        | inr hq => exact Or.inr ⟨q, hq, hqv⟩

private theorem formulaHolds_forallHorizontal : ∀ {C v} (R : Realization C) epsilon
    (p : Formula C 1 v) (x : Fin 0 → Real) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.forallHorizontal p) x y ↔
      ∀ t : Real, formulaHoldsInOrientation R epsilon p (Fin.cons t x) y := by
  intro C v R epsilon p x y
  simp [Formula.forallHorizontal, formulaHoldsInOrientation]

private theorem formulaHolds_forallVertical : ∀ {C} (R : Realization C) epsilon
    (p : Formula C 0 1) (x : Fin 0 → Real) (y : Fin 0 → Real),
    formulaHoldsInOrientation R epsilon (Formula.forallVertical p) x y ↔
      ∀ t : Real, formulaHoldsInOrientation R epsilon p x (Fin.cons t y) := by
  intro C R epsilon p x y
  simp [Formula.forallVertical, formulaHoldsInOrientation]

private theorem formulaHolds_false : ∀ {C h v} (R : Realization C)
    (f : Formula C h v) (x : Fin h → Real) (y : Fin v → Real),
    Formula.Holds R f x y ↔ formulaHoldsInOrientation R false f x y := by
  intro C h v R f
  induction f with
  | truth => intro x y; rfl
  | falsity => intro x y; rfl
  | horizontalLe A B => intro x y; rfl
  | horizontalLt A B => intro x y; rfl
  | verticalLe A B => intro x y; rfl
  | verticalLt A B => intro x y; rfl
  | conjunction p q ihp ihq =>
      intro x y
      simp only [Formula.Holds, formulaHoldsInOrientation, ihp, ihq]
  | disjunction p q ihp ihq =>
      intro x y
      simp only [Formula.Holds, formulaHoldsInOrientation, ihp, ihq]
  | negation p ih =>
      intro x y
      simp only [Formula.Holds, formulaHoldsInOrientation, ih]
  | existsHorizontal p ih =>
      intro x y
      simp only [Formula.Holds, formulaHoldsInOrientation]
      exact exists_congr fun t => ih (Fin.cons t x) y
  | existsVertical p ih =>
      intro x y
      simp only [Formula.Holds, formulaHoldsInOrientation]
      exact exists_congr fun t => ih x (Fin.cons t y)

private theorem evalAffineInOrientation_zero {C n} (R : Realization C) epsilon
    (s : CoordSort) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.zero C n) x = 0 := by
  simp [evalAffineInOrientation, Expr.zero, Coeff.zero]

private theorem evalAffineInOrientation_input {C n} (R : Realization C) epsilon
    (s : CoordSort) (a : Coeff C) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.input n a) x =
      ∑ i, (a i : Real) * (selectedAxis epsilon s).coord (R.vertex i) := by
  simp [evalAffineInOrientation, Expr.input]

private theorem evalAffineInOrientation_input_single_sub {C n} (R : Realization C)
    epsilon (s : CoordSort) (a b : Fin C.vertexCount) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s
        (Expr.input n (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) x =
      (selectedAxis epsilon s).coord (R.vertex a) -
        (selectedAxis epsilon s).coord (R.vertex b) := by
  rw [evalAffineInOrientation_input]
  classical
  have hsum (c : Fin C.vertexCount) :
      (∑ i : Fin C.vertexCount,
        (if i = c then (1 : Real) else 0) *
          (selectedAxis epsilon s).coord (R.vertex i)) =
        (selectedAxis epsilon s).coord (R.vertex c) := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro d hd hne
      simp [hne]
    · simp
  simp only [Coeff.sub, Coeff.single]
  norm_num
  calc
    (∑ i : Fin C.vertexCount,
        ((if i = a then (1 : Real) else 0) -
          (if i = b then (1 : Real) else 0)) *
            (selectedAxis epsilon s).coord (R.vertex i)) =
      (∑ i : Fin C.vertexCount,
        (if i = a then (1 : Real) else 0) *
          (selectedAxis epsilon s).coord (R.vertex i)) -
      (∑ i : Fin C.vertexCount,
        (if i = b then (1 : Real) else 0) *
          (selectedAxis epsilon s).coord (R.vertex i)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring_nf
    _ = (selectedAxis epsilon s).coord (R.vertex a) -
          (selectedAxis epsilon s).coord (R.vertex b) := by
      rw [hsum a, hsum b]

private theorem evalAffineInOrientation_neg {C n} (R : Realization C) epsilon
    (s : CoordSort) (A : AffineExpr C n) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.neg A) x =
      -evalAffineInOrientation R epsilon s A x := by
  simp [evalAffineInOrientation, Expr.neg, Coeff.neg]
  ring_nf

private theorem evalAffineInOrientation_scale_int {C n} (R : Realization C) epsilon
    (s : CoordSort) (q : Int) (A : AffineExpr C n) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.scale q A) x =
      (q : Real) * evalAffineInOrientation R epsilon s A x := by
  simp only [evalAffineInOrientation, Expr.scale]
  norm_num
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  ring_nf

private theorem evalAffineInOrientation_add {C n} (R : Realization C) epsilon
    (s : CoordSort) (A B : AffineExpr C n) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.add A B) x =
      evalAffineInOrientation R epsilon s A x +
        evalAffineInOrientation R epsilon s B x := by
  simp only [evalAffineInOrientation, Expr.add, Coeff.add]
  norm_num
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring_nf

/- private theorem eval_triangularCentreX {C} (R : Realization C) (epsilon : Bool)
    (code : RawTriangularCode) (x : Fin (triangularHorizontalVariableCount code) → Real)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j)
    (hrep : triangularRepresentativeXId code ⟨j, i.1⟩ <
      triangularHorizontalVariableCount code) (hβ : triangularBetaId <
      triangularHorizontalVariableCount code) :
    evalAffineInOrientation R epsilon .horizontal
        (triangularCentreX C code 0 j i) x =
      x ⟨triangularRepresentativeXId code ⟨j, i.1⟩, hrep⟩ +
        (centeredInteger i.2.1 : Real) * x ⟨triangularBetaId, hβ⟩ := by
  unfold triangularCentreX
  rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int]
  change
    evalAffineInOrientation R epsilon .horizontal
        (Expr.var C (triangularHorizontalVariableCount code)
          (triangularRepresentativeXId code ⟨j, i.1⟩)) x +
      (centeredInteger i.2.1 : Real) *
        evalAffineInOrientation R epsilon .horizontal
          (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId) x = _
  rw [evalAffineInOrientation_var R epsilon .horizontal x
        (triangularRepresentativeXId code ⟨j, i.1⟩) hrep,
      evalAffineInOrientation_var R epsilon .horizontal x triangularBetaId hβ]

private theorem eval_triangularCentreY {C} (R : Realization C) (epsilon : Bool)
    (code : RawTriangularCode) (y : Fin (triangularVerticalVariableCount code) → Real)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j)
    (hrep : triangularRepresentativeYId code ⟨j, i.1⟩ <
      triangularVerticalVariableCount code) (hs : triangularShearId j.val <
      triangularVerticalVariableCount code) (hα : triangularAlphaId <
      triangularVerticalVariableCount code) :
    evalAffineInOrientation R epsilon .vertical
        (triangularCentreY C code 0 j i) y =
      (y ⟨triangularRepresentativeYId code ⟨j, i.1⟩, hrep⟩ +
        (centeredInteger i.2.1 : Real) * y ⟨triangularShearId j.val, hs⟩) +
        (centeredInteger i.2.2 : Real) * y ⟨triangularAlphaId, hα⟩ := by
  unfold triangularCentreY
  rw [evalAffineInOrientation_add, evalAffineInOrientation_add,
    evalAffineInOrientation_scale_int, evalAffineInOrientation_scale_int]
  change
    (evalAffineInOrientation R epsilon .vertical
        (Expr.var C (triangularVerticalVariableCount code)
          (triangularRepresentativeYId code ⟨j, i.1⟩)) y +
      (centeredInteger i.2.1 : Real) *
        evalAffineInOrientation R epsilon .vertical
          (Expr.var C (triangularVerticalVariableCount code) (triangularShearId j.val)) y) +
      (centeredInteger i.2.2 : Real) *
        evalAffineInOrientation R epsilon .vertical
          (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId) y = _
  rw [evalAffineInOrientation_var R epsilon .vertical y
        (triangularRepresentativeYId code ⟨j, i.1⟩) hrep,
      evalAffineInOrientation_var R epsilon .vertical y (triangularShearId j.val) hs,
      evalAffineInOrientation_var R epsilon .vertical y triangularAlphaId hα]

private theorem formulaHolds_sameCentre_iff {C h v} (R : Realization C) epsilon
    (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v)
    (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R epsilon
        (sameCentreFormula cx cx' cy cy') x y ↔
      (evalAffineInOrientation R epsilon .horizontal cx x =
          evalAffineInOrientation R epsilon .horizontal cx' x) ∧
      (evalAffineInOrientation R epsilon .vertical cy y =
          evalAffineInOrientation R epsilon .vertical cy' y) := by
  simp only [sameCentreFormula, Formula.horizontalEq, formulaHoldsInOrientation,
    evalAffineInOrientation]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨le_antisymm h₁ h₂, le_antisymm h₃ h₄⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨le_of_eq hx, le_of_eq hx.symm⟩, ⟨le_of_eq hy, le_of_eq hy.symm⟩⟩

private theorem formulaHolds_cellNonoverlap_iff {C h v} (R : Realization C)
    epsilon (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h)
    (cy cy' : AffineExpr C v) (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R epsilon
        (cellNonoverlapFormula epsilon e e' cx cx' cy cy') x y ↔
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx' (Expr.input h (selectedCellLeft C epsilon e'))) x) ∨
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx' (Expr.input h (selectedCellRight C epsilon e'))) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x) ∨
      (evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy' (Expr.input v (selectedCellBottom C epsilon e'))) y) ∨
      (evalAffineInOrientation R epsilon .vertical
          (Expr.add cy' (Expr.input v (selectedCellTop C epsilon e'))) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y) := by
  simp only [cellNonoverlapFormula, Formula.orList, formulaHoldsInOrientation,
    or_false]

private theorem evalAffineInOrientation_selectedCell {C n} (R : Realization C)
    (epsilon : Bool) (s : CoordSort) (e : Fin C.cellCount) (x : Fin n → Real)
    (a : Coeff C) :
    evalAffineInOrientation R epsilon s (Expr.input n a) x =
      ∑ i, (a i : Real) * (selectedAxis epsilon s).coord (R.vertex i) :=
  evalAffineInOrientation_input R epsilon s a x

private theorem eval_selectedCellCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellRight C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.rightVertex e)]
      · simp [selectedCellRight, selectedCoordinate, Coeff.cellRight, Coeff.single]
      · intro b hb hne
        simp [selectedCellRight, Coeff.cellRight, Coeff.single, hne]
      · simp [selectedCellRight, Coeff.cellRight, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.topVertex e)]
      · simp [selectedCellRight, selectedCoordinate, Coeff.cellTop, Coeff.single]
      · intro b hb hne
        simp [selectedCellRight, Coeff.cellTop, Coeff.single, hne]
      · simp [selectedCellRight, Coeff.cellTop, Coeff.single]

private theorem eval_selectedCellLeftCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellLeft C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.leftVertex e)]
      · simp [selectedCellLeft, selectedCoordinate, Coeff.cellLeft, Coeff.single]
      · intro b hb hne
        simp [selectedCellLeft, Coeff.cellLeft, Coeff.single, hne]
      · simp [selectedCellLeft, Coeff.cellLeft, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.bottomVertex e)]
      · simp [selectedCellLeft, selectedCoordinate, Coeff.cellBottom, Coeff.single]
      · intro b hb hne
        simp [selectedCellLeft, Coeff.cellBottom, Coeff.single, hne]
      · simp [selectedCellLeft, Coeff.cellBottom, Coeff.single]

private theorem eval_selectedCellBottomCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellBottom C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.bottomVertex e)]
      · simp [selectedCellBottom, selectedCoordinate, Coeff.cellBottom, Coeff.single]
      · intro b hb hne
        simp [selectedCellBottom, Coeff.cellBottom, Coeff.single, hne]
      · simp [selectedCellBottom, Coeff.cellBottom, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.leftVertex e)]
      · simp [selectedCellBottom, selectedCoordinate, Coeff.cellLeft, Coeff.single]
      · intro b hb hne
        simp [selectedCellBottom, Coeff.cellLeft, Coeff.single, hne]
      · simp [selectedCellBottom, Coeff.cellLeft, Coeff.single]

private theorem eval_selectedCellTopCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellTop C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.topVertex e)]
      · simp [selectedCellTop, selectedCoordinate, Coeff.cellTop, Coeff.single]
      · intro b hb hne
        simp [selectedCellTop, Coeff.cellTop, Coeff.single, hne]
      · simp [selectedCellTop, Coeff.cellTop, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.rightVertex e)]
      · simp [selectedCellTop, selectedCoordinate, Coeff.cellRight, Coeff.single]
      · intro b hb hne
        simp [selectedCellTop, Coeff.cellRight, Coeff.single, hne]
      · simp [selectedCellTop, Coeff.cellRight, Coeff.single]
-/

private theorem evalAffineInOrientation_var {C n} (R : Realization C) epsilon
    (s : CoordSort) (x : Fin n → Real) (id : Nat) (hid : id < n) :
    evalAffineInOrientation R epsilon s (Expr.var C n id) x = x ⟨id, hid⟩ := by
  simp only [evalAffineInOrientation, Expr.var]
  have hsum : (∑ i : Fin n, (if i.val = id then (1 : Rat) else 0) * x i) =
      x ⟨id, hid⟩ := by
    rw [Finset.sum_eq_single ⟨id, hid⟩]
    · simp
    · intro b hb hne
      have hval : b.val ≠ id := by
        intro hval
        exact hne (Fin.ext hval)
      simp [hval]
    · simp
  simpa [Coeff.zero] using hsum

private theorem eval_triangularCentreX {C} (R : Realization C) (epsilon : Bool)
    (code : RawTriangularCode) (x : Fin (triangularHorizontalVariableCount code) → Real)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j)
    (hrep : triangularRepresentativeXId code ⟨j, i.1⟩ <
      triangularHorizontalVariableCount code) (hβ : triangularBetaId <
      triangularHorizontalVariableCount code) :
    evalAffineInOrientation R epsilon .horizontal
        (triangularCentreX C code 0 j i) x =
      x ⟨triangularRepresentativeXId code ⟨j, i.1⟩, hrep⟩ +
        (centeredInteger i.2.1 : Real) * x ⟨triangularBetaId, hβ⟩ := by
  unfold triangularCentreX
  rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int]
  change
    evalAffineInOrientation R epsilon .horizontal
        (Expr.var C (triangularHorizontalVariableCount code)
          (triangularRepresentativeXId code ⟨j, i.1⟩)) x +
      (centeredInteger i.2.1 : Real) *
        evalAffineInOrientation R epsilon .horizontal
          (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId) x = _
  rw [evalAffineInOrientation_var R epsilon .horizontal x
        (triangularRepresentativeXId code ⟨j, i.1⟩) hrep,
      evalAffineInOrientation_var R epsilon .horizontal x triangularBetaId hβ]

private theorem eval_triangularCentreY {C} (R : Realization C) (epsilon : Bool)
    (code : RawTriangularCode) (y : Fin (triangularVerticalVariableCount code) → Real)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j)
    (hrep : triangularRepresentativeYId code ⟨j, i.1⟩ <
      triangularVerticalVariableCount code) (hs : triangularShearId j.val <
      triangularVerticalVariableCount code) (hα : triangularAlphaId <
      triangularVerticalVariableCount code) :
    evalAffineInOrientation R epsilon .vertical
        (triangularCentreY C code 0 j i) y =
      (y ⟨triangularRepresentativeYId code ⟨j, i.1⟩, hrep⟩ +
        (centeredInteger i.2.1 : Real) * y ⟨triangularShearId j.val, hs⟩) +
        (centeredInteger i.2.2 : Real) * y ⟨triangularAlphaId, hα⟩ := by
  unfold triangularCentreY
  rw [evalAffineInOrientation_add, evalAffineInOrientation_add,
    evalAffineInOrientation_scale_int, evalAffineInOrientation_scale_int]
  change
    (evalAffineInOrientation R epsilon .vertical
        (Expr.var C (triangularVerticalVariableCount code)
          (triangularRepresentativeYId code ⟨j, i.1⟩)) y +
      (centeredInteger i.2.1 : Real) *
        evalAffineInOrientation R epsilon .vertical
          (Expr.var C (triangularVerticalVariableCount code) (triangularShearId j.val)) y) +
      (centeredInteger i.2.2 : Real) *
        evalAffineInOrientation R epsilon .vertical
          (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId) y = _
  rw [evalAffineInOrientation_var R epsilon .vertical y
        (triangularRepresentativeYId code ⟨j, i.1⟩) hrep,
      evalAffineInOrientation_var R epsilon .vertical y (triangularShearId j.val) hs,
      evalAffineInOrientation_var R epsilon .vertical y triangularAlphaId hα]

private theorem formulaHolds_sameCentre_iff {C h v} (R : Realization C) epsilon
    (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v)
    (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R epsilon
        (sameCentreFormula cx cx' cy cy') x y ↔
      (evalAffineInOrientation R epsilon .horizontal cx x =
          evalAffineInOrientation R epsilon .horizontal cx' x) ∧
      (evalAffineInOrientation R epsilon .vertical cy y =
          evalAffineInOrientation R epsilon .vertical cy' y) := by
  simp only [sameCentreFormula, Formula.horizontalEq, formulaHoldsInOrientation,
    evalAffineInOrientation]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨le_antisymm h₁ h₂, le_antisymm h₃ h₄⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨le_of_eq hx, le_of_eq hx.symm⟩, ⟨le_of_eq hy, le_of_eq hy.symm⟩⟩

private theorem formulaHolds_cellNonoverlap_iff {C h v} (R : Realization C)
    epsilon (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h)
    (cy cy' : AffineExpr C v) (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R epsilon
        (cellNonoverlapFormula epsilon e e' cx cx' cy cy') x y ↔
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx' (Expr.input h (selectedCellLeft C epsilon e'))) x) ∨
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx' (Expr.input h (selectedCellRight C epsilon e'))) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x) ∨
      (evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy' (Expr.input v (selectedCellBottom C epsilon e'))) y) ∨
      (evalAffineInOrientation R epsilon .vertical
          (Expr.add cy' (Expr.input v (selectedCellTop C epsilon e'))) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y) := by
  simp only [cellNonoverlapFormula, Formula.orList, formulaHoldsInOrientation,
    or_false]

private theorem eval_selectedCellCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellRight C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.topVertex e else C.rightVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.rightVertex e)]
      · simp [selectedCellRight, selectedCoordinate, Coeff.cellRight, Coeff.single]
      · intro b hb hne
        simp [selectedCellRight, Coeff.cellRight, Coeff.single, hne]
      · simp [selectedCellRight, Coeff.cellRight, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.topVertex e)]
      · simp [selectedCellRight, selectedCoordinate, Coeff.cellTop, Coeff.single]
      · intro b hb hne
        simp [selectedCellRight, Coeff.cellTop, Coeff.single, hne]
      · simp [selectedCellRight, Coeff.cellTop, Coeff.single]

private theorem eval_selectedCellLeftCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellLeft C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.bottomVertex e else C.leftVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.leftVertex e)]
      · simp [selectedCellLeft, selectedCoordinate, Coeff.cellLeft, Coeff.single]
      · intro b hb hne
        simp [selectedCellLeft, Coeff.cellLeft, Coeff.single, hne]
      · simp [selectedCellLeft, Coeff.cellLeft, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.bottomVertex e)]
      · simp [selectedCellLeft, selectedCoordinate, Coeff.cellBottom, Coeff.single]
      · intro b hb hne
        simp [selectedCellLeft, Coeff.cellBottom, Coeff.single, hne]
      · simp [selectedCellLeft, Coeff.cellBottom, Coeff.single]

private theorem eval_selectedCellBottomCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellBottom C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.leftVertex e else C.bottomVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.bottomVertex e)]
      · simp [selectedCellBottom, selectedCoordinate, Coeff.cellBottom, Coeff.single]
      · intro b hb hne
        simp [selectedCellBottom, Coeff.cellBottom, Coeff.single, hne]
      · simp [selectedCellBottom, Coeff.cellBottom, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.leftVertex e)]
      · simp [selectedCellBottom, selectedCoordinate, Coeff.cellLeft, Coeff.single]
      · intro b hb hne
        simp [selectedCellBottom, Coeff.cellLeft, Coeff.single, hne]
      · simp [selectedCellBottom, Coeff.cellLeft, Coeff.single]

private theorem eval_selectedCellTopCoeff {C} (R : Realization C) (epsilon : Bool)
    (s : CoordSort) (e : Fin C.cellCount) :
    (∑ i, (selectedCellTop C epsilon e i : Real) *
        (selectedAxis epsilon s).coord (R.vertex i)) =
      selectedCoordinate epsilon s
        (R.vertex (if epsilon then C.rightVertex e else C.topVertex e)) := by
  classical
  cases epsilon with
  | false =>
      rw [Finset.sum_eq_single (C.topVertex e)]
      · simp [selectedCellTop, selectedCoordinate, Coeff.cellTop, Coeff.single]
      · intro b hb hne
        simp [selectedCellTop, Coeff.cellTop, Coeff.single, hne]
      · simp [selectedCellTop, Coeff.cellTop, Coeff.single]
  | true =>
      rw [Finset.sum_eq_single (C.rightVertex e)]
      · simp [selectedCellTop, selectedCoordinate, Coeff.cellRight, Coeff.single]
      · intro b hb hne
        simp [selectedCellTop, Coeff.cellRight, Coeff.single, hne]
      · simp [selectedCellTop, Coeff.cellRight, Coeff.single]

private theorem prefix_get_sum_le {α : Type} (f : α → Nat) :
    ∀ (xs : List α) (j : Fin xs.length),
      ((xs.take j.val).map f).sum + f (xs.get j) ≤ (xs.map f).sum := by
  intro xs j
  have htake : (xs.take j.val).concat (xs.get j) = xs.take (j.val + 1) :=
    List.take_concat_get j.isLt
  have hle : ((xs.take (j.val + 1)).map f).sum ≤ (xs.map f).sum := by
    have hsplit := congrArg (fun l : List α => (l.map f).sum)
      (List.take_append_drop (j.val + 1) xs)
    simp only [List.map_append, List.sum_append] at hsplit
    omega
  have hsum := congrArg (fun l : List α => (l.map f).sum) htake
  rw [← hsum, List.map_concat, List.sum_concat] at hle
  exact hle

private theorem triangularIntervalOrdinal_lt' : ∀ (pieces : List RawTriangularPieceCode)
    (j : Fin pieces.length) (ell : Fin (pieces.get j).intervalCount),
    ((pieces.take j.val).map RawTriangularPieceCode.intervalCount).sum + ell.val <
      (pieces.map RawTriangularPieceCode.intervalCount).sum := by
  intro pieces j ell
  have hle := prefix_get_sum_le RawTriangularPieceCode.intervalCount pieces j
  omega

private theorem triangularIntervalOrdinal_lt {code : RawTriangularCode}
    (i : TriangularIntervalIndex code) :
    triangularIntervalOrdinal code i < triangularTotalIntervalCount code := by
  have hle := prefix_get_sum_le RawTriangularPieceCode.intervalCount code.pieces i.1
  dsimp [triangularIntervalOrdinal, triangularTotalIntervalCount, triangularPiece]
    at hle ⊢
  omega

private theorem triangularRepresentativeOrdinal_lt' : ∀ (pieces : List RawTriangularPieceCode)
    (j : Fin pieces.length) (r : Fin (pieces.get j).representativeCount),
    ((pieces.take j.val).map RawTriangularPieceCode.representativeCount).sum + r.val <
      (pieces.map RawTriangularPieceCode.representativeCount).sum := by
  intro pieces j r
  have hle := prefix_get_sum_le RawTriangularPieceCode.representativeCount pieces j
  omega

private theorem triangularRepresentativeOrdinal_lt {code : RawTriangularCode}
    (i : TriangularRepresentativeIndex code) :
    triangularRepresentativeOrdinal code i < triangularTotalRepresentativeCount code := by
  have hle := prefix_get_sum_le RawTriangularPieceCode.representativeCount code.pieces i.1
  dsimp [triangularRepresentativeOrdinal, triangularTotalRepresentativeCount,
    triangularPiece] at hle ⊢
  omega

private theorem mem_triangularFiniteIndices (code : RawTriangularCode)
    (j : Fin (triangularPieceCount code)) (i : TriangularFiniteIndex code j) :
    i ∈ triangularFiniteIndices code j := by
  rcases i with ⟨r, n, k⟩
  unfold triangularFiniteIndices
  apply List.mem_flatMap.mpr
  refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨n, List.mem_ofFn.mpr ⟨n, rfl⟩, ?_⟩
  exact List.mem_ofFn.mpr ⟨k, rfl⟩

private theorem mem_triangularIntervalIndices (code : RawTriangularCode)
    (i : TriangularIntervalIndex code) : i ∈ triangularIntervalIndices code := by
  rcases i with ⟨j, ell⟩
  unfold triangularIntervalIndices
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
  exact List.mem_ofFn.mpr ⟨ell, rfl⟩

private theorem mem_triangularRepresentativeIndices (code : RawTriangularCode)
    (i : TriangularRepresentativeIndex code) :
    i ∈ triangularRepresentativeIndices code := by
  rcases i with ⟨j, r⟩
  unfold triangularRepresentativeIndices
  apply List.mem_flatMap.mpr
  exact ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, List.mem_ofFn.mpr ⟨r, rfl⟩⟩

private theorem triangular_forward_packing_formula : ∀ {C} (R : Realization C) code
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real),
    formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y →
      ∀ (j : Fin (triangularPieceCount code))
        (i i' : TriangularFiniteIndex code j), i ≠ i' →
        formulaHoldsInOrientation R code.orientation
          ((sameCentreFormula (triangularCentreX C code 0 j i)
              (triangularCentreX C code 0 j i')
              (triangularCentreY C code 0 j i)
              (triangularCentreY C code 0 j i')).disjunction
            (Formula.andList
              ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
                (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                  cellNonoverlapFormula code.orientation e e'
                    (triangularCentreX C code 0 j i)
                    (triangularCentreX C code 0 j i')
                    (triangularCentreY C code 0 j i)
                    (triangularCentreY C code 0 j i')))) x y := by
  intro C R code y x hbody
  have hbody' := hbody
  simp only [triangularBody] at hbody'
  have hall := (formulaHolds_andList R code.orientation _ x y).mp hbody'
  let pieces : List (Fin (triangularPieceCount code)) := List.ofFn fun j => j
  let cells : List (Fin C.cellCount) := List.ofFn fun e => e
  let packingFormula : Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) := Formula.andList
    (pieces.flatMap fun j =>
      (triangularFiniteIndices code j).flatMap fun i =>
        (triangularFiniteIndices code j).map fun i' =>
          if i = i' then Formula.truth else
            (sameCentreFormula (triangularCentreX C code 0 j i)
              (triangularCentreX C code 0 j i')
              (triangularCentreY C code 0 j i)
              (triangularCentreY C code 0 j i')).disjunction
              (Formula.andList
                (cells.flatMap fun e => cells.map fun e' =>
                  cellNonoverlapFormula code.orientation e e'
                    (triangularCentreX C code 0 j i)
                    (triangularCentreX C code 0 j i')
                    (triangularCentreY C code 0 j i)
                    (triangularCentreY C code 0 j i'))))
  have hpacking := hall packingFormula (by
    dsimp [packingFormula, pieces, cells]
    simp [List.mem_append])
  have hpacking' := (formulaHolds_andList R code.orientation _ x y).mp hpacking
  intro j i i' hne
  let p :=
    (sameCentreFormula (triangularCentreX C code 0 j i)
      (triangularCentreX C code 0 j i')
      (triangularCentreY C code 0 j i)
      (triangularCentreY C code 0 j i')).disjunction
      (Formula.andList
        ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
          (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
            cellNonoverlapFormula code.orientation e e'
              (triangularCentreX C code 0 j i)
              (triangularCentreX C code 0 j i')
              (triangularCentreY C code 0 j i)
              (triangularCentreY C code 0 j i')))
  have hp := hpacking' p (by
    dsimp [p, pieces, cells]
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨i, mem_triangularFiniteIndices code j i, ?_⟩
    apply List.mem_map.mpr
    refine ⟨i', mem_triangularFiniteIndices code j i', ?_⟩
    simp [hne])
  simpa [p] using hp

private theorem formulaHolds_cellNonoverlap_semantic_iff {C h v} (R : Realization C)
    (epsilon : Bool) (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h)
    (cy cy' : AffineExpr C v) (x : Fin h → Real) (y : Fin v → Real)
    (c c' : Tiling.Plane)
    (hcx : evalAffineInOrientation R epsilon .horizontal cx x = c.re)
    (hcx' : evalAffineInOrientation R epsilon .horizontal cx' x = c'.re)
    (hcy : evalAffineInOrientation R epsilon .vertical cy y = c.im)
    (hcy' : evalAffineInOrientation R epsilon .vertical cy' y = c'.im) :
    formulaHoldsInOrientation R epsilon
        (cellNonoverlapFormula epsilon e e' cx cx' cy cy') x y ↔
      semanticCellsNonoverlap R epsilon e e' c c' := by
  rw [formulaHolds_cellNonoverlap_iff]
  simp only [evalAffineInOrientation_add, evalAffineInOrientation_input]
  rw [eval_selectedCellCoeff, eval_selectedCellLeftCoeff,
    eval_selectedCellCoeff, eval_selectedCellLeftCoeff,
    eval_selectedCellTopCoeff, eval_selectedCellBottomCoeff,
    eval_selectedCellTopCoeff, eval_selectedCellBottomCoeff]
  simp only [semanticCellsNonoverlap]
  rw [hcx, hcx', hcy, hcy']

private theorem formulaHolds_sameCentre_semantic_iff {C h v} (R : Realization C)
    (epsilon : Bool) (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v)
    (x : Fin h → Real) (y : Fin v → Real) (c c' : Tiling.Plane)
    (hcx : evalAffineInOrientation R epsilon .horizontal cx x = c.re)
    (hcx' : evalAffineInOrientation R epsilon .horizontal cx' x = c'.re)
    (hcy : evalAffineInOrientation R epsilon .vertical cy y = c.im)
    (hcy' : evalAffineInOrientation R epsilon .vertical cy' y = c'.im) :
    formulaHoldsInOrientation R epsilon
        (sameCentreFormula cx cx' cy cy') x y ↔ c = c' := by
  rw [formulaHolds_sameCentre_iff, hcx, hcx', hcy, hcy']
  constructor
  · rintro ⟨hr, hi⟩
    apply Complex.ext
    · exact hr
    · exact hi
  · intro he
    exact ⟨congrArg Complex.re he, congrArg Complex.im he⟩

private theorem triangular_packing_semantic_bridge {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (hpack : ∀ (j : Fin (triangularPieceCount code))
      (i i' : TriangularFiniteIndex code j), i ≠ i' →
      formulaHoldsInOrientation R code.orientation
        ((sameCentreFormula (triangularCentreX C code 0 j i)
            (triangularCentreX C code 0 j i')
            (triangularCentreY C code 0 j i)
            (triangularCentreY C code 0 j i')).disjunction
          (Formula.andList
            ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
              (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                cellNonoverlapFormula code.orientation e e'
                  (triangularCentreX C code 0 j i)
                  (triangularCentreX C code 0 j i')
                  (triangularCentreY C code 0 j i)
                  (triangularCentreY C code 0 j i')))) x y)
    (hcx : ∀ (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 0 j i) x =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 0 j i) y =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im) :
    ∀ (j : Fin (triangularPieceCount code))
      (i i' : TriangularFiniteIndex code j), i ≠ i' →
      triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2) =
          triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
            (centeredInteger i'.2.2) ∨
      ∀ e e', semanticCellsNonoverlap R code.orientation e e'
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2))
        (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
          (centeredInteger i'.2.2)) := by
  intro j i i' hne
  rcases hpack j i i' hne with hp | hp
  · left
    exact (formulaHolds_sameCentre_semantic_iff R code.orientation
      (triangularCentreX C code 0 j i) (triangularCentreX C code 0 j i')
      (triangularCentreY C code 0 j i) (triangularCentreY C code 0 j i') x y
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2))
      (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
        (centeredInteger i'.2.2)) (hcx j i) (hcx j i') (hcy j i) (hcy j i')).mp hp
  · right
    intro e e'
    have hlist := (formulaHolds_andList R code.orientation _ x y).mp hp
    have he := hlist
        (cellNonoverlapFormula code.orientation e e'
          (triangularCentreX C code 0 j i)
          (triangularCentreX C code 0 j i')
          (triangularCentreY C code 0 j i)
          (triangularCentreY C code 0 j i')) (by
      apply List.mem_flatMap.mpr
      refine ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, ?_⟩
      apply List.mem_map.mpr
      exact ⟨e', List.mem_ofFn.mpr ⟨e', rfl⟩, rfl⟩)
    exact (formulaHolds_cellNonoverlap_semantic_iff R code.orientation e e'
      (triangularCentreX C code 0 j i) (triangularCentreX C code 0 j i')
      (triangularCentreY C code 0 j i) (triangularCentreY C code 0 j i') x y
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2))
      (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
        (centeredInteger i'.2.2)) (hcx j i) (hcx j i') (hcy j i) (hcy j i')).mp he

private theorem formulaHolds_openCell_semantic_iff {C h v} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (cx : AffineExpr C h)
    (cy : AffineExpr C v) (x : Fin h → Real) (y : Fin v → Real)
    (c p : Tiling.Plane)
    (hcx : evalAffineInOrientation R epsilon .horizontal cx x = c.re)
    (hcy : evalAffineInOrientation R epsilon .vertical cy y = c.im)
    (hpx : evalAffineInOrientation R epsilon .horizontal
        (Expr.var C h 0) x = p.re)
    (hpy : evalAffineInOrientation R epsilon .vertical
        (Expr.var C v 0) y = p.im) :
      formulaHoldsInOrientation R epsilon
        (openCellFormula epsilon e cx (Expr.var C h 0) cy (Expr.var C v 0)) x y ↔
      semanticOpenCell R epsilon e c p := by
  simp only [openCellFormula]
  rw [formulaHolds_andList]
  constructor
  · intro hall
    have h1 := hall
      (Formula.horizontalLt
        (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e)))
        (Expr.var C h 0)) (by simp)
    have h2 := hall
      (Formula.horizontalLt (Expr.var C h 0)
        (Expr.add cx (Expr.input h (selectedCellRight C epsilon e)))) (by simp)
    have h3 := hall
      (Formula.verticalLt
        (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e)))
        (Expr.var C v 0)) (by simp)
    have h4 := hall
      (Formula.verticalLt (Expr.var C v 0)
        (Expr.add cy (Expr.input v (selectedCellTop C epsilon e)))) (by simp)
    change evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x <
        evalAffineInOrientation R epsilon .horizontal (Expr.var C h 0) x at h1
    change evalAffineInOrientation R epsilon .horizontal
          (Expr.var C h 0) x <
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x at h2
    change evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y <
        evalAffineInOrientation R epsilon .vertical (Expr.var C v 0) y at h3
    change evalAffineInOrientation R epsilon .vertical
          (Expr.var C v 0) y <
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y at h4
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellLeftCoeff, hcx, hpx] at h1
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellCoeff, hcx, hpx] at h2
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellBottomCoeff, hcy, hpy] at h3
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellTopCoeff, hcy, hpy] at h4
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · change evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x <
        evalAffineInOrientation R epsilon .horizontal (Expr.var C h 0) x
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellLeftCoeff, hcx, hpx]
      exact h1
    · change evalAffineInOrientation R epsilon .horizontal
          (Expr.var C h 0) x <
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellCoeff, hcx, hpx]
      exact h2
    · change evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y <
        evalAffineInOrientation R epsilon .vertical (Expr.var C v 0) y
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellBottomCoeff, hcy, hpy]
      exact h3
    · change evalAffineInOrientation R epsilon .vertical
          (Expr.var C v 0) y <
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellTopCoeff, hcy, hpy]
      exact h4

private theorem evalAffineInOrientation_scale_small {C n} (R : Realization C) epsilon
    (s : CoordSort) (q : Rat) (A : AffineExpr C n) (x : Fin n → Real)
    (hq : q = (-1 : Rat) ∨ q = 0 ∨ q = 1) :
    evalAffineInOrientation R epsilon s (Expr.scale q A) x =
      (q : Real) * evalAffineInOrientation R epsilon s A x := by
  rcases hq with hq | hq | hq
  · subst q
    simpa using (evalAffineInOrientation_scale_int R epsilon s (-1) A x)
  · subst q
    simpa using (evalAffineInOrientation_scale_int R epsilon s 0 A x)
  · subst q
    simpa using (evalAffineInOrientation_scale_int R epsilon s 1 A x)

private theorem formulaHolds_triangularBaseClosed_iff {C} (R : Realization C)
    (epsilon : Bool) (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (x : Fin (triangularHorizontalVariableCount code + 1) → Real)
    {w : Nat} (y : Fin w → Real) (p : Tiling.Plane)
    (hβ : evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 triangularBetaId) x = X.beta)
    (hpx : evalAffineInOrientation R epsilon .horizontal
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x = p.re)
    (hleft : ∀ ell, evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩)) x =
          X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ ell, evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩)) x =
          X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R epsilon
        (triangularBaseClosedFormula C code 1 j
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0)) x y
      ↔ ∃ ell, ∃ q : Int, q ∈ ([-1, 0, 1] : List Int) ∧
        X.intervalLeft ⟨j, ell⟩ + q * X.beta ≤ p.re ∧
        p.re ≤ X.intervalRight ⟨j, ell⟩ + q * X.beta := by
  simp only [triangularBaseClosedFormula]
  rw [formulaHolds_orList]
  constructor
  · rintro ⟨f, hf, hF⟩
    simp only [List.mem_flatMap] at hf
    rcases hf with ⟨ell, hell, hf⟩
    rcases List.mem_map.mp hf with ⟨q, hq, hformula⟩
    subst f
    have hq' : q = (-1 : Rat) ∨ q = 0 ∨ q = 1 := by
      simpa using hq
    have hscale := evalAffineInOrientation_scale_small R epsilon .horizontal q
      (triH C code 1 triangularBetaId) x hq'
    have hconj := hF
    change (_ ∧ _) at hconj
    have hL := hconj.1
    have hR := hconj.2
    simp only [formulaHoldsInOrientation] at hL hR
    rw [evalAffineInOrientation_add, hscale,
      hleft ell, hβ, hpx] at hL
    rw [evalAffineInOrientation_add, hscale,
      hright ell, hβ, hpx] at hR
    rcases hq' with hq' | hq' | hq'
    · rw [hq'] at hL hR
      exact ⟨ell, -1, by simp, by simpa using hL, by simpa using hR⟩
    · rw [hq'] at hL hR
      exact ⟨ell, 0, by simp, by simpa using hL, by simpa using hR⟩
    · rw [hq'] at hL hR
      exact ⟨ell, 1, by simp, by simpa using hL, by simpa using hR⟩
  · rintro ⟨ell, q, hq, hL, hR⟩
    have hqRat : (q : Rat) ∈ (do
        let a ← ([-1, 0, 1] : List Int)
        pure (a : Rat)) := by
      have hq' : q = -1 ∨ q = 0 ∨ q = 1 := by simpa using hq
      rcases hq' with rfl | rfl | rfl <;> simp
    refine ⟨(Formula.horizontalLe
          (Expr.add (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
            (Expr.scale q (triH C code 1 triangularBetaId)))
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
        (Formula.horizontalLe (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
          (Expr.add (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
            (Expr.scale q (triH C code 1 triangularBetaId)))), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨ell, List.mem_ofFn.mpr ⟨ell, rfl⟩, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(q : Rat), hqRat, rfl⟩
    · change
        (evalAffineInOrientation R epsilon .horizontal
            (Expr.add (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
              (Expr.scale q (triH C code 1 triangularBetaId))) x ≤
          evalAffineInOrientation R epsilon .horizontal
            (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x) ∧
        (evalAffineInOrientation R epsilon .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x ≤
          evalAffineInOrientation R epsilon .horizontal
            (Expr.add (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
              (Expr.scale q (triH C code 1 triangularBetaId))) x)
      constructor
      · rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int,
          hleft ell, hβ, hpx]
        exact hL
      · rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int,
          hright ell, hβ, hpx]
        exact hR

private def triangularLeakageInnerFormula (C : RegionCode) (code : RawTriangularCode)
    (j : Fin (triangularPieceCount code)) :
    Formula C (triangularHorizontalVariableCount code + 1)
      (triangularVerticalVariableCount code + 1) :=
  let h := triangularHorizontalVariableCount code
  let v := triangularVerticalVariableCount code
  let x := Expr.var C (h + 1) 0
  let y := Expr.var C (v + 1) 0
  let beta' := triH C code 1 triangularBetaId
  let alpha' := triV C code 1 triangularAlphaId
  let hit := Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
    (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
      openCellFormula code.orientation e
        (triangularCentreX C code 1 j i) x
        (triangularCentreY C code 1 j i) y)
  Formula.implication
    (Formula.andList
      [.horizontalLt (Expr.zero C (h + 1)) x, .horizontalLt x beta',
       .verticalLt (Expr.zero C (v + 1)) y, .verticalLt y alpha', hit])
    (triangularBaseClosedFormula C code 1 j x)

private theorem triangular_forward_leakage_formula : ∀ {C} (R : Realization C) code
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real),
    formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y →
      ∀ j, formulaHoldsInOrientation R code.orientation
        (Formula.forallHorizontal (Formula.forallVertical
          (triangularLeakageInnerFormula C code j))) x y := by
  intro C R code y x hbody
  have hall := (formulaHolds_andList R code.orientation _ x y).mp (by
    simpa only [triangularBody] using hbody)
  let pieces : List (Fin (triangularPieceCount code)) := List.ofFn fun j => j
  let leakageFormula := Formula.andList (pieces.map fun j =>
    Formula.forallHorizontal (Formula.forallVertical
      (triangularLeakageInnerFormula C code j)))
  have hleak := hall leakageFormula (by
    dsimp [leakageFormula, pieces, triangularLeakageInnerFormula]
    simp [List.mem_append])
  have hleak' := (formulaHolds_andList R code.orientation _ x y).mp hleak
  intro j
  exact hleak' _ (by
    dsimp [leakageFormula, pieces]
    exact List.mem_map.mpr ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩)

private theorem triangular_no_leakage_semantic_bridge {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (x0 : Fin (triangularHorizontalVariableCount code) → Real)
    (y0 : Fin (triangularVerticalVariableCount code) → Real)
    (hleak : formulaHoldsInOrientation R code.orientation
      (Formula.forallHorizontal (Formula.forallVertical
        (triangularLeakageInnerFormula C code j))) x0 y0)
    (hcx : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i)
          (Fin.cons p.re x0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i)
          (Fin.cons p.im y0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 triangularBetaId) (Fin.cons p.re x0) = X.beta)
    (hα : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .vertical
        (triV C code 1 triangularAlphaId) (Fin.cons p.im y0) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalRight ⟨j, ell⟩) :
    ∀ p, 0 < p.re → p.re < X.beta → 0 < p.im → p.im < X.alpha →
      (∃ i ∈ triangularFiniteIndices code j, ∃ e,
        semanticOpenCell R code.orientation e
          (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
            (centeredInteger i.2.2)) p) →
      ∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
        X.intervalLeft ⟨j, ell⟩ + q * X.beta ≤ p.re ∧
        p.re ≤ X.intervalRight ⟨j, ell⟩ + q * X.beta := by
  intro p hp0 hpβ hpI0 hpα hhit
  let hx : Fin (triangularHorizontalVariableCount code + 1) → Real :=
    Fin.cons p.re x0
  let hy : Fin (triangularVerticalVariableCount code + 1) → Real :=
    Fin.cons p.im y0
  have hpx : evalAffineInOrientation R code.orientation .horizontal
      (Expr.var C _ 0) hx = p.re := by
    rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
      (Nat.zero_lt_succ _)]
    simp [hx]
  have hpy : evalAffineInOrientation R code.orientation .vertical
      (Expr.var C _ 0) hy = p.im := by
    rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
      (Nat.zero_lt_succ _)]
    simp [hy]
  have hH : ∀ t : Real, formulaHoldsInOrientation R code.orientation
      (Formula.forallVertical (triangularLeakageInnerFormula C code j))
      (Fin.cons t x0) y0 := by
    simpa [Formula.forallHorizontal, formulaHoldsInOrientation] using hleak
  have hV : ∀ t : Real, formulaHoldsInOrientation R code.orientation
      (triangularLeakageInnerFormula C code j) (Fin.cons p.re x0) (Fin.cons t y0) := by
    simpa [Formula.forallVertical, formulaHoldsInOrientation] using hH p.re
  have hImp := hV p.im
  have hhitFormula : formulaHoldsInOrientation R code.orientation
      (Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
        (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
          openCellFormula code.orientation e
            (triangularCentreX C code 1 j i) (Expr.var C _ 0)
            (triangularCentreY C code 1 j i) (Expr.var C _ 0))) hx hy := by
    rcases hhit with ⟨i, hi, e, he⟩
    apply (formulaHolds_orList R code.orientation _ hx hy).2
    refine ⟨openCellFormula code.orientation e
      (triangularCentreX C code 1 j i) (Expr.var C _ 0)
      (triangularCentreY C code 1 j i) (Expr.var C _ 0), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨i, hi, ?_⟩
      apply List.mem_map.mpr
      exact ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, rfl⟩
    · apply (formulaHolds_openCell_semantic_iff R code.orientation e
        (triangularCentreX C code 1 j i) (triangularCentreY C code 1 j i)
        (Fin.cons p.re x0) (Fin.cons p.im y0)
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)) p (hcx p i) (hcy p i) hpx hpy).2
      exact he
  have hAnte : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        [.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
            (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
         .horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (triH C code 1 triangularBetaId),
         .verticalLt (Expr.zero C (triangularVerticalVariableCount code + 1))
            (Expr.var C (triangularVerticalVariableCount code + 1) 0),
         .verticalLt (Expr.var C (triangularVerticalVariableCount code + 1) 0)
            (triV C code 1 triangularAlphaId),
         Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
           (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
             openCellFormula code.orientation e
               (triangularCentreX C code 1 j i) (Expr.var C _ 0)
               (triangularCentreY C code 1 j i) (Expr.var C _ 0))]) hx hy := by
    apply (formulaHolds_andList R code.orientation _ hx hy).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_zero,
        evalAffineInOrientation_var, hx] using hp0
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_var, hβ p, hx]
        using hpβ
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_zero,
        evalAffineInOrientation_var, hy] using hpI0
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_var, hα p, hy]
        using hpα
    · exact hhitFormula
  have hImp' := hImp
  simp only [triangularLeakageInnerFormula, Formula.implication,
    formulaHoldsInOrientation] at hImp'
  have hbase := hImp'.resolve_left (fun hnot => hnot hAnte)
  exact (formulaHolds_triangularBaseClosed_iff R code.orientation code X j hx
    hy p (by simpa [hx] using hβ p) hpx (hleft p) (hright p)).mp hbase

private theorem formulaHolds_closedCell_semantic_iff {C h v} (R : Realization C)
    (epsilon : Bool) (e : Fin C.cellCount) (cx : AffineExpr C h)
    (cy : AffineExpr C v) (x : Fin h → Real) (y : Fin v → Real)
    (c p : Tiling.Plane)
    (hcx : evalAffineInOrientation R epsilon .horizontal cx x = c.re)
    (hcy : evalAffineInOrientation R epsilon .vertical cy y = c.im)
    (hpx : evalAffineInOrientation R epsilon .horizontal
        (Expr.var C h 0) x = p.re)
    (hpy : evalAffineInOrientation R epsilon .vertical
        (Expr.var C v 0) y = p.im) :
    formulaHoldsInOrientation R epsilon
        (closedCellFormula epsilon e cx (Expr.var C h 0) cy (Expr.var C v 0)) x y ↔
      semanticClosedCell R epsilon e c p := by
  simp only [closedCellFormula]
  rw [formulaHolds_andList]
  constructor
  · intro hall
    have h1 := hall
      (Formula.horizontalLe
        (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e)))
        (Expr.var C h 0)) (by simp)
    have h2 := hall
      (Formula.horizontalLe (Expr.var C h 0)
        (Expr.add cx (Expr.input h (selectedCellRight C epsilon e)))) (by simp)
    have h3 := hall
      (Formula.verticalLe
        (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e)))
        (Expr.var C v 0)) (by simp)
    have h4 := hall
      (Formula.verticalLe (Expr.var C v 0)
        (Expr.add cy (Expr.input v (selectedCellTop C epsilon e)))) (by simp)
    change evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x ≤
        evalAffineInOrientation R epsilon .horizontal (Expr.var C h 0) x at h1
    change evalAffineInOrientation R epsilon .horizontal
          (Expr.var C h 0) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x at h2
    change evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y ≤
        evalAffineInOrientation R epsilon .vertical (Expr.var C v 0) y at h3
    change evalAffineInOrientation R epsilon .vertical
          (Expr.var C v 0) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y at h4
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellLeftCoeff, hcx, hpx] at h1
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellCoeff, hcx, hpx] at h2
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellBottomCoeff, hcy, hpy] at h3
    rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
      eval_selectedCellTopCoeff, hcy, hpy] at h4
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · change evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C epsilon e))) x ≤
        evalAffineInOrientation R epsilon .horizontal (Expr.var C h 0) x
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellLeftCoeff, hcx, hpx]
      exact h1
    · change evalAffineInOrientation R epsilon .horizontal
          (Expr.var C h 0) x ≤
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C epsilon e))) x
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellCoeff, hcx, hpx]
      exact h2
    · change evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C epsilon e))) y ≤
        evalAffineInOrientation R epsilon .vertical (Expr.var C v 0) y
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellBottomCoeff, hcy, hpy]
      exact h3
    · change evalAffineInOrientation R epsilon .vertical
          (Expr.var C v 0) y ≤
        evalAffineInOrientation R epsilon .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C epsilon e))) y
      rw [evalAffineInOrientation_add, evalAffineInOrientation_input,
        eval_selectedCellTopCoeff, hcy, hpy]
      exact h4

private def triangularCoverageInnerFormula (C : RegionCode) (code : RawTriangularCode)
    (j : Fin (triangularPieceCount code)) :
    Formula C (triangularHorizontalVariableCount code + 1)
      (triangularVerticalVariableCount code + 1) :=
  let h := triangularHorizontalVariableCount code
  let v := triangularVerticalVariableCount code
  let x := Expr.var C (h + 1) 0
  let y := Expr.var C (v + 1) 0
  let beta' := triH C code 1 triangularBetaId
  let alpha' := triV C code 1 triangularAlphaId
  let base := triangularBaseOpenFormula C code 1 j x
  let covered := Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
    (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
      closedCellFormula code.orientation e
        (triangularCentreX C code 1 j i) x
        (triangularCentreY C code 1 j i) y)
  Formula.implication
    (Formula.andList
      [.horizontalLt (Expr.zero C (h + 1)) x, .horizontalLt x beta',
       .verticalLt (Expr.zero C (v + 1)) y, .verticalLt y alpha', base])
    covered

private theorem triangularBaseOpen_extract {C} (R : Realization C)
    (epsilon : Bool) (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (x : Fin (triangularHorizontalVariableCount code + 1) → Real)
    {w : Nat} (y : Fin w → Real) (p : Tiling.Plane)
    (hβ : evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 triangularBetaId) x = X.beta)
    (hpx : evalAffineInOrientation R epsilon .horizontal
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x = p.re)
    (hleft : ∀ ell, evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩)) x =
          X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ ell, evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩)) x =
          X.intervalRight ⟨j, ell⟩)
    (hbase : formulaHoldsInOrientation R epsilon
      (triangularBaseOpenFormula C code 1 j
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0)) x y) :
    ∃ ell, ∃ q : Int, q ∈ ([-1, 0, 1] : List Int) ∧
      X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
      p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta := by
  simp only [triangularBaseOpenFormula] at hbase
  have hor := (formulaHolds_orList R epsilon _ x y).mp hbase
  rcases hor with ⟨f, hf, hF⟩
  simp only [List.mem_flatMap] at hf
  rcases hf with ⟨ell, hell, hf⟩
  rcases List.mem_map.mp hf with ⟨q, hq, hformula⟩
  subst f
  have hq' : q = (-1 : Rat) ∨ q = 0 ∨ q = 1 := by simpa using hq
  have hscale := evalAffineInOrientation_scale_small R epsilon .horizontal q
    (triH C code 1 triangularBetaId) x hq'
  have hconj := hF
  change (_ ∧ _) at hconj
  have hL := hconj.1
  have hR := hconj.2
  simp only [formulaHoldsInOrientation] at hL hR
  rw [evalAffineInOrientation_add, hscale, hleft ell, hβ, hpx] at hL
  rw [evalAffineInOrientation_add, hscale, hright ell, hβ, hpx] at hR
  rcases hq' with hq' | hq' | hq'
  · rw [hq'] at hL hR
    exact ⟨ell, -1, by simp, by simpa using hL, by simpa using hR⟩
  · rw [hq'] at hL hR
    exact ⟨ell, 0, by simp, by simpa using hL, by simpa using hR⟩
  · rw [hq'] at hL hR
    exact ⟨ell, 1, by simp, by simpa using hL, by simpa using hR⟩

private theorem triangularBaseOpen_realize {C} (R : Realization C)
    (epsilon : Bool) (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (x : Fin (triangularHorizontalVariableCount code + 1) → Real)
    {w : Nat} (y : Fin w → Real) (p : Tiling.Plane)
    (ell : Fin (triangularPiece code j).intervalCount) (q : Int)
    (hq : q ∈ ([-1, 0, 1] : List Int))
    (hL : X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re)
    (hR : p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta)
    (hβ : evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 triangularBetaId) x = X.beta)
    (hpx : evalAffineInOrientation R epsilon .horizontal
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x = p.re)
    (hleft : evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩)) x =
          X.intervalLeft ⟨j, ell⟩)
    (hright : evalAffineInOrientation R epsilon .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩)) x =
          X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R epsilon
      (triangularBaseOpenFormula C code 1 j
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0)) x y := by
  simp only [triangularBaseOpenFormula]
  apply (formulaHolds_orList R epsilon _ x y).2
  have hqRat : (q : Rat) ∈ (do
      let a ← ([-1, 0, 1] : List Int)
      pure (a : Rat)) := by
    have hq' : q = -1 ∨ q = 0 ∨ q = 1 := by simpa using hq
    rcases hq' with rfl | rfl | rfl <;> simp
  refine ⟨(Formula.horizontalLt
        (Expr.add (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
          (Expr.scale q (triH C code 1 triangularBetaId)))
        (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
      (Formula.horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
        (Expr.add (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
          (Expr.scale q (triH C code 1 triangularBetaId)))), ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    refine ⟨ell, List.mem_ofFn.mpr ⟨ell, rfl⟩, ?_⟩
    apply List.mem_map.mpr
    exact ⟨(q : Rat), hqRat, rfl⟩
  · change
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.add (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
            (Expr.scale q (triH C code 1 triangularBetaId))) x <
        evalAffineInOrientation R epsilon .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x) ∧
      (evalAffineInOrientation R epsilon .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0) x <
        evalAffineInOrientation R epsilon .horizontal
          (Expr.add (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
            (Expr.scale q (triH C code 1 triangularBetaId))) x)
    constructor
    · rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int,
        hleft, hβ, hpx]
      exact hL
    · rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int,
        hright, hβ, hpx]
      exact hR

private theorem triangular_coverage_semantic_bridge {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (j : Fin (triangularPieceCount code))
    (x0 : Fin (triangularHorizontalVariableCount code) → Real)
    (y0 : Fin (triangularVerticalVariableCount code) → Real)
    (hcoverage : formulaHoldsInOrientation R code.orientation
      (Formula.forallHorizontal (Formula.forallVertical
        (triangularCoverageInnerFormula C code j))) x0 y0)
    (hcx : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) (Fin.cons p.re x0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) (Fin.cons p.im y0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ (p : Tiling.Plane), evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 triangularBetaId) (Fin.cons p.re x0) = X.beta)
    (hα : ∀ (p : Tiling.Plane), evalAffineInOrientation R code.orientation .vertical
        (triV C code 1 triangularAlphaId) (Fin.cons p.im y0) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) ell, evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) ell, evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalRight ⟨j, ell⟩) :
    ∀ p, 0 < p.re → p.re < X.beta → 0 < p.im → p.im < X.alpha →
      (∃ ell q, q ∈ ([-1, 0, 1] : List Int) ∧
        X.intervalLeft ⟨j, ell⟩ + q * X.beta < p.re ∧
        p.re < X.intervalRight ⟨j, ell⟩ + q * X.beta) →
      ∃ i ∈ triangularFiniteIndices code j, ∃ e,
        semanticClosedCell R code.orientation e
          (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
            (centeredInteger i.2.2)) p := by
  intro p hp0 hpβ hpI0 hpα hbase
  rcases hbase with ⟨ell, q, hq, hL, hR⟩
  let hx : Fin (triangularHorizontalVariableCount code + 1) → Real := Fin.cons p.re x0
  let hy : Fin (triangularVerticalVariableCount code + 1) → Real := Fin.cons p.im y0
  have hpx : evalAffineInOrientation R code.orientation .horizontal
      (Expr.var C _ 0) hx = p.re := by
    rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
      (Nat.zero_lt_succ _)]
    simp [hx]
  have hpy : evalAffineInOrientation R code.orientation .vertical
      (Expr.var C _ 0) hy = p.im := by
    rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
      (Nat.zero_lt_succ _)]
    simp [hy]
  have hH : ∀ t : Real, formulaHoldsInOrientation R code.orientation
      (Formula.forallVertical (triangularCoverageInnerFormula C code j))
      (Fin.cons t x0) y0 := by
    simpa [Formula.forallHorizontal, formulaHoldsInOrientation] using hcoverage
  have hV : ∀ t : Real, formulaHoldsInOrientation R code.orientation
      (triangularCoverageInnerFormula C code j) (Fin.cons p.re x0)
      (Fin.cons t y0) := by
    simpa [Formula.forallVertical, formulaHoldsInOrientation] using hH p.re
  have hImp := hV p.im
  have hbaseFormula := triangularBaseOpen_realize R code.orientation code X j hx hy p
    ell q hq hL hR
    (by simpa [hx] using hβ p) hpx
    (by simpa [hx] using hleft p ell)
    (by simpa [hx] using hright p ell)
  have hAnte : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        [.horizontalLt (Expr.zero C _) (Expr.var C _ 0),
         .horizontalLt (Expr.var C _ 0) (triH C code 1 triangularBetaId),
         .verticalLt (Expr.zero C _) (Expr.var C _ 0),
         .verticalLt (Expr.var C _ 0) (triV C code 1 triangularAlphaId),
         triangularBaseOpenFormula C code 1 j (Expr.var C _ 0)]) hx hy := by
    apply (formulaHolds_andList R code.orientation _ hx hy).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_zero,
        evalAffineInOrientation_var, hx] using hp0
    · change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ 0) hx <
        evalAffineInOrientation R code.orientation .horizontal
          (triH C code 1 triangularBetaId) hx
      rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
        (Nat.zero_lt_succ _), hβ p]
      exact hpβ
    · simpa [formulaHoldsInOrientation, evalAffineInOrientation_zero,
        evalAffineInOrientation_var, hy] using hpI0
    · change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ 0) hy <
        evalAffineInOrientation R code.orientation .vertical
          (triV C code 1 triangularAlphaId) hy
      rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
        (Nat.zero_lt_succ _), hα p]
      exact hpα
    · exact hbaseFormula
  have hcovered := hImp
  simp only [triangularCoverageInnerFormula, Formula.implication,
    formulaHoldsInOrientation] at hcovered
  have hcovered := hcovered.resolve_left (fun hnot => hnot hAnte)
  rcases (formulaHolds_orList R code.orientation _ hx hy).mp hcovered with
    ⟨f, hf, hF⟩
  simp only [List.mem_flatMap] at hf
  rcases hf with ⟨i, hi, hf⟩
  rcases List.mem_map.mp hf with ⟨e, he, rfl⟩
  refine ⟨i, hi, e, ?_⟩
  exact (formulaHolds_closedCell_semantic_iff R code.orientation e
    (triangularCentreX C code 1 j i) (triangularCentreY C code 1 j i)
    hx hy
    (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
      (centeredInteger i.2.2)) p (hcx p i) (hcy p i) hpx hpy).mp hF

private theorem triangular_forward_coverage_formula : ∀ {C} (R : Realization C) code
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real),
    formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y →
      ∀ j, formulaHoldsInOrientation R code.orientation
        (Formula.forallHorizontal (Formula.forallVertical
          (triangularCoverageInnerFormula C code j))) x y := by
  intro C R code y x hbody
  have hall := (formulaHolds_andList R code.orientation _ x y).mp (by
    simpa only [triangularBody] using hbody)
  let pieces : List (Fin (triangularPieceCount code)) := List.ofFn fun j => j
  let coverageFormula := Formula.andList (pieces.map fun j =>
    Formula.forallHorizontal (Formula.forallVertical
      (triangularCoverageInnerFormula C code j)))
  have hcoverage := hall coverageFormula (by
    dsimp [coverageFormula, pieces, triangularCoverageInnerFormula]
    simp [List.mem_append])
  have hcoverage' := (formulaHolds_andList R code.orientation _ x y).mp hcoverage
  intro j
  exact hcoverage' _ (by
    dsimp [coverageFormula, pieces]
    exact List.mem_map.mpr ⟨j, List.mem_ofFn.mpr ⟨j, rfl⟩, rfl⟩)

private def triangularParametersFromWitness (code : RawTriangularCode)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real) :
    TriangularRawParameters code :=
  let hids := triangular_variable_ids_lt code
  { alpha := y ⟨triangularAlphaId, hids.2.2.2.1⟩
    beta := x ⟨triangularBetaId, hids.1⟩
    shear := fun j => y ⟨triangularShearId j.val, hids.2.2.2.2.1 j⟩
    intervalLeft := fun i => x ⟨triangularIntervalLeftId code i, (hids.2.1 i).1⟩
    intervalRight := fun i => x ⟨triangularIntervalRightId code i, (hids.2.1 i).2⟩
    representativeX := fun i => x ⟨triangularRepresentativeXId code i, hids.2.2.1 i⟩
    representativeY := fun i => y ⟨triangularRepresentativeYId code i, hids.2.2.2.2.2 i⟩ }

private theorem triangular_forward_period_shear_intervals : ∀ {C} (R : Realization C) code
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real),
    formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y →
    ∃ X : TriangularRawParameters code,
      X = triangularParametersFromWitness code y x ∧
      0 < X.alpha ∧ 0 < X.beta ∧
      (∀ j, 0 ≤ X.shear j ∧ X.shear j < X.alpha) ∧
      (∀ i, 0 ≤ X.intervalLeft i ∧ X.intervalLeft i < X.intervalRight i ∧
        X.intervalRight i ≤ X.beta) ∧
      (∀ i i', i ≠ i' →
        X.intervalRight i ≤ X.intervalLeft i' ∨
          X.intervalRight i' ≤ X.intervalLeft i) ∧
      (∀ z, 0 < z → z < X.beta →
        ∃ i, X.intervalLeft i ≤ z ∧ z ≤ X.intervalRight i) ∧
      (∀ i, (0 ≤ X.representativeX i ∧ X.representativeX i < X.beta) ∧
        (0 ≤ X.representativeY i ∧ X.representativeY i < X.alpha)) := by
  intro C R code y x hbody
  have hbody' := hbody
  simp only [triangularBody] at hbody'
  have hall := (formulaHolds_andList R code.orientation _ x y).mp hbody'
  have hids := triangular_variable_ids_lt code
  have hβ : triangularBetaId < triangularHorizontalVariableCount code := hids.1
  have hIL : ∀ i, triangularIntervalLeftId code i <
      triangularHorizontalVariableCount code := fun i => (hids.2.1 i).1
  have hIR : ∀ i, triangularIntervalRightId code i <
      triangularHorizontalVariableCount code := fun i => (hids.2.1 i).2
  have hRX : ∀ i, triangularRepresentativeXId code i <
      triangularHorizontalVariableCount code := hids.2.2.1
  have hα : triangularAlphaId < triangularVerticalVariableCount code := hids.2.2.2.1
  have hSJ : ∀ (j : Fin (triangularPieceCount code)), triangularShearId j.val <
      triangularVerticalVariableCount code := hids.2.2.2.2.1
  have hRY : ∀ i, triangularRepresentativeYId code i <
      triangularVerticalVariableCount code := hids.2.2.2.2.2
  let X : TriangularRawParameters code :=
    { alpha := y ⟨triangularAlphaId, hα⟩
      beta := x ⟨triangularBetaId, hβ⟩
      shear := fun j => y ⟨triangularShearId j.val, hSJ j⟩
      intervalLeft := fun i => x ⟨triangularIntervalLeftId code i, hIL i⟩
      intervalRight := fun i => x ⟨triangularIntervalRightId code i, hIR i⟩
      representativeX := fun i => x ⟨triangularRepresentativeXId code i, hRX i⟩
      representativeY := fun i => y ⟨triangularRepresentativeYId code i, hRY i⟩ }
  refine ⟨X, ?_, ?_⟩
  · rfl
  dsimp [X]
  have hpos := hall
      ((Formula.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code))
        (triH C code 0 triangularBetaId)).conjunction
        (Formula.verticalLt (Expr.zero C (triangularVerticalVariableCount code))
          (triV C code 0 triangularAlphaId))) (by
    simp)
  change
    evalAffineInOrientation R code.orientation .horizontal
        (Expr.zero C (triangularHorizontalVariableCount code)) x <
      evalAffineInOrientation R code.orientation .horizontal
        (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId) x ∧
    evalAffineInOrientation R code.orientation .vertical
        (Expr.zero C (triangularVerticalVariableCount code)) y <
      evalAffineInOrientation R code.orientation .vertical
        (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId) y at hpos
  rw [evalAffineInOrientation_zero, evalAffineInOrientation_var R code.orientation
        .horizontal x triangularBetaId hβ,
      evalAffineInOrientation_zero, evalAffineInOrientation_var R code.orientation
        .vertical y triangularAlphaId hα] at hpos
  have hpos' :
      0 < y ⟨triangularAlphaId, hα⟩ ∧
      0 < x ⟨triangularBetaId, hβ⟩ := by
    exact ⟨hpos.2, hpos.1⟩
  have hshear : ∀ j, 0 ≤ y ⟨triangularShearId j.val, hSJ j⟩ ∧
      y ⟨triangularShearId j.val, hSJ j⟩ < y ⟨triangularAlphaId, hα⟩ := by
    intro j
    have hj := hall
        (Formula.andList
          [Formula.verticalLe (Expr.zero C (triangularVerticalVariableCount code))
              (triV C code 0 (triangularShearId j.val)),
           Formula.verticalLt (triV C code 0 (triangularShearId j.val))
              (triV C code 0 triangularAlphaId)]) (by simp)
    have hj' := (formulaHolds_andList R code.orientation _ x y).mp hj
    have hj0 := hj'
        (Formula.verticalLe (Expr.zero C (triangularVerticalVariableCount code))
          (triV C code 0 (triangularShearId j.val))) (by simp)
    have hj1 := hj'
        (Formula.verticalLt (triV C code 0 (triangularShearId j.val))
          (triV C code 0 triangularAlphaId)) (by simp)
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.zero C (triangularVerticalVariableCount code)) y ≤
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code) (triangularShearId j.val)) y at hj0
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code) (triangularShearId j.val)) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId) y at hj1
    rw [evalAffineInOrientation_zero,
      evalAffineInOrientation_var R code.orientation .vertical y
        (triangularShearId j.val) (hSJ j)] at hj0
    rw [evalAffineInOrientation_var R code.orientation .vertical y
        (triangularShearId j.val) (hSJ j),
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hj1
    exact ⟨hj0, hj1⟩
  have hinterval : ∀ i,
      0 ≤ x ⟨triangularIntervalLeftId code i, hIL i⟩ ∧
      x ⟨triangularIntervalLeftId code i, hIL i⟩ <
        x ⟨triangularIntervalRightId code i, hIR i⟩ ∧
      x ⟨triangularIntervalRightId code i, hIR i⟩ ≤
        x ⟨triangularBetaId, hβ⟩ := by
    intro i
    have hi := hall
        (Formula.andList
          [Formula.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
              (triH C code 0 (triangularIntervalLeftId code i)),
           Formula.horizontalLt (triH C code 0 (triangularIntervalLeftId code i))
              (triH C code 0 (triangularIntervalRightId code i)),
           Formula.horizontalLe (triH C code 0 (triangularIntervalRightId code i))
              (triH C code 0 triangularBetaId)]) (by
          simp [mem_triangularIntervalIndices])
    have hi' := (formulaHolds_andList R code.orientation _ x y).mp hi
    have hi0 := hi'
        (Formula.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
          (triH C code 0 (triangularIntervalLeftId code i))) (by simp)
    have hi1 := hi'
        (Formula.horizontalLt (triH C code 0 (triangularIntervalLeftId code i))
          (triH C code 0 (triangularIntervalRightId code i))) (by simp)
    have hi2 := hi'
        (Formula.horizontalLe (triH C code 0 (triangularIntervalRightId code i))
          (triH C code 0 triangularBetaId)) (by simp)
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.zero C (triangularHorizontalVariableCount code)) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalLeftId code i)) x at hi0
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalLeftId code i)) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalRightId code i)) x at hi1
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalRightId code i)) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId) x at hi2
    rw [evalAffineInOrientation_zero,
      evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularIntervalLeftId code i) (hIL i)] at hi0
    rw [evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularIntervalLeftId code i) (hIL i),
      evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularIntervalRightId code i) (hIR i)] at hi1
    rw [evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularIntervalRightId code i) (hIR i),
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hi2
    exact ⟨hi0, hi1, hi2⟩
  have hdisjoint : ∀ i i', i ≠ i' →
      x ⟨triangularIntervalRightId code i, hIR i⟩ ≤
          x ⟨triangularIntervalLeftId code i', hIL i'⟩ ∨
        x ⟨triangularIntervalRightId code i', hIR i'⟩ ≤
          x ⟨triangularIntervalLeftId code i, hIL i⟩ := by
    intro i i' hne
    have hd := hall
        (Formula.disjunction
          (Formula.horizontalLe (triH C code 0 (triangularIntervalRightId code i))
            (triH C code 0 (triangularIntervalLeftId code i'))
          )
          (Formula.horizontalLe (triH C code 0 (triangularIntervalRightId code i'))
            (triH C code 0 (triangularIntervalLeftId code i)))) (by
          have hi_mem := mem_triangularIntervalIndices code i
          have hi'_mem := mem_triangularIntervalIndices code i'
          simp only [List.mem_append]
          apply Or.inl
          apply Or.inr
          apply List.mem_flatMap.mpr
          refine ⟨i, hi_mem, ?_⟩
          apply List.mem_map.mpr
          refine ⟨i', hi'_mem, ?_⟩
          simp [hne])
    change
      (evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalRightId code i)) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalLeftId code i')) x) ∨
      (evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalRightId code i')) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularIntervalLeftId code i)) x) at hd
    rw [evalAffineInOrientation_var R code.orientation .horizontal x
          (triangularIntervalRightId code i) (hIR i),
      evalAffineInOrientation_var R code.orientation .horizontal x
          (triangularIntervalLeftId code i') (hIL i'),
      evalAffineInOrientation_var R code.orientation .horizontal x
          (triangularIntervalRightId code i') (hIR i'),
      evalAffineInOrientation_var R code.orientation .horizontal x
          (triangularIntervalLeftId code i) (hIL i)] at hd
    exact hd
  have hcoverage : ∀ z, 0 < z → z < x ⟨triangularBetaId, hβ⟩ →
      ∃ i, x ⟨triangularIntervalLeftId code i, hIL i⟩ ≤ z ∧
        z ≤ x ⟨triangularIntervalRightId code i, hIR i⟩ := by
    intro z hz0 hzb
    let partitionInner : Formula C (triangularHorizontalVariableCount code + 1)
        (triangularVerticalVariableCount code) := Formula.implication
            (Formula.andList
              [Formula.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
                  (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
               Formula.horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
                  (triH C code 1 triangularBetaId)])
            (Formula.orList
              (List.map
                (fun i =>
                  (Formula.horizontalLe (triH C code 1 (triangularIntervalLeftId code i))
                      (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
                    (Formula.horizontalLe
                      (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
                      (triH C code 1 (triangularIntervalRightId code i))))
                (triangularIntervalIndices code)))
    let partitionFormula : Formula C (triangularHorizontalVariableCount code)
        (triangularVerticalVariableCount code) := Formula.forallHorizontal partitionInner
    have hp := hall partitionFormula (by
      dsimp [partitionFormula, partitionInner]
      simp [List.mem_append])
    have hp' : ∀ t : Real,
        formulaHoldsInOrientation R code.orientation partitionInner (Fin.cons t x) y := by
      simpa [partitionFormula, Formula.forallHorizontal, formulaHoldsInOrientation] using hp
    have hz' := hp' z
    change
      (¬ formulaHoldsInOrientation R code.orientation
          (Formula.andList
            [Formula.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
                (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
             Formula.horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
                (triH C code 1 triangularBetaId)]) (Fin.cons z x) y ∨
       formulaHoldsInOrientation R code.orientation
          (Formula.orList
            (List.map
              (fun i =>
                (Formula.horizontalLe (triH C code 1 (triangularIntervalLeftId code i))
                    (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
                  (Formula.horizontalLe (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
                    (triH C code 1 (triangularIntervalRightId code i))))
              (triangularIntervalIndices code))) (Fin.cons z x) y) at hz'
    have hdom : formulaHoldsInOrientation R code.orientation
        (Formula.andList
          [Formula.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
              (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
           Formula.horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
              (triH C code 1 triangularBetaId)]) (Fin.cons z x) y := by
      apply (formulaHolds_andList R code.orientation _ (Fin.cons z x) y).2
      intro p hp_mem
      simp only [List.mem_cons] at hp_mem
      rcases hp_mem with rfl | hp_mem
      · change
          evalAffineInOrientation R code.orientation .horizontal
              (Expr.zero C (triangularHorizontalVariableCount code + 1))
              (Fin.cons z x) <
            evalAffineInOrientation R code.orientation .horizontal
              (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
              (Fin.cons z x)
        rw [evalAffineInOrientation_zero,
          evalAffineInOrientation_var R code.orientation .horizontal
            (Fin.cons z x) 0 (Nat.zero_lt_succ _)]
        simpa using hz0
      · have hp_mem' : p = Formula.horizontalLt
            (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
              (triH C code 1 triangularBetaId) := by simpa using hp_mem
        rw [hp_mem']
        change
          evalAffineInOrientation R code.orientation .horizontal
              (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (Fin.cons z x) <
            evalAffineInOrientation R code.orientation .horizontal
              (Expr.var C (triangularHorizontalVariableCount code + 1)
                (triangularBetaId + 1))
              (Fin.cons z x)
        rw [evalAffineInOrientation_var R code.orientation .horizontal
              (Fin.cons z x) 0 (Nat.zero_lt_succ _),
          evalAffineInOrientation_var R code.orientation .horizontal
              (Fin.cons z x) (triangularBetaId + 1) (Nat.succ_lt_succ hβ)]
        rw [show (⟨triangularBetaId + 1, Nat.succ_lt_succ hβ⟩ :
            Fin (triangularHorizontalVariableCount code + 1)) =
              Fin.succ ⟨triangularBetaId, hβ⟩ by rfl, Fin.cons_succ]
        exact hzb
    have hor := hz'.resolve_left (fun hnot => hnot hdom)
    have hor' := (formulaHolds_orList R code.orientation _ (Fin.cons z x) y).mp hor
    rcases hor' with ⟨p, hp_mem, hp⟩
    simp only [List.mem_map] at hp_mem
    rcases hp_mem with ⟨i, hi_mem, rfl⟩
    refine ⟨i, ?_⟩
    have hi' := hp
    have hi0 := hi'.1
    have hi1 := hi'.2
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1)
            (triangularIntervalLeftId code i + 1)) (Fin.cons z x) ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (Fin.cons z x) at hi0
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (Fin.cons z x) ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1)
            (triangularIntervalRightId code i + 1)) (Fin.cons z x) at hi1
    rw [evalAffineInOrientation_var R code.orientation .horizontal
          (Fin.cons z x) (triangularIntervalLeftId code i + 1)
            (Nat.succ_lt_succ (hIL i)),
      evalAffineInOrientation_var R code.orientation .horizontal
          (Fin.cons z x) 0 (Nat.zero_lt_succ _)] at hi0
    rw [evalAffineInOrientation_var R code.orientation .horizontal
          (Fin.cons z x) 0 (Nat.zero_lt_succ _),
      evalAffineInOrientation_var R code.orientation .horizontal
          (Fin.cons z x) (triangularIntervalRightId code i + 1)
            (Nat.succ_lt_succ (hIR i))] at hi1
    exact ⟨hi0, hi1⟩
  have hrepresentative : ∀ i,
      (0 ≤ x ⟨triangularRepresentativeXId code i, hRX i⟩ ∧
        x ⟨triangularRepresentativeXId code i, hRX i⟩ <
          x ⟨triangularBetaId, hβ⟩) ∧
      (0 ≤ y ⟨triangularRepresentativeYId code i, hRY i⟩ ∧
        y ⟨triangularRepresentativeYId code i, hRY i⟩ <
          y ⟨triangularAlphaId, hα⟩) := by
    intro i
    have hr := hall
        (Formula.andList
          [Formula.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
              (triH C code 0 (triangularRepresentativeXId code i)),
           Formula.horizontalLt (triH C code 0 (triangularRepresentativeXId code i))
              (triH C code 0 triangularBetaId),
           Formula.verticalLe (Expr.zero C (triangularVerticalVariableCount code))
              (triV C code 0 (triangularRepresentativeYId code i)),
           Formula.verticalLt (triV C code 0 (triangularRepresentativeYId code i))
              (triV C code 0 triangularAlphaId)]) (by
          simp [mem_triangularRepresentativeIndices])
    have hr' := (formulaHolds_andList R code.orientation _ x y).mp hr
    have hr0 := hr'
        (Formula.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
          (triH C code 0 (triangularRepresentativeXId code i))) (by simp)
    have hr1 := hr'
        (Formula.horizontalLt (triH C code 0 (triangularRepresentativeXId code i))
          (triH C code 0 triangularBetaId)) (by simp)
    have hr2 := hr'
        (Formula.verticalLe (Expr.zero C (triangularVerticalVariableCount code))
          (triV C code 0 (triangularRepresentativeYId code i))) (by simp)
    have hr3 := hr'
        (Formula.verticalLt (triV C code 0 (triangularRepresentativeYId code i))
          (triV C code 0 triangularAlphaId)) (by simp)
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.zero C (triangularHorizontalVariableCount code)) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularRepresentativeXId code i)) x at hr0
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code)
            (triangularRepresentativeXId code i)) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId) x at hr1
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.zero C (triangularVerticalVariableCount code)) y ≤
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code)
            (triangularRepresentativeYId code i)) y at hr2
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code)
            (triangularRepresentativeYId code i)) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId) y at hr3
    rw [evalAffineInOrientation_zero,
      evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularRepresentativeXId code i) (hRX i)] at hr0
    rw [evalAffineInOrientation_var R code.orientation .horizontal x
        (triangularRepresentativeXId code i) (hRX i),
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hr1
    rw [evalAffineInOrientation_zero,
      evalAffineInOrientation_var R code.orientation .vertical y
        (triangularRepresentativeYId code i) (hRY i)] at hr2
    rw [evalAffineInOrientation_var R code.orientation .vertical y
        (triangularRepresentativeYId code i) (hRY i),
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hr3
    exact ⟨⟨hr0, hr1⟩, ⟨hr2, hr3⟩⟩
  exact ⟨hpos'.1, hpos'.2, hshear, hinterval, hdisjoint, hcoverage, hrepresentative⟩

/- private theorem triangular_forward_vertex_diameter : ∀ {C} (R : Realization C) code,
    (∃ y x, formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y) →
    ∃ (y : Fin (triangularVerticalVariableCount code) → Real)
      (x : Fin (triangularHorizontalVariableCount code) → Real),
      ((∀ a b, |selectedCoordinate code.orientation .horizontal (R.vertex a) -
        selectedCoordinate code.orientation .horizontal (R.vertex b)| <
          (code.checkingRadius : Real) *
            x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩) ∧
    (∀ a b, |selectedCoordinate code.orientation .vertical (R.vertex a) -
        selectedCoordinate code.orientation .vertical (R.vertex b)| <
          (code.checkingRadius : Real) *
            y ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩)) := by
  intro C R code h
  rcases h with ⟨y, x, hbody⟩
  have hbody' := hbody
  simp only [triangularBody] at hbody'
  have hall := (formulaHolds_andList R code.orientation _ x y).mp hbody'
  have hids := triangular_variable_ids_lt code
  have hβ : triangularBetaId < triangularHorizontalVariableCount code := hids.1
  have hα : triangularAlphaId < triangularVerticalVariableCount code := hids.2.2.2.1
  refine ⟨y, x, ?_⟩
  constructor
  · intro a b
    let p : Formula C (triangularHorizontalVariableCount code)
        (triangularVerticalVariableCount code) :=
      Formula.andList
        [Formula.horizontalLt
            (Expr.input (triangularHorizontalVariableCount code)
              (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
            (Expr.scale (Int.ofNat code.checkingRadius)
              (triH C code 0 triangularBetaId)),
         Formula.horizontalLt
            (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
              (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
            (Expr.scale (Int.ofNat code.checkingRadius)
              (triH C code 0 triangularBetaId))]
    have hp := hall p (by
      dsimp [p]
      simp [List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_ofFn, (List.mem_ofFn.mpr ⟨a, rfl⟩),
        (List.mem_ofFn.mpr ⟨b, rfl⟩)])
    have hp' := (formulaHolds_andList R code.orientation _ x y).mp hp
    have hplus := hp'
      (Formula.horizontalLt
        (Expr.input (triangularHorizontalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triH C code 0 triangularBetaId))) (by simp)
    have hminus := hp'
      (Formula.horizontalLt
        (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triH C code 0 triangularBetaId))) (by simp)
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId)) x at hplus
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId)) x at hminus
    rw [evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hplus
    rw [evalAffineInOrientation_neg,
      evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hminus
    apply (abs_lt).2
    constructor
    · simpa [selectedCoordinate] using hminus
    · simpa [selectedCoordinate] using hplus
  · intro a b
    let p : Formula C (triangularHorizontalVariableCount code)
        (triangularVerticalVariableCount code) :=
      Formula.andList
        [Formula.verticalLt
            (Expr.input (triangularVerticalVariableCount code)
              (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
            (Expr.scale (Int.ofNat code.checkingRadius)
              (triV C code 0 triangularAlphaId)),
         Formula.verticalLt
            (Expr.neg (Expr.input (triangularVerticalVariableCount code)
              (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
            (Expr.scale (Int.ofNat code.checkingRadius)
              (triV C code 0 triangularAlphaId))]
    have hp := hall p (by
      dsimp [p]
      simp [List.mem_append, List.mem_flatMap, List.mem_map,
        List.mem_ofFn, (List.mem_ofFn.mpr ⟨a, rfl⟩),
        (List.mem_ofFn.mpr ⟨b, rfl⟩)])
    have hp' := (formulaHolds_andList R code.orientation _ x y).mp hp
    have hplus := hp'
      (Formula.verticalLt
        (Expr.input (triangularVerticalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triV C code 0 triangularAlphaId))) (by simp)
    have hminus := hp'
      (Formula.verticalLt
        (Expr.neg (Expr.input (triangularVerticalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triV C code 0 triangularAlphaId))) (by simp)
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId)) y at hplus
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.neg (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId)) y at hminus
    rw [evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hplus
    rw [evalAffineInOrientation_neg,
      evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hminus
    apply (abs_lt).2
    constructor
    · simpa [selectedCoordinate] using hminus
    · simpa [selectedCoordinate] using hplus

-/

private theorem triangular_forward_vertex_diameter_nested : ∀ {C} (R : Realization C) code
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real),
    formulaHoldsInOrientation R code.orientation
      (triangularBody C code) x y →
      ((∀ a b, |selectedCoordinate code.orientation .horizontal (R.vertex a) -
          selectedCoordinate code.orientation .horizontal (R.vertex b)| <
            (code.checkingRadius : Real) *
              x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩) ∧
       (∀ a b, |selectedCoordinate code.orientation .vertical (R.vertex a) -
          selectedCoordinate code.orientation .vertical (R.vertex b)| <
            (code.checkingRadius : Real) *
              y ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩)) := by
  intro C R code y x hbody
  have hbody' := hbody
  simp only [triangularBody] at hbody'
  have hall := (formulaHolds_andList R code.orientation _ x y).mp hbody'
  have hids := triangular_variable_ids_lt code
  have hβ : triangularBetaId < triangularHorizontalVariableCount code := hids.1
  have hα : triangularAlphaId < triangularVerticalVariableCount code := hids.2.2.2.1
  let vertices : List (Fin C.vertexCount) := List.ofFn fun i => i
  let diameterFormula : Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) := Formula.andList
    ((vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input (triangularHorizontalVariableCount code)
        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      Formula.andList
        [.horizontalLt d (Expr.scale (Int.ofNat code.checkingRadius)
            (triH C code 0 triangularBetaId)),
         .horizontalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius)
            (triH C code 0 triangularBetaId))]) ++
     (vertices.flatMap fun a => vertices.map fun b =>
      let d := Expr.input (triangularVerticalVariableCount code)
        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
      Formula.andList
        [.verticalLt d (Expr.scale (Int.ofNat code.checkingRadius)
            (triV C code 0 triangularAlphaId)),
         .verticalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius)
            (triV C code 0 triangularAlphaId))]))
  have hdiam := hall diameterFormula (by
    dsimp [diameterFormula, vertices]
    simp [List.mem_append])
  have hdiam' := (formulaHolds_andList R code.orientation _ x y).mp hdiam
  constructor
  · intro a b
    let p : Formula C (triangularHorizontalVariableCount code)
        (triangularVerticalVariableCount code) := Formula.andList
      [Formula.horizontalLt
          (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
          (Expr.scale (Int.ofNat code.checkingRadius)
            (triH C code 0 triangularBetaId)),
       Formula.horizontalLt
          (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
          (Expr.scale (Int.ofNat code.checkingRadius)
            (triH C code 0 triangularBetaId))]
    have hp := hdiam' p (by
      dsimp [p, vertices]
      simp [List.mem_append, List.mem_flatMap])
    have hp' := (formulaHolds_andList R code.orientation _ x y).mp hp
    have hplus := hp'
      (Formula.horizontalLt
        (Expr.input (triangularHorizontalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triH C code 0 triangularBetaId))) (by simp)
    have hminus := hp'
      (Formula.horizontalLt
        (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triH C code 0 triangularBetaId))) (by simp)
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId)) x at hplus
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.neg (Expr.input (triangularHorizontalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularHorizontalVariableCount code) triangularBetaId)) x at hminus
    rw [evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hplus
    rw [evalAffineInOrientation_neg, evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .horizontal x triangularBetaId hβ] at hminus
    have hplus' : selectedCoordinate code.orientation .horizontal (R.vertex a) -
        selectedCoordinate code.orientation .horizontal (R.vertex b) <
          (code.checkingRadius : Real) * x ⟨triangularBetaId, hβ⟩ := by
      simpa [selectedCoordinate] using hplus
    have hminus' : -(selectedCoordinate code.orientation .horizontal (R.vertex a) -
        selectedCoordinate code.orientation .horizontal (R.vertex b)) <
          (code.checkingRadius : Real) * x ⟨triangularBetaId, hβ⟩ := by
      simpa [selectedCoordinate] using hminus
    exact (abs_lt).2 ⟨by linarith, hplus'⟩
  · intro a b
    let p : Formula C (triangularHorizontalVariableCount code)
        (triangularVerticalVariableCount code) := Formula.andList
      [Formula.verticalLt
          (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
          (Expr.scale (Int.ofNat code.checkingRadius)
            (triV C code 0 triangularAlphaId)),
       Formula.verticalLt
          (Expr.neg (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
          (Expr.scale (Int.ofNat code.checkingRadius)
            (triV C code 0 triangularAlphaId))]
    have hp := hdiam' p (by
      dsimp [p, vertices]
      simp [List.mem_append, List.mem_flatMap])
    have hp' := (formulaHolds_andList R code.orientation _ x y).mp hp
    have hplus := hp'
      (Formula.verticalLt
        (Expr.input (triangularVerticalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triV C code 0 triangularAlphaId))) (by simp)
    have hminus := hp'
      (Formula.verticalLt
        (Expr.neg (Expr.input (triangularVerticalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
        (Expr.scale (Int.ofNat code.checkingRadius)
          (triV C code 0 triangularAlphaId))) (by simp)
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId)) y at hplus
    change
      evalAffineInOrientation R code.orientation .vertical
          (Expr.neg (Expr.input (triangularVerticalVariableCount code)
            (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.scale (Int.ofNat code.checkingRadius)
            (Expr.var C (triangularVerticalVariableCount code) triangularAlphaId)) y at hminus
    rw [evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hplus
    rw [evalAffineInOrientation_neg, evalAffineInOrientation_input_single_sub,
      evalAffineInOrientation_scale_int,
      evalAffineInOrientation_var R code.orientation .vertical y triangularAlphaId hα] at hminus
    have hplus' : selectedCoordinate code.orientation .vertical (R.vertex a) -
        selectedCoordinate code.orientation .vertical (R.vertex b) <
          (code.checkingRadius : Real) * y ⟨triangularAlphaId, hα⟩ := by
      simpa [selectedCoordinate] using hplus
    have hminus' : -(selectedCoordinate code.orientation .vertical (R.vertex a) -
        selectedCoordinate code.orientation .vertical (R.vertex b)) <
          (code.checkingRadius : Real) * y ⟨triangularAlphaId, hα⟩ := by
      simpa [selectedCoordinate] using hminus
    exact (abs_lt).2 ⟨by linarith, hplus'⟩

private theorem triangular_witness_evaluators {C} (R : Realization C)
    (code : RawTriangularCode)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (x : Fin (triangularHorizontalVariableCount code) → Real) :
    let X := triangularParametersFromWitness code y x
    (∀ j i, evalAffineInOrientation R code.orientation .horizontal
        (triangularCentreX C code 0 j i) x =
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2)).re) ∧
    (∀ j i, evalAffineInOrientation R code.orientation .vertical
        (triangularCentreY C code 0 j i) y =
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2)).im) ∧
    (∀ (p : Tiling.Plane) j i, evalAffineInOrientation R code.orientation .horizontal
        (triangularCentreX C code 1 j i) (Fin.cons p.re x) =
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2)).re) ∧
    (∀ (p : Tiling.Plane) j i, evalAffineInOrientation R code.orientation .vertical
        (triangularCentreY C code 1 j i) (Fin.cons p.im y) =
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2)).im) ∧
    (∀ (p : Tiling.Plane), evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 triangularBetaId) (Fin.cons p.re x) = X.beta) ∧
    (∀ (p : Tiling.Plane), evalAffineInOrientation R code.orientation .vertical
        (triV C code 1 triangularAlphaId) (Fin.cons p.im y) = X.alpha) ∧
    (∀ (p : Tiling.Plane) j ell, evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalLeft ⟨j, ell⟩) ∧
    (∀ (p : Tiling.Plane) j ell, evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalRight ⟨j, ell⟩) := by
  dsimp
  let hids := triangular_variable_ids_lt code
  have hβ := hids.1
  have hα := hids.2.2.2.1
  have hRX : ∀ i : TriangularRepresentativeIndex code,
      triangularRepresentativeXId code i < triangularHorizontalVariableCount code :=
    hids.2.2.1
  have hRY : ∀ i : TriangularRepresentativeIndex code,
      triangularRepresentativeYId code i < triangularVerticalVariableCount code :=
    hids.2.2.2.2.2
  have hS : ∀ j : Fin (triangularPieceCount code),
      triangularShearId j.val < triangularVerticalVariableCount code :=
    hids.2.2.2.2.1
  have hIL : ∀ i : TriangularIntervalIndex code,
      triangularIntervalLeftId code i < triangularHorizontalVariableCount code :=
    fun i => (hids.2.1 i).1
  have hIR : ∀ i : TriangularIntervalIndex code,
      triangularIntervalRightId code i < triangularHorizontalVariableCount code :=
    fun i => (hids.2.1 i).2
  have hvarH : ∀ (z : Real) id (hid : id < triangularHorizontalVariableCount code),
      evalAffineInOrientation R code.orientation .horizontal
        (Expr.var C (triangularHorizontalVariableCount code + 1) (id + 1))
        (Fin.cons z x) = x ⟨id, hid⟩ := by
    intro z id hid
    rw [evalAffineInOrientation_var R code.orientation .horizontal (Fin.cons z x)
      (id + 1) (Nat.succ_lt_succ hid)]
    rfl
  have hvarV : ∀ (z : Real) id (hid : id < triangularVerticalVariableCount code),
      evalAffineInOrientation R code.orientation .vertical
        (Expr.var C (triangularVerticalVariableCount code + 1) (id + 1))
        (Fin.cons z y) = y ⟨id, hid⟩ := by
    intro z id hid
    rw [evalAffineInOrientation_var R code.orientation .vertical (Fin.cons z y)
      (id + 1) (Nat.succ_lt_succ hid)]
    rfl
  constructor
  · intro j i
    rw [eval_triangularCentreX R code.orientation code x j i (hRX ⟨j, i.1⟩) hβ]
    simp [triangularParametersFromWitness, triangularSemanticCentre]
  constructor
  · intro j i
    rw [eval_triangularCentreY R code.orientation code y j i (hRY ⟨j, i.1⟩)
      (hS j) hα]
    simp [triangularParametersFromWitness, triangularSemanticCentre]
  constructor
  · intro p j i
    unfold triangularCentreX
    rw [evalAffineInOrientation_add, evalAffineInOrientation_scale_int]
    change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C (triangularHorizontalVariableCount code + 1)
            (triangularRepresentativeXId code ⟨j, i.1⟩ + 1)) (Fin.cons p.re x) +
        (centeredInteger i.2.1 : Real) *
          evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C (triangularHorizontalVariableCount code + 1)
              (triangularBetaId + 1)) (Fin.cons p.re x) = _
    rw [hvarH p.re _ (hRX ⟨j, i.1⟩), hvarH p.re _ hβ]
    simp [triangularParametersFromWitness, triangularSemanticCentre]
  constructor
  · intro p j i
    unfold triangularCentreY
    rw [evalAffineInOrientation_add, evalAffineInOrientation_add,
      evalAffineInOrientation_scale_int, evalAffineInOrientation_scale_int]
    change
      (evalAffineInOrientation R code.orientation .vertical
          (Expr.var C (triangularVerticalVariableCount code + 1)
            (triangularRepresentativeYId code ⟨j, i.1⟩ + 1)) (Fin.cons p.im y) +
        (centeredInteger i.2.1 : Real) *
          evalAffineInOrientation R code.orientation .vertical
            (Expr.var C (triangularVerticalVariableCount code + 1)
              (triangularShearId j.val + 1)) (Fin.cons p.im y)) +
        (centeredInteger i.2.2 : Real) *
          evalAffineInOrientation R code.orientation .vertical
            (Expr.var C (triangularVerticalVariableCount code + 1)
              (triangularAlphaId + 1)) (Fin.cons p.im y) = _
    rw [hvarV p.im _ (hRY ⟨j, i.1⟩), hvarV p.im _ (hS j), hvarV p.im _ hα]
    simp [triangularParametersFromWitness, triangularSemanticCentre]
  constructor
  · intro p
    rw [show triH C code 1 triangularBetaId =
      Expr.var C (triangularHorizontalVariableCount code + 1)
        (triangularBetaId + 1) by rfl]
    exact hvarH p.re _ hβ
  constructor
  · intro p
    rw [show triV C code 1 triangularAlphaId =
      Expr.var C (triangularVerticalVariableCount code + 1)
        (triangularAlphaId + 1) by rfl]
    exact hvarV p.im _ hα
  constructor
  · intro p j ell
    rw [show triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩) =
      Expr.var C (triangularHorizontalVariableCount code + 1)
        (triangularIntervalLeftId code ⟨j, ell⟩ + 1) by rfl]
    exact hvarH p.re _ (hIL ⟨j, ell⟩)
  · intro p j ell
    rw [show triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩) =
      Expr.var C (triangularHorizontalVariableCount code + 1)
        (triangularIntervalRightId code ⟨j, ell⟩ + 1) by rfl]
    exact hvarH p.re _ (hIR ⟨j, ell⟩)

private theorem triangularFormula_forward : ∀ {C} (R : Realization C) code,
    code.wellFormed = true →
    formulaHoldsInOrientation R code.orientation
      (triangularSlabFormula C code) Fin.elim0 Fin.elim0 →
    ∃ X : TriangularRawParameters code, TriangularChecks R code X := by
  intro C R code hcode hslab
  have hbodyClosed : formulaHoldsInOrientation R code.orientation
      (Formula.close (triangularBody C code)) Fin.elim0 Fin.elim0 := by
    simpa [triangularSlabFormula, hcode] using hslab
  rw [Formula.close] at hbodyClosed
  rcases (formulaHolds_closeVertical R code.orientation
    (triangularVerticalVariableCount code)
    (Formula.closeHorizontal (triangularHorizontalVariableCount code)
      (triangularBody C code))).mp hbodyClosed with ⟨y, hy⟩
  rw [formulaHolds_closeHorizontal] at hy
  rcases hy with ⟨x, hbody⟩
  rcases triangular_forward_period_shear_intervals R code y x hbody with
    ⟨X, hX, hperiods⟩
  subst X
  let X : TriangularRawParameters code := triangularParametersFromWitness code y x
  have heval := triangular_witness_evaluators R code y x
  dsimp [X] at heval
  rcases heval with ⟨hcx, hcy, hcxShift, hcyShift, hβ, hα, hleft, hright⟩
  have hdiam := triangular_forward_vertex_diameter_nested R code y x hbody
  have hpack := triangular_forward_packing_formula R code y x hbody
  have hleak := triangular_forward_leakage_formula R code y x hbody
  have hcoverage := triangular_forward_coverage_formula R code y x hbody
  refine ⟨X, ?_⟩
  refine
    { periods_pos := ⟨hperiods.1, hperiods.2.1⟩
      shear_normalized := hperiods.2.2.1
      intervals_normalized := hperiods.2.2.2.1
      interval_interiors_disjoint := hperiods.2.2.2.2.1
      base_period_covered := hperiods.2.2.2.2.2.1
      representatives_normalized := hperiods.2.2.2.2.2.2
      vertex_diameter_bounds := hdiam
      finite_packing := triangular_packing_semantic_bridge R code X y x hpack
        (fun j i => by simpa [X] using hcx j i)
        (fun j i => by simpa [X] using hcy j i)
      no_leakage := ?_
      finite_coverage := ?_ }
  · intro j p hp0 hpβ hpI0 hpα hhit
    exact triangular_no_leakage_semantic_bridge R code X j x y (hleak j)
      (fun p i => by simpa [X] using hcxShift p j i)
      (fun p i => by simpa [X] using hcyShift p j i)
      (fun p => by simpa [X] using hβ p) (fun p => by simpa [X] using hα p)
      (fun p ell => by simpa [X] using hleft p j ell)
      (fun p ell => by simpa [X] using hright p j ell) p hp0 hpβ hpI0 hpα hhit
  · intro j p hp0 hpβ hpI0 hpα hbase
    exact triangular_coverage_semantic_bridge R code X j x y (hcoverage j)
      (fun p i => by simpa [X] using hcxShift p j i)
      (fun p i => by simpa [X] using hcyShift p j i)
      (fun p => by simpa [X] using hβ p) (fun p => by simpa [X] using hα p)
      (fun p ell => by simpa [X] using hleft p j ell)
      (fun p ell => by simpa [X] using hright p j ell) p hp0 hpβ hpI0 hpα hbase

private theorem test_mapped_ordinal_lt_of_lt_local :
    ∀ (pieces : List RawTriangularPieceCode) (f : RawTriangularPieceCode → Nat)
      (j k : Fin pieces.length) (n m : Nat),
      n < f (pieces.get j) → m < f (pieces.get k) → j < k →
      (pieces.take j.val |>.map f).sum + n <
        (pieces.take k.val |>.map f).sum + m := by
  intro pieces
  induction pieces with
  | nil => intro f j; exact Fin.elim0 j
  | cons a as ih =>
      intro f j k n m hn hm hjk
      revert hn hm hjk
      refine Fin.cases ?_ ?_ j
      · intro hn hm hjk
        revert hm hjk
        refine Fin.cases ?_ ?_ k
        · intro hm hjk
          omega
        · intro l hm hjk
          change n < f a at hn
          change m < f (as.get l) at hm
          change (0 : Nat) < (Fin.succ l).val at hjk
          simp at ⊢
          omega
      · intro l hn hm hjk
        revert hm hjk
        refine Fin.cases ?_ ?_ k
        · intro hm hjk
          change n < f (as.get l) at hn
          change m < f a at hm
          change (Fin.succ l).val < (0 : Nat) at hjk
          simp at ⊢
          omega
        · intro q hm hjk
          change n < f (as.get l) at hn
          change m < f (as.get q) at hm
          have hjk' : l < q := Nat.lt_of_succ_lt_succ hjk
          simp [List.map_take] at ⊢
          have htail := ih f l q n m hn hm hjk'
          simp only [List.map_take] at htail
          omega

private theorem triangular_interval_ordinal_injective_local : ∀ code,
    Function.Injective (triangularIntervalOrdinal code) := by
  intro code i i' h
  rcases i with ⟨j, n⟩
  rcases i' with ⟨j', n'⟩
  unfold triangularIntervalOrdinal at h
  have hnot : ¬ j < j' := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt_local code.pieces
      RawTriangularPieceCode.intervalCount j j' n.val n'.val n.isLt n'.isLt hij
    exact (Nat.ne_of_lt hord) h
  have hnot' : ¬ j' < j := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt_local code.pieces
      RawTriangularPieceCode.intervalCount j' j n'.val n.val n'.isLt n.isLt hij
    exact (Nat.ne_of_lt hord) h.symm
  have hfirst : j = j' := by
    apply Fin.ext
    omega
  cases hfirst
  simp at h
  congr
  apply Fin.ext
  omega

private theorem triangular_representative_ordinal_injective_local : ∀ code,
    Function.Injective (triangularRepresentativeOrdinal code) := by
  intro code i i' h
  rcases i with ⟨j, n⟩
  rcases i' with ⟨j', n'⟩
  unfold triangularRepresentativeOrdinal at h
  have hnot : ¬ j < j' := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt_local code.pieces
      RawTriangularPieceCode.representativeCount j j' n.val n'.val n.isLt n'.isLt hij
    exact (Nat.ne_of_lt hord) h
  have hnot' : ¬ j' < j := by
    intro hij
    have hord := test_mapped_ordinal_lt_of_lt_local code.pieces
      RawTriangularPieceCode.representativeCount j' j n'.val n.val n'.isLt n.isLt hij
    exact (Nat.ne_of_lt hord) h.symm
  have hfirst : j = j' := by
    apply Fin.ext
    omega
  cases hfirst
  simp at h
  congr
  apply Fin.ext
  omega

private theorem triangular_interval_left_id_injective {code : RawTriangularCode}
    {i i' : TriangularIntervalIndex code}
    (h : triangularIntervalLeftId code i = triangularIntervalLeftId code i') : i = i' := by
  apply triangular_interval_ordinal_injective_local code
  dsimp [triangularIntervalLeftId] at h
  omega

private theorem triangular_interval_right_id_injective {code : RawTriangularCode}
    {i i' : TriangularIntervalIndex code}
    (h : triangularIntervalRightId code i = triangularIntervalRightId code i') : i = i' := by
  apply triangular_interval_ordinal_injective_local code
  dsimp [triangularIntervalRightId] at h
  omega

private theorem triangular_representative_x_id_injective {code : RawTriangularCode}
    {i i' : TriangularRepresentativeIndex code}
    (h : triangularRepresentativeXId code i = triangularRepresentativeXId code i') : i = i' := by
  apply triangular_representative_ordinal_injective_local code
  dsimp [triangularRepresentativeXId] at h
  omega

private theorem triangular_representative_y_id_injective {code : RawTriangularCode}
    {i i' : TriangularRepresentativeIndex code}
    (h : triangularRepresentativeYId code i = triangularRepresentativeYId code i') : i = i' := by
  apply triangular_representative_ordinal_injective_local code
  dsimp [triangularRepresentativeYId] at h
  omega

private noncomputable def triangularReverseHorizontal (code : RawTriangularCode)
    (X : TriangularRawParameters code)
    (i : Fin (triangularHorizontalVariableCount code)) : Real :=
  if i.val = triangularBetaId then X.beta else
  if h : ∃ k : TriangularIntervalIndex code,
      i.val = triangularIntervalLeftId code k then
    X.intervalLeft (Classical.choose h)
  else if h : ∃ k : TriangularIntervalIndex code,
      i.val = triangularIntervalRightId code k then
    X.intervalRight (Classical.choose h)
  else if h : ∃ k : TriangularRepresentativeIndex code,
      i.val = triangularRepresentativeXId code k then
    X.representativeX (Classical.choose h)
  else 0

private noncomputable def triangularReverseVertical (code : RawTriangularCode)
    (X : TriangularRawParameters code)
    (i : Fin (triangularVerticalVariableCount code)) : Real :=
  if i.val = triangularAlphaId then X.alpha else
  if h : ∃ j : Fin (triangularPieceCount code),
      i.val = triangularShearId j.val then
    X.shear ⟨(Classical.choose h).val, (Classical.choose h).isLt⟩
  else if h : ∃ k : TriangularRepresentativeIndex code,
      i.val = triangularRepresentativeYId code k then
    X.representativeY (Classical.choose h)
  else 0

private theorem triangularReverseHorizontal_lookup_beta (code : RawTriangularCode)
    (X : TriangularRawParameters code) :
    triangularReverseHorizontal code X
      ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ = X.beta := by
  simp [triangularReverseHorizontal, triangularBetaId]

private theorem triangularReverseHorizontal_lookup_left (code : RawTriangularCode)
    (X : TriangularRawParameters code) (i : TriangularIntervalIndex code) :
    triangularReverseHorizontal code X
      ⟨triangularIntervalLeftId code i, (triangular_variable_ids_lt code).2.1 i |>.1⟩ =
      X.intervalLeft i := by
  have hne : triangularIntervalLeftId code i ≠ triangularBetaId := by
    dsimp [triangularIntervalLeftId, triangularBetaId]
    omega
  have hex : ∃ k : TriangularIntervalIndex code,
      triangularIntervalLeftId code i = triangularIntervalLeftId code k := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := by
    apply triangular_interval_left_id_injective
    exact (Classical.choose_spec hex).symm
  simp [triangularReverseHorizontal, hne, hex, hc]

private theorem triangularReverseHorizontal_lookup_right (code : RawTriangularCode)
    (X : TriangularRawParameters code) (i : TriangularIntervalIndex code) :
    triangularReverseHorizontal code X
      ⟨triangularIntervalRightId code i, (triangular_variable_ids_lt code).2.1 i |>.2⟩ =
      X.intervalRight i := by
  have hne : triangularIntervalRightId code i ≠ triangularBetaId := by
    dsimp [triangularIntervalRightId, triangularBetaId]
    omega
  have hleft : ¬ ∃ k : TriangularIntervalIndex code,
      triangularIntervalRightId code i = triangularIntervalLeftId code k := by
    rintro ⟨k, hk⟩
    dsimp [triangularIntervalRightId, triangularIntervalLeftId, triangularBetaId] at hk
    omega
  have hex : ∃ k : TriangularIntervalIndex code,
      triangularIntervalRightId code i = triangularIntervalRightId code k := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := by
    apply triangular_interval_right_id_injective
    exact (Classical.choose_spec hex).symm
  simp [triangularReverseHorizontal, hne, hleft, hex, hc]

private theorem triangularReverseHorizontal_lookup_rep (code : RawTriangularCode)
    (X : TriangularRawParameters code) (i : TriangularRepresentativeIndex code) :
    triangularReverseHorizontal code X
      ⟨triangularRepresentativeXId code i, (triangular_variable_ids_lt code).2.2.1 i⟩ =
      X.representativeX i := by
  have hne : triangularRepresentativeXId code i ≠ triangularBetaId := by
    dsimp [triangularRepresentativeXId, triangularBetaId]
    omega
  have hleft : ¬ ∃ k : TriangularIntervalIndex code,
      triangularRepresentativeXId code i = triangularIntervalLeftId code k := by
    rintro ⟨k, hk⟩
    dsimp [triangularRepresentativeXId, triangularIntervalLeftId, triangularBetaId] at hk
    have hik := triangularIntervalOrdinal_lt k
    have hir := triangularRepresentativeOrdinal_lt i
    omega
  have hright : ¬ ∃ k : TriangularIntervalIndex code,
      triangularRepresentativeXId code i = triangularIntervalRightId code k := by
    rintro ⟨k, hk⟩
    dsimp [triangularRepresentativeXId, triangularIntervalRightId, triangularBetaId] at hk
    have hik := triangularIntervalOrdinal_lt k
    have hir := triangularRepresentativeOrdinal_lt i
    omega
  have hex : ∃ k : TriangularRepresentativeIndex code,
      triangularRepresentativeXId code i = triangularRepresentativeXId code k := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := by
    apply triangular_representative_x_id_injective
    exact (Classical.choose_spec hex).symm
  simp [triangularReverseHorizontal, hne, hleft, hright, hex, hc]

private theorem triangular_shear_id_injective (code : RawTriangularCode)
    {a b : Fin (triangularPieceCount code)}
    (h : triangularShearId a.val = triangularShearId b.val) : a = b := by
  dsimp [triangularShearId] at h
  apply Fin.ext
  omega

private theorem triangularReverseVertical_lookup_alpha (code : RawTriangularCode)
    (X : TriangularRawParameters code) :
    triangularReverseVertical code X
      ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩ = X.alpha := by
  simp [triangularReverseVertical, triangularAlphaId]

private theorem triangularReverseVertical_lookup_shear (code : RawTriangularCode)
    (X : TriangularRawParameters code) (j : Fin (triangularPieceCount code)) :
    triangularReverseVertical code X
      ⟨triangularShearId j.val, (triangular_variable_ids_lt code).2.2.2.2.1 j⟩ = X.shear j := by
  have hne : triangularShearId j.val ≠ triangularAlphaId := by
    dsimp [triangularShearId, triangularAlphaId]
    omega
  have hrep : ¬ ∃ k : TriangularRepresentativeIndex code,
      triangularShearId j.val = triangularRepresentativeYId code k := by
    rintro ⟨k, hk⟩
    dsimp [triangularShearId, triangularRepresentativeYId] at hk
    have hkr := triangularRepresentativeOrdinal_lt k
    omega
  have hex : ∃ k : Fin (triangularPieceCount code),
      triangularShearId j.val = triangularShearId k.val := ⟨j, rfl⟩
  have hc : Classical.choose hex = j := by
    apply triangular_shear_id_injective code
    exact (Classical.choose_spec hex).symm
  simp [triangularReverseVertical, hne, hex, hc]

private theorem triangularReverseVertical_lookup_rep (code : RawTriangularCode)
    (X : TriangularRawParameters code) (i : TriangularRepresentativeIndex code) :
    triangularReverseVertical code X
      ⟨triangularRepresentativeYId code i, (triangular_variable_ids_lt code).2.2.2.2.2 i⟩ =
      X.representativeY i := by
  have hne : triangularRepresentativeYId code i ≠ triangularAlphaId := by
    dsimp [triangularRepresentativeYId, triangularAlphaId]
    omega
  have hshear : ¬ ∃ j : Fin (triangularPieceCount code),
      triangularRepresentativeYId code i = triangularShearId j.val := by
    rintro ⟨j, hj⟩
    dsimp [triangularRepresentativeYId, triangularShearId] at hj
    have hir := triangularRepresentativeOrdinal_lt i
    omega
  have hex : ∃ k : TriangularRepresentativeIndex code,
      triangularRepresentativeYId code i = triangularRepresentativeYId code k := ⟨i, rfl⟩
  have hc : Classical.choose hex = i := by
    apply triangular_representative_y_id_injective
    exact (Classical.choose_spec hex).symm
  simp [triangularReverseVertical, hne, hshear, hex, hc]

private theorem triangular_reverse_vectors_lookup (code : RawTriangularCode)
    (X : TriangularRawParameters code) :
    ∃ (x : Fin (triangularHorizontalVariableCount code) → Real)
      (y : Fin (triangularVerticalVariableCount code) → Real),
      x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ = X.beta ∧
      y ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩ = X.alpha ∧
      (∀ j, y ⟨triangularShearId j.val,
        (triangular_variable_ids_lt code).2.2.2.2.1 j⟩ = X.shear j) ∧
      (∀ i, x ⟨triangularIntervalLeftId code i,
        (triangular_variable_ids_lt code).2.1 i |>.1⟩ = X.intervalLeft i) ∧
      (∀ i, x ⟨triangularIntervalRightId code i,
        (triangular_variable_ids_lt code).2.1 i |>.2⟩ = X.intervalRight i) ∧
      (∀ i, x ⟨triangularRepresentativeXId code i,
        (triangular_variable_ids_lt code).2.2.1 i⟩ = X.representativeX i) ∧
      (∀ i, y ⟨triangularRepresentativeYId code i,
        (triangular_variable_ids_lt code).2.2.2.2.2 i⟩ = X.representativeY i) := by
  refine ⟨triangularReverseHorizontal code X, triangularReverseVertical code X, ?_⟩
  refine ⟨triangularReverseHorizontal_lookup_beta code X,
    triangularReverseVertical_lookup_alpha code X,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    exact triangularReverseVertical_lookup_shear code X j
  · intro i
    exact triangularReverseHorizontal_lookup_left code X i
  · intro i
    exact triangularReverseHorizontal_lookup_right code X i
  · intro i
    exact triangularReverseHorizontal_lookup_rep code X i
  · intro i
    exact triangularReverseVertical_lookup_rep code X i

private theorem triangular_reverse_parameters_eq (code : RawTriangularCode)
    (X : TriangularRawParameters code)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (hβ : x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ = X.beta)
    (hα : y ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩ = X.alpha)
    (hS : ∀ j, y ⟨triangularShearId j.val,
      (triangular_variable_ids_lt code).2.2.2.2.1 j⟩ = X.shear j)
    (hIL : ∀ i, x ⟨triangularIntervalLeftId code i,
      (triangular_variable_ids_lt code).2.1 i |>.1⟩ = X.intervalLeft i)
    (hIR : ∀ i, x ⟨triangularIntervalRightId code i,
      (triangular_variable_ids_lt code).2.1 i |>.2⟩ = X.intervalRight i)
    (hRX : ∀ i, x ⟨triangularRepresentativeXId code i,
      (triangular_variable_ids_lt code).2.2.1 i⟩ = X.representativeX i)
    (hRY : ∀ i, y ⟨triangularRepresentativeYId code i,
      (triangular_variable_ids_lt code).2.2.2.2.2 i⟩ = X.representativeY i) :
    triangularParametersFromWitness code y x = X := by
  cases X with
  | mk alpha beta shear intervalLeft intervalRight representativeX representativeY =>
    dsimp [triangularParametersFromWitness]
    congr 1 <;> simp [hS, hIL, hIR, hRX, hRY]

private def triangularDiameterFormula (C : RegionCode) (code : RawTriangularCode) :
    Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) :=
  let horizontal : List (Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code)) :=
    (List.ofFn fun a : Fin C.vertexCount => a).flatMap fun a =>
      (List.ofFn fun b : Fin C.vertexCount => b).map fun b =>
        let d := Expr.input (triangularHorizontalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
        Formula.andList
          [.horizontalLt d (Expr.scale (Int.ofNat code.checkingRadius)
              (triH C code 0 triangularBetaId)),
           .horizontalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius)
              (triH C code 0 triangularBetaId))]
  let vertical : List (Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code)) :=
    (List.ofFn fun a : Fin C.vertexCount => a).flatMap fun a =>
      (List.ofFn fun b : Fin C.vertexCount => b).map fun b =>
        let d := Expr.input (triangularVerticalVariableCount code)
          (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))
        Formula.andList
          [.verticalLt d (Expr.scale (Int.ofNat code.checkingRadius)
              (triV C code 0 triangularAlphaId)),
           .verticalLt (Expr.neg d) (Expr.scale (Int.ofNat code.checkingRadius)
              (triV C code 0 triangularAlphaId))]
  Formula.andList (horizontal ++ vertical)

private theorem triangular_reverse_basic_components {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X) :
    ∃ (x : Fin (triangularHorizontalVariableCount code) → Real)
      (y : Fin (triangularVerticalVariableCount code) → Real),
      formulaHoldsInOrientation R code.orientation
        ((Formula.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code))
          (triH C code 0 triangularBetaId)).conjunction
          (Formula.verticalLt (Expr.zero C (triangularVerticalVariableCount code))
            (triV C code 0 triangularAlphaId))) x y ∧
      (∀ (j : Fin (triangularPieceCount code)), formulaHoldsInOrientation R code.orientation
        (Formula.andList
          [.verticalLe (Expr.zero C (triangularVerticalVariableCount code))
              (triV C code 0 (triangularShearId j.val)),
           .verticalLt (triV C code 0 (triangularShearId j.val))
              (triV C code 0 triangularAlphaId)]) x y) ∧
      (∀ (i : TriangularIntervalIndex code), formulaHoldsInOrientation R code.orientation
        (Formula.andList
          [.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
              (triH C code 0 (triangularIntervalLeftId code i)),
           .horizontalLt (triH C code 0 (triangularIntervalLeftId code i))
              (triH C code 0 (triangularIntervalRightId code i)),
           .horizontalLe (triH C code 0 (triangularIntervalRightId code i))
              (triH C code 0 triangularBetaId)]) x y) ∧
      (∀ (i i' : TriangularIntervalIndex code), formulaHoldsInOrientation R code.orientation
        (if i = i' then Formula.truth else Formula.disjunction
          (.horizontalLe (triH C code 0 (triangularIntervalRightId code i))
            (triH C code 0 (triangularIntervalLeftId code i')))
          (.horizontalLe (triH C code 0 (triangularIntervalRightId code i'))
            (triH C code 0 (triangularIntervalLeftId code i)))) x y) ∧
      (∀ (i : TriangularRepresentativeIndex code), formulaHoldsInOrientation R code.orientation
        (Formula.andList
          [.horizontalLe (Expr.zero C (triangularHorizontalVariableCount code))
              (triH C code 0 (triangularRepresentativeXId code i)),
           .horizontalLt (triH C code 0 (triangularRepresentativeXId code i))
              (triH C code 0 triangularBetaId),
           .verticalLe (Expr.zero C (triangularVerticalVariableCount code))
              (triV C code 0 (triangularRepresentativeYId code i)),
           .verticalLt (triV C code 0 (triangularRepresentativeYId code i))
              (triV C code 0 triangularAlphaId)]) x y) ∧
      formulaHoldsInOrientation R code.orientation
        (triangularDiameterFormula C code) x y ∧
      x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ = X.beta ∧
      y ⟨triangularAlphaId, (triangular_variable_ids_lt code).2.2.2.1⟩ = X.alpha ∧
      (∀ j, y ⟨triangularShearId j.val,
        (triangular_variable_ids_lt code).2.2.2.2.1 j⟩ = X.shear j) ∧
      (∀ i, x ⟨triangularIntervalLeftId code i,
        (triangular_variable_ids_lt code).2.1 i |>.1⟩ = X.intervalLeft i) ∧
      (∀ i, x ⟨triangularIntervalRightId code i,
        (triangular_variable_ids_lt code).2.1 i |>.2⟩ = X.intervalRight i) ∧
      (∀ i, x ⟨triangularRepresentativeXId code i,
        (triangular_variable_ids_lt code).2.2.1 i⟩ = X.representativeX i) ∧
      (∀ i, y ⟨triangularRepresentativeYId code i,
        (triangular_variable_ids_lt code).2.2.2.2.2 i⟩ = X.representativeY i) := by
  obtain ⟨x, y, hβ, hα, hS, hIL, hIR, hRX, hRY⟩ :=
    triangular_reverse_vectors_lookup code X
  have hP := triangular_reverse_parameters_eq code X x y hβ hα hS hIL hIR hRX hRY
  have heval := triangular_witness_evaluators R code y x
  rw [hP] at heval
  rcases heval with ⟨hcx, hcy, hcxShift, hcyShift, hβ', hα', hleft', hright'⟩
  have hvarH : ∀ id (hid : id < triangularHorizontalVariableCount code),
      evalAffineInOrientation R code.orientation .horizontal
        (Expr.var C (triangularHorizontalVariableCount code) id) x = x ⟨id, hid⟩ :=
    fun id hid => evalAffineInOrientation_var R code.orientation .horizontal x id hid
  have hvarV : ∀ id (hid : id < triangularVerticalVariableCount code),
      evalAffineInOrientation R code.orientation .vertical
        (Expr.var C (triangularVerticalVariableCount code) id) y = y ⟨id, hid⟩ :=
    fun id hid => evalAffineInOrientation_var R code.orientation .vertical y id hid
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change
      evalAffineInOrientation R code.orientation .horizontal
          (Expr.zero C _) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ triangularBetaId) x ∧
      evalAffineInOrientation R code.orientation .vertical
          (Expr.zero C _) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ triangularAlphaId) y
    rw [evalAffineInOrientation_zero, hvarH _ (triangular_variable_ids_lt code).1, hβ,
      evalAffineInOrientation_zero, hvarV _ (triangular_variable_ids_lt code).2.2.2.1, hα]
    exact ⟨hX.periods_pos.2, hX.periods_pos.1⟩
  · intro j
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · change evalAffineInOrientation R code.orientation .vertical (Expr.zero C _) y ≤
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ (triangularShearId j.val)) y
      rw [evalAffineInOrientation_zero,
        hvarV _ ((triangular_variable_ids_lt code).2.2.2.2.1 j), hS j]
      exact (hX.shear_normalized j).1
    · change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ (triangularShearId j.val)) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ triangularAlphaId) y
      rw [hvarV _ ((triangular_variable_ids_lt code).2.2.2.2.1 j), hS j,
        hvarV _ (triangular_variable_ids_lt code).2.2.2.1, hα]
      exact (hX.shear_normalized j).2
  · intro i
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · change evalAffineInOrientation R code.orientation .horizontal (Expr.zero C _) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularIntervalLeftId code i)) x
      rw [evalAffineInOrientation_zero, hvarH _ ((triangular_variable_ids_lt code).2.1 i).1, hIL i]
      exact (hX.intervals_normalized i).1
    · change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularIntervalLeftId code i)) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularIntervalRightId code i)) x
      rw [hvarH _ ((triangular_variable_ids_lt code).2.1 i).1, hIL i,
        hvarH _ ((triangular_variable_ids_lt code).2.1 i).2, hIR i]
      exact (hX.intervals_normalized i).2.1
    · change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularIntervalRightId code i)) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ triangularBetaId) x
      rw [hvarH _ ((triangular_variable_ids_lt code).2.1 i).2, hIR i,
        hvarH _ (triangular_variable_ids_lt code).1, hβ]
      exact (hX.intervals_normalized i).2.2
  · intro i i'
    by_cases h : i = i'
    · subst i'
      simp only [ite_true]
      simp [formulaHoldsInOrientation]
    · simp only [h]
      change
        (evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C _ (triangularIntervalRightId code i)) x ≤
          evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C _ (triangularIntervalLeftId code i')) x) ∨
        (evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C _ (triangularIntervalRightId code i')) x ≤
          evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C _ (triangularIntervalLeftId code i)) x)
      rw [hvarH _ ((triangular_variable_ids_lt code).2.1 i).2, hIR i,
        hvarH _ ((triangular_variable_ids_lt code).2.1 i').1, hIL i',
        hvarH _ ((triangular_variable_ids_lt code).2.1 i').2, hIR i',
        hvarH _ ((triangular_variable_ids_lt code).2.1 i).1, hIL i]
      exact hX.interval_interiors_disjoint i i' h
  · intro i
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl
    · change evalAffineInOrientation R code.orientation .horizontal (Expr.zero C _) x ≤ _
      change evalAffineInOrientation R code.orientation .horizontal (Expr.zero C _) x ≤
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularRepresentativeXId code i)) x
      rw [evalAffineInOrientation_zero, hvarH _ ((triangular_variable_ids_lt code).2.2.1 i), hRX i]
      exact (hX.representatives_normalized i).1.1
    · change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularRepresentativeXId code i)) x < _
      change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ (triangularRepresentativeXId code i)) x <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ triangularBetaId) x
      rw [hvarH _ ((triangular_variable_ids_lt code).2.2.1 i), hRX i,
        hvarH _ (triangular_variable_ids_lt code).1, hβ]
      exact (hX.representatives_normalized i).1.2
    · change evalAffineInOrientation R code.orientation .vertical (Expr.zero C _) y ≤ _
      change evalAffineInOrientation R code.orientation .vertical (Expr.zero C _) y ≤
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ (triangularRepresentativeYId code i)) y
      rw [evalAffineInOrientation_zero,
        hvarV _ ((triangular_variable_ids_lt code).2.2.2.2.2 i), hRY i]
      exact (hX.representatives_normalized i).2.1
    · change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ (triangularRepresentativeYId code i)) y < _
      change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ (triangularRepresentativeYId code i)) y <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ triangularAlphaId) y
      rw [hvarV _ ((triangular_variable_ids_lt code).2.2.2.2.2 i), hRY i,
        hvarV _ (triangular_variable_ids_lt code).2.2.2.1, hα]
      exact (hX.representatives_normalized i).2.2
  · simp only [triangularDiameterFormula]
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    simp only [List.mem_append] at hf
    rcases hf with hf | hf
    · simp only [List.mem_flatMap] at hf
      rcases hf with ⟨a, ha, hf⟩
      rcases List.mem_map.mp hf with ⟨b, hb, rfl⟩
      have hd := hX.vertex_diameter_bounds.1 a b
      have hd' := (abs_lt.mp hd)
      apply (formulaHolds_andList R code.orientation _ x y).2
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · change evalAffineInOrientation R code.orientation .horizontal _ x < _
        rw [show triH C code 0 triangularBetaId =
          Expr.var C _ triangularBetaId by rfl]
        simp only [Nat.add_zero]
        rw [evalAffineInOrientation_input_single_sub,
          evalAffineInOrientation_scale_int,
          hvarH _ (triangular_variable_ids_lt code).1, hβ]
        simpa [selectedCoordinate] using hd'.2
      · change evalAffineInOrientation R code.orientation .horizontal _ x < _
        rw [show triH C code 0 triangularBetaId =
          Expr.var C _ triangularBetaId by rfl]
        simp only [Nat.add_zero]
        rw [evalAffineInOrientation_neg, evalAffineInOrientation_input_single_sub,
          evalAffineInOrientation_scale_int,
          hvarH _ (triangular_variable_ids_lt code).1, hβ]
        have hdl := hd'.1
        simp [selectedCoordinate] at hdl ⊢
        linarith
    · simp only [List.mem_flatMap] at hf
      rcases hf with ⟨a, ha, hf⟩
      rcases List.mem_map.mp hf with ⟨b, hb, rfl⟩
      have hd := hX.vertex_diameter_bounds.2 a b
      have hd' := (abs_lt.mp hd)
      apply (formulaHolds_andList R code.orientation _ x y).2
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · change evalAffineInOrientation R code.orientation .vertical _ y < _
        rw [show triV C code 0 triangularAlphaId =
          Expr.var C _ triangularAlphaId by rfl]
        simp only [Nat.add_zero]
        rw [evalAffineInOrientation_input_single_sub,
          evalAffineInOrientation_scale_int,
          hvarV _ (triangular_variable_ids_lt code).2.2.2.1, hα]
        simpa [selectedCoordinate] using hd'.2
      · change evalAffineInOrientation R code.orientation .vertical _ y < _
        rw [show triV C code 0 triangularAlphaId =
          Expr.var C _ triangularAlphaId by rfl]
        simp only [Nat.add_zero]
        rw [evalAffineInOrientation_neg, evalAffineInOrientation_input_single_sub,
          evalAffineInOrientation_scale_int,
          hvarV _ (triangular_variable_ids_lt code).2.2.2.1, hα]
        have hdl := hd'.1
        simp [selectedCoordinate] at hdl ⊢
        linarith
  · exact ⟨hβ, hα, hS, hIL, hIR, hRX, hRY⟩

private theorem triangular_reverse_partition_component {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (hβ : x ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ = X.beta)
    (hIL : ∀ i, x ⟨triangularIntervalLeftId code i,
      (triangular_variable_ids_lt code).2.1 i |>.1⟩ = X.intervalLeft i)
    (hIR : ∀ i, x ⟨triangularIntervalRightId code i,
      (triangular_variable_ids_lt code).2.1 i |>.2⟩ = X.intervalRight i)
    (hbase : ∀ z, 0 < z → z < X.beta →
      ∃ i, X.intervalLeft i ≤ z ∧ z ≤ X.intervalRight i) :
    formulaHoldsInOrientation R code.orientation
      (triangularPartitionFormula C code) x y := by
  let partitionAnte : Formula C (triangularHorizontalVariableCount code + 1)
      (triangularVerticalVariableCount code) :=
    Formula.andList
      [.horizontalLt (Expr.zero C (triangularHorizontalVariableCount code + 1))
          (Expr.var C (triangularHorizontalVariableCount code + 1) 0),
       .horizontalLt (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
          (triH C code 1 triangularBetaId)]
  let partitionConclusion : Formula C (triangularHorizontalVariableCount code + 1)
      (triangularVerticalVariableCount code) :=
    Formula.orList
      ((triangularIntervalIndices code).map fun i =>
        (Formula.horizontalLe (triH C code 1 (triangularIntervalLeftId code i))
            (Expr.var C (triangularHorizontalVariableCount code + 1) 0)).conjunction
          (Formula.horizontalLe (Expr.var C (triangularHorizontalVariableCount code + 1) 0)
            (triH C code 1 (triangularIntervalRightId code i))))
  let partitionInner : Formula C (triangularHorizontalVariableCount code + 1)
      (triangularVerticalVariableCount code) :=
    Formula.implication partitionAnte partitionConclusion
  have hforall : ∀ t : Real, formulaHoldsInOrientation R code.orientation
      partitionInner (Fin.cons t x) y := by
    intro t
    by_cases ht0 : 0 < t
    · by_cases htβ : t < X.beta
      · obtain ⟨i, hiL, hiR⟩ := hbase t ht0 htβ
        have hconcl : formulaHoldsInOrientation R code.orientation
            partitionConclusion (Fin.cons t x) y := by
          apply (formulaHolds_orList R code.orientation _ (Fin.cons t x) y).2
          refine ⟨_, List.mem_map.mpr ⟨i, mem_triangularIntervalIndices code i, rfl⟩, ?_⟩
          constructor
          · change evalAffineInOrientation R code.orientation .horizontal
                (Expr.var C _ (triangularIntervalLeftId code i + 1))
                (Fin.cons t x) ≤
              evalAffineInOrientation R code.orientation .horizontal
                (Expr.var C _ 0) (Fin.cons t x)
            rw [evalAffineInOrientation_var R code.orientation .horizontal
                  (Fin.cons t x) (triangularIntervalLeftId code i + 1)
                  (Nat.succ_lt_succ ((triangular_variable_ids_lt code).2.1 i).1),
                evalAffineInOrientation_var R code.orientation .horizontal
                  (Fin.cons t x) 0 (Nat.zero_lt_succ _)]
            rw [show (⟨triangularIntervalLeftId code i + 1,
                Nat.succ_lt_succ ((triangular_variable_ids_lt code).2.1 i).1⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) =
                Fin.succ ⟨triangularIntervalLeftId code i,
                  (triangular_variable_ids_lt code).2.1 i |>.1⟩ by rfl,
              show (⟨0, Nat.zero_lt_succ _⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) = 0 by rfl,
              Fin.cons_succ, Fin.cons_zero]
            rw [hIL i]
            exact hiL
          · change evalAffineInOrientation R code.orientation .horizontal
                (Expr.var C _ 0) (Fin.cons t x) ≤
              evalAffineInOrientation R code.orientation .horizontal
                (Expr.var C _ (triangularIntervalRightId code i + 1))
                (Fin.cons t x)
            rw [evalAffineInOrientation_var R code.orientation .horizontal
                  (Fin.cons t x) 0 (Nat.zero_lt_succ _),
                evalAffineInOrientation_var R code.orientation .horizontal
                  (Fin.cons t x) (triangularIntervalRightId code i + 1)
                  (Nat.succ_lt_succ ((triangular_variable_ids_lt code).2.1 i).2)]
            rw [show (⟨0, Nat.zero_lt_succ _⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) = 0 by rfl,
              show (⟨triangularIntervalRightId code i + 1,
                Nat.succ_lt_succ ((triangular_variable_ids_lt code).2.1 i).2⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) =
                Fin.succ ⟨triangularIntervalRightId code i,
                  (triangular_variable_ids_lt code).2.1 i |>.2⟩ by rfl,
              Fin.cons_zero, Fin.cons_succ]
            rw [hIR i]
            exact hiR
        change (¬ formulaHoldsInOrientation R code.orientation partitionAnte
          (Fin.cons t x) y ∨ formulaHoldsInOrientation R code.orientation partitionConclusion
            (Fin.cons t x) y)
        exact Or.inr hconcl
      · have hnot : ¬ formulaHoldsInOrientation R code.orientation
            partitionAnte (Fin.cons t x) y := by
          intro hante
          have hz := (formulaHolds_andList R code.orientation _ (Fin.cons t x) y).mp hante
          have hβ' := hz
            (Formula.horizontalLt (Expr.var C _ 0) (triH C code 1 triangularBetaId))
            (by simp)
          change evalAffineInOrientation R code.orientation .horizontal
              (Expr.var C _ 0) (Fin.cons t x) <
            evalAffineInOrientation R code.orientation .horizontal
              (Expr.var C _ (triangularBetaId + 1)) (Fin.cons t x) at hβ'
          rw [evalAffineInOrientation_var R code.orientation .horizontal
                (Fin.cons t x) 0 (Nat.zero_lt_succ _),
              evalAffineInOrientation_var R code.orientation .horizontal
                (Fin.cons t x) (triangularBetaId + 1)
                (Nat.succ_lt_succ (triangular_variable_ids_lt code).1)] at hβ'
          rw [show (⟨0, Nat.zero_lt_succ _⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) = 0 by rfl,
              show (⟨triangularBetaId + 1,
                Nat.succ_lt_succ (triangular_variable_ids_lt code).1⟩ :
                Fin (triangularHorizontalVariableCount code + 1)) =
                Fin.succ ⟨triangularBetaId, (triangular_variable_ids_lt code).1⟩ by rfl,
              Fin.cons_zero, Fin.cons_succ] at hβ'
          rw [hβ] at hβ'
          exact (not_lt_of_ge (le_of_not_gt htβ)) hβ'
        change (¬ formulaHoldsInOrientation R code.orientation partitionAnte
          (Fin.cons t x) y ∨ formulaHoldsInOrientation R code.orientation partitionConclusion
            (Fin.cons t x) y)
        exact Or.inl hnot
    · have hnot : ¬ formulaHoldsInOrientation R code.orientation
          partitionAnte (Fin.cons t x) y := by
        intro hante
        have hz := (formulaHolds_andList R code.orientation _ (Fin.cons t x) y).mp hante
        have hz' := hz
          (Formula.horizontalLt (Expr.zero C _) (Expr.var C _ 0)) (by simp)
        change evalAffineInOrientation R code.orientation .horizontal
            (Expr.zero C _) (Fin.cons t x) <
          evalAffineInOrientation R code.orientation .horizontal
            (Expr.var C _ 0) (Fin.cons t x) at hz'
        rw [evalAffineInOrientation_zero,
          evalAffineInOrientation_var R code.orientation .horizontal
            (Fin.cons t x) 0 (Nat.zero_lt_succ _)] at hz'
        simpa using (not_lt_of_ge (le_of_not_gt ht0) hz')
      change (¬ formulaHoldsInOrientation R code.orientation partitionAnte
        (Fin.cons t x) y ∨ formulaHoldsInOrientation R code.orientation partitionConclusion
          (Fin.cons t x) y)
      exact Or.inl hnot
  simpa [triangularPartitionFormula, partitionInner, partitionAnte,
    partitionConclusion, Formula.forallHorizontal, formulaHoldsInOrientation] using hforall

private theorem triangular_reverse_packing_component {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (hcx : ∀ (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 0 j i) x =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 0 j i) y =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im) :
    formulaHoldsInOrientation R code.orientation
      (Formula.andList
        ((List.ofFn fun j : Fin (triangularPieceCount code) => j).flatMap fun j =>
          (triangularFiniteIndices code j).flatMap fun i =>
            (triangularFiniteIndices code j).map fun i' =>
              if i = i' then Formula.truth else
                (sameCentreFormula (triangularCentreX C code 0 j i)
                  (triangularCentreX C code 0 j i')
                  (triangularCentreY C code 0 j i)
                  (triangularCentreY C code 0 j i')).disjunction
                  (Formula.andList
                    ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
                      (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                        cellNonoverlapFormula code.orientation e e'
                          (triangularCentreX C code 0 j i)
                          (triangularCentreX C code 0 j i')
                          (triangularCentreY C code 0 j i)
                          (triangularCentreY C code 0 j i'))))) x y := by
  apply (formulaHolds_andList R code.orientation _ x y).2
  intro f hf
  simp only [List.mem_flatMap] at hf
  rcases hf with ⟨j, hj, hf⟩
  rcases hf with ⟨i, hi, hf⟩
  rcases List.mem_map.mp hf with ⟨i', hi', rfl⟩
  by_cases heq : i = i'
  · subst i'
    simp [formulaHoldsInOrientation]
  · simp only [heq, ↓reduceIte, formulaHoldsInOrientation]
    rcases hX.finite_packing j i i' heq with hs | hs
    · have hsame := (formulaHolds_sameCentre_semantic_iff R code.orientation
        (triangularCentreX C code 0 j i) (triangularCentreX C code 0 j i')
        (triangularCentreY C code 0 j i) (triangularCentreY C code 0 j i') x y
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2))
        (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
          (centeredInteger i'.2.2)) (hcx j i) (hcx j i') (hcy j i) (hcy j i')).2 hs
      exact Or.inl hsame
    · right
      apply (formulaHolds_andList R code.orientation _ x y).2
      intro g hg
      simp only [List.mem_flatMap] at hg
      rcases hg with ⟨e, he, hg⟩
      rcases List.mem_map.mp hg with ⟨e', he', rfl⟩
      exact (formulaHolds_cellNonoverlap_semantic_iff R code.orientation e e'
        (triangularCentreX C code 0 j i) (triangularCentreX C code 0 j i')
        (triangularCentreY C code 0 j i) (triangularCentreY C code 0 j i') x y
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2))
        (triangularSemanticCentre code X j i'.1 (centeredInteger i'.2.1)
          (centeredInteger i'.2.2)) (hcx j i) (hcx j i') (hcy j i) (hcy j i')).2
        (hs e e')

private theorem triangular_reverse_leakage_inner {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X)
    (j : Fin (triangularPieceCount code))
    (x0 : Fin (triangularHorizontalVariableCount code) → Real)
    (y0 : Fin (triangularVerticalVariableCount code) → Real)
    (hcx : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) (Fin.cons p.re x0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) (Fin.cons p.im y0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 triangularBetaId) (Fin.cons p.re x0) = X.beta)
    (hα : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .vertical
        (triV C code 1 triangularAlphaId) (Fin.cons p.im y0) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R code.orientation
      (Formula.forallHorizontal (Formula.forallVertical
        (triangularLeakageInnerFormula C code j))) x0 y0 := by
  simp only [Formula.forallHorizontal, Formula.forallVertical,
    formulaHoldsInOrientation, not_exists, not_not]
  intro pre pim
  let p : Tiling.Plane := pre + pim * Complex.I
  let hx : Fin (triangularHorizontalVariableCount code + 1) → Real :=
    Fin.cons pre x0
  let hy : Fin (triangularVerticalVariableCount code + 1) → Real :=
    Fin.cons pim y0
  have hp_re : p.re = pre := by simp [p]
  have hp_im : p.im = pim := by simp [p]
  have hpx : evalAffineInOrientation R code.orientation .horizontal
      (Expr.var C _ 0) hx = p.re := by
    rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
      (Nat.zero_lt_succ _)]
    simp [hx, p]
  have hpy : evalAffineInOrientation R code.orientation .vertical
      (Expr.var C _ 0) hy = p.im := by
    rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
      (Nat.zero_lt_succ _)]
    simp [hy, p]
  have hcx' : ∀ i : TriangularFiniteIndex code j,
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) hx =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re := by
    intro i
    simpa [hx, hp_re] using hcx p i
  have hcy' : ∀ i : TriangularFiniteIndex code j,
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) hy =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im := by
    intro i
    simpa [hy, hp_im] using hcy p i
  have hβ' : evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 triangularBetaId) hx = X.beta := by
    simpa [hx, hp_re] using hβ p
  have hα' : evalAffineInOrientation R code.orientation .vertical
      (triV C code 1 triangularAlphaId) hy = X.alpha := by
    simpa [hy, hp_im] using hα p
  have hleft' : ∀ ell, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩)) hx =
        X.intervalLeft ⟨j, ell⟩ := by
    intro ell
    simpa [hx, hp_re] using hleft p ell
  have hright' : ∀ ell, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩)) hx =
        X.intervalRight ⟨j, ell⟩ := by
    intro ell
    simpa [hx, hp_re] using hright p ell
  change formulaHoldsInOrientation R code.orientation
    (triangularLeakageInnerFormula C code j) hx hy
  simp only [triangularLeakageInnerFormula, Formula.implication,
    formulaHoldsInOrientation]
  by_cases hante : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        [.horizontalLt (Expr.zero C _) (Expr.var C _ 0),
         .horizontalLt (Expr.var C _ 0) (triH C code 1 triangularBetaId),
         .verticalLt (Expr.zero C _) (Expr.var C _ 0),
         .verticalLt (Expr.var C _ 0) (triV C code 1 triangularAlphaId),
         Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
           (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
             openCellFormula code.orientation e
               (triangularCentreX C code 1 j i) (Expr.var C _ 0)
               (triangularCentreY C code 1 j i) (Expr.var C _ 0))]) hx hy
  · right
    have hall := (formulaHolds_andList R code.orientation _ hx hy).mp hante
    have hhit := hall (Formula.orList ((triangularFiniteIndices code j).flatMap fun i =>
      (List.ofFn fun e : Fin C.cellCount => e).map fun e =>
        openCellFormula code.orientation e
          (triangularCentreX C code 1 j i) (Expr.var C _ 0)
          (triangularCentreY C code 1 j i) (Expr.var C _ 0))) (by simp)
    rcases (formulaHolds_orList R code.orientation _ hx hy).mp hhit with
      ⟨f, hf, hfval⟩
    simp only [List.mem_flatMap] at hf
    rcases hf with ⟨i, hi, hf⟩
    rcases List.mem_map.mp hf with ⟨e, he, rfl⟩
    have hopen := (formulaHolds_openCell_semantic_iff R code.orientation e
      (triangularCentreX C code 1 j i) (triangularCentreY C code 1 j i) hx hy
      (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
        (centeredInteger i.2.2)) p (hcx' i) (hcy' i) hpx hpy).mp hfval
    have hp0 : 0 < pre := by
      have h := hall (Formula.horizontalLt (Expr.zero C _) (Expr.var C _ 0)) (by simp)
      change evalAffineInOrientation R code.orientation .horizontal
          (Expr.zero C _) hx <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ 0) hx at h
      rw [evalAffineInOrientation_zero,
        evalAffineInOrientation_var R code.orientation .horizontal hx 0
          (Nat.zero_lt_succ _)] at h
      simpa [hx] using h
    have hpβ : pre < X.beta := by
      have h := hall (Formula.horizontalLt (Expr.var C _ 0)
        (triH C code 1 triangularBetaId)) (by simp)
      change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ 0) hx <
        evalAffineInOrientation R code.orientation .horizontal
          (triH C code 1 triangularBetaId) hx at h
      rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
        (Nat.zero_lt_succ _), hβ'] at h
      simpa [hx, hp_re] using h
    have hpI0 : 0 < pim := by
      have h := hall (Formula.verticalLt (Expr.zero C _) (Expr.var C _ 0)) (by simp)
      change evalAffineInOrientation R code.orientation .vertical
          (Expr.zero C _) hy <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ 0) hy at h
      rw [evalAffineInOrientation_zero,
        evalAffineInOrientation_var R code.orientation .vertical hy 0
          (Nat.zero_lt_succ _)] at h
      simpa [hy] using h
    have hpα : pim < X.alpha := by
      have h := hall (Formula.verticalLt (Expr.var C _ 0)
        (triV C code 1 triangularAlphaId)) (by simp)
      change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ 0) hy <
        evalAffineInOrientation R code.orientation .vertical
          (triV C code 1 triangularAlphaId) hy at h
      rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
        (Nat.zero_lt_succ _), hα'] at h
      simpa [hy, hp_im] using h
    rcases hX.no_leakage j p (by simpa [hp_re] using hp0)
      (by simpa [hp_re] using hpβ) (by simpa [hp_im] using hpI0)
      (by simpa [hp_im] using hpα) ⟨i, hi, e, hopen⟩ with
      ⟨ell, q, hq, hL, hR⟩
    exact (formulaHolds_triangularBaseClosed_iff R code.orientation code X j hx hy p
      hβ' hpx hleft' hright').2 ⟨ell, q, hq, hL, hR⟩
  · left
    exact hante

private theorem triangular_reverse_leakage_component {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (hcx : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) (Fin.cons p.re x) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) (Fin.cons p.im y) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ p : Tiling.Plane, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 triangularBetaId) (Fin.cons p.re x) = X.beta)
    (hα : ∀ p : Tiling.Plane, evalAffineInOrientation R code.orientation .vertical
      (triV C code 1 triangularAlphaId) (Fin.cons p.im y) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (ell : Fin (triangularPiece code j).intervalCount),
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (ell : Fin (triangularPiece code j).intervalCount),
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R code.orientation
      (Formula.andList ((List.ofFn fun j : Fin (triangularPieceCount code) => j).map fun j =>
        Formula.forallHorizontal (Formula.forallVertical
          (triangularLeakageInnerFormula C code j)))) x y := by
  apply (formulaHolds_andList R code.orientation _ x y).2
  intro f hf
  simp only [List.mem_map] at hf
  rcases hf with ⟨j, hj, rfl⟩
  exact triangular_reverse_leakage_inner R code X hX j x y
    (fun p i => hcx p j i) (fun p i => hcy p j i) (hβ) (hα)
    (fun p ell => hleft p j ell) (fun p ell => hright p j ell)

private theorem triangular_reverse_coverage_inner {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X)
    (j : Fin (triangularPieceCount code))
    (x0 : Fin (triangularHorizontalVariableCount code) → Real)
    (y0 : Fin (triangularVerticalVariableCount code) → Real)
    (hcx : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) (Fin.cons p.re x0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) (Fin.cons p.im y0) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 triangularBetaId) (Fin.cons p.re x0) = X.beta)
    (hα : ∀ p : Tiling.Plane,
      evalAffineInOrientation R code.orientation .vertical
        (triV C code 1 triangularAlphaId) (Fin.cons p.im y0) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) ell,
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x0) = X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R code.orientation
      (Formula.forallHorizontal (Formula.forallVertical
        (triangularCoverageInnerFormula C code j))) x0 y0 := by
  simp only [Formula.forallHorizontal, Formula.forallVertical,
    formulaHoldsInOrientation, not_exists, not_not]
  intro pre pim
  let p : Tiling.Plane := pre + pim * Complex.I
  let hx : Fin (triangularHorizontalVariableCount code + 1) → Real := Fin.cons pre x0
  let hy : Fin (triangularVerticalVariableCount code + 1) → Real := Fin.cons pim y0
  have hp_re : p.re = pre := by simp [p]
  have hp_im : p.im = pim := by simp [p]
  have hpx : evalAffineInOrientation R code.orientation .horizontal
      (Expr.var C _ 0) hx = p.re := by
    rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
      (Nat.zero_lt_succ _)]
    simp [hx, p]
  have hpy : evalAffineInOrientation R code.orientation .vertical
      (Expr.var C _ 0) hy = p.im := by
    rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
      (Nat.zero_lt_succ _)]
    simp [hy, p]
  have hcx' : ∀ i : TriangularFiniteIndex code j,
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) hx =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re := by
    intro i
    simpa [hx, hp_re] using hcx p i
  have hcy' : ∀ i : TriangularFiniteIndex code j,
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) hy =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im := by
    intro i
    simpa [hy, hp_im] using hcy p i
  have hβ' : evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 triangularBetaId) hx = X.beta := by
    simpa [hx, hp_re] using hβ p
  have hα' : evalAffineInOrientation R code.orientation .vertical
      (triV C code 1 triangularAlphaId) hy = X.alpha := by
    simpa [hy, hp_im] using hα p
  have hleft' : ∀ ell, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩)) hx =
        X.intervalLeft ⟨j, ell⟩ := by
    intro ell
    simpa [hx, hp_re] using hleft p ell
  have hright' : ∀ ell, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩)) hx =
        X.intervalRight ⟨j, ell⟩ := by
    intro ell
    simpa [hx, hp_re] using hright p ell
  change formulaHoldsInOrientation R code.orientation
    (triangularCoverageInnerFormula C code j) hx hy
  simp only [triangularCoverageInnerFormula, Formula.implication,
    formulaHoldsInOrientation]
  by_cases hante : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        [.horizontalLt (Expr.zero C _) (Expr.var C _ 0),
         .horizontalLt (Expr.var C _ 0) (triH C code 1 triangularBetaId),
         .verticalLt (Expr.zero C _) (Expr.var C _ 0),
         .verticalLt (Expr.var C _ 0) (triV C code 1 triangularAlphaId),
         triangularBaseOpenFormula C code 1 j (Expr.var C _ 0)]) hx hy
  · right
    have hall := (formulaHolds_andList R code.orientation _ hx hy).mp hante
    have hp0 : 0 < pre := by
      have h := hall (Formula.horizontalLt (Expr.zero C _) (Expr.var C _ 0)) (by simp)
      change evalAffineInOrientation R code.orientation .horizontal
          (Expr.zero C _) hx <
        evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ 0) hx at h
      rw [evalAffineInOrientation_zero,
        evalAffineInOrientation_var R code.orientation .horizontal hx 0
          (Nat.zero_lt_succ _)] at h
      simpa [hx] using h
    have hpβ : pre < X.beta := by
      have h := hall (Formula.horizontalLt (Expr.var C _ 0)
        (triH C code 1 triangularBetaId)) (by simp)
      change evalAffineInOrientation R code.orientation .horizontal
          (Expr.var C _ 0) hx <
        evalAffineInOrientation R code.orientation .horizontal
          (triH C code 1 triangularBetaId) hx at h
      rw [evalAffineInOrientation_var R code.orientation .horizontal hx 0
        (Nat.zero_lt_succ _), hβ'] at h
      simpa [hx, hp_re] using h
    have hpI0 : 0 < pim := by
      have h := hall (Formula.verticalLt (Expr.zero C _) (Expr.var C _ 0)) (by simp)
      change evalAffineInOrientation R code.orientation .vertical
          (Expr.zero C _) hy <
        evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ 0) hy at h
      rw [evalAffineInOrientation_zero,
        evalAffineInOrientation_var R code.orientation .vertical hy 0
          (Nat.zero_lt_succ _)] at h
      simpa [hy] using h
    have hpα : pim < X.alpha := by
      have h := hall (Formula.verticalLt (Expr.var C _ 0)
        (triV C code 1 triangularAlphaId)) (by simp)
      change evalAffineInOrientation R code.orientation .vertical
          (Expr.var C _ 0) hy <
        evalAffineInOrientation R code.orientation .vertical
          (triV C code 1 triangularAlphaId) hy at h
      rw [evalAffineInOrientation_var R code.orientation .vertical hy 0
        (Nat.zero_lt_succ _), hα'] at h
      simpa [hy, hp_im] using h
    have hbase := hall (triangularBaseOpenFormula C code 1 j (Expr.var C _ 0)) (by simp)
    obtain ⟨ell, q, hq, hL, hR⟩ := triangularBaseOpen_extract R code.orientation
      code X j hx hy p hβ' hpx hleft' hright' hbase
    obtain ⟨i, hi, e, hclosed⟩ := hX.finite_coverage j p
      (by simpa [hp_re] using hp0) (by simpa [hp_re] using hpβ)
      (by simpa [hp_im] using hpI0) (by simpa [hp_im] using hpα)
      ⟨ell, q, hq, hL, hR⟩
    apply (formulaHolds_orList R code.orientation _ hx hy).2
    refine ⟨closedCellFormula code.orientation e
      (triangularCentreX C code 1 j i) (Expr.var C _ 0)
      (triangularCentreY C code 1 j i) (Expr.var C _ 0), ?_, ?_⟩
    · apply List.mem_flatMap.mpr
      refine ⟨i, hi, ?_⟩
      apply List.mem_map.mpr
      exact ⟨e, List.mem_ofFn.mpr ⟨e, rfl⟩, rfl⟩
    · exact (formulaHolds_closedCell_semantic_iff R code.orientation e
        (triangularCentreX C code 1 j i) (triangularCentreY C code 1 j i) hx hy
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)) p (hcx' i) (hcy' i) hpx hpy).2 hclosed
  · left
    exact hante

private theorem triangular_reverse_coverage_component {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X)
    (x : Fin (triangularHorizontalVariableCount code) → Real)
    (y : Fin (triangularVerticalVariableCount code) → Real)
    (hcx : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .horizontal
          (triangularCentreX C code 1 j i) (Fin.cons p.re x) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).re)
    (hcy : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (i : TriangularFiniteIndex code j),
      evalAffineInOrientation R code.orientation .vertical
          (triangularCentreY C code 1 j i) (Fin.cons p.im y) =
        (triangularSemanticCentre code X j i.1 (centeredInteger i.2.1)
          (centeredInteger i.2.2)).im)
    (hβ : ∀ p : Tiling.Plane, evalAffineInOrientation R code.orientation .horizontal
      (triH C code 1 triangularBetaId) (Fin.cons p.re x) = X.beta)
    (hα : ∀ p : Tiling.Plane, evalAffineInOrientation R code.orientation .vertical
      (triV C code 1 triangularAlphaId) (Fin.cons p.im y) = X.alpha)
    (hleft : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (ell : Fin (triangularPiece code j).intervalCount),
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalLeftId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalLeft ⟨j, ell⟩)
    (hright : ∀ (p : Tiling.Plane) (j : Fin (triangularPieceCount code))
      (ell : Fin (triangularPiece code j).intervalCount),
      evalAffineInOrientation R code.orientation .horizontal
        (triH C code 1 (triangularIntervalRightId code ⟨j, ell⟩))
        (Fin.cons p.re x) = X.intervalRight ⟨j, ell⟩) :
    formulaHoldsInOrientation R code.orientation
      (Formula.andList ((List.ofFn fun j : Fin (triangularPieceCount code) => j).map fun j =>
        Formula.forallHorizontal (Formula.forallVertical
          (triangularCoverageInnerFormula C code j)))) x y := by
  apply (formulaHolds_andList R code.orientation _ x y).2
  intro f hf
  simp only [List.mem_map] at hf
  rcases hf with ⟨j, hj, rfl⟩
  exact triangular_reverse_coverage_inner R code X hX j x y
    (fun p i => hcx p j i) (fun p i => hcy p j i) hβ hα
    (fun p ell => hleft p j ell) (fun p ell => hright p j ell)

private theorem formulaHolds_andList_append {C h v} (R : Realization C) epsilon
    (ps qs : List (Formula C h v)) (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R epsilon (Formula.andList (ps ++ qs)) x y ↔
      formulaHoldsInOrientation R epsilon (Formula.andList ps) x y ∧
      formulaHoldsInOrientation R epsilon (Formula.andList qs) x y := by
  rw [formulaHolds_andList, formulaHolds_andList, formulaHolds_andList]
  constructor
  · intro hall
    constructor
    · intro p hp
      exact hall p (List.mem_append_left _ hp)
    · intro p hp
      exact hall p (List.mem_append_right _ hp)
  · rintro ⟨hps, hqs⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hps p hp
    · exact hqs p hp

private theorem triangular_reverse_body {C} (R : Realization C)
    (code : RawTriangularCode) (X : TriangularRawParameters code)
    (hX : TriangularChecks R code X) :
    ∃ (x : Fin (triangularHorizontalVariableCount code) → Real)
      (y : Fin (triangularVerticalVariableCount code) → Real),
      formulaHoldsInOrientation R code.orientation (triangularBody C code) x y := by
  obtain ⟨x, y, hpos, hS, hI, hdis, hrep, hdiam,
    hβ, hα, hshear, hIL, hIR, hRX, hRY⟩ :=
    triangular_reverse_basic_components R code X hX
  have hP := triangular_reverse_parameters_eq code X x y hβ hα hshear hIL hIR hRX hRY
  have heval := triangular_witness_evaluators R code y x
  rw [hP] at heval
  rcases heval with ⟨hcx, hcy, hcxShift, hcyShift, hβShift, hαShift,
    hleftShift, hrightShift⟩
  have hpart := triangular_reverse_partition_component R code X x y hβ hIL hIR
    hX.base_period_covered
  have hpack := triangular_reverse_packing_component R code X hX x y hcx hcy
  have hleak := triangular_reverse_leakage_component R code X hX x y
    (fun p j i => hcxShift p j i) (fun p j i => hcyShift p j i)
    (fun p => hβShift p) (fun p => hαShift p)
    (fun p j ell => hleftShift p j ell) (fun p j ell => hrightShift p j ell)
  have hcoverage := triangular_reverse_coverage_component R code X hX x y
    (fun p j i => hcxShift p j i) (fun p j i => hcyShift p j i)
    (fun p => hβShift p) (fun p => hαShift p)
    (fun p j ell => hleftShift p j ell) (fun p j ell => hrightShift p j ell)
  let h := triangularHorizontalVariableCount code
  let v := triangularVerticalVariableCount code
  let zeroH := Expr.zero C h
  let zeroV := Expr.zero C v
  let beta := triH C code 0 triangularBetaId
  let alpha := triV C code 0 triangularAlphaId
  let pieces := List.ofFn fun j : Fin (triangularPieceCount code) => j
  let intervals := triangularIntervalIndices code
  let reps := triangularRepresentativeIndices code
  let vertices := List.ofFn fun i : Fin C.vertexCount => i
  let cells := List.ofFn fun e : Fin C.cellCount => e
  let positivity : Formula C h v :=
    .conjunction (.horizontalLt zeroH beta) (.verticalLt zeroV alpha)
  let shearChecks : List (Formula C h v) := pieces.map fun j =>
    Formula.andList (h := h) (v := v)
    [.verticalLe zeroV (triV C code 0 (triangularShearId j.val)),
     .verticalLt (triV C code 0 (triangularShearId j.val)) alpha]
  let intervalChecks := intervals.map fun i =>
    let a := triH C code 0 (triangularIntervalLeftId code i)
    let b := triH C code 0 (triangularIntervalRightId code i)
    Formula.andList (h := h) (v := v)
      [Formula.horizontalLe (h := h) (v := v) zeroH a,
       Formula.horizontalLt (h := h) (v := v) a b,
       Formula.horizontalLe (h := h) (v := v) b beta]
  let intervalDisjoint : List (Formula C h v) :=
    intervals.flatMap fun i => intervals.map fun i' =>
      if i = i' then Formula.truth else Formula.disjunction
        (Formula.horizontalLe (h := h) (v := v)
          (triH C code 0 (triangularIntervalRightId code i))
          (triH C code 0 (triangularIntervalLeftId code i')))
        (Formula.horizontalLe (h := h) (v := v)
          (triH C code 0 (triangularIntervalRightId code i'))
          (triH C code 0 (triangularIntervalLeftId code i)))
  let representativeChecks : List (Formula C h v) := reps.map fun i =>
    Formula.andList (h := h) (v := v)
    [Formula.horizontalLe (h := h) (v := v) zeroH
        (triH C code 0 (triangularRepresentativeXId code i)),
     Formula.horizontalLt (h := h) (v := v)
        (triH C code 0 (triangularRepresentativeXId code i)) beta,
     Formula.verticalLe (h := h) (v := v) zeroV
        (triV C code 0 (triangularRepresentativeYId code i)),
     Formula.verticalLt (h := h) (v := v)
        (triV C code 0 (triangularRepresentativeYId code i)) alpha]
  let packingChecks := Formula.andList (pieces.flatMap fun j =>
    let indices := triangularFiniteIndices code j
    indices.flatMap fun i => indices.map fun i' =>
      if i = i' then Formula.truth else
        let cx := triangularCentreX C code 0 j i
        let cy := triangularCentreY C code 0 j i
        let cx' := triangularCentreX C code 0 j i'
        let cy' := triangularCentreY C code 0 j i'
        Formula.disjunction (sameCentreFormula cx cx' cy cy')
          (Formula.andList (cells.flatMap fun e => cells.map fun e' =>
            cellNonoverlapFormula code.orientation e e' cx cx' cy cy')))
  let leakageChecks : Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) := Formula.andList (pieces.map fun j =>
    Formula.forallHorizontal (Formula.forallVertical
      (triangularLeakageInnerFormula C code j)))
  let coverageChecks : Formula C (triangularHorizontalVariableCount code)
      (triangularVerticalVariableCount code) := Formula.andList (pieces.map fun j =>
    Formula.forallHorizontal (Formula.forallVertical
      (triangularCoverageInnerFormula C code j)))
  have hprefix : formulaHoldsInOrientation R code.orientation
      (Formula.andList [positivity, triangularPartitionFormula C code,
        triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]) x y := by
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [positivity, zeroH, zeroV, beta, alpha] using hpos
    · simpa [triangularPartitionFormula] using hpart
    · simpa [triangularDiameterFormula] using hdiam
    · simpa [packingChecks, pieces, cells] using hpack
    · simpa [leakageChecks, pieces] using hleak
    · simpa [coverageChecks, pieces] using hcoverage
  have hshearList : formulaHoldsInOrientation R code.orientation
      (Formula.andList shearChecks) x y := by
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    rcases List.mem_map.mp hf with ⟨j, hj, rfl⟩
    simpa [shearChecks, zeroV, alpha] using hS j
  have hintervalList : formulaHoldsInOrientation R code.orientation
      (Formula.andList intervalChecks) x y := by
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    rcases List.mem_map.mp hf with ⟨i, hi, rfl⟩
    simpa [intervalChecks, zeroH, beta] using hI i
  have hdisjointList : formulaHoldsInOrientation R code.orientation
      (Formula.andList intervalDisjoint) x y := by
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    rcases List.mem_flatMap.mp hf with ⟨i, hi, hf⟩
    rcases List.mem_map.mp hf with ⟨i', hi', rfl⟩
    simpa [intervalDisjoint] using hdis i i'
  have hrepresentativeList : formulaHoldsInOrientation R code.orientation
      (Formula.andList representativeChecks) x y := by
    apply (formulaHolds_andList R code.orientation _ x y).2
    intro f hf
    rcases List.mem_map.mp hf with ⟨i, hi, rfl⟩
    simpa [representativeChecks, zeroH, zeroV, beta, alpha] using hrep i
  have hprefixShear : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        ([positivity, triangularPartitionFormula C code,
          triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]
          ++ shearChecks)) x y := by
    exact (formulaHolds_andList_append R code.orientation _ _ x y).2
      ⟨hprefix, hshearList⟩
  have hprefixShearInterval : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        (([positivity, triangularPartitionFormula C code,
          triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]
          ++ shearChecks) ++ intervalChecks)) x y := by
    exact (formulaHolds_andList_append R code.orientation _ _ x y).2
      ⟨hprefixShear, hintervalList⟩
  have hprefixShearIntervalDisjoint : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        ((([positivity, triangularPartitionFormula C code,
          triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]
          ++ shearChecks) ++ intervalChecks) ++ intervalDisjoint)) x y := by
    exact (formulaHolds_andList_append R code.orientation _ _ x y).2
      ⟨hprefixShearInterval, hdisjointList⟩
  have hbody : formulaHoldsInOrientation R code.orientation
      (Formula.andList
        ((((
          [positivity, triangularPartitionFormula C code,
            triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]
          ++ shearChecks) ++ intervalChecks) ++ intervalDisjoint) ++
          representativeChecks)) x y := by
    exact (formulaHolds_andList_append R code.orientation _ _ x y).2
      ⟨hprefixShearIntervalDisjoint, hrepresentativeList⟩
  exact ⟨x, y, by
    change formulaHoldsInOrientation R code.orientation
      (Formula.andList
        ((((
          [positivity, triangularPartitionFormula C code,
            triangularDiameterFormula C code, packingChecks, leakageChecks, coverageChecks]
          ++ shearChecks) ++ intervalChecks) ++ intervalDisjoint) ++ representativeChecks)) x y
    exact hbody⟩

private theorem triangularFormula_adequate : ∀ {C} (R : Realization C) code,
    code.wellFormed = true →
    (formulaHoldsInOrientation R code.orientation
      (triangularSlabFormula C code) Fin.elim0 Fin.elim0 ↔
      ∃ X : TriangularRawParameters code, TriangularChecks R code X) := by
  intro C R code hcode
  constructor
  · intro hslab
    exact triangularFormula_forward R code hcode hslab
  · rintro ⟨X, hX⟩
    obtain ⟨x, y, hbody⟩ := triangular_reverse_body R code X hX
    simp only [triangularSlabFormula, hcode]
    rw [Formula.close]
    apply (formulaHolds_closeVertical R code.orientation
      (triangularVerticalVariableCount code)
      (Formula.closeHorizontal (triangularHorizontalVariableCount code)
        (triangularBody C code))).2
    refine ⟨y, ?_⟩
    apply (formulaHolds_closeHorizontal R code.orientation
      (triangularHorizontalVariableCount code) (triangularBody C code) y).2
    exact ⟨x, hbody⟩

private theorem formulaHolds_forallHorizontal_general : ∀ {C h v} (R : Realization C)
    epsilon (p : Formula C (h + 1) v) (x : Fin h → Real) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.forallHorizontal p) x y ↔
      ∀ t : Real, formulaHoldsInOrientation R epsilon p (Fin.cons t x) y := by
  intro C h v R epsilon p x y
  simp [Formula.forallHorizontal, formulaHoldsInOrientation]

private theorem formulaHolds_forallVertical_general : ∀ {C h v} (R : Realization C)
    epsilon (p : Formula C h (v + 1)) (x : Fin h → Real) (y : Fin v → Real),
    formulaHoldsInOrientation R epsilon (Formula.forallVertical p) x y ↔
      ∀ t : Real, formulaHoldsInOrientation R epsilon p x (Fin.cons t y) := by
  intro C h v R epsilon p x y
  simp [Formula.forallVertical, formulaHoldsInOrientation]

private theorem finCons_addOne {α n} (a : α) (z : Fin n → α)
    (id : Nat) (hid : id < n) (hsucc : id + 1 < n + 1) :
    (Fin.cons (α := fun _ : Fin (n + 1) => α) a (fun i => z i))
        ⟨id + 1, hsucc⟩ =
      z ⟨id, hid⟩ := by
  have hi : (⟨id + 1, hsucc⟩ : Fin (n + 1)) = Fin.succ ⟨id, hid⟩ := by
    apply Fin.ext
    rfl
  rw [hi, Fin.cons_succ]

private theorem evalCellInputHorizontal {C h} (R : Realization C)
    (a : Coeff C) (x : Fin h → Real) :
    evalAffineInOrientation R false .horizontal (Expr.input h a) x =
      ∑ i, (a i : Real) * (R.vertex i).re := by
  rw [evalAffineInOrientation_input]
  rfl

private theorem evalSelectedCellHorizontal {C h} (R : Realization C)
    (e : Fin C.cellCount) (x : Fin h → Real) :
    evalAffineInOrientation R false .horizontal
        (Expr.input h (selectedCellRight C false e)) x =
      (R.vertex (C.rightVertex e)).re := by
  simp [evalCellInputHorizontal, selectedCellRight, Coeff.cellRight,
    Coeff.single]

private theorem evalSelectedCellLeftHorizontal {C h} (R : Realization C)
    (e : Fin C.cellCount) (x : Fin h → Real) :
    evalAffineInOrientation R false .horizontal
        (Expr.input h (selectedCellLeft C false e)) x =
      (R.vertex (C.leftVertex e)).re := by
  simp [evalCellInputHorizontal, selectedCellLeft, Coeff.cellLeft,
    Coeff.single]

private theorem evalSelectedCellVertical {C v} (R : Realization C)
    (e : Fin C.cellCount) (x : Fin v → Real) (top : Bool) :
    evalAffineInOrientation R false .vertical
        (Expr.input v (if top then selectedCellTop C false e
          else selectedCellBottom C false e)) x =
      (R.vertex (if top then C.topVertex e else C.bottomVertex e)).im := by
  cases top <;>
    simp [evalAffineInOrientation_input, selectedCellTop, selectedCellBottom,
      Coeff.cellTop, Coeff.cellBottom, Coeff.single, selectedAxis,
      CoordSort.axis] <;> rfl

private theorem evalAffineInOrientation_scale_var {C n} (R : Realization C) epsilon
    (s : CoordSort) (q : Rat) (x : Fin n → Real) (id : Nat) (hid : id < n) :
    evalAffineInOrientation R epsilon s
        (Expr.scale q (Expr.var C n id)) x =
      (q : Real) * x ⟨id, hid⟩ := by
  simp only [evalAffineInOrientation, Expr.scale, Expr.var, Coeff.zero]
  rw [Finset.sum_eq_single ⟨id, hid⟩]
  · simp
  · intro b hb hne
    have hval : b.val ≠ id := by
      intro hval
      exact hne (Fin.ext hval)
    simp [hval]
  · simp

private theorem evalAffineInOrientation_sub {C n} (R : Realization C) epsilon
    (s : CoordSort) (A B : AffineExpr C n) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.sub A B) x =
      evalAffineInOrientation R epsilon s A x -
        evalAffineInOrientation R epsilon s B x := by
  rw [Expr.sub, evalAffineInOrientation_add, evalAffineInOrientation_neg]
  ring

private theorem eval_input_vertex_difference_horizontal {C n} (R : Realization C)
    (a b : Fin C.vertexCount) (x : Fin n → Real) :
    evalAffineInOrientation R false .horizontal
        (Expr.input n (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) x =
      (R.vertex a).re - (R.vertex b).re := by
  rw [evalAffineInOrientation_input]
  simp [Coeff.sub, Coeff.single, selectedAxis, CoordSort.axis,
    Tiling.AxisParallel.Axis.coord, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq']

private theorem eval_input_vertex_difference_vertical {C n} (R : Realization C)
    (a b : Fin C.vertexCount) (x : Fin n → Real) :
    evalAffineInOrientation R false .vertical
        (Expr.input n (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) x =
      (R.vertex a).im - (R.vertex b).im := by
  rw [evalAffineInOrientation_input]
  simp [Coeff.sub, Coeff.single, selectedAxis, CoordSort.axis,
    Tiling.AxisParallel.Axis.coord, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq']

private theorem evalAffineInOrientation_scale_of_zero {C n} (R : Realization C)
    (epsilon : Bool) (s : CoordSort) (q : Rat) (A : AffineExpr C n)
    (hA : ∀ i, A.inputConstant i = 0) (x : Fin n → Real) :
    evalAffineInOrientation R epsilon s (Expr.scale q A) x =
      (q : Real) * evalAffineInOrientation R epsilon s A x := by
  simp only [evalAffineInOrientation, Expr.scale, hA, Int.cast_zero,
    zero_mul, Finset.sum_const_zero, add_zero]
  rw [show (∑ i, (↑(q * A.variableCoefficient i) : Real) * x i) =
      ∑ i, (↑q : Real) * (↑(A.variableCoefficient i) * x i) by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Rat.cast_mul]
    ring]
  norm_num
  rw [Finset.mul_sum]

private theorem sameCentreFormula_holds_iff {C h v} (R : Realization C)
    (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v)
    (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R false (sameCentreFormula cx cx' cy cy') x y ↔
      (evalAffineInOrientation R false .horizontal cx x =
          evalAffineInOrientation R false .horizontal cx' x ∧
        evalAffineInOrientation R false .vertical cy y =
          evalAffineInOrientation R false .vertical cy' y) := by
  simp [sameCentreFormula, Formula.horizontalEq, Formula.verticalEq,
    formulaHoldsInOrientation, le_antisymm_iff]

private theorem cellNonoverlapFormula_holds_iff {C h v} (R : Realization C)
    (e e' : Fin C.cellCount) (cx cx' : AffineExpr C h) (cy cy' : AffineExpr C v)
    (x : Fin h → Real) (y : Fin v → Real) :
    formulaHoldsInOrientation R false
        (cellNonoverlapFormula false e e' cx cx' cy cy') x y ↔
      (evalAffineInOrientation R false .horizontal
          (Expr.add cx (Expr.input h (selectedCellRight C false e))) x ≤
          evalAffineInOrientation R false .horizontal
            (Expr.add cx' (Expr.input h (selectedCellLeft C false e'))) x ∨
       evalAffineInOrientation R false .horizontal
          (Expr.add cx' (Expr.input h (selectedCellRight C false e'))) x ≤
          evalAffineInOrientation R false .horizontal
            (Expr.add cx (Expr.input h (selectedCellLeft C false e))) x ∨
       evalAffineInOrientation R false .vertical
          (Expr.add cy (Expr.input v (selectedCellTop C false e))) y ≤
          evalAffineInOrientation R false .vertical
            (Expr.add cy' (Expr.input v (selectedCellBottom C false e'))) y ∨
       evalAffineInOrientation R false .vertical
          (Expr.add cy' (Expr.input v (selectedCellTop C false e'))) y ≤
          evalAffineInOrientation R false .vertical
            (Expr.add cy (Expr.input v (selectedCellBottom C false e))) y) := by
  simp [cellNonoverlapFormula, Formula.orList, formulaHoldsInOrientation]

private theorem closedCellFormula_holds_iff {C h v} (R : Realization C)
    (e : Fin C.cellCount) (cx x : AffineExpr C h) (cy y : AffineExpr C v)
    (xh : Fin h → Real) (yv : Fin v → Real) :
    formulaHoldsInOrientation R false
        (closedCellFormula false e cx x cy y) xh yv ↔
      (evalAffineInOrientation R false .horizontal
          (Expr.add cx (Expr.input h (selectedCellLeft C false e))) xh ≤
          evalAffineInOrientation R false .horizontal x xh ∧
       evalAffineInOrientation R false .horizontal x xh ≤
          evalAffineInOrientation R false .horizontal
            (Expr.add cx (Expr.input h (selectedCellRight C false e))) xh ∧
       evalAffineInOrientation R false .vertical
          (Expr.add cy (Expr.input v (selectedCellBottom C false e))) yv ≤
          evalAffineInOrientation R false .vertical y yv ∧
       evalAffineInOrientation R false .vertical y yv ≤
          evalAffineInOrientation R false .vertical
            (Expr.add cy (Expr.input v (selectedCellTop C false e))) yv) := by
  simp [closedCellFormula, Formula.andList, formulaHoldsInOrientation]

private theorem latticeReverseVectors (code : RawLatticeCode)
    (X : LatticeRawParameters code) :
    ∃ x : Fin (latticeHorizontalVariableCount code) → Real,
      ∃ y : Fin (latticeVerticalVariableCount code) → Real,
        x ⟨latticeFirstPeriodXId, by
          dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
            X.firstPeriod.re ∧
        x ⟨latticeSecondPeriodXId, by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
            X.secondPeriod.re ∧
        (∀ r, x ⟨latticeRepresentativeXId r.val, by
          dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]; omega⟩ =
            (X.representative r).re) ∧
        x ⟨latticeHorizontalBoundId code, by
          dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
            X.horizontalBound ∧
        x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
          dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ =
            X.firstPeriodAbsoluteXBound ∧
        y ⟨latticeFirstPeriodYId, by
          dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
            X.firstPeriod.im ∧
        y ⟨latticeSecondPeriodYId, by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
            X.secondPeriod.im ∧
        (∀ r, y ⟨latticeRepresentativeYId r.val, by
          dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]; omega⟩ =
            (X.representative r).im) ∧
        y ⟨latticeVerticalBoundId code, by
          dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
            X.verticalBound := by
  let x : Fin (latticeHorizontalVariableCount code) → Real := fun i =>
    dite (i.val = 0) (fun _ => X.firstPeriod.re) (fun h0 =>
      dite (i.val = 1) (fun _ => X.secondPeriod.re) (fun h1 =>
        dite (i.val < 2 + code.representativeCount)
          (fun hr => (X.representative ⟨i.val - 2, by omega⟩).re)
          (fun _ => if i.val = 2 + code.representativeCount then
            X.horizontalBound else X.firstPeriodAbsoluteXBound)))
  let y : Fin (latticeVerticalVariableCount code) → Real := fun i =>
    dite (i.val = 0) (fun _ => X.firstPeriod.im) (fun h0 =>
      dite (i.val = 1) (fun _ => X.secondPeriod.im) (fun h1 =>
        dite (i.val < 2 + code.representativeCount)
          (fun hr => (X.representative ⟨i.val - 2, by omega⟩).im)
          (fun _ => X.verticalBound)))
  have hx0 : x ⟨latticeFirstPeriodXId, by
      dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
      X.firstPeriod.re := by
    simp [x, latticeFirstPeriodXId]
  have hx1 : x ⟨latticeSecondPeriodXId, by
      dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
      X.secondPeriod.re := by
    simp [x, latticeSecondPeriodXId]
  have hxrep : ∀ r, x ⟨latticeRepresentativeXId r.val, by
      dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]; omega⟩ =
      (X.representative r).re := by
    intro r
    have hrlt : 2 + r.val < 2 + code.representativeCount := by omega
    have hr0 : 2 + r.val ≠ 0 := by omega
    have hr1 : 2 + r.val ≠ 1 := by omega
    simp [x, latticeRepresentativeXId, hrlt, hr1]
  have hxb : x ⟨latticeHorizontalBoundId code, by
      dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
      X.horizontalBound := by
    have hnlt : ¬(2 + code.representativeCount <
        2 + code.representativeCount) := by omega
    have hn0 : 2 + code.representativeCount ≠ 0 := by omega
    have hn1 : 2 + code.representativeCount ≠ 1 := by omega
    simp [x, latticeHorizontalBoundId, hn1]
  have hxub : x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
      dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ =
      X.firstPeriodAbsoluteXBound := by
    have hnlt : ¬(3 + code.representativeCount <
        2 + code.representativeCount) := by omega
    have hn0 : 3 + code.representativeCount ≠ 0 := by omega
    have hn1 : 3 + code.representativeCount ≠ 1 := by omega
    have hneq : 3 + code.representativeCount ≠ 2 + code.representativeCount := by omega
    simp [x, latticeFirstPeriodAbsoluteXBoundId, hnlt, hn1]
  have hy0 : y ⟨latticeFirstPeriodYId, by
      dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
      X.firstPeriod.im := by
    simp [y, latticeFirstPeriodYId]
  have hy1 : y ⟨latticeSecondPeriodYId, by
      dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
      X.secondPeriod.im := by
    simp [y, latticeSecondPeriodYId]
  have hyrep : ∀ r, y ⟨latticeRepresentativeYId r.val, by
      dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]; omega⟩ =
      (X.representative r).im := by
    intro r
    have hrlt : 2 + r.val < 2 + code.representativeCount := by omega
    have hr0 : 2 + r.val ≠ 0 := by omega
    have hr1 : 2 + r.val ≠ 1 := by omega
    simp [y, latticeRepresentativeYId, hrlt, hr1]
  have hyb : y ⟨latticeVerticalBoundId code, by
      dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
      X.verticalBound := by
    have hnlt : ¬(2 + code.representativeCount <
        2 + code.representativeCount) := by omega
    have hn0 : 2 + code.representativeCount ≠ 0 := by omega
    have hn1 : 2 + code.representativeCount ≠ 1 := by omega
    simp [y, latticeVerticalBoundId, hn1]
  exact ⟨x, y, hx0, hx1, hxrep, hxb, hxub, hy0, hy1, hyrep, hyb⟩

private theorem latticeReverseCanonicalEvaluations {C : RegionCode} (R : Realization C)
    (code : RawLatticeCode) (X : LatticeRawParameters code) :
    ∃ x : Fin (latticeHorizontalVariableCount code) → Real,
      ∃ y : Fin (latticeVerticalVariableCount code) → Real,
        evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeFirstPeriodXId) x = X.firstPeriod.re ∧
        evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeSecondPeriodXId) x = X.secondPeriod.re ∧
        (∀ r, evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeRepresentativeXId r.val)) x =
              (X.representative r).re) ∧
        evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeHorizontalBoundId code)) x =
              X.horizontalBound ∧
        evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x =
              X.firstPeriodAbsoluteXBound ∧
        evalAffineInOrientation R false .vertical
            (latV C code 0 latticeFirstPeriodYId) y = X.firstPeriod.im ∧
        evalAffineInOrientation R false .vertical
            (latV C code 0 latticeSecondPeriodYId) y = X.secondPeriod.im ∧
        (∀ r, evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeRepresentativeYId r.val)) y =
              (X.representative r).im) ∧
        evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeVerticalBoundId code)) y =
              X.verticalBound := by
  rcases latticeReverseVectors code X with
    ⟨x, y, hxux, hxvx, hxrep, hxhx, huxb, hyuy, hyvy, hyrep, hyhy⟩
  have huxId : latticeFirstPeriodXId < latticeHorizontalVariableCount code := by
    dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]
    omega
  have hvxId : latticeSecondPeriodXId < latticeHorizontalVariableCount code := by
    dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]
    omega
  have huyId : latticeFirstPeriodYId < latticeVerticalVariableCount code := by
    dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]
    omega
  have hvyId : latticeSecondPeriodYId < latticeVerticalVariableCount code := by
    dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]
    omega
  have hhxId : latticeHorizontalBoundId code < latticeHorizontalVariableCount code := by
    dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]
    omega
  have hhyId : latticeVerticalBoundId code < latticeVerticalVariableCount code := by
    dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]
    omega
  have huxbId : latticeFirstPeriodAbsoluteXBoundId code <
      latticeHorizontalVariableCount code := by
    dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]
    omega
  refine ⟨x, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [latH] using
      (evalAffineInOrientation_var R false .horizontal x
        latticeFirstPeriodXId huxId) |>.trans hxux
  · simpa [latH] using
      (evalAffineInOrientation_var R false .horizontal x
        latticeSecondPeriodXId hvxId) |>.trans hxvx
  · intro r
    simpa [latH] using
      (evalAffineInOrientation_var R false .horizontal x
        (latticeRepresentativeXId r.val) (by
          dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
          omega)) |>.trans (hxrep r)
  · simpa [latH] using
      (evalAffineInOrientation_var R false .horizontal x
        (latticeHorizontalBoundId code) hhxId) |>.trans hxhx
  · simpa [latH] using
      (evalAffineInOrientation_var R false .horizontal x
        (latticeFirstPeriodAbsoluteXBoundId code) huxbId) |>.trans huxb
  · simpa [latV] using
      (evalAffineInOrientation_var R false .vertical y
        latticeFirstPeriodYId huyId) |>.trans hyuy
  · simpa [latV] using
      (evalAffineInOrientation_var R false .vertical y
        latticeSecondPeriodYId hvyId) |>.trans hyvy
  · intro r
    simpa [latV] using
      (evalAffineInOrientation_var R false .vertical y
        (latticeRepresentativeYId r.val) (by
          dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
          omega)) |>.trans (hyrep r)
  · simpa [latV] using
      (evalAffineInOrientation_var R false .vertical y
        (latticeVerticalBoundId code) hhyId) |>.trans hyhy

private theorem latticeReverseRankBounds {C} (R : Realization C)
    (code : RawLatticeCode) (X : LatticeRawParameters code)
    (hsep : 0 < X.secondPeriod.re ∧ 0 < X.secondPeriod.im ∧
      0 < X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re ∧
      0 < code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im)
    (hbounds : 0 < X.horizontalBound ∧ 0 < X.verticalBound)
    (hux : 0 ≤ X.firstPeriodAbsoluteXBound ∧
      X.firstPeriod.re ≤ X.firstPeriodAbsoluteXBound ∧
      -X.firstPeriod.re ≤ X.firstPeriodAbsoluteXBound) :
    ∃ x : Fin (latticeHorizontalVariableCount code) → Real,
      ∃ y : Fin (latticeVerticalVariableCount code) → Real,
        (0 < evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeSecondPeriodXId) x ∧
         0 < evalAffineInOrientation R false .vertical
            (latV C code 0 latticeSecondPeriodYId) y ∧
         0 < evalAffineInOrientation R false .horizontal
            (Expr.sub (latH C code 0 latticeFirstPeriodXId)
              (Expr.scale code.rationalSeparator
                (latH C code 0 latticeSecondPeriodXId))) x ∧
         0 < evalAffineInOrientation R false .vertical
            (Expr.sub (Expr.scale code.rationalSeparator
                (latV C code 0 latticeSecondPeriodYId))
              (latV C code 0 latticeFirstPeriodYId)) y ∧
         0 < evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeHorizontalBoundId code)) x ∧
         0 < evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeVerticalBoundId code)) y) ∧
        (0 ≤ evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x ∧
         evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeFirstPeriodXId) x ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x ∧
         -evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeFirstPeriodXId) x ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x) := by
  rcases latticeReverseCanonicalEvaluations R code X with
    ⟨x, y, hxux, hxvx, hxrep, hxhx, huxb, hyuy, hyvy, hyrep, hyhy⟩
  have hax : evalAffineInOrientation R false .horizontal
      (Expr.sub (latH C code 0 latticeFirstPeriodXId)
        (Expr.scale code.rationalSeparator
          (latH C code 0 latticeSecondPeriodXId))) x =
      X.firstPeriod.re - (code.rationalSeparator : Real) * X.secondPeriod.re := by
    rw [evalAffineInOrientation_sub, hxux]
    have hIdX : latticeSecondPeriodXId < latticeHorizontalVariableCount code := by
      dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega
    have hs := evalAffineInOrientation_scale_var R false .horizontal
      code.rationalSeparator x latticeSecondPeriodXId (by
        dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
    have hs' : evalAffineInOrientation R false .horizontal
        (Expr.scale code.rationalSeparator
          (latH C code 0 latticeSecondPeriodXId)) x =
        (code.rationalSeparator : Real) *
          x ⟨latticeSecondPeriodXId, hIdX⟩ := by
      simpa [latH] using hs
    have hxvx0 : x ⟨latticeSecondPeriodXId, hIdX⟩ =
        X.secondPeriod.re := by
      have hv := evalAffineInOrientation_var R false .horizontal x
        latticeSecondPeriodXId hIdX
      calc
        x ⟨latticeSecondPeriodXId, hIdX⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 latticeSecondPeriodXId) x := by
                simpa [latH] using hv.symm
        _ = X.secondPeriod.re := hxvx
    rw [hs', hxvx0]
  have hay : evalAffineInOrientation R false .vertical
      (Expr.sub (Expr.scale code.rationalSeparator
          (latV C code 0 latticeSecondPeriodYId))
        (latV C code 0 latticeFirstPeriodYId)) y =
      (code.rationalSeparator : Real) * X.secondPeriod.im - X.firstPeriod.im := by
    rw [evalAffineInOrientation_sub]
    have hIdY : latticeSecondPeriodYId < latticeVerticalVariableCount code := by
      dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega
    have hs := evalAffineInOrientation_scale_var R false .vertical
      code.rationalSeparator y latticeSecondPeriodYId (by
        dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
    have hs' : evalAffineInOrientation R false .vertical
        (Expr.scale code.rationalSeparator
          (latV C code 0 latticeSecondPeriodYId)) y =
        (code.rationalSeparator : Real) *
          y ⟨latticeSecondPeriodYId, hIdY⟩ := by
      simpa [latV] using hs
    have hyvy0 : y ⟨latticeSecondPeriodYId, hIdY⟩ =
        X.secondPeriod.im := by
      have hv := evalAffineInOrientation_var R false .vertical y
        latticeSecondPeriodYId hIdY
      calc
        y ⟨latticeSecondPeriodYId, hIdY⟩ =
            evalAffineInOrientation R false .vertical
              (latV C code 0 latticeSecondPeriodYId) y := by
                simpa [latV] using hv.symm
        _ = X.secondPeriod.im := hyvy
    rw [hs', hyvy0, hyuy]
  have hnegux : evalAffineInOrientation R false .horizontal
      (Expr.neg (latH C code 0 latticeFirstPeriodXId)) x =
      -X.firstPeriod.re := by
    rw [evalAffineInOrientation_neg, hxux]
  refine ⟨x, y, ?_, ?_⟩
  · simpa [hxvx, hyvy, hax, hay, hxhx, hyhy] using
      ⟨hsep.1, hsep.2.1, sub_pos.mp hsep.2.2.1,
        sub_pos.mp hsep.2.2.2, hbounds.1, hbounds.2⟩
  · simpa [huxb, hxux, hnegux] using hux

private theorem latticeReversePeriodRepresentative {C} (R : Realization C)
    (code : RawLatticeCode) (X : LatticeRawParameters code)
    (hperiod : ∀ sx ∈ ([-1, 1] : List Int), ∀ sy ∈ ([-1, 1] : List Int),
      sx * X.firstPeriod.re + sy * X.secondPeriod.re ≤ X.horizontalBound ∧
      sx * X.firstPeriod.im + sy * X.secondPeriod.im ≤ X.verticalBound)
    (hrep : ∀ r,
      |(X.representative r).re| ≤ X.horizontalBound ∧
      |(X.representative r).im| ≤ X.verticalBound) :
    ∃ x : Fin (latticeHorizontalVariableCount code) → Real,
      ∃ y : Fin (latticeVerticalVariableCount code) → Real,
        (∀ sx ∈ ([-1, 1] : List Int), ∀ sy ∈ ([-1, 1] : List Int),
          evalAffineInOrientation R false .horizontal
            (Expr.add
              (Expr.scale (sx : Rat)
                (latH C code 0 latticeFirstPeriodXId))
              (Expr.scale (sy : Rat)
                (latH C code 0 latticeSecondPeriodXId))) x ≤
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x ∧
          evalAffineInOrientation R false .vertical
            (Expr.add
              (Expr.scale (sx : Rat)
                (latV C code 0 latticeFirstPeriodYId))
              (Expr.scale (sy : Rat)
                (latV C code 0 latticeSecondPeriodYId))) y ≤
            evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y) ∧
        (∀ r : Fin code.representativeCount,
          |evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeRepresentativeXId r.val)) x| ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeHorizontalBoundId code)) x ∧
          |evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeRepresentativeYId r.val)) y| ≤
              evalAffineInOrientation R false .vertical
                (latV C code 0 (latticeVerticalBoundId code)) y) := by
  rcases latticeReverseCanonicalEvaluations R code X with
    ⟨x, y, hxux, hxvx, hxrep, hxhx, huxb, hyuy, hyvy, hyrep, hyhy⟩
  have hxux0 : x ⟨latticeFirstPeriodXId, by
      dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
      X.firstPeriod.re := by
    calc
      x ⟨latticeFirstPeriodXId, by
          dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeFirstPeriodXId) x := by
              simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                latticeFirstPeriodXId (by
                  dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)).symm
      _ = X.firstPeriod.re := hxux
  have hxvx0 : x ⟨latticeSecondPeriodXId, by
      dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
      X.secondPeriod.re := by
    calc
      x ⟨latticeSecondPeriodXId, by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeSecondPeriodXId) x := by
              simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                latticeSecondPeriodXId (by
                  dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)).symm
      _ = X.secondPeriod.re := hxvx
  have hxhx0 : x ⟨latticeHorizontalBoundId code, by
      dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
      X.horizontalBound := by
    calc
      x ⟨latticeHorizontalBoundId code, by
          dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeHorizontalBoundId code)) x := by
              simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                (latticeHorizontalBoundId code) (by
                  dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)).symm
      _ = X.horizontalBound := hxhx
  have hyuy0 : y ⟨latticeFirstPeriodYId, by
      dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
      X.firstPeriod.im := by
    calc
      y ⟨latticeFirstPeriodYId, by
          dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .vertical
            (latV C code 0 latticeFirstPeriodYId) y := by
              simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                latticeFirstPeriodYId (by
                  dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)).symm
      _ = X.firstPeriod.im := hyuy
  have hyvy0 : y ⟨latticeSecondPeriodYId, by
      dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
      X.secondPeriod.im := by
    calc
      y ⟨latticeSecondPeriodYId, by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .vertical
            (latV C code 0 latticeSecondPeriodYId) y := by
              simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                latticeSecondPeriodYId (by
                  dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)).symm
      _ = X.secondPeriod.im := hyvy
  have hyhy0 : y ⟨latticeVerticalBoundId code, by
      dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
      X.verticalBound := by
    calc
      y ⟨latticeVerticalBoundId code, by
          dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
          evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeVerticalBoundId code)) y := by
              simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                (latticeVerticalBoundId code) (by
                  dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)).symm
      _ = X.verticalBound := hyhy
  have hxhx' : evalAffineInOrientation R false .horizontal
      (Expr.var C (latticeHorizontalVariableCount code)
        (latticeHorizontalBoundId code)) x = X.horizontalBound := by
    simpa [latH] using hxhx
  have hyhy' : evalAffineInOrientation R false .vertical
      (Expr.var C (latticeVerticalVariableCount code)
        (latticeVerticalBoundId code)) y = X.verticalBound := by
    simpa [latV] using hyhy
  refine ⟨x, y, ?_, ?_⟩
  · intro sx hs sy hsy
    have hsx := evalAffineInOrientation_scale_var R false .horizontal
      (sx : Rat) x latticeFirstPeriodXId (by
        dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)
    have hsy' := evalAffineInOrientation_scale_var R false .horizontal
      (sy : Rat) x latticeSecondPeriodXId (by
        dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
    have hsyv := evalAffineInOrientation_scale_var R false .vertical
      (sy : Rat) y latticeSecondPeriodYId (by
        dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
    have hsxv := evalAffineInOrientation_scale_var R false .vertical
      (sx : Rat) y latticeFirstPeriodYId (by
        dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)
    have h := hperiod sx hs sy hsy
    constructor
    · rw [evalAffineInOrientation_add]
      simpa [latH, hsx, hsy', hxux0, hxvx0, hxhx'] using h.1
    · rw [evalAffineInOrientation_add]
      simpa [latV, hsxv, hsyv, hyuy0, hyvy0, hyhy'] using h.2
  · intro r
    have hxr := hxrep r
    have hyr := hyrep r
    constructor
    · simpa [hxr, hxhx] using (hrep r).1
    · simpa [hyr, hyhy] using (hrep r).2

private theorem latticeFormula_adequate : ∀ {C} (R : Realization C) code,
    code.wellFormed = true →
    ((latticeCertificateFormula C code).Holds R Fin.elim0 Fin.elim0 ↔
      ∃ X : LatticeRawParameters code, LatticeChecks R code X) := by
  intro C R code hcode
  simp only [latticeCertificateFormula, hcode, ↓reduceIte]
  rw [formulaHolds_false]
  simp only [Formula.close]
  rw [formulaHolds_closeVertical]
  constructor
  · rintro ⟨y, hy⟩
    rw [formulaHolds_closeHorizontal] at hy
    rcases hy with ⟨x, hxy⟩
    let X : LatticeRawParameters code :=
      { firstPeriod :=
          (x ⟨latticeFirstPeriodXId, by
            dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩) +
            (y ⟨latticeFirstPeriodYId, by
              dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩) * Complex.I
        secondPeriod :=
          (x ⟨latticeSecondPeriodXId, by
            dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩) +
            (y ⟨latticeSecondPeriodYId, by
              dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩) * Complex.I
        representative := fun r =>
          (x ⟨latticeRepresentativeXId r.val, by
            dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
            omega⟩) +
            (y ⟨latticeRepresentativeYId r.val, by
              dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
              omega⟩) * Complex.I
        horizontalBound :=
          x ⟨latticeHorizontalBoundId code, by
            dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩
        verticalBound :=
          y ⟨latticeVerticalBoundId code, by
            dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩
        firstPeriodAbsoluteXBound :=
          x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
            dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ }
    simp only [latticeBody, Formula.andList, formulaHoldsInOrientation] at hxy
    rcases hxy with ⟨hrank, hper, hrep, hfirst, hux, hsecond, hpack, hcov, hnil⟩
    have huxId : latticeFirstPeriodXId < latticeHorizontalVariableCount code := by
      dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]
      omega
    have hvxId : latticeSecondPeriodXId < latticeHorizontalVariableCount code := by
      dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]
      omega
    have huyId : latticeFirstPeriodYId < latticeVerticalVariableCount code := by
      dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]
      omega
    have hvyId : latticeSecondPeriodYId < latticeVerticalVariableCount code := by
      dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]
      omega
    have hhxId : latticeHorizontalBoundId code < latticeHorizontalVariableCount code := by
      dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]
      omega
    have hhyId : latticeVerticalBoundId code < latticeVerticalVariableCount code := by
      dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]
      omega
    have hxux : evalAffineInOrientation R false .horizontal
        (latH C code 0 latticeFirstPeriodXId) x = X.firstPeriod.re := by
      have h := evalAffineInOrientation_var R false .horizontal x
        latticeFirstPeriodXId huxId
      simpa [latH, X, Complex.add_re, Complex.mul_re] using h
    have hxvx : evalAffineInOrientation R false .horizontal
        (latH C code 0 latticeSecondPeriodXId) x = X.secondPeriod.re := by
      have h := evalAffineInOrientation_var R false .horizontal x
        latticeSecondPeriodXId hvxId
      simpa [latH, X, Complex.add_re, Complex.mul_re] using h
    have hyuy : evalAffineInOrientation R false .vertical
        (latV C code 0 latticeFirstPeriodYId) y = X.firstPeriod.im := by
      have h := evalAffineInOrientation_var R false .vertical y
        latticeFirstPeriodYId huyId
      simpa [latV, X, Complex.add_im, Complex.mul_im] using h
    have hyvy : evalAffineInOrientation R false .vertical
        (latV C code 0 latticeSecondPeriodYId) y = X.secondPeriod.im := by
      have h := evalAffineInOrientation_var R false .vertical y
        latticeSecondPeriodYId hvyId
      simpa [latV, X, Complex.add_im, Complex.mul_im] using h
    have hxhx : evalAffineInOrientation R false .horizontal
        (latH C code 0 (latticeHorizontalBoundId code)) x = X.horizontalBound := by
      have h := evalAffineInOrientation_var R false .horizontal x
        (latticeHorizontalBoundId code) hhxId
      simpa [latH, X] using h
    have hyhy : evalAffineInOrientation R false .vertical
        (latV C code 0 (latticeVerticalBoundId code)) y = X.verticalBound := by
      have h := evalAffineInOrientation_var R false .vertical y
        (latticeVerticalBoundId code) hhyId
      simpa [latV, X] using h
    have hax : evalAffineInOrientation R false .horizontal
        (Expr.sub (latH C code 0 latticeFirstPeriodXId)
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId))) x =
        X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re := by
      rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
        evalAffineInOrientation_add, evalAffineInOrientation_neg]
      rw [hxux]
      have hs := evalAffineInOrientation_scale_var R false .horizontal
        code.rationalSeparator x latticeSecondPeriodXId hvxId
      have hs' : evalAffineInOrientation R false .horizontal
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId)) x =
          code.rationalSeparator * X.secondPeriod.re := by
        simpa [latH, X, Complex.add_re, Complex.mul_re] using hs
      rw [hs']
      ring
    have hxhx0 : x ⟨latticeHorizontalBoundId code, by
        dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
        X.horizontalBound := by
      calc
        x ⟨latticeHorizontalBoundId code, by
            dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x := by
                simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                  (latticeHorizontalBoundId code) (by
                    dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)).symm
        _ = X.horizontalBound := hxhx
    have hyhy0 : y ⟨latticeVerticalBoundId code, by
        dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
        X.verticalBound := by
      calc
        y ⟨latticeVerticalBoundId code, by
            dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y := by
                simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                  (latticeVerticalBoundId code) (by
                    dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)).symm
        _ = X.verticalBound := hyhy
    have hay : evalAffineInOrientation R false .vertical
        (Expr.sub (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId))
          (latV C code 0 latticeFirstPeriodYId)) y =
        code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im := by
      rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
        evalAffineInOrientation_add, evalAffineInOrientation_neg]
      have hs := evalAffineInOrientation_scale_var R false .vertical
        code.rationalSeparator y latticeSecondPeriodYId hvyId
      have hs' : evalAffineInOrientation R false .vertical
          (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId)) y =
          code.rationalSeparator * X.secondPeriod.im := by
        simpa [latV, X, Complex.add_im, Complex.mul_im] using hs
      rw [hs', hyuy]
      ring
    simp only [evalAffineInOrientation_zero] at hrank
    change (0 < evalAffineInOrientation R false .horizontal
        (latH C code 0 latticeSecondPeriodXId) x ∧
      0 < evalAffineInOrientation R false .vertical
        (latV C code 0 latticeSecondPeriodYId) y ∧
      0 < evalAffineInOrientation R false .horizontal
        (Expr.sub (latH C code 0 latticeFirstPeriodXId)
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId))) x ∧
      0 < evalAffineInOrientation R false .vertical
        (Expr.sub (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId))
          (latV C code 0 latticeFirstPeriodYId)) y ∧
      0 < evalAffineInOrientation R false .horizontal
        (latH C code 0 (latticeHorizontalBoundId code)) x ∧
      0 < evalAffineInOrientation R false .vertical
        (latV C code 0 (latticeVerticalBoundId code)) y ∧ True) at hrank
    have hseparated :
        0 < X.secondPeriod.re ∧ 0 < X.secondPeriod.im ∧
        0 < X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re ∧
        0 < code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im := by
      exact ⟨by simpa [hxvx] using hrank.1,
        by simpa [hyvy] using hrank.2.1,
        by simpa [hax] using hrank.2.2.1,
        by simpa [hay] using hrank.2.2.2.1⟩
    have hbounds : 0 < X.horizontalBound ∧ 0 < X.verticalBound := by
      exact ⟨by simpa [hxhx] using hrank.2.2.2.2.1,
        by simpa [hyhy] using hrank.2.2.2.2.2.1⟩
    refine ⟨X, ?_⟩
    refine ⟨hseparated, hbounds, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hper' := (formulaHolds_andList R false _ x y).mp hper
      have hscaleUx : ∀ s : Int,
          evalAffineInOrientation R false .horizontal
              (Expr.scale (s : Rat) (latH C code 0 latticeFirstPeriodXId)) x =
            (s : Real) * X.firstPeriod.re := by
        intro s
        have hs := evalAffineInOrientation_scale_var R false .horizontal
          (s : Rat) x latticeFirstPeriodXId huxId
        simpa [latH, X, Complex.add_re, Complex.mul_re] using hs
      have hscaleVx : ∀ s : Int,
          evalAffineInOrientation R false .horizontal
              (Expr.scale (s : Rat) (latH C code 0 latticeSecondPeriodXId)) x =
            (s : Real) * X.secondPeriod.re := by
        intro s
        have hs := evalAffineInOrientation_scale_var R false .horizontal
          (s : Rat) x latticeSecondPeriodXId hvxId
        simpa [latH, X, Complex.add_re, Complex.mul_re] using hs
      have hscaleUy : ∀ s : Int,
          evalAffineInOrientation R false .vertical
              (Expr.scale (s : Rat) (latV C code 0 latticeFirstPeriodYId)) y =
            (s : Real) * X.firstPeriod.im := by
        intro s
        have hs := evalAffineInOrientation_scale_var R false .vertical
          (s : Rat) y latticeFirstPeriodYId huyId
        simpa [latV, X, Complex.add_im, Complex.mul_im] using hs
      have hscaleVy : ∀ s : Int,
          evalAffineInOrientation R false .vertical
              (Expr.scale (s : Rat) (latV C code 0 latticeSecondPeriodYId)) y =
            (s : Real) * X.secondPeriod.im := by
        intro s
        have hs := evalAffineInOrientation_scale_var R false .vertical
          (s : Rat) y latticeSecondPeriodYId hvyId
        simpa [latV, X, Complex.add_im, Complex.mul_im] using hs
      intro sx hsx sy hsy
      have hsx' : sx = 1 ∨ sx = -1 := by simpa [or_comm] using hsx
      have hsy' : sy = 1 ∨ sy = -1 := by simpa [or_comm] using hsy
      rcases hsx' with rfl | rfl <;> rcases hsy' with rfl | rfl
      · have hst := hper'
          (Formula.andList
            [.horizontalLe
                (Expr.add (Expr.scale ((1 : Int) : Rat)
                  (latH C code 0 latticeFirstPeriodXId))
                  (Expr.scale ((1 : Int) : Rat)
                    (latH C code 0 latticeSecondPeriodXId)))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.add (Expr.scale ((1 : Int) : Rat)
                  (latV C code 0 latticeFirstPeriodYId))
                  (Expr.scale ((1 : Int) : Rat)
                    (latV C code 0 latticeSecondPeriodYId)))
                (latV C code 0 (latticeVerticalBoundId code))]) (by
          apply List.mem_flatMap.mpr
          refine ⟨1, by norm_num, ?_⟩
          apply List.mem_map.mpr
          refine ⟨1, by norm_num, ?_⟩
          rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hst
        simp only [evalAffineInOrientation_add, hscaleUx, hscaleVx, hxhx,
          hscaleUy, hscaleVy, hyhy] at hst
        exact ⟨by simpa using hst.1, by simpa using hst.2.1⟩
      · have hst := hper'
          (Formula.andList
            [.horizontalLe
                (Expr.add (Expr.scale ((1 : Int) : Rat)
                  (latH C code 0 latticeFirstPeriodXId))
                  (Expr.scale ((-1 : Int) : Rat)
                    (latH C code 0 latticeSecondPeriodXId)))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.add (Expr.scale ((1 : Int) : Rat)
                  (latV C code 0 latticeFirstPeriodYId))
                  (Expr.scale ((-1 : Int) : Rat)
                    (latV C code 0 latticeSecondPeriodYId)))
                (latV C code 0 (latticeVerticalBoundId code))]) (by
          apply List.mem_flatMap.mpr
          refine ⟨1, by norm_num, ?_⟩
          apply List.mem_map.mpr
          refine ⟨-1, by norm_num, ?_⟩
          rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hst
        simp only [evalAffineInOrientation_add, hscaleUx, hscaleVx, hxhx,
          hscaleUy, hscaleVy, hyhy] at hst
        exact ⟨by simpa using hst.1, by simpa using hst.2.1⟩
      · have hst := hper'
          (Formula.andList
            [.horizontalLe
                (Expr.add (Expr.scale ((-1 : Int) : Rat)
                  (latH C code 0 latticeFirstPeriodXId))
                  (Expr.scale ((1 : Int) : Rat)
                    (latH C code 0 latticeSecondPeriodXId)))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.add (Expr.scale ((-1 : Int) : Rat)
                  (latV C code 0 latticeFirstPeriodYId))
                  (Expr.scale ((1 : Int) : Rat)
                    (latV C code 0 latticeSecondPeriodYId)))
                (latV C code 0 (latticeVerticalBoundId code))]) (by
          apply List.mem_flatMap.mpr
          refine ⟨-1, by norm_num, ?_⟩
          apply List.mem_map.mpr
          refine ⟨1, by norm_num, ?_⟩
          rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hst
        simp only [evalAffineInOrientation_add, hscaleUx, hscaleVx, hxhx,
          hscaleUy, hscaleVy, hyhy] at hst
        exact ⟨by simpa using hst.1, by simpa using hst.2.1⟩
      · have hst := hper'
          (Formula.andList
            [.horizontalLe
                (Expr.add (Expr.scale ((-1 : Int) : Rat)
                  (latH C code 0 latticeFirstPeriodXId))
                  (Expr.scale ((-1 : Int) : Rat)
                    (latH C code 0 latticeSecondPeriodXId)))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.add (Expr.scale ((-1 : Int) : Rat)
                  (latV C code 0 latticeFirstPeriodYId))
                  (Expr.scale ((-1 : Int) : Rat)
                    (latV C code 0 latticeSecondPeriodYId)))
                (latV C code 0 (latticeVerticalBoundId code))]) (by
          apply List.mem_flatMap.mpr
          refine ⟨-1, by norm_num, ?_⟩
          apply List.mem_map.mpr
          refine ⟨-1, by norm_num, ?_⟩
          rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hst
        simp only [evalAffineInOrientation_add, hscaleUx, hscaleVx, hxhx,
          hscaleUy, hscaleVy, hyhy] at hst
        exact ⟨by simpa using hst.1, by simpa using hst.2.1⟩
    · have hrep' := (formulaHolds_andList R false _ x y).mp hrep
      intro r
      have hrepXId : latticeRepresentativeXId r.val <
          latticeHorizontalVariableCount code := by
        dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
        omega
      have hrepYId : latticeRepresentativeYId r.val <
          latticeVerticalVariableCount code := by
        dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
        omega
      have hrepX : evalAffineInOrientation R false .horizontal
          (latH C code 0 (latticeRepresentativeXId r.val)) x =
          (X.representative r).re := by
        have h := evalAffineInOrientation_var R false .horizontal x
          (latticeRepresentativeXId r.val) hrepXId
        simpa [latH, X, Complex.add_re, Complex.mul_re] using h
      have hrepY : evalAffineInOrientation R false .vertical
          (latV C code 0 (latticeRepresentativeYId r.val)) y =
          (X.representative r).im := by
        have h := evalAffineInOrientation_var R false .vertical y
          (latticeRepresentativeYId r.val) hrepYId
        simpa [latV, X, Complex.add_im, Complex.mul_im] using h
      have hr := hrep'
          (Formula.andList
            [.horizontalLe
                (Expr.neg (latH C code 0 (latticeHorizontalBoundId code)))
                (latH C code 0 (latticeRepresentativeXId r.val)),
             .horizontalLe
                (latH C code 0 (latticeRepresentativeXId r.val))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.neg (latV C code 0 (latticeVerticalBoundId code)))
                (latV C code 0 (latticeRepresentativeYId r.val)),
             .verticalLe
                (latV C code 0 (latticeRepresentativeYId r.val))
                (latV C code 0 (latticeVerticalBoundId code))]) (by
          apply List.mem_map.mpr
          refine ⟨r, List.mem_ofFn.mpr ⟨r, rfl⟩, ?_⟩
          rfl)
      simp only [Formula.andList, formulaHoldsInOrientation] at hr
      simp only [evalAffineInOrientation_neg, hxhx, hyhy, hrepX, hrepY] at hr
      exact ⟨abs_le.mpr ⟨hr.1, hr.2.1⟩,
        abs_le.mpr ⟨hr.2.2.1, hr.2.2.2.1⟩⟩
    · have hfirst' := (formulaHolds_andList R false _ x y).mp hfirst
      constructor
      · intro a b
        have hh := hfirst'
            (Formula.andList
              [.horizontalLt
                  (Expr.add (Expr.scale (2 : Rat)
                    (latH C code 0 (latticeHorizontalBoundId code)))
                    (Expr.input (latticeHorizontalVariableCount code)
                      (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                  (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                    (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                      (Expr.scale code.rationalSeparator
                        (latH C code 0 latticeSecondPeriodXId)))),
               .horizontalLt
                  (Expr.add (Expr.scale (2 : Rat)
                    (latH C code 0 (latticeHorizontalBoundId code)))
                    (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                      (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                  (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                    (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                      (Expr.scale code.rationalSeparator
                        (latH C code 0 latticeSecondPeriodXId))))]) (by
            apply List.mem_append.mpr
            left
            apply List.mem_flatMap.mpr
            refine ⟨a, List.mem_ofFn.mpr ⟨a, rfl⟩, ?_⟩
            apply List.mem_map.mpr
            refine ⟨b, List.mem_ofFn.mpr ⟨b, rfl⟩, ?_⟩
            rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hh
        have hscaleHBound : ∀ q : Rat,
            evalAffineInOrientation R false .horizontal
                (Expr.scale q (latH C code 0 (latticeHorizontalBoundId code))) x =
              (q : Real) * X.horizontalBound := by
          intro q
          have hz : ∀ i, (latH C code 0 (latticeHorizontalBoundId code)).inputConstant i = 0 := by
            intro i
            simp [latH, Expr.var, Coeff.zero]
          have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
            (latH C code 0 (latticeHorizontalBoundId code)) hz x
          have hv := evalAffineInOrientation_var R false .horizontal x
            (latticeHorizontalBoundId code) hhxId
          have hv' : evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x =
              x ⟨latticeHorizontalBoundId code, hhxId⟩ := by
            simpa [latH] using hv
          rw [hv'] at hs
          simpa [latH, X] using hs
        have hscaleAx : ∀ q : Rat,
            evalAffineInOrientation R false .horizontal
                (Expr.scale q (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                  (Expr.scale code.rationalSeparator
                    (latH C code 0 latticeSecondPeriodXId)))) x =
              (q : Real) *
                (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) := by
          intro q
          have hz : ∀ i, (Expr.sub (latH C code 0 latticeFirstPeriodXId)
              (Expr.scale code.rationalSeparator
                (latH C code 0 latticeSecondPeriodXId))).inputConstant i = 0 := by
            intro i
            simp [Expr.sub, Expr.add, Expr.neg, Expr.scale, latH, Expr.var,
              Coeff.zero, Coeff.add, Coeff.neg]
          have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
            (Expr.sub (latH C code 0 latticeFirstPeriodXId)
              (Expr.scale code.rationalSeparator
                (latH C code 0 latticeSecondPeriodXId))) hz x
          simpa [hax] using hs
        simp only [evalAffineInOrientation_add, evalAffineInOrientation_neg,
          hscaleHBound, hscaleAx, eval_input_vertex_difference_horizontal] at hh
        let d : Real := (R.vertex a).re - (R.vertex b).re
        let rhs : Real := code.firstIndexBound *
          (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re)
        rcases hh with ⟨hp, hn, _⟩
        norm_num at hp hn ⊢
        have habs : |d| < rhs - 2 * X.horizontalBound := by
          rw [abs_lt]
          constructor <;> dsimp [d, rhs] <;> linarith [hp, hn]
        dsimp [d, rhs] at habs ⊢
        linarith
      · intro a b
        have hvv := hfirst'
            (Formula.andList
              [.verticalLt
                  (Expr.add (Expr.scale (2 : Rat)
                    (latV C code 0 (latticeVerticalBoundId code)))
                    (Expr.input (latticeVerticalVariableCount code)
                      (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                  (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                    (Expr.sub (Expr.scale code.rationalSeparator
                        (latV C code 0 latticeSecondPeriodYId))
                      (latV C code 0 latticeFirstPeriodYId))),
               .verticalLt
                  (Expr.add (Expr.scale (2 : Rat)
                    (latV C code 0 (latticeVerticalBoundId code)))
                    (Expr.neg (Expr.input (latticeVerticalVariableCount code)
                      (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                  (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                    (Expr.sub (Expr.scale code.rationalSeparator
                        (latV C code 0 latticeSecondPeriodYId))
                      (latV C code 0 latticeFirstPeriodYId)))]) (by
            apply List.mem_append.mpr
            right
            apply List.mem_flatMap.mpr
            refine ⟨a, List.mem_ofFn.mpr ⟨a, rfl⟩, ?_⟩
            apply List.mem_map.mpr
            refine ⟨b, List.mem_ofFn.mpr ⟨b, rfl⟩, ?_⟩
            rfl)
        simp only [Formula.andList, formulaHoldsInOrientation] at hvv
        have hscaleVBound : ∀ q : Rat,
            evalAffineInOrientation R false .vertical
                (Expr.scale q (latV C code 0 (latticeVerticalBoundId code))) y =
              (q : Real) * X.verticalBound := by
          intro q
          have hz : ∀ i, (latV C code 0 (latticeVerticalBoundId code)).inputConstant i = 0 := by
            intro i
            simp [latV, Expr.var, Coeff.zero]
          have hs := evalAffineInOrientation_scale_of_zero R false .vertical q
            (latV C code 0 (latticeVerticalBoundId code)) hz y
          have hv := evalAffineInOrientation_var R false .vertical y
            (latticeVerticalBoundId code) hhyId
          have hv' : evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y =
              y ⟨latticeVerticalBoundId code, hhyId⟩ := by
            simpa [latV] using hv
          rw [hv'] at hs
          simpa [latV, X] using hs
        have hscaleAy : ∀ q : Rat,
            evalAffineInOrientation R false .vertical
                (Expr.scale q (Expr.sub
                  (Expr.scale code.rationalSeparator
                    (latV C code 0 latticeSecondPeriodYId))
                  (latV C code 0 latticeFirstPeriodYId))) y =
              (q : Real) *
                (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) := by
          intro q
          have hz : ∀ i, (Expr.sub
              (Expr.scale code.rationalSeparator
                (latV C code 0 latticeSecondPeriodYId))
              (latV C code 0 latticeFirstPeriodYId)).inputConstant i = 0 := by
            intro i
            simp [Expr.sub, Expr.add, Expr.neg, Expr.scale, latV, Expr.var,
              Coeff.zero, Coeff.add, Coeff.neg]
          have hs := evalAffineInOrientation_scale_of_zero R false .vertical q
            (Expr.sub (Expr.scale code.rationalSeparator
              (latV C code 0 latticeSecondPeriodYId))
              (latV C code 0 latticeFirstPeriodYId)) hz y
          simpa [hay] using hs
        simp only [evalAffineInOrientation_add, evalAffineInOrientation_neg,
          hscaleVBound, hscaleAy, eval_input_vertex_difference_vertical] at hvv
        let d : Real := (R.vertex a).im - (R.vertex b).im
        let rhs : Real := code.firstIndexBound *
          (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im)
        rcases hvv with ⟨hp, hn, _⟩
        norm_num at hp hn ⊢
        have habs : |d| < rhs - 2 * X.verticalBound := by
          rw [abs_lt]
          constructor <;> dsimp [d, rhs] <;> linarith [hp, hn]
        dsimp [d, rhs] at habs ⊢
        linarith
    · have hxaId : latticeFirstPeriodAbsoluteXBoundId code <
          latticeHorizontalVariableCount code := by
        dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]
        omega
      have hxa : evalAffineInOrientation R false .horizontal
          (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x =
          X.firstPeriodAbsoluteXBound := by
        have hv := evalAffineInOrientation_var R false .horizontal x
          (latticeFirstPeriodAbsoluteXBoundId code) hxaId
        have hv' : evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x =
            x ⟨latticeFirstPeriodAbsoluteXBoundId code, hxaId⟩ := by
          simpa [latH] using hv
        simpa [X] using hv'
      simp only [evalAffineInOrientation_zero, evalAffineInOrientation_neg,
        hxa, hxux] at hux
      exact ⟨hux.1, hux.2.1, hux.2.2.1⟩
    · have hsecond' := (formulaHolds_andList R false _ x y).mp hsecond
      intro a b
      have hh := hsecond'
          (Formula.andList
            [.horizontalLt
                (Expr.add
                  (Expr.add (Expr.scale (2 : Rat)
                    (latH C code 0 (latticeHorizontalBoundId code)))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (latH C code 0
                        (latticeFirstPeriodAbsoluteXBoundId code))))
                  (Expr.input (latticeHorizontalVariableCount code)
                    (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                (Expr.scale (Int.ofNat code.secondIndexBound : Rat)
                  (latH C code 0 latticeSecondPeriodXId)),
             .horizontalLt
                (Expr.add
                  (Expr.add (Expr.scale (2 : Rat)
                    (latH C code 0 (latticeHorizontalBoundId code)))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (latH C code 0
                        (latticeFirstPeriodAbsoluteXBoundId code))))
                  (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                    (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                (Expr.scale (Int.ofNat code.secondIndexBound : Rat)
                  (latH C code 0 latticeSecondPeriodXId))]) (by
          apply List.mem_flatMap.mpr
          refine ⟨a, List.mem_ofFn.mpr ⟨a, rfl⟩, ?_⟩
          apply List.mem_map.mpr
          refine ⟨b, List.mem_ofFn.mpr ⟨b, rfl⟩, ?_⟩
          rfl)
      simp only [Formula.andList, formulaHoldsInOrientation] at hh
      have hscaleHx : ∀ q : Rat,
          evalAffineInOrientation R false .horizontal
              (Expr.scale q (latH C code 0 (latticeHorizontalBoundId code))) x =
            (q : Real) * X.horizontalBound := by
        intro q
        have hz : ∀ i, (latH C code 0 (latticeHorizontalBoundId code)).inputConstant i = 0 := by
          intro i
          simp [latH, Expr.var, Coeff.zero]
        have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
          (latH C code 0 (latticeHorizontalBoundId code)) hz x
        have hv := evalAffineInOrientation_var R false .horizontal x
          (latticeHorizontalBoundId code) hhxId
        have hv' : evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeHorizontalBoundId code)) x =
            x ⟨latticeHorizontalBoundId code, hhxId⟩ := by
          simpa [latH] using hv
        rw [hv'] at hs
        simpa [latH, X] using hs
      have hxaId : latticeFirstPeriodAbsoluteXBoundId code <
          latticeHorizontalVariableCount code := by
        dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]
        omega
      have hscaleHxa : ∀ q : Rat,
          evalAffineInOrientation R false .horizontal
              (Expr.scale q
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code))) x =
            (q : Real) * X.firstPeriodAbsoluteXBound := by
        intro q
        have hz : ∀ i, (latH C code 0
            (latticeFirstPeriodAbsoluteXBoundId code)).inputConstant i = 0 := by
          intro i
          simp [latH, Expr.var, Coeff.zero]
        have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
          (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) hz x
        have hv := evalAffineInOrientation_var R false .horizontal x
          (latticeFirstPeriodAbsoluteXBoundId code) hxaId
        have hv' : evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x =
            x ⟨latticeFirstPeriodAbsoluteXBoundId code, hxaId⟩ := by
          simpa [latH] using hv
        rw [hv'] at hs
        simpa [latH, X] using hs
      have hscaleVx : ∀ q : Rat,
          evalAffineInOrientation R false .horizontal
              (Expr.scale q (latH C code 0 latticeSecondPeriodXId)) x =
            (q : Real) * X.secondPeriod.re := by
        intro q
        have hs := evalAffineInOrientation_scale_var R false .horizontal q x
          latticeSecondPeriodXId hvxId
        simpa [latH, X, Complex.add_re, Complex.mul_re] using hs
      simp only [evalAffineInOrientation_add, evalAffineInOrientation_neg,
        hscaleHx, hscaleHxa, hscaleVx,
        eval_input_vertex_difference_horizontal] at hh
      let d : Real := (R.vertex a).re - (R.vertex b).re
      let rhs : Real := code.secondIndexBound * X.secondPeriod.re
      rcases hh with ⟨hp, hn, _⟩
      norm_num at hp hn ⊢
      have habs : |d| < rhs - 2 * X.horizontalBound -
          code.firstIndexBound * X.firstPeriodAbsoluteXBound := by
        rw [abs_lt]
        constructor <;> dsimp [d, rhs] <;> linarith [hp, hn]
      dsimp [d, rhs] at habs ⊢
      linarith
    · intro i i' hi hi' hne
      by_cases heq : i = i'
      · exact False.elim (hne heq)
      · have hpack' := (formulaHolds_andList R false _ x y).mp hpack
        have hp := hpack'
            (Formula.disjunction
              (sameCentreFormula (latticeCentreX C code 0 i)
                (latticeCentreX C code 0 i')
                (latticeCentreY C code 0 i)
                (latticeCentreY C code 0 i'))
              (Formula.andList
                ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
                  (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                    cellNonoverlapFormula false e e'
                      (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
                      (latticeCentreY C code 0 i) (latticeCentreY C code 0 i')))) (by
          apply List.mem_flatMap.mpr
          refine ⟨i, hi, ?_⟩
          apply List.mem_map.mpr
          exact ⟨i', hi', by simp [heq]⟩)
        simp only [formulaHoldsInOrientation] at hp
        cases hp with
        | inl hcentre =>
            have hcentre' := (sameCentreFormula_holds_iff R
              (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
              (latticeCentreY C code 0 i) (latticeCentreY C code 0 i') x y).mp hcentre
            have evalCentreX : ∀ j : LatticeFiniteIndex code,
                evalAffineInOrientation R false .horizontal
                    (latticeCentreX C code 0 j) x =
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).re := by
              intro j
              have hrid : latticeRepresentativeXId j.1.val <
                  latticeHorizontalVariableCount code := by
                dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
                omega
              have hr := evalAffineInOrientation_var R false .horizontal x
                (latticeRepresentativeXId j.1.val) hrid
              have hnr := evalAffineInOrientation_scale_var R false .horizontal
                (centeredInteger j.2.1 : Rat) x latticeFirstPeriodXId huxId
              have hmr := evalAffineInOrientation_scale_var R false .horizontal
                (centeredInteger j.2.2 : Rat) x latticeSecondPeriodXId hvxId
              have hr' : evalAffineInOrientation R false .horizontal
                  (latH C code 0 (latticeRepresentativeXId j.1.val)) x =
                  x ⟨latticeRepresentativeXId j.1.val, hrid⟩ := by
                simpa [latH] using hr
              have hnr' : evalAffineInOrientation R false .horizontal
                  (Expr.scale (centeredInteger j.2.1)
                    (latH C code 0 latticeFirstPeriodXId)) x =
                  (centeredInteger j.2.1 : Real) *
                    x ⟨latticeFirstPeriodXId, huxId⟩ := by
                simpa [latH] using hnr
              have hmr' : evalAffineInOrientation R false .horizontal
                  (Expr.scale (centeredInteger j.2.2)
                    (latH C code 0 latticeSecondPeriodXId)) x =
                  (centeredInteger j.2.2 : Real) *
                    x ⟨latticeSecondPeriodXId, hvxId⟩ := by
                simpa [latH] using hmr
              simp only [latticeCentreX, evalAffineInOrientation_add]
              rw [hr', hnr', hmr']
              have hsmulRe (n : Int) (z : Complex) :
                  (n • z).re = (n : Real) * z.re := by
                rw [Complex.smul_re, ← Int.cast_smul_eq_zsmul Real n z.re]
                simp [smul_eq_mul]
              dsimp [latticeSemanticCentre, X]
              simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
                Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                hsmulRe, mul_zero, sub_zero, add_zero, zero_mul]
            have evalCentreY : ∀ j : LatticeFiniteIndex code,
                evalAffineInOrientation R false .vertical
                    (latticeCentreY C code 0 j) y =
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).im := by
              intro j
              have hrid : latticeRepresentativeYId j.1.val <
                  latticeVerticalVariableCount code := by
                dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
                omega
              have hr := evalAffineInOrientation_var R false .vertical y
                (latticeRepresentativeYId j.1.val) hrid
              have hnr := evalAffineInOrientation_scale_var R false .vertical
                (centeredInteger j.2.1 : Rat) y latticeFirstPeriodYId huyId
              have hmr := evalAffineInOrientation_scale_var R false .vertical
                (centeredInteger j.2.2 : Rat) y latticeSecondPeriodYId hvyId
              have hr' : evalAffineInOrientation R false .vertical
                  (latV C code 0 (latticeRepresentativeYId j.1.val)) y =
                  y ⟨latticeRepresentativeYId j.1.val, hrid⟩ := by
                simpa [latV] using hr
              have hnr' : evalAffineInOrientation R false .vertical
                  (Expr.scale (centeredInteger j.2.1)
                    (latV C code 0 latticeFirstPeriodYId)) y =
                  (centeredInteger j.2.1 : Real) *
                    y ⟨latticeFirstPeriodYId, huyId⟩ := by
                simpa [latV] using hnr
              have hmr' : evalAffineInOrientation R false .vertical
                  (Expr.scale (centeredInteger j.2.2)
                    (latV C code 0 latticeSecondPeriodYId)) y =
                  (centeredInteger j.2.2 : Real) *
                    y ⟨latticeSecondPeriodYId, hvyId⟩ := by
                simpa [latV] using hmr
              simp only [latticeCentreY, evalAffineInOrientation_add]
              rw [hr', hnr', hmr']
              have hsmulIm (n : Int) (z : Complex) :
                  (n • z).im = (n : Real) * z.im := by
                rw [Complex.smul_im, ← Int.cast_smul_eq_zsmul Real n z.im]
                simp [smul_eq_mul]
              dsimp [latticeSemanticCentre, X]
              simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
                Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                hsmulIm, mul_zero, add_zero]
              ring
            rw [evalCentreX i, evalCentreX i', evalCentreY i, evalCentreY i'] at hcentre'
            apply Or.inl
            exact Complex.ext hcentre'.1 hcentre'.2
        | inr hcells =>
            have hcells' := (formulaHolds_andList R false _ x y).mp hcells
            apply Or.inr
            intro e e'
            have evalCentreX2 : ∀ j : LatticeFiniteIndex code,
                evalAffineInOrientation R false .horizontal
                    (latticeCentreX C code 0 j) x =
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).re := by
              intro j
              have hrid : latticeRepresentativeXId j.1.val <
                  latticeHorizontalVariableCount code := by
                dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
                omega
              have hr := evalAffineInOrientation_var R false .horizontal x
                (latticeRepresentativeXId j.1.val) hrid
              have hnr := evalAffineInOrientation_scale_var R false .horizontal
                (centeredInteger j.2.1 : Rat) x latticeFirstPeriodXId huxId
              have hmr := evalAffineInOrientation_scale_var R false .horizontal
                (centeredInteger j.2.2 : Rat) x latticeSecondPeriodXId hvxId
              have hr' : evalAffineInOrientation R false .horizontal
                  (latH C code 0 (latticeRepresentativeXId j.1.val)) x =
                  x ⟨latticeRepresentativeXId j.1.val, hrid⟩ := by
                simpa [latH] using hr
              have hnr' : evalAffineInOrientation R false .horizontal
                  (Expr.scale (centeredInteger j.2.1)
                    (latH C code 0 latticeFirstPeriodXId)) x =
                  (centeredInteger j.2.1 : Real) *
                    x ⟨latticeFirstPeriodXId, huxId⟩ := by
                simpa [latH] using hnr
              have hmr' : evalAffineInOrientation R false .horizontal
                  (Expr.scale (centeredInteger j.2.2)
                    (latH C code 0 latticeSecondPeriodXId)) x =
                  (centeredInteger j.2.2 : Real) *
                    x ⟨latticeSecondPeriodXId, hvxId⟩ := by
                simpa [latH] using hmr
              simp only [latticeCentreX, evalAffineInOrientation_add]
              rw [hr', hnr', hmr']
              have hsmulRe (n : Int) (z : Complex) :
                  (n • z).re = (n : Real) * z.re := by
                rw [Complex.smul_re, ← Int.cast_smul_eq_zsmul Real n z.re]
                simp [smul_eq_mul]
              dsimp [latticeSemanticCentre, X]
              simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
                Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                hsmulRe, mul_zero, sub_zero, add_zero, zero_mul]
            have evalCentreY2 : ∀ j : LatticeFiniteIndex code,
                evalAffineInOrientation R false .vertical
                    (latticeCentreY C code 0 j) y =
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).im := by
              intro j
              have hrid : latticeRepresentativeYId j.1.val <
                  latticeVerticalVariableCount code := by
                dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
                omega
              have hr := evalAffineInOrientation_var R false .vertical y
                (latticeRepresentativeYId j.1.val) hrid
              have hnr := evalAffineInOrientation_scale_var R false .vertical
                (centeredInteger j.2.1 : Rat) y latticeFirstPeriodYId huyId
              have hmr := evalAffineInOrientation_scale_var R false .vertical
                (centeredInteger j.2.2 : Rat) y latticeSecondPeriodYId hvyId
              have hr' : evalAffineInOrientation R false .vertical
                  (latV C code 0 (latticeRepresentativeYId j.1.val)) y =
                  y ⟨latticeRepresentativeYId j.1.val, hrid⟩ := by
                simpa [latV] using hr
              have hnr' : evalAffineInOrientation R false .vertical
                  (Expr.scale (centeredInteger j.2.1)
                    (latV C code 0 latticeFirstPeriodYId)) y =
                  (centeredInteger j.2.1 : Real) *
                    y ⟨latticeFirstPeriodYId, huyId⟩ := by
                simpa [latV] using hnr
              have hmr' : evalAffineInOrientation R false .vertical
                  (Expr.scale (centeredInteger j.2.2)
                    (latV C code 0 latticeSecondPeriodYId)) y =
                  (centeredInteger j.2.2 : Real) *
                    y ⟨latticeSecondPeriodYId, hvyId⟩ := by
                simpa [latV] using hmr
              simp only [latticeCentreY, evalAffineInOrientation_add]
              rw [hr', hnr', hmr']
              have hsmulIm (n : Int) (z : Complex) :
                  (n • z).im = (n : Real) * z.im := by
                rw [Complex.smul_im, ← Int.cast_smul_eq_zsmul Real n z.im]
                simp [smul_eq_mul]
              dsimp [latticeSemanticCentre, X]
              simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
                Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
                hsmulIm, mul_zero, add_zero]
              ring
            have hp := hcells'
              (cellNonoverlapFormula false e e'
                (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
                (latticeCentreY C code 0 i) (latticeCentreY C code 0 i')) (by
                apply List.mem_flatMap.mpr
                refine ⟨e, by simp, ?_⟩
                exact List.mem_map.mpr ⟨e', by simp⟩)
            have hp' := (cellNonoverlapFormula_holds_iff R e e'
              (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
              (latticeCentreY C code 0 i) (latticeCentreY C code 0 i') x y).mp hp
            simp only [evalAffineInOrientation_add] at hp'
            simp only [Nat.add_zero] at hp'
            rw [evalCentreX2 i, evalCentreX2 i', evalCentreY2 i,
              evalCentreY2 i'] at hp'
            rw [evalSelectedCellHorizontal R e x,
              evalSelectedCellLeftHorizontal R e' x,
              evalSelectedCellHorizontal R e' x,
              evalSelectedCellLeftHorizontal R e x] at hp'
            have htop : ∀ z : Fin C.cellCount,
                evalAffineInOrientation R false .vertical
                    (Expr.input (latticeVerticalVariableCount code)
                      (selectedCellTop C false z)) y =
                  (R.vertex (C.topVertex z)).im := by
              intro z
              simpa using evalSelectedCellVertical R z y true
            have hbottom : ∀ z : Fin C.cellCount,
                evalAffineInOrientation R false .vertical
                    (Expr.input (latticeVerticalVariableCount code)
                      (selectedCellBottom C false z)) y =
                  (R.vertex (C.bottomVertex z)).im := by
              intro z
              simpa using evalSelectedCellVertical R z y false
            rw [htop e, hbottom e', htop e', hbottom e] at hp'
            change
              (latticeSemanticCentre code X i.1
                    (centeredInteger i.2.1) (centeredInteger i.2.2)).re +
                    (R.vertex (C.rightVertex e)).re ≤
                  (latticeSemanticCentre code X i'.1
                    (centeredInteger i'.2.1) (centeredInteger i'.2.2)).re +
                    (R.vertex (C.leftVertex e')).re ∨
                (latticeSemanticCentre code X i'.1
                    (centeredInteger i'.2.1) (centeredInteger i'.2.2)).re +
                    (R.vertex (C.rightVertex e')).re ≤
                  (latticeSemanticCentre code X i.1
                    (centeredInteger i.2.1) (centeredInteger i.2.2)).re +
                    (R.vertex (C.leftVertex e)).re ∨
                (latticeSemanticCentre code X i.1
                    (centeredInteger i.2.1) (centeredInteger i.2.2)).im +
                    (R.vertex (C.topVertex e)).im ≤
                  (latticeSemanticCentre code X i'.1
                    (centeredInteger i'.2.1) (centeredInteger i'.2.2)).im +
                    (R.vertex (C.bottomVertex e')).im ∨
                (latticeSemanticCentre code X i'.1
                    (centeredInteger i'.2.1) (centeredInteger i'.2.2)).im +
                    (R.vertex (C.topVertex e')).im ≤
                  (latticeSemanticCentre code X i.1
                    (centeredInteger i.2.1) (centeredInteger i.2.2)).im +
                    (R.vertex (C.bottomVertex e)).im
            exact hp'
    · intro p hp
      have hcov' := (formulaHolds_forallHorizontal_general R false _ x y).mp hcov
      have hcov'' := (formulaHolds_forallVertical_general R false _
        (Fin.cons p.re x) y).mp (hcov' p.re)
      have hpoint := hcov'' p.im
      simp only [Formula.implication,
        formulaHoldsInOrientation] at hpoint
      change -X.horizontalBound < p.re ∧ p.re < X.horizontalBound ∧
        -X.verticalBound < p.im ∧ p.im < X.verticalBound at hp
      have hbhid : latticeHorizontalBoundId code + 1 <
          latticeHorizontalVariableCount code + 1 := by
        dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]
        omega
      have hbvid : latticeVerticalBoundId code + 1 <
          latticeVerticalVariableCount code + 1 := by
        dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]
        omega
      have hbh := evalAffineInOrientation_var R false .horizontal
        (Fin.cons p.re x) (latticeHorizontalBoundId code + 1) hbhid
      have hbv := evalAffineInOrientation_var R false .vertical
        (Fin.cons p.im y) (latticeVerticalBoundId code + 1) hbvid
      have hxh := evalAffineInOrientation_var R false .horizontal
        (Fin.cons p.re x) 0 (by omega)
      have hyv := evalAffineInOrientation_var R false .vertical
        (Fin.cons p.im y) 0 (by omega)
      have hbh' : evalAffineInOrientation R false .horizontal
          (latH C code 1 (latticeHorizontalBoundId code))
          (Fin.cons p.re x) = X.horizontalBound := by
        rw [finCons_addOne p.re x _ (by
          dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)
          hbhid] at hbh
        simpa [latH, X] using hbh
      have hbv' : evalAffineInOrientation R false .vertical
          (latV C code 1 (latticeVerticalBoundId code))
          (Fin.cons p.im y) = X.verticalBound := by
        rw [finCons_addOne p.im y _ (by
          dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)
          hbvid] at hbv
        simpa [latV, X] using hbv
      have hxh' : evalAffineInOrientation R false .horizontal
          (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
          (Fin.cons p.re x) = p.re := by
        simpa using hxh
      have hyv' : evalAffineInOrientation R false .vertical
          (Expr.var C (latticeVerticalVariableCount code + 1) 0)
          (Fin.cons p.im y) = p.im := by
        simpa using hyv
      have hant :
          evalAffineInOrientation R false .horizontal
              (Expr.neg (latH C code 1 (latticeHorizontalBoundId code)))
              (Fin.cons p.re x) <
            evalAffineInOrientation R false .horizontal
              (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
              (Fin.cons p.re x) ∧
          evalAffineInOrientation R false .horizontal
              (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
              (Fin.cons p.re x) <
            evalAffineInOrientation R false .horizontal
              (latH C code 1 (latticeHorizontalBoundId code))
              (Fin.cons p.re x) ∧
          evalAffineInOrientation R false .vertical
              (Expr.neg (latV C code 1 (latticeVerticalBoundId code)))
              (Fin.cons p.im y) <
            evalAffineInOrientation R false .vertical
              (Expr.var C (latticeVerticalVariableCount code + 1) 0)
              (Fin.cons p.im y) ∧
          evalAffineInOrientation R false .vertical
              (Expr.var C (latticeVerticalVariableCount code + 1) 0)
              (Fin.cons p.im y) <
            evalAffineInOrientation R false .vertical
              (latV C code 1 (latticeVerticalBoundId code))
              (Fin.cons p.im y) ∧ True := by
        simpa [evalAffineInOrientation_neg, hbh', hbv', hxh', hyv'] using hp
      have hcovered := hpoint.resolve_left (fun hn => hn hant)
      have hmember := (formulaHolds_orList R false _
        (Fin.cons p.re x) (Fin.cons p.im y)).mp hcovered
      rcases hmember with ⟨q, hq, hqv⟩
      rcases List.mem_flatMap.mp hq with ⟨j, hj, hqj⟩
      rcases List.mem_map.mp hqj with ⟨e, he, rfl⟩
      have evalCentreXShift : ∀ k : LatticeFiniteIndex code,
          evalAffineInOrientation R false .horizontal
              (latticeCentreX C code 1 k) (Fin.cons p.re x) =
            (latticeSemanticCentre code X k.1
              (centeredInteger k.2.1) (centeredInteger k.2.2)).re := by
        intro k
        have hrid : latticeRepresentativeXId k.1.val + 1 <
            latticeHorizontalVariableCount code + 1 := by
          dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
          omega
        have huxid : latticeFirstPeriodXId + 1 <
            latticeHorizontalVariableCount code + 1 := by
          dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]
          omega
        have hvxid : latticeSecondPeriodXId + 1 <
            latticeHorizontalVariableCount code + 1 := by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]
          omega
        have hr := evalAffineInOrientation_var R false .horizontal
          (Fin.cons p.re x) (latticeRepresentativeXId k.1.val + 1) hrid
        have hnr := evalAffineInOrientation_scale_var R false .horizontal
          (centeredInteger k.2.1 : Rat) (Fin.cons p.re x)
          (latticeFirstPeriodXId + 1) huxid
        have hmr := evalAffineInOrientation_scale_var R false .horizontal
          (centeredInteger k.2.2 : Rat) (Fin.cons p.re x)
          (latticeSecondPeriodXId + 1) hvxid
        have hr' : evalAffineInOrientation R false .horizontal
            (latH C code 1 (latticeRepresentativeXId k.1.val))
            (Fin.cons p.re x) = x ⟨latticeRepresentativeXId k.1.val,
              by dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]; omega⟩ := by
          rw [finCons_addOne p.re x _ (by
            dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]; omega)
            hrid] at hr
          simpa [latH] using hr
        have hnr' : evalAffineInOrientation R false .horizontal
            (Expr.scale (centeredInteger k.2.1)
              (latH C code 1 latticeFirstPeriodXId)) (Fin.cons p.re x) =
            (centeredInteger k.2.1 : Real) *
              x ⟨latticeFirstPeriodXId, huxId⟩ := by
          rw [finCons_addOne p.re x _ (by
            dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)
            huxid] at hnr
          simpa [latH] using hnr
        have hmr' : evalAffineInOrientation R false .horizontal
            (Expr.scale (centeredInteger k.2.2)
              (latH C code 1 latticeSecondPeriodXId)) (Fin.cons p.re x) =
            (centeredInteger k.2.2 : Real) *
              x ⟨latticeSecondPeriodXId, hvxId⟩ := by
          rw [finCons_addOne p.re x _ (by
            dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
            hvxid] at hmr
          simpa [latH] using hmr
        simp only [latticeCentreX, evalAffineInOrientation_add]
        rw [hr', hnr', hmr']
        have hsmulRe (n : Int) (z : Complex) :
            (n • z).re = (n : Real) * z.re := by
          rw [Complex.smul_re, ← Int.cast_smul_eq_zsmul Real n z.re]
          simp [smul_eq_mul]
        dsimp [latticeSemanticCentre, X]
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          hsmulRe, mul_zero, sub_zero, add_zero, zero_mul]
      have evalCentreYShift : ∀ k : LatticeFiniteIndex code,
          evalAffineInOrientation R false .vertical
              (latticeCentreY C code 1 k) (Fin.cons p.im y) =
            (latticeSemanticCentre code X k.1
              (centeredInteger k.2.1) (centeredInteger k.2.2)).im := by
        intro k
        have hrid : latticeRepresentativeYId k.1.val + 1 <
            latticeVerticalVariableCount code + 1 := by
          dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
          omega
        have huyid : latticeFirstPeriodYId + 1 <
            latticeVerticalVariableCount code + 1 := by
          dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]
          omega
        have hvyid : latticeSecondPeriodYId + 1 <
            latticeVerticalVariableCount code + 1 := by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]
          omega
        have hr := evalAffineInOrientation_var R false .vertical
          (Fin.cons p.im y) (latticeRepresentativeYId k.1.val + 1) hrid
        have hnr := evalAffineInOrientation_scale_var R false .vertical
          (centeredInteger k.2.1 : Rat) (Fin.cons p.im y)
          (latticeFirstPeriodYId + 1) huyid
        have hmr := evalAffineInOrientation_scale_var R false .vertical
          (centeredInteger k.2.2 : Rat) (Fin.cons p.im y)
          (latticeSecondPeriodYId + 1) hvyid
        have hr' : evalAffineInOrientation R false .vertical
            (latV C code 1 (latticeRepresentativeYId k.1.val))
            (Fin.cons p.im y) = y ⟨latticeRepresentativeYId k.1.val,
              by dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]; omega⟩ := by
          rw [finCons_addOne p.im y _ (by
            dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]; omega)
            hrid] at hr
          simpa [latV] using hr
        have hnr' : evalAffineInOrientation R false .vertical
            (Expr.scale (centeredInteger k.2.1)
              (latV C code 1 latticeFirstPeriodYId)) (Fin.cons p.im y) =
            (centeredInteger k.2.1 : Real) *
              y ⟨latticeFirstPeriodYId, huyId⟩ := by
          rw [finCons_addOne p.im y _ (by
            dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)
            huyid] at hnr
          simpa [latV] using hnr
        have hmr' : evalAffineInOrientation R false .vertical
            (Expr.scale (centeredInteger k.2.2)
              (latV C code 1 latticeSecondPeriodYId)) (Fin.cons p.im y) =
            (centeredInteger k.2.2 : Real) *
              y ⟨latticeSecondPeriodYId, hvyId⟩ := by
          rw [finCons_addOne p.im y _ (by
            dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
            hvyid] at hmr
          simpa [latV] using hmr
        simp only [latticeCentreY, evalAffineInOrientation_add]
        rw [hr', hnr', hmr']
        have hsmulIm (n : Int) (z : Complex) :
            (n • z).im = (n : Real) * z.im := by
          rw [Complex.smul_im, ← Int.cast_smul_eq_zsmul Real n z.im]
          simp [smul_eq_mul]
        dsimp [latticeSemanticCentre, X]
        simp only [Complex.add_im, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
          hsmulIm, mul_zero, add_zero]
        ring
      have hqv0 : formulaHoldsInOrientation R false
          (closedCellFormula false e (latticeCentreX C code 1 j)
            (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
            (latticeCentreY C code 1 j)
            (Expr.var C (latticeVerticalVariableCount code + 1) 0))
          (Fin.cons p.re x) (Fin.cons p.im y) := by
        simpa [Function.comp_apply] using hqv
      have hqv' := (closedCellFormula_holds_iff R e
        (latticeCentreX C code 1 j)
        (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
        (latticeCentreY C code 1 j)
        (Expr.var C (latticeVerticalVariableCount code + 1) 0)
        (Fin.cons p.re x) (Fin.cons p.im y)).mp hqv0
      simp only [evalAffineInOrientation_add] at hqv'
      rw [evalCentreXShift j, evalCentreYShift j, hxh', hyv'] at hqv'
      rw [evalSelectedCellLeftHorizontal R e (Fin.cons p.re x),
        evalSelectedCellHorizontal R e (Fin.cons p.re x)] at hqv'
      have hbottom := evalSelectedCellVertical R e (Fin.cons p.im y) false
      have htop := evalSelectedCellVertical R e (Fin.cons p.im y) true
      have hbottom' : evalAffineInOrientation R false .vertical
          (Expr.input (latticeVerticalVariableCount code + 1)
            (selectedCellBottom C false e)) (Fin.cons p.im y) =
          (R.vertex (C.bottomVertex e)).im := by
        simpa using hbottom
      have htop' : evalAffineInOrientation R false .vertical
          (Expr.input (latticeVerticalVariableCount code + 1)
            (selectedCellTop C false e)) (Fin.cons p.im y) =
          (R.vertex (C.topVertex e)).im := by
        simpa using htop
      rw [hbottom', htop'] at hqv'
      refine ⟨j, hj, e, ?_⟩
      change
        (latticeSemanticCentre code X j.1
            (centeredInteger j.2.1) (centeredInteger j.2.2)).re +
            (R.vertex (C.leftVertex e)).re ≤ p.re ∧
          p.re ≤
            (latticeSemanticCentre code X j.1
              (centeredInteger j.2.1) (centeredInteger j.2.2)).re +
              (R.vertex (C.rightVertex e)).re ∧
          (latticeSemanticCentre code X j.1
            (centeredInteger j.2.1) (centeredInteger j.2.2)).im +
              (R.vertex (C.bottomVertex e)).im ≤ p.im ∧
          p.im ≤
            (latticeSemanticCentre code X j.1
              (centeredInteger j.2.1) (centeredInteger j.2.2)).im +
              (R.vertex (C.topVertex e)).im
      exact hqv'
  · rintro ⟨X, hX⟩
    rcases latticeReverseCanonicalEvaluations R code X with
      ⟨x, y, hxux, hxvx, hxrep, hxhx, huxb, hyuy, hyvy, hyrep, hyhy⟩
    refine ⟨y, ?_⟩
    rw [formulaHolds_closeHorizontal]
    refine ⟨x, ?_⟩
    simp only [latticeBody, Formula.andList, formulaHoldsInOrientation]
    rcases hX with
      ⟨hsep, hbounds, hperiod, hrep, hfirst, hux, hsecond, hpack, hcov⟩
    have hxux0 : x ⟨latticeFirstPeriodXId, by
        dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
        X.firstPeriod.re := by
      calc
        x ⟨latticeFirstPeriodXId, by
            dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 latticeFirstPeriodXId) x := by
                simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                  latticeFirstPeriodXId (by
                    dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)).symm
        _ = X.firstPeriod.re := hxux
    have hxvx0 : x ⟨latticeSecondPeriodXId, by
        dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
        X.secondPeriod.re := by
      calc
        x ⟨latticeSecondPeriodXId, by
            dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 latticeSecondPeriodXId) x := by
                simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                  latticeSecondPeriodXId (by
                    dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)).symm
        _ = X.secondPeriod.re := hxvx
    have hyuy0 : y ⟨latticeFirstPeriodYId, by
        dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
        X.firstPeriod.im := by
      calc
        y ⟨latticeFirstPeriodYId, by
            dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .vertical
              (latV C code 0 latticeFirstPeriodYId) y := by
                simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                  latticeFirstPeriodYId (by
                    dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)).symm
        _ = X.firstPeriod.im := hyuy
    have hyvy0 : y ⟨latticeSecondPeriodYId, by
        dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
        X.secondPeriod.im := by
      calc
        y ⟨latticeSecondPeriodYId, by
            dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .vertical
              (latV C code 0 latticeSecondPeriodYId) y := by
                simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                  latticeSecondPeriodYId (by
                    dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)).symm
        _ = X.secondPeriod.im := hyvy
    have hxhx' : evalAffineInOrientation R false .horizontal
        (Expr.var C (latticeHorizontalVariableCount code)
          (latticeHorizontalBoundId code)) x = X.horizontalBound := by
      simpa [latH] using hxhx
    have hyhy' : evalAffineInOrientation R false .vertical
        (Expr.var C (latticeVerticalVariableCount code)
          (latticeVerticalBoundId code)) y = X.verticalBound := by
      simpa [latV] using hyhy
    have hsep' :
        0 < evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeSecondPeriodXId) x ∧
        0 < evalAffineInOrientation R false .vertical
            (latV C code 0 latticeSecondPeriodYId) y ∧
        0 < evalAffineInOrientation R false .horizontal
            (Expr.sub (latH C code 0 latticeFirstPeriodXId)
              (Expr.scale code.rationalSeparator
                (latH C code 0 latticeSecondPeriodXId))) x ∧
        0 < evalAffineInOrientation R false .vertical
            (Expr.sub (Expr.scale code.rationalSeparator
                (latV C code 0 latticeSecondPeriodYId))
              (latV C code 0 latticeFirstPeriodYId)) y ∧
        0 < evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeHorizontalBoundId code)) x ∧
        0 < evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeVerticalBoundId code)) y := by
      have hax : evalAffineInOrientation R false .horizontal
          (Expr.sub (latH C code 0 latticeFirstPeriodXId)
            (Expr.scale code.rationalSeparator
              (latH C code 0 latticeSecondPeriodXId))) x =
          X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re := by
        rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
          evalAffineInOrientation_add, evalAffineInOrientation_neg]
        rw [hxux]
        have hs := evalAffineInOrientation_scale_var R false .horizontal
          code.rationalSeparator x latticeSecondPeriodXId (by
            dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
        have hs' : evalAffineInOrientation R false .horizontal
            (Expr.scale code.rationalSeparator
              (latH C code 0 latticeSecondPeriodXId)) x =
            code.rationalSeparator * X.secondPeriod.re := by
          simpa [latH, Complex.add_re, Complex.mul_re, hxvx0] using hs
        rw [hs']
        ring
      have hay : evalAffineInOrientation R false .vertical
          (Expr.sub (Expr.scale code.rationalSeparator
              (latV C code 0 latticeSecondPeriodYId))
            (latV C code 0 latticeFirstPeriodYId)) y =
          code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im := by
        rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
          evalAffineInOrientation_add, evalAffineInOrientation_neg]
        have hs := evalAffineInOrientation_scale_var R false .vertical
          code.rationalSeparator y latticeSecondPeriodYId (by
            dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
        have hs' : evalAffineInOrientation R false .vertical
            (Expr.scale code.rationalSeparator
              (latV C code 0 latticeSecondPeriodYId)) y =
            code.rationalSeparator * X.secondPeriod.im := by
          simpa [latV, Complex.add_im, Complex.mul_im, hyvy0] using hs
        rw [hs', hyuy]
        ring
      exact ⟨by simpa [hxvx] using hsep.1,
        by simpa [hyvy] using hsep.2.1,
        by simpa [hax] using hsep.2.2.1,
        by simpa [hay] using hsep.2.2.2,
        by simpa [hxhx] using hbounds.1,
        by simpa [hyhy] using hbounds.2⟩
    have hperiod' : ∀ sx ∈ ([-1, 1] : List Int), ∀ sy ∈ ([-1, 1] : List Int),
        evalAffineInOrientation R false .horizontal
            (Expr.add (Expr.scale (sx : Rat)
              (latH C code 0 latticeFirstPeriodXId))
              (Expr.scale (sy : Rat)
                (latH C code 0 latticeSecondPeriodXId))) x ≤
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x ∧
        evalAffineInOrientation R false .vertical
            (Expr.add (Expr.scale (sx : Rat)
              (latV C code 0 latticeFirstPeriodYId))
              (Expr.scale (sy : Rat)
                (latV C code 0 latticeSecondPeriodYId))) y ≤
            evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y := by
      intro sx hs sy hsy
      have hsx := evalAffineInOrientation_scale_var R false .horizontal
        (sx : Rat) x latticeFirstPeriodXId (by
          dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)
      have hsy' := evalAffineInOrientation_scale_var R false .horizontal
        (sy : Rat) x latticeSecondPeriodXId (by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
      have hsxv := evalAffineInOrientation_scale_var R false .vertical
        (sx : Rat) y latticeFirstPeriodYId (by
          dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)
      have hsyv := evalAffineInOrientation_scale_var R false .vertical
        (sy : Rat) y latticeSecondPeriodYId (by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
      have h := hperiod sx hs sy hsy
      constructor
      · rw [evalAffineInOrientation_add]
        simpa [latH, hsx, hsy', hxux0, hxvx0, hxhx'] using h.1
      · rw [evalAffineInOrientation_add]
        simpa [latV, hsxv, hsyv, hyuy0, hyvy0, hyhy'] using h.2
    have hrep' : ∀ (r : Fin code.representativeCount),
        |evalAffineInOrientation R false .horizontal
            (latH C code 0 (latticeRepresentativeXId r.val)) x| ≤
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x ∧
        |evalAffineInOrientation R false .vertical
            (latV C code 0 (latticeRepresentativeYId r.val)) y| ≤
            evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y := by
      intro r
      constructor
      · simpa [hxrep r, hxhx] using (hrep r).1
      · simpa [hyrep r, hyhy] using (hrep r).2
    have hax : evalAffineInOrientation R false .horizontal
        (Expr.sub (latH C code 0 latticeFirstPeriodXId)
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId))) x =
        X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re := by
      rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
        evalAffineInOrientation_add, evalAffineInOrientation_neg, hxux]
      have hs := evalAffineInOrientation_scale_var R false .horizontal
        code.rationalSeparator x latticeSecondPeriodXId (by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
      have hs' : evalAffineInOrientation R false .horizontal
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId)) x =
          code.rationalSeparator * X.secondPeriod.re := by
        simpa [latH, hxvx0] using hs
      rw [hs']
      ring
    have hay : evalAffineInOrientation R false .vertical
        (Expr.sub (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId))
          (latV C code 0 latticeFirstPeriodYId)) y =
        code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im := by
      rw [show Expr.sub _ _ = Expr.add _ (Expr.neg _) by rfl,
        evalAffineInOrientation_add, evalAffineInOrientation_neg, hyuy]
      have hs := evalAffineInOrientation_scale_var R false .vertical
        code.rationalSeparator y latticeSecondPeriodYId (by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
      have hs' : evalAffineInOrientation R false .vertical
          (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId)) y =
          code.rationalSeparator * X.secondPeriod.im := by
        simpa [latV, hyvy0] using hs
      rw [hs']
      ring
    have hxhx0 : x ⟨latticeHorizontalBoundId code, by
        dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
        X.horizontalBound := by
      calc
        x ⟨latticeHorizontalBoundId code, by
            dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeHorizontalBoundId code)) x := by
                simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                  (latticeHorizontalBoundId code) (by
                    dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)).symm
        _ = X.horizontalBound := hxhx
    have hyhy0 : y ⟨latticeVerticalBoundId code, by
        dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
        X.verticalBound := by
      calc
        y ⟨latticeVerticalBoundId code, by
            dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .vertical
              (latV C code 0 (latticeVerticalBoundId code)) y := by
                simpa [latV] using (evalAffineInOrientation_var R false .vertical y
                  (latticeVerticalBoundId code) (by
                    dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)).symm
        _ = X.verticalBound := hyhy
    have hscaleHBound : ∀ q : Rat,
        evalAffineInOrientation R false .horizontal
            (Expr.scale q (latH C code 0 (latticeHorizontalBoundId code))) x =
          (q : Real) * X.horizontalBound := by
      intro q
      have hz : ∀ i, (latH C code 0 (latticeHorizontalBoundId code)).inputConstant i = 0 := by
        intro i
        simp [latH, Expr.var, Coeff.zero]
      have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
        (latH C code 0 (latticeHorizontalBoundId code)) hz x
      have hv := evalAffineInOrientation_var R false .horizontal x
        (latticeHorizontalBoundId code) (by
          dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)
      have hv' : evalAffineInOrientation R false .horizontal
          (latH C code 0 (latticeHorizontalBoundId code)) x =
          x ⟨latticeHorizontalBoundId code, by
            dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega⟩ := by
        simpa [latH] using hv
      rw [hv'] at hs
      simpa [latH, hxhx0] using hs
    have hscaleAx : ∀ q : Rat,
        evalAffineInOrientation R false .horizontal
            (Expr.scale q (Expr.sub (latH C code 0 latticeFirstPeriodXId)
              (Expr.scale code.rationalSeparator
                (latH C code 0 latticeSecondPeriodXId)))) x =
          (q : Real) *
            (X.firstPeriod.re - code.rationalSeparator * X.secondPeriod.re) := by
      intro q
      have hz : ∀ i, (Expr.sub (latH C code 0 latticeFirstPeriodXId)
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId))).inputConstant i = 0 := by
        intro i
        simp [Expr.sub, Expr.add, Expr.neg, Expr.scale, latH, Expr.var,
          Coeff.zero, Coeff.add, Coeff.neg]
      have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
        (Expr.sub (latH C code 0 latticeFirstPeriodXId)
          (Expr.scale code.rationalSeparator
            (latH C code 0 latticeSecondPeriodXId))) hz x
      simpa [hax] using hs
    have hscaleVBound : ∀ q : Rat,
        evalAffineInOrientation R false .vertical
            (Expr.scale q (latV C code 0 (latticeVerticalBoundId code))) y =
          (q : Real) * X.verticalBound := by
      intro q
      have hz : ∀ i, (latV C code 0 (latticeVerticalBoundId code)).inputConstant i = 0 := by
        intro i
        simp [latV, Expr.var, Coeff.zero]
      have hs := evalAffineInOrientation_scale_of_zero R false .vertical q
        (latV C code 0 (latticeVerticalBoundId code)) hz y
      have hv := evalAffineInOrientation_var R false .vertical y
        (latticeVerticalBoundId code) (by
          dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)
      have hv' : evalAffineInOrientation R false .vertical
          (latV C code 0 (latticeVerticalBoundId code)) y =
          y ⟨latticeVerticalBoundId code, by
            dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega⟩ := by
        simpa [latV] using hv
      rw [hv'] at hs
      simpa [latV, hyhy0] using hs
    have hscaleAy : ∀ q : Rat,
        evalAffineInOrientation R false .vertical
            (Expr.scale q (Expr.sub
              (Expr.scale code.rationalSeparator
                (latV C code 0 latticeSecondPeriodYId))
              (latV C code 0 latticeFirstPeriodYId))) y =
          (q : Real) *
            (code.rationalSeparator * X.secondPeriod.im - X.firstPeriod.im) := by
      intro q
      have hz : ∀ i, (Expr.sub
          (Expr.scale code.rationalSeparator
            (latV C code 0 latticeSecondPeriodYId))
          (latV C code 0 latticeFirstPeriodYId)).inputConstant i = 0 := by
        intro i
        simp [Expr.sub, Expr.add, Expr.neg, Expr.scale, latV, Expr.var,
          Coeff.zero, Coeff.add, Coeff.neg]
      have hs := evalAffineInOrientation_scale_of_zero R false .vertical q
        (Expr.sub (Expr.scale code.rationalSeparator
          (latV C code 0 latticeSecondPeriodYId))
          (latV C code 0 latticeFirstPeriodYId)) hz y
      simpa [hay] using hs
    have hfirstFormula : formulaHoldsInOrientation R false
        (Formula.andList
          (((List.ofFn fun a : Fin C.vertexCount => a).flatMap fun a =>
            (List.ofFn fun b : Fin C.vertexCount => b).map fun b =>
              Formula.andList
                [.horizontalLt
                    (Expr.add (Expr.scale 2
                      (latH C code 0 (latticeHorizontalBoundId code)))
                      (Expr.input (latticeHorizontalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                        (Expr.scale code.rationalSeparator
                          (latH C code 0 latticeSecondPeriodXId)))),
                 .horizontalLt
                    (Expr.add (Expr.scale 2
                      (latH C code 0 (latticeHorizontalBoundId code)))
                      (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                        (Expr.scale code.rationalSeparator
                          (latH C code 0 latticeSecondPeriodXId))))]) ++
           (List.ofFn fun a : Fin C.vertexCount => a).flatMap fun a =>
            (List.ofFn fun b : Fin C.vertexCount => b).map fun b =>
              Formula.andList
                [.verticalLt
                    (Expr.add (Expr.scale 2
                      (latV C code 0 (latticeVerticalBoundId code)))
                      (Expr.input (latticeVerticalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (Expr.sub (Expr.scale code.rationalSeparator
                        (latV C code 0 latticeSecondPeriodYId))
                        (latV C code 0 latticeFirstPeriodYId))),
                 .verticalLt
                    (Expr.add (Expr.scale 2
                      (latV C code 0 (latticeVerticalBoundId code)))
                      (Expr.neg (Expr.input (latticeVerticalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                    (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                      (Expr.sub (Expr.scale code.rationalSeparator
                        (latV C code 0 latticeSecondPeriodYId))
                        (latV C code 0 latticeFirstPeriodYId)))])) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · rcases List.mem_flatMap.mp hp with ⟨a, ha, hp⟩
        rcases List.mem_map.mp hp with ⟨b, hb, rfl⟩
        apply (formulaHolds_andList R false _ x y).mpr
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst q
          simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
            hscaleHBound, hscaleAx]
          have hd := eval_input_vertex_difference_horizontal R a b x
          rw [hd]
          have hh := hfirst.1 a b
          norm_num at hh ⊢
          linarith [hh, le_abs_self ((R.vertex a).re - (R.vertex b).re)]
        · have hq' : q = Formula.horizontalLt
              (Expr.add (Expr.scale 2
                (latH C code 0 (latticeHorizontalBoundId code)))
                (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                  (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
              (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                  (Expr.scale code.rationalSeparator
                    (latH C code 0 latticeSecondPeriodXId)))) := by
            simpa using hq
          subst q
          simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
            evalAffineInOrientation_neg, hscaleHBound, hscaleAx]
          have hd := eval_input_vertex_difference_horizontal R a b x
          rw [hd]
          have hh := hfirst.1 a b
          norm_num at hh ⊢
          linarith [hh, neg_le_abs ((R.vertex a).re - (R.vertex b).re)]
      · rcases List.mem_flatMap.mp hp with ⟨a, ha, hp⟩
        rcases List.mem_map.mp hp with ⟨b, hb, rfl⟩
        apply (formulaHolds_andList R false _ x y).mpr
        intro q hq
        simp only [List.mem_cons] at hq
        rcases hq with hq | hq
        · subst q
          simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
            hscaleVBound, hscaleAy]
          have hd := eval_input_vertex_difference_vertical R a b y
          rw [hd]
          have hh := hfirst.2 a b
          norm_num at hh ⊢
          linarith [hh, le_abs_self ((R.vertex a).im - (R.vertex b).im)]
        · have hq' : q = Formula.verticalLt
              (Expr.add (Expr.scale 2
                (latV C code 0 (latticeVerticalBoundId code)))
                (Expr.neg (Expr.input (latticeVerticalVariableCount code)
                  (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
              (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                (Expr.sub (Expr.scale code.rationalSeparator
                  (latV C code 0 latticeSecondPeriodYId))
                  (latV C code 0 latticeFirstPeriodYId))) := by
            simpa using hq
          subst q
          simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
            evalAffineInOrientation_neg, hscaleVBound, hscaleAy]
          have hd := eval_input_vertex_difference_vertical R a b y
          rw [hd]
          have hh := hfirst.2 a b
          norm_num at hh ⊢
          linarith [hh, neg_le_abs ((R.vertex a).im - (R.vertex b).im)]
    have hrankValues :
        evalAffineInOrientation R false .horizontal
            (Expr.zero C (latticeHorizontalVariableCount code)) x <
              evalAffineInOrientation R false .horizontal
                (latH C code 0 latticeSecondPeriodXId) x ∧
        evalAffineInOrientation R false .vertical
            (Expr.zero C (latticeVerticalVariableCount code)) y <
              evalAffineInOrientation R false .vertical
                (latV C code 0 latticeSecondPeriodYId) y ∧
        evalAffineInOrientation R false .horizontal
            (Expr.zero C (latticeHorizontalVariableCount code)) x <
              evalAffineInOrientation R false .horizontal
                (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                  (Expr.scale code.rationalSeparator
                    (latH C code 0 latticeSecondPeriodXId))) x ∧
        evalAffineInOrientation R false .vertical
            (Expr.zero C (latticeVerticalVariableCount code)) y <
              evalAffineInOrientation R false .vertical
                (Expr.sub (Expr.scale code.rationalSeparator
                    (latV C code 0 latticeSecondPeriodYId))
                  (latV C code 0 latticeFirstPeriodYId)) y ∧
        evalAffineInOrientation R false .horizontal
            (Expr.zero C (latticeHorizontalVariableCount code)) x <
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeHorizontalBoundId code)) x ∧
        evalAffineInOrientation R false .vertical
            (Expr.zero C (latticeVerticalVariableCount code)) y <
              evalAffineInOrientation R false .vertical
                (latV C code 0 (latticeVerticalBoundId code)) y ∧ True := by
      simpa only [evalAffineInOrientation_zero] using
        ⟨hsep'.1, hsep'.2.1, hsep'.2.2.1, hsep'.2.2.2.1,
          hsep'.2.2.2.2.1, hsep'.2.2.2.2.2, True.intro⟩
    have huxFormula :
        evalAffineInOrientation R false .horizontal
            (Expr.zero C (latticeHorizontalVariableCount code)) x ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x ∧
        evalAffineInOrientation R false .horizontal
            (latH C code 0 latticeFirstPeriodXId) x ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x ∧
        evalAffineInOrientation R false .horizontal
            (Expr.neg (latH C code 0 latticeFirstPeriodXId)) x ≤
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x ∧ True := by
      simpa only [evalAffineInOrientation_zero, evalAffineInOrientation_neg,
        hxux, huxb] using
        ⟨hux.1, hux.2.1, hux.2.2, True.intro⟩
    have hrankFormula : formulaHoldsInOrientation R false
        (Formula.andList
          [.horizontalLt (Expr.zero C (latticeHorizontalVariableCount code))
              (latH C code 0 latticeSecondPeriodXId),
           .verticalLt (Expr.zero C (latticeVerticalVariableCount code))
              (latV C code 0 latticeSecondPeriodYId),
           .horizontalLt (Expr.zero C (latticeHorizontalVariableCount code))
              (Expr.sub (latH C code 0 latticeFirstPeriodXId)
                (Expr.scale code.rationalSeparator
                  (latH C code 0 latticeSecondPeriodXId))),
           .verticalLt (Expr.zero C (latticeVerticalVariableCount code))
              (Expr.sub (Expr.scale code.rationalSeparator
                  (latV C code 0 latticeSecondPeriodYId))
                (latV C code 0 latticeFirstPeriodYId)),
           .horizontalLt (Expr.zero C (latticeHorizontalVariableCount code))
              (latH C code 0 (latticeHorizontalBoundId code)),
           .verticalLt (Expr.zero C (latticeVerticalVariableCount code))
              (latV C code 0 (latticeVerticalBoundId code))]) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | hfalse
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.1
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.2.1
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.2.2.1
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.2.2.2.1
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.2.2.2.2.1
      · simpa only [formulaHoldsInOrientation, evalAffineInOrientation_zero] using hsep'.2.2.2.2.2
      · simp at hfalse
    have hperiodFormula : formulaHoldsInOrientation R false
        (Formula.andList
          (([1, -1] : List Int).flatMap fun s : Int =>
            ([1, -1] : List Int).map fun t : Int => Formula.andList
              [.horizontalLe
                  (Expr.add (Expr.scale s
                    (latH C code 0 latticeFirstPeriodXId))
                    (Expr.scale t
                      (latH C code 0 latticeSecondPeriodXId)))
                  (latH C code 0 (latticeHorizontalBoundId code)),
               .verticalLe
                  (Expr.add (Expr.scale s
                    (latV C code 0 latticeFirstPeriodYId))
                    (Expr.scale t
                      (latV C code 0 latticeSecondPeriodYId)))
                  (latV C code 0 (latticeVerticalBoundId code))])) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      rcases List.mem_flatMap.mp hp with ⟨s, hs, hp⟩
      rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
      have hs' : s ∈ ([-1, 1] : List Int) := by simpa [or_comm] using hs
      have ht' : t ∈ ([-1, 1] : List Int) := by simpa [or_comm] using ht
      apply (formulaHolds_andList R false _ x y).mpr
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        simp only [formulaHoldsInOrientation]
        simpa [latH, evalAffineInOrientation_scale_var, hxux0, hxvx0, hxhx'] using
          (hperiod' s hs' t ht').1
      · have hq' : q = Formula.verticalLe
            (Expr.add (Expr.scale s
              (latV C code 0 latticeFirstPeriodYId))
              (Expr.scale t
                (latV C code 0 latticeSecondPeriodYId)))
            (latV C code 0 (latticeVerticalBoundId code)) := by
          simpa using hq
        subst q
        simp only [formulaHoldsInOrientation]
        simpa [latV, evalAffineInOrientation_scale_var, hyuy0, hyvy0, hyhy'] using
          (hperiod' s hs' t ht').2
    have hrepFormula : formulaHoldsInOrientation R false
        (Formula.andList ((List.ofFn fun r : Fin code.representativeCount => r).map
          (fun r => Formula.andList
            [.horizontalLe
                (Expr.neg (latH C code 0 (latticeHorizontalBoundId code)))
                (latH C code 0 (latticeRepresentativeXId r.val)),
             .horizontalLe
                (latH C code 0 (latticeRepresentativeXId r.val))
                (latH C code 0 (latticeHorizontalBoundId code)),
             .verticalLe
                (Expr.neg (latV C code 0 (latticeVerticalBoundId code)))
                (latV C code 0 (latticeRepresentativeYId r.val)),
             .verticalLe
                (latV C code 0 (latticeRepresentativeYId r.val))
                (latV C code 0 (latticeVerticalBoundId code))]))) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      rcases List.mem_map.mp hp with ⟨r, hr, rfl⟩
      apply (formulaHolds_andList R false _ x y).mpr
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        simp only [formulaHoldsInOrientation]
        rw [evalAffineInOrientation_neg]
        rw [hxhx, hxrep r]
        exact (abs_le.mp (hrep r).1).1
      · rcases hq with hq | hq
        · subst q
          simp only [formulaHoldsInOrientation]
          rw [hxrep r, hxhx]
          exact (abs_le.mp (hrep r).1).2
        · rcases hq with hq | hq
          · subst q
            simp only [formulaHoldsInOrientation]
            rw [evalAffineInOrientation_neg, hyhy, hyrep r]
            exact (abs_le.mp (hrep r).2).1
          · have hq' : q = Formula.verticalLe
                (latV C code 0 (latticeRepresentativeYId r.val))
                (latV C code 0 (latticeVerticalBoundId code)) := by
              simpa using hq
            subst q
            simp only [formulaHoldsInOrientation]
            rw [hyrep r, hyhy]
            exact (abs_le.mp (hrep r).2).2
    have huxb0 : x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
        dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ =
        X.firstPeriodAbsoluteXBound := by
      calc
        x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
            dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ =
            evalAffineInOrientation R false .horizontal
              (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x := by
                simpa [latH] using (evalAffineInOrientation_var R false .horizontal x
                  (latticeFirstPeriodAbsoluteXBoundId code) (by
                    dsimp [latticeFirstPeriodAbsoluteXBoundId,
                      latticeHorizontalVariableCount]
                    omega)).symm
        _ = X.firstPeriodAbsoluteXBound := huxb
    have hscaleHxa : ∀ q : Rat,
        evalAffineInOrientation R false .horizontal
            (Expr.scale q
              (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code))) x =
          (q : Real) * X.firstPeriodAbsoluteXBound := by
      intro q
      have hz : ∀ i, (latH C code 0
          (latticeFirstPeriodAbsoluteXBoundId code)).inputConstant i = 0 := by
        intro i
        simp [latH, Expr.var, Coeff.zero]
      have hs := evalAffineInOrientation_scale_of_zero R false .horizontal q
        (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) hz x
      have hv := evalAffineInOrientation_var R false .horizontal x
        (latticeFirstPeriodAbsoluteXBoundId code) (by
          dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega)
      have hv' : evalAffineInOrientation R false .horizontal
          (latH C code 0 (latticeFirstPeriodAbsoluteXBoundId code)) x =
          x ⟨latticeFirstPeriodAbsoluteXBoundId code, by
            dsimp [latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalVariableCount]; omega⟩ := by
        simpa [latH] using hv
      rw [hv'] at hs
      simpa [latH, huxb0] using hs
    have hscaleVx : ∀ q : Rat,
        evalAffineInOrientation R false .horizontal
            (Expr.scale q (latH C code 0 latticeSecondPeriodXId)) x =
          (q : Real) * X.secondPeriod.re := by
      intro q
      have hs := evalAffineInOrientation_scale_var R false .horizontal q x
        latticeSecondPeriodXId (by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
      simpa [latH, hxvx0] using hs
    have hsecondFormula : formulaHoldsInOrientation R false
        (Formula.andList
          ((List.ofFn fun a : Fin C.vertexCount => a).flatMap fun a =>
            (List.ofFn fun b : Fin C.vertexCount => b).map fun b =>
              Formula.andList
                [.horizontalLt
                    (Expr.add
                      (Expr.add (Expr.scale 2
                        (latH C code 0 (latticeHorizontalBoundId code)))
                        (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                          (latH C code 0
                            (latticeFirstPeriodAbsoluteXBoundId code))))
                      (Expr.input (latticeHorizontalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))))
                    (Expr.scale (Int.ofNat code.secondIndexBound : Rat)
                      (latH C code 0 latticeSecondPeriodXId)),
                 .horizontalLt
                    (Expr.add
                      (Expr.add (Expr.scale 2
                        (latH C code 0 (latticeHorizontalBoundId code)))
                        (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                          (latH C code 0
                            (latticeFirstPeriodAbsoluteXBoundId code))))
                      (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                        (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
                    (Expr.scale (Int.ofNat code.secondIndexBound : Rat)
                      (latH C code 0 latticeSecondPeriodXId))])) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      rcases List.mem_flatMap.mp hp with ⟨a, ha, hp⟩
      rcases List.mem_map.mp hp with ⟨b, hb, rfl⟩
      apply (formulaHolds_andList R false _ x y).mpr
      intro q hq
      simp only [List.mem_cons] at hq
      rcases hq with hq | hq
      · subst q
        simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
          hscaleHBound, hscaleHxa, hscaleVx]
        rw [eval_input_vertex_difference_horizontal]
        have hh := hsecond a b
        norm_num at hh ⊢
        linarith [hh, le_abs_self ((R.vertex a).re - (R.vertex b).re)]
      · have hq' : q = Formula.horizontalLt
            (Expr.add
              (Expr.add (Expr.scale 2
                (latH C code 0 (latticeHorizontalBoundId code)))
                (Expr.scale (Int.ofNat code.firstIndexBound : Rat)
                  (latH C code 0
                    (latticeFirstPeriodAbsoluteXBoundId code))))
              (Expr.neg (Expr.input (latticeHorizontalVariableCount code)
                (Coeff.sub (Coeff.single a 1) (Coeff.single b 1)))))
            (Expr.scale (Int.ofNat code.secondIndexBound : Rat)
              (latH C code 0 latticeSecondPeriodXId)) := by
          simpa using hq
        subst q
        simp only [formulaHoldsInOrientation, evalAffineInOrientation_add,
          evalAffineInOrientation_neg, hscaleHBound, hscaleHxa, hscaleVx]
        rw [eval_input_vertex_difference_horizontal]
        have hh := hsecond a b
        norm_num at hh ⊢
        linarith [hh, neg_le_abs ((R.vertex a).re - (R.vertex b).re)]
    have evalCentreX : ∀ j : LatticeFiniteIndex code,
        evalAffineInOrientation R false .horizontal
            (latticeCentreX C code 0 j) x =
          (latticeSemanticCentre code X j.1
            (centeredInteger j.2.1) (centeredInteger j.2.2)).re := by
      intro j
      have hrid : latticeRepresentativeXId j.1.val <
          latticeHorizontalVariableCount code := by
        dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]
        omega
      have hr := evalAffineInOrientation_var R false .horizontal x
        (latticeRepresentativeXId j.1.val) hrid
      have hnr := evalAffineInOrientation_scale_var R false .horizontal
        (centeredInteger j.2.1 : Rat) x latticeFirstPeriodXId (by
          dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega)
      have hmr := evalAffineInOrientation_scale_var R false .horizontal
        (centeredInteger j.2.2 : Rat) x latticeSecondPeriodXId (by
          dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)
      have hr' : evalAffineInOrientation R false .horizontal
          (latH C code 0 (latticeRepresentativeXId j.1.val)) x =
          x ⟨latticeRepresentativeXId j.1.val, hrid⟩ := by
        simpa [latH] using hr
      have hnr' : evalAffineInOrientation R false .horizontal
          (Expr.scale (centeredInteger j.2.1)
            (latH C code 0 latticeFirstPeriodXId)) x =
          (centeredInteger j.2.1 : Real) *
            x ⟨latticeFirstPeriodXId, by
              dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega⟩ := by
        simpa [latH] using hnr
      have hmr' : evalAffineInOrientation R false .horizontal
          (Expr.scale (centeredInteger j.2.2)
            (latH C code 0 latticeSecondPeriodXId)) x =
          (centeredInteger j.2.2 : Real) *
            x ⟨latticeSecondPeriodXId, by
              dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega⟩ := by
        simpa [latH] using hmr
      have hr0 : x ⟨latticeRepresentativeXId j.1.val, hrid⟩ =
          (X.representative j.1).re := by
        calc
          x ⟨latticeRepresentativeXId j.1.val, hrid⟩ =
              evalAffineInOrientation R false .horizontal
                (latH C code 0 (latticeRepresentativeXId j.1.val)) x := by
                  simpa [latH] using hr.symm
          _ = (X.representative j.1).re := hxrep j.1
      simp only [latticeCentreX, evalAffineInOrientation_add]
      rw [hr', hnr', hmr', hr0, hxux0, hxvx0]
      have hsmulRe (n : Int) (z : Complex) :
          (n • z).re = (n : Real) * z.re := by
        rw [Complex.smul_re, ← Int.cast_smul_eq_zsmul Real n z.re]
        simp [smul_eq_mul]
      dsimp [latticeSemanticCentre]
      simp only [hsmulRe]
    have evalCentreY : ∀ j : LatticeFiniteIndex code,
        evalAffineInOrientation R false .vertical
            (latticeCentreY C code 0 j) y =
          (latticeSemanticCentre code X j.1
            (centeredInteger j.2.1) (centeredInteger j.2.2)).im := by
      intro j
      have hrid : latticeRepresentativeYId j.1.val <
          latticeVerticalVariableCount code := by
        dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]
        omega
      have hr := evalAffineInOrientation_var R false .vertical y
        (latticeRepresentativeYId j.1.val) hrid
      have hnr := evalAffineInOrientation_scale_var R false .vertical
        (centeredInteger j.2.1 : Rat) y latticeFirstPeriodYId (by
          dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega)
      have hmr := evalAffineInOrientation_scale_var R false .vertical
        (centeredInteger j.2.2 : Rat) y latticeSecondPeriodYId (by
          dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)
      have hr' : evalAffineInOrientation R false .vertical
          (latV C code 0 (latticeRepresentativeYId j.1.val)) y =
          y ⟨latticeRepresentativeYId j.1.val, hrid⟩ := by
        simpa [latV] using hr
      have hnr' : evalAffineInOrientation R false .vertical
          (Expr.scale (centeredInteger j.2.1)
            (latV C code 0 latticeFirstPeriodYId)) y =
          (centeredInteger j.2.1 : Real) *
            y ⟨latticeFirstPeriodYId, by
              dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega⟩ := by
        simpa [latV] using hnr
      have hmr' : evalAffineInOrientation R false .vertical
          (Expr.scale (centeredInteger j.2.2)
            (latV C code 0 latticeSecondPeriodYId)) y =
          (centeredInteger j.2.2 : Real) *
            y ⟨latticeSecondPeriodYId, by
              dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega⟩ := by
        simpa [latV] using hmr
      have hr0 : y ⟨latticeRepresentativeYId j.1.val, hrid⟩ =
          (X.representative j.1).im := by
        calc
          y ⟨latticeRepresentativeYId j.1.val, hrid⟩ =
              evalAffineInOrientation R false .vertical
                (latV C code 0 (latticeRepresentativeYId j.1.val)) y := by
                  simpa [latV] using hr.symm
          _ = (X.representative j.1).im := hyrep j.1
      simp only [latticeCentreY, evalAffineInOrientation_add]
      rw [hr', hnr', hmr', hr0, hyuy0, hyvy0]
      have hsmulIm (n : Int) (z : Complex) :
          (n • z).im = (n : Real) * z.im := by
        rw [Complex.smul_im, ← Int.cast_smul_eq_zsmul Real n z.im]
        simp [smul_eq_mul]
      dsimp [latticeSemanticCentre]
      simp only [hsmulIm]
    have hpackFormula : formulaHoldsInOrientation R false
        (Formula.andList
          ((latticeFiniteIndices code).flatMap fun i =>
            (latticeFiniteIndices code).map fun i' =>
              if i = i' then Formula.truth else
                Formula.disjunction
                  (sameCentreFormula (latticeCentreX C code 0 i)
                    (latticeCentreX C code 0 i')
                    (latticeCentreY C code 0 i)
                    (latticeCentreY C code 0 i'))
                  (Formula.andList
                    ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
                      (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                        cellNonoverlapFormula false e e'
                          (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
                          (latticeCentreY C code 0 i) (latticeCentreY C code 0 i'))))) x y := by
      apply (formulaHolds_andList R false _ x y).mpr
      intro p hp
      rcases List.mem_flatMap.mp hp with ⟨i, hi, hp⟩
      rcases List.mem_map.mp hp with ⟨i', hi', rfl⟩
      by_cases heq : i = i'
      · subst i'
        simp [formulaHoldsInOrientation]
      · have hsem := hpack i i' hi hi' heq
        simp only [if_neg heq]
        change
          formulaHoldsInOrientation R false
              (sameCentreFormula (latticeCentreX C code 0 i)
                (latticeCentreX C code 0 i')
                (latticeCentreY C code 0 i)
                (latticeCentreY C code 0 i')) x y ∨
            formulaHoldsInOrientation R false
              (Formula.andList
                ((List.ofFn fun e : Fin C.cellCount => e).flatMap fun e =>
                  (List.ofFn fun e' : Fin C.cellCount => e').map fun e' =>
                    cellNonoverlapFormula false e e'
                      (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
                      (latticeCentreY C code 0 i) (latticeCentreY C code 0 i'))) x y
        rcases hsem with hcentre | hcells
        · apply Or.inl
          apply (sameCentreFormula_holds_iff R
            (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
            (latticeCentreY C code 0 i) (latticeCentreY C code 0 i') x y).mpr
          constructor
          · rw [evalCentreX i, evalCentreX i']
            exact congrArg Complex.re hcentre
          · rw [evalCentreY i, evalCentreY i']
            exact congrArg Complex.im hcentre
        · apply Or.inr
          apply (formulaHolds_andList R false _ x y).mpr
          intro q hq
          rcases List.mem_flatMap.mp hq with ⟨e, he, hq⟩
          rcases List.mem_map.mp hq with ⟨e', he', rfl⟩
          apply (cellNonoverlapFormula_holds_iff R e e'
            (latticeCentreX C code 0 i) (latticeCentreX C code 0 i')
            (latticeCentreY C code 0 i) (latticeCentreY C code 0 i') x y).mpr
          simp only [evalAffineInOrientation_add]
          simp only [Nat.add_zero]
          rw [evalCentreX i, evalCentreX i', evalCentreY i, evalCentreY i']
          rw [evalSelectedCellHorizontal R e x,
            evalSelectedCellLeftHorizontal R e' x,
            evalSelectedCellHorizontal R e' x,
            evalSelectedCellLeftHorizontal R e x]
          have htop : ∀ z : Fin C.cellCount,
              evalAffineInOrientation R false .vertical
                  (Expr.input (latticeVerticalVariableCount code)
                    (selectedCellTop C false z)) y =
                (R.vertex (C.topVertex z)).im := by
            intro z
            simpa using evalSelectedCellVertical R z y true
          have hbottom : ∀ z : Fin C.cellCount,
              evalAffineInOrientation R false .vertical
                  (Expr.input (latticeVerticalVariableCount code)
                    (selectedCellBottom C false z)) y =
                (R.vertex (C.bottomVertex z)).im := by
            intro z
            simpa using evalSelectedCellVertical R z y false
          rw [htop e, hbottom e', htop e', hbottom e]
          exact hcells e e'
    refine ⟨hrankValues, hperiodFormula, hrepFormula, hfirstFormula, huxFormula,
      hsecondFormula, hpackFormula, by
        refine ⟨?_, True.intro⟩
        apply (formulaHolds_forallHorizontal_general R false _ x y).mpr
        intro px
        apply (formulaHolds_forallVertical_general R false _ (Fin.cons px x) y).mpr
        intro py
        simp only [Formula.implication, formulaHoldsInOrientation]
        by_cases hinside :
            (evalAffineInOrientation R false .horizontal
                (Expr.neg (latH C code 1 (latticeHorizontalBoundId code)))
                (Fin.cons px x) <
              evalAffineInOrientation R false .horizontal
                (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
                (Fin.cons px x) ∧
            evalAffineInOrientation R false .horizontal
                (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
                (Fin.cons px x) <
              evalAffineInOrientation R false .horizontal
                (latH C code 1 (latticeHorizontalBoundId code))
                (Fin.cons px x) ∧
            evalAffineInOrientation R false .vertical
                (Expr.neg (latV C code 1 (latticeVerticalBoundId code)))
                (Fin.cons py y) <
              evalAffineInOrientation R false .vertical
                (Expr.var C (latticeVerticalVariableCount code + 1) 0)
                (Fin.cons py y) ∧
            evalAffineInOrientation R false .vertical
                (Expr.var C (latticeVerticalVariableCount code + 1) 0)
                (Fin.cons py y) <
              evalAffineInOrientation R false .vertical
                (latV C code 1 (latticeVerticalBoundId code))
                (Fin.cons py y) ∧ True)
        · right
          have hbhid : latticeHorizontalBoundId code + 1 <
              latticeHorizontalVariableCount code + 1 := by
            dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]
            omega
          have hbvid : latticeVerticalBoundId code + 1 <
              latticeVerticalVariableCount code + 1 := by
            dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]
            omega
          have hbh := evalAffineInOrientation_var R false .horizontal
            (Fin.cons px x) (latticeHorizontalBoundId code + 1) hbhid
          have hbv := evalAffineInOrientation_var R false .vertical
            (Fin.cons py y) (latticeVerticalBoundId code + 1) hbvid
          have hxh := evalAffineInOrientation_var R false .horizontal
            (Fin.cons px x) 0 (by omega)
          have hyv := evalAffineInOrientation_var R false .vertical
            (Fin.cons py y) 0 (by omega)
          have hbh' : evalAffineInOrientation R false .horizontal
              (latH C code 1 (latticeHorizontalBoundId code))
              (Fin.cons px x) = X.horizontalBound := by
            rw [finCons_addOne px x _ (by
              dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)
              hbhid] at hbh
            have h0 := evalAffineInOrientation_var R false .horizontal x
              (latticeHorizontalBoundId code) (by
                dsimp [latticeHorizontalBoundId, latticeHorizontalVariableCount]; omega)
            simpa [latH] using hbh.trans (h0.symm.trans hxhx)
          have hbv' : evalAffineInOrientation R false .vertical
              (latV C code 1 (latticeVerticalBoundId code))
              (Fin.cons py y) = X.verticalBound := by
            rw [finCons_addOne py y _ (by
              dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)
              hbvid] at hbv
            have h0 := evalAffineInOrientation_var R false .vertical y
              (latticeVerticalBoundId code) (by
                dsimp [latticeVerticalBoundId, latticeVerticalVariableCount]; omega)
            simpa [latV] using hbv.trans (h0.symm.trans hyhy)
          have hxh' : evalAffineInOrientation R false .horizontal
              (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
              (Fin.cons px x) = px := by
            simpa using hxh
          have hyv' : evalAffineInOrientation R false .vertical
              (Expr.var C (latticeVerticalVariableCount code + 1) 0)
              (Fin.cons py y) = py := by
            simpa using hyv
          have hpoint : -X.horizontalBound < px ∧ px < X.horizontalBound ∧
              -X.verticalBound < py ∧ py < X.verticalBound := by
            simpa [evalAffineInOrientation_neg, hbh', hbv', hxh', hyv']
              using hinside
          let p : Tiling.Plane := px + py * Complex.I
          have hp : p ∈ latticeOpenCheckingBox code X := by
            change -X.horizontalBound < p.re ∧ p.re < X.horizontalBound ∧
              -X.verticalBound < p.im ∧ p.im < X.verticalBound
            dsimp [p]
            simpa using hpoint
          rcases hcov p hp with ⟨j, hj, e, he⟩
          have hshiftH : ∀ (id : Nat) (hid : id < latticeHorizontalVariableCount code),
              evalAffineInOrientation R false .horizontal
                  (latH C code 1 id) (Fin.cons px x) =
                evalAffineInOrientation R false .horizontal
                  (latH C code 0 id) x := by
            intro id hid
            have h1 := evalAffineInOrientation_var R false .horizontal
              (Fin.cons px x) (id + 1) (by omega)
            rw [finCons_addOne px x id (by omega) (by omega)] at h1
            have h0 := evalAffineInOrientation_var R false .horizontal x id hid
            simpa [latH] using h1.trans h0.symm
          have hshiftV : ∀ (id : Nat) (hid : id < latticeVerticalVariableCount code),
              evalAffineInOrientation R false .vertical
                  (latV C code 1 id) (Fin.cons py y) =
                evalAffineInOrientation R false .vertical
                  (latV C code 0 id) y := by
            intro id hid
            have h1 := evalAffineInOrientation_var R false .vertical
              (Fin.cons py y) (id + 1) (by omega)
            rw [finCons_addOne py y id (by omega) (by omega)] at h1
            have h0 := evalAffineInOrientation_var R false .vertical y id hid
            simpa [latV] using h1.trans h0.symm
          have hshiftScaleH : ∀ (q : Rat) (id : Nat)
              (hid : id < latticeHorizontalVariableCount code),
              evalAffineInOrientation R false .horizontal
                  (Expr.scale q (latH C code 1 id)) (Fin.cons px x) =
                evalAffineInOrientation R false .horizontal
                  (Expr.scale q (latH C code 0 id)) x := by
            intro q id hid
            have h1 := evalAffineInOrientation_scale_var R false .horizontal q
              (Fin.cons px x) (id + 1) (by omega)
            rw [finCons_addOne px x id (by omega) (by omega)] at h1
            have h0 := evalAffineInOrientation_scale_var R false .horizontal q x id hid
            simpa [latH] using h1.trans h0.symm
          have hshiftScaleV : ∀ (q : Rat) (id : Nat)
              (hid : id < latticeVerticalVariableCount code),
              evalAffineInOrientation R false .vertical
                  (Expr.scale q (latV C code 1 id)) (Fin.cons py y) =
                evalAffineInOrientation R false .vertical
                  (Expr.scale q (latV C code 0 id)) y := by
            intro q id hid
            have h1 := evalAffineInOrientation_scale_var R false .vertical q
              (Fin.cons py y) (id + 1) (by omega)
            rw [finCons_addOne py y id (by omega) (by omega)] at h1
            have h0 := evalAffineInOrientation_scale_var R false .vertical q y id hid
            simpa [latV] using h1.trans h0.symm
          have evalCentreXShift : ∀ k : LatticeFiniteIndex code,
              evalAffineInOrientation R false .horizontal
                  (latticeCentreX C code 1 k) (Fin.cons px x) =
                (latticeSemanticCentre code X k.1
                  (centeredInteger k.2.1) (centeredInteger k.2.2)).re := by
            intro k
            calc
              evalAffineInOrientation R false .horizontal
                  (latticeCentreX C code 1 k) (Fin.cons px x) =
                  evalAffineInOrientation R false .horizontal
                    (latticeCentreX C code 0 k) x := by
                      simp only [latticeCentreX, evalAffineInOrientation_add]
                      rw [hshiftH (latticeRepresentativeXId k.1.val) (by
                        dsimp [latticeRepresentativeXId, latticeHorizontalVariableCount]; omega),
                        hshiftScaleH (centeredInteger k.2.1)
                          latticeFirstPeriodXId (by
                            dsimp [latticeFirstPeriodXId, latticeHorizontalVariableCount]; omega),
                        hshiftScaleH (centeredInteger k.2.2)
                          latticeSecondPeriodXId (by
                            dsimp [latticeSecondPeriodXId, latticeHorizontalVariableCount]; omega)]
              _ = (latticeSemanticCentre code X k.1
                  (centeredInteger k.2.1) (centeredInteger k.2.2)).re := evalCentreX k
          have evalCentreYShift : ∀ k : LatticeFiniteIndex code,
              evalAffineInOrientation R false .vertical
                  (latticeCentreY C code 1 k) (Fin.cons py y) =
                (latticeSemanticCentre code X k.1
                  (centeredInteger k.2.1) (centeredInteger k.2.2)).im := by
            intro k
            calc
              evalAffineInOrientation R false .vertical
                  (latticeCentreY C code 1 k) (Fin.cons py y) =
                  evalAffineInOrientation R false .vertical
                    (latticeCentreY C code 0 k) y := by
                      simp only [latticeCentreY, evalAffineInOrientation_add]
                      rw [hshiftV (latticeRepresentativeYId k.1.val) (by
                        dsimp [latticeRepresentativeYId, latticeVerticalVariableCount]; omega),
                        hshiftScaleV (centeredInteger k.2.1)
                          latticeFirstPeriodYId (by
                            dsimp [latticeFirstPeriodYId, latticeVerticalVariableCount]; omega),
                        hshiftScaleV (centeredInteger k.2.2)
                          latticeSecondPeriodYId (by
                            dsimp [latticeSecondPeriodYId, latticeVerticalVariableCount]; omega)]
              _ = (latticeSemanticCentre code X k.1
                  (centeredInteger k.2.1) (centeredInteger k.2.2)).im := evalCentreY k
          apply (formulaHolds_orList R false _
            (Fin.cons px x) (Fin.cons py y)).mpr
          refine ⟨closedCellFormula false e (latticeCentreX C code 1 j)
              (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
              (latticeCentreY C code 1 j)
              (Expr.var C (latticeVerticalVariableCount code + 1) 0), ?_, ?_⟩
          · apply List.mem_flatMap.mpr
            refine ⟨j, hj, ?_⟩
            apply List.mem_map.mpr
            refine ⟨e, ?_, rfl⟩
            exact List.mem_ofFn.mpr ⟨e, rfl⟩
          · apply (closedCellFormula_holds_iff R e
              (latticeCentreX C code 1 j)
              (Expr.var C (latticeHorizontalVariableCount code + 1) 0)
              (latticeCentreY C code 1 j)
              (Expr.var C (latticeVerticalVariableCount code + 1) 0)
              (Fin.cons px x) (Fin.cons py y)).mpr
            simp only [evalAffineInOrientation_add]
            rw [evalCentreXShift j, evalCentreYShift j, hxh', hyv']
            rw [evalSelectedCellLeftHorizontal R e (Fin.cons px x),
              evalSelectedCellHorizontal R e (Fin.cons px x)]
            have hbottom := evalSelectedCellVertical R e (Fin.cons py y) false
            have htop := evalSelectedCellVertical R e (Fin.cons py y) true
            have hbottom' : evalAffineInOrientation R false .vertical
                (Expr.input (latticeVerticalVariableCount code + 1)
                  (selectedCellBottom C false e)) (Fin.cons py y) =
                (R.vertex (C.bottomVertex e)).im := by
              simpa using hbottom
            have htop' : evalAffineInOrientation R false .vertical
                (Expr.input (latticeVerticalVariableCount code + 1)
                  (selectedCellTop C false e)) (Fin.cons py y) =
                (R.vertex (C.topVertex e)).im := by
              simpa using htop
            rw [hbottom', htop']
            change
              (latticeSemanticCentre code X j.1
                  (centeredInteger j.2.1) (centeredInteger j.2.2)).re +
                    (R.vertex (C.leftVertex e)).re ≤ p.re ∧
                p.re ≤
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).re +
                    (R.vertex (C.rightVertex e)).re ∧
                (latticeSemanticCentre code X j.1
                  (centeredInteger j.2.1) (centeredInteger j.2.2)).im +
                    (R.vertex (C.bottomVertex e)).im ≤ p.im ∧
                p.im ≤
                  (latticeSemanticCentre code X j.1
                    (centeredInteger j.2.1) (centeredInteger j.2.2)).im +
                    (R.vertex (C.topVertex e)).im at he
            simpa [p] using he
        · exact Or.inl hinside⟩

theorem verifyPositive_correct : ∀ {C} (R : Realization C) (O : CorrectOracle C R) code,
    verifyPositive C O.toOracle code = true ↔
      code.wellFormed = true ∧ match code with
        | .triangular c => ∃ X : TriangularRawParameters c, TriangularChecks R c X
        | .lattice c => ∃ X : LatticeRawParameters c, LatticeChecks R c X := by
  intro C R O code
  cases code with
  | triangular code =>
      by_cases hcode : code.wellFormed = true
      · simp only [verifyPositive, RawPositiveCode.wellFormed, hcode, Bool.true_and,
          positiveCertificateFormula]
        rw [AffineCompiler.decideFormula_correct R O, orientClosed_holds]
        simpa using triangularFormula_adequate R code hcode
      · simp only [verifyPositive, RawPositiveCode.wellFormed, hcode,
          Bool.false_eq_true, Bool.false_and]
        simp
  | lattice code =>
      by_cases hcode : code.wellFormed = true
      · simp only [verifyPositive, RawPositiveCode.wellFormed, hcode, Bool.true_and,
          positiveCertificateFormula]
        rw [AffineCompiler.decideFormula_correct R O]
        simpa using latticeFormula_adequate R code hcode
      · simp only [verifyPositive, RawPositiveCode.wellFormed, hcode,
          Bool.false_eq_true, Bool.false_and]
        simp

theorem verifyPositive_sound : ∀ {C} (R : Realization C) (O : CorrectOracle C R) code,
    verifyPositive C O.toOracle code = true → realizationPlaneTileable R := by
  intro C R O code hverify
  have hcorrect := (verifyPositive_correct R O code).mp hverify
  rcases hcorrect with ⟨_, hsemantic⟩
  cases code with
  | triangular code =>
      rcases hsemantic with ⟨X, hX⟩
      exact triangularChecks_sound R code X hX
  | lattice code =>
      rcases hsemantic with ⟨X, hX⟩
      exact latticeChecks_sound R code X hX

theorem verifyPositiveStage_sound :
    ∀ {C} (R : Realization C) (O : CorrectOracle C R) stage,
      verifyPositiveStage C O.toOracle stage = true → realizationPlaneTileable R := by
  intro C R O stage hstage
  cases hcode : wellFormedPositiveStage stage with
  | none =>
      simp [verifyPositiveStage, hcode] at hstage
  | some code =>
      rw [verifyPositiveStage, hcode] at hstage
      exact verifyPositive_sound R O code hstage

end Tiling.AxisParallel.Terminal.Executable.PositiveVerification
