import Tiling.AxisParallel.Decidability.Certificates.FormulaCells
import Tiling.AxisParallel.Decidability.Certificates.FormulaComputability

/-! Computable postorder code for the production positive lattice certificate formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.CertificateFormulas
open Tiling.AxisParallel.Decidability.Affine
open PositiveCoding
open Tiling.AxisParallel.Terminal.Executable

@[fun_prop] theorem c_latticeRepresentatives {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => (f x).representativeCount) :=
  rawLattice_representativeCount_primrec.to_comp.comp hf

@[fun_prop] theorem c_latticeFirstBound {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => (f x).firstIndexBound) :=
  rawLattice_firstIndexBound_primrec.to_comp.comp hf

@[fun_prop] theorem c_latticeSecondBound {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => (f x).secondIndexBound) :=
  rawLattice_secondIndexBound_primrec.to_comp.comp hf

@[fun_prop] theorem c_latticeSeparator {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => (f x).rationalSeparator) :=
  rawLattice_rationalSeparator_computable.comp hf

@[fun_prop] theorem c_latticeWellFormed {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => (f x).wellFormed) :=
  rawLattice_wellFormed_computable.comp hf

abbrev LatticeIndex := ℕ × ℕ × ℕ

def latticeHorizontalVariableCount (c : RawLatticeCode) : ℕ := 4 + c.representativeCount
def latticeVerticalVariableCount (c : RawLatticeCode) : ℕ := 3 + c.representativeCount
def latticeFirstPeriodXId : ℕ := 0
def latticeSecondPeriodXId : ℕ := 1
def latticeFirstPeriodYId : ℕ := 0
def latticeSecondPeriodYId : ℕ := 1
def latticeRepresentativeXId (r : ℕ) : ℕ := 2 + r
def latticeRepresentativeYId (r : ℕ) : ℕ := 2 + r
def latticeHorizontalBoundId (c : RawLatticeCode) : ℕ := 2 + c.representativeCount
def latticeVerticalBoundId (c : RawLatticeCode) : ℕ := 2 + c.representativeCount
def latticeFirstPeriodAbsoluteXBoundId (c : RawLatticeCode) : ℕ := 3 + c.representativeCount

def latticeIndices (c : RawLatticeCode) : List LatticeIndex :=
  ((List.range c.representativeCount).flatMap fun r =>
    (List.range (2 * c.firstIndexBound + 1)).flatMap fun n =>
      (List.range (2 * c.secondIndexBound + 1)).map fun m => (r, n, m)).filter
    fun i => decide ((Int.ofNat i.2.1 - Int.ofNat c.firstIndexBound).natAbs < c.firstIndexBound ∧
      (Int.ofNat i.2.2 - Int.ofNat c.secondIndexBound).natAbs < c.secondIndexBound)

theorem latticeIndices_computable : Computable latticeIndices := by
  have hr : PrimrecRel (fun (i : LatticeIndex) (c : RawLatticeCode) =>
      (Int.ofNat i.2.1 - Int.ofNat c.firstIndexBound).natAbs < c.firstIndexBound ∧
      (Int.ofNat i.2.2 - Int.ofNat c.secondIndexBound).natAbs < c.secondIndexBound) := by
    have hfirst : Primrec (fun p : LatticeIndex × RawLatticeCode => p.2.firstIndexBound) :=
      rawLattice_firstIndexBound_primrec.comp Primrec.snd
    have hsecond : Primrec (fun p : LatticeIndex × RawLatticeCode => p.2.secondIndexBound) :=
      rawLattice_secondIndexBound_primrec.comp Primrec.snd
    exact (Primrec.nat_lt.comp (int_natAbs_primrec.comp
      (int_sub_primrec.comp
        (int_ofNat_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (int_ofNat_primrec.comp hfirst))) hfirst).and
      (Primrec.nat_lt.comp (int_natAbs_primrec.comp
        (int_sub_primrec.comp
          (int_ofNat_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (int_ofNat_primrec.comp hsecond))) hsecond)
  have hl : Computable (fun c : RawLatticeCode =>
      (List.range c.representativeCount).flatMap fun r =>
        (List.range (2 * c.firstIndexBound + 1)).flatMap fun n =>
          (List.range (2 * c.secondIndexBound + 1)).map fun m => (r, n, m)) := by fun_prop
  exact (hr.listFilter.to_comp.comp hl Computable.id).of_eq (fun _ => rfl)

@[fun_prop] theorem c_latticeIndices {α : Type*} [Primcodable α] (f : α → RawLatticeCode)
    (hf : Computable f) : Computable (fun x => latticeIndices (f x)) :=
  latticeIndices_computable.comp hf

def latH (region : RegionInput) (c : RawLatticeCode) (shift id : ℕ) : Expr :=
  affineVariable (latticeHorizontalVariableCount c + shift) region.1 (id + shift)
def latV (region : RegionInput) (c : RawLatticeCode) (shift id : ℕ) : Expr :=
  affineVariable (latticeVerticalVariableCount c + shift) region.1 (id + shift)

def latticeCentreX (region : RegionInput) (c : RawLatticeCode) (shift : ℕ)
    (i : LatticeIndex) : Expr :=
  exprAdd (exprAdd (latH region c shift (latticeRepresentativeXId i.1))
    (exprScale ((Int.ofNat i.2.1 - Int.ofNat c.firstIndexBound : ℤ) : ℚ) (latH region c shift 0)))
    (exprScale ((Int.ofNat i.2.2 - Int.ofNat c.secondIndexBound : ℤ) : ℚ) (latH region c shift 1))
def latticeCentreY (region : RegionInput) (c : RawLatticeCode) (shift : ℕ)
    (i : LatticeIndex) : Expr :=
  exprAdd (exprAdd (latV region c shift (latticeRepresentativeYId i.1))
    (exprScale ((Int.ofNat i.2.1 - Int.ofNat c.firstIndexBound : ℤ) : ℚ) (latV region c shift 0)))
    (exprScale ((Int.ofNat i.2.2 - Int.ofNat c.secondIndexBound : ℤ) : ℚ) (latV region c shift 1))

def vertexDifference (region : RegionInput) (n a b : ℕ) : Expr :=
  exprSub (affineInput n (basisArray region.1 a 1))
    (affineInput n (basisArray region.1 b 1))

def latticeBody (region : RegionInput) (code : RawLatticeCode) : Code :=
  let h := latticeHorizontalVariableCount code
  let v := latticeVerticalVariableCount code
  let zeroH := affineZero h region.1
  let zeroV := affineZero v region.1
  let ux := latH region code 0 latticeFirstPeriodXId
  let vx := latH region code 0 latticeSecondPeriodXId
  let uy := latV region code 0 latticeFirstPeriodYId
  let vy := latV region code 0 latticeSecondPeriodYId
  let hx := latH region code 0 (latticeHorizontalBoundId code)
  let hy := latV region code 0 (latticeVerticalBoundId code)
  let uxBound := latH region code 0 (latticeFirstPeriodAbsoluteXBoundId code)
  let q : Rat := code.rationalSeparator
  let ax := exprSub ux (exprScale q vx)
  let ay := exprSub (exprScale q vy) uy
  let reps := List.range code.representativeCount
  let vertices := List.range region.1
  let cells := List.range region.2.length
  let indices := latticeIndices code
  let rankChecks := andList
    [(horizontalLt zeroH vx), (verticalLt zeroV vy),
      (     horizontalLt zeroH ax), (verticalLt zeroV ay),
      (     horizontalLt zeroH hx), (verticalLt zeroV hy)]
  let periodBounds := andList
    ([1, -1].flatMap fun s : Int => [1, -1].map fun t : Int => andList
      [(horizontalLe (exprAdd (exprScale s ux) (exprScale t vx)) hx),
      (       verticalLe (exprAdd (exprScale s uy) (exprScale t vy)) hy)])
  let representativeBounds := andList (reps.map fun r => andList
    [(horizontalLe (exprNeg hx) (latH region code 0 (latticeRepresentativeXId r))),
      (     horizontalLe (latH region code 0 (latticeRepresentativeXId r)) hx),
      (     verticalLe (exprNeg hy) (latV region code 0 (latticeRepresentativeYId r))),
      (     verticalLe (latV region code 0 (latticeRepresentativeYId r)) hy)])
  let firstIndexBounds := andList
    ((vertices.flatMap fun a => vertices.map fun b =>
      let d := vertexDifference region h a b
      let lhsPos := exprAdd (exprScale 2 hx) d
      let lhsNeg := exprAdd (exprScale 2 hx) (exprNeg d)
      let rhs := exprScale (Int.ofNat code.firstIndexBound) ax
      andList [(horizontalLt lhsPos rhs), (horizontalLt lhsNeg rhs)]) ++
     (vertices.flatMap fun a => vertices.map fun b =>
      let d := vertexDifference region v a b
      let lhsPos := exprAdd (exprScale 2 hy) d
      let lhsNeg := exprAdd (exprScale 2 hy) (exprNeg d)
      let rhs := exprScale (Int.ofNat code.firstIndexBound) ay
      andList [(verticalLt lhsPos rhs), (verticalLt lhsNeg rhs)]))
  let uxBounds := andList
    [(horizontalLe zeroH uxBound), (horizontalLe ux uxBound), (horizontalLe (exprNeg ux) uxBound)]
  let secondIndexBounds := andList (vertices.flatMap fun a => vertices.map fun b =>
    let d := vertexDifference region h a b
    let common := exprAdd (exprScale 2 hx)
      (exprScale (Int.ofNat code.firstIndexBound) uxBound)
    let rhs := exprScale (Int.ofNat code.secondIndexBound) vx
    andList
      [(horizontalLt (exprAdd common d) rhs), (horizontalLt (exprAdd common (exprNeg d)) rhs)])
  let packingChecks := andList (indices.flatMap fun i => indices.map fun i' =>
    if i = i' then truth else
      let cx := latticeCentreX region code 0 i
      let cy := latticeCentreY region code 0 i
      let cx' := latticeCentreX region code 0 i'
      let cy' := latticeCentreY region code 0 i'
      disjunction (sameCentre cx cx' cy cy')
        (andList (cells.flatMap fun e => cells.map fun e' =>
          cellNonoverlap region false h v e e' cx cx' cy cy')))
  let coverageCheck : Code := forallHorizontal (forallVertical
    (let x := affineVariable (h + 1) region.1 0
     let y := affineVariable (v + 1) region.1 0
     let hx' := latH region code 1 (latticeHorizontalBoundId code)
     let hy' := latV region code 1 (latticeVerticalBoundId code)
     implication
       (andList
         [(horizontalLt (exprNeg hx') x), (horizontalLt x hx'),
      (          verticalLt (exprNeg hy') y), (verticalLt y hy')])
       (orList (indices.flatMap fun i => cells.map fun e =>
         closedCell region false (h + 1) (v + 1) e (latticeCentreX region code 1 i) x
           (latticeCentreY region code 1 i) y))))
  andList
    [rankChecks, periodBounds, representativeBounds, firstIndexBounds, uxBounds,
      secondIndexBounds, packingChecks, coverageCheck]

def latticeCertificate (region : RegionInput) (code : RawLatticeCode) : Code :=
  bif code.wellFormed then
    closeVertical (latticeVerticalVariableCount code)
      (closeHorizontal (latticeHorizontalVariableCount code) (latticeBody region code))
  else falsity

set_option maxSynthPendingDepth 32 in
theorem latticeBody_computable : Computable (fun p : RegionInput × RawLatticeCode =>
    latticeBody p.1 p.2) := by
  dsimp only [latticeBody, latticeCentreX, latticeCentreY, latH, latV, vertexDifference,
    latticeHorizontalVariableCount, latticeVerticalVariableCount,
    latticeFirstPeriodXId, latticeSecondPeriodXId, latticeFirstPeriodYId, latticeSecondPeriodYId,
    latticeHorizontalBoundId, latticeVerticalBoundId, latticeFirstPeriodAbsoluteXBoundId,
    latticeRepresentativeXId, latticeRepresentativeYId]
  fun_prop

theorem latticeCertificate_computable : Computable (fun p : RegionInput × RawLatticeCode =>
    latticeCertificate p.1 p.2) := by
  unfold latticeCertificate latticeHorizontalVariableCount latticeVerticalVariableCount
  have hc := latticeBody_computable
  fun_prop

end Tiling.AxisParallel.Decidability.CertificateFormulas
