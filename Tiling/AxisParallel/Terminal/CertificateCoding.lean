import Tiling.AxisParallel.Terminal.ExecutableInput
import Mathlib.Data.List.GetD
import Mathlib.Logic.Encodable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Rat.Encodable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tiling.AxisParallel.Terminal.Executable

/-- Raw negative search parameters. The cardinality bound is recomputed by the decoder. -/
structure RawNegativeCode where
  boxIndex : Nat
  horizontalSubdivisions : Nat
  verticalSubdivisions : Nat
  deriving DecidableEq, Repr

/-- One triangular piece stores its interval and orbit-representative counts. -/
structure RawTriangularPieceCode where
  intervalCount : Nat
  representativeCount : Nat
  deriving DecidableEq, Repr

/-- Proof-free triangular-certificate input. List length is the number of pieces. -/
structure RawTriangularCode where
  orientation : Bool
  pieces : List RawTriangularPieceCode
  checkingRadius : Nat
  deriving DecidableEq, Repr

/-- Proof-free lattice-certificate input. -/
structure RawLatticeCode where
  rationalSeparator : Rat
  representativeCount : Nat
  firstIndexBound : Nat
  secondIndexBound : Nat
  deriving DecidableEq, Repr

/-- The two raw positive schemas. -/
inductive RawPositiveCode
  | triangular (code : RawTriangularCode)
  | lattice (code : RawLatticeCode)
  deriving DecidableEq, Repr

private def rawNegativeEquiv : RawNegativeCode ≃ Nat × Nat × Nat where
  toFun c := (c.boxIndex, c.horizontalSubdivisions, c.verticalSubdivisions)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, d⟩; rfl

instance : Encodable RawNegativeCode := Encodable.ofEquiv _ rawNegativeEquiv

private def rawPieceEquiv : RawTriangularPieceCode ≃ Nat × Nat where
  toFun c := (c.intervalCount, c.representativeCount)
  invFun c := ⟨c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

instance : Encodable RawTriangularPieceCode := Encodable.ofEquiv _ rawPieceEquiv

private def rawTriangularEquiv : RawTriangularCode ≃ Bool × List RawTriangularPieceCode × Nat where
  toFun c := (c.orientation, c.pieces, c.checkingRadius)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, d⟩; rfl

instance : Encodable RawTriangularCode := Encodable.ofEquiv _ rawTriangularEquiv

private def rawLatticeEquiv : RawLatticeCode ≃ Rat × Nat × Nat × Nat where
  toFun c := (c.rationalSeparator, c.representativeCount, c.firstIndexBound,
    c.secondIndexBound)
  invFun c := ⟨c.1, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, d, e⟩; rfl

instance : Encodable RawLatticeCode := Encodable.ofEquiv _ rawLatticeEquiv

private def rawPositiveEquiv : RawPositiveCode ≃ RawTriangularCode ⊕ RawLatticeCode where
  toFun
    | .triangular c => .inl c
    | .lattice c => .inr c
  invFun
    | .inl c => .triangular c
    | .inr c => .lattice c
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

instance : Encodable RawPositiveCode := Encodable.ofEquiv _ rawPositiveEquiv

def RawNegativeCode.wellFormed (c : RawNegativeCode) : Bool :=
  decide (0 < c.boxIndex && 0 < c.horizontalSubdivisions && 0 < c.verticalSubdivisions)

def RawTriangularPieceCode.wellFormed (p : RawTriangularPieceCode) : Bool :=
  decide (0 < p.intervalCount && 0 < p.representativeCount)

def RawTriangularCode.wellFormed (c : RawTriangularCode) : Bool :=
  decide (!c.pieces.isEmpty && c.pieces.all RawTriangularPieceCode.wellFormed &&
    0 < c.checkingRadius)

def RawLatticeCode.wellFormed (c : RawLatticeCode) : Bool :=
  decide (0 < c.representativeCount && 0 < c.firstIndexBound && 0 < c.secondIndexBound)

def RawPositiveCode.wellFormed : RawPositiveCode → Bool
  | .triangular c => c.wellFormed
  | .lattice c => c.wellFormed

private def stageCode (α : Type) [Encodable α] (n : Nat) : Option α := Encodable.decode n

def rawNegativeStage (n : Nat) : Option RawNegativeCode := stageCode RawNegativeCode n

def rawPositiveStage (n : Nat) : Option RawPositiveCode := stageCode RawPositiveCode n

def wellFormedNegativeStage (n : Nat) : Option RawNegativeCode :=
  (rawNegativeStage n).filter (·.wellFormed)

def wellFormedPositiveStage (n : Nat) : Option RawPositiveCode :=
  (rawPositiveStage n).filter (·.wellFormed)

private theorem stageCode_surjective (α : Type) [Encodable α] (a : α) :
    ∃ n, stageCode α n = some a := by
  exact ⟨Encodable.encode a, Encodable.encodek a⟩

private theorem rawNegativeStage_complete (c : RawNegativeCode) :
    ∃ n, rawNegativeStage n = some c :=
  stageCode_surjective _ c

private theorem rawPositiveStage_complete (c : RawPositiveCode) :
    ∃ n, rawPositiveStage n = some c :=
  stageCode_surjective _ c

theorem wellFormedNegativeStage_complete (c : RawNegativeCode)
    (hc : c.wellFormed = true) : ∃ n, wellFormedNegativeStage n = some c := by
  obtain ⟨n, hn⟩ := rawNegativeStage_complete c
  exact ⟨n, by simp [wellFormedNegativeStage, hn, hc]⟩

theorem wellFormedPositiveStage_complete (c : RawPositiveCode)
    (hc : c.wellFormed = true) : ∃ n, wellFormedPositiveStage n = some c := by
  obtain ⟨n, hn⟩ := rawPositiveStage_complete c
  exact ⟨n, by simp [wellFormedPositiveStage, hn, hc]⟩

end Tiling.AxisParallel.Terminal.Executable
