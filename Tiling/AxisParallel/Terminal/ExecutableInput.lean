import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Executable finite input

The finite runtime syntax used by the terminal decision procedure.  This module contains no
semantic realization, geometric region, correctness certificate, or real-number computation.
-/

open scoped BigOperators

namespace Tiling.AxisParallel.Terminal.Executable

/-- Finite runtime data. Carrying `originVertex` makes `vertexCount = 0` uninhabited. -/
structure RegionCode where
  vertexCount : Nat
  cellCount : Nat
  originVertex : Fin vertexCount
  leftVertex : Fin cellCount → Fin vertexCount
  rightVertex : Fin cellCount → Fin vertexCount
  bottomVertex : Fin cellCount → Fin vertexCount
  topVertex : Fin cellCount → Fin vertexCount

/-- The raw frontend check. Positivity is computed rather than stored as a proposition. -/
def RegionCode.wellFormed (C : RegionCode) : Bool := decide (0 < C.cellCount)

/-- Integer coefficients over the supplied runtime vertex identifiers. -/
abbrev Coeff (C : RegionCode) := Fin C.vertexCount → Int

namespace Coeff

def zero (C : RegionCode) : Coeff C := fun _ => 0

def single {C : RegionCode} (i : Fin C.vertexCount) (z : Int) : Coeff C :=
  fun j => if j = i then z else 0

def add {C : RegionCode} (a b : Coeff C) : Coeff C := fun i => a i + b i

def neg {C : RegionCode} (a : Coeff C) : Coeff C := fun i => -a i

def sub {C : RegionCode} (a b : Coeff C) : Coeff C := fun i => a i - b i

def nsmul {C : RegionCode} (n : Nat) (a : Coeff C) : Coeff C :=
  fun i => Int.ofNat n * a i

def cellLeft {C : RegionCode} (e : Fin C.cellCount) : Coeff C := single (C.leftVertex e) 1

def cellRight {C : RegionCode} (e : Fin C.cellCount) : Coeff C := single (C.rightVertex e) 1

def cellBottom {C : RegionCode} (e : Fin C.cellCount) : Coeff C := single (C.bottomVertex e) 1

def cellTop {C : RegionCode} (e : Fin C.cellCount) : Coeff C := single (C.topVertex e) 1

end Coeff

/-- The two coordinate sorts. -/
inductive CoordSort
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- A runtime same-sort comparison. -/
structure Query (C : RegionCode) where
  sort : CoordSort
  lhs : Coeff C
  rhs : Coeff C

/-- A supplied executable oracle. Correctness is deliberately absent from this runtime record. -/
structure Oracle (C : RegionCode) where
  answer : Query C → Bool

/-- Rational affine syntax over one coordinate sort. -/
structure AffineExpr (C : RegionCode) (variableCount : Nat) where
  variableCoefficient : Fin variableCount → Rat
  inputConstant : Coeff C

/-- Coordinate-separated first-order syntax. -/
inductive Formula (C : RegionCode) : Nat → Nat → Type
  | truth {h v : Nat} : Formula C h v
  | falsity {h v : Nat} : Formula C h v
  | horizontalLe {h v : Nat} : AffineExpr C h → AffineExpr C h → Formula C h v
  | horizontalLt {h v : Nat} : AffineExpr C h → AffineExpr C h → Formula C h v
  | verticalLe {h v : Nat} : AffineExpr C v → AffineExpr C v → Formula C h v
  | verticalLt {h v : Nat} : AffineExpr C v → AffineExpr C v → Formula C h v
  | conjunction {h v : Nat} : Formula C h v → Formula C h v → Formula C h v
  | disjunction {h v : Nat} : Formula C h v → Formula C h v → Formula C h v
  | negation {h v : Nat} : Formula C h v → Formula C h v
  | existsHorizontal {h v : Nat} : Formula C (h + 1) v → Formula C h v
  | existsVertical {h v : Nat} : Formula C h (v + 1) → Formula C h v

/-- A compiler-friendly atom after rational denominators have been cleared positively. -/
structure IntegralAffineAtom (C : RegionCode) (variableCount : Nat) where
  variableCoefficient : Fin variableCount → Int
  inputConstant : Coeff C

/-- Quantifier-free Boolean syntax emitted after elimination. -/
inductive QuantifierFreeFormula (C : RegionCode)
  | truth
  | falsity
  | le (sort : CoordSort) (lhs rhs : Coeff C)
  | lt (sort : CoordSort) (lhs rhs : Coeff C)
  | conjunction (left right : QuantifierFreeFormula C)
  | disjunction (left right : QuantifierFreeFormula C)
  | negation (body : QuantifierFreeFormula C)

def Query.evaluate {C : RegionCode} (O : Oracle C) (q : Query C) : Bool := O.answer q

def QuantifierFreeFormula.evaluate {C : RegionCode} (O : Oracle C) :
    QuantifierFreeFormula C → Bool
  | .truth => true
  | .falsity => false
  | .le s a b => O.answer ⟨s, a, b⟩
  | .lt s a b => !(O.answer ⟨s, b, a⟩)
  | .conjunction F G => F.evaluate O && G.evaluate O
  | .disjunction F G => F.evaluate O || G.evaluate O
  | .negation F => !(F.evaluate O)

namespace RuntimeRebase

/-- Replace `a` by coefficients denoting `sum aᵢ(vᵢ-v_origin)` against original vertices. -/
def rebaseCoeff {C : RegionCode} (origin : Fin C.vertexCount) (a : Coeff C) : Coeff C :=
  Coeff.sub a (Coeff.single origin (∑ i, a i))

def rebaseQuery {C : RegionCode} (origin : Fin C.vertexCount) (q : Query C) : Query C :=
  ⟨q.sort, rebaseCoeff origin q.lhs, rebaseCoeff origin q.rhs⟩

/-- An original-coordinate oracle answers normalized-coordinate queries after
coefficient rebasing. -/
def rebaseOracle {C : RegionCode} (origin : Fin C.vertexCount) (O : Oracle C) : Oracle C :=
  ⟨fun q => O.answer (rebaseQuery origin q)⟩

end RuntimeRebase

end Tiling.AxisParallel.Terminal.Executable
