import Tiling.AxisParallel.Terminal.ExecutableInput
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Mathlib.Data.Rat.Encodable

/-! Executable finite Fourier--Motzkin compiler and finite oracle-query program. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

namespace Tiling.AxisParallel.Terminal.Executable.AffineCompiler

inductive Comparison | weak | strict deriving DecidableEq, Repr

structure LinearExpr (C : RegionCode) (n : Nat) where
  coefficients : Fin n → Rat
  constant : Fin C.vertexCount → Rat

namespace LinearExpr

def zero (C : RegionCode) (n : Nat) : LinearExpr C n := ⟨fun _ => 0, fun _ => 0⟩
def add {C n} (a b : LinearExpr C n) : LinearExpr C n :=
  ⟨fun i => a.coefficients i + b.coefficients i, fun i => a.constant i + b.constant i⟩
def neg {C n} (a : LinearExpr C n) : LinearExpr C n :=
  ⟨fun i => -a.coefficients i, fun i => -a.constant i⟩
def sub {C n} (a b : LinearExpr C n) : LinearExpr C n := add a b.neg
def scale {C n} (q : Rat) (a : LinearExpr C n) : LinearExpr C n :=
  ⟨fun i => q * a.coefficients i, fun i => q * a.constant i⟩
def tail {C n} (a : LinearExpr C (n + 1)) : LinearExpr C n :=
  ⟨fun i => a.coefficients i.succ, a.constant⟩
def head {C n} (a : LinearExpr C (n + 1)) : Rat := a.coefficients 0

def ofAffine {C n} (a : AffineExpr C n) : LinearExpr C n :=
  ⟨a.variableCoefficient, fun i => a.inputConstant i⟩

end LinearExpr

structure Atom (C : RegionCode) (n : Nat) where
  comparison : Comparison
  expr : LinearExpr C n

def Atom.negate {C n} (a : Atom C n) : Atom C n :=
  match a.comparison with
  | .weak => ⟨.strict, a.expr.neg⟩
  | .strict => ⟨.weak, a.expr.neg⟩

inductive SortedAtom (C : RegionCode) (h v : Nat)
  | horizontal (atom : Atom C h)
  | vertical (atom : Atom C v)

def SortedAtom.negate {C h v} : SortedAtom C h v → SortedAtom C h v
  | .horizontal a => .horizontal a.negate
  | .vertical a => .vertical a.negate

abbrev Clause (C : RegionCode) (h v : Nat) := List (SortedAtom C h v)
abbrev DNF (C : RegionCode) (h v : Nat) := List (Clause C h v)

def dnfFalse (C : RegionCode) (h v : Nat) : DNF C h v := []
def dnfTrue (C : RegionCode) (h v : Nat) : DNF C h v := [[]]
def dnfAtom {C h v} (a : SortedAtom C h v) : DNF C h v := [[a]]

def dnfOr {C h v} (p q : DNF C h v) : DNF C h v := p ++ q
def dnfAnd {C h v} (p q : DNF C h v) : DNF C h v :=
  p.flatMap fun cp => q.map fun cq => cp ++ cq

/-- `¬(a₁∧...∧aₙ)` as a disjunction of singleton clauses. -/
def negateClause {C h v} (c : Clause C h v) : DNF C h v :=
  c.map fun a => [a.negate]

/-- De Morgan normalization of the negation of a DNF. -/
def negateDNF {C h v} (p : DNF C h v) : DNF C h v :=
  p.foldl (fun acc c => dnfAnd acc (negateClause c)) (dnfTrue C h v)

/-- Combine a positive upper bound `a*x+r ⋖ 0` and a negative lower bound
`b*x+s ⋖ 0`.  The result is `a*s-b*r ⋖ 0`; it is strict iff either input is. -/
def combineBounds {C n} (upper lower : Atom C (n + 1)) : Atom C n :=
  let a := upper.expr.head
  let b := lower.expr.head
  { comparison := if upper.comparison = .strict || lower.comparison = .strict then
      .strict else .weak
    expr := (lower.expr.tail.scale a).sub (upper.expr.tail.scale b) }

def horizontalZeroTail {C n v} (a : SortedAtom C (n + 1) v) :
    Option (SortedAtom C n v) :=
  match a with
  | .horizontal q => if q.expr.head = 0 then some (.horizontal ⟨q.comparison, q.expr.tail⟩)
      else none
  | .vertical q => some (.vertical q)

def positiveHorizontal {C n v} (a : SortedAtom C (n + 1) v) : Option (Atom C (n+1)) :=
  match a with | .horizontal q => if 0 < q.expr.head then some q else none | _ => none
def negativeHorizontal {C n v} (a : SortedAtom C (n + 1) v) : Option (Atom C (n+1)) :=
  match a with | .horizontal q => if q.expr.head < 0 then some q else none | _ => none

def eliminateHorizontalClause {C n v} (c : Clause C (n + 1) v) : Clause C n v :=
  let fixed := c.filterMap horizontalZeroTail
  let uppers := c.filterMap positiveHorizontal
  let lowers := c.filterMap negativeHorizontal
  fixed ++ uppers.flatMap (fun u => lowers.map fun l => .horizontal (combineBounds u l))

def eliminateHorizontal {C n v} (p : DNF C (n + 1) v) : DNF C n v :=
  p.map eliminateHorizontalClause

def verticalZeroTail {C h n} (a : SortedAtom C h (n + 1)) :
    Option (SortedAtom C h n) :=
  match a with
  | .vertical q => if q.expr.head = 0 then some (.vertical ⟨q.comparison, q.expr.tail⟩)
      else none
  | .horizontal q => some (.horizontal q)
def positiveVertical {C h n} (a : SortedAtom C h (n + 1)) : Option (Atom C (n+1)) :=
  match a with | .vertical q => if 0 < q.expr.head then some q else none | _ => none
def negativeVertical {C h n} (a : SortedAtom C h (n + 1)) : Option (Atom C (n+1)) :=
  match a with | .vertical q => if q.expr.head < 0 then some q else none | _ => none

def eliminateVerticalClause {C h n} (c : Clause C h (n + 1)) : Clause C h n :=
  let fixed := c.filterMap verticalZeroTail
  let uppers := c.filterMap positiveVertical
  let lowers := c.filterMap negativeVertical
  fixed ++ uppers.flatMap (fun u => lowers.map fun l => .vertical (combineBounds u l))

def eliminateVertical {C h n} (p : DNF C h (n + 1)) : DNF C h n :=
  p.map eliminateVerticalClause

/-- Bottom-up quantifier elimination.  Negated existentials are handled because negation is applied
to the already-eliminated body DNF, then normalized constructively by `negateDNF`. -/
def compile {C : RegionCode} : {h v : Nat} → Formula C h v → DNF C h v
  | _, _, .truth => dnfTrue C _ _
  | _, _, .falsity => dnfFalse C _ _
  | _, _, .horizontalLe a b => dnfAtom (.horizontal ⟨.weak,
      (LinearExpr.ofAffine a).sub (LinearExpr.ofAffine b)⟩)
  | _, _, .horizontalLt a b => dnfAtom (.horizontal ⟨.strict,
      (LinearExpr.ofAffine a).sub (LinearExpr.ofAffine b)⟩)
  | _, _, .verticalLe a b => dnfAtom (.vertical ⟨.weak,
      (LinearExpr.ofAffine a).sub (LinearExpr.ofAffine b)⟩)
  | _, _, .verticalLt a b => dnfAtom (.vertical ⟨.strict,
      (LinearExpr.ofAffine a).sub (LinearExpr.ofAffine b)⟩)
  | _, _, .conjunction p q => dnfAnd (compile p) (compile q)
  | _, _, .disjunction p q => dnfOr (compile p) (compile q)
  | _, _, .negation p => negateDNF (compile p)
  | _, _, .existsHorizontal p => eliminateHorizontal (compile p)
  | _, _, .existsVertical p => eliminateVertical (compile p)

/-- Product of rational denominators; executable and positive. -/
def commonDenominator {C : RegionCode} (e : LinearExpr C 0) : Nat :=
  ∏ i, (e.constant i).den

/-- Integer query coefficients after multiplying by the common positive denominator. -/
def clearInput {C : RegionCode} (e : LinearExpr C 0) : Coeff C :=
  fun i => (((commonDenominator e : Nat) : Rat) * e.constant i).num

def closedAtomQuery {C : RegionCode} (s : CoordSort) (a : Atom C 0) : Query C :=
  ⟨s, clearInput a.expr, Coeff.zero C⟩

def evalClosedAtom {C : RegionCode} (O : Oracle C) (s : CoordSort) (a : Atom C 0) : Bool :=
  match a.comparison with
  | .weak => O.answer (closedAtomQuery s a)
  | .strict => !(O.answer ⟨s, Coeff.zero C, clearInput a.expr⟩)

def evalClosedSortedAtom {C : RegionCode} (O : Oracle C) : SortedAtom C 0 0 → Bool
  | .horizontal a => evalClosedAtom O .horizontal a
  | .vertical a => evalClosedAtom O .vertical a

def evalClosedClause {C : RegionCode} (O : Oracle C) (c : Clause C 0 0) : Bool :=
  c.all (evalClosedSortedAtom O)
def evalClosedDNF {C : RegionCode} (O : Oracle C) (p : DNF C 0 0) : Bool :=
  p.any (evalClosedClause O)

def decideFormula {C : RegionCode} (O : Oracle C) (f : Formula C 0 0) : Bool :=
  evalClosedDNF O (compile f)

/-! ## The affine compiler as a finite query tree -/

private def evalClosedAtomProgram {C : RegionCode} (s : CoordSort) (a : Atom C 0) :
    OracleProgram (Query C) Bool :=
  match a.comparison with
  | .weak => .query (closedAtomQuery s a) OracleProgram.pure
  | .strict => .query ⟨s, Coeff.zero C, clearInput a.expr⟩
      (fun b => .pure (!b))

private def evalClosedSortedAtomProgram {C : RegionCode} : SortedAtom C 0 0 →
    OracleProgram (Query C) Bool
  | .horizontal a => evalClosedAtomProgram .horizontal a
  | .vertical a => evalClosedAtomProgram .vertical a

private def evalClosedClauseProgram {C : RegionCode} : Clause C 0 0 → OracleProgram (Query C) Bool
  | [] => .pure true
  | a :: rest => OracleProgram.bind (evalClosedSortedAtomProgram a) fun accepted =>
      if accepted then evalClosedClauseProgram rest else .pure false

private def evalClosedDNFProgram {C : RegionCode} : DNF C 0 0 → OracleProgram (Query C) Bool
  | [] => .pure false
  | clause :: rest => OracleProgram.bind (evalClosedClauseProgram clause) fun accepted =>
      if accepted then .pure true else evalClosedDNFProgram rest

def decideFormulaProgram {C : RegionCode} (f : Formula C 0 0) :
    OracleProgram (Query C) Bool :=
  evalClosedDNFProgram (compile f)



private theorem evalClosedAtomProgram_evaluate {C : RegionCode}
    (O : Oracle C) (s : CoordSort) (a : Atom C 0) :
    OracleProgram.evaluate O.answer (evalClosedAtomProgram s a) =
      evalClosedAtom O s a := by
  rcases a with ⟨comparison, expr⟩
  cases comparison <;> rfl

private theorem evalClosedSortedAtomProgram_evaluate {C : RegionCode}
    (O : Oracle C) (a : SortedAtom C 0 0) :
    OracleProgram.evaluate O.answer (evalClosedSortedAtomProgram a) =
      evalClosedSortedAtom O a := by
  cases a with
  | horizontal a => exact evalClosedAtomProgram_evaluate O .horizontal a
  | vertical a => exact evalClosedAtomProgram_evaluate O .vertical a

private theorem evalClosedClauseProgram_evaluate {C : RegionCode}
    (O : Oracle C) (c : Clause C 0 0) :
    OracleProgram.evaluate O.answer (evalClosedClauseProgram c) =
      evalClosedClause O c := by
  induction c with
  | nil => rfl
  | cons a rest ih =>
      rw [evalClosedClauseProgram, OracleProgram.evaluate_bind,
        evalClosedSortedAtomProgram_evaluate]
      cases h : evalClosedSortedAtom O a <;>
        simp [h, ih, evalClosedClause, OracleProgram.evaluate]

private theorem evalClosedDNFProgram_evaluate {C : RegionCode}
    (O : Oracle C) (p : DNF C 0 0) :
    OracleProgram.evaluate O.answer (evalClosedDNFProgram p) =
      evalClosedDNF O p := by
  induction p with
  | nil => rfl
  | cons clause rest ih =>
      rw [evalClosedDNFProgram, OracleProgram.evaluate_bind,
        evalClosedClauseProgram_evaluate]
      cases h : evalClosedClause O clause <;>
        simp [h, ih, evalClosedDNF, OracleProgram.evaluate]

theorem decideFormulaProgram_evaluate {C : RegionCode}
    (O : Oracle C) (f : Formula C 0 0) :
    OracleProgram.evaluate O.answer (decideFormulaProgram f) =
      AffineCompiler.decideFormula O f := by
  exact evalClosedDNFProgram_evaluate O (compile f)

end Tiling.AxisParallel.Terminal.Executable.AffineCompiler
