import Tiling.Computability.List
import Tiling.AxisParallel.Terminal.AffineCompiler
import Mathlib.Data.List.OfFn

/-!
# Packed finite Fourier–Motzkin compilation

Coefficient arrays and postorder formula instructions use the standard tuple and
list encodings. The runtime has no dependent function fields. Native expressions
and formulas are packed only for correspondence proofs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.Affine

abbrev Expr := List ℚ × List ℚ
abbrev Atom := Bool × Expr
abbrev SortedAtom := Bool × Atom
abbrev Clause := List SortedAtom
abbrev DNF := List Clause
abbrev Instruction := ℕ × SortedAtom × ℕ × ℕ
abbrev Code := List Instruction

def addArray (a b : List ℚ) : List ℚ :=
  (List.range a.length).map fun i => a.getD i 0 + b.getD i 0

def exprAdd (a b : Expr) : Expr := (addArray a.1 b.1, addArray a.2 b.2)
def exprNeg (a : Expr) : Expr := (a.1.map Neg.neg, a.2.map Neg.neg)
def exprSub (a b : Expr) : Expr := exprAdd a (exprNeg b)
def exprScale (q : ℚ) (a : Expr) : Expr := (a.1.map (q * ·), a.2.map (q * ·))
def exprTail (a : Expr) : Expr := (a.1.tail, a.2)
def exprHead (a : Expr) : ℚ := a.1.getD 0 0

def atomNegate (a : Atom) : Atom := (!a.1, exprNeg a.2)
def sortedNegate (a : SortedAtom) : SortedAtom := (a.1, atomNegate a.2)

def dnfAnd (p q : DNF) : DNF := p.flatMap fun cp => q.map fun cq => cp ++ cq
def negateClause (c : Clause) : DNF := c.map fun a => [sortedNegate a]
def negateDNF (p : DNF) : DNF := p.foldl (fun acc c => dnfAnd acc (negateClause c)) [[]]

def combineBounds (upper lower : Atom) : Atom :=
  (upper.1 || lower.1,
    exprSub (exprScale (exprHead upper.2) (exprTail lower.2))
      (exprScale (exprHead lower.2) (exprTail upper.2)))

/-- The sort is `false` for horizontal and `true` for vertical. -/
def zeroTail (vertical : Bool) (a : SortedAtom) : Option SortedAtom :=
  if a.1 = vertical then
    if exprHead a.2.2 = 0 then some (vertical, a.2.1, exprTail a.2.2) else none
  else some a

def positive (vertical : Bool) (a : SortedAtom) : Option Atom :=
  if a.1 = vertical ∧ 0 < exprHead a.2.2 then some a.2 else none

def negative (vertical : Bool) (a : SortedAtom) : Option Atom :=
  if a.1 = vertical ∧ exprHead a.2.2 < 0 then some a.2 else none

def eliminateClause (vertical : Bool) (c : Clause) : Clause :=
  c.filterMap (zeroTail vertical) ++
    (c.filterMap (positive vertical)).flatMap fun upper =>
      (c.filterMap (negative vertical)).map fun lower =>
        (vertical, combineBounds upper lower)

def eliminate (vertical : Bool) (p : DNF) : DNF := p.map (eliminateClause vertical)

/-- Tags: 0 true, 1 false, 2 atom, 3 and, 4 or, 5 not, 6 exists-horizontal,
7 exists-vertical. Other tags produce false. -/
def instruction (results : List DNF) (i : Instruction) : DNF :=
  if i.1 = 0 then [[]]
  else if i.1 = 1 then []
  else if i.1 = 2 then [[i.2.1]]
  else if i.1 = 3 then dnfAnd (results.getD i.2.2.1 []) (results.getD i.2.2.2 [])
  else if i.1 = 4 then results.getD i.2.2.1 [] ++ results.getD i.2.2.2 []
  else if i.1 = 5 then negateDNF (results.getD i.2.2.1 [])
  else if i.1 = 6 then eliminate false (results.getD i.2.2.1 [])
  else if i.1 = 7 then eliminate true (results.getD i.2.2.1 [])
  else []

def compileInto (initial : List DNF) (code : Code) : List DNF :=
  code.foldl (fun results i => results ++ [instruction results i]) initial

def compile (code : Code) : DNF := (compileInto [] code).getLast?.getD []

namespace Native

open Tiling.AxisParallel.Terminal.Executable

def packExpr {C : RegionCode} {n : ℕ} (a : AffineCompiler.LinearExpr C n) : Expr :=
  (List.ofFn a.coefficients, List.ofFn a.constant)

def packAtom {C : RegionCode} {n : ℕ} (a : AffineCompiler.Atom C n) : Atom :=
  (decide (a.comparison = .strict), packExpr a.expr)

def packSorted {C : RegionCode} {h v : ℕ} : AffineCompiler.SortedAtom C h v → SortedAtom
  | .horizontal a => (false, packAtom a)
  | .vertical a => (true, packAtom a)

def packDNF {C : RegionCode} {h v : ℕ} (p : AffineCompiler.DNF C h v) : DNF :=
  p.map fun clause => clause.map packSorted

private theorem addArray_ofFn {n : ℕ} (a b : Fin n → ℚ) :
    addArray (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => a i + b i) := by
  apply List.ext_getElem
  · simp [addArray]
  · intro i hi hi'
    have hin : i < n := by simpa using hi'
    have ha : (List.ofFn a).getD i 0 = a ⟨i, hin⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simp only [List.getElem_ofFn]
    have hb : (List.ofFn b).getD i 0 = b ⟨i, hin⟩ := by
      rw [List.getD_eq_getElem _ _ (by simpa using hin)]
      simp only [List.getElem_ofFn]
    simp only [addArray, List.length_ofFn, List.getElem_map, List.getElem_range,
      ha, hb, List.getElem_ofFn]

@[simp] theorem packExpr_add {C : RegionCode} {n : ℕ} (a b : AffineCompiler.LinearExpr C n) :
    exprAdd (packExpr a) (packExpr b) = packExpr (AffineCompiler.LinearExpr.add a b) := by
  simp only [exprAdd, packExpr, AffineCompiler.LinearExpr.add, addArray_ofFn]

@[simp] theorem packExpr_neg {C : RegionCode} {n : ℕ} (a : AffineCompiler.LinearExpr C n) :
    exprNeg (packExpr a) = packExpr (AffineCompiler.LinearExpr.neg a) := by
  simp only [exprNeg, packExpr, AffineCompiler.LinearExpr.neg, List.map_ofFn, Function.comp_def]

@[simp] theorem packExpr_sub {C : RegionCode} {n : ℕ} (a b : AffineCompiler.LinearExpr C n) :
    exprSub (packExpr a) (packExpr b) = packExpr (AffineCompiler.LinearExpr.sub a b) := by
  simp only [exprSub, AffineCompiler.LinearExpr.sub, packExpr_neg, packExpr_add]

@[simp] theorem packExpr_scale {C : RegionCode} {n : ℕ}
    (q : ℚ) (a : AffineCompiler.LinearExpr C n) :
    exprScale q (packExpr a) =
      packExpr (AffineCompiler.LinearExpr.scale q a) := by
  simp only [exprScale, packExpr, AffineCompiler.LinearExpr.scale,
    List.map_ofFn, Function.comp_def]

@[simp] theorem packExpr_tail {C : RegionCode} {n : ℕ} (a : AffineCompiler.LinearExpr C (n + 1)) :
    exprTail (packExpr a) = packExpr (AffineCompiler.LinearExpr.tail a) := by
  simp only [exprTail, packExpr, AffineCompiler.LinearExpr.tail, List.ofFn_succ, List.tail_cons]

@[simp] theorem packExpr_head {C : RegionCode} {n : ℕ} (a : AffineCompiler.LinearExpr C (n + 1)) :
    exprHead (packExpr a) = AffineCompiler.LinearExpr.head a := by
  simp only [exprHead, packExpr, AffineCompiler.LinearExpr.head,
    List.ofFn_succ, List.getD_cons_zero]

@[simp] theorem packAtom_negate {C : RegionCode} {n : ℕ} (a : AffineCompiler.Atom C n) :
    atomNegate (packAtom a) = packAtom (AffineCompiler.Atom.negate a) := by
  rcases a with ⟨comparison, expr⟩
  cases comparison <;> simp [packAtom, atomNegate, AffineCompiler.Atom.negate]

@[simp] theorem packSorted_negate {C : RegionCode} {h v : ℕ} (a : AffineCompiler.SortedAtom C h v) :
    sortedNegate (packSorted a) = packSorted (AffineCompiler.SortedAtom.negate a) := by
  cases a <;> simp [sortedNegate, packSorted, AffineCompiler.SortedAtom.negate]

@[simp] theorem packAtom_combineBounds {C : RegionCode} {n : ℕ}
    (upper lower : AffineCompiler.Atom C (n + 1)) :
    combineBounds (packAtom upper) (packAtom lower) =
      packAtom (AffineCompiler.combineBounds upper lower) := by
  rcases upper with ⟨uc, ue⟩
  rcases lower with ⟨lc, le⟩
  cases uc <;> cases lc <;>
    simp [combineBounds, packAtom, AffineCompiler.combineBounds]

@[simp] theorem packSorted_zeroTail_horizontal {C : RegionCode} {n v : ℕ}
    (a : AffineCompiler.SortedAtom C (n + 1) v) :
    zeroTail false (packSorted a) =
      (AffineCompiler.horizontalZeroTail a).map packSorted := by
  cases a <;>
    simp [zeroTail, packSorted, packAtom, AffineCompiler.horizontalZeroTail]

@[simp] theorem packSorted_zeroTail_vertical {C : RegionCode} {h n : ℕ}
    (a : AffineCompiler.SortedAtom C h (n + 1)) :
    zeroTail true (packSorted a) =
      (AffineCompiler.verticalZeroTail a).map packSorted := by
  cases a <;>
    simp [zeroTail, packSorted, packAtom, AffineCompiler.verticalZeroTail]

@[simp] theorem packSorted_positive_horizontal {C : RegionCode} {n v : ℕ}
    (a : AffineCompiler.SortedAtom C (n + 1) v) :
    positive false (packSorted a) =
      (AffineCompiler.positiveHorizontal a).map packAtom := by
  cases a <;> simp [positive, packSorted, packAtom, AffineCompiler.positiveHorizontal]

@[simp] theorem packSorted_positive_vertical {C : RegionCode} {h n : ℕ}
    (a : AffineCompiler.SortedAtom C h (n + 1)) :
    positive true (packSorted a) =
      (AffineCompiler.positiveVertical a).map packAtom := by
  cases a <;> simp [positive, packSorted, packAtom, AffineCompiler.positiveVertical]

@[simp] theorem packSorted_negative_horizontal {C : RegionCode} {n v : ℕ}
    (a : AffineCompiler.SortedAtom C (n + 1) v) :
    negative false (packSorted a) =
      (AffineCompiler.negativeHorizontal a).map packAtom := by
  cases a <;> simp [negative, packSorted, packAtom, AffineCompiler.negativeHorizontal]

@[simp] theorem packSorted_negative_vertical {C : RegionCode} {h n : ℕ}
    (a : AffineCompiler.SortedAtom C h (n + 1)) :
    negative true (packSorted a) =
      (AffineCompiler.negativeVertical a).map packAtom := by
  cases a <;> simp [negative, packSorted, packAtom, AffineCompiler.negativeVertical]

@[simp] theorem packDNF_and {C : RegionCode} {h v : ℕ}
    (p q : AffineCompiler.DNF C h v) :
    dnfAnd (packDNF p) (packDNF q) = packDNF (AffineCompiler.dnfAnd p q) := by
  simp [dnfAnd, packDNF, AffineCompiler.dnfAnd, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def]

@[simp] theorem packDNF_or {C : RegionCode} {h v : ℕ}
    (p q : AffineCompiler.DNF C h v) :
    packDNF p ++ packDNF q = packDNF (AffineCompiler.dnfOr p q) := by
  simp only [packDNF, AffineCompiler.dnfOr, List.map_append]

@[simp] theorem pack_negateClause {C : RegionCode} {h v : ℕ}
    (c : AffineCompiler.Clause C h v) :
    negateClause (c.map packSorted) = packDNF (AffineCompiler.negateClause c) := by
  simp [negateClause, AffineCompiler.negateClause, packDNF, List.map_map,
    Function.comp_def]

@[simp] theorem pack_negateDNF {C : RegionCode} {h v : ℕ}
    (p : AffineCompiler.DNF C h v) :
    negateDNF (packDNF p) = packDNF (AffineCompiler.negateDNF p) := by
  have hf : ∀ (p acc : AffineCompiler.DNF C h v),
      (packDNF p).foldl (fun acc c => dnfAnd acc (negateClause c)) (packDNF acc) =
        packDNF (p.foldl (fun acc c => AffineCompiler.dnfAnd acc
          (AffineCompiler.negateClause c)) acc) := by
    intro p
    induction p with
    | nil => intro acc; rfl
    | cons c rest ih =>
      intro acc
      change (c.map packSorted :: packDNF rest).foldl _ (packDNF acc) = _
      rw [List.foldl_cons, pack_negateClause, packDNF_and]
      exact ih (AffineCompiler.dnfAnd acc (AffineCompiler.negateClause c))
  exact hf p [[]]

@[simp] theorem pack_eliminateClause_horizontal {C : RegionCode} {n v : ℕ}
    (c : AffineCompiler.Clause C (n + 1) v) :
    eliminateClause false (c.map packSorted) =
      (AffineCompiler.eliminateHorizontalClause c).map packSorted := by
  have hz : (c.map packSorted).filterMap (zeroTail false) =
      (c.filterMap AffineCompiler.horizontalZeroTail).map packSorted := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_zeroTail_horizontal]
  have hp : (c.map packSorted).filterMap (positive false) =
      (c.filterMap AffineCompiler.positiveHorizontal).map packAtom := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_positive_horizontal]
  have hn : (c.map packSorted).filterMap (negative false) =
      (c.filterMap AffineCompiler.negativeHorizontal).map packAtom := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_negative_horizontal]
  simp only [eliminateClause, hz, hp, hn, AffineCompiler.eliminateHorizontalClause,
    List.map_append, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    packAtom_combineBounds, packSorted]

@[simp] theorem pack_eliminateClause_vertical {C : RegionCode} {h n : ℕ}
    (c : AffineCompiler.Clause C h (n + 1)) :
    eliminateClause true (c.map packSorted) =
      (AffineCompiler.eliminateVerticalClause c).map packSorted := by
  have hz : (c.map packSorted).filterMap (zeroTail true) =
      (c.filterMap AffineCompiler.verticalZeroTail).map packSorted := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_zeroTail_vertical]
  have hp : (c.map packSorted).filterMap (positive true) =
      (c.filterMap AffineCompiler.positiveVertical).map packAtom := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_positive_vertical]
  have hn : (c.map packSorted).filterMap (negative true) =
      (c.filterMap AffineCompiler.negativeVertical).map packAtom := by
    simp only [List.filterMap_map, List.map_filterMap, Function.comp_def,
      packSorted_negative_vertical]
  simp only [eliminateClause, hz, hp, hn, AffineCompiler.eliminateVerticalClause,
    List.map_append, List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def,
    packAtom_combineBounds, packSorted]

@[simp] theorem pack_eliminate_horizontal {C : RegionCode} {n v : ℕ}
    (p : AffineCompiler.DNF C (n + 1) v) :
    eliminate false (packDNF p) = packDNF (AffineCompiler.eliminateHorizontal p) := by
  simp [eliminate, packDNF, AffineCompiler.eliminateHorizontal, List.map_map,
    Function.comp_def]

@[simp] theorem pack_eliminate_vertical {C : RegionCode} {h n : ℕ}
    (p : AffineCompiler.DNF C h (n + 1)) :
    eliminate true (packDNF p) = packDNF (AffineCompiler.eliminateVertical p) := by
  simp [eliminate, packDNF, AffineCompiler.eliminateVertical, List.map_map,
    Function.comp_def]

end Native

end Tiling.AxisParallel.Decidability.Affine
