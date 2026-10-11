import Tiling.AxisParallel.Decidability.Affine.Compiler
import Tiling.AxisParallel.Decidability.Certificates.PositiveCoding

/-!
# Finite constructors for certificate formulas

Formula generators assemble the affine compiler's postorder instructions. Shifting
changes child references only; leaf data and unused references are preserved.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas

open Tiling.AxisParallel.Decidability.Affine

def dummy : SortedAtom := (false, false, [], [])

def shiftInstruction (offset : ℕ) (i : Instruction) : Instruction :=
  (i.1, i.2.1,
    if i.1 = 3 ∨ i.1 = 4 ∨ i.1 = 5 ∨ i.1 = 6 ∨ i.1 = 7 then offset + i.2.2.1
      else i.2.2.1,
    if i.1 = 3 ∨ i.1 = 4 then offset + i.2.2.2 else i.2.2.2)

def shiftCode (offset : ℕ) (code : Code) : Code := code.map (shiftInstruction offset)

def truth : Code := [(0, dummy, 0, 0)]
def falsity : Code := [(1, dummy, 0, 0)]

def atomCode (vertical strict : Bool) (expr : Expr) : Code :=
  [(2, (vertical, strict, expr), 0, 0)]

def unary (tag : ℕ) (body : Code) : Code :=
  body ++ [(tag, dummy, body.length - 1, 0)]

def binary (tag : ℕ) (left right : Code) : Code :=
  left ++ shiftCode left.length right ++
    [(tag, dummy, left.length - 1, left.length + right.length - 1)]

def conjunction (left right : Code) : Code := binary 3 left right
def disjunction (left right : Code) : Code := binary 4 left right
def negation (body : Code) : Code := unary 5 body
def existsHorizontal (body : Code) : Code := unary 6 body
def existsVertical (body : Code) : Code := unary 7 body

def implication (left right : Code) : Code := disjunction (negation left) right

def andList (formulas : List Code) : Code := formulas.foldr conjunction truth
def orList (formulas : List Code) : Code := formulas.foldr disjunction falsity

def closeHorizontal (count : ℕ) (body : Code) : Code := existsHorizontal^[count] body
def closeVertical (count : ℕ) (body : Code) : Code := existsVertical^[count] body

private theorem instructionNode_primrec : Primrec (fun p : ℕ × ℕ × ℕ =>
    ((p.1, dummy, p.2.1, p.2.2) : Instruction)) :=
  Primrec.fst.pair ((Primrec.const dummy).pair Primrec.snd)

private theorem singleton_primrec {α : Type*} [Primcodable α] :
    Primrec (fun a : α => [a]) := Primrec.list_cons.comp Primrec.id (Primrec.const [])

theorem shiftInstruction_primrec : Primrec₂ shiftInstruction := by
  have htag : Primrec (fun p : ℕ × Instruction => p.2.1) := Primrec.fst.comp Primrec.snd
  have hatom : Primrec (fun p : ℕ × Instruction => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hleft : Primrec (fun p : ℕ × Instruction => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hright : Primrec (fun p : ℕ × Instruction => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbinary : PrimrecPred (fun p : ℕ × Instruction => p.2.1 = 3 ∨ p.2.1 = 4) :=
    (Primrec.eq.comp htag (Primrec.const 3)).or
      (Primrec.eq.comp htag (Primrec.const 4))
  have href : PrimrecPred (fun p : ℕ × Instruction =>
      p.2.1 = 3 ∨ p.2.1 = 4 ∨ p.2.1 = 5 ∨ p.2.1 = 6 ∨ p.2.1 = 7) :=
    (Primrec.eq.comp htag (Primrec.const 3)).or
      ((Primrec.eq.comp htag (Primrec.const 4)).or
        ((Primrec.eq.comp htag (Primrec.const 5)).or
          ((Primrec.eq.comp htag (Primrec.const 6)).or
            (Primrec.eq.comp htag (Primrec.const 7)))))
  exact htag.pair (hatom.pair
    ((Primrec.ite href (Primrec.nat_add.comp Primrec.fst hleft) hleft).pair
      (Primrec.ite hbinary (Primrec.nat_add.comp Primrec.fst hright) hright)))

theorem shiftCode_primrec : Primrec₂ shiftCode :=
  Primrec.list_map Primrec.snd
    (shiftInstruction_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem atomCode_primrec : Primrec (fun p : Bool × Bool × Expr =>
    atomCode p.1 p.2.1 p.2.2) :=
  singleton_primrec.comp ((Primrec.const 2).pair
    (Primrec.id.pair ((Primrec.const 0).pair (Primrec.const 0))))

theorem unary_primrec : Primrec₂ unary :=
  Primrec.list_append.comp Primrec.snd
    (singleton_primrec.comp (instructionNode_primrec.comp
      (Primrec.fst.pair
        ((Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd)
          (Primrec.const 1)).pair (Primrec.const 0)))))

theorem binary_primrec : Primrec (fun p : ℕ × Code × Code => binary p.1 p.2.1 p.2.2) := by
  have hleft : Primrec (fun p : ℕ × Code × Code => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hright : Primrec (fun p : ℕ × Code × Code => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlenleft := Primrec.list_length.comp hleft
  have hlenright := Primrec.list_length.comp hright
  exact Primrec.list_append.comp
    (Primrec.list_append.comp hleft (shiftCode_primrec.comp hlenleft hright))
    (singleton_primrec.comp (instructionNode_primrec.comp
      (Primrec.fst.pair
        ((Primrec.nat_sub.comp hlenleft (Primrec.const 1)).pair
          (Primrec.nat_sub.comp (Primrec.nat_add.comp hlenleft hlenright)
            (Primrec.const 1))))))

theorem conjunction_primrec : Primrec₂ conjunction :=
  binary_primrec.comp ((Primrec.const 3).pair Primrec.id)

theorem disjunction_primrec : Primrec₂ disjunction :=
  binary_primrec.comp ((Primrec.const 4).pair Primrec.id)

theorem negation_primrec : Primrec negation :=
  unary_primrec.comp (Primrec.const 5) Primrec.id

theorem existsHorizontal_primrec : Primrec existsHorizontal :=
  unary_primrec.comp (Primrec.const 6) Primrec.id

theorem existsVertical_primrec : Primrec existsVertical :=
  unary_primrec.comp (Primrec.const 7) Primrec.id

theorem implication_primrec : Primrec₂ implication :=
  disjunction_primrec.comp (negation_primrec.comp Primrec.fst) Primrec.snd

theorem andList_primrec : Primrec andList :=
  Primrec.list_foldr Primrec.id (Primrec.const truth)
    (conjunction_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem orList_primrec : Primrec orList :=
  Primrec.list_foldr Primrec.id (Primrec.const falsity)
    (disjunction_primrec.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem closeHorizontal_primrec : Primrec₂ closeHorizontal :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    (existsHorizontal_primrec.comp Primrec.snd).to₂

theorem closeVertical_primrec : Primrec₂ closeVertical :=
  Primrec.nat_iterate Primrec.fst Primrec.snd
    (existsVertical_primrec.comp Primrec.snd).to₂

end Tiling.AxisParallel.Decidability.CertificateFormulas
