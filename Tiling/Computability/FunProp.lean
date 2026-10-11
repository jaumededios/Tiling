import Tiling.Computability.Rational
import Tiling.Computability.List
import Mathlib.Tactic.FunProp

/-! Compositional computability rules for arithmetic and finite lists. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair
attribute [fun_prop] Computable.fst Computable.snd

namespace Tiling.Computability.FunProp

open Tiling.Computability.Rational

@[fun_prop] theorem c_natAdd {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => (f0 x) + (f1 x)) :=
  Primrec.nat_add.to_comp.comp h0 h1

@[fun_prop] theorem c_natMul {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => (f0 x) * (f1 x)) :=
  Primrec.nat_mul.to_comp.comp h0 h1

@[fun_prop] theorem c_natSub {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (f1 : α → ℕ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => (f0 x) - (f1 x)) :=
  Primrec.nat_sub.to_comp.comp h0 h1

@[fun_prop] theorem c_intOfNat {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (h0 : Computable f0) :
    Computable (fun x => Int.ofNat (f0 x)) :=
  int_ofNat_computable.comp h0

@[fun_prop] theorem c_intSub {α : Type*} [Primcodable α]
    (f0 : α → ℤ) (f1 : α → ℤ) (h0 : Computable f0) (h1 : Computable f1) :
    Computable (fun x => (f0 x) - (f1 x)) :=
  int_sub_computable.comp h0 h1

@[fun_prop] theorem c_intRat {α : Type*} [Primcodable α]
    (f0 : α → ℤ) (h0 : Computable f0) :
    Computable (fun x => ((f0 x) : ℚ)) :=
  int_rat_computable.comp h0

@[fun_prop] theorem c_natRat {α : Type*} [Primcodable α]
    (f0 : α → ℕ) (h0 : Computable f0) :
    Computable (fun x => ((f0 x) : ℚ)) :=
  nat_rat_computable.comp h0

@[fun_prop] theorem c_ratNeg {α : Type*} [Primcodable α]
    (f0 : α → ℚ) (h0 : Computable f0) :
    Computable (fun x => -(f0 x)) :=
  rat_neg_computable.comp h0

@[fun_prop] theorem c_listLength {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → List β) (hf : Computable f) : Computable (fun x => (f x).length) :=
  Computable.list_length.comp hf

@[fun_prop] theorem c_listRange {α : Type*} [Primcodable α]
    (f : α → ℕ) (hf : Computable f) : Computable (fun x => List.range (f x)) :=
  Primrec.list_range.to_comp.comp hf

@[fun_prop] theorem c_listCons {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → β) (g : α → List β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => f x :: g x) := Computable.list_cons.comp hf hg

@[fun_prop] theorem c_listAppend {α β : Type*} [Primcodable α] [Primcodable β]
    (f g : α → List β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => f x ++ g x) := Computable.list_append.comp hf hg

@[fun_prop] theorem c_listMap {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Inhabited β] (f : α → List β) (g : α → β → γ)
    (hf : Computable f) (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun x => (f x).map (g x)) :=
  Tiling.Computability.List.map_computable default hf hg

@[fun_prop] theorem c_listFlatMap {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Inhabited β] (f : α → List β) (g : α → β → List γ)
    (hf : Computable f) (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun x => (f x).flatMap (g x)) :=
  Tiling.Computability.List.flatMap_computable default hf hg

@[fun_prop] theorem c_listGetD {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → List β) (g : α → ℕ) (default : β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => (f x).getD (g x) default) :=
  (Primrec.list_getD default).to_comp.comp hf hg

@[fun_prop] theorem c_listTake {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → ℕ) (g : α → List β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => (g x).take (f x)) := Primrec.list_take.to_comp.comp hf hg

@[fun_prop] theorem c_natListSum {α : Type*} [Primcodable α]
    (f : α → List ℕ) (hf : Computable f) : Computable (fun x => (f x).sum) :=
  (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).to_comp.comp hf

@[fun_prop] theorem c_iteEq {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [DecidableEq β] (f g : α → β) (a b : α → γ)
    (hf : Computable f) (hg : Computable g) (ha : Computable a) (hb : Computable b) :
    Computable (fun x => if f x = g x then a x else b x) :=
  (Computable.cond ((Primrec.eq.decide.to_comp).comp hf hg) ha hb).of_eq
    (fun x => by by_cases h : f x = g x <;> simp [h])

@[fun_prop] theorem c_cond {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → Bool) (a b : α → β) (hf : Computable f) (ha : Computable a) (hb : Computable b) :
    Computable (fun x => bif f x then a x else b x) := Computable.cond hf ha hb

end Tiling.Computability.FunProp
