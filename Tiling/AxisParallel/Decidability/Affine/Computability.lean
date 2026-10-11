import Tiling.AxisParallel.Decidability.Affine.Compiler
import Tiling.AxisParallel.Decidability.Certificates.PositiveCoding

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.Computability.List

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.Affine

private theorem boolNot_computable : Computable Bool.not :=
  (Primrec.dom_bool _).to_comp

private theorem boolOr_computable : Computable₂ Bool.or :=
  (Primrec.dom_bool₂ _).to_comp

private theorem addArray_computable_of {hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ)} :
    Computable₂ addArray := by
  exact map_computable 0
    ((Primrec.list_range.to_comp).comp (Computable.list_length.comp Computable.fst))
    ((hadd.comp
      ((Primrec.list_getD (0 : ℚ)).to_comp.comp
        (Computable.fst.comp Computable.fst) Computable.snd)
      ((Primrec.list_getD (0 : ℚ)).to_comp.comp
        (Computable.snd.comp Computable.fst) Computable.snd)).to₂)

private theorem exprAdd_computable_of (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ)) :
    Computable₂ exprAdd :=
  ((@addArray_computable_of hadd).comp
    (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)).pair
  ((@addArray_computable_of hadd).comp
    (Computable.snd.comp Computable.fst) (Computable.snd.comp Computable.snd))

private theorem exprNeg_computable_of (hneg : Computable (Neg.neg : ℚ → ℚ)) :
    Computable exprNeg :=
  (map_computable (0 : ℚ) Computable.fst (hneg.comp Computable.snd).to₂).pair
  (map_computable (0 : ℚ) Computable.snd (hneg.comp Computable.snd).to₂)

private theorem exprSub_computable_of (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ))
    (hneg : Computable (Neg.neg : ℚ → ℚ)) : Computable₂ exprSub :=
  (exprAdd_computable_of hadd).comp Computable.fst
    ((exprNeg_computable_of hneg).comp Computable.snd)

private theorem exprScale_computable_of (hmul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ)) :
    Computable₂ exprScale :=
  (map_computable (0 : ℚ) (Computable.fst.comp Computable.snd)
    (hmul.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).pair
  (map_computable (0 : ℚ) (Computable.snd.comp Computable.snd)
    (hmul.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)

private theorem exprTail_computable : Computable exprTail :=
  ((Primrec.list_tail.to_comp).comp Computable.fst).pair Computable.snd

private theorem exprHead_computable : Computable exprHead :=
  (Primrec.list_getD (0 : ℚ)).to_comp.comp Computable.fst (Computable.const 0)

private theorem atomNegate_computable_of (hneg : Computable (Neg.neg : ℚ → ℚ)) :
    Computable atomNegate :=
  (boolNot_computable.comp Computable.fst).pair
    ((exprNeg_computable_of hneg).comp Computable.snd)

private theorem sortedNegate_computable_of (hneg : Computable (Neg.neg : ℚ → ℚ)) :
    Computable sortedNegate :=
  Computable.fst.pair ((atomNegate_computable_of hneg).comp Computable.snd)

private theorem dnfAnd_computable : Computable₂ dnfAnd := by
  exact flatMap_computable ([] : Clause) Computable.fst
    (map_computable ([] : Clause)
      (Computable.snd.comp Computable.fst)
      ((Computable.list_append.comp (Computable.snd.comp Computable.fst)
        Computable.snd).to₂)).to₂

private theorem negateClause_computable_of (hneg : Computable (Neg.neg : ℚ → ℚ)) :
    Computable negateClause :=
  map_computable (false, false, [], []) Computable.id
    ((Computable.list_cons.comp ((sortedNegate_computable_of hneg).comp Computable.snd)
      (Computable.const [])).to₂)

private theorem negateDNF_computable_of (hneg : Computable (Neg.neg : ℚ → ℚ)) :
    Computable negateDNF :=
  foldl_computable ([] : Clause) Computable.id (Computable.const [[]])
    ((dnfAnd_computable.comp (Computable.fst.comp Computable.snd)
      ((negateClause_computable_of hneg).comp (Computable.snd.comp Computable.snd))).to₂)

private theorem combineBounds_computable_of
    (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ))
    (hneg : Computable (Neg.neg : ℚ → ℚ))
    (hmul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ)) : Computable₂ combineBounds := by
  have hu : Computable (fun x : Atom × Atom => x.1.2) :=
    Computable.snd.comp Computable.fst
  have hl : Computable (fun x : Atom × Atom => x.2.2) :=
    Computable.snd.comp Computable.snd
  exact (boolOr_computable.comp
      (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd)).pair
    ((exprSub_computable_of hadd hneg).comp
      ((exprScale_computable_of hmul).comp
        (exprHead_computable.comp hu) (exprTail_computable.comp hl))
      ((exprScale_computable_of hmul).comp
        (exprHead_computable.comp hl) (exprTail_computable.comp hu)))

private theorem zeroTail_computable : Computable₂ zeroTail := by
  have hsort : Computable (fun x : Bool × SortedAtom => decide (x.2.1 = x.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).decide.to_comp
  have hexpr : Computable (fun x : Bool × SortedAtom => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hzero : Computable (fun x : Bool × SortedAtom => decide (exprHead x.2.2.2 = 0)) :=
    (Primrec.eq.decide.to_comp).comp
      (exprHead_computable.comp hexpr) (Computable.const (0 : ℚ))
  refine (Computable.cond hsort
    (Computable.cond hzero
      (Computable.option_some.comp (Computable.fst.pair
        ((Computable.fst.comp (Computable.snd.comp Computable.snd)).pair
          (exprTail_computable.comp hexpr))))
      (Computable.const none))
    (Computable.option_some.comp Computable.snd)).of_eq ?_
  intro x
  by_cases hs : x.2.1 = x.1 <;> by_cases hz : exprHead x.2.2.2 = 0 <;>
    simp [zeroTail, hs, hz]

private theorem positive_computable_of
    (hlt : Computable₂ (fun x y : ℚ => decide (x < y))) : Computable₂ positive := by
  have hsort : Computable (fun x : Bool × SortedAtom => decide (x.2.1 = x.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).decide.to_comp
  have hexpr : Computable (fun x : Bool × SortedAtom => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hpos := hlt.comp (Computable.const 0) (exprHead_computable.comp hexpr)
  refine (Computable.cond
    ((Primrec.dom_bool₂ Bool.and).to_comp.comp hsort hpos)
    (Computable.option_some.comp (Computable.snd.comp Computable.snd))
    (Computable.const none)).of_eq ?_
  intro x
  by_cases hs : x.2.1 = x.1 <;> by_cases hp : 0 < exprHead x.2.2.2 <;>
    simp [positive, hs, hp]

private theorem negative_computable_of
    (hlt : Computable₂ (fun x y : ℚ => decide (x < y))) : Computable₂ negative := by
  have hsort : Computable (fun x : Bool × SortedAtom => decide (x.2.1 = x.1)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) Primrec.fst).decide.to_comp
  have hexpr : Computable (fun x : Bool × SortedAtom => x.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hneg := hlt.comp (exprHead_computable.comp hexpr) (Computable.const 0)
  refine (Computable.cond
    ((Primrec.dom_bool₂ Bool.and).to_comp.comp hsort hneg)
    (Computable.option_some.comp (Computable.snd.comp Computable.snd))
    (Computable.const none)).of_eq ?_
  intro x
  by_cases hs : x.2.1 = x.1 <;> by_cases hn : exprHead x.2.2.2 < 0 <;>
    simp [negative, hs, hn]

private theorem eliminateClause_computable_of
    (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ))
    (hneg : Computable (Neg.neg : ℚ → ℚ))
    (hmul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ))
    (hlt : Computable₂ (fun x y : ℚ => decide (x < y))) :
    Computable₂ eliminateClause := by
  have hfixed : Computable (fun x : Bool × Clause => x.2.filterMap (zeroTail x.1)) :=
    filterMap_computable (false, false, [], []) Computable.snd
      (zeroTail_computable.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have huppers : Computable (fun x : Bool × Clause => x.2.filterMap (positive x.1)) :=
    filterMap_computable (false, false, [], []) Computable.snd
      ((positive_computable_of hlt).comp
        (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hlowers : Computable (fun x : Bool × Clause => x.2.filterMap (negative x.1)) :=
    filterMap_computable (false, false, [], []) Computable.snd
      ((negative_computable_of hlt).comp
        (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hcombined : Computable₂ (fun x : (Bool × Clause) × Atom => fun lower : Atom =>
      (x.1.1, combineBounds x.2 lower)) :=
    (Computable.fst.comp (Computable.fst.comp Computable.fst)).pair
      ((combineBounds_computable_of hadd hneg hmul).comp
        (Computable.snd.comp Computable.fst) Computable.snd)
  exact Computable.list_append.comp hfixed
    (flatMap_computable (false, [], []) huppers
      (map_computable (false, [], []) (hlowers.comp Computable.fst) hcombined).to₂)

private theorem eliminate_computable_of
    (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ))
    (hneg : Computable (Neg.neg : ℚ → ℚ))
    (hmul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ))
    (hlt : Computable₂ (fun x y : ℚ => decide (x < y))) : Computable₂ eliminate :=
  map_computable ([] : Clause) Computable.snd
    ((eliminateClause_computable_of hadd hneg hmul hlt).comp
      (Computable.fst.comp Computable.fst) Computable.snd).to₂

private theorem chooseTag_computable {α σ : Type*} [Primcodable α] [Primcodable σ]
    {tag : α → ℕ} {yes no : α → σ} (value : ℕ)
    (htag : Computable tag) (hyes : Computable yes) (hno : Computable no) :
    Computable (fun x => if tag x = value then yes x else no x) := by
  refine (Computable.cond
    (Primrec.eq.decide.to_comp.comp htag (Computable.const value)) hyes hno).of_eq ?_
  intro x
  by_cases h : tag x = value <;> simp [h]

private theorem instruction_computable_of
    (hadd : Computable₂ ((· + ·) : ℚ → ℚ → ℚ))
    (hneg : Computable (Neg.neg : ℚ → ℚ))
    (hmul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ))
    (hlt : Computable₂ (fun x y : ℚ => decide (x < y))) : Computable₂ instruction := by
  have htag : Computable (fun x : List DNF × Instruction => x.2.1) :=
    Computable.fst.comp Computable.snd
  have hleft : Computable (fun x : List DNF × Instruction => x.1.getD x.2.2.2.1 []) :=
    (Primrec.list_getD ([] : DNF)).to_comp.comp Computable.fst
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hright : Computable (fun x : List DNF × Instruction => x.1.getD x.2.2.2.2 []) :=
    (Primrec.list_getD ([] : DNF)).to_comp.comp Computable.fst
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hatom : Computable (fun x : List DNF × Instruction => [[x.2.2.1]]) :=
    Computable.list_cons.comp
      (Computable.list_cons.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd)) (Computable.const []))
      (Computable.const [])
  exact chooseTag_computable 0 htag (Computable.const [[]])
    (chooseTag_computable 1 htag (Computable.const [])
    (chooseTag_computable 2 htag hatom
    (chooseTag_computable 3 htag (dnfAnd_computable.comp hleft hright)
    (chooseTag_computable 4 htag (Computable.list_append.comp hleft hright)
    (chooseTag_computable 5 htag ((negateDNF_computable_of hneg).comp hleft)
    (chooseTag_computable 6 htag
      ((eliminate_computable_of hadd hneg hmul hlt).comp (Computable.const false) hleft)
    (chooseTag_computable 7 htag
      ((eliminate_computable_of hadd hneg hmul hlt).comp (Computable.const true) hleft)
      (Computable.const []))))))))

theorem exprAdd_computable : Computable₂ exprAdd :=
  exprAdd_computable_of rat_add_computable

theorem exprNeg_computable : Computable exprNeg :=
  exprNeg_computable_of rat_neg_computable

theorem exprSub_computable : Computable₂ exprSub :=
  exprSub_computable_of rat_add_computable
    rat_neg_computable

theorem exprScale_computable : Computable₂ exprScale :=
  exprScale_computable_of rat_mul_computable

/-- Every packed instruction is computable with Mathlib's native rational encoding. -/
theorem instruction_computable : Computable₂ instruction :=
  instruction_computable_of rat_add_computable
    rat_neg_computable rat_mul_computable
    rat_lt_computable

/-- Compilation of a finite packed instruction list is uniformly computable. -/
theorem compileInto_computable : Computable₂ compileInto :=
  foldl_computable (0, (false, false, [], []), 0, 0) Computable.snd Computable.fst
    ((Computable.list_concat.comp (Computable.fst.comp Computable.snd)
      (instruction_computable.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))).to₂)

/-- The full finite Fourier–Motzkin compiler has an actual computation certificate. -/
theorem compile_computable : Computable compile := by
  have hresults : Computable (fun code : Code => compileInto [] code) :=
    compileInto_computable.comp (Computable.const []) Computable.id
  refine (Computable.option_getD
    (Computable.list_getElem?.comp hresults
      (Primrec.nat_sub.to_comp.comp (Computable.list_length.comp hresults) (Computable.const 1)))
    (Computable.const [])).of_eq ?_
  intro code
  rw [compile, List.getLast?_eq_getElem?]

end Tiling.AxisParallel.Decidability.Affine
