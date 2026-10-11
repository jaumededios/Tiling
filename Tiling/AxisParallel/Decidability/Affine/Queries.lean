import Tiling.AxisParallel.Decidability.Affine.Computability
import Tiling.AxisParallel.Decidability.Affine.Correspondence
import Tiling.AxisParallel.Terminal.AffineCompilerCorrectness
import Mathlib.Algebra.BigOperators.Fin

/-! Positive denominator clearing and oracle interpretation of packed compilation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.Affine

abbrev PackedQuery := Bool × List ℤ × List ℤ

def commonDenominator (constants : List ℚ) : ℕ := (constants.map Rat.den).prod

def clearCoefficients (constants : List ℚ) : List ℤ :=
  constants.map fun q => (((commonDenominator constants : ℕ) : ℚ) * q).num

def atomQuery (a : SortedAtom) : PackedQuery :=
  let constants := a.2.2.2
  let coefficients := clearCoefficients constants
  let zeros := List.replicate constants.length 0
  if a.2.1 then (a.1, zeros, coefficients) else (a.1, coefficients, zeros)

def evalAtom (answer : PackedQuery → Bool) (a : SortedAtom) : Bool :=
  if a.2.1 then !(answer (atomQuery a)) else answer (atomQuery a)

def evalDNF (answer : PackedQuery → Bool) (p : DNF) : Bool :=
  p.any fun clause => clause.all (evalAtom answer)

def decidePackedFormula (answer : PackedQuery → Bool) (code : Code) : Bool :=
  evalDNF answer (compile code)

theorem commonDenominator_computable : Computable commonDenominator := by
  have hm : Computable (fun constants : List ℚ => constants.map Rat.den) :=
    Tiling.Computability.List.map_computable (0 : ℚ) Computable.id
      (rat_den_computable.comp Computable.snd).to₂
  have hp : Computable (fun xs : List ℕ => xs.prod) := by
    refine (Tiling.Computability.List.foldl_computable 0 Computable.id (Computable.const 1)
      (Primrec.nat_mul.to_comp.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd)).to₂).of_eq ?_
    intro xs
    have hgeneral : ∀ (xs : List ℕ) (initial : ℕ),
        xs.foldl (fun acc x => acc * x) initial = initial * xs.prod := by
      intro xs
      induction xs with
      | nil => intro initial; simp
      | cons x rest ih => intro initial; simp [List.foldl_cons, ih, Nat.mul_assoc]
    simpa using hgeneral xs 1
  exact hp.comp hm

theorem clearCoefficients_computable : Computable clearCoefficients :=
  Tiling.Computability.List.map_computable (0 : ℚ) Computable.id
    (rat_num_computable.comp
      (rat_mul_computable.comp
        (nat_rat_computable.comp
          (commonDenominator_computable.comp Computable.fst)) Computable.snd)).to₂

private theorem replicate_primrec : Primrec₂ (fun n : ℕ => fun x : ℤ => List.replicate n x) := by
  have hrec : Primrec₂ (fun x : ℤ => fun n : ℕ =>
      Nat.rec (motive := fun _ => List ℤ) [] (fun _ xs => x :: xs) n) :=
    Primrec.nat_rec (Primrec.const [])
      (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  refine (hrec.comp Primrec.snd Primrec.fst).of_eq ?_
  rintro ⟨n, x⟩
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, ih]

theorem atomQuery_computable : Computable atomQuery := by
  have hconstants : Computable (fun a : SortedAtom => a.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hclear := clearCoefficients_computable.comp hconstants
  have hzeros := replicate_primrec.to_comp.comp
    (Computable.list_length.comp hconstants) (Computable.const 0)
  refine (Computable.cond (Computable.fst.comp Computable.snd)
    (Computable.fst.pair (hzeros.pair hclear))
    (Computable.fst.pair (hclear.pair hzeros))).of_eq ?_
  intro a
  cases h : a.2.1 <;> simp only [atomQuery, h, Bool.false_eq_true, ↓reduceIte] <;> rfl

namespace Native

open Tiling.AxisParallel.Terminal.Executable

def packQuery {C : RegionCode} (q : Query C) : PackedQuery :=
  (decide (q.sort = .vertical), List.ofFn q.lhs, List.ofFn q.rhs)

/-- Interpret arbitrary packed coefficients as a native fixed-dimension query. -/
def unpackQuery (C : RegionCode) (q : PackedQuery) : Query C :=
  ⟨if q.1 then .vertical else .horizontal,
    fun i => q.2.1.getD i 0, fun i => q.2.2.getD i 0⟩

@[simp] theorem unpackQuery_packQuery {C : RegionCode} (q : Query C) :
    unpackQuery C (packQuery q) = q := by
  cases q with
  | mk sort lhs rhs =>
    cases sort <;> simp [unpackQuery, packQuery]

@[simp] theorem commonDenominator_packExpr {C : RegionCode}
    (e : AffineCompiler.LinearExpr C 0) :
    commonDenominator (packExpr e).2 = AffineCompiler.commonDenominator e := by
  simp [commonDenominator, packExpr, AffineCompiler.commonDenominator, List.prod_ofFn,
    Function.comp_def]

@[simp] theorem clearCoefficients_packExpr {C : RegionCode}
    (e : AffineCompiler.LinearExpr C 0) :
    clearCoefficients (packExpr e).2 = List.ofFn (AffineCompiler.clearInput e) := by
  change (List.ofFn e.constant).map _ = _
  rw [commonDenominator_packExpr]
  rw [List.map_ofFn]
  rfl

@[simp] theorem evalAtom_pack {C : RegionCode} (O : Oracle C)
    (answer : PackedQuery → Bool) (hanswer : ∀ q, answer (packQuery q) = O.answer q)
    (s : CoordSort) (a : AffineCompiler.Atom C 0) :
    evalAtom answer (decide (s = .vertical), packAtom a) =
      AffineCompiler.evalClosedAtom O s a := by
  rcases a with ⟨comparison, e⟩
  have hz : List.ofFn (Coeff.zero C) = List.replicate C.vertexCount 0 := by
    change List.ofFn (fun _ : Fin C.vertexCount => (0 : ℤ)) = _
    simp
  cases comparison
  · have hquery : atomQuery (decide (s = .vertical), packAtom ⟨.weak, e⟩) =
        packQuery (AffineCompiler.closedAtomQuery s ⟨.weak, e⟩) := by
      simp [atomQuery, packAtom, packExpr, packQuery, AffineCompiler.closedAtomQuery,
        hz, ← clearCoefficients_packExpr e]
      rfl
    change answer (atomQuery (decide (s = .vertical), packAtom ⟨.weak, e⟩)) = _
    rw [hquery, hanswer]
    rfl
  · have hquery : atomQuery (decide (s = .vertical), packAtom ⟨.strict, e⟩) =
        packQuery ⟨s, Coeff.zero C, AffineCompiler.clearInput e⟩ := by
      simp [atomQuery, packAtom, packExpr, packQuery, hz,
        ← clearCoefficients_packExpr e]
    change Bool.not (answer (atomQuery (decide (s = .vertical), packAtom ⟨.strict, e⟩))) =
      Bool.not (O.answer ⟨s, Coeff.zero C, AffineCompiler.clearInput e⟩)
    rw [hquery, hanswer]

@[simp] theorem evalDNF_pack {C : RegionCode} (O : Oracle C)
    (answer : PackedQuery → Bool) (hanswer : ∀ q, answer (packQuery q) = O.answer q)
    (p : AffineCompiler.DNF C 0 0) :
    evalDNF answer (packDNF p) = AffineCompiler.evalClosedDNF O p := by
  have ha : ∀ a : AffineCompiler.SortedAtom C 0 0,
      evalAtom answer (packSorted a) = AffineCompiler.evalClosedSortedAtom O a := by
    intro a
    cases a with
    | horizontal a =>
      simpa [packSorted, AffineCompiler.evalClosedSortedAtom] using
        (evalAtom_pack O answer hanswer .horizontal a)
    | vertical a =>
      simpa [packSorted, AffineCompiler.evalClosedSortedAtom] using
        (evalAtom_pack O answer hanswer .vertical a)
  have hc : ∀ clause : AffineCompiler.Clause C 0 0,
      (clause.map packSorted).all (evalAtom answer) =
        AffineCompiler.evalClosedClause O clause := by
    intro clause
    simp only [List.all_map, AffineCompiler.evalClosedClause]
    congr 1
    funext a
    exact ha a
  simp only [evalDNF, packDNF, List.any_map, AffineCompiler.evalClosedDNF]
  congr 1
  funext clause
  exact hc clause

/-- Packed compilation followed by packed queries agrees with native formula decision. -/
theorem decidePackedFormula_eq_decideFormula {C : RegionCode} (O : Oracle C)
    (answer : PackedQuery → Bool) (hanswer : ∀ q, answer (packQuery q) = O.answer q)
    (f : Formula C 0 0) :
    decidePackedFormula answer (packFormula f) = AffineCompiler.decideFormula O f := by
  rw [decidePackedFormula, compile_packFormula, evalDNF_pack O answer hanswer]
  rfl

/-- Native semantic correctness therefore applies to the concrete packed compiler. -/
theorem decidePackedFormula_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (answer : PackedQuery → Bool)
    (hanswer : ∀ q, answer (packQuery q) = O.toOracle.answer q) (f : Formula C 0 0) :
    decidePackedFormula answer (packFormula f) = true ↔
      Formula.Holds R f (Fin.elim0) (Fin.elim0) := by
  rw [decidePackedFormula_eq_decideFormula O.toOracle answer hanswer]
  exact AffineCompiler.decideFormula_correct R O f

/-- The canonical packed oracle gives native decision without an extra representation hypothesis. -/
theorem decidePackedFormula_native {C : RegionCode} (O : Oracle C) (f : Formula C 0 0) :
    decidePackedFormula (fun q => O.answer (unpackQuery C q)) (packFormula f) =
      AffineCompiler.decideFormula O f := by
  apply decidePackedFormula_eq_decideFormula
  intro q
  rw [unpackQuery_packQuery]

/-- Semantic correctness for native input and its canonical packed query oracle. -/
theorem decidePackedFormula_native_correct {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (f : Formula C 0 0) :
    decidePackedFormula (fun q => O.toOracle.answer (unpackQuery C q)) (packFormula f) = true ↔
      Formula.Holds R f Fin.elim0 Fin.elim0 := by
  rw [decidePackedFormula_native]
  exact AffineCompiler.decideFormula_correct R O f

end Native

end Tiling.AxisParallel.Decidability.Affine
