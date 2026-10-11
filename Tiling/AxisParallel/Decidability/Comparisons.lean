import Tiling.AxisParallel.Decidability.Input
import Mathlib.Computability.Partrec

/-!
# Finite signed comparison queries

An integer weighted sum of labelled coordinates can be decided by one native
comparison query. Positive and negative coefficients become repeated indices
on the left and right sides, respectively.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.Queries

abbrev SignedTerm := ℕ × ℤ

def positiveCopies (terms : List SignedTerm) : List ℕ :=
  terms.flatMap fun (j, c) => List.replicate c.toNat j

def negativeCopies (terms : List SignedTerm) : List ℕ :=
  terms.flatMap fun (j, c) => List.replicate (-c).toNat j

def compileSignedComparison (axis : Fin 2) (terms : List SignedTerm) : Query :=
  (axis, positiveCopies terms, negativeCopies terms)

def signedWeightSum (V : List Plane) (axis : Fin 2) (terms : List SignedTerm) : ℝ :=
  (terms.map fun (j, c) => (c : ℝ) * coordinate axis (V.getD j 0)).sum

private theorem intEncode_ofNat (n : ℕ) : Encodable.encode (Int.ofNat n) = 2 * n := by
  rw [Encodable.encode_ofEquiv Equiv.intEquivNat]
  change Function.uncurry Nat.bit (Prod.mk false n) = 2 * n
  simp [Nat.bit]

private theorem intEncode_negSucc (n : ℕ) : Encodable.encode (Int.negSucc n) = 2 * n + 1 := by
  rw [Encodable.encode_ofEquiv Equiv.intEquivNat]
  change Function.uncurry Nat.bit (Prod.mk true n) = 2 * n + 1
  simp [Nat.bit]

private theorem intToNat_primrec : Primrec Int.toNat := by
  have heven : Primrec (fun z : ℤ => decide (Encodable.encode z % 2 = 0)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.encode (Primrec.const 2))
      (Primrec.const 0)).decide
  refine (Primrec.cond heven
      (Primrec.nat_div.comp Primrec.encode (Primrec.const 2))
      (Primrec.const 0)).of_eq ?_
  intro z
  cases z with
  | ofNat n =>
      rw [intEncode_ofNat]
      simp
  | negSucc n =>
      rw [intEncode_negSucc]
      simp

private theorem replicate_primrec : Primrec₂ (fun n j : ℕ => List.replicate n j) := by
  have hrec : Primrec₂ (fun j n : ℕ =>
      Nat.rec (motive := fun _ => List ℕ) [] (fun _ xs => j :: xs) n) := by
    exact Primrec.nat_rec (Primrec.const ([] : List ℕ))
      (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂
  refine (hrec.comp Primrec.snd Primrec.fst).of_eq ?_
  intro x
  rcases x with ⟨n, j⟩
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate, ih]

private theorem intNegToNat_primrec : Primrec (fun z : ℤ => (-z).toNat) := by
  have hodd : Primrec (fun z : ℤ => decide (Encodable.encode z % 2 = 1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.encode (Primrec.const 2))
      (Primrec.const 1)).decide
  have hsucc : Primrec (fun z : ℤ => Encodable.encode z / 2 + 1) :=
    Primrec.nat_add.comp (Primrec.nat_div.comp Primrec.encode (Primrec.const 2))
      (Primrec.const 1)
  refine (Primrec.cond hodd hsucc (Primrec.const 0)).of_eq ?_
  intro z
  cases z with
  | ofNat n =>
      rw [intEncode_ofNat]
      simp
  | negSucc n =>
      rw [intEncode_negSucc]
      simp
      omega

private theorem positiveCopies_primrec : Primrec positiveCopies := by
  have hflat : Primrec₂ (fun terms : List SignedTerm => fun t : SignedTerm =>
      List.replicate t.2.toNat t.1) := by
    exact (replicate_primrec.comp
      (intToNat_primrec.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)).to₂
  refine (Primrec.list_flatMap Primrec.id hflat).of_eq ?_
  intro terms
  rfl

private theorem negativeCopies_primrec : Primrec negativeCopies := by
  have hflat : Primrec₂ (fun terms : List SignedTerm => fun t : SignedTerm =>
      List.replicate (-t.2).toNat t.1) := by
    exact (replicate_primrec.comp
      (intNegToNat_primrec.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.fst.comp Primrec.snd)).to₂
  refine (Primrec.list_flatMap Primrec.id hflat).of_eq ?_
  intro terms
  rfl

theorem compileSignedComparison_primrec :
    Primrec (fun x : Fin 2 × List SignedTerm =>
      compileSignedComparison x.1 x.2) := by
  exact Primrec.pair Primrec.fst
    (Primrec.pair (positiveCopies_primrec.comp Primrec.snd)
      (negativeCopies_primrec.comp Primrec.snd))

theorem compileSignedComparison_computable :
    Computable (fun x : Fin 2 × List SignedTerm =>
      compileSignedComparison x.1 x.2) :=
  compileSignedComparison_primrec.to_comp

private theorem coordinateSum_replicate (V : List Plane) (axis : Fin 2)
    (n j : ℕ) :
    coordinateSum V axis (List.replicate n j) =
      (n : ℝ) * coordinate axis (V.getD j 0) := by
  simp [coordinateSum, List.map_replicate, List.sum_replicate,
    nsmul_eq_mul]

private theorem coordinateSum_append (V : List Plane) (axis : Fin 2)
    (xs ys : List ℕ) :
    coordinateSum V axis (xs ++ ys) =
      coordinateSum V axis xs + coordinateSum V axis ys := by
  simp [coordinateSum, List.map_append, List.sum_append]

private theorem coordinateSum_positiveCopies (V : List Plane) (axis : Fin 2)
    (terms : List SignedTerm) :
    coordinateSum V axis (positiveCopies terms) =
      (terms.map fun (j, c) => (c.toNat : ℝ) * coordinate axis (V.getD j 0)).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨j, c⟩
      change coordinateSum V axis (List.replicate c.toNat j ++ positiveCopies terms) =
        ((c.toNat : ℝ) * coordinate axis (V.getD j 0)) +
          (terms.map fun (j, c) => (c.toNat : ℝ) * coordinate axis (V.getD j 0)).sum
      rw [coordinateSum_append, coordinateSum_replicate, ih]

private theorem coordinateSum_negativeCopies (V : List Plane) (axis : Fin 2)
    (terms : List SignedTerm) :
    coordinateSum V axis (negativeCopies terms) =
      (terms.map fun (j, c) => ((-c).toNat : ℝ) * coordinate axis (V.getD j 0)).sum := by
  induction terms with
  | nil => rfl
  | cons term terms ih =>
      rcases term with ⟨j, c⟩
      change coordinateSum V axis (List.replicate (-c).toNat j ++ negativeCopies terms) =
        (((-c).toNat : ℝ) * coordinate axis (V.getD j 0)) +
          (terms.map fun (j, c) => ((-c).toNat : ℝ) * coordinate axis (V.getD j 0)).sum
      rw [coordinateSum_append, coordinateSum_replicate, ih]

private theorem intToNat_sub_neg (c : ℤ) :
    (c.toNat : ℝ) - ((-c).toNat : ℝ) = (c : ℝ) := by
  cases c <;> simp

theorem signedComparison_semantics (V : List Plane) (axis : Fin 2)
    (terms : List SignedTerm) :
    coordinateSum V axis (positiveCopies terms) -
        coordinateSum V axis (negativeCopies terms) =
      signedWeightSum V axis terms := by
  rw [coordinateSum_positiveCopies, coordinateSum_negativeCopies]
  induction terms with
  | nil => simp [signedWeightSum]
  | cons term terms ih =>
      rcases term with ⟨j, c⟩
      let x := coordinate axis (V.getD j 0)
      calc
        (c.toNat : ℝ) * x +
            (terms.map fun (j, c) => (c.toNat : ℝ) * coordinate axis (V.getD j 0)).sum -
          (((-c).toNat : ℝ) * x +
            (terms.map fun (j, c) => ((-c).toNat : ℝ) * coordinate axis (V.getD j 0)).sum) =
            ((c.toNat : ℝ) - ((-c).toNat : ℝ)) * x +
              ((terms.map fun (j, c) => (c.toNat : ℝ) * coordinate axis (V.getD j 0)).sum -
                (terms.map fun (j, c) =>
                  ((-c).toNat : ℝ) * coordinate axis (V.getD j 0)).sum) := by ring
        _ = (c : ℝ) * x + signedWeightSum V axis terms := by
          rw [intToNat_sub_neg, ih]

theorem compileSignedComparison_correct {V : List Plane} {answer : Query → Bool}
    (hanswer : CorrectOracle V answer) (axis : Fin 2) (terms : List SignedTerm) :
    answer (compileSignedComparison axis terms) = true ↔
      signedWeightSum V axis terms ≤ 0 := by
  change answer (axis, positiveCopies terms, negativeCopies terms) = true ↔ _
  rw [hanswer axis (positiveCopies terms) (negativeCopies terms)]
  rw [← signedComparison_semantics]
  exact (sub_nonpos : _ ↔ _).symm

end Tiling.AxisParallel.Decidability.Queries
