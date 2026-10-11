import Tiling.AxisParallel.Decidability.RectangleInput.Oracle
import Tiling.AxisParallel.Terminal.LocalCoverSearch

/-!
# Finite-query construction of the local covering bound

A second fixed comparison schedule compares every ordered pair of vertex
differences. Its Boolean table suffices for the exact maximum folds in the
production bound builder. The selected width is always cell zero.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.RectangleInput.LocalBound

open Tiling.AxisParallel.Decidability.RectangleInput
open Tiling.AxisParallel.Decidability.PositiveCoding

abbrev Bounds := List ℤ × List ℤ × List ℤ × List ℤ
abbrev Key := Bool × Cell

def keys (n : ℕ) : List Key :=
  (candidates n).flatMap fun c => [(false, c), (true, c)]

def cornerLabel (labels : List PointLabel) (vertical : Bool) (i : ℕ) : ℕ :=
  bif vertical then (labels.getD i (0, 0)).2 else (labels.getD i (0, 0)).1

def query (labels : List PointLabel) (k : Key) : Tiling.AxisParallel.Decidability.Query :=
  (axis k.1, [cornerLabel labels k.1 k.2.1.1, cornerLabel labels k.1 k.2.2.2],
    [cornerLabel labels k.1 k.2.2.1, cornerLabel labels k.1 k.2.1.2])

def queries (P : PackedRegion) : List Tiling.AxisParallel.Decidability.Query :=
  (keys P.1.length).map (query P.1)

def history (P : PackedRegion)
    (answer : Tiling.AxisParallel.Decidability.Query → Bool) : List Bool :=
  (queries P).map answer

def table (n : ℕ) (answers : List Bool) (vertical : Bool) (a b : ℕ × ℕ) : Bool :=
  answers.getD ((keys n).findIdx (fun k => decide (k = (vertical, a, b)))) false

def differenceCandidates (n : ℕ) : List (ℕ × ℕ) :=
  (pairs n).flatMap fun p => [p, (p.2, p.1)]

def maximumPair (n : ℕ) (answers : List Bool) (vertical : Bool) : ℕ × ℕ :=
  (differenceCandidates n).foldl
    (fun a b => bif table n answers vertical a b then b else a) (0, 0)

def differenceCoeff (n : ℕ) (p : ℕ × ℕ) : List ℤ :=
  (List.range n).map fun i =>
    (bif i == p.1 then (1 : ℤ) else 0) - (bif i == p.2 then (1 : ℤ) else 0)

def build (P : PackedRegion) (answers : List Bool) : Option Bounds :=
  if 0 < P.2.length then
    let n := P.1.length
    let c := P.2.getD 0 (0, 0)
    some (differenceCoeff n (maximumPair n answers false),
      differenceCoeff n (maximumPair n answers true),
      differenceCoeff n (c.1.2 % n, c.1.1 % n),
      differenceCoeff n (c.2.2 % n, c.2.1 % n))
  else none

theorem mem_keys {n : ℕ} {k : Key} :
    k ∈ keys n ↔ k.2.1.1 < n ∧ k.2.1.2 < n ∧ k.2.2.1 < n ∧ k.2.2.2 < n := by
  cases k with
  | mk v c => cases v <;> simp [keys, mem_candidates]

theorem table_history {P : PackedRegion} {vertical : Bool} {a b : ℕ × ℕ}
    (ha : a.1 < P.1.length ∧ a.2 < P.1.length)
    (hb : b.1 < P.1.length ∧ b.2 < P.1.length)
    (answer : Tiling.AxisParallel.Decidability.Query → Bool) :
    table P.1.length (history P answer) vertical a b = answer (query P.1 (vertical, a, b)) := by
  have hkey : (vertical, a, b) ∈ keys P.1.length := mem_keys.mpr ⟨ha.1, ha.2, hb.1, hb.2⟩
  have hex : ∃ k ∈ keys P.1.length, decide (k = (vertical, a, b)) = true :=
    ⟨_, hkey, by simp⟩
  have hlt := List.findIdx_lt_length_of_exists hex
  have hget := List.findIdx_getElem (w := hlt)
  have hgeteq : (keys P.1.length)[
      (keys P.1.length).findIdx (fun k => decide (k = (vertical, a, b)))] =
      (vertical, a, b) := by simpa only [decide_eq_true_eq] using hget
  simp only [table, history, queries, List.map_map]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hlt)]
  simp only [List.getElem_map, Function.comp_apply]
  rw [hgeteq]

theorem keys_primrec : Primrec keys :=
  Primrec.list_flatMap candidates_primrec
    (Primrec.list_cons.comp (Primrec.pair (Primrec.const false) Primrec.snd)
      (Primrec.list_cons.comp (Primrec.pair (Primrec.const true) Primrec.snd)
        (Primrec.const [])))

theorem cornerLabel_comp {α : Type*} [Primcodable α]
    {labels : α → List PointLabel} {v : α → Bool} {i : α → ℕ}
    (hl : Primrec labels) (hv : Primrec v) (hi : Primrec i) :
    Primrec (fun x => cornerLabel (labels x) (v x) (i x)) :=
  Primrec.cond hv
    (Primrec.snd.comp ((Primrec.list_getD (0, 0)).comp hl hi))
    (Primrec.fst.comp ((Primrec.list_getD (0, 0)).comp hl hi))

theorem query_primrec : Primrec₂ query := by
  have hv : Primrec (fun x : List PointLabel × Key => x.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun x : List PointLabel × Key => x.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.pair ((Primrec.dom_bool axis).comp hv)
    (Primrec.pair
      (Primrec.list_cons.comp
        (cornerLabel_comp Primrec.fst hv (Primrec.fst.comp (Primrec.fst.comp hc)))
        (Primrec.list_cons.comp
          (cornerLabel_comp Primrec.fst hv (Primrec.snd.comp (Primrec.snd.comp hc)))
          (Primrec.const [])))
      (Primrec.list_cons.comp
        (cornerLabel_comp Primrec.fst hv (Primrec.fst.comp (Primrec.snd.comp hc)))
        (Primrec.list_cons.comp
          (cornerLabel_comp Primrec.fst hv (Primrec.snd.comp (Primrec.fst.comp hc)))
          (Primrec.const []))))

theorem queries_primrec : Primrec queries :=
  Primrec.list_map (keys_primrec.comp (Primrec.list_length.comp Primrec.fst))
    (query_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)

theorem table_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {answers : α → List Bool} {v : α → Bool}
    {a b : α → ℕ × ℕ} (hn : Primrec n) (hh : Primrec answers) (hv : Primrec v)
    (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => table (n x) (answers x) (v x) (a x) (b x)) :=
  (Primrec.list_getD false).comp hh
    (listFindIdx_comp (keys_primrec.comp hn)
      ((Primrec.eq.comp Primrec.snd
        ((hv.comp Primrec.fst).pair ((ha.comp Primrec.fst).pair
          (hb.comp Primrec.fst)))).decide).to₂)

theorem differenceCandidates_primrec : Primrec differenceCandidates :=
  Primrec.list_flatMap pairs_primrec
    (Primrec.list_cons.comp Primrec.snd
      (Primrec.list_cons.comp
        (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
        (Primrec.const [])))

theorem maximumPair_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {answers : α → List Bool} {v : α → Bool}
    (hn : Primrec n) (hh : Primrec answers) (hv : Primrec v) :
    Primrec (fun x => maximumPair (n x) (answers x) (v x)) :=
  Primrec.list_foldl (differenceCandidates_primrec.comp hn) (Primrec.const (0, 0))
    (Primrec.cond
      (table_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst) (hv.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).to₂

theorem differenceCoeff_primrec : Primrec₂ differenceCoeff :=
  Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (int_sub_primrec.comp
      (Primrec.cond (Primrec.beq.comp Primrec.snd
          (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const (1 : ℤ)) (Primrec.const 0))
      (Primrec.cond (Primrec.beq.comp Primrec.snd
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const (1 : ℤ)) (Primrec.const 0)))

theorem build_primrec : Primrec₂ build := by
  have hn : Primrec (fun x : PackedRegion × List Bool => x.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hc : Primrec (fun x : PackedRegion × List Bool => x.1.2.getD 0 (0, 0)) :=
    (Primrec.list_getD (0, 0)).comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)
  have hw (vertical : Bool) : Primrec (fun x : PackedRegion × List Bool =>
      (bif vertical then (x.1.2.getD 0 (0, 0)).2.2 else (x.1.2.getD 0 (0, 0)).1.2) %
        x.1.1.length) := by
    cases vertical
    · exact Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.fst.comp hc)) hn
    · exact Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp hc)) hn
  have hl (vertical : Bool) : Primrec (fun x : PackedRegion × List Bool =>
      (bif vertical then (x.1.2.getD 0 (0, 0)).2.1 else (x.1.2.getD 0 (0, 0)).1.1) %
        x.1.1.length) := by
    cases vertical
    · exact Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.fst.comp hc)) hn
    · exact Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.snd.comp hc)) hn
  refine (Primrec.cond
    ((Primrec.nat_lt.comp (Primrec.const 0)
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).decide)
    (Primrec.option_some.comp (Primrec.pair
      (differenceCoeff_primrec.comp hn (maximumPair_comp hn Primrec.snd (Primrec.const false)))
      (Primrec.pair
        (differenceCoeff_primrec.comp hn (maximumPair_comp hn Primrec.snd (Primrec.const true)))
        (Primrec.pair (differenceCoeff_primrec.comp hn ((hw false).pair (hl false)))
          (differenceCoeff_primrec.comp hn ((hw true).pair (hl true)))))))
    (Primrec.const none)).of_eq ?_
  intro x
  by_cases h : 0 < x.1.2.length <;> simp [build, h]

end Tiling.AxisParallel.Decidability.RectangleInput.LocalBound
