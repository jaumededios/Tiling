import Tiling.AxisParallel.Decidability.RectangleInput.Comparisons

/-!
# Effective subdivision of a finite rectangle presentation

Cells are represented by four labels in the corner list. Coincident coordinate
levels use their least label, and consecutive levels are recognized with bounded
tests. An accepted cell lies in at least one input rectangle. Overlap, repeated
rectangles, reversed endpoints and degenerate rectangles need no special case.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

abbrev TableInput := ℕ × List Bool
abbrev Cell := (ℕ × ℕ) × (ℕ × ℕ)

def allBelow (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

def anyBelow (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).any p

def equalLevel (n : ℕ) (history : List Bool) (vertical : Bool) (i j : ℕ) : Bool :=
  compare n history vertical i j && compare n history vertical j i

def strictLevel (n : ℕ) (history : List Bool) (vertical : Bool) (i j : ℕ) : Bool :=
  !compare n history vertical j i

def canonicalLevel (n : ℕ) (history : List Bool) (vertical : Bool) (i : ℕ) : Bool :=
  allBelow i fun j => !equalLevel n history vertical i j

def adjacentLevels (n : ℕ) (history : List Bool) (vertical : Bool) (i j : ℕ) : Bool :=
  canonicalLevel n history vertical i && canonicalLevel n history vertical j &&
    strictLevel n history vertical i j &&
    allBelow n (fun k => !(strictLevel n history vertical i k &&
      strictLevel n history vertical k j))

def rectangleCovers (r : ℕ) (history : List Bool) (c : Cell) (k : ℕ) : Bool :=
  compare (2 * r) history false (2 * k) c.1.1 &&
    compare (2 * r) history false c.1.2 (2 * k + 1) &&
    compare (2 * r) history true (2 * k) c.2.1 &&
    compare (2 * r) history true c.2.2 (2 * k + 1)

def occupied (r : ℕ) (history : List Bool) (c : Cell) : Bool :=
  anyBelow r (rectangleCovers r history c)

def accepted (input : TableInput) (c : Cell) : Bool :=
  adjacentLevels (2 * input.1) input.2 false c.1.1 c.1.2 &&
    adjacentLevels (2 * input.1) input.2 true c.2.1 c.2.2 &&
    occupied input.1 input.2 c

def pairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

def candidates (n : ℕ) : List Cell :=
  (pairs n).flatMap fun p => (pairs n).map fun q => (p, q)

/-- The finite disjoint-cell presentation computed solely from comparison answers. -/
def cells (input : TableInput) : List Cell :=
  (candidates (2 * input.1)).filter (accepted input)

theorem allBelow_eq_true {n : ℕ} {p : ℕ → Bool} :
    allBelow n p = true ↔ ∀ i < n, p i = true := by
  simp [allBelow, List.all_eq_true]

theorem anyBelow_eq_true {n : ℕ} {p : ℕ → Bool} :
    anyBelow n p = true ↔ ∃ i < n, p i = true := by
  simp [anyBelow, List.any_eq_true]

theorem mem_pairs {n : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by
  rcases p with ⟨a, b⟩
  simp [pairs]

theorem mem_candidates {n : ℕ} {c : Cell} :
    c ∈ candidates n ↔
      c.1.1 < n ∧ c.1.2 < n ∧ c.2.1 < n ∧ c.2.2 < n := by
  rcases c with ⟨⟨a, b⟩, ⟨d, e⟩⟩
  simp [candidates, mem_pairs, and_assoc]

theorem mem_cells {input : TableInput} {c : Cell} :
    c ∈ cells input ↔
      (c.1.1 < 2 * input.1 ∧ c.1.2 < 2 * input.1 ∧
        c.2.1 < 2 * input.1 ∧ c.2.2 < 2 * input.1) ∧ accepted input c = true := by
  simp [cells, mem_candidates]

theorem pairs_nodup (n : ℕ) : (pairs n).Nodup :=
  List.nodup_range.product List.nodup_range

theorem candidates_nodup (n : ℕ) : (candidates n).Nodup :=
  (pairs_nodup n).product (pairs_nodup n)

theorem cells_nodup (input : TableInput) : (cells input).Nodup :=
  (candidates_nodup (2 * input.1)).filter (accepted input)

theorem compare_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v : α → Bool} {i j : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v)
    (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => compare (n x) (h x) (v x) (i x) (j x)) :=
  compare_primrec.comp ((hn.pair hh).pair (hv.pair (hi.pair hj)))

theorem allBelow_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {p : α → ℕ → Bool} (hn : Primrec n) (hp : Primrec₂ p) :
    Primrec (fun x => allBelow (n x) (p x)) := by
  refine (Primrec.list_foldr (Primrec.list_range.comp hn) (Primrec.const true)
    ((Primrec.dom_bool₂ Bool.and).comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro x
  simp only [allBelow]
  induction List.range (n x) with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem anyBelow_primrec {α : Type*} [Primcodable α]
    {n : α → ℕ} {p : α → ℕ → Bool} (hn : Primrec n) (hp : Primrec₂ p) :
    Primrec (fun x => anyBelow (n x) (p x)) := by
  refine (Primrec.list_foldr (Primrec.list_range.comp hn) (Primrec.const false)
    ((Primrec.dom_bool₂ Bool.or).comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro x
  simp only [anyBelow]
  induction List.range (n x) with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem listAny_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {p : α → β → Bool} (hxs : Primrec xs) (hp : Primrec₂ p) :
    Primrec (fun x => (xs x).any (p x)) := by
  refine (Primrec.list_foldr hxs (Primrec.const false)
    ((Primrec.dom_bool₂ Bool.or).comp
      (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro x
  induction xs x with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem listFilter_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {p : α → β → Bool} (hxs : Primrec xs) (hp : Primrec₂ p) :
    Primrec (fun x => (xs x).filter (p x)) := by
  refine (Primrec.list_foldr hxs (Primrec.const [])
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro x
  induction xs x with
  | nil => rfl
  | cons a as ih => simp [List.filter_cons, ih]

theorem equalLevel_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v : α → Bool} {i j : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v)
    (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => equalLevel (n x) (h x) (v x) (i x) (j x)) :=
  (Primrec.dom_bool₂ Bool.and).comp
    (compare_comp hn hh hv hi hj) (compare_comp hn hh hv hj hi)

theorem strictLevel_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v : α → Bool} {i j : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v)
    (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => strictLevel (n x) (h x) (v x) (i x) (j x)) :=
  (Primrec.dom_bool Bool.not).comp (compare_comp hn hh hv hj hi)

theorem canonicalLevel_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v : α → Bool} {i : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v) (hi : Primrec i) :
    Primrec (fun x => canonicalLevel (n x) (h x) (v x) (i x)) :=
  allBelow_primrec hi ((Primrec.dom_bool Bool.not).comp
    (equalLevel_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst)
      (hv.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd))

theorem adjacentLevels_comp {α : Type*} [Primcodable α]
    {n : α → ℕ} {h : α → List Bool} {v : α → Bool} {i j : α → ℕ}
    (hn : Primrec n) (hh : Primrec h) (hv : Primrec v)
    (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => adjacentLevels (n x) (h x) (v x) (i x) (j x)) := by
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        (canonicalLevel_comp hn hh hv hi) (canonicalLevel_comp hn hh hv hj))
      (strictLevel_comp hn hh hv hi hj))
    (allBelow_primrec hn ((Primrec.dom_bool Bool.not).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        (strictLevel_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst)
          (hv.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd)
        (strictLevel_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst)
          (hv.comp Primrec.fst) Primrec.snd (hj.comp Primrec.fst)))))

private theorem rectangleCovers_primrec :
    Primrec (fun x : TableInput × Cell × ℕ =>
      rectangleCovers x.1.1 x.1.2 x.2.1 x.2.2) := by
  have hn : Primrec (fun x : TableInput × Cell × ℕ => 2 * x.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  have hh : Primrec (fun x : TableInput × Cell × ℕ => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun x : TableInput × Cell × ℕ => 2 * x.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun x : TableInput × Cell × ℕ => 2 * x.2.2 + 1) :=
    Primrec.nat_add.comp ha (Primrec.const 1)
  have hc : Primrec (fun x : TableInput × Cell × ℕ => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        (compare_comp hn hh (Primrec.const false) ha
          (Primrec.fst.comp (Primrec.fst.comp hc)))
        (compare_comp hn hh (Primrec.const false)
          (Primrec.snd.comp (Primrec.fst.comp hc)) hb))
      (compare_comp hn hh (Primrec.const true) ha
        (Primrec.fst.comp (Primrec.snd.comp hc))))
    (compare_comp hn hh (Primrec.const true)
      (Primrec.snd.comp (Primrec.snd.comp hc)) hb)

theorem accepted_primrec : Primrec₂ accepted := by
  have hn : Primrec (fun x : TableInput × Cell => 2 * x.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  have hh : Primrec (fun x : TableInput × Cell => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hocc : Primrec (fun x : TableInput × Cell => occupied x.1.1 x.1.2 x.2) :=
    anyBelow_primrec (Primrec.fst.comp Primrec.fst)
      (rectangleCovers_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      (adjacentLevels_comp hn hh (Primrec.const false)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (adjacentLevels_comp hn hh (Primrec.const true)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) hocc

theorem pairs_primrec : Primrec pairs :=
  Primrec.list_flatMap Primrec.list_range
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem candidates_primrec : Primrec candidates :=
  Primrec.list_flatMap pairs_primrec
    (Primrec.list_map (pairs_primrec.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))

theorem cells_primrec : Primrec cells := by
  refine (Primrec.list_foldr
    (candidates_primrec.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    (Primrec.const [])
    (Primrec.cond (accepted_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro input
  change (candidates (2 * input.1)).foldr
    (fun c cs => bif accepted input c then c :: cs else cs) [] =
    (candidates (2 * input.1)).filter (accepted input)
  induction candidates (2 * input.1) with
  | nil => rfl
  | cons c cs ih => simp [List.filter_cons, ih]

end Tiling.AxisParallel.Decidability.RectangleInput
