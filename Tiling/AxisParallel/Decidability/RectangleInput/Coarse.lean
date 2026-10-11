import Tiling.AxisParallel.Decidability.RectangleInput.Vertices

/-!
# Subdivision on intrinsic coordinate levels

The fine subdivision can contain internal rectangle endpoints that are absent
from the intrinsic vertex set. Runtime region input uses only intrinsic levels.
This second finite pass retains levels used by a vertex and merges the fine
subdivision. A coarse cell is occupied when it contains an occupied fine cell.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

def usedLevel (input : TableInput) (vertical : Bool) (i : ℕ) : Bool :=
  (vertexLabels input).any fun p => (bif vertical then p.2 else p.1) == i

def coarseAdjacent (input : TableInput) (vertical : Bool) (i j : ℕ) : Bool :=
  usedLevel input vertical i && usedLevel input vertical j &&
    strictLevel (2 * input.1) input.2 vertical i j &&
    allBelow (2 * input.1) (fun k => !(usedLevel input vertical k &&
      strictLevel (2 * input.1) input.2 vertical i k &&
      strictLevel (2 * input.1) input.2 vertical k j))

def cellContained (input : TableInput) (outer inner : Cell) : Bool :=
  compare (2 * input.1) input.2 false outer.1.1 inner.1.1 &&
    compare (2 * input.1) input.2 false inner.1.2 outer.1.2 &&
    compare (2 * input.1) input.2 true outer.2.1 inner.2.1 &&
    compare (2 * input.1) input.2 true inner.2.2 outer.2.2

def coarseAccepted (input : TableInput) (c : Cell) : Bool :=
  coarseAdjacent input false c.1.1 c.1.2 && coarseAdjacent input true c.2.1 c.2.2 &&
    (cells input).any (cellContained input c)

def coarseCells (input : TableInput) : List Cell :=
  (candidates (2 * input.1)).filter (coarseAccepted input)

theorem usedLevel_eq_true {input : TableInput} {vertical : Bool} {i : ℕ} :
    usedLevel input vertical i = true ↔
      ∃ p ∈ vertexLabels input, (bif vertical then p.2 else p.1) = i := by
  simp [usedLevel, List.any_eq_true]

theorem coarseCells_nodup (input : TableInput) : (coarseCells input).Nodup :=
  (candidates_nodup (2 * input.1)).filter (coarseAccepted input)

theorem mem_coarseCells {input : TableInput} {c : Cell} :
    c ∈ coarseCells input ↔
      (c.1.1 < 2 * input.1 ∧ c.1.2 < 2 * input.1 ∧
        c.2.1 < 2 * input.1 ∧ c.2.2 < 2 * input.1) ∧ coarseAccepted input c = true := by
  simp [coarseCells, mem_candidates]

theorem usedLevel_comp {α : Type*} [Primcodable α]
    {input : α → TableInput} {v : α → Bool} {i : α → ℕ}
    (hin : Primrec input) (hv : Primrec v) (hi : Primrec i) :
    Primrec (fun x => usedLevel (input x) (v x) (i x)) :=
  listAny_comp (vertexLabels_primrec.comp hin)
    (Primrec.beq.comp
      (Primrec.cond (hv.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)) (hi.comp Primrec.fst))

theorem coarseAdjacent_comp {α : Type*} [Primcodable α]
    {input : α → TableInput} {v : α → Bool} {i j : α → ℕ}
    (hin : Primrec input) (hv : Primrec v) (hi : Primrec i) (hj : Primrec j) :
    Primrec (fun x => coarseAdjacent (input x) (v x) (i x) (j x)) := by
  have hn : Primrec (fun x => 2 * (input x).1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp hin)
  have hh : Primrec (fun x => (input x).2) := Primrec.snd.comp hin
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        (usedLevel_comp hin hv hi) (usedLevel_comp hin hv hj))
      (strictLevel_comp hn hh hv hi hj))
    (allBelow_primrec hn ((Primrec.dom_bool Bool.not).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        ((Primrec.dom_bool₂ Bool.and).comp
          (usedLevel_comp (hin.comp Primrec.fst) (hv.comp Primrec.fst) Primrec.snd)
          (strictLevel_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst)
            (hv.comp Primrec.fst) (hi.comp Primrec.fst) Primrec.snd))
        (strictLevel_comp (hn.comp Primrec.fst) (hh.comp Primrec.fst)
          (hv.comp Primrec.fst) Primrec.snd (hj.comp Primrec.fst)))))

theorem cellContained_primrec :
    Primrec (fun x : TableInput × Cell × Cell => cellContained x.1 x.2.1 x.2.2) := by
  have hn : Primrec (fun x : TableInput × Cell × Cell => 2 * x.1.1) :=
    Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)
  have hh : Primrec (fun x : TableInput × Cell × Cell => x.1.2) :=
    Primrec.snd.comp Primrec.fst
  have ho : Primrec (fun x : TableInput × Cell × Cell => x.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun x : TableInput × Cell × Cell => x.2.2) :=
    Primrec.snd.comp Primrec.snd
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      ((Primrec.dom_bool₂ Bool.and).comp
        (compare_comp hn hh (Primrec.const false)
          (Primrec.fst.comp (Primrec.fst.comp ho))
          (Primrec.fst.comp (Primrec.fst.comp hi)))
        (compare_comp hn hh (Primrec.const false)
          (Primrec.snd.comp (Primrec.fst.comp hi))
          (Primrec.snd.comp (Primrec.fst.comp ho))))
      (compare_comp hn hh (Primrec.const true)
        (Primrec.fst.comp (Primrec.snd.comp ho))
        (Primrec.fst.comp (Primrec.snd.comp hi))))
    (compare_comp hn hh (Primrec.const true)
      (Primrec.snd.comp (Primrec.snd.comp hi))
      (Primrec.snd.comp (Primrec.snd.comp ho)))

theorem coarseAccepted_primrec : Primrec₂ coarseAccepted :=
  (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp
      (coarseAdjacent_comp Primrec.fst (Primrec.const false)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (coarseAdjacent_comp Primrec.fst (Primrec.const true)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (listAny_comp (cells_primrec.comp Primrec.fst)
      (cellContained_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))))

theorem coarseCells_primrec : Primrec coarseCells :=
  listFilter_comp
    (candidates_primrec.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    coarseAccepted_primrec

end Tiling.AxisParallel.Decidability.RectangleInput
