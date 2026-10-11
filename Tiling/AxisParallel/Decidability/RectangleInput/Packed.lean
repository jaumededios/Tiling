import Tiling.AxisParallel.Decidability.RectangleInput.Coarse
import Tiling.AxisParallel.Terminal.ExecutableInput

/-!
# Packed runtime region input

The frontend returns finite lists of point labels and cell selectors. Each
selector chooses the first intrinsic vertex on a cell's supporting coordinate
line. The dependent production `RegionCode` is recovered from these lists once
the vertex list is nonempty; malformed selectors have a fixed modular default.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

abbrev PackedRegion := List PointLabel × List Cell

def firstVertex (input : TableInput) (vertical : Bool) (i : ℕ) : ℕ :=
  (vertexLabels input).findIdx fun p => (bif vertical then p.2 else p.1) == i

def encodedCell (input : TableInput) (c : Cell) : Cell :=
  ((firstVertex input false c.1.1, firstVertex input false c.1.2),
    (firstVertex input true c.2.1, firstVertex input true c.2.2))

def packedRegion (input : TableInput) : PackedRegion :=
  (vertexLabels input, (coarseCells input).map (encodedCell input))

theorem firstVertex_spec {input : TableInput} {vertical : Bool} {i : ℕ}
    (hi : usedLevel input vertical i = true) :
    firstVertex input vertical i < (vertexLabels input).length ∧
      (bif vertical then
        ((vertexLabels input).getD (firstVertex input vertical i) (0, 0)).2
      else ((vertexLabels input).getD (firstVertex input vertical i) (0, 0)).1) = i := by
  have hex : ∃ p ∈ vertexLabels input, (bif vertical then p.2 else p.1) == i := by
    simpa only [beq_iff_eq] using usedLevel_eq_true.mp hi
  have hlt : firstVertex input vertical i < (vertexLabels input).length :=
    List.findIdx_lt_length_of_exists hex
  refine ⟨hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

theorem listFindIdx_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {p : α → β → Bool} (hxs : Primrec xs) (hp : Primrec₂ p) :
    Primrec (fun x => (xs x).findIdx (p x)) := by
  refine (Primrec.list_foldr hxs (Primrec.const 0)
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.const 0) (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))).to₂).of_eq ?_
  intro x
  induction xs x with
  | nil => rfl
  | cons a as ih => simp [List.findIdx_cons, ih]

theorem firstVertex_comp {α : Type*} [Primcodable α]
    {input : α → TableInput} {v : α → Bool} {i : α → ℕ}
    (hin : Primrec input) (hv : Primrec v) (hi : Primrec i) :
    Primrec (fun x => firstVertex (input x) (v x) (i x)) :=
  listFindIdx_comp (vertexLabels_primrec.comp hin)
    (Primrec.beq.comp
      (Primrec.cond (hv.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)
        (Primrec.fst.comp Primrec.snd)) (hi.comp Primrec.fst))

theorem encodedCell_primrec : Primrec₂ encodedCell :=
  Primrec.pair
    (Primrec.pair
      (firstVertex_comp Primrec.fst (Primrec.const false)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (firstVertex_comp Primrec.fst (Primrec.const false)
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
    (Primrec.pair
      (firstVertex_comp Primrec.fst (Primrec.const true)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (firstVertex_comp Primrec.fst (Primrec.const true)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem packedRegion_primrec : Primrec packedRegion :=
  vertexLabels_primrec.pair (Primrec.list_map coarseCells_primrec encodedCell_primrec)

/-- Interpret packed selectors in the production finite input type. The modular
fallback affects malformed data only. -/
def regionCode (P : PackedRegion) (hP : 0 < P.1.length) :
    Tiling.AxisParallel.Terminal.Executable.RegionCode where
  vertexCount := P.1.length
  cellCount := P.2.length
  originVertex := ⟨0, hP⟩
  leftVertex e := ⟨(P.2.getD e (0, 0)).1.1 % P.1.length, Nat.mod_lt _ hP⟩
  rightVertex e := ⟨(P.2.getD e (0, 0)).1.2 % P.1.length, Nat.mod_lt _ hP⟩
  bottomVertex e := ⟨(P.2.getD e (0, 0)).2.1 % P.1.length, Nat.mod_lt _ hP⟩
  topVertex e := ⟨(P.2.getD e (0, 0)).2.2 % P.1.length, Nat.mod_lt _ hP⟩

end Tiling.AxisParallel.Decidability.RectangleInput
