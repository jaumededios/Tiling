import Tiling.AxisParallel.Decidability.Uniform
import Tiling.AxisParallel.Decidability.Oracle.Prefix
import Tiling.AxisParallel.Decidability.RectangleInput.Validity

set_option autoImplicit false
set_option warningAsError true

open Set Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.AllInput

def query (axis : Fin 2) (k : ℕ) : Query := (axis, [2*k+1], [2*k])

def schedule (n : ℕ) : List Query :=
  (List.range n).map (query 0) ++ (List.range n).map (query 1)

def proper (n : ℕ) (answers : List Bool) : Bool :=
  (List.range n).foldr (fun k found =>
    (!(answers.getD k false) && !(answers.getD (n+k) false)) || found) false

def body (n : ℕ) (answers history : List Bool) : Bool ⊕ Query :=
  if proper n answers then uniformDecisionProgram n history else .inl false

def program : OracleCode := OraclePrefix.prefixProgram schedule body

private theorem query_primrec (axis : Fin 2) : Primrec (query axis) := by
  have hleft : Primrec (fun k : ℕ => [2*k]) :=
    Primrec.list_cons.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const [])
  have hright : Primrec (fun k : ℕ => [2*k+1]) :=
    Primrec.list_cons.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 1)) (Primrec.const [])
  exact (Primrec.const axis).pair (hright.pair hleft)

theorem schedule_computable : Computable schedule :=
  (Primrec.list_append.comp
    (Primrec.list_map Primrec.list_range ((query_primrec 0).comp Primrec.snd).to₂)
    (Primrec.list_map Primrec.list_range ((query_primrec 1).comp Primrec.snd).to₂)).to_comp

theorem proper_computable : Computable₂ proper := by
  have hk : Computable (fun x : (ℕ × List Bool) × (ℕ × Bool) => x.2.1) :=
    Computable.fst.comp Computable.snd
  have hn : Computable (fun x : (ℕ × List Bool) × (ℕ × Bool) => x.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun x : (ℕ × List Bool) × (ℕ × Bool) => x.1.2) :=
    Computable.snd.comp Computable.fst
  have ha := (Primrec.list_getD false).to_comp.comp hp hk
  have hb := (Primrec.list_getD false).to_comp.comp hp (Primrec.nat_add.to_comp.comp hn hk)
  exact Tiling.Computability.List.computable_list_foldr_param
    (Primrec.list_range.to_comp.comp Computable.fst) (Computable.const false)
    ((Primrec.dom_bool₂ Bool.or).to_comp.comp
      ((Primrec.dom_bool₂ Bool.and).to_comp.comp
        ((Primrec.dom_bool Bool.not).to_comp.comp ha)
        ((Primrec.dom_bool Bool.not).to_comp.comp hb))
      (Computable.snd.comp Computable.snd)).to₂

theorem program_computable : Computable₂ program := by
  apply OraclePrefix.prefixProgram_computable schedule_computable
  refine (Computable.cond
    (proper_computable.comp Computable.fst (Computable.fst.comp Computable.snd))
    (uniformDecisionProgram_computable.comp Computable.fst (Computable.snd.comp Computable.snd))
    (Computable.const (.inl false))).of_eq ?_
  intro x
  simp only [Bool.cond_eq_ite, body]

private theorem fold_or (p : ℕ → Bool) (xs : List ℕ) :
    xs.foldr (fun k found => p k || found) false = true ↔ ∃ k ∈ xs, p k = true := by
  induction xs with
  | nil => simp
  | cons k xs ih => simp [ih]

theorem proper_correct {R : List (Plane × Plane)} {answer : Query → Bool}
    (ha : CorrectOracle (cornerList R) answer) :
    proper R.length ((schedule R.length).map answer) = true ↔
      (interior (⋃ r ∈ R, rectangle r.1 r.2)).Nonempty := by
  rw [proper, fold_or, RectangleInput.Validity.interior_rectangles_nonempty]
  have hentry (k : ℕ) (hk : k < R.length) :
      (!( ((schedule R.length).map answer).getD k false) &&
       !( ((schedule R.length).map answer).getD (R.length+k) false)) =
      RectangleInput.Validity.properRectangle answer k := by
    simp [schedule, List.map_append, List.map_map, List.getD_eq_getElem?_getD,
      List.getElem?_append, hk,
      query, RectangleInput.Validity.properRectangle]
  simp only [List.mem_range]
  constructor
  · rintro ⟨k, hk, hp⟩
    rw [hentry k hk] at hp
    refine ⟨R.getD k (0,0), ?_, (RectangleInput.Validity.properRectangle_correct ha hk).mp hp⟩
    rw [List.getD_eq_getElem R (0,0) hk]
    exact List.getElem_mem hk
  · rintro ⟨r, hr, hp⟩
    obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hr
    refine ⟨k, hk, ?_⟩
    rw [hentry k hk]
    apply (RectangleInput.Validity.properRectangle_correct ha hk).mpr
    simpa only [List.getD_eq_getElem R (0,0) hk, he] using hp

private theorem not_tiles_empty (T : Set Plane) : ¬ Tiles ∅ T := by
  intro h
  have he : (univ : Set Plane) =ᵐ[MeasureTheory.volume] (∅ : Set Plane) := by
    simpa only [CoversExactly, Set.vadd_empty] using h.2.2
  have hz : MeasureTheory.volume (univ : Set Plane) = 0 := by
    simpa using MeasureTheory.measure_congr he
  simp at hz

theorem program_correct {R : List (Plane × Plane)} {answer : Query → Bool}
    (ha : CorrectOracle (cornerList R) answer) :
    (∃ fuel b, run (program R.length) answer fuel [] = some b) ∧
      ∀ fuel b, run (program R.length) answer fuel [] = some b →
        (b = true ↔ ∃ T, Tiles (interior (⋃ r ∈ R, rectangle r.1 r.2)) T) := by
  let answers := (schedule R.length).map answer
  have hc (fuel : ℕ) : run (program R.length) answer ((schedule R.length).length + fuel) [] =
      run (body R.length answers) answer fuel [] :=
    OraclePrefix.run_from_empty_after_schedule schedule body R.length answer fuel
  by_cases hp : proper R.length answers = true
  · have hbody : body R.length answers = uniformDecisionProgram R.length := by
      funext history
      simp [body, hp]
    have hbody' : body R.length ((schedule R.length).map answer) =
        uniformDecisionProgram R.length := hbody
    have hR : RectanglePresentation R (interior (⋃ r ∈ R, rectangle r.1 r.2)) :=
      ⟨(proper_correct ha).mp hp, rfl⟩
    obtain ⟨⟨fuel, b, hf⟩, hs⟩ := uniformDecisionProgram_correct hR ha
    constructor
    · exact ⟨(schedule R.length).length + fuel, b, by rw [hc, hbody]; exact hf⟩
    · intro fuel b hf
      obtain ⟨f, hf'⟩ :=
        OraclePrefix.run_answer_after_schedule schedule body R.length answer fuel b hf
      exact hs f b (by rw [hbody'] at hf'; exact hf')
  · have hbody : body R.length answers = (fun _ => .inl false) := by
      funext history
      simp [body, hp]
    have hbody' : body R.length ((schedule R.length).map answer) = (fun _ => .inl false) := hbody
    have he : interior (⋃ r ∈ R, rectangle r.1 r.2) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (mt (proper_correct ha).mpr hp)
    constructor
    · exact ⟨(schedule R.length).length + 1, false, by rw [hc, hbody]; rfl⟩
    · intro fuel b hf
      obtain ⟨f, hf'⟩ :=
        OraclePrefix.run_answer_after_schedule schedule body R.length answer fuel b hf
      cases f with
      | zero => simp [run] at hf'
      | succ f =>
        have hb : b = false := by rw [hbody'] at hf'; simpa [run] using hf'.symm
        simp [hb, he, not_tiles_empty]

end Tiling.AxisParallel.Decidability.AllInput
