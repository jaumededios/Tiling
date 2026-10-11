import Tiling.AxisParallel.Decidability.Oracle.Run

/-! A uniform conversion from sequential query programs to numerical oracle prefixes.
Unavailable queries are detected by comparing two sentinel executions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.NumericalPrefix

def guarded (program : OracleCode) (code : ℕ → Query → ℕ)
    (input : ℕ × List Bool) (fallback : Bool) (history : List Bool) : Bool ⊕ Query :=
  match program input.1 history with
  | .inl b => .inl b
  | .inr q => if code input.1 q < input.2.length then .inr q else .inl fallback

def answer (code : ℕ → Query → ℕ) (input : ℕ × List Bool) (q : Query) : Bool :=
  input.2.getD (code input.1 q) false

def execute (program : OracleCode) (code : ℕ → Query → ℕ)
    (input : ℕ × List Bool) (fallback : Bool) : Option Bool :=
  run (guarded program code input fallback) (answer code input) input.2.length []

def decide (program : OracleCode) (code : ℕ → Query → ℕ)
    (input : ℕ × List Bool) : Option Bool :=
  if execute program code input false = execute program code input true then
    execute program code input false else none

theorem guarded_computable {program : OracleCode} {code : ℕ → Query → ℕ}
    (hp : Computable₂ program) (hc : Computable₂ code) (fallback : Bool) :
    Computable₂ (fun input history => guarded program code input fallback history) := by
  have hq : Computable₂ (fun x : (ℕ × List Bool) × List Bool => fun q : Query =>
      if code x.1.1 q < x.1.2.length then Sum.inr q else Sum.inl fallback) := by
    refine (Computable.cond
      ((Primrec.nat_lt.decide.to_comp.comp
        (hc.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)) Computable.snd)
        (Computable.list_length.comp
          (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
      (Computable.sumInr.comp Computable.snd) (Computable.const (.inl fallback))).of_eq ?_
    intro x
    simp only [Bool.cond_decide]
  refine (Computable.sumCasesOn
    (hp.comp (Computable.fst.comp Computable.fst) Computable.snd)
    (Computable.sumInl.comp Computable.snd).to₂ hq).of_eq ?_
  intro x
  unfold guarded
  dsimp only
  cases program x.1.1 x.2 <;> rfl

theorem answer_computable {code : ℕ → Query → ℕ} (hc : Computable₂ code) :
    Computable₂ (answer code) :=
  (Primrec.list_getD false).to_comp.comp (Computable.snd.comp Computable.fst)
    (hc.comp (Computable.fst.comp Computable.fst) Computable.snd)

theorem execute_computable {program : OracleCode} {code : ℕ → Query → ℕ}
    (hp : Computable₂ program) (hc : Computable₂ code) (fallback : Bool) :
    Computable (fun input => execute program code input fallback) :=
  (OracleRun.run_from_empty_computable (guarded_computable hp hc fallback)
    (answer_computable hc)).comp Computable.id
      (Computable.list_length.comp Computable.snd)

theorem decide_computable {program : OracleCode} {code : ℕ → Query → ℕ}
    (hp : Computable₂ program) (hc : Computable₂ code) : Computable (decide program code) :=
by
  refine (Computable.cond ((Primrec.eq.decide.to_comp).comp
    (execute_computable hp hc false) (execute_computable hp hc true))
    (execute_computable hp hc false) (Computable.const none)).of_eq ?_
  intro x
  simp only [Bool.cond_decide, decide]

/-- Agreeing sentinel simulations have not used an unavailable oracle answer. -/
theorem guarded_sound (program : OracleCode) (code : ℕ → Query → ℕ)
    (input : ℕ × List Bool) (oracle : ℕ → Bool)
    (hprefix : ∀ j, j < input.2.length → input.2.getD j false = oracle j)
    (fuel : ℕ) : ∀ history b,
    run (guarded program code input false) (answer code input) fuel history = some b →
    run (guarded program code input true) (answer code input) fuel history = some b →
    run (program input.1) (fun q => oracle (code input.1 q)) fuel history = some b := by
  induction fuel with
  | zero => intro history b h; simp [run] at h
  | succ fuel ih =>
    intro history b hfalse htrue
    cases hstep : program input.1 history with
    | inl a => simpa [run, guarded, hstep] using hfalse
    | inr q =>
      by_cases hq : code input.1 q < input.2.length
      · have ha : answer code input q = oracle (code input.1 q) := hprefix _ hq
        simp only [run, guarded, hstep, if_pos hq] at hfalse htrue
        simp only [run, hstep]
        rw [ha] at hfalse htrue
        exact ih _ _ hfalse htrue
      · simp [run, guarded, hstep, hq] at hfalse htrue
        simp_all

theorem decide_sound (program : OracleCode) (code : ℕ → Query → ℕ)
    (n : ℕ) (oracle : ℕ → Bool) (k : ℕ) (b : Bool)
    (h : decide program code (n, (List.range k).map oracle) = some b) :
    run (program n) (fun q => oracle (code n q)) k [] = some b := by
  unfold decide at h
  split at h
  next heq =>
    apply guarded_sound program code (n, (List.range k).map oracle) oracle
      (by intro j hj; simp only [List.length_map, List.length_range] at hj
          simp [List.getD_eq_getElem?_getD, hj])
      k [] b
    · simpa [execute] using h
    · have hh : execute program code (n, (List.range k).map oracle) true = some b :=
        heq.symm.trans h
      simpa [execute] using hh
  next => simp at h

theorem run_mono (step : List Bool → Bool ⊕ Query) (ans : Query → Bool)
    {fuel larger : ℕ} (hle : fuel ≤ larger) {history : List Bool} {b : Bool}
    (h : run step ans fuel history = some b) : run step ans larger history = some b := by
  induction fuel generalizing larger history with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases larger with
    | zero => omega
    | succ larger =>
      cases hs : step history with
      | inl a => simpa [run, hs] using h
      | inr q =>
        simp only [run, hs] at h ⊢
        exact ih (by omega) h

/-- A terminating execution uses finitely many numbered oracle entries. -/
theorem guarded_complete (program : OracleCode) (code : ℕ → Query → ℕ)
    (n : ℕ) (oracle : ℕ → Bool) (fuel : ℕ) : ∀ history b,
    run (program n) (fun q => oracle (code n q)) fuel history = some b →
    ∃ bound, ∀ k, bound ≤ k → ∀ fallback,
      run (guarded program code (n, (List.range k).map oracle) fallback)
        (answer code (n, (List.range k).map oracle)) fuel history = some b := by
  induction fuel with
  | zero => intro history b h; simp [run] at h
  | succ fuel ih =>
    intro history b h
    cases hs : program n history with
    | inl a => exact ⟨0, fun k _ fallback => by simpa [run, guarded, hs] using h⟩
    | inr q =>
      simp only [run, hs] at h
      obtain ⟨bound, hb⟩ := ih _ _ h
      refine ⟨max bound (code n q + 1), ?_⟩
      intro k hk fallback
      have hq : code n q < k := by omega
      have ha : answer code (n, (List.range k).map oracle) q = oracle (code n q) := by
        simp [answer, List.getD_eq_getElem?_getD, hq]
      simp only [run, guarded, hs, List.length_map, List.length_range, if_pos hq]
      rw [ha]
      exact hb k (by omega) fallback

theorem decide_complete (program : OracleCode) (code : ℕ → Query → ℕ)
    (n : ℕ) (oracle : ℕ → Bool) {fuel : ℕ} {b : Bool}
    (h : run (program n) (fun q => oracle (code n q)) fuel [] = some b) :
    ∃ bound, ∀ k, bound ≤ k →
      decide program code (n, (List.range k).map oracle) = some b := by
  obtain ⟨bound, hb⟩ := guarded_complete program code n oracle fuel [] b h
  refine ⟨max bound fuel, ?_⟩
  intro k hk
  have hf (fallback : Bool) :
      execute program code (n, (List.range k).map oracle) fallback = some b := by
    unfold execute
    simp only [List.length_map, List.length_range]
    exact run_mono _ _ (by omega) (hb k (by omega) fallback)
  simp only [decide, hf, ↓reduceIte]

/-- Searching the prefixes is equivalent to any bounded execution returning that answer. -/
theorem returns_iff (program : OracleCode) (code : ℕ → Query → ℕ)
    (n : ℕ) (oracle : ℕ → Bool) (b : Bool) :
    b ∈ Nat.rfindOpt (fun k => decide program code (n, (List.range k).map oracle)) ↔
      ∃ fuel, run (program n) (fun q => oracle (code n q)) fuel [] = some b := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec h
    exact ⟨k, decide_sound program code n oracle k b (by simpa using hk)⟩
  · rintro ⟨fuel, hf⟩
    obtain ⟨bound, hb⟩ := decide_complete program code n oracle hf
    have hdom : (Nat.rfindOpt (fun k => decide program code (n, (List.range k).map oracle))).Dom :=
      Nat.rfindOpt_dom.mpr ⟨bound, b, by simpa using hb bound le_rfl⟩
    obtain ⟨k, hk⟩ := Nat.rfindOpt_spec ⟨hdom, rfl⟩
    have hr := decide_sound program code n oracle k _ (by simpa using hk)
    have hf' := run_mono _ _ (Nat.le_max_left fuel k) hf
    have hr' := run_mono _ _ (Nat.le_max_right fuel k) hr
    have heq := hf'.symm.trans hr'
    have heq' := Option.some.inj heq
    exact ⟨hdom, heq'.symm⟩

end Tiling.AxisParallel.Decidability.NumericalPrefix
