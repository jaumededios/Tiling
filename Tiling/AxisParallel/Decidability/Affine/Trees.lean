import Tiling.AxisParallel.Decidability.Affine.Queries
import Tiling.AxisParallel.Decidability.Oracle.Replay
import Mathlib.Data.List.Fold

/-! Finite oracle trees for the concrete packed affine compiler. Each query points
backwards, and a failed clause continues at the already compiled remaining DNF. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.Affine.Trees

abbrev Tree := OracleReplay.Code

open OracleReplay

/-- Append one comparison, reversing branches for a strict atom. -/
def appendAtom (transport : PackedQuery → Query) (bad good : ℕ)
    (a : SortedAtom) (initial : Tree) : Tree :=
  initial ++ [.inr (transport (atomQuery a),
    if a.2.1 then good else bad, if a.2.1 then bad else good)]

/-- The clause returns true on success and continues at `bad` on failure. -/
def clauseInto (transport : PackedQuery → Query) (bad : ℕ)
    (initial : Tree) (clause : Clause) : Tree :=
  clause.foldr (fun a code => appendAtom transport bad (root code) a code)
    (initial ++ [.inl (some true)])

/-- Compile the disjunction from right to left so failed clauses can continue. -/
def dnfInto (transport : PackedQuery → Query) (initial : Tree) (dnf : DNF) : Tree :=
  dnf.foldr (fun clause code => clauseInto transport (root code) code clause)
    (initial ++ [.inl (some false)])

/-- Compile an arbitrary packed DNF to a finite query tree. -/
def treeOfDNF (transport : PackedQuery → Query) (dnf : DNF) : Tree :=
  dnfInto transport [] dnf

/-- Executable finite oracle tree for an arbitrary packed formula code. -/
def treeOfFormula (transport : PackedQuery → Query) (code : Code) : Tree :=
  treeOfDNF transport (compile code)

private theorem node_append (initial ending : Tree) (index : ℕ)
    (h : index < initial.length) : node (initial ++ ending) index = node initial index :=
  List.getD_append initial ending (.inl none) index h

private theorem node_outside (code : Tree) (index : ℕ) (h : code.length ≤ index) :
    node code index = .inl none := List.getD_eq_default code (.inl none) h

private theorem node_at_end (initial : Tree) (n : Node) :
    node (initial ++ [n]) initial.length = n := by
  rw [node, List.getD_append_right _ _ _ _ (by rfl)]
  simp

private theorem wf_append (initial : Tree) (n : Node) (h : WellFormed initial)
    (hn : ∀ q left right, n = .inr (q, left, right) →
      left < initial.length ∧ right < initial.length) : WellFormed (initial ++ [n]) := by
  intro index q left right hnode
  by_cases hi : index < initial.length
  · exact h index q left right (by rwa [node_append _ _ _ hi] at hnode)
  · by_cases he : index = initial.length
    · subst index
      exact hn q left right (by rwa [node_at_end] at hnode)
    · rw [node_outside _ _ (by simp; omega)] at hnode
      contradiction

private theorem evalFuel_append (answer : Query → Bool) (initial ending : Tree)
    (h : WellFormed initial) (fuel index : ℕ) (hi : index < initial.length) :
    evalFuel answer (initial ++ ending) fuel index = evalFuel answer initial fuel index := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
    simp only [evalFuel, node_append _ _ _ hi]
    cases hn : node initial index with
    | inl o => rfl
    | inr q =>
      rcases q with ⟨q, left, right⟩
      have hchildren := h index q left right hn
      cases ha : answer q with
      | false => simp only [ha, cond_false]; exact ih left (by omega)
      | true => simp only [ha, cond_true]; exact ih right (by omega)

private theorem clauseInto_prefix (transport : PackedQuery → Query) (bad : ℕ)
    (initial : Tree) (clause : Clause) : ∃ ending, clauseInto transport bad initial clause =
      initial ++ ending := by
  induction clause with
  | nil => exact ⟨[.inl (some true)], rfl⟩
  | cons a rest ih =>
    obtain ⟨ending, he⟩ := ih
    exact ⟨ending ++ [.inr (transport (atomQuery a),
      if a.2.1 then root (clauseInto transport bad initial rest) else bad,
      if a.2.1 then bad else root (clauseInto transport bad initial rest))],
      by
        change clauseInto transport bad initial rest ++ _ = initial ++ _
        simp only [clauseInto, appendAtom] at he ⊢
        rw [he, List.append_assoc]⟩

private theorem clauseInto_length_pos (transport : PackedQuery → Query) (bad : ℕ)
    (initial : Tree) (clause : Clause) : 0 < (clauseInto transport bad initial clause).length := by
  cases clause <;> simp [clauseInto, appendAtom]

private theorem clauseInto_wf (transport : PackedQuery → Query) (bad : ℕ)
    (initial : Tree) (clause : Clause) (h : WellFormed initial) (hb : bad < initial.length) :
    WellFormed (clauseInto transport bad initial clause) := by
  induction clause with
  | nil => exact wf_append initial _ h (by intros; contradiction)
  | cons a rest ih =>
    apply wf_append _ _ ih
    intro q left right he
    obtain ⟨ending, hprefix⟩ := clauseInto_prefix transport bad initial rest
    have hlength := clauseInto_length_pos transport bad initial rest
    have hbad : bad < (clauseInto transport bad initial rest).length := by
      rw [hprefix]
      simp only [List.length_append]
      omega
    simp only [Sum.inr.injEq, Prod.mk.injEq] at he
    rcases he with ⟨_, hl, hr⟩
    change (if a.2.1 then root (clauseInto transport bad initial rest) else bad) = left at hl
    change (if a.2.1 then bad else root (clauseInto transport bad initial rest)) = right at hr
    have hgood : root (clauseInto transport bad initial rest) <
        (clauseInto transport bad initial rest).length := by
      unfold root
      omega
    cases ha : a.2.1 <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at hl hr <;>
      constructor <;> omega

private theorem evalFuel_unique (answer : Query → Bool) (code : Tree)
    (fuel fuel' index : ℕ) (b b' : Bool)
    (hb : evalFuel answer code fuel index = some b)
    (hb' : evalFuel answer code fuel' index = some b') : b = b' := by
  induction fuel generalizing fuel' index with
  | zero => simp [evalFuel] at hb
  | succ fuel ih =>
    cases fuel' with
    | zero => simp [evalFuel] at hb'
    | succ fuel' =>
      cases hn : node code index with
      | inl o =>
        simp only [evalFuel, hn] at hb hb'
        exact Option.some.inj (hb.symm.trans hb')
      | inr q =>
        exact ih fuel' _ (by simpa only [evalFuel, hn] using hb)
          (by simpa only [evalFuel, hn] using hb')

private theorem appendAtom_eval (transport : PackedQuery → Query) (answer : Query → Bool)
    (initial : Tree) (bad good : ℕ) (a : SortedAtom) (b g : Bool)
    (h : WellFormed initial) (hbad : bad < initial.length) (hgood : good < initial.length)
    (hb : ∃ fuel, evalFuel answer initial fuel bad = some b)
    (hg : ∃ fuel, evalFuel answer initial fuel good = some g) :
    ∃ fuel, evalFuel answer (appendAtom transport bad good a initial) fuel
      (root (appendAtom transport bad good a initial)) =
        some (cond (evalAtom (answer ∘ transport) a) g b) := by
  obtain ⟨fb, hb⟩ := hb
  obtain ⟨fg, hg⟩ := hg
  have hbe : evalFuel answer (appendAtom transport bad good a initial) fb bad = some b := by
    rw [appendAtom, evalFuel_append answer initial _ h fb bad hbad, hb]
  have hge : evalFuel answer (appendAtom transport bad good a initial) fg good = some g := by
    rw [appendAtom, evalFuel_append answer initial _ h fg good hgood, hg]
  have hn : node (appendAtom transport bad good a initial)
      (root (appendAtom transport bad good a initial)) =
      .inr (transport (atomQuery a), if a.2.1 then good else bad,
        if a.2.1 then bad else good) := by
    simpa only [root, appendAtom, List.length_append, List.length_singleton,
      Nat.add_sub_cancel] using node_at_end initial _
  cases ha : a.2.1 <;> cases hq : answer (transport (atomQuery a))
  · refine ⟨fb + 1, ?_⟩
    simpa only [evalFuel, hn, ha, hq, evalAtom, Function.comp_apply, Bool.false_eq_true,
      ↓reduceIte, cond_false] using hbe
  · refine ⟨fg + 1, ?_⟩
    simpa only [evalFuel, hn, ha, hq, evalAtom, Function.comp_apply, Bool.false_eq_true,
      ↓reduceIte, cond_true] using hge
  · refine ⟨fg + 1, ?_⟩
    simpa only [evalFuel, hn, ha, hq, evalAtom, Function.comp_apply,
      ↓reduceIte, Bool.not_false, cond_false, cond_true] using hge
  · refine ⟨fb + 1, ?_⟩
    simpa only [evalFuel, hn, ha, hq, evalAtom, Function.comp_apply,
      ↓reduceIte, Bool.not_true, cond_true, cond_false] using hbe

private theorem clauseInto_eval (transport : PackedQuery → Query) (answer : Query → Bool)
    (initial : Tree) (bad : ℕ) (clause : Clause) (b : Bool)
    (h : WellFormed initial) (hbad : bad < initial.length)
    (hb : ∃ fuel, evalFuel answer initial fuel bad = some b) :
    ∃ fuel, evalFuel answer (clauseInto transport bad initial clause) fuel
      (root (clauseInto transport bad initial clause)) =
        some (clause.all (evalAtom (answer ∘ transport)) || b) := by
  induction clause with
  | nil =>
    refine ⟨1, ?_⟩
    have hn := node_at_end initial (.inl (some true))
    simp only [clauseInto, List.foldr_nil, root, List.length_append,
      List.length_singleton, Nat.add_sub_cancel, evalFuel, List.all_nil,
      Bool.true_or, hn]
  | cons a rest ih =>
    let code := clauseInto transport bad initial rest
    have hw : WellFormed code := clauseInto_wf transport bad initial rest h hbad
    obtain ⟨ending, he⟩ := clauseInto_prefix transport bad initial rest
    have hbad' : bad < code.length := by
      change bad < (clauseInto transport bad initial rest).length
      rw [he]; simp only [List.length_append]; omega
    have hbadEval : ∃ fuel, evalFuel answer code fuel bad = some b := by
      obtain ⟨fuel, hf⟩ := hb
      refine ⟨fuel, ?_⟩
      change evalFuel answer (clauseInto transport bad initial rest) fuel bad = some b
      rw [he, evalFuel_append answer initial ending h fuel bad hbad, hf]
    have hgood : root code < code.length := by
      have hp := clauseInto_length_pos transport bad initial rest
      change code.length - 1 < code.length
      omega
    obtain ⟨fuel, hf⟩ := appendAtom_eval transport answer code bad (root code) a b
      (rest.all (evalAtom (answer ∘ transport)) || b) hw hbad' hgood hbadEval ih
    refine ⟨fuel, ?_⟩
    change evalFuel answer (appendAtom transport bad (root code) a code) fuel
      (root (appendAtom transport bad (root code) a code)) = _
    rw [hf, List.all_cons]
    congr 1
    cases evalAtom (answer ∘ transport) a <;>
      cases rest.all (evalAtom (answer ∘ transport)) <;> cases b <;> rfl

private theorem dnfInto_length_pos (transport : PackedQuery → Query)
    (initial : Tree) (dnf : DNF) : 0 < (dnfInto transport initial dnf).length := by
  cases dnf with
  | nil => simp [dnfInto]
  | cons clause rest => exact clauseInto_length_pos _ _ _ _

private theorem dnfInto_wf (transport : PackedQuery → Query)
    (initial : Tree) (dnf : DNF) (h : WellFormed initial) :
    WellFormed (dnfInto transport initial dnf) := by
  induction dnf with
  | nil => exact wf_append initial _ h (by intros; contradiction)
  | cons clause rest ih =>
    apply clauseInto_wf transport _ _ clause ih
    have hp := dnfInto_length_pos transport initial rest
    change (dnfInto transport initial rest).length - 1 < (dnfInto transport initial rest).length
    omega

private theorem dnfInto_eval (transport : PackedQuery → Query) (answer : Query → Bool)
    (initial : Tree) (dnf : DNF) (h : WellFormed initial) :
    ∃ fuel, evalFuel answer (dnfInto transport initial dnf) fuel
      (root (dnfInto transport initial dnf)) = some (evalDNF (answer ∘ transport) dnf) := by
  induction dnf with
  | nil =>
    refine ⟨1, ?_⟩
    have hn := node_at_end initial (.inl (some false))
    simp only [dnfInto, List.foldr_nil, root, List.length_append,
      List.length_singleton, Nat.add_sub_cancel, evalFuel, evalDNF, List.any_nil, hn]
  | cons clause rest ih =>
    have hw := dnfInto_wf transport initial rest h
    have hroot : root (dnfInto transport initial rest) <
        (dnfInto transport initial rest).length := by
      have hp := dnfInto_length_pos transport initial rest
      simp only [root]
      omega
    simpa only [dnfInto, List.foldr_cons, evalDNF, List.any_cons] using
      clauseInto_eval transport answer (dnfInto transport initial rest)
        (root (dnfInto transport initial rest)) clause (evalDNF (answer ∘ transport) rest)
        hw hroot ih

/-- The generated query tree is well formed for all finite packed inputs. -/
theorem treeOfDNF_wellFormed (transport : PackedQuery → Query) (dnf : DNF) :
    WellFormed (treeOfDNF transport dnf) :=
  dnfInto_wf transport [] dnf (by intro index q left right hn; simp [node] at hn)

/-- The tree always reaches the concrete DNF's Boolean value in finitely many queries. -/
theorem treeOfDNF_eval (transport : PackedQuery → Query) (answer : Query → Bool) (dnf : DNF) :
    ∃ fuel, evalFuel answer (treeOfDNF transport dnf) fuel
      (root (treeOfDNF transport dnf)) = some (evalDNF (answer ∘ transport) dnf) :=
  dnfInto_eval transport answer [] dnf (by intro index q left right hn; simp [node] at hn)

/-- Every finite path answer is exactly the compiled DNF's answer. -/
theorem treeOfDNF_stageAnswer (transport : PackedQuery → Query) (answer : Query → Bool)
    (dnf : DNF) (b : Bool) :
    StageAnswer answer (treeOfDNF transport dnf) b ↔ evalDNF (answer ∘ transport) dnf = b := by
  obtain ⟨fuel, hf⟩ := treeOfDNF_eval transport answer dnf
  rw [stageAnswer_iff_evalFuel]
  constructor
  · rintro ⟨fuel', hf'⟩
    exact evalFuel_unique answer _ fuel fuel' _ _ b hf hf'
  · intro he
    exact ⟨fuel, by rwa [he] at hf⟩

/-- The affine compiler's finite tree is always well formed. -/
theorem treeOfFormula_wellFormed (transport : PackedQuery → Query) (code : Code) :
    WellFormed (treeOfFormula transport code) := treeOfDNF_wellFormed transport (compile code)

/-- The finite tree agrees with the concrete formula decision procedure. -/
theorem treeOfFormula_stageAnswer (transport : PackedQuery → Query) (answer : Query → Bool)
    (code : Code) (b : Bool) :
    StageAnswer answer (treeOfFormula transport code) b ↔
      decidePackedFormula (answer ∘ transport) code = b := treeOfDNF_stageAnswer _ _ _ _

private theorem foldr_computable {α β σ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → β × σ → σ} (default : β)
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b state => h a (b, state)) (g a)) := by
  refine (Tiling.Computability.List.foldl_computable default (Computable.list_reverse.comp hf) hg
    ((hh.comp Computable.fst
      ((Computable.snd.comp Computable.snd).pair
        (Computable.fst.comp Computable.snd))).to₂)).of_eq ?_
  intro a
  simp [List.foldl_reverse]

private theorem root_computable : Computable root :=
  Primrec.nat_sub.to_comp.comp Computable.list_length (Computable.const 1)

private theorem appendAtom_computable_of {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} {bad good : α → ℕ}
    {a : α → SortedAtom} {initial : α → Tree}
    (ht : Computable₂ transport) (hb : Computable bad) (hg : Computable good)
    (ha : Computable a) (hi : Computable initial) :
    Computable (fun x => appendAtom (transport x) (bad x) (good x) (a x) (initial x)) := by
  have hs : Computable (fun x => (a x).2.1) := Computable.fst.comp (Computable.snd.comp ha)
  have hquery := ht.comp Computable.id (atomQuery_computable.comp ha)
  have hn := (Computable.sumInr (α := Option Bool)).comp (hquery.pair
    ((Computable.cond hs hg hb).pair (Computable.cond hs hb hg)))
  refine (Computable.list_concat.comp hi hn).of_eq ?_
  intro x
  cases he : (a x).2.1 <;> simp only [appendAtom, he, Bool.false_eq_true, ↓reduceIte] <;> rfl

private theorem clauseInto_computable_of {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} {bad : α → ℕ}
    {initial : α → Tree} {clause : α → Clause}
    (ht : Computable₂ transport) (hb : Computable bad)
    (hi : Computable initial) (hc : Computable clause) :
    Computable (fun x => clauseInto (transport x) (bad x) (initial x) (clause x)) := by
  exact foldr_computable (false, false, [], []) hc
    (Computable.list_concat.comp hi (Computable.const (.inl (some true))))
    (appendAtom_computable_of
      ((ht.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)
      (hb.comp Computable.fst)
      (root_computable.comp (Computable.snd.comp Computable.snd))
      (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂

private theorem dnfInto_computable_of {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} {initial : α → Tree} {dnf : α → DNF}
    (ht : Computable₂ transport) (hi : Computable initial) (hd : Computable dnf) :
    Computable (fun x => dnfInto (transport x) (initial x) (dnf x)) := by
  exact foldr_computable [] hd
    (Computable.list_concat.comp hi (Computable.const (.inl (some false))))
    (clauseInto_computable_of
      ((ht.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)
      (root_computable.comp (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)).to₂

/-- Finite DNF tree generation is computable uniformly in a computable query transport. -/
theorem treeOfDNF_computable {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} (ht : Computable₂ transport) :
    Computable (fun x : α × DNF => treeOfDNF (transport x.1) x.2) :=
  dnfInto_computable_of
    ((ht.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂)
    (Computable.const []) Computable.snd

/-- The complete packed affine compiler produces its finite oracle tree computably. -/
theorem treeOfFormula_computable {α : Type*} [Primcodable α]
    {transport : α → PackedQuery → Query} (ht : Computable₂ transport) :
    Computable (fun x : α × Code => treeOfFormula (transport x.1) x.2) :=
  (treeOfDNF_computable ht).comp
    (Computable.fst.pair (compile_computable.comp Computable.snd))

/-- Native semantic correctness transfers to the generated finite oracle tree. -/
theorem treeOfFormula_native_correct
    {C : Tiling.AxisParallel.Terminal.Executable.RegionCode}
    (R : Tiling.AxisParallel.Terminal.Executable.Realization C)
    (O : Tiling.AxisParallel.Terminal.Executable.CorrectOracle C R)
    (transport : PackedQuery → Query) (answer : Query → Bool)
    (hanswer : ∀ q, answer (transport (Native.packQuery q)) = O.toOracle.answer q)
    (f : Tiling.AxisParallel.Terminal.Executable.Formula C 0 0) :
    StageAnswer answer (treeOfFormula transport (Native.packFormula f)) true ↔
      Tiling.AxisParallel.Terminal.Executable.Formula.Holds R f Fin.elim0 Fin.elim0 := by
  rw [treeOfFormula_stageAnswer]
  exact Native.decidePackedFormula_correct R O (answer ∘ transport) hanswer f

end Tiling.AxisParallel.Decidability.Affine.Trees
