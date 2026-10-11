import Mathlib.Computability.Partrec
import Mathlib.Data.List.GetD

/-! Computable bounded list traversal with computable element callbacks. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.Computability.List

private def foldBounded {α β σ : Type*} (f : α → List β) (g : α → σ)
    (h : α → σ × β → σ) (default : β) (input : α) : ℕ → σ
  | 0 => g input
  | n + 1 => h input (foldBounded f g h default input n, (f input).getD n default)

/-- A finite left fold is computable for any computable element operation. -/
theorem foldl_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → σ} {h : α → σ × β → σ} (default : β)
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun input => (f input).foldl (fun state value => h input (state, value))
      (g input)) := by
  have hbounded : Computable (fun x : α × ℕ => foldBounded f g h default x.1 x.2) := by
    have hrec := Computable.nat_rec
      (Computable.snd : Computable (fun x : α × ℕ => x.2))
      (hg.comp Computable.fst)
      ((hh.comp (Computable.fst.comp Computable.fst)
        ((Computable.snd.comp Computable.snd).pair
          ((Primrec.list_getD default).to_comp.comp
            (hf.comp (Computable.fst.comp Computable.fst))
            (Computable.fst.comp Computable.snd)))).to₂)
    refine hrec.of_eq ?_
    intro x
    induction x.2 with
    | zero => rfl
    | succ n ih => simp only [foldBounded, ih]
  refine (hbounded.comp (Computable.id.pair (Computable.list_length.comp hf))).of_eq ?_
  intro input
  have hfold : ∀ n, n ≤ (f input).length → foldBounded f g h default input n =
      ((f input).take n).foldl (fun state value => h input (state, value)) (g input) := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [foldBounded, ih (by omega), List.take_succ_eq_append_getElem (by omega),
        List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [List.getD_eq_getElem (f input) default (by omega)]
  simpa only [List.take_length, id_eq] using hfold (f input).length (by rfl)

/-- Finite mapping is computable uniformly in the parameters of the callback. -/
theorem map_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → σ} (default : β)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun input => (f input).map (g input)) := by
  have hfold := foldl_computable (σ := List σ) default hf (Computable.const [])
    ((Computable.list_concat.comp
      (Computable.fst.comp Computable.snd)
      (hg.comp Computable.fst (Computable.snd.comp Computable.snd))).to₂)
  refine hfold.of_eq ?_
  intro input
  have hgeneral : ∀ (values : List β) (initial : List σ),
      values.foldl (fun state value => state ++ [g input value]) initial =
        initial ++ values.map (g input) := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons value rest ih =>
      intro initial
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.append_assoc, List.singleton_append]
  simpa only [List.nil_append] using hgeneral (f input) []

/-- Flat mapping is computable uniformly in the parameters of the callback. -/
theorem flatMap_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → List σ} (default : β)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun input => (f input).flatMap (g input)) := by
  have hfold := foldl_computable (σ := List σ) default hf (Computable.const [])
    ((Computable.list_append.comp
      (Computable.fst.comp Computable.snd)
      (hg.comp Computable.fst (Computable.snd.comp Computable.snd))).to₂)
  refine hfold.of_eq ?_
  intro input
  have hgeneral : ∀ (values : List β) (initial : List σ),
      values.foldl (fun state value => state ++ g input value) initial =
        initial ++ values.flatMap (g input) := by
    intro values
    induction values with
    | nil => intro initial; simp
    | cons value rest ih =>
      intro initial
      rw [List.foldl_cons, ih]
      simp only [List.flatMap_cons, List.append_assoc]
  simpa only [List.nil_append] using hgeneral (f input) []

/-- Option-valued filtering is a finite computable operation. -/
theorem filterMap_computable {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α → List β} {g : α → β → Option σ} (default : β)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun input => (f input).filterMap (g input)) := by
  have hoption : Computable (fun o : Option σ => o.toList) := by
    refine (Computable.option_casesOn Computable.id (Computable.const [])
      ((Computable.list_cons.comp Computable.snd (Computable.const [])).to₂)).of_eq ?_
    intro o
    cases o <;> rfl
  refine (flatMap_computable default hf
    (hoption.comp hg).to₂).of_eq ?_
  intro input
  induction f input with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.flatMap_cons, List.filterMap_cons]
    cases g input value <;> simp [ih]

variable {α β : Type*}

private def foldTransition (f : α → β → α) (state : List β × α) : List β × α :=
  match state.1 with
  | [] => state
  | b :: bs => (bs, f state.2 b)

private theorem foldTransition_computable [Primcodable α] [Primcodable β]
    {f : α → β → α} (hf : Computable₂ f) : Computable (foldTransition f) := by
  refine (Computable.option_casesOn
    (Primrec.list_head?.to_comp.comp Computable.fst) Computable.id
    (Computable.pair
      (Primrec.list_tail.to_comp.comp (Computable.fst.comp Computable.fst))
      (hf.comp (Computable.snd.comp Computable.fst) Computable.snd)).to₂).of_eq ?_
  rintro ⟨xs, state⟩
  cases xs <;> rfl

private theorem foldTransition_iterate (f : α → β → α)
    (xs : List β) (state : α) :
    ((foldTransition f)^[xs.length] (xs, state)).2 = xs.foldl f state := by
  induction xs generalizing state with
  | nil => rfl
  | cons b bs ih =>
      rw [List.length_cons, Function.iterate_succ_apply]
      exact ih (f state b)

set_option maxHeartbeats 800000 in
-- Nested native list/product computation closures require additional elaboration steps.
/-- Finite folds preserve computability, under the native encodings. -/
theorem computable_list_foldl [Primcodable α] [Primcodable β]
    {f : α → β → α} (hf : Computable₂ f) :
    Computable₂ (fun (xs : List β) (state : α) => xs.foldl f state) := by
  have htransition := foldTransition_computable hf
  have hit : Computable (fun p : List β × α =>
      Nat.rec (motive := fun _ => List β × α) p
        (fun _ state => foldTransition f state) p.1.length) :=
    Computable.nat_rec (Computable.list_length.comp Computable.fst) Computable.id
      (htransition.comp (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.snd.comp hit).to₂.of_eq ?_
  rintro ⟨xs, state⟩
  change (Nat.rec (motive := fun _ => List β × α) (xs, state)
    (fun _ state => foldTransition f state) xs.length).2 = xs.foldl f state
  have hrec : Nat.rec (motive := fun _ => List β × α) (xs, state)
      (fun _ state => foldTransition f state) xs.length =
      (foldTransition f)^[xs.length] (xs, state) := by
    induction xs.length with
    | zero => rfl
    | succ n ih => simp [Function.iterate_succ_apply', ih]
  rw [hrec]
  exact foldTransition_iterate f xs state

theorem computable_list_foldr [Primcodable α] [Primcodable β]
    {f : β → α → α} (hf : Computable₂ f) :
    Computable₂ (fun (xs : List β) (state : α) => xs.foldr f state) := by
  have hflip : Computable₂ (fun a b => f b a) :=
    (hf.comp Computable.snd Computable.fst).to₂
  have hfold := computable_list_foldl hflip
  refine (hfold.comp (Computable.list_reverse.comp Computable.fst)
    Computable.snd).to₂.of_eq ?_
  rintro ⟨xs, state⟩
  exact List.foldl_reverse

set_option maxHeartbeats 800000 in
-- The persistent parameter adds product encodings to the certified fold composition.
/-- A computable input parameter can be retained throughout a finite fold. -/
theorem computable_list_foldr_param {γ : Type*}
    [Primcodable α] [Primcodable β] [Primcodable γ]
    {xs : γ → List β} {initial : γ → α} {combine : γ → β × α → α}
    (hxs : Computable xs) (hinitial : Computable initial) (hcombine : Computable₂ combine) :
    Computable (fun input =>
      (xs input).foldr (fun b state => combine input (b, state)) (initial input)) := by
  let step : β → γ × α → γ × α :=
    fun b state => (state.1, combine state.1 (b, state.2))
  have hstep : Computable₂ step :=
    (Computable.pair (Computable.fst.comp Computable.snd)
      (hcombine.comp (Computable.fst.comp Computable.snd)
        (Computable.pair Computable.fst (Computable.snd.comp Computable.snd)))).to₂
  have hfold := computable_list_foldr hstep
  refine (Computable.snd.comp
    (hfold.comp hxs (Computable.pair Computable.id hinitial))).of_eq ?_
  intro input
  have hsem : (xs input).foldr step (input, initial input) =
      (input, (xs input).foldr (fun b state => combine input (b, state)) (initial input)) := by
    induction xs input with
    | nil => rfl
    | cons b bs ih => simp only [List.foldr_cons, ih, step]
  exact congrArg Prod.snd hsem

theorem computable_list_map {γ : Type*} [Primcodable β] [Primcodable γ]
    {f : β → γ} (hf : Computable f) : Computable (List.map f) := by
  have hstep : Computable₂ (fun b (xs : List γ) => f b :: xs) :=
    (Computable.list_cons.comp (hf.comp Computable.fst) Computable.snd).to₂
  refine ((computable_list_foldr hstep).comp Computable.id (Computable.const [])).of_eq ?_
  intro xs
  induction xs with
  | nil => rfl
  | cons b bs _ => simp

theorem list_replicate_primrec {α : Type*} [Primcodable α] :
    Primrec₂ (List.replicate : ℕ → α → List α) := by
  refine (Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.snd.comp Primrec.fst).to₂).to₂.of_eq ?_
  intro count value
  simp

end Tiling.Computability.List
