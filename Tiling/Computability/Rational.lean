import Mathlib.Data.Rat.Denumerable
import Mathlib.Computability.RE
import Mathlib.Tactic.Ring

/-! Computability of integer and rational arithmetic with native encodings.
The sparse rational representation also provides an explicit bridge to the dense
native representation. This module has no geometric or certificate dependencies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.Computability.Rational

private def gcdStep (p : ℕ × ℕ) : ℕ × ℕ :=
  if p.2 = 0 then p else (p.2, p.1 % p.2)

private theorem gcdStep_primrec : Primrec gcdStep :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) Primrec.id
    (Primrec.pair Primrec.snd (Primrec.nat_mod.comp Primrec.fst Primrec.snd))

private theorem gcdStep_iterate (fuel a b : ℕ) (hb : b < fuel) :
    gcdStep^[fuel] (a, b) = (Nat.gcd a b, 0) := by
  induction fuel generalizing a b with
  | zero => omega
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    by_cases h : b = 0
    · subst b
      simp only [gcdStep, Nat.gcd_zero_right]
      exact Function.iterate_fixed (by simp [gcdStep]) _
    · rw [gcdStep, if_neg h]
      rw [ih b (a % b) (lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero h))
        (Nat.lt_succ_iff.mp hb))]
      exact congrArg (fun g => (g, 0)) ((Nat.gcd_comm b (a % b)).trans
        ((Nat.gcd_rec b a).symm.trans (Nat.gcd_comm b a)))

theorem nat_gcd_primrec : Primrec₂ Nat.gcd := by
  have hit : Primrec (fun x : (ℕ × ℕ) × ℕ => gcdStep^[x.2] x.1) := by
    have hrec : Primrec (fun x : (ℕ × ℕ) × ℕ =>
        Nat.rec (motive := fun _ => ℕ × ℕ) x.1 (fun _ p => gcdStep p) x.2) :=
      Primrec.nat_rec Primrec.id
        (gcdStep_primrec.comp (Primrec.snd.comp Primrec.snd)).to₂
    refine hrec.of_eq ?_
    rintro ⟨p, n⟩
    induction n with
    | zero => rfl
    | succ n ih =>
      change gcdStep (Nat.rec (motive := fun _ => ℕ × ℕ) p (fun _ p => gcdStep p) n) = _
      rw [ih, Function.iterate_succ_apply']
  refine (Primrec.fst.comp (hit.comp
    (Primrec.pair Primrec.id (Primrec.succ.comp Primrec.snd)))).to₂.of_eq ?_
  intro a b
  change (gcdStep^[b + 1] (a, b)).1 = Nat.gcd a b
  rw [gcdStep_iterate (b + 1) a b (Nat.lt_succ_self b)]

theorem int_natAbs_primrec : Primrec Int.natAbs := by
  refine (Primrec.nat_add.comp
    (Primrec.nat_div.comp Primrec.encode (Primrec.const 2))
    (Primrec.nat_mod.comp Primrec.encode (Primrec.const 2))).of_eq ?_
  intro z
  cases z with
  | ofNat n =>
    change (2 * n) / 2 + (2 * n) % 2 = n
    omega
  | negSucc n =>
    change (2 * n + 1) / 2 + (2 * n + 1) % 2 = n + 1
    omega

private abbrev CanonicalPair := {p : ℤ × ℕ // 0 < p.2 ∧ p.1.natAbs.Coprime p.2}

private theorem canonicalPair_primrec :
    PrimrecPred (fun p : ℤ × ℕ => 0 < p.2 ∧ p.1.natAbs.Coprime p.2) := by
  refine (PrimrecPred.and (Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd)
    (Primrec.eq.comp (nat_gcd_primrec.comp
      (int_natAbs_primrec.comp Primrec.fst) Primrec.snd) (Primrec.const 1))).of_eq ?_
  intro p
  rw [Nat.coprime_iff_gcd_eq_one]

private instance : Primcodable CanonicalPair := Primcodable.subtype canonicalPair_primrec

/-- A rational with the sparse production encoding, kept distinct from native rational codes. -/
structure SparseRat where
  value : ℚ
  deriving DecidableEq

private theorem encodable_ext {α : Type*} (e₁ e₂ : Encodable α)
    (he : ∀ x, @Encodable.encode α e₁ x = @Encodable.encode α e₂ x)
    (hd : ∀ n, @Encodable.decode α e₁ n = @Encodable.decode α e₂ n) : e₁ = e₂ := by
  cases e₁ with
  | mk e₁ d₁ h₁ =>
    cases e₂ with
    | mk e₂ d₂ h₂ =>
      have he' : e₁ = e₂ := funext he
      have hd' : d₁ = d₂ := funext hd
      cases he'
      cases hd'
      rfl

private def sparseRatPair : SparseRat ≃ CanonicalPair where
  toFun q := ⟨(q.value.num, q.value.den), Nat.pos_of_ne_zero q.value.den_nz,
    q.value.reduced⟩
  invFun q := ⟨⟨q.1.1, q.1.2, Nat.ne_of_gt q.2.1, q.2.2⟩⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

instance instPrimcodableSparseRat : Primcodable SparseRat :=
  Primcodable.ofEquiv _ sparseRatPair

theorem sparseRat_encoding_eq (q : ℚ) :
    Encodable.encode (SparseRat.mk q) = @Encodable.encode ℚ Rat.instEncodable q := rfl

private def rationalSigma : ℚ ≃ Σ z : ℤ, {d : ℕ // 0 < d ∧ z.natAbs.Coprime d} where
  toFun q := ⟨q.num, q.den, Nat.pos_of_ne_zero q.den_nz, q.reduced⟩
  invFun
    | ⟨z, ⟨d, hpos, hcop⟩⟩ => ⟨z, d, Nat.ne_of_gt hpos, hcop⟩
  left_inv q := by cases q; rfl
  right_inv q := by rcases q with ⟨z, d, hpos, hcop⟩; rfl

theorem sparseRat_decode_eq (n : ℕ) :
    Encodable.decode (α := SparseRat) n =
      (@Encodable.decode ℚ Rat.instEncodable n).map SparseRat.mk := by
  simp only [Encodable.decode_ofEquiv, Option.map_map]
  change (Encodable.decodeSubtype n : Option CanonicalPair).map sparseRatPair.symm =
    (Encodable.decodeSigma n : Option (Σ z : ℤ, {d : ℕ // 0 < d ∧ z.natAbs.Coprime d})).map
      (SparseRat.mk ∘ rationalSigma.symm)
  simp only [Encodable.decodeSubtype, Encodable.decodeSigma, Encodable.decode_prod_val,
    Option.map_bind, Option.bind_assoc]
  apply congrArg (fun f => (Encodable.decode n.unpair.1 : Option ℤ).bind f)
  funext z
  simp only [Function.comp_def, Option.bind_map, Option.map_map]
  change _ = (Encodable.decodeSubtype n.unpair.2 :
    Option {d : ℕ // 0 < d ∧ z.natAbs.Coprime d}).map _
  simp only [Encodable.decodeSubtype, Option.map_bind]
  simp only [Encodable.decode_nat, Option.bind_some]
  by_cases h : 0 < n.unpair.2 ∧ z.natAbs.Coprime n.unpair.2
  · simp only [Function.comp_apply, Option.map_dif]
    split
    · congr 1
      apply congrArg SparseRat.mk
      apply rationalSigma.injective
      change (⟨z, n.unpair.2, h.1, h.2⟩ : Σ z : ℤ, {d : ℕ // 0 < d ∧ z.natAbs.Coprime d}) = _
      rw [rationalSigma.apply_symm_apply]
    · rename_i hn
      exact (hn h).elim
  · simp [h]

theorem sparseRat_num_primrec : Primrec (fun q : SparseRat => q.value.num) :=
  Primrec.fst.comp (Primrec.subtype_val.comp
    (show Primrec sparseRatPair from Primrec.of_equiv))

theorem sparseRat_den_primrec : Primrec (fun q : SparseRat => q.value.den) :=
  Primrec.snd.comp (Primrec.subtype_val.comp
    (show Primrec sparseRatPair from Primrec.of_equiv))

section NativeRationals

local instance nativeRatEncodable : Encodable ℚ := Rat.instDenumerable.toEncodable

private instance sparseRange_decidable :
    DecidablePred (fun n => n ∈ Set.range (Encodable.encode : SparseRat → ℕ)) :=
  Encodable.decidableRangeEncode SparseRat

private def denseRank (n : ℕ) : ℕ :=
  (List.range n).countP (fun k => k ∈ Set.range (Encodable.encode : SparseRat → ℕ))

private theorem denseRank_primrec : Primrec denseRank := by
  refine (Primrec.list_length.comp
    ((Primrec.listFilter (Primcodable.mem_range_encode (α := SparseRat))).comp
      Primrec.list_range)).of_eq ?_
  intro n
  exact List.countP_eq_length_filter.symm

private theorem native_rat_encoding_eq (q : ℚ) :
    Encodable.encode q = denseRank (Encodable.encode (SparseRat.mk q)) := by
  let : DecidablePred (fun k => k ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable)) :=
    @Encodable.decidableRangeEncode ℚ Rat.instEncodable
  change (List.range (@Encodable.encode ℚ Rat.instEncodable q)).countP
    (fun k => decide (k ∈ Set.range (@Encodable.encode ℚ Rat.instEncodable))) = _
  unfold denseRank
  apply congrArg (fun p => (List.range (@Encodable.encode ℚ Rat.instEncodable q)).countP p)
  funext k
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨⟨x⟩, hx⟩
  · rintro ⟨⟨x⟩, hx⟩
    exact ⟨x, hx⟩

theorem sparseRat_value_primrec : Primrec SparseRat.value := by
  apply Primrec.encode_iff.mp
  exact (denseRank_primrec.comp Primrec.encode).of_eq
    (fun q => (native_rat_encoding_eq q.value).symm)

private theorem nativeSparseCode_exists (q : ℚ) :
    ∃ n, n ∈ Set.range (Encodable.encode : SparseRat → ℕ) ∧ denseRank n = Encodable.encode q :=
  ⟨Encodable.encode (SparseRat.mk q), Set.mem_range_self _, (native_rat_encoding_eq q).symm⟩

private def nativeSparseCode (q : ℚ) : ℕ := Nat.find (nativeSparseCode_exists q)

private theorem nativeSparseCode_computable : Computable nativeSparseCode := by
  apply Computable.find
  have hp : PrimrecPred (fun x : ℚ × ℕ =>
      x.2 ∈ Set.range (Encodable.encode : SparseRat → ℕ) ∧ denseRank x.2 = Encodable.encode x.1) :=
    PrimrecPred.and ((Primcodable.mem_range_encode (α := SparseRat)).comp Primrec.snd)
    (Primrec.eq.comp (denseRank_primrec.comp Primrec.snd)
      (Primrec.encode.comp Primrec.fst))
  exact ⟨inferInstance, hp.decide.to_comp⟩

theorem sparseRat_mk_computable : Computable SparseRat.mk := by
  have h : Computable (fun q : ℚ =>
      (Encodable.decode (α := SparseRat) (nativeSparseCode q)).getD ⟨0⟩) :=
    Computable.option_getD (Primrec.decode.to_comp.comp nativeSparseCode_computable)
      (Computable.const (⟨0⟩ : SparseRat))
  refine h.of_eq ?_
  intro q
  obtain ⟨⟨x, hx⟩, hrank⟩ := Nat.find_spec (nativeSparseCode_exists q)
  have hxq : x.value = q := by
    apply Encodable.encode_injective
    rw [native_rat_encoding_eq x.value]
    exact hx.symm ▸ hrank
  have hxmk : x = SparseRat.mk q := by cases x; congr
  rw [nativeSparseCode, ← hx, Encodable.encodek, Option.getD_some, hxmk]

theorem rat_num_computable : Computable Rat.num :=
  sparseRat_num_primrec.to_comp.comp sparseRat_mk_computable

theorem rat_den_computable : Computable Rat.den :=
  sparseRat_den_primrec.to_comp.comp sparseRat_mk_computable

end NativeRationals

theorem int_ofNat_primrec : Primrec Int.ofNat := by
  apply Primrec.encode_iff.mp
  exact (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id).of_eq (fun _ => rfl)

private theorem int_negSucc_primrec : Primrec Int.negSucc := by
  apply Primrec.encode_iff.mp
  exact (Primrec.succ.comp
    (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)).of_eq (fun _ => rfl)

theorem int_toNat_primrec : Primrec Int.toNat := by
  refine (Primrec.cond
    (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.encode (Primrec.const 2))
      (Primrec.const 0))
    (Primrec.nat_div.comp Primrec.encode (Primrec.const 2)) (Primrec.const 0)).of_eq ?_
  intro z
  cases z with
  | ofNat n =>
    change (bif (2 * n) % 2 == 0 then (2 * n) / 2 else 0) = n
    simp
  | negSucc n =>
    change (bif (2 * n + 1) % 2 == 0 then (2 * n + 1) / 2 else 0) = 0
    simp

private def negativeMagnitude (z : ℤ) : ℕ := z.natAbs - z.toNat

private theorem negativeMagnitude_primrec : Primrec negativeMagnitude :=
  Primrec.nat_sub.comp int_natAbs_primrec int_toNat_primrec

private theorem integer_magnitudes (z : ℤ) :
    z = (z.toNat : ℤ) - (negativeMagnitude z : ℤ) := by
  cases z with
  | ofNat n => simp [negativeMagnitude]
  | negSucc n =>
    change Int.negSucc n = (0 : ℤ) - ((n + 1 : ℕ) : ℤ)
    rw [Int.negSucc_eq]
    simp

theorem int_subNatNat_primrec : Primrec₂ Int.subNatNat := by
  refine (Primrec.nat_casesOn (Primrec.nat_sub.comp Primrec.snd Primrec.fst)
    (int_ofNat_primrec.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (int_negSucc_primrec.comp Primrec.snd).to₂).to₂.of_eq ?_
  intro m n
  change Nat.casesOn (n - m) (Int.ofNat (m - n)) Int.negSucc = Int.subNatNat m n
  unfold Int.subNatNat
  cases n - m <;> rfl

theorem int_add_primrec : Primrec₂ (fun x y : ℤ => x + y) := by
  refine (int_subNatNat_primrec.comp
    (Primrec.nat_add.comp (int_toNat_primrec.comp Primrec.fst)
      (int_toNat_primrec.comp Primrec.snd))
    (Primrec.nat_add.comp (negativeMagnitude_primrec.comp Primrec.fst)
      (negativeMagnitude_primrec.comp Primrec.snd))).to₂.of_eq ?_
  intro x y
  rw [Int.subNatNat_eq_coe, Nat.cast_add, Nat.cast_add]
  conv_rhs => rw [integer_magnitudes x, integer_magnitudes y]
  ring

theorem int_neg_primrec : Primrec (fun x : ℤ => -x) := by
  refine (int_subNatNat_primrec.comp negativeMagnitude_primrec int_toNat_primrec).of_eq ?_
  intro x
  rw [Int.subNatNat_eq_coe]
  conv_rhs => rw [integer_magnitudes x]
  ring

theorem int_mul_primrec : Primrec₂ (fun x y : ℤ => x * y) := by
  refine (int_subNatNat_primrec.comp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (int_toNat_primrec.comp Primrec.fst)
        (int_toNat_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativeMagnitude_primrec.comp Primrec.fst)
        (negativeMagnitude_primrec.comp Primrec.snd)))
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (int_toNat_primrec.comp Primrec.fst)
        (negativeMagnitude_primrec.comp Primrec.snd))
      (Primrec.nat_mul.comp (negativeMagnitude_primrec.comp Primrec.fst)
        (int_toNat_primrec.comp Primrec.snd)))).to₂.of_eq ?_
  intro x y
  rw [Int.subNatNat_eq_coe, Nat.cast_add, Nat.cast_add]
  simp only [Nat.cast_mul]
  conv_rhs => rw [integer_magnitudes x, integer_magnitudes y]
  ring

theorem int_le_primrec : PrimrecRel (fun x y : ℤ => x ≤ y) := by
  refine (Primrec.nat_le.comp
    (Primrec.nat_add.comp (int_toNat_primrec.comp Primrec.fst)
      (negativeMagnitude_primrec.comp Primrec.snd))
    (Primrec.nat_add.comp (int_toNat_primrec.comp Primrec.snd)
      (negativeMagnitude_primrec.comp Primrec.fst))).of_eq ?_
  rintro ⟨x, y⟩
  change (x.toNat + negativeMagnitude y ≤ y.toNat + negativeMagnitude x) ↔ x ≤ y
  have hx := integer_magnitudes x
  have hy := integer_magnitudes y
  omega

theorem int_lt_primrec : PrimrecRel (fun x y : ℤ => x < y) :=
  (int_le_primrec.swap.not).of_eq (fun _ _ => not_le)

theorem int_add_computable : Computable₂ (fun x y : ℤ => x + y) := int_add_primrec.to_comp

theorem int_mul_computable : Computable₂ (fun x y : ℤ => x * y) := int_mul_primrec.to_comp

theorem int_neg_computable : Computable (fun x : ℤ => -x) := int_neg_primrec.to_comp

theorem int_natAbs_computable : Computable Int.natAbs := int_natAbs_primrec.to_comp

theorem int_ofNat_computable : Computable Int.ofNat := int_ofNat_primrec.to_comp

theorem int_le_computable : Computable₂ (fun x y : ℤ => decide (x ≤ y)) :=
  int_le_primrec.decide.to_comp

theorem int_lt_computable : Computable₂ (fun x y : ℤ => decide (x < y)) :=
  int_lt_primrec.decide.to_comp

/-- Total functions with a computable equality graph into a denumerable type are computable. -/
theorem computable_of_graph {α β : Type*} [Primcodable α] [Denumerable β] [DecidableEq β]
    {f : α → β} (hgraph : Computable (fun p : α × β => decide (f p.1 = p.2))) :
    Computable f := by
  have hex : ∀ a : α, ∃ n, f a = Denumerable.ofNat β n :=
    fun a => ⟨Encodable.encode (f a), (Denumerable.ofNat_encode (f a)).symm⟩
  have hp : ComputablePred (fun p : α × ℕ => f p.1 = Denumerable.ofNat β p.2) :=
    ⟨inferInstance, hgraph.comp
      (Computable.pair Computable.fst ((Primrec.ofNat β).to_comp.comp Computable.snd))⟩
  exact ((Primrec.ofNat β).to_comp.comp (Computable.find hp hex)).of_eq
    (fun a => (Nat.find_spec (hex a)).symm)

theorem rat_divInt_computable : Computable₂ Rat.divInt := by
  apply computable_of_graph
  have hn : Computable (fun x : (ℤ × ℤ) × ℚ => x.1.1) :=
    Computable.fst.comp Computable.fst
  have hd : Computable (fun x : (ℤ × ℤ) × ℚ => x.1.2) :=
    Computable.snd.comp Computable.fst
  have hnum : Computable (fun x : (ℤ × ℤ) × ℚ => x.2.num) :=
    rat_num_computable.comp Computable.snd
  have hden : Computable (fun x : (ℤ × ℤ) × ℚ => (x.2.den : ℤ)) :=
    int_ofNat_computable.comp (rat_den_computable.comp Computable.snd)
  have hzero : Computable (fun x : (ℤ × ℤ) × ℚ => decide (x.1.2 = 0)) :=
    (Primrec.eq.decide : Primrec₂ (fun n m : ℤ => decide (n = m))).to_comp.comp
      hd (Computable.const 0)
  have hqzero : Computable (fun x : (ℤ × ℤ) × ℚ => decide (x.2 = 0)) :=
    (Primrec.eq.decide : Primrec₂ (fun q r : ℚ => decide (q = r))).to_comp.comp
      Computable.snd (Computable.const 0)
  have hcross : Computable (fun x : (ℤ × ℤ) × ℚ =>
      decide (x.1.1 * (x.2.den : ℤ) = x.2.num * x.1.2)) :=
    (Primrec.eq.decide : Primrec₂ (fun n m : ℤ => decide (n = m))).to_comp.comp
      (int_mul_computable.comp hn hden) (int_mul_computable.comp hnum hd)
  refine (Computable.cond hzero hqzero hcross).of_eq ?_
  rintro ⟨⟨n, d⟩, q⟩
  change (bif decide (d = 0) then decide (q = 0) else
    decide (n * (q.den : ℤ) = q.num * d)) = decide (Rat.divInt n d = q)
  by_cases hd : d = 0
  · simp [hd, eq_comm]
  · simp only [hd, decide_false, Bool.cond_false]
    apply Bool.decide_congr
    exact (Rat.divInt_eq_divInt_iff hd (Int.natCast_ne_zero.mpr q.den_nz)).symm.trans
      (by rw [Rat.num_divInt_den])

theorem rat_mkRat_computable : Computable₂ mkRat := by
  have h : Computable (fun p : ℤ × ℕ => Rat.divInt p.1 (Int.ofNat p.2)) :=
    rat_divInt_computable.comp Computable.fst
      (int_ofNat_computable.comp Computable.snd)
  exact h.of_eq (fun p => (Rat.mkRat_eq_divInt p.1 p.2).symm)

theorem int_rat_computable : Computable (fun n : ℤ => (n : ℚ)) := by
  exact (rat_divInt_computable.comp Computable.id (Computable.const 1)).of_eq
    (fun n => (Rat.intCast_eq_divInt n).symm)

theorem nat_rat_computable : Computable (fun n : ℕ => (n : ℚ)) :=
  int_rat_computable.comp int_ofNat_computable

theorem rat_neg_computable : Computable (fun q : ℚ => -q) := by
  refine (rat_divInt_computable.comp (int_neg_computable.comp rat_num_computable)
    (int_ofNat_computable.comp rat_den_computable)).of_eq ?_
  intro q
  exact (Rat.neg_def q).symm

theorem rat_add_computable : Computable₂ (fun q r : ℚ => q + r) := by
  have hn : Computable (fun x : ℚ × ℚ => x.1.num) :=
    rat_num_computable.comp Computable.fst
  have hm : Computable (fun x : ℚ × ℚ => x.2.num) :=
    rat_num_computable.comp Computable.snd
  have hd : Computable (fun x : ℚ × ℚ => x.1.den) :=
    rat_den_computable.comp Computable.fst
  have he : Computable (fun x : ℚ × ℚ => x.2.den) :=
    rat_den_computable.comp Computable.snd
  refine (rat_mkRat_computable.comp
    (int_add_computable.comp
      (int_mul_computable.comp hn (int_ofNat_computable.comp he))
      (int_mul_computable.comp hm (int_ofNat_computable.comp hd)))
    (Primrec.nat_mul.to_comp.comp hd he)).to₂.of_eq ?_
  rintro ⟨q, r⟩
  exact (Rat.add_def' q r).symm

theorem rat_mul_computable : Computable₂ (fun q r : ℚ => q * r) := by
  refine (rat_mkRat_computable.comp
    (int_mul_computable.comp (rat_num_computable.comp Computable.fst)
      (rat_num_computable.comp Computable.snd))
    (Primrec.nat_mul.to_comp.comp (rat_den_computable.comp Computable.fst)
      (rat_den_computable.comp Computable.snd))).to₂.of_eq ?_
  rintro ⟨q, r⟩
  exact (Rat.mul_def' q r).symm

theorem rat_le_computable : Computable₂ (fun q r : ℚ => decide (q ≤ r)) := by
  refine (int_le_computable.comp
    (int_mul_computable.comp (rat_num_computable.comp Computable.fst)
      (int_ofNat_computable.comp (rat_den_computable.comp Computable.snd)))
    (int_mul_computable.comp (rat_num_computable.comp Computable.snd)
      (int_ofNat_computable.comp (rat_den_computable.comp Computable.fst)))).to₂.of_eq ?_
  rintro ⟨q, r⟩
  exact Bool.decide_congr (Rat.le_iff q r).symm

theorem rat_lt_computable : Computable₂ (fun q r : ℚ => decide (q < r)) := by
  refine (int_lt_computable.comp
    (int_mul_computable.comp (rat_num_computable.comp Computable.fst)
      (int_ofNat_computable.comp (rat_den_computable.comp Computable.snd)))
    (int_mul_computable.comp (rat_num_computable.comp Computable.snd)
      (int_ofNat_computable.comp (rat_den_computable.comp Computable.fst)))).to₂.of_eq ?_
  rintro ⟨q, r⟩
  exact Bool.decide_congr (Rat.lt_iff q r).symm

theorem int_sub_primrec : Primrec₂ (fun x y : ℤ => x - y) := by
  exact (int_add_primrec.comp Primrec.fst (int_neg_primrec.comp Primrec.snd)).to₂.of_eq
    (fun x y => (sub_eq_add_neg x y).symm)

theorem int_sub_computable : Computable₂ (fun x y : ℤ => x - y) := int_sub_primrec.to_comp

theorem rat_sub_computable : Computable₂ (fun q r : ℚ => q - r) := by
  exact (rat_add_computable.comp Computable.fst
    (rat_neg_computable.comp Computable.snd)).of_eq
      (fun p : ℚ × ℚ => (sub_eq_add_neg p.1 p.2).symm)

theorem rat_inv_computable : Computable (fun q : ℚ => q⁻¹) :=
  (rat_divInt_computable.comp (int_ofNat_computable.comp rat_den_computable)
    rat_num_computable).of_eq (fun q => (Rat.inv_def q).symm)

theorem rat_div_computable : Computable₂ (fun q r : ℚ => q / r) :=
  (rat_mul_computable.comp Computable.fst
    (rat_inv_computable.comp Computable.snd)).of_eq
      (fun p : ℚ × ℚ => (div_eq_mul_inv p.1 p.2).symm)

theorem monoid_pow_primrec {α : Type*} [Primcodable α] [Monoid α]
    (hmul : Primrec₂ (fun x y : α => x * y)) : Primrec₂ (fun x : α => (x ^ · : ℕ → α)) := by
  have hrec : Primrec (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => α) 1 (fun _ r => r * p.1) p.2) :=
    Primrec.nat_rec (Primrec.const 1)
      (hmul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂
  refine hrec.to₂.of_eq ?_
  intro x n
  induction n with
  | zero => exact (pow_zero x).symm
  | succ n ih =>
    change Nat.rec (motive := fun _ => α) 1 (fun _ r => r * x) n * x = x ^ (n + 1)
    rw [ih, pow_succ]

theorem monoid_pow_computable {α : Type*} [Primcodable α] [Monoid α]
    (hmul : Computable₂ (fun x y : α => x * y)) :
    Computable₂ (fun x : α => (x ^ · : ℕ → α)) := by
  have hrec : Computable (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => α) 1 (fun _ r => r * p.1) p.2) :=
    Computable.nat_rec Computable.snd (Computable.const 1)
      (hmul.comp (Computable.snd.comp Computable.snd)
        (Computable.fst.comp Computable.fst)).to₂
  refine hrec.of_eq ?_
  rintro ⟨x, n⟩
  induction n with
  | zero => exact (pow_zero x).symm
  | succ n ih =>
    change Nat.rec (motive := fun _ => α) 1 (fun _ r => r * x) n * x = x ^ (n + 1)
    rw [ih, pow_succ]

theorem nat_pow_primrec : Primrec₂ (fun x : ℕ => (x ^ · : ℕ → ℕ)) :=
  monoid_pow_primrec Primrec.nat_mul

theorem int_pow_primrec : Primrec₂ (fun x : ℤ => (x ^ · : ℕ → ℤ)) :=
  monoid_pow_primrec int_mul_primrec

theorem int_pow_computable : Computable₂ (fun x : ℤ => (x ^ · : ℕ → ℤ)) :=
  int_pow_primrec.to_comp

theorem rat_pow_computable : Computable₂ (fun q : ℚ => (q ^ · : ℕ → ℚ)) :=
  monoid_pow_computable rat_mul_computable

end Tiling.Computability.Rational
