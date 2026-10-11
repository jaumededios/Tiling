import Tiling.AxisParallel.Decidability.Certificates.Coding
import Tiling.Computability.Rational

/-!
# Effective positive certificate coding

The production lattice enumeration uses the sparse numerator/denominator rational
encoding. We preserve that encoding and relate it to Mathlib's native dense encoding.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Tiling.Computability.Rational

namespace Tiling.AxisParallel.Decidability.PositiveCoding

open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Decidability.CertificateCoding

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

private def latticeTuple : RawLatticeCode ≃ SparseRat × ℕ × ℕ × ℕ where
  toFun c := (⟨c.rationalSeparator⟩, c.representativeCount, c.firstIndexBound, c.secondIndexBound)
  invFun c := ⟨c.1.value, c.2.1, c.2.2.1, c.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨⟨q⟩, a, b, d⟩; rfl

instance instPrimcodableRawLatticeCode : Primcodable RawLatticeCode :=
  Primcodable.ofEquiv _ latticeTuple

theorem rawLattice_encoding_eq :
    instPrimcodableRawLatticeCode.toEncodable = instEncodableRawLatticeCode := by
  apply encodable_ext
  · intro c; rfl
  · intro n
    conv_lhs => rw [Encodable.decode_ofEquiv]
    conv_rhs => rw [Encodable.decode_ofEquiv]
    simp only [Encodable.decode_prod_val, sparseRat_decode_eq,
      Option.bind_map, Option.map_bind]
    rfl

theorem rawLattice_decode_primrec :
    Primrec (@Encodable.decode RawLatticeCode instEncodableRawLatticeCode) := by
  rw [← rawLattice_encoding_eq]
  exact Primrec.decode

private theorem boolAnd_primrec : Primrec₂ Bool.and := Primrec.dom_bool₂ _

private theorem positive_primrec : Primrec (fun n : ℕ => decide (0 < n)) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide

theorem rawLattice_representativeCount_primrec : Primrec RawLatticeCode.representativeCount :=
  Primrec.fst.comp (Primrec.snd.comp
    (show Primrec latticeTuple from Primrec.of_equiv))

theorem rawLattice_firstIndexBound_primrec : Primrec RawLatticeCode.firstIndexBound :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
    (show Primrec latticeTuple from Primrec.of_equiv)))

theorem rawLattice_secondIndexBound_primrec : Primrec RawLatticeCode.secondIndexBound :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
    (show Primrec latticeTuple from Primrec.of_equiv)))

theorem rawLattice_sparseSeparator_primrec :
    Primrec (fun c : RawLatticeCode => SparseRat.mk c.rationalSeparator) :=
  Primrec.fst.comp (show Primrec latticeTuple from Primrec.of_equiv)

theorem rawLattice_wellFormed_primrec : Primrec RawLatticeCode.wellFormed := by
  refine (boolAnd_primrec.comp
    (boolAnd_primrec.comp (positive_primrec.comp rawLattice_representativeCount_primrec)
      (positive_primrec.comp rawLattice_firstIndexBound_primrec))
    (positive_primrec.comp rawLattice_secondIndexBound_primrec)).of_eq ?_
  intro c
  simp only [RawLatticeCode.wellFormed, Bool.decide_coe]

private def positiveSum : RawPositiveCode ≃ RawTriangularCode ⊕ RawLatticeCode where
  toFun
    | .triangular c => .inl c
    | .lattice c => .inr c
  invFun
    | .inl c => .triangular c
    | .inr c => .lattice c
  left_inv c := by cases c <;> rfl
  right_inv c := by cases c <;> rfl

instance instPrimcodableRawPositiveCode : Primcodable RawPositiveCode :=
  Primcodable.ofEquiv _ positiveSum

theorem rawPositive_encoding_eq :
    instPrimcodableRawPositiveCode.toEncodable = instEncodableRawPositiveCode := by
  change @Encodable.ofEquiv RawPositiveCode (RawTriangularCode ⊕ RawLatticeCode)
    (@Sum.encodable _ _ instPrimcodableRawTriangularCode.toEncodable
      instPrimcodableRawLatticeCode.toEncodable) positiveSum = _
  rw [rawLattice_encoding_eq]
  rfl

theorem rawPositive_triangular_primrec : Primrec RawPositiveCode.triangular :=
  (show Primrec positiveSum.symm from Primrec.of_equiv_symm).comp Primrec.sumInl

theorem rawPositive_lattice_primrec : Primrec RawPositiveCode.lattice :=
  (show Primrec positiveSum.symm from Primrec.of_equiv_symm).comp Primrec.sumInr

theorem rawPositive_casesOn_computable {α : Type*} [Primcodable α]
    {triangular : RawTriangularCode → α} {lattice : RawLatticeCode → α}
    (ht : Computable triangular) (hl : Computable lattice) :
    Computable (fun c : RawPositiveCode =>
      match c with
      | .triangular t => triangular t
      | .lattice l => lattice l) := by
  refine (Computable.sumCasesOn
    (show Primrec positiveSum from Primrec.of_equiv).to_comp
    (ht.comp Computable.snd).to₂ (hl.comp Computable.snd).to₂).of_eq ?_
  intro c
  cases c <;> rfl

/-- Uniform elimination of a positive certificate with an encoded parameter. -/
theorem rawPositive_casesOn_computable₂ {α β : Type*} [Primcodable α] [Primcodable β]
    {triangular : α → RawTriangularCode → β} {lattice : α → RawLatticeCode → β}
    (ht : Computable₂ triangular) (hl : Computable₂ lattice) :
    Computable₂ (fun a (c : RawPositiveCode) =>
      match c with
      | .triangular t => triangular a t
      | .lattice l => lattice a l) := by
  have he : Computable (fun p : α × RawPositiveCode => positiveSum p.2) :=
    (show Primrec positiveSum from Primrec.of_equiv).to_comp.comp Computable.snd
  refine (Computable.sumCasesOn he
    (ht.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
    (hl.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂).of_eq ?_
  rintro ⟨a, c⟩
  cases c <;> rfl

theorem rawPositive_wellFormed_primrec : Primrec RawPositiveCode.wellFormed := by
  refine (Primrec.sumCasesOn (show Primrec positiveSum from Primrec.of_equiv)
    (rawTriangular_wellFormed_primrec.comp Primrec.snd).to₂
    (rawLattice_wellFormed_primrec.comp Primrec.snd).to₂).of_eq ?_
  intro c
  cases c <;> rfl

theorem rawPositiveStage_primrec : Primrec rawPositiveStage := by
  change Primrec (@Encodable.decode RawPositiveCode instEncodableRawPositiveCode)
  rw [← rawPositive_encoding_eq]
  exact Primrec.decode

private theorem optionFilter_primrec {α : Type*} [Primcodable α]
    {p : α → Bool} (hp : Primrec p) : Primrec (Option.filter p) := by
  refine (Primrec.option_casesOn Primrec.id (Primrec.const none)
    (Primrec.cond (hp.comp Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq ?_
  intro o
  cases o <;> simp [Option.filter]

theorem wellFormedPositiveStage_primrec : Primrec wellFormedPositiveStage :=
  (optionFilter_primrec rawPositive_wellFormed_primrec).comp rawPositiveStage_primrec

theorem rawLattice_wellFormed_computable : Computable RawLatticeCode.wellFormed :=
  rawLattice_wellFormed_primrec.to_comp

theorem rawPositive_wellFormed_computable : Computable RawPositiveCode.wellFormed :=
  rawPositive_wellFormed_primrec.to_comp

theorem rawPositiveStage_computable : Computable rawPositiveStage :=
  rawPositiveStage_primrec.to_comp

theorem wellFormedPositiveStage_computable : Computable wellFormedPositiveStage :=
  wellFormedPositiveStage_primrec.to_comp

theorem rawLattice_rationalSeparator_computable : Computable RawLatticeCode.rationalSeparator := by
  have hv : Computable SparseRat.value := sparseRat_value_primrec.to_comp
  have hs : Computable (fun c : RawLatticeCode => SparseRat.mk c.rationalSeparator) :=
    rawLattice_sparseSeparator_primrec.to_comp
  have h := Computable.comp (α := RawLatticeCode) (β := SparseRat) (σ := ℚ) hv hs
  exact h.of_eq (fun _ => rfl)

theorem rawLattice_mk_computable : Computable (fun p : ℚ × ℕ × ℕ × ℕ =>
    RawLatticeCode.mk p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have htuple : Computable (fun p : ℚ × ℕ × ℕ × ℕ =>
      (SparseRat.mk p.1, p.2)) :=
    Computable.pair (sparseRat_mk_computable.comp Computable.fst) Computable.snd
  have hinverse : Computable latticeTuple.symm :=
    (show Primrec latticeTuple.symm from Primrec.of_equiv_symm).to_comp
  exact (hinverse.comp htuple).of_eq (fun _ => rfl)

end Tiling.AxisParallel.Decidability.PositiveCoding
