import Tiling.AxisParallel.Terminal.CertificateCoding
import Mathlib.Computability.Partrec

/-!
# Effectivity certificates for the finite certificate enumeration

The primitive recursive instances below preserve the production encodings of the
negative and finite triangular certificate data. Their decoding and validity checks
are therefore certified operations of the existing search. Rational lattice data,
formula generation and oracle execution require further computation certificates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateCoding

open Tiling.AxisParallel.Terminal.Executable

private def negativeTuple : RawNegativeCode ≃ ℕ × ℕ × ℕ where
  toFun c := (c.boxIndex, c.horizontalSubdivisions, c.verticalSubdivisions)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, d⟩; rfl

instance instPrimcodableRawNegativeCode : Primcodable RawNegativeCode :=
  Primcodable.ofEquiv _ negativeTuple

theorem rawNegative_encoding_eq :
    instPrimcodableRawNegativeCode.toEncodable = instEncodableRawNegativeCode := rfl

theorem rawNegative_mk_primrec : Primrec (fun p : ℕ × ℕ × ℕ =>
    RawNegativeCode.mk p.1 p.2.1 p.2.2) :=
  show Primrec negativeTuple.symm from Primrec.of_equiv_symm

theorem rawNegative_boxIndex_primrec : Primrec RawNegativeCode.boxIndex :=
  Primrec.fst.comp (show Primrec negativeTuple from Primrec.of_equiv)

theorem rawNegative_horizontalSubdivisions_primrec :
    Primrec RawNegativeCode.horizontalSubdivisions :=
  Primrec.fst.comp (Primrec.snd.comp
    (show Primrec negativeTuple from Primrec.of_equiv))

theorem rawNegative_verticalSubdivisions_primrec :
    Primrec RawNegativeCode.verticalSubdivisions :=
  Primrec.snd.comp (Primrec.snd.comp
    (show Primrec negativeTuple from Primrec.of_equiv))

private theorem boolAnd_primrec : Primrec₂ Bool.and := Primrec.dom_bool₂ _

private theorem positive_primrec : Primrec (fun n : ℕ => decide (0 < n)) :=
  (Primrec.nat_lt.comp (Primrec.const 0) Primrec.id).decide

theorem rawNegative_wellFormed_primrec : Primrec RawNegativeCode.wellFormed := by
  refine (boolAnd_primrec.comp
      (boolAnd_primrec.comp
        (positive_primrec.comp rawNegative_boxIndex_primrec)
        (positive_primrec.comp rawNegative_horizontalSubdivisions_primrec))
      (positive_primrec.comp rawNegative_verticalSubdivisions_primrec)).of_eq ?_
  intro c
  simp only [RawNegativeCode.wellFormed, Bool.decide_coe]

theorem rawNegativeStage_primrec : Primrec rawNegativeStage := by
  change Primrec (@Encodable.decode RawNegativeCode _)
  exact Primrec.decode

private theorem optionFilter_primrec {α : Type*} [Primcodable α]
    {p : α → Bool} (hp : Primrec p) : Primrec (Option.filter p) := by
  refine (Primrec.option_casesOn Primrec.id (Primrec.const none)
    (Primrec.cond (hp.comp Primrec.snd)
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).of_eq ?_
  intro o
  cases o <;> simp [Option.filter]

theorem wellFormedNegativeStage_primrec : Primrec wellFormedNegativeStage := by
  exact (optionFilter_primrec rawNegative_wellFormed_primrec).comp
    rawNegativeStage_primrec

theorem rawNegativeStage_computable : Computable rawNegativeStage :=
  rawNegativeStage_primrec.to_comp

theorem rawNegative_wellFormed_computable : Computable RawNegativeCode.wellFormed :=
  rawNegative_wellFormed_primrec.to_comp

theorem wellFormedNegativeStage_computable : Computable wellFormedNegativeStage :=
  wellFormedNegativeStage_primrec.to_comp

private def pieceTuple : RawTriangularPieceCode ≃ ℕ × ℕ where
  toFun c := (c.intervalCount, c.representativeCount)
  invFun c := ⟨c.1, c.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by cases c; rfl

instance instPrimcodableRawTriangularPieceCode : Primcodable RawTriangularPieceCode :=
  Primcodable.ofEquiv _ pieceTuple

theorem rawPiece_encoding_eq :
    instPrimcodableRawTriangularPieceCode.toEncodable =
      instEncodableRawTriangularPieceCode := rfl

theorem rawPiece_mk_primrec : Primrec (fun p : ℕ × ℕ =>
    RawTriangularPieceCode.mk p.1 p.2) :=
  show Primrec pieceTuple.symm from Primrec.of_equiv_symm

theorem rawPiece_decode_primrec :
    Primrec (@Encodable.decode RawTriangularPieceCode instEncodableRawTriangularPieceCode) :=
  Primrec.decode

theorem rawPiece_intervalCount_primrec : Primrec RawTriangularPieceCode.intervalCount :=
  Primrec.fst.comp (show Primrec pieceTuple from Primrec.of_equiv)

theorem rawPiece_representativeCount_primrec :
    Primrec RawTriangularPieceCode.representativeCount :=
  Primrec.snd.comp (show Primrec pieceTuple from Primrec.of_equiv)

theorem rawPiece_wellFormed_primrec : Primrec RawTriangularPieceCode.wellFormed := by
  refine (boolAnd_primrec.comp
      (positive_primrec.comp rawPiece_intervalCount_primrec)
      (positive_primrec.comp rawPiece_representativeCount_primrec)).of_eq ?_
  intro c
  simp only [RawTriangularPieceCode.wellFormed, Bool.decide_coe]

theorem rawPiece_wellFormed_computable : Computable RawTriangularPieceCode.wellFormed :=
  rawPiece_wellFormed_primrec.to_comp

private def triangularTuple : RawTriangularCode ≃ Bool × List RawTriangularPieceCode × ℕ where
  toFun c := (c.orientation, c.pieces, c.checkingRadius)
  invFun c := ⟨c.1, c.2.1, c.2.2⟩
  left_inv c := by cases c; rfl
  right_inv c := by rcases c with ⟨a, b, d⟩; rfl

instance instPrimcodableRawTriangularCode : Primcodable RawTriangularCode :=
  Primcodable.ofEquiv _ triangularTuple

theorem rawTriangular_encoding_eq :
    instPrimcodableRawTriangularCode.toEncodable = instEncodableRawTriangularCode := rfl

theorem rawTriangular_mk_primrec : Primrec (fun p : Bool × List RawTriangularPieceCode × ℕ =>
    RawTriangularCode.mk p.1 p.2.1 p.2.2) :=
  show Primrec triangularTuple.symm from Primrec.of_equiv_symm

theorem rawTriangular_decode_primrec :
    Primrec (@Encodable.decode RawTriangularCode instEncodableRawTriangularCode) :=
  Primrec.decode

theorem rawTriangular_orientation_primrec : Primrec RawTriangularCode.orientation :=
  Primrec.fst.comp (show Primrec triangularTuple from Primrec.of_equiv)

theorem rawTriangular_pieces_primrec : Primrec RawTriangularCode.pieces :=
  Primrec.fst.comp (Primrec.snd.comp
    (show Primrec triangularTuple from Primrec.of_equiv))

theorem rawTriangular_checkingRadius_primrec : Primrec RawTriangularCode.checkingRadius :=
  Primrec.snd.comp (Primrec.snd.comp
    (show Primrec triangularTuple from Primrec.of_equiv))

private theorem listNonempty_primrec {α : Type*} [Primcodable α] :
    Primrec (fun xs : List α => !xs.isEmpty) := by
  refine (Primrec.list_casesOn Primrec.id (Primrec.const false)
    (Primrec.const true).to₂).of_eq ?_
  intro xs
  cases xs <;> rfl

private theorem listAll_primrec {α : Type*} [Primcodable α]
    {p : α → Bool} (hp : Primrec p) : Primrec (List.all · p) := by
  refine (Primrec.list_foldr Primrec.id (Primrec.const true)
    (boolAnd_primrec.comp (hp.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq ?_
  intro xs
  change xs.foldr (fun a b => p a && b) true = xs.all p
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem rawTriangular_wellFormed_primrec : Primrec RawTriangularCode.wellFormed := by
  refine (boolAnd_primrec.comp
      (boolAnd_primrec.comp
        (listNonempty_primrec.comp rawTriangular_pieces_primrec)
        ((listAll_primrec rawPiece_wellFormed_primrec).comp rawTriangular_pieces_primrec))
      (positive_primrec.comp rawTriangular_checkingRadius_primrec)).of_eq ?_
  intro c
  simp only [RawTriangularCode.wellFormed, Bool.decide_coe]

theorem rawTriangular_wellFormed_computable : Computable RawTriangularCode.wellFormed :=
  rawTriangular_wellFormed_primrec.to_comp

end Tiling.AxisParallel.Decidability.CertificateCoding
