import Tiling.AxisParallel.Decidability.Certificates.FormulaTriangular
import Tiling.AxisParallel.Decidability.Certificates.FormulaOrientation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas.Native

open Tiling.AxisParallel.Decidability.Affine
open Tiling.AxisParallel.Terminal.Executable
open Triangular

attribute [local implicit_reducible] PositiveVerification.triangularPieceCount
  PositiveVerification.triangularPiece PositiveVerification.triangularHorizontalVariableCount
  PositiveVerification.triangularVerticalVariableCount

def eraseInterval {c : RawTriangularCode}
    (i : PositiveVerification.TriangularIntervalIndex c) : Index := (i.1.val, i.2.val)
def eraseRepresentative {c : RawTriangularCode}
    (i : PositiveVerification.TriangularRepresentativeIndex c) : Index := (i.1.val, i.2.val)
def eraseFinite {c : RawTriangularCode}
    {j : Fin (PositiveVerification.triangularPieceCount c)}
    (i : PositiveVerification.TriangularFiniteIndex c j) : FiniteIndex :=
  (i.1.val, i.2.1.val, i.2.2.val)

private theorem range_eq_map_fin (n : ℕ) :
    List.range n = (List.ofFn (fun i : Fin n => i)).map Fin.val := by
  apply List.ext_getElem <;> simp

@[simp] theorem triangularPiece_eq_native (c : RawTriangularCode)
    (j : Fin (PositiveVerification.triangularPieceCount c)) :
    triangularPiece c j.val = PositiveVerification.triangularPiece c j := by
  change c.pieces.getD j.val ⟨0, 0⟩ = c.pieces.get j
  rw [List.getD_eq_getElem _ _ j.isLt]
  rfl

theorem triangularIntervalIndices_eq_native (c : RawTriangularCode) :
    triangularIntervalIndices c =
      (PositiveVerification.triangularIntervalIndices c).map eraseInterval := by
  simp only [triangularIntervalIndices, PositiveVerification.triangularIntervalIndices,
    triangularPieceCount, PositiveVerification.triangularPieceCount]
  rw [range_eq_map_fin c.pieces.length]
  simp only [List.flatMap_map, List.map_flatMap]
  congr 1
  funext j
  rw [triangularPiece_eq_native c j, range_eq_map_fin]
  simp only [List.map_ofFn, Function.comp_def, eraseInterval]

theorem triangularRepresentativeIndices_eq_native (c : RawTriangularCode) :
    triangularRepresentativeIndices c =
      (PositiveVerification.triangularRepresentativeIndices c).map eraseRepresentative := by
  simp only [triangularRepresentativeIndices, PositiveVerification.triangularRepresentativeIndices,
    triangularPieceCount, PositiveVerification.triangularPieceCount]
  rw [range_eq_map_fin c.pieces.length]
  simp only [List.flatMap_map, List.map_flatMap]
  congr 1
  funext j
  rw [triangularPiece_eq_native c j, range_eq_map_fin]
  simp only [List.map_ofFn, Function.comp_def, eraseRepresentative]

theorem triangularFiniteIndices_eq_native (c : RawTriangularCode)
    (j : Fin (PositiveVerification.triangularPieceCount c)) :
    triangularFiniteIndices c j.val =
      (PositiveVerification.triangularFiniteIndices c j).map eraseFinite := by
  simp only [triangularFiniteIndices, PositiveVerification.triangularFiniteIndices,
    triangularPiece_eq_native]
  rw [range_eq_map_fin, range_eq_map_fin, range_eq_map_fin]
  simp only [List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def]
  simp only [List.map_ofFn, Function.comp_def, eraseFinite]

@[simp] theorem eraseInterval_inj {c : RawTriangularCode}
    (i j : PositiveVerification.TriangularIntervalIndex c) :
    eraseInterval i = eraseInterval j ↔ i = j := by
  constructor
  · intro h
    have he : i.1 = j.1 := Fin.ext (congrArg Prod.fst h)
    cases i with
    | mk a b =>
      cases j with
      | mk d e =>
        dsimp at he
        subst d
        have he' : b = e := Fin.ext (congrArg Prod.snd h)
        subst e
        rfl
  · rintro rfl
    rfl

@[simp] theorem eraseFinite_inj {c : RawTriangularCode}
    {j : Fin (PositiveVerification.triangularPieceCount c)}
    (i i' : PositiveVerification.TriangularFiniteIndex c j) :
    eraseFinite i = eraseFinite i' ↔ i = i' := by
  simp [eraseFinite, Prod.ext_iff, Fin.ext_iff]

@[simp] theorem pack_triH (C : RegionCode) (c : RawTriangularCode) (shift id : ℕ) :
    packAffine (PositiveVerification.triH C c shift id) = triH (encodeRegion C) c shift id := by
  rw [PositiveVerification.triH, pack_var]
  rfl

@[simp] theorem pack_triV (C : RegionCode) (c : RawTriangularCode) (shift id : ℕ) :
    packAffine (PositiveVerification.triV C c shift id) = triV (encodeRegion C) c shift id := by
  rw [PositiveVerification.triV, pack_var]
  rfl

@[simp] theorem pack_triangularCentreX (C : RegionCode) (c : RawTriangularCode) (shift : ℕ)
    (j : Fin (PositiveVerification.triangularPieceCount c))
    (i : PositiveVerification.TriangularFiniteIndex c j) :
    packAffine (PositiveVerification.triangularCentreX C c shift j i) =
      triangularCentreX (encodeRegion C) c shift j.val (eraseFinite i) := by
  simp only [PositiveVerification.triangularCentreX, pack_add, pack_intScale, pack_triH,
    triangularCentreX, eraseFinite, PositiveVerification.triangularRepresentativeXId,
    triangularRepresentativeXId, PositiveVerification.triangularRepresentativeOrdinal,
    triangularRepresentativeOrdinal, PositiveVerification.triangularTotalIntervalCount,
    triangularTotalIntervalCount, PositiveVerification.centeredInteger, centeredInteger,
    PositiveVerification.triangularBetaId, triangularBetaId]

@[simp] theorem pack_triangularCentreY (C : RegionCode) (c : RawTriangularCode) (shift : ℕ)
    (j : Fin (PositiveVerification.triangularPieceCount c))
    (i : PositiveVerification.TriangularFiniteIndex c j) :
    packAffine (PositiveVerification.triangularCentreY C c shift j i) =
      triangularCentreY (encodeRegion C) c shift j.val (eraseFinite i) := by
  simp only [PositiveVerification.triangularCentreY, pack_add, pack_intScale, pack_triV,
    triangularCentreY, eraseFinite, PositiveVerification.triangularRepresentativeYId,
    triangularRepresentativeYId, PositiveVerification.triangularRepresentativeOrdinal,
    triangularRepresentativeOrdinal, PositiveVerification.triangularPieceCount,
    triangularPieceCount, PositiveVerification.centeredInteger, centeredInteger,
    PositiveVerification.triangularAlphaId, triangularAlphaId,
    PositiveVerification.triangularShearId, triangularShearId]

@[simp] theorem triH_inputConstant_zero (C : RegionCode) (c : RawTriangularCode)
    (shift id : ℕ) : (PositiveVerification.triH C c shift id).inputConstant = Coeff.zero C := rfl

@[simp] theorem triV_inputConstant_zero (C : RegionCode) (c : RawTriangularCode)
    (shift id : ℕ) : (PositiveVerification.triV C c shift id).inputConstant = Coeff.zero C := rfl

@[simp] theorem pack_triH_scale (C : RegionCode) (c : RawTriangularCode)
    (shift id : ℕ) (q : ℚ) :
    packAffine (PositiveVerification.Expr.scale q (PositiveVerification.triH C c shift id)) =
      exprScale q (triH (encodeRegion C) c shift id) := by
  rw [pack_scale_zero q _ (by rfl), pack_triH]

@[simp] theorem pack_triV_scale (C : RegionCode) (c : RawTriangularCode)
    (shift id : ℕ) (q : ℚ) :
    packAffine (PositiveVerification.Expr.scale q (PositiveVerification.triV C c shift id)) =
      exprScale q (triV (encodeRegion C) c shift id) := by
  rw [pack_scale_zero q _ (by rfl), pack_triV]

@[simp] theorem pack_triangularBaseOpen (C : RegionCode) (c : RawTriangularCode)
    (shift : ℕ) (j : Fin (PositiveVerification.triangularPieceCount c)) {v : ℕ}
    (x : AffineExpr C (PositiveVerification.triangularHorizontalVariableCount c + shift)) :
    Affine.Native.packFormula
      (PositiveVerification.triangularBaseOpenFormula (v := v) C c shift j x) =
      triangularBaseOpenFormula (encodeRegion C) c shift j.val (packAffine x) := by
  simp only [PositiveVerification.triangularBaseOpenFormula, triangularBaseOpenFormula,
    pack_orList, List.map_flatMap, List.map_map, Function.comp_def,
    Affine.Native.packFormula_conjunction, pack_horizontalLt,
    pack_add, pack_triH_scale, pack_triH, triangularPiece_eq_native]
  rw [range_eq_map_fin]
  simp only [List.flatMap_map, PositiveVerification.triangularIntervalLeftId,
    PositiveVerification.triangularIntervalRightId, triangularIntervalLeftId,
    triangularIntervalRightId, PositiveVerification.triangularIntervalOrdinal,
    triangularIntervalOrdinal, PositiveVerification.triangularBetaId, triangularBetaId]

@[simp] theorem pack_triangularBaseClosed (C : RegionCode) (c : RawTriangularCode)
    (shift : ℕ) (j : Fin (PositiveVerification.triangularPieceCount c)) {v : ℕ}
    (x : AffineExpr C (PositiveVerification.triangularHorizontalVariableCount c + shift)) :
    Affine.Native.packFormula
      (PositiveVerification.triangularBaseClosedFormula (v := v) C c shift j x) =
      triangularBaseClosedFormula (encodeRegion C) c shift j.val (packAffine x) := by
  simp only [PositiveVerification.triangularBaseClosedFormula, triangularBaseClosedFormula,
    pack_orList, List.map_flatMap, List.map_map, Function.comp_def,
    Affine.Native.packFormula_conjunction, pack_horizontalLe,
    pack_add, pack_triH_scale, pack_triH, triangularPiece_eq_native]
  rw [range_eq_map_fin]
  simp only [List.flatMap_map, PositiveVerification.triangularIntervalLeftId,
    PositiveVerification.triangularIntervalRightId, triangularIntervalLeftId,
    triangularIntervalRightId, PositiveVerification.triangularIntervalOrdinal,
    triangularIntervalOrdinal, PositiveVerification.triangularBetaId, triangularBetaId]

@[simp] theorem pack_triangularSingleInput (C : RegionCode) (n : ℕ) (a : Fin C.vertexCount) :
    packAffine (PositiveVerification.Expr.input n (Coeff.single a 1)) =
      affineInput n (basisArray C.vertexCount a.val 1) := by
  rw [pack_input, basisArray_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [Coeff.single, Fin.ext_iff, eq_comm]

@[simp] theorem pack_diameterInput (C : RegionCode) (n : ℕ) (a b : Fin C.vertexCount) :
    packAffine (PositiveVerification.Expr.input n
      (Coeff.sub (Coeff.single a 1) (Coeff.single b 1))) =
      diameterInput (encodeRegion C) n a.val b.val := by
  have he : PositiveVerification.Expr.input n (Coeff.sub (Coeff.single a 1)
      (Coeff.single b 1)) = PositiveVerification.Expr.sub
      (PositiveVerification.Expr.input n (Coeff.single a 1))
      (PositiveVerification.Expr.input n (Coeff.single b 1)) := by
    dsimp only [PositiveVerification.Expr.input, PositiveVerification.Expr.sub,
      PositiveVerification.Expr.add, PositiveVerification.Expr.neg,
      Coeff.sub, Coeff.add, Coeff.neg]
    congr 1
    funext i
    simp
  rw [he, pack_sub, pack_triangularSingleInput, pack_triangularSingleInput]
  rfl

theorem triangularBody_eq_pack (C : RegionCode) (c : RawTriangularCode) :
    triangularBody (encodeRegion C) c =
      Affine.Native.packFormula (PositiveVerification.triangularBody C c) := by
  symm
  dsimp only [PositiveVerification.triangularBody, triangularBody]
  simp only [pack_andList, pack_orList, pack_implication, pack_forallHorizontal,
    pack_forallVertical, pack_horizontalLt, pack_verticalLt, pack_horizontalLe, pack_verticalLe,
    Affine.Native.packFormula_conjunction,
    Affine.Native.packFormula_disjunction,
    Affine.Native.packFormula_truth,
    pack_sameCentre, pack_cellNonoverlap, pack_openCell, pack_closedCell,
    pack_triangularCentreX, pack_triangularCentreY, pack_diameterInput,
    pack_triH, pack_triV, pack_neg, pack_zero, pack_var,
    pack_intScale, pack_triangularBaseOpen, pack_triangularBaseClosed,
    triangularIntervalIndices_eq_native, triangularRepresentativeIndices_eq_native,
    encodeRegion_vertexCount, encodeRegion_cellCount,
    range_eq_map_fin, apply_ite,
    List.map_flatMap, List.flatMap_map, List.map_map, List.map_cons,
    List.map_nil, List.map_append, Function.comp_def, eraseInterval_inj]
  simp only [PositiveVerification.triangularHorizontalVariableCount,
    PositiveVerification.triangularVerticalVariableCount, triangularHorizontalVariableCount,
    triangularVerticalVariableCount, PositiveVerification.triangularTotalIntervalCount,
    PositiveVerification.triangularTotalRepresentativeCount, triangularTotalIntervalCount,
    triangularTotalRepresentativeCount, PositiveVerification.triangularPieceCount,
    triangularPieceCount, PositiveVerification.triangularBetaId, triangularBetaId,
    PositiveVerification.triangularAlphaId, triangularAlphaId,
    PositiveVerification.triangularIntervalLeftId, triangularIntervalLeftId,
    PositiveVerification.triangularIntervalRightId, triangularIntervalRightId,
    PositiveVerification.triangularRepresentativeXId, triangularRepresentativeXId,
    PositiveVerification.triangularRepresentativeYId, triangularRepresentativeYId,
    PositiveVerification.triangularIntervalOrdinal, triangularIntervalOrdinal,
    PositiveVerification.triangularRepresentativeOrdinal, triangularRepresentativeOrdinal,
    PositiveVerification.triangularShearId, triangularShearId, eraseInterval,
    eraseRepresentative]
  simp only [triangularFiniteIndices_eq_native, List.flatMap_map, List.map_map,
    Function.comp_def, eraseFinite_inj]

theorem triangularSlab_eq_pack (C : RegionCode) (c : RawTriangularCode) :
    triangularSlabFormula (encodeRegion C) c =
      Affine.Native.packFormula
        (PositiveVerification.triangularSlabFormula C c) := by
  cases hw : c.wellFormed with
  | false => simp only [triangularSlabFormula, PositiveVerification.triangularSlabFormula,
      hw, Bool.false_eq_true, if_false, Affine.Native.packFormula_falsity]
  | true =>
    simp only [triangularSlabFormula, PositiveVerification.triangularSlabFormula, hw,
      if_true, triangularBody_eq_pack]
    exact (pack_close (PositiveVerification.triangularBody C c)).symm

end Tiling.AxisParallel.Decidability.CertificateFormulas.Native
