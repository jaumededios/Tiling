import Tiling.AxisParallel.Decidability.Certificates.FormulaLattice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.CertificateFormulas.Native
open Tiling.AxisParallel.Decidability.Affine
open Tiling.AxisParallel.Terminal.Executable

-- Count normalization must remain available when matching dependently typed expressions.
attribute [local implicit_reducible] PositiveVerification.latticeHorizontalVariableCount
  PositiveVerification.latticeVerticalVariableCount

def eraseLatticeIndex {c : RawLatticeCode}
    (i : PositiveVerification.LatticeFiniteIndex c) : LatticeIndex :=
  (i.1.val, i.2.1.val, i.2.2.val)

private theorem range_eq_map_fin (n : ℕ) :
    List.range n = (List.ofFn (fun i : Fin n => i)).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem latticeIndices_eq_native (c : RawLatticeCode) :
    latticeIndices c = (PositiveVerification.latticeFiniteIndices c).map eraseLatticeIndex := by
  have he : ((List.range c.representativeCount).flatMap fun r =>
      (List.range (2 * c.firstIndexBound + 1)).flatMap fun n =>
        (List.range (2 * c.secondIndexBound + 1)).map fun m => (r, n, m)) =
      (((List.ofFn fun r : Fin c.representativeCount => r).flatMap fun r =>
        (List.ofFn fun n : PositiveVerification.LatticeBoundedInteger c.firstIndexBound => n)
          |>.flatMap fun n =>
          List.ofFn fun m : PositiveVerification.LatticeBoundedInteger c.secondIndexBound =>
            (r, n, m))).map eraseLatticeIndex := by
    simp only [range_eq_map_fin, List.flatMap_map, List.map_flatMap, List.map_map,
      Function.comp_def]
    simp only [List.map_ofFn, eraseLatticeIndex, Function.comp_def]
  rw [latticeIndices, he, List.filter_map]
  rfl

@[simp] theorem pack_latH (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) :
    packAffine (PositiveVerification.latH C c shift id) = latH (encodeRegion C) c shift id := by
  simp only [PositiveVerification.latH, pack_var, latH,
    PositiveVerification.latticeHorizontalVariableCount,
    latticeHorizontalVariableCount, encodeRegion]

@[simp] theorem pack_latV (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) :
    packAffine (PositiveVerification.latV C c shift id) = latV (encodeRegion C) c shift id := by
  simp only [PositiveVerification.latV, pack_var, latV,
    PositiveVerification.latticeVerticalVariableCount,
    latticeVerticalVariableCount, encodeRegion]

@[simp] theorem latH_inputConstant_zero (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) :
    (PositiveVerification.latH C c shift id).inputConstant = Coeff.zero C := rfl

@[simp] theorem latV_inputConstant_zero (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) :
    (PositiveVerification.latV C c shift id).inputConstant = Coeff.zero C := rfl

@[simp] theorem pack_latHScale (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) (q : ℚ) :
    packAffine (PositiveVerification.Expr.scale q (PositiveVerification.latH C c shift id)) =
      exprScale q (latH (encodeRegion C) c shift id) := by
  rw [pack_scale_zero q _ rfl, pack_latH]

@[simp] theorem pack_latVScale (C : RegionCode) (c : RawLatticeCode) (shift id : ℕ) (q : ℚ) :
    packAffine (PositiveVerification.Expr.scale q (PositiveVerification.latV C c shift id)) =
      exprScale q (latV (encodeRegion C) c shift id) := by
  rw [pack_scale_zero q _ rfl, pack_latV]

@[simp] theorem pack_latticeCentreX (C : RegionCode) (c : RawLatticeCode) (shift : ℕ)
    (i : PositiveVerification.LatticeFiniteIndex c) :
    packAffine (PositiveVerification.latticeCentreX C c shift i) =
      latticeCentreX (encodeRegion C) c shift (eraseLatticeIndex i) := by
  simp only [PositiveVerification.latticeCentreX, latticeCentreX, pack_add,
    pack_intScale, pack_latH, PositiveVerification.centeredInteger, eraseLatticeIndex,
    PositiveVerification.latticeRepresentativeXId, latticeRepresentativeXId,
    PositiveVerification.latticeFirstPeriodXId, PositiveVerification.latticeSecondPeriodXId]

@[simp] theorem pack_latticeCentreY (C : RegionCode) (c : RawLatticeCode) (shift : ℕ)
    (i : PositiveVerification.LatticeFiniteIndex c) :
    packAffine (PositiveVerification.latticeCentreY C c shift i) =
      latticeCentreY (encodeRegion C) c shift (eraseLatticeIndex i) := by
  simp only [PositiveVerification.latticeCentreY, latticeCentreY, pack_add,
    pack_intScale, pack_latV, PositiveVerification.centeredInteger, eraseLatticeIndex,
    PositiveVerification.latticeRepresentativeYId, latticeRepresentativeYId,
    PositiveVerification.latticeFirstPeriodYId, PositiveVerification.latticeSecondPeriodYId]

@[simp] theorem eraseLatticeIndex_inj {c : RawLatticeCode}
    (i j : PositiveVerification.LatticeFiniteIndex c) :
    eraseLatticeIndex i = eraseLatticeIndex j ↔ i = j := by
  simp [eraseLatticeIndex, Prod.ext_iff, Fin.ext_iff]

@[simp] theorem pack_singleInput (C : RegionCode) (n : ℕ) (a : Fin C.vertexCount) :
    packAffine (PositiveVerification.Expr.input n (Coeff.single a 1)) =
      affineInput n (basisArray C.vertexCount a.val 1) := by
  rw [pack_input, basisArray_eq_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext i
  simp [Coeff.single, Fin.ext_iff, eq_comm]

@[simp] theorem pack_vertexDifference (C : RegionCode) (n : ℕ)
    (a b : Fin C.vertexCount) :
    packAffine (PositiveVerification.Expr.input n (Coeff.sub (Coeff.single a 1)
      (Coeff.single b 1))) = vertexDifference (encodeRegion C) n a.val b.val := by
  have he : PositiveVerification.Expr.input n (Coeff.sub (Coeff.single a 1)
      (Coeff.single b 1)) =
      PositiveVerification.Expr.sub (PositiveVerification.Expr.input n (Coeff.single a 1))
        (PositiveVerification.Expr.input n (Coeff.single b 1)) := by
    dsimp only [PositiveVerification.Expr.input, PositiveVerification.Expr.sub,
      PositiveVerification.Expr.add, PositiveVerification.Expr.neg,
      Coeff.sub, Coeff.add, Coeff.neg]
    congr 1
    · funext i
      simp
  rw [he, pack_sub, pack_singleInput, pack_singleInput]
  rfl

theorem latticeBody_eq_pack (C : RegionCode) (c : RawLatticeCode) :
    latticeBody (encodeRegion C) c =
      Affine.Native.packFormula (PositiveVerification.latticeBody C c) := by
  symm
  dsimp only [PositiveVerification.latticeBody, latticeBody]
  simp only [pack_andList, pack_orList, pack_implication, pack_forallHorizontal,
    pack_forallVertical, pack_horizontalLt, pack_verticalLt, pack_horizontalLe, pack_verticalLe,
    Affine.Native.packFormula_disjunction,
    Affine.Native.packFormula_truth,
    pack_sameCentre, pack_cellNonoverlap, pack_closedCell,
    pack_latticeCentreX, pack_latticeCentreY, pack_vertexDifference,
    pack_latH, pack_latV, pack_add, pack_sub, pack_neg, pack_zero, pack_var,
    pack_intScale, pack_latHScale, pack_latVScale,
    latticeIndices_eq_native, range_eq_map_fin, List.map_flatMap, List.flatMap_map,
    List.map_map, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.map_append, List.append_nil, List.nil_append, List.cons_append,
    Function.comp_def, eraseLatticeIndex_inj, apply_ite,
    PositiveVerification.latticeHorizontalVariableCount,
    PositiveVerification.latticeVerticalVariableCount, latticeHorizontalVariableCount,
    latticeVerticalVariableCount, PositiveVerification.latticeFirstPeriodXId,
    PositiveVerification.latticeSecondPeriodXId, PositiveVerification.latticeFirstPeriodYId,
    PositiveVerification.latticeSecondPeriodYId, latticeFirstPeriodXId,
    latticeSecondPeriodXId, latticeFirstPeriodYId, latticeSecondPeriodYId,
    PositiveVerification.latticeHorizontalBoundId, PositiveVerification.latticeVerticalBoundId,
    PositiveVerification.latticeFirstPeriodAbsoluteXBoundId, latticeHorizontalBoundId,
    latticeVerticalBoundId, latticeFirstPeriodAbsoluteXBoundId,
    PositiveVerification.latticeRepresentativeXId, PositiveVerification.latticeRepresentativeYId,
    latticeRepresentativeXId, latticeRepresentativeYId, encodeRegion, List.length_ofFn,
    Int.cast_one, Int.cast_neg]

theorem latticeCertificate_eq_pack (C : RegionCode) (c : RawLatticeCode) :
    latticeCertificate (encodeRegion C) c =
      Affine.Native.packFormula
        (PositiveVerification.latticeCertificateFormula C c) := by
  cases hw : c.wellFormed <;>
    simp only [latticeCertificate, PositiveVerification.latticeCertificateFormula, hw,
      Bool.false_eq_true, eq_self, Bool.cond_false, Bool.cond_true, if_false, if_true,
      Affine.Native.packFormula_falsity,
      pack_close, close, latticeBody_eq_pack, latticeHorizontalVariableCount,
      latticeVerticalVariableCount, PositiveVerification.latticeHorizontalVariableCount,
      PositiveVerification.latticeVerticalVariableCount]

/-- The production lattice formula itself has a certified computable finite encoding. -/
theorem nativeLatticeCertificate_computable (C : RegionCode) :
    Computable (fun c : RawLatticeCode => Affine.Native.packFormula
      (PositiveVerification.latticeCertificateFormula C c)) := by
  have hc := latticeCertificate_computable.comp
    ((Computable.const (encodeRegion C)).pair Computable.id)
  exact hc.of_eq (latticeCertificate_eq_pack C)

end Tiling.AxisParallel.Decidability.CertificateFormulas.Native
