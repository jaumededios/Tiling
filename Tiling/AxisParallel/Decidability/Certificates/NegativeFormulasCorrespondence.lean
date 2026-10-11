import Tiling.AxisParallel.Decidability.Certificates.NegativeFormulas

/-!
# Exact correspondence of finite negative-certificate formulas

Packing the native local-cover syntax gives exactly the finite runtime code.
Bounds retain every integer coefficient, and the finite enumerations preserve
native index order. These statements are code equalities, rather than only
agreement of the formulas' truth values.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.NegativeFormulas.Native

open Tiling.AxisParallel.Terminal.Executable
open Tiling.AxisParallel.Decidability.Affine
open Affine.Native
open CertificateFormulas
open CertificateFormulas.Native

/-- Four native coefficient arrays in the runtime bound order. -/
def encodeBound {C : RegionCode} (B : LocalCoverSearch.LocalBoundCode C) : Bounds :=
  (List.ofFn B.horizontalDiameter, List.ofFn B.verticalDiameter,
    List.ofFn B.horizontalWidth, List.ofFn B.verticalWidth)

@[simp] theorem pack_listAnd {C : RegionCode} {h v : ℕ} (fs : List (Formula C h v)) :
    packFormula (LocalCoverSearch.listAnd fs) = andList (fs.map packFormula) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change packFormula (.conjunction f (LocalCoverSearch.listAnd fs)) =
      conjunction (packFormula f) (andList (fs.map packFormula))
    rw [packFormula_conjunction, ih]

@[simp] theorem pack_listOr {C : RegionCode} {h v : ℕ} (fs : List (Formula C h v)) :
    packFormula (LocalCoverSearch.listOr fs) = orList (fs.map packFormula) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    change packFormula (.disjunction f (LocalCoverSearch.listOr fs)) =
      disjunction (packFormula f) (orList (fs.map packFormula))
    rw [packFormula_disjunction, ih]

@[simp] theorem pack_existsAllHorizontal {C : RegionCode} {v : ℕ} (h : ℕ)
    (f : Formula C h v) :
    packFormula (LocalCoverSearch.existsAllHorizontal h f) =
      closeHorizontal h (packFormula f) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    simp only [LocalCoverSearch.existsAllHorizontal, ih, packFormula_existsHorizontal,
      closeHorizontal, Function.iterate_succ_apply]

@[simp] theorem pack_existsAllVertical {C : RegionCode} (v : ℕ) (f : Formula C 0 v) :
    packFormula (LocalCoverSearch.existsAllVertical v f) = closeVertical v (packFormula f) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    simp only [LocalCoverSearch.existsAllVertical, ih, packFormula_existsVertical,
      closeVertical, Function.iterate_succ_apply]

/-- Replace bounded natural-number enumeration by native finite-index enumeration. -/
theorem range_map_eq_ofFn {α : Type*} {n : ℕ} (f : ℕ → α) (g : Fin n → α)
    (h : ∀ i : Fin n, f i = g i) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simpa using h ⟨i, by simpa using hi⟩

theorem range_flatMap_eq_ofFn {α : Type*} {m n : ℕ} (f : ℕ → ℕ → α)
    (g : Fin m → Fin n → α) (h : ∀ (i : Fin m) (j : Fin n), f i j = g i j) :
    (List.range m).flatMap (fun i => (List.range n).map (f i)) =
      (List.ofFn fun i => List.ofFn (g i)).flatten := by
  rw [List.flatMap_def]
  congr 1
  apply range_map_eq_ofFn
  intro i
  exact range_map_eq_ofFn (f i) (g i) (h i)

@[simp] theorem constantExpr_eq_pack {C : RegionCode} (m : ℕ) (a : Coeff C) :
    constantExpr m (List.ofFn a) = packAffine (LocalCoverSearch.constantExpr C m a) := by
  simp only [constantExpr, List.map_ofFn]
  exact affineInput_eq_pack a

@[simp] theorem variableExpr_eq_pack (C : RegionCode) (m : ℕ) (i : Fin m) :
    variableExpr (encodeRegion C) m i = packAffine (LocalCoverSearch.variableExpr C m i) := by
  simpa only [variableExpr, encodeRegion, LocalCoverSearch.variableExpr, Fin.ext_iff] using
    (affineVariable_eq_pack (C := C) m i)

@[simp] theorem constantExpr_scale_eq_pack {C : RegionCode} (m N : ℕ) (a : Coeff C) :
    exprScale (N : ℚ) (constantExpr m (List.ofFn a)) =
      packAffine (LocalCoverSearch.constantExpr C m (Coeff.nsmul N a)) := by
  rw [constantExpr_eq_pack]
  change exprScale (N : ℚ) (packAffine (⟨fun _ => 0, a⟩ : AffineExpr C m)) =
    packAffine (⟨fun _ => 0, fun i => (N : ℤ) * a i⟩ : AffineExpr C m)
  simpa using packAffine_intScale (N : ℤ) (⟨fun _ => 0, a⟩ : AffineExpr C m)

@[simp] theorem constantExpr_neg_eq_pack {C : RegionCode} (m : ℕ) (a : Coeff C) :
    exprNeg (packAffine (LocalCoverSearch.constantExpr C m a)) =
      packAffine (LocalCoverSearch.constantExpr C m (Coeff.neg a)) := by
  change exprNeg (packAffine (⟨fun _ => 0, a⟩ : AffineExpr C m)) =
    packAffine (⟨fun _ => 0, fun i => -a i⟩ : AffineExpr C m)
  simpa using packAffine_neg (⟨fun _ => 0, a⟩ : AffineExpr C m)

@[simp] theorem translatedExpr_left_eq_pack (C : RegionCode) (m : ℕ)
    (i : Fin m) (e : Fin C.cellCount) :
    translatedExpr (encodeRegion C) m i 0 e =
      packAffine (LocalCoverSearch.translatedExpr i (Coeff.cellLeft e)) := by
  unfold translatedExpr
  rw [(cellSelector_encodeRegion C e).1]
  simp only [encodeRegion, basisArray_eq_ofFn]
  simp [packAffine, packExpr, AffineCompiler.LinearExpr.ofAffine,
    LocalCoverSearch.translatedExpr, Coeff.cellLeft, Coeff.single, Fin.ext_iff]

@[simp] theorem translatedExpr_right_eq_pack (C : RegionCode) (m : ℕ)
    (i : Fin m) (e : Fin C.cellCount) :
    translatedExpr (encodeRegion C) m i 1 e =
      packAffine (LocalCoverSearch.translatedExpr i (Coeff.cellRight e)) := by
  unfold translatedExpr
  rw [(cellSelector_encodeRegion C e).2.1]
  simp only [encodeRegion, basisArray_eq_ofFn]
  simp [packAffine, packExpr, AffineCompiler.LinearExpr.ofAffine,
    LocalCoverSearch.translatedExpr, Coeff.cellRight, Coeff.single, Fin.ext_iff]

@[simp] theorem translatedExpr_bottom_eq_pack (C : RegionCode) (m : ℕ)
    (i : Fin m) (e : Fin C.cellCount) :
    translatedExpr (encodeRegion C) m i 2 e =
      packAffine (LocalCoverSearch.translatedExpr i (Coeff.cellBottom e)) := by
  unfold translatedExpr
  rw [(cellSelector_encodeRegion C e).2.2.1]
  simp only [encodeRegion, basisArray_eq_ofFn]
  simp [packAffine, packExpr, AffineCompiler.LinearExpr.ofAffine,
    LocalCoverSearch.translatedExpr, Coeff.cellBottom, Coeff.single, Fin.ext_iff]

@[simp] theorem translatedExpr_top_eq_pack (C : RegionCode) (m : ℕ)
    (i : Fin m) (e : Fin C.cellCount) :
    translatedExpr (encodeRegion C) m i 3 e =
      packAffine (LocalCoverSearch.translatedExpr i (Coeff.cellTop e)) := by
  unfold translatedExpr
  rw [(cellSelector_encodeRegion C e).2.2.2]
  simp only [encodeRegion, basisArray_eq_ofFn]
  simp [packAffine, packExpr, AffineCompiler.LinearExpr.ofAffine,
    LocalCoverSearch.translatedExpr, Coeff.cellTop, Coeff.single, Fin.ext_iff]

@[simp] theorem distinctCentres_eq_pack (C : RegionCode) (m : ℕ) (i j : Fin m) :
    distinctCentres (encodeRegion C) m i j =
      packFormula (LocalCoverSearch.distinctCentres C m i j) := by
  rw [distinctCentres, LocalCoverSearch.distinctCentres, pack_listOr]
  simp only [List.map_cons, List.map_nil, ← horizontalLt_eq_pack, ← verticalLt_eq_pack,
    variableExpr_eq_pack, LocalCoverSearch.horizontalLt, LocalCoverSearch.verticalLt]

@[simp] theorem cellPairSeparated_eq_pack (C : RegionCode) (m : ℕ) (i j : Fin m)
    (a b : Fin C.cellCount) :
    cellPairSeparated (encodeRegion C) m i j a b =
      packFormula (LocalCoverSearch.cellPairSeparated C m i j a b) := by
  rw [cellPairSeparated, LocalCoverSearch.cellPairSeparated, pack_listOr]
  simp only [List.map_cons, List.map_nil, ← horizontalLe_eq_pack, ← verticalLe_eq_pack,
    translatedExpr_left_eq_pack, translatedExpr_right_eq_pack,
    translatedExpr_bottom_eq_pack, translatedExpr_top_eq_pack,
    LocalCoverSearch.horizontalLe, LocalCoverSearch.verticalLe]

@[simp] theorem cellPairsSeparated_eq_pack (C : RegionCode) (m : ℕ) (i j : Fin m) :
    cellPairsSeparated (encodeRegion C) m i j =
      packFormula (LocalCoverSearch.cellPairsSeparated C m i j) := by
  rw [cellPairsSeparated, LocalCoverSearch.cellPairsSeparated, pack_listAnd]
  have hlen : (encodeRegion C).2.length = C.cellCount := by simp [encodeRegion]
  simp only [hlen, List.map_flatten, List.map_ofFn, Function.comp_def]
  apply congrArg andList
  apply range_flatMap_eq_ofFn
  intro a b
  exact cellPairSeparated_eq_pack C m i j a b

@[simp] theorem centrePairPacking_eq_pack (C : RegionCode) (m : ℕ) (i j : Fin m) :
    centrePairPacking (encodeRegion C) m i j =
      packFormula (LocalCoverSearch.centrePairPacking C m i j) := by
  by_cases hij : i = j
  · simp [centrePairPacking, LocalCoverSearch.centrePairPacking, hij]
  · have hnat : (i : ℕ) ≠ j := by simpa [Fin.ext_iff] using hij
    simp only [centrePairPacking, hnat, if_false, LocalCoverSearch.centrePairPacking,
      hij, packFormula_conjunction, distinctCentres_eq_pack, cellPairsSeparated_eq_pack]

@[simp] theorem packingFormula_eq_pack (C : RegionCode) (m : ℕ) :
    packingFormula (encodeRegion C) m = packFormula (LocalCoverSearch.packingFormula C m) := by
  rw [packingFormula, LocalCoverSearch.packingFormula, pack_listAnd]
  simp only [List.map_flatten, List.map_ofFn, Function.comp_def]
  apply congrArg andList
  apply range_flatMap_eq_ofFn
  intro i j
  exact centrePairPacking_eq_pack C m i j

@[simp] theorem withinBoundHorizontal_eq_pack (C : RegionCode) (m N : ℕ)
    (a : Coeff C) (i : Fin m) :
    withinBoundHorizontal (encodeRegion C) m N (List.ofFn a) i =
      packFormula (LocalCoverSearch.withinBoundHorizontal C m N a i) := by
  rw [withinBoundHorizontal, LocalCoverSearch.withinBoundHorizontal]
  simp only [constantExpr_scale_eq_pack, constantExpr_neg_eq_pack,
    variableExpr_eq_pack, packFormula_conjunction, LocalCoverSearch.horizontalLe,
    ← horizontalLe_eq_pack]

@[simp] theorem withinBoundVertical_eq_pack (C : RegionCode) (m N : ℕ)
    (a : Coeff C) (i : Fin m) :
    withinBoundVertical (encodeRegion C) m N (List.ofFn a) i =
      packFormula (LocalCoverSearch.withinBoundVertical C m N a i) := by
  rw [withinBoundVertical, LocalCoverSearch.withinBoundVertical]
  simp only [constantExpr_scale_eq_pack, constantExpr_neg_eq_pack,
    variableExpr_eq_pack, packFormula_conjunction, LocalCoverSearch.verticalLe,
    ← verticalLe_eq_pack]

@[simp] theorem relevanceFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (N m : ℕ) :
    relevanceFormula (encodeRegion C) (encodeBound B) N m =
      packFormula (LocalCoverSearch.relevanceFormula C B N m) := by
  rw [relevanceFormula, LocalCoverSearch.relevanceFormula, pack_listAnd]
  simp only [encodeBound, List.map_ofFn, Function.comp_def]
  apply congrArg andList
  apply range_map_eq_ofFn
  intro i
  simp only [withinBoundHorizontal_eq_pack, withinBoundVertical_eq_pack,
    packFormula_conjunction]

@[simp] theorem variableExpr_zero_eq_pack (C : RegionCode) (m : ℕ) :
    variableExpr (encodeRegion C) (m + 1) 0 =
      packAffine (LocalCoverSearch.variableExpr C (m + 1) 0) :=
  variableExpr_eq_pack C (m + 1) 0

@[simp] theorem outsideClosedCell_eq_pack (C : RegionCode) (m : ℕ)
    (i : Fin m) (a : Fin C.cellCount) :
    outsideClosedCell (encodeRegion C) m i a =
      packFormula (LocalCoverSearch.outsideClosedCell C m i a) := by
  rw [outsideClosedCell, LocalCoverSearch.outsideClosedCell,
    packFormula_negation, pack_listAnd]
  simp only [List.map_cons, List.map_nil, LocalCoverSearch.horizontalLe,
    LocalCoverSearch.verticalLe, ← horizontalLe_eq_pack, ← verticalLe_eq_pack]
  rw [show (i : ℕ) + 1 = (i.succ : ℕ) from rfl]
  simp only [translatedExpr_left_eq_pack, translatedExpr_right_eq_pack,
    translatedExpr_bottom_eq_pack, translatedExpr_top_eq_pack, variableExpr_zero_eq_pack]

@[simp] theorem uncoveredPointBody_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (N m : ℕ) :
    uncoveredPointBody (encodeRegion C) (encodeBound B) N m =
      packFormula (LocalCoverSearch.uncoveredPointBody C B N m) := by
  rw [uncoveredPointBody, LocalCoverSearch.uncoveredPointBody, pack_listAnd]
  have hlen : (encodeRegion C).2.length = C.cellCount := by simp [encodeRegion]
  simp only [encodeBound, hlen, List.map_append, List.map_cons, List.map_nil,
    List.map_flatten, List.map_ofFn, Function.comp_def, LocalCoverSearch.horizontalLt,
    LocalCoverSearch.verticalLt, ← horizontalLt_eq_pack, ← verticalLt_eq_pack]
  simp only [constantExpr_scale_eq_pack, constantExpr_neg_eq_pack, variableExpr_zero_eq_pack]
  apply congrArg andList
  congr 1
  apply range_flatMap_eq_ofFn
  intro i a
  exact outsideClosedCell_eq_pack C m i a

@[simp] theorem coverageFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (N m : ℕ) :
    coverageFormula (encodeRegion C) (encodeBound B) N m =
      packFormula (LocalCoverSearch.coverageFormula C B N m) := by
  simp only [coverageFormula, LocalCoverSearch.coverageFormula, packFormula_negation,
    packFormula_existsHorizontal, packFormula_existsVertical, uncoveredPointBody_eq_pack]

/-- The complete finite local-cover code is the exact packed native formula. -/
theorem localCoverFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (N m : ℕ) :
    localCoverFormula (encodeRegion C) (encodeBound B) N m =
      packFormula (LocalCoverSearch.localCoverFormula C B N m) := by
  simp only [localCoverFormula, LocalCoverSearch.localCoverFormula,
    pack_existsAllVertical, pack_existsAllHorizontal, pack_listAnd,
    List.map_cons, List.map_nil, packingFormula_eq_pack, relevanceFormula_eq_pack,
    coverageFormula_eq_pack]

/-- The finite subdivision comparison code is the exact packed native formula. -/
theorem positiveSubdivisionFormula_eq_pack (C : RegionCode)
    (B : LocalCoverSearch.LocalBoundCode C) (c : RawNegativeCode) :
    positiveSubdivisionFormula (encodeBound B) c.boxIndex
      c.horizontalSubdivisions c.verticalSubdivisions =
      packFormula (LocalCoverSearch.positiveSubdivisionFormula C B c) := by
  simp only [positiveSubdivisionFormula, LocalCoverSearch.positiveSubdivisionFormula,
    encodeBound, packFormula_conjunction, LocalCoverSearch.horizontalLt,
    LocalCoverSearch.verticalLt, ← horizontalLt_eq_pack, ← verticalLt_eq_pack,
    constantExpr_scale_eq_pack]

end Tiling.AxisParallel.Decidability.NegativeFormulas.Native
