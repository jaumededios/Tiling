import Tiling.AxisParallel.Decidability.Certificates.NegativeFormulas
import Tiling.AxisParallel.Decidability.Certificates.FormulaComputability

/-! Computability of the finite local-cover formula constructors. -/

set_option autoImplicit false
set_option warningAsError true

namespace Tiling.AxisParallel.Decidability.NegativeFormulas

open CertificateFormulas

@[fun_prop] theorem c_cellSelector {α : Type*} [Primcodable α]
    (r : α → RegionInput) (s i : α → ℕ)
    (hr : Computable r) (hs : Computable s) (hi : Computable i) :
    Computable (fun x => cellSelector (r x) (s x) (i x)) :=
  cellSelector_primrec.to_comp.comp (hr.pair (hs.pair hi))

@[fun_prop] theorem c_constantExpr {α : Type*} [Primcodable α]
    (m : α → ℕ) (c : α → List ℤ)
    (hm : Computable m) (hc : Computable c) :
    Computable (fun x => constantExpr (m x) (c x)) := by
  unfold constantExpr
  fun_prop

@[fun_prop] theorem c_variableExpr {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) :
    Computable (fun x => variableExpr (r x) (m x) (i x)) := by
  unfold variableExpr
  fun_prop

@[fun_prop] theorem c_translatedExpr {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (s : α → ℕ) (a : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (hs : Computable s)
    (ha : Computable a) :
    Computable (fun x => translatedExpr (r x) (m x) (i x) (s x) (a x)) := by
  unfold translatedExpr
  fun_prop

@[fun_prop] theorem c_distinctCentres {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (j : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (hj : Computable j) :
    Computable (fun x => distinctCentres (r x) (m x) (i x) (j x)) := by
  unfold distinctCentres
  fun_prop

@[fun_prop] theorem c_cellPairSeparated {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (j : α → ℕ) (a : α → ℕ) (b : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (hj : Computable j)
    (ha : Computable a) (hb : Computable b) :
    Computable (fun x => cellPairSeparated (r x) (m x) (i x) (j x) (a x) (b x)) := by
  unfold cellPairSeparated
  fun_prop

@[fun_prop] theorem c_cellPairsSeparated {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (j : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (hj : Computable j) :
    Computable (fun x => cellPairsSeparated (r x) (m x) (i x) (j x)) := by
  unfold cellPairsSeparated
  fun_prop

@[fun_prop] theorem c_centrePairPacking {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (j : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (hj : Computable j) :
    Computable (fun x => centrePairPacking (r x) (m x) (i x) (j x)) := by
  unfold centrePairPacking
  fun_prop

@[fun_prop] theorem c_packingFormula {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ)
    (hr : Computable r) (hm : Computable m) :
    Computable (fun x => packingFormula (r x) (m x)) := by
  unfold packingFormula
  fun_prop

@[fun_prop] theorem c_withinBoundHorizontal {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (N : α → ℕ) (b : α → List ℤ) (i : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hN : Computable N) (hb : Computable b)
    (hi : Computable i) :
    Computable (fun x => withinBoundHorizontal (r x) (m x) (N x) (b x) (i x)) := by
  unfold withinBoundHorizontal
  fun_prop

@[fun_prop] theorem c_withinBoundVertical {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (N : α → ℕ) (b : α → List ℤ) (i : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hN : Computable N) (hb : Computable b)
    (hi : Computable i) :
    Computable (fun x => withinBoundVertical (r x) (m x) (N x) (b x) (i x)) := by
  unfold withinBoundVertical
  fun_prop

@[fun_prop] theorem c_relevanceFormula {α : Type*} [Primcodable α]
    (r : α → RegionInput) (b : α → Bounds) (N : α → ℕ) (m : α → ℕ)
    (hr : Computable r) (hb : Computable b) (hN : Computable N) (hm : Computable m) :
    Computable (fun x => relevanceFormula (r x) (b x) (N x) (m x)) := by
  unfold relevanceFormula
  fun_prop

@[fun_prop] theorem c_outsideClosedCell {α : Type*} [Primcodable α]
    (r : α → RegionInput) (m : α → ℕ) (i : α → ℕ) (a : α → ℕ)
    (hr : Computable r) (hm : Computable m) (hi : Computable i) (ha : Computable a) :
    Computable (fun x => outsideClosedCell (r x) (m x) (i x) (a x)) := by
  unfold outsideClosedCell
  fun_prop

@[fun_prop] theorem c_uncoveredPointBody {α : Type*} [Primcodable α]
    (r : α → RegionInput) (b : α → Bounds) (N : α → ℕ) (m : α → ℕ)
    (hr : Computable r) (hb : Computable b) (hN : Computable N) (hm : Computable m) :
    Computable (fun x => uncoveredPointBody (r x) (b x) (N x) (m x)) := by
  unfold uncoveredPointBody
  fun_prop

@[fun_prop] theorem c_coverageFormula {α : Type*} [Primcodable α]
    (r : α → RegionInput) (b : α → Bounds) (N : α → ℕ) (m : α → ℕ)
    (hr : Computable r) (hb : Computable b) (hN : Computable N) (hm : Computable m) :
    Computable (fun x => coverageFormula (r x) (b x) (N x) (m x)) := by
  unfold coverageFormula
  fun_prop

@[fun_prop] theorem c_localCoverFormula {α : Type*} [Primcodable α]
    (r : α → RegionInput) (b : α → Bounds) (N : α → ℕ) (m : α → ℕ)
    (hr : Computable r) (hb : Computable b) (hN : Computable N) (hm : Computable m) :
    Computable (fun x => localCoverFormula (r x) (b x) (N x) (m x)) := by
  unfold localCoverFormula
  fun_prop

@[fun_prop] theorem c_positiveSubdivisionFormula {α : Type*} [Primcodable α]
    (b : α → Bounds) (N : α → ℕ) (h : α → ℕ) (v : α → ℕ)
    (hb : Computable b) (hN : Computable N) (hh : Computable h) (hv : Computable v) :
    Computable (fun x => positiveSubdivisionFormula (b x) (N x) (h x) (v x)) := by
  unfold positiveSubdivisionFormula
  fun_prop

theorem localCoverFormula_computable :
    Computable (fun p : RegionInput × Bounds × ℕ × ℕ =>
      localCoverFormula p.1 p.2.1 p.2.2.1 p.2.2.2) := by fun_prop

theorem positiveSubdivisionFormula_computable :
    Computable (fun p : Bounds × ℕ × ℕ × ℕ =>
      positiveSubdivisionFormula p.1 p.2.1 p.2.2.1 p.2.2.2) := by fun_prop

open Tiling.AxisParallel.Terminal.Executable
open CertificateCoding

@[fun_prop] theorem c_negativeBox {α : Type*} [Primcodable α]
    (f : α → RawNegativeCode) (hf : Computable f) :
    Computable (fun x => (f x).boxIndex) := rawNegative_boxIndex_primrec.to_comp.comp hf

@[fun_prop] theorem c_negativeHorizontal {α : Type*} [Primcodable α]
    (f : α → RawNegativeCode) (hf : Computable f) :
    Computable (fun x => (f x).horizontalSubdivisions) :=
  rawNegative_horizontalSubdivisions_primrec.to_comp.comp hf

@[fun_prop] theorem c_negativeVertical {α : Type*} [Primcodable α]
    (f : α → RawNegativeCode) (hf : Computable f) :
    Computable (fun x => (f x).verticalSubdivisions) :=
  rawNegative_verticalSubdivisions_primrec.to_comp.comp hf

@[fun_prop] theorem c_negativeWellFormed {α : Type*} [Primcodable α]
    (f : α → RawNegativeCode) (hf : Computable f) :
    Computable (fun x => (f x).wellFormed) := rawNegative_wellFormed_computable.comp hf

@[fun_prop] theorem c_negativeCertificateFormula {α : Type*} [Primcodable α]
    (r : α → RegionInput) (b : α → Bounds) (c : α → RawNegativeCode)
    (hr : Computable r) (hb : Computable b) (hc : Computable c) :
    Computable (fun x => negativeCertificateFormula (r x) (b x) (c x)) := by
  unfold negativeCertificateFormula
  fun_prop

theorem negativeFormula_computable :
    Computable (fun p : RegionInput × Bounds × ℕ => negativeFormula p.1 p.2.1 p.2.2) := by
  have hstage : Computable (fun p : RegionInput × Bounds × ℕ =>
      wellFormedNegativeStage p.2.2) :=
    wellFormedNegativeStage_computable.comp (Computable.snd.comp Computable.snd)
  have hbody : Computable₂ (fun p : RegionInput × Bounds × ℕ => fun code : RawNegativeCode =>
      negativeCertificateFormula p.1 p.2.1 code) := by
    change Computable (fun p : (RegionInput × Bounds × ℕ) × RawNegativeCode =>
      negativeCertificateFormula p.1.1 p.1.2.1 p.2)
    fun_prop
  refine (Computable.option_casesOn hstage (Computable.const falsity) hbody).of_eq ?_
  intro p
  unfold negativeFormula
  cases wellFormedNegativeStage p.2.2 <;> rfl

end Tiling.AxisParallel.Decidability.NegativeFormulas
