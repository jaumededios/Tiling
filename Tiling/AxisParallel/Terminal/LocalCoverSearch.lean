import Tiling.AxisParallel.Terminal.ExecutableInput
import Tiling.AxisParallel.Terminal.CertificateCoding
import Tiling.AxisParallel.Terminal.AffineCompiler
import Tiling.AxisParallel.Terminal.OracleProgramCore
import Tiling.AxisParallel.Terminal.ExecutableInputSemantics
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Pointwise

namespace Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch

open Tiling.AxisParallel.Terminal.Executable

/-- Runtime data obtained from a positive cell and finite oracle maxima. -/
structure LocalBoundCode (C : RegionCode) where
  widthCell : Fin C.cellCount
  horizontalDiameter : Coeff C
  verticalDiameter : Coeff C
  horizontalWidth : Coeff C
  verticalWidth : Coeff C

def chooseLargerCoeff {C : RegionCode} (O : Oracle C) (s : CoordSort)
    (a b : Coeff C) : Coeff C :=
  if O.answer ⟨s, a, b⟩ then b else a

def maxCoeffList {C : RegionCode} (O : Oracle C) (s : CoordSort) :
    List (Coeff C) → Coeff C :=
  List.foldl (chooseLargerCoeff O s) (Coeff.zero C)

def diameterCandidates (C : RegionCode) : List (Coeff C) :=
  (List.ofFn fun i : Fin C.vertexCount => List.ofFn fun j : Fin C.vertexCount =>
    [Coeff.sub (Coeff.single i 1) (Coeff.single j 1),
      Coeff.sub (Coeff.single j 1) (Coeff.single i 1)]).flatten.flatten

/-- The runtime bound producer uses cell `0` and finite oracle folds only. -/
def buildLocalBound (C : RegionCode) (O : Oracle C) : Option (LocalBoundCode C) :=
  if h : 0 < C.cellCount then
    let e : Fin C.cellCount := ⟨0, h⟩
    some {
      widthCell := e
      horizontalDiameter := maxCoeffList O .horizontal (diameterCandidates C)
      verticalDiameter := maxCoeffList O .vertical (diameterCandidates C)
      horizontalWidth := Coeff.sub (Coeff.cellRight e) (Coeff.cellLeft e)
      verticalWidth := Coeff.sub (Coeff.cellTop e) (Coeff.cellBottom e) }
  else none

/-- Raw subdivision data are accepted only after every positive and product check succeeds. -/
def subdivisionWellFormed (c : RawNegativeCode) : Bool :=
  decide (0 < c.boxIndex && 0 < c.horizontalSubdivisions &&
    0 < c.verticalSubdivisions)

def localCardinalityBound (c : RawNegativeCode) : Nat :=
  c.horizontalSubdivisions * c.verticalSubdivisions

/-- The semantic open box denoted by runtime index `N` and the two computed
diameter coefficients. -/
def semanticLocalBox {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N : Nat) : Set Tiling.Plane :=
  {z | -(N * evalCoeff R .horizontal B.horizontalDiameter) < z.re ∧
    z.re < N * evalCoeff R .horizontal B.horizontalDiameter ∧
    -(N * evalCoeff R .vertical B.verticalDiameter) < z.im ∧
    z.im < N * evalCoeff R .vertical B.verticalDiameter}

/-- A candidate local cover uses `m` horizontal and `m` vertical centre variables. -/
abbrev LocalCoverFormula (C : RegionCode) (m : Nat) := Formula C m m

def listAnd {C h v} : List (Formula C h v) → Formula C h v :=
  List.foldr .conjunction .truth

def listOr {C h v} : List (Formula C h v) → Formula C h v :=
  List.foldr .disjunction .falsity

def constantExpr (C : RegionCode) (n : Nat) (a : Coeff C) : AffineExpr C n :=
  ⟨fun _ => 0, a⟩

def variableExpr (C : RegionCode) (n : Nat) (i : Fin n) : AffineExpr C n :=
  ⟨fun j => if j = i then 1 else 0, Coeff.zero C⟩

def translatedExpr {C : RegionCode} {n : Nat} (i : Fin n) (a : Coeff C) :
    AffineExpr C n :=
  ⟨fun j => if j = i then 1 else 0, a⟩

def horizontalLe {C h v} (a b : AffineExpr C h) : Formula C h v := .horizontalLe a b
def horizontalLt {C h v} (a b : AffineExpr C h) : Formula C h v := .horizontalLt a b
def verticalLe {C h v} (a b : AffineExpr C v) : Formula C h v := .verticalLe a b
def verticalLt {C h v} (a b : AffineExpr C v) : Formula C h v := .verticalLt a b

def distinctCentres (C : RegionCode) (m : Nat) (i j : Fin m) : LocalCoverFormula C m :=
  listOr [horizontalLt (variableExpr C m i) (variableExpr C m j),
    horizontalLt (variableExpr C m j) (variableExpr C m i),
    verticalLt (variableExpr C m i) (variableExpr C m j),
    verticalLt (variableExpr C m j) (variableExpr C m i)]

def cellPairSeparated (C : RegionCode) (m : Nat) (i j : Fin m)
    (a b : Fin C.cellCount) : LocalCoverFormula C m :=
  listOr [
    horizontalLe (translatedExpr i (Coeff.cellRight a))
      (translatedExpr j (Coeff.cellLeft b)),
    horizontalLe (translatedExpr j (Coeff.cellRight b))
      (translatedExpr i (Coeff.cellLeft a)),
    verticalLe (translatedExpr i (Coeff.cellTop a))
      (translatedExpr j (Coeff.cellBottom b)),
    verticalLe (translatedExpr j (Coeff.cellTop b))
      (translatedExpr i (Coeff.cellBottom a))]

def cellPairsSeparated (C : RegionCode) (m : Nat) (i j : Fin m) :
    LocalCoverFormula C m :=
  listAnd ((List.ofFn fun a : Fin C.cellCount =>
    List.ofFn fun b : Fin C.cellCount => cellPairSeparated C m i j a b).flatten)

def centrePairPacking (C : RegionCode) (m : Nat) (i j : Fin m) :
    LocalCoverFormula C m :=
  if i = j then .truth else
    .conjunction (distinctCentres C m i j) (cellPairsSeparated C m i j)

def packingFormula (C : RegionCode) (m : Nat) : LocalCoverFormula C m :=
  listAnd ((List.ofFn fun i : Fin m =>
    List.ofFn fun j : Fin m => centrePairPacking C m i j).flatten)

def withinBoundHorizontal (C : RegionCode) (m N : Nat) (B : Coeff C) (i : Fin m) :
    LocalCoverFormula C m :=
  Formula.conjunction
    (horizontalLe (constantExpr C m (Coeff.neg (Coeff.nsmul N B))) (variableExpr C m i))
    (horizontalLe (variableExpr C m i) (constantExpr C m (Coeff.nsmul N B)))

def withinBoundVertical (C : RegionCode) (m N : Nat) (B : Coeff C) (i : Fin m) :
    LocalCoverFormula C m :=
  Formula.conjunction
    (verticalLe (constantExpr C m (Coeff.neg (Coeff.nsmul N B))) (variableExpr C m i))
    (verticalLe (variableExpr C m i) (constantExpr C m (Coeff.nsmul N B)))

def relevanceFormula (C : RegionCode) (B : LocalBoundCode C) (N m : Nat) :
    LocalCoverFormula C m :=
  listAnd (List.ofFn fun i : Fin m => Formula.conjunction
    (withinBoundHorizontal C m (N + 1) B.horizontalDiameter i)
    (withinBoundVertical C m (N + 1) B.verticalDiameter i))

/-- In the coverage body, index `0` is the uncovered-point variable and `i.succ` is centre `i`. -/
def outsideClosedCell (C : RegionCode) (m : Nat) (i : Fin m) (a : Fin C.cellCount) :
    Formula C (m + 1) (m + 1) :=
  Formula.negation (listAnd [
    horizontalLe (translatedExpr i.succ (Coeff.cellLeft a)) (variableExpr C (m+1) 0),
    horizontalLe (variableExpr C (m+1) 0) (translatedExpr i.succ (Coeff.cellRight a)),
    verticalLe (translatedExpr i.succ (Coeff.cellBottom a)) (variableExpr C (m+1) 0),
    verticalLe (variableExpr C (m+1) 0) (translatedExpr i.succ (Coeff.cellTop a))])

def uncoveredPointBody (C : RegionCode) (B : LocalBoundCode C) (N m : Nat) :
    Formula C (m + 1) (m + 1) :=
  listAnd ([
    horizontalLt (constantExpr C (m+1) (Coeff.neg (Coeff.nsmul N B.horizontalDiameter)))
      (variableExpr C (m+1) 0),
    horizontalLt (variableExpr C (m+1) 0)
      (constantExpr C (m+1) (Coeff.nsmul N B.horizontalDiameter)),
    verticalLt (constantExpr C (m+1) (Coeff.neg (Coeff.nsmul N B.verticalDiameter)))
      (variableExpr C (m+1) 0),
    verticalLt (variableExpr C (m+1) 0)
      (constantExpr C (m+1) (Coeff.nsmul N B.verticalDiameter))] ++
    (List.ofFn fun i : Fin m => List.ofFn fun a : Fin C.cellCount =>
      outsideClosedCell C m i a).flatten)

def coverageFormula (C : RegionCode) (B : LocalBoundCode C) (N m : Nat) :
    LocalCoverFormula C m :=
  Formula.negation (.existsHorizontal (.existsVertical (uncoveredPointBody C B N m)))

def existsAllHorizontal {C v} : (n : Nat) → Formula C n v → Formula C 0 v
  | 0, f => f
  | n + 1, f => existsAllHorizontal n (.existsHorizontal f)

def existsAllVertical {C} : (n : Nat) → Formula C 0 n → Formula C 0 0
  | 0, f => f
  | n + 1, f => existsAllVertical n (.existsVertical f)

def localCoverFormula (C : RegionCode) (B : LocalBoundCode C) (N m : Nat) : Formula C 0 0 :=
  existsAllVertical m (existsAllHorizontal m
    (listAnd [packingFormula C m, relevanceFormula C B N m, coverageFormula C B N m]))

private theorem listAnd_holds {C : RegionCode} (R : Realization C) {h v : Nat}
    (fs : List (Formula C h v)) (x : Fin h → Real) (y : Fin v → Real) :
    (listAnd fs).Holds R x y ↔ ∀ f ∈ fs, f.Holds R x y := by
  induction fs with
  | nil => simp [listAnd, Formula.Holds]
  | cons f fs ih =>
      change (f.Holds R x y ∧ (listAnd fs).Holds R x y) ↔ _
      simp only [ih, List.forall_mem_cons]

private theorem listOr_holds {C : RegionCode} (R : Realization C) {h v : Nat}
    (fs : List (Formula C h v)) (x : Fin h → Real) (y : Fin v → Real) :
    (listOr fs).Holds R x y ↔ ∃ f ∈ fs, f.Holds R x y := by
  induction fs with
  | nil => simp [listOr, Formula.Holds]
  | cons f fs ih =>
      change (f.Holds R x y ∨ (listOr fs).Holds R x y) ↔ _
      rw [ih]
      constructor
      · rintro (hf | ⟨g, hg, hG⟩)
        · exact ⟨f, List.mem_cons_self, hf⟩
        · exact ⟨g, List.mem_cons_of_mem f hg, hG⟩
      · rintro ⟨g, hg, hG⟩
        rcases List.mem_cons.mp hg with rfl | hg
        · exact Or.inl hG
        · exact Or.inr ⟨g, hg, hG⟩

private def openRectangle (l r b t : Real) : Set Tiling.Plane :=
  {z | l < z.re ∧ z.re < r ∧ b < z.im ∧ z.im < t}

private theorem isOpen_openRectangle (l r b t : Real) :
    IsOpen (openRectangle l r b t) := by
  change IsOpen ({z : Tiling.Plane | l < z.re} ∩ ({z : Tiling.Plane | z.re < r} ∩
    ({z : Tiling.Plane | b < z.im} ∩ {z : Tiling.Plane | z.im < t})))
  exact (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im continuous_const)))

private theorem openRectangle_inter_measure_eq_zero_iff
    {l₁ r₁ b₁ t₁ l₂ r₂ b₂ t₂ : Real}
    (h₁ : l₁ < r₁ ∧ b₁ < t₁) (h₂ : l₂ < r₂ ∧ b₂ < t₂) :
    MeasureTheory.volume
      (openRectangle l₁ r₁ b₁ t₁ ∩ openRectangle l₂ r₂ b₂ t₂) = 0 ↔
      r₁ ≤ l₂ ∨ r₂ ≤ l₁ ∨ t₁ ≤ b₂ ∨ t₂ ≤ b₁ := by
  constructor
  · intro hzero
    by_contra hsep
    push Not at hsep
    have hne : (openRectangle l₁ r₁ b₁ t₁ ∩
        openRectangle l₂ r₂ b₂ t₂).Nonempty := by
      let u := (max l₁ l₂ + min r₁ r₂) / 2
      let v := (max b₁ b₂ + min t₁ t₂) / 2
      have hu : max l₁ l₂ < min r₁ r₂ := by
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨h₁.1, hsep.2.1⟩, hsep.1, h₂.1⟩
      have hv : max b₁ b₂ < min t₁ t₂ := by
        rw [max_lt_iff, lt_min_iff, lt_min_iff]
        exact ⟨⟨h₁.2, hsep.2.2.2⟩, hsep.2.2.1, h₂.2⟩
      refine ⟨(u : ℂ) + (v : ℂ) * Complex.I, ?_⟩
      simp only [openRectangle, Set.mem_inter_iff, Set.mem_ofPred_eq,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero,
        Complex.add_im, Complex.mul_im, mul_one, zero_add]
      dsimp [u, v]
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [le_max_left l₁ l₂,
          min_le_left r₁ r₂, le_max_left b₁ b₂, min_le_left t₁ t₂, hu, hv]
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [le_max_right l₁ l₂,
          min_le_right r₁ r₂, le_max_right b₁ b₂, min_le_right t₁ t₂, hu, hv]
    exact ((isOpen_openRectangle l₁ r₁ b₁ t₁).inter
      (isOpen_openRectangle l₂ r₂ b₂ t₂)).measure_ne_zero
        MeasureTheory.volume hne hzero
  · intro hsep
    have hempty : openRectangle l₁ r₁ b₁ t₁ ∩
        openRectangle l₂ r₂ b₂ t₂ = ∅ := by
      ext z
      simp only [openRectangle, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨hz₁, hz₂⟩
        rcases hsep with h | h | h | h <;> linarith [hz₁.1, hz₁.2.1,
          hz₁.2.2.1, hz₁.2.2.2, hz₂.1, hz₂.2.1, hz₂.2.2.1, hz₂.2.2.2]
      · simp
    rw [hempty, MeasureTheory.measure_empty]

private def realizedCell {C : RegionCode} (R : Realization C) (e : Fin C.cellCount) :
    Set Tiling.Plane := openRectangle (R.vertex (C.leftVertex e)).re
      (R.vertex (C.rightVertex e)).re (R.vertex (C.bottomVertex e)).im
      (R.vertex (C.topVertex e)).im

private theorem translatedRegion_ae_cells {C : RegionCode} (R : Realization C)
    (a : Tiling.Plane) :
    a +ᵥ R.region.openCarrier =ᵐ[MeasureTheory.volume]
      ⋃ e, a +ᵥ realizedCell R e := by
  have h := (MeasureTheory.vadd_set_ae_eq a).2 R.presentation_correct.symm
  apply h.trans
  filter_upwards [] with z
  apply propext
  change z ∈ a +ᵥ (⋃ e, realizedCell R e) ↔ z ∈ ⋃ e, a +ᵥ realizedCell R e
  simp only [Set.mem_vadd_set, Set.mem_iUnion]
  constructor
  · rintro ⟨w, ⟨e, he⟩, rfl⟩
    exact ⟨e, w, he, rfl⟩
  · rintro ⟨e, w, hw, rfl⟩
    exact ⟨w, ⟨e, hw⟩, rfl⟩

private theorem translatedRegions_inter_null_iff_cells {C : RegionCode}
    (R : Realization C) (a b : Tiling.Plane) :
    MeasureTheory.volume ((a +ᵥ R.region.openCarrier) ∩
      (b +ᵥ R.region.openCarrier)) = 0 ↔
    ∀ e f, MeasureTheory.volume ((a +ᵥ realizedCell R e) ∩
      (b +ᵥ realizedCell R f)) = 0 := by
  have hae := (translatedRegion_ae_cells R a).inter (translatedRegion_ae_cells R b)
  rw [hae.measure_eq]
  constructor
  · intro h e f
    apply MeasureTheory.measure_mono_null ?_ h
    intro z hz
    exact ⟨Set.mem_iUnion.mpr ⟨e, hz.1⟩, Set.mem_iUnion.mpr ⟨f, hz.2⟩⟩
  · intro h
    rw [Set.iUnion_inter]
    apply MeasureTheory.measure_iUnion_null
    intro e
    rw [Set.inter_iUnion]
    exact MeasureTheory.measure_iUnion_null (h e)

private theorem translatedCells_inter_null_iff {C : RegionCode} (R : Realization C)
    (x₁ y₁ x₂ y₂ : Real) (e f : Fin C.cellCount) :
    MeasureTheory.volume
      ((((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) +ᵥ realizedCell R e) ∩
       (((x₂ : ℂ) + (y₂ : ℂ) * Complex.I) +ᵥ realizedCell R f)) = 0 ↔
      x₁ + (R.vertex (C.rightVertex e)).re ≤ x₂ + (R.vertex (C.leftVertex f)).re ∨
      x₂ + (R.vertex (C.rightVertex f)).re ≤ x₁ + (R.vertex (C.leftVertex e)).re ∨
      y₁ + (R.vertex (C.topVertex e)).im ≤ y₂ + (R.vertex (C.bottomVertex f)).im ∨
      y₂ + (R.vertex (C.topVertex f)).im ≤ y₁ + (R.vertex (C.bottomVertex e)).im := by
  have he : ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I) +ᵥ realizedCell R e =
      openRectangle (x₁ + (R.vertex (C.leftVertex e)).re)
        (x₁ + (R.vertex (C.rightVertex e)).re)
        (y₁ + (R.vertex (C.bottomVertex e)).im)
        (y₁ + (R.vertex (C.topVertex e)).im) := by
    ext z
    simp only [Set.mem_vadd_set, realizedCell, openRectangle, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, ⟨hw₁, hw₂, hw₃, hw₄⟩, rfl⟩
      simp only [vadd_eq_add, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro hz
      refine ⟨z - ((x₁ : ℂ) + (y₁ : ℂ) * Complex.I), ?_, by simp⟩
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
      exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1],
        by linarith [hz.2.2.2]⟩
  have hf : ((x₂ : ℂ) + (y₂ : ℂ) * Complex.I) +ᵥ realizedCell R f =
      openRectangle (x₂ + (R.vertex (C.leftVertex f)).re)
        (x₂ + (R.vertex (C.rightVertex f)).re)
        (y₂ + (R.vertex (C.bottomVertex f)).im)
        (y₂ + (R.vertex (C.topVertex f)).im) := by
    ext z
    simp only [Set.mem_vadd_set, realizedCell, openRectangle, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨w, ⟨hw₁, hw₂, hw₃, hw₄⟩, rfl⟩
      simp only [vadd_eq_add, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
        Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · intro hz
      refine ⟨z - ((x₂ : ℂ) + (y₂ : ℂ) * Complex.I), ?_, by simp⟩
      simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one, zero_add]
      exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1],
        by linarith [hz.2.2.2]⟩
  rw [he, hf]
  apply openRectangle_inter_measure_eq_zero_iff
  · exact ⟨by linarith [R.left_lt_right e], by linarith [R.bottom_lt_top e]⟩
  · exact ⟨by linarith [R.left_lt_right f], by linarith [R.bottom_lt_top f]⟩

def positiveSubdivisionFormula (C : RegionCode) (B : LocalBoundCode C)
    (c : RawNegativeCode) : Formula C 0 0 :=
  Formula.conjunction
    (horizontalLt (constantExpr C 0 (Coeff.nsmul (2 * (c.boxIndex + 1)) B.horizontalDiameter))
      (constantExpr C 0 (Coeff.nsmul c.horizontalSubdivisions B.horizontalWidth)))
    (verticalLt (constantExpr C 0 (Coeff.nsmul (2 * (c.boxIndex + 1)) B.verticalDiameter))
      (constantExpr C 0 (Coeff.nsmul c.verticalSubdivisions B.verticalWidth)))

def checkSubdivision (evaluate : {C : RegionCode} → Oracle C → Formula C 0 0 → Bool)
    {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (c : RawNegativeCode) : Bool :=
  subdivisionWellFormed c && evaluate O (positiveSubdivisionFormula C B c)

def checkLocalCover (evaluate : {C : RegionCode} → Oracle C → Formula C 0 0 → Bool)
    {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (N m : Nat) : Bool :=
  evaluate O (localCoverFormula C B N m)

def allLocalCardinalitiesFail
    (evaluate : {C : RegionCode} → Oracle C → Formula C 0 0 → Bool)
    {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (c : RawNegativeCode) : Bool :=
  (List.range (localCardinalityBound c + 1)).all
    (fun m => !(checkLocalCover evaluate O B c.boxIndex m))

def negativeVerifier (evaluate : {C : RegionCode} → Oracle C → Formula C 0 0 → Bool)
    {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (c : RawNegativeCode) : Bool :=
  checkSubdivision evaluate O B c && allLocalCardinalitiesFail evaluate O B c

/-! ## Finite oracle programs -/

private def chooseLargerCoeffProgram {C : RegionCode} (s : CoordSort) (a b : Coeff C) :
    Tiling.AxisParallel.Terminal.OracleProgram (Query C) (Coeff C) :=
  .query ⟨s, a, b⟩ (fun answer => .pure (if answer then b else a))

private def maxCoeffListAuxProgram {C : RegionCode} (s : CoordSort) :
    Coeff C → List (Coeff C) →
      Tiling.AxisParallel.Terminal.OracleProgram (Query C) (Coeff C)
  | current, [] => .pure current
  | current, next :: rest =>
      Tiling.AxisParallel.Terminal.OracleProgram.bind
        (chooseLargerCoeffProgram s current next)
        (fun larger => maxCoeffListAuxProgram s larger rest)

private def maxCoeffListProgram {C : RegionCode} (s : CoordSort) (xs : List (Coeff C)) :
    Tiling.AxisParallel.Terminal.OracleProgram (Query C) (Coeff C) :=
  maxCoeffListAuxProgram s (Coeff.zero C) xs

def buildLocalBoundProgram (C : RegionCode) :
    Tiling.AxisParallel.Terminal.OracleProgram (Query C) (Option (LocalBoundCode C)) :=
  if h : 0 < C.cellCount then
    let e : Fin C.cellCount := ⟨0, h⟩
    Tiling.AxisParallel.Terminal.OracleProgram.bind
      (maxCoeffListProgram .horizontal (diameterCandidates C)) fun hd =>
    Tiling.AxisParallel.Terminal.OracleProgram.bind
      (maxCoeffListProgram .vertical (diameterCandidates C)) fun vd =>
    .pure (some {
      widthCell := e
      horizontalDiameter := hd
      verticalDiameter := vd
      horizontalWidth := Coeff.sub (Coeff.cellRight e) (Coeff.cellLeft e)
      verticalWidth := Coeff.sub (Coeff.cellTop e) (Coeff.cellBottom e) })
  else .pure none

def checkSubdivisionProgram {C : RegionCode} (B : LocalBoundCode C)
    (c : RawNegativeCode) : Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool :=
  if subdivisionWellFormed c then
    AffineCompiler.decideFormulaProgram (positiveSubdivisionFormula C B c)
  else .pure false

def checkLocalCoverProgram {C : RegionCode} (B : LocalBoundCode C) (N m : Nat) :
    Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool :=
  AffineCompiler.decideFormulaProgram (localCoverFormula C B N m)

def allLocalCardinalitiesFailAuxProgram {C : RegionCode} (B : LocalBoundCode C)
    (N : Nat) : List Nat → Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool
  | [] => .pure true
  | m :: rest =>
      Tiling.AxisParallel.Terminal.OracleProgram.bind (checkLocalCoverProgram B N m) fun covered =>
        if covered then .pure false else allLocalCardinalitiesFailAuxProgram B N rest

def allLocalCardinalitiesFailProgram {C : RegionCode} (B : LocalBoundCode C)
    (c : RawNegativeCode) : Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool :=
  allLocalCardinalitiesFailAuxProgram B c.boxIndex
    (List.range (localCardinalityBound c + 1))

def negativeVerifierProgram {C : RegionCode} (B : LocalBoundCode C)
    (c : RawNegativeCode) : Tiling.AxisParallel.Terminal.OracleProgram (Query C) Bool :=
  Tiling.AxisParallel.Terminal.OracleProgram.bind (checkSubdivisionProgram B c) fun ok =>
    if ok then allLocalCardinalitiesFailProgram B c else .pure false

private theorem chooseLargerCoeffProgram_evaluate {C : RegionCode} (O : Oracle C)
    (s : CoordSort) (a b : Coeff C) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (chooseLargerCoeffProgram s a b) = chooseLargerCoeff O s a b := by
  rfl

private theorem maxCoeffListAuxProgram_evaluate {C : RegionCode} (O : Oracle C)
    (s : CoordSort) (current : Coeff C) (xs : List (Coeff C)) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (maxCoeffListAuxProgram s current xs) =
      List.foldl (chooseLargerCoeff O s) current xs := by
  induction xs generalizing current with
  | nil => rfl
  | cons next rest ih =>
      rw [maxCoeffListAuxProgram,
        Tiling.AxisParallel.Terminal.OracleProgram.evaluate_bind,
        chooseLargerCoeffProgram_evaluate]
      exact ih _

private theorem maxCoeffListProgram_evaluate {C : RegionCode} (O : Oracle C)
    (s : CoordSort) (xs : List (Coeff C)) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (maxCoeffListProgram s xs) = maxCoeffList O s xs := by
  exact maxCoeffListAuxProgram_evaluate O s (Coeff.zero C) xs

theorem buildLocalBoundProgram_evaluate (C : RegionCode) (O : Oracle C) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (buildLocalBoundProgram C) = buildLocalBound C O := by
  simp only [buildLocalBoundProgram, buildLocalBound]
  split
  · rw [Tiling.AxisParallel.Terminal.OracleProgram.evaluate_bind,
      maxCoeffListProgram_evaluate,
      Tiling.AxisParallel.Terminal.OracleProgram.evaluate_bind,
      maxCoeffListProgram_evaluate]
    rfl
  · rfl

private theorem checkSubdivisionProgram_evaluate {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (c : RawNegativeCode) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (checkSubdivisionProgram B c) =
      checkSubdivision AffineCompiler.decideFormula O B c := by
  simp only [checkSubdivisionProgram, checkSubdivision]
  cases h : subdivisionWellFormed c
  · rfl
  · simpa using AffineCompiler.decideFormulaProgram_evaluate O
      (positiveSubdivisionFormula C B c)

private theorem checkLocalCoverProgram_evaluate {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (N m : Nat) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (checkLocalCoverProgram B N m) =
      checkLocalCover AffineCompiler.decideFormula O B N m := by
  exact AffineCompiler.decideFormulaProgram_evaluate O _

private theorem allLocalCardinalitiesFailAuxProgram_evaluate {C : RegionCode}
    (O : Oracle C) (B : LocalBoundCode C) (N : Nat) (xs : List Nat) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (allLocalCardinalitiesFailAuxProgram B N xs) =
      xs.all (fun m => !(checkLocalCover AffineCompiler.decideFormula O B N m)) := by
  induction xs with
  | nil => rfl
  | cons m rest ih =>
      rw [allLocalCardinalitiesFailAuxProgram,
        Tiling.AxisParallel.Terminal.OracleProgram.evaluate_bind,
        checkLocalCoverProgram_evaluate]
      cases h : checkLocalCover AffineCompiler.decideFormula O B N m
      · simpa [h] using ih
      · simp [h, Tiling.AxisParallel.Terminal.OracleProgram.evaluate]

private theorem allLocalCardinalitiesFailProgram_evaluate {C : RegionCode}
    (O : Oracle C) (B : LocalBoundCode C) (c : RawNegativeCode) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (allLocalCardinalitiesFailProgram B c) =
      allLocalCardinalitiesFail AffineCompiler.decideFormula O B c := by
  exact allLocalCardinalitiesFailAuxProgram_evaluate O B c.boxIndex _

theorem negativeVerifierProgram_evaluate {C : RegionCode} (O : Oracle C)
    (B : LocalBoundCode C) (c : RawNegativeCode) :
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate O.answer
        (negativeVerifierProgram B c) =
      negativeVerifier AffineCompiler.decideFormula O B c := by
  rw [negativeVerifierProgram,
    Tiling.AxisParallel.Terminal.OracleProgram.evaluate_bind,
    checkSubdivisionProgram_evaluate]
  cases h : checkSubdivision AffineCompiler.decideFormula O B c
  · simp [negativeVerifier, h,
      Tiling.AxisParallel.Terminal.OracleProgram.evaluate]
  · simpa [negativeVerifier, h] using
      allLocalCardinalitiesFailProgram_evaluate O B c

theorem positiveSubdivision_adequate {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (c : RawNegativeCode) :
    (positiveSubdivisionFormula C B c).Holds R Fin.elim0 Fin.elim0 ↔
      2 * (c.boxIndex + 1) * evalCoeff R .horizontal B.horizontalDiameter <
        c.horizontalSubdivisions * evalCoeff R .horizontal B.horizontalWidth ∧
      2 * (c.boxIndex + 1) * evalCoeff R .vertical B.verticalDiameter <
        c.verticalSubdivisions * evalCoeff R .vertical B.verticalWidth := by
  simp [positiveSubdivisionFormula, Formula.Holds, horizontalLt, verticalLt,
    constantExpr, evalAffine, evalCoeff, Coeff.nsmul, Finset.mul_sum,
    Nat.cast_mul, Nat.cast_add, mul_assoc]

private theorem existsAllHorizontal_holds {C : RegionCode} (R : Realization C) {v : Nat}
    (y : Fin v → Real) : ∀ (n : Nat) (f : Formula C n v),
    (existsAllHorizontal n f).Holds R Fin.elim0 y ↔
      ∃ x : Fin n → Real, f.Holds R x y := by
  intro n
  induction n with
  | zero =>
      intro f
      constructor
      · intro h
        exact ⟨Fin.elim0, h⟩
      · rintro ⟨x, hx⟩
        simpa only [existsAllHorizontal, Subsingleton.elim x Fin.elim0] using hx
  | succ n ih =>
      intro f
      rw [existsAllHorizontal, ih]
      simp only [Formula.Holds]
      constructor
      · rintro ⟨x, t, h⟩
        exact ⟨Fin.cons t x, h⟩
      · rintro ⟨x, hx⟩
        exact ⟨Fin.tail x, x 0, by simpa only [Fin.cons_self_tail] using hx⟩

private theorem existsAllVertical_holds {C : RegionCode} (R : Realization C) :
    ∀ (n : Nat) (f : Formula C 0 n),
    (existsAllVertical n f).Holds R Fin.elim0 Fin.elim0 ↔
      ∃ y : Fin n → Real, f.Holds R Fin.elim0 y := by
  intro n
  induction n with
  | zero =>
      intro f
      constructor
      · intro h
        exact ⟨Fin.elim0, h⟩
      · rintro ⟨y, hy⟩
        simpa only [existsAllVertical, Subsingleton.elim y Fin.elim0] using hy
  | succ n ih =>
      intro f
      rw [existsAllVertical, ih]
      simp only [Formula.Holds]
      constructor
      · rintro ⟨y, t, h⟩
        exact ⟨Fin.cons t y, h⟩
      · rintro ⟨y, hy⟩
        exact ⟨Fin.tail y, y 0, by simpa only [Fin.cons_self_tail] using hy⟩

theorem localCover_adequate {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N m : Nat) :
    (localCoverFormula C B N m).Holds R Fin.elim0 Fin.elim0 ↔
      ∃ x y : Fin m → Real,
        (packingFormula C m).Holds R x y ∧
        (relevanceFormula C B N m).Holds R x y ∧
        (coverageFormula C B N m).Holds R x y := by
  rw [localCoverFormula, existsAllVertical_holds]
  constructor
  · rintro ⟨y, hy⟩
    rw [existsAllHorizontal_holds] at hy
    rcases hy with ⟨x, hx⟩
    have hx' :
        (packingFormula C m).Holds R x y ∧
        (relevanceFormula C B N m).Holds R x y ∧
        (coverageFormula C B N m).Holds R x y := by
      simpa [listAnd, Formula.Holds] using hx
    exact ⟨x, y, hx'⟩
  · rintro ⟨x, y, hx⟩
    refine ⟨y, ?_⟩
    rw [existsAllHorizontal_holds]
    refine ⟨x, ?_⟩
    simpa [listAnd, Formula.Holds] using hx

private theorem evalCoeff_zero {C : RegionCode} (R : Realization C) (s : CoordSort) :
    evalCoeff R s (Coeff.zero C) = 0 := by
  simp [evalCoeff, Coeff.zero]

private theorem evalCoeff_single {C : RegionCode} (R : Realization C) (s : CoordSort)
    (i : Fin C.vertexCount) (z : Int) :
    evalCoeff R s (Coeff.single i z) = (z : Real) * s.axis.coord (R.vertex i) := by
  simp [evalCoeff, Coeff.single]

private theorem evalCoeff_sub {C : RegionCode} (R : Realization C) (s : CoordSort)
    (a b : Coeff C) :
    evalCoeff R s (Coeff.sub a b) = evalCoeff R s a - evalCoeff R s b := by
  simp [evalCoeff, Coeff.sub, sub_mul, Finset.sum_sub_distrib]

private theorem evalCoeff_neg {C : RegionCode} (R : Realization C) (s : CoordSort)
    (a : Coeff C) : evalCoeff R s (Coeff.neg a) = -evalCoeff R s a := by
  simp [evalCoeff, Coeff.neg, Finset.sum_neg_distrib]

private theorem evalCoeff_nsmul {C : RegionCode} (R : Realization C) (s : CoordSort)
    (n : Nat) (a : Coeff C) :
    evalCoeff R s (Coeff.nsmul n a) = n * evalCoeff R s a := by
  simp only [evalCoeff, Coeff.nsmul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  ring

private theorem evalCoeff_chooseLargerCoeff {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (s : CoordSort) (a b : Coeff C) :
    evalCoeff R s (chooseLargerCoeff O.toOracle s a b) =
      max (evalCoeff R s a) (evalCoeff R s b) := by
  rw [chooseLargerCoeff]
  by_cases h : O.answer ⟨s, a, b⟩ = true
  · rw [if_pos h, max_eq_right]
    exact (O.correct _).mp h
  · rw [if_neg h, max_eq_left]
    exact le_of_not_ge fun hba => h ((O.correct _).mpr hba)

private theorem evalCoeff_fold_chooseLarger {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (s : CoordSort) (current : Coeff C) :
    ∀ xs : List (Coeff C),
      evalCoeff R s (List.foldl (chooseLargerCoeff O.toOracle s) current xs) =
        List.foldl max (evalCoeff R s current) (xs.map (evalCoeff R s)) := by
  intro xs
  induction xs generalizing current with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, evalCoeff_chooseLargerCoeff]

private theorem le_foldl_max_of_mem (a current : Real) :
    ∀ xs : List Real, a ∈ xs → a ≤ List.foldl max current xs := by
  have hcurrent : ∀ (c : Real) (ys : List Real), c ≤ List.foldl max c ys := by
    intro c ys
    induction ys generalizing c with
    | nil => exact le_rfl
    | cons b rest ih =>
        exact le_trans (le_max_left _ _) (ih _)
  intro xs
  induction xs generalizing current with
  | nil => simp
  | cons b rest ih =>
      intro ha
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_trans (le_max_right _ _) (hcurrent _ _)
      · exact ih _ ha

private theorem evalCoeff_le_maxCoeffList_of_mem {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (s : CoordSort) {a : Coeff C} {xs : List (Coeff C)}
    (ha : a ∈ xs) :
    evalCoeff R s a ≤ evalCoeff R s (maxCoeffList O.toOracle s xs) := by
  rw [maxCoeffList, evalCoeff_fold_chooseLarger, evalCoeff_zero]
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

private theorem signedDifference_mem_diameterCandidates (C : RegionCode)
    (i j : Fin C.vertexCount) :
    Coeff.sub (Coeff.single i 1) (Coeff.single j 1) ∈ diameterCandidates C := by
  rw [diameterCandidates]
  apply List.mem_flatten.mpr
  refine ⟨[Coeff.sub (Coeff.single i 1) (Coeff.single j 1),
      Coeff.sub (Coeff.single j 1) (Coeff.single i 1)], ?_, List.mem_cons_self⟩
  apply List.mem_flatten.mpr
  refine ⟨List.ofFn fun j : Fin C.vertexCount =>
    [Coeff.sub (Coeff.single i 1) (Coeff.single j 1),
      Coeff.sub (Coeff.single j 1) (Coeff.single i 1)],
    List.mem_ofFn.mpr ⟨i, rfl⟩, ?_⟩
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

theorem buildLocalBound_adequate {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) :
    (∀ i j, |(R.vertex i).re - (R.vertex j).re| ≤
      evalCoeff R .horizontal B.horizontalDiameter) ∧
    (∀ i j, |(R.vertex i).im - (R.vertex j).im| ≤
      evalCoeff R .vertical B.verticalDiameter) ∧
    evalCoeff R .horizontal B.horizontalWidth =
      (R.vertex (C.rightVertex B.widthCell)).re -
        (R.vertex (C.leftVertex B.widthCell)).re ∧
    evalCoeff R .vertical B.verticalWidth =
      (R.vertex (C.topVertex B.widthCell)).im -
        (R.vertex (C.bottomVertex B.widthCell)).im := by
  simp only [buildLocalBound] at hB
  split at hB
  next hcell =>
    simp only [Option.some.injEq] at hB
    subst B
    constructor
    · intro i j
      rw [abs_le]
      constructor
      · have h := evalCoeff_le_maxCoeffList_of_mem R O .horizontal
            (signedDifference_mem_diameterCandidates C j i)
        simp [evalCoeff_sub, evalCoeff_single, CoordSort.axis,
          Tiling.AxisParallel.Axis.coord] at h
        linarith
      · have h := evalCoeff_le_maxCoeffList_of_mem R O .horizontal
            (signedDifference_mem_diameterCandidates C i j)
        simp [evalCoeff_sub, evalCoeff_single, CoordSort.axis,
          Tiling.AxisParallel.Axis.coord] at h
        linarith
    constructor
    · intro i j
      rw [abs_le]
      constructor
      · have h := evalCoeff_le_maxCoeffList_of_mem R O .vertical
            (signedDifference_mem_diameterCandidates C j i)
        simp [evalCoeff_sub, evalCoeff_single, CoordSort.axis,
          Tiling.AxisParallel.Axis.coord] at h
        linarith
      · have h := evalCoeff_le_maxCoeffList_of_mem R O .vertical
            (signedDifference_mem_diameterCandidates C i j)
        simp [evalCoeff_sub, evalCoeff_single, CoordSort.axis,
          Tiling.AxisParallel.Axis.coord] at h
        linarith
    constructor
    · simp [evalCoeff_sub, Coeff.cellRight, Coeff.cellLeft, evalCoeff_single,
        CoordSort.axis, Tiling.AxisParallel.Axis.coord]
    · simp [evalCoeff_sub, Coeff.cellTop, Coeff.cellBottom, evalCoeff_single,
        CoordSort.axis, Tiling.AxisParallel.Axis.coord]
  next hcell => simp at hB

theorem subdivision_exists {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) (N : Nat) (_hN : 0 < N) :
    ∃ q₁ q₂ : Nat, 0 < q₁ ∧ 0 < q₂ ∧
      2 * (N + 1) * evalCoeff R .horizontal B.horizontalDiameter <
        q₁ * evalCoeff R .horizontal B.horizontalWidth ∧
      2 * (N + 1) * evalCoeff R .vertical B.verticalDiameter <
        q₂ * evalCoeff R .vertical B.verticalWidth := by
  have hAdequate := buildLocalBound_adequate R O B hB
  have hhw : 0 < evalCoeff R .horizontal B.horizontalWidth := by
    rw [hAdequate.2.2.1]
    exact sub_pos.mpr (R.left_lt_right B.widthCell)
  have hvw : 0 < evalCoeff R .vertical B.verticalWidth := by
    rw [hAdequate.2.2.2]
    exact sub_pos.mpr (R.bottom_lt_top B.widthCell)
  obtain ⟨q₁, hq₁⟩ := exists_nat_gt
    ((2 * (N + 1) * evalCoeff R .horizontal B.horizontalDiameter) /
      evalCoeff R .horizontal B.horizontalWidth)
  obtain ⟨q₂, hq₂⟩ := exists_nat_gt
    ((2 * (N + 1) * evalCoeff R .vertical B.verticalDiameter) /
      evalCoeff R .vertical B.verticalWidth)
  refine ⟨q₁ + 1, q₂ + 1, Nat.zero_lt_succ _, Nat.zero_lt_succ _, ?_, ?_⟩
  · apply (div_lt_iff₀ hhw).mp
    exact lt_trans hq₁ (by exact_mod_cast Nat.lt_succ_self q₁)
  · apply (div_lt_iff₀ hvw).mp
    exact lt_trans hq₂ (by exact_mod_cast Nat.lt_succ_self q₂)

private theorem semanticLocalBox_isBounded {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N : Nat) :
    Bornology.IsBounded (semanticLocalBox R B N) := by
  let A := N * evalCoeff R .horizontal B.horizontalDiameter
  let D := N * evalCoeff R .vertical B.verticalDiameter
  rw [Metric.isBounded_iff_subset_ball 0]
  refine ⟨2 * (|A| + |D|) + 1, ?_⟩
  intro z hz
  have hre : |z.re| < |A| := by
    apply lt_of_lt_of_le (abs_lt.mpr ⟨hz.1, hz.2.1⟩)
    exact le_abs_self A
  have him : |z.im| < |D| := by
    apply lt_of_lt_of_le (abs_lt.mpr ⟨hz.2.2.1, hz.2.2.2⟩)
    exact le_abs_self D
  rw [Metric.mem_ball, dist_eq_norm]
  simp only [sub_zero]
  calc
    ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ < |A| + |D| := add_lt_add hre him
    _ < 2 * (|A| + |D|) + 1 := by
      nlinarith [abs_nonneg A, abs_nonneg D]

theorem contributingCentres_finite {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (_hB : buildLocalBound C O.toOracle = some B) (N : Nat) (S : Set Tiling.Plane)
    (hpacking : Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
      (R.region.toPolygonalRegion.placements S)) :
    {s : Tiling.Plane | s ∈ S ∧
      MeasureTheory.volume ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N) ≠ 0}.Finite := by
  apply ((Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).1
    (semanticLocalBox R B N - R.region.support)
    ((semanticLocalBox_isBounded R B N).sub R.region.isPolygonal.isBounded)).subset
  intro s hs
  refine ⟨hs.1, ?_⟩
  have hne : ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun hempty => hs.2 (by simp [hempty])
  obtain ⟨z, hzopen, hzbox⟩ := hne
  obtain ⟨k, hk, rfl⟩ := hzopen
  refine ⟨s + k, hzbox, k, interior_subset hk, ?_⟩
  simp

private theorem sum_indicator {n : Nat} (x : Fin n → Real) (i : Fin n) :
    ∑ j, ((if j = i then (1 : Int) else 0) : Real) * x j = x i := by
  simp

private theorem evalAffine_variableExpr {C : RegionCode} (R : Realization C)
    (s : CoordSort) {n : Nat} (x : Fin n → Real) (i : Fin n) :
    evalAffine R s (variableExpr C n i) x = x i := by
  rw [evalAffine]
  have hs : (∑ j, ((variableExpr C n i).variableCoefficient j : Real) * x j) = x i := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [variableExpr]
    · intro j _ hji
      simp [variableExpr, hji]
    · simp
  calc
    _ = x i + evalCoeff R s (variableExpr C n i).inputConstant :=
      congrArg (fun q => q + evalCoeff R s (Coeff.zero C)) hs
    _ = x i := by simp [variableExpr, evalCoeff, Coeff.zero]

private theorem evalAffine_translatedExpr {C : RegionCode} (R : Realization C)
    (s : CoordSort) {n : Nat} (x : Fin n → Real) (i : Fin n) (a : Coeff C) :
    evalAffine R s (translatedExpr i a) x = x i + evalCoeff R s a := by
  rw [evalAffine]
  have hs : (∑ j, ((translatedExpr i a).variableCoefficient j : Real) * x j) = x i := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [translatedExpr]
    · intro j _ hji
      simp [translatedExpr, hji]
    · simp
  exact congrArg (fun q => q + evalCoeff R s a) hs

private theorem evalAffine_constantExpr {C : RegionCode} (R : Realization C)
    (s : CoordSort) {n : Nat} (x : Fin n → Real) (a : Coeff C) :
    evalAffine R s (constantExpr C n a) x = evalCoeff R s a := by
  simp [evalAffine, constantExpr]

private theorem outsideClosedCell_holds {C : RegionCode} (R : Realization C)
    (m : Nat) (x y : Fin m → Real) (u v : Real) (i : Fin m) (e : Fin C.cellCount) :
    (outsideClosedCell C m i e).Holds R (Fin.cons u x) (Fin.cons v y) ↔
      ¬(x i + (R.vertex (C.leftVertex e)).re ≤ u ∧
        u ≤ x i + (R.vertex (C.rightVertex e)).re ∧
        y i + (R.vertex (C.bottomVertex e)).im ≤ v ∧
        v ≤ y i + (R.vertex (C.topVertex e)).im) := by
  simp [outsideClosedCell, listAnd, horizontalLe, verticalLe, Formula.Holds,
    evalAffine_translatedExpr, evalAffine_variableExpr,
    Coeff.cellLeft, Coeff.cellRight, Coeff.cellBottom, Coeff.cellTop,
    evalCoeff_single, CoordSort.axis, Tiling.AxisParallel.Axis.coord]

private theorem uncoveredPointBody_holds {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N m : Nat) (x y : Fin m → Real) (u v : Real) :
    (uncoveredPointBody C B N m).Holds R (Fin.cons u x) (Fin.cons v y) ↔
      (-(N * evalCoeff R .horizontal B.horizontalDiameter) < u ∧
        u < N * evalCoeff R .horizontal B.horizontalDiameter ∧
        -(N * evalCoeff R .vertical B.verticalDiameter) < v ∧
        v < N * evalCoeff R .vertical B.verticalDiameter) ∧
      ∀ i : Fin m, ∀ e : Fin C.cellCount,
        ¬(x i + (R.vertex (C.leftVertex e)).re ≤ u ∧
          u ≤ x i + (R.vertex (C.rightVertex e)).re ∧
          y i + (R.vertex (C.bottomVertex e)).im ≤ v ∧
          v ≤ y i + (R.vertex (C.topVertex e)).im) := by
  rw [uncoveredPointBody, listAnd_holds]
  simp only [List.mem_append]
  constructor
  · intro h
    have hfixed := fun f hf => h f (Or.inl hf)
    have htail := fun f hf => h f (Or.inr hf)
    constructor
    · simpa [horizontalLt, verticalLt, Formula.Holds,
        evalAffine_constantExpr, evalAffine_variableExpr, evalCoeff_neg,
        evalCoeff_nsmul] using hfixed
    · intro i e
      exact (outsideClosedCell_holds R m x y u v i e).mp
        (htail _ (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨i, rfl⟩,
          List.mem_ofFn.mpr ⟨e, rfl⟩⟩))
  · rintro ⟨hbox, hout⟩ f (hf | hf)
    · simp only [List.mem_cons] at hf
      rcases hf with rfl | rfl | rfl | rfl | hf
      · simpa [horizontalLt, Formula.Holds, evalAffine_constantExpr,
          evalAffine_variableExpr, evalCoeff_neg, evalCoeff_nsmul] using hbox.1
      · simpa [horizontalLt, Formula.Holds, evalAffine_constantExpr,
          evalAffine_variableExpr, evalCoeff_nsmul] using hbox.2.1
      · simpa [verticalLt, Formula.Holds, evalAffine_constantExpr,
          evalAffine_variableExpr, evalCoeff_neg, evalCoeff_nsmul] using hbox.2.2.1
      · simpa [verticalLt, Formula.Holds, evalAffine_constantExpr,
          evalAffine_variableExpr, evalCoeff_nsmul] using hbox.2.2.2
      · simp at hf
    · obtain ⟨row, hi, he⟩ := List.mem_flatten.mp hf
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hi
      obtain ⟨e, rfl⟩ := List.mem_ofFn.mp he
      exact (outsideClosedCell_holds R m x y u v i e).mpr (hout i e)

private def closedRealizedCell {C : RegionCode} (R : Realization C)
    (e : Fin C.cellCount) : Set Tiling.Plane :=
  {z | (R.vertex (C.leftVertex e)).re ≤ z.re ∧
    z.re ≤ (R.vertex (C.rightVertex e)).re ∧
    (R.vertex (C.bottomVertex e)).im ≤ z.im ∧
    z.im ≤ (R.vertex (C.topVertex e)).im}

private theorem isClosed_closedRealizedCell {C : RegionCode} (R : Realization C)
    (e : Fin C.cellCount) : IsClosed (closedRealizedCell R e) := by
  change IsClosed ({z : Tiling.Plane | _ ≤ z.re} ∩ ({z : Tiling.Plane | z.re ≤ _} ∩
    ({z : Tiling.Plane | _ ≤ z.im} ∩ {z : Tiling.Plane | z.im ≤ _})))
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le Complex.continuous_re continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))

private theorem semanticLocalBox_isOpen {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N : Nat) : IsOpen (semanticLocalBox R B N) := by
  exact isOpen_openRectangle _ _ _ _

private theorem coverageFormula_of_ae_cover {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N m : Nat) (x y : Fin m → Real)
    (hcover : ∀ᵐ z ∂MeasureTheory.volume, z ∈ semanticLocalBox R B N →
      ∃ i : Fin m,
        z ∈ (((x i : ℂ) + (y i : ℂ) * Complex.I) +ᵥ R.region.openCarrier)) :
    (coverageFormula C B N m).Holds R x y := by
  let c : Fin m → Tiling.Plane := fun i => (x i : ℂ) + (y i : ℂ) * Complex.I
  let F : Set Tiling.Plane := ⋃ i : Fin m, ⋃ e : Fin C.cellCount,
    c i +ᵥ closedRealizedCell R e
  have hFclosed : IsClosed F := by
    rw [show F = ⋃ i ∈ Set.univ, ⋃ e ∈ Set.univ,
        c i +ᵥ closedRealizedCell R e by simp [F]]
    apply Set.Finite.isClosed_biUnion (Set.toFinite Set.univ)
    intro i _
    apply Set.Finite.isClosed_biUnion (Set.toFinite Set.univ)
    intro e _
    exact (isClosed_closedRealizedCell R e).vadd _
  have hopenToCells :
      (⋃ i : Fin m, c i +ᵥ R.region.openCarrier) =ᵐ[MeasureTheory.volume]
        ⋃ i : Fin m, ⋃ e : Fin C.cellCount, c i +ᵥ realizedCell R e := by
    apply Filter.EventuallyEq.iUnion
    intro i
    exact translatedRegion_ae_cells R (c i)
  have hboxF : ∀ᵐ z ∂MeasureTheory.volume,
      z ∈ semanticLocalBox R B N → z ∈ F := by
    filter_upwards [hcover, hopenToCells] with z hzcover hzEq
    intro hzbox
    have hzCells := hzEq.mp (Set.mem_iUnion.mpr ⟨_, hzcover hzbox |>.choose_spec⟩)
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzCells
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hi
    obtain ⟨w, hw, rfl⟩ := he
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e, w,
      ⟨le_of_lt hw.1, le_of_lt hw.2.1, le_of_lt hw.2.2.1, le_of_lt hw.2.2.2⟩, rfl⟩⟩
  rw [coverageFormula, Formula.Holds]
  rintro ⟨u, v, huv⟩
  rw [uncoveredPointBody_holds] at huv
  rcases huv with ⟨hbox, hout⟩
  let z : Tiling.Plane := (u : ℂ) + (v : ℂ) * Complex.I
  have hzbox : z ∈ semanticLocalBox R B N := by
    simpa [z, semanticLocalBox] using hbox
  have hznotF : z ∉ F := by
    intro hzF
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzF
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hi
    obtain ⟨w, hw, hzw⟩ := he
    have hcoords : w.re = u - x i ∧ w.im = v - y i := by
      have hre := congrArg Complex.re hzw
      have him := congrArg Complex.im hzw
      dsimp [c, z] at hre him
      simp at hre him
      exact ⟨by linarith, by linarith⟩
    exact hout i e (by
      dsimp [closedRealizedCell] at hw
      rcases hw with ⟨hl, hr, hb, ht⟩
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩)
  have hnonempty : (semanticLocalBox R B N \ F).Nonempty := ⟨z, hzbox, hznotF⟩
  have hzero : MeasureTheory.volume (semanticLocalBox R B N \ F) = 0 := by
    have hnull := MeasureTheory.ae_iff.mp hboxF
    rw [show semanticLocalBox R B N \ F =
      {q | ¬(q ∈ semanticLocalBox R B N → q ∈ F)} by ext q; simp]
    exact hnull
  exact (semanticLocalBox_isOpen R B N).sdiff hFclosed |>.measure_ne_zero
    MeasureTheory.volume hnonempty hzero

theorem packing_adequate {C : RegionCode} (R : Realization C) (m : Nat) x y :
    (packingFormula C m).Holds R x y ↔
      ∀ i j : Fin m, i ≠ j →
        MeasureTheory.volume
          ((((x i : ℂ) + (y i : ℂ) * Complex.I) +ᵥ R.region.openCarrier) ∩
           (((x j : ℂ) + (y j : ℂ) * Complex.I) +ᵥ R.region.openCarrier)) = 0 := by
  rw [packingFormula, listAnd_holds]
  simp only [List.mem_flatten, List.mem_ofFn]
  constructor
  · intro h i j hij
    rw [translatedRegions_inter_null_iff_cells]
    intro e f
    rw [translatedCells_inter_null_iff]
    have hp := h (centrePairPacking C m i j)
      ⟨_, ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩
    simp only [centrePairPacking, if_neg hij, Formula.Holds] at hp
    have hs := hp.2
    rw [cellPairsSeparated, listAnd_holds] at hs
    have hef := hs (cellPairSeparated C m i j e f)
      (List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨e, rfl⟩,
        List.mem_ofFn.mpr ⟨f, rfl⟩⟩)
    rw [cellPairSeparated, listOr_holds] at hef
    simpa [cellPairSeparated, horizontalLe, verticalLe, Formula.Holds,
      evalAffine_variableExpr, evalAffine_translatedExpr,
      Coeff.cellLeft, Coeff.cellRight, Coeff.cellBottom, Coeff.cellTop,
      evalCoeff, Coeff.single, sum_indicator, CoordSort.axis,
      Tiling.AxisParallel.Axis.coord] using hef
  · intro h f hf
    obtain ⟨row, ⟨i, rfl⟩, hf⟩ := hf
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hf
    by_cases hij : i = j
    · subst j
      simp [centrePairPacking, Formula.Holds]
    · simp only [centrePairPacking, if_neg hij, Formula.Holds]
      constructor
      · rw [distinctCentres, listOr_holds]
        have hxy : x i ≠ x j ∨ y i ≠ y j := by
          by_contra hn
          push Not at hn
          have hz := h i j hij
          have hcentres : (x i : ℂ) + (y i : ℂ) * Complex.I =
              (x j : ℂ) + (y j : ℂ) * Complex.I := by
            apply Complex.ext <;> simp [hn.1, hn.2]
          rw [hcentres, Set.inter_self] at hz
          rw [MeasureTheory.measure_vadd] at hz
          have hne := (R.region.isPolygonal.interior_nonempty R.region.nonempty)
          exact (isOpen_interior.measure_ne_zero MeasureTheory.volume hne) hz
        rcases hxy with hx | hy
        · rcases lt_or_gt_of_ne hx with hlt | hgt
          · refine ⟨horizontalLt (variableExpr C m i) (variableExpr C m j), by simp, ?_⟩
            simpa [horizontalLt, Formula.Holds, evalAffine_variableExpr]
          · refine ⟨horizontalLt (variableExpr C m j) (variableExpr C m i), by simp, ?_⟩
            simpa [horizontalLt, Formula.Holds, evalAffine_variableExpr] using hgt
        · rcases lt_or_gt_of_ne hy with hlt | hgt
          · refine ⟨verticalLt (variableExpr C m i) (variableExpr C m j), by simp, ?_⟩
            simpa [verticalLt, Formula.Holds, evalAffine_variableExpr]
          · refine ⟨verticalLt (variableExpr C m j) (variableExpr C m i), by simp, ?_⟩
            simpa [verticalLt, Formula.Holds, evalAffine_variableExpr] using hgt
      · rw [cellPairsSeparated, listAnd_holds]
        intro g hg
        obtain ⟨row, he, hg⟩ := List.mem_flatten.mp hg
        obtain ⟨e, rfl⟩ := List.mem_ofFn.mp he
        obtain ⟨f, rfl⟩ := List.mem_ofFn.mp hg
        rw [cellPairSeparated, listOr_holds]
        have hc := (translatedRegions_inter_null_iff_cells R
          ((x i : ℂ) + (y i : ℂ) * Complex.I)
          ((x j : ℂ) + (y j : ℂ) * Complex.I)).mp (h i j hij) e f
        rw [translatedCells_inter_null_iff] at hc
        simpa [cellPairSeparated, horizontalLe, verticalLe, Formula.Holds,
          evalAffine_variableExpr, evalAffine_translatedExpr,
          Coeff.cellLeft, Coeff.cellRight, Coeff.cellBottom, Coeff.cellTop,
          evalCoeff, Coeff.single, sum_indicator, CoordSort.axis,
          Tiling.AxisParallel.Axis.coord] using hc

private theorem contributor_coordinate_bounds {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) (N : Nat) (s : Tiling.Plane)
    (hs : MeasureTheory.volume
      ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N) ≠ 0) :
    -(N + 1) * evalCoeff R .horizontal B.horizontalDiameter ≤ s.re ∧
    s.re ≤ (N + 1) * evalCoeff R .horizontal B.horizontalDiameter ∧
    -(N + 1) * evalCoeff R .vertical B.verticalDiameter ≤ s.im ∧
    s.im ≤ (N + 1) * evalCoeff R .vertical B.verticalDiameter := by
  have hae := (translatedRegion_ae_cells R s).inter
    (Filter.EventuallyEq.rfl : semanticLocalBox R B N =ᵐ[MeasureTheory.volume]
      semanticLocalBox R B N)
  have hunion : MeasureTheory.volume
      (((⋃ e, s +ᵥ realizedCell R e) ∩ semanticLocalBox R B N)) ≠ 0 := by
    intro hz
    exact hs (hae.measure_eq.trans hz)
  have hex : ∃ e, MeasureTheory.volume
      ((s +ᵥ realizedCell R e) ∩ semanticLocalBox R B N) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hunion
    rw [Set.iUnion_inter]
    exact MeasureTheory.measure_iUnion_null hn
  obtain ⟨e, he⟩ := hex
  have hne : ((s +ᵥ realizedCell R e) ∩ semanticLocalBox R B N).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr fun hempty => he (by simp [hempty])
  obtain ⟨z, ⟨k, hk, hzk⟩, hzbox⟩ := hne
  have hdiam := buildLocalBound_adequate R O B hB
  have hkReLo := hdiam.1 (C.leftVertex e) C.originVertex
  have hkReHi := hdiam.1 (C.rightVertex e) C.originVertex
  have hkImLo := hdiam.2.1 (C.bottomVertex e) C.originVertex
  have hkImHi := hdiam.2.1 (C.topVertex e) C.originVertex
  rw [R.origin_eq_zero] at hkReLo hkReHi hkImLo hkImHi
  simp only [Complex.zero_re, Complex.zero_im, sub_zero, abs_le] at hkReLo hkReHi hkImLo hkImHi
  have hcoords : z.re = s.re + k.re ∧ z.im = s.im + k.im := by
    subst z
    simp [vadd_eq_add]
  rcases hk with ⟨hkl, hkr, hkb, hkt⟩
  dsimp [semanticLocalBox] at hzbox
  constructor
  · linarith [hkReHi.1, hkReLo.1]
  constructor
  · linarith [hkReHi.2, hkReLo.2]
  constructor
  · linarith [hkImHi.1, hkImLo.1]
  · linarith [hkImHi.2, hkImLo.2]

private theorem ae_coveredByContributors {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N : Nat) (S : Set Tiling.Plane)
    (hpacking : Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
      (R.region.toPolygonalRegion.placements S))
    (hmult : ∀ᵐ z ∂MeasureTheory.volume, z ∈ semanticLocalBox R B N →
      Set.ncard {s : Tiling.Plane | s ∈ S ∧ z ∈ s +ᵥ R.region.openCarrier} = 1) :
    ∀ᵐ z ∂MeasureTheory.volume, z ∈ semanticLocalBox R B N →
      ∃ s, s ∈ S ∧
        MeasureTheory.volume ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N) ≠ 0 ∧
        z ∈ s +ᵥ R.region.openCarrier := by
  let F : Set Tiling.Plane := {s | s ∈ S ∧
    MeasureTheory.volume ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N) ≠ 0}
  let D : Set Tiling.Plane := S \ F
  have hDcount : D.Countable :=
    (Tiling.AxisParallel.IsPacking.locallyFinite_centres hpacking).2.mono Set.sdiff_subset
  let _ : Encodable D := hDcount.toEncodable
  let U : Set Tiling.Plane := ⋃ d : D,
    ((d.1 +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N)
  have hUzero : MeasureTheory.volume U = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro d
    by_contra hd
    exact d.2.2 ⟨d.2.1, hd⟩
  have havoid : ∀ᵐ z ∂MeasureTheory.volume, z ∉ U :=
    MeasureTheory.ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hUzero)
  filter_upwards [hmult, havoid] with z hzmult hzavoid
  intro hzbox
  obtain ⟨s, hsone⟩ := Set.ncard_eq_one.mp (hzmult hzbox)
  have hsMem : s ∈ {s : Tiling.Plane | s ∈ S ∧
      z ∈ s +ᵥ R.region.openCarrier} := hsone.symm ▸ Set.mem_singleton s
  rcases hsMem with ⟨hsS, hzs⟩
  refine ⟨s, hsS, ?_, hzs⟩
  by_contra hsnull
  have hsnotF : s ∉ F := by
    intro hsF
    exact hsF.2 hsnull
  exact hzavoid (Set.mem_iUnion.mpr ⟨⟨s, hsS, hsnotF⟩, hzs, hzbox⟩)

private theorem relevanceFormula_of_coordinate_bounds {C : RegionCode}
    (R : Realization C) (B : LocalBoundCode C) (N m : Nat)
    (x y : Fin m → Real)
    (h : ∀ i,
      -(N + 1) * evalCoeff R .horizontal B.horizontalDiameter ≤ x i ∧
      x i ≤ (N + 1) * evalCoeff R .horizontal B.horizontalDiameter ∧
      -(N + 1) * evalCoeff R .vertical B.verticalDiameter ≤ y i ∧
      y i ≤ (N + 1) * evalCoeff R .vertical B.verticalDiameter) :
    (relevanceFormula C B N m).Holds R x y := by
  rw [relevanceFormula, listAnd_holds]
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hf
  simp only [withinBoundHorizontal, withinBoundVertical, Formula.Holds,
    horizontalLe, verticalLe, evalAffine_constantExpr, evalAffine_variableExpr,
    evalCoeff_neg, evalCoeff_nsmul]
  rcases h i with ⟨hxl, hxr, hyl, hyr⟩
  norm_num [Nat.cast_add, Nat.cast_one] at hxl hxr hyl hyr ⊢
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

theorem semanticLocalPacking_formulaWitness {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) (N : Nat) (S : Set Tiling.Plane)
    (hpacking : Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
      (R.region.toPolygonalRegion.placements S))
    (hmult : ∀ᵐ z ∂MeasureTheory.volume, z ∈ semanticLocalBox R B N →
      Set.ncard {s : Tiling.Plane | s ∈ S ∧ z ∈ s +ᵥ R.region.openCarrier} = 1) :
    ∃ (m : Nat) (x y : Fin m → Real),
      (packingFormula C m).Holds R x y ∧
      (relevanceFormula C B N m).Holds R x y ∧
      (coverageFormula C B N m).Holds R x y := by
  let F : Set Tiling.Plane := {s | s ∈ S ∧
    MeasureTheory.volume ((s +ᵥ R.region.openCarrier) ∩ semanticLocalBox R B N) ≠ 0}
  have hFfinite : F.Finite := contributingCentres_finite R O B hB N S hpacking
  let _ : Fintype F := hFfinite.fintype
  let m := Fintype.card F
  let e : Fin m ≃ F := (Fintype.equivFin F).symm
  let x : Fin m → Real := fun i => (e i : Tiling.Plane).re
  let y : Fin m → Real := fun i => (e i : Tiling.Plane).im
  refine ⟨m, x, y, ?_, ?_, ?_⟩
  · rw [packing_adequate]
    intro i j hij
    have heij : (e i : Tiling.Plane) ≠ e j := fun h => hij (e.injective (Subtype.ext h))
    have hd := (isPacking_iff_openCarrier_disjoint R.region S).mp hpacking
      (e i).2.1 (e j).2.1 heij
    have hempty : ((e i : Tiling.Plane) +ᵥ R.region.openCarrier) ∩
        ((e j : Tiling.Plane) +ᵥ R.region.openCarrier) = ∅ := Set.disjoint_iff_inter_eq_empty.mp hd
    simpa [x, y, Complex.ext_iff] using congrArg MeasureTheory.volume hempty
  · apply relevanceFormula_of_coordinate_bounds
    intro i
    simpa [x, y] using contributor_coordinate_bounds R O B hB N (e i) (e i).2.2
  · apply coverageFormula_of_ae_cover
    filter_upwards [ae_coveredByContributors R B N S hpacking hmult] with z hz
    intro hzbox
    obtain ⟨s, hsS, hsvol, hzs⟩ := hz hzbox
    have hsF : s ∈ F := ⟨hsS, hsvol⟩
    obtain ⟨i, hi⟩ := e.surjective ⟨s, hsF⟩
    refine ⟨i, ?_⟩
    have hcenter : (e i : Tiling.Plane) = s := congrArg Subtype.val hi
    simpa [x, y, Complex.ext_iff, hcenter] using hzs

private noncomputable def subdivisionIndex (q : Nat) (A w x : Real) (_hq : 0 < q)
    (hw : 0 < w) (hspan : 2 * A < q * w) (hx : -A ≤ x ∧ x ≤ A) : Fin q :=
  ⟨Int.toNat ⌊(x + A) / w⌋, by
    rw [Int.toNat_lt]
    · rw [Int.floor_lt]
      rw [div_lt_iff₀ hw]
      norm_num at *
      linarith
    · rw [Int.floor_nonneg]
      exact div_nonneg (by linarith) (le_of_lt hw)⟩

private theorem subdivisionIndex_eq_implies_sub_lt (q : Nat) (A w x y : Real)
    (hq : 0 < q) (hw : 0 < w) (hspan : 2 * A < q * w)
    (hx : -A ≤ x ∧ x ≤ A) (hy : -A ≤ y ∧ y ≤ A)
    (heq : subdivisionIndex q A w x hq hw hspan hx =
      subdivisionIndex q A w y hq hw hspan hy) : |x - y| < w := by
  have hfx : 0 ≤ ⌊(x + A) / w⌋ := Int.floor_nonneg.mpr
    (div_nonneg (by linarith) (le_of_lt hw))
  have hfy : 0 ≤ ⌊(y + A) / w⌋ := Int.floor_nonneg.mpr
    (div_nonneg (by linarith) (le_of_lt hw))
  have hnat : Int.toNat ⌊(x + A) / w⌋ = Int.toNat ⌊(y + A) / w⌋ :=
    congrArg Fin.val heq
  have hfloor : ⌊(x + A) / w⌋ = ⌊(y + A) / w⌋ := by
    rw [← Int.toNat_of_nonneg hfx, ← Int.toNat_of_nonneg hfy, hnat]
  have hxl := Int.floor_le ((x + A) / w)
  have hxu := Int.lt_floor_add_one ((x + A) / w)
  have hyl := Int.floor_le ((y + A) / w)
  have hyu := Int.lt_floor_add_one ((y + A) / w)
  rw [hfloor] at hxl hxu
  rw [abs_lt]
  constructor <;> (rw [div_lt_iff₀ hw] at hxu hyu; rw [le_div_iff₀ hw] at hxl hyl) <;>
    linarith

private theorem coordinate_bounds_of_relevanceFormula {C : RegionCode}
    (R : Realization C) (B : LocalBoundCode C) (N m : Nat)
    (x y : Fin m → Real) (h : (relevanceFormula C B N m).Holds R x y) :
    ∀ i,
      -(N + 1) * evalCoeff R .horizontal B.horizontalDiameter ≤ x i ∧
      x i ≤ (N + 1) * evalCoeff R .horizontal B.horizontalDiameter ∧
      -(N + 1) * evalCoeff R .vertical B.verticalDiameter ≤ y i ∧
      y i ≤ (N + 1) * evalCoeff R .vertical B.verticalDiameter := by
  rw [relevanceFormula, listAnd_holds] at h
  intro i
  have hi := h _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
  simp only [withinBoundHorizontal, withinBoundVertical, Formula.Holds,
    horizontalLe, verticalLe, evalAffine_constantExpr, evalAffine_variableExpr,
    evalCoeff_neg, evalCoeff_nsmul] at hi
  rcases hi with ⟨⟨hxl, hxr⟩, hyl, hyr⟩
  norm_num [Nat.cast_add, Nat.cast_one] at hxl hxr hyl hyr ⊢
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem relevantPacking_cardinality {C : RegionCode} (R : Realization C)
    (O : CorrectOracle C R) (B : LocalBoundCode C)
    (hB : buildLocalBound C O.toOracle = some B) (c : RawNegativeCode)
    (hc : subdivisionWellFormed c = true)
    (hsub : (positiveSubdivisionFormula C B c).Holds R Fin.elim0 Fin.elim0)
    {m : Nat} (x y : Fin m → Real)
    (hpack : (packingFormula C m).Holds R x y)
    (hrel : (relevanceFormula C B c.boxIndex m).Holds R x y) :
    m ≤ localCardinalityBound c := by
  have hcpos : 0 < c.boxIndex ∧ 0 < c.horizontalSubdivisions ∧
      0 < c.verticalSubdivisions := by
    have h := (by simpa [subdivisionWellFormed, Bool.and_eq_true] using hc :
      (0 < c.boxIndex ∧ 0 < c.horizontalSubdivisions) ∧ 0 < c.verticalSubdivisions)
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hs := (positiveSubdivision_adequate R B c).mp hsub
  have hb := buildLocalBound_adequate R O B hB
  let wx := evalCoeff R .horizontal B.horizontalWidth
  let wy := evalCoeff R .vertical B.verticalWidth
  let Ax := (c.boxIndex + 1) * evalCoeff R .horizontal B.horizontalDiameter
  let Ay := (c.boxIndex + 1) * evalCoeff R .vertical B.verticalDiameter
  have hwx : 0 < wx := by
    dsimp [wx]
    rw [hb.2.2.1]
    linarith [R.left_lt_right B.widthCell]
  have hwy : 0 < wy := by
    dsimp [wy]
    rw [hb.2.2.2]
    linarith [R.bottom_lt_top B.widthCell]
  have hsx : 2 * Ax < c.horizontalSubdivisions * wx := by
    dsimp [Ax, wx]
    nlinarith [hs.1]
  have hsy : 2 * Ay < c.verticalSubdivisions * wy := by
    dsimp [Ay, wy]
    nlinarith [hs.2]
  have hbounds := coordinate_bounds_of_relevanceFormula R B c.boxIndex m x y hrel
  have hxbound : ∀ i, -Ax ≤ x i ∧ x i ≤ Ax := by
    intro i
    dsimp [Ax]
    rcases hbounds i with ⟨hxl, hxr, -⟩
    norm_num [Nat.cast_add, Nat.cast_one] at hxl hxr ⊢
    constructor <;> linarith
  have hybound : ∀ i, -Ay ≤ y i ∧ y i ≤ Ay := by
    intro i
    dsimp [Ay]
    rcases hbounds i with ⟨-, -, hyl, hyr⟩
    norm_num [Nat.cast_add, Nat.cast_one] at hyl hyr ⊢
    constructor <;> linarith
  let f : Fin m → Fin c.horizontalSubdivisions × Fin c.verticalSubdivisions := fun i =>
    (subdivisionIndex c.horizontalSubdivisions Ax wx (x i) hcpos.2.1 hwx hsx
      (hxbound i),
     subdivisionIndex c.verticalSubdivisions Ay wy (y i) hcpos.2.2 hwy hsy
      (hybound i))
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hxclose := subdivisionIndex_eq_implies_sub_lt
      c.horizontalSubdivisions Ax wx (x i) (x j) hcpos.2.1 hwx hsx
      (hxbound i) (hxbound j)
      (congrArg Prod.fst hij)
    have hyclose := subdivisionIndex_eq_implies_sub_lt
      c.verticalSubdivisions Ay wy (y i) (y j) hcpos.2.2 hwy hsy
      (hybound i) (hybound j) (congrArg Prod.snd hij)
    have hp := (packing_adequate R m x y).mp hpack i j hne
    have hcell := (translatedRegions_inter_null_iff_cells R
      ((x i : ℂ) + (y i : ℂ) * Complex.I)
      ((x j : ℂ) + (y j : ℂ) * Complex.I)).mp hp
      B.widthCell B.widthCell
    rw [translatedCells_inter_null_iff] at hcell
    rcases hcell with hsep | hsep | hsep | hsep
    all_goals rw [abs_lt] at hxclose hyclose
    · dsimp [wx] at hwx hxclose
      rw [hb.2.2.1] at hxclose
      linarith
    · dsimp [wx] at hwx hxclose
      rw [hb.2.2.1] at hxclose
      linarith
    · dsimp [wy] at hwy hyclose
      rw [hb.2.2.2] at hyclose
      linarith
    · dsimp [wy] at hwy hyclose
      rw [hb.2.2.2] at hyclose
      linarith
  change m ≤ c.horizontalSubdivisions * c.verticalSubdivisions
  simpa using Fintype.card_le_of_injective f hf

end Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch

open MeasureTheory Set

namespace Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch

/-- A finite local cover extracted from a true local-cover formula. -/
theorem localCoverFormula_sound {C : RegionCode} (R : Realization C)
    (B : LocalBoundCode C) (N m : Nat)
    (hformula : (localCoverFormula C B N m).Holds R Fin.elim0 Fin.elim0) :
    ∃ S : Set Tiling.Plane, S.Finite ∧
      Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
        (R.region.toPolygonalRegion.placements S) ∧
      (∀ᵐ z ∂volume, z ∈ semanticLocalBox R B N →
        ∃ s ∈ S, z ∈ s +ᵥ R.region.openCarrier) := by
  obtain ⟨x, y, hpack, _hrel, hcoverage⟩ :=
    localCover_adequate R B N m |>.mp hformula
  change ¬ ∃ u v : Real, _ at hcoverage
  let centre : Fin m → Tiling.Plane := fun i =>
    (x i : ℂ) + (y i : ℂ) * Complex.I
  let S : Set Tiling.Plane := Set.range centre
  have hfinite : S.Finite := Set.finite_range centre
  have hpacking : Tiling.IsPacking R.region.toPolygonalRegion.prototileFamily
      (R.region.toPolygonalRegion.placements S) := by
    apply (isPacking_iff_openCarrier_disjoint R.region S).mpr
    intro s hs t ht hst
    rcases hs with ⟨i, rfl⟩
    rcases ht with ⟨j, rfl⟩
    have hij : i ≠ j := by
      intro hij
      apply hst
      simp [hij]
    have hvol := (packing_adequate R m x y).mp hpack i j hij
    apply Set.disjoint_left.2
    intro z hzi hzj
    have hopen : IsOpen ((centre i +ᵥ R.region.openCarrier) ∩
        (centre j +ᵥ R.region.openCarrier)) :=
      (R.region.openCarrier_regularOpen.1.vadd _).inter
        (R.region.openCarrier_regularOpen.1.vadd _)
    have hne : ((centre i +ᵥ R.region.openCarrier) ∩
        (centre j +ᵥ R.region.openCarrier)).Nonempty := ⟨z, hzi, hzj⟩
    exact (hopen.measure_ne_zero volume hne) (by simpa [centre] using hvol)
  have hclosed : ∀ z ∈ semanticLocalBox R B N, ∃ i : Fin m, ∃ e : Fin C.cellCount,
      z ∈ centre i +ᵥ closedRealizedCell R e := by
    intro z hz
    by_contra hnone
    apply hcoverage
    refine ⟨z.re, z.im, ?_⟩
    apply (uncoveredPointBody_holds R B N m x y z.re z.im).mpr
    refine ⟨?_, ?_⟩
    · simpa [semanticLocalBox] using hz
    · intro i e hcell
      apply hnone
      refine ⟨i, e, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [centre, closedRealizedCell, vadd_eq_add] using hcell
  have volume_re_eq_zero_local (a : ℝ) :
      volume {z : Tiling.Plane | z.re = a} = 0 := by
    let H : Set Tiling.Plane := {z | z.re = a}
    have hclosedH : IsClosed H := isClosed_eq Complex.continuous_re continuous_const
    have hinter : interior H = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨w, hw⟩
      obtain ⟨ε, hε, hwε⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
      have hw' := hwε (show w + (ε / 2 : ℝ) ∈ Metric.ball w ε by
        rw [Metric.mem_ball, Complex.dist_eq]
        simpa [Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
      have hwmem : w ∈ H := interior_subset hw
      have hw'mem : w + (ε / 2 : ℝ) ∈ H := interior_subset hw'
      have hwre : w.re = a := hwmem
      have hw're : (w + (ε / 2 : ℝ)).re = a := hw'mem
      simp only [Complex.add_re, Complex.ofReal_re] at hw're
      linarith
    have hfrontier : frontier H = H := by
      rw [frontier, hclosedH.closure_eq, hinter, sdiff_empty]
    change volume H = 0
    rw [← hfrontier]
    exact (convex_hyperplane Complex.reLm.isLinear a).addHaar_frontier volume
  have volume_im_eq_zero_local (a : ℝ) :
      volume {z : Tiling.Plane | z.im = a} = 0 := by
    let H : Set Tiling.Plane := {z | z.im = a}
    have hclosedH : IsClosed H := isClosed_eq Complex.continuous_im continuous_const
    have hinter : interior H = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨w, hw⟩
      obtain ⟨ε, hε, hwε⟩ := Metric.isOpen_iff.mp isOpen_interior w hw
      have hw' := hwε (show w + (ε / 2 : ℝ) * Complex.I ∈ Metric.ball w ε by
        rw [Metric.mem_ball, Complex.dist_eq]
        simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
      have hwmem : w ∈ H := interior_subset hw
      have hw'mem : w + (ε / 2 : ℝ) * Complex.I ∈ H := interior_subset hw'
      have hwim : w.im = a := hwmem
      have hw'im : (w + (ε / 2 : ℝ) * Complex.I).im = a := hw'mem
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hw'im
      linarith
    have hfrontier : frontier H = H := by
      rw [frontier, hclosedH.closure_eq, hinter, sdiff_empty]
    change volume H = 0
    rw [← hfrontier]
    exact (convex_hyperplane Complex.imLm.isLinear a).addHaar_frontier volume
  let U : Set Tiling.Plane := ⋃ i : Fin m, ⋃ e : Fin C.cellCount,
      centre i +ᵥ realizedCell R e
  let V : Set Tiling.Plane := ⋃ i : Fin m, ⋃ e : Fin C.cellCount,
    ({z : Tiling.Plane | z.re = (centre i).re +
        (R.vertex (C.leftVertex e)).re} ∪
      ({z : Tiling.Plane | z.re = (centre i).re +
        (R.vertex (C.rightVertex e)).re} ∪
        ({z : Tiling.Plane | z.im = (centre i).im +
          (R.vertex (C.bottomVertex e)).im} ∪
          {z : Tiling.Plane | z.im = (centre i).im +
            (R.vertex (C.topVertex e)).im})))
  have hboundary : volume (semanticLocalBox R B N \ U) = 0 := by
    refine measure_mono_null (s := semanticLocalBox R B N \ U) (t := V) ?_ ?_
    · intro z hz
      change z ∈ ⋃ i : Fin m, ⋃ e : Fin C.cellCount, _
      obtain ⟨i, e, hzc⟩ := hclosed z hz.1
      have hnotopen : z ∉ centre i +ᵥ realizedCell R e := by
        intro hopen
        exact hz.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e, hopen⟩⟩)
      obtain ⟨w, hw, rfl⟩ := hzc
      have hwclosed : w ∈ closedRealizedCell R e := hw
      have hboundary' :
          w.re = (R.vertex (C.leftVertex e)).re ∨
          w.re = (R.vertex (C.rightVertex e)).re ∨
          w.im = (R.vertex (C.bottomVertex e)).im ∨
          w.im = (R.vertex (C.topVertex e)).im := by
        by_contra hnb
        push Not at hnb
        have hwopen : w ∈ realizedCell R e := by
          dsimp [realizedCell, openRectangle]
          exact ⟨lt_of_le_of_ne hwclosed.1 hnb.1.symm,
            lt_of_le_of_ne hwclosed.2.1 hnb.2.1,
            lt_of_le_of_ne hwclosed.2.2.1 hnb.2.2.1.symm,
            lt_of_le_of_ne hwclosed.2.2.2 hnb.2.2.2⟩
        exact hnotopen ⟨w, hwopen, rfl⟩
      rcases hboundary' with h | h | h | h
      · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e,
          Or.inl (by simpa [centre, vadd_eq_add] using h)⟩⟩
      · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e,
          Or.inr (Or.inl (by simpa [centre, vadd_eq_add] using h))⟩⟩
      · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e,
          Or.inr (Or.inr (Or.inl (by simpa [centre, vadd_eq_add] using h)))⟩⟩
      · exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨e,
          Or.inr (Or.inr (Or.inr (by simpa [centre, vadd_eq_add] using h)))⟩⟩
    · dsimp [V]
      apply measure_iUnion_null
      intro i
      apply measure_iUnion_null
      intro e
      apply measure_union_null
      · exact volume_re_eq_zero_local _
      · apply measure_union_null
        · exact volume_re_eq_zero_local _
        · apply measure_union_null
          · exact volume_im_eq_zero_local _
          · exact volume_im_eq_zero_local _
  have hEq : (⋃ i : Fin m, centre i +ᵥ R.region.openCarrier) =ᵐ[volume] U := by
    apply Filter.EventuallyEq.iUnion
    intro i
    exact translatedRegion_ae_cells R (centre i)
  have hnot : ∀ᵐ z ∂volume, z ∉ semanticLocalBox R B N \ U :=
    MeasureTheory.ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hboundary)
  refine ⟨S, hfinite, hpacking, ?_⟩
  filter_upwards [hnot, hEq] with z hznot hzEq hzbox
  have hzU : z ∈ U := by
    by_contra hzU
    exact hznot ⟨hzbox, hzU⟩
  have hzopen : z ∈ ⋃ i : Fin m, centre i +ᵥ R.region.openCarrier := hzEq.mpr hzU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzopen
  exact ⟨centre i, Set.mem_range.mpr ⟨i, rfl⟩, hi⟩

end Tiling.AxisParallel.Terminal.Executable.LocalCoverSearch
