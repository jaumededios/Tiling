import Tiling.RationalSlopes.Basic
import Tiling.Approximation.RationalLinear
import Mathlib.Analysis.Convex.KreinMilman

/-!
# Rational line geometry and polygonal approximation

Finite rational line arrangements provide polygonal supports and rational-linear
approximation maps, with boundary agreement and continuous inverse.
-/

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Approximation
open Tiling.RationalPolygonal (IntegerPlane integerPoint integerPoint_injective)

noncomputable section

namespace Tiling.RationalSlopes.Approximation


private def perpendicularVector (x y : ℝ) : Plane := -y + x * Complex.I

private theorem normalKernel_eq_span_perpendicular (x y : ℝ)
    (hne : x ≠ 0 ∨ y ≠ 0) :
    LinearMap.ker ((x • Complex.reCLM + y • Complex.imCLM).toLinearMap) =
      Submodule.span ℝ ({perpendicularVector x y} : Set Plane) := by
  let v := perpendicularVector x y
  have hv : v ≠ 0 := by
    intro hv
    have hre := congrArg Complex.re hv
    have him := congrArg Complex.im hv
    simp [v, perpendicularVector] at hre him
    rcases hne with hx | hy
    · exact hx him
    · exact hy hre
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    change x * z.re + y * z.im = 0 at hz
    rw [Submodule.mem_span_singleton]
    rcases hne with hx | hy
    · refine ⟨z.im / x, ?_⟩
      apply Complex.ext
      · simp [perpendicularVector]
        field_simp
        nlinarith [hz]
      · simp [perpendicularVector]
        field_simp
    · have hy' : y ≠ 0 := hy
      refine ⟨-z.re / y, ?_⟩
      apply Complex.ext
      · simp [perpendicularVector]
        field_simp
      · simp [perpendicularVector]
        field_simp
        nlinarith [hz]
  · rw [Submodule.span_singleton_le_iff_mem]
    rw [LinearMap.mem_ker]
    change x * (perpendicularVector x y).re +
      y * (perpendicularVector x y).im = 0
    simp [perpendicularVector]
    ring

theorem normalDirection_rational :
  ∀ n : RationalNormal, Module.finrank ℝ (normalDirection n) = 1 ∧
    Tiling.RationalSlopes.HasRationalDirection (normalDirection n) := by
  intro n
  let v := perpendicularVector (n.x : ℝ) (n.y : ℝ)
  have hn : (n.x : ℝ) ≠ 0 ∨ (n.y : ℝ) ≠ 0 := by
    rcases n.nonzero with hx | hy
    · exact Or.inl (by exact_mod_cast hx)
    · exact Or.inr (by exact_mod_cast hy)
  have hv : v ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [v, perpendicularVector] at him
    rcases hn with hx | hy
    · exact hx (by exact_mod_cast him)
    · have hre := congrArg Complex.re h
      simp [v, perpendicularVector] at hre
      exact hy (by exact_mod_cast hre)
  have hker : normalDirection n = Submodule.span ℝ ({v} : Set Plane) := by
    simpa [normalDirection, v] using
      (normalKernel_eq_span_perpendicular (n.x : ℝ) (n.y : ℝ) hn)
  constructor
  · rw [hker, finrank_span_singleton]
    simp [hv]
  · let p : IntegerPlane := ![-n.y.num * n.x.den, n.x.num * n.y.den]
    have hp : p ≠ 0 := by
      intro hp
      have he : -n.y.num * n.x.den = 0 := by simpa [p] using congrFun hp 0
      have hd : n.x.num * n.y.den = 0 := by simpa [p] using congrFun hp 1
      rcases n.nonzero with hx | hy
      · have hnum : n.x.num = 0 := by
          have hden : (n.y.den : ℤ) ≠ 0 := by exact_mod_cast n.y.den_nz
          exact (mul_eq_zero.mp hd).resolve_right hden
        exact hx (Rat.num_eq_zero.mp hnum)
      · have hnum : n.y.num = 0 := by
          have hden : (n.x.den : ℤ) ≠ 0 := by exact_mod_cast n.x.den_nz
          have : n.y.num * n.x.den = 0 := by nlinarith
          exact (mul_eq_zero.mp this).resolve_right hden
        exact hy (Rat.num_eq_zero.mp hnum)
    have hpv : integerPoint p = ((n.x.den : ℝ) * n.y.den) • v := by
      apply Complex.ext
      · simp [p, v, perpendicularVector, integerPoint, Rat.cast_def]
        field_simp
      · simp [p, v, perpendicularVector, integerPoint, Rat.cast_def]
        field_simp
    refine ⟨p, hp, ?_⟩
    rw [hker]
    rw [hpv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem rationalDirection_hasNormal :
  ∀ δ : Submodule ℝ Plane, Module.finrank ℝ δ = 1 →
    Tiling.RationalSlopes.HasRationalDirection δ →
      ∃ n : RationalNormal, normalDirection n = δ := by
  intro δ hdim ⟨p, hp, hpδ⟩
  let z : Plane := integerPoint p
  let n : RationalNormal := ⟨p 1, -(p 0), by
    by_cases h0 : p 0 = 0
    · left
      intro h1
      have hp1 : p 1 = 0 := by exact_mod_cast h1
      apply hp
      funext i
      fin_cases i <;> simp [h0, hp1]
    · right
      intro h1
      have hp0 : p 0 = 0 := by
        have : -(p 0 : ℚ) = 0 := by exact_mod_cast h1
        exact_mod_cast (neg_eq_zero.mp this)
      exact h0 hp0⟩
  have hz : z ≠ 0 := by
    intro hz
    apply hp
    exact integerPoint_injective (by simpa [z] using hz)
  have hspan : δ = Submodule.span ℝ ({z} : Set Plane) := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact Submodule.span_le.mpr (by simpa [z] using hpδ)
    · have hrank : Module.finrank ℝ (Submodule.span ℝ ({z} : Set Plane)) = 1 :=
        finrank_span_singleton hz
      rw [hrank, hdim]
  have hnormal : normalDirection n = Submodule.span ℝ ({z} : Set Plane) := by
    have hx : (n.x : ℝ) = z.im := by simp [n, z, integerPoint]
    have hy : (n.y : ℝ) = -z.re := by simp [n, z, integerPoint]
    have hkernel := normalKernel_eq_span_perpendicular (n.x : ℝ) (n.y : ℝ) (by
      rcases n.nonzero with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h))
    have hv : perpendicularVector z.im (-z.re) = z := by
      apply Complex.ext <;> simp [perpendicularVector]
    simpa [normalDirection, hx, hy, hv] using hkernel
  exact ⟨n, hnormal.trans hspan.symm⟩

structure RationalLine where
  normal : RationalNormal
  offset : ℝ

def RationalLine.eval (l : RationalLine) (z : Plane) : ℝ :=
  normalEval l.normal z - l.offset

def deformLine (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) : RationalLine :=
  ⟨l.normal, (φ l.offset : ℝ)⟩

/-- The intersection formulas have rational coefficients; concurrency is exact, not merely
stable under small perturbation. This is the core finite-arrangement algebraic helper. -/
theorem rationalLine_pairIntersection :
  ∀ l m : RationalLine,
    l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∃ z : Plane, l.eval z = 0 ∧ m.eval z = 0 ∧
        (∀ w : Plane, l.eval w = 0 → m.eval w = 0 → w = z) ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ,
          (deformLine φ l).eval (deformPoint φ z) = 0 ∧
            (deformLine φ m).eval (deformPoint φ z) = 0 := by
  intro l m hdet
  let d : ℝ := (l.normal.x : ℝ) * (m.normal.y : ℝ) -
    (l.normal.y : ℝ) * (m.normal.x : ℝ)
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast hdet
  let z : Plane := Complex.mk
    ((l.offset * (m.normal.y : ℝ) - (l.normal.y : ℝ) * m.offset) / d)
    (((l.normal.x : ℝ) * m.offset - l.offset * (m.normal.x : ℝ)) / d)
  have hl : l.eval z = 0 := by
    dsimp [RationalLine.eval, normalEval, z]
    field_simp
    ring
  have hm : m.eval z = 0 := by
    dsimp [RationalLine.eval, normalEval, z]
    field_simp
    ring
  refine ⟨z, hl, hm, ?_, ?_⟩
  · intro w hlw hmw
    dsimp [RationalLine.eval, normalEval] at hlw hmw
    apply Complex.ext
    · change w.re = (l.offset * (m.normal.y : ℝ) -
        (l.normal.y : ℝ) * m.offset) / d
      apply (eq_div_iff hd).2
      dsimp [d]
      linear_combination (m.normal.y : ℝ) * hlw - (l.normal.y : ℝ) * hmw
    · change w.im = ((l.normal.x : ℝ) * m.offset -
        l.offset * (m.normal.x : ℝ)) / d
      apply (eq_div_iff hd).2
      dsimp [d]
      linear_combination (l.normal.x : ℝ) * hmw - (m.normal.x : ℝ) * hlw
  · intro φ
    have commute (n : RationalNormal) (w : Plane) :
        normalEval n (deformPoint φ w) = (φ (normalEval n w) : ℝ) := by
      dsimp [normalEval, deformPoint]
      have hx := φ.map_smul n.x w.re
      have hy := φ.map_smul n.y w.im
      simp only [Rat.smul_def] at hx hy
      rw [map_add, hx, hy]
      push_cast
      rfl
    constructor
    · change normalEval l.normal (deformPoint φ z) - (φ l.offset : ℝ) = 0
      rw [commute, sub_eq_zero.mp hl, sub_self]
    · change normalEval m.normal (deformPoint φ z) - (φ m.offset : ℝ) = 0
      rw [commute, sub_eq_zero.mp hm, sub_self]

abbrev PolyhedralCode := List (List RationalLine)

def polyhedralSupport (P : PolyhedralCode) : Set Plane :=
  {z | ∃ cell ∈ P, ∀ l ∈ cell, l.eval z ≤ 0}

def deformedPolyhedralSupport (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) : Set Plane :=
  polyhedralSupport (P.map (fun cell => cell.map (deformLine φ)))

private def closedCell (cell : List RationalLine) : Set Plane :=
  {z | ∀ l ∈ cell, l.eval z ≤ 0}

private def openCell (cell : List RationalLine) : Set Plane :=
  {z | ∀ l ∈ cell, l.eval z < 0}

private theorem lineEval_continuous (l : RationalLine) : Continuous l.eval := by
  change Continuous (fun z : Plane =>
    (l.normal.x : ℝ) * z.re + (l.normal.y : ℝ) * z.im - l.offset)
  fun_prop

private theorem closedCell_isClosed (cell : List RationalLine) :
    IsClosed (closedCell cell) := by
  change IsClosed {z | ∀ l, ∀ (_ : l ∈ cell), l.eval z ≤ 0}
  simp only [ofPred_forall]
  exact isClosed_iInter fun l => isClosed_iInter fun _ =>
    isClosed_le (lineEval_continuous l) continuous_const

private theorem openCell_isOpen (cell : List RationalLine) : IsOpen (openCell cell) := by
  induction cell with
  | nil => simp [openCell]
  | cons l cell ih =>
    have heq : openCell (l :: cell) = {z | l.eval z < 0} ∩ openCell cell := by
      ext z
      simp [openCell]
    rw [heq]
    exact (isOpen_lt (lineEval_continuous l) continuous_const).inter ih

private theorem normalEval_isLinear (n : RationalNormal) :
    IsLinearMap ℝ (normalEval n) := by
  change IsLinearMap ℝ
    (((n.x : ℝ) • Complex.reCLM + (n.y : ℝ) • Complex.imCLM).toLinearMap)
  exact LinearMap.isLinear _

private theorem closedCell_convex (cell : List RationalLine) : Convex ℝ (closedCell cell) := by
  induction cell with
  | nil => simpa [closedCell] using convex_univ (𝕜 := ℝ) (E := Plane)
  | cons l cell ih =>
    have heq : closedCell (l :: cell) =
        {z | normalEval l.normal z ≤ l.offset} ∩ closedCell cell := by
      ext z
      simp [closedCell, RationalLine.eval]
    rw [heq]
    exact (convex_halfSpace_le (normalEval_isLinear l.normal) l.offset).inter ih

/-- Krein-Milman is used only after an actual finite extreme-point proof. It is not a
triangulation existence theorem. The finite hull is closed, so no closure remains. -/
private theorem closedCell_eq_convexHull_extremePoints (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell))
    (hfinite : ((closedCell cell).extremePoints ℝ).Finite) :
    closedCell cell = convexHull ℝ ((closedCell cell).extremePoints ℝ) := by
  have hKM := closure_convexHull_extremePoints hcompact (closedCell_convex cell)
  rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at hKM
  exact hKM.symm

private theorem openCell_convex (cell : List RationalLine) : Convex ℝ (openCell cell) := by
  induction cell with
  | nil => simpa [openCell] using convex_univ (𝕜 := ℝ) (E := Plane)
  | cons l cell ih =>
    have heq : openCell (l :: cell) =
        {z | normalEval l.normal z < l.offset} ∩ openCell cell := by
      ext z
      simp [openCell, RationalLine.eval]
    rw [heq]
    exact (convex_halfSpace_lt (normalEval_isLinear l.normal) l.offset).inter ih

private theorem lineEval_combo (l : RationalLine) (x y : Plane) (a b : ℝ)
    (hab : a + b = 1) : l.eval (a • x + b • y) = a * l.eval x + b * l.eval y := by
  simp only [RationalLine.eval, normalEval, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  linear_combination l.offset * hab

private def tangentNormal (n : RationalNormal) : RationalNormal :=
  ⟨-n.y, n.x, by
    rcases n.nonzero with hx | hy
    · exact Or.inr hx
    · exact Or.inl (neg_ne_zero.mpr hy)⟩

private theorem normal_tangent_ext (n : RationalNormal) (z w : Plane)
    (hn : normalEval n z = normalEval n w)
    (ht : normalEval (tangentNormal n) z = normalEval (tangentNormal n) w) : z = w := by
  have hdet : n.x * (tangentNormal n).y - n.y * (tangentNormal n).x ≠ 0 := by
    dsimp [tangentNormal]
    rcases n.nonzero with hx | hy
    · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg n.y]
    · nlinarith [sq_pos_of_ne_zero hy, sq_nonneg n.x]
  let l : RationalLine := ⟨n, normalEval n z⟩
  let m : RationalLine := ⟨tangentNormal n, normalEval (tangentNormal n) z⟩
  obtain ⟨x, _, _, huniq, _⟩ := rationalLine_pairIntersection l m hdet
  have hz : z = x := huniq z (by simp [l, RationalLine.eval])
    (by simp [m, RationalLine.eval])
  have hw : w = x := huniq w (by simp [l, RationalLine.eval, hn])
    (by simp [m, RationalLine.eval, ht])
  exact hz.trans hw.symm

private theorem normalEval_combo (n : RationalNormal) (x y : Plane) (a b : ℝ)
    (hab : a + b = 1) :
    normalEval n (a • x + b • y) = a * normalEval n x + b * normalEval n y := by
  simpa only [RationalLine.eval, sub_zero] using
    lineEval_combo (⟨n, 0⟩ : RationalLine) x y a b hab

private def cellFace (cell : List RationalLine) (l : RationalLine) : Set Plane :=
  closedCell cell ∩ {z | l.eval z = 0}

/-- A nonempty compact line face is its actual endpoint segment. Degenerate singleton faces
are retained here and discarded only when constructing nondegenerate triangular pieces. -/
private theorem cellFace_eq_segment (cell : List RationalLine) (l : RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (cellFace cell l).Nonempty) :
    ∃ a b : Plane, cellFace cell l = segment ℝ a b := by
  let t := tangentNormal l.normal
  have hfaceCompact : IsCompact (cellFace cell l) :=
    hcompact.inter_right (isClosed_eq (lineEval_continuous l) continuous_const)
  have htcont : Continuous (normalEval t) := by
    change Continuous (fun z : Plane => (t.x : ℝ) * z.re + (t.y : ℝ) * z.im)
    fun_prop
  obtain ⟨a, ha, hmin⟩ := hfaceCompact.exists_isMinOn hne htcont.continuousOn
  obtain ⟨b, hb, hmax⟩ := hfaceCompact.exists_isMaxOn hne htcont.continuousOn
  have hfaceConvex : Convex ℝ (cellFace cell l) := by
    have heq : cellFace cell l =
        closedCell cell ∩ {z | normalEval l.normal z = l.offset} := by
      ext z
      simp [cellFace, RationalLine.eval, sub_eq_zero]
    rw [heq]
    exact (closedCell_convex cell).inter
      (convex_hyperplane (normalEval_isLinear l.normal) l.offset)
  refine ⟨a, b, subset_antisymm ?_ (hfaceConvex.segment_subset ha hb)⟩
  intro z hz
  have han : normalEval l.normal a = l.offset := sub_eq_zero.mp ha.2
  have hbn : normalEval l.normal b = l.offset := sub_eq_zero.mp hb.2
  have hzn : normalEval l.normal z = l.offset := sub_eq_zero.mp hz.2
  have haz : normalEval t a ≤ normalEval t z := hmin hz
  have hzb : normalEval t z ≤ normalEval t b := hmax hz
  by_cases heq : normalEval t b = normalEval t a
  · have hza : z = a := normal_tangent_ext l.normal z a
      (hzn.trans han.symm) (le_antisymm (heq ▸ hzb) haz)
    exact hza.symm ▸ left_mem_segment ℝ a b
  · have hden : 0 < normalEval t b - normalEval t a := by
      have hab := hmin hb
      exact sub_pos.mpr (lt_of_le_of_ne hab (Ne.symm heq))
    let r : ℝ := (normalEval t z - normalEval t a) /
      (normalEval t b - normalEval t a)
    have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr haz) hden.le
    have hr1 : r ≤ 1 := (div_le_one hden).mpr (by linarith)
    have hcombo : (1 - r) • a + r • b = z := by
      apply normal_tangent_ext l.normal
      · rw [normalEval_combo l.normal a b (1-r) r (by ring), han, hbn, hzn]
        ring
      · change normalEval t ((1-r) • a + r • b) = normalEval t z
        rw [normalEval_combo t a b (1-r) r (by ring)]
        dsimp [r]
        field_simp
        ring
    exact ⟨1-r, r, sub_nonneg.mpr hr1, hr, by ring, hcombo⟩

private def tangentToNormal (n : RationalNormal) : Plane :=
  -(n.y : ℝ) + (n.x : ℝ) * Complex.I

private theorem perturb_normalEval_add (n : RationalNormal) (z w : Plane) :
    normalEval n (z + w) = normalEval n z + normalEval n w := by
  simp [normalEval, Complex.add_re, Complex.add_im]
  ring

private theorem perturb_normalEval_sub (n : RationalNormal) (z w : Plane) :
    normalEval n (z - w) = normalEval n z - normalEval n w := by
  simp [normalEval, Complex.sub_re, Complex.sub_im]
  ring

private theorem normalEval_smul (n : RationalNormal) (r : ℝ) (z : Plane) :
    normalEval n (r • z) = r * normalEval n z := by
  simp [normalEval, Complex.mul_re, Complex.mul_im]
  ring

private theorem line_perturb_formula (l : RationalLine) (x u : Plane) (t : ℝ) :
    l.eval (x + t • u) = l.eval x + t * normalEval l.normal u ∧
      l.eval (x - t • u) = l.eval x - t * normalEval l.normal u := by
  constructor
  · simp only [RationalLine.eval, perturb_normalEval_add, normalEval_smul]
    ring
  · simp only [RationalLine.eval, perturb_normalEval_sub, normalEval_smul]
    ring

private theorem line_perturb_nonpos_eventually (l : RationalLine) (x u : Plane)
    (hle : l.eval x ≤ 0)
    (hactive : l.eval x = 0 → normalEval l.normal u = 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      l.eval (x + t • u) ≤ 0 ∧ l.eval (x - t • u) ≤ 0 := by
  by_cases hzero : l.eval x = 0
  · have hu : normalEval l.normal u = 0 := hactive hzero
    filter_upwards [] with t
    have hformula := line_perturb_formula l x u t
    rw [hzero, hu] at hformula
    constructor
    · have hval : l.eval (x + t • u) = 0 := by simpa using hformula.1
      rw [hval]
    · have hval : l.eval (x - t • u) = 0 := by simpa using hformula.2
      rw [hval]
  · have hneg : l.eval x < 0 := lt_of_le_of_ne hle hzero
    have hplus : ∀ᶠ t in 𝓝 (0 : ℝ), l.eval (x + t • u) < 0 := by
      have hcont : Continuous fun t : ℝ => l.eval (x + t • u) := by
        fun_prop [RationalLine.eval, normalEval]
      have hmem : l.eval (x + (0 : ℝ) • u) ∈ Set.Iio (0 : ℝ) := by
        simpa using hneg
      exact hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hmem)
    have hminus : ∀ᶠ t in 𝓝 (0 : ℝ), l.eval (x - t • u) < 0 := by
      have hcont : Continuous fun t : ℝ => l.eval (x - t • u) := by
        fun_prop [RationalLine.eval, normalEval]
      have hmem : l.eval (x - (0 : ℝ) • u) ∈ Set.Iio (0 : ℝ) := by
        simpa using hneg
      exact hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hmem)
    filter_upwards [hplus.filter_mono nhdsWithin_le_nhds,
      hminus.filter_mono nhdsWithin_le_nhds] with t htplus htminus
    exact ⟨htplus.le, htminus.le⟩

private theorem all_lines_perturb_eventually (cell : List RationalLine) (x u : Plane)
    (hbase : ∀ l ∈ cell, l.eval x ≤ 0)
    (hactive : ∀ l ∈ cell, l.eval x = 0 → normalEval l.normal u = 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∀ l ∈ cell, l.eval (x + t • u) ≤ 0) ∧
      (∀ l ∈ cell, l.eval (x - t • u) ≤ 0) := by
  induction cell with
  | nil =>
      filter_upwards [] with t
      simp
  | cons l cell ih =>
      have hl := line_perturb_nonpos_eventually l x u (hbase l (by simp))
        (hactive l (by simp))
      have htail := ih (by
        intro k hk
        exact hbase k (by simp [hk])) (by
        intro k hk hkx
        exact hactive k (by simp [hk]) hkx)
      filter_upwards [hl, htail] with t hlt htail
      constructor
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hlt.1
        · exact htail.1 k hk
      · intro k hk
        rcases List.mem_cons.mp hk with rfl | hk
        · exact hlt.2
        · exact htail.2 k hk

private theorem tangentToNormal_ne_zero (n : RationalNormal) :
    tangentToNormal n ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  have hy : n.y = 0 := by
    have : (n.y : ℝ) = 0 := by simpa [tangentToNormal] using hre
    exact_mod_cast this
  have hx : n.x = 0 := by
    have : (n.x : ℝ) = 0 := by simpa [tangentToNormal] using him
    exact_mod_cast this
  rcases n.nonzero with h | h
  · exact h hx
  · exact h hy

private theorem closedCell_extreme_has_active_nonparallel
    (cell : List RationalLine) (x : Plane)
    (hx : x ∈ (closedCell cell).extremePoints ℝ) :
    ∃ l ∈ cell, ∃ m ∈ cell,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 ∧
      l.eval x = 0 ∧ m.eval x = 0 := by
  by_contra hno
  have hno' : ¬ ∃ l ∈ cell, ∃ m ∈ cell,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 ∧
      l.eval x = 0 ∧ m.eval x = 0 := by simpa using hno
  by_cases hactive : ∃ l ∈ cell, l.eval x = 0
  · obtain ⟨k, hk, hkx⟩ := hactive
    let u := tangentToNormal k.normal
    have hu : u ≠ 0 := tangentToNormal_ne_zero k.normal
    have horth : ∀ l ∈ cell, l.eval x = 0 → normalEval l.normal u = 0 := by
      intro l hl hlx
      have hdet : l.normal.x * k.normal.y - l.normal.y * k.normal.x = 0 := by
        by_contra hdet
        exact hno' ⟨l, hl, k, hk, hdet, hlx, hkx⟩
      have hdetR : (l.normal.x : ℝ) * k.normal.y -
          (l.normal.y : ℝ) * k.normal.x = 0 := by exact_mod_cast hdet
      change normalEval l.normal (tangentToNormal k.normal) = 0
      simp [normalEval, tangentToNormal]
      nlinarith [hdetR]
    have hpert := all_lines_perturb_eventually cell x u hx.1 horth
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
    obtain ⟨t, ⟨htcell, htpos⟩⟩ := (hpert.and hpos).exists
    have hplus : x + t • u ∈ closedCell cell := htcell.1
    have hminus : x - t • u ∈ closedCell cell := htcell.2
    have hmid := (mem_extremePoints_iff_left.mp hx).2
      (x - t • u) hminus (x + t • u) hplus
      (mem_openSegment_sub_add x (t • u))
    have htu : t • u ≠ 0 := smul_ne_zero (ne_of_gt htpos) hu
    have : x - t • u ≠ x := by
      intro h
      have hneg : -(t • u) = 0 := by
        calc
          -(t • u) = (x - t • u) - x := by abel
          _ = x - x := congrArg (fun z : Plane => z - x) h
          _ = 0 := by simp
      have hzero : t • u = 0 := neg_eq_zero.mp hneg
      exact htu hzero
    exact this hmid
  · let u : Plane := 1
    have hu : u ≠ 0 := one_ne_zero
    have horth : ∀ l ∈ cell, l.eval x = 0 → normalEval l.normal u = 0 := by
      intro l hl hlx
      exact (hactive ⟨l, hl, hlx⟩).elim
    have hpert := all_lines_perturb_eventually cell x u hx.1 horth
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
    obtain ⟨t, ⟨htcell, htpos⟩⟩ := (hpert.and hpos).exists
    have hplus : x + t • u ∈ closedCell cell := htcell.1
    have hminus : x - t • u ∈ closedCell cell := htcell.2
    have hmid := (mem_extremePoints_iff_left.mp hx).2
      (x - t • u) hminus (x + t • u) hplus
      (mem_openSegment_sub_add x (t • u))
    have htu : t • u ≠ 0 := smul_ne_zero (ne_of_gt htpos) hu
    have : x - t • u ≠ x := by
      intro h
      have hneg : -(t • u) = 0 := by
        calc
          -(t • u) = (x - t • u) - x := by abel
          _ = x - x := congrArg (fun z : Plane => z - x) h
          _ = 0 := by simp
      have hzero : t • u = 0 := neg_eq_zero.mp hneg
      exact htu hzero
    exact this hmid

/-- A strict cell with an interior point closes to exactly its non-strict halfspace code.
This also handles redundant and concurrent line constraints. -/
private theorem closedCell_pairPoint_extreme (cell : List RationalLine)
    (l m : RationalLine) (hl : l ∈ cell) (hm : m ∈ cell)
    (hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0)
    (x : Plane) (hx : x ∈ closedCell cell) (hlx : l.eval x = 0) (hmx : m.eval x = 0) :
    x ∈ (closedCell cell).extremePoints ℝ := by
  refine ⟨hx, ?_⟩
  intro a ha b hb hab
  obtain ⟨α, β, hα, hβ, hsum, heq⟩ := hab
  have hlcombo := lineEval_combo l a b α β hsum
  have hmcombo := lineEval_combo m a b α β hsum
  rw [heq, hlx] at hlcombo
  rw [heq, hmx] at hmcombo
  have hla : l.eval a = 0 := by
    have hnb := mul_nonpos_of_nonneg_of_nonpos hβ.le (hb l hl)
    nlinarith [ha l hl]
  have hma : m.eval a = 0 := by
    have hnb := mul_nonpos_of_nonneg_of_nonpos hβ.le (hb m hm)
    nlinarith [ha m hm]
  obtain ⟨p, _, _, huniq, _⟩ := rationalLine_pairIntersection l m hdet
  exact (huniq a hla hma).trans (huniq x hlx hmx).symm

private theorem closedCell_extremePoints_finite (cell : List RationalLine) :
    ((closedCell cell).extremePoints ℝ).Finite := by
  classical
  let A : Finset RationalLine := cell.toFinset
  let pairs : Finset (RationalLine × RationalLine) := (A ×ˢ A).filter fun p =>
    p.1.normal.x * p.2.normal.y - p.1.normal.y * p.2.normal.x ≠ 0
  let point (p : {p // p ∈ pairs}) : Plane := Classical.choose
    (rationalLine_pairIntersection p.1.1 p.1.2 (Finset.mem_filter.mp p.2).2)
  apply (Set.finite_range point).subset
  intro x hx
  obtain ⟨l, hl, m, hm, hdet, hlx, hmx⟩ :=
    closedCell_extreme_has_active_nonparallel cell x hx
  have hp : (l, m) ∈ pairs := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨List.mem_toFinset.mpr hl, List.mem_toFinset.mpr hm⟩,
      hdet⟩
  refine ⟨⟨(l, m), hp⟩, ?_⟩
  symm
  exact (Classical.choose_spec (rationalLine_pairIntersection l m
    (Finset.mem_filter.mp hp).2)).2.2.1 x hlx hmx

private theorem openCell_closure (cell : List RationalLine) (hne : (openCell cell).Nonempty) :
    closure (openCell cell) = closedCell cell := by
  apply subset_antisymm
  · apply closure_minimal _ (closedCell_isClosed cell)
    intro z hz l hl
    exact (hz l hl).le
  · intro x hx
    obtain ⟨w, hw⟩ := hne
    have hsegment : openSegment ℝ w x ⊆ openCell cell := by
      rintro z ⟨a, b, ha, hb, hab, rfl⟩ l hl
      rw [lineEval_combo l w x a b hab]
      exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha (hw l hl))
        (mul_nonpos_of_nonneg_of_nonpos hb.le (hx l hl))
    exact closure_mono hsegment
      (segment_subset_closure_openSegment (right_mem_segment ℝ w x))

private theorem openCell_subset_interior (cell : List RationalLine) :
    openCell cell ⊆ interior (closedCell cell) := by
  intro z hz
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset ((openCell_isOpen cell).mem_nhds hz)
  intro w hw l hl
  exact (hw l hl).le

/-- True cell boundary lies on the arrangement lines. No statement here concerns fan diagonals. -/
private theorem closedCell_frontier_lines (cell : List RationalLine) :
    ∀ z ∈ frontier (closedCell cell), ∃ l ∈ cell, l.eval z = 0 := by
  intro z hz
  have hzclosed : z ∈ closedCell cell :=
    (closedCell_isClosed cell).closure_eq ▸ frontier_subset_closure hz
  by_contra hzero
  push Not at hzero
  have hzopen : z ∈ openCell cell := by
    intro l hl
    exact lt_of_le_of_ne (hzclosed l hl) (hzero l hl)
  exact hz.2 (openCell_subset_interior cell hzopen)

/-- The exit point along every nontrivial ray exists by compactness and is genuinely on
the frontier. This is the covering half of the cell fan construction. -/
private theorem closedCell_radial_boundary (cell : List RationalLine) (c x : Plane)
    (hcompact : IsCompact (closedCell cell)) (hx : x ∈ closedCell cell) (hxc : x ≠ c) :
    ∃ y ∈ frontier (closedCell cell), x ∈ segment ℝ c y := by
  let f : ℝ → Plane := fun r => c + r • (x-c)
  have hu : x-c ≠ 0 := sub_ne_zero.mpr hxc
  have hf : Topology.IsClosedEmbedding f :=
    (Homeomorph.addLeft c).isClosedEmbedding.comp (isClosedEmbedding_smul_left hu)
  have hpre : IsCompact (f ⁻¹' closedCell cell) := hf.isCompact_preimage hcompact
  have h1 : (1 : ℝ) ∈ f ⁻¹' closedCell cell := by simpa [f] using hx
  obtain ⟨r, hr, hmax⟩ := hpre.exists_isMaxOn ⟨1, h1⟩ continuous_id.continuousOn
  have hr1 : 1 ≤ r := hmax h1
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hyfront : f r ∈ frontier (closedCell cell) := by
    have hrCell : f r ∈ closedCell cell := hr
    apply (mem_frontier_iff_notMem_interior hrCell).mpr
    intro hint
    have hnear : ∀ᶠ s in 𝓝[>] r, f s ∈ interior (closedCell cell) :=
      (hf.continuous.continuousAt.eventually (isOpen_interior.mem_nhds hint)).filter_mono
        nhdsWithin_le_nhds
    have hgt : ∀ᶠ s in 𝓝[>] r, r < s := eventually_mem_nhdsWithin
    obtain ⟨s, hs, hrs⟩ := (hnear.and hgt).exists
    have hsCell : s ∈ f ⁻¹' closedCell cell := by
      change f s ∈ closedCell cell
      exact interior_subset hs
    have hsr : s ≤ r := hmax hsCell
    exact (not_le_of_gt hrs) hsr
  refine ⟨f r, hyfront, ?_⟩
  have hinv : 0 ≤ 1/r := div_nonneg zero_le_one hrpos.le
  have hinv1 : 1/r ≤ 1 := (div_le_one hrpos).mpr hr1
  refine ⟨1-(1/r), 1/r, sub_nonneg.mpr hinv1, hinv, by ring, ?_⟩
  apply Complex.ext <;>
    simp only [f, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul] <;>
    field_simp <;> ring

private theorem fanTriangle_area_ne (l : RationalLine) (c a b : Plane)
    (hc : l.eval c < 0) (ha : l.eval a = 0) (hb : l.eval b = 0) (hab : a ≠ b) :
    Tiling.twiceSignedArea c a b ≠ 0 := by
  intro harea
  let v : Plane := a-c
  let w : Plane := b-c
  have hv : normalEval l.normal v ≠ 0 := by
    rw [perturb_normalEval_sub, sub_eq_zero.mp ha]
    exact sub_ne_zero.mpr (Ne.symm (ne_of_lt (sub_neg.mp hc)))
  have hn : normalEval l.normal w = normalEval l.normal v := by
    simp only [v, w, perturb_normalEval_sub]
    rw [sub_eq_zero.mp ha, sub_eq_zero.mp hb]
  have hdet : v.re * w.im - v.im * w.re = 0 := harea
  have hwv : w = v := by
    by_cases hvr : v.re = 0
    · have hvi : v.im ≠ 0 := by
        intro hvi
        apply hv
        simp [normalEval, hvr, hvi]
      have hscale : w = (w.im/v.im) • v := by
        apply Complex.ext
        · simp only [Complex.smul_re, smul_eq_mul, hvr, mul_zero]
          have hprod : v.im * w.re = 0 := by simpa [hvr] using hdet
          exact (mul_eq_zero.mp hprod).resolve_left hvi
        · simp only [Complex.smul_im, smul_eq_mul]
          field_simp
      have hr : w.im/v.im = 1 := by
        rw [hscale, normalEval_smul] at hn
        apply (mul_right_cancel₀ hv)
        simpa using hn
      rw [hscale, hr, one_smul]
    · have hscale : w = (w.re/v.re) • v := by
        apply Complex.ext
        · simp only [Complex.smul_re, smul_eq_mul]
          field_simp
        · simp only [Complex.smul_im, smul_eq_mul]
          field_simp
          nlinarith [hdet]
      have hr : w.re/v.re = 1 := by
        rw [hscale, normalEval_smul] at hn
        apply (mul_right_cancel₀ hv)
        simpa using hn
      rw [hscale, hr, one_smul]
  apply hab
  exact (sub_left_inj.mp hwv).symm

private theorem volume_segment_zero (a b : Plane) : volume (segment ℝ a b) = 0 := by
  rw [← convexHull_pair]
  apply measure_mono_null (convexHull_subset_affineSpan {a, b})
  apply Measure.addHaar_affineSubspace
  by_cases hab : a = b
  · subst b
    intro htop
    have htop' : affineSpan ℝ ({a} : Set Plane) = ⊤ := by simpa using htop
    have hmem : a + 1 ∈ affineSpan ℝ ({a} : Set Plane) := by rw [htop']; simp
    have ha := (AffineSubspace.mem_affineSpan_singleton ℝ Plane).mp hmem
    have : (1 : Plane) = 0 := by linear_combination ha
    exact one_ne_zero this
  · intro htop
    have hdim := congrArg (fun s : AffineSubspace ℝ Plane => Module.finrank ℝ s.direction) htop
    rw [direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub,
      finrank_span_singleton (sub_ne_zero.mpr (Ne.symm hab)), AffineSubspace.direction_top,
      finrank_top, Complex.finrank_real_complex] at hdim
    omega

private theorem dense_compl_of_volume_zero (s : Set Plane) (hs : volume s = 0) : Dense sᶜ := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hpos := isOpen_interior.measure_pos volume (show (interior s).Nonempty from ⟨x, hx⟩)
  have hzero : volume (interior s) = 0 := measure_mono_null interior_subset hs
  exact (ne_of_gt hpos) hzero

private def shiftedCell (cell : List RationalLine) (offsets : RationalLine → ℝ) : Set Plane :=
  {z | ∀ l ∈ cell, normalEval l.normal z ≤ offsets l}

private theorem fanTriangle_isTriangle (l : RationalLine) (c a b : Plane)
    (hc : l.eval c < 0) (ha : l.eval a = 0) (hb : l.eval b = 0) (hab : a ≠ b) :
    Tiling.IsTriangle (convexHull ℝ {c, a, b}) := by
  exact ⟨c, a, b, fanTriangle_area_ne l c a b hc ha hb hab, rfl⟩

private theorem continuous_normalEval (n : RationalNormal) :
    Continuous fun z : Plane => normalEval n z := by
  fun_prop [normalEval]

private def listMaxEval (cell : List RationalLine) (z : Plane) : ℝ :=
  cell.foldr (fun l r => max (normalEval l.normal z) r) 0

private theorem continuous_listMaxEval (cell : List RationalLine) :
    Continuous (listMaxEval cell) := by
  induction cell with
  | nil =>
      change Continuous (fun _ : Plane => (0 : ℝ))
      exact continuous_const
  | cons l cell ih =>
      change Continuous (fun z => max (normalEval l.normal z) (listMaxEval cell z))
      exact (continuous_normalEval l.normal).max ih

private theorem eval_le_listMaxEval (cell : List RationalLine) (z : Plane) :
    ∀ l ∈ cell, normalEval l.normal z ≤ listMaxEval cell z := by
  induction cell with
  | nil => simp
  | cons k cell ih =>
      intro l hl
      simp only [listMaxEval, List.foldr_cons]
      rcases List.mem_cons.mp hl with h | h
      · subst l
        exact le_max_left _ _
      · exact (ih l h).trans (le_max_right _ _)

private theorem listMaxEval_le (cell : List RationalLine) (z : Plane) (B : ℝ)
    (hB : 0 ≤ B) (h : ∀ l ∈ cell, normalEval l.normal z ≤ B) :
    listMaxEval cell z ≤ B := by
  induction cell with
  | nil => simpa [listMaxEval] using hB
  | cons l cell ih =>
      simp only [listMaxEval, List.foldr_cons]
      apply max_le
      · exact h l (by simp)
      · apply ih
        intro k hk
        exact h k (by simp [hk])

private def listMaxOffset (cell : List RationalLine) (offsets : RationalLine → ℝ) : ℝ :=
  cell.foldr (fun l r => max (offsets l) r) 0

private theorem listMaxOffset_nonneg (cell : List RationalLine)
    (offsets : RationalLine → ℝ) : 0 ≤ listMaxOffset cell offsets := by
  induction cell with
  | nil => simp [listMaxOffset]
  | cons l cell ih =>
      simp only [listMaxOffset, List.foldr_cons]
      exact ih.trans (le_max_right _ _)

private theorem offset_le_listMaxOffset (cell : List RationalLine)
    (offsets : RationalLine → ℝ) :
    ∀ l ∈ cell, offsets l ≤ listMaxOffset cell offsets := by
  induction cell with
  | nil => simp
  | cons k cell ih =>
      intro l hl
      simp only [listMaxOffset, List.foldr_cons]
      rcases List.mem_cons.mp hl with h | h
      · subst l
        exact le_max_left _ _
      · exact (ih l h).trans (le_max_right _ _)

private theorem compact_cell_excludes_recession
    (cell : List RationalLine) (hcompact : IsCompact (closedCell cell))
    (hne : (closedCell cell).Nonempty) (u : Plane) (hu : u ≠ 0) :
    ∃ l ∈ cell, 0 < normalEval l.normal u := by
  by_contra hpos
  push Not at hpos
  obtain ⟨c, hc⟩ := hne
  obtain ⟨R, hball⟩ := (Metric.isBounded_iff_subset_ball (0 : Plane)).mp hcompact.isBounded
  have hUnorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hUpos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let t : ℝ := (|R| + ‖c‖ + 1) / ‖u‖
  have ht : 0 < t := by dsimp [t]; positivity
  have htmul : t * ‖u‖ = |R| + ‖c‖ + 1 := by
    dsimp [t]
    field_simp
  let y : Plane := c + t • u
  have hy : y ∈ closedCell cell := by
    intro l hl
    have hform : l.eval y = l.eval c + t * normalEval l.normal u := by
      change normalEval l.normal (c + t • u) - l.offset =
        (normalEval l.normal c - l.offset) + t * normalEval l.normal u
      rw [perturb_normalEval_add, normalEval_smul]
      ring
    rw [hform]
    have := hc l hl
    have := hpos l hl
    nlinarith
  have hyball := hball hy
  have hylength : ‖y‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hyball
  have hyminus : y - c = t • u := by dsimp [y]; module
  have hnorm : t * ‖u‖ ≤ ‖y‖ + ‖c‖ := by
    calc
      t * ‖u‖ = ‖t • u‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ = ‖y - c‖ := by rw [hyminus]
      _ ≤ ‖y‖ + ‖c‖ := norm_sub_le y c
  rw [htmul] at hnorm
  have hRabs : R ≤ |R| := le_abs_self R
  have := abs_nonneg R
  linarith

private theorem shiftedCell_isClosed (cell : List RationalLine)
    (offsets : RationalLine → ℝ) : IsClosed (shiftedCell cell offsets) := by
  induction cell with
  | nil => simp [shiftedCell]
  | cons l cell ih =>
      have heq : shiftedCell (l :: cell) offsets =
          {z | normalEval l.normal z ≤ offsets l} ∩ shiftedCell cell offsets := by
        ext z
        simp [shiftedCell]
      rw [heq]
      exact (isClosed_le (continuous_normalEval l.normal) continuous_const).inter ih

private theorem shiftedCell_isCompact_of_compact_same_normals
    (cell : List RationalLine) (hcompact : IsCompact (closedCell cell))
    (hne : (closedCell cell).Nonempty) (offsets : RationalLine → ℝ) :
    IsCompact (shiftedCell cell offsets) := by
  let S : Set Plane := Metric.sphere (0 : Plane) 1
  have hScompact : IsCompact S := isCompact_sphere _ _
  have hSnonempty : S.Nonempty := by
    refine ⟨1, ?_⟩
    simp [S, Metric.sphere, dist_eq_norm]
  obtain ⟨u, huS, huMin⟩ := hScompact.exists_isMinOn hSnonempty
    (continuous_listMaxEval cell).continuousOn
  have huNorm : ‖u‖ = 1 := by simpa [S, Metric.sphere, dist_eq_norm] using huS
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp at huNorm
  obtain ⟨l₀, hl₀, hl₀pos⟩ := compact_cell_excludes_recession cell hcompact hne u hu0
  have hεpos : 0 < listMaxEval cell u := by
    exact lt_of_lt_of_le hl₀pos (eval_le_listMaxEval cell u l₀ hl₀)
  let ε : ℝ := listMaxEval cell u
  have hε : 0 < ε := by simpa [ε] using hεpos
  have hmin : ∀ v ∈ S, ε ≤ listMaxEval cell v := by
    intro v hv
    exact huMin hv
  let B : ℝ := listMaxOffset cell offsets
  have hB : 0 ≤ B := by dsimp [B]; exact listMaxOffset_nonneg cell offsets
  have hbound : shiftedCell cell offsets ⊆ Metric.closedBall (0 : Plane) (B / ε) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simpa using div_nonneg hB hε.le
    · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      let v : Plane := (‖x‖⁻¹) • x
      have hvnorm : ‖v‖ = 1 := by
        change ‖(‖x‖⁻¹ : ℝ) • x‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxnorm)]
        simp [ne_of_gt hxnorm]
      have hvS : v ∈ S := by simpa [S, Metric.sphere, dist_eq_norm] using hvnorm
      have hinv : 0 ≤ ‖x‖⁻¹ := inv_nonneg.mpr hxnorm.le
      have hlin : ∀ l ∈ cell, normalEval l.normal v ≤ B / ‖x‖ := by
        intro l hl
        have hscale := normalEval_smul l.normal (‖x‖⁻¹) x
        have hpoint := hx l hl
        have hoff := offset_le_listMaxOffset cell offsets l hl
        calc
          normalEval l.normal v = ‖x‖⁻¹ * normalEval l.normal x := by
            dsimp [v]
            exact hscale
          _ ≤ ‖x‖⁻¹ * offsets l := mul_le_mul_of_nonneg_left hpoint hinv
          _ ≤ ‖x‖⁻¹ * B := mul_le_mul_of_nonneg_left hoff hinv
          _ = B / ‖x‖ := by ring
      have hfbound : listMaxEval cell v ≤ B / ‖x‖ :=
        listMaxEval_le cell v (B / ‖x‖) (div_nonneg hB hxnorm.le) hlin
      have hεbound : ε ≤ B / ‖x‖ := (hmin v hvS).trans hfbound
      have hprod : ε * ‖x‖ ≤ B := (le_div_iff₀ hxnorm).mp hεbound
      have hnorm : ‖x‖ ≤ B / ε := by
        apply (le_div_iff₀ hε).2
        nlinarith [hprod]
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  have hbounded : Bornology.IsBounded (shiftedCell cell offsets) :=
    (Metric.isBounded_iff_subset_closedBall (0 : Plane)).2 ⟨B / ε, hbound⟩
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨shiftedCell_isClosed cell offsets, hbounded⟩

private theorem lineEval_affine (l : RationalLine) (x y : Plane) (r s : ℝ) :
    l.eval (r • x + s • y) = r * l.eval x + s * l.eval y + (r+s-1)*l.offset := by
  simp only [RationalLine.eval, perturb_normalEval_add, normalEval_smul]
  ring

private theorem weighted_triangle_factors (c a b z : Plane) (wc wa wb : ℝ)
    (hwc : 0 ≤ wc) (hwa : 0 ≤ wa) (hwb : 0 ≤ wb)
    (hsum : wc + wa + wb = 1) (hxyz : wc • c + wa • a + wb • b = z)
    (hedge : wa + wb ≠ 0) :
    ∃ p ∈ segment ℝ a b, z ∈ segment ℝ c p := by
  let s : ℝ := wa + wb
  have hs : s ≠ 0 := hedge
  have hspos : 0 < s := lt_of_le_of_ne (add_nonneg hwa hwb) (Ne.symm hs)
  let p : Plane := (wa/s) • a + (wb/s) • b
  have hp : p ∈ segment ℝ a b := by
    refine ⟨wa/s, wb/s, div_nonneg hwa hspos.le, div_nonneg hwb hspos.le, ?_, rfl⟩
    dsimp [s]
    field_simp
  refine ⟨p, hp, wc, s, hwc, add_nonneg hwa hwb, ?_, ?_⟩
  · dsimp [s]
    linarith [hsum]
  · have ha : s * (wa/s) = wa := by field_simp
    have hb : s * (wb/s) = wb := by field_simp
    calc
      wc • c + s • p = wc • c + (s * (wa/s)) • a + (s * (wb/s)) • b := by
        simp [p, smul_add, add_assoc]
        ring
      _ = wc • c + wa • a + wb • b := by rw [ha, hb]
      _ = z := hxyz

private theorem triangle_hull_factors (c a b z : Plane)
    (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b)
    (hz : z ∈ convexHull ℝ {c, a, b}) (hzc : z ≠ c) :
    ∃ p ∈ segment ℝ a b, z ∈ segment ℝ c p := by
  have hz' : z ∈ convexHull ℝ (↑({c, a, b} : Finset Plane) : Set Plane) := by
    simpa using hz
  obtain ⟨w, hw_nonneg, hw_sum, hwz⟩ := Finset.mem_convexHull'.mp hz'
  have hw_sum' : w c + w a + w b = 1 := by
    simpa [hca, hcb, hab, hca.symm, hcb.symm, hab.symm, add_assoc] using hw_sum
  have hwz' : w c • c + w a • a + w b • b = z := by
    simpa [hca, hcb, hab, hca.symm, hcb.symm, hab.symm, add_assoc] using hwz
  have hwc : 0 ≤ w c := hw_nonneg c (by simp)
  have hwa : 0 ≤ w a := hw_nonneg a (by simp)
  have hwb : 0 ≤ w b := hw_nonneg b (by simp)
  have hedge : w a + w b ≠ 0 := by
    intro hs
    have ha0 : w a = 0 := by nlinarith
    have hb0 : w b = 0 := by nlinarith
    have hc1 : w c = 1 := by rw [ha0, hb0] at hw_sum'; linarith
    have hzc' : z = c := by
      simpa [ha0, hb0, hc1] using hwz'.symm
    exact hzc hzc'
  exact weighted_triangle_factors c a b z (w c) (w a) (w b)
    hwc hwa hwb hw_sum' hwz' hedge

private theorem volume_convexHull_pair_eq_zero (a b : Plane) :
    volume (convexHull ℝ {a, b}) = 0 := by
  rw [convexHull_pair]
  exact volume_segment_zero a b

private theorem segment_decomp (x y z : Plane) (hz : z ∈ segment ℝ x y) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α + β = 1 ∧ α • x + β • y = z := hz

private theorem segment_ray_eq_of_strict_cell
    (cell : List RationalLine) (c p q z : Plane) (l m : RationalLine)
    (hlmem : l ∈ cell) (hmmem : m ∈ cell)
    (hc : ∀ k ∈ cell, k.eval c < 0)
    (hp : p ∈ closedCell cell) (hq : q ∈ closedCell cell)
    (hlp : l.eval p = 0) (hmq : m.eval q = 0)
    (hzc : z ≠ c) (hzp : z ∈ segment ℝ c p) (hzq : z ∈ segment ℝ c q) :
    p = q := by
  obtain ⟨α, β, hα, hβ, hsum, hz1⟩ := segment_decomp c p z hzp
  obtain ⟨γ, δ, hγ, hδ, hsum', hz2⟩ := segment_decomp c q z hzq
  have hlz₁ : l.eval z = α * l.eval c := by
    have he := lineEval_affine l c p α β
    rw [hz1, hlp, show α + β - 1 = 0 by linarith] at he
    simpa using he
  have hlz₂ : l.eval z = γ * l.eval c + δ * l.eval q := by
    have he := lineEval_affine l c q γ δ
    rw [hz2, show γ + δ - 1 = 0 by linarith] at he
    simpa using he
  have hmz₁ : m.eval z = α * m.eval c + β * m.eval p := by
    have he := lineEval_affine m c p α β
    rw [hz1, show α + β - 1 = 0 by linarith] at he
    simpa using he
  have hmz₂ : m.eval z = γ * m.eval c := by
    have he := lineEval_affine m c q γ δ
    rw [hz2, hmq, show γ + δ - 1 = 0 by linarith] at he
    simpa using he
  have hle₁ : α * l.eval c ≤ γ * l.eval c := by
    have hqle := mul_nonpos_of_nonneg_of_nonpos hδ (hq l hlmem)
    linarith [hlz₁, hlz₂]
  have hle₂ : γ * m.eval c ≤ α * m.eval c := by
    have hple := mul_nonpos_of_nonneg_of_nonpos hβ (hp m hmmem)
    linarith [hmz₁, hmz₂]
  have hαeq : α = γ := le_antisymm
    ((mul_le_mul_right_of_neg (hc m hmmem)).mp hle₂)
    ((mul_le_mul_right_of_neg (hc l hlmem)).mp hle₁)
  have hβeq : β = δ := by linarith [hsum, hsum', hαeq]
  have hp_eq : α • c + β • p = α • c + β • q := by
    calc
      α • c + β • p = z := hz1
      _ = γ • c + δ • q := hz2.symm
      _ = α • c + β • q := by rw [← hαeq, ← hβeq]
  have hp_sm : β • p = β • q := add_left_cancel hp_eq
  have hβne : β ≠ 0 := by
    intro hzβ
    have heq : α = 1 := by linarith
    have : z = c := by simpa [heq, hzβ] using hz1.symm
    exact hzc this
  have hinv := congrArg (fun x : Plane => β⁻¹ • x) hp_sm
  simpa [smul_smul, hβne] using hinv

private theorem lineEval_parallel_eq (l m : RationalLine)
    (hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x = 0)
    (p : Plane) (hlp : l.eval p = 0) (hmp : m.eval p = 0) :
    ∃ r : ℝ, r ≠ 0 ∧ ∀ z, m.eval z = r * l.eval z := by
  let lx : ℝ := l.normal.x
  let ly : ℝ := l.normal.y
  let mx : ℝ := m.normal.x
  let my : ℝ := m.normal.y
  have hdetR : lx * my - ly * mx = 0 := by
    dsimp [lx, ly, mx, my]
    exact_mod_cast hdet
  have hlne : lx ≠ 0 ∨ ly ≠ 0 := by
    rcases l.normal.nonzero with hx | hy
    · exact Or.inl (by dsimp [lx]; exact_mod_cast hx)
    · exact Or.inr (by dsimp [ly]; exact_mod_cast hy)
  have hmne : mx ≠ 0 ∨ my ≠ 0 := by
    rcases m.normal.nonzero with hx | hy
    · exact Or.inl (by dsimp [mx]; exact_mod_cast hx)
    · exact Or.inr (by dsimp [my]; exact_mod_cast hy)
  let r : ℝ := if lx ≠ 0 then mx/lx else my/ly
  have hmx : mx = r * lx := by
    by_cases hx : lx = 0
    · have hy : ly ≠ 0 := hlne.resolve_left (not_not.mpr hx)
      have hmzero : mx = 0 := by
        have hzero : ly * mx = 0 := by rw [hx] at hdetR; linarith
        exact (mul_eq_zero.mp hzero).resolve_left hy
      simp [r, hx, hmzero]
    · dsimp only [r]
      rw [if_pos hx]
      field_simp
  have hmy : my = r * ly := by
    by_cases hx : lx = 0
    · have hy : ly ≠ 0 := hlne.resolve_left (not_not.mpr hx)
      dsimp only [r]
      rw [if_neg (not_not.mpr hx)]
      field_simp
    · dsimp only [r]
      rw [if_pos hx]
      field_simp
      nlinarith [hdetR]
  have hr : r ≠ 0 := by
    intro hr0
    rcases hmne with hmx0 | hmy0
    · apply hmx0
      rw [hmx, hr0]
      simp
    · apply hmy0
      rw [hmy, hr0]
      simp
  have hnormal (z : Plane) : normalEval m.normal z = r * normalEval l.normal z := by
    change mx * z.re + my * z.im = r * (lx * z.re + ly * z.im)
    rw [hmx, hmy]
    ring
  have hl0 : normalEval l.normal p = l.offset := sub_eq_zero.mp hlp
  have hm0 : normalEval m.normal p = m.offset := sub_eq_zero.mp hmp
  have hoff : m.offset = r * l.offset := by rw [← hm0, hnormal p, hl0]
  refine ⟨r, hr, ?_⟩
  intro z
  change normalEval m.normal z - m.offset = r * (normalEval l.normal z - l.offset)
  rw [hoff, hnormal z]
  ring

private theorem common_zero_unique (l m : RationalLine)
    (hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0)
    (p q : Plane) (hlp : l.eval p = 0) (hlq : l.eval q = 0)
    (hmp : m.eval p = 0) (hmq : m.eval q = 0) : p = q := by
  let lx : ℝ := l.normal.x
  let ly : ℝ := l.normal.y
  let mx : ℝ := m.normal.x
  let my : ℝ := m.normal.y
  let D : ℝ := lx * my - ly * mx
  have hD : D ≠ 0 := by
    dsimp [D, lx, ly, mx, my]
    exact_mod_cast hdet
  have hLp : lx * p.re + ly * p.im = l.offset := by
    simpa [normalEval, lx, ly] using (sub_eq_zero.mp hlp)
  have hLq : lx * q.re + ly * q.im = l.offset := by
    simpa [normalEval, lx, ly] using (sub_eq_zero.mp hlq)
  have hMp : mx * p.re + my * p.im = m.offset := by
    simpa [normalEval, mx, my] using (sub_eq_zero.mp hmp)
  have hMq : mx * q.re + my * q.im = m.offset := by
    simpa [normalEval, mx, my] using (sub_eq_zero.mp hmq)
  have hre : D * (p.re - q.re) = 0 := by
    dsimp [D]
    linear_combination my * (hLp - hLq) - ly * (hMp - hMq)
  have him : D * (p.im - q.im) = 0 := by
    dsimp [D]
    linear_combination lx * (hMp - hMq) - mx * (hLp - hLq)
  have hre0 : p.re = q.re := by
    have h := (mul_eq_zero.mp hre).resolve_left hD
    exact sub_eq_zero.mp h
  have him0 : p.im = q.im := by
    have h := (mul_eq_zero.mp him).resolve_left hD
    exact sub_eq_zero.mp h
  exact Complex.ext hre0 him0

private theorem triple_hulls_eq_of_segment_eq (c a b d e : Plane)
    (hseg : segment ℝ a b = segment ℝ d e) :
    convexHull ℝ {c, a, b} = convexHull ℝ {c, d, e} := by
  have hsub₁ : {c, a, b} ⊆ convexHull ℝ {c, d, e} := by
    intro x hx
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with hx | hx | hx
    · rw [hx]
      exact subset_convexHull ℝ _ (by simp)
    · rw [hx]
      have ha : a ∈ segment ℝ d e := by
        rw [← hseg]
        exact left_mem_segment ℝ a b
      exact segment_subset_convexHull (by simp) (by simp) ha
    · rw [hx]
      have hb : b ∈ segment ℝ d e := by
        rw [← hseg]
        exact right_mem_segment ℝ a b
      exact segment_subset_convexHull (by simp) (by simp) hb
  have hsub₂ : {c, d, e} ⊆ convexHull ℝ {c, a, b} := by
    intro x hx
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with hx | hx | hx
    · rw [hx]
      exact subset_convexHull ℝ _ (by simp)
    · rw [hx]
      have hd : d ∈ segment ℝ a b := by
        rw [hseg]
        exact left_mem_segment ℝ d e
      exact segment_subset_convexHull (by simp) (by simp) hd
    · rw [hx]
      have he : e ∈ segment ℝ a b := by
        rw [hseg]
        exact right_mem_segment ℝ d e
      exact segment_subset_convexHull (by simp) (by simp) he
  exact le_antisymm (convexHull_min hsub₁ (convex_convexHull _ _))
    (convexHull_min hsub₂ (convex_convexHull _ _))

private theorem distinct_fan_triangles_aedisjoint
    (cell : List RationalLine) (c a b d e : Plane) (l m : RationalLine)
    (hlmem : l ∈ cell) (hmmem : m ∈ cell)
    (hc : ∀ k ∈ cell, k.eval c < 0)
    (hfaceL : closedCell cell ∩ {z | l.eval z = 0} = segment ℝ a b)
    (hfaceM : closedCell cell ∩ {z | m.eval z = 0} = segment ℝ d e)
    (hab : a ≠ b) (hde : d ≠ e)
    (htri : convexHull ℝ {c, a, b} ≠ convexHull ℝ {c, d, e}) :
    AEDisjoint volume (convexHull ℝ {c, a, b}) (convexHull ℝ {c, d, e}) := by
  have haFace : a ∈ closedCell cell ∩ {z | l.eval z = 0} := by
    rw [hfaceL]
    exact left_mem_segment ℝ a b
  have hbFace : b ∈ closedCell cell ∩ {z | l.eval z = 0} := by
    rw [hfaceL]
    exact right_mem_segment ℝ a b
  have hdFace : d ∈ closedCell cell ∩ {z | m.eval z = 0} := by
    rw [hfaceM]
    exact left_mem_segment ℝ d e
  have heFace : e ∈ closedCell cell ∩ {z | m.eval z = 0} := by
    rw [hfaceM]
    exact right_mem_segment ℝ d e
  have hca : c ≠ a := by
    intro h
    apply (ne_of_lt (hc l hlmem))
    simpa [h] using haFace.2
  have hcb : c ≠ b := by
    intro h
    apply (ne_of_lt (hc l hlmem))
    simpa [h] using hbFace.2
  have hcd : c ≠ d := by
    intro h
    apply (ne_of_lt (hc m hmmem))
    simpa [h] using hdFace.2
  have hce : c ≠ e := by
    intro h
    apply (ne_of_lt (hc m hmmem))
    simpa [h] using heFace.2
  by_cases hnon : ∃ z, z ∈ convexHull ℝ {c, a, b} ∩ convexHull ℝ {c, d, e} ∧ z ≠ c
  · obtain ⟨z₀, hz₀, hz₀c⟩ := hnon
    obtain ⟨p₀, hp₀seg, hz₀p⟩ := triangle_hull_factors c a b z₀ hca hcb hab hz₀.1 hz₀c
    obtain ⟨q₀, hq₀seg, hz₀q⟩ := triangle_hull_factors c d e z₀ hcd hce hde hz₀.2 hz₀c
    have hp₀face : p₀ ∈ closedCell cell ∩ {z | l.eval z = 0} := by rw [hfaceL]; exact hp₀seg
    have hq₀face : q₀ ∈ closedCell cell ∩ {z | m.eval z = 0} := by rw [hfaceM]; exact hq₀seg
    have hp₀q₀ := segment_ray_eq_of_strict_cell cell c p₀ q₀ z₀ l m
      hlmem hmmem hc hp₀face.1 hq₀face.1 hp₀face.2 hq₀face.2 hz₀c hz₀p hz₀q
    have hm₀ : m.eval p₀ = 0 := by rw [hp₀q₀]; exact hq₀face.2
    have hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 := by
      intro hzero
      obtain ⟨r, hr, heval⟩ := lineEval_parallel_eq l m hzero p₀ hp₀face.2 hm₀
      have hfaces : closedCell cell ∩ {z | l.eval z = 0} =
          closedCell cell ∩ {z | m.eval z = 0} := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hx, hlx⟩
          exact ⟨hx, by rw [heval x, hlx]; simp⟩
        · rintro ⟨hx, hmx⟩
          have hz : r * l.eval x = 0 := by simpa [heval x] using hmx
          rcases mul_eq_zero.mp hz with hr0 | hlx
          · exact False.elim (hr hr0)
          · exact ⟨hx, hlx⟩
      have hseg : segment ℝ a b = segment ℝ d e := by
        calc
          segment ℝ a b = closedCell cell ∩ {z | l.eval z = 0} := hfaceL.symm
          _ = closedCell cell ∩ {z | m.eval z = 0} := hfaces
          _ = segment ℝ d e := hfaceM
      exact htri (triple_hulls_eq_of_segment_eq c a b d e hseg)
    change volume (convexHull ℝ {c, a, b} ∩ convexHull ℝ {c, d, e}) = 0
    apply measure_mono_null ?_ (volume_convexHull_pair_eq_zero c p₀)
    intro x hx
    by_cases hxc : x = c
    · subst x
      exact subset_convexHull ℝ _ (by simp)
    · obtain ⟨p, hpseg, hxp⟩ := triangle_hull_factors c a b x hca hcb hab hx.1 hxc
      obtain ⟨q, hqseg, hxq⟩ := triangle_hull_factors c d e x hcd hce hde hx.2 hxc
      have hpface : p ∈ closedCell cell ∩ {z | l.eval z = 0} := by rw [hfaceL]; exact hpseg
      have hqface : q ∈ closedCell cell ∩ {z | m.eval z = 0} := by rw [hfaceM]; exact hqseg
      have hpq := segment_ray_eq_of_strict_cell cell c p q x l m
        hlmem hmmem hc hpface.1 hqface.1 hpface.2 hqface.2 hxc hxp hxq
      have hm_p : m.eval p = 0 := by rw [hpq]; exact hqface.2
      have hp₀p := common_zero_unique l m hdet p p₀
        hpface.2 hp₀face.2 hm_p hm₀
      have hxp₀ : x ∈ segment ℝ c p₀ := by simpa [hp₀p] using hxp
      exact segment_subset_convexHull (by simp) (by simp) hxp₀
  · have hsub : convexHull ℝ {c, a, b} ∩ convexHull ℝ {c, d, e} ⊆ convexHull ℝ {c, c} := by
      intro x hx
      have hxc : x = c := by
        by_contra hn
        exact hnon ⟨x, hx, hn⟩
      rw [hxc]
      exact subset_convexHull ℝ _ (by simp)
    change volume (convexHull ℝ {c, a, b} ∩ convexHull ℝ {c, d, e}) = 0
    exact measure_mono_null hsub (volume_convexHull_pair_eq_zero c c)

private theorem left_endpoint_openSegment_unique (a b y z : Plane) (hab : a ≠ b)
    (hy : y ∈ segment ℝ a b) (hz : z ∈ segment ℝ a b)
    (ha : a ∈ openSegment ℝ y z) : y = a := by
  obtain ⟨α, β, hα, hβ, hsum, hyform⟩ := hy
  obtain ⟨γ, δ, hγ, hδ, hsum', hzform⟩ := hz
  obtain ⟨r, s, hr, hs, hrsum, hpoint⟩ := ha
  have hyparam : y = a + β • (b - a) := by
    calc
      y = α • a + β • b := hyform.symm
      _ = (α + β) • a + β • (b - a) := by module
      _ = a + β • (b - a) := by rw [hsum]; simp
  have hzparam : z = a + δ • (b - a) := by
    calc
      z = γ • a + δ • b := hzform.symm
      _ = (γ + δ) • a + δ • (b - a) := by module
      _ = a + δ • (b - a) := by rw [hsum']; simp
  have hmodule : r • y + s • z = (r + s) • a + (r * β + s * δ) • (b - a) := by
    rw [hyparam, hzparam]
    module
  have hzero : (r * β + s * δ) • (b - a) = 0 := by
    have hcalc : r • y + s • z = a + (r * β + s * δ) • (b - a) := by
      rw [hmodule, hrsum]
      simp
    rw [hcalc] at hpoint
    exact add_left_cancel (show a + (r * β + s * δ) • (b - a) = a + 0 by
      simpa using hpoint)
  have hcoef : r * β + s * δ = 0 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact h
    · exact (hab (sub_eq_zero.mp h).symm).elim
  have hβ : β = 0 := by nlinarith
  rw [hyparam, hβ, zero_smul, add_zero]

private theorem face_endpoint_extreme (cell : List RationalLine) (l : RationalLine)
    (hl : l ∈ cell) (a b x : Plane)
    (hface : closedCell cell ∩ {z | l.eval z = 0} = segment ℝ a b)
    (hxend : x = a ∨ x = b) : x ∈ (closedCell cell).extremePoints ℝ := by
  have hxend' := hxend
  have hxseg : x ∈ segment ℝ a b := by
    exact hxend.elim (fun h => h ▸ left_mem_segment ℝ a b)
      (fun h => h ▸ right_mem_segment ℝ a b)
  have hxface : x ∈ closedCell cell ∩ {z | l.eval z = 0} := by
    rw [hface]
    exact hxseg
  refine mem_extremePoints_iff_left.mpr ⟨hxface.1, ?_⟩
  intro y hy z hz hxopen
  have hxopen' := hxopen
  obtain ⟨r, s, hr, hs, hrsum, hpoint⟩ := hxopen
  have hweighted : 0 = r * l.eval y + s * l.eval z := by
    have hformula := lineEval_affine l y z r s
    have hxline : l.eval x = 0 := hxface.2
    calc
      0 = l.eval x := hxline.symm
      _ = l.eval (r • y + s • z) := by rw [hpoint]
      _ = r * l.eval y + s * l.eval z + (r + s - 1) * l.offset := hformula
      _ = r * l.eval y + s * l.eval z := by rw [show r + s - 1 = 0 by linarith]; ring
  have hyline : l.eval y = 0 := by
    have hyineq : l.eval y ≤ 0 := hy l hl
    have hzineq : l.eval z ≤ 0 := hz l hl
    nlinarith
  have hzline : l.eval z = 0 := by
    have hyineq : l.eval y ≤ 0 := hy l hl
    have hzineq : l.eval z ≤ 0 := hz l hl
    nlinarith
  have hyface : y ∈ closedCell cell ∩ {z | l.eval z = 0} := ⟨hy, hyline⟩
  have hzface : z ∈ closedCell cell ∩ {z | l.eval z = 0} := ⟨hz, hzline⟩
  have hyseg : y ∈ segment ℝ a b := by rw [← hface]; exact hyface
  have hzseg : z ∈ segment ℝ a b := by rw [← hface]; exact hzface
  rcases hxend' with hleft | hright
  · have haopen : a ∈ openSegment ℝ y z := by simpa [hleft] using hxopen'
    by_cases hab : a = b
    · simpa [hab, hleft] using hyseg
    · have hy_eq := left_endpoint_openSegment_unique a b y z hab hyseg hzseg haopen
      simpa [hleft] using hy_eq
  · have hbopen : b ∈ openSegment ℝ y z := by simpa [hright] using hxopen'
    by_cases hab : a = b
    · simpa [hab, hright] using hyseg
    · have hyseg' : y ∈ segment ℝ b a := by simpa [segment_symm] using hyseg
      have hzseg' : z ∈ segment ℝ b a := by simpa [segment_symm] using hzseg
      have hba : b ≠ a := fun h => hab h.symm
      have hy_eq := left_endpoint_openSegment_unique b a y z hba hyseg' hzseg' hbopen
      simpa [hright] using hy_eq

private theorem closedCell_activeFace_isExtreme (cell : List RationalLine) (l : RationalLine)
    (hl : l ∈ cell) :
    IsExtreme ℝ (closedCell cell) (closedCell cell ∩ {z | l.eval z = 0}) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hxopen
  obtain ⟨r, s, hr, hs, hrsum, hpoint⟩ := hxopen
  have hweighted : 0 = r * l.eval x + s * l.eval y := by
    have hformula := lineEval_affine l x y r s
    have hzline : l.eval z = 0 := hz.2
    calc
      0 = l.eval z := hzline.symm
      _ = l.eval (r • x + s • y) := by rw [hpoint]
      _ = r * l.eval x + s * l.eval y + (r + s - 1) * l.offset := hformula
      _ = r * l.eval x + s * l.eval y := by rw [show r + s - 1 = 0 by linarith]; ring
  have hxline : l.eval x = 0 := by
    have hxineq : l.eval x ≤ 0 := hx l hl
    have hyineq : l.eval y ≤ 0 := hy l hl
    nlinarith
  have hyline : l.eval y = 0 := by
    have hxineq : l.eval x ≤ 0 := hx l hl
    have hyineq : l.eval y ≤ 0 := hy l hl
    nlinarith
  exact ⟨hx, hxline⟩

private theorem closedCell_face_segment_endpoints_extreme
    (cell : List RationalLine) (l : RationalLine) (hl : l ∈ cell)
    (a b : Plane)
    (hface : closedCell cell ∩ {z | l.eval z = 0} = segment ℝ a b) :
    a ∈ (closedCell cell).extremePoints ℝ ∧ b ∈ (closedCell cell).extremePoints ℝ := by
  constructor
  · exact face_endpoint_extreme cell l hl a b a hface (Or.inl rfl)
  · exact face_endpoint_extreme cell l hl a b b hface (Or.inr rfl)

private theorem closedCell_face_convex (cell : List RationalLine) (l : RationalLine)
    (_hl : l ∈ cell) : Convex ℝ (closedCell cell ∩ {z | l.eval z = 0}) := by
  have heq : closedCell cell ∩ {z | l.eval z = 0} =
      closedCell cell ∩ {z | normalEval l.normal z = l.offset} := by
    ext z
    simp [RationalLine.eval, sub_eq_zero]
  rw [heq]
  exact (closedCell_convex cell).inter
    (convex_hyperplane (normalEval_isLinear l.normal) l.offset)

private theorem closedCell_face_compact (cell : List RationalLine) (l : RationalLine)
    (hcompact : IsCompact (closedCell cell)) :
    IsCompact (closedCell cell ∩ {z | l.eval z = 0}) := by
  exact hcompact.inter_right (isClosed_eq (lineEval_continuous l) continuous_const)

private theorem face_target_extreme_subset (C D : List RationalLine)
    (l : RationalLine) (hl : l ∈ C) (m : RationalLine) (hm : m ∈ D)
    (f : Plane → Plane) (a b : Plane)
    (hImage : (closedCell D).extremePoints ℝ = f '' (closedCell C).extremePoints ℝ)
    (hReflect : ∀ v ∈ (closedCell C).extremePoints ℝ,
      m.eval (f v) = 0 ↔ l.eval v = 0)
    (hSourceFace : closedCell C ∩ {z | l.eval z = 0} = segment ℝ a b) :
    (closedCell D ∩ {z | m.eval z = 0}).extremePoints ℝ ⊆ {f a, f b} := by
  have hSourceExtremeFace := closedCell_activeFace_isExtreme C l hl
  intro x hx
  rw [(closedCell_activeFace_isExtreme D m hm).extremePoints_eq] at hx
  have hxTargetExtreme := hx.2
  rw [hImage] at hxTargetExtreme
  rcases hxTargetExtreme with ⟨v, hv, hxv⟩
  have hvline : m.eval (f v) = 0 := by simpa [hxv] using hx.1.2
  have hvsourceface : v ∈ closedCell C ∩ {z | l.eval z = 0} :=
    ⟨hv.1, (hReflect v hv).mp hvline⟩
  have hvfaceExtreme : v ∈ (closedCell C ∩ {z | l.eval z = 0}).extremePoints ℝ := by
    rw [hSourceExtremeFace.extremePoints_eq]
    exact ⟨hvsourceface, hv⟩
  rw [hSourceFace] at hvfaceExtreme
  rw [← convexHull_pair] at hvfaceExtreme
  have hvpair : v ∈ ({a, b} : Set Plane) := extremePoints_convexHull_subset hvfaceExtreme
  rcases (show v = a ∨ v = b by simpa using hvpair) with hva | hvb
  · rw [← hxv, hva]
    exact mem_insert _ _
  · rw [← hxv, hvb]
    exact mem_insert_of_mem _ (mem_singleton _)

private theorem face_transport_eq_segment
    (C D : List RationalLine) (l : RationalLine) (hl : l ∈ C)
    (m : RationalLine) (hm : m ∈ D) (f : Plane → Plane)
    (hcompact : IsCompact (closedCell D))
    (hImage : (closedCell D).extremePoints ℝ = f '' (closedCell C).extremePoints ℝ)
    (hReflect : ∀ v ∈ (closedCell C).extremePoints ℝ,
      m.eval (f v) = 0 ↔ l.eval v = 0)
    (a b : Plane)
    (hSourceFace : closedCell C ∩ {z | l.eval z = 0} = segment ℝ a b) :
    closedCell D ∩ {z | m.eval z = 0} = segment ℝ (f a) (f b) := by
  let F := closedCell D ∩ {z | m.eval z = 0}
  have hFaceCompact : IsCompact F := by
    dsimp [F]
    exact closedCell_face_compact D m hcompact
  have hFaceConvex : Convex ℝ F := by
    dsimp [F]
    exact closedCell_face_convex D m hm
  have hFaceExtremeSubset : F.extremePoints ℝ ⊆ {f a, f b} := by
    dsimp [F]
    exact face_target_extreme_subset C D l hl m hm f a b hImage hReflect hSourceFace
  have hFaceExtremeFinite : (F.extremePoints ℝ).Finite :=
    (Set.finite_singleton (f b)).insert (f a) |>.subset hFaceExtremeSubset
  have hHullSubset : convexHull ℝ (F.extremePoints ℝ) ⊆ segment ℝ (f a) (f b) := by
    calc
      convexHull ℝ (F.extremePoints ℝ) ⊆ convexHull ℝ ({f a, f b} : Set Plane) :=
        convexHull_mono hFaceExtremeSubset
      _ = segment ℝ (f a) (f b) := convexHull_pair (f a) (f b)
  have hFsubset : F ⊆ segment ℝ (f a) (f b) := by
    have hKM := closure_convexHull_extremePoints hFaceCompact hFaceConvex
    calc
      F = closure (convexHull ℝ (F.extremePoints ℝ)) := hKM.symm
      _ = convexHull ℝ (F.extremePoints ℝ) :=
        (hFaceExtremeFinite.isClosed_convexHull ℝ).closure_eq
      _ ⊆ segment ℝ (f a) (f b) := hHullSubset
  have hfa : f a ∈ F := by
    have haSource : a ∈ (closedCell C).extremePoints ℝ :=
      face_endpoint_extreme C l hl a b a hSourceFace (Or.inl rfl)
    have haTarget : f a ∈ (closedCell D).extremePoints ℝ := by
      rw [hImage]
      exact ⟨a, haSource, rfl⟩
    have haLine : m.eval (f a) = 0 := (hReflect a haSource).mpr (by
      have : a ∈ segment ℝ a b := left_mem_segment ℝ a b
      rw [← hSourceFace] at this
      exact this.2)
    exact ⟨haTarget.1, haLine⟩
  have hfb : f b ∈ F := by
    have hbSource : b ∈ (closedCell C).extremePoints ℝ :=
      face_endpoint_extreme C l hl a b b hSourceFace (Or.inr rfl)
    have hbTarget : f b ∈ (closedCell D).extremePoints ℝ := by
      rw [hImage]
      exact ⟨b, hbSource, rfl⟩
    have hbLine : m.eval (f b) = 0 := (hReflect b hbSource).mpr (by
      have : b ∈ segment ℝ a b := right_mem_segment ℝ a b
      rw [← hSourceFace] at this
      exact this.2)
    exact ⟨hbTarget.1, hbLine⟩
  have hSegmentSubset : segment ℝ (f a) (f b) ⊆ F := hFaceConvex.segment_subset hfa hfb
  exact Subset.antisymm hFsubset hSegmentSubset


/-- Actual finite nondegenerate fan pieces cover a compact full-dimensional cell. Singleton
faces are discarded only after their finite union of rays is proved null and nowhere dense. -/
private theorem closedCell_fanModel (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ A : Tiling.Triangulation (closedCell cell),
      (∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ insert c ((closedCell cell).extremePoints ℝ)) ∧
      (∀ t ∈ A.pieces, ∃ l ∈ cell, ∃ a b : Plane,
        a ≠ b ∧ cellFace cell l = segment ℝ a b ∧
          Tiling.twiceSignedArea c a b ≠ 0 ∧ t = convexHull ℝ {c, a, b}) ∧
      (∀ l ∈ cell, ∀ a b : Plane, a ≠ b → cellFace cell l = segment ℝ a b →
        convexHull ℝ {c, a, b} ∈ A.pieces) := by
  classical
  let F : Finset RationalLine := cell.toFinset.filter fun l => (cellFace cell l).Nonempty
  have hsegments : ∀ l : {l // l ∈ F}, ∃ a b : Plane, cellFace cell l.1 = segment ℝ a b := by
    intro l
    exact cellFace_eq_segment cell l.1 hcompact (Finset.mem_filter.mp l.2).2
  choose a b hface using hsegments
  let good : Finset {l // l ∈ F} := Finset.univ.filter fun l => a l ≠ b l
  let bad : Finset {l // l ∈ F} := Finset.univ.filter fun l => a l = b l
  let triangle := fun l : {l // l ∈ F} => convexHull ℝ {c, a l, b l}
  let U : Set Plane := ⋃ l ∈ good, triangle l
  let B : Set Plane := {c} ∪ ⋃ l ∈ bad, segment ℝ c (a l)
  have hacell (l : {l // l ∈ F}) : a l ∈ closedCell cell := by
    have hm : a l ∈ cellFace cell l.1 := (hface l).symm ▸ left_mem_segment ℝ (a l) (b l)
    exact hm.1
  have hbcell (l : {l // l ∈ F}) : b l ∈ closedCell cell := by
    have hm : b l ∈ cellFace cell l.1 := (hface l).symm ▸ right_mem_segment ℝ (a l) (b l)
    exact hm.1
  have haline (l : {l // l ∈ F}) : l.1.eval (a l) = 0 := by
    exact ((hface l).symm ▸ left_mem_segment ℝ (a l) (b l) : a l ∈ cellFace cell l.1).2
  have hbline (l : {l // l ∈ F}) : l.1.eval (b l) = 0 := by
    exact ((hface l).symm ▸ right_mem_segment ℝ (a l) (b l) : b l ∈ cellFace cell l.1).2
  have hUclosed : IsClosed U := isClosed_biUnion_finset fun l _ =>
    (Set.toFinite {c, a l, b l}).isClosed_convexHull ℝ
  have hBzero : volume B = 0 := measure_union_null (measure_singleton c)
    ((measure_biUnion_null_iff bad.countable_toSet).mpr fun l _ => volume_segment_zero c (a l))
  have hUsub : U ⊆ closedCell cell := by
    intro z hz
    obtain ⟨l, _, hz⟩ := mem_iUnion₂.mp hz
    apply convexHull_min _ (closedCell_convex cell) hz
    intro w hw
    simp only [mem_insert_iff, mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact fun k hk => (hc k hk).le
    · exact hacell l
    · exact hbcell l
  have hclean : openCell cell ∩ Bᶜ ⊆ U := by
    rintro x ⟨hx, hxB⟩
    have hxc : x ≠ c := fun h => hxB (Or.inl (mem_singleton_iff.mpr h))
    obtain ⟨y, hy, hxy⟩ := closedCell_radial_boundary cell c x hcompact
      (fun k hk => (hx k hk).le) hxc
    obtain ⟨l, hl, hly⟩ := closedCell_frontier_lines cell y hy
    have hycell : y ∈ closedCell cell :=
      (closedCell_isClosed cell).closure_eq ▸ frontier_subset_closure hy
    have hlF : l ∈ F := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hl, ⟨y, hycell, hly⟩⟩
    let i : {l // l ∈ F} := ⟨l, hlF⟩
    have hyface : y ∈ segment ℝ (a i) (b i) := (hface i) ▸ ⟨hycell, hly⟩
    have hxtri : x ∈ triangle i := (convex_convexHull ℝ {c, a i, b i}).segment_subset
      (subset_convexHull ℝ _ (by simp))
      (segment_subset_convexHull (by simp) (by simp) hyface) hxy
    by_cases hab : a i = b i
    · apply False.elim
      apply hxB
      right
      apply mem_iUnion₂.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, ?_⟩
      simpa [triangle, hab, ← convexHull_pair] using hxtri
    · exact mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, hxtri⟩
  have hcellU : closedCell cell ⊆ U := by
    rw [← openCell_closure cell ⟨c, hc⟩]
    apply closure_minimal _ hUclosed
    exact ((dense_compl_of_volume_zero B hBzero).open_subset_closure_inter
      (openCell_isOpen cell)).trans (closure_minimal hclean hUclosed)
  refine ⟨⟨good.image triangle, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    apply fanTriangle_isTriangle l.1 c (a l) (b l)
      (hc l.1 (List.mem_toFinset.mp (Finset.mem_filter.mp l.2).1))
      (haline l) (hbline l) (Finset.mem_filter.mp hl).2
  · intro t ht u hu htu
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hu
    exact distinct_fan_triangles_aedisjoint cell c (a l) (b l) (a m) (b m) l.1 m.1
      (List.mem_toFinset.mp (Finset.mem_filter.mp l.2).1)
      (List.mem_toFinset.mp (Finset.mem_filter.mp m.2).1) hc (hface l) (hface m)
      (Finset.mem_filter.mp hl).2 (Finset.mem_filter.mp hm).2 htu
  · have heq : ⋃₀ ((good.image triangle : Finset (Set Plane)) : Set (Set Plane)) = U := by
      ext z
      simp [U]
    rw [heq]
    exact subset_antisymm hUsub hcellU
  · intro t ht z hz
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    have hend := closedCell_face_segment_endpoints_extreme cell l.1
      (List.mem_toFinset.mp (Finset.mem_filter.mp l.2).1) (a l) (b l) (hface l)
    have hz' : z ∈ ({c, a l, b l} : Set Plane) := extremePoints_convexHull_subset hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz'
    rcases hz' with hz' | hz' | hz'
    · exact Or.inl hz'
    · exact Or.inr (hz'.symm ▸ hend.1)
    · exact Or.inr (hz'.symm ▸ hend.2)

  · intro t ht
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    have hlcell := List.mem_toFinset.mp (Finset.mem_filter.mp l.2).1
    have hab := (Finset.mem_filter.mp hl).2
    exact ⟨l.1, hlcell, a l, b l, hab, hface l,
      fanTriangle_area_ne l.1 c (a l) (b l) (hc l.1 hlcell) (haline l) (hbline l) hab, rfl⟩
  · intro l hl d e hde hdeFace
    have hlF : l ∈ F := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hl, ⟨d, hdeFace.symm ▸ left_mem_segment ℝ d e⟩⟩
    let i : {l // l ∈ F} := ⟨l, hlF⟩
    have hseg : segment ℝ d e = segment ℝ (a i) (b i) :=
      hdeFace.symm.trans (hface i)
    have hab : a i ≠ b i := by
      intro hab
      have hd : d ∈ segment ℝ (a i) (b i) := hseg ▸ left_mem_segment ℝ d e
      have he : e ∈ segment ℝ (a i) (b i) := hseg ▸ right_mem_segment ℝ d e
      have hd' : d = a i := by simpa [hab] using hd
      have he' : e = a i := by simpa [hab] using he
      exact hde (hd'.trans he'.symm)
    have ht := triple_hulls_eq_of_segment_eq c d e (a i) (b i) hseg
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩, ?_⟩
    exact ht.symm

private theorem closedCell_fanTriangulation (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ A : Tiling.Triangulation (closedCell cell),
      ∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ insert c ((closedCell cell).extremePoints ℝ) := by
  obtain ⟨A, hA, _⟩ := closedCell_fanModel cell hcompact c hc
  exact ⟨A, hA⟩

private theorem closedCell_isPolygonal (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (openCell cell).Nonempty) :
    Tiling.IsPolygonal (closedCell cell) := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨A, _⟩ := closedCell_fanTriangulation cell hcompact c hc
  exact ⟨A⟩

private def negateLine (l : RationalLine) : RationalLine :=
  ⟨⟨-l.normal.x, -l.normal.y, by
    rcases l.normal.nonzero with hx | hy
    · exact Or.inl (neg_ne_zero.mpr hx)
    · exact Or.inr (neg_ne_zero.mpr hy)⟩, -l.offset⟩

private theorem negateLine_eval (l : RationalLine) (z : Plane) :
    (negateLine l).eval z = -l.eval z := by
  simp only [negateLine, RationalLine.eval, normalEval, Rat.cast_neg]
  ring

private def signedCodes : List RationalLine → PolyhedralCode
  | [] => [[]]
  | l :: L => (signedCodes L).map (fun cell => l :: cell) ++
      (signedCodes L).map (fun cell => negateLine l :: cell)

private theorem signedCodes_separate (L : List RationalLine) :
    ∀ cell ∈ signedCodes L, ∀ other ∈ signedCodes L, cell ≠ other →
      ∃ l ∈ cell, closedCell cell ∩ closedCell other ⊆ {z | l.eval z = 0} := by
  induction L with
  | nil =>
    intro cell hc other ho hne
    simp only [signedCodes, List.mem_singleton] at hc ho
    exact False.elim (hne (hc.trans ho.symm))
  | cons k L ih =>
    intro cell hc other ho hne
    simp only [signedCodes, List.mem_append, List.mem_map] at hc ho
    rcases hc with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      rcases ho with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · obtain ⟨l, hl, hzero⟩ := ih c hc d hd (fun h => hne (congrArg (List.cons k) h))
      refine ⟨l, List.mem_cons_of_mem k hl, ?_⟩
      intro z hz
      exact hzero ⟨fun m hm => hz.1 m (List.mem_cons_of_mem k hm),
        fun m hm => hz.2 m (List.mem_cons_of_mem k hm)⟩
    · refine ⟨k, List.mem_cons_self, ?_⟩
      intro z hz
      have h₁ := hz.1 k List.mem_cons_self
      have h₂ := hz.2 (negateLine k) List.mem_cons_self
      rw [negateLine_eval] at h₂
      exact le_antisymm h₁ (by linarith)
    · refine ⟨negateLine k, List.mem_cons_self, ?_⟩
      intro z hz
      have h₁ := hz.1 (negateLine k) List.mem_cons_self
      have h₂ := hz.2 k List.mem_cons_self
      change (negateLine k).eval z = 0
      rw [negateLine_eval] at h₁ ⊢
      linarith
    · obtain ⟨l, hl, hzero⟩ := ih c hc d hd
        (fun h => hne (congrArg (List.cons (negateLine k)) h))
      refine ⟨l, List.mem_cons_of_mem (negateLine k) hl, ?_⟩
      intro z hz
      exact hzero ⟨fun m hm => hz.1 m (List.mem_cons_of_mem (negateLine k) hm),
        fun m hm => hz.2 m (List.mem_cons_of_mem (negateLine k) hm)⟩

private theorem signedCodes_aedisjoint (L : List RationalLine)
    (cell other : List RationalLine) (hc : cell ∈ signedCodes L)
    (ho : other ∈ signedCodes L) (hne : cell ≠ other)
    (hcompact : IsCompact (closedCell cell)) :
    AEDisjoint volume (closedCell cell) (closedCell other) := by
  obtain ⟨l, hl, hzero⟩ := signedCodes_separate L cell hc other ho hne
  by_cases hface : (cellFace cell l).Nonempty
  · obtain ⟨a, b, hab⟩ := cellFace_eq_segment cell l hcompact hface
    change volume (closedCell cell ∩ closedCell other) = 0
    apply measure_mono_null ?_ (volume_segment_zero a b)
    intro z hz
    rw [← hab]
    exact ⟨hz.1, hzero hz⟩
  · have he : closedCell cell ∩ closedCell other = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hface ⟨z, hz.1, hzero hz⟩
    change volume (closedCell cell ∩ closedCell other) = 0
    rw [he, measure_empty]

private theorem negateLine_deformLine (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) :
    negateLine (deformLine φ l) = deformLine φ (negateLine l) := by
  cases l
  simp [negateLine, deformLine, map_neg]

private theorem deformedSignedCodes_separate (L : List RationalLine)
    (φ : ℝ →ₗ[ℚ] ℚ) :
    ∀ cell ∈ signedCodes L, ∀ other ∈ signedCodes L, cell ≠ other →
      ∃ l ∈ cell,
        closedCell (cell.map (deformLine φ)) ∩
          closedCell (other.map (deformLine φ)) ⊆
            {z | (deformLine φ l).eval z = 0} := by
  induction L with
  | nil =>
    intro cell hc other ho hne
    simp only [signedCodes, List.mem_singleton] at hc ho
    exact False.elim (hne (hc.trans ho.symm))
  | cons k L ih =>
    intro cell hc other ho hne
    simp only [signedCodes, List.mem_append, List.mem_map] at hc ho
    rcases hc with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩ <;>
      rcases ho with ⟨d, hd, rfl⟩ | ⟨d, hd, rfl⟩
    · obtain ⟨l, hl, hzero⟩ := ih c hc d hd
        (fun h => hne (congrArg (List.cons k) h))
      refine ⟨l, List.mem_cons_of_mem k hl, ?_⟩
      intro z hz
      apply hzero
      constructor
      · intro m hm
        exact hz.1 m (List.mem_cons_of_mem _ hm)
      · intro m hm
        exact hz.2 m (List.mem_cons_of_mem _ hm)
    · refine ⟨k, List.mem_cons_self, ?_⟩
      intro z hz
      have h₁ := hz.1 (deformLine φ k) List.mem_cons_self
      have h₂ := hz.2 (deformLine φ (negateLine k)) List.mem_cons_self
      rw [← negateLine_deformLine] at h₂
      rw [negateLine_eval] at h₂
      change (deformLine φ k).eval z = 0
      exact le_antisymm h₁ (by linarith)
    · refine ⟨negateLine k, List.mem_cons_self, ?_⟩
      intro z hz
      have h₁ := hz.1 (deformLine φ (negateLine k)) List.mem_cons_self
      have h₂ := hz.2 (deformLine φ k) List.mem_cons_self
      rw [← negateLine_deformLine] at h₁
      rw [negateLine_eval] at h₁
      change (deformLine φ (negateLine k)).eval z = 0
      rw [← negateLine_deformLine]
      rw [negateLine_eval]
      linarith
    · obtain ⟨l, hl, hzero⟩ := ih c hc d hd
        (fun h => hne (congrArg (List.cons (negateLine k)) h))
      refine ⟨l, ?_, ?_⟩
      · exact List.mem_cons_of_mem (negateLine k) hl
      · intro z hz
        apply hzero
        constructor
        · intro m hm
          exact hz.1 m (List.mem_cons_of_mem _ hm)
        · intro m hm
          exact hz.2 m (List.mem_cons_of_mem _ hm)

private theorem deformedSignedCodes_aedisjoint (L : List RationalLine) (φ : ℝ →ₗ[ℚ] ℚ)
    (cell other : List RationalLine) (hc : cell ∈ signedCodes L)
    (ho : other ∈ signedCodes L) (hne : cell ≠ other)
    (hcompact : IsCompact (closedCell (cell.map (deformLine φ)))) :
    AEDisjoint volume (closedCell (cell.map (deformLine φ)))
      (closedCell (other.map (deformLine φ))) := by
  obtain ⟨l, hl, hzero⟩ := deformedSignedCodes_separate L φ cell hc other ho hne
  let C := cell.map (deformLine φ)
  let D := other.map (deformLine φ)
  by_cases hface : (cellFace C (deformLine φ l)).Nonempty
  · obtain ⟨a, b, hab⟩ := cellFace_eq_segment C (deformLine φ l) hcompact hface
    change volume (closedCell C ∩ closedCell D) = 0
    apply measure_mono_null ?_ (volume_segment_zero a b)
    intro z hz
    rw [← hab]
    exact ⟨hz.1, hzero hz⟩
  · have he : closedCell C ∩ closedCell D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hface ⟨z, hz.1, hzero hz⟩
    change volume (closedCell C ∩ closedCell D) = 0
    rw [he, measure_empty]

private theorem signedCodes_has_each_line (L : List RationalLine) :
    ∀ cell ∈ signedCodes L, ∀ l ∈ L, l ∈ cell ∨ negateLine l ∈ cell := by
  induction L with
  | nil => simp
  | cons m L ih =>
    intro cell hc l hl
    simp only [signedCodes, List.mem_append, List.mem_map] at hc
    rcases hc with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inl List.mem_cons_self
      · exact (ih c hc l hl).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
    · rcases List.mem_cons.mp hl with rfl | hl
      · exact Or.inr List.mem_cons_self
      · exact (ih c hc l hl).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)

private def offLines (L : List RationalLine) : Set Plane :=
  {z | ∀ l ∈ L, l.eval z ≠ 0}

private theorem offLines_isOpen (L : List RationalLine) : IsOpen (offLines L) := by
  induction L with
  | nil => simp [offLines]
  | cons l L ih =>
    have heq : offLines (l :: L) = {z | l.eval z ≠ 0} ∩ offLines L := by
      ext z
      simp [offLines]
    rw [heq]
    exact (isOpen_ne.preimage (lineEval_continuous l)).inter ih

private theorem lineComplement_dense (l : RationalLine) : Dense {z | l.eval z ≠ 0} := by
  let f : Plane →ₗ[ℝ] ℝ :=
    (((l.normal.x : ℝ) • Complex.reCLM +
      (l.normal.y : ℝ) • Complex.imCLM).toLinearMap)
  have hsurj : Function.Surjective f := by
    intro r
    rcases l.normal.nonzero with hx | hy
    · have hx' : (l.normal.x : ℝ) ≠ 0 := by exact_mod_cast hx
      refine ⟨Complex.mk (r / (l.normal.x : ℝ)) 0, ?_⟩
      change (l.normal.x : ℝ) * (r / (l.normal.x : ℝ)) + (l.normal.y : ℝ) * 0 = r
      field_simp
      ring
    · have hy' : (l.normal.y : ℝ) ≠ 0 := by exact_mod_cast hy
      refine ⟨Complex.mk 0 (r / (l.normal.y : ℝ)), ?_⟩
      change (l.normal.x : ℝ) * 0 + (l.normal.y : ℝ) * (r / (l.normal.y : ℝ)) = r
      field_simp
      ring
  have hd := (dense_compl_singleton l.offset).preimage
    (IsModuleTopology.isOpenMap_of_surjective hsurj)
  change Dense {z : Plane | normalEval l.normal z ≠ l.offset} at hd
  simpa only [RationalLine.eval, sub_ne_zero] using hd

private theorem offLines_dense (L : List RationalLine) : Dense (offLines L) := by
  induction L with
  | nil => simp [offLines]
  | cons l L ih =>
    have heq : offLines (l :: L) = {z | l.eval z ≠ 0} ∩ offLines L := by
      ext z
      simp [offLines]
    rw [heq]
    exact (lineComplement_dense l).inter_of_isOpen_right ih (offLines_isOpen L)

private theorem offLines_covered_by_signedCodes (L : List RationalLine) :
    ∀ z ∈ offLines L, ∃ cell ∈ signedCodes L, z ∈ openCell cell := by
  induction L with
  | nil => intro z _; exact ⟨[], by simp [signedCodes], by simp [openCell]⟩
  | cons l L ih =>
    intro z hz
    have hzL : z ∈ offLines L := fun m hm => hz m (List.mem_cons_of_mem l hm)
    obtain ⟨cell, hc, hzcell⟩ := ih z hzL
    rcases (hz l List.mem_cons_self).lt_or_gt with hneg | hpos
    · refine ⟨l :: cell, ?_, ?_⟩
      · simp only [signedCodes, List.mem_append, List.mem_map]
        exact Or.inl ⟨cell, hc, rfl⟩
      · simp only [openCell, mem_ofPred_eq, List.mem_cons, forall_eq_or_imp]
        exact ⟨hneg, hzcell⟩
    · refine ⟨negateLine l :: cell, ?_, ?_⟩
      · simp only [signedCodes, List.mem_append, List.mem_map]
        exact Or.inr ⟨cell, hc, rfl⟩
      · simp only [openCell, mem_ofPred_eq, List.mem_cons, forall_eq_or_imp]
        exact ⟨by rw [negateLine_eval]; exact neg_neg_of_pos hpos, hzcell⟩

private theorem polyhedralSupport_isClosed (P : PolyhedralCode) :
    IsClosed (polyhedralSupport P) := by
  induction P with
  | nil => simp [polyhedralSupport]
  | cons cell P ih =>
    have heq : polyhedralSupport (cell :: P) = closedCell cell ∪ polyhedralSupport P := by
      ext z
      simp [polyhedralSupport, closedCell]
    rw [heq]
    exact (closedCell_isClosed cell).union ih

private theorem polyhedralSupport_frontier_lines (P : PolyhedralCode) :
    ∀ z ∈ frontier (polyhedralSupport P), ∃ l ∈ P.flatten, l.eval z = 0 := by
  induction P with
  | nil =>
    intro z hz
    simp [polyhedralSupport] at hz
  | cons cell P ih =>
    intro z hz
    have hsupport : polyhedralSupport (cell :: P) =
        closedCell cell ∪ polyhedralSupport P := by
      ext x
      simp [polyhedralSupport, closedCell]
    rw [hsupport] at hz
    rcases frontier_union_subset (closedCell cell) (polyhedralSupport P) hz with hcell | htail
    · obtain ⟨l, hl, he⟩ := closedCell_frontier_lines cell z hcell.1
      refine ⟨l, ?_, he⟩
      simp only [List.flatten_cons, List.mem_append]
      exact Or.inl hl
    · obtain ⟨l, hl, he⟩ := ih z htail.2
      refine ⟨l, ?_, he⟩
      simp only [List.flatten_cons, List.mem_append]
      exact Or.inr hl

/-- A chamber avoiding the finite frontier line family is wholly occupied or wholly outside.
The argument uses convex connectedness, so also applies to pinched or disconnected regions. -/
private theorem occupiedCell_subset_interior (s : Set Plane) (hs : IsClosed s) (L : List RationalLine)
    (hfront : ∀ z ∈ frontier s, ∃ l ∈ L, l.eval z = 0)
    (cell : List RationalLine) (hc : cell ∈ signedCodes L)
    (hne : (openCell cell ∩ interior s).Nonempty) :
    openCell cell ⊆ interior s := by
  have havoid : ∀ z ∈ openCell cell, z ∉ frontier s := by
    intro z hz hf
    obtain ⟨l, hl, he⟩ := hfront z hf
    rcases signedCodes_has_each_line L cell hc l hl with hm | hm
    · exact (ne_of_lt (hz l hm)) he
    · have hz' := hz (negateLine l) hm
      rw [negateLine_eval, he, neg_zero] at hz'
      exact (lt_irrefl 0) hz'
  have hcover : openCell cell ⊆ interior s ∪ sᶜ := by
    intro z hz
    by_cases hzK : z ∈ s
    · left
      by_contra hni
      exact havoid z hz ((mem_frontier_iff_notMem_interior hzK).mpr hni)
    · exact Or.inr hzK
  have hd : Disjoint (interior s) sᶜ :=
    Set.disjoint_left.mpr fun _ hi hc => hc (interior_subset hi)
  exact (openCell_convex cell).isPreconnected.subset_left_of_subset_union
    isOpen_interior hs.isOpen_compl hd hcover hne

/-- The normal form is built by selecting the occupied sign chambers, not by mapping all
points with the ambient rational-linear approximation. -/
private noncomputable def occupiedCodes (s : Set Plane) (L : List RationalLine) : PolyhedralCode :=
  (signedCodes L).filter (fun cell => by
    classical
    exact decide (openCell cell ∩ interior s).Nonempty)

private theorem occupiedCodes_support (s : Set Plane) (hs : IsClosed s)
    (hregular : closure (interior s) = s) (L : List RationalLine)
    (hfront : ∀ z ∈ frontier s, ∃ l ∈ L, l.eval z = 0) :
    polyhedralSupport (occupiedCodes s L) = s := by
  classical
  let P : PolyhedralCode := occupiedCodes s L
  have hsub : polyhedralSupport P ⊆ s := by
    rintro z ⟨cell, hc, hz⟩
    obtain ⟨hc, hne⟩ := List.mem_filter.mp hc
    have hne : (openCell cell ∩ interior s).Nonempty := of_decide_eq_true hne
    have hcell := occupiedCell_subset_interior s hs L hfront cell hc hne
    have hne' : (openCell cell).Nonempty := hne.mono inter_subset_left
    have hz' : z ∈ closure (openCell cell) := by
      rw [openCell_closure cell hne']
      exact hz
    exact closure_minimal (hcell.trans interior_subset) hs hz'
  have hinside : interior s ∩ offLines L ⊆ polyhedralSupport P := by
    rintro z ⟨hzK, hzL⟩
    obtain ⟨cell, hc, hzcell⟩ := offLines_covered_by_signedCodes L z hzL
    refine ⟨cell, List.mem_filter.mpr ⟨hc, ?_⟩, ?_⟩
    · exact decide_eq_true (show (openCell cell ∩ interior s).Nonempty from
        ⟨z, hzcell, hzK⟩)
    · intro l hl
      exact (hzcell l hl).le
  apply subset_antisymm hsub
  have hint : interior s ⊆ polyhedralSupport P :=
    ((offLines_dense L).open_subset_closure_inter isOpen_interior).trans
      (closure_minimal hinside (polyhedralSupport_isClosed P))
  rw [← hregular]
  exact closure_minimal hint (polyhedralSupport_isClosed P)

/-- Bounded regular-closed rational-normal codes admit the actual finite triangle model. -/
theorem polyhedralSupport_isPolygonal :
  ∀ P : PolyhedralCode, IsCompact (polyhedralSupport P) →
    closure (interior (polyhedralSupport P)) = polyhedralSupport P →
      Tiling.IsPolygonal (polyhedralSupport P) := by
  intro P hcompact hregular
  classical
  let Q := occupiedCodes (polyhedralSupport P) P.flatten
  have hQ : polyhedralSupport Q = polyhedralSupport P :=
    occupiedCodes_support (polyhedralSupport P) (polyhedralSupport_isClosed P)
      hregular P.flatten (polyhedralSupport_frontier_lines P)
  let S : Finset (List RationalLine) := Q.toFinset
  have hmem (i : {cell // cell ∈ S}) : i.1 ∈ Q := List.mem_toFinset.mp i.2
  have hselected (i : {cell // cell ∈ S}) :
      i.1 ∈ signedCodes P.flatten ∧ (openCell i.1 ∩ interior (polyhedralSupport P)).Nonempty := by
    obtain ⟨hc, hne⟩ := List.mem_filter.mp (hmem i)
    exact ⟨hc, of_decide_eq_true hne⟩
  have hbounded (i : {cell // cell ∈ S}) : IsCompact (closedCell i.1) := by
    apply hcompact.of_isClosed_subset (closedCell_isClosed i.1)
    intro z hz
    rw [← hQ]
    exact ⟨i.1, hmem i, hz⟩
  let T : ∀ i : {cell // cell ∈ S}, Tiling.Triangulation (closedCell i.1) := fun i =>
    Classical.choice (closedCell_isPolygonal i.1 (hbounded i)
      ((hselected i).2.mono inter_subset_left))
  have hpair : Pairwise (fun i j : {cell // cell ∈ S} =>
      AEDisjoint volume (closedCell i.1) (closedCell j.1)) := by
    intro i j hij
    exact signedCodes_aedisjoint P.flatten i.1 j.1 (hselected i).1 (hselected j).1
      (fun heq => hij (Subtype.ext heq)) (hbounded i)
  have hunion : (⋃ i : {cell // cell ∈ S}, closedCell i.1) = polyhedralSupport P := by
    rw [← hQ]
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact ⟨i.1, hmem i, hi⟩
    · rintro ⟨cell, hc, hz⟩
      exact mem_iUnion.mpr ⟨⟨cell, List.mem_toFinset.mpr hc⟩, hz⟩
  rw [← hunion]
  exact ⟨Tiling.Triangulation.finiteUnion T hpair⟩

/-- A compact regular-closed set with frontier supported by finitely many rational lines
admits a genuine finite triangulation. -/
theorem isPolygonal_of_finite_rational_frontier_lines (s : Set Plane)
    (hcompact : IsCompact s) (hregular : closure (interior s) = s)
    (L : List RationalLine) (hfront : ∀ z ∈ frontier s, ∃ l ∈ L, l.eval z = 0) :
    Tiling.IsPolygonal s := by
  let P := occupiedCodes s L
  have hP : polyhedralSupport P = s :=
    occupiedCodes_support s hcompact.isClosed hregular L hfront
  have hPc : IsCompact (polyhedralSupport P) := hP.symm ▸ hcompact
  have hPr : closure (interior (polyhedralSupport P)) = polyhedralSupport P := by
    rw [hP]
    exact hregular
  simpa only [hP] using polyhedralSupport_isPolygonal P hPc hPr

/-- A finite genuine triangulation decoration; it need not equal the intrinsic vertex set. -/
def Decorates (K : PolygonalRegion) (W : Finset Plane) : Prop :=
  ∃ A : Tiling.Triangulation K.support,
    ∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W : Set Plane)

private theorem exists_decoration (K : PolygonalRegion) :
    ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W := by
  classical
  obtain ⟨A⟩ := K.isPolygonal
  have hfinite : (⋃ t ∈ A.pieces, t.extremePoints ℝ).Finite := by
    apply A.pieces.finite_toSet.biUnion
    intro t ht
    obtain ⟨a, b, c, _, rfl⟩ := A.isTriangle t ht
    exact (Set.toFinite {a, b, c}).subset extremePoints_convexHull_subset
  let W : Finset Plane := insert 0 hfinite.toFinset
  refine ⟨W, ⟨A, ?_⟩, Finset.mem_insert_self _ _⟩
  intro t ht z hz
  exact Finset.mem_insert_of_mem (hfinite.mem_toFinset.mpr (mem_biUnion ht hz))

def decoratedCloud (W : Finset Plane) (T : Set Plane) : Set Plane :=
  (W : Set Plane) + T

private theorem exists_finiteDecoration (K : PolygonalRegion) :
    ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W := by
  classical
  obtain ⟨A⟩ := K.isPolygonal
  have htfinite : ∀ t ∈ A.pieces, (t.extremePoints ℝ).Finite := by
    intro t ht
    obtain ⟨a, b, c, _, rfl⟩ := A.isTriangle t ht
    exact (Set.toFinite {a, b, c}).subset extremePoints_convexHull_subset
  let V : Set Plane := ⋃ t ∈ A.pieces, t.extremePoints ℝ
  have hV : V.Finite := A.pieces.finite_toSet.biUnion htfinite
  refine ⟨insert 0 hV.toFinset, ⟨A, ?_⟩, by simp⟩
  intro t ht z hz
  apply Finset.mem_insert_of_mem
  exact hV.mem_toFinset.mpr (mem_biUnion ht hz)

theorem decorates_intrinsicVertices :
  ∀ (K : PolygonalRegion) (W : Finset Plane), Decorates K W →
    Tiling.vertexSet K.support ⊆ (W : Set Plane) := by
  rintro K W ⟨A, hA⟩ v hv
  obtain ⟨t, ht, hvt⟩ := hv A
  exact hA t ht hvt

private theorem rationalSlopes_frontierLineFamily :
  ∀ K : PolygonalRegion, Tiling.RationalSlopes.HasRationalSlopes K →
    ∃ L : List RationalLine, ∀ z ∈ frontier K.support, ∃ l ∈ L, l.eval z = 0 := by
  classical
  intro K hK
  obtain ⟨E, hE, hfront⟩ := hK
  have hline : ∀ e : {e // e ∈ E}, ∃ l : RationalLine,
      ∀ z ∈ segment ℝ e.1.1 e.1.2, l.eval z = 0 := by
    intro e
    obtain ⟨hne, hrat⟩ := hE e.1 e.2
    obtain ⟨n, hn⟩ := rationalDirection_hasNormal
      (Submodule.span ℝ ({e.1.2 - e.1.1} : Set Plane))
      (finrank_span_singleton hne) hrat
    let l : RationalLine := ⟨n, normalEval n e.1.1⟩
    have hd : normalEval n (e.1.2 - e.1.1) = 0 := by
      have hm : e.1.2 - e.1.1 ∈ normalDirection n := by
        rw [hn]
        exact Submodule.subset_span (by simp)
      exact LinearMap.mem_ker.mp hm
    have ha : l.eval e.1.1 = 0 := by simp [l, RationalLine.eval]
    have hb : l.eval e.1.2 = 0 := by
      dsimp [l, RationalLine.eval, normalEval]
      dsimp [normalEval] at hd
      linear_combination hd
    refine ⟨l, ?_⟩
    rintro z ⟨a, b, _, _, hab, rfl⟩
    rw [lineEval_combo l e.1.1 e.1.2 a b hab, ha, hb]
    ring
  choose lines hlines using hline
  let L : List RationalLine := E.attach.toList.map lines
  refine ⟨L, ?_⟩
  intro z hz
  rw [hfront] at hz
  simp only [mem_iUnion] at hz
  obtain ⟨e, he, hz⟩ := hz
  refine ⟨lines ⟨e, he⟩, ?_, hlines ⟨e, he⟩ z hz⟩
  exact List.mem_map.mpr ⟨⟨e, he⟩, by simp, rfl⟩

theorem rationalSlopes_polyhedralNormalForm :
  ∀ K : PolygonalRegion, Tiling.RationalSlopes.HasRationalSlopes K →
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support := by
  intro K hK
  obtain ⟨L, hfront⟩ := rationalSlopes_frontierLineFamily K hK
  exact ⟨occupiedCodes K.support L, occupiedCodes_support K.support K.isPolygonal.isClosed
    K.isPolygonal.closure_interior L hfront⟩

private theorem affineIndependent_of_twiceSignedArea_ne_zero (a b c : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0) : AffineIndependent ℝ ![a, b, c] := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ ![a, b, c] 0]
  rw [← linearIndependent_equiv (finSuccAboveEquiv (0 : Fin 3))]
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hg' : g 0 • (b - a) + g 1 • (c - a) = 0 := by
    simpa [Fin.sum_univ_two, finSuccAboveEquiv] using hg
  have hgre := congrArg Complex.re hg'
  have hgim := congrArg Complex.im hg'
  simp only [Complex.add_re, Complex.smul_re, Complex.sub_re, Complex.zero_re,
    smul_eq_mul] at hgre
  simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, Complex.zero_im,
    smul_eq_mul] at hgim
  have hg0 : g 0 = 0 := by
    apply mul_right_cancel₀ harea
    rw [Tiling.twiceSignedArea]
    linear_combination (c.im - a.im) * hgre - (c.re - a.re) * hgim
  have hg1 : g 1 = 0 := by
    apply mul_right_cancel₀ harea
    rw [Tiling.twiceSignedArea]
    linear_combination -(b.im - a.im) * hgre + (b.re - a.re) * hgim
  fin_cases i
  · exact hg0
  · exact hg1

private noncomputable def triangleAffineBasis (a b c : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0) : AffineBasis (Fin 3) ℝ Plane where
  toFun := ![a, b, c]
  ind' := affineIndependent_of_twiceSignedArea_ne_zero a b c harea
  tot' := by
    apply (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
      (affineIndependent_of_twiceSignedArea_ne_zero a b c harea)).mpr
    simp [Complex.finrank_real_complex]

private theorem triangleAffineBasis_apply_zero (a b c : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0) :
    triangleAffineBasis a b c harea 0 = a := by
  rfl

private theorem triangleAffineBasis_apply_one (a b c : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0) :
    triangleAffineBasis a b c harea 1 = b := by
  rfl

private theorem triangleAffineBasis_apply_two (a b c : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0) :
    triangleAffineBasis a b c harea 2 = c := by
  rfl

/-- An affine equivalence matching two ordered nondegenerate triangle frames.
It transports the filled triangles and their corresponding edges exactly. -/
private theorem exists_affineEquiv_matching_triangles
    (a b c a' b' c' : Plane)
    (harea : Tiling.twiceSignedArea a b c ≠ 0)
    (harea' : Tiling.twiceSignedArea a' b' c' ≠ 0) :
    ∃ f : Plane ≃ᵃ[ℝ] Plane,
      f a = a' ∧ f b = b' ∧ f c = c' ∧
      (f : Plane → Plane) '' convexHull ℝ ({a, b, c} : Set Plane) =
        convexHull ℝ ({a', b', c'} : Set Plane) ∧
      (f : Plane → Plane) '' segment ℝ b c = segment ℝ b' c' := by
  let source := triangleAffineBasis a b c harea
  let target := triangleAffineBasis a' b' c' harea'
  let A : Plane ≃ₗ[ℝ] Plane :=
    (source.basisOf (0 : Fin 3)).equiv (target.basisOf (0 : Fin 3)) (Equiv.refl _)
  let f : Plane ≃ᵃ[ℝ] Plane := AffineEquiv.ofLinearEquiv A a a'
  have hB : A (b -ᵥ a) = b' -ᵥ a' := by
    have hbidx : (1 : Fin 3) ≠ 0 := by decide
    have hbs : source.basisOf 0 ⟨1, hbidx⟩ = b -ᵥ a := by
      rw [source.basisOf_apply]
      rfl
    have hbt : target.basisOf 0 ⟨1, hbidx⟩ = b' -ᵥ a' := by
      rw [target.basisOf_apply]
      rfl
    rw [← hbs, ← hbt]
    exact Module.Basis.equiv_apply (b := source.basisOf 0) (b' := target.basisOf 0)
      (e := Equiv.refl _) (i := ⟨1, hbidx⟩)
  have hC : A (c -ᵥ a) = c' -ᵥ a' := by
    have hcidx : (2 : Fin 3) ≠ 0 := by decide
    have hcs : source.basisOf 0 ⟨2, hcidx⟩ = c -ᵥ a := by
      rw [source.basisOf_apply]
      rfl
    have hct : target.basisOf 0 ⟨2, hcidx⟩ = c' -ᵥ a' := by
      rw [target.basisOf_apply]
      rfl
    rw [← hcs, ← hct]
    exact Module.Basis.equiv_apply (b := source.basisOf 0) (b' := target.basisOf 0)
      (e := Equiv.refl _) (i := ⟨2, hcidx⟩)
  have hfa : f a = a' := by simp [f, AffineEquiv.ofLinearEquiv_apply]
  have hfb : f b = b' := by
    change A (b -ᵥ a) +ᵥ a' = b'
    rw [hB]
    simp
  have hfc : f c = c' := by
    change A (c -ᵥ a) +ᵥ a' = c'
    rw [hC]
    simp
  refine ⟨f, hfa, hfb, hfc, ?_, ?_⟩
  · change f.toAffineMap '' convexHull ℝ ({a, b, c} : Set Plane) = _
    rw [AffineMap.image_convexHull]
    have himage : f.toAffineMap '' ({a, b, c} : Set Plane) =
        ({a', b', c'} : Set Plane) := by
      change (f : Plane → Plane) '' ({a, b, c} : Set Plane) = _
      ext z
      simp only [mem_image, mem_insert_iff, mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl | rfl
        · exact Or.inl hfa
        · exact Or.inr (Or.inl hfb)
        · exact Or.inr (Or.inr hfc)
      · intro hz
        rcases hz with rfl | rfl | rfl
        · exact ⟨a, Or.inl rfl, hfa⟩
        · exact ⟨b, Or.inr (Or.inl rfl), hfb⟩
        · exact ⟨c, Or.inr (Or.inr rfl), hfc⟩
    rw [himage]
  · change f.toAffineMap '' segment ℝ b c = segment ℝ b' c'
    rw [← convexHull_pair, ← convexHull_pair, AffineMap.image_convexHull]
    have hpair : f.toAffineMap '' ({b, c} : Set Plane) = ({b', c'} : Set Plane) := by
      change (f : Plane → Plane) '' ({b, c} : Set Plane) = _
      simp only [Set.image_pair, hfb, hfc]
    rw [hpair]


private def affineEquiv_homeomorph (f : Plane ≃ᵃ[ℝ] Plane) : Plane ≃ₜ Plane where
  toEquiv := f.toEquiv
  continuous_toFun := AffineMap.continuous_linear_iff.mp
    f.toAffineMap.linear.continuous_of_finiteDimensional
  continuous_invFun := AffineMap.continuous_linear_iff.mp
    f.symm.toAffineMap.linear.continuous_of_finiteDimensional

private def affineEquiv_restrict_image (f : Plane ≃ᵃ[ℝ] Plane) (s t : Set Plane)
    (himage : (f : Plane → Plane) '' s = t) : s ≃ₜ t :=
  ((affineEquiv_homeomorph f).image s).trans (Homeomorph.setCongr himage)

private theorem affineEquiv_restrict_image_apply (f : Plane ≃ᵃ[ℝ] Plane) (s t : Set Plane)
    (himage : (f : Plane → Plane) '' s = t) (x : s) :
    ((affineEquiv_restrict_image f s t himage) x : Plane) = f x := by
  rfl

/-- A finite closed cover can be glued from compatible homeomorphisms of its pieces.
The agreement hypotheses are stated on the actual source and target overlaps. -/
private def finiteClosedCover_homeomorph
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (T : Set Y)
    (C : ι → Set S) (D : ι → Set T)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCcover : ∀ x : S, ∃ i, x ∈ C i)
    (hDcover : ∀ y : T, ∃ i, y ∈ D i)
    (piece : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val)
    (hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val) :
    S ≃ₜ T := by
  let sourceIndex (x : S) : ι := Classical.choose (hCcover x)
  have sourceIndex_mem (x : S) : x ∈ C (sourceIndex x) :=
    (Classical.choose_spec (hCcover x))
  let targetIndex (y : T) : ι := Classical.choose (hDcover y)
  have targetIndex_mem (y : T) : y ∈ D (targetIndex y) :=
    (Classical.choose_spec (hDcover y))
  let glued (x : S) : T :=
    (piece (sourceIndex x) ⟨x, sourceIndex_mem x⟩).val
  let gluedInv (y : T) : S :=
    ((piece (targetIndex y)).symm ⟨y, targetIndex_mem y⟩).val
  have glued_on_piece (i : ι) (x : C i) :
      glued x.val = (piece i x).val := by
    change (piece (sourceIndex x.val) ⟨x.val, sourceIndex_mem x.val⟩).val =
      (piece i x).val
    exact hforward (sourceIndex x.val) i x.val (sourceIndex_mem x.val) x.property
  have gluedInv_on_piece (i : ι) (y : D i) :
      gluedInv y.val = ((piece i).symm y).val := by
    change ((piece (targetIndex y.val)).symm
      ⟨y.val, targetIndex_mem y.val⟩).val = ((piece i).symm y).val
    exact hinverse (targetIndex y.val) i y.val (targetIndex_mem y.val) y.property
  have hglued_piece (i : ι) : ContinuousOn glued (C i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (C i).domRestrict glued = fun x : C i => (piece i x).val := by
      funext x
      exact glued_on_piece i x
    rw [heq]
    exact continuous_subtype_val.comp (piece i).continuous
  have hgluedInv_piece (i : ι) : ContinuousOn gluedInv (D i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (D i).domRestrict gluedInv = fun y : D i => ((piece i).symm y).val := by
      funext y
      exact gluedInv_on_piece i y
    rw [heq]
    exact continuous_subtype_val.comp (piece i).symm.continuous
  have hCunion : (⋃ i, C i) = (Set.univ : Set S) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hCcover x
  have hDunion : (⋃ i, D i) = (Set.univ : Set T) := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hDcover y
  have hglued : Continuous glued := by
    apply (locallyFinite_of_finite C).continuous hCunion hCclosed hglued_piece
  have hgluedInv : Continuous gluedInv := by
    apply (locallyFinite_of_finite D).continuous hDunion hDclosed hgluedInv_piece
  have hleft (x : S) : gluedInv (glued x) = x := by
    let i := sourceIndex x
    let j := targetIndex (glued x)
    have hxi : x ∈ C i := by dsimp [i]; exact sourceIndex_mem x
    have hyi : glued x ∈ D i := by
      dsimp [glued]
      exact (piece i ⟨x, hxi⟩).property
    have hyj : glued x ∈ D j := by dsimp [j]; exact targetIndex_mem (glued x)
    have hval : gluedInv (glued x) = ((piece i).symm ⟨glued x, hyi⟩).val := by
      dsimp [gluedInv, j]
      exact hinverse (targetIndex (glued x)) i (glued x)
        (targetIndex_mem (glued x)) hyi
    have hfirst : ((piece i).symm ⟨glued x, hyi⟩).val = x := by
      have heq : (piece i) ⟨x, hxi⟩ = ⟨glued x, hyi⟩ := by
        apply Subtype.ext
        exact (glued_on_piece i ⟨x, hxi⟩).symm
      have hinv : (piece i).symm ⟨glued x, hyi⟩ = ⟨x, hxi⟩ := by
        rw [← heq]
        simp
      exact congrArg Subtype.val hinv
    rw [hval, hfirst]
  have hright (y : T) : glued (gluedInv y) = y := by
    let i := targetIndex y
    let x := (piece i).symm ⟨y, targetIndex_mem y⟩
    have hyi : y ∈ D i := by dsimp [i]; exact targetIndex_mem y
    have hxi : x.val ∈ C i := x.property
    have hmap : (piece i x).val = y := by
      exact congrArg Subtype.val ((piece i).apply_symm_apply ⟨y, hyi⟩)
    have hinvval : gluedInv y = x.val := by
      dsimp [gluedInv, i, x]
    rw [hinvval, glued_on_piece i x]
    exact hmap
  let e : S ≃ T :=
    { toFun := glued
      invFun := gluedInv
      left_inv := hleft
      right_inv := hright }
  exact Homeomorph.mk e hglued hgluedInv



/-- Independent normal-form choices give the same image once their combined finite tests hold. -/
private theorem sign_nonpos_iff (a : ℝ) : Real.sign a ≤ 0 ↔ a ≤ 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · simp [Real.sign_of_neg ha, ha.le]
  · simp [ha]
  · simp [Real.sign_of_pos ha, not_le.mpr ha]

private theorem polyhedralSupport_transport_mem
    (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (H : Plane ≃ₜ Plane)
    (hH : ∀ cell ∈ P, ∀ l ∈ cell, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z))
    (z : Plane) :
    H z ∈ deformedPolyhedralSupport P φ ↔ z ∈ polyhedralSupport P := by
  have hle (cell : List RationalLine) (hc : cell ∈ P) (l : RationalLine)
      (hl : l ∈ cell) : (deformLine φ l).eval (H z) ≤ 0 ↔ l.eval z ≤ 0 := by
    rw [← sign_nonpos_iff, hH cell hc l hl z, sign_nonpos_iff]
  constructor
  · rintro ⟨cell', hcell', hcell⟩
    obtain ⟨cell, hc, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨cell, hc, ?_⟩
    intro l hl
    exact (hle cell hc l hl).mp
      (hcell (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩))
  · rintro ⟨cell, hc, hcell⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hc, rfl⟩, ?_⟩
    intro l' hl'
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    exact (hle cell hc l hl).mpr (hcell l hl)


private theorem normalEval_add (n : RationalNormal) (z w : Plane) :
    normalEval n (z + w) = normalEval n z + normalEval n w := by
  simp [normalEval, Complex.add_re, Complex.add_im]
  ring

private theorem normalEval_sub (n : RationalNormal) (z w : Plane) :
    normalEval n (z - w) = normalEval n z - normalEval n w := by
  simp [normalEval, Complex.sub_re, Complex.sub_im]
  ring

private theorem source_eval_anchor (l : RationalLine) (v x : Plane) :
    l.eval x = l.eval v + normalEval l.normal (x - v) := by
  simp [RationalLine.eval, normalEval_sub]

private theorem target_eval_anchor (l : RationalLine) (φ : ℝ →ₗ[ℚ] ℚ)
    (v x : Plane) :
    (deformLine φ l).eval (deformPoint φ v + (x - v)) =
      (deformLine φ l).eval (deformPoint φ v) + normalEval l.normal (x - v) := by
  simp [RationalLine.eval, deformLine, normalEval_add]
  ring

private theorem line_nonpos_iff_eventually (l : RationalLine) (φ : ℝ →ₗ[ℚ] ℚ)
    (v : Plane)
    (hsign : Real.sign ((deformLine φ l).eval (deformPoint φ v)) =
      Real.sign (l.eval v)) :
    ∀ᶠ x in 𝓝 v,
      (l.eval x ≤ 0 ↔
        (deformLine φ l).eval (deformPoint φ v + (x - v)) ≤ 0) := by
  let c := l.eval v
  let d := (deformLine φ l).eval (deformPoint φ v)
  have hsgn : Real.sign d = Real.sign c := by simpa [c, d] using hsign
  by_cases hc : c = 0
  · have hd : d = 0 := by
      have hs : Real.sign d = 0 := by simpa [hc] using hsgn
      exact Real.sign_eq_zero_iff.mp hs
    have hpoint : ∀ x : Plane,
        l.eval x = (deformLine φ l).eval (deformPoint φ v + (x - v)) := by
      intro x
      rw [source_eval_anchor l v x, target_eval_anchor l φ v x]
      dsimp [c] at hc
      dsimp [d] at hd
      simp [hc, hd]
    filter_upwards [] with x
    simp only [hpoint x]
  · rcases lt_or_gt_of_ne hc with hcneg | hcpos
    · have hdneg : d < 0 := by
        by_contra h
        have hdpos : 0 ≤ d := le_of_not_gt h
        have hdc : Real.sign d = -1 := hsgn.trans (Real.sign_of_neg hcneg)
        rcases eq_or_lt_of_le hdpos with hdzero | hdpos
        · have hdzero : d = 0 := hdzero.symm
          rw [hdzero, Real.sign_zero] at hdc
          norm_num at hdc
        · rw [Real.sign_of_pos hdpos] at hdc
          norm_num at hdc
      have hs : ∀ᶠ x in 𝓝 v, l.eval x < 0 := by
        have hcont : Continuous fun x : Plane => l.eval x := by
          fun_prop [RationalLine.eval, normalEval]
        have hmem : l.eval v ∈ Set.Iio (0 : ℝ) := hcneg
        exact hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hmem)
      have ht : ∀ᶠ x in 𝓝 v,
          (deformLine φ l).eval (deformPoint φ v + (x - v)) < 0 := by
        have hcont : Continuous fun x : Plane =>
            (deformLine φ l).eval (deformPoint φ v + (x - v)) := by
          fun_prop [RationalLine.eval, deformLine, normalEval]
        have hmem :
            (fun x : Plane => (deformLine φ l).eval
              (deformPoint φ v + (x - v))) v ∈ Set.Iio (0 : ℝ) := by
          simpa using hdneg
        exact hcont.continuousAt.eventually (isOpen_Iio.mem_nhds hmem)
      filter_upwards [hs, ht] with x hx htx
      exact ⟨fun _ => htx.le, fun _ => hx.le⟩
    · have hdpos : 0 < d := by
        by_contra h
        have hdneg : d ≤ 0 := le_of_not_gt h
        have hdc : Real.sign d = 1 := hsgn.trans (Real.sign_of_pos hcpos)
        rcases eq_or_lt_of_le hdneg with hdzero | hdneg
        · have hdzero : d = 0 := hdzero
          rw [hdzero, Real.sign_zero] at hdc
          norm_num at hdc
        · rw [Real.sign_of_neg hdneg] at hdc
          norm_num at hdc
      have hs : ∀ᶠ x in 𝓝 v, 0 < l.eval x := by
        have hcont : Continuous fun x : Plane => l.eval x := by
          fun_prop [RationalLine.eval, normalEval]
        have hmem : l.eval v ∈ Set.Ioi (0 : ℝ) := hcpos
        exact hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hmem)
      have ht : ∀ᶠ x in 𝓝 v,
          0 < (deformLine φ l).eval (deformPoint φ v + (x - v)) := by
        have hcont : Continuous fun x : Plane =>
            (deformLine φ l).eval (deformPoint φ v + (x - v)) := by
          fun_prop [RationalLine.eval, deformLine, normalEval]
        have hmem :
            (fun x : Plane => (deformLine φ l).eval
              (deformPoint φ v + (x - v))) v ∈ Set.Ioi (0 : ℝ) := by
          simpa using hdpos
        exact hcont.continuousAt.eventually (isOpen_Ioi.mem_nhds hmem)
      filter_upwards [hs, ht] with x hx htx
      exact ⟨fun h => (not_le_of_gt hx h).elim,
        fun h => (not_le_of_gt htx h).elim⟩

private theorem lineIffs_eventually (L : List RationalLine) (φ : ℝ →ₗ[ℚ] ℚ)
    (v : Plane)
    (hsign : ∀ l ∈ L,
      Real.sign ((deformLine φ l).eval (deformPoint φ v)) =
        Real.sign (l.eval v)) :
    ∀ᶠ x in 𝓝 v, ∀ l ∈ L,
      (l.eval x ≤ 0 ↔
        (deformLine φ l).eval (deformPoint φ v + (x - v)) ≤ 0) := by
  induction L with
  | nil =>
      filter_upwards [] with x l hl
      simp at hl
  | cons l L ih =>
      have hl := line_nonpos_iff_eventually l φ v (hsign l (by simp))
      have htail := ih (by
        intro k hk
        exact hsign k (by simp [hk]))
      filter_upwards [hl, htail] with x hx hxs k hk
      rcases List.mem_cons.mp hk with rfl | hk
      · exact hx
      · exact hxs k hk

private theorem deformedSupport_iff_cells (P : PolyhedralCode)
    (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane) :
    z ∈ deformedPolyhedralSupport P φ ↔
      ∃ cell ∈ P, ∀ l ∈ cell,
        (deformLine φ l).eval z ≤ 0 := by
  change z ∈ polyhedralSupport (P.map (fun cell => cell.map (deformLine φ))) ↔ _
  change (∃ cell' ∈ P.map (fun cell => cell.map (deformLine φ)),
      ∀ l ∈ cell', l.eval z ≤ 0) ↔ _
  constructor
  · rintro ⟨cell', hcell', hlines⟩
    obtain ⟨cell, hcell, rfl⟩ := List.mem_map.mp hcell'
    refine ⟨cell, hcell, ?_⟩
    intro l hl
    exact hlines (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩)
  · rintro ⟨cell, hcell, hlines⟩
    refine ⟨cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hcell, rfl⟩, ?_⟩
    intro l hl
    obtain ⟨k, hk, hkl⟩ := List.mem_map.mp hl
    subst l
    exact hlines k hk

private theorem polyhedralSupport_alignedGerm
    (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (v : Plane)
    (hsign : ∀ cell ∈ P, ∀ l ∈ cell,
      Real.sign ((deformLine φ l).eval (deformPoint φ v)) =
        Real.sign (l.eval v)) :
    Tiling.Polygonal.SameGermAt (polyhedralSupport P) v
      (deformedPolyhedralSupport P φ) (deformPoint φ v) := by
  let v' := deformPoint φ v
  have hsign_flat : ∀ l ∈ P.flatten,
      Real.sign ((deformLine φ l).eval v') = Real.sign (l.eval v) := by
    intro l hl
    obtain ⟨cell, hcell, hmem⟩ := List.mem_flatten.mp hl
    exact hsign cell hcell l hmem
  have hlocal := lineIffs_eventually P.flatten φ v hsign_flat
  have hsupport : ∀ᶠ x in 𝓝 v,
      (x ∈ polyhedralSupport P ↔
        v' + (x - v) ∈ deformedPolyhedralSupport P φ) := by
    filter_upwards [hlocal] with x hx
    constructor
    · rintro ⟨cell, hcell, hlines⟩
      apply (deformedSupport_iff_cells P φ (v' + (x - v))).2
      refine ⟨cell, hcell, ?_⟩
      intro l hl
      have hline := hx l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)
      exact (hline).mp (by simpa [v'] using hlines l hl)
    · intro htarget
      obtain ⟨cell, hcell, hlines⟩ :=
        (deformedSupport_iff_cells P φ (v' + (x - v))).1 htarget
      refine ⟨cell, hcell, ?_⟩
      intro l hl
      have hline := hx l (List.mem_flatten.mpr ⟨cell, hcell, hl⟩)
      exact (hline).mpr (by simpa [v'] using hlines l hl)
  unfold Tiling.Polygonal.SameGermAt
  filter_upwards [hsupport] with x hx
  apply propext
  have hset :
      x ∈ (v - deformPoint φ v) +ᵥ deformedPolyhedralSupport P φ ↔
        v' + (x - v) ∈ deformedPolyhedralSupport P φ := by
    simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    have halign : -(v - deformPoint φ v) + x = v' + (x - v) := by
      simp [v']
      abel
    rw [halign]
  exact hx.trans hset.symm

private theorem polyhedralSupport_alignedInteriorGerm
    (P : PolyhedralCode) (φ : ℝ →ₗ[ℚ] ℚ) (v : Plane)
    (hsign : ∀ cell ∈ P, ∀ l ∈ cell,
      Real.sign ((deformLine φ l).eval (deformPoint φ v)) =
        Real.sign (l.eval v)) :
    Tiling.Polygonal.SameGermAt (interior (polyhedralSupport P)) v
      (interior (deformedPolyhedralSupport P φ)) (deformPoint φ v) := by
  have hg := polyhedralSupport_alignedGerm P φ v hsign
  unfold Tiling.Polygonal.SameGermAt at hg ⊢
  rw [← interior_vadd]
  filter_upwards [hg.eventuallyEq_nhds] with x hx
  exact propext hx.mem_interior_iff

private theorem deformLine_eval_commutes (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) (z : Plane) :
    (deformLine φ l).eval (deformPoint φ z) = (φ (l.eval z) : ℝ) := by
  have hx := φ.map_smul l.normal.x z.re
  have hy := φ.map_smul l.normal.y z.im
  simp only [Rat.smul_def] at hx hy
  dsimp [RationalLine.eval, deformLine, normalEval, deformPoint]
  rw [map_sub, map_add, hx, hy]
  push_cast
  rfl

private theorem finite_nonzero_gap (E : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ E, x ≠ 0 → ε ≤ |x| := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x E hx ih =>
    obtain ⟨ε, hε, hgap⟩ := ih
    by_cases hx0 : x = 0
    · refine ⟨ε, hε, ?_⟩
      intro y hy hy0
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact False.elim (hy0 hx0)
      · exact hgap y hy hy0
    · refine ⟨min ε |x|, lt_min hε (abs_pos.mpr hx0), ?_⟩
      intro y hy hy0
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hgap y hy hy0)

private theorem unify_finiteApproximationTests {ι : Type*} [Fintype ι]
    (tests : ι → Finset ℝ) (threshold : ι → ℝ) (hpos : ∀ i, 0 < threshold i) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ i, IsFiniteApproximation (tests i) (threshold i) φ := by
  classical
  let E := Finset.univ.image threshold
  obtain ⟨ε, hε, hgap⟩ := finite_nonzero_gap E
  refine ⟨Finset.univ.biUnion tests, ε, hε, ?_⟩
  intro φ hφ i
  refine ⟨hφ.1, ?_⟩
  intro x hx
  have hi : threshold i ∈ E := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hle : ε ≤ threshold i := by
    simpa [abs_of_pos (hpos i)] using hgap (threshold i) hi (ne_of_gt (hpos i))
  exact (hφ.2 x (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩)).trans_le hle

private theorem finite_scalar_signTests (E : Finset ℝ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation E ε φ →
      ∀ x ∈ E, Real.sign (φ x : ℝ) = Real.sign x := by
  obtain ⟨ε, hε, hgap⟩ := finite_nonzero_gap E
  refine ⟨ε, hε, ?_⟩
  intro φ hφ x hx
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · have hsmall := abs_lt.mp ((hφ.2 x hx).trans_le (hgap x hx (ne_of_lt hneg)))
    have hp : (φ x : ℝ) < 0 := by rw [abs_of_neg hneg] at hsmall; linarith [hsmall.2]
    rw [Real.sign_of_neg hneg, Real.sign_of_neg hp]
  · simp [hzero]
  · have hsmall := abs_lt.mp ((hφ.2 x hx).trans_le (hgap x hx (ne_of_gt hpos)))
    have hp : 0 < (φ x : ℝ) := by rw [abs_of_pos hpos] at hsmall; linarith [hsmall.1]
    rw [Real.sign_of_pos hpos, Real.sign_of_pos hp]

private theorem sign_eq_neg_one_iff (a : ℝ) : Real.sign a = -1 ↔ a < 0 := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · simp [Real.sign_of_neg ha, ha]
  · simp [ha]
  · norm_num [Real.sign_of_pos ha, not_lt.mpr ha.le]

private theorem finiteCell_strictPointTests (cell : List RationalLine) (c : Plane)
    (hc : c ∈ openCell cell) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        deformPoint φ c ∈ openCell (cell.map (deformLine φ)) := by
  classical
  let E := cell.toFinset.image (fun l => l.eval c)
  obtain ⟨ε, hε, hsign⟩ := finite_scalar_signTests E
  refine ⟨E, ε, hε, ?_⟩
  intro φ hφ m hm
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
  apply (sign_eq_neg_one_iff _).mp
  rw [deformLine_eval_commutes, hsign φ hφ _
    (Finset.mem_image.mpr ⟨l, List.mem_toFinset.mpr hl, rfl⟩)]
  exact Real.sign_of_neg (hc l hl)

private theorem finiteCell_extremePoints_transport (cell : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        (closedCell (cell.map (deformLine φ))).extremePoints ℝ =
          deformPoint φ '' (closedCell cell).extremePoints ℝ := by
  classical
  let A := cell.toFinset
  let I : Finset (RationalLine × RationalLine) := (A ×ˢ A).filter fun p =>
    p.1.normal.x * p.2.normal.y - p.1.normal.y * p.2.normal.x ≠ 0
  let point (i : {p // p ∈ I}) : Plane := Classical.choose
    (rationalLine_pairIntersection i.1.1 i.1.2 (Finset.mem_filter.mp i.2).2)
  have hpoint (i : {p // p ∈ I}) := Classical.choose_spec
    (rationalLine_pairIntersection i.1.1 i.1.2 (Finset.mem_filter.mp i.2).2)
  let E : Finset ℝ := Finset.univ.biUnion fun i : {p // p ∈ I} => A.image (fun l => l.eval (point i))
  obtain ⟨ε, hε, hsign⟩ := finite_scalar_signTests E
  refine ⟨E, ε, hε, ?_⟩
  intro φ hφ
  have hfeasible (i : {p // p ∈ I}) :
      deformPoint φ (point i) ∈ closedCell (cell.map (deformLine φ)) ↔
        point i ∈ closedCell cell := by
    have hle (l : RationalLine) (hl : l ∈ cell) :
        (deformLine φ l).eval (deformPoint φ (point i)) ≤ 0 ↔ l.eval (point i) ≤ 0 := by
      rw [← sign_nonpos_iff, deformLine_eval_commutes,
        hsign φ hφ _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
          Finset.mem_image.mpr ⟨l, List.mem_toFinset.mpr hl, rfl⟩⟩), sign_nonpos_iff]
    constructor
    · intro hx l hl
      exact (hle l hl).mp (hx (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩))
    · intro hx m hm
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
      exact (hle l hl).mpr (hx l hl)
  have hindex (l m : RationalLine) (hl : l ∈ cell) (hm : m ∈ cell)
      (hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0) : (l,m) ∈ I :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨List.mem_toFinset.mpr hl, List.mem_toFinset.mpr hm⟩, hdet⟩
  ext z
  constructor
  · intro hz
    obtain ⟨l', hl', m', hm', hdet, hlz, hmz⟩ :=
      closedCell_extreme_has_active_nonparallel (cell.map (deformLine φ)) z hz
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hl'
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hm'
    have hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 := hdet
    let i : {p // p ∈ I} := ⟨(l,m), hindex l m hl hm hdet⟩
    have hp : l.eval (point i) = 0 ∧ m.eval (point i) = 0 := ⟨(hpoint i).1, (hpoint i).2.1⟩
    have hmap := (hpoint i).2.2.2 φ
    have hzmap : z = deformPoint φ (point i) := common_zero_unique
      (deformLine φ l) (deformLine φ m) hdet z (deformPoint φ (point i))
      hlz hmap.1 hmz hmap.2
    have hpCell : point i ∈ closedCell cell := (hfeasible i).mp (hzmap ▸ hz.1)
    refine ⟨point i, closedCell_pairPoint_extreme cell l m hl hm hdet
      (point i) hpCell hp.1 hp.2, hzmap.symm⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨l, hl, m, hm, hdet, hlx, hmx⟩ := closedCell_extreme_has_active_nonparallel cell x hx
    let i : {p // p ∈ I} := ⟨(l,m), hindex l m hl hm hdet⟩
    have hxp : x = point i := (hpoint i).2.2.1 x hlx hmx
    have htarget : deformPoint φ x ∈ closedCell (cell.map (deformLine φ)) := by
      rw [hxp]
      apply (hfeasible i).mpr
      exact hxp ▸ hx.1
    apply closedCell_pairPoint_extreme (cell.map (deformLine φ)) (deformLine φ l) (deformLine φ m)
      (List.mem_map.mpr ⟨l, hl, rfl⟩) (List.mem_map.mpr ⟨m, hm, rfl⟩) hdet
      (deformPoint φ x) htarget
    · rw [deformLine_eval_commutes, hlx, map_zero, Rat.cast_zero]
    · rw [deformLine_eval_commutes, hmx, map_zero, Rat.cast_zero]

private theorem finiteCell_vertexSignTests (cell : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ v ∈ (closedCell cell).extremePoints ℝ, ∀ l ∈ cell,
          Real.sign ((deformLine φ l).eval (deformPoint φ v)) = Real.sign (l.eval v) := by
  classical
  let V := (closedCell_extremePoints_finite cell).toFinset
  let E := cell.toFinset.biUnion (fun l => V.image l.eval)
  obtain ⟨ε, hε, hsign⟩ := finite_scalar_signTests E
  refine ⟨E, ε, hε, ?_⟩
  intro φ hφ v hv l hl
  rw [deformLine_eval_commutes]
  apply hsign φ hφ
  exact Finset.mem_biUnion.mpr ⟨l, List.mem_toFinset.mpr hl,
    Finset.mem_image.mpr ⟨v, (closedCell_extremePoints_finite cell).mem_toFinset.mpr hv, rfl⟩⟩

private theorem finiteCell_extremePoints_injective (cell : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        Set.InjOn (deformPoint φ) ((closedCell cell).extremePoints ℝ) := by
  obtain ⟨F, ε, hε, hsign⟩ := finiteCell_vertexSignTests cell
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ a ha b hb hab
  obtain ⟨l, hl, m, hm, hdet, hal, ham⟩ :=
    closedCell_extreme_has_active_nonparallel cell a ha
  have hzero (k : RationalLine) (hk : k ∈ cell) (hka : k.eval a = 0) :
      k.eval b = 0 := by
    have htarget : (deformLine φ k).eval (deformPoint φ b) = 0 := by
      rw [← hab, deformLine_eval_commutes, hka, map_zero, Rat.cast_zero]
    have hs := hsign φ hφ b hb k hk
    have hs0 : Real.sign (k.eval b) = 0 := by
      simpa only [htarget, Real.sign_zero] using hs.symm
    exact Real.sign_eq_zero_iff.mp hs0
  exact common_zero_unique l m hdet a b hal (hzero l hl hal) ham (hzero m hm ham)

private theorem closedCell_map_eq_shiftedCell (cell : List RationalLine) (φ : ℝ →ₗ[ℚ] ℚ) :
    closedCell (cell.map (deformLine φ)) = shiftedCell cell (fun l => (φ l.offset : ℝ)) := by
  ext z
  simp [closedCell, shiftedCell, RationalLine.eval, deformLine]

private theorem finiteDecoration_uniformImageBound (W : Finset Plane) :
    ∃ F : Finset ℝ, ∃ B : ℝ, 0 < B ∧ ∀ φ : ℝ →ₗ[ℚ] ℚ,
      IsFiniteApproximation F 1 φ → ∀ w ∈ W, ‖deformPoint φ w‖ ≤ B := by
  let F := W.image Complex.re ∪ W.image Complex.im
  let B := 2 * (∑ w ∈ W, ‖w‖) + 3
  have hsum0 : 0 ≤ ∑ w ∈ W, ‖w‖ := Finset.sum_nonneg (fun w _ => norm_nonneg w)
  refine ⟨F, B, by dsimp [B]; linarith, ?_⟩
  intro φ hφ w hw
  have hre := hφ.2 w.re (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨w, hw, rfl⟩)))
  have him := hφ.2 w.im (Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨w, hw, rfl⟩)))
  have hreBound : |(φ w.re : ℝ)| ≤ |w.re| + 1 := by
    calc
      |(φ w.re : ℝ)| = |((φ w.re : ℝ) - w.re) + w.re| := by congr 1; ring
      _ ≤ |(φ w.re : ℝ) - w.re| + |w.re| := abs_add_le _ _
      _ ≤ |w.re| + 1 := by linarith
  have himBound : |(φ w.im : ℝ)| ≤ |w.im| + 1 := by
    calc
      |(φ w.im : ℝ)| = |((φ w.im : ℝ) - w.im) + w.im| := by congr 1; ring
      _ ≤ |(φ w.im : ℝ) - w.im| + |w.im| := abs_add_le _ _
      _ ≤ |w.im| + 1 := by linarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im (deformPoint φ w)
  change ‖deformPoint φ w‖ ≤ |(φ w.re : ℝ)| + |(φ w.im : ℝ)| at hnorm
  have hsum : ‖w‖ ≤ ∑ w ∈ W, ‖w‖ :=
    Finset.single_le_sum (fun u _ => norm_nonneg u) hw
  dsimp only [B]
  linarith [Complex.abs_re_le_norm w, Complex.abs_im_le_norm w]

private theorem finiteCell_convexHull_transport (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (closedCell cell).Nonempty) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        closedCell (cell.map (deformLine φ)) =
          convexHull ℝ (deformPoint φ '' (closedCell cell).extremePoints ℝ) := by
  obtain ⟨F, ε, hε, hext⟩ := finiteCell_extremePoints_transport cell
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  have htargetCompact : IsCompact (closedCell (cell.map (deformLine φ))) := by
    rw [closedCell_map_eq_shiftedCell]
    exact shiftedCell_isCompact_of_compact_same_normals cell hcompact hne _
  rw [closedCell_eq_convexHull_extremePoints _ htargetCompact
    (closedCell_extremePoints_finite _), hext φ hφ]

private theorem midpoint_eval (l : RationalLine) (x y : Plane) :
    l.eval ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) = (l.eval x + l.eval y) / 2 := by
  have h := lineEval_affine l x y (1 / 2) (1 / 2)
  norm_num at h ⊢
  linarith

/-- Repeated midpointing combines finitely many strict witnesses while staying in the
same weak feasible set. -/
private theorem strict_on_list_of_neg_witnesses
    (constraints cell : List RationalLine) (base : Plane)
    (hbase : base ∈ closedCell cell)
    (done : List RationalLine)
    (hdoneMem : ∀ l ∈ done, l ∈ cell)
    (hdone : ∀ l ∈ done, l.eval base < 0)
    (hconstraints : ∀ l ∈ constraints, l ∈ cell)
    (hneg : ∀ l ∈ constraints, ∃ z ∈ closedCell cell, l.eval z < 0) :
    ∃ c ∈ closedCell cell, ∀ l ∈ done ++ constraints, l.eval c < 0 := by
  induction constraints generalizing done base with
  | nil =>
        exact ⟨base, hbase, by simpa using hdone⟩
  | cons l rest ih =>
      obtain ⟨z, hz, hzl⟩ := hneg l (by simp)
      let mid : Plane := (1 / 2 : ℝ) • base + (1 / 2 : ℝ) • z
      have hmidweak : mid ∈ closedCell cell := by
        intro k hk
        have hb := hbase k hk
        have hz' := hz k hk
        rw [midpoint_eval]
        linarith
      have hmiddone : ∀ k ∈ done ++ [l], k.eval mid < 0 := by
        intro k hk
        rcases List.mem_append.mp hk with hkdone | hkeq
        · have hb := hdone k hkdone
          have hz' := hz k (hdoneMem k hkdone)
          rw [midpoint_eval]
          linarith
        · have hkl : k = l := by simpa using hkeq
          subst k
          have hb := hbase l (hconstraints l (by simp))
          rw [midpoint_eval]
          linarith
      have hdoneMem' : ∀ k ∈ done ++ [l], k ∈ cell := by
        intro k hk
        rcases List.mem_append.mp hk with hkdone | hkeq
        · exact hdoneMem k hkdone
        · have hkl : k = l := by simpa using hkeq
          subst k
          exact hconstraints l (by simp)
      have hnegRest : ∀ k ∈ rest, ∃ w ∈ closedCell cell, k.eval w < 0 := by
        intro k hk
        exact hneg k (by simp [hk])
      have hconstraintsRest : ∀ k ∈ rest, k ∈ cell := by
        intro k hk
        exact hconstraints k (by simp [hk])
      obtain ⟨c, hc, hstrict⟩ := ih mid hmidweak (done ++ [l]) hdoneMem' hmiddone
        hconstraintsRest hnegRest
      refine ⟨c, hc, ?_⟩
      simpa [List.append_assoc] using hstrict

/-- A nonempty weak cell with no strict point has a defining line active everywhere. -/
private theorem closedCell_emptyOpen_has_universally_active_line
    (cell : List RationalLine) (hne : (closedCell cell).Nonempty)
    (hempty : openCell cell = ∅) :
    ∃ l ∈ cell, ∀ z ∈ closedCell cell, l.eval z = 0 := by
  by_contra h
  push Not at h
  obtain ⟨base, hbase⟩ := hne
  have hneg : ∀ l ∈ cell, ∃ z ∈ closedCell cell, l.eval z < 0 := by
    intro l hl
    obtain ⟨z, hz, hneval⟩ := h l hl
    have hle := hz l hl
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact ⟨z, hz, hlt⟩
    · exact (hneval heq).elim
  obtain ⟨c, hc, hstrict⟩ :=
    strict_on_list_of_neg_witnesses cell cell base hbase [] (by simp) (by simp) (by simp) hneg
  have hcopen : c ∈ openCell cell := hstrict
  rw [hempty] at hcopen
  simp at hcopen


private theorem closedCell_append (C D : List RationalLine) :
    closedCell (C ++ D) = closedCell C ∩ closedCell D := by
  ext z
  constructor
  · intro hz
    exact ⟨fun l hl => hz l (List.mem_append.mpr (Or.inl hl)),
      fun l hl => hz l (List.mem_append.mpr (Or.inr hl))⟩
  · rintro ⟨hC, hD⟩ l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hC l hl
    · exact hD l hl

private def squareLines (R : ℚ) : List RationalLine :=
  [⟨⟨1, 0, by norm_num⟩, (R : ℝ)⟩,
   ⟨⟨-1, 0, by norm_num⟩, (R : ℝ)⟩,
   ⟨⟨0, 1, by norm_num⟩, (R : ℝ)⟩,
   ⟨⟨0, -1, by norm_num⟩, (R : ℝ)⟩]

private theorem normalized_map_rat (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) (q : ℚ) :
    φ (q : ℝ) = q := by
  have h := φ.map_smul q (1 : ℝ)
  rw [hφ] at h
  simpa [Rat.smul_def] using h

private theorem deform_squareLines (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) (R : ℚ) :
    (squareLines R).map (deformLine φ) = squareLines R := by
  simp [squareLines, deformLine, normalized_map_rat φ hφ]

private theorem mem_closedCell_squareLines (R : ℚ) (z : Plane) :
    z ∈ closedCell (squareLines R) ↔
      (-(R : ℝ) ≤ z.re ∧ z.re ≤ (R : ℝ)) ∧
      (-(R : ℝ) ≤ z.im ∧ z.im ≤ (R : ℝ)) := by
  simp only [closedCell, squareLines, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RationalLine.eval, normalEval]
  norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem closedCell_squareLines_isCompact (R : ℚ) :
    IsCompact (closedCell (squareLines R)) := by
  have hsub : closedCell (squareLines R) ⊆ Metric.closedBall 0 (2*(R : ℝ)) := by
    intro z hz
    obtain ⟨hre, him⟩ := (mem_closedCell_squareLines R z).mp hz
    have har : |z.re| ≤ (R : ℝ) := abs_le.mpr hre
    have hai : |z.im| ≤ (R : ℝ) := abs_le.mpr him
    have hn := Complex.norm_le_abs_re_add_abs_im z
    have hbound : ‖z‖ ≤ 2*(R : ℝ) := by linarith
    simpa [Metric.mem_closedBall, dist_eq_norm] using hbound
  exact Metric.isCompact_of_isClosed_isBounded (closedCell_isClosed _)
    (Metric.isBounded_closedBall.subset hsub)

private theorem squareClippedCell_target_isCompact (R : ℚ) (cell : List RationalLine)
    (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) :
    IsCompact (closedCell (((squareLines R) ++ cell).map (deformLine φ))) := by
  rw [List.map_append, deform_squareLines φ hφ R, closedCell_append]
  exact (closedCell_squareLines_isCompact R).inter_right (closedCell_isClosed _)

/-- Integer-square clipping supplies this compactness independently of source feasibility.
Consequently empty and lower-dimensional intersections are transported as actual hulls too. -/
private theorem finiteCell_hull_transport_of_targetCompact (cell : List RationalLine)
    (hcompact : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell (cell.map (deformLine φ)))) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        closedCell (cell.map (deformLine φ)) =
          convexHull ℝ (deformPoint φ '' (closedCell cell).extremePoints ℝ) := by
  obtain ⟨F, ε, hε, hext⟩ := finiteCell_extremePoints_transport cell
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  rw [closedCell_eq_convexHull_extremePoints _ (hcompact φ hφ.1)
    (closedCell_extremePoints_finite _), hext φ hφ]

private theorem cellFace_eq_closedCell_append_negate (cell : List RationalLine)
    (l : RationalLine) (hl : l ∈ cell) :
    cellFace cell l = closedCell (cell ++ [negateLine l]) := by
  rw [closedCell_append]
  ext z
  constructor
  · rintro ⟨hz, hzero⟩
    refine ⟨hz, ?_⟩
    intro k hk
    have hk' : k = negateLine l := by simpa using hk
    subst k
    rw [negateLine_eval, hzero]
    norm_num
  · rintro ⟨hz, hneg⟩
    refine ⟨hz, ?_⟩
    have hn := hneg (negateLine l) (by simp)
    rw [negateLine_eval] at hn
    exact le_antisymm (hz l hl) (by linarith)

/-- Every active face, including empty and singleton faces, has its actual transported hull.
The compactness callback is supplied by square clipping in the arrangement construction. -/
private theorem finiteCell_allFaces_hull_transport (cell : List RationalLine)
    (hcompact : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell (cell.map (deformLine φ)))) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ l ∈ cell, cellFace (cell.map (deformLine φ)) (deformLine φ l) =
          convexHull ℝ (deformPoint φ '' (cellFace cell l).extremePoints ℝ) := by
  classical
  let I := cell.toFinset
  have htests : ∀ i : {l // l ∈ I}, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        cellFace (cell.map (deformLine φ)) (deformLine φ i.1) =
          convexHull ℝ (deformPoint φ '' (cellFace cell i.1).extremePoints ℝ) := by
    intro i
    have hi : i.1 ∈ cell := List.mem_toFinset.mp i.2
    have hc : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
        IsCompact (closedCell ((cell ++ [negateLine i.1]).map (deformLine φ))) := by
      intro φ hφ
      rw [List.map_append, closedCell_append]
      exact (hcompact φ hφ).inter_right (closedCell_isClosed _)
    obtain ⟨F, ε, hε, ht⟩ :=
      finiteCell_hull_transport_of_targetCompact (cell ++ [negateLine i.1]) hc
    refine ⟨F, ε, hε, ?_⟩
    intro φ hφ
    have ht' := ht φ hφ
    rw [List.map_append, List.map_singleton, ← negateLine_deformLine] at ht'
    rw [← cellFace_eq_closedCell_append_negate cell i.1 hi,
      ← cellFace_eq_closedCell_append_negate (cell.map (deformLine φ)) (deformLine φ i.1)
        (List.mem_map.mpr ⟨i.1, hi, rfl⟩)] at ht'
    exact ht'
  choose tests threshold hpos hproof using htests
  obtain ⟨F, ε, hε, ht⟩ := unify_finiteApproximationTests tests threshold hpos
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ l hl
  exact hproof ⟨l, List.mem_toFinset.mpr hl⟩ φ (ht φ hφ ⟨l, List.mem_toFinset.mpr hl⟩)

private theorem affineMaps_agree_on_convexHull (f g : Plane →ᵃ[ℝ] Plane) (V : Set Plane)
    (hV : ∀ v ∈ V, f v = g v) :
    ∀ x ∈ convexHull ℝ V, f x = g x := by
  let E : Set Plane := {x | f x = g x}
  have hE : Convex ℝ E := by
    intro x hx y hy a b ha hb hab
    change f x = g x at hx
    change f y = g y at hy
    change f (a • x + b • y) = g (a • x + b • y)
    rw [Convex.combo_affine_apply hab, Convex.combo_affine_apply hab, hx, hy]
  have hVE : V ⊆ E := fun v hv => hV v hv
  intro x hx
  exact convexHull_min hVE hE hx

private theorem cellFaces_intersection_eq_endpointHull
    (cell : List RationalLine) (hcompact : IsCompact (closedCell cell))
    (l m : RationalLine) (hl : l ∈ cell) (hm : m ∈ cell) (a b d e : Plane)
    (hfaceL : cellFace cell l = segment ℝ a b)
    (hfaceM : cellFace cell m = segment ℝ d e) :
    cellFace cell l ∩ cellFace cell m =
      convexHull ℝ (({a,b} : Set Plane) ∩ {d,e}) := by
  let E := cellFace cell l ∩ cellFace cell m
  have hL : IsExtreme ℝ (closedCell cell) (cellFace cell l) :=
    closedCell_activeFace_isExtreme cell l hl
  have hM : IsExtreme ℝ (closedCell cell) (cellFace cell m) :=
    closedCell_activeFace_isExtreme cell m hm
  have hE : IsExtreme ℝ (closedCell cell) E := hL.inter hM
  have hEconvex : Convex ℝ E :=
    (closedCell_face_convex cell l hl).inter (closedCell_face_convex cell m hm)
  have hEcompact : IsCompact E := (closedCell_face_compact cell l hcompact).inter_right
    ((closedCell_isClosed cell).inter (isClosed_eq (lineEval_continuous m) continuous_const))
  have hextSubset : E.extremePoints ℝ ⊆ ({a,b} : Set Plane) ∩ {d,e} := by
    intro x hx
    have hxC := hE.extremePoints_subset_extremePoints hx
    have hxL : x ∈ (cellFace cell l).extremePoints ℝ := by
      rw [hL.extremePoints_eq]
      exact ⟨hx.1.1, hxC⟩
    have hxM : x ∈ (cellFace cell m).extremePoints ℝ := by
      rw [hM.extremePoints_eq]
      exact ⟨hx.1.2, hxC⟩
    rw [hfaceL, ← convexHull_pair] at hxL
    rw [hfaceM, ← convexHull_pair] at hxM
    exact ⟨extremePoints_convexHull_subset hxL, extremePoints_convexHull_subset hxM⟩
  have hfinite : (E.extremePoints ℝ).Finite :=
    ((Set.toFinite ({a,b} : Set Plane)).inter_of_left _).subset hextSubset
  have hKM := closure_convexHull_extremePoints hEcompact hEconvex
  rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at hKM
  apply Set.Subset.antisymm
  · change E ⊆ convexHull ℝ (({a,b} : Set Plane) ∩ {d,e})
    rw [← hKM]
    exact convexHull_mono hextSubset
  · apply convexHull_min ?_ hEconvex
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hfaceL, ← convexHull_pair]
      exact subset_convexHull ℝ _ hx.1
    · rw [hfaceM, ← convexHull_pair]
      exact subset_convexHull ℝ _ hx.2

/-- Two fan triangles over faces of one strictly feasible cell intersect exactly in the
convex hull of their shared face together with the center. -/
private theorem fanTriangles_intersection_eq_commonFaceHull
    (cell : List RationalLine) (c a b d e : Plane) (l m : RationalLine)
    (hab : a ≠ b) (hde : d ≠ e)
    (hlmem : l ∈ cell) (hmmem : m ∈ cell)
    (hc : ∀ k ∈ cell, k.eval c < 0)
    (hfaceL : cellFace cell l = segment ℝ a b)
    (hfaceM : cellFace cell m = segment ℝ d e) :
    convexHull ℝ {c, a, b} ∩ convexHull ℝ {c, d, e} =
      convexHull ℝ ({c} ∪ (cellFace cell l ∩ cellFace cell m)) := by
  have haL : a ∈ cellFace cell l := by rw [hfaceL]; exact left_mem_segment ℝ a b
  have hbL : b ∈ cellFace cell l := by rw [hfaceL]; exact right_mem_segment ℝ a b
  have hdM : d ∈ cellFace cell m := by rw [hfaceM]; exact left_mem_segment ℝ d e
  have heM : e ∈ cellFace cell m := by rw [hfaceM]; exact right_mem_segment ℝ d e
  have hca : c ≠ a := by
    intro h
    have : l.eval c = 0 := by simpa [h] using haL.2
    exact (ne_of_lt (hc l hlmem)) this
  have hcb : c ≠ b := by
    intro h
    have : l.eval c = 0 := by simpa [h] using hbL.2
    exact (ne_of_lt (hc l hlmem)) this
  have hcd : c ≠ d := by
    intro h
    have : m.eval c = 0 := by simpa [h] using hdM.2
    exact (ne_of_lt (hc m hmmem)) this
  have hce : c ≠ e := by
    intro h
    have : m.eval c = 0 := by simpa [h] using heM.2
    exact (ne_of_lt (hc m hmmem)) this
  apply subset_antisymm
  · rintro z ⟨hzL, hzM⟩
    by_cases hzc : z = c
    · subst z
      exact subset_convexHull ℝ _ (by simp)
    · obtain ⟨p, hpseg, hpz⟩ := triangle_hull_factors c a b z hca hcb hab hzL hzc
      obtain ⟨q, hqseg, hqz⟩ := triangle_hull_factors c d e z hcd hce hde hzM hzc
      have hpface : p ∈ cellFace cell l := by rw [hfaceL]; exact hpseg
      have hqface : q ∈ cellFace cell m := by rw [hfaceM]; exact hqseg
      have hpq : p = q := segment_ray_eq_of_strict_cell cell c p q z l m hlmem hmmem hc
        hpface.1 hqface.1 hpface.2 hqface.2 hzc hpz hqz
      have hpcommon : p ∈ cellFace cell l ∩ cellFace cell m := by
        rw [hpq]
        exact ⟨hpq ▸ hpface, hqface⟩
      have hzcp : z ∈ convexHull ℝ ({c, p} : Set Plane) := by
        simpa [convexHull_pair] using hpz
      apply convexHull_mono ?_ hzcp
      intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Set.mem_union_left _ rfl
      · exact Set.mem_union_right _ hpcommon
  · apply convexHull_min
    · intro z hz
      simp only [mem_union, mem_singleton_iff, mem_inter_iff] at hz
      rcases hz with hzc | ⟨hzL, hzM⟩
      · subst z
        exact ⟨subset_convexHull ℝ _ (by simp), subset_convexHull ℝ _ (by simp)⟩
      · have hzab : z ∈ segment ℝ a b := by rw [← hfaceL]; exact hzL
        have hzde : z ∈ segment ℝ d e := by rw [← hfaceM]; exact hzM
        have ha : a ∈ convexHull ℝ ({c, a, b} : Set Plane) := subset_convexHull ℝ _ (by simp)
        have hb : b ∈ convexHull ℝ ({c, a, b} : Set Plane) := subset_convexHull ℝ _ (by simp)
        have hd : d ∈ convexHull ℝ ({c, d, e} : Set Plane) := subset_convexHull ℝ _ (by simp)
        have he : e ∈ convexHull ℝ ({c, d, e} : Set Plane) := subset_convexHull ℝ _ (by simp)
        exact ⟨(convex_convexHull ℝ ({c, a, b} : Set Plane)).segment_subset ha hb hzab,
          (convex_convexHull ℝ ({c, d, e} : Set Plane)).segment_subset hd he hzde⟩
    · exact (convex_convexHull ℝ ({c, a, b} : Set Plane)).inter
        (convex_convexHull ℝ ({c, d, e} : Set Plane))


private theorem fanTriangles_intersection_eq_endpointHull
    (cell : List RationalLine) (hcompact : IsCompact (closedCell cell))
    (c a b d e : Plane) (l m : RationalLine) (hab : a ≠ b) (hde : d ≠ e)
    (hl : l ∈ cell) (hm : m ∈ cell) (hc : c ∈ openCell cell)
    (hfaceL : cellFace cell l = segment ℝ a b)
    (hfaceM : cellFace cell m = segment ℝ d e) :
    convexHull ℝ {c,a,b} ∩ convexHull ℝ {c,d,e} =
      convexHull ℝ ({c} ∪ (({a,b} : Set Plane) ∩ {d,e})) := by
  rw [fanTriangles_intersection_eq_commonFaceHull cell c a b d e l m hab hde hl hm hc
    hfaceL hfaceM,
    cellFaces_intersection_eq_endpointHull cell hcompact l m hl hm a b d e hfaceL hfaceM,
    convexHull_convexHull_union_right]

private theorem finiteCell_emptyOpen_transport (cell : List RationalLine)
    (hempty : openCell cell = ∅)
    (hcompact : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell (cell.map (deformLine φ)))) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        openCell (cell.map (deformLine φ)) = ∅ := by
  obtain ⟨F, ε, hε, hhull⟩ := finiteCell_hull_transport_of_targetCompact cell hcompact
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzclosed : z ∈ closedCell (cell.map (deformLine φ)) :=
    fun l hl => (hz l hl).le
  by_cases hne : (closedCell cell).Nonempty
  · obtain ⟨l, hl, hactive⟩ := closedCell_emptyOpen_has_universally_active_line cell hne hempty
    have hsub : closedCell (cell.map (deformLine φ)) ⊆
        {w | (deformLine φ l).eval w = 0} := by
      rw [hhull φ hφ]
      apply convexHull_min ?_ ?_
      · rintro w ⟨v, hv, rfl⟩
        change (deformLine φ l).eval (deformPoint φ v) = 0
        rw [deformLine_eval_commutes, hactive v hv.1, map_zero, Rat.cast_zero]
      · have heq : {w | (deformLine φ l).eval w = 0} =
            {w | normalEval l.normal w = (φ l.offset : ℝ)} := by
          ext w
          simp [RationalLine.eval, deformLine, sub_eq_zero]
        rw [heq]
        exact convex_hyperplane (normalEval_isLinear l.normal) _
    have hzero := hsub hzclosed
    have hneg := hz (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩)
    change (deformLine φ l).eval z = 0 at hzero
    linarith
  · have hext : (closedCell cell).extremePoints ℝ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hv
      exact hne ⟨v, hv.1⟩
    have htarget : closedCell (cell.map (deformLine φ)) = ∅ := by
      rw [hhull φ hφ, hext, Set.image_empty, convexHull_empty]
    rw [htarget] at hzclosed
    exact hzclosed

private theorem finiteCell_intersection_transport (C D : List RationalLine)
    (hcompact : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)))) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)) =
          convexHull ℝ (deformPoint φ '' (closedCell C ∩ closedCell D).extremePoints ℝ) := by
  have hc : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell ((C ++ D).map (deformLine φ))) := by
    intro φ hφ
    simpa only [List.map_append, closedCell_append] using hcompact φ hφ
  simpa only [List.map_append, closedCell_append] using
    finiteCell_hull_transport_of_targetCompact (C ++ D) hc

private theorem finiteSquareCell_hull_transport (R : ℚ) (cell : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        closedCell (squareLines R ++ cell.map (deformLine φ)) =
          convexHull ℝ (deformPoint φ '' (closedCell (squareLines R ++ cell)).extremePoints ℝ) := by
  obtain ⟨F, ε, hε, htarget⟩ := finiteCell_hull_transport_of_targetCompact
    (squareLines R ++ cell) (squareClippedCell_target_isCompact R cell)
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  simpa only [List.map_append, deform_squareLines φ hφ.1 R] using htarget φ hφ

private theorem finiteSquareCell_strictFeasibility (R : ℚ) (cell : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ((openCell (squareLines R ++ cell.map (deformLine φ))).Nonempty ↔
          (openCell (squareLines R ++ cell)).Nonempty) := by
  classical
  let C := squareLines R ++ cell
  by_cases hne : (openCell C).Nonempty
  · obtain ⟨c, hc⟩ := hne
    obtain ⟨F, ε, hε, htarget⟩ := finiteCell_strictPointTests C c hc
    refine ⟨F, ε, hε, ?_⟩
    intro φ hφ
    constructor
    · intro _
      exact ⟨c, hc⟩
    · intro _
      have ht : deformPoint φ c ∈ openCell (C.map (deformLine φ)) := htarget φ hφ
      have ht' : deformPoint φ c ∈ openCell (squareLines R ++ cell.map (deformLine φ)) := by
        simpa only [C, List.map_append, deform_squareLines φ hφ.1 R] using ht
      exact ⟨deformPoint φ c, ht'⟩
  · have he : openCell C = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨F, ε, hε, htarget⟩ := finiteCell_emptyOpen_transport C he
      (squareClippedCell_target_isCompact R cell)
    refine ⟨F, ε, hε, ?_⟩
    intro φ hφ
    have ht : openCell (squareLines R ++ cell.map (deformLine φ)) = ∅ := by
      simpa only [C, List.map_append, deform_squareLines φ hφ.1 R] using htarget φ hφ
    constructor
    · intro htargetNe
      exact ((Set.not_nonempty_iff_eq_empty.mpr ht) htargetNe).elim
    · intro hsourceNe
      exact (hne hsourceNe).elim

private theorem openCell_append (C D : List RationalLine) :
    openCell (C ++ D) = openCell C ∩ openCell D := by
  ext z
  constructor
  · intro hz
    exact ⟨fun l hl => hz l (List.mem_append.mpr (Or.inl hl)),
      fun l hl => hz l (List.mem_append.mpr (Or.inr hl))⟩
  · rintro ⟨hC, hD⟩ l hl
    rcases List.mem_append.mp hl with hl | hl
    · exact hC l hl
    · exact hD l hl

private def fullSquareCodes (R : ℚ) (L : List RationalLine) : PolyhedralCode :=
  ((signedCodes L).filter (fun cell => by
    classical
    exact decide (openCell (squareLines R ++ cell)).Nonempty)).map
      (fun cell => squareLines R ++ cell)

private theorem fullSquareCodes_support (R : ℚ) (hR : 0 < R) (L : List RationalLine) :
    polyhedralSupport (fullSquareCodes R L) = closedCell (squareLines R) := by
  classical
  let P := fullSquareCodes R L
  have hsub : polyhedralSupport P ⊆ closedCell (squareLines R) := by
    rintro z ⟨cell, hc, hz⟩
    obtain ⟨C, _, rfl⟩ := List.mem_map.mp hc
    exact fun l hl => hz l (List.mem_append.mpr (Or.inl hl))
  have hinside : openCell (squareLines R) ∩ offLines L ⊆ polyhedralSupport P := by
    rintro z ⟨hzSquare, hzLines⟩
    obtain ⟨cell, hc, hzcell⟩ := offLines_covered_by_signedCodes L z hzLines
    have hz : z ∈ openCell (squareLines R ++ cell) := by
      rw [openCell_append]
      exact ⟨hzSquare, hzcell⟩
    refine ⟨squareLines R ++ cell, List.mem_map.mpr ⟨cell,
      List.mem_filter.mpr ⟨hc, decide_eq_true (show (openCell (squareLines R ++ cell)).Nonempty from
        ⟨z, hz⟩)⟩, rfl⟩, fun l hl => (hz l hl).le⟩
  have hint : openCell (squareLines R) ⊆ polyhedralSupport P :=
    ((offLines_dense L).open_subset_closure_inter (openCell_isOpen _)).trans
      (closure_minimal hinside (polyhedralSupport_isClosed P))
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have h0 : (0 : Plane) ∈ openCell (squareLines R) := by
    simpa [openCell, squareLines, RationalLine.eval, normalEval] using neg_neg_of_pos hRreal
  apply subset_antisymm hsub
  rw [← openCell_closure (squareLines R) ⟨0, h0⟩]
  exact closure_minimal hint (polyhedralSupport_isClosed P)

private theorem fullSquareCodes_cellData (R : ℚ) (L : List RationalLine) :
    ∀ cell ∈ fullSquareCodes R L,
      IsCompact (closedCell cell) ∧ (openCell cell).Nonempty := by
  classical
  intro cell hc
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hc
  obtain ⟨_, hne⟩ := List.mem_filter.mp hC
  refine ⟨?_, of_decide_eq_true hne⟩
  rw [closedCell_append]
  exact (closedCell_squareLines_isCompact R).inter_right (closedCell_isClosed _)

private theorem signedCodes_map_deform (L : List RationalLine) (φ : ℝ →ₗ[ℚ] ℚ) :
    (signedCodes L).map (fun cell => cell.map (deformLine φ)) =
      signedCodes (L.map (deformLine φ)) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [signedCodes, List.map_cons]
    rw [← ih]
    simp only [List.map_append, List.map_map, Function.comp_def, List.map_cons,
      negateLine_deformLine]

private theorem finiteSquareCodes_strictFeasibility (R : ℚ) (L : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ cell ∈ signedCodes L,
          ((openCell (squareLines R ++ cell.map (deformLine φ))).Nonempty ↔
            (openCell (squareLines R ++ cell)).Nonempty) := by
  classical
  let S := (signedCodes L).toFinset
  have hchoices : ∀ i : {cell // cell ∈ S},
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ((openCell (squareLines R ++ i.1.map (deformLine φ))).Nonempty ↔
            (openCell (squareLines R ++ i.1)).Nonempty) :=
    fun i => finiteSquareCell_strictFeasibility R i.1
  choose tests threshold hpos htests using hchoices
  obtain ⟨F, ε, hε, hall⟩ := unify_finiteApproximationTests tests threshold hpos
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ cell hc
  let i : {cell // cell ∈ S} := ⟨cell, List.mem_toFinset.mpr hc⟩
  exact htests i φ (hall φ hφ i)

private theorem fullSquareCodes_targetSupport (R : ℚ) (hR : 0 < R) (L : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        deformedPolyhedralSupport (fullSquareCodes R L) φ = closedCell (squareLines R) := by
  classical
  obtain ⟨F, ε, hε, hfeasible⟩ := finiteSquareCodes_strictFeasibility R L
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  have hsupports : deformedPolyhedralSupport (fullSquareCodes R L) φ =
      polyhedralSupport (fullSquareCodes R (L.map (deformLine φ))) := by
    ext z
    constructor
    · rintro ⟨cell, hc, hz⟩
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hc
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hC
      obtain ⟨hD, hDstrict⟩ := List.mem_filter.mp hD
      have hsource : (openCell (squareLines R ++ D)).Nonempty := of_decide_eq_true hDstrict
      have htarget := (hfeasible φ hφ D hD).mpr hsource
      have hmapped : D.map (deformLine φ) ∈ signedCodes (L.map (deformLine φ)) := by
        rw [← signedCodes_map_deform L φ]
        exact List.mem_map.mpr ⟨D, hD, rfl⟩
      refine ⟨squareLines R ++ D.map (deformLine φ), List.mem_map.mpr ⟨D.map (deformLine φ),
        List.mem_filter.mpr ⟨hmapped, decide_eq_true htarget⟩, rfl⟩, ?_⟩
      simpa only [List.map_append, deform_squareLines φ hφ.1 R] using hz
    · rintro ⟨cell, hc, hz⟩
      obtain ⟨D, hD, rfl⟩ := List.mem_map.mp hc
      obtain ⟨hD, hDstrict⟩ := List.mem_filter.mp hD
      rw [← signedCodes_map_deform L φ] at hD
      obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hD
      have htarget : (openCell (squareLines R ++ C.map (deformLine φ))).Nonempty :=
        of_decide_eq_true hDstrict
      have hsource := (hfeasible φ hφ C hC).mp htarget
      refine ⟨(squareLines R ++ C).map (deformLine φ), List.mem_map.mpr ⟨squareLines R ++ C,
        List.mem_map.mpr ⟨C, List.mem_filter.mpr ⟨hC, decide_eq_true hsource⟩, rfl⟩, rfl⟩, ?_⟩
      simpa only [List.map_append, deform_squareLines φ hφ.1 R] using hz
  exact hsupports.trans (fullSquareCodes_support R hR (L.map (deformLine φ)))

private theorem finiteCell_face_transport (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (closedCell cell).Nonempty) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ l ∈ cell, ∀ a b : Plane,
          cellFace cell l = segment ℝ a b →
          cellFace (cell.map (deformLine φ)) (deformLine φ l) =
            segment ℝ (deformPoint φ a) (deformPoint φ b) := by
  obtain ⟨F₁, ε₁, hε₁, hext⟩ := finiteCell_extremePoints_transport cell
  obtain ⟨F₂, ε₂, hε₂, hsign⟩ := finiteCell_vertexSignTests cell
  refine ⟨F₁ ∪ F₂, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro φ hφ l hl a b hface
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
  have hcompactφ : IsCompact (closedCell (cell.map (deformLine φ))) := by
    rw [closedCell_map_eq_shiftedCell]
    exact shiftedCell_isCompact_of_compact_same_normals cell hcompact hne _
  apply face_transport_eq_segment cell (cell.map (deformLine φ)) l hl
    (deformLine φ l) (List.mem_map.mpr ⟨l, hl, rfl⟩) (deformPoint φ)
    hcompactφ (hext φ hφ₁) ?_ a b hface
  intro v hv
  have hs := hsign φ hφ₂ v hv l hl
  rw [← Real.sign_eq_zero_iff, hs, Real.sign_eq_zero_iff]

private theorem finiteApproximation_narrow {F G : Finset ℝ} {ε η : ℝ}
    {φ : ℝ →ₗ[ℚ] ℚ} (hφ : IsFiniteApproximation G η φ)
    (hFG : F ⊆ G) (hεη : η ≤ ε) : IsFiniteApproximation F ε φ :=
  ⟨hφ.1, fun x hx => (hφ.2 x (hFG hx)).trans_le hεη⟩

/-- The same actual finite ordered face frames cover both compact chambers. This is not
an abstract triangulation certificate: target coverage follows from target radial fans and
the transported hull of every face, so empty source faces cannot create target edges. -/
private theorem finiteCell_matchedFanFamily (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ I : Finset RationalLine, ∃ a b : {l // l ∈ I} → Plane,
      (∀ i, i.1 ∈ cell ∧ a i ≠ b i ∧ cellFace cell i.1 = segment ℝ (a i) (b i)) ∧
      (⋃ i, convexHull ℝ {c, a i, b i}) = closedCell cell ∧
      (∀ l ∈ cell, ∀ d e : Plane, d ≠ e → cellFace cell l = segment ℝ d e →
        ∃ i : {l // l ∈ I}, i.1 = l) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          (∀ i, Tiling.twiceSignedArea (deformPoint φ c)
            (deformPoint φ (a i)) (deformPoint φ (b i)) ≠ 0) ∧
          (∀ i, cellFace (cell.map (deformLine φ)) (deformLine φ i.1) =
            segment ℝ (deformPoint φ (a i)) (deformPoint φ (b i))) ∧
          (⋃ i, convexHull ℝ {deformPoint φ c, deformPoint φ (a i), deformPoint φ (b i)}) =
            closedCell (cell.map (deformLine φ)) := by
  classical
  let I := cell.toFinset.filter fun l =>
    ∃ a b : Plane, a ≠ b ∧ cellFace cell l = segment ℝ a b
  have hchoices : ∀ i : {l // l ∈ I}, ∃ a b : Plane,
      a ≠ b ∧ cellFace cell i.1 = segment ℝ a b :=
    fun i => (Finset.mem_filter.mp i.2).2
  choose a b hab hface using hchoices
  have himem (i : {l // l ∈ I}) : i.1 ∈ cell :=
    List.mem_toFinset.mp (Finset.mem_filter.mp i.2).1
  have hcomplete : ∀ l ∈ cell, ∀ d e : Plane, d ≠ e →
      cellFace cell l = segment ℝ d e → ∃ i : {l // l ∈ I}, i.1 = l := by
    intro l hl d e hde hdeFace
    have hlI : l ∈ I := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr hl,d,e,hde,hdeFace⟩
    exact ⟨⟨l,hlI⟩,rfl⟩
  have hsource : (⋃ i, convexHull ℝ {c, a i, b i}) = closedCell cell := by
    obtain ⟨A, _, hshape, _⟩ := closedCell_fanModel cell hcompact c hc
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      have ha : a i ∈ closedCell cell :=
        ((hface i).symm ▸ left_mem_segment ℝ (a i) (b i) : a i ∈ cellFace cell i.1).1
      have hb : b i ∈ closedCell cell :=
        ((hface i).symm ▸ right_mem_segment ℝ (a i) (b i) : b i ∈ cellFace cell i.1).1
      apply convexHull_min ?_ (closedCell_convex cell) hx
      intro v hv
      simp only [mem_insert_iff, mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact fun l hl => (hc l hl).le
      · exact ha
      · exact hb
    · intro x hx
      have hxA : x ∈ ⋃₀ (A.pieces : Set (Set Plane)) := A.sUnion_eq.symm ▸ hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hxA
      obtain ⟨l, hl, d, e, hde, hdeFace, _, rfl⟩ := hshape t ht
      have hlI : l ∈ I := Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hl, d, e, hde, hdeFace⟩
      let i : {l // l ∈ I} := ⟨l, hlI⟩
      have heq := triple_hulls_eq_of_segment_eq c d e (a i) (b i)
        (hdeFace.symm.trans (hface i))
      exact Set.mem_iUnion.mpr ⟨i, heq ▸ hxt⟩
  have htargetCompact : ∀ φ : ℝ →ₗ[ℚ] ℚ, φ 1 = 1 →
      IsCompact (closedCell (cell.map (deformLine φ))) := by
    intro φ _
    rw [closedCell_map_eq_shiftedCell]
    exact shiftedCell_isCompact_of_compact_same_normals cell hcompact
      ⟨c, fun l hl => (hc l hl).le⟩ _
  obtain ⟨F₁, ε₁, hε₁, hcenter⟩ := finiteCell_strictPointTests cell c hc
  obtain ⟨F₂, ε₂, hε₂, hfaces⟩ :=
    finiteCell_face_transport cell hcompact ⟨c, fun l hl => (hc l hl).le⟩
  obtain ⟨F₃, ε₃, hε₃, hinj⟩ := finiteCell_extremePoints_injective cell
  obtain ⟨F₄, ε₄, hε₄, hallFaces⟩ := finiteCell_allFaces_hull_transport cell htargetCompact
  refine ⟨I, a, b, fun i => ⟨himem i, hab i, hface i⟩, hsource, hcomplete,
    (F₁ ∪ F₂) ∪ (F₃ ∪ F₄), min (min ε₁ ε₂) (min ε₃ ε₄),
    lt_min (lt_min hε₁ hε₂) (lt_min hε₃ hε₄), ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_left _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_right _ _))
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_left _ _))
  have hφ₄ : IsFiniteApproximation F₄ ε₄ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_right _ _).trans (min_le_right _ _))
  have hcφ := hcenter φ hφ₁
  have hfaceφ (i : {l // l ∈ I}) := hfaces φ hφ₂ i.1 (himem i) (a i) (b i) (hface i)
  have habφ (i : {l // l ∈ I}) : deformPoint φ (a i) ≠ deformPoint φ (b i) := by
    have hend := closedCell_face_segment_endpoints_extreme cell i.1 (himem i)
      (a i) (b i) (hface i)
    exact fun h => hab i (hinj φ hφ₃ hend.1 hend.2 h)
  refine ⟨?_, hfaceφ, ?_⟩
  · intro i
    have haφ : deformPoint φ (a i) ∈ cellFace (cell.map (deformLine φ)) (deformLine φ i.1) :=
      (hfaceφ i).symm ▸ left_mem_segment ℝ _ _
    have hbφ : deformPoint φ (b i) ∈ cellFace (cell.map (deformLine φ)) (deformLine φ i.1) :=
      (hfaceφ i).symm ▸ right_mem_segment ℝ _ _
    exact fanTriangle_area_ne (deformLine φ i.1) _ _ _
      (hcφ _ (List.mem_map.mpr ⟨i.1, himem i, rfl⟩)) haφ.2 hbφ.2 (habφ i)
  · obtain ⟨A, _, hshape, _⟩ := closedCell_fanModel (cell.map (deformLine φ))
      (htargetCompact φ hφ.1) (deformPoint φ c) hcφ
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
      have haφ : deformPoint φ (a i) ∈ closedCell (cell.map (deformLine φ)) :=
        ((hfaceφ i).symm ▸ left_mem_segment ℝ _ _ :
          deformPoint φ (a i) ∈ cellFace (cell.map (deformLine φ)) (deformLine φ i.1)).1
      have hbφ : deformPoint φ (b i) ∈ closedCell (cell.map (deformLine φ)) :=
        ((hfaceφ i).symm ▸ right_mem_segment ℝ _ _ :
          deformPoint φ (b i) ∈ cellFace (cell.map (deformLine φ)) (deformLine φ i.1)).1
      apply convexHull_min ?_ (closedCell_convex _) hx
      intro v hv
      simp only [mem_insert_iff, mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · exact fun l hl => (hcφ l hl).le
      · exact haφ
      · exact hbφ
    · intro x hx
      have hxA : x ∈ ⋃₀ (A.pieces : Set (Set Plane)) := A.sUnion_eq.symm ▸ hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hxA
      obtain ⟨m, hm, d, e, hde, hdeFace, _, rfl⟩ := hshape t ht
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
      have hsourceFaceNe : (cellFace cell l).Nonempty := by
        have hhullNe : (convexHull ℝ (deformPoint φ '' (cellFace cell l).extremePoints ℝ)).Nonempty := by
          rw [← hallFaces φ hφ₄ l hl, hdeFace]
          exact ⟨d, left_mem_segment ℝ d e⟩
        obtain ⟨_, v, hv, _⟩ := convexHull_nonempty_iff.mp hhullNe
        exact ⟨v, hv.1⟩
      obtain ⟨v, w, hvwFace⟩ := cellFace_eq_segment cell l hcompact hsourceFaceNe
      have hvwφFace := hfaces φ hφ₂ l hl v w hvwFace
      have hvw : v ≠ w := by
        intro h
        have hd : d ∈ segment ℝ (deformPoint φ v) (deformPoint φ w) :=
          (hdeFace.symm.trans hvwφFace) ▸ left_mem_segment ℝ d e
        have he : e ∈ segment ℝ (deformPoint φ v) (deformPoint φ w) :=
          (hdeFace.symm.trans hvwφFace) ▸ right_mem_segment ℝ d e
        have hd' : d = deformPoint φ v := by simpa [h] using hd
        have he' : e = deformPoint φ v := by simpa [h] using he
        exact hde (hd'.trans he'.symm)
      have hlI : l ∈ I := Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hl, v, w, hvw, hvwFace⟩
      let i : {l // l ∈ I} := ⟨l, hlI⟩
      have heq := triple_hulls_eq_of_segment_eq (deformPoint φ c) d e
        (deformPoint φ (a i)) (deformPoint φ (b i))
        (hdeFace.symm.trans (hfaceφ i))
      exact Set.mem_iUnion.mpr ⟨i, heq ▸ hxt⟩

private theorem affineFanMaps_agree_on_actual_overlap
    (cell : List RationalLine) (hcompact : IsCompact (closedCell cell))
    (c a b d e : Plane) (l m : RationalLine) (hab : a ≠ b) (hde : d ≠ e)
    (hl : l ∈ cell) (hm : m ∈ cell) (hc : c ∈ openCell cell)
    (hfaceL : cellFace cell l = segment ℝ a b)
    (hfaceM : cellFace cell m = segment ℝ d e)
    (f g : Plane →ᵃ[ℝ] Plane) (hcenter : f c = g c)
    (hend : ∀ v ∈ ({a,b} : Set Plane) ∩ {d,e}, f v = g v) :
    ∀ x ∈ convexHull ℝ {c,a,b} ∩ convexHull ℝ {c,d,e}, f x = g x := by
  rw [fanTriangles_intersection_eq_endpointHull cell hcompact c a b d e l m
    hab hde hl hm hc hfaceL hfaceM]
  apply affineMaps_agree_on_convexHull
  intro v hv
  rcases hv with hv | hv
  · have hv' : v = c := hv
    simpa only [hv'] using hcenter
  · exact hend v hv

/-- Actual affine pieces with two-sided overlap agreement on the matched chamber fans.
Only finite extreme-point injection is used to identify target anchors. -/
private theorem finiteCell_affineFanFamily (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ I : Finset RationalLine, ∃ a b : {l // l ∈ I} → Plane,
      (∀ i, i.1 ∈ cell ∧ a i ≠ b i ∧ cellFace cell i.1 = segment ℝ (a i) (b i)) ∧
      (⋃ i, convexHull ℝ {c, a i, b i}) = closedCell cell ∧
      (∀ l ∈ cell, ∀ d e : Plane, d ≠ e → cellFace cell l = segment ℝ d e →
        ∃ i : {l // l ∈ I}, i.1 = l) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ f : {l // l ∈ I} → Plane ≃ᵃ[ℝ] Plane,
            (∀ i, f i c = deformPoint φ c ∧ f i (a i) = deformPoint φ (a i) ∧
              f i (b i) = deformPoint φ (b i) ∧
              (f i : Plane → Plane) '' convexHull ℝ {c,a i,b i} =
                convexHull ℝ {deformPoint φ c,deformPoint φ (a i),deformPoint φ (b i)}) ∧
            (⋃ i, convexHull ℝ {deformPoint φ c,deformPoint φ (a i),deformPoint φ (b i)}) =
              closedCell (cell.map (deformLine φ)) ∧
            (∀ i j x, x ∈ convexHull ℝ {c,a i,b i} →
              x ∈ convexHull ℝ {c,a j,b j} → f i x = f j x) ∧
            (∀ i j y, y ∈ convexHull ℝ {deformPoint φ c,deformPoint φ (a i),deformPoint φ (b i)} →
              y ∈ convexHull ℝ {deformPoint φ c,deformPoint φ (a j),deformPoint φ (b j)} →
                (f i).symm y = (f j).symm y) := by
  classical
  obtain ⟨I, a, b, hframe, hsource, hcomplete, F₁, ε₁, hε₁, hmatched⟩ :=
    finiteCell_matchedFanFamily cell hcompact c hc
  obtain ⟨F₂, ε₂, hε₂, hinj⟩ := finiteCell_extremePoints_injective cell
  obtain ⟨F₃, ε₃, hε₃, hcenter⟩ := finiteCell_strictPointTests cell c hc
  refine ⟨I, a, b, hframe, hsource, hcomplete, (F₁ ∪ F₂) ∪ F₃,
    min (min ε₁ ε₂) ε₃, lt_min (lt_min hε₁ hε₂) hε₃, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_left _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_right _ _))
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto) (min_le_right _ _)
  obtain ⟨hareaφ, hfaceφ, htarget⟩ := hmatched φ hφ₁
  have harea (i : {l // l ∈ I}) : Tiling.twiceSignedArea c (a i) (b i) ≠ 0 := by
    have ha : a i ∈ cellFace cell i.1 := (hframe i).2.2.symm ▸ left_mem_segment ℝ _ _
    have hb : b i ∈ cellFace cell i.1 := (hframe i).2.2.symm ▸ right_mem_segment ℝ _ _
    exact fanTriangle_area_ne i.1 c (a i) (b i) (hc _ (hframe i).1) ha.2 hb.2 (hframe i).2.1
  have hfChoices (i : {l // l ∈ I}) := exists_affineEquiv_matching_triangles
    c (a i) (b i) (deformPoint φ c) (deformPoint φ (a i)) (deformPoint φ (b i))
    (harea i) (hareaφ i)
  choose f hfc hfa hfb hfImage hfEdge using hfChoices
  have hends (i : {l // l ∈ I}) := closedCell_face_segment_endpoints_extreme
    cell i.1 (hframe i).1 (a i) (b i) (hframe i).2.2
  have hvalue (i : {l // l ∈ I}) (v : Plane) (hv : v ∈ ({a i,b i} : Set Plane)) :
      f i v = deformPoint φ v := by
    simp only [mem_insert_iff, mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hfa i
    · exact hfb i
  refine ⟨f, fun i => ⟨hfc i, hfa i, hfb i, hfImage i⟩, htarget, ?_, ?_⟩
  · intro i j x hxi hxj
    apply affineFanMaps_agree_on_actual_overlap cell hcompact c (a i) (b i) (a j) (b j)
      i.1 j.1 (hframe i).2.1 (hframe j).2.1 (hframe i).1 (hframe j).1 hc
      (hframe i).2.2 (hframe j).2.2 (f i).toAffineMap (f j).toAffineMap
      ((hfc i).trans (hfc j).symm) ?_ x ⟨hxi,hxj⟩
    intro v hv
    exact (hvalue i v hv.1).trans (hvalue j v hv.2).symm
  · intro i j y hyi hyj
    have hcφ := hcenter φ hφ₃
    have hcompactφ : IsCompact (closedCell (cell.map (deformLine φ))) := by
      rw [closedCell_map_eq_shiftedCell]
      exact shiftedCell_isCompact_of_compact_same_normals cell hcompact
        ⟨c, fun l hl => (hc l hl).le⟩ _
    have habφ (k : {l // l ∈ I}) : deformPoint φ (a k) ≠ deformPoint φ (b k) :=
      fun h => (hframe k).2.1 (hinj φ hφ₂ (hends k).1 (hends k).2 h)
    have hci : (f i).symm (deformPoint φ c) = c := by rw [← hfc i]; simp
    have hcj : (f j).symm (deformPoint φ c) = c := by rw [← hfc j]; simp
    apply affineFanMaps_agree_on_actual_overlap (cell.map (deformLine φ)) hcompactφ
      (deformPoint φ c) (deformPoint φ (a i)) (deformPoint φ (b i))
      (deformPoint φ (a j)) (deformPoint φ (b j)) (deformLine φ i.1) (deformLine φ j.1)
      (habφ i) (habφ j) (List.mem_map.mpr ⟨i.1,(hframe i).1,rfl⟩)
      (List.mem_map.mpr ⟨j.1,(hframe j).1,rfl⟩) hcφ (hfaceφ i) (hfaceφ j)
      (f i).symm.toAffineMap (f j).symm.toAffineMap (hci.trans hcj.symm) ?_ y ⟨hyi,hyj⟩
    intro v hv
    have hpre (k : {l // l ∈ I}) (hvk : v ∈ ({deformPoint φ (a k),deformPoint φ (b k)} : Set Plane)) :
        ∃ w ∈ ({a k,b k} : Set Plane), deformPoint φ w = v := by
      have hv' : v ∈ deformPoint φ '' ({a k,b k} : Set Plane) := by
        rw [Set.image_pair]
        exact hvk
      exact hv'
    obtain ⟨u, hu, huv⟩ := hpre i hv.1
    obtain ⟨w, hw, hwv⟩ := hpre j hv.2
    have hExt (k : {l // l ∈ I}) : ({a k,b k} : Set Plane) ⊆ (closedCell cell).extremePoints ℝ := by
      intro z hz
      simp only [mem_insert_iff,mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (hends k).1
      · exact (hends k).2
    have huw : u = w := hinj φ hφ₂ (hExt i hu) (hExt j hw) (huv.trans hwv.symm)
    have hui : (f i).symm v = u := by rw [← huv, ← hvalue i u hu]; simp
    have hwj : (f j).symm v = w := by rw [← hwv, ← hvalue j w hw]; simp
    exact hui.trans (huw.trans hwj.symm)

/-- Approximation can be made injective on a specified finite point decoration. This makes
no assertion of injectivity, continuity or an inverse for the ambient rational-linear map. -/
private def relativePiece_homeomorph (S C : Set Plane) (hCS : C ⊆ S) :
    ({x : S | x.val ∈ C} : Set S) ≃ₜ C where
  toFun x := ⟨x.val.val,x.property⟩
  invFun y := ⟨⟨y.val,hCS y.property⟩,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Adapter for actual absolute affine pieces, retaining the exact piece restriction. -/
private theorem finiteAffineClosedCover_homeomorph {ι : Type*} [Fintype ι]
    (S T : Set Plane) (C D : ι → Set Plane)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCsub : ∀ i, C i ⊆ S) (hDsub : ∀ i, D i ⊆ T)
    (hCcover : ∀ x ∈ S, ∃ i, x ∈ C i) (hDcover : ∀ y ∈ T, ∃ i, y ∈ D i)
    (f : ι → Plane ≃ᵃ[ℝ] Plane) (himage : ∀ i, (f i : Plane → Plane) '' C i = D i)
    (hforward : ∀ i j x, x ∈ C i → x ∈ C j → f i x = f j x)
    (hinverse : ∀ i j y, y ∈ D i → y ∈ D j → (f i).symm y = (f j).symm y) :
    ∃ H : S ≃ₜ T, ∀ i (x : S), x.val ∈ C i → (H x : Plane) = f i x.val := by
  let Cr (i : ι) : Set S := {x | x.val ∈ C i}
  let Dr (i : ι) : Set T := {y | y.val ∈ D i}
  have hCrclosed (i : ι) : IsClosed (Cr i) :=
    (hCclosed i).preimage continuous_subtype_val
  have hDrclosed (i : ι) : IsClosed (Dr i) :=
    (hDclosed i).preimage continuous_subtype_val
  have hCrcover (x : S) : ∃ i, x ∈ Cr i := hCcover x.val x.property
  have hDrcover (y : T) : ∃ i, y ∈ Dr i := hDcover y.val y.property
  let piece (i : ι) : Cr i ≃ₜ Dr i :=
    (relativePiece_homeomorph S (C i) (hCsub i)).trans
      ((affineEquiv_restrict_image (f i) (C i) (D i) (himage i)).trans
        (relativePiece_homeomorph T (D i) (hDsub i)).symm)
  have hpforward : ∀ i j (x : S) (hxi : x ∈ Cr i) (hxj : x ∈ Cr j),
      (piece i ⟨x,hxi⟩).val = (piece j ⟨x,hxj⟩).val := by
    intro i j x hxi hxj
    apply Subtype.ext
    change f i x.val = f j x.val
    exact hforward i j x.val hxi hxj
  have hpinverse : ∀ i j (y : T) (hyi : y ∈ Dr i) (hyj : y ∈ Dr j),
      ((piece i).symm ⟨y,hyi⟩).val = ((piece j).symm ⟨y,hyj⟩).val := by
    intro i j y hyi hyj
    apply Subtype.ext
    change (f i).symm y.val = (f j).symm y.val
    exact hinverse i j y.val hyi hyj
  let H := finiteClosedCover_homeomorph S T Cr Dr hCrclosed hDrclosed hCrcover hDrcover
    piece hpforward hpinverse
  refine ⟨H, ?_⟩
  intro i x hx
  change f (Classical.choose (hCrcover x)) x.val = f i x.val
  exact hforward (Classical.choose (hCrcover x)) i x.val
    (Classical.choose_spec (hCrcover x)) hx

private theorem finiteHomeomorphClosedCover {ι : Type*} [Fintype ι]
    (S T : Set Plane) (C D : ι → Set Plane)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCsub : ∀ i, C i ⊆ S) (hDsub : ∀ i, D i ⊆ T)
    (hCcover : ∀ x ∈ S, ∃ i, x ∈ C i) (hDcover : ∀ y ∈ T, ∃ i, y ∈ D i)
    (localMap : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j x (hxi : x ∈ C i) (hxj : x ∈ C j),
      (localMap i ⟨x,hxi⟩ : Plane) = (localMap j ⟨x,hxj⟩ : Plane))
    (hinverse : ∀ i j y (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((localMap i).symm ⟨y,hyi⟩ : Plane) = ((localMap j).symm ⟨y,hyj⟩ : Plane)) :
    ∃ H : S ≃ₜ T, ∀ i (x : S) (hx : x.val ∈ C i),
      (H x : Plane) = (localMap i ⟨x.val,hx⟩ : Plane) := by
  let Cr (i : ι) : Set S := {x | x.val ∈ C i}
  let Dr (i : ι) : Set T := {y | y.val ∈ D i}
  have hCrclosed (i : ι) : IsClosed (Cr i) :=
    (hCclosed i).preimage continuous_subtype_val
  have hDrclosed (i : ι) : IsClosed (Dr i) :=
    (hDclosed i).preimage continuous_subtype_val
  have hCrcover (x : S) : ∃ i, x ∈ Cr i := hCcover x.val x.property
  have hDrcover (y : T) : ∃ i, y ∈ Dr i := hDcover y.val y.property
  let piece (i : ι) : Cr i ≃ₜ Dr i :=
    (relativePiece_homeomorph S (C i) (hCsub i)).trans
      ((localMap i).trans (relativePiece_homeomorph T (D i) (hDsub i)).symm)
  have hpforward : ∀ i j (x : S) (hxi : x ∈ Cr i) (hxj : x ∈ Cr j),
      (piece i ⟨x,hxi⟩).val = (piece j ⟨x,hxj⟩).val := by
    intro i j x hxi hxj
    apply Subtype.ext
    change (localMap i ⟨x.val,hxi⟩ : Plane) = (localMap j ⟨x.val,hxj⟩ : Plane)
    exact hforward i j x.val hxi hxj
  have hpinverse : ∀ i j (y : T) (hyi : y ∈ Dr i) (hyj : y ∈ Dr j),
      ((piece i).symm ⟨y,hyi⟩).val = ((piece j).symm ⟨y,hyj⟩).val := by
    intro i j y hyi hyj
    apply Subtype.ext
    change ((localMap i).symm ⟨y.val,hyi⟩ : Plane) = ((localMap j).symm ⟨y.val,hyj⟩ : Plane)
    exact hinverse i j y.val hyi hyj
  let H := finiteClosedCover_homeomorph S T Cr Dr hCrclosed hDrclosed hCrcover hDrcover
    piece hpforward hpinverse
  refine ⟨H,?_⟩
  intro i x hx
  change (localMap (Classical.choose (hCrcover x))
    ⟨x.val,Classical.choose_spec (hCrcover x)⟩ : Plane) = (localMap i ⟨x.val,hx⟩ : Plane)
  exact hforward (Classical.choose (hCrcover x)) i x.val (Classical.choose_spec (hCrcover x)) hx

private theorem finiteCell_fanHomeomorph (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ I : Finset RationalLine, ∃ a b : {l // l ∈ I} → Plane,
      (∀ i, i.1 ∈ cell ∧ a i ≠ b i ∧ cellFace cell i.1 = segment ℝ (a i) (b i)) ∧
      (⋃ i, convexHull ℝ {c,a i,b i}) = closedCell cell ∧
      (∀ l ∈ cell, ∀ d e : Plane, d ≠ e → cellFace cell l = segment ℝ d e →
        ∃ i : {l // l ∈ I}, i.1 = l) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ H : closedCell cell ≃ₜ closedCell (cell.map (deformLine φ)),
          ∃ f : {l // l ∈ I} → Plane ≃ᵃ[ℝ] Plane,
            (∀ i, f i c = deformPoint φ c ∧ f i (a i) = deformPoint φ (a i) ∧
              f i (b i) = deformPoint φ (b i)) ∧
            (∀ i (x : closedCell cell), x.val ∈ convexHull ℝ {c,a i,b i} →
              (H x : Plane) = f i x.val) := by
  obtain ⟨I,a,b,hframe,hsource,hcomplete,F,ε,hε,hfamily⟩ := finiteCell_affineFanFamily cell hcompact c hc
  refine ⟨I,a,b,hframe,hsource,hcomplete,F,ε,hε,?_⟩
  intro φ hφ
  obtain ⟨f,hf,htarget,hforward,hinverse⟩ := hfamily φ hφ
  let C := fun i : {l // l ∈ I} => convexHull ℝ {c,a i,b i}
  let D := fun i : {l // l ∈ I} =>
    convexHull ℝ {deformPoint φ c,deformPoint φ (a i),deformPoint φ (b i)}
  have hCsub (i) : C i ⊆ closedCell cell := by
    rw [← hsource]
    exact Set.subset_iUnion C i
  have hDsub (i) : D i ⊆ closedCell (cell.map (deformLine φ)) := by
    rw [← htarget]
    exact Set.subset_iUnion D i
  obtain ⟨H,hH⟩ := finiteAffineClosedCover_homeomorph (closedCell cell)
    (closedCell (cell.map (deformLine φ))) C D
    (fun i => (Set.toFinite {c,a i,b i}).isClosed_convexHull ℝ)
    (fun i => (Set.toFinite {deformPoint φ c,deformPoint φ (a i),deformPoint φ (b i)}).isClosed_convexHull ℝ)
    hCsub hDsub
    (fun x hx => Set.mem_iUnion.mp (hsource.symm ▸ hx))
    (fun y hy => Set.mem_iUnion.mp (htarget.symm ▸ hy))
    f (fun i => (hf i).2.2.2) hforward hinverse
  exact ⟨H,f,fun i => ⟨(hf i).1,(hf i).2.1,(hf i).2.2.1⟩,hH⟩

/-- The actual glued fan maps all cell extreme vertices and is affine on each whole edge. -/
private theorem fanHomeomorph_facewise (cell : List RationalLine) (c : Plane)
    (I : Finset RationalLine) (a b : {l // l ∈ I} → Plane)
    (hframe : ∀ i, i.1 ∈ cell ∧ a i ≠ b i ∧ cellFace cell i.1 = segment ℝ (a i) (b i))
    (hsource : (⋃ i, convexHull ℝ {c,a i,b i}) = closedCell cell)
    (hcomplete : ∀ l ∈ cell, ∀ d e : Plane, d ≠ e → cellFace cell l = segment ℝ d e →
      ∃ i : {l // l ∈ I}, i.1 = l)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : closedCell cell ≃ₜ closedCell (cell.map (deformLine φ)))
    (f : {l // l ∈ I} → Plane ≃ᵃ[ℝ] Plane)
    (hvalues : ∀ i, f i c = deformPoint φ c ∧ f i (a i) = deformPoint φ (a i) ∧
      f i (b i) = deformPoint φ (b i))
    (hpiece : ∀ i (x : closedCell cell), x.val ∈ convexHull ℝ {c,a i,b i} →
      (H x : Plane) = f i x.val) :
    (∀ v (hv : v ∈ (closedCell cell).extremePoints ℝ),
      (H ⟨v,hv.1⟩ : Plane) = deformPoint φ v) ∧
    (∀ l ∈ cell, ∀ a b : Plane, a ≠ b → cellFace cell l = segment ℝ a b →
      ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
        ∀ x : closedCell cell, x.val ∈ cellFace cell l → (H x : Plane) = g x.val) := by
  have hvertex : ∀ v (hv : v ∈ (closedCell cell).extremePoints ℝ),
      (H ⟨v,hv.1⟩ : Plane) = deformPoint φ v := by
    intro v hv
    obtain ⟨i,hvi⟩ := Set.mem_iUnion.mp (hsource.symm ▸ hv.1)
    have hsub : convexHull ℝ {c,a i,b i} ⊆ closedCell cell := by
      rw [← hsource]
      exact Set.subset_iUnion (fun j : {l // l ∈ I} => convexHull ℝ {c,a j,b j}) i
    have hvTri : v ∈ (convexHull ℝ {c,a i,b i}).extremePoints ℝ :=
      inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hvi,hv⟩
    have hvAnchors := extremePoints_convexHull_subset hvTri
    rw [hpiece i ⟨v,hv.1⟩ hvi]
    simp only [mem_insert_iff,mem_singleton_iff] at hvAnchors
    rcases hvAnchors with rfl | rfl | rfl
    · exact (hvalues i).1
    · exact (hvalues i).2.1
    · exact (hvalues i).2.2
  refine ⟨hvertex,?_⟩
  intro l hl d e hde hface
  obtain ⟨i,hi⟩ := hcomplete l hl d e hde hface
  have hfacei : cellFace cell l = segment ℝ (a i) (b i) := by
    simpa only [hi] using (hframe i).2.2
  have hFaceTri : cellFace cell l ⊆ convexHull ℝ {c,a i,b i} := by
    rw [hfacei]
    exact segment_subset_convexHull (by simp) (by simp)
  have hend := closedCell_face_segment_endpoints_extreme cell l hl d e hface
  have hdFace : d ∈ cellFace cell l := hface.symm ▸ left_mem_segment ℝ d e
  have heFace : e ∈ cellFace cell l := hface.symm ▸ right_mem_segment ℝ d e
  refine ⟨f i,?_,?_,?_⟩
  · exact (hpiece i ⟨d,hend.1.1⟩ (hFaceTri hdFace)).symm.trans (hvertex d hend.1)
  · exact (hpiece i ⟨e,hend.2.1⟩ (hFaceTri heFace)).symm.trans (hvertex e hend.2)
  · intro x hx
    exact hpiece i x (hFaceTri hx)


private theorem finiteCell_facewiseHomeomorph (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ H : closedCell cell ≃ₜ closedCell (cell.map (deformLine φ)),
          (∀ v (hv : v ∈ (closedCell cell).extremePoints ℝ),
            (H ⟨v,hv.1⟩ : Plane) = deformPoint φ v) ∧
          (∀ l ∈ cell, ∀ a b : Plane, a ≠ b → cellFace cell l = segment ℝ a b →
            ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
              ∀ x : closedCell cell, x.val ∈ cellFace cell l → (H x : Plane) = g x.val) := by
  obtain ⟨I,a,b,hframe,hsource,hcomplete,F,ε,hε,hhomeo⟩ :=
    finiteCell_fanHomeomorph cell hcompact c hc
  refine ⟨F,ε,hε,?_⟩
  intro φ hφ
  obtain ⟨H,f,hvalues,hpiece⟩ := hhomeo φ hφ
  exact ⟨H,fanHomeomorph_facewise cell c I a b hframe hsource hcomplete φ H f hvalues hpiece⟩

/-- An affine piece preserves a weak half-plane's sign on its filled finite hull if
 the vertex signs agree. Zero faces and strict interiors are both included. -/
private theorem affineMap_preserves_line_sign_on_convexHull
    (l m : RationalLine) (f : Plane →ᵃ[ℝ] Plane) (V : Set Plane)
    (hV : ∀ v ∈ V, l.eval v ≤ 0 ∧ Real.sign (m.eval (f v)) = Real.sign (l.eval v)) :
    ∀ x ∈ convexHull ℝ V, Real.sign (m.eval (f x)) = Real.sign (l.eval x) := by
  let E : Set Plane := {x | l.eval x ≤ 0 ∧ m.eval (f x) ≤ 0 ∧
    (l.eval x = 0 ↔ m.eval (f x) = 0)}
  have hVE : V ⊆ E := by
    intro v hv
    obtain ⟨hle,hsgn⟩ := hV v hv
    have hzero : l.eval v = 0 ↔ m.eval (f v) = 0 := by
      constructor
      · intro hz
        apply Real.sign_eq_zero_iff.mp
        rw [hsgn,hz,Real.sign_zero]
      · intro hz
        apply Real.sign_eq_zero_iff.mp
        rw [← hsgn,hz,Real.sign_zero]
    refine ⟨hle, ?_, hzero⟩
    by_cases hz : l.eval v = 0
    · rw [hzero.mp hz]
    · have hneg : l.eval v < 0 := lt_of_le_of_ne hle hz
      by_contra h
      have htpos : 0 < m.eval (f v) := lt_of_not_ge h
      rw [Real.sign_of_pos htpos, Real.sign_of_neg hneg] at hsgn
      norm_num at hsgn
  have hEconvex : Convex ℝ E := by
    intro x hx y hy r s hr hs hrs
    obtain ⟨hx₁,hx₂,hxzero⟩ := hx
    obtain ⟨hy₁,hy₂,hyzero⟩ := hy
    have hsource := lineEval_affine l x y r s
    have htarget := lineEval_affine m (f x) (f y) r s
    rw [show r+s-1=0 by linarith, zero_mul, add_zero] at hsource htarget
    have hformula : m.eval (f (r • x+s • y)) =
        r*m.eval (f x)+s*m.eval (f y) := by
      rw [Convex.combo_affine_apply hrs]
      exact htarget
    change l.eval (r • x+s • y) ≤ 0 ∧ m.eval (f (r • x+s • y)) ≤ 0 ∧ _
    rw [hsource,hformula]
    have hs₁ := mul_nonpos_of_nonneg_of_nonpos hr hx₁
    have hs₂ := mul_nonpos_of_nonneg_of_nonpos hs hy₁
    have ht₁ := mul_nonpos_of_nonneg_of_nonpos hr hx₂
    have ht₂ := mul_nonpos_of_nonneg_of_nonpos hs hy₂
    refine ⟨add_nonpos hs₁ hs₂,add_nonpos ht₁ ht₂,?_⟩
    constructor
    · intro hsum
      have hxr : r*l.eval x = 0 := by linarith
      have hys : s*l.eval y = 0 := by linarith
      have hxr' : r*m.eval (f x) = 0 :=
        mul_eq_zero.mpr ((mul_eq_zero.mp hxr).imp id hxzero.mp)
      have hys' : s*m.eval (f y) = 0 :=
        mul_eq_zero.mpr ((mul_eq_zero.mp hys).imp id hyzero.mp)
      rw [hxr',hys',add_zero]
    · intro hsum
      have hxr : r*m.eval (f x) = 0 := by linarith
      have hys : s*m.eval (f y) = 0 := by linarith
      have hxr' : r*l.eval x = 0 :=
        mul_eq_zero.mpr ((mul_eq_zero.mp hxr).imp id hxzero.mpr)
      have hys' : s*l.eval y = 0 :=
        mul_eq_zero.mpr ((mul_eq_zero.mp hys).imp id hyzero.mpr)
      rw [hxr',hys',add_zero]
  intro x hx
  obtain ⟨hle,hφle,hzero⟩ := convexHull_min hVE hEconvex hx
  by_cases hz : l.eval x = 0
  · rw [hz,hzero.mp hz]
  · have hneg : l.eval x < 0 := lt_of_le_of_ne hle hz
    have hφzero : m.eval (f x) ≠ 0 := fun h => hz (hzero.mpr h)
    have hφneg : m.eval (f x) < 0 := lt_of_le_of_ne hφle hφzero
    rw [Real.sign_of_neg hneg,Real.sign_of_neg hφneg]

private theorem fanHomeomorph_preserves_cellLineSigns (cell : List RationalLine)
    (c : Plane) (hc : c ∈ openCell cell) (I : Finset RationalLine)
    (a b : {l // l ∈ I} → Plane)
    (hframe : ∀ i, i.1 ∈ cell ∧ a i ≠ b i ∧ cellFace cell i.1 = segment ℝ (a i) (b i))
    (hsource : (⋃ i, convexHull ℝ {c,a i,b i}) = closedCell cell)
    (φ : ℝ →ₗ[ℚ] ℚ) (H : closedCell cell ≃ₜ closedCell (cell.map (deformLine φ)))
    (f : {l // l ∈ I} → Plane ≃ᵃ[ℝ] Plane)
    (hvalues : ∀ i, f i c = deformPoint φ c ∧ f i (a i) = deformPoint φ (a i) ∧
      f i (b i) = deformPoint φ (b i))
    (hpiece : ∀ i (x : closedCell cell), x.val ∈ convexHull ℝ {c,a i,b i} →
      (H x : Plane) = f i x.val)
    (hcφ : deformPoint φ c ∈ openCell (cell.map (deformLine φ)))
    (hsign : ∀ v ∈ (closedCell cell).extremePoints ℝ, ∀ l ∈ cell,
      Real.sign ((deformLine φ l).eval (deformPoint φ v)) = Real.sign (l.eval v)) :
    ∀ l ∈ cell, ∀ x : closedCell cell,
      Real.sign ((deformLine φ l).eval (H x : Plane)) = Real.sign (l.eval x.val) := by
  intro l hl x
  have hxUnion : x.val ∈ ⋃ i, convexHull ℝ {c,a i,b i} := by
    rw [hsource]
    exact x.property
  obtain ⟨i,hxi⟩ := Set.mem_iUnion.mp hxUnion
  rw [hpiece i x hxi]
  apply affineMap_preserves_line_sign_on_convexHull l (deformLine φ l)
    (f i).toAffineMap {c,a i,b i} ?_ x.val hxi
  intro v hv
  have hend := closedCell_face_segment_endpoints_extreme cell i.1 (hframe i).1
    (a i) (b i) (hframe i).2.2
  simp only [mem_insert_iff,mem_singleton_iff] at hv
  rcases hv with rfl | rfl | rfl
  · refine ⟨(hc l hl).le,?_⟩
    change Real.sign ((deformLine φ l).eval (f i v)) = Real.sign (l.eval v)
    rw [(hvalues i).1,Real.sign_of_neg (hc l hl),
      Real.sign_of_neg (hcφ _ (List.mem_map.mpr ⟨l,hl,rfl⟩))]
  · refine ⟨hend.1.1 l hl,?_⟩
    change Real.sign ((deformLine φ l).eval (f i (a i))) = Real.sign (l.eval (a i))
    rw [(hvalues i).2.1]
    exact hsign (a i) hend.1 l hl
  · refine ⟨hend.2.1 l hl,?_⟩
    change Real.sign ((deformLine φ l).eval (f i (b i))) = Real.sign (l.eval (b i))
    rw [(hvalues i).2.2]
    exact hsign (b i) hend.2 l hl

private theorem negateLine_negateLine (l : RationalLine) : negateLine (negateLine l) = l := by
  cases l with
  | mk n b => cases n with
    | mk x y hn => simp [negateLine]

private theorem signedCodes_opposite (L : List RationalLine) :
    ∀ C ∈ signedCodes L, ∀ D ∈ signedCodes L, C ≠ D →
      ∃ l ∈ C, negateLine l ∈ D := by
  induction L with
  | nil =>
      intro C hC D hD hne
      simp only [signedCodes, List.mem_singleton] at hC hD
      exact False.elim (hne (hC.trans hD.symm))
  | cons k L ih =>
      intro C hC D hD hne
      simp only [signedCodes, List.mem_append, List.mem_map] at hC hD
      rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩ <;>
        rcases hD with ⟨D', hD', rfl⟩ | ⟨D', hD', rfl⟩
      · obtain ⟨l, hlC, hlD⟩ := ih C' hC' D' hD' (fun h => hne (congrArg (List.cons k) h))
        exact ⟨l, List.mem_cons_of_mem k hlC, List.mem_cons_of_mem k hlD⟩
      · exact ⟨k, List.mem_cons_self, by simp⟩
      · exact ⟨negateLine k, List.mem_cons_self, by simp [negateLine_negateLine]⟩
      · obtain ⟨l, hlC, hlD⟩ := ih C' hC' D' hD'
          (fun h => hne (congrArg (List.cons (negateLine k)) h))
        exact ⟨l, List.mem_cons_of_mem (negateLine k) hlC,
          List.mem_cons_of_mem (negateLine k) hlD⟩

private theorem signedCodes_literals (L : List RationalLine) :
    ∀ C ∈ signedCodes L, ∀ k ∈ C, ∃ n ∈ L, k = n ∨ k = negateLine n := by
  induction L with
  | nil =>
      intro C hC k hk
      simp only [signedCodes, List.mem_singleton] at hC
      subst C
      simp at hk
  | cons n L ih =>
      intro C hC k hk
      simp only [signedCodes, List.mem_append, List.mem_map] at hC
      rcases hC with ⟨C', hC', rfl⟩ | ⟨C', hC', rfl⟩
      · rcases List.mem_cons.mp hk with hhead | hk
        · exact ⟨n, by simp, Or.inl hhead⟩
        · obtain ⟨m, hm, hkm⟩ := ih C' hC' k hk
          exact ⟨m, by simp [hm], hkm⟩
      · rcases List.mem_cons.mp hk with hhead | hk
        · exact ⟨n, by simp, Or.inr hhead⟩
        · obtain ⟨m, hm, hkm⟩ := ih C' hC' k hk
          exact ⟨m, by simp [hm], hkm⟩


private theorem line_zero_iff_of_two_zeros (l m : RationalLine) (p q : Plane)
    (hpq : p ≠ q) (hlp : l.eval p = 0) (hlq : l.eval q = 0)
    (hmp : m.eval p = 0) (hmq : m.eval q = 0) :
    ∀ z, l.eval z = 0 ↔ m.eval z = 0 := by
  have hdet : l.normal.x*m.normal.y-l.normal.y*m.normal.x = 0 := by
    by_contra h
    exact hpq (common_zero_unique l m h p q hlp hlq hmp hmq)
  obtain ⟨r,hr,hrule⟩ := lineEval_parallel_eq l m hdet p hlp hmp
  intro z
  rw [hrule z,mul_eq_zero]
  simp [hr]

/-- Distinct strict signed chambers with a one-dimensional common intersection share the
entire common active face, not just a ray or an oriented supporting line. -/
private theorem signedCells_common_whole_face
    (L C D : List RationalLine) (hC : C ∈ signedCodes L) (hD : D ∈ signedCodes L)
    (hne : C ≠ D) (cC cD p q : Plane) (hpq : p ≠ q)
    (_hcC : ∀ l ∈ C, l.eval cC < 0) (_hcD : ∀ l ∈ D, l.eval cD < 0)
    (hp : p ∈ closedCell C ∩ closedCell D) (hq : q ∈ closedCell C ∩ closedCell D) :
    ∃ l ∈ C, ∃ m ∈ D,
      closedCell C ∩ closedCell D = cellFace C l ∧
      closedCell C ∩ closedCell D = cellFace D m := by
  obtain ⟨l, hlC, hlD⟩ := signedCodes_opposite L C hC D hD hne
  have hzeroL (z : Plane) (hz : z ∈ closedCell C ∩ closedCell D) : l.eval z = 0 := by
    have h₁ := hz.1 l hlC
    have h₂ := hz.2 (negateLine l) hlD
    rw [negateLine_eval] at h₂
    exact le_antisymm h₁ (by linarith)
  have hlp : l.eval p = 0 := hzeroL p hp
  have hlq : l.eval q = 0 := hzeroL q hq
  have hconflict (n : RationalLine) (hnC : n ∈ C)
      (hnD : negateLine n ∈ D) (z : Plane)
      (hz : z ∈ closedCell C ∩ closedCell D) : n.eval z = 0 := by
    have h₁ := hz.1 n hnC
    have h₂ := hz.2 (negateLine n) hnD
    rw [negateLine_eval] at h₂
    exact le_antisymm h₁ (by linarith)
  have hconflict' (n : RationalLine) (hnC : negateLine n ∈ C)
      (hnD : n ∈ D) (z : Plane)
      (hz : z ∈ closedCell C ∩ closedCell D) : n.eval z = 0 := by
    have h₁ := hz.1 (negateLine n) hnC
    have h₂ := hz.2 n hnD
    rw [negateLine_eval] at h₁
    exact le_antisymm h₂ (by linarith)
  have hconflict_p (n : RationalLine) (hnC : n ∈ C) (hnD : negateLine n ∈ D) :
      n.eval p = 0 := hconflict n hnC hnD p hp
  have hconflict_q (n : RationalLine) (hnC : n ∈ C) (hnD : negateLine n ∈ D) :
      n.eval q = 0 := hconflict n hnC hnD q hq
  have hconflict'_p (n : RationalLine) (hnC : negateLine n ∈ C) (hnD : n ∈ D) :
      n.eval p = 0 := hconflict' n hnC hnD p hp
  have hconflict'_q (n : RationalLine) (hnC : negateLine n ∈ C) (hnD : n ∈ D) :
      n.eval q = 0 := hconflict' n hnC hnD q hq
  have hfaceC : cellFace C l = closedCell C ∩ closedCell D := by
    apply subset_antisymm
    · intro z hz
      refine ⟨hz.1, ?_⟩
      intro j hj
      obtain ⟨n, hn, hjorient⟩ := signedCodes_literals L D hD j hj
      have hCorient := signedCodes_has_each_line L C hC n hn
      rcases hjorient with hjn | hjneg
      · rw [hjn] at hj ⊢
        rcases hCorient with hnC | hnegC
        · exact hz.1 n hnC
        · have hnp : n.eval p = 0 := by
            exact hconflict'_p n hnegC hj
          have hnq : n.eval q = 0 := hconflict'_q n hnegC hj
          have hzero := line_zero_iff_of_two_zeros l n p q hpq hlp hlq hnp hnq
          exact ((hzero z).mp hz.2).le
      · rw [hjneg] at hj ⊢
        rcases hCorient with hnC | hnegC
        · have hnp := hconflict_p n hnC hj
          have hnq := hconflict_q n hnC hj
          have hzero := line_zero_iff_of_two_zeros l n p q hpq hlp hlq hnp hnq
          have hnz : n.eval z = 0 := hzero z |>.mp hz.2
          rw [negateLine_eval]
          linarith
        · exact hz.1 (negateLine n) hnegC
    · intro z hz
      exact ⟨hz.1, hzeroL z hz⟩
  have hfaceD : cellFace D (negateLine l) = closedCell C ∩ closedCell D := by
    apply subset_antisymm
    · intro z hz
      refine ⟨?_, hz.1⟩
      intro j hj
      obtain ⟨n, hn, hjorient⟩ := signedCodes_literals L C hC j hj
      have hDorient := signedCodes_has_each_line L D hD n hn
      rcases hjorient with hjn | hjneg
      · rw [hjn] at hj ⊢
        rcases hDorient with hnD | hnegD
        · exact hz.1 n hnD
        · have hnp := hconflict_p n hj hnegD
          have hnq := hconflict_q n hj hnegD
          have hzero := line_zero_iff_of_two_zeros l n p q hpq hlp hlq hnp hnq
          have hzline : (negateLine l).eval z = 0 := hz.2
          rw [negateLine_eval] at hzline
          exact ((hzero z).mp (by linarith)).le
      · rw [hjneg] at hj ⊢
        rcases hDorient with hnD | hnegD
        · have hnp := hconflict'_p n hj hnD
          have hnq := hconflict'_q n hj hnD
          have hzero := line_zero_iff_of_two_zeros l n p q hpq hlp hlq hnp hnq
          have hzline : (negateLine l).eval z = 0 := hz.2
          rw [negateLine_eval] at hzline
          have hnz : n.eval z = 0 := (hzero z).mp (by linarith)
          rw [negateLine_eval]
          linarith
        · exact hz.1 (negateLine n) hnegD
    · intro z hz
      refine ⟨hz.2, ?_⟩
      change (negateLine l).eval z = 0
      rw [negateLine_eval]
      have hz0 := hzeroL z hz
      linarith
  exact ⟨l, hlC, negateLine l, hlD, hfaceC.symm, hfaceD.symm⟩


private theorem signedCell_intersection_isExtreme (L C D : List RationalLine)
    (hC : C ∈ signedCodes L) (hD : D ∈ signedCodes L) :
    IsExtreme ℝ (closedCell C) (closedCell C ∩ closedCell D) ∧
    IsExtreme ℝ (closedCell D) (closedCell C ∩ closedCell D) := by
  have hleft (A B : List RationalLine) (hA : A ∈ signedCodes L)
      (hB : B ∈ signedCodes L) :
      IsExtreme ℝ (closedCell A) (closedCell A ∩ closedCell B) := by
    refine ⟨inter_subset_left, ?_⟩
    intro y hy z hz x hx hxopen
    obtain ⟨r, s, hr, hs, hrsum, hpoint⟩ := hxopen
    have hcombo (k : RationalLine) :
        k.eval (r • y + s • z) = r * k.eval y + s * k.eval z :=
      lineEval_combo k y z r s hrsum
    have endpoint_in_B (w v : Plane) (hwA : w ∈ closedCell A)
        (hvA : v ∈ closedCell A) (u t : ℝ) (hu : 0 < u) (ht : 0 ≤ t)
        (hutsum : u + t = 1) (hpoint' : u • w + t • v = x) :
        w ∈ closedCell B := by
      intro k hkB
      obtain ⟨n, hn, hsign⟩ := signedCodes_literals L B hB k hkB
      have hAsign := signedCodes_has_each_line L A hA n hn
      rcases hsign with hpos | hneg
      · rw [hpos] at hkB ⊢
        rcases hAsign with hnA | hnegA
        · exact hwA n hnA
        · have hxzero : n.eval x = 0 := by
            have hxc := hx.1 (negateLine n) hnegA
            have hxd := hx.2 n hkB
            rw [negateLine_eval] at hxc
            exact le_antisymm hxd (by linarith)
          have hny : 0 ≤ n.eval w := by
            have hineq := hwA (negateLine n) hnegA
            rw [negateLine_eval] at hineq
            linarith
          have hnv : 0 ≤ n.eval v := by
            have hineq := hvA (negateLine n) hnegA
            rw [negateLine_eval] at hineq
            linarith
          have heq : u * n.eval w + t * n.eval v = 0 := by
            have he := lineEval_combo n w v u t hutsum
            rw [hpoint', hxzero] at he
            exact he.symm
          have hwzero : n.eval w = 0 := by nlinarith
          rw [hwzero]
      · rw [hneg] at hkB ⊢
        rcases hAsign with hnA | hnegA
        · have hxzero : n.eval x = 0 := by
            have hxc := hx.1 n hnA
            have hxd := hx.2 (negateLine n) hkB
            rw [negateLine_eval] at hxd
            exact le_antisymm hxc (by linarith)
          have hny : n.eval w ≤ 0 := hwA n hnA
          have hnv : n.eval v ≤ 0 := hvA n hnA
          have heq : u * n.eval w + t * n.eval v = 0 := by
            have he := lineEval_combo n w v u t hutsum
            rw [hpoint', hxzero] at he
            exact he.symm
          have hwzero : n.eval w = 0 := by nlinarith
          rw [negateLine_eval, hwzero]
          norm_num
        · exact hwA (negateLine n) hnegA
    have hyB := endpoint_in_B y z hy hz r s hr hs.le hrsum hpoint
    exact ⟨hy, hyB⟩
  exact ⟨hleft C D hC hD, by simpa [inter_comm] using hleft D C hD hC⟩

private theorem finiteCell_signedFacewiseHomeomorph (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (c : Plane) (hc : c ∈ openCell cell) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ H : closedCell cell ≃ₜ closedCell (cell.map (deformLine φ)),
          (∀ v (hv : v ∈ (closedCell cell).extremePoints ℝ),
            (H ⟨v,hv.1⟩ : Plane) = deformPoint φ v) ∧
          (∀ l ∈ cell, ∀ a b : Plane, a ≠ b → cellFace cell l = segment ℝ a b →
            ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
              ∀ x : closedCell cell, x.val ∈ cellFace cell l → (H x : Plane) = g x.val) ∧
          (∀ l ∈ cell, ∀ x : closedCell cell,
            Real.sign ((deformLine φ l).eval (H x : Plane)) = Real.sign (l.eval x.val)) := by
  obtain ⟨I,a,b,hframe,hsource,hcomplete,F₁,ε₁,hε₁,hhomeo⟩ :=
    finiteCell_fanHomeomorph cell hcompact c hc
  obtain ⟨F₂,ε₂,hε₂,hvertexSign⟩ := finiteCell_vertexSignTests cell
  obtain ⟨F₃,ε₃,hε₃,hcenter⟩ := finiteCell_strictPointTests cell c hc
  refine ⟨(F₁ ∪ F₂) ∪ F₃,min (min ε₁ ε₂) ε₃,lt_min (lt_min hε₁ hε₂) hε₃,?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_left _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_right _ _))
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto) (min_le_right _ _)
  obtain ⟨H,f,hvalues,hpiece⟩ := hhomeo φ hφ₁
  obtain ⟨hvertex,hface⟩ := fanHomeomorph_facewise cell c I a b hframe hsource hcomplete
    φ H f hvalues hpiece
  exact ⟨H,hvertex,hface,fanHomeomorph_preserves_cellLineSigns cell c hc I a b hframe hsource
    φ H f hvalues hpiece (hcenter φ hφ₃) (hvertexSign φ hφ₂)⟩

private theorem signedCodes_positive_prefix (A L : List RationalLine) :
    ∀ C ∈ signedCodes L, A ++ C ∈ signedCodes (A ++ L) := by
  induction A with
  | nil => simp
  | cons l A ih =>
    intro C hC
    change l :: (A ++ C) ∈
      (signedCodes (A ++ L)).map (fun D => l :: D) ++
        (signedCodes (A ++ L)).map (fun D => negateLine l :: D)
    exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨A ++ C,ih C hC,rfl⟩))

private theorem signedFacewiseHomeomorphs_overlap
    (L C D : List RationalLine) (hC : C ∈ signedCodes L) (hD : D ∈ signedCodes L)
    (hne : C ≠ D) (hcompact : IsCompact (closedCell C))
    (c d : Plane) (hc : c ∈ openCell C) (hd : d ∈ openCell D)
    (φ : ℝ →ₗ[ℚ] ℚ)
    (H : closedCell C ≃ₜ closedCell (C.map (deformLine φ)))
    (K : closedCell D ≃ₜ closedCell (D.map (deformLine φ)))
    (hHv : ∀ v (hv : v ∈ (closedCell C).extremePoints ℝ),
      (H ⟨v,hv.1⟩ : Plane) = deformPoint φ v)
    (hKv : ∀ v (hv : v ∈ (closedCell D).extremePoints ℝ),
      (K ⟨v,hv.1⟩ : Plane) = deformPoint φ v)
    (hHf : ∀ l ∈ C, ∀ a b : Plane, a ≠ b → cellFace C l = segment ℝ a b →
      ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
        ∀ x : closedCell C, x.val ∈ cellFace C l → (H x : Plane) = g x.val)
    (hKf : ∀ l ∈ D, ∀ a b : Plane, a ≠ b → cellFace D l = segment ℝ a b →
      ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
        ∀ x : closedCell D, x.val ∈ cellFace D l → (K x : Plane) = g x.val)
    (htarget : closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)) =
      convexHull ℝ (deformPoint φ '' (closedCell C ∩ closedCell D).extremePoints ℝ)) :
    (∀ x (hx : x ∈ closedCell C ∩ closedCell D),
      (H ⟨x,hx.1⟩ : Plane) = (K ⟨x,hx.2⟩ : Plane)) ∧
    (∀ y (_hy : y ∈ closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ))),
      ∃ x, ∃ hx : x ∈ closedCell C ∩ closedCell D,
        (H ⟨x,hx.1⟩ : Plane) = y ∧ (K ⟨x,hx.2⟩ : Plane) = y) := by
  classical
  let E := closedCell C ∩ closedCell D
  obtain ⟨hEC,hED⟩ := signedCell_intersection_isExtreme L C D hC hD
  by_cases htwo : ∃ p ∈ E, ∃ q ∈ E, p ≠ q
  · obtain ⟨p,hp,q,hq,hpq⟩ := htwo
    obtain ⟨l,hl,m,hm,hfaceC,hfaceD⟩ :=
      signedCells_common_whole_face L C D hC hD hne c d p q hpq hc hd hp hq
    obtain ⟨a,b,hab⟩ := cellFace_eq_segment C l hcompact ⟨p,hfaceC ▸ hp⟩
    have habne : a ≠ b := by
      intro heq
      have hp' : p ∈ segment ℝ a b := hab ▸ (hfaceC ▸ hp)
      have hq' : q ∈ segment ℝ a b := hab ▸ (hfaceC ▸ hq)
      have hpa : p = a := by simpa [heq] using hp'
      have hqa : q = a := by simpa [heq] using hq'
      exact hpq (hpa.trans hqa.symm)
    have hDab : cellFace D m = segment ℝ a b := hfaceD.symm.trans (hfaceC.trans hab)
    obtain ⟨g,hga,hgb,hg⟩ := hHf l hl a b habne hab
    obtain ⟨k,hka,hkb,hk⟩ := hKf m hm a b habne hDab
    have hagree : ∀ x ∈ E, g x = k x := by
      intro x hx
      apply affineMaps_agree_on_convexHull g.toAffineMap k.toAffineMap {a,b}
        (by intro v hv; rcases hv with rfl | hv; exact hga.trans hka.symm
            have hv' : v = b := hv; subst v; exact hgb.trans hkb.symm) x
      rw [convexHull_pair]
      exact hab ▸ (hfaceC ▸ hx)
    have hforward : ∀ x (hx : x ∈ E),
        (H ⟨x,hx.1⟩ : Plane) = (K ⟨x,hx.2⟩ : Plane) := by
      intro x hx
      exact (hg ⟨x,hx.1⟩ (hfaceC ▸ hx)).trans
        ((hagree x hx).trans (hk ⟨x,hx.2⟩ (hfaceD ▸ hx)).symm)
    have hfinite : (E.extremePoints ℝ).Finite :=
      (closedCell_extremePoints_finite C).subset hEC.extremePoints_subset_extremePoints
    have hKM := closure_convexHull_extremePoints
      (hcompact.inter_right (closedCell_isClosed D)) ((closedCell_convex C).inter (closedCell_convex D))
    have hsource : E = convexHull ℝ (E.extremePoints ℝ) := by
      rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at hKM
      exact hKM.symm
    have himage : g '' E = closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)) := by
      change g.toAffineMap '' E = _
      rw [htarget]
      change g.toAffineMap '' E = convexHull ℝ (deformPoint φ '' E.extremePoints ℝ)
      conv_lhs => rw [hsource]
      rw [AffineMap.image_convexHull]
      congr 1
      apply Set.image_congr
      intro v hv
      exact (hg ⟨v,hv.1.1⟩ (hfaceC ▸ hv.1)).symm.trans
        (hHv v (hEC.extremePoints_subset_extremePoints hv))
    refine ⟨hforward,?_⟩
    intro y hy
    obtain ⟨x,hx,hxy⟩ := himage.symm ▸ hy
    have hHx : (H ⟨x,hx.1⟩ : Plane) = y := (hg ⟨x,hx.1⟩ (hfaceC ▸ hx)).trans hxy
    exact ⟨x,hx,hHx,(hforward x hx).symm.trans hHx⟩
  · by_cases hnonempty : E.Nonempty
    · obtain ⟨p,hp⟩ := hnonempty
      have hsingleton : E = {p} := by
        ext x
        constructor
        · intro hx
          have hxp : x = p := by by_contra h; exact htwo ⟨x,hx,p,hp,h⟩
          exact hxp
        · intro hx
          have hxp : x = p := hx
          simpa [hxp] using hp
      have hpExt : p ∈ E.extremePoints ℝ := by rw [hsingleton,extremePoints_singleton]; rfl
      have hHp := hHv p (hEC.extremePoints_subset_extremePoints hpExt)
      have hKp := hKv p (hED.extremePoints_subset_extremePoints hpExt)
      have ht : closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)) =
          {deformPoint φ p} := by
        rw [htarget]
        change convexHull ℝ (deformPoint φ '' E.extremePoints ℝ) = _
        rw [hsingleton,extremePoints_singleton,Set.image_singleton,convexHull_singleton]
      constructor
      · intro x hx
        have hxp : x = p := by
          change x ∈ E at hx
          rw [hsingleton] at hx
          exact hx
        subst x
        exact hHp.trans hKp.symm
      · intro y hy
        have hyp : y = deformPoint φ p := by rw [ht] at hy; exact hy
        exact ⟨p,hp,hHp.trans hyp.symm,hKp.trans hyp.symm⟩
    · have hempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hnonempty
      have ht : closedCell (C.map (deformLine φ)) ∩ closedCell (D.map (deformLine φ)) = ∅ := by
        rw [htarget]
        change convexHull ℝ (deformPoint φ '' E.extremePoints ℝ) = _
        rw [hempty,extremePoints_empty,Set.image_empty,convexHull_empty]
      constructor
      · intro x hx
        change x ∈ E at hx
        rw [hempty] at hx
        exact hx.elim
      · intro y hy
        rw [ht] at hy
        exact hy.elim

private theorem fullSquareCodes_signed (R : ℚ) (L C : List RationalLine)
    (hC : C ∈ fullSquareCodes R L) : C ∈ signedCodes (squareLines R ++ L) := by
  obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hC
  exact signedCodes_positive_prefix _ _ D (List.mem_filter.mp hD).1

private theorem finiteSquare_signedHomeomorph (R : ℚ) (hR : 0 < R) (L : List RationalLine) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ H : closedCell (squareLines R) ≃ₜ closedCell (squareLines R),
          (∀ l ∈ squareLines R ++ L, ∀ x : closedCell (squareLines R),
            Real.sign ((deformLine φ l).eval (H x : Plane)) = Real.sign (l.eval x.val)) ∧
          (∀ C ∈ fullSquareCodes R L,
            ∃ K : closedCell C ≃ₜ closedCell (C.map (deformLine φ)),
              (∀ v (hv : v ∈ (closedCell C).extremePoints ℝ),
                (K ⟨v,hv.1⟩ : Plane) = deformPoint φ v) ∧
              (∀ l ∈ C, ∀ a b : Plane, a ≠ b → cellFace C l = segment ℝ a b →
                ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
                  ∀ x : closedCell C, x.val ∈ cellFace C l → (K x : Plane) = g x.val) ∧
              (∀ l ∈ C, ∀ x : closedCell C,
                Real.sign ((deformLine φ l).eval (K x : Plane)) = Real.sign (l.eval x.val)) ∧
              (∀ x : closedCell (squareLines R), ∀ hx : x.val ∈ closedCell C,
                (H x : Plane) = (K ⟨x.val,hx⟩ : Plane))) := by
  classical
  let P := fullSquareCodes R L
  let I := {C // C ∈ P.toFinset}
  have hmem (i : I) : i.val ∈ P := List.mem_toFinset.mp i.property
  have hdata (i : I) := fullSquareCodes_cellData R L i.val (hmem i)
  choose centre hcentre using fun i : I => (hdata i).2
  have hchoices (i : I) := finiteCell_signedFacewiseHomeomorph i.val (hdata i).1
    (centre i) (hcentre i)
  choose tests threshold hpos hlocal using hchoices
  obtain ⟨F₁,ε₁,hε₁,hallLocal⟩ := unify_finiteApproximationTests tests threshold hpos
  have htargetCompact (i : I) (φ : ℝ →ₗ[ℚ] ℚ) :
      IsCompact (closedCell (i.val.map (deformLine φ))) := by
    rw [closedCell_map_eq_shiftedCell]
    exact shiftedCell_isCompact_of_compact_same_normals i.val (hdata i).1
      ⟨centre i,fun l hl => (hcentre i l hl).le⟩ _
  have hpairChoices (ij : I × I) := finiteCell_intersection_transport ij.1.val ij.2.val
    (fun φ _ => (htargetCompact ij.1 φ).inter_right (closedCell_isClosed _))
  choose pairTests pairThreshold hpairPos hpair using hpairChoices
  obtain ⟨F₂,ε₂,hε₂,hallPairs⟩ := unify_finiteApproximationTests pairTests pairThreshold hpairPos
  obtain ⟨F₃,ε₃,hε₃,hcoverTarget⟩ := fullSquareCodes_targetSupport R hR L
  refine ⟨(F₁ ∪ F₂) ∪ F₃,min (min ε₁ ε₂) ε₃,lt_min (lt_min hε₁ hε₂) hε₃,?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_left _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_right _ _))
  have hφ₃ : IsFiniteApproximation F₃ ε₃ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto) (min_le_right _ _)
  choose localMap hvertex hface hsign using
    fun i : I => hlocal i φ (hallLocal φ hφ₁ i)
  have hsourceSub (i : I) : closedCell i.val ⊆ closedCell (squareLines R) := by
    intro x hx
    have hxP : x ∈ polyhedralSupport P := ⟨i.val,hmem i,hx⟩
    rw [fullSquareCodes_support R hR L] at hxP
    exact hxP
  have htargetSub (i : I) : closedCell (i.val.map (deformLine φ)) ⊆
      closedCell (squareLines R) := by
    intro y hy
    have hyP : y ∈ deformedPolyhedralSupport P φ :=
      ⟨i.val.map (deformLine φ),List.mem_map.mpr ⟨i.val,hmem i,rfl⟩,hy⟩
    rw [hcoverTarget φ hφ₃] at hyP
    exact hyP
  have hsourceCover : ∀ x ∈ closedCell (squareLines R), ∃ i : I, x ∈ closedCell i.val := by
    intro x hx
    have hxP : x ∈ polyhedralSupport P := by rw [fullSquareCodes_support R hR L]; exact hx
    obtain ⟨C,hC,hxC⟩ := hxP
    exact ⟨⟨C,List.mem_toFinset.mpr hC⟩,hxC⟩
  have htargetCover : ∀ y ∈ closedCell (squareLines R),
      ∃ i : I, y ∈ closedCell (i.val.map (deformLine φ)) := by
    intro y hy
    have hyP : y ∈ deformedPolyhedralSupport P φ := by rw [hcoverTarget φ hφ₃]; exact hy
    obtain ⟨D,hD,hyD⟩ := hyP
    obtain ⟨C,hC,rfl⟩ := List.mem_map.mp hD
    exact ⟨⟨C,List.mem_toFinset.mpr hC⟩,hyD⟩
  have hcompat (i j : I) (hne : i ≠ j) := signedFacewiseHomeomorphs_overlap
    (squareLines R ++ L) i.val j.val (fullSquareCodes_signed R L i.val (hmem i))
    (fullSquareCodes_signed R L j.val (hmem j))
    (fun h => hne (Subtype.ext h)) (hdata i).1
    (centre i) (centre j) (hcentre i) (hcentre j) φ (localMap i) (localMap j)
    (hvertex i) (hvertex j) (hface i) (hface j)
    (hpair (i,j) φ (hallPairs φ hφ₂ (i,j)))
  have hforward : ∀ i j x (hxi : x ∈ closedCell i.val) (hxj : x ∈ closedCell j.val),
      (localMap i ⟨x,hxi⟩ : Plane) = (localMap j ⟨x,hxj⟩ : Plane) := by
    intro i j x hxi hxj
    by_cases hij : i = j
    · subst j; rfl
    · exact (hcompat i j hij).1 x ⟨hxi,hxj⟩
  have hinverse : ∀ i j y (hyi : y ∈ closedCell (i.val.map (deformLine φ)))
      (hyj : y ∈ closedCell (j.val.map (deformLine φ))),
      ((localMap i).symm ⟨y,hyi⟩ : Plane) = ((localMap j).symm ⟨y,hyj⟩ : Plane) := by
    intro i j y hyi hyj
    by_cases hij : i = j
    · subst j; rfl
    · obtain ⟨x,hx,hix,hjx⟩ := (hcompat i j hij).2 y ⟨hyi,hyj⟩
      have hi : (localMap i).symm ⟨y,hyi⟩ = ⟨x,hx.1⟩ := by
        apply (localMap i).injective
        simp only [Homeomorph.apply_symm_apply]
        exact Subtype.ext hix.symm
      have hj : (localMap j).symm ⟨y,hyj⟩ = ⟨x,hx.2⟩ := by
        apply (localMap j).injective
        simp only [Homeomorph.apply_symm_apply]
        exact Subtype.ext hjx.symm
      exact (congrArg Subtype.val hi).trans (congrArg Subtype.val hj).symm
  obtain ⟨H,hrestriction⟩ := finiteHomeomorphClosedCover
    (closedCell (squareLines R)) (closedCell (squareLines R))
    (fun i : I => closedCell i.val) (fun i : I => closedCell (i.val.map (deformLine φ)))
    (fun _ => closedCell_isClosed _) (fun _ => closedCell_isClosed _)
    hsourceSub htargetSub hsourceCover htargetCover localMap hforward hinverse
  refine ⟨H,?_,?_⟩
  · intro l hl x
    obtain ⟨i,hxi⟩ := hsourceCover x.val x.property
    rcases signedCodes_has_each_line (squareLines R ++ L) i.val
      (fullSquareCodes_signed R L i.val (hmem i)) l hl with hli | hnegli
    · rw [hrestriction i x hxi]
      exact hsign i l hli ⟨x.val,hxi⟩
    · have hs := hsign i (negateLine l) hnegli ⟨x.val,hxi⟩
      rw [← negateLine_deformLine,negateLine_eval,negateLine_eval,
        Real.sign_neg,Real.sign_neg] at hs
      rw [hrestriction i x hxi]
      exact neg_injective hs
  · intro C hC
    let i : I := ⟨C,List.mem_toFinset.mpr hC⟩
    exact ⟨localMap i,hvertex i,hface i,hsign i,hrestriction i⟩

private def squareExterior (R : ℚ) : Set Plane :=
  {z | (R : ℝ) ≤ max |z.re| |z.im|}

private theorem squareExterior_isClosed (R : ℚ) : IsClosed (squareExterior R) := by
  exact isClosed_le continuous_const
    ((Complex.continuous_re.abs).max (Complex.continuous_im.abs))

private theorem square_and_exterior_cover (R : ℚ) (z : Plane) :
    z ∈ closedCell (squareLines R) ∨ z ∈ squareExterior R := by
  by_cases h : (R : ℝ) ≤ max |z.re| |z.im|
  · exact Or.inr h
  · left
    apply (mem_closedCell_squareLines R z).mpr
    have hlt := lt_of_not_ge h
    have hr := lt_of_le_of_lt (le_max_left |z.re| |z.im|) hlt
    have hi := lt_of_le_of_lt (le_max_right |z.re| |z.im|) hlt
    exact ⟨abs_le.mp hr.le,abs_le.mp hi.le⟩

private theorem square_boundary_iff_active_clip (R : ℚ) (z : closedCell (squareLines R)) :
    z.val ∈ squareExterior R ↔ ∃ l ∈ squareLines R, l.eval z.val = 0 := by
  obtain ⟨hre,him⟩ := (mem_closedCell_squareLines R z.val).mp z.property
  change (R : ℝ) ≤ max |z.val.re| |z.val.im| ↔ _
  simp only [squareLines,List.mem_cons,List.not_mem_nil,or_false,exists_eq_or_imp,
    exists_eq_left,RationalLine.eval,normalEval]
  norm_num
  constructor
  · intro h
    rcases h with hr | hi
    · by_cases hs : 0 ≤ z.val.re
      · rw [abs_of_nonneg hs] at hr
        exact Or.inl (by linarith)
      · rw [abs_of_nonpos (le_of_not_ge hs)] at hr
        exact Or.inr (Or.inl (by linarith))
    · by_cases hs : 0 ≤ z.val.im
      · rw [abs_of_nonneg hs] at hi
        exact Or.inr (Or.inr (Or.inl (by linarith)))
      · rw [abs_of_nonpos (le_of_not_ge hs)] at hi
        exact Or.inr (Or.inr (Or.inr (by linarith)))
  · rintro (h | h | h | h)
    · have heq : z.val.re = R := by linarith
      exact Or.inl (by rw [heq]; exact le_abs_self _)
    · have heq : -z.val.re = R := by linarith
      exact Or.inl (heq.ge.trans (neg_le_abs _))
    · have heq : z.val.im = R := by linarith
      exact Or.inr (by rw [heq]; exact le_abs_self _)
    · have heq : -z.val.im = R := by linarith
      exact Or.inr (heq.ge.trans (neg_le_abs _))

private theorem squareHomeomorph_preserves_boundary (R : ℚ) (φ : ℝ →ₗ[ℚ] ℚ)
    (hφ : φ 1 = 1) (H : closedCell (squareLines R) ≃ₜ closedCell (squareLines R))
    (hsign : ∀ l ∈ squareLines R, ∀ x : closedCell (squareLines R),
      Real.sign ((deformLine φ l).eval (H x : Plane)) = Real.sign (l.eval x.val)) :
    ∀ x : closedCell (squareLines R),
      x.val ∈ squareExterior R ↔ (H x : Plane) ∈ squareExterior R := by
  intro x
  rw [square_boundary_iff_active_clip,square_boundary_iff_active_clip]
  have hfixed : ∀ l ∈ squareLines R, deformLine φ l = l := by
    intro l hl
    simp only [squareLines,List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;>
      simp [deformLine,normalized_map_rat φ hφ]
  constructor
  · rintro ⟨l,hl,hzero⟩
    refine ⟨l,hl,?_⟩
    have hs := hsign l hl x
    rw [hfixed l hl,hzero,Real.sign_zero] at hs
    exact Real.sign_eq_zero_iff.mp hs
  · rintro ⟨l,hl,hzero⟩
    refine ⟨l,hl,?_⟩
    have hs := hsign l hl x
    rw [hfixed l hl,hzero,Real.sign_zero] at hs
    exact Real.sign_eq_zero_iff.mp hs.symm

private theorem twoClosedCover_globalHomeomorph (S T : Set Plane)
    (hS : IsClosed S) (hT : IsClosed T) (hcover : ∀ z : Plane, z ∈ S ∨ z ∈ T)
    (H : S ≃ₜ S) (K : T ≃ₜ T)
    (hboundary : ∀ x : S, x.val ∈ T ↔ (H x : Plane) ∈ T)
    (hagree : ∀ x (hxS : x ∈ S) (hxT : x ∈ T),
      (H ⟨x,hxS⟩ : Plane) = (K ⟨x,hxT⟩ : Plane)) :
    ∃ G : Plane ≃ₜ Plane,
      (∀ x (hx : x ∈ S), G x = (H ⟨x,hx⟩ : Plane)) ∧
      (∀ x (hx : x ∈ T), G x = (K ⟨x,hx⟩ : Plane)) := by
  classical
  let C : Bool → Set Plane := fun i => if i then T else S
  let localMap : ∀ i, C i ≃ₜ C i := fun i => by cases i; exact H; exact K
  have hclosed (i : Bool) : IsClosed (C i) := by cases i; exact hS; exact hT
  have hsub (i : Bool) : C i ⊆ (Set.univ : Set Plane) := subset_univ _
  have hcover' : ∀ z ∈ (Set.univ : Set Plane), ∃ i, z ∈ C i := by
    intro z _
    rcases hcover z with hz | hz
    · exact ⟨false,hz⟩
    · exact ⟨true,hz⟩
  have hforward : ∀ i j x (hxi : x ∈ C i) (hxj : x ∈ C j),
      (localMap i ⟨x,hxi⟩ : Plane) = (localMap j ⟨x,hxj⟩ : Plane) := by
    intro i j x hxi hxj
    cases i <;> cases j
    · rfl
    · exact hagree x hxi hxj
    · exact (hagree x hxj hxi).symm
    · rfl
  have hinverseCross : ∀ y (hyS : y ∈ S) (hyT : y ∈ T),
      (H.symm ⟨y,hyS⟩ : Plane) = (K.symm ⟨y,hyT⟩ : Plane) := by
    intro y hyS hyT
    let x := H.symm ⟨y,hyS⟩
    have hxT : x.val ∈ T := (hboundary x).mpr (by simpa [x] using hyT)
    have hKx : K ⟨x.val,hxT⟩ = ⟨y,hyT⟩ := by
      apply Subtype.ext
      exact (hagree x.val x.property hxT).symm.trans
        (congrArg Subtype.val (H.apply_symm_apply ⟨y,hyS⟩))
    have hxK : K.symm ⟨y,hyT⟩ = ⟨x.val,hxT⟩ := by rw [← hKx]; exact K.symm_apply_apply _
    exact (congrArg Subtype.val hxK).symm
  have hinverse : ∀ i j y (hyi : y ∈ C i) (hyj : y ∈ C j),
      ((localMap i).symm ⟨y,hyi⟩ : Plane) = ((localMap j).symm ⟨y,hyj⟩ : Plane) := by
    intro i j y hyi hyj
    cases i <;> cases j
    · rfl
    · exact hinverseCross y hyi hyj
    · exact (hinverseCross y hyj hyi).symm
    · rfl
  obtain ⟨G,hrestriction⟩ := finiteHomeomorphClosedCover Set.univ Set.univ C C
    hclosed hclosed hsub hsub hcover' hcover' localMap hforward hinverse
  let e := Homeomorph.Set.univ Plane
  refine ⟨e.symm.trans (G.trans e),?_,?_⟩
  · intro x hx
    exact hrestriction false ⟨x,Set.mem_univ x⟩ hx
  · intro x hx
    exact hrestriction true ⟨x,Set.mem_univ x⟩ hx

private theorem finitePointSet_injective (W : Finset Plane) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        Set.InjOn (deformPoint φ) (W : Set Plane) := by
  classical
  let E := (W.product W).image (fun p => p.1.re - p.2.re) ∪
    (W.product W).image (fun p => p.1.im - p.2.im)
  obtain ⟨ε, hε, hsign⟩ := finite_scalar_signTests E
  refine ⟨E, ε, hε, ?_⟩
  intro φ hφ a ha b hb hab
  have hreφ : (φ (a.re-b.re) : ℝ) = 0 := by
    rw [map_sub, Rat.cast_sub]
    exact sub_eq_zero.mpr (by simpa [deformPoint] using congrArg Complex.re hab)
  have himφ : (φ (a.im-b.im) : ℝ) = 0 := by
    rw [map_sub, Rat.cast_sub]
    exact sub_eq_zero.mpr (by simpa [deformPoint] using congrArg Complex.im hab)
  have hreE : a.re-b.re ∈ E := Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩))
  have himE : a.im-b.im ∈ E := Finset.mem_union.mpr (Or.inr
    (Finset.mem_image.mpr ⟨(a,b), Finset.mem_product.mpr ⟨ha,hb⟩, rfl⟩))
  have hrSign := hsign φ hφ (a.re-b.re) hreE
  have hiSign := hsign φ hφ (a.im-b.im) himE
  rw [hreφ, Real.sign_zero] at hrSign
  rw [himφ, Real.sign_zero] at hiSign
  have hre : a.re-b.re = 0 := Real.sign_eq_zero_iff.mp hrSign.symm
  have him : a.im-b.im = 0 := Real.sign_eq_zero_iff.mp hiSign.symm
  exact Complex.ext (sub_eq_zero.mp hre) (sub_eq_zero.mp him)

/-- All actual nonparallel intersections are recorded in one finite set; concurrency of
their target images is the exact rational-coefficient intersection formula. -/
private theorem finiteLinePairPoints (L : Finset RationalLine) :
    ∃ W : Finset Plane, ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∃ p ∈ W, l.eval p = 0 ∧ m.eval p = 0 ∧
        (∀ z, l.eval z = 0 → m.eval z = 0 → z = p) ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, (deformLine φ l).eval (deformPoint φ p) = 0 ∧
          (deformLine φ m).eval (deformPoint φ p) = 0 := by
  classical
  let I := (L.product L).filter fun p =>
    p.1.normal.x*p.2.normal.y-p.1.normal.y*p.2.normal.x ≠ 0
  let point (i : {p // p ∈ I}) := Classical.choose
    (rationalLine_pairIntersection i.1.1 i.1.2 (Finset.mem_filter.mp i.2).2)
  refine ⟨Finset.univ.image point, ?_⟩
  intro l hl m hm hdet
  have hi : (l,m) ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hl,hm⟩,hdet⟩
  let i : {p // p ∈ I} := ⟨(l,m),hi⟩
  refine ⟨point i, Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩, ?_⟩
  exact Classical.choose_spec (rationalLine_pairIntersection l m hdet)

/-- One fixed positive integer square encloses the chosen source and target finite points.
This square is chosen before approximation, not rescaled by the exterior chart. -/
private theorem finitePointSet_integerSquare_enclosure (W : Finset Plane) :
    ∃ R : ℚ, 0 < R ∧ (∀ w ∈ W, ‖w‖ < (R : ℝ)) ∧
      ∃ F : Finset ℝ, ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F 1 φ →
        ∀ w ∈ W, ‖deformPoint φ w‖ < (R : ℝ) := by
  obtain ⟨F,B,hB,hbound⟩ := finiteDecoration_uniformImageBound W
  let S := ∑ w ∈ W, ‖w‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  obtain ⟨n,hn⟩ := exists_nat_gt (B+S+1)
  have hnpos : 0 < (n : ℝ) := by linarith
  have hRpos : 0 < (n : ℚ) := by exact_mod_cast hnpos
  refine ⟨(n : ℚ),hRpos,?_,F,?_⟩
  · intro w hw
    have hwS : ‖w‖ ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun z _ => norm_nonneg z) hw
    have hwn : ‖w‖ < (n : ℝ) := by linarith
    simpa using hwn
  · intro φ hφ w hw
    have hwb := hbound φ hφ w hw
    have hwn : ‖deformPoint φ w‖ < (n : ℝ) := by linarith
    simpa using hwn

private def markLines (v : Plane) : List RationalLine :=
  [⟨⟨1,0,by norm_num⟩,v.re⟩,⟨⟨0,1,by norm_num⟩,v.im⟩]

private def diagonalLines : List RationalLine :=
  [⟨⟨1,-1,by norm_num⟩,0⟩,⟨⟨1,1,by norm_num⟩,0⟩]

/-- Pre-box lines include marks and fixed corner rays. The later four clipping lines
are deliberately absent from this outgoing exterior label family. -/
private def augmentedArrangementLines (L : Finset RationalLine) (M : Finset Plane) : List RationalLine :=
  L.toList ++ M.toList.flatMap markLines ++ diagonalLines

private theorem deform_diagonalLines (φ : ℝ →ₗ[ℚ] ℚ) :
    diagonalLines.map (deformLine φ) = diagonalLines := by
  simp [diagonalLines,deformLine,map_zero]

private theorem markLines_common_zero (v z : Plane) :
    (∀ l ∈ markLines v, l.eval z = 0) ↔ z = v := by
  simp only [markLines,List.mem_cons,List.not_mem_nil,or_false,
    forall_eq_or_imp,forall_eq,RationalLine.eval,normalEval]
  norm_num
  constructor
  · rintro ⟨hre,him⟩
    exact Complex.ext (sub_eq_zero.mp hre) (sub_eq_zero.mp him)
  · intro h
    subst z
    exact ⟨sub_self _,sub_self _⟩

private theorem deform_markLines (φ : ℝ →ₗ[ℚ] ℚ) (v : Plane) :
    (markLines v).map (deformLine φ) = markLines (deformPoint φ v) := by
  simp [markLines,deformLine,deformPoint]

private theorem signPreservingMap_transports_marks
    (A : List RationalLine) (S : Set Plane) (φ : ℝ →ₗ[ℚ] ℚ) (H : S → Plane)
    (hsign : ∀ l ∈ A, ∀ x : S,
      Real.sign ((deformLine φ l).eval (H x)) = Real.sign (l.eval x.val))
    (v : Plane) (hv : v ∈ S) (hmarks : ∀ l ∈ markLines v, l ∈ A) :
    H ⟨v,hv⟩ = deformPoint φ v := by
  apply (markLines_common_zero (deformPoint φ v) _).mp
  intro l hl
  rw [← deform_markLines φ v] at hl
  obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hl
  have hmzero := (markLines_common_zero v v).mpr rfl m hm
  have hs := hsign m (hmarks m hm) ⟨v,hv⟩
  rw [hmzero,Real.sign_zero] at hs
  exact Real.sign_eq_zero_iff.mp hs

private theorem augmentedArrangement_integerSquare_enclosure
    (L : Finset RationalLine) (M : Finset Plane) :
    ∃ R : ℚ, 0 < R ∧ ∃ F : Finset ℝ,
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F 1 φ →
        (∀ v ∈ M, ‖v‖ < (R : ℝ) ∧ ‖deformPoint φ v‖ < (R : ℝ)) ∧
        (∀ l ∈ augmentedArrangementLines L M, ∀ m ∈ augmentedArrangementLines L M,
          l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
          (∀ p, l.eval p = 0 → m.eval p = 0 → ‖p‖ < (R : ℝ)) ∧
          (∀ q, (deformLine φ l).eval q = 0 → (deformLine φ m).eval q = 0 →
            ‖q‖ < (R : ℝ))) := by
  classical
  let A := augmentedArrangementLines L M
  obtain ⟨W,hpoints⟩ := finiteLinePairPoints A.toFinset
  obtain ⟨R,hR,hsource,F,htarget⟩ := finitePointSet_integerSquare_enclosure (W ∪ M)
  refine ⟨R,hR,F,?_⟩
  intro φ hφ
  refine ⟨?_,?_⟩
  · intro v hv
    have hv' : v ∈ W ∪ M := Finset.mem_union.mpr (Or.inr hv)
    exact ⟨hsource v hv',htarget φ hφ v hv'⟩
  · intro l hl m hm hdet
    obtain ⟨p,hp,hlp,hmp,hunique,hmap⟩ :=
      hpoints l (List.mem_toFinset.mpr hl) m (List.mem_toFinset.mpr hm) hdet
    have hp' : p ∈ W ∪ M := Finset.mem_union.mpr (Or.inl hp)
    constructor
    · intro z hlz hmz
      rw [hunique z hlz hmz]
      exact hsource p hp'
    · intro z hlz hmz
      have heq : z = deformPoint φ p := common_zero_unique
        (deformLine φ l) (deformLine φ m) hdet z (deformPoint φ p)
        hlz (hmap φ).1 hmz (hmap φ).2
      rw [heq]
      exact htarget φ hφ p hp'

namespace ExteriorFourFaces

private abbrev Plane := ℝ × ℝ

private def exterior (R : ℝ) : Set Plane :=
  {p | R ≤ max |p.1| |p.2|}

private def face (R : ℝ) (i : Fin 4) : Set Plane :=
  match i.val with
  | 0 => {p | R ≤ p.1 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}
  | 1 => {p | R ≤ p.2 ∧ -p.2 ≤ p.1 ∧ p.1 ≤ p.2}
  | 2 => {p | R ≤ -p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ -p.1}
  | 3 => {p | R ≤ -p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ -p.2}
  | _ => ∅

private abbrev FacePoint (R : ℝ) (i : Fin 4) := {p : Plane // p ∈ face R i}

private def diagonalRays : Set Plane := {p | p.1 = p.2 ∨ p.1 = -p.2}

private def affineLineFunctional (a b c : ℝ) (p : Plane) : ℝ := a * p.1 + b * p.2 + c

private theorem rightFace_convex (R : ℝ) : Convex ℝ (face R 0) := by
  rw [convex_iff_segment_subset]
  intro p hp q hq
  rw [segment_subset_iff]
  intro x y hx hy hxy
  change R ≤ p.1 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1 at hp
  change R ≤ q.1 ∧ -q.1 ≤ q.2 ∧ q.2 ≤ q.1 at hq
  change R ≤ x * p.1 + y * q.1 ∧
    -(x * p.1 + y * q.1) ≤ x * p.2 + y * q.2 ∧
      x * p.2 + y * q.2 ≤ x * p.1 + y * q.1
  refine ⟨?_, ?_, ?_⟩
  · have hle := add_le_add
      (mul_le_mul_of_nonneg_left hp.1 hx) (mul_le_mul_of_nonneg_left hq.1 hy)
    have hR : R = x * R + y * R := by rw [← add_mul, hxy]; ring
    rw [hR]
    exact hle
  · have hle := add_le_add
      (mul_le_mul_of_nonneg_left hp.2.1 hx) (mul_le_mul_of_nonneg_left hq.2.1 hy)
    nlinarith
  · have hle := add_le_add
      (mul_le_mul_of_nonneg_left hp.2.2 hx) (mul_le_mul_of_nonneg_left hq.2.2 hy)
    exact hle

private theorem affineLineFunctional_combo (a b c : ℝ) (p q : Plane)
    (x y : ℝ) (hxy : x + y = 1) :
    affineLineFunctional a b c (x • p + y • q) =
      x * affineLineFunctional a b c p + y * affineLineFunctional a b c q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp [affineLineFunctional, Prod.smul_mk]
  have hc : c = x * c + y * c := by
    calc
      c = (x + y) * c := by rw [hxy]; ring
      _ = x * c + y * c := by ring
  linear_combination hc

private theorem realSignNeg_iff (z : ℝ) (hz : z ≠ 0) :
    Real.sign z = -1 ↔ z < 0 := by
  constructor
  · intro h
    by_contra hn
    have hnonneg : 0 ≤ z := le_of_not_gt hn
    rcases hnonneg.eq_or_lt with heq | hpos
    · exact hz heq.symm
    · rw [Real.sign_of_pos hpos] at h
      norm_num at h
  · exact Real.sign_of_neg

private theorem realSignPos_iff (z : ℝ) (hz : z ≠ 0) :
    Real.sign z = 1 ↔ 0 < z := by
  constructor
  · intro h
    by_contra hn
    have hnonpos : z ≤ 0 := le_of_not_gt hn
    rcases hnonpos.eq_or_lt with heq | hneg
    · exact hz heq
    · rw [Real.sign_of_neg hneg] at h
      norm_num at h
  · exact Real.sign_of_pos

/-- A zero-free affine functional has constant sign on the actual right-face
sector. This argument is independent of the orientation or slope of its zero
line, so it includes vertical lines. -/
private theorem affineLineFunctional_sign_constant_on_rightFace {R a b c : ℝ}
    (hzero : ∀ p ∈ face R 0, affineLineFunctional a b c p ≠ 0)
    {p q : Plane} (hp : p ∈ face R 0) (hq : q ∈ face R 0) :
    Real.sign (affineLineFunctional a b c p) =
      Real.sign (affineLineFunctional a b c q) := by
  have hp0 := hzero p hp
  have hq0 := hzero q hq
  by_contra hsign
  rcases Real.sign_apply_eq_of_ne_zero _ hp0 with hpneg | hppos <;>
    rcases Real.sign_apply_eq_of_ne_zero _ hq0 with hqneg | hqpos
  · rw [hpneg, hqneg] at hsign
    exact hsign rfl
  · have hfp : affineLineFunctional a b c p < 0 :=
      (realSignNeg_iff _ hp0).mp hpneg
    have hfq : 0 < affineLineFunctional a b c q :=
      (realSignPos_iff _ hq0).mp hqpos
    let D := affineLineFunctional a b c q - affineLineFunctional a b c p
    let x := affineLineFunctional a b c q / D
    let y := -(affineLineFunctional a b c p) / D
    have hD : 0 < D := by dsimp [D]; linarith
    have hx : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (le_of_lt hfq) (le_of_lt hD)
    have hy : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (le_of_lt (neg_pos.mpr hfp)) (le_of_lt hD)
    have hxy : x + y = 1 := by
      dsimp [x, y, D]
      have hDne : affineLineFunctional a b c q - affineLineFunctional a b c p ≠ 0 := ne_of_gt hD
      field_simp [hDne]
      ring
    have hz : affineLineFunctional a b c (x • p + y • q) = 0 := by
      rw [affineLineFunctional_combo a b c p q x y hxy]
      dsimp [x, y, D]
      have hDne : affineLineFunctional a b c q - affineLineFunctional a b c p ≠ 0 := ne_of_gt hD
      field_simp [hDne]
      ring
    have hmem := (rightFace_convex R).segment_subset hp hq
      ⟨x, y, hx, hy, hxy, rfl⟩
    exact (hzero _ hmem hz).elim
  · have hfq : affineLineFunctional a b c q < 0 :=
      (realSignNeg_iff _ hq0).mp hqneg
    have hfp : 0 < affineLineFunctional a b c p :=
      (realSignPos_iff _ hp0).mp hppos
    let D := affineLineFunctional a b c p - affineLineFunctional a b c q
    let x := -(affineLineFunctional a b c q) / D
    let y := affineLineFunctional a b c p / D
    have hD : 0 < D := by dsimp [D]; linarith
    have hx : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (le_of_lt (neg_pos.mpr hfq)) (le_of_lt hD)
    have hy : 0 ≤ y := by
      dsimp [y]
      exact div_nonneg (le_of_lt hfp) (le_of_lt hD)
    have hxy : x + y = 1 := by
      dsimp [x, y, D]
      have hDne : affineLineFunctional a b c p - affineLineFunctional a b c q ≠ 0 := ne_of_gt hD
      field_simp [hDne]
      ring
    have hz : affineLineFunctional a b c (x • p + y • q) = 0 := by
      rw [affineLineFunctional_combo a b c p q x y hxy]
      dsimp [x, y, D]
      have hDne : affineLineFunctional a b c p - affineLineFunctional a b c q ≠ 0 := ne_of_gt hD
      field_simp [hDne]
      ring
    have hmem := (rightFace_convex R).segment_subset hp hq
      ⟨x, y, hx, hy, hxy, rfl⟩
    exact (hzero _ hmem hz).elim
  · rw [hppos, hqpos] at hsign
    exact hsign rfl

/-- If source and target affine line functionals are each zero-free on the
right-face sector, their signs are matched everywhere by a face homeomorphism
that fixes a common reference point where the signs agree. No continuity or
linearity of an approximation map is used here. The zero-free conditions are
intended to be discharged from the coordinator's outgoing-graph
classification, not assumed as arrangement data. -/
private theorem faceHomeomorph_preserves_zeroFree_affine_sign {R : ℝ}
    (H : FacePoint R 0 ≃ₜ FacePoint R 0)
    (a₁ b₁ c₁ a₂ b₂ c₂ : ℝ)
    (hzero₁ : ∀ p ∈ face R 0, affineLineFunctional a₁ b₁ c₁ p ≠ 0)
    (hzero₂ : ∀ p ∈ face R 0, affineLineFunctional a₂ b₂ c₂ p ≠ 0)
    (p₀ : Plane) (hp₀ : p₀ ∈ face R 0)
    (hfix : (H ⟨p₀, hp₀⟩).1 = p₀)
    (hanchor : Real.sign (affineLineFunctional a₂ b₂ c₂ p₀) =
      Real.sign (affineLineFunctional a₁ b₁ c₁ p₀))
    (p : FacePoint R 0) :
    Real.sign (affineLineFunctional a₂ b₂ c₂ (H p).1) =
      Real.sign (affineLineFunctional a₁ b₁ c₁ p.1) := by
  have hs₁ := affineLineFunctional_sign_constant_on_rightFace hzero₁ p.property hp₀
  have hs₂ := affineLineFunctional_sign_constant_on_rightFace hzero₂ (H p).property
    (H ⟨p₀, hp₀⟩).property
  rw [hfix] at hs₂
  rw [hs₂, hanchor, hs₁]

private theorem face_subset_exterior {R : ℝ} (hR : 0 < R) (i : Fin 4) :
    face R i ⊆ exterior R := by
  intro p hp
  fin_cases i
  · simp only [face, exterior] at hp ⊢
    rcases hp with ⟨hr, _, _⟩
    have hx : 0 ≤ p.1 := (le_of_lt hR).trans hr
    change R ≤ max |p.1| |p.2|
    rw [abs_of_nonneg hx]
    exact hr.trans (le_max_left _ _)
  · simp only [face, exterior] at hp ⊢
    rcases hp with ⟨hr, _, _⟩
    have hy : 0 ≤ p.2 := (le_of_lt hR).trans hr
    change R ≤ max |p.1| |p.2|
    rw [abs_of_nonneg hy]
    exact hr.trans (le_max_right _ _)
  · simp only [face, exterior] at hp ⊢
    rcases hp with ⟨hr, _, _⟩
    have hx : p.1 ≤ 0 := by linarith
    change R ≤ max |p.1| |p.2|
    rw [abs_of_nonpos hx]
    exact hr.trans (le_max_left _ _)
  · simp only [face, exterior] at hp ⊢
    rcases hp with ⟨hr, _, _⟩
    have hy : p.2 ≤ 0 := by linarith
    change R ≤ max |p.1| |p.2|
    rw [abs_of_nonpos hy]
    exact hr.trans (le_max_right _ _)

private theorem exterior_covered_by_faces {R : ℝ} :
    exterior R ⊆ ⋃ i : Fin 4, face R i := by
  intro p hp
  have hmax : R ≤ max |p.1| |p.2| := hp
  by_cases hx : |p.1| ≥ |p.2|
  · have hxR : R ≤ |p.1| := by simpa [max_eq_left hx] using hmax
    rcases le_total 0 p.1 with hnonneg | hnonpos
    · have hbound : |p.2| ≤ p.1 := by rw [abs_of_nonneg hnonneg] at hx; linarith
      have hlow : -p.1 ≤ p.2 := by
        have habs := abs_le.mp hbound
        linarith
      have hhigh : p.2 ≤ p.1 := (abs_le.mp hbound).2
      refine mem_iUnion.mpr ⟨0, ?_⟩
      simpa [face] using ⟨by simpa [abs_of_nonneg hnonneg] using hxR, hlow, hhigh⟩
    · have hneg : p.1 ≤ 0 := hnonpos
      have hbound : |p.2| ≤ -p.1 := by rw [abs_of_nonpos hneg] at hx; linarith
      have hlow : p.1 ≤ p.2 := by
        have habs := abs_le.mp hbound
        linarith
      have hhigh : p.2 ≤ -p.1 := (abs_le.mp hbound).2
      refine mem_iUnion.mpr ⟨2, ?_⟩
      simpa [face, abs_of_nonpos hneg] using ⟨by simpa [abs_of_nonpos hneg] using hxR, hlow, hhigh⟩
  · have hy : |p.1| ≤ |p.2| := le_of_not_ge hx
    have hyR : R ≤ |p.2| := by simpa [max_eq_right hy] using hmax
    rcases le_total 0 p.2 with hnonneg | hnonpos
    · have hbound : |p.1| ≤ p.2 := by rw [abs_of_nonneg hnonneg] at hy; linarith
      have hlow : -p.2 ≤ p.1 := by
        have habs := abs_le.mp hbound
        linarith
      have hhigh : p.1 ≤ p.2 := (abs_le.mp hbound).2
      refine mem_iUnion.mpr ⟨1, ?_⟩
      simpa [face, abs_of_nonneg hnonneg] using ⟨by simpa [abs_of_nonneg hnonneg] using hyR, hlow, hhigh⟩
    · have hneg : p.2 ≤ 0 := hnonpos
      have hbound : |p.1| ≤ -p.2 := by rw [abs_of_nonpos hneg] at hy; linarith
      have hlow : p.2 ≤ p.1 := by
        have habs := abs_le.mp hbound
        linarith
      have hhigh : p.1 ≤ -p.2 := (abs_le.mp hbound).2
      refine mem_iUnion.mpr ⟨3, ?_⟩
      simpa [face, abs_of_nonpos hneg] using ⟨by simpa [abs_of_nonpos hneg] using hyR, hlow, hhigh⟩

private theorem face_overlap_is_diagonal {R : ℝ} {i j : Fin 4} {p : Plane}
    (hi : p ∈ face R i) (hj : p ∈ face R j) (hij : i ≠ j) :
    p ∈ diagonalRays := by
  fin_cases i <;> fin_cases j <;> simp_all [face, diagonalRays] <;>
    first
    | exact Or.inl (by linarith)
    | exact Or.inr (by linarith)

private theorem right_top_intersection {R : ℝ} (hR : 0 < R) {p : Plane} :
    p ∈ face R 0 ∧ p ∈ face R 1 ↔ R ≤ p.1 ∧ p.1 = p.2 := by
  change (R ≤ p.1 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1) ∧
    (R ≤ p.2 ∧ -p.2 ≤ p.1 ∧ p.1 ≤ p.2) ↔ _
  constructor
  · rintro ⟨⟨hr, _, hyx⟩, ⟨_, _, hxy⟩⟩
    exact ⟨hr, le_antisymm hxy hyx⟩
  · rintro ⟨hr, hxy⟩
    constructor
    · refine ⟨hr, ?_, ?_⟩ <;> linarith [hR]
    · refine ⟨?_, ?_, ?_⟩ <;> linarith [hR]

private theorem top_left_intersection {R : ℝ} (hR : 0 < R) {p : Plane} :
    p ∈ face R 1 ∧ p ∈ face R 2 ↔ R ≤ p.2 ∧ p.1 = -p.2 := by
  change (R ≤ p.2 ∧ -p.2 ≤ p.1 ∧ p.1 ≤ p.2) ∧
    (R ≤ -p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ -p.1) ↔ _
  constructor
  · rintro ⟨⟨hr, _, hxy⟩, ⟨_, _, hyx⟩⟩
    exact ⟨hr, by linarith⟩
  · rintro ⟨hr, hxy⟩
    constructor
    · refine ⟨hr, ?_, ?_⟩ <;> linarith [hR]
    · refine ⟨?_, ?_, ?_⟩ <;> linarith [hR]

private theorem left_bottom_intersection {R : ℝ} (hR : 0 < R) {p : Plane} :
    p ∈ face R 2 ∧ p ∈ face R 3 ↔ R ≤ -p.1 ∧ p.1 = p.2 := by
  change (R ≤ -p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ -p.1) ∧
    (R ≤ -p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ -p.2) ↔ _
  constructor
  · rintro ⟨⟨hr, hxy, _⟩, ⟨_, hyx, _⟩⟩
    exact ⟨hr, le_antisymm hxy hyx⟩
  · rintro ⟨hr, hxy⟩
    constructor
    · refine ⟨hr, ?_, ?_⟩ <;> linarith [hR]
    · refine ⟨?_, ?_, ?_⟩ <;> linarith [hR]

private theorem bottom_right_intersection {R : ℝ} (hR : 0 < R) {p : Plane} :
    p ∈ face R 3 ∧ p ∈ face R 0 ↔ R ≤ -p.2 ∧ p.1 = -p.2 := by
  change (R ≤ -p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ -p.2) ∧
    (R ≤ p.1 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1) ↔ _
  constructor
  · rintro ⟨⟨hr, hlow, hxy⟩, ⟨_, hneg, _⟩⟩
    exact ⟨hr, by linarith⟩
  · rintro ⟨hr, hxy⟩
    constructor
    · refine ⟨hr, ?_, ?_⟩ <;> linarith [hR]
    · refine ⟨?_, ?_, ?_⟩ <;> linarith [hR]

private theorem opposite_faces_disjoint {R : ℝ} (hR : 0 < R) {p : Plane}
    (hi : p ∈ face R 0) (hj : p ∈ face R 2) : False := by
  change R ≤ p.1 ∧ _ at hi
  change R ≤ -p.1 ∧ _ at hj
  rcases hi with ⟨h1, _, _⟩
  rcases hj with ⟨h2, _, _⟩
  linarith

private theorem opposite_faces_disjoint_top_bottom {R : ℝ} (hR : 0 < R) {p : Plane}
    (hi : p ∈ face R 1) (hj : p ∈ face R 3) : False := by
  change R ≤ p.2 ∧ _ at hi
  change R ≤ -p.2 ∧ _ at hj
  rcases hi with ⟨h1, _, _⟩
  rcases hj with ⟨h2, _, _⟩
  linarith

private abbrev ExteriorPoint (R : ℝ) := {p : Plane // p ∈ exterior R}

private def facePiece (R : ℝ) (i : Fin 4) : Set (ExteriorPoint R) :=
  {p | p.1 ∈ face R i}

private def facePieceEquiv (R : ℝ) (hR : 0 < R) (i : Fin 4) :
    {p : ExteriorPoint R // p ∈ facePiece R i} ≃ₜ FacePoint R i := by
  let S := {p : ExteriorPoint R // p ∈ facePiece R i}
  let T := FacePoint R i
  let f : S → T := fun p => ⟨p.1.1, p.2⟩
  let g : T → S := fun p => ⟨⟨p.1, face_subset_exterior hR i p.2⟩, p.2⟩
  have hfg : Function.LeftInverse g f := by intro p; apply Subtype.ext; apply Subtype.ext; rfl
  have hgf : Function.LeftInverse f g := by intro p; apply Subtype.ext; rfl
  have hfbase : Continuous (fun p : S => p.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hf : Continuous f := hfbase.subtype_mk _
  have hgbase : Continuous (fun p : T =>
      (⟨p.1, face_subset_exterior hR i p.2⟩ : ExteriorPoint R)) :=
    continuous_subtype_val.subtype_mk _
  have hg : Continuous g := hgbase.subtype_mk _
  exact Homeomorph.mk ⟨f, g, hfg, hgf⟩ hf hg

private def transportedFaceHomeomorph {R : ℝ} (hR : 0 < R) (i : Fin 4)
    (H : FacePoint R i ≃ₜ FacePoint R i) :
    {p : ExteriorPoint R // p ∈ facePiece R i} ≃ₜ
      {p : ExteriorPoint R // p ∈ facePiece R i} :=
  (facePieceEquiv R hR i).trans (H.trans (facePieceEquiv R hR i).symm)

private def finiteClosedCover_homeomorph
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (T : Set Y)
    (C : ι → Set S) (D : ι → Set T)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCcover : ∀ x : S, ∃ i, x ∈ C i)
    (hDcover : ∀ y : T, ∃ i, y ∈ D i)
    (piece : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val)
    (hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val) :
    S ≃ₜ T := by
  let sourceIndex (x : S) : ι := Classical.choose (hCcover x)
  have sourceIndex_mem (x : S) : x ∈ C (sourceIndex x) := Classical.choose_spec (hCcover x)
  let targetIndex (y : T) : ι := Classical.choose (hDcover y)
  have targetIndex_mem (y : T) : y ∈ D (targetIndex y) := Classical.choose_spec (hDcover y)
  let glued (x : S) : T := (piece (sourceIndex x) ⟨x, sourceIndex_mem x⟩).val
  let gluedInv (y : T) : S := ((piece (targetIndex y)).symm ⟨y, targetIndex_mem y⟩).val
  have glued_on_piece (i : ι) (x : C i) : glued x.val = (piece i x).val := by
    change (piece (sourceIndex x.val) ⟨x.val, sourceIndex_mem x.val⟩).val = (piece i x).val
    exact hforward (sourceIndex x.val) i x.val (sourceIndex_mem x.val) x.property
  have gluedInv_on_piece (i : ι) (y : D i) :
      gluedInv y.val = ((piece i).symm y).val := by
    change ((piece (targetIndex y.val)).symm ⟨y.val, targetIndex_mem y.val⟩).val =
      ((piece i).symm y).val
    exact hinverse (targetIndex y.val) i y.val (targetIndex_mem y.val) y.property
  have hglued_piece (i : ι) : ContinuousOn glued (C i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (C i).domRestrict glued = fun x : C i => (piece i x).val := by
      funext x
      exact glued_on_piece i x
    rw [heq]
    exact continuous_subtype_val.comp (piece i).continuous
  have hgluedInv_piece (i : ι) : ContinuousOn gluedInv (D i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (D i).domRestrict gluedInv = fun y : D i => ((piece i).symm y).val := by
      funext y
      exact gluedInv_on_piece i y
    rw [heq]
    exact continuous_subtype_val.comp (piece i).symm.continuous
  have hCunion : (⋃ i, C i) = (Set.univ : Set S) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hCcover x
  have hDunion : (⋃ i, D i) = (Set.univ : Set T) := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hDcover y
  have hglued : Continuous glued :=
    (locallyFinite_of_finite C).continuous hCunion hCclosed hglued_piece
  have hgluedInv : Continuous gluedInv :=
    (locallyFinite_of_finite D).continuous hDunion hDclosed hgluedInv_piece
  have hleft (x : S) : gluedInv (glued x) = x := by
    let i := sourceIndex x
    let j := targetIndex (glued x)
    have hxi : x ∈ C i := by dsimp [i]; exact sourceIndex_mem x
    have hyi : glued x ∈ D i := by
      dsimp [glued]
      exact (piece i ⟨x, hxi⟩).property
    have hyj : glued x ∈ D j := by dsimp [j]; exact targetIndex_mem (glued x)
    have hval : gluedInv (glued x) = ((piece i).symm ⟨glued x, hyi⟩).val := by
      dsimp [gluedInv, j]
      exact hinverse (targetIndex (glued x)) i (glued x)
        (targetIndex_mem (glued x)) hyi
    have hfirst : ((piece i).symm ⟨glued x, hyi⟩).val = x := by
      have heq : (piece i) ⟨x, hxi⟩ = ⟨glued x, hyi⟩ := by
        apply Subtype.ext
        exact (glued_on_piece i ⟨x, hxi⟩).symm
      have hinv : (piece i).symm ⟨glued x, hyi⟩ = ⟨x, hxi⟩ := by
        rw [← heq]
        simp
      exact congrArg Subtype.val hinv
    rw [hval, hfirst]
  have hright (y : T) : glued (gluedInv y) = y := by
    let i := targetIndex y
    let x := (piece i).symm ⟨y, targetIndex_mem y⟩
    have hyi : y ∈ D i := by dsimp [i]; exact targetIndex_mem y
    have hxi : x.val ∈ C i := x.property
    have hmap : (piece i x).val = y :=
      congrArg Subtype.val ((piece i).apply_symm_apply ⟨y, hyi⟩)
    have hinvval : gluedInv y = x.val := by dsimp [gluedInv, i, x]
    rw [hinvval, glued_on_piece i x]
    exact hmap
  let e : S ≃ T := ⟨glued, gluedInv, hleft, hright⟩
  exact Homeomorph.mk e hglued hgluedInv

private theorem finiteClosedCover_homeomorph_apply_piece
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (T : Set Y)
    (C : ι → Set S) (D : ι → Set T)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCcover : ∀ x : S, ∃ i, x ∈ C i)
    (hDcover : ∀ y : T, ∃ i, y ∈ D i)
    (piece : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val)
    (hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val)
    (i : ι) (x : S) (hxi : x ∈ C i) :
    (finiteClosedCover_homeomorph S T C D hCclosed hDclosed hCcover hDcover
      piece hforward hinverse x).val = (piece i ⟨x, hxi⟩).val.val := by
  classical
  let k : ι := Classical.choose (hCcover x)
  have hk : x ∈ C k := Classical.choose_spec (hCcover x)
  have heq := hforward k i x hk hxi
  simpa [finiteClosedCover_homeomorph, k] using congrArg Subtype.val heq

private theorem transportedFaceHomeomorph_fixes_diagonal {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    (i : Fin 4) (p : {p : ExteriorPoint R // p ∈ facePiece R i})
    (hdiag : p.1.1 ∈ diagonalRays) :
    (transportedFaceHomeomorph hR i (H i) p).val = p.1 := by
  apply Subtype.ext
  have heq : H i ((facePieceEquiv R hR i) p) = (facePieceEquiv R hR i) p :=
    hfix i _ hdiag
  change ((facePieceEquiv R hR i).symm (H i ((facePieceEquiv R hR i) p))).val = p.1.1
  rw [heq]
  rfl

private theorem transportedFaceHomeomorph_inverse_fixes_diagonal {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    (i : Fin 4) (p : {p : ExteriorPoint R // p ∈ facePiece R i})
    (hdiag : p.1.1 ∈ diagonalRays) :
    ((transportedFaceHomeomorph hR i (H i)).symm p).val = p.1 := by
  apply Subtype.ext
  have hinvfix : (H i).symm ((facePieceEquiv R hR i) p) = (facePieceEquiv R hR i) p := by
    have heq := hfix i ((facePieceEquiv R hR i) p) hdiag
    calc
      (H i).symm ((facePieceEquiv R hR i) p) =
          (H i).symm (H i ((facePieceEquiv R hR i) p)) := by rw [heq]
      _ = (facePieceEquiv R hR i) p := (H i).symm_apply_apply _
  change ((facePieceEquiv R hR i).symm ((H i).symm ((facePieceEquiv R hR i) p))).val = p.1.1
  rw [hinvfix]
  rfl

private structure FourFaceHomeomorphData {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p) where
  homeo : ExteriorPoint R ≃ₜ ExteriorPoint R
  on_face : ∀ (i : Fin 4) (p : ExteriorPoint R) (hp : p ∈ facePiece R i),
    (homeo p).1 = (transportedFaceHomeomorph hR i (H i) ⟨p, hp⟩).val.1

private def fourFaceHomeomorphWithPieces {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p) :
    FourFaceHomeomorphData hR H hfix := by
  let S := exterior R
  let T := exterior R
  let C : Fin 4 → Set {p : Plane // p ∈ S} := facePiece R
  let D : Fin 4 → Set {p : Plane // p ∈ T} := facePiece R
  have hX : Continuous (fun p : {p : Plane // p ∈ S} => p.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hY : Continuous (fun p : {p : Plane // p ∈ S} => p.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hCclosed : ∀ i, IsClosed (C i) := by
    intro i
    change IsClosed {p : {p : Plane // p ∈ S} | p.1 ∈ face R i}
    fin_cases i
    · change IsClosed {p : {p : Plane // p ∈ S} |
      R ≤ p.1.1 ∧ -p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ p.1.1}
      exact (isClosed_le continuous_const hX).inter
        ((isClosed_le (continuous_neg.comp hX) hY).inter (isClosed_le hY hX))
    · change IsClosed {p : {p : Plane // p ∈ S} |
      R ≤ p.1.2 ∧ -p.1.2 ≤ p.1.1 ∧ p.1.1 ≤ p.1.2}
      exact (isClosed_le continuous_const hY).inter
        ((isClosed_le (continuous_neg.comp hY) hX).inter (isClosed_le hX hY))
    · change IsClosed {p : {p : Plane // p ∈ S} |
      R ≤ -p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ -p.1.1}
      exact (isClosed_le continuous_const (continuous_neg.comp hX)).inter
        ((isClosed_le hX hY).inter (isClosed_le hY (continuous_neg.comp hX)))
    · change IsClosed {p : {p : Plane // p ∈ S} |
      R ≤ -p.1.2 ∧ p.1.2 ≤ p.1.1 ∧ p.1.1 ≤ -p.1.2}
      exact (isClosed_le continuous_const (continuous_neg.comp hY)).inter
        ((isClosed_le hY hX).inter (isClosed_le hX (continuous_neg.comp hY)))
  have hDclosed : ∀ i, IsClosed (D i) := hCclosed
  have hCcover : ∀ x : {p : Plane // p ∈ S}, ∃ i, x ∈ C i := by
    intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (exterior_covered_by_faces x.2)
    exact ⟨i, hi⟩
  have hDcover : ∀ y : {p : Plane // p ∈ T}, ∃ i, y ∈ D i := hCcover
  let piece : ∀ i, C i ≃ₜ D i := fun i => transportedFaceHomeomorph hR i (H i)
  have hforward : ∀ i j (x : {p : Plane // p ∈ S}) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val := by
    intro i j x hxi hxj
    by_cases hij : i = j
    · subst j
      have harg : (⟨x, hxi⟩ : C i) = ⟨x, hxj⟩ := by apply Subtype.ext; rfl
      rw [harg]
    · have hd := face_overlap_is_diagonal hxi hxj hij
      have hleft := transportedFaceHomeomorph_fixes_diagonal hR H hfix i ⟨x, hxi⟩ hd
      have hright := transportedFaceHomeomorph_fixes_diagonal hR H hfix j ⟨x, hxj⟩ hd
      exact hleft.trans hright.symm
  have hinverse : ∀ i j (y : {p : Plane // p ∈ T}) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val := by
    intro i j y hyi hyj
    by_cases hij : i = j
    · subst j
      have harg : (⟨y, hyi⟩ : D i) = ⟨y, hyj⟩ := by apply Subtype.ext; rfl
      rw [harg]
    · have hd := face_overlap_is_diagonal hyi hyj hij
      have hleft := transportedFaceHomeomorph_inverse_fixes_diagonal hR H hfix i ⟨y, hyi⟩ hd
      have hright := transportedFaceHomeomorph_inverse_fixes_diagonal hR H hfix j ⟨y, hyj⟩ hd
      exact hleft.trans hright.symm
  let G := finiteClosedCover_homeomorph S T C D hCclosed hDclosed hCcover hDcover
    piece hforward hinverse
  have hpiece (i : Fin 4) (p : {p : Plane // p ∈ S}) (hp : p ∈ C i) :
      (G p).1 = (piece i ⟨p, hp⟩).val := by
    exact finiteClosedCover_homeomorph_apply_piece S T C D hCclosed hDclosed
      hCcover hDcover piece hforward hinverse i p hp
  exact ⟨G, hpiece⟩

private def fourFaceHomeomorph {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p) :
    ExteriorPoint R ≃ₜ ExteriorPoint R :=
  (fourFaceHomeomorphWithPieces hR H hfix).homeo

private theorem fourFaceHomeomorph_on_face {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    (i : Fin 4) (p : ExteriorPoint R) (hp : p ∈ facePiece R i) :
    (fourFaceHomeomorph hR H hfix p).1 =
      (transportedFaceHomeomorph hR i (H i) ⟨p, hp⟩).val.1 :=
  (fourFaceHomeomorphWithPieces hR H hfix).on_face i p hp

private theorem fourFaceHomeomorph_fixes_diagonal {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    (p : ExteriorPoint R) (hp : p.1 ∈ diagonalRays) :
    (fourFaceHomeomorph hR H hfix p).1 = p := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (exterior_covered_by_faces p.2)
  have hlocal := fourFaceHomeomorph_on_face hR H hfix i p hi
  have hfixlocal := transportedFaceHomeomorph_fixes_diagonal hR H hfix i ⟨p, hi⟩ hp
  exact hlocal.trans (congrArg Subtype.val hfixlocal)


private theorem fourFaceHomeomorph_preserves_affine_signs {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    {ι : Type*} (a₁ b₁ c₁ a₂ b₂ c₂ : ι → ℝ)
    (hlocal : ∀ i (p : FacePoint R i) (ℓ : ι),
      Real.sign (affineLineFunctional (a₂ ℓ) (b₂ ℓ) (c₂ ℓ) (H i p).1) =
        Real.sign (affineLineFunctional (a₁ ℓ) (b₁ ℓ) (c₁ ℓ) p.1))
    (p : ExteriorPoint R) (ℓ : ι) :
    Real.sign (affineLineFunctional (a₂ ℓ) (b₂ ℓ) (c₂ ℓ)
      (fourFaceHomeomorph hR H hfix p).1) =
      Real.sign (affineLineFunctional (a₁ ℓ) (b₁ ℓ) (c₁ ℓ) p.1) := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (exterior_covered_by_faces p.2)
  have hglue := fourFaceHomeomorph_on_face hR H hfix i p hi
  have hface := hlocal i (facePieceEquiv R hR i ⟨p, hi⟩) ℓ
  rw [hglue]
  simpa [transportedFaceHomeomorph, facePieceEquiv] using hface

/-- The exterior glue preserves the square radius whenever each coordinate-face
map does. This transfers the actual local max-norm identity through the derived
face cover and the exact restriction of the glued homeomorphism. -/
private theorem fourFaceHomeomorph_preserves_squareRadius {R : ℝ} (hR : 0 < R)
    (H : ∀ i : Fin 4, FacePoint R i ≃ₜ FacePoint R i)
    (hfix : ∀ i (p : FacePoint R i), p.1 ∈ diagonalRays → H i p = p)
    (hlocal : ∀ i (p : FacePoint R i),
      max |(H i p).1.1| |(H i p).1.2| = max |p.1.1| |p.1.2|)
    (p : ExteriorPoint R) :
    max |(fourFaceHomeomorph hR H hfix p).1.1| |(fourFaceHomeomorph hR H hfix p).1.2| =
      max |p.1.1| |p.1.2| := by
  obtain ⟨i, hi⟩ := mem_iUnion.mp (exterior_covered_by_faces p.2)
  have hglue := fourFaceHomeomorph_on_face hR H hfix i p hi
  have hface := hlocal i (facePieceEquiv R hR i ⟨p, hi⟩)
  rw [hglue]
  simpa [transportedFaceHomeomorph, facePieceEquiv] using hface

end ExteriorFourFaces

namespace ExteriorFaceCharts

private def finiteClosedCover_homeomorph
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (T : Set Y)
    (C : ι → Set S) (D : ι → Set T)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCcover : ∀ x : S, ∃ i, x ∈ C i)
    (hDcover : ∀ y : T, ∃ i, y ∈ D i)
    (piece : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val)
    (hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val) :
    S ≃ₜ T := by
  let sourceIndex (x : S) : ι := Classical.choose (hCcover x)
  have sourceIndex_mem (x : S) : x ∈ C (sourceIndex x) := Classical.choose_spec (hCcover x)
  let targetIndex (y : T) : ι := Classical.choose (hDcover y)
  have targetIndex_mem (y : T) : y ∈ D (targetIndex y) := Classical.choose_spec (hDcover y)
  let glued (x : S) : T := (piece (sourceIndex x) ⟨x, sourceIndex_mem x⟩).val
  let gluedInv (y : T) : S := ((piece (targetIndex y)).symm ⟨y, targetIndex_mem y⟩).val
  have glued_on_piece (i : ι) (x : C i) : glued x.val = (piece i x).val := by
    change (piece (sourceIndex x.val) ⟨x.val, sourceIndex_mem x.val⟩).val = (piece i x).val
    exact hforward (sourceIndex x.val) i x.val (sourceIndex_mem x.val) x.property
  have gluedInv_on_piece (i : ι) (y : D i) :
      gluedInv y.val = ((piece i).symm y).val := by
    change ((piece (targetIndex y.val)).symm ⟨y.val, targetIndex_mem y.val⟩).val =
      ((piece i).symm y).val
    exact hinverse (targetIndex y.val) i y.val (targetIndex_mem y.val) y.property
  have hglued_piece (i : ι) : ContinuousOn glued (C i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (C i).domRestrict glued = fun x : C i => (piece i x).val := by
      funext x
      exact glued_on_piece i x
    rw [heq]
    exact continuous_subtype_val.comp (piece i).continuous
  have hgluedInv_piece (i : ι) : ContinuousOn gluedInv (D i) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : (D i).domRestrict gluedInv = fun y : D i => ((piece i).symm y).val := by
      funext y
      exact gluedInv_on_piece i y
    rw [heq]
    exact continuous_subtype_val.comp (piece i).symm.continuous
  have hCunion : (⋃ i, C i) = (Set.univ : Set S) := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hCcover x
  have hDunion : (⋃ i, D i) = (Set.univ : Set T) := by
    ext y
    simp only [mem_iUnion, mem_univ, iff_true]
    exact hDcover y
  have hglued : Continuous glued := by
    apply (locallyFinite_of_finite C).continuous hCunion hCclosed hglued_piece
  have hgluedInv : Continuous gluedInv := by
    apply (locallyFinite_of_finite D).continuous hDunion hDclosed hgluedInv_piece
  have hleft (x : S) : gluedInv (glued x) = x := by
    let i := sourceIndex x
    let j := targetIndex (glued x)
    have hxi : x ∈ C i := by dsimp [i]; exact sourceIndex_mem x
    have hyi : glued x ∈ D i := by
      dsimp [glued]
      exact (piece i ⟨x, hxi⟩).property
    have hyj : glued x ∈ D j := by dsimp [j]; exact targetIndex_mem (glued x)
    have hval : gluedInv (glued x) = ((piece i).symm ⟨glued x, hyi⟩).val := by
      dsimp [gluedInv, j]
      exact hinverse (targetIndex (glued x)) i (glued x)
        (targetIndex_mem (glued x)) hyi
    have hfirst : ((piece i).symm ⟨glued x, hyi⟩).val = x := by
      have heq : (piece i) ⟨x, hxi⟩ = ⟨glued x, hyi⟩ := by
        apply Subtype.ext
        exact (glued_on_piece i ⟨x, hxi⟩).symm
      have hinv : (piece i).symm ⟨glued x, hyi⟩ = ⟨x, hxi⟩ := by
        rw [← heq]
        simp
      exact congrArg Subtype.val hinv
    rw [hval, hfirst]
  have hright (y : T) : glued (gluedInv y) = y := by
    let i := targetIndex y
    let x := (piece i).symm ⟨y, targetIndex_mem y⟩
    have hyi : y ∈ D i := by dsimp [i]; exact targetIndex_mem y
    have hxi : x.val ∈ C i := x.property
    have hmap : (piece i x).val = y := congrArg Subtype.val ((piece i).apply_symm_apply ⟨y, hyi⟩)
    have hinvval : gluedInv y = x.val := by dsimp [gluedInv, i, x]
    rw [hinvval, glued_on_piece i x]
    exact hmap
  let e : S ≃ T :=
    { toFun := glued, invFun := gluedInv, left_inv := hleft, right_inv := hright }
  exact Homeomorph.mk e hglued hgluedInv

private theorem finiteClosedCover_homeomorph_apply_piece
    {ι X Y : Type*} [Fintype ι] [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (T : Set Y)
    (C : ι → Set S) (D : ι → Set T)
    (hCclosed : ∀ i, IsClosed (C i)) (hDclosed : ∀ i, IsClosed (D i))
    (hCcover : ∀ x : S, ∃ i, x ∈ C i)
    (hDcover : ∀ y : T, ∃ i, y ∈ D i)
    (piece : ∀ i, C i ≃ₜ D i)
    (hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val)
    (hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val)
    (i : ι) (x : S) (hxi : x ∈ C i) :
    (finiteClosedCover_homeomorph S T C D hCclosed hDclosed hCcover hDcover
      piece hforward hinverse x).val = (piece i ⟨x, hxi⟩).val.val := by
  classical
  let k : ι := Classical.choose (hCcover x)
  have hk : x ∈ C k := Classical.choose_spec (hCcover x)
  have heq := hforward k i x hk hxi
  simpa [finiteClosedCover_homeomorph, k] using congrArg Subtype.val heq

private def lower (a b : ℝ) (r : ℝ) : ℝ := a * r + b
private def upper (c d : ℝ) (r : ℝ) : ℝ := c * r + d
private def gap (a b c d : ℝ) (r : ℝ) : ℝ := upper c d r - lower a b r

private def closedStrip (R a b c d : ℝ) : Set (ℝ × ℝ) :=
  {p | R ≤ p.1 ∧ lower a b p.1 ≤ p.2 ∧ p.2 ≤ upper c d p.1}

private def stripChart (a b c d b' d' : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, lower a b' p.1 + (p.2 - lower a b p.1) *
    (gap a b' c d' p.1 / gap a b c d p.1))

private def stripInverseChart (a b c d b' d' : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, lower a b p.1 + (p.2 - lower a b' p.1) *
    (gap a b c d p.1 / gap a b' c d' p.1))

private def faceSector (R : ℝ) : Set (ℝ × ℝ) :=
  {p | R ≤ p.1 ∧ -p.1 ≤ p.2 ∧ p.2 ≤ p.1}

private def intervalStrip {n : ℕ} (R : ℝ) (A : Fin (n + 1) → ℝ → ℝ) (i : Fin n) :
    Set (ℝ × ℝ) :=
  {p | R ≤ p.1 ∧ A i.castSucc p.1 ≤ p.2 ∧ p.2 ≤ A i.succ p.1}

private def affineGraph {n : ℕ} (a b : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (r : ℝ) : ℝ := lower (a i) (b i) r

private def affineGraphGap {n : ℕ} (a b : Fin (n + 1) → ℝ) (i : Fin n)
    (r : ℝ) : ℝ :=
  affineGraph a b i.succ r - affineGraph a b i.castSucc r

private abbrev RationalGraph := ℚ × ℝ

private def rationalGraphValue (R : ℚ) (g : RationalGraph) : ℝ :=
  (g.1 : ℝ) * (R : ℝ) + g.2

private def rationalGraphIntersection (g h : RationalGraph) : ℝ :=
  (g.2 - h.2) / ((h.1 : ℝ) - (g.1 : ℝ))

private def targetRationalGraphValue (φ : ℝ →ₗ[ℚ] ℚ) (g : RationalGraph) (r : ℝ) : ℝ :=
  (g.1 : ℝ) * r + (φ g.2 : ℝ)

private def targetRationalGraphGap (φ : ℝ →ₗ[ℚ] ℚ) (g h : RationalGraph) (r : ℝ) : ℝ :=
  targetRationalGraphValue φ h r - targetRationalGraphValue φ g r

private def outgoingRationalGapTests (A : Finset RationalGraph) (R : ℚ) : Finset ℝ :=
  let V := A ∪ {(-1, 0), (1, 0)}
  ((V.product V).filter fun e =>
    rationalGraphValue R e.1 ≠ rationalGraphValue R e.2).image fun e =>
      rationalGraphValue R e.2 - rationalGraphValue R e.1

/-- The concrete finite family of outgoing graphs: retain precisely those
source labels strictly between the two corner lines at `R`, then adjoin the
two geometric corners (so coincident source labels are deduplicated). -/
private def outgoingRationalGraphs (A : Finset RationalGraph) (R : ℚ) :
    Finset RationalGraph :=
  (A.filter fun g => -(R : ℝ) < rationalGraphValue R g ∧
      rationalGraphValue R g < R) ∪ {(-1, 0), (1, 0)}

private theorem rationalGraphValue_injective_on (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    {g h : RationalGraph} (hg : g ∈ G) (hh : h ∈ G)
    (heq : rationalGraphValue R g = rationalGraphValue R h) : g = h := by
  rcases g with ⟨a, b⟩
  rcases h with ⟨c, d⟩
  change (a : ℝ) * (R : ℝ) + b = (c : ℝ) * (R : ℝ) + d at heq
  by_cases hslope : a = c
  · have hb : b = d := by subst c; linarith
    subst c
    subst d
    rfl
  · have hden : (c : ℝ) - (a : ℝ) ≠ 0 := by
      intro hz
      apply hslope
      exact_mod_cast (sub_eq_zero.mp hz).symm
    have hcross : b - d = ((c : ℝ) - (a : ℝ)) * (R : ℝ) := by linarith
    have ht : rationalGraphIntersection (a, b) (c, d) = R := by
      unfold rationalGraphIntersection
      rw [hcross, mul_div_cancel_left₀ _ hden]
    have hbefore := hinter (a, b) hg (c, d) hh hslope
    rw [ht] at hbefore
    linarith

private theorem rationalSlope_order_of_value_order
    (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    {g h : RationalGraph} (hg : g ∈ G) (hh : h ∈ G)
    (horder : rationalGraphValue R g < rationalGraphValue R h) :
    g.1 ≤ h.1 := by
  by_cases hslope : g.1 = h.1
  · exact le_of_eq hslope
  · have hfactor : rationalGraphValue R h - rationalGraphValue R g =
        ((h.1 : ℝ) - (g.1 : ℝ)) *
          ((R : ℝ) - rationalGraphIntersection g h) := by
      unfold rationalGraphValue rationalGraphIntersection
      field_simp [show (h.1 : ℝ) - (g.1 : ℝ) ≠ 0 from by
        intro hz
        apply hslope
        exact_mod_cast (sub_eq_zero.mp hz).symm]
      ring
    have hdist : 0 < (R : ℝ) - rationalGraphIntersection g h := by
      have hc := hinter g hg h hh hslope
      exact_mod_cast sub_pos.mpr hc
    have hslope' : (g.1 : ℝ) ≤ (h.1 : ℝ) := by
      by_contra hnot
      have hneg : (h.1 : ℝ) - (g.1 : ℝ) < 0 := by linarith
      have hgap : 0 < rationalGraphValue R h - rationalGraphValue R g := sub_pos.mpr horder
      rw [hfactor] at hgap
      have hprod := mul_neg_of_neg_of_pos hneg hdist
      linarith [hgap]
    exact_mod_cast hslope'

private def sortedOutgoingGraphSequence (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R) : List {g // g ∈ G} := by
  classical
  let rel : {g // g ∈ G} → {g // g ∈ G} → Prop := fun g h =>
    rationalGraphValue R g.1 ≤ rationalGraphValue R h.1
  letI : DecidableRel rel := fun _ _ => inferInstance
  letI : IsTrans _ rel := ⟨by
    intro x y z hxy hyz
    exact le_trans hxy hyz⟩
  letI : Std.Antisymm rel := ⟨by
    intro x y hxy hyx
    apply Subtype.ext
    exact rationalGraphValue_injective_on G R hinter x.2 y.2 (le_antisymm hxy hyx)⟩
  letI : Std.Total rel := ⟨by intro x y; exact le_total _ _⟩
  exact G.attach.sort rel

private theorem sorted_le_pairwise_to_lt (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    {L : List {g // g ∈ G}}
    (hle : L.Pairwise (fun g h => rationalGraphValue R g.1 ≤ rationalGraphValue R h.1))
    (hnodup : L.Nodup) :
    L.Pairwise (fun g h => rationalGraphValue R g.1 < rationalGraphValue R h.1) := by
  induction L with
  | nil => simp
  | cons x xs ih =>
      simp only [List.pairwise_cons, List.nodup_cons] at hle hnodup ⊢
      refine ⟨?_, ih hle.2 hnodup.2⟩
      intro y hy
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hnodup.1 hy
      have hne : rationalGraphValue R x.1 ≠ rationalGraphValue R y.1 := by
        intro heq
        apply hxy
        apply Subtype.ext
        exact rationalGraphValue_injective_on G R hinter x.2 y.2 heq
      exact lt_of_le_of_ne (hle.1 y hy) hne

private theorem sortedOutgoingGraphSequence_strict (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R) :
    (sortedOutgoingGraphSequence G R hinter).Pairwise
      (fun g h => rationalGraphValue R g.1 < rationalGraphValue R h.1) := by
  classical
  let rel : {g // g ∈ G} → {g // g ∈ G} → Prop := fun g h =>
    rationalGraphValue R g.1 ≤ rationalGraphValue R h.1
  letI : DecidableRel rel := fun _ _ => inferInstance
  letI : IsTrans _ rel := ⟨by
    intro x y z hxy hyz
    exact le_trans hxy hyz⟩
  letI : Std.Antisymm rel := ⟨by
    intro x y hxy hyx
    apply Subtype.ext
    exact rationalGraphValue_injective_on G R hinter x.2 y.2 (le_antisymm hxy hyx)⟩
  letI : Std.Total rel := ⟨by intro x y; exact le_total _ _⟩
  exact sorted_le_pairwise_to_lt G R hinter
    (by simpa [sortedOutgoingGraphSequence, rel] using (Finset.pairwise_sort G.attach rel))
    (by simpa [sortedOutgoingGraphSequence, rel] using (Finset.sort_nodup G.attach rel))

private theorem sortedOutgoingGraphSequence_toFinset (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R) :
    (sortedOutgoingGraphSequence G R hinter).toFinset = G.attach := by
  classical
  let rel : {g // g ∈ G} → {g // g ∈ G} → Prop := fun g h =>
    rationalGraphValue R g.1 ≤ rationalGraphValue R h.1
  letI : DecidableRel rel := fun _ _ => inferInstance
  letI : IsTrans _ rel := ⟨by intro x y z hxy hyz; exact le_trans hxy hyz⟩
  letI : Std.Antisymm rel := ⟨by
    intro x y hxy hyx
    apply Subtype.ext
    exact rationalGraphValue_injective_on G R hinter x.2 y.2 (le_antisymm hxy hyx)⟩
  letI : Std.Total rel := ⟨by intro x y; exact le_total _ _⟩
  simp [sortedOutgoingGraphSequence]

private theorem sortedOutgoingGraphSequence_head_corner
    (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    (hleft : (-1, 0) ∈ G)
    (hbound : ∀ g ∈ G, -(R : ℝ) ≤ rationalGraphValue R g ∧
      rationalGraphValue R g ≤ R) :
    ∃ tail, sortedOutgoingGraphSequence G R hinter =
      (⟨(-1, 0), hleft⟩ : {g // g ∈ G}) :: tail := by
  classical
  let L := sortedOutgoingGraphSequence G R hinter
  let left : {g // g ∈ G} := ⟨(-1, 0), hleft⟩
  have hmem : left ∈ L := by
    apply List.mem_toFinset.mp
    rw [sortedOutgoingGraphSequence_toFinset]
    simp [left]
  have hstrict := sortedOutgoingGraphSequence_strict G R hinter
  cases hseq : L with
  | nil => simp [hseq] at hmem
  | cons first tail =>
      have hmem' : left ∈ first :: tail := by simpa [hseq] using hmem
      by_cases heq : first = left
      · refine ⟨tail, ?_⟩
        calc
          sortedOutgoingGraphSequence G R hinter = L := rfl
          _ = first :: tail := hseq
          _ = left :: tail := by rw [heq]
      · have htail : left ∈ tail := by
          rcases List.mem_cons.mp hmem' with hhead | htail
          · exact (heq hhead.symm).elim
          · exact htail
        have hpair : (first :: tail).Pairwise
            (fun x y => rationalGraphValue R x.1 < rationalGraphValue R y.1) := by
          simpa [hseq, L] using hstrict
        have hlt := hpair.rel_head_tail htail
        have hlt' : rationalGraphValue R first.1 < rationalGraphValue R left.1 := by
          simpa using hlt
        have hmin := (hbound first.1 first.2).1
        have hleftval : rationalGraphValue R left.1 = -(R : ℝ) := by
          simp [left, rationalGraphValue]
        rw [hleftval] at hlt'
        linarith

private theorem sortedOutgoingGraphSequence_last_corner
    (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    (hright : (1, 0) ∈ G)
    (hbound : ∀ g ∈ G, -(R : ℝ) ≤ rationalGraphValue R g ∧
      rationalGraphValue R g ≤ R) :
    ∃ pre, sortedOutgoingGraphSequence G R hinter =
      pre ++ [(⟨(1, 0), hright⟩ : {g // g ∈ G})] := by
  classical
  let L := sortedOutgoingGraphSequence G R hinter
  let right : {g // g ∈ G} := ⟨(1, 0), hright⟩
  have hmem : right ∈ L := by
    apply List.mem_toFinset.mp
    rw [sortedOutgoingGraphSequence_toFinset]
    simp [right]
  have hne : L ≠ [] := List.ne_nil_of_mem hmem
  have hstrict := sortedOutgoingGraphSequence_strict G R hinter
  have hlastEq : L.getLast hne = right := by
    apply Subtype.ext
    by_contra hneq
    have hdrop : right ∈ L.dropLast := by
      have hmem' : right ∈ L.dropLast ++ [L.getLast hne] := by
        simpa [List.dropLast_concat_getLast hne] using hmem
      rcases List.mem_append.mp hmem' with hpre | hlast
      · exact hpre
      · simp only [List.mem_singleton] at hlast
        exact (hneq (congrArg Subtype.val hlast).symm).elim
    have hlt := hstrict.rel_dropLast_getLast hdrop
    have hrightval : rationalGraphValue R right.1 = R := by
      simp [right, rationalGraphValue]
    have hupper := (hbound (L.getLast hne).1 (L.getLast hne).2).2
    rw [hrightval] at hlt
    linarith
  refine ⟨L.dropLast, ?_⟩
  change L = L.dropLast ++ [right]
  rw [← hlastEq]
  exact (List.dropLast_concat_getLast hne).symm

/-- The active graphs are genuinely obtained from the finite arrangement
labels: sorting by their evaluation at `R` gives a finite strict chain whose
endpoints are the two diagonal corners. This is the concrete list interface
used to build a face family, not an assumed ordered-family certificate. -/
private theorem outgoingRationalGraphs_sorted_faceFamily
    (A : Finset RationalGraph) (R : ℚ) (hR : 0 < R)
    (hinter : ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
      ∀ h ∈ A ∪ {(-1, 0), (1, 0)}, g.1 ≠ h.1 →
        rationalGraphIntersection g h < R) :
    ∃ L : List {g // g ∈ outgoingRationalGraphs A R},
      ∃ hlen : 2 ≤ L.length,
      L.Pairwise (fun g h =>
        rationalGraphValue R g.1 < rationalGraphValue R h.1) ∧
      (L.get ⟨0, by omega⟩).1 = (-1, 0) ∧
      (L.get ⟨L.length - 1, by omega⟩).1 = (1, 0) ∧
      (∀ g ∈ outgoingRationalGraphs A R,
        ∃ i : Fin L.length, ∃ hg : g ∈ outgoingRationalGraphs A R,
          L.get i = (⟨g, hg⟩ : {g // g ∈ outgoingRationalGraphs A R})) := by
  classical
  let G := outgoingRationalGraphs A R
  have hsubset : ∀ g ∈ G, g ∈ A ∪ {(-1, 0), (1, 0)} := by
    intro g hg
    simp only [G, outgoingRationalGraphs, Finset.mem_union,
      Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hg ⊢
    rcases hg with ⟨hA, _⟩ | hcorner
    · exact Or.inl hA
    · exact Or.inr hcorner
  have hGinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R := by
    intro g hg h hh hne
    exact hinter g (hsubset g hg) h (hsubset h hh) hne
  have hbound : ∀ g ∈ G,
      -(R : ℝ) ≤ rationalGraphValue R g ∧ rationalGraphValue R g ≤ R := by
    intro g hg
    simp only [G, outgoingRationalGraphs, Finset.mem_union,
      Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with ⟨_, hv⟩ | hcorner
    · exact ⟨le_of_lt hv.1, le_of_lt hv.2⟩
    · rcases hcorner with hleft | hright
      · subst g
        simp [rationalGraphValue]
        linarith [hR]
      · subst g
        simp [rationalGraphValue]
        linarith [hR]
  have hleft : (-1, 0) ∈ G := by
    simp [G, outgoingRationalGraphs]
  have hright : (1, 0) ∈ G := by
    simp [G, outgoingRationalGraphs]
  let L := sortedOutgoingGraphSequence G R hGinter
  have hhead := sortedOutgoingGraphSequence_head_corner G R hGinter hleft hbound
  have hlast := sortedOutgoingGraphSequence_last_corner G R hGinter hright hbound
  rcases hhead with ⟨tail, hhead⟩
  rcases hlast with ⟨pre, hlast⟩
  have hrightmem : (⟨(1, 0), hright⟩ : {g // g ∈ G}) ∈ L := by
    change (⟨(1, 0), hright⟩ : {g // g ∈ G}) ∈ sortedOutgoingGraphSequence G R hGinter
    apply List.mem_toFinset.mp
    rw [sortedOutgoingGraphSequence_toFinset]
    simp
  have hleftne : (⟨(1, 0), hright⟩ : {g // g ∈ G}) ≠
      (⟨(-1, 0), hleft⟩ : {g // g ∈ G}) := by
    intro heq
    have := congrArg Subtype.val heq
    norm_num at this
  have htailmem : (⟨(1, 0), hright⟩ : {g // g ∈ G}) ∈ tail := by
    change (⟨(1, 0), hright⟩ : {g // g ∈ G}) ∈ sortedOutgoingGraphSequence G R hGinter at hrightmem
    rw [hhead] at hrightmem
    rcases List.mem_cons.mp hrightmem with heq | hmem
    · exact (hleftne heq).elim
    · exact hmem
  have hlen : 2 ≤ L.length := by
    change 2 ≤ (sortedOutgoingGraphSequence G R hGinter).length
    rw [hhead]
    have htailpos : 0 < tail.length :=
      List.length_pos_iff.mpr (List.ne_nil_of_mem htailmem)
    simp only [List.length_cons]
    omega
  have hstrict : L.Pairwise (fun g h =>
      rationalGraphValue R g.1 < rationalGraphValue R h.1) := by
    change (sortedOutgoingGraphSequence G R hGinter).Pairwise _
    exact sortedOutgoingGraphSequence_strict G R hGinter
  have hlen' : 2 ≤ (sortedOutgoingGraphSequence G R hGinter).length := by
    simpa [L] using hlen
  have hfirst : (L.get ⟨0, by omega⟩).1 = (-1, 0) := by
    simp [L, hhead]
  have hlastval : (L.get ⟨L.length - 1, by omega⟩).1 = (1, 0) := by
    simp [L, hlast]
  have hcover : ∀ g ∈ G,
      ∃ i : Fin L.length, ∃ hg : g ∈ G,
        L.get i = (⟨g, hg⟩ : {g // g ∈ G}) := by
    intro g hg
    let x : {g // g ∈ G} := ⟨g, hg⟩
    have hmem : x ∈ L := by
      change (⟨g, hg⟩ : {g // g ∈ G}) ∈ sortedOutgoingGraphSequence G R hGinter
      apply List.mem_toFinset.mp
      rw [sortedOutgoingGraphSequence_toFinset]
      simp
    have hex : ∃ x ∈ L, x = (⟨g, hg⟩ : {g // g ∈ G}) :=
      ⟨⟨g, hg⟩, hmem, rfl⟩
    rcases List.exists_mem_iff_get.mp hex with ⟨i, hi⟩
    exact ⟨i, hg, hi⟩
  exact ⟨L, hlen, hstrict, hfirst, hlastval, hcover⟩



/-- Adapt an actually sorted finite graph list to the `Fin`-indexed interface
used by the closed-face gluing theorem. Pairwise strict value order and the
real pair-incidence hypothesis derive nonnegative slope steps, hence positive
gaps for every radius beyond `R`. -/
private theorem listGraphFamily_to_faceFamily
    (G : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R)
    (L : List {g // g ∈ G})
    (hlen : 2 ≤ L.length)
    (hstrict : L.Pairwise (fun g h =>
      rationalGraphValue R g.1 < rationalGraphValue R h.1))
    (hfirst : (L.get ⟨0, by omega⟩).1 = (-1, 0))
    (hlast : (L.get ⟨L.length - 1, by omega⟩).1 = (1, 0))
    (hcover : ∀ g ∈ G, ∃ i : Fin L.length, ∃ hg : g ∈ G,
      L.get i = (⟨g, hg⟩ : {g // g ∈ G})) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin (n + 1) → ℝ,
      (∀ r, affineGraph a b 0 r = -r) ∧
      (∀ r, affineGraph a b ⟨n, by omega⟩ r = r) ∧
      (∀ i : Fin n, a i.castSucc ≤ a i.succ) ∧
      (∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
        0 < affineGraphGap a b i r) ∧
      (∀ i : Fin (n + 1), ∃ g ∈ G,
        a i = (g.1 : ℝ) ∧ b i = g.2) ∧
      (∀ g ∈ G, ∃ i : Fin (n + 1),
        a i = (g.1 : ℝ) ∧ b i = g.2) := by
  classical
  let n := L.length - 1
  have hn : 0 < n := by dsimp [n]; omega
  have hcardEq : n + 1 = L.length := by dsimp [n]; omega
  let arr (i : Fin (n + 1)) := L.get (Fin.cast hcardEq i)
  let a : Fin (n + 1) → ℝ := fun i => ((arr i).1.1 : ℝ)
  let b : Fin (n + 1) → ℝ := fun i => (arr i).1.2
  have hfirstGraph : (arr (0 : Fin (n + 1))).1 = (-1, 0) := by
    dsimp [arr]
    have hidx : Fin.cast hcardEq (0 : Fin (n + 1)) = ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    calc
      (L.get (Fin.cast hcardEq (0 : Fin (n + 1)))).1 =
          (L.get ⟨0, by omega⟩).1 :=
        congrArg Subtype.val (congrArg L.get hidx)
      _ = (-1, 0) := hfirst
  have hlastGraph : (arr ⟨n, by omega⟩).1 = (1, 0) := by
    dsimp [arr]
    have hidx : Fin.cast hcardEq (⟨n, by omega⟩ : Fin (n + 1)) =
        (⟨L.length - 1, by omega⟩ : Fin L.length) := by
      apply Fin.ext
      simp [n]
    calc
      (L.get (Fin.cast hcardEq (⟨n, by omega⟩ : Fin (n + 1)))).1 =
          (L.get ⟨L.length - 1, by omega⟩).1 :=
        congrArg Subtype.val (congrArg L.get hidx)
      _ = (1, 0) := hlast
  have hfirstEq : ∀ r, affineGraph a b 0 r = -r := by
    intro r
    change ((arr 0).1.1 : ℝ) * r + (arr 0).1.2 = -r
    rw [hfirstGraph]
    simp
  have hlastEq : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r := by
    intro r
    change ((arr ⟨n, by omega⟩).1.1 : ℝ) * r +
      (arr ⟨n, by omega⟩).1.2 = r
    rw [hlastGraph]
    simp
  have hmono : ∀ i : Fin n, a i.castSucc ≤ a i.succ := by
    intro i
    let i₁ := Fin.cast hcardEq i.castSucc
    let i₂ := Fin.cast hcardEq i.succ
    have hidx : i₁ < i₂ := by
      apply Fin.lt_def.mpr
      simp [i₁, i₂]
    have heval : rationalGraphValue R (arr i.castSucc).1 <
        rationalGraphValue R (arr i.succ).1 := by
      have := hstrict.rel_get_of_lt hidx
      simpa [arr, i₁, i₂, hcardEq] using this
    have hslope := rationalSlope_order_of_value_order G R hinter
      (arr i.castSucc).2 (arr i.succ).2 heval
    change ((arr i.castSucc).1.1 : ℝ) ≤ ((arr i.succ).1.1 : ℝ)
    exact_mod_cast hslope
  have hgap : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
      0 < affineGraphGap a b i r := by
    intro i r hr
    let i₁ := Fin.cast hcardEq i.castSucc
    let i₂ := Fin.cast hcardEq i.succ
    have hidx : i₁ < i₂ := by
      apply Fin.lt_def.mpr
      simp [i₁, i₂]
    have heval : rationalGraphValue R (arr i.castSucc).1 <
        rationalGraphValue R (arr i.succ).1 := by
      have := hstrict.rel_get_of_lt hidx
      simpa [arr, i₁, i₂, hcardEq] using this
    have hsourceR : 0 < rationalGraphValue R (arr i.succ).1 -
        rationalGraphValue R (arr i.castSucc).1 := by linarith
    have hslope : (arr i.castSucc).1.1 ≤ (arr i.succ).1.1 :=
      rationalSlope_order_of_value_order G R hinter
        (arr i.castSucc).2 (arr i.succ).2 heval
    have hcoef : 0 ≤ ((arr i.succ).1.1 : ℝ) - ((arr i.castSucc).1.1 : ℝ) := by
      exact_mod_cast sub_nonneg.mpr hslope
    have hdecomp :
      (((arr i.succ).1.1 : ℝ) * r + (arr i.succ).1.2) -
        (((arr i.castSucc).1.1 : ℝ) * r + (arr i.castSucc).1.2) =
      (rationalGraphValue R (arr i.succ).1 -
        rationalGraphValue R (arr i.castSucc).1) +
        (((arr i.succ).1.1 : ℝ) - ((arr i.castSucc).1.1 : ℝ)) *
          (r - (R : ℝ)) := by
      simp [rationalGraphValue]
      ring
    dsimp [affineGraphGap, affineGraph, lower, a, b]
    rw [hdecomp]
    exact add_pos_of_pos_of_nonneg hsourceR
      (mul_nonneg hcoef (sub_nonneg.mpr hr))
  have hforward : ∀ i : Fin (n + 1), ∃ g ∈ G,
      a i = (g.1 : ℝ) ∧ b i = g.2 := by
    intro i
    exact ⟨(arr i).1, (arr i).2, rfl, rfl⟩
  have hbackward : ∀ g ∈ G, ∃ i : Fin (n + 1),
      a i = (g.1 : ℝ) ∧ b i = g.2 := by
    intro g hg
    rcases hcover g hg with ⟨j, hj, hget⟩
    let i : Fin (n + 1) := Fin.cast hcardEq.symm j
    have hidx : Fin.cast hcardEq i = j := by
      apply Fin.ext
      rfl
    refine ⟨i, ?_, ?_⟩
    · change ((L.get (Fin.cast hcardEq i)).1.1 : ℝ) = (g.1 : ℝ)
      rw [hidx, hget]
    · change (L.get (Fin.cast hcardEq i)).1.2 = g.2
      rw [hidx, hget]
  exact ⟨n, hn, a, b, hfirstEq, hlastEq, hmono, hgap, hforward, hbackward⟩

/-- Build the actual active right-face graph family from the source labels.
Every source label strictly between the corner values is retained as a member
of the sorted list and is consequently represented at a `Fin` index. -/
private theorem outgoingRationalGraphs_faceFamily
    (A : Finset RationalGraph) (R : ℚ) (hR : 0 < R)
    (hinter : ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
      ∀ h ∈ A ∪ {(-1, 0), (1, 0)}, g.1 ≠ h.1 →
        rationalGraphIntersection g h < R) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin (n + 1) → ℝ,
      (∀ r, affineGraph a b 0 r = -r) ∧
      (∀ r, affineGraph a b ⟨n, by omega⟩ r = r) ∧
      (∀ i : Fin n, a i.castSucc ≤ a i.succ) ∧
      (∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
        0 < affineGraphGap a b i r) ∧
      (∀ i : Fin (n + 1), ∃ g ∈ outgoingRationalGraphs A R,
        a i = (g.1 : ℝ) ∧ b i = g.2) ∧
      (∀ g ∈ A, -(R : ℝ) < rationalGraphValue R g →
        rationalGraphValue R g < R →
        ∃ i : Fin (n + 1), a i = (g.1 : ℝ) ∧ b i = g.2) := by
  classical
  obtain ⟨L, hlen, hstrict, hfirst, hlast, hcover⟩ :=
    outgoingRationalGraphs_sorted_faceFamily A R hR hinter
  let G := outgoingRationalGraphs A R
  have hGinter : ∀ g ∈ G, ∀ h ∈ G, g.1 ≠ h.1 →
      rationalGraphIntersection g h < R := by
    intro g hg h hh hne
    have hg' : g ∈ A ∪ {(-1, 0), (1, 0)} := by
      simp only [G, outgoingRationalGraphs, Finset.mem_union] at hg
      rcases hg with hsrc | hcorner
      · exact Finset.mem_union_left _ (Finset.mem_filter.mp hsrc).1
      · exact Finset.mem_union_right _ hcorner
    have hh' : h ∈ A ∪ {(-1, 0), (1, 0)} := by
      simp only [G, outgoingRationalGraphs, Finset.mem_union] at hh
      rcases hh with hsrc | hcorner
      · exact Finset.mem_union_left _ (Finset.mem_filter.mp hsrc).1
      · exact Finset.mem_union_right _ hcorner
    exact hinter g hg' h hh' hne
  have hfamily := listGraphFamily_to_faceFamily G R hGinter L hlen hstrict
    hfirst hlast hcover
  rcases hfamily with ⟨n, hn, a, b, hleft, hright, hmono, hgap,
    hforward, hbackward⟩
  have hlabels : ∀ g ∈ A, -(R : ℝ) < rationalGraphValue R g →
      rationalGraphValue R g < R →
      ∃ i : Fin (n + 1), a i = (g.1 : ℝ) ∧ b i = g.2 := by
    intro g hg hlo hhi
    have hG : g ∈ G := by
      simp only [G, outgoingRationalGraphs, Finset.mem_union,
        Finset.mem_filter]
      exact Or.inl ⟨hg, ⟨hlo, hhi⟩⟩
    exact hbackward g hG
  exact ⟨n, hn, a, b, hleft, hright, hmono, hgap, hforward, hlabels⟩

private def facePiece {n : ℕ} (R : ℝ) (A : Fin (n + 1) → ℝ → ℝ) (i : Fin n) :
    Set {p : ℝ × ℝ // p ∈ faceSector R} :=
  {p | p.1 ∈ intervalStrip R A i}

private theorem chart_mem_strip {R a b c d b' d' : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closedStrip R a b c d)
    (hgap : ∀ r, R ≤ r → 0 < gap a b c d r)
    (hgap' : ∀ r, R ≤ r → 0 < gap a b' c d' r) :
    stripChart a b c d b' d' p ∈ closedStrip R a b' c d' := by
  rcases hp with ⟨hr, hlo, hhi⟩
  have hg := hgap p.1 hr
  have hg' := hgap' p.1 hr
  have hratio : 0 < gap a b' c d' p.1 / gap a b c d p.1 := div_pos hg' hg
  have hdiff : 0 ≤ p.2 - lower a b p.1 := sub_nonneg.mpr hlo
  have hup : p.2 - lower a b p.1 ≤ gap a b c d p.1 := by
    dsimp [gap, upper, lower] at hhi ⊢
    linarith
  have hratio_le : (p.2 - lower a b p.1) *
      (gap a b' c d' p.1 / gap a b c d p.1) ≤ gap a b' c d' p.1 := by
    rw [← mul_div_assoc, div_le_iff₀ hg]
    calc
      (p.2 - lower a b p.1) * gap a b' c d' p.1 ≤
          gap a b c d p.1 * gap a b' c d' p.1 :=
        mul_le_mul_of_nonneg_right hup hg'.le
      _ = gap a b' c d' p.1 * gap a b c d p.1 := mul_comm _ _
  refine ⟨hr, ?_, ?_⟩
  · dsimp [stripChart]
    nlinarith [mul_nonneg (sub_nonneg.mpr hlo) hratio.le]
  · dsimp [stripChart]
    dsimp [lower, upper, gap] at hratio_le ⊢
    nlinarith [hratio_le]

private theorem inverse_mem_strip {R a b c d b' d' : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ closedStrip R a b' c d')
    (hgap : ∀ r, R ≤ r → 0 < gap a b c d r)
    (hgap' : ∀ r, R ≤ r → 0 < gap a b' c d' r) :
    stripInverseChart a b c d b' d' p ∈ closedStrip R a b c d := by
  apply chart_mem_strip (a := a) (b := b') (c := c) (d := d')
    (b' := b) (d' := d) hp hgap' hgap

private theorem inverse_left {a b c d b' d' : ℝ} {p : ℝ × ℝ}
    (hden : gap a b' c d' p.1 ≠ 0) (hden' : gap a b c d p.1 ≠ 0) :
    stripInverseChart a b c d b' d' (stripChart a b c d b' d' p) = p := by
  rcases p with ⟨r, y⟩
  apply Prod.ext
  · rfl
  · dsimp [stripChart, stripInverseChart]
    field_simp [hden, hden']
    ring

private theorem inverse_right {a b c d b' d' : ℝ} {p : ℝ × ℝ}
    (hden : gap a b c d p.1 ≠ 0) (hden' : gap a b' c d' p.1 ≠ 0) :
    stripChart a b c d b' d' (stripInverseChart a b c d b' d' p) = p := by
  rcases p with ⟨r, y⟩
  apply Prod.ext
  · rfl
  · dsimp [stripChart, stripInverseChart]
    field_simp [hden, hden']
    ring

private theorem stripChart_lower_anchor {a b c d b' d' r : ℝ} :
    stripChart a b c d b' d' (r, lower a b r) = (r, lower a b' r) := by
  apply Prod.ext
  · rfl
  · simp [stripChart]

private theorem stripChart_upper_anchor {a b c d b' d' r : ℝ}
    (hden : gap a b c d r ≠ 0) :
    stripChart a b c d b' d' (r, upper c d r) = (r, upper c d' r) := by
  apply Prod.ext
  · rfl
  · change lower a b' r + gap a b c d r *
      (gap a b' c d' r / gap a b c d r) = upper c d' r
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ hden]
    simp only [gap]
    dsimp [lower, upper]
    ring

private theorem continuousOn_stripChart {R a b c d b' d' : ℝ}
    (hgap : ∀ r, R ≤ r → 0 < gap a b c d r) :
    ContinuousOn (stripChart a b c d b' d') (closedStrip R a b c d) := by
  intro p hp
  have hden : gap a b c d p.1 ≠ 0 := ne_of_gt (hgap p.1 hp.1)
  have hl' : ContinuousAt (fun q : ℝ × ℝ => lower a b' q.1) p := by fun_prop [lower]
  have hl : ContinuousAt (fun q : ℝ × ℝ => lower a b q.1) p := by fun_prop [lower]
  have hg' : ContinuousAt (fun q : ℝ × ℝ => gap a b' c d' q.1) p := by
    fun_prop [gap, upper, lower]
  have hg : ContinuousAt (fun q : ℝ × ℝ => gap a b c d q.1) p := by
    fun_prop [gap, upper, lower]
  have hr := hg'.div hg hden
  have hy : ContinuousAt (fun q : ℝ × ℝ => lower a b' q.1 +
      (q.2 - lower a b q.1) * (gap a b' c d' q.1 / gap a b c d q.1)) p := by
    exact hl'.add ((continuousAt_snd.sub hl).mul hr)
  have hc : ContinuousAt (stripChart a b c d b' d') p := by
    change ContinuousAt (fun q : ℝ × ℝ => (q.1, lower a b' q.1 +
      (q.2 - lower a b q.1) * (gap a b' c d' q.1 / gap a b c d q.1))) p
    exact continuousAt_fst.prodMk hy
  exact hc.continuousWithinAt

private theorem continuousOn_stripInverseChart {R a b c d b' d' : ℝ}
    (hgap : ∀ r, R ≤ r → 0 < gap a b' c d' r) :
    ContinuousOn (stripInverseChart a b c d b' d') (closedStrip R a b' c d') := by
  exact continuousOn_stripChart (R := R) (a := a) (b := b') (c := c) (d := d')
    (b' := b) (d' := d) hgap

/-- The actual closed-strip chart is a homeomorphism of the source and target
closed subtypes whenever both gap functions stay strictly positive on the ray. -/
private def closedStripHomeomorph (R a b c d b' d' : ℝ)
    (hgap : ∀ r, R ≤ r → 0 < gap a b c d r)
    (hgap' : ∀ r, R ≤ r → 0 < gap a b' c d' r) :
    {p : ℝ × ℝ // p ∈ closedStrip R a b c d} ≃ₜ
      {p : ℝ × ℝ // p ∈ closedStrip R a b' c d'} := by
  let S := {p : ℝ × ℝ // p ∈ closedStrip R a b c d}
  let T := {p : ℝ × ℝ // p ∈ closedStrip R a b' c d'}
  let f : S → T := fun p => ⟨stripChart a b c d b' d' p.1,
    chart_mem_strip p.2 hgap hgap'⟩
  let g : T → S := fun p => ⟨stripInverseChart a b c d b' d' p.1,
    inverse_mem_strip p.2 hgap hgap'⟩
  have hfg : Function.LeftInverse g f := by
    intro p
    apply Subtype.ext
    exact inverse_left (ne_of_gt (hgap' p.1.1 p.2.1)) (ne_of_gt (hgap p.1.1 p.2.1))
  have hgf : Function.LeftInverse f g := by
    intro p
    apply Subtype.ext
    exact inverse_right (ne_of_gt (hgap p.1.1 p.2.1)) (ne_of_gt (hgap' p.1.1 p.2.1))
  have hfval : Continuous (fun p : S => stripChart a b c d b' d' p.1) := by
    have hc := (continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_stripChart (R := R) (a := a) (b := b) (c := c) (d := d)
        (b' := b') (d' := d') hgap))
    change Continuous (fun p : S => stripChart a b c d b' d' p.1) at hc
    exact hc
  have hgval : Continuous (fun p : T => stripInverseChart a b c d b' d' p.1) := by
    have hc := (continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_stripInverseChart (R := R) (a := a) (b := b) (c := c) (d := d)
        (b' := b') (d' := d') hgap'))
    change Continuous (fun p : T => stripInverseChart a b c d b' d' p.1) at hc
    exact hc
  have hf : Continuous f := by
    exact hfval.subtype_mk _
  have hg : Continuous g := by
    exact hgval.subtype_mk _
  let e : S ≃ T := ⟨f, g, hfg, hgf⟩
  exact Homeomorph.mk e hf hg

private theorem closedStripHomeomorph_radius (R a b c d b' d' : ℝ)
    (hgap : ∀ r, R ≤ r → 0 < gap a b c d r)
    (hgap' : ∀ r, R ≤ r → 0 < gap a b' c d' r)
    (p : {p : ℝ × ℝ // p ∈ closedStrip R a b c d}) :
    (closedStripHomeomorph R a b c d b' d' hgap hgap' p).1.1 = p.1.1 := rfl

private def stripToFacePieceHomeomorph {n : ℕ} (R : ℝ)
    (A : Fin (n + 1) → ℝ → ℝ) (i : Fin n)
    (hsub : intervalStrip R A i ⊆ faceSector R) :
    {p : ℝ × ℝ // p ∈ intervalStrip R A i} ≃ₜ
      {p : {p : ℝ × ℝ // p ∈ faceSector R} // p ∈ facePiece R A i} := by
  let S := {p : ℝ × ℝ // p ∈ intervalStrip R A i}
  let T := {p : {p : ℝ × ℝ // p ∈ faceSector R} // p ∈ facePiece R A i}
  let f : S → T := fun p => ⟨⟨p.1, hsub p.2⟩, p.2⟩
  let g : T → S := fun p => ⟨p.1.1, p.2⟩
  have hfg : Function.LeftInverse g f := by intro p; apply Subtype.ext; rfl
  have hgf : Function.LeftInverse f g := by
    intro p
    apply Subtype.ext
    apply Subtype.ext
    rfl
  have hbase : Continuous (fun p : S => (⟨p.1, hsub p.2⟩ : {p : ℝ × ℝ // p ∈ faceSector R})) := by
    exact continuous_subtype_val.subtype_mk _
  have hf : Continuous f := hbase.subtype_mk _
  have hval : Continuous (fun p : T => p.1.1) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hg : Continuous g := hval.subtype_mk _
  let e : S ≃ T := ⟨f, g, hfg, hgf⟩
  exact Homeomorph.mk e hf hg

private def affineFacePieceHomeomorph {n : ℕ} (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ) (i : Fin n)
    (hsourceSub : intervalStrip R (affineGraph a b) i ⊆ faceSector R)
    (htargetSub : intervalStrip R (affineGraph a b') i ⊆ faceSector R)
    (hsourceGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r)
    (htargetGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r) :
    {p : {p : ℝ × ℝ // p ∈ faceSector R} // p ∈ facePiece R (affineGraph a b) i} ≃ₜ
      {p : {p : ℝ × ℝ // p ∈ faceSector R} // p ∈ facePiece R (affineGraph a b') i} := by
  let eS := stripToFacePieceHomeomorph R (affineGraph a b) i hsourceSub
  let eT := stripToFacePieceHomeomorph R (affineGraph a b') i htargetSub
  have heqS : closedStrip R (a i.castSucc) (b i.castSucc)
      (a i.succ) (b i.succ) = intervalStrip R (affineGraph a b) i := by
    ext p
    rfl
  have heqT : closedStrip R (a i.castSucc) (b' i.castSucc)
      (a i.succ) (b' i.succ) = intervalStrip R (affineGraph a b') i := by
    ext p
    rfl
  let stripH := closedStripHomeomorph R (a i.castSucc) (b i.castSucc)
    (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) hsourceGap htargetGap
  have hS : {p : ℝ × ℝ // p ∈ closedStrip R (a i.castSucc) (b i.castSucc)
      (a i.succ) (b i.succ)} ≃ₜ
      {p : ℝ × ℝ // p ∈ intervalStrip R (affineGraph a b) i} := by
    exact Homeomorph.setCongr (by simp [heqS])
  have hT : {p : ℝ × ℝ // p ∈ closedStrip R (a i.castSucc) (b' i.castSucc)
      (a i.succ) (b' i.succ)} ≃ₜ
      {p : ℝ × ℝ // p ∈ intervalStrip R (affineGraph a b') i} := by
    exact Homeomorph.setCongr (by simp [heqT])
  exact eS.symm.trans (hS.symm.trans (stripH.trans (hT.trans eT)))

private theorem affineFacePieceHomeomorph_apply {n : ℕ} (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ) (i : Fin n)
    (hsourceSub : intervalStrip R (affineGraph a b) i ⊆ faceSector R)
    (htargetSub : intervalStrip R (affineGraph a b') i ⊆ faceSector R)
    (hsourceGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r)
    (htargetGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r)
    (p : {p : {p : ℝ × ℝ // p ∈ faceSector R} //
      p ∈ facePiece R (affineGraph a b) i}) :
    (affineFacePieceHomeomorph R a b b' i hsourceSub htargetSub
      hsourceGap htargetGap p).val.1 =
        stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p.1.1 := by
  rfl

private theorem affineFacePieceHomeomorph_symm_apply {n : ℕ} (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ) (i : Fin n)
    (hsourceSub : intervalStrip R (affineGraph a b) i ⊆ faceSector R)
    (htargetSub : intervalStrip R (affineGraph a b') i ⊆ faceSector R)
    (hsourceGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r)
    (htargetGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r)
    (p : {p : {p : ℝ × ℝ // p ∈ faceSector R} //
      p ∈ facePiece R (affineGraph a b') i}) :
    ((affineFacePieceHomeomorph R a b b' i hsourceSub htargetSub
      hsourceGap htargetGap).symm p).val.1 =
        stripInverseChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p.1.1 := by
  rfl

/-- A finite adjacent chain of closed intervals covers the interval between its
endpoints. This is proved by searching the chain, not supplied as a cover
certificate. -/
private theorem exists_adjacent_interval_cover :
    ∀ n : ℕ, 0 < n → ∀ (A : Fin (n + 1) → ℝ) (y : ℝ),
      A 0 ≤ y → y ≤ A ⟨n, by omega⟩ →
      (∀ i : Fin n, A i.castSucc ≤ A i.succ) →
      ∃ i : Fin n, A i.castSucc ≤ y ∧ y ≤ A i.succ := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ n ih =>
      intro hn A y hstart hend hmono
      let one : Fin (n + 2) := ⟨1, by omega⟩
      by_cases hy : y ≤ A one
      · refine ⟨⟨0, by omega⟩, ?_, ?_⟩
        · simpa using hstart
        · simpa [one] using hy
      · have hone : A one < y := lt_of_not_ge hy
        by_cases hn0 : n = 0
        · subst n
          have hend' : y ≤ A one := by simpa [one] using hend
          exact (hy hend').elim
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
          let B : Fin (n + 1) → ℝ := fun i => A i.succ
          obtain ⟨j, hj₁, hj₂⟩ := ih hnpos B y (by
            simpa [B, one] using hone.le) (by
            simpa [B] using hend) (by
            intro k
            have hk := hmono k.succ
            simpa [B] using hk)
          refine ⟨j.succ, ?_, hj₂⟩
          simpa [B] using hj₁

private theorem strictMono_finFamily {n : ℕ} (A : Fin (n + 1) → ℝ)
    (hstep : ∀ i : Fin n, A i.castSucc < A i.succ) : StrictMono A :=
  Fin.strictMono_iff_lt_succ.mpr hstep

private theorem affineGraph_strictMono_on_ray {n : ℕ} (R r : ℝ)
    (a b : Fin (n + 1) → ℝ)
    (hr : R ≤ r)
    (hgap : ∀ i : Fin n, R ≤ r → 0 < affineGraphGap a b i r) :
    StrictMono (fun i : Fin (n + 1) => affineGraph a b i r) := by
  apply strictMono_finFamily
  intro i
  have hi := hgap i hr
  dsimp [affineGraphGap, affineGraph] at hi ⊢
  exact sub_pos.mp hi

private theorem intervalStrip_subset_faceSector {n : ℕ} (R : ℝ)
    (A : Fin (n + 1) → ℝ → ℝ) (i : Fin n)
    (hfirst : ∀ r, A 0 r = -r)
    (hlast : ∀ r, A ⟨n, by omega⟩ r = r)
    (hstrict : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => A k r)) :
    intervalStrip R A i ⊆ faceSector R := by
  intro p hp
  rcases hp with ⟨hr, hlo, hhi⟩
  have hm := hstrict p.1 hr
  have hzle : (0 : Fin (n + 1)) ≤ i.castSucc := Fin.zero_le _
  have hile : i.succ ≤ (⟨n, by omega⟩ : Fin (n + 1)) := by
    apply Fin.le_iff_val_le_val.mpr
    change i.val + 1 ≤ n
    exact Nat.succ_le_iff.mpr i.isLt
  have hleft := hm.monotone hzle
  have hright := hm.monotone hile
  refine ⟨hr, ?_, ?_⟩
  · rw [hfirst] at hleft
    exact hleft.trans hlo
  · rw [hlast] at hright
    exact hhi.trans hright

/-- The actual sector is covered by the adjacent strips when the endpoint
graphs are its two diagonal rays. -/
private theorem faceSector_subset_adjacentStrips {n : ℕ} (hn : 0 < n) (R : ℝ)
    (A : Fin (n + 1) → ℝ → ℝ)
    (hfirst : ∀ r, A 0 r = -r)
    (hlast : ∀ r, A ⟨n, by omega⟩ r = r)
    (hstep : ∀ r, R ≤ r → ∀ i : Fin n, A i.castSucc r < A i.succ r) :
    faceSector R ⊆ ⋃ i : Fin n, intervalStrip R A i := by
  intro p hp
  rcases hp with ⟨hr, hlo, hhi⟩
  have hmono : ∀ i : Fin n, A i.castSucc p.1 ≤ A i.succ p.1 :=
    fun i => (hstep p.1 hr i).le
  obtain ⟨i, hi₁, hi₂⟩ := exists_adjacent_interval_cover n hn
    (fun i => A i p.1) p.2 (by simpa [hfirst] using hlo)
    (by simpa [hlast] using hhi) hmono
  exact mem_iUnion.mpr ⟨i, ⟨hr, hi₁, hi₂⟩⟩

private theorem affineGraphFamily_face_cover {n : ℕ} (hn : 0 < n) (R : ℝ)
    (a b : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r) :
    faceSector R ⊆ ⋃ i : Fin n, intervalStrip R (affineGraph a b) i := by
  apply faceSector_subset_adjacentStrips hn R (affineGraph a b) hfirst hlast
  intro r hr i
  have h := hgap i r hr
  dsimp [affineGraphGap] at h
  exact sub_pos.mp h

/-- Intersections of members of a strictly ordered interval family are exactly
the same interval or their shared endpoint. In particular non-neighbors cannot
overlap. -/
private theorem adjacent_interval_overlap {n : ℕ} {R : ℝ}
    {A : Fin (n + 1) → ℝ → ℝ} {i j : Fin n} {p : ℝ × ℝ}
    (hstrict : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => A k r))
    (hi : p ∈ intervalStrip R A i) (hj : p ∈ intervalStrip R A j) :
    i = j ∨
      (i.val + 1 = j.val ∧ p.2 = A ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ p.1) ∨
      (j.val + 1 = i.val ∧ p.2 = A ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ p.1) := by
  rcases hi with ⟨hr, hil, hiu⟩
  rcases hj with ⟨_, hjl, hju⟩
  by_cases heq : i = j
  · exact Or.inl heq
  · rcases lt_or_gt_of_ne heq with hij | hji
    · have hval : i.val < j.val := by omega
      let u : Fin (n + 1) := ⟨i.val + 1, by omega⟩
      let l : Fin (n + 1) := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      have hul : u ≤ l := Fin.le_iff_val_le_val.mpr (by simp [u, l]; omega)
      by_cases heq' : i.val + 1 = j.val
      · have hidx : u = l := by ext; simp [u, l, heq']
        have hUi : i.succ = u := by ext; simp [u]
        have hLj : j.castSucc = l := by ext; simp [l]
        have hyhi : p.2 ≤ A u p.1 := by rw [← hUi]; exact hiu
        have hylo : A l p.1 ≤ p.2 := by rw [← hLj]; exact hjl
        have hyu : p.2 = A u p.1 := le_antisymm hyhi (by simpa [hidx] using hylo)
        have hy : p.2 = A l p.1 := by simpa [hidx] using hyu
        exact Or.inr (Or.inl ⟨heq', hy⟩)
      · have hult : u < l := lt_of_le_of_ne hul (by
          intro h
          apply heq'
          have hv := congrArg Fin.val h
          dsimp [u, l] at hv
          omega)
        have horder := hstrict p.1 hr hult
        have hy : A l p.1 ≤ A u p.1 := le_trans hjl hiu
        exact (not_lt_of_ge hy horder).elim
    · have hval : j.val < i.val := by omega
      let u : Fin (n + 1) := ⟨j.val + 1, by omega⟩
      let l : Fin (n + 1) := ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩
      have hul : u ≤ l := Fin.le_iff_val_le_val.mpr (by simp [u, l]; omega)
      by_cases heq' : j.val + 1 = i.val
      · have hidx : u = l := by ext; simp [u, l, heq']
        have hUj : j.succ = u := by ext; simp [u]
        have hLi : i.castSucc = l := by ext; simp [l]
        have hyhi : p.2 ≤ A u p.1 := by rw [← hUj]; exact hju
        have hylo : A l p.1 ≤ p.2 := by rw [← hLi]; exact hil
        have hyu : p.2 = A u p.1 := le_antisymm hyhi (by simpa [hidx] using hylo)
        have hy : p.2 = A l p.1 := by simpa [hidx] using hyu
        exact Or.inr (Or.inr ⟨heq', hy⟩)
      · have hult : u < l := lt_of_le_of_ne hul (by
          intro h
          apply heq'
          have hv := congrArg Fin.val h
          dsimp [u, l] at hv
          omega)
        have horder := hstrict p.1 hr hult
        have hy : A l p.1 ≤ A u p.1 := le_trans hil hju
        exact (not_lt_of_ge hy horder).elim

private theorem adjacent_strip_charts_agree {n : ℕ} {R : ℝ}
    (a b b' : Fin (n + 1) → ℝ) (i j : Fin n) (p : ℝ × ℝ)
    (hstrict : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => affineGraph a b k r))
    (hi : p ∈ intervalStrip R (affineGraph a b) i)
    (hj : p ∈ intervalStrip R (affineGraph a b) j)
    (hsourceGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r)
    (hsourceGapJ : ∀ r, R ≤ r →
      0 < gap (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ) r)
    (_htargetGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r)
    (htargetGapJ : ∀ r, R ≤ r →
      0 < gap (a j.castSucc) (b' j.castSucc) (a j.succ) (b' j.succ) r) :
    stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
      (b' i.castSucc) (b' i.succ) p =
    stripChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
      (b' j.castSucc) (b' j.succ) p := by
  rcases adjacent_interval_overlap hstrict hi hj with heq | hnext | hprev
  · subst j
    rfl
  · rcases hnext with ⟨hval, hy⟩
    have hidx : i.succ = j.castSucc := by
      apply Fin.ext
      simp
      omega
    have hyi : p.2 = upper (a i.succ) (b i.succ) p.1 := by
      calc
        p.2 = affineGraph a b ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ p.1 := hy
        _ = affineGraph a b j.castSucc p.1 := rfl
        _ = affineGraph a b i.succ p.1 := by rw [← hidx]
        _ = upper (a i.succ) (b i.succ) p.1 := rfl
    have hpointI : p = (p.1, upper (a i.succ) (b i.succ) p.1) := by
      apply Prod.ext <;> simp [hyi]
    have hpointJ : p = (p.1, lower (a j.castSucc) (b j.castSucc) p.1) := by
      apply Prod.ext
      · rfl
      · calc
          p.2 = upper (a i.succ) (b i.succ) p.1 := hyi
          _ = lower (a j.castSucc) (b j.castSucc) p.1 := by rw [hidx]; rfl
    calc
      stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p =
        stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) (p.1, upper (a i.succ) (b i.succ) p.1) := by rw [hpointI]
      _ = (p.1, upper (a i.succ) (b' i.succ) p.1) :=
        stripChart_upper_anchor (a := a i.castSucc) (b := b i.castSucc)
          (c := a i.succ) (d := b i.succ) (b' := b' i.castSucc)
          (d' := b' i.succ) (r := p.1) (ne_of_gt (hsourceGap p.1 hi.1))
      _ = (p.1, lower (a j.castSucc) (b' j.castSucc) p.1) := by
        rw [hidx]
        simp [lower, upper]
      _ = stripChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
          (b' j.castSucc) (b' j.succ) p := by
        rw [hpointJ]
        exact (stripChart_lower_anchor (a := a j.castSucc) (b := b j.castSucc)
          (c := a j.succ) (d := b j.succ) (b' := b' j.castSucc)
          (d' := b' j.succ) (r := p.1)).symm
  · rcases hprev with ⟨hval, hy⟩
    have hidx : j.succ = i.castSucc := by
      apply Fin.ext
      simp
      omega
    have hyj : p.2 = upper (a j.succ) (b j.succ) p.1 := by
      calc
        p.2 = affineGraph a b ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ p.1 := hy
        _ = affineGraph a b i.castSucc p.1 := rfl
        _ = affineGraph a b j.succ p.1 := by rw [← hidx]
        _ = upper (a j.succ) (b j.succ) p.1 := rfl
    have hpointJ : p = (p.1, upper (a j.succ) (b j.succ) p.1) := by
      apply Prod.ext <;> simp [hyj]
    have hpointI : p = (p.1, lower (a i.castSucc) (b i.castSucc) p.1) := by
      apply Prod.ext
      · rfl
      · calc
          p.2 = upper (a j.succ) (b j.succ) p.1 := hyj
          _ = lower (a i.castSucc) (b i.castSucc) p.1 := by rw [hidx]; rfl
    calc
      stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p =
        stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) (p.1, lower (a i.castSucc) (b i.castSucc) p.1) := by rw [hpointI]
      _ = (p.1, lower (a i.castSucc) (b' i.castSucc) p.1) :=
        stripChart_lower_anchor (a := a i.castSucc) (b := b i.castSucc)
          (c := a i.succ) (d := b i.succ) (b' := b' i.castSucc)
          (d' := b' i.succ) (r := p.1)
      _ = (p.1, upper (a j.succ) (b' j.succ) p.1) := by
        rw [hidx]
        simp [lower, upper]
      _ = stripChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
          (b' j.castSucc) (b' j.succ) p := by
        rw [hpointJ]
        exact (stripChart_upper_anchor (a := a j.castSucc) (b := b j.castSucc)
          (c := a j.succ) (d := b j.succ) (b' := b' j.castSucc)
          (d' := b' j.succ) (r := p.1)
          (ne_of_gt (hsourceGapJ p.1 hi.1))).symm

private theorem adjacent_strip_inverse_charts_agree {n : ℕ} {R : ℝ}
    (a b b' : Fin (n + 1) → ℝ) (i j : Fin n) (p : ℝ × ℝ)
    (hstrict : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => affineGraph a b' k r))
    (hi : p ∈ intervalStrip R (affineGraph a b') i)
    (hj : p ∈ intervalStrip R (affineGraph a b') j)
    (hsourceGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r)
    (hsourceGapJ : ∀ r, R ≤ r →
      0 < gap (a j.castSucc) (b' j.castSucc) (a j.succ) (b' j.succ) r)
    (htargetGap : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r)
    (htargetGapJ : ∀ r, R ≤ r →
      0 < gap (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ) r) :
    stripInverseChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
      (b' i.castSucc) (b' i.succ) p =
    stripInverseChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
      (b' j.castSucc) (b' j.succ) p := by
  simpa [stripInverseChart, stripChart] using
    adjacent_strip_charts_agree (R := R) a b' b i j p hstrict hi hj
      hsourceGap hsourceGapJ htargetGap htargetGapJ

private structure AffineFaceSectorHomeomorphData {n : ℕ} (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r) where
  homeo : {p : ℝ × ℝ // p ∈ faceSector R} ≃ₜ {p : ℝ × ℝ // p ∈ faceSector R}
  on_piece : ∀ (i : Fin n) (p : {p : ℝ × ℝ // p ∈ faceSector R}),
    p ∈ facePiece R (affineGraph a b) i →
      (homeo p).1 = stripChart (a i.castSucc) (b i.castSucc)
        (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) p.1

/-- Glue the actual affine strip homeomorphisms into a homeomorphism of the
whole closed face sector. The source and target covers and all overlaps are
derived from the ordered graph families. -/
private def affineFaceSectorHomeomorphWithPieces {n : ℕ} (hn : 0 < n) (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r) :
    AffineFaceSectorHomeomorphData R a b b' hfirst hlast hfirst' hlast' hgap hgap' := by
  let S := {p : ℝ × ℝ // p ∈ faceSector R}
  let T := {p : ℝ × ℝ // p ∈ faceSector R}
  let C : Fin n → Set S := fun i => facePiece R (affineGraph a b) i
  let D : Fin n → Set T := fun i => facePiece R (affineGraph a b') i
  have hstrict : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => affineGraph a b k r) := by
    intro r hr
    exact affineGraph_strictMono_on_ray R r a b hr (fun i _ => hgap i r hr)
  have hstrict' : ∀ r, R ≤ r → StrictMono (fun k : Fin (n + 1) => affineGraph a b' k r) := by
    intro r hr
    exact affineGraph_strictMono_on_ray R r a b' hr (fun i _ => hgap' i r hr)
  have hsourceSub (i : Fin n) : intervalStrip R (affineGraph a b) i ⊆ faceSector R :=
    intervalStrip_subset_faceSector R (affineGraph a b) i hfirst hlast hstrict
  have htargetSub (i : Fin n) : intervalStrip R (affineGraph a b') i ⊆ faceSector R :=
    intervalStrip_subset_faceSector R (affineGraph a b') i hfirst' hlast' hstrict'
  have hgapLocal (i : Fin n) : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r := by
    intro r hr
    simpa [affineGraphGap, affineGraph, gap, upper, lower] using hgap i r hr
  have hgapLocal' (i : Fin n) : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r := by
    intro r hr
    simpa [affineGraphGap, affineGraph, gap, upper, lower] using hgap' i r hr
  have hCclosed : ∀ i, IsClosed (C i) := by
    intro i
    have heq : C i = {p : S | affineGraph a b i.castSucc p.1.1 ≤ p.1.2 ∧
        p.1.2 ≤ affineGraph a b i.succ p.1.1} := by
      ext p
      change p.1 ∈ intervalStrip R (affineGraph a b) i ↔ _
      constructor
      · rintro ⟨_, hl, hu⟩
        exact ⟨hl, hu⟩
      · rintro ⟨hl, hu⟩
        exact ⟨p.2.1, hl, hu⟩
    rw [heq]
    have hA : Continuous (fun p : S => affineGraph a b i.castSucc p.1.1) := by
      fun_prop [affineGraph, lower]
    have hY : Continuous (fun p : S => p.1.2) := by fun_prop
    have hU : Continuous (fun p : S => affineGraph a b i.succ p.1.1) := by
      fun_prop [affineGraph, lower]
    exact (isClosed_le hA hY).inter (isClosed_le hY hU)
  have hDclosed : ∀ i, IsClosed (D i) := by
    intro i
    have heq : D i = {p : T | affineGraph a b' i.castSucc p.1.1 ≤ p.1.2 ∧
        p.1.2 ≤ affineGraph a b' i.succ p.1.1} := by
      ext p
      change p.1 ∈ intervalStrip R (affineGraph a b') i ↔ _
      constructor
      · rintro ⟨_, hl, hu⟩
        exact ⟨hl, hu⟩
      · rintro ⟨hl, hu⟩
        exact ⟨p.2.1, hl, hu⟩
    rw [heq]
    have hA : Continuous (fun p : T => affineGraph a b' i.castSucc p.1.1) := by
      fun_prop [affineGraph, lower]
    have hY : Continuous (fun p : T => p.1.2) := by fun_prop
    have hU : Continuous (fun p : T => affineGraph a b' i.succ p.1.1) := by
      fun_prop [affineGraph, lower]
    exact (isClosed_le hA hY).inter (isClosed_le hY hU)
  have hCcover : ∀ x : S, ∃ i, x ∈ C i := by
    intro x
    have hxcover := faceSector_subset_adjacentStrips hn R (affineGraph a b)
      hfirst hlast (by
        intro r hr i
        have h := hgap i r hr
        dsimp [affineGraphGap] at h
        exact sub_pos.mp h)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hxcover x.2)
    refine ⟨i, ?_⟩
    change x.1 ∈ intervalStrip R (affineGraph a b) i
    exact hi
  have hDcover : ∀ y : T, ∃ i, y ∈ D i := by
    intro y
    have hycover := faceSector_subset_adjacentStrips hn R (affineGraph a b')
      hfirst' hlast' (by
        intro r hr i
        have h := hgap' i r hr
        dsimp [affineGraphGap] at h
        exact sub_pos.mp h)
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hycover y.2)
    refine ⟨i, ?_⟩
    change y.1 ∈ intervalStrip R (affineGraph a b') i
    exact hi
  let piece : ∀ i, C i ≃ₜ D i := fun i =>
    affineFacePieceHomeomorph R a b b' i (hsourceSub i) (htargetSub i)
      (hgapLocal i) (hgapLocal' i)
  have hforward : ∀ i j (x : S) (hxi : x ∈ C i) (hxj : x ∈ C j),
      (piece i ⟨x, hxi⟩).val = (piece j ⟨x, hxj⟩).val := by
    intro i j x hxi hxj
    apply Subtype.ext
    have hxi' : x.1 ∈ intervalStrip R (affineGraph a b) i := by
      change x.1 ∈ intervalStrip R (affineGraph a b) i at hxi
      exact hxi
    have hxj' : x.1 ∈ intervalStrip R (affineGraph a b) j := by
      change x.1 ∈ intervalStrip R (affineGraph a b) j at hxj
      exact hxj
    have hagree := adjacent_strip_charts_agree a b b' i j x.1
      hstrict hxi' hxj' (hgapLocal i) (hgapLocal j) (hgapLocal' i)
      (hgapLocal' j)
    have hpi := affineFacePieceHomeomorph_apply R a b b' i (hsourceSub i)
      (htargetSub i) (hgapLocal i) (hgapLocal' i) ⟨x, hxi⟩
    have hpj := affineFacePieceHomeomorph_apply R a b b' j (hsourceSub j)
      (htargetSub j) (hgapLocal j) (hgapLocal' j) ⟨x, hxj⟩
    change stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
        (b' i.castSucc) (b' i.succ) x.1 =
      stripChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
        (b' j.castSucc) (b' j.succ) x.1
    rw [← hpi, ← hpj]
    exact hagree
  have hinverse : ∀ i j (y : T) (hyi : y ∈ D i) (hyj : y ∈ D j),
      ((piece i).symm ⟨y, hyi⟩).val = ((piece j).symm ⟨y, hyj⟩).val := by
    intro i j y hyi hyj
    apply Subtype.ext
    have hyi' : y.1 ∈ intervalStrip R (affineGraph a b') i := by
      change y.1 ∈ intervalStrip R (affineGraph a b') i at hyi
      exact hyi
    have hyj' : y.1 ∈ intervalStrip R (affineGraph a b') j := by
      change y.1 ∈ intervalStrip R (affineGraph a b') j at hyj
      exact hyj
    have hagree := adjacent_strip_inverse_charts_agree a b b' i j y.1
      hstrict' hyi' hyj' (hgapLocal' i) (hgapLocal' j) (hgapLocal i)
      (hgapLocal j)
    have hpi := affineFacePieceHomeomorph_symm_apply R a b b' i (hsourceSub i)
      (htargetSub i) (hgapLocal i) (hgapLocal' i) ⟨y, hyi⟩
    have hpj := affineFacePieceHomeomorph_symm_apply R a b b' j (hsourceSub j)
      (htargetSub j) (hgapLocal j) (hgapLocal' j) ⟨y, hyj⟩
    change stripInverseChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
        (b' i.castSucc) (b' i.succ) y.1 =
      stripInverseChart (a j.castSucc) (b j.castSucc) (a j.succ) (b j.succ)
        (b' j.castSucc) (b' j.succ) y.1
    rw [← hpi, ← hpj]
    exact hagree
  let H := finiteClosedCover_homeomorph (faceSector R) (faceSector R)
    C D hCclosed hDclosed hCcover hDcover piece hforward hinverse
  have hpiece (i : Fin n) (p : S) (hp : p ∈ C i) :
      (H p).1 = stripChart (a i.castSucc) (b i.castSucc)
        (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) p.1 := by
    calc
      (H p).1 = (piece i ⟨p, hp⟩).val.val :=
        finiteClosedCover_homeomorph_apply_piece (faceSector R) (faceSector R)
          C D hCclosed hDclosed hCcover hDcover piece hforward hinverse i p hp
      _ = stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p.1 :=
        affineFacePieceHomeomorph_apply R a b b' i (hsourceSub i)
          (htargetSub i) (hgapLocal i) (hgapLocal' i) ⟨p, hp⟩
  exact ⟨H, hpiece⟩

private def affineFaceSectorHomeomorph {n : ℕ} (hn : 0 < n) (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r) :
    {p : ℝ × ℝ // p ∈ faceSector R} ≃ₜ {p : ℝ × ℝ // p ∈ faceSector R} :=
  (affineFaceSectorHomeomorphWithPieces hn R a b b' hfirst hlast hfirst' hlast'
    hgap hgap').homeo

private theorem affineFaceSectorHomeomorph_radius {n : ℕ} (hn : 0 < n) (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r)
    (p : {p : ℝ × ℝ // p ∈ faceSector R}) :
    (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 = p.1.1 := by
  classical
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (affineGraphFamily_face_cover hn R a b hfirst hlast hgap p.2)
  have hp : p ∈ facePiece R (affineGraph a b) i := by
    change p.1 ∈ intervalStrip R (affineGraph a b) i
    exact hi
  have hlocal := (affineFaceSectorHomeomorphWithPieces hn R a b b'
    hfirst hlast hfirst' hlast' hgap hgap').on_piece i p hp
  calc
    (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 =
        (stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
          (b' i.castSucc) (b' i.succ) p.1).1 := congrArg Prod.fst hlocal
    _ = p.1.1 := rfl

private theorem affineFaceSectorHomeomorph_on_piece {n : ℕ} (hn : 0 < n) (R : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r)
    (i : Fin n) (p : {p : ℝ × ℝ // p ∈ faceSector R})
    (hp : p ∈ facePiece R (affineGraph a b) i) :
    (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1 =
      stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
        (b' i.castSucc) (b' i.succ) p.1 := by
  simpa [affineFaceSectorHomeomorph] using
    (affineFaceSectorHomeomorphWithPieces hn R a b b'
      hfirst hlast hfirst' hlast' hgap hgap').on_piece i p hp

private theorem affineFaceSectorHomeomorph_lower_corner {n : ℕ} (hn : 0 < n) (R r : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r)
    (hr : R ≤ r) (hr0 : 0 ≤ r) :
    (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap'
      ⟨(r, -r), ⟨hr, le_rfl, by linarith⟩⟩).1 = (r, -r) := by
  let i0 : Fin n := ⟨0, by omega⟩
  have hstep : affineGraph a b i0.castSucc r < affineGraph a b i0.succ r := by
    have hg := hgap i0 r hr
    dsimp [affineGraphGap] at hg
    exact sub_pos.mp hg
  let p : {p : ℝ × ℝ // p ∈ faceSector R} :=
    ⟨(r, -r), ⟨hr, le_rfl, by linarith⟩⟩
  have hp : p ∈ facePiece R (affineGraph a b) i0 := by
    change (r, -r) ∈ intervalStrip R (affineGraph a b) i0
    refine ⟨hr, ?_, ?_⟩
    · change affineGraph a b i0.castSucc r ≤ -r
      rw [show i0.castSucc = (0 : Fin (n + 1)) by ext; simp [i0], hfirst]
    · change -r ≤ affineGraph a b i0.succ r
      rw [show i0.castSucc = (0 : Fin (n + 1)) by ext; simp [i0], hfirst] at hstep
      exact hstep.le
  have hmap := affineFaceSectorHomeomorph_on_piece hn R a b b'
    hfirst hlast hfirst' hlast' hgap hgap' i0 p hp
  apply Prod.ext
  · rfl
  · rw [hmap]
    change (stripChart (a i0.castSucc) (b i0.castSucc) (a i0.succ) (b i0.succ)
      (b' i0.castSucc) (b' i0.succ) (r, -r)).2 = -r
    have hsourceAnchor : (r, -r) =
        (r, lower (a i0.castSucc) (b i0.castSucc) r) := by
      apply Prod.ext
      · rfl
      · change -r = affineGraph a b i0.castSucc r
        rw [show i0.castSucc = (0 : Fin (n + 1)) by ext; simp [i0]]
        exact (hfirst r).symm
    rw [hsourceAnchor, stripChart_lower_anchor]
    change lower (a i0.castSucc) (b' i0.castSucc) r = -r
    rw [show i0.castSucc = (0 : Fin (n + 1)) by ext; simp [i0]]
    exact hfirst' r

private theorem affineFaceSectorHomeomorph_upper_corner {n : ℕ} (hn : 0 < n) (R r : ℝ)
    (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r)
    (hr : R ≤ r) (hr0 : 0 ≤ r) :
    (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap'
      ⟨(r, r), ⟨hr, by linarith, le_rfl⟩⟩).1 = (r, r) := by
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have hisucc : ilast.succ = (⟨n, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    simp [ilast]
    omega
  have hstep : affineGraph a b ilast.castSucc r < affineGraph a b ⟨n, by omega⟩ r := by
    have hg := hgap ilast r hr
    dsimp [affineGraphGap] at hg
    rw [hisucc] at hg
    exact sub_pos.mp hg
  let p : {p : ℝ × ℝ // p ∈ faceSector R} :=
    ⟨(r, r), ⟨hr, by linarith, le_rfl⟩⟩
  have hp : p ∈ facePiece R (affineGraph a b) ilast := by
    change (r, r) ∈ intervalStrip R (affineGraph a b) ilast
    refine ⟨hr, ?_, ?_⟩
    · change affineGraph a b ilast.castSucc r ≤ r
      exact hstep.le.trans_eq (hlast r)
    · change r ≤ affineGraph a b ilast.succ r
      simpa only [hisucc] using (hlast r).ge
  have hmap := affineFaceSectorHomeomorph_on_piece hn R a b b'
    hfirst hlast hfirst' hlast' hgap hgap' ilast p hp
  have hgaplast : 0 < gap (a ilast.castSucc) (b ilast.castSucc)
      (a ilast.succ) (b ilast.succ) r := by
    simpa [affineGraphGap, affineGraph, gap, upper, lower] using (hgap ilast r hr)
  apply Prod.ext
  · rfl
  · rw [hmap]
    change (stripChart (a ilast.castSucc) (b ilast.castSucc) (a ilast.succ) (b ilast.succ)
      (b' ilast.castSucc) (b' ilast.succ) (r, r)).2 = r
    have hsourceAnchor : (r, r) =
        (r, upper (a ilast.succ) (b ilast.succ) r) := by
      apply Prod.ext
      · rfl
      · change r = affineGraph a b ilast.succ r
        simpa only [hisucc] using (hlast r).symm
    rw [hsourceAnchor, stripChart_upper_anchor
      (a := a ilast.castSucc) (b := b ilast.castSucc)
      (c := a ilast.succ) (d := b ilast.succ)
      (b' := b' ilast.castSucc) (d' := b' ilast.succ)
      (ne_of_gt hgaplast)]
    change affineGraph a b' ilast.succ r = r
    simpa only [hisucc] using hlast' r

private theorem realSign_mul_pos (x k : ℝ) (hk : 0 < k) :
    Real.sign (x * k) = Real.sign x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · by_cases hx : 0 < x
    · rw [Real.sign_of_pos (mul_pos hx hk), Real.sign_of_pos hx]
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hxneg hk), Real.sign_of_neg hxneg]

private theorem stripChart_upperDifference (a b c d b' d' r y : ℝ)
    (hden : gap a b c d r ≠ 0) :
  (stripChart a b c d b' d' (r, y)).2 - upper c d' r =
      (y - upper c d r) * (gap a b' c d' r / gap a b c d r) := by
  dsimp [stripChart]
  field_simp [hden]
  dsimp [upper, lower, gap]
  ring

/-- The glued face map preserves the sign relative to every graph in the
ordered breakpoint family. Inside a strip this is the positive affine fiber
rescaling for its two anchors; all other labels remain strictly on the same
side by the actual source and target graph order. -/
private theorem affineFaceSectorHomeomorph_preserves_graph_sign {n : ℕ} (hn : 0 < n)
    (R : ℝ) (a b b' : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (hfirst' : ∀ r, affineGraph a b' 0 r = -r)
    (hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b i r)
    (hgap' : ∀ i : Fin n, ∀ r, R ≤ r → 0 < affineGraphGap a b' i r)
    (j : Fin (n + 1)) (p : {p : ℝ × ℝ // p ∈ faceSector R}) :
    Real.sign ((affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast'
      hgap hgap' p).1.2 - affineGraph a b' j
        (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast'
          hgap hgap' p).1.1) =
      Real.sign (p.1.2 - affineGraph a b j p.1.1) := by
  classical
  obtain ⟨i, hi⟩ := mem_iUnion.mp
    (affineGraphFamily_face_cover hn R a b hfirst hlast hgap p.2)
  have hstrip : p.1 ∈ intervalStrip R (affineGraph a b) i := hi
  have hlocal := affineFaceSectorHomeomorph_on_piece hn R a b b'
    hfirst hlast hfirst' hlast' hgap hgap' i p (by
      change p.1 ∈ intervalStrip R (affineGraph a b) i
      exact hi)
  have hr : R ≤ p.1.1 := p.2.1
  have hsourceStrict := affineGraph_strictMono_on_ray R p.1.1 a b hr
    (fun k _ => hgap k p.1.1 hr)
  have htargetStrict := affineGraph_strictMono_on_ray R p.1.1 a b' hr
    (fun k _ => hgap' k p.1.1 hr)
  have hsourceLower : affineGraph a b i.castSucc p.1.1 ≤ p.1.2 := hstrip.2.1
  have hsourceUpper : p.1.2 ≤ affineGraph a b i.succ p.1.1 := hstrip.2.2
  have hsourceClosed : p.1 ∈ closedStrip R (a i.castSucc) (b i.castSucc)
      (a i.succ) (b i.succ) := by
    change R ≤ p.1.1 ∧ lower (a i.castSucc) (b i.castSucc) p.1.1 ≤ p.1.2 ∧
      p.1.2 ≤ upper (a i.succ) (b i.succ) p.1.1
    exact ⟨hr, hsourceLower, hsourceUpper⟩
  have hgapLocal : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) r := by
    intro r hrr
    simpa [affineGraphGap, affineGraph, gap, upper, lower] using hgap i r hrr
  have hgapLocal' : ∀ r, R ≤ r →
      0 < gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) r := by
    intro r hrr
    simpa [affineGraphGap, affineGraph, gap, upper, lower] using hgap' i r hrr
  have htargetClosed := chart_mem_strip hsourceClosed hgapLocal hgapLocal'
  have htargetLower : affineGraph a b' i.castSucc
      (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 ≤
      (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 := by
    rw [hlocal]
    exact htargetClosed.2.1
  have htargetUpper : (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 ≤
      affineGraph a b' i.succ
        (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 := by
    rw [hlocal]
    exact htargetClosed.2.2
  have hfactorLower :
      (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 -
        affineGraph a b' i.castSucc
          (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 =
      (p.1.2 - affineGraph a b i.castSucc p.1.1) *
        (gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) p.1.1 /
          gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) p.1.1) := by
    rw [hlocal]
    simp only [stripChart]
    dsimp [affineGraph, lower, gap, upper]
    field_simp [ne_of_gt (hgapLocal p.1.1 hr)]
    ring_nf
  have hfactorUpper :
      (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 -
        affineGraph a b' i.succ
          (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 =
      (p.1.2 - affineGraph a b i.succ p.1.1) *
        (gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) p.1.1 /
          gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) p.1.1) := by
    rw [hlocal]
    change (stripChart (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ)
        (b' i.castSucc) (b' i.succ) p.1).2 -
        upper (a i.succ) (b' i.succ) p.1.1 =
      (p.1.2 - upper (a i.succ) (b i.succ) p.1.1) *
        (gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) p.1.1 /
          gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) p.1.1)
    exact stripChart_upperDifference (a i.castSucc) (b i.castSucc)
      (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) p.1.1 p.1.2
      (ne_of_gt (hgapLocal p.1.1 hr))
  have hfactorPos : 0 <
      gap (a i.castSucc) (b' i.castSucc) (a i.succ) (b' i.succ) p.1.1 /
        gap (a i.castSucc) (b i.castSucc) (a i.succ) (b i.succ) p.1.1 := by
    exact div_pos (hgapLocal' p.1.1 hr) (hgapLocal p.1.1 hr)
  have hindex : j.val < i.val ∨ j.val = i.val ∨ j.val = i.val + 1 ∨
      i.val + 1 < j.val := by omega
  rcases hindex with hjlow | hjlower | hjupper | hjhigh
  · have hidx : j < i.castSucc := Fin.lt_def.mpr hjlow
    have hsrc : affineGraph a b j p.1.1 < affineGraph a b i.castSucc p.1.1 :=
      hsourceStrict hidx
    have htgt : affineGraph a b' j p.1.1 < affineGraph a b' i.castSucc p.1.1 :=
      htargetStrict hidx
    have hsrcPos : 0 < p.1.2 - affineGraph a b j p.1.1 := by linarith
    have htgtPos : 0 < (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 -
        affineGraph a b' j (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 := by
      rw [affineFaceSectorHomeomorph_radius hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p]
      have hlo' := htargetLower
      rw [affineFaceSectorHomeomorph_radius hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p] at hlo'
      linarith [hlo']
    rw [Real.sign_of_pos htgtPos, Real.sign_of_pos hsrcPos]
  · have hidx : j = i.castSucc := Fin.ext hjlower
    subst j
    rw [hfactorLower]
    exact realSign_mul_pos _ _ hfactorPos
  · have hidx : j = i.succ := Fin.ext (by simpa using hjupper)
    subst j
    rw [hfactorUpper]
    exact realSign_mul_pos _ _ hfactorPos
  · have hidx : i.succ < j := Fin.lt_def.mpr hjhigh
    have hsrc : affineGraph a b i.succ p.1.1 < affineGraph a b j p.1.1 :=
      hsourceStrict hidx
    have htgt : affineGraph a b' i.succ p.1.1 < affineGraph a b' j p.1.1 :=
      htargetStrict hidx
    have hsrcNeg : p.1.2 - affineGraph a b j p.1.1 < 0 := by linarith
    have htgtNeg :
        (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.2 -
          affineGraph a b' j (affineFaceSectorHomeomorph hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p).1.1 < 0 := by
      rw [affineFaceSectorHomeomorph_radius hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p]
      have hup' := htargetUpper
      rw [affineFaceSectorHomeomorph_radius hn R a b b' hfirst hlast hfirst' hlast' hgap hgap' p] at hup'
      linarith [hup']
    rw [Real.sign_of_neg htgtNeg, Real.sign_of_neg hsrcNeg]

private theorem finitePositiveGap (F : Finset ℝ) (hF : ∀ x ∈ F, 0 < x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, ε ≤ x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a F ha ih =>
      obtain ⟨ε, hε, hbound⟩ := ih (by
        intro x hx
        exact hF x (Finset.mem_insert_of_mem hx))
      have haPos : 0 < a := hF a (Finset.mem_insert_self _ _)
      refine ⟨min ε (a / 2), lt_min hε (by linarith), ?_⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (min_le_right _ _).trans (by linarith)
      · exact (min_le_left _ _).trans (hbound x hx)

private theorem finitePositiveAbsMargin (F : Finset ℝ)
    (hnz : ∀ x ∈ F, x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ F, ε ≤ |x| := by
  classical
  let A := F.image abs
  have hApos : ∀ x ∈ A, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact abs_pos.mpr (hnz y hy)
  obtain ⟨ε, hε, hbound⟩ := finitePositiveGap A hApos
  refine ⟨ε, hε, ?_⟩
  intro x hx
  exact hbound |x| (Finset.mem_image.mpr ⟨x, hx, rfl⟩)

private theorem normalized_map_rational_for_outgoing (φ : ℝ →ₗ[ℚ] ℚ)
    (hφ1 : φ 1 = 1) (q : ℚ) : (φ (q : ℝ) : ℝ) = q := by
  have hcast : (q : ℝ) = q • (1 : ℝ) := by simp [Rat.smul_def]
  rw [hcast, map_smul, hφ1]
  simp [Rat.smul_def]

private theorem targetRationalGraphGap_at_rational (φ : ℝ →ₗ[ℚ] ℚ)
    (hφ1 : φ 1 = 1) (g h : RationalGraph) (R : ℚ) :
    targetRationalGraphGap φ g h (R : ℝ) =
      (φ (rationalGraphValue R h - rationalGraphValue R g) : ℝ) := by
  rcases g with ⟨a₁, b₁⟩
  rcases h with ⟨a₂, b₂⟩
  change ((a₂ : ℝ) * (R : ℝ) + (φ b₂ : ℝ)) -
      ((a₁ : ℝ) * (R : ℝ) + (φ b₁ : ℝ)) =
    (φ (((a₂ : ℝ) * (R : ℝ) + b₂) - ((a₁ : ℝ) * (R : ℝ) + b₁)) : ℝ)
  have hφa : φ (((a₂ - a₁) * R : ℚ) : ℝ) = (a₂ - a₁) * R := by
    exact_mod_cast normalized_map_rational_for_outgoing φ hφ1 ((a₂ - a₁) * R)
  have hφb : φ (b₂ - b₁) = φ b₂ - φ b₁ := map_sub φ b₂ b₁
  have hsource : ((a₂ : ℝ) * (R : ℝ) + b₂) -
      ((a₁ : ℝ) * (R : ℝ) + b₁) = (((a₂ - a₁) * R : ℚ) : ℝ) + (b₂ - b₁) := by
    push_cast
    ring
  rw [hsource, map_add, hφa, hφb]
  push_cast
  ring

private theorem targetRationalGraphGap_positive_ray
    (φ : ℝ →ₗ[ℚ] ℚ) (g h : RationalGraph) (R : ℚ)
    (hslope : g.1 ≤ h.1)
    (hgap : 0 < targetRationalGraphGap φ g h (R : ℝ)) :
    ∀ r : ℝ, (R : ℝ) ≤ r → 0 < targetRationalGraphGap φ g h r := by
  intro r hr
  have hformula : targetRationalGraphGap φ g h r =
      targetRationalGraphGap φ g h (R : ℝ) +
        ((h.1 : ℝ) - (g.1 : ℝ)) * (r - (R : ℝ)) := by
    rcases g with ⟨a₁, b₁⟩
    rcases h with ⟨a₂, b₂⟩
    simp [targetRationalGraphGap, targetRationalGraphValue]
    ring
  rw [hformula]
  have hslope' : 0 ≤ (h.1 : ℝ) - (g.1 : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hslope
  exact add_pos_of_pos_of_nonneg hgap
    (mul_nonneg hslope' (sub_nonneg.mpr hr))

private theorem sourceRationalGraphGap_positive_ray
    (g h : RationalGraph) (R : ℚ) (hslope : g.1 ≤ h.1)
    (hgap : 0 < rationalGraphValue R h - rationalGraphValue R g) :
    ∀ r : ℝ, (R : ℝ) ≤ r →
      0 < ((h.1 : ℝ) * r + h.2) - ((g.1 : ℝ) * r + g.2) := by
  intro r hr
  have hformula : ((h.1 : ℝ) * r + h.2) - ((g.1 : ℝ) * r + g.2) =
      rationalGraphValue R h - rationalGraphValue R g +
        ((h.1 : ℝ) - (g.1 : ℝ)) * (r - (R : ℝ)) := by
    simp [rationalGraphValue]
    ring
  rw [hformula]
  have hslope' : 0 ≤ (h.1 : ℝ) - (g.1 : ℝ) := by
    exact_mod_cast sub_nonneg.mpr hslope
  exact add_pos_of_pos_of_nonneg hgap
    (mul_nonneg hslope' (sub_nonneg.mpr hr))

/-- Finite scalar tests built from every nonzero ordered gap among the actual
source labels and the two geometric corners preserve that order throughout
the exterior ray. This includes both active breakpoints and inactive lines. -/
private theorem exists_finite_tests_preserve_all_outgoing_pair_orders
    (A : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
      ∀ h ∈ A ∪ {(-1, 0), (1, 0)}, g.1 ≠ h.1 →
        rationalGraphIntersection g h < R) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
          ∀ h ∈ A ∪ {(-1, 0), (1, 0)},
            rationalGraphValue R g < rationalGraphValue R h →
              ∀ r : ℝ, (R : ℝ) ≤ r →
                0 < targetRationalGraphGap φ g h r := by
  classical
  let V := A ∪ {(-1, 0), (1, 0)}
  let F := outgoingRationalGapTests A R
  have hFnonzero : ∀ x ∈ F, x ≠ 0 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
    exact sub_ne_zero.mpr (Finset.mem_filter.mp he).2.symm
  obtain ⟨ε, hε, hmargin⟩ := finitePositiveAbsMargin F hFnonzero
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ g hg h hh horder r hr
  have hmemF : rationalGraphValue R h - rationalGraphValue R g ∈ F := by
    apply Finset.mem_image.mpr
    refine ⟨(g, h), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨hg, hh⟩, ne_of_lt horder⟩
  have happ := hφ.2 _ hmemF
  have hmargin' := hmargin _ hmemF
  have hmapPos : 0 < (φ (rationalGraphValue R h - rationalGraphValue R g) : ℝ) := by
    have habs := abs_lt.mp happ
    rw [abs_of_pos (sub_pos.mpr horder)] at hmargin'
    linarith
  have htargetR : 0 < targetRationalGraphGap φ g h (R : ℝ) := by
    rw [targetRationalGraphGap_at_rational φ hφ.1 g h R]
    exact hmapPos
  have hslope : g.1 ≤ h.1 :=
    rationalSlope_order_of_value_order V R hinter hg hh horder
  exact targetRationalGraphGap_positive_ray φ g h R hslope htargetR r hr

/-- Turn a source family extracted from the actual outgoing labels into a
target face-sector homeomorphism using only finitely many scalar tests. The
source-family parameters are intended to be supplied by
`outgoingRationalGraphs_faceFamily`; the target order is proved from the
constructed pair-gap tests, not assumed. -/
private theorem finite_tests_give_outgoing_face_transport
    (A : Finset RationalGraph) (R : ℚ)
    (hinter : ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
      ∀ h ∈ A ∪ {(-1, 0), (1, 0)}, g.1 ≠ h.1 →
        rationalGraphIntersection g h < R)
    (n : ℕ) (hn : 0 < n) (a b : Fin (n + 1) → ℝ)
    (hfirst : ∀ r, affineGraph a b 0 r = -r)
    (hlast : ∀ r, affineGraph a b ⟨n, by omega⟩ r = r)
    (_hmono : ∀ i : Fin n, a i.castSucc ≤ a i.succ)
    (hgap : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
      0 < affineGraphGap a b i r)
    (hforward : ∀ i : Fin (n + 1), ∃ g ∈ outgoingRationalGraphs A R,
      a i = (g.1 : ℝ) ∧ b i = g.2)
    (hlabels : ∀ g ∈ A, -(R : ℝ) < rationalGraphValue R g →
      rationalGraphValue R g < R →
      ∃ i : Fin (n + 1), a i = (g.1 : ℝ) ∧ b i = g.2) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ b' : Fin (n + 1) → ℝ,
          ∃ hfirst' : ∀ r, affineGraph a b' 0 r = -r,
          ∃ hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r,
          ∃ hgap' : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
            0 < affineGraphGap a b' i r,
          ∃ D : AffineFaceSectorHomeomorphData (R : ℝ) a b b'
            hfirst hlast hfirst' hlast' hgap hgap',
            (∀ p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
              (D.homeo p).1.1 = p.1.1) ∧
            (∀ i (p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)})
              (_hp : p ∈ facePiece (R : ℝ) (affineGraph a b) i),
              (D.homeo p).1 = stripChart (a i.castSucc) (b i.castSucc)
                (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) p.1) ∧
            (∀ g ∈ A,
              ∀ p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
              Real.sign ((D.homeo p).1.2 -
                  targetRationalGraphValue φ g (D.homeo p).1.1) =
                Real.sign (p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2))) := by
  classical
  obtain ⟨F, ε, hε, hcontrols⟩ :=
    exists_finite_tests_preserve_all_outgoing_pair_orders A R hinter
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  let b' : Fin (n + 1) → ℝ := fun i => (φ (b i) : ℝ)
  have hb0 : b 0 = 0 := by
    have hx := hfirst 0
    simpa [affineGraph, lower] using hx
  have hbn : b ⟨n, by omega⟩ = 0 := by
    have hx := hlast 0
    simpa [affineGraph, lower] using hx
  have hfirst' : ∀ r, affineGraph a b' 0 r = -r := by
    intro r
    have heq : b' 0 = b 0 := by simp [b', hb0]
    change a 0 * r + b' 0 = -r
    rw [heq]
    change affineGraph a b 0 r = -r
    exact hfirst r
  have hlast' : ∀ r, affineGraph a b' ⟨n, by omega⟩ r = r := by
    intro r
    have heq : b' ⟨n, by omega⟩ = b ⟨n, by omega⟩ := by simp [b', hbn]
    change a ⟨n, by omega⟩ * r + b' ⟨n, by omega⟩ = r
    rw [heq]
    change affineGraph a b ⟨n, by omega⟩ r = r
    exact hlast r
  have hsubset : ∀ g ∈ outgoingRationalGraphs A R,
      g ∈ A ∪ {(-1, 0), (1, 0)} := by
    intro g hg
    simp only [outgoingRationalGraphs, Finset.mem_union,
      Finset.mem_filter] at hg ⊢
    rcases hg with ⟨hA, _⟩ | hcorner
    · exact Or.inl hA
    · exact Or.inr hcorner
  have hgap' : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
      0 < affineGraphGap a b' i r := by
    intro i r hr
    rcases hforward i.castSucc with ⟨g, hg, hag, hbg⟩
    rcases hforward i.succ with ⟨h, hh, hah, hbh⟩
    have horder : rationalGraphValue R g < rationalGraphValue R h := by
      have hsrc := hgap i (R : ℝ) le_rfl
      dsimp [affineGraphGap, affineGraph, lower] at hsrc
      rw [hag, hbg, hah, hbh] at hsrc
      exact sub_pos.mp hsrc
    have htarget := hcontrols φ hφ g (hsubset g hg) h (hsubset h hh)
      horder r hr
    have heq : affineGraphGap a b' i r =
        targetRationalGraphGap φ g h r := by
      simp [affineGraphGap, affineGraph, lower, targetRationalGraphGap,
        targetRationalGraphValue, b', hag, hbg, hah, hbh]
    rw [heq]
    exact htarget
  let D := affineFaceSectorHomeomorphWithPieces hn (R : ℝ) a b b'
    hfirst hlast hfirst' hlast' hgap hgap'
  have hradius (p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)}) :
      (D.homeo p).1.1 = p.1.1 := by
    simpa [D, affineFaceSectorHomeomorph] using
      affineFaceSectorHomeomorph_radius hn (R : ℝ) a b b'
        hfirst hlast hfirst' hlast' hgap hgap' p
  have hsignAtIndex : ∀ (g : RationalGraph) (i : Fin (n + 1)),
      a i = (g.1 : ℝ) → b i = g.2 →
      ∀ p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
        Real.sign ((D.homeo p).1.2 -
          targetRationalGraphValue φ g (D.homeo p).1.1) =
        Real.sign (p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2)) := by
    intro g i hai hbi p
    have hsrc : affineGraph a b i p.1.1 = (g.1 : ℝ) * p.1.1 + g.2 := by
      simp [affineGraph, lower, hai, hbi]
    have htgt : affineGraph a b' i (D.homeo p).1.1 =
        targetRationalGraphValue φ g (D.homeo p).1.1 := by
      simp [affineGraph, lower, b', targetRationalGraphValue, hai, hbi]
    have hsignFamily := affineFaceSectorHomeomorph_preserves_graph_sign
      hn (R : ℝ) a b b' hfirst hlast hfirst' hlast' hgap hgap' i p
    have hhomeo : D.homeo = affineFaceSectorHomeomorph hn (R : ℝ) a b b'
        hfirst hlast hfirst' hlast' hgap hgap' := rfl
    rw [← hhomeo, htgt, hsrc] at hsignFamily
    exact hsignFamily
  have hfirstSlope : a 0 = -1 := by
    have h0 := hfirst 0
    have h1 := hfirst 1
    simp [affineGraph, lower] at h0 h1
    linarith
  have hlastSlope : a ⟨n, by omega⟩ = 1 := by
    have h0 := hlast 0
    have h1 := hlast 1
    simp [affineGraph, lower] at h0 h1
    linarith
  have hsign : ∀ g ∈ A,
      ∀ p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
        Real.sign ((D.homeo p).1.2 -
          targetRationalGraphValue φ g (D.homeo p).1.1) =
        Real.sign (p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2)) := by
    intro g hg p
    have hgV : g ∈ A ∪ {(-1, 0), (1, 0)} :=
      Finset.mem_union_left _ hg
    rcases lt_trichotomy (rationalGraphValue R g) (-(R : ℝ)) with hbelow | hequal | habove
    · let c : RationalGraph := (-1, 0)
      have hcV : c ∈ A ∪ {(-1, 0), (1, 0)} := by simp [c]
      have horder : rationalGraphValue R g < rationalGraphValue R c := by
        simpa [c, rationalGraphValue] using hbelow
      have hslope : g.1 ≤ c.1 :=
        rationalSlope_order_of_value_order (A ∪ {(-1, 0), (1, 0)}) R
          hinter hgV hcV horder
      have hsrc := sourceRationalGraphGap_positive_ray g c R hslope
        (sub_pos.mpr horder) p.1.1 p.2.1
      have htgt := hcontrols φ hφ g hgV c hcV horder (D.homeo p).1.1
        (D.homeo p).2.1
      have hsrcPos : 0 < p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2) := by
        have hline : 0 < -p.1.1 - ((g.1 : ℝ) * p.1.1 + g.2) := by
          simpa [c] using hsrc
        linarith [p.2.2.1]
      have htgtPos : 0 < (D.homeo p).1.2 -
          targetRationalGraphValue φ g (D.homeo p).1.1 := by
        have hline : 0 < -(D.homeo p).1.1 -
            targetRationalGraphValue φ g (D.homeo p).1.1 := by
          simpa [targetRationalGraphGap, targetRationalGraphValue, c] using htgt
        linarith [(D.homeo p).2.2.1]
      rw [Real.sign_of_pos htgtPos, Real.sign_of_pos hsrcPos]
    · have hcorner : g = (-1, 0) := by
        apply rationalGraphValue_injective_on (A ∪ {(-1, 0), (1, 0)}) R
          hinter hgV (Finset.mem_union_right A (by simp))
        simpa [rationalGraphValue] using hequal
      subst g
      exact hsignAtIndex (-1, 0) 0 (by simpa using hfirstSlope) hb0 p
    · rcases lt_trichotomy (rationalGraphValue R g) (R : ℝ) with hactive | hequalTop | habove
      · obtain ⟨i, hai, hbi⟩ := hlabels g hg habove hactive
        exact hsignAtIndex g i hai hbi p
      · have hcorner : g = (1, 0) := by
          apply rationalGraphValue_injective_on (A ∪ {(-1, 0), (1, 0)}) R
            hinter hgV (Finset.mem_union_right A (by simp))
          simpa [rationalGraphValue] using hequalTop
        subst g
        exact hsignAtIndex (1, 0) ⟨n, by omega⟩
          (by simpa using hlastSlope) hbn p
      · let c : RationalGraph := (1, 0)
        have hcV : c ∈ A ∪ {(-1, 0), (1, 0)} := by simp [c]
        have horder : rationalGraphValue R c < rationalGraphValue R g := by
          simpa [c, rationalGraphValue] using habove
        have hslope : c.1 ≤ g.1 :=
          rationalSlope_order_of_value_order (A ∪ {(-1, 0), (1, 0)}) R
            hinter hcV hgV horder
        have hsrc := sourceRationalGraphGap_positive_ray c g R hslope
          (sub_pos.mpr horder) p.1.1 p.2.1
        have htgt := hcontrols φ hφ c hcV g hgV horder (D.homeo p).1.1
          (D.homeo p).2.1
        have hsrcNeg : p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2) < 0 := by
          have hline : 0 < ((g.1 : ℝ) * p.1.1 + g.2) - p.1.1 := by
            simpa [c] using hsrc
          linarith [p.2.2.2]
        have htgtNeg : (D.homeo p).1.2 -
            targetRationalGraphValue φ g (D.homeo p).1.1 < 0 := by
          have hline : 0 < targetRationalGraphValue φ g (D.homeo p).1.1 -
              (D.homeo p).1.1 := by
            simpa [targetRationalGraphGap, targetRationalGraphValue, c] using htgt
          linarith [(D.homeo p).2.2.2]
        rw [Real.sign_of_neg htgtNeg, Real.sign_of_neg hsrcNeg]
  refine ⟨b', hfirst', hlast', hgap', D, hradius, ?_, hsign⟩
  intro i p hp
  exact D.on_piece i p hp

/-- The finite-test face transport with its source graph family constructed
directly from the actual finite arrangement labels. In particular the final
sign statement covers active graphs, inactive graphs, and labels coincident
with either diagonal corner. -/
private theorem outgoingRationalGraphs_actual_exterior_transport
    (A : Finset RationalGraph) (R : ℚ) (hR : 0 < R)
    (hinter : ∀ g ∈ A ∪ {(-1, 0), (1, 0)},
      ∀ h ∈ A ∪ {(-1, 0), (1, 0)}, g.1 ≠ h.1 →
        rationalGraphIntersection g h < R) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin (n + 1) → ℝ,
      (∀ r, affineGraph a b 0 r = -r) ∧
      (∀ r, affineGraph a b ⟨n, by omega⟩ r = r) ∧
      (∀ i : Fin n, a i.castSucc ≤ a i.succ) ∧
      (∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
        0 < affineGraphGap a b i r) ∧
      (∀ i : Fin (n + 1), ∃ g ∈ outgoingRationalGraphs A R,
        a i = (g.1 : ℝ) ∧ b i = g.2) ∧
      (∀ g ∈ A, -(R : ℝ) < rationalGraphValue R g →
        rationalGraphValue R g < R →
        ∃ i : Fin (n + 1), a i = (g.1 : ℝ) ∧ b i = g.2) ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ b' : Fin (n + 1) → ℝ,
            (∀ r, affineGraph a b' 0 r = -r) ∧
            (∀ r, affineGraph a b' ⟨n, by omega⟩ r = r) ∧
            (∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
              0 < affineGraphGap a b' i r) ∧
            ∃ H : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)} ≃ₜ
              {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
              (∀ p, (H p).1.1 = p.1.1) ∧
              (∀ i (p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)})
                (_hp : p ∈ facePiece (R : ℝ) (affineGraph a b) i),
                (H p).1 = stripChart (a i.castSucc) (b i.castSucc)
                  (a i.succ) (b i.succ) (b' i.castSucc) (b' i.succ) p.1) ∧
              (∀ g ∈ A,
                ∀ p : {p : ℝ × ℝ // p ∈ faceSector (R : ℝ)},
                  Real.sign ((H p).1.2 -
                    targetRationalGraphValue φ g (H p).1.1) =
                  Real.sign (p.1.2 - ((g.1 : ℝ) * p.1.1 + g.2))) := by
  classical
  obtain ⟨n, hn, a, b, hfirst, hlast, hmono, hgap,
      hforward, hlabels⟩ := outgoingRationalGraphs_faceFamily A R
    (by exact_mod_cast hR) hinter
  obtain ⟨F, ε, hε, htransport⟩ :=
      finite_tests_give_outgoing_face_transport A R hinter n hn a b
      hfirst hlast hmono hgap hforward hlabels
  refine ⟨n, hn, a, b, hfirst, hlast, hmono, hgap, hforward, hlabels,
    F, ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨b', hfirst', hlast', hgap', D, hradius, hpiece, hsign⟩ :=
    htransport φ hφ
  exact ⟨b', hfirst', hlast', hgap', D.homeo, hradius, hpiece, hsign⟩


private theorem affineMap_verticalSegment_value
    (R y₀ y₁ y₀' y₁' : ℝ) (hgap : y₀ < y₁)
    (f : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ))
    (h₀ : f (R, y₀) = (R, y₀'))
    (h₁ : f (R, y₁) = (R, y₁'))
    (p : ℝ × ℝ) (hp : p ∈ segment ℝ (R, y₀) (R, y₁)) :
    f p = (R, y₀' + (p.2 - y₀) * ((y₁' - y₀') / (y₁ - y₀))) := by
  rw [segment_eq_image'] at hp
  rcases hp with ⟨t, ht, rfl⟩
  have hmap : f (AffineMap.lineMap (R, y₀) (R, y₁) t) =
      AffineMap.lineMap (f (R, y₀)) (f (R, y₁)) t := by
    rw [AffineMap.lineMap_apply, f.map_vadd, f.linear.map_smul,
      f.linearMap_vsub, AffineMap.lineMap_apply]
  have hpoint : (R, y₀) + t • ((R, y₁) - (R, y₀)) =
      AffineMap.lineMap (R, y₀) (R, y₁) t := by
    rw [AffineMap.lineMap_apply, vadd_eq_add]
    abel
  change f ((R, y₀) + t • ((R, y₁) - (R, y₀))) = _
  rw [hpoint, hmap, h₀, h₁]
  apply Prod.ext
  · simp
  · simp [AffineMap.lineMap_apply_module, smul_eq_mul]
    field_simp [show y₁ - y₀ ≠ 0 by linarith]
    ring

/-- On a vertical boundary edge, the endpoint-matching affine interpolation is
exactly the value of the corresponding exterior strip chart. -/
private theorem stripChart_vertical_edge_value
    (R a c b d b' d' y : ℝ)
    (hsegment : lower a b R ≤ y ∧ y ≤ upper c d R) :
    stripChart a b c d b' d' (R, y) =
      (R, lower a b' R + (y - lower a b R) *
        ((upper c d' R - lower a b' R) /
          (upper c d R - lower a b R))) := by
  rcases hsegment with ⟨_, _⟩
  simp [stripChart, gap, lower, upper]

private theorem segment_vertical_bounds
    (R y₀ y₁ : ℝ) (hgap : y₀ < y₁) (p : ℝ × ℝ)
    (hp : p ∈ segment ℝ (R, y₀) (R, y₁)) :
    p.1 = R ∧ y₀ ≤ p.2 ∧ p.2 ≤ y₁ := by
  rw [segment_eq_image'] at hp
  rcases hp with ⟨t, ht, rfl⟩
  rcases ht with ⟨ht0, ht1⟩
  have hfst : ((R, y₀) + t • ((R, y₁) - (R, y₀))).1 = R := by
    simp
  have hsnd : ((R, y₀) + t • ((R, y₁) - (R, y₀))).2 =
      (1 - t) * y₀ + t * y₁ := by
    simp [smul_eq_mul]
    ring
  constructor
  · exact hfst
  · rw [hsnd]
    constructor
    · have ht0' : 0 ≤ t * (y₁ - y₀) := mul_nonneg ht0 (sub_nonneg.mpr hgap.le)
      nlinarith
    · have ht1' : 0 ≤ (1 - t) * (y₁ - y₀) :=
        mul_nonneg (by linarith) (sub_nonneg.mpr hgap.le)
      nlinarith


private theorem affine_agrees_with_stripChart_on_vertical_edge
    (R a c b d b' d' : ℝ)
    (hsource : gap a b c d R > 0) (htarget : gap a b' c d' R > 0)
    (H : ℝ × ℝ → ℝ × ℝ)
    (hpiece : ∀ p : ℝ × ℝ, p.1 = R → lower a b R ≤ p.2 →
      p.2 ≤ upper c d R → H p = stripChart a b c d b' d' p)
    (f : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ))
    (hf₀ : f (R, lower a b R) = H (R, lower a b R))
    (hf₁ : f (R, upper c d R) = H (R, upper c d R))
    (p : ℝ × ℝ) (hp : p ∈ segment ℝ (R, lower a b R) (R, upper c d R)) :
    f p = H p := by
  have hsource_ne : gap a b c d R ≠ 0 := ne_of_gt hsource
  have hsource_order : lower a b R < upper c d R := by
    change upper c d R - lower a b R > 0 at hsource
    linarith
  have _ : lower a b' R < upper c d' R := by
    change upper c d' R - lower a b' R > 0 at htarget
    linarith
  have hlow := hpiece (R, lower a b R) rfl le_rfl (by
    exact le_of_lt hsource_order)
  have hupp := hpiece (R, upper c d R) rfl (by
      exact hsource_order.le) le_rfl
  rw [stripChart_lower_anchor] at hlow
  rw [stripChart_upper_anchor hsource_ne] at hupp
  have hf₀' : f (R, lower a b R) = (R, lower a b' R) := hf₀.trans hlow
  have hf₁' : f (R, upper c d R) = (R, upper c d' R) := hf₁.trans hupp
  have hbounds := segment_vertical_bounds R (lower a b R) (upper c d R)
    hsource_order p hp
  have hinterp := affineMap_verticalSegment_value R (lower a b R) (upper c d R)
      (lower a b' R) (upper c d' R) hsource_order f hf₀' hf₁' p hp
  have hpiece' := hpiece p hbounds.1 hbounds.2.1 hbounds.2.2
  have hformula : stripChart a b c d b' d' p =
      (R, lower a b' R + (p.2 - lower a b R) *
        ((upper c d' R - lower a b' R) /
          (upper c d R - lower a b R))) := by
    rw [stripChart, hbounds.1]
    simp [gap]
  calc
    f p = (R, lower a b' R + (p.2 - lower a b R) *
        ((upper c d' R - lower a b' R) /
          (upper c d R - lower a b R))) := hinterp
    _ = stripChart a b c d b' d' p := hformula.symm
    _ = H p := hpiece'.symm

end ExteriorFaceCharts

private def rightGraph (l : RationalLine) : ℚ × ℝ :=
  (-l.normal.x/l.normal.y,l.offset/(l.normal.y : ℝ))

private theorem lineEval_rightGraph (l : RationalLine) (hly : l.normal.y ≠ 0) (z : Plane) :
    l.eval z = (l.normal.y : ℝ) *
      (z.im - (rightGraph l).1*z.re - (rightGraph l).2) := by
  have hy : (l.normal.y : ℝ) ≠ 0 := by exact_mod_cast hly
  simp only [rightGraph,RationalLine.eval,normalEval,Rat.cast_div,Rat.cast_neg]
  field_simp
  ring

private theorem rightGraph_deform (l : RationalLine) (hly : l.normal.y ≠ 0)
    (φ : ℝ →ₗ[ℚ] ℚ) :
    rightGraph (deformLine φ l) = ((rightGraph l).1,(φ (rightGraph l).2 : ℝ)) := by
  have hy : (l.normal.y : ℝ) ≠ 0 := by exact_mod_cast hly
  have hmap := φ.map_smul (1/l.normal.y) l.offset
  have harg : (1/l.normal.y) • l.offset = l.offset/(l.normal.y : ℝ) := by
    simp [Rat.smul_def]; ring
  rw [harg] at hmap
  apply Prod.ext
  · rfl
  · dsimp [rightGraph,deformLine]
    rw [hmap]
    simp
    ring

private theorem rightGraph_distinctSlopes_det (l m : RationalLine)
    (hly : l.normal.y ≠ 0) (hmy : m.normal.y ≠ 0)
    (hne : (rightGraph l).1 ≠ (rightGraph m).1) :
    l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 := by
  intro hdet
  apply hne
  dsimp [rightGraph]
  apply (div_eq_div_iff hly hmy).mpr
  linear_combination -hdet

private theorem rightGraph_intersection_before (L : List RationalLine) (R : ℚ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (l m : RationalLine) (hl : l ∈ L) (hm : m ∈ L)
    (hly : l.normal.y ≠ 0) (hmy : m.normal.y ≠ 0)
    (hne : (rightGraph l).1 ≠ (rightGraph m).1) :
    ((rightGraph m).2-(rightGraph l).2) /
      ((rightGraph l).1-(rightGraph m).1 : ℝ) < R := by
  let g := rightGraph l
  let h := rightGraph m
  let r : ℝ := (h.2-g.2)/((g.1 : ℝ)-h.1)
  let s : ℝ := g.1*r+g.2
  let z : Plane := r + s*Complex.I
  have hden : (g.1 : ℝ)-(h.1 : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hne
  have hmul : ((g.1 : ℝ)-(h.1 : ℝ))*r = h.2-g.2 := mul_div_cancel₀ _ hden
  have hlz : l.eval z = 0 := by
    rw [lineEval_rightGraph l hly]
    simp [z,s,g]
  have hmz : m.eval z = 0 := by
    rw [lineEval_rightGraph m hmy]
    have hs : s = (h.1 : ℝ)*r+h.2 := by dsimp [s]; nlinarith [hmul]
    simp [z,hs,h]
  have hn := hinter l hl m hm (rightGraph_distinctSlopes_det l m hly hmy hne) z hlz hmz
  have hr : r ≤ ‖z‖ := by
    have hreal : z.re = r := by simp [z]
    rw [← hreal]
    exact (le_abs_self _).trans (Complex.abs_re_le_norm _)
  exact hr.trans_lt hn

private def rightGraphSet (L : List RationalLine) : Finset (ℚ × ℝ) := by
  classical
  exact (L.toFinset.filter (fun l => l.normal.y ≠ 0)).image rightGraph

private theorem rightGraphSet_incidence (L : List RationalLine) (R : ℚ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ)) :
    ∀ g ∈ rightGraphSet L, ∀ h ∈ rightGraphSet L, g.1 ≠ h.1 →
      (h.2-g.2)/((g.1 : ℝ)-h.1) < R := by
  classical
  intro g hg h hh hne
  unfold rightGraphSet at hg hh
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hh
  obtain ⟨hl,hly⟩ := Finset.mem_filter.mp hl
  obtain ⟨hm,hmy⟩ := Finset.mem_filter.mp hm
  exact rightGraph_intersection_before L R hinter l m
    (List.mem_toFinset.mp hl) (List.mem_toFinset.mp hm) hly hmy hne

private theorem rightGraphSet_has_corners (L : List RationalLine)
    (hdiagonal : ∀ l ∈ diagonalLines, l ∈ L) :
    (-1,0) ∈ rightGraphSet L ∧ (1,0) ∈ rightGraphSet L := by
  classical
  unfold rightGraphSet
  constructor
  · let l : RationalLine := ⟨⟨1,1,by norm_num⟩,0⟩
    have hl : l ∈ L := hdiagonal l (by simp [l,diagonalLines])
    have hlf : l ∈ L.toFinset.filter (fun k => k.normal.y ≠ 0) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hl,by norm_num [l]⟩
    have heq : rightGraph l = (-1,0) := by norm_num [rightGraph,l]
    exact Finset.mem_image.mpr ⟨l,hlf,heq⟩
  · let l : RationalLine := ⟨⟨1,-1,by norm_num⟩,0⟩
    have hl : l ∈ L := hdiagonal l (by simp [l,diagonalLines])
    have hlf : l ∈ L.toFinset.filter (fun k => k.normal.y ≠ 0) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hl,by norm_num [l]⟩
    have heq : rightGraph l = (1,0) := by norm_num [rightGraph,l]
    exact Finset.mem_image.mpr ⟨l,hlf,heq⟩

private theorem verticalLine_rightFace_zeroFree (L : List RationalLine) (R : ℚ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (hdiagonal : ∀ l ∈ diagonalLines, l ∈ L)
    (l : RationalLine) (hl : l ∈ L) (hly : l.normal.y = 0) :
    ∀ z : Plane, (R : ℝ) ≤ z.re → l.eval z ≠ 0 := by
  have hlx : l.normal.x ≠ 0 := l.normal.nonzero.resolve_right (not_not_intro hly)
  have hx : (l.normal.x : ℝ) ≠ 0 := by exact_mod_cast hlx
  let t : ℝ := l.offset/(l.normal.x : ℝ)
  let p : Plane := t+t*Complex.I
  let m : RationalLine := ⟨⟨1,-1,by norm_num⟩,0⟩
  have hm : m ∈ L := hdiagonal m (by simp [m,diagonalLines])
  have hdet : l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 := by
    simpa [m,hly] using neg_ne_zero.mpr hlx
  have hlp : l.eval p = 0 := by
    simp [RationalLine.eval,normalEval,p,t,hly]
    field_simp
    ring
  have hmp : m.eval p = 0 := by simp [RationalLine.eval,normalEval,m,p]
  have hpn := hinter l hl m hm hdet p hlp hmp
  have ht : t < (R : ℝ) := by
    have hpReal : p.re = t := by simp [p]
    have hle := (le_abs_self p.re).trans (Complex.abs_re_le_norm p)
    rw [hpReal] at hle
    exact hle.trans_lt hpn
  intro z hz hzero
  have hzt : z.re = t := by
    apply (eq_div_iff hx).mpr
    have heq : (l.normal.x : ℝ)*z.re-l.offset = 0 := by
      simpa [RationalLine.eval,normalEval,hly] using hzero
    nlinarith
  rw [hzt] at hz
  exact (not_lt_of_ge hz) ht

private def squareFaceCoordinates (i : Fin 4) : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  match i.val with
  | 0 => Homeomorph.refl _
  | 1 => Homeomorph.prodComm ℝ ℝ
  | 2 => (Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ)
  | 3 => (Homeomorph.prodComm ℝ ℝ).trans
      ((Homeomorph.neg ℝ).prodCongr (Homeomorph.refl ℝ))
  | _ => Homeomorph.refl _

private theorem squareFaceCoordinates_mem (R : ℝ) (i : Fin 4) (p : ℝ × ℝ) :
    p ∈ ExteriorFourFaces.face R i ↔
      squareFaceCoordinates i p ∈ ExteriorFaceCharts.faceSector R := by
  fin_cases i <;>
    simp [squareFaceCoordinates,ExteriorFourFaces.face,ExteriorFaceCharts.faceSector]

private theorem squareFaceCoordinates_image (R : ℝ) (i : Fin 4) :
    squareFaceCoordinates i '' ExteriorFourFaces.face R i = ExteriorFaceCharts.faceSector R := by
  apply subset_antisymm
  · rintro q ⟨p,hp,rfl⟩
    exact (squareFaceCoordinates_mem R i p).mp hp
  · intro q hq
    let p := (squareFaceCoordinates i).symm q
    have hp : p ∈ ExteriorFourFaces.face R i :=
      (squareFaceCoordinates_mem R i p).mpr (by simpa [p] using hq)
    exact ⟨p,hp,(squareFaceCoordinates i).apply_symm_apply q⟩

private def squareFaceSectorHomeomorph (R : ℝ) (i : Fin 4) :
    ExteriorFourFaces.FacePoint R i ≃ₜ ExteriorFaceCharts.faceSector R :=
  ((squareFaceCoordinates i).image (ExteriorFourFaces.face R i)).trans
    (Homeomorph.setCongr (squareFaceCoordinates_image R i))

private theorem squareFaceSectorHomeomorph_apply (R : ℝ) (i : Fin 4)
    (p : ExteriorFourFaces.FacePoint R i) :
    (squareFaceSectorHomeomorph R i p).val = squareFaceCoordinates i p.val := rfl

private theorem squareFaceCoordinates_diagonal (i : Fin 4) (p : ℝ × ℝ)
    (hp : p ∈ ExteriorFourFaces.diagonalRays) :
    (squareFaceCoordinates i p).2 = (squareFaceCoordinates i p).1 ∨
      (squareFaceCoordinates i p).2 = -(squareFaceCoordinates i p).1 := by
  change p.1 = p.2 ∨ p.1 = -p.2 at hp
  fin_cases i <;> rcases hp with h | h <;> simp_all [squareFaceCoordinates]

private def sectorHomeomorph_on_squareFace (R : ℝ) (i : Fin 4)
    (H : ExteriorFaceCharts.faceSector R ≃ₜ ExteriorFaceCharts.faceSector R) :
    ExteriorFourFaces.FacePoint R i ≃ₜ ExteriorFourFaces.FacePoint R i :=
  (squareFaceSectorHomeomorph R i).trans (H.trans (squareFaceSectorHomeomorph R i).symm)

private theorem sectorHomeomorph_on_squareFace_fixes_diagonal (R : ℝ) (i : Fin 4)
    (H : ExteriorFaceCharts.faceSector R ≃ₜ ExteriorFaceCharts.faceSector R)
    (hfix : ∀ q : ExteriorFaceCharts.faceSector R,
      q.val.2 = q.val.1 ∨ q.val.2 = -q.val.1 → H q = q)
    (p : ExteriorFourFaces.FacePoint R i) (hp : p.val ∈ ExteriorFourFaces.diagonalRays) :
    sectorHomeomorph_on_squareFace R i H p = p := by
  have hq := squareFaceCoordinates_diagonal i p.val hp
  have hfixed := hfix (squareFaceSectorHomeomorph R i p) hq
  change (squareFaceSectorHomeomorph R i).symm (H (squareFaceSectorHomeomorph R i p)) = p
  rw [hfixed]
  exact (squareFaceSectorHomeomorph R i).symm_apply_apply p

private def squareFaceLine (i : Fin 4) (l : RationalLine) : RationalLine :=
  match i.val with
  | 0 => l
  | 1 => ⟨⟨l.normal.y,l.normal.x,l.normal.nonzero.symm⟩,l.offset⟩
  | 2 => ⟨⟨-l.normal.x,l.normal.y,l.normal.nonzero.imp neg_ne_zero.mpr id⟩,l.offset⟩
  | 3 => ⟨⟨-l.normal.y,l.normal.x,l.normal.nonzero.symm.imp neg_ne_zero.mpr id⟩,l.offset⟩
  | _ => l

private theorem squareFaceLine_eval (i : Fin 4) (l : RationalLine) (p : ℝ × ℝ) :
    l.eval (Complex.equivRealProdCLM.symm p) =
      (squareFaceLine i l).eval (Complex.equivRealProdCLM.symm (squareFaceCoordinates i p)) := by
  fin_cases i <;> simp [squareFaceLine,squareFaceCoordinates,RationalLine.eval,normalEval] <;> ring

private theorem squareFaceLine_deform (i : Fin 4) (l : RationalLine) (φ : ℝ →ₗ[ℚ] ℚ) :
    squareFaceLine i (deformLine φ l) = deformLine φ (squareFaceLine i l) := by
  fin_cases i <;> rfl

private theorem squareFaceCoordinates_preserves_norm (i : Fin 4) (p : ℝ × ℝ) :
    ‖Complex.equivRealProdCLM.symm (squareFaceCoordinates i p)‖ =
      ‖Complex.equivRealProdCLM.symm p‖ := by
  fin_cases i <;>
    simp [squareFaceCoordinates,Complex.norm_def,Complex.normSq_apply,add_comm]

private theorem squareFaceLines_intersections_enclosed (L : List RationalLine) (R : ℚ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ)) (i : Fin 4) :
    ∀ l ∈ L.map (squareFaceLine i), ∀ m ∈ L.map (squareFaceLine i),
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ) := by
  intro l hl m hm hdet z hlz hmz
  obtain ⟨l,hlSource,rfl⟩ := List.mem_map.mp hl
  obtain ⟨m,hmSource,rfl⟩ := List.mem_map.mp hm
  have hdetOriginal : l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 := by
    intro h
    apply hdet
    fin_cases i <;> simp [squareFaceLine] <;> nlinarith [h]
  let p := (squareFaceCoordinates i).symm (Complex.equivRealProdCLM z)
  have hchart : squareFaceCoordinates i p = Complex.equivRealProdCLM z :=
    (squareFaceCoordinates i).apply_symm_apply _
  have hlp := squareFaceLine_eval i l p
  have hmp := squareFaceLine_eval i m p
  rw [hchart,Complex.equivRealProdCLM.symm_apply_apply,hlz] at hlp
  rw [hchart,Complex.equivRealProdCLM.symm_apply_apply,hmz] at hmp
  have hnorm := squareFaceCoordinates_preserves_norm i p
  rw [hchart,Complex.equivRealProdCLM.symm_apply_apply] at hnorm
  rw [hnorm]
  exact hinter l hlSource m hmSource hdetOriginal _ hlp hmp

private def squareFaceLinearCoordinates (i : Fin 4) : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
  match i.val with
  | 0 => ContinuousLinearEquiv.refl ℝ _
  | 1 => ContinuousLinearEquiv.prodComm ℝ ℝ ℝ
  | 2 => (ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)
  | 3 => (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).trans
      ((ContinuousLinearEquiv.neg ℝ : ℝ ≃L[ℝ] ℝ).prodCongr
        (ContinuousLinearEquiv.refl ℝ ℝ))
  | _ => ContinuousLinearEquiv.refl ℝ _

private theorem squareFaceLinearCoordinates_eq (i : Fin 4) (p : ℝ × ℝ) :
    squareFaceLinearCoordinates i p = squareFaceCoordinates i p := by
  fin_cases i <;> rfl

private def squareFacePlaneCoordinates (i : Fin 4) : Plane ≃L[ℝ] (ℝ × ℝ) :=
  Complex.equivRealProdCLM.trans (squareFaceLinearCoordinates i)

private theorem rightGraphSet_mono (L M : List RationalLine)
    (hsub : ∀ l ∈ L, l ∈ M) : rightGraphSet L ⊆ rightGraphSet M := by
  classical
  intro g hg
  unfold rightGraphSet at hg ⊢
  obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨hl,hly⟩ := Finset.mem_filter.mp hl
  have hlM : l ∈ M.toFinset.filter (fun k => k.normal.y ≠ 0) :=
    Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (hsub l (List.mem_toFinset.mp hl)),hly⟩
  exact Finset.mem_image.mpr ⟨l,hlM,rfl⟩

private theorem squareFaceGraphSet_has_corners (L : List RationalLine)
    (hdiagonal : ∀ l ∈ diagonalLines, l ∈ L) (i : Fin 4) :
    (-1,0) ∈ rightGraphSet (L.map (squareFaceLine i)) ∧
      (1,0) ∈ rightGraphSet (L.map (squareFaceLine i)) := by
  classical
  have hsub : rightGraphSet (diagonalLines.map (squareFaceLine i)) ⊆
      rightGraphSet (L.map (squareFaceLine i)) := by
    apply rightGraphSet_mono
    intro m hm
    obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hm
    exact List.mem_map.mpr ⟨l,hdiagonal l hl,rfl⟩
  have hsmall : (-1,0) ∈ rightGraphSet (diagonalLines.map (squareFaceLine i)) ∧
      (1,0) ∈ rightGraphSet (diagonalLines.map (squareFaceLine i)) := by
    let dpos : RationalLine := ⟨⟨1,1,by norm_num⟩,0⟩
    let dneg : RationalLine := ⟨⟨1,-1,by norm_num⟩,0⟩
    have hgraph (d : RationalLine) (hd : d ∈ diagonalLines)
        (hy : (squareFaceLine i d).normal.y ≠ 0) :
        rightGraph (squareFaceLine i d) ∈ rightGraphSet (diagonalLines.map (squareFaceLine i)) := by
      unfold rightGraphSet
      have hd' : squareFaceLine i d ∈
          (diagonalLines.map (squareFaceLine i)).toFinset.filter (fun l => l.normal.y ≠ 0) :=
        Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨d,hd,rfl⟩),hy⟩
      exact Finset.mem_image.mpr ⟨squareFaceLine i d,hd',rfl⟩
    have hpos := hgraph dpos (by simp [dpos,diagonalLines])
      (by fin_cases i <;> norm_num [squareFaceLine,dpos])
    have hneg := hgraph dneg (by simp [dneg,diagonalLines])
      (by fin_cases i <;> norm_num [squareFaceLine,dneg])
    fin_cases i
    · exact ⟨by simpa [squareFaceLine,rightGraph,dpos] using hpos,
        by simpa [squareFaceLine,rightGraph,dneg] using hneg⟩
    · exact ⟨by simpa [squareFaceLine,rightGraph,dpos] using hpos,
        by simpa [squareFaceLine,rightGraph,dneg] using hneg⟩
    · exact ⟨by simpa [squareFaceLine,rightGraph,dneg] using hneg,
        by simpa [squareFaceLine,rightGraph,dpos] using hpos⟩
    · exact ⟨by simpa [squareFaceLine,rightGraph,dneg] using hneg,
        by simpa [squareFaceLine,rightGraph,dpos] using hpos⟩
  exact ⟨hsub hsmall.1,hsub hsmall.2⟩

private theorem squareFaceGraphSet_incidence (L : List RationalLine) (R : ℚ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (hdiagonal : ∀ l ∈ diagonalLines, l ∈ L) (i : Fin 4) :
    ∀ g ∈ rightGraphSet (L.map (squareFaceLine i)) ∪ {(-1,0),(1,0)},
      ∀ h ∈ rightGraphSet (L.map (squareFaceLine i)) ∪ {(-1,0),(1,0)},
        g.1 ≠ h.1 → ExteriorFaceCharts.rationalGraphIntersection g h < R := by
  classical
  obtain ⟨hleft,hright⟩ := squareFaceGraphSet_has_corners L hdiagonal i
  have hmem : ∀ g ∈ rightGraphSet (L.map (squareFaceLine i)) ∪ {(-1,0),(1,0)},
      g ∈ rightGraphSet (L.map (squareFaceLine i)) := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hg
    · rcases Finset.mem_insert.mp hg with rfl | hg
      · exact hleft
      · have heq : g = (1,0) := Finset.mem_singleton.mp hg
        simpa [heq] using hright
  intro g hg h hh hne
  have hraw := rightGraphSet_incidence (L.map (squareFaceLine i)) R
    (squareFaceLines_intersections_enclosed L R hinter i) g (hmem g hg) h (hmem h hh) hne
  have hden : (g.1 : ℝ)-(h.1 : ℝ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hne
  have hden' : (h.1 : ℝ)-(g.1 : ℝ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp hden))
  have heq : ExteriorFaceCharts.rationalGraphIntersection g h =
      (h.2-g.2)/((g.1 : ℝ)-(h.1 : ℝ)) := by
    dsimp [ExteriorFaceCharts.rationalGraphIntersection]
    field_simp
    ring
  rw [heq]
  exact hraw

private theorem realSign_mul_congr {c x y : ℝ}
    (hxy : Real.sign x = Real.sign y) : Real.sign (c * x) = Real.sign (c * y) := by
  by_cases hc : c = 0
  · simp [hc]
  · rcases lt_or_gt_of_ne hc with hc | hc
    · have hleft : Real.sign (c * x) = -Real.sign x := by
        rcases lt_trichotomy x 0 with hx | rfl | hx
        · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg hc hx), Real.sign_of_neg hx]
          simp
        · simp
        · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hc hx), Real.sign_of_pos hx]
      have hright : Real.sign (c * y) = -Real.sign y := by
        rcases lt_trichotomy y 0 with hy | rfl | hy
        · rw [Real.sign_of_pos (mul_pos_of_neg_of_neg hc hy), Real.sign_of_neg hy]
          simp
        · simp
        · rw [Real.sign_of_neg (mul_neg_of_neg_of_pos hc hy), Real.sign_of_pos hy]
      rw [hleft, hright, hxy]
    · have hleft : Real.sign (c * x) = Real.sign x := by
        rcases lt_trichotomy x 0 with hx | rfl | hx
        · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx), Real.sign_of_neg hx]
        · simp
        · rw [Real.sign_of_pos (mul_pos hc hx), Real.sign_of_pos hx]
      have hright : Real.sign (c * y) = Real.sign y := by
        rcases lt_trichotomy y 0 with hy | rfl | hy
        · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hc hy), Real.sign_of_neg hy]
        · simp
        · rw [Real.sign_of_pos (mul_pos hc hy), Real.sign_of_pos hy]
      rw [hleft, hright, hxy]

/-- If a sector map preserves the sign of the outgoing graph coordinate, it
preserves the sign of every nonvertical rational-normal line. The factor
`normal.y` is retained, so either orientation of the line is covered. -/
private theorem nonvertical_line_sign_transport
    (φ : ℝ →ₗ[ℚ] ℚ) (l : RationalLine) (hly : l.normal.y ≠ 0)
    (H : Plane → Plane) (z : Plane)
    (hgraph : Real.sign
        ((H z).im - (rightGraph l).1 * (H z).re - (φ (rightGraph l).2 : ℝ)) =
      Real.sign (z.im - (rightGraph l).1 * z.re - (rightGraph l).2)) :
    Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
  rw [lineEval_rightGraph (deformLine φ l) hly, rightGraph_deform l hly φ,
    lineEval_rightGraph l hly]
  simpa only [deformLine, Prod.fst, Prod.snd] using
    realSign_mul_congr (c := (l.normal.y : ℝ)) hgraph

private theorem vertical_root_before_radius
    (L : Finset RationalLine) (R : ℝ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < R)
    (l m : RationalLine) (hl : l ∈ L) (hm : m ∈ L)
    (hly : l.normal.y = 0) (hmy : m.normal.y ≠ 0)
    (hmgraph : rightGraph m = (1, 0)) :
    l.offset / (l.normal.x : ℝ) < R := by
  have hlx : l.normal.x ≠ 0 := by
    rcases l.normal.nonzero with hx | hy
    · exact hx
    · exact (hy hly).elim
  have hx : (l.normal.x : ℝ) ≠ 0 := by exact_mod_cast hlx
  let t : ℝ := l.offset / (l.normal.x : ℝ)
  let p : Plane := t + t * Complex.I
  have hdet : l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 := by
    have hprod : l.normal.x * m.normal.y ≠ 0 := mul_ne_zero hlx hmy
    simpa [hly] using hprod
  have hlp : l.eval p = 0 := by
    simp [RationalLine.eval, normalEval, p, t, hly]
    field_simp
    ring
  have hmp : m.eval p = 0 := by
    rw [lineEval_rightGraph m hmy p, hmgraph]
    simp [p]
  have hnorm := hinter l hl m hm hdet p hlp hmp
  have hpRe : p.re = t := by simp [p]
  have hle : t ≤ ‖p‖ := by
    calc
      t ≤ |t| := le_abs_self t
      _ = |p.re| := by rw [hpRe]
      _ ≤ ‖p‖ := Complex.abs_re_le_norm p
  have htless : t < R := lt_of_le_of_lt hle hnorm
  simpa [t] using htless

/-- On the right exterior ray, a vertical line has the sign of its horizontal
normal. Its root is forced inside the radius by intersecting the fixed outgoing
diagonal graph. -/
private theorem vertical_line_sign_of_intersections
    (L : Finset RationalLine) (R : ℝ)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < R)
    (m : RationalLine) (hm : m ∈ L) (hmy : m.normal.y ≠ 0)
    (hmgraph : rightGraph m = (1, 0))
    (l : RationalLine) (hl : l ∈ L) (hly : l.normal.y = 0)
    (z : Plane) (hz : R ≤ z.re) :
    Real.sign (l.eval z) = Real.sign (l.normal.x : ℝ) := by
  have hlx : l.normal.x ≠ 0 := by
    rcases l.normal.nonzero with hx | hy
    · exact hx
    · exact (hy hly).elim
  have hx : (l.normal.x : ℝ) ≠ 0 := by exact_mod_cast hlx
  have ht := vertical_root_before_radius L R hinter l m hl hm hly hmy hmgraph
  have hradial : 0 < z.re - l.offset / (l.normal.x : ℝ) := by linarith
  have hfactor : l.eval z = (l.normal.x : ℝ) *
      (z.re - l.offset / (l.normal.x : ℝ)) := by
    simp [RationalLine.eval, normalEval, hly]
    field_simp
  rw [hfactor]
  have hsign : Real.sign ((l.normal.x : ℝ) *
      (z.re - l.offset / (l.normal.x : ℝ))) =
      Real.sign (l.normal.x : ℝ) := by
    simpa only [mul_one] using realSign_mul_congr (c := (l.normal.x : ℝ))
      (x := z.re - l.offset / (l.normal.x : ℝ)) (y := 1)
      (by rw [Real.sign_of_pos hradial, Real.sign_one])
  simpa using hsign

/-- Source and deformed vertical labels have the same sign after any map that
preserves the exterior radius, provided the actual target intersections also
remain inside that radius. No initial-sign test is used. -/
private theorem vertical_line_sign_transport
    (φ : ℝ →ₗ[ℚ] ℚ) (L : Finset RationalLine) (R : ℝ)
    (hsource : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < R)
    (htarget : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < R)
    (m : RationalLine) (hm : m ∈ L) (hmy : m.normal.y ≠ 0)
    (hmgraph : rightGraph m = (1, 0))
    (l : RationalLine) (hl : l ∈ L) (hly : l.normal.y = 0)
    (H : Plane → Plane) (z : Plane) (hz : R ≤ z.re)
    (hradius : (H z).re = z.re) :
    Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
  classical
  have hsourceSign := vertical_line_sign_of_intersections L R hsource m hm hmy
    hmgraph l hl hly z hz
  have hmTargetGraph : rightGraph (deformLine φ m) = (1, 0) := by
    rw [rightGraph_deform m hmy φ, hmgraph]
    simp [map_zero]
  have htargetBound : ∀ l' ∈ L.image (deformLine φ),
      ∀ m' ∈ L.image (deformLine φ),
      l'.normal.x * m'.normal.y - l'.normal.y * m'.normal.x ≠ 0 →
        ∀ q : Plane, l'.eval q = 0 → m'.eval q = 0 → ‖q‖ < R := by
    intro l' hl' m' hm' hdet q hq hmq
    obtain ⟨l₁, hl₁, rfl⟩ := Finset.mem_image.mp hl'
    obtain ⟨m₁, hm₁, rfl⟩ := Finset.mem_image.mp hm'
    exact htarget l₁ hl₁ m₁ hm₁ hdet q hq hmq
  have htargetM : deformLine φ m ∈ L.image (deformLine φ) :=
    Finset.mem_image.mpr ⟨m, hm, rfl⟩
  have htargetL : deformLine φ l ∈ L.image (deformLine φ) :=
    Finset.mem_image.mpr ⟨l, hl, rfl⟩
  have htargetY : (deformLine φ l).normal.y = 0 := by simpa [deformLine] using hly
  have htargetRadius : R ≤ (H z).re := by rw [hradius]; exact hz
  have htargetSign := vertical_line_sign_of_intersections
    (L.image (deformLine φ)) R htargetBound (deformLine φ m) htargetM hmy
    hmTargetGraph (deformLine φ l) htargetL htargetY (H z) htargetRadius
  have hnxy : (deformLine φ l).normal.x = l.normal.x := rfl
  rw [hnxy] at htargetSign
  exact htargetSign.trans hsourceSign.symm

private def exteriorPairPoint (p : ℝ × ℝ) : Plane := p.1 + p.2 * Complex.I

private theorem pairSectorHomeomorph_preserves_line_signs
    (φ : ℝ →ₗ[ℚ] ℚ) (L : Finset RationalLine) (R : ℝ)
    (hsource : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < R)
    (htarget : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x * m.normal.y - l.normal.y * m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < R)
    (m : RationalLine) (hm : m ∈ L) (hmy : m.normal.y ≠ 0)
    (hmgraph : rightGraph m = (1, 0))
    (H : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R} ≃ₜ {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R})
    (hradius : ∀ p, (H p).val.1 = p.val.1)
    (hgraph : ∀ l ∈ L, ∀ _hly : l.normal.y ≠ 0, ∀ p : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R},
      Real.sign ((H p).val.2 - (rightGraph l).1 * (H p).val.1 -
        (φ (rightGraph l).2 : ℝ)) =
      Real.sign (p.val.2 - (rightGraph l).1 * p.val.1 - (rightGraph l).2))
    (l : RationalLine) (hl : l ∈ L) (p : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R}) :
    Real.sign ((deformLine φ l).eval (exteriorPairPoint (H p).val)) =
      Real.sign (l.eval (exteriorPairPoint p.val)) := by
  by_cases hly : l.normal.y = 0
  · have hz : R ≤ (exteriorPairPoint p.val).re := by
      simpa [exteriorPairPoint] using p.property.1
    have hrad : (exteriorPairPoint (H p).val).re = (exteriorPairPoint p.val).re := by
      simpa [exteriorPairPoint] using hradius p
    have hv := vertical_line_sign_transport φ L R hsource htarget m hm hmy hmgraph
      l hl hly (fun _ : Plane => exteriorPairPoint (H p).val) (exteriorPairPoint p.val) hz hrad
    simpa [exteriorPairPoint] using hv
  · have hg := hgraph l hl hly p
    have hgraphPlane : Real.sign (
        ((fun _ : Plane => exteriorPairPoint (H p).val) (exteriorPairPoint p.val)).im -
          (rightGraph l).1 * ((fun _ : Plane => exteriorPairPoint (H p).val) (exteriorPairPoint p.val)).re -
            (φ (rightGraph l).2 : ℝ)) =
        Real.sign ((exteriorPairPoint p.val).im - (rightGraph l).1 * (exteriorPairPoint p.val).re -
          (rightGraph l).2) := by
      simpa [exteriorPairPoint] using hg
    have hn := nonvertical_line_sign_transport φ l hly
      (fun _ : Plane => exteriorPairPoint (H p).val) (exteriorPairPoint p.val) hgraphPlane
    simpa [exteriorPairPoint] using hn

/-- Graph-sign identities for actual labels representing the two diagonal
corner graphs force the sector homeomorphism to fix both corner rays. -/
private theorem pairSectorHomeomorph_fixes_corner_rays
    (φ : ℝ →ₗ[ℚ] ℚ) (L : Finset RationalLine) (R : ℝ)
    (H : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R} ≃ₜ {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R})
    (hradius : ∀ p, (H p).val.1 = p.val.1)
    (hgraph : ∀ l ∈ L, ∀ _hly : l.normal.y ≠ 0, ∀ p : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R},
      Real.sign ((H p).val.2 - (rightGraph l).1 * (H p).val.1 -
        (φ (rightGraph l).2 : ℝ)) =
      Real.sign (p.val.2 - (rightGraph l).1 * p.val.1 - (rightGraph l).2))
    (mminus mplus : RationalLine) (hmminus : mminus ∈ L) (hmplus : mplus ∈ L)
    (hmyminus : mminus.normal.y ≠ 0) (hmyplus : mplus.normal.y ≠ 0)
    (hminus : rightGraph mminus = (-1, 0))
    (hplus : rightGraph mplus = (1, 0))
    (p : {p : ℝ × ℝ // p ∈ ExteriorFaceCharts.faceSector R})
    (hp : p.val.2 = p.val.1 ∨ p.val.2 = -p.val.1) : H p = p := by
  rcases hp with hupper | hlower
  · have hs := hgraph mplus hmplus hmyplus p
    have hsourcezero : Real.sign
        (p.val.2 - (rightGraph mplus).1 * p.val.1 - (rightGraph mplus).2) = 0 := by
      rw [hplus]
      simp [hupper]
    have htargetzero := hs.trans hsourcezero
    have hzero : Real.sign ((H p).val.2 - (H p).val.1) = 0 := by
      simpa [hplus, map_zero] using htargetzero
    have heq : (H p).val.2 - (H p).val.1 = 0 := Real.sign_eq_zero_iff.mp hzero
    have hrad := hradius p
    apply Subtype.ext
    apply Prod.ext
    · exact hradius p
    · linarith [heq, hupper, hrad]
  · have hs := hgraph mminus hmminus hmyminus p
    have hsourcezero : Real.sign
        (p.val.2 - (rightGraph mminus).1 * p.val.1 - (rightGraph mminus).2) = 0 := by
      rw [hminus]
      simp [hlower]
    have htargetzero := hs.trans hsourcezero
    have hzero : Real.sign ((H p).val.2 + (H p).val.1) = 0 := by
      simpa [hminus, map_zero] using htargetzero
    have heq : (H p).val.2 + (H p).val.1 = 0 := Real.sign_eq_zero_iff.mp hzero
    have hrad := hradius p
    apply Subtype.ext
    apply Prod.ext
    · exact hradius p
    · linarith [heq, hlower, hrad]

private theorem signedCodes_strictAt (L : List RationalLine) (p : Plane)
    (hoff : ∀ l ∈ L, l.eval p ≠ 0) :
    ∃ C ∈ signedCodes L, ∀ l ∈ C, l.eval p < 0 := by
  induction L with
  | nil =>
      refine ⟨[], by simp [signedCodes], ?_⟩
      simp
  | cons l L ih =>
      have hoffTail : ∀ k ∈ L, k.eval p ≠ 0 := by
        intro k hk
        exact hoff k (List.mem_cons_of_mem l hk)
      obtain ⟨C, hC, hstrictC⟩ := ih hoffTail
      have hline : l.eval p ≠ 0 := hoff l List.mem_cons_self
      by_cases hlneg : l.eval p < 0
      · refine ⟨l :: C, ?_, ?_⟩
        · simp [signedCodes, hC]
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hlneg
          · exact hstrictC k hk
      · have hlpos : 0 < l.eval p := lt_of_le_of_ne (le_of_not_gt hlneg) (Ne.symm hline)
        refine ⟨negateLine l :: C, ?_, ?_⟩
        · simp [signedCodes, hC]
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · rw [negateLine_eval]
            linarith
          · exact hstrictC k hk


private def rightPoint (R y : ℝ) : Plane := (R : ℂ) + y * Complex.I


private theorem lineEval_rightPoint (l : RationalLine) (R y : ℝ) :
    l.eval (rightPoint R y) = (l.normal.x : ℝ) * R +
      (l.normal.y : ℝ) * y - l.offset := by
  simp [RationalLine.eval, rightPoint, normalEval]


private def rightGraphValue (l : RationalLine) (R : ℝ) : ℝ :=
  -((l.normal.x : ℝ) / (l.normal.y : ℝ)) * R + l.offset / (l.normal.y : ℝ)


private theorem lineEval_rightPoint_zero_iff_graph (l : RationalLine) (R y : ℝ)
    (hny : (l.normal.y : ℝ) ≠ 0) :
    l.eval (rightPoint R y) = 0 ↔ y = rightGraphValue l R := by
  rw [lineEval_rightPoint]
  unfold rightGraphValue
  constructor <;> intro h <;> field_simp [hny] at h ⊢ <;> nlinarith


private theorem lineEval_rightPoint_graphValue (l : RationalLine) (R : ℝ)
    (hny : (l.normal.y : ℝ) ≠ 0) :
    l.eval (rightPoint R (rightGraphValue l R)) = 0 :=
  (lineEval_rightPoint_zero_iff_graph l R (rightGraphValue l R) hny).mpr rfl


private theorem lineEval_rightPoint_affine (l : RationalLine) (R y z : ℝ)
    (r s : ℝ) (hsum : r + s = 1) :
    l.eval (rightPoint R (r*y + s*z)) =
      r * l.eval (rightPoint R y) + s * l.eval (rightPoint R z) := by
  rw [lineEval_rightPoint, lineEval_rightPoint, lineEval_rightPoint]
  linear_combination -((l.normal.x : ℝ) * R - l.offset) * hsum


private def realSquareLines (R : ℝ) : List RationalLine :=
  [⟨⟨1, 0, by norm_num⟩, R⟩, ⟨⟨-1, 0, by norm_num⟩, R⟩,
   ⟨⟨0, 1, by norm_num⟩, R⟩, ⟨⟨0, -1, by norm_num⟩, R⟩]


private def clippedRightFace (R : ℝ) (cell : List RationalLine) : Set Plane :=
  closedCell (realSquareLines R ++ cell) ∩ {z | z.re = R}


private theorem openSquareLines_inward (R ym δ : ℝ)
    (_hR : 0 < R) (hδ : 0 < δ) (hδR : δ < R) (hym : -R < ym ∧ ym < R) :
    rightPoint (R-δ) ym ∈ openCell (realSquareLines R) := by
  intro l hl
  simp only [realSquareLines, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with hl | hl | hl | hl
  · subst l
    simp [RationalLine.eval, normalEval, rightPoint]
    linarith
  · subst l
    simp [RationalLine.eval, normalEval, rightPoint]
    linarith
  · subst l
    simp [RationalLine.eval, normalEval, rightPoint]
    linarith
  · subst l
    simp [RationalLine.eval, normalEval, rightPoint]
    linarith


private theorem exists_strict_inward_point (R y₀ y₁ : ℝ) (C : List RationalLine)
    (hR : 0 < R) (hy₀ : -R ≤ y₀) (hy₁ : y₁ ≤ R) (horder : y₀ < y₁)
    (hstrict : ∀ l ∈ C, l.eval (rightPoint R ((y₀+y₁)/2)) < 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
      rightPoint (R-δ) ((y₀+y₁)/2) ∈ openCell (realSquareLines R ++ C) := by
  let ym := (y₀+y₁)/2
  let p := rightPoint R ym
  have hym : -R < ym ∧ ym < R := by constructor <;> dsimp [ym] <;> linarith
  have hp : p ∈ openCell C := hstrict
  have hopen := openCell_isOpen C
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen p hp
  let δ := min (ε/2) (R/2)
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by linarith) (by linarith)
  have hδR : δ < R := by dsimp [δ]; exact (min_le_right _ _).trans_lt (by linarith)
  have hdist : dist (rightPoint (R-δ) ym) p = δ := by
    simp [p, rightPoint, dist_eq_norm, abs_of_pos hδ]
  have hpδ : rightPoint (R-δ) ym ∈ openCell C := by
    apply hball
    rw [Metric.mem_ball, hdist]
    have hδeps : δ ≤ ε/2 := min_le_left _ _
    have hhalf : ε/2 < ε := by linarith
    exact lt_of_le_of_lt hδeps hhalf
  have hsquare : rightPoint (R-δ) ym ∈ openCell (realSquareLines R) :=
    openSquareLines_inward R ym δ hR hδ hδR hym
  refine ⟨δ, hδ, hδR, ?_⟩
  rw [openCell_append]
  exact ⟨hsquare, hpδ⟩



private theorem lineEval_nonposOnVerticalInterval
    (l : RationalLine) (R y₀ yₘ y₁ : ℝ)
    (hy₀ : y₀ < yₘ) (hy₁ : yₘ < y₁)
    (hmid : l.eval (rightPoint R yₘ) < 0)
    (hroot : ∀ y, y₀ < y → y < y₁ → l.eval (rightPoint R y) ≠ 0) :
    ∀ y, y₀ ≤ y → y ≤ y₁ → l.eval (rightPoint R y) ≤ 0 := by
  intro y hylo hyhi
  by_contra hnot
  have hypos : 0 < l.eval (rightPoint R y) := lt_of_not_ge hnot
  let den := l.eval (rightPoint R y) - l.eval (rightPoint R yₘ)
  let r := l.eval (rightPoint R y) / den
  let s := -(l.eval (rightPoint R yₘ)) / den
  have hden : 0 < den := by dsimp [den]; linarith
  have hr : 0 < r := div_pos hypos hden
  have hs : 0 < s := by dsimp [s]; exact div_pos (neg_pos.mpr hmid) hden
  have hrsum : r + s = 1 := by
    have hnum : l.eval (rightPoint R y) + -l.eval (rightPoint R yₘ) = den := by
      dsimp [den]
      ring
    dsimp [r, s]
    rw [← add_div, hnum, div_self (ne_of_gt hden)]
  have hzero : l.eval (rightPoint R (r*yₘ + s*y)) = 0 := by
    have h := lineEval_rightPoint_affine l R yₘ y r s hrsum
    have hcancel :
        r * l.eval (rightPoint R yₘ) + s * l.eval (rightPoint R y) = 0 := by
      dsimp [r, s, den]
      field_simp
      ring
    calc
      l.eval (rightPoint R (r*yₘ + s*y)) =
          r * l.eval (rightPoint R yₘ) + s * l.eval (rightPoint R y) := h
      _ = 0 := hcancel
  have hbetween : y₀ < r*yₘ+s*y ∧ r*yₘ+s*y < y₁ := by
    have hlo₁ : 0 < r * (yₘ-y₀) := mul_pos hr (sub_pos.mpr hy₀)
    have hlo₂ : 0 ≤ s * (y-y₀) := mul_nonneg hs.le (sub_nonneg.mpr hylo)
    have hhi₁ : 0 < r * (y₁-yₘ) := mul_pos hr (sub_pos.mpr hy₁)
    have hhi₂ : 0 ≤ s * (y₁-y) := mul_nonneg hs.le (sub_nonneg.mpr hyhi)
    have hlowid : r*yₘ+s*y-y₀ = r*(yₘ-y₀)+s*(y-y₀) := by
      have hr' : r = 1-s := by linarith
      rw [hr']
      ring
    have hhighid : y₁-(r*yₘ+s*y) = r*(y₁-yₘ)+s*(y₁-y) := by
      have hr' : r = 1-s := by linarith
      rw [hr']
      ring
    constructor
    · linarith [hlowid, hlo₁, hlo₂]
    · linarith [hhighid, hhi₁, hhi₂]
  exact hroot _ hbetween.1 hbetween.2 hzero


private theorem mem_closedCell_realSquareLines (R : ℝ) (z : Plane) :
    z ∈ closedCell (realSquareLines R) ↔
      (-R ≤ z.re ∧ z.re ≤ R) ∧ (-R ≤ z.im ∧ z.im ≤ R) := by
  simp only [closedCell, realSquareLines, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RationalLine.eval, normalEval]
  norm_num
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩


private theorem rightPoint_mem_segment_iff (R y₀ y₁ y : ℝ) (horder : y₀ < y₁) :
    rightPoint R y ∈ segment ℝ (rightPoint R y₀) (rightPoint R y₁) ↔
      y₀ ≤ y ∧ y ≤ y₁ := by
  constructor
  · rintro ⟨r, s, hr, hs, hrs, hpoint⟩
    have him : y = r*y₀+s*y₁ := by
      have him := congrArg Complex.im hpoint
      simpa [rightPoint] using him.symm
    constructor
    · rw [him]
      have hid : r*y₀+s*y₁-y₀ = s*(y₁-y₀) := by
        have hr' : r = 1-s := by linarith
        rw [hr']
        ring
      have h := mul_nonneg hs (sub_nonneg.mpr (le_of_lt horder))
      linarith [hid, h]
    · rw [him]
      have hid : y₁-(r*y₀+s*y₁) = r*(y₁-y₀) := by
        have hr' : r = 1-s := by linarith
        rw [hr']
        ring
      have h := mul_nonneg hr (sub_nonneg.mpr (le_of_lt horder))
      linarith [hid, h]
  · rintro ⟨hy₀, hy₁⟩
    have hgap : 0 < y₁-y₀ := sub_pos.mpr horder
    let r := (y₁-y)/(y₁-y₀)
    let s := (y-y₀)/(y₁-y₀)
    have hrs : r+s=1 := by
      dsimp [r, s]
      field_simp
      ring
    refine ⟨r, s, ?_, ?_, hrs, ?_⟩
    · exact div_nonneg (sub_nonneg.mpr hy₁) hgap.le
    · exact div_nonneg (sub_nonneg.mpr hy₀) hgap.le
    · apply Complex.ext
      · simp [rightPoint]
        linear_combination R * hrs
      · simp [rightPoint]
        dsimp [r, s]
        field_simp
        ring


private theorem segment_rightPoint_real (R y₀ y₁ : ℝ) (z : Plane)
    (hz : z ∈ segment ℝ (rightPoint R y₀) (rightPoint R y₁)) : z.re = R := by
  obtain ⟨r, s, _, _, hrs, hpoint⟩ := hz
  have hre := congrArg Complex.re hpoint
  simp [rightPoint] at hre
  have hre' : r * R + s * R = R := by
    calc
      r * R + s * R = (r+s)*R := by ring
      _ = 1*R := by rw [hrs]
      _ = R := by ring
  linarith


private theorem clippedRightFace_eq_segment
    (R y₀ y₁ : ℝ) (C : List RationalLine)
    (hR : 0 < R) (hy₀ : -R ≤ y₀) (hy₁ : y₁ ≤ R) (horder : y₀ < y₁)
    (hstrict : ∀ l ∈ C, l.eval (rightPoint R ((y₀+y₁)/2)) < 0)
    (hroot : ∀ l ∈ C, ∀ y, y₀ < y → y < y₁ →
      l.eval (rightPoint R y) ≠ 0)
    (kl kh : RationalLine) (hkl : kl ∈ C) (hkh : kh ∈ C)
    (hlzero : kl.eval (rightPoint R y₀) = 0)
    (hhzero : kh.eval (rightPoint R y₁) = 0) :
    clippedRightFace R C =
      segment ℝ (rightPoint R y₀) (rightPoint R y₁) := by
  let ym := (y₀+y₁)/2
  have hy₀m : y₀ < ym := by dsimp [ym]; linarith
  have hym₁ : ym < y₁ := by dsimp [ym]; linarith
  have hklmid : kl.eval (rightPoint R ym) < 0 := hstrict kl hkl
  have hkhmid : kh.eval (rightPoint R ym) < 0 := hstrict kh hkh
  have hklcoef : (kl.normal.y : ℝ) < 0 := by
    have hmid' := lineEval_rightPoint kl R ym
    have hzero' := lineEval_rightPoint kl R y₀
    rw [hmid'] at hklmid
    rw [hzero'] at hlzero
    by_contra hn
    have hcoef : 0 ≤ (kl.normal.y : ℝ) := by exact_mod_cast (le_of_not_gt hn)
    have hprod := mul_nonneg hcoef (le_of_lt (sub_pos.mpr hy₀m))
    nlinarith
  have hkhcoef : 0 < (kh.normal.y : ℝ) := by
    have hmid' := lineEval_rightPoint kh R ym
    have hzero' := lineEval_rightPoint kh R y₁
    rw [hmid'] at hkhmid
    rw [hzero'] at hhzero
    by_contra hn
    have hcoef : (kh.normal.y : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_gt hn)
    have hprod := mul_nonneg_of_nonpos_of_nonpos hcoef (le_of_lt (sub_neg.mpr hym₁))
    nlinarith
  have hclosed : closedCell (realSquareLines R ++ C) =
      closedCell (realSquareLines R) ∩ closedCell C := closedCell_append _ _
  apply Set.Subset.antisymm
  · intro z hz
    change z ∈ closedCell (realSquareLines R ++ C) ∧ z.re = R at hz
    rw [hclosed] at hz
    have hzbox : z ∈ closedCell (realSquareLines R) := hz.1.1
    have hzC : z ∈ closedCell C := hz.1.2
    have hzr : z.re = R := hz.2
    have hzy : -R ≤ z.im ∧ z.im ≤ R := ((mem_closedCell_realSquareLines R z).mp hzbox).2
    have hzeq : z = rightPoint R z.im := by
      apply Complex.ext
      · simp [rightPoint, hzr]
      · simp [rightPoint]
    have hineqL : (kl.normal.x : ℝ) * R + (kl.normal.y : ℝ) * z.im - kl.offset ≤ 0 := by
      have hineq := hzC kl hkl
      rw [hzeq, lineEval_rightPoint] at hineq
      exact hineq
    have hlzero' := lineEval_rightPoint kl R y₀
    rw [hlzero'] at hlzero
    have hlo : y₀ ≤ z.im := by
      by_contra hn
      have hlt : z.im < y₀ := lt_of_not_ge hn
      have hp := mul_pos (neg_pos.mpr hklcoef) (sub_pos.mpr hlt)
      nlinarith [hineqL, hlzero]
    have hineqH : (kh.normal.x : ℝ) * R + (kh.normal.y : ℝ) * z.im - kh.offset ≤ 0 := by
      have hineq := hzC kh hkh
      rw [hzeq, lineEval_rightPoint] at hineq
      exact hineq
    have hhzero' := lineEval_rightPoint kh R y₁
    rw [hhzero'] at hhzero
    have hhi : z.im ≤ y₁ := by
      by_contra hn
      have hlt : y₁ < z.im := lt_of_not_ge hn
      have hp := mul_pos hkhcoef (sub_pos.mpr hlt)
      nlinarith [hineqH, hhzero]
    have hzseg : rightPoint R z.im ∈ segment ℝ (rightPoint R y₀) (rightPoint R y₁) :=
      (rightPoint_mem_segment_iff R y₀ y₁ z.im horder).mpr ⟨hlo, hhi⟩
    rw [hzeq]
    exact hzseg
  · intro z hz
    change z ∈ segment ℝ (rightPoint R y₀) (rightPoint R y₁) at hz
    have hzr : z.re = R := segment_rightPoint_real R y₀ y₁ z hz
    have hzpoint : z = rightPoint R z.im := by
      apply Complex.ext
      · simp [rightPoint, hzr]
      · simp [rightPoint]
    have hzright : rightPoint R z.im ∈ segment ℝ (rightPoint R y₀) (rightPoint R y₁) := by
      rw [← hzpoint]
      exact hz
    have hzy := rightPoint_mem_segment_iff R y₀ y₁ z.im horder |>.mp hzright
    have hzbox : z ∈ closedCell (realSquareLines R) := by
      apply (mem_closedCell_realSquareLines R z).mpr
      refine ⟨?_, ?_⟩
      · constructor
        · rw [hzr]
          linarith
        · rw [hzr]
      · exact ⟨by linarith [hy₀], by linarith [hy₁]⟩
    have hzC : z ∈ closedCell C := by
      intro l hl
      have hm₀ : y₀ < (y₀+y₁)/2 := by linarith
      have hm₁ : (y₀+y₁)/2 < y₁ := by linarith
      have hn := lineEval_nonposOnVerticalInterval l R y₀ ((y₀+y₁)/2) y₁ hm₀ hm₁
        (hstrict l hl) (hroot l hl)
      have hle := hn z.im hzy.1 hzy.2
      rw [hzpoint]
      exact hle
    have hzall : z ∈ closedCell (realSquareLines R ++ C) := by rw [hclosed]; exact ⟨hzbox, hzC⟩
    change z ∈ closedCell (realSquareLines R ++ C) ∧ z.re = R
    exact ⟨hzall, hzr⟩

/-- Adjacent source boundary roots determine an actual strict signed clipped cell and its
entire right clipping face. The hypotheses are finite-arrangement facts: the two endpoint
labels vanish at the anchors, and no source label vanishes in the open interval between. -/

private theorem exists_clippedRightFace_for_adjacent_roots
    (R y₀ y₁ : ℝ) (L : List RationalLine) (lo hi : RationalLine)
    (hR : 0 < R) (hy₀ : -R ≤ y₀) (hy₁ : y₁ ≤ R) (horder : y₀ < y₁)
    (hlo : lo ∈ L) (hhi : hi ∈ L)
    (hlzero : lo.eval (rightPoint R y₀) = 0)
    (hhzero : hi.eval (rightPoint R y₁) = 0)
    (hnoroot : ∀ l ∈ L, ∀ y, y₀ < y → y < y₁ →
      l.eval (rightPoint R y) ≠ 0) :
    ∃ C ∈ signedCodes L,
      (∀ k ∈ C, k.eval (rightPoint R ((y₀+y₁)/2)) < 0) ∧
      clippedRightFace R C = segment ℝ (rightPoint R y₀) (rightPoint R y₁) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
        rightPoint (R-δ) ((y₀+y₁)/2) ∈ openCell (realSquareLines R ++ C) := by
  let ym := (y₀+y₁)/2
  have hym₀ : y₀ < ym := by dsimp [ym]; linarith
  have hym₁ : ym < y₁ := by dsimp [ym]; linarith
  have hoff : ∀ l ∈ L, l.eval (rightPoint R ym) ≠ 0 := by
    intro l hl
    exact hnoroot l hl ym hym₀ hym₁
  obtain ⟨C, hC, hstrict⟩ := signedCodes_strictAt L (rightPoint R ym) hoff
  have hlorient := signedCodes_has_each_line L C hC lo hlo
  obtain ⟨kl, hkl, hlzeroC⟩ : ∃ k ∈ C, k.eval (rightPoint R y₀) = 0 := by
    rcases hlorient with h | h
    · exact ⟨lo, h, hlzero⟩
    · exact ⟨negateLine lo, h, by rw [negateLine_eval, hlzero]; simp⟩
  have hhiorient := signedCodes_has_each_line L C hC hi hhi
  obtain ⟨kh, hkh, hhzeroC⟩ : ∃ k ∈ C, k.eval (rightPoint R y₁) = 0 := by
    rcases hhiorient with h | h
    · exact ⟨hi, h, hhzero⟩
    · exact ⟨negateLine hi, h, by rw [negateLine_eval, hhzero]; simp⟩
  have hrootC : ∀ k ∈ C, ∀ y, y₀ < y → y < y₁ →
      k.eval (rightPoint R y) ≠ 0 := by
    intro k hk y hy₀y hyy₁
    obtain ⟨l, hl, hkind⟩ := signedCodes_literals L C hC k hk
    rcases hkind with hkind | hkind
    · subst k
      exact hnoroot l hl y hy₀y hyy₁
    · subst k
      have hn := hnoroot l hl y hy₀y hyy₁
      rw [negateLine_eval]
      exact neg_ne_zero.mpr hn
  have hface := clippedRightFace_eq_segment R y₀ y₁ C hR hy₀ hy₁ horder
    hstrict hrootC kl kh hkl hkh hlzeroC hhzeroC
  have hinterior := exists_strict_inward_point R y₀ y₁ C hR hy₀ hy₁ horder hstrict
  exact ⟨C, hC, hstrict, hface, hinterior⟩

/-- Instantiates adjacent whole-face incidence from an actually sorted finite graph family.
Every label root strictly inside the box must be represented by one of the listed graph
indices; vertical labels are separately certified to miss the box's right side. -/

private theorem adjacent_right_faces_of_sorted_family
    (R : ℝ) (n : ℕ) (_hn : 0 < n) (L : List RationalLine)
    (a b : Fin (n+1) → ℝ)
    (hR : 0 < R)
    (hfirst : a 0 * R + b 0 = -R)
    (hlast : a (Fin.last n) * R + b (Fin.last n) = R)
    (hmono : StrictMono (fun j : Fin (n+1) => a j * R + b j))
    (hlabels : ∀ j : Fin (n+1), ∃ l ∈ L,
      (l.normal.y : ℝ) ≠ 0 ∧
      -((l.normal.x : ℝ)/(l.normal.y : ℝ)) = a j ∧
      l.offset/(l.normal.y : ℝ) = b j)
    (hlookup : ∀ l ∈ L, (l.normal.y : ℝ) ≠ 0 →
      -R < rightGraphValue l R → rightGraphValue l R < R →
      ∃ j : Fin (n+1), rightGraphValue l R = a j * R + b j)
    (hvertical : ∀ l ∈ L, (l.normal.y : ℝ) = 0 →
      ∀ y, -R ≤ y → y ≤ R → l.eval (rightPoint R y) ≠ 0) :
    ∀ i : Fin n, ∃ C ∈ signedCodes L,
      (∀ k ∈ C, k.eval (rightPoint R ((a i.castSucc * R + b i.castSucc +
        a i.succ * R + b i.succ)/2)) < 0) ∧
      clippedRightFace R C = segment ℝ
        (rightPoint R (a i.castSucc * R + b i.castSucc))
        (rightPoint R (a i.succ * R + b i.succ)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < R ∧
        rightPoint (R-δ) ((a i.castSucc * R + b i.castSucc +
          a i.succ * R + b i.succ)/2) ∈ openCell (realSquareLines R ++ C) := by
  intro i
  let v : Fin (n+1) → ℝ := fun j => a j * R + b j
  have hfirst' : v 0 = -R := by simpa [v] using hfirst
  have hlast' : v (Fin.last n) = R := by simpa [v] using hlast
  have hzero_le : (0 : Fin (n+1)) ≤ i.castSucc := Fin.zero_le _
  have hlast_ge : i.succ ≤ Fin.last n := by
    apply Fin.le_iff_val_le_val.mpr
    simp [Fin.val_last]
  have hlow : -R ≤ v i.castSucc := by
    have h := hmono.monotone hzero_le
    simpa [v, hfirst'] using h
  have hhigh : v i.succ ≤ R := by
    have h := hmono.monotone hlast_ge
    simpa [v, hlast'] using h
  have horder : v i.castSucc < v i.succ := hmono i.castSucc_lt_succ
  obtain ⟨lo, hlo, hloy, hloSlope, hloOffset⟩ := hlabels i.castSucc
  obtain ⟨hi, hhi, hhiy, hhiSlope, hhiOffset⟩ := hlabels i.succ
  have hlozero : lo.eval (rightPoint R (v i.castSucc)) = 0 := by
    rw [lineEval_rightPoint]
    change (lo.normal.x : ℝ) * R + (lo.normal.y : ℝ) *
      (a i.castSucc * R + b i.castSucc) - lo.offset = 0
    rw [← hloSlope, ← hloOffset]
    field_simp [hloy]
    ring
  have hhizero : hi.eval (rightPoint R (v i.succ)) = 0 := by
    rw [lineEval_rightPoint]
    change (hi.normal.x : ℝ) * R + (hi.normal.y : ℝ) *
      (a i.succ * R + b i.succ) - hi.offset = 0
    rw [← hhiSlope, ← hhiOffset]
    field_simp [hhiy]
    ring
  have hnoroot : ∀ l ∈ L, ∀ y, v i.castSucc < y → y < v i.succ →
      l.eval (rightPoint R y) ≠ 0 := by
    intro l hl y hloy' hyhi'
    by_cases hvertical' : (l.normal.y : ℝ) = 0
    · exact fun hz => hvertical l hl hvertical' y (by linarith [hlow]) (by linarith [hhigh]) hz
    · intro heval
      have hyGraph : y = rightGraphValue l R :=
        (lineEval_rightPoint_zero_iff_graph l R y hvertical').mp heval
      have hyBoxL : -R < rightGraphValue l R := by rw [← hyGraph]; linarith [hlow, hloy']
      have hyBoxU : rightGraphValue l R < R := by rw [← hyGraph]; linarith [hhigh, hyhi']
      obtain ⟨j, hj⟩ := hlookup l hl hvertical' hyBoxL hyBoxU
      have hyv : y = v j := by simpa [v] using hyGraph.trans hj
      by_cases hjlow : j.val ≤ i.val
      · have hjle : j ≤ i.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          simpa using hjlow
        have hvle := hmono.monotone hjle
        have hvle' : v j ≤ v i.castSucc := by simpa [v] using hvle
        rw [← hyv] at hvle'
        linarith
      · have hjhigh : i.succ ≤ j := by
          apply Fin.le_iff_val_le_val.mpr
          simp [Fin.val_succ] at *
          omega
        have hvle := hmono.monotone hjhigh
        have hvle' : v i.succ ≤ v j := by simpa [v] using hvle
        rw [← hyv] at hvle'
        linarith
  simpa [v, add_assoc] using
    (exists_clippedRightFace_for_adjacent_roots R (v i.castSucc) (v i.succ) L lo hi
      hR hlow hhigh horder hlo hhi hlozero hhizero hnoroot)

/-- Conjugating the actual sector map into any of the four square faces transports
the signs of original lines.  The square-coordinate line identity is exact, and
the commuting deformation identity ensures the target is the prescribed
deformation of the original line. -/
private theorem sectorHomeomorph_on_squareFace_preserves_line_signs
    (φ : ℝ →ₗ[ℚ] ℚ) (L : Finset RationalLine) (R : ℝ) (i : Fin 4)
    (H : ExteriorFaceCharts.faceSector R ≃ₜ ExteriorFaceCharts.faceSector R)
    (hsector : ∀ l ∈ L, ∀ q : ExteriorFaceCharts.faceSector R,
      Real.sign ((deformLine φ (squareFaceLine i l)).eval (Complex.equivRealProdCLM.symm (H q).val)) =
        Real.sign ((squareFaceLine i l).eval (Complex.equivRealProdCLM.symm q.val)))
    (l : RationalLine) (hl : l ∈ L) (p : ExteriorFourFaces.FacePoint R i) :
    Real.sign ((deformLine φ l).eval (Complex.equivRealProdCLM.symm (sectorHomeomorph_on_squareFace R i H p).val)) =
      Real.sign (l.eval (Complex.equivRealProdCLM.symm p.val)) := by
  have hs := hsector l hl (squareFaceSectorHomeomorph R i p)
  have hpoint : (sectorHomeomorph_on_squareFace R i H p).val =
      (squareFaceCoordinates i).symm (H (squareFaceSectorHomeomorph R i p)).val := by
    rfl
  rw [hpoint]
  have hout := squareFaceLine_eval i (deformLine φ l)
    ((squareFaceCoordinates i).symm (H (squareFaceSectorHomeomorph R i p)).val)
  rw [squareFaceLine_deform] at hout
  simp only [(squareFaceCoordinates i).apply_symm_apply] at hout
  have hin := squareFaceLine_eval i l p.val
  calc
    Real.sign ((deformLine φ l).eval
        (Complex.equivRealProdCLM.symm ((squareFaceCoordinates i).symm (H (squareFaceSectorHomeomorph R i p)).val))) =
        Real.sign ((deformLine φ (squareFaceLine i l)).eval
          (Complex.equivRealProdCLM.symm (H (squareFaceSectorHomeomorph R i p)).val)) := by
            exact congrArg Real.sign hout
    _ = Real.sign ((squareFaceLine i l).eval (Complex.equivRealProdCLM.symm (squareFaceSectorHomeomorph R i p).val)) := hs
    _ = Real.sign (l.eval (Complex.equivRealProdCLM.symm p.val)) := (congrArg Real.sign hin).symm

private theorem equivRealProdCLM_mem (R : ℚ) (z : Plane) :
    z ∈ squareExterior R ↔ Complex.equivRealProdCLM z ∈ ExteriorFourFaces.exterior R := by
  have hcoords : Complex.equivRealProdCLM z = (z.re, z.im) := by
    simp only [Complex.equivRealProdCLM_apply]
  rw [hcoords]
  rfl

/-- The usual complex/product linear equivalence restricts to the actual closed
square exteriors; this is the coordinate conversion needed after the product
four-face gluing. -/
private def planeExteriorHomeomorph (R : ℚ) :
    {z : Plane // z ∈ squareExterior R} ≃ₜ {p : ℝ × ℝ // p ∈ ExteriorFourFaces.exterior R} :=
  ((Complex.equivRealProdCLM.toHomeomorph).image (squareExterior R)).trans
    (Homeomorph.setCongr (by
      apply Set.ext
      intro p
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact (equivRealProdCLM_mem R z).mp hz
      · intro hp
        refine ⟨Complex.equivRealProdCLM.symm p, ?_, ?_⟩
        · exact (equivRealProdCLM_mem R _).mpr (by simpa using hp)
        · exact Complex.equivRealProdCLM.apply_symm_apply p))

private theorem planeExteriorHomeomorph_apply (R : ℚ)
    (z : {z : Plane // z ∈ squareExterior R}) :
    (planeExteriorHomeomorph R z).val = Complex.equivRealProdCLM z.val := rfl

private theorem actualGraphFamily_adjacentFaces
    (R : ℚ) (hR : 0 < R) (L : List RationalLine)
    (hcorners : (-1,0) ∈ rightGraphSet L ∧ (1,0) ∈ rightGraphSet L)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (n : ℕ) (hn : 0 < n) (a b : Fin (n+1) → ℝ)
    (hfirst : ∀ r, ExteriorFaceCharts.affineGraph a b 0 r = -r)
    (hlast : ∀ r, ExteriorFaceCharts.affineGraph a b ⟨n,by omega⟩ r = r)
    (hgap : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
      0 < ExteriorFaceCharts.affineGraphGap a b i r)
    (hforward : ∀ j : Fin (n+1), ∃ g ∈
      ExteriorFaceCharts.outgoingRationalGraphs (rightGraphSet L) R,
      a j = (g.1 : ℝ) ∧ b j = g.2)
    (hlookup : ∀ g ∈ rightGraphSet L,
      -(R : ℝ) < ExteriorFaceCharts.rationalGraphValue R g →
      ExteriorFaceCharts.rationalGraphValue R g < R →
      ∃ j : Fin (n+1), a j = (g.1 : ℝ) ∧ b j = g.2) :
    ∀ i : Fin n, ∃ C ∈ signedCodes L,
      (∀ k ∈ C, k.eval (rightPoint R ((a i.castSucc * R + b i.castSucc +
        a i.succ * R + b i.succ)/2)) < 0) ∧
      clippedRightFace R C = segment ℝ
        (rightPoint R (a i.castSucc * R + b i.castSucc))
        (rightPoint R (a i.succ * R + b i.succ)) ∧
      ∃ δ : ℝ, 0 < δ ∧ δ < (R : ℝ) ∧
        rightPoint ((R : ℝ)-δ) ((a i.castSucc * R + b i.castSucc +
          a i.succ * R + b i.succ)/2) ∈ openCell (realSquareLines R ++ C) := by
  classical
  have hout : ExteriorFaceCharts.outgoingRationalGraphs (rightGraphSet L) R ⊆
      rightGraphSet L := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact (Finset.mem_filter.mp hg).1
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact hcorners.1
      · exact hcorners.2
  have hlabels : ∀ j : Fin (n+1), ∃ l ∈ L,
      (l.normal.y : ℝ) ≠ 0 ∧ -((l.normal.x : ℝ)/(l.normal.y : ℝ)) = a j ∧
      l.offset/(l.normal.y : ℝ) = b j := by
    intro j
    obtain ⟨g,hg,ha,hb⟩ := hforward j
    have hg' := hout hg
    unfold rightGraphSet at hg'
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp hg'
    obtain ⟨hl,hly⟩ := Finset.mem_filter.mp hl
    refine ⟨l,List.mem_toFinset.mp hl,by exact_mod_cast hly,?_,hb.symm⟩
    simpa only [rightGraph, Rat.cast_div, Rat.cast_neg, neg_div] using ha.symm
  have hrootLookup : ∀ l ∈ L, (l.normal.y : ℝ) ≠ 0 →
      -(R : ℝ) < rightGraphValue l R → rightGraphValue l R < R →
      ∃ j : Fin (n+1), rightGraphValue l R = a j * R + b j := by
    intro l hl hly hlo hhi
    have hlyQ : l.normal.y ≠ 0 := by exact_mod_cast hly
    have hg : rightGraph l ∈ rightGraphSet L := by
      unfold rightGraphSet
      exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr
        ⟨List.mem_toFinset.mpr hl,hlyQ⟩,rfl⟩
    obtain ⟨j,ha,hb⟩ := hlookup (rightGraph l) hg
      (by simpa only [ExteriorFaceCharts.rationalGraphValue,rightGraph,rightGraphValue,
        Rat.cast_div,Rat.cast_neg,neg_div] using hlo)
      (by simpa only [ExteriorFaceCharts.rationalGraphValue,rightGraph,rightGraphValue,
        Rat.cast_div,Rat.cast_neg,neg_div] using hhi)
    refine ⟨j,?_⟩
    rw [ha,hb]
    simp only [rightGraphValue,rightGraph,Rat.cast_div,Rat.cast_neg,neg_div]
  have hcorner := hcorners.2
  unfold rightGraphSet at hcorner
  obtain ⟨m,hm,hmgraph⟩ := Finset.mem_image.mp hcorner
  obtain ⟨hm,hmy⟩ := Finset.mem_filter.mp hm
  have hvertical : ∀ l ∈ L, (l.normal.y : ℝ) = 0 →
      ∀ y, -(R : ℝ) ≤ y → y ≤ R → l.eval (rightPoint R y) ≠ 0 := by
    intro l hl hly y _ _ hz
    have hlyQ : l.normal.y = 0 := by exact_mod_cast hly
    have hlx : l.normal.x ≠ 0 := l.normal.nonzero.resolve_right (not_not_intro hlyQ)
    have hx : (l.normal.x : ℝ) ≠ 0 := by exact_mod_cast hlx
    have ht := vertical_root_before_radius L.toFinset R
      (fun l hl m hm => hinter l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm))
      l m (List.mem_toFinset.mpr hl) hm hlyQ hmy hmgraph
    have heq : (R : ℝ) = l.offset / (l.normal.x : ℝ) := by
      apply (eq_div_iff hx).mpr
      have hzero : (l.normal.x : ℝ)*(R : ℝ)-l.offset = 0 := by
        simpa [lineEval_rightPoint,hly] using hz
      nlinarith
    exact (ne_of_lt ht) heq.symm
  exact adjacent_right_faces_of_sorted_family R n hn L a b
    (by exact_mod_cast hR) (hfirst R) (hlast R)
    (ExteriorFaceCharts.affineGraph_strictMono_on_ray R R a b le_rfl
      (fun i hr => hgap i R hr)) hlabels hrootLookup hvertical

private structure ExteriorFaceFamily (R : ℚ) (L : List RationalLine) where
  n : ℕ
  hn : 0 < n
  a : Fin (n+1) → ℝ
  b : Fin (n+1) → ℝ
  first : ∀ r, ExteriorFaceCharts.affineGraph a b 0 r = -r
  last : ∀ r, ExteriorFaceCharts.affineGraph a b (Fin.last n) r = r
  gap : ∀ i : Fin n, ∀ r, (R : ℝ) ≤ r →
    0 < ExteriorFaceCharts.affineGraphGap a b i r
  labels : ∀ j : Fin (n+1), ∃ g ∈ rightGraphSet L,
    a j = (g.1 : ℝ) ∧ b j = g.2
  cell : Fin n → List RationalLine
  cell_mem : ∀ i, cell i ∈ signedCodes L
  face : ∀ i, clippedRightFace R (cell i) = segment ℝ
    (rightPoint R (a i.castSucc * R + b i.castSucc))
    (rightPoint R (a i.succ * R + b i.succ))
  strict : ∀ i, (openCell (realSquareLines R ++ cell i)).Nonempty

private structure ExteriorFaceMap {R : ℚ} {L : List RationalLine}
    (D : ExteriorFaceFamily R L) (φ : ℝ →ₗ[ℚ] ℚ) where
  b' : Fin (D.n+1) → ℝ
  first : ∀ r, ExteriorFaceCharts.affineGraph D.a b' 0 r = -r
  last : ∀ r, ExteriorFaceCharts.affineGraph D.a b' (Fin.last D.n) r = r
  gap : ∀ i : Fin D.n, ∀ r, (R : ℝ) ≤ r →
    0 < ExteriorFaceCharts.affineGraphGap D.a b' i r
  H : ExteriorFaceCharts.faceSector (R : ℝ) ≃ₜ ExteriorFaceCharts.faceSector (R : ℝ)
  radius : ∀ p, (H p).val.1 = p.val.1
  piece : ∀ i (p : ExteriorFaceCharts.faceSector (R : ℝ))
    (_hp : p ∈ ExteriorFaceCharts.facePiece (R : ℝ)
      (ExteriorFaceCharts.affineGraph D.a D.b) i),
    (H p).val = ExteriorFaceCharts.stripChart (D.a i.castSucc) (D.b i.castSucc)
      (D.a i.succ) (D.b i.succ) (b' i.castSucc) (b' i.succ) p.val
  graph_sign : ∀ g ∈ rightGraphSet L, ∀ p : ExteriorFaceCharts.faceSector (R : ℝ),
    Real.sign ((H p).val.2 -
      ExteriorFaceCharts.targetRationalGraphValue φ g (H p).val.1) =
    Real.sign (p.val.2 - ((g.1 : ℝ)*p.val.1+g.2))

/-- Construct the source subdivision, its actual incident clipped chambers,
and the corresponding finite-test strip homeomorphisms from the given labels. -/
private theorem finiteExteriorFace_family
    (R : ℚ) (hR : 0 < R) (L : List RationalLine)
    (hcorners : (-1,0) ∈ rightGraphSet L ∧ (1,0) ∈ rightGraphSet L)
    (hinter : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ)) :
    ∃ D : ExteriorFaceFamily R L, ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        Nonempty (ExteriorFaceMap D φ) := by
  classical
  let A := rightGraphSet L
  have hsub : A ∪ {(-1,0),(1,0)} ⊆ A := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact hg
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact hcorners.1
      · exact hcorners.2
  have hinc : ∀ g ∈ A ∪ {(-1,0),(1,0)}, ∀ h ∈ A ∪ {(-1,0),(1,0)},
      g.1 ≠ h.1 → ExteriorFaceCharts.rationalGraphIntersection g h < R := by
    intro g hg h hh hne
    have hs := rightGraphSet_incidence L R hinter g (hsub hg) h (hsub hh) hne
    have heq : ExteriorFaceCharts.rationalGraphIntersection g h =
        (h.2-g.2)/((g.1 : ℝ)-(h.1 : ℝ)) := by
      unfold ExteriorFaceCharts.rationalGraphIntersection
      rw [show g.2-h.2 = -(h.2-g.2) by ring,
        show (h.1 : ℝ)-(g.1 : ℝ) = -((g.1 : ℝ)-(h.1 : ℝ)) by ring,
        neg_div_neg_eq]
    rw [heq]
    exact hs
  obtain ⟨n,hn,a,b,hfirst,hlast,_,hgap,hforward,hlookup,F,ε,hε,htransport⟩ :=
    ExteriorFaceCharts.outgoingRationalGraphs_actual_exterior_transport A R hR hinc
  have hfaces := actualGraphFamily_adjacentFaces R hR L hcorners hinter n hn a b
    hfirst hlast hgap hforward hlookup
  choose C hC hmid hface δ hδ hδR hstrict using hfaces
  have hout : ExteriorFaceCharts.outgoingRationalGraphs A R ⊆ A := by
    intro g hg
    rcases Finset.mem_union.mp hg with hg | hg
    · exact (Finset.mem_filter.mp hg).1
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hg
      rcases hg with rfl | rfl
      · exact hcorners.1
      · exact hcorners.2
  let D : ExteriorFaceFamily R L :=
    { n := n, hn := hn, a := a, b := b, first := hfirst, last := hlast,
      gap := hgap, labels := fun j => by
        obtain ⟨g,hg,ha,hb⟩ := hforward j
        exact ⟨g,hout hg,ha,hb⟩,
      cell := C, cell_mem := hC, face := hface,
      strict := fun i => ⟨_,hstrict i⟩ }
  refine ⟨D,F,ε,hε,?_⟩
  intro φ hφ
  obtain ⟨b',hfirst',hlast',hgap',H,hradius,hpiece,hsign⟩ := htransport φ hφ
  exact ⟨{ b' := b'
           first := hfirst'
           last := hlast'
           gap := hgap'
           H := H
           radius := hradius
           piece := hpiece
           graph_sign := hsign }⟩

private theorem ExteriorFaceMap_lineSigns_and_corners {R : ℚ} {L : List RationalLine}
    (D : ExteriorFaceFamily R L) (φ : ℝ →ₗ[ℚ] ℚ) (E : ExteriorFaceMap D φ)
    (hcorners : (-1,0) ∈ rightGraphSet L ∧ (1,0) ∈ rightGraphSet L)
    (hsource : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (htarget : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < (R : ℝ)) :
    (∀ l ∈ L, ∀ p : ExteriorFaceCharts.faceSector (R : ℝ),
      Real.sign ((deformLine φ l).eval (exteriorPairPoint (E.H p).val)) =
        Real.sign (l.eval (exteriorPairPoint p.val))) ∧
    (∀ p : ExteriorFaceCharts.faceSector (R : ℝ),
      p.val.2 = p.val.1 ∨ p.val.2 = -p.val.1 → E.H p = p) := by
  classical
  have hminus := hcorners.1
  have hplus := hcorners.2
  unfold rightGraphSet at hminus hplus
  obtain ⟨mminus,hmminus,hminus⟩ := Finset.mem_image.mp hminus
  obtain ⟨mplus,hmplus,hplus⟩ := Finset.mem_image.mp hplus
  obtain ⟨hmminus,hmyminus⟩ := Finset.mem_filter.mp hmminus
  obtain ⟨hmplus,hmyplus⟩ := Finset.mem_filter.mp hmplus
  have hgraph : ∀ l ∈ L.toFinset, ∀ _hly : l.normal.y ≠ 0,
      ∀ p : ExteriorFaceCharts.faceSector (R : ℝ),
      Real.sign ((E.H p).val.2-(rightGraph l).1*(E.H p).val.1-
        (φ (rightGraph l).2 : ℝ)) =
      Real.sign (p.val.2-(rightGraph l).1*p.val.1-(rightGraph l).2) := by
    intro l hl hly p
    have hg : rightGraph l ∈ rightGraphSet L := by
      unfold rightGraphSet
      exact Finset.mem_image.mpr ⟨l,Finset.mem_filter.mpr ⟨hl,hly⟩,rfl⟩
    simpa only [ExteriorFaceCharts.targetRationalGraphValue,sub_add_eq_sub_sub] using
      E.graph_sign (rightGraph l) hg p
  constructor
  · intro l hl p
    exact pairSectorHomeomorph_preserves_line_signs φ L.toFinset R
      (fun l hl m hm => hsource l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm))
      (fun l hl m hm => htarget l (List.mem_toFinset.mp hl) m (List.mem_toFinset.mp hm))
      mplus hmplus hmyplus hplus E.H E.radius hgraph l (List.mem_toFinset.mpr hl) p
  · exact pairSectorHomeomorph_fixes_corner_rays φ L.toFinset R E.H E.radius hgraph
      mminus mplus hmminus hmplus hmyminus hmyplus hminus hplus

private theorem ExteriorFaceMap_anchorValue {R : ℚ} {L : List RationalLine}
    (D : ExteriorFaceFamily R L) (φ : ℝ →ₗ[ℚ] ℚ) (E : ExteriorFaceMap D φ)
    (j : Fin (D.n+1)) (p : ExteriorFaceCharts.faceSector (R : ℝ))
    (hp : p.val = ((R : ℝ),D.a j*R+D.b j)) :
    (E.H p).val = ((R : ℝ),D.a j*R+(φ (D.b j) : ℝ)) := by
  obtain ⟨g,hg,ha,hb⟩ := D.labels j
  have hs := E.graph_sign g hg p
  have hz : Real.sign (p.val.2-((g.1 : ℝ)*p.val.1+g.2)) = 0 := by
    rw [hp,ha,hb]
    simp
  have ht := Real.sign_eq_zero_iff.mp (hs.trans hz)
  have hr : (E.H p).val.1 = (R : ℝ) := (E.radius p).trans (congrArg Prod.fst hp)
  apply Prod.ext
  · exact hr
  · rw [ExteriorFaceCharts.targetRationalGraphValue,hr] at ht
    rw [ha,hb]
    linarith

private theorem deformPoint_rightPoint_rationalSlope
    (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1) (R s : ℚ) (b : ℝ) :
    deformPoint φ (rightPoint R ((s : ℝ)*R+b)) =
      rightPoint R ((s : ℝ)*R+(φ b : ℝ)) := by
  have hmap := φ.map_smul s (R : ℝ)
  have harg : s • (R : ℝ) = (s : ℝ)*(R : ℝ) := by simp [Rat.smul_def]
  rw [harg,normalized_map_rat φ hφ R] at hmap
  apply Complex.ext
  · simp [deformPoint,rightPoint,normalized_map_rat φ hφ R]
  · simp [deformPoint,rightPoint,map_add,hmap]

private theorem squareFaceLine_negate (i : Fin 4) (l : RationalLine) :
    squareFaceLine i (negateLine l) = negateLine (squareFaceLine i l) := by
  fin_cases i <;> rfl

private theorem signedCodes_map_squareFaceLine (i : Fin 4) (L : List RationalLine) :
    (signedCodes L).map (List.map (squareFaceLine i)) =
      signedCodes (L.map (squareFaceLine i)) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
      simp only [signedCodes, List.map_append, List.map_map]
      have hpos : List.map (fun C => List.map (squareFaceLine i) (l :: C))
          (signedCodes L) =
          List.map (fun C => squareFaceLine i l :: C)
            (signedCodes (L.map (squareFaceLine i))) := by
        rw [← ih]
        simp only [List.map_map, Function.comp_def, List.map_cons]
      have hneg : List.map (fun C => List.map (squareFaceLine i) (negateLine l :: C))
          (signedCodes L) =
          List.map (fun C => negateLine (squareFaceLine i l) :: C)
            (signedCodes (L.map (squareFaceLine i))) := by
        rw [← ih]
        simp only [List.map_map, Function.comp_def, List.map_cons, squareFaceLine_negate]
      have hpos' : List.map (List.map (squareFaceLine i) ∘ fun C => l :: C)
          (signedCodes L) =
          List.map (fun C => squareFaceLine i l :: C)
            (signedCodes (L.map (squareFaceLine i))) := by
        simpa only [Function.comp_def] using hpos
      have hneg' : List.map (List.map (squareFaceLine i) ∘ fun C => negateLine l :: C)
          (signedCodes L) =
          List.map (fun C => negateLine (squareFaceLine i l) :: C)
            (signedCodes (L.map (squareFaceLine i))) := by
        simpa only [Function.comp_def] using hneg
      rw [hpos', hneg']
      rfl

private def squareFaceChart (i : Fin 4) (z : Plane) : Plane :=
  Complex.equivRealProdCLM.symm
    (squareFaceCoordinates i (Complex.equivRealProdCLM z))

private theorem squareFaceLine_eval_chart (i : Fin 4) (l : RationalLine) (z : Plane) :
    l.eval z = (squareFaceLine i l).eval (squareFaceChart i z) := by
  calc
    l.eval z = l.eval (Complex.equivRealProdCLM.symm
        (Complex.equivRealProdCLM z)) := by rw [Complex.equivRealProdCLM.symm_apply_apply]
    _ = (squareFaceLine i l).eval (squareFaceChart i z) := by
      exact squareFaceLine_eval i l (Complex.equivRealProdCLM z)

private theorem closedCell_squareFace_iff (i : Fin 4) (cell : List RationalLine)
    (z : Plane) :
    z ∈ closedCell cell ↔
      squareFaceChart i z ∈ closedCell (cell.map (squareFaceLine i)) := by
  simp only [closedCell, Set.mem_ofPred_eq]
  constructor
  · intro hz l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have h := hz k hk
    rw [squareFaceLine_eval_chart] at h
    exact h
  · intro hz l hl
    have h := hz (squareFaceLine i l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    rw [← squareFaceLine_eval_chart] at h
    simpa using h

private theorem openCell_squareFace_iff (i : Fin 4) (cell : List RationalLine)
    (z : Plane) :
    z ∈ openCell cell ↔
      squareFaceChart i z ∈ openCell (cell.map (squareFaceLine i)) := by
  simp only [openCell, Set.mem_ofPred_eq]
  constructor
  · intro hz l hl
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hl
    have h := hz k hk
    rw [squareFaceLine_eval_chart] at h
    exact h
  · intro hz l hl
    have h := hz (squareFaceLine i l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
    rw [← squareFaceLine_eval_chart] at h
    simpa using h

private theorem squareFaceChart_right_coordinate (i : Fin 4) (z : Plane) :
    (squareFaceChart i z).re =
      (squareFaceCoordinates i (Complex.equivRealProdCLM z)).1 := by
  change (Complex.equivRealProdCLM.symm
    (squareFaceCoordinates i (Complex.equivRealProdCLM z))).re = _
  simp [squareFaceCoordinates]

private theorem squareFaceChart_imag_coordinate (i : Fin 4) (z : Plane) :
    (squareFaceChart i z).im =
      (squareFaceCoordinates i (Complex.equivRealProdCLM z)).2 := by
  change (Complex.equivRealProdCLM.symm
    (squareFaceCoordinates i (Complex.equivRealProdCLM z))).im = _
  simp [squareFaceCoordinates]

private theorem squareFaceLinearCoordinates_apply (i : Fin 4) (p : ℝ × ℝ) :
    squareFaceLinearCoordinates i p = squareFaceCoordinates i p := by
  fin_cases i <;> rfl

private def squareFacePlaneEquiv (i : Fin 4) : Plane ≃L[ℝ] Plane :=
  (squareFacePlaneCoordinates i).trans Complex.equivRealProdCLM.symm

private theorem squareFaceChart_eq_equiv (i : Fin 4) (z : Plane) :
    squareFaceChart i z = squareFacePlaneEquiv i z := by
  simp [squareFaceChart, squareFacePlaneEquiv, squareFacePlaneCoordinates,
    squareFaceLinearCoordinates_apply]

private theorem squareFacePlaneEquiv_deform (i : Fin 4) (φ : ℝ →ₗ[ℚ] ℚ)
    (z : Plane) :
    squareFacePlaneEquiv i (deformPoint φ z) =
      deformPoint φ (squareFacePlaneEquiv i z) := by
  fin_cases i <;> apply Complex.ext <;>
    simp [squareFacePlaneEquiv, squareFacePlaneCoordinates, squareFaceLinearCoordinates,
      deformPoint, Complex.equivRealProdCLM_symm_apply]

private theorem mem_closedCell_realSquareLines_flat (R : ℝ) (z : Plane) :
    z ∈ closedCell (realSquareLines R) ↔
      -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R := by
  simp only [closedCell, realSquareLines, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RationalLine.eval, normalEval]
  norm_num
  constructor <;> intro h
  · rcases h with ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rcases h with ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem mem_openCell_realSquareLines (R : ℝ) (z : Plane) :
    z ∈ openCell (realSquareLines R) ↔
      -R < z.re ∧ z.re < R ∧ -R < z.im ∧ z.im < R := by
  simp only [openCell, realSquareLines, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, RationalLine.eval, normalEval]
  norm_num
  constructor <;> intro h
  · rcases h with ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rcases h with ⟨h₁,h₂,h₃,h₄⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem squareFaceChart_square (R : ℝ) (i : Fin 4) (z : Plane) :
    ( -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R) ↔
    ( -R ≤ (squareFaceChart i z).re ∧ (squareFaceChart i z).re ≤ R ∧
      -R ≤ (squareFaceChart i z).im ∧ (squareFaceChart i z).im ≤ R) := by
  have hre := squareFaceChart_right_coordinate i z
  have him := squareFaceChart_imag_coordinate i z
  rw [hre, him]
  fin_cases i <;>
    simp [squareFaceCoordinates] <;>
      constructor <;> intro h <;>
        rcases h with ⟨h₁,h₂,h₃,h₄⟩ <;>
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem squareFaceChart_openSquare (R : ℝ) (i : Fin 4) (z : Plane) :
    (-R < z.re ∧ z.re < R ∧ -R < z.im ∧ z.im < R) ↔
    (-R < (squareFaceChart i z).re ∧ (squareFaceChart i z).re < R ∧
      -R < (squareFaceChart i z).im ∧ (squareFaceChart i z).im < R) := by
  have hre := squareFaceChart_right_coordinate i z
  have him := squareFaceChart_imag_coordinate i z
  rw [hre, him]
  fin_cases i <;>
    simp [squareFaceCoordinates] <;>
      constructor <;> intro h <;>
        rcases h with ⟨h₁,h₂,h₃,h₄⟩ <;>
          exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private theorem closedCell_clip_squareFace_iff (i : Fin 4) (R : ℝ)
    (cell : List RationalLine) (z : Plane) :
    z ∈ closedCell (realSquareLines R ++ cell) ↔
      squareFaceChart i z ∈
        closedCell (realSquareLines R ++ cell.map (squareFaceLine i)) := by
  rw [closedCell_append, closedCell_append]
  constructor
  · rintro ⟨hzbox,hzcell⟩
    refine ⟨(mem_closedCell_realSquareLines_flat R _).2 ?_,
      (closedCell_squareFace_iff i cell z).mp hzcell⟩
    exact (squareFaceChart_square R i z).mp
      ((mem_closedCell_realSquareLines_flat R z).mp hzbox)
  · rintro ⟨hzbox,hzcell⟩
    refine ⟨(mem_closedCell_realSquareLines_flat R z).2 ?_,
      (closedCell_squareFace_iff i cell z).mpr hzcell⟩
    exact (squareFaceChart_square R i z).mpr
      ((mem_closedCell_realSquareLines_flat R _).mp hzbox)

private theorem openCell_clip_squareFace_iff (i : Fin 4) (R : ℝ)
    (cell : List RationalLine) (z : Plane) :
    z ∈ openCell (realSquareLines R ++ cell) ↔
      squareFaceChart i z ∈
        openCell (realSquareLines R ++ cell.map (squareFaceLine i)) := by
  rw [openCell_append, openCell_append]
  constructor
  · intro hz
    refine ⟨?_, ?_⟩
    · exact (mem_openCell_realSquareLines R _).2
        ((squareFaceChart_openSquare R i z).mp
          ((mem_openCell_realSquareLines R z).mp hz.1))
    · exact (openCell_squareFace_iff i cell z).mp hz.2
  · rintro ⟨hzbox,hzcell⟩
    exact ⟨(mem_openCell_realSquareLines R z).2
      ((squareFaceChart_openSquare R i z).mpr
        ((mem_openCell_realSquareLines R _).mp hzbox)),
      (openCell_squareFace_iff i cell z).mpr hzcell⟩

private def squarePhysicalFaceLine (i : Fin 4) (R : ℝ) : RationalLine :=
  match i.val with
  | 0 => ⟨⟨1, 0, by norm_num⟩, R⟩
  | 1 => ⟨⟨0, 1, by norm_num⟩, R⟩
  | 2 => ⟨⟨-1, 0, by norm_num⟩, R⟩
  | 3 => ⟨⟨0, -1, by norm_num⟩, R⟩
  | _ => ⟨⟨1, 0, by norm_num⟩, R⟩

private def squareRightLine (R : ℝ) : RationalLine :=
  ⟨⟨1, 0, by norm_num⟩, R⟩

private theorem squareFaceLine_physical (i : Fin 4) (R : ℝ) :
    squareFaceLine i (squarePhysicalFaceLine i R) = squareRightLine R := by
  fin_cases i <;> rfl

private theorem squarePhysicalFaceLine_eval_zero_iff (i : Fin 4) (R : ℝ) (z : Plane) :
    (squarePhysicalFaceLine i R).eval z = 0 ↔
      (squareFaceChart i z).re = R := by
  have heval := squareFaceLine_eval_chart i (squarePhysicalFaceLine i R) z
  rw [squareFaceLine_physical] at heval
  simp [squareRightLine, RationalLine.eval, normalEval] at heval
  change (((squarePhysicalFaceLine i R).normal.x : ℝ) * z.re +
    ((squarePhysicalFaceLine i R).normal.y : ℝ) * z.im -
    (squarePhysicalFaceLine i R).offset = 0) ↔ (squareFaceChart i z).re = R
  calc
    _ ↔ (squareFaceChart i z).re - R = 0 := by rw [heval]
    _ ↔ (squareFaceChart i z).re = R := by constructor <;> intro h <;> linarith

private theorem closedCell_physicalFace_preimage (i : Fin 4) (R : ℝ)
    (cell : List RationalLine) (z : Plane) :
    z ∈ closedCell (realSquareLines R ++ cell) ∧
        (squarePhysicalFaceLine i R).eval z = 0 ↔
      squareFaceChart i z ∈ clippedRightFace R (cell.map (squareFaceLine i)) := by
  rw [clippedRightFace, closedCell_clip_squareFace_iff,
    squarePhysicalFaceLine_eval_zero_iff]
  rfl

private theorem squareLines_real (R : ℚ) : squareLines R = realSquareLines (R : ℝ) := rfl

private theorem squarePhysicalFaceLine_mem_squareLines (i : Fin 4) (R : ℚ) :
    squarePhysicalFaceLine i (R : ℝ) ∈ squareLines R := by
  fin_cases i <;> simp [squarePhysicalFaceLine, squareLines, realSquareLines]

private theorem squareCode_source_of_rotated (i : Fin 4) (L : List RationalLine)
    (Crot : List RationalLine) (hrot : Crot ∈ signedCodes (L.map (squareFaceLine i))) :
    ∃ C ∈ signedCodes L, C.map (squareFaceLine i) = Crot := by
  have hmap : Crot ∈ (signedCodes L).map (List.map (squareFaceLine i)) := by
    rw [signedCodes_map_squareFaceLine]
    exact hrot
  obtain ⟨C,hC,hEq⟩ := List.mem_map.mp hmap
  exact ⟨C,hC,hEq⟩

/-- An adjacent maximal right-face segment in a chart pulls back to the exact
physical square-face segment of an actual full-square code. -/
private theorem rotated_adjacent_face_pulls_back
    (i : Fin 4) (R : ℚ) (L Crot : List RationalLine) (u v : ℝ)
    (hrot : Crot ∈ signedCodes (L.map (squareFaceLine i)))
    (hstrict : ∃ z, z ∈ openCell (realSquareLines (R : ℝ) ++ Crot))
    (hface : clippedRightFace (R : ℝ) Crot =
      segment ℝ (rightPoint (R : ℝ) u) (rightPoint (R : ℝ) v)) :
    ∃ C ∈ fullSquareCodes R L,
      closedCell C ∩ {z | (squarePhysicalFaceLine i (R : ℝ)).eval z = 0} =
      segment ℝ
          ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) u))
          ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) v)) := by
  classical
  obtain ⟨cell,hcell,hcellMap⟩ := squareCode_source_of_rotated i L Crot hrot
  obtain ⟨zt,hzt⟩ := hstrict
  let z := (squareFacePlaneEquiv i).symm zt
  have hchart : squareFaceChart i z = zt := by
    rw [squareFaceChart_eq_equiv]
    simp [z]
  have hsourceStrict : z ∈ openCell (squareLines R ++ cell) := by
    rw [squareLines_real]
    apply (openCell_clip_squareFace_iff i (R : ℝ) cell z).mpr
    simpa [hchart, hcellMap] using hzt
  have hmemFull : squareLines R ++ cell ∈ fullSquareCodes R L := by
    unfold fullSquareCodes
    apply List.mem_map.mpr
    refine ⟨cell, ?_, rfl⟩
    apply List.mem_filter.mpr
    constructor
    · exact hcell
    · apply decide_eq_true
      exact ⟨z,hsourceStrict⟩
  refine ⟨squareLines R ++ cell,hmemFull,?_⟩
  ext w
  change (w ∈ closedCell (squareLines R ++ cell) ∧
      (squarePhysicalFaceLine i (R : ℝ)).eval w = 0) ↔
    w ∈ segment ℝ ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) u))
      ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) v))
  have hfaceImage : (squareFacePlaneEquiv i).symm ''
      segment ℝ (rightPoint (R : ℝ) u) (rightPoint (R : ℝ) v) =
      segment ℝ ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) u))
        ((squareFacePlaneEquiv i).symm (rightPoint (R : ℝ) v)) := by
    exact image_segment ℝ (squareFacePlaneEquiv i).symm.toAffineMap _ _
  constructor
  · intro hw
    have htarget := (closedCell_physicalFace_preimage i (R : ℝ) cell w).mp hw
    rw [hcellMap] at htarget
    rw [hface] at htarget
    have himage : (squareFacePlaneEquiv i).symm ((squareFacePlaneEquiv i) w) ∈
        (squareFacePlaneEquiv i).symm ''
          segment ℝ (rightPoint (R : ℝ) u) (rightPoint (R : ℝ) v) :=
      Set.mem_image_of_mem _ (by simpa [squareFaceChart_eq_equiv] using htarget)
    simpa [hfaceImage] using himage
  · intro hw
    have himage : w ∈ (squareFacePlaneEquiv i).symm ''
        segment ℝ (rightPoint (R : ℝ) u) (rightPoint (R : ℝ) v) := by
      simpa [hfaceImage] using hw
    obtain ⟨zt',hzt',hwEq⟩ := (Set.mem_image _ _ _).mp himage
    have hwChart : squareFaceChart i w = zt' := by
      rw [squareFaceChart_eq_equiv]
      simpa using (congrArg (squareFacePlaneEquiv i) hwEq).symm
    have htarget : squareFaceChart i w ∈
        clippedRightFace (R : ℝ) (cell.map (squareFaceLine i)) := by
      rw [hcellMap, hface]
      exact hwChart ▸ hzt'
    exact (closedCell_physicalFace_preimage i (R : ℝ) cell w).mpr htarget

private theorem squareFacePlaneCoordinates_deform
    (i : Fin 4) (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane) :
    squareFacePlaneCoordinates i (deformPoint φ z) =
      (((φ (squareFacePlaneCoordinates i z).1 : ℝ),
        (φ (squareFacePlaneCoordinates i z).2 : ℝ))) := by
  fin_cases i <;> apply Prod.ext <;>
    simp [squareFacePlaneCoordinates, squareFaceLinearCoordinates, deformPoint, map_neg]


/-- The actual inverse-chart image of a rational affine graph anchor remains the
same first coordinate and has its affine endpoint evaluated under `φ`. -/
private theorem squareFace_rationalAnchor_deform
    (i : Fin 4) (φ : ℝ →ₗ[ℚ] ℚ) (hφ : φ 1 = 1)
    (R s : ℚ) (b : ℝ) :
    squareFacePlaneCoordinates i
      (deformPoint φ ((squareFacePlaneCoordinates i).symm
        ((R : ℝ), (s : ℝ) * (R : ℝ) + b))) =
      ((R : ℝ), (s : ℝ) * (R : ℝ) + (φ b : ℝ)) := by
  rw [squareFacePlaneCoordinates_deform]
  have hfirst : φ ((R : ℝ)) = R := normalized_map_rat φ hφ R
  have harg : (s : ℝ) * (R : ℝ) + b = ((s * R : ℚ) : ℝ) + b := by
    norm_num
  have hsecond : φ ((s : ℝ) * (R : ℝ) + b) = s * R + φ b := by
    rw [harg, map_add, normalized_map_rat φ hφ (s * R)]
  have hcoord : squareFacePlaneCoordinates i
      ((squareFacePlaneCoordinates i).symm ((R : ℝ), (s : ℝ) * (R : ℝ) + b)) =
      ((R : ℝ), (s : ℝ) * (R : ℝ) + b) :=
    (squareFacePlaneCoordinates i).apply_symm_apply _
  rw [hcoord]
  apply Prod.ext
  · change (φ (R : ℝ) : ℝ) = (R : ℝ)
    exact_mod_cast hfirst
  · change (φ ((s : ℝ) * (R : ℝ) + b) : ℝ) =
      (s : ℝ) * (R : ℝ) + (φ b : ℝ)
    exact_mod_cast hsecond

/-- Membership in a nondegenerate vertical segment is exactly membership of
the second coordinate in the corresponding closed interval. -/
private theorem vertical_segment_mem_iff
    (R y₀ y₁ y : ℝ) (hgap : y₀ < y₁) :
    (R, y) ∈ segment ℝ (R, y₀) (R, y₁) ↔ y₀ ≤ y ∧ y ≤ y₁ := by
  constructor
  · intro hp
    exact ⟨(ExteriorFaceCharts.segment_vertical_bounds R y₀ y₁ hgap (R, y) hp).2.1,
      (ExteriorFaceCharts.segment_vertical_bounds R y₀ y₁ hgap (R, y) hp).2.2⟩
  · rintro ⟨hy₀, hy₁⟩
    rw [segment_eq_image']
    let t := (y - y₀) / (y₁ - y₀)
    have hden : y₁ - y₀ ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hy₀) (le_of_lt (sub_pos.mpr hgap))
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one (sub_pos.mpr hgap)]
      linarith
    refine ⟨t, ⟨ht0, ht1⟩, ?_⟩
    apply Prod.ext
    · simp [t]
    · simp [smul_eq_mul, t]
      field_simp [hden]
      ring

/-- Any point on the vertical line with the segment's closed interval bounds
belongs to the actual segment, not merely to its supporting line. -/
private theorem vertical_segment_mem_of_bounds
    (R y₀ y₁ : ℝ) (hgap : y₀ < y₁) (p : ℝ × ℝ)
    (hpR : p.1 = R) (hlo : y₀ ≤ p.2) (hhi : p.2 ≤ y₁) :
    p ∈ segment ℝ (R, y₀) (R, y₁) := by
  have hp' : p = (R, p.2) := by apply Prod.ext <;> simp [hpR]
  rw [hp']
  exact (vertical_segment_mem_iff R y₀ y₁ p.2 hgap).2 ⟨hlo, hhi⟩

private def exteriorFaceAnchor {R : ℚ} {L : List RationalLine}
    (D : ExteriorFaceFamily R L) (j : Fin (D.n+1)) :
    ExteriorFaceCharts.faceSector (R : ℝ) := by
  have hm := ExteriorFaceCharts.affineGraph_strictMono_on_ray R R D.a D.b le_rfl
    (fun i hr => D.gap i R hr)
  have hlo := hm.monotone (Fin.zero_le j)
  have hjlast : j ≤ Fin.last D.n :=
    Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.isLt)
  have hhi := hm.monotone hjlast
  rw [D.first] at hlo
  rw [D.last] at hhi
  exact ⟨((R : ℝ),D.a j*R+D.b j),le_rfl,hlo,hhi⟩

private theorem ExteriorFaceMap_affineEdgeAgreement {R : ℚ} {L : List RationalLine}
    (D : ExteriorFaceFamily R L) (φ : ℝ →ₗ[ℚ] ℚ) (E : ExteriorFaceMap D φ)
    (j : Fin D.n) (f : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ))
    (hf₀ : f (exteriorFaceAnchor D j.castSucc).val =
      (E.H (exteriorFaceAnchor D j.castSucc)).val)
    (hf₁ : f (exteriorFaceAnchor D j.succ).val =
      (E.H (exteriorFaceAnchor D j.succ)).val)
    (p : ExteriorFaceCharts.faceSector (R : ℝ))
    (hp : p.val ∈ segment ℝ (exteriorFaceAnchor D j.castSucc).val
      (exteriorFaceAnchor D j.succ).val) : f p.val = (E.H p).val := by
  have hg := D.gap j R le_rfl
  have horder : D.a j.castSucc*(R : ℝ)+D.b j.castSucc <
      D.a j.succ*(R : ℝ)+D.b j.succ := by
    exact sub_pos.mp hg
  have hp₀ : exteriorFaceAnchor D j.castSucc ∈
      ExteriorFaceCharts.facePiece (R : ℝ)
        (ExteriorFaceCharts.affineGraph D.a D.b) j := by
    change (R : ℝ) ≤ R ∧ D.a j.castSucc*R+D.b j.castSucc ≤
      D.a j.castSucc*R+D.b j.castSucc ∧
      D.a j.castSucc*R+D.b j.castSucc ≤ D.a j.succ*R+D.b j.succ
    exact ⟨le_rfl,le_rfl,horder.le⟩
  have hp₁ : exteriorFaceAnchor D j.succ ∈
      ExteriorFaceCharts.facePiece (R : ℝ)
        (ExteriorFaceCharts.affineGraph D.a D.b) j := by
    change (R : ℝ) ≤ R ∧ D.a j.castSucc*R+D.b j.castSucc ≤
      D.a j.succ*R+D.b j.succ ∧
      D.a j.succ*R+D.b j.succ ≤ D.a j.succ*R+D.b j.succ
    exact ⟨le_rfl,horder.le,le_rfl⟩
  have h₀ := E.piece j (exteriorFaceAnchor D j.castSucc) hp₀
  have h₁ := E.piece j (exteriorFaceAnchor D j.succ) hp₁
  change _ = ExteriorFaceCharts.stripChart (D.a j.castSucc) (D.b j.castSucc)
    (D.a j.succ) (D.b j.succ) (E.b' j.castSucc) (E.b' j.succ)
    ((R : ℝ),ExteriorFaceCharts.lower (D.a j.castSucc) (D.b j.castSucc) R) at h₀
  change _ = ExteriorFaceCharts.stripChart (D.a j.castSucc) (D.b j.castSucc)
    (D.a j.succ) (D.b j.succ) (E.b' j.castSucc) (E.b' j.succ)
    ((R : ℝ),ExteriorFaceCharts.upper (D.a j.succ) (D.b j.succ) R) at h₁
  rw [ExteriorFaceCharts.stripChart_lower_anchor] at h₀
  rw [ExteriorFaceCharts.stripChart_upper_anchor (ne_of_gt hg)] at h₁
  have hb := ExteriorFaceCharts.segment_vertical_bounds R
    (D.a j.castSucc*R+D.b j.castSucc) (D.a j.succ*R+D.b j.succ) horder p.val hp
  have hpj : p ∈ ExteriorFaceCharts.facePiece (R : ℝ)
      (ExteriorFaceCharts.affineGraph D.a D.b) j := by
    change (R : ℝ) ≤ p.val.1 ∧ D.a j.castSucc*p.val.1+D.b j.castSucc ≤ p.val.2 ∧
      p.val.2 ≤ D.a j.succ*p.val.1+D.b j.succ
    rw [hb.1]
    exact ⟨le_rfl,hb.2.1,hb.2.2⟩
  have hf := ExteriorFaceCharts.affineMap_verticalSegment_value R
    (D.a j.castSucc*R+D.b j.castSucc) (D.a j.succ*R+D.b j.succ)
    (D.a j.castSucc*R+E.b' j.castSucc) (D.a j.succ*R+E.b' j.succ)
    horder f (hf₀.trans h₀) (hf₁.trans h₁) p.val hp
  rw [E.piece j p hpj]
  rw [hf]
  simp only [ExteriorFaceCharts.stripChart,ExteriorFaceCharts.gap,
    ExteriorFaceCharts.lower,ExteriorFaceCharts.upper,hb.1]

private theorem squareFacePlaneCoordinates_apply (i : Fin 4) (z : Plane) :
    squareFacePlaneCoordinates i z = squareFaceCoordinates i (z.re,z.im) := by
  simp [squareFacePlaneCoordinates, squareFaceLinearCoordinates_eq]

private theorem squareFaceCoordinates_max_abs (i : Fin 4) (p : ℝ × ℝ) :
    max |(squareFaceCoordinates i p).1| |(squareFaceCoordinates i p).2| =
      max |p.1| |p.2| := by
  fin_cases i <;> simp [squareFaceCoordinates, max_comm]

private theorem faceSector_max_eq_first {R : ℝ} (hR : 0 < R)
    {q : ℝ × ℝ} (hq : q ∈ ExteriorFaceCharts.faceSector R) :
    max |q.1| |q.2| = q.1 := by
  change R ≤ q.1 ∧ -q.1 ≤ q.2 ∧ q.2 ≤ q.1 at hq
  have hqpos : 0 < q.1 := lt_of_lt_of_le hR hq.1
  have habs : |q.2| ≤ q.1 := abs_le.mpr ⟨hq.2.1, hq.2.2⟩
  rw [abs_of_pos hqpos, max_eq_left habs]

/-- A point in the clipped box and in the indexed exterior face lies on the
corresponding physical square side after applying the actual face chart. -/
private theorem squareFacePlaneCoordinates_right_eq_of_box_face
    (R : ℝ) (i : Fin 4) (z : Plane)
    (hbox : -R ≤ z.re ∧ z.re ≤ R ∧ -R ≤ z.im ∧ z.im ≤ R)
    (hface : (z.re,z.im) ∈ ExteriorFourFaces.face R i) :
    (squareFacePlaneCoordinates i z).1 = R := by
  rw [squareFacePlaneCoordinates_apply]
  fin_cases i <;>
    simp [squareFaceCoordinates, ExteriorFourFaces.face] at hface ⊢ <;>
    rcases hbox with ⟨hxlo,hxhi,hylo,hyhi⟩ <;>
    rcases hface with ⟨houter,_,_⟩ <;> linarith

private theorem finiteExterior_arrangementHomeomorph
    (R : ℚ) (hR : 0 < R) (L : List RationalLine) (φ : ℝ →ₗ[ℚ] ℚ)
    (hdiagonal : ∀ l ∈ diagonalLines, l ∈ L)
    (hsource : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ))
    (htarget : ∀ l ∈ L, ∀ m ∈ L,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < (R : ℝ))
    (D : ∀ i : Fin 4, ExteriorFaceFamily R (L.map (squareFaceLine i)))
    (E : ∀ i : Fin 4, ExteriorFaceMap (D i) φ) :
    ∃ K : squareExterior R ≃ₜ squareExterior R,
      (∀ l ∈ L, ∀ x : squareExterior R,
        Real.sign ((deformLine φ l).eval (K x : Plane)) = Real.sign (l.eval x.val)) ∧
      (∀ i (x : squareExterior R)
        (hx : Complex.equivRealProdCLM x.val ∈ ExteriorFourFaces.face (R : ℝ) i),
        squareFacePlaneCoordinates i (K x : Plane) =
          ((E i).H (squareFaceSectorHomeomorph R i
            ⟨Complex.equivRealProdCLM x.val,hx⟩)).val) := by
  classical
  have htargetList : ∀ l ∈ L.map (deformLine φ), ∀ m ∈ L.map (deformLine φ),
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ) := by
    intro l hl m hm hd z hz hmz
    obtain ⟨l,hlSource,rfl⟩ := List.mem_map.mp hl
    obtain ⟨m,hmSource,rfl⟩ := List.mem_map.mp hm
    exact htarget l hlSource m hmSource hd z hz hmz
  have hchartTarget (i : Fin 4) : ∀ l ∈ L.map (squareFaceLine i),
      ∀ m ∈ L.map (squareFaceLine i),
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < (R : ℝ) := by
    have hc := squareFaceLines_intersections_enclosed (L.map (deformLine φ)) R
      htargetList i
    have hmap : (L.map (deformLine φ)).map (squareFaceLine i) =
        (L.map (squareFaceLine i)).map (deformLine φ) := by
      simp only [List.map_map]
      congr 1
      funext l
      exact squareFaceLine_deform i l φ
    rw [hmap] at hc
    intro l hl m hm hd z hz hmz
    exact hc (deformLine φ l) (List.mem_map.mpr ⟨l,hl,rfl⟩)
      (deformLine φ m) (List.mem_map.mpr ⟨m,hm,rfl⟩) hd z hz hmz
  have hsector (i : Fin 4) := ExteriorFaceMap_lineSigns_and_corners (D i) φ (E i)
    (squareFaceGraphSet_has_corners L hdiagonal i)
    (squareFaceLines_intersections_enclosed L R hsource i) (hchartTarget i)
  let H : ∀ i : Fin 4, ExteriorFourFaces.FacePoint (R : ℝ) i ≃ₜ
      ExteriorFourFaces.FacePoint (R : ℝ) i :=
    fun i => sectorHomeomorph_on_squareFace R i (E i).H
  have hfix : ∀ i (p : ExteriorFourFaces.FacePoint (R : ℝ) i),
      p.val ∈ ExteriorFourFaces.diagonalRays → H i p = p := by
    intro i p hp
    exact sectorHomeomorph_on_squareFace_fixes_diagonal R i (E i).H
      (hsector i).2 p hp
  have hfaceSign (i : Fin 4) (l : RationalLine) (hl : l ∈ L)
      (p : ExteriorFourFaces.FacePoint (R : ℝ) i) :
      Real.sign ((deformLine φ l).eval (Complex.equivRealProdCLM.symm (H i p).val)) =
        Real.sign (l.eval (Complex.equivRealProdCLM.symm p.val)) := by
    apply sectorHomeomorph_on_squareFace_preserves_line_signs φ L.toFinset R i (E i).H
      (fun l hl q => ?_) l (List.mem_toFinset.mpr hl) p
    have hs := (hsector i).1 (squareFaceLine i l)
      (List.mem_map.mpr ⟨l,List.mem_toFinset.mp hl,rfl⟩) q
    simpa [exteriorPairPoint,Complex.equivRealProdCLM_symm_apply] using hs
  let G := ExteriorFourFaces.fourFaceHomeomorph
    (show 0 < (R : ℝ) by exact_mod_cast hR) H hfix
  have hGlocal (i : Fin 4) (p : ExteriorFourFaces.ExteriorPoint (R : ℝ))
      (hp : p.val ∈ ExteriorFourFaces.face (R : ℝ) i) :
      (G p).val = (H i ⟨p.val,hp⟩).val := by
    have h := ExteriorFourFaces.fourFaceHomeomorph_on_face
      (show 0 < (R : ℝ) by exact_mod_cast hR) H hfix i p hp
    change (G p).val = (H i ⟨p.val,hp⟩).val at h
    exact h
  let P := planeExteriorHomeomorph R
  let K := P.trans (G.trans P.symm)
  have hKprod (x : squareExterior R) :
      Complex.equivRealProdCLM (K x).val = (G (P x)).val := by
    have hc : P (K x) = G (P x) := P.apply_symm_apply _
    exact congrArg Subtype.val hc
  have hcoordinates (i : Fin 4) (p : ExteriorFourFaces.FacePoint (R : ℝ) i) :
      squareFaceCoordinates i (H i p).val =
        ((E i).H (squareFaceSectorHomeomorph R i p)).val := by
    change squareFaceCoordinates i ((squareFaceCoordinates i).symm _) = _
    exact (squareFaceCoordinates i).apply_symm_apply _
  refine ⟨K,?_,?_⟩
  · intro l hl x
    obtain ⟨i,hi⟩ := mem_iUnion.mp
      (ExteriorFourFaces.exterior_covered_by_faces (P x).property)
    have hs := hfaceSign i l hl ⟨(P x).val,hi⟩
    have hx : (K x).val = Complex.equivRealProdCLM.symm (G (P x)).val := by
      rw [← hKprod,Complex.equivRealProdCLM.symm_apply_apply]
    rw [hx,hGlocal i (P x) hi]
    simpa only [P,planeExteriorHomeomorph_apply,
      Complex.equivRealProdCLM.symm_apply_apply] using hs
  · intro i x hx
    change squareFaceLinearCoordinates i (Complex.equivRealProdCLM (K x).val) = _
    rw [squareFaceLinearCoordinates_eq,hKprod,hGlocal i (P x) hx]
    exact hcoordinates i ⟨(P x).val,hx⟩

private theorem squareFacePlaneEquiv_symm_rightPoint (i : Fin 4) (R y : ℝ) :
    (squareFacePlaneEquiv i).symm (rightPoint R y) =
      (squareFacePlaneCoordinates i).symm (R,y) := by
  apply (squareFacePlaneEquiv i).injective
  rw [(squareFacePlaneEquiv i).apply_symm_apply]
  change rightPoint R y = Complex.equivRealProdCLM.symm
    (squareFacePlaneCoordinates i ((squareFacePlaneCoordinates i).symm (R,y)))
  rw [(squareFacePlaneCoordinates i).apply_symm_apply]
  simp [rightPoint,Complex.equivRealProdCLM_symm_apply]

/-- Each actual maximal clipping edge uses exactly the same anchors in the
bounded affine restriction and in its outgoing strip. The equality is along
the whole edge, not inferred merely from endpoint continuity. -/
private theorem ExteriorFaceMap_boundedBoundaryAgreement
    (R : ℚ) (L : List RationalLine) (i : Fin 4) (φ : ℝ →ₗ[ℚ] ℚ)
    (hφ : φ 1 = 1)
    (D : ExteriorFaceFamily R (L.map (squareFaceLine i))) (E : ExteriorFaceMap D φ)
    (H : closedCell (squareLines R) ≃ₜ closedCell (squareLines R))
    (hfaces : ∀ C ∈ fullSquareCodes R L, ∀ l ∈ C, ∀ a b : Plane,
      a ≠ b → cellFace C l = segment ℝ a b →
      ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
        ∀ x : closedCell (squareLines R), x.val ∈ cellFace C l → (H x : Plane) = g x.val)
    (x : closedCell (squareLines R))
    (hx : Complex.equivRealProdCLM x.val ∈ ExteriorFourFaces.face (R : ℝ) i) :
    squareFacePlaneCoordinates i (H x : Plane) =
      (E.H (squareFaceSectorHomeomorph R i ⟨Complex.equivRealProdCLM x.val,hx⟩)).val := by
  classical
  let p := squareFaceSectorHomeomorph R i ⟨Complex.equivRealProdCLM x.val,hx⟩
  have hpx : p.val = squareFacePlaneCoordinates i x.val := by
    exact (squareFaceLinearCoordinates_eq i (Complex.equivRealProdCLM x.val)).symm
  have hpR : p.val.1 = (R : ℝ) := by
    rw [hpx]
    obtain ⟨hre,him⟩ := (mem_closedCell_squareLines R x.val).mp x.property
    exact squareFacePlaneCoordinates_right_eq_of_box_face R i x.val
      ⟨hre.1,hre.2,him.1,him.2⟩
      (by simpa only [Complex.equivRealProdCLM_apply] using hx)
  have hcover := ExteriorFaceCharts.affineGraphFamily_face_cover D.hn R D.a D.b
    D.first D.last D.gap p.property
  obtain ⟨j,hpj⟩ := mem_iUnion.mp hcover
  have hb : D.a j.castSucc*(R : ℝ)+D.b j.castSucc ≤ p.val.2 ∧
      p.val.2 ≤ D.a j.succ*(R : ℝ)+D.b j.succ := by
    change (R : ℝ) ≤ p.val.1 ∧ D.a j.castSucc*p.val.1+D.b j.castSucc ≤ p.val.2 ∧
      p.val.2 ≤ D.a j.succ*p.val.1+D.b j.succ at hpj
    rw [hpR] at hpj
    exact hpj.2
  have horder : D.a j.castSucc*(R : ℝ)+D.b j.castSucc <
      D.a j.succ*(R : ℝ)+D.b j.succ := sub_pos.mp (D.gap j R le_rfl)
  have hpseg : p.val ∈ segment ℝ (exteriorFaceAnchor D j.castSucc).val
      (exteriorFaceAnchor D j.succ).val :=
    vertical_segment_mem_of_bounds R _ _ horder p.val hpR hb.1 hb.2
  obtain ⟨C,hC,hface⟩ := rotated_adjacent_face_pulls_back i R L (D.cell j)
    (D.a j.castSucc*R+D.b j.castSucc) (D.a j.succ*R+D.b j.succ)
    (D.cell_mem j) (D.strict j) (D.face j)
  rw [squareFacePlaneEquiv_symm_rightPoint,squareFacePlaneEquiv_symm_rightPoint] at hface
  let A : Plane := (squareFacePlaneCoordinates i).symm (exteriorFaceAnchor D j.castSucc).val
  let B : Plane := (squareFacePlaneCoordinates i).symm (exteriorFaceAnchor D j.succ).val
  change cellFace C (squarePhysicalFaceLine i (R : ℝ)) = segment ℝ A B at hface
  have hlC : squarePhysicalFaceLine i (R : ℝ) ∈ C := by
    have hc := hC
    unfold fullSquareCodes at hc
    obtain ⟨cell,_,hEq⟩ := List.mem_map.mp hc
    rw [← hEq]
    exact List.mem_append.mpr (Or.inl (squarePhysicalFaceLine_mem_squareLines i R))
  have hAB : A ≠ B := by
    intro heq
    have hs := congrArg (fun z : Plane => (squareFacePlaneCoordinates i z).2) heq
    dsimp only [A,B] at hs
    rw [(squareFacePlaneCoordinates i).apply_symm_apply,
      (squareFacePlaneCoordinates i).apply_symm_apply] at hs
    change D.a j.castSucc*R+D.b j.castSucc = D.a j.succ*R+D.b j.succ at hs
    exact (ne_of_lt horder) hs
  obtain ⟨g,hgA,hgB,hgH⟩ := hfaces C hC (squarePhysicalFaceLine i R) hlC A B hAB hface
  let f : AffineMap ℝ (ℝ × ℝ) (ℝ × ℝ) :=
    (squareFacePlaneCoordinates i).toAffineMap.comp
      (g.toAffineMap.comp (squareFacePlaneCoordinates i).symm.toAffineMap)
  have hanchor (k : Fin (D.n+1)) :
      squareFacePlaneCoordinates i (deformPoint φ
        ((squareFacePlaneCoordinates i).symm (exteriorFaceAnchor D k).val)) =
      (E.H (exteriorFaceAnchor D k)).val := by
    rw [ExteriorFaceMap_anchorValue D φ E k (exteriorFaceAnchor D k) rfl]
    change squareFacePlaneCoordinates i (deformPoint φ
      ((squareFacePlaneCoordinates i).symm ((R : ℝ),D.a k*R+D.b k))) =
      ((R : ℝ),D.a k*R+(φ (D.b k) : ℝ))
    obtain ⟨u,_,ha,hb⟩ := D.labels k
    rw [ha,hb]
    exact squareFace_rationalAnchor_deform i φ hφ R u.1 u.2
  have hf₀ : f (exteriorFaceAnchor D j.castSucc).val =
      (E.H (exteriorFaceAnchor D j.castSucc)).val := by
    change squareFacePlaneCoordinates i (g A) = _
    rw [hgA]
    exact hanchor j.castSucc
  have hf₁ : f (exteriorFaceAnchor D j.succ).val =
      (E.H (exteriorFaceAnchor D j.succ)).val := by
    change squareFacePlaneCoordinates i (g B) = _
    rw [hgB]
    exact hanchor j.succ
  have hresult := ExteriorFaceMap_affineEdgeAgreement D φ E j f hf₀ hf₁ p hpseg
  have hxImage : x.val ∈ (squareFacePlaneCoordinates i).symm ''
      segment ℝ (exteriorFaceAnchor D j.castSucc).val
        (exteriorFaceAnchor D j.succ).val := by
    refine ⟨p.val,hpseg,?_⟩
    rw [hpx,(squareFacePlaneCoordinates i).symm_apply_apply]
  have himage : (squareFacePlaneCoordinates i).symm ''
      segment ℝ (exteriorFaceAnchor D j.castSucc).val
        (exteriorFaceAnchor D j.succ).val = segment ℝ A B :=
    image_segment ℝ (squareFacePlaneCoordinates i).symm.toAffineMap _ _
  rw [himage,← hface] at hxImage
  rw [hgH x hxImage]
  change squareFacePlaneCoordinates i
    (g ((squareFacePlaneCoordinates i).symm p.val)) = _ at hresult
  rw [hpx,(squareFacePlaneCoordinates i).symm_apply_apply] at hresult
  exact hresult

theorem finiteRationalArrangement_transport :
  ∀ (L : Finset RationalLine) (Z : Finset Plane),
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        ∃ H : Plane ≃ₜ Plane, (∀ z ∈ Z, H z = deformPoint φ z) ∧
          ∀ l ∈ L, ∀ z : Plane,
            Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
  classical
  intro L Z
  let A := augmentedArrangementLines L Z
  have hdiagonal : ∀ l ∈ diagonalLines, l ∈ A := by
    intro l hl
    simp only [A,augmentedArrangementLines,List.mem_append]
    tauto
  obtain ⟨R,hR,F₀,hroot⟩ := augmentedArrangement_integerSquare_enclosure L Z
  obtain ⟨ψ,hψ⟩ := exists_finiteApproximation F₀ 1 zero_lt_one
  have hsource : ∀ l ∈ A, ∀ m ∈ A,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, l.eval z = 0 → m.eval z = 0 → ‖z‖ < (R : ℝ) :=
    fun l hl m hm hd => ((hroot ψ hψ).2 l hl m hm hd).1
  have hchoices (i : Fin 4) := finiteExteriorFace_family R hR
    (A.map (squareFaceLine i)) (squareFaceGraphSet_has_corners A hdiagonal i)
    (squareFaceLines_intersections_enclosed A R hsource i)
  choose D tests threshold hthreshold hmap using hchoices
  obtain ⟨F₂,ε₂,hε₂,hall⟩ := unify_finiteApproximationTests tests threshold hthreshold
  obtain ⟨F₁,ε₁,hε₁,hbounded⟩ := finiteSquare_signedHomeomorph R hR A
  refine ⟨(F₀ ∪ F₁) ∪ F₂,min (min 1 ε₁) ε₂,lt_min (lt_min zero_lt_one hε₁) hε₂,?_⟩
  intro φ hφ
  have hφ₀ : IsFiniteApproximation F₀ 1 φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_left _ _))
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto)
    ((min_le_left _ _).trans (min_le_right _ _))
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := finiteApproximation_narrow hφ
    (by intro x hx; simp only [Finset.mem_union]; tauto) (min_le_right _ _)
  let E (i : Fin 4) : ExteriorFaceMap (D i) φ :=
    Classical.choice (hmap i φ (hall φ hφ₂ i))
  have htarget : ∀ l ∈ A, ∀ m ∈ A,
      l.normal.x*m.normal.y-l.normal.y*m.normal.x ≠ 0 →
      ∀ z : Plane, (deformLine φ l).eval z = 0 →
        (deformLine φ m).eval z = 0 → ‖z‖ < (R : ℝ) :=
    fun l hl m hm hd => ((hroot φ hφ₀).2 l hl m hm hd).2
  obtain ⟨B,hBsign,hBcells⟩ := hbounded φ hφ₁
  have hBfaces : ∀ C ∈ fullSquareCodes R A, ∀ l ∈ C, ∀ a b : Plane,
      a ≠ b → cellFace C l = segment ℝ a b →
      ∃ g : Plane ≃ᵃ[ℝ] Plane, g a = deformPoint φ a ∧ g b = deformPoint φ b ∧
        ∀ x : closedCell (squareLines R), x.val ∈ cellFace C l →
          (B x : Plane) = g x.val := by
    intro C hC l hl a b hab hface
    obtain ⟨K,_,hKface,_,hKB⟩ := hBcells C hC
    obtain ⟨g,hga,hgb,hgK⟩ := hKface l hl a b hab hface
    refine ⟨g,hga,hgb,?_⟩
    intro x hx
    exact (hKB x hx.1).trans (hgK ⟨x.val,hx.1⟩ hx)
  obtain ⟨K,hKsign,hKlocal⟩ := finiteExterior_arrangementHomeomorph
    R hR A φ hdiagonal hsource htarget D E
  have hboundary := squareHomeomorph_preserves_boundary R φ hφ.1 B
    (fun l hl => hBsign l (List.mem_append.mpr (Or.inl hl)))
  have hagree : ∀ x (hxB : x ∈ closedCell (squareLines R)) (hxK : x ∈ squareExterior R),
      (B ⟨x,hxB⟩ : Plane) = (K ⟨x,hxK⟩ : Plane) := by
    intro x hxB hxK
    obtain ⟨i,hi⟩ := mem_iUnion.mp (ExteriorFourFaces.exterior_covered_by_faces
      (planeExteriorHomeomorph R ⟨x,hxK⟩).property)
    apply (squareFacePlaneCoordinates i).injective
    exact (ExteriorFaceMap_boundedBoundaryAgreement R A i φ hφ.1 (D i) (E i)
      B hBfaces ⟨x,hxB⟩ hi).trans (hKlocal i ⟨x,hxK⟩ hi).symm
  obtain ⟨H,hHbounded,hHexterior⟩ := twoClosedCover_globalHomeomorph
    (closedCell (squareLines R)) (squareExterior R) (closedCell_isClosed _)
    (squareExterior_isClosed R) (square_and_exterior_cover R) B K hboundary hagree
  have hAsign : ∀ l ∈ A, ∀ z : Plane,
      Real.sign ((deformLine φ l).eval (H z)) = Real.sign (l.eval z) := by
    intro l hl z
    rcases square_and_exterior_cover R z with hz | hz
    · rw [hHbounded z hz]
      exact hBsign l (List.mem_append.mpr (Or.inr hl)) ⟨z,hz⟩
    · rw [hHexterior z hz]
      exact hKsign l hl ⟨z,hz⟩
  refine ⟨H,?_,?_⟩
  · intro z hz
    have hn := ((hroot φ hφ₀).1 z hz).1
    have hre : |z.re| ≤ (R : ℝ) := (Complex.abs_re_le_norm z).trans hn.le
    have him : |z.im| ≤ (R : ℝ) := (Complex.abs_im_le_norm z).trans hn.le
    have hzB : z ∈ closedCell (squareLines R) :=
      (mem_closedCell_squareLines R z).mpr ⟨abs_le.mp hre,abs_le.mp him⟩
    rw [hHbounded z hzB]
    apply signPreservingMap_transports_marks A (closedCell (squareLines R)) φ
      (fun x => (B x : Plane))
      (fun l hl => hBsign l (List.mem_append.mpr (Or.inr hl))) z hzB
    intro l hl
    have hm : l ∈ Z.toList.flatMap markLines :=
      List.mem_flatMap.mpr ⟨z,Finset.mem_toList.mpr hz,hl⟩
    simp only [A,augmentedArrangementLines,List.mem_append]
    tauto
  · intro l hl z
    apply hAsign l ?_ z
    have hl' : l ∈ L.toList := Finset.mem_toList.mpr hl
    simp only [A,augmentedArrangementLines,List.mem_append]
    tauto

theorem polyhedralDeformation_independentOfCode :
  ∀ (K : PolygonalRegion) (P Q : PolyhedralCode),
    polyhedralSupport P = K.support → polyhedralSupport Q = K.support →
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          deformedPolyhedralSupport P φ = deformedPolyhedralSupport Q φ := by
  classical
  intro K P Q hP hQ
  let L : Finset RationalLine := (P.flatten ++ Q.flatten).toFinset
  obtain ⟨F, ε, hε, htransport⟩ := finiteRationalArrangement_transport L ∅
  refine ⟨F, ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨H, _, hH⟩ := htransport φ hφ
  have hLP : ∀ cell ∈ P, ∀ l ∈ cell, l ∈ L := by
    intro cell hc l hl
    simp only [L, List.mem_toFinset, List.mem_append, List.mem_flatten]
    exact Or.inl ⟨cell, hc, hl⟩
  have hLQ : ∀ cell ∈ Q, ∀ l ∈ cell, l ∈ L := by
    intro cell hc l hl
    simp only [L, List.mem_toFinset, List.mem_append, List.mem_flatten]
    exact Or.inr ⟨cell, hc, hl⟩
  ext y
  obtain ⟨z, rfl⟩ := H.surjective y
  rw [polyhedralSupport_transport_mem P φ H (fun cell hc l hl => hH l (hLP cell hc l hl)),
    polyhedralSupport_transport_mem Q φ H (fun cell hc l hl => hH l (hLQ cell hc l hl)),
    hP, hQ]

private theorem finiteCell_decoratedTriangulations (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (openCell cell).Nonempty) :
    ∃ W : Finset Plane,
      (∃ A : Tiling.Triangulation (closedCell cell),
        ∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W : Set Plane)) ∧ 0 ∈ W ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ A : Tiling.Triangulation (closedCell (cell.map (deformLine φ))),
            (∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W.image (deformPoint φ) : Set Plane)) ∧
              (closedCell (cell.map (deformLine φ))).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := hne
  let V := (closedCell_extremePoints_finite cell).toFinset
  let W := insert 0 (insert c V)
  obtain ⟨A, hA⟩ := closedCell_fanTriangulation cell hcompact c hc
  obtain ⟨F₁, ε₁, hε₁, hext⟩ := finiteCell_extremePoints_transport cell
  obtain ⟨F₂, ε₂, hε₂, hcenter⟩ := finiteCell_strictPointTests cell c hc
  refine ⟨W, ⟨A, ?_⟩, by simp [W], F₁ ∪ F₂, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  · intro t ht z hz
    rcases hA t ht hz with hz | hz
    · simp [W, hz]
    · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        ((closedCell_extremePoints_finite cell).mem_toFinset.mpr hz))
  · intro φ hφ
    have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
      (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
    have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := ⟨hφ.1, fun x hx =>
      (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
    have hcφ := hcenter φ hφ₂
    have hcompactφ : IsCompact (closedCell (cell.map (deformLine φ))) := by
      rw [closedCell_map_eq_shiftedCell]
      exact shiftedCell_isCompact_of_compact_same_normals cell hcompact
        ⟨c, fun l hl => (hc l hl).le⟩ _
    obtain ⟨Aφ, hAφ⟩ := closedCell_fanTriangulation _ hcompactφ (deformPoint φ c) hcφ
    refine ⟨Aφ, ?_, deformPoint φ c, fun l hl => (hcφ l hl).le⟩
    intro t ht z hz
    rcases hAφ t ht hz with hz | hz
    · exact Finset.mem_image.mpr ⟨c, by simp [W], hz.symm⟩
    · rw [hext φ hφ₁] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      exact Finset.mem_image.mpr ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        ((closedCell_extremePoints_finite cell).mem_toFinset.mpr hv)), rfl⟩

private theorem finiteCode_decoratedTriangulations (L : List RationalLine) (P : PolyhedralCode)
    (hdata : ∀ cell ∈ P, cell ∈ signedCodes L ∧
      IsCompact (closedCell cell) ∧ (openCell cell).Nonempty)
    (hne : (polyhedralSupport P).Nonempty) :
    ∃ W : Finset Plane,
      (∃ A : Tiling.Triangulation (polyhedralSupport P),
        ∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W : Set Plane)) ∧ 0 ∈ W ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ A : Tiling.Triangulation (deformedPolyhedralSupport P φ),
            (∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W.image (deformPoint φ) : Set Plane)) ∧
              (deformedPolyhedralSupport P φ).Nonempty := by
  classical
  let S := P.toFinset
  have hmem (i : {cell // cell ∈ S}) : i.1 ∈ P := List.mem_toFinset.mp i.2
  have hlocal (i : {cell // cell ∈ S}) := finiteCell_decoratedTriangulations i.1
    (hdata i.1 (hmem i)).2.1 (hdata i.1 (hmem i)).2.2
  choose W hW using hlocal
  choose A hA using (fun i => (hW i).1)
  choose tests threshold hpos htarget using (fun i => (hW i).2.2)
  obtain ⟨F, ε, hε, htests⟩ := unify_finiteApproximationTests tests threshold hpos
  let V : Finset Plane := insert 0 (Finset.univ.biUnion W)
  have hpair : Pairwise (fun i j : {cell // cell ∈ S} =>
      AEDisjoint volume (closedCell i.1) (closedCell j.1)) := by
    intro i j hij
    exact signedCodes_aedisjoint L i.1 j.1 (hdata i.1 (hmem i)).1
      (hdata j.1 (hmem j)).1 (fun heq => hij (Subtype.ext heq)) (hdata i.1 (hmem i)).2.1
  have hunion : (⋃ i : {cell // cell ∈ S}, closedCell i.1) = polyhedralSupport P := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact ⟨i.1, hmem i, hi⟩
    · rintro ⟨cell, hc, hz⟩
      exact mem_iUnion.mpr ⟨⟨cell, List.mem_toFinset.mpr hc⟩, hz⟩
  refine ⟨V, ?_, by simp [V], F, ε, hε, ?_⟩
  · rw [← hunion]
    refine ⟨Tiling.Triangulation.finiteUnion A hpair, ?_⟩
    intro t ht z hz
    obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, hA i t hti hz⟩)
  · intro φ hφ
    have hi (i : {cell // cell ∈ S}) := htarget i φ (htests φ hφ i)
    choose T hT using hi
    have hcompactTarget (i : {cell // cell ∈ S}) :
        IsCompact (closedCell (i.1.map (deformLine φ))) := by
      rw [closedCell_map_eq_shiftedCell]
      apply shiftedCell_isCompact_of_compact_same_normals i.1 (hdata i.1 (hmem i)).2.1
      exact (hdata i.1 (hmem i)).2.2.mono (fun z hz l hl => (hz l hl).le)
    have hpairTarget : Pairwise (fun i j : {cell // cell ∈ S} =>
        AEDisjoint volume (closedCell (i.1.map (deformLine φ)))
          (closedCell (j.1.map (deformLine φ)))) := by
      intro i j hij
      exact deformedSignedCodes_aedisjoint L φ i.1 j.1 (hdata i.1 (hmem i)).1
        (hdata j.1 (hmem j)).1 (fun heq => hij (Subtype.ext heq)) (hcompactTarget i)
    have hunionTarget : (⋃ i : {cell // cell ∈ S}, closedCell (i.1.map (deformLine φ))) =
        deformedPolyhedralSupport P φ := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := mem_iUnion.mp hz
        exact ⟨i.1.map (deformLine φ), List.mem_map.mpr ⟨i.1, hmem i, rfl⟩, hi⟩
      · rintro ⟨cell, hmapped, hz⟩
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hmapped
        exact mem_iUnion.mpr ⟨⟨c, List.mem_toFinset.mpr hc⟩, hz⟩
    have hnonemptyTarget : (deformedPolyhedralSupport P φ).Nonempty := by
      obtain ⟨x, cell, hc, _⟩ := hne
      let i : {cell // cell ∈ S} := ⟨cell, List.mem_toFinset.mpr hc⟩
      obtain ⟨y, hy⟩ := (hT i).2
      exact ⟨y, cell.map (deformLine φ), List.mem_map.mpr ⟨cell, hc, rfl⟩, hy⟩
    rw [← hunionTarget]
    refine ⟨Tiling.Triangulation.finiteUnion T hpairTarget, ?_, hunionTarget.symm ▸ hnonemptyTarget⟩
    intro t ht z hz
    obtain ⟨i, _, hti⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp ((hT i).1 t hti hz)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_insert_of_mem
      (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩), rfl⟩

private theorem finiteCell_uniformRadius (cell : List RationalLine)
    (hcompact : IsCompact (closedCell cell)) (hne : (closedCell cell).Nonempty) :
    ∃ F : Finset ℝ, ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        closedCell (cell.map (deformLine φ)) ⊆ Metric.closedBall 0 B := by
  classical
  obtain ⟨F₁, ε₁, hε₁, hhull⟩ := finiteCell_convexHull_transport cell hcompact hne
  let V := (closedCell_extremePoints_finite cell).toFinset
  obtain ⟨F₂, B, hB, hbound⟩ := finiteDecoration_uniformImageBound V
  refine ⟨F₁ ∪ F₂, min ε₁ 1, B, lt_min hε₁ zero_lt_one, hB, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
  have hφ₂ : IsFiniteApproximation F₂ 1 φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
  rw [hhull φ hφ₁]
  apply convexHull_min ?_ (convex_closedBall (0 : Plane) B)
  rintro z ⟨v, hv, rfl⟩
  have hvV : v ∈ V := (closedCell_extremePoints_finite cell).mem_toFinset.mpr hv
  simpa [Metric.mem_closedBall, dist_eq_norm] using hbound φ hφ₂ v hvV

private theorem finiteCode_uniformRadius (P : PolyhedralCode)
    (hdata : ∀ cell ∈ P, IsCompact (closedCell cell) ∧ (closedCell cell).Nonempty) :
    ∃ F : Finset ℝ, ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
        deformedPolyhedralSupport P φ ⊆ Metric.closedBall 0 B := by
  induction P with
  | nil =>
    refine ⟨∅, 1, 1, zero_lt_one, zero_lt_one, ?_⟩
    intro φ hφ
    simp [deformedPolyhedralSupport, polyhedralSupport]
  | cons cell P ih =>
    obtain ⟨F₁, ε₁, B₁, hε₁, hB₁, h₁⟩ := finiteCell_uniformRadius cell
      (hdata cell List.mem_cons_self).1 (hdata cell List.mem_cons_self).2
    obtain ⟨F₂, ε₂, B₂, hε₂, hB₂, h₂⟩ := ih
      (fun c hc => hdata c (List.mem_cons_of_mem cell hc))
    refine ⟨F₁ ∪ F₂, min ε₁ ε₂, B₁+B₂, lt_min hε₁ hε₂, add_pos hB₁ hB₂, ?_⟩
    intro φ hφ z hz
    have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
      (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
    have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := ⟨hφ.1, fun x hx =>
      (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
    have heq : deformedPolyhedralSupport (cell :: P) φ =
        closedCell (cell.map (deformLine φ)) ∪ deformedPolyhedralSupport P φ := by
      ext w
      simp [deformedPolyhedralSupport, polyhedralSupport, closedCell]
    rw [heq] at hz
    rcases hz with hz | hz
    · exact Metric.closedBall_subset_closedBall (le_add_of_nonneg_right hB₂.le) (h₁ φ hφ₁ hz)
    · exact Metric.closedBall_subset_closedBall (le_add_of_nonneg_left hB₁.le) (h₂ φ hφ₂ hz)

private theorem occupiedCodes_cellData (s : Set Plane) (hcompact : IsCompact s)
    (hregular : closure (interior s) = s) (L : List RationalLine)
    (hfront : ∀ z ∈ frontier s, ∃ l ∈ L, l.eval z = 0) :
    ∀ cell ∈ occupiedCodes s L,
      IsCompact (closedCell cell) ∧ (openCell cell).Nonempty := by
  classical
  have hsupport := occupiedCodes_support s hcompact.isClosed hregular L hfront
  intro cell hc
  have hne : (openCell cell ∩ interior s).Nonempty :=
    of_decide_eq_true (List.mem_filter.mp hc).2
  refine ⟨hcompact.of_isClosed_subset (closedCell_isClosed cell) ?_,
    hne.mono inter_subset_left⟩
  intro z hz
  rw [← hsupport]
  exact ⟨cell, hc, hz⟩

/-- Finite line evaluations supply simultaneous exact aligned support and interior germs. -/
private theorem finiteCode_germTests (P : PolyhedralCode) (Z : Finset Plane) :
    ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
      ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ → ∀ v ∈ Z,
        Tiling.Polygonal.SameGermAt (interior (polyhedralSupport P)) v
          (interior (deformedPolyhedralSupport P φ)) (deformPoint φ v) := by
  classical
  let E : Finset ℝ := P.flatten.toFinset.biUnion fun l => Z.image l.eval
  obtain ⟨ε, hε, hsign⟩ := finite_scalar_signTests E
  refine ⟨E, ε, hε, ?_⟩
  intro φ hφ v hv
  apply polyhedralSupport_alignedInteriorGerm P φ v
  intro cell hc l hl
  rw [deformLine_eval_commutes]
  apply hsign φ hφ
  apply Finset.mem_biUnion.mpr
  refine ⟨l, List.mem_toFinset.mpr (List.mem_flatten.mpr ⟨cell, hc, hl⟩), ?_⟩
  exact Finset.mem_image.mpr ⟨v, hv, rfl⟩

private theorem rationalPoint_vectorDirection (v : Plane) (hv : Tiling.IsRationalPoint v)
    (hne : v ≠ 0) : Tiling.RationalSlopes.IsRationalVectorDirection v := by
  obtain ⟨x, y, hre, him⟩ := hv
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    apply Complex.ext <;> simp [hre, him, h.1, h.2]
  let n : RationalNormal := ⟨y, -x, by
    rcases hxy with hx | hy
    · exact Or.inr (neg_ne_zero.mpr hx)
    · exact Or.inl hy⟩
  have hreal : (n.x : ℝ) ≠ 0 ∨ (n.y : ℝ) ≠ 0 := by
    rcases n.nonzero with hx | hy
    · exact Or.inl (by exact_mod_cast hx)
    · exact Or.inr (by exact_mod_cast hy)
  have hp : perpendicularVector (n.x : ℝ) (n.y : ℝ) = v := by
    apply Complex.ext <;> simp [perpendicularVector, n, hre, him]
  have hn : normalDirection n = Submodule.span ℝ ({v} : Set Plane) := by
    simpa only [normalDirection, hp] using normalKernel_eq_span_perpendicular
      (n.x : ℝ) (n.y : ℝ) hreal
  exact ⟨hne, hn ▸ (normalDirection_rational n).2⟩

private theorem rationalPoint_sub (a b : Plane) (ha : Tiling.IsRationalPoint a)
    (hb : Tiling.IsRationalPoint b) : Tiling.IsRationalPoint (a-b) := by
  obtain ⟨ax, ay, hax, hay⟩ := ha
  obtain ⟨bx, by_, hbx, hby⟩ := hb
  exact ⟨ax-bx, ay-by_, by simp [Complex.sub_re, hax, hbx],
    by simp [Complex.sub_im, hay, hby]⟩

/-- Uses the canonical finite intrinsic boundary ancestor. -/
private theorem rationalPolygon_hasRationalSlopes (K : PolygonalRegion)
    (hK : Tiling.IsRational K.support) : Tiling.RationalSlopes.HasRationalSlopes K := by
  obtain ⟨E, hE, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  refine ⟨E, ?_, hfront⟩
  intro e he
  have hends := hE e he
  exact rationalPoint_vectorDirection (e.2-e.1)
    (rationalPoint_sub e.2 e.1 (hK.2 e.2 hends.2.2.1) (hK.2 e.1 hends.2.1))
    (sub_ne_zero.mpr hends.1.symm)

private theorem deformPoint_isRational (φ : ℝ →ₗ[ℚ] ℚ) (z : Plane) :
    Tiling.IsRationalPoint (deformPoint φ z) := by
  exact ⟨φ z.re, φ z.im, rfl, rfl⟩

private theorem rationalPolygon_coreConstruction :
  ∀ K : PolygonalRegion, Tiling.RationalSlopes.HasRationalSlopes K →
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
      ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
        ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
          ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
            ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
              Tiling.IsRational Kφ.support ∧ Decorates Kφ (W.image (deformPoint φ)) ∧
                ∀ v ∈ W,
                  Tiling.Polygonal.SameGermAt K.openCarrier v Kφ.openCarrier (deformPoint φ v) := by
  classical
  intro K hK
  obtain ⟨L, hfront⟩ := rationalSlopes_frontierLineFamily K hK
  let P := occupiedCodes K.support L
  have hP : polyhedralSupport P = K.support := occupiedCodes_support K.support
    K.isPolygonal.isClosed K.isPolygonal.closure_interior L hfront
  have hcell := occupiedCodes_cellData K.support K.isPolygonal.isCompact
    K.isPolygonal.closure_interior L hfront
  have hdata : ∀ cell ∈ P, cell ∈ signedCodes L ∧
      IsCompact (closedCell cell) ∧ (openCell cell).Nonempty := by
    intro cell hc
    exact ⟨(List.mem_filter.mp hc).1, hcell cell hc⟩
  obtain ⟨W, hsource, h0, F₁, ε₁, hε₁, htarget⟩ :=
    finiteCode_decoratedTriangulations L P hdata (hP.symm ▸ K.nonempty)
  have hdec : Decorates K W := by
    change ∃ A : Tiling.Triangulation K.support, ∀ t ∈ A.pieces, t.extremePoints ℝ ⊆ (W : Set Plane)
    rw [← hP]
    exact hsource
  obtain ⟨F₂, ε₂, hε₂, hgerm⟩ := finiteCode_germTests P W
  refine ⟨P, hP, W, hdec, h0, F₁ ∪ F₂, min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
  have hφ₂ : IsFiniteApproximation F₂ ε₂ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
  obtain ⟨A, hA, hne⟩ := htarget φ hφ₁
  let Kφ : PolygonalRegion := ⟨deformedPolyhedralSupport P φ, ⟨A⟩, hne⟩
  refine ⟨Kφ, rfl, ⟨⟨A⟩, ?_⟩, ⟨A, hA⟩, ?_⟩
  · intro z hz
    obtain ⟨t, ht, hzt⟩ := hz A
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (hA t ht hzt)
    exact deformPoint_isRational φ v
  · intro v hv
    have hg := hgerm φ hφ₂ v hv
    rw [hP] at hg
    exact hg

private theorem segment_sub_mem_span_direction (a b x y : Plane)
    (hx : x ∈ segment ℝ a b) (hy : y ∈ segment ℝ a b) :
    y - x ∈ Submodule.span ℝ ({b - a} : Set Plane) := by
  rw [segment_eq_image'] at hx hy
  obtain ⟨s, hs, hx⟩ := hx
  obtain ⟨t, ht, hy⟩ := hy
  have hcalc : (a + t • (b - a)) - (a + s • (b - a)) = (t - s) • (b - a) := by
    module
  rw [← hx, ← hy, hcalc]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

private theorem segment_inter_subsingleton_of_span_ne (a b c d : Plane)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hspan : Submodule.span ℝ ({b - a} : Set Plane) ≠
      Submodule.span ℝ ({d - c} : Set Plane)) :
    ∀ ⦃x y : Plane⦄,
      x ∈ segment ℝ a b ∩ segment ℝ c d →
      y ∈ segment ℝ a b ∩ segment ℝ c d → x = y := by
  intro x y hx hy
  by_contra hxy
  have hdiff : y - x ≠ 0 := sub_ne_zero.mpr (fun h => hxy h.symm)
  have hw₁ : y - x ∈ Submodule.span ℝ ({b - a} : Set Plane) :=
    segment_sub_mem_span_direction a b x y hx.1 hy.1
  have hw₂ : y - x ∈ Submodule.span ℝ ({d - c} : Set Plane) :=
    segment_sub_mem_span_direction c d x y hx.2 hy.2
  have hspan₁ : Module.finrank ℝ (Submodule.span ℝ ({b - a} : Set Plane)) = 1 := by
    simpa using finrank_span_singleton (K := ℝ) (show b - a ≠ 0 from sub_ne_zero.mpr hab.symm)
  have hspan₂ : Module.finrank ℝ (Submodule.span ℝ ({d - c} : Set Plane)) = 1 := by
    simpa using finrank_span_singleton (K := ℝ) (show d - c ≠ 0 from sub_ne_zero.mpr hcd.symm)
  have heq₁ : Submodule.span ℝ ({b - a} : Set Plane) =
      Submodule.span ℝ ({y - x} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hspan₁ hw₁ hdiff
  have heq₂ : Submodule.span ℝ ({d - c} : Set Plane) =
      Submodule.span ℝ ({y - x} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hspan₂ hw₂ hdiff
  exact hspan (heq₁.trans heq₂.symm)

private theorem segment_infinite_of_ne (a b : Plane) (hab : a ≠ b) :
    (segment ℝ a b).Infinite := by
  rw [segment_eq_image_lineMap]
  have hinj : Set.InjOn (AffineMap.lineMap a b) (Icc (0 : ℝ) 1) :=
    (AffineMap.lineMap_injective ℝ hab).injOn
  exact (infinite_image_iff hinj).2 (Icc_infinite (show (0 : ℝ) < 1 by norm_num))

private theorem finiteBoundaryCover_contains_direction
    (E : Finset (Plane × Plane))
    (hEdges : ∀ e ∈ E, e.1 ≠ e.2)
    (a b : Plane) (hab : a ≠ b)
    (hcovered : segment ℝ a b ⊆ ⋃ e ∈ (E : Set (Plane × Plane)),
      segment ℝ e.1 e.2) :
    ∃ e ∈ E,
      Submodule.span ℝ ({e.2 - e.1} : Set Plane) =
        Submodule.span ℝ ({b - a} : Set Plane) := by
  by_contra hnone
  have hnotdir : ∀ e ∈ E,
      Submodule.span ℝ ({e.2 - e.1} : Set Plane) ≠
        Submodule.span ℝ ({b - a} : Set Plane) := by
    intro e he heq
    exact hnone ⟨e, he, heq⟩
  let U : Set Plane := ⋃ e ∈ (E : Set (Plane × Plane)),
    segment ℝ a b ∩ segment ℝ e.1 e.2
  have hUfinite : U.Finite := by
    change (⋃ e ∈ (E : Set (Plane × Plane)), segment ℝ a b ∩
      segment ℝ e.1 e.2).Finite
    apply E.finite_toSet.biUnion
    intro e he
    have hSub : ∀ ⦃x y : Plane⦄,
        x ∈ segment ℝ a b ∩ segment ℝ e.1 e.2 →
        y ∈ segment ℝ a b ∩ segment ℝ e.1 e.2 → x = y :=
      segment_inter_subsingleton_of_span_ne a b e.1 e.2 hab (hEdges e he)
        (hnotdir e he).symm
    by_cases hne : (segment ℝ a b ∩ segment ℝ e.1 e.2).Nonempty
    · obtain ⟨x, hx⟩ := hne
      apply (Set.finite_singleton x).subset
      intro y hy
      simp only [mem_singleton_iff]
      exact hSub hy hx
    · have hempty : segment ℝ a b ∩ segment ℝ e.1 e.2 = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      exact Set.finite_empty
  have hsub : segment ℝ a b ⊆ U := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp (hcovered hx)
    obtain ⟨he, hxe⟩ := Set.mem_iUnion.mp he
    exact mem_iUnion.2 ⟨e, mem_iUnion.2 ⟨he, ⟨hx, hxe⟩⟩⟩
  have hinfinite := segment_infinite_of_ne a b hab
  exact hUfinite.not_infinite (hinfinite.mono hsub)

private theorem small_segment_inside_ball (a b : Plane) (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ dist (a + t • (b - a)) a < ε := by
  let τ := min 1 ε
  have hτ : 0 < τ := lt_min zero_lt_one hε
  let t := τ / (2 * (‖b - a‖ + 1))
  have ht : 0 < t := by
    dsimp [t]
    positivity
  have ht1 : t < 1 := by
    dsimp [t, τ]
    have hn : 0 ≤ ‖b - a‖ := norm_nonneg _
    have hm : min 1 ε ≤ 1 := min_le_left _ _
    rw [div_lt_one (by positivity)]
    nlinarith
  have hdist : dist (a + t • (b - a)) a < ε := by
    have hn : 0 ≤ ‖b - a‖ := norm_nonneg _
    have hm : min 1 ε ≤ ε := min_le_right _ _
    have hmul : t * ‖b - a‖ < ε := by
      dsimp [t, τ]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity)).2
      nlinarith
    calc
      dist (a + t • (b - a)) a = ‖(a + t • (b - a)) - a‖ := dist_eq_norm _ _
      _ = ‖t • (b - a)‖ := by congr 1; abel
      _ = t * ‖b - a‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      _ < ε := hmul
  exact ⟨t, ht, ht1, hdist⟩

private theorem sameFrontierGerm_transfers_boundary_direction
    (K M : Tiling.RationalPolygonal.PolygonalRegion)
    (a b c : Plane) (hab : a ≠ b)
    (hsegment : segment ℝ a b ⊆ frontier K.support)
    (hfrontierGerm : frontier K.support =ᶠ[𝓝 a]
      ((a - c) +ᵥ frontier M.support)) :
    Tiling.Polygonal.HasBoundaryDirection M
      (Submodule.span ℝ ({b - a} : Set Plane)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hfrontierGerm
  obtain ⟨t, ht, ht1, hdist⟩ := small_segment_inside_ball a b ε hε
  let d : Plane := a + t • (b - a)
  have hdsegment : d ∈ segment ℝ a b := by
    rw [segment_eq_image']
    exact ⟨t, ⟨le_of_lt ht, le_of_lt ht1⟩, rfl⟩
  have hshort : segment ℝ a d ⊆ segment ℝ a b :=
    (convex_segment a b).segment_subset (left_mem_segment ℝ a b) hdsegment
  have hballShort : segment ℝ a d ⊆ Metric.ball a ε :=
    (convex_ball a ε).segment_subset (Metric.mem_ball_self hε) (by simpa [d] using hdist)
  have htranslated : segment ℝ c (c + t • (b - a)) ⊆ frontier M.support := by
    have hsegEq : (c - a) +ᵥ segment ℝ a d = segment ℝ c (c + t • (b - a)) := by
      rw [vadd_segment]
      congr 1
      · simp [vadd_eq_add, sub_eq_add_neg]
      · simp [d, vadd_eq_add, sub_eq_add_neg]
    rw [← hsegEq]
    intro y hy
    have hsource : (a - c) +ᵥ y ∈ segment ℝ a d := by
      have hy' : y ∈ (c - a) +ᵥ segment ℝ a d := by
        exact hy
      have htemp : (c - a) +ᵥ ((a - c) +ᵥ y) ∈
          (c - a) +ᵥ segment ℝ a d := by
        simpa [vadd_eq_add, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy'
      exact vadd_mem_vadd_set_iff.mp htemp
    have hsourceFront : (a - c) +ᵥ y ∈ frontier K.support := hsegment (hshort hsource)
    have hEq := hball (hballShort hsource)
    have htarget : (a - c) +ᵥ y ∈ (a - c) +ᵥ frontier M.support := hEq.mp hsourceFront
    exact vadd_mem_vadd_set_iff.mp htarget
  have hne : c ≠ c + t • (b - a) := by
    intro h
    have hvec : t • (b - a) = 0 := by
      have h' : c + 0 = c + t • (b - a) := by simpa using h
      exact (add_left_cancel h').symm
    rcases smul_eq_zero.mp hvec with htzero | habzero
    · exact (ne_of_gt ht) htzero
    · exact hab (sub_eq_zero.mp habzero).symm
  have hdir : Submodule.span ℝ ({(c + t • (b - a)) - c} : Set Plane) =
      Submodule.span ℝ ({b - a} : Set Plane) := by
    have hdiff : (c + t • (b - a)) - c = t • (b - a) := by abel
    rw [hdiff]
    simpa using (Submodule.span_singleton_smul_eq
      (isUnit_iff_ne_zero.mpr (ne_of_gt ht)) (b - a))
  exact ⟨c, c + t • (b - a), hne, htranslated, hdir.symm⟩


private theorem decoration_support_bound (K : PolygonalRegion) (W : Finset Plane)
    (hW : Decorates K W) (B : ℝ) (hB : ∀ w ∈ W, ‖w‖ ≤ B) :
    K.support ⊆ Metric.closedBall 0 B := by
  obtain ⟨A, hA⟩ := hW
  intro x hx
  rw [← A.sUnion_eq] at hx
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx
  have htri := A.isTriangle t ht
  have hfinite : (t.extremePoints ℝ).Finite := by
    obtain ⟨a, b, c, _, rfl⟩ := htri
    exact (Set.toFinite ({a, b, c} : Set Plane)).subset extremePoints_convexHull_subset
  have hconvex : Convex ℝ t := by
    obtain ⟨a, b, c, _, rfl⟩ := htri
    exact convex_convexHull ℝ _
  have hhull := closure_convexHull_extremePoints htri.isCompact hconvex
  rw [hfinite.isClosed_convexHull ℝ |>.closure_eq] at hhull
  have hsub : t ⊆ Metric.closedBall 0 B := by
    rw [← hhull]
    apply convexHull_min ?_ (convex_closedBall (0 : Plane) B)
    intro w hw
    simpa [Metric.mem_closedBall, dist_eq_norm] using hB w (hA t ht hw)
  exact hsub hxt

private theorem decoration_boundary_length (K : PolygonalRegion) (W : Finset Plane)
    (hW : Decorates K W) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ w ∈ W, ‖w‖ ≤ B) :
    ∃ E : Finset (Plane × Plane),
      frontier K.support = ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
      (∑ e ∈ E, dist e.1 e.2) ≤ (W.card : ℝ)^2 * (2*B) := by
  classical
  obtain ⟨E, hE, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  have hvertices := decorates_intrinsicVertices K W hW
  have hsub : E ⊆ W ×ˢ W := by
    intro e he
    exact Finset.mem_product.mpr ⟨hvertices (hE e he).2.1, hvertices (hE e he).2.2.1⟩
  have hcard : E.card ≤ W.card * W.card := by
    simpa only [Finset.card_product] using Finset.card_le_card hsub
  have hcardR : (E.card : ℝ) ≤ (W.card : ℝ)^2 := by
    exact_mod_cast (by simpa only [pow_two] using hcard)
  refine ⟨E, hfront, ?_⟩
  calc
    (∑ e ∈ E, dist e.1 e.2) ≤ ∑ e ∈ E, (2*B) := by
      apply Finset.sum_le_sum
      intro e he
      have h₁ := hbound e.1 (hvertices (hE e he).2.1)
      have h₂ := hbound e.2 (hvertices (hE e he).2.2.1)
      have hd := dist_triangle e.1 (0 : Plane) e.2
      simp only [dist_zero_right, dist_zero_left] at hd
      linarith
    _ = (E.card : ℝ) * (2*B) := by simp
    _ ≤ (W.card : ℝ)^2 * (2*B) := mul_le_mul_of_nonneg_right hcardR (by positivity)

private theorem boundaryDirection_has_intrinsicEdge (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (hδ : Tiling.Polygonal.HasBoundaryDirection K δ) :
    ∃ a b : Plane, a ≠ b ∧ a ∈ Tiling.vertexSet K.support ∧
      b ∈ Tiling.vertexSet K.support ∧ segment ℝ a b ⊆ frontier K.support ∧
      δ = Submodule.span ℝ ({b-a} : Set Plane) := by
  obtain ⟨a, b, hab, hs, hspan⟩ := hδ
  obtain ⟨E, hE, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  obtain ⟨e, he, hdir⟩ := finiteBoundaryCover_contains_direction E
    (fun e he => (hE e he).1) a b hab (hfront ▸ hs)
  exact ⟨e.1, e.2, (hE e he).1, (hE e he).2.1, (hE e he).2.2.1,
    (hE e he).2.2.2, hspan.trans hdir.symm⟩

private theorem locally_equal_closures {s t : Set Plane} {x : Plane}
    (h : s =ᶠ[𝓝 x] t) : closure s =ᶠ[𝓝 x] closure t := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  apply propext
  change y ∈ closure s ↔ y ∈ closure t
  have hn : 𝓝[s] y = 𝓝[t] y := nhdsWithin_eq_iff_eventuallyEq.mpr hy
  rw [mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhdsWithin_neBot, hn]

private theorem locally_equal_frontiers {s t : Set Plane} {x : Plane}
    (h : s =ᶠ[𝓝 x] t) : frontier s =ᶠ[𝓝 x] frontier t := by
  filter_upwards [h.eventuallyEq_nhds, locally_equal_closures h] with y hy hcl
  apply propext
  change (y ∈ closure s ∧ y ∉ interior s) ↔ (y ∈ closure t ∧ y ∉ interior t)
  exact and_congr (iff_of_eq hcl) (not_congr hy.mem_interior_iff)

private theorem sameOpenGerm_frontierSupport (K M : PolygonalRegion) (a c : Plane)
    (h : Tiling.Polygonal.SameGermAt K.openCarrier a M.openCarrier c) :
    frontier K.support =ᶠ[𝓝 a] ((a-c) +ᵥ frontier M.support) := by
  unfold Tiling.Polygonal.SameGermAt at h
  have hs : K.support =ᶠ[𝓝 a] ((a-c) +ᵥ M.support) := by
    simpa only [PolygonalRegion.openCarrier, closure_vadd,
      K.isPolygonal.closure_interior, M.isPolygonal.closure_interior] using locally_equal_closures h
  have hf := locally_equal_frontiers hs
  have hv : frontier ((a-c) +ᵥ M.support) = (a-c) +ᵥ frontier M.support :=
    ((Homeomorph.addLeft (a-c)).image_frontier M.support).symm
  simpa only [hv] using hf

private theorem sameGermAt_symm {s t : Set Plane} {a c : Plane}
    (h : Tiling.Polygonal.SameGermAt s a t c) :
    Tiling.Polygonal.SameGermAt t c s a := by
  unfold Tiling.Polygonal.SameGermAt at h ⊢
  have ht : Tendsto (fun y : Plane => (a-c)+y) (𝓝 c) (𝓝 a) := by
    have hc : Continuous (fun y : Plane => (a-c)+y) := continuous_const.add continuous_id
    have htc : Tendsto (fun y : Plane => (a-c)+y) (𝓝 c) (𝓝 ((a-c)+c)) := hc.continuousAt
    simpa only [sub_add_cancel] using htc
  filter_upwards [ht.eventually h] with y hy
  apply propext
  change y ∈ t ↔ y ∈ (c-a) +ᵥ s
  have hy' : (a-c)+y ∈ s ↔ y ∈ t := by
    have hmem : ((a-c)+y ∈ s) = ((a-c)+y ∈ (a-c) +ᵥ t) := hy
    simpa only [← vadd_eq_add, vadd_mem_vadd_set_iff] using iff_of_eq hmem
  constructor
  · intro hyt
    refine Set.mem_vadd_set.mpr ⟨(a-c)+y, hy'.mpr hyt, ?_⟩
    change (c-a)+((a-c)+y) = y
    abel
  · intro hys
    obtain ⟨z, hz, heq⟩ := Set.mem_vadd_set.mp hys
    apply hy'.mp
    have hz' : (a-c)+y = z := by
      rw [← heq]
      change (a-c)+((c-a)+z) = z
      abel
    simpa only [hz'] using hz

private theorem decoratedGerms_boundaryDirections (K M : PolygonalRegion)
    (W : Finset Plane) (f : Plane → Plane)
    (hK : Decorates K W) (hM : Decorates M (W.image f))
    (hg : ∀ v ∈ W, Tiling.Polygonal.SameGermAt K.openCarrier v M.openCarrier (f v)) :
    ∀ δ : Submodule ℝ Plane,
      Tiling.Polygonal.HasBoundaryDirection M δ ↔ Tiling.Polygonal.HasBoundaryDirection K δ := by
  intro δ
  constructor
  · intro hδ
    obtain ⟨a, b, hab, ha, _, hs, rfl⟩ := boundaryDirection_has_intrinsicEdge M δ hδ
    have haW := decorates_intrinsicVertices M (W.image f) hM ha
    obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp haW
    have hlocal := sameOpenGerm_frontierSupport M K a v
      (hfv ▸ sameGermAt_symm (hg v hv))
    exact sameFrontierGerm_transfers_boundary_direction M K a b v hab hs hlocal
  · intro hδ
    obtain ⟨a, b, hab, ha, _, hs, rfl⟩ := boundaryDirection_has_intrinsicEdge K δ hδ
    have haW := decorates_intrinsicVertices K W hK ha
    exact sameFrontierGerm_transfers_boundary_direction K M a b (f a) hab hs
      (sameOpenGerm_frontierSupport K M a (f a) (hg a haW))

theorem rationalPolygon_construction :
  ∀ K : PolygonalRegion, Tiling.RationalSlopes.HasRationalSlopes K →
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
      ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
      ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
        ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
          ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
            Tiling.IsRational Kφ.support ∧ Tiling.RationalSlopes.HasRationalSlopes Kφ ∧
            Decorates Kφ (W.image (deformPoint φ)) ∧
            (∀ v ∈ W,
              Tiling.Polygonal.SameGermAt K.openCarrier v Kφ.openCarrier (deformPoint φ v)) := by
  intro K hK
  obtain ⟨P, hP, W, hW, h0, F, ε, hε, htarget⟩ := rationalPolygon_coreConstruction K hK
  refine ⟨P, hP, W, hW, h0, F, ε, hε, ?_⟩
  intro φ hφ
  obtain ⟨Kφ, hs, hr, hd, hg⟩ := htarget φ hφ
  exact ⟨Kφ, hs, hr, rationalPolygon_hasRationalSlopes Kφ hr, hd, hg⟩

/-- Fixed finite boundary data supplies uniform size/length bounds before φ is selected.
The actual boundary directions, not arbitrary triangulation diagonals, are preserved. -/
theorem rationalPolygon_uniformBoundaryControl :
  ∀ K : PolygonalRegion, Tiling.RationalSlopes.HasRationalSlopes K →
    ∃ P : PolyhedralCode, polyhedralSupport P = K.support ∧
      ∃ W : Finset Plane, Decorates K W ∧ 0 ∈ W ∧
        ∃ B L : ℝ, 0 < B ∧ 0 < L ∧
          ∃ F : Finset ℝ, ∃ ε : ℝ, 0 < ε ∧
            ∀ φ : ℝ →ₗ[ℚ] ℚ, IsFiniteApproximation F ε φ →
              ∃ Kφ : PolygonalRegion, Kφ.support = deformedPolyhedralSupport P φ ∧
                Kφ.support ⊆ Metric.closedBall 0 B ∧
                (∃ E : Finset (Plane × Plane),
                  frontier Kφ.support = ⋃ e ∈ E, segment ℝ e.1 e.2 ∧
                  (∑ e ∈ E, dist e.1 e.2) ≤ L) ∧
                ∀ δ : Submodule ℝ Plane,
                  Tiling.Polygonal.HasBoundaryDirection Kφ δ ↔
                    Tiling.Polygonal.HasBoundaryDirection K δ := by
  classical
  intro K hK
  obtain ⟨P, hP, W, hW, h0, F₁, ε₁, hε₁, htarget⟩ := rationalPolygon_construction K hK
  obtain ⟨F₂, B, hB, hbound⟩ := finiteDecoration_uniformImageBound W
  let L : ℝ := (W.card : ℝ)^2 * (2*B) + 1
  refine ⟨P, hP, W, hW, h0, B, L, hB, by dsimp [L]; positivity,
    F₁ ∪ F₂, min ε₁ 1, lt_min hε₁ zero_lt_one, ?_⟩
  intro φ hφ
  have hφ₁ : IsFiniteApproximation F₁ ε₁ φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inl hx))).trans_le (min_le_left _ _)⟩
  have hφ₂ : IsFiniteApproximation F₂ 1 φ := ⟨hφ.1, fun x hx =>
    (hφ.2 x (Finset.mem_union.mpr (Or.inr hx))).trans_le (min_le_right _ _)⟩
  obtain ⟨Kφ, hs, _, _, hd, hg⟩ := htarget φ hφ₁
  have hWbound : ∀ w ∈ W.image (deformPoint φ), ‖w‖ ≤ B := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    exact hbound φ hφ₂ v hv
  obtain ⟨E, hfront, hlength⟩ := decoration_boundary_length Kφ
    (W.image (deformPoint φ)) hd B hB.le hWbound
  have hcard : ((W.image (deformPoint φ)).card : ℝ) ≤ (W.card : ℝ) := by
    exact_mod_cast Finset.card_image_le
  have hcardsq : ((W.image (deformPoint φ)).card : ℝ)^2 ≤ (W.card : ℝ)^2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (W.image (deformPoint φ)).card]
  refine ⟨Kφ, hs, decoration_support_bound Kφ (W.image (deformPoint φ)) hd B hWbound,
    ⟨E, hfront, ?_⟩, decoratedGerms_boundaryDirections K Kφ W (deformPoint φ) hW hd hg⟩
  have hm := mul_le_mul_of_nonneg_right hcardsq (show 0 ≤ 2*B by positivity)
  dsimp [L]
  linarith


end Tiling.RationalSlopes.Approximation

