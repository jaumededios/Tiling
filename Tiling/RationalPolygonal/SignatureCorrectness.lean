import Tiling.RationalPolygonal.SignatureCompiler
import Tiling.RationalPolygonal.Raster

set_option autoImplicit false
set_option warningAsError true
set_option linter.style.header false

open Function MeasureTheory Set

namespace Tiling.RationalPolygonal.Raw.SemanticBridge

/-- Real evaluation of an integer affine form on the complex model of the real plane. -/
def planeEval (A B C : ℤ) (u : Plane) : ℝ :=
  (A : ℝ) * u.re + (B : ℝ) * u.im + (C : ℝ)

/-- The real affine line cut out by an integer affine form. -/
def lineZeroSet (A B C : ℤ) : Set Plane :=
  {u | planeEval A B C u = 0}

theorem continuous_planeEval (A B C : ℤ) :
    Continuous (planeEval A B C) := by
  unfold planeEval
  fun_prop

theorem isClosed_lineZeroSet (A B C : ℤ) :
    IsClosed (lineZeroSet A B C) := by
  exact isClosed_singleton.preimage (continuous_planeEval A B C)

theorem convex_lineZeroSet (A B C : ℤ) :
    Convex ℝ (lineZeroSet A B C) := by
  intro x hx y hy a b ha hb hab
  change planeEval A B C (a • x + b • y) = 0
  change planeEval A B C x = 0 at hx
  change planeEval A B C y = 0 at hy
  simp only [planeEval, Complex.add_re, Complex.smul_re, Complex.add_im, Complex.smul_im,
    smul_eq_mul] at hx hy ⊢
  linear_combination a * hx + b * hy - (C : ℝ) * hab

theorem interior_lineZeroSet_eq_empty {A B C : ℤ}
    (hnonzero : A ≠ 0 ∨ B ≠ 0) :
    interior (lineZeroSet A B C) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  rintro ⟨u, hu⟩
  rw [mem_interior_iff_mem_nhds] at hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  have hu0 : planeEval A B C u = 0 := by
    have humem : u ∈ lineZeroSet A B C := mem_of_mem_nhds hu
    exact humem
  rcases hnonzero with hA | hB
  · let v : Plane := u + (ε / 2 : ℝ)
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, Complex.dist_eq]
      dsimp only [v]
      rw [show u + (ε / 2 : ℝ) - u = (ε / 2 : ℝ) by ring]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (half_pos hε)]
      linarith
    have hv0 : planeEval A B C v = 0 := hball hvball
    have hAr : (A : ℝ) ≠ 0 := by exact_mod_cast hA
    have hε2 : (ε / 2 : ℝ) ≠ 0 := (half_pos hε).ne'
    have heval : planeEval A B C v = planeEval A B C u + (A : ℝ) * (ε / 2) := by
      simp only [planeEval, v, Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, add_zero]
      ring
    rw [heval, hu0, zero_add] at hv0
    exact (mul_ne_zero hAr hε2) hv0
  · let v : Plane := u + Complex.I * (ε / 2 : ℝ)
    have hvball : v ∈ Metric.ball u ε := by
      rw [Metric.mem_ball, Complex.dist_eq]
      dsimp only [v]
      rw [show u + Complex.I * (ε / 2 : ℝ) - u = Complex.I * (ε / 2 : ℝ) by ring]
      rw [norm_mul]
      rw [Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    have hv0 : planeEval A B C v = 0 := hball hvball
    have hBr : (B : ℝ) ≠ 0 := by exact_mod_cast hB
    have hε2 : (ε / 2 : ℝ) ≠ 0 := (half_pos hε).ne'
    have heval : planeEval A B C v = planeEval A B C u + (B : ℝ) * (ε / 2) := by
      simp only [planeEval, v, Complex.add_re, Complex.mul_re, Complex.add_im,
        Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, zero_mul, Complex.ofReal_im, Complex.I_im, mul_zero,
        sub_zero, add_zero, one_mul]
      ring
    rw [heval, hu0, zero_add] at hv0
    exact (mul_ne_zero hBr hε2) hv0

/-- Every genuine real affine line has zero planar Lebesgue measure. -/
theorem volume_lineZeroSet {A B C : ℤ} (hnonzero : A ≠ 0 ∨ B ≠ 0) :
    volume (lineZeroSet A B C) = 0 := by
  have hfrontier : frontier (lineZeroSet A B C) = lineZeroSet A B C := by
    rw [frontier, (isClosed_lineZeroSet A B C).closure_eq,
      interior_lineZeroSet_eq_empty hnonzero, sdiff_empty]
  rw [← hfrontier]
  exact (convex_lineZeroSet A B C).addHaar_frontier volume

/-- Rational pairs embedded in the real plane through the standard real-pair model. -/
noncomputable def rationalPlanePoint (p : ℚ × ℚ) : Plane :=
  Complex.equivRealProdCLM.symm ((p.1 : ℝ), (p.2 : ℝ))

@[simp] theorem rationalPlanePoint_eq (p : ℚ × ℚ) :
    rationalPlanePoint p = (p.1 : ℝ) + (p.2 : ℝ) * Complex.I := by
  exact Complex.equivRealProdCLM_symm_apply _

/-- Rational pairs embedded in the real plane are dense. -/
theorem denseRange_rationalPlanePoint : DenseRange rationalPlanePoint := by
  let castPair : ℚ × ℚ → ℝ × ℝ :=
    Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  have hcast : DenseRange castPair :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hsymm : DenseRange (Complex.equivRealProdCLM.symm : ℝ × ℝ → Plane) :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  have hcomp := hsymm.comp hcast Complex.equivRealProdCLM.symm.continuous
  change DenseRange (Complex.equivRealProdCLM.symm ∘ castPair) at hcomp
  change DenseRange (Complex.equivRealProdCLM.symm ∘ castPair)
  exact hcomp

/-- Every nonempty open subset of the real plane contains a rational-coordinate point. -/
theorem exists_rational_point_mem {U : Set Plane} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ p : ℚ × ℚ, rationalPlanePoint p ∈ U :=
  denseRange_rationalPlanePoint.exists_mem_open hU hne

end Tiling.RationalPolygonal.Raw.SemanticBridge

namespace Tiling.RationalPolygonal.Raw.Compiler

open LinearFeasibility
open SemanticBridge

private theorem foldl_min_le_acc (xs : List ℤ) (a : ℤ) : xs.foldl min a ≤ a := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
      exact (ih (min a b)).trans (min_le_left a b)

private theorem foldl_min_le_of_mem {xs : List ℤ} {x : ℤ} (hx : x ∈ xs) (a : ℤ) :
    xs.foldl min a ≤ x := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons b bs ih =>
      simp only [List.mem_cons] at hx
      rw [List.foldl_cons]
      rcases hx with rfl | hx
      · exact (foldl_min_le_acc bs (min a x)).trans (min_le_right a x)
      · exact ih hx (min a b)

private theorem le_foldl_max_acc (xs : List ℤ) (a : ℤ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
      exact (le_max_left a b).trans (ih (max a b))

private theorem le_foldl_max_of_mem {xs : List ℤ} {x : ℤ} (hx : x ∈ xs) (a : ℤ) :
    x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons b bs ih =>
      simp only [List.mem_cons] at hx
      rw [List.foldl_cons]
      rcases hx with rfl | hx
      · exact (le_max_right a x).trans (le_foldl_max_acc bs (max a x))
      · exact ih hx (max a b)

private theorem convex_re_Icc (lo hi : ℝ) :
    Convex ℝ {p : Plane | lo ≤ p.re ∧ p.re ≤ hi} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change lo ≤ x.re ∧ x.re ≤ hi at hx
  change lo ≤ y.re ∧ y.re ≤ hi at hy
  change lo ≤ (a • x + b • y).re ∧ (a • x + b • y).re ≤ hi
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  constructor
  · calc
      lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x.re + b * y.re :=
        add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc
      a * x.re + b * y.re ≤ a * hi + b * hi :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = hi := by rw [← add_mul, hab, one_mul]

private theorem convex_im_Icc (lo hi : ℝ) :
    Convex ℝ {p : Plane | lo ≤ p.im ∧ p.im ≤ hi} := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  change lo ≤ x.im ∧ x.im ≤ hi at hx
  change lo ≤ y.im ∧ y.im ≤ hi at hy
  change lo ≤ (a • x + b • y).im ∧ (a • x + b • y).im ≤ hi
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  constructor
  · calc
      lo = a * lo + b * lo := by rw [← add_mul, hab, one_mul]
      _ ≤ a * x.im + b * y.im :=
        add_le_add (mul_le_mul_of_nonneg_left hx.1 ha) (mul_le_mul_of_nonneg_left hy.1 hb)
  · calc
      a * x.im + b * y.im ≤ a * hi + b * hi :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = hi := by rw [← add_mul, hab, one_mul]

private theorem ZTriangle.re_bounds_of_mem_carrier {t : ZTriangle} {p : Plane} {lo hi : ℤ}
    (haLo : lo ≤ t.a.x) (hbLo : lo ≤ t.b.x) (hcLo : lo ≤ t.c.x)
    (haHi : t.a.x ≤ hi) (hbHi : t.b.x ≤ hi) (hcHi : t.c.x ≤ hi)
    (hp : p ∈ t.carrier) :
    (lo : ℝ) ≤ p.re ∧ p.re ≤ (hi : ℝ) := by
  apply convexHull_min _ (convex_re_Icc (lo : ℝ) (hi : ℝ)) hp
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · have h : (lo : ℝ) ≤ (t.a.x : ℝ) ∧ (t.a.x : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast haLo
      · exact_mod_cast haHi
    simpa [ZPoint.toPlane] using h
  · have h : (lo : ℝ) ≤ (t.b.x : ℝ) ∧ (t.b.x : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast hbLo
      · exact_mod_cast hbHi
    simpa [ZPoint.toPlane] using h
  · have h : (lo : ℝ) ≤ (t.c.x : ℝ) ∧ (t.c.x : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast hcLo
      · exact_mod_cast hcHi
    simpa [ZPoint.toPlane] using h

private theorem ZTriangle.im_bounds_of_mem_carrier {t : ZTriangle} {p : Plane} {lo hi : ℤ}
    (haLo : lo ≤ t.a.y) (hbLo : lo ≤ t.b.y) (hcLo : lo ≤ t.c.y)
    (haHi : t.a.y ≤ hi) (hbHi : t.b.y ≤ hi) (hcHi : t.c.y ≤ hi)
    (hp : p ∈ t.carrier) :
    (lo : ℝ) ≤ p.im ∧ p.im ≤ (hi : ℝ) := by
  apply convexHull_min _ (convex_im_Icc (lo : ℝ) (hi : ℝ)) hp
  intro q hq
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
  rcases hq with rfl | rfl | rfl
  · have h : (lo : ℝ) ≤ (t.a.y : ℝ) ∧ (t.a.y : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast haLo
      · exact_mod_cast haHi
    simpa [ZPoint.toPlane] using h
  · have h : (lo : ℝ) ≤ (t.b.y : ℝ) ∧ (t.b.y : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast hbLo
      · exact_mod_cast hbHi
    simpa [ZPoint.toPlane] using h
  · have h : (lo : ℝ) ≤ (t.c.y : ℝ) ∧ (t.c.y : ℝ) ≤ (hi : ℝ) := by
      constructor
      · exact_mod_cast hcLo
      · exact_mod_cast hcHi
    simpa [ZPoint.toPlane] using h

/-- Every point in a listed triangle lies between the extrema used to construct its offset
window. -/
theorem ZTriangle.coordinate_bounds_of_mem {ts : List ZTriangle} {t : ZTriangle} {p : Plane}
    (ht : t ∈ ts) (hp : p ∈ t.carrier) :
    ((minCoord (xCoordinates ts) : ℤ) : ℝ) ≤ p.re ∧
      p.re ≤ ((maxCoord (xCoordinates ts) : ℤ) : ℝ) ∧
      ((minCoord (yCoordinates ts) : ℤ) : ℝ) ≤ p.im ∧
      p.im ≤ ((maxCoord (yCoordinates ts) : ℤ) : ℝ) := by
  have hax : t.a.x ∈ xCoordinates ts := by
    simp only [xCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hbx : t.b.x ∈ xCoordinates ts := by
    simp only [xCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hcx : t.c.x ∈ xCoordinates ts := by
    simp only [xCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hay : t.a.y ∈ yCoordinates ts := by
    simp only [yCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hby : t.b.y ∈ yCoordinates ts := by
    simp only [yCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hcy : t.c.y ∈ yCoordinates ts := by
    simp only [yCoordinates, List.mem_flatMap]
    exact ⟨t, ht, by simp⟩
  have hx := ZTriangle.re_bounds_of_mem_carrier
    (foldl_min_le_of_mem hax 0) (foldl_min_le_of_mem hbx 0)
    (foldl_min_le_of_mem hcx 0) (le_foldl_max_of_mem hax 0)
    (le_foldl_max_of_mem hbx 0) (le_foldl_max_of_mem hcx 0) hp
  have hy := ZTriangle.im_bounds_of_mem_carrier
    (foldl_min_le_of_mem hay 0) (foldl_min_le_of_mem hby 0)
    (foldl_min_le_of_mem hcy 0) (le_foldl_max_of_mem hay 0)
    (le_foldl_max_of_mem hby 0) (le_foldl_max_of_mem hcy 0) hp
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

/-- Membership in the compiler's rectangular offset window, stated as four coordinate bounds. -/
theorem mem_offsetWindow_iff {ts : List ZTriangle} {z : ZPoint} :
    z ∈ offsetWindow ts ↔
      minCoord (xCoordinates ts) - 1 ≤ z.x ∧
      z.x ≤ maxCoord (xCoordinates ts) ∧
      minCoord (yCoordinates ts) - 1 ≤ z.y ∧
      z.y ≤ maxCoord (yCoordinates ts) := by
  simp only [offsetWindow, List.mem_flatMap, List.mem_map, mem_intRange_iff]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    cases hxy
    exact ⟨hx.1, hx.2, hy.1, hy.2⟩
  · rintro ⟨hxLo, hxHi, hyLo, hyHi⟩
    exact ⟨z.x, ⟨hxLo, hxHi⟩, z.y, ⟨hyLo, hyHi⟩, rfl⟩

private theorem intRange_nodup (lo hi : ℤ) : (intRange lo hi).Nodup := by
  simp only [intRange]
  split
  · apply List.Nodup.map _ List.nodup_range
    intro n m h
    have hcast : (n : ℤ) = (m : ℤ) := add_left_cancel h
    exact_mod_cast hcast
  · exact List.nodup_nil

/-- The compiler's rectangular offset window contains no duplicate lattice points. -/
theorem offsetWindow_nodup (ts : List ZTriangle) : (offsetWindow ts).Nodup := by
  rw [offsetWindow, List.nodup_flatMap]
  constructor
  · intro x hx
    exact (intRange_nodup _ _).map fun y y' h => by
      injection h
  · exact (intRange_nodup _ _).imp fun {x x'} hxx' p hp hp' => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
      obtain ⟨y', hy', hEq⟩ := List.mem_map.mp hp'
      exact hxx' (congrArg ZPoint.x hEq.symm)

private theorem add_integerPoint_toIntegerPlane_re (u : Plane) (z : ZPoint) :
    (u + integerPoint z.toIntegerPlane).re = u.re + z.x := by
  simp [ZPoint.toIntegerPlane]

private theorem add_integerPoint_toIntegerPlane_im (u : Plane) (z : ZPoint) :
    (u + integerPoint z.toIntegerPlane).im = u.im + z.y := by
  simp [ZPoint.toIntegerPlane]

/-- Any translate offset whose copy meets the triangle union over the closed unit cell belongs to
the finite padded window. Since the open unit cell is contained in the closed one, this is also the
completeness statement needed for strict arrangement samples. -/
theorem mem_offsetWindow_of_add_mem_triangleUnion {ts : List ZTriangle} {u : Plane} {z : ZPoint}
    (huRe : u.re ∈ Set.Icc (0 : ℝ) 1) (huIm : u.im ∈ Set.Icc (0 : ℝ) 1)
    (hmem : u + integerPoint z.toIntegerPlane ∈ ⋃ t ∈ ts.toFinset, t.carrier) :
    z ∈ offsetWindow ts := by
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨t, ht, hp⟩ := hmem
  have htList : t ∈ ts := by simpa only [List.mem_toFinset] using ht
  obtain ⟨hxLo, hxHi, hyLo, hyHi⟩ := ZTriangle.coordinate_bounds_of_mem htList hp
  rw [add_integerPoint_toIntegerPlane_re] at hxLo hxHi
  rw [add_integerPoint_toIntegerPlane_im] at hyLo hyHi
  rw [mem_offsetWindow_iff]
  constructor
  · have hreal : ((minCoord (xCoordinates ts) - 1 : ℤ) : ℝ) ≤ (z.x : ℝ) := by
      rw [Int.cast_sub, Int.cast_one]
      linarith [huRe.2]
    exact_mod_cast hreal
  · constructor
    · have hreal : (z.x : ℝ) ≤ (maxCoord (xCoordinates ts) : ℝ) := by
        linarith [huRe.1]
      exact_mod_cast hreal
    · constructor
      · have hreal : ((minCoord (yCoordinates ts) - 1 : ℤ) : ℝ) ≤ (z.y : ℝ) := by
          rw [Int.cast_sub, Int.cast_one]
          linarith [huIm.2]
        exact_mod_cast hreal
      · have hreal : (z.y : ℝ) ≤ (maxCoord (yCoordinates ts) : ℝ) := by
          linarith [huIm.1]
        exact_mod_cast hreal

/-- An offset outside the padded window cannot meet the triangle union over the closed unit cell. -/
theorem add_not_mem_triangleUnion_of_not_mem_offsetWindow {ts : List ZTriangle} {u : Plane}
    {z : ZPoint} (huRe : u.re ∈ Set.Icc (0 : ℝ) 1) (huIm : u.im ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∉ offsetWindow ts) :
    u + integerPoint z.toIntegerPlane ∉ ⋃ t ∈ ts.toFinset, t.carrier := by
  intro hmem
  exact hz (mem_offsetWindow_of_add_mem_triangleUnion huRe huIm hmem)

/-- The coordinate-free closed-unit-cell form of offset-window completeness. -/
theorem mem_offsetWindow_of_add_mem_triangleUnion_closedUnitCell {ts : List ZTriangle}
    {u : Plane} {z : ZPoint} (hu : u ∈ closedUnitCell)
    (hmem : u + integerPoint z.toIntegerPlane ∈ ⋃ t ∈ ts.toFinset, t.carrier) :
    z ∈ offsetWindow ts := by
  rw [closedUnitCell] at hu
  change (u.re, u.im) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 at hu
  exact mem_offsetWindow_of_add_mem_triangleUnion hu.1 hu.2 hmem

/-- The coordinate-free contrapositive of offset-window completeness. -/
theorem add_not_mem_triangleUnion_of_not_mem_offsetWindow_closedUnitCell
    {ts : List ZTriangle} {u : Plane} {z : ZPoint} (hu : u ∈ closedUnitCell)
    (hz : z ∉ offsetWindow ts) :
    u + integerPoint z.toIntegerPlane ∉ ⋃ t ∈ ts.toFinset, t.carrier := by
  intro hmem
  exact hz (mem_offsetWindow_of_add_mem_triangleUnion_closedUnitCell hu hmem)

/-- The support of the normalized semantic region is the union of the compiler's triangles. -/
theorem normalizedRegion_support_eq_list_iUnion (P : Code.Input) :
    P.rationalPolygonalRegion.normalizedRegion.support =
      ⋃ t ∈ (normalizedTriangles P).toFinset, t.carrier := by
  rw [RationalPolygonalRegion.normalizedRegion_support,
    P.normalizedSupport_eq_iUnion]
  ext x
  simp [normalizedTriangles, Code.triangleFinset]

/-- A normalized translate meeting semantic support over the closed unit square is in the window. -/
theorem mem_offsetWindow_of_add_mem_normalizedSupport (P : Code.Input) {u : Plane} {z : ZPoint}
    (huRe : u.re ∈ Set.Icc (0 : ℝ) 1) (huIm : u.im ∈ Set.Icc (0 : ℝ) 1)
    (hmem : u + integerPoint z.toIntegerPlane ∈
      P.rationalPolygonalRegion.normalizedRegion.support) :
    z ∈ offsetWindow (normalizedTriangles P) := by
  rw [normalizedRegion_support_eq_list_iUnion] at hmem
  exact mem_offsetWindow_of_add_mem_triangleUnion huRe huIm hmem

/-- A normalized offset outside the compiler window cannot meet support over the unit square. -/
theorem add_not_mem_normalizedSupport_of_not_mem_offsetWindow (P : Code.Input) {u : Plane}
    {z : ZPoint} (huRe : u.re ∈ Set.Icc (0 : ℝ) 1) (huIm : u.im ∈ Set.Icc (0 : ℝ) 1)
    (hz : z ∉ offsetWindow (normalizedTriangles P)) :
    u + integerPoint z.toIntegerPlane ∉
      P.rationalPolygonalRegion.normalizedRegion.support := by
  rw [normalizedRegion_support_eq_list_iUnion]
  exact add_not_mem_triangleUnion_of_not_mem_offsetWindow huRe huIm hz

/-- The closed-unit-cell form of normalized offset-window completeness. -/
theorem mem_offsetWindow_of_add_mem_normalizedSupport_closedUnitCell (P : Code.Input)
    {u : Plane} {z : ZPoint} (hu : u ∈ closedUnitCell)
    (hmem : u + integerPoint z.toIntegerPlane ∈
      P.rationalPolygonalRegion.normalizedRegion.support) :
    z ∈ offsetWindow (normalizedTriangles P) := by
  rw [normalizedRegion_support_eq_list_iUnion] at hmem
  exact mem_offsetWindow_of_add_mem_triangleUnion_closedUnitCell hu hmem

/-- The real zero set of one compiler arrangement line. -/
def ZLine.zeroSet (l : ZLine) : Set Plane :=
  lineZeroSet l.A l.B l.C

theorem ZLine.volume_zeroSet (l : ZLine) (hnonzero : l.A ≠ 0 ∨ l.B ≠ 0) :
    volume l.zeroSet = 0 :=
  volume_lineZeroSet hnonzero

/-- The finite exceptional set formed by a list of arrangement lines. -/
def exceptionalSet (ls : List ZLine) : Set Plane :=
  ⋃ l ∈ ls.toFinset, l.zeroSet

theorem volume_exceptionalSet (ls : List ZLine)
    (hnonzero : ∀ l ∈ ls, l.A ≠ 0 ∨ l.B ≠ 0) :
    volume (exceptionalSet ls) = 0 := by
  unfold exceptionalSet
  apply measure_biUnion_null_iff ls.toFinset.countable_toSet |>.2
  intro l hl
  exact l.volume_zeroSet (hnonzero l (List.mem_toFinset.mp hl))

/-- A nontrivial segment gives a genuine arrangement line. -/
theorem edgeLine_coefficients_ne_zero {z p q : ZPoint} (hpq : p ≠ q) :
    (edgeLine z p q).A ≠ 0 ∨ (edgeLine z p q).B ≠ 0 := by
  contrapose! hpq
  cases p with
  | mk px py =>
      cases q with
      | mk qx qy =>
          simp only [edgeLine] at hpq
          congr <;> omega

/-- Real satisfaction of one strict rational affine inequality. -/
def satisfiesPlane (q : StrictInequality) (u : Plane) : Prop :=
  (q.a : ℝ) * u.re + (q.b : ℝ) * u.im < (q.c : ℝ)

/-- Real realization of a finite strict rational system. -/
def realCell (qs : List StrictInequality) : Set Plane :=
  {u | ∀ q ∈ qs, satisfiesPlane q u}

theorem realCell_nil : realCell [] = Set.univ := by
  ext u
  simp [realCell]

theorem realCell_cons (q : StrictInequality) (qs : List StrictInequality) :
    realCell (q :: qs) = {u | satisfiesPlane q u} ∩ realCell qs := by
  ext u
  simp [realCell]

theorem isOpen_realCell (qs : List StrictInequality) : IsOpen (realCell qs) := by
  induction qs with
  | nil => rw [realCell_nil]; exact isOpen_univ
  | cons q qs ih =>
      rw [realCell_cons]
      apply IsOpen.inter _ ih
      apply isOpen_lt
      · fun_prop
      · fun_prop

theorem satisfiesPlane_sampleToPlane_iff (q : StrictInequality) (p : ℚ × ℚ) :
    satisfiesPlane q (sampleToPlane p) ↔ q.Satisfies p := by
  simp only [satisfiesPlane, sampleToPlane_re, sampleToPlane_im,
    StrictInequality.Satisfies]
  norm_cast

theorem mem_realCell_sampleToPlane_iff (qs : List StrictInequality) (p : ℚ × ℚ) :
    sampleToPlane p ∈ realCell qs ↔ SatisfiesAll qs p := by
  constructor
  · intro h q hq
    exact (satisfiesPlane_sampleToPlane_iff q p).mp (h q hq)
  · intro h q hq
    exact (satisfiesPlane_sampleToPlane_iff q p).mpr (h q hq)

theorem sideConstraint_true_satisfiesPlane_iff (l : ZLine) (u : Plane) :
    satisfiesPlane (sideConstraint true l) u ↔ 0 < l.evalPlane u := by
  simp only [sideConstraint, if_true, satisfiesPlane, ZLine.evalPlane]
  push_cast
  constructor <;> intro h <;> linarith

theorem sideConstraint_false_satisfiesPlane_iff (l : ZLine) (u : Plane) :
    satisfiesPlane (sideConstraint false l) u ↔ l.evalPlane u < 0 := by
  simp only [sideConstraint, Bool.false_eq_true, if_false,
    satisfiesPlane, ZLine.evalPlane]
  push_cast
  constructor <;> intro h <;> linarith

private theorem mem_refineCell_cellOfSystem {l : ZLine} {parent child : SignCell}
    (hchild : child ∈ refineCell l parent) :
    cellOfSystem? (sideConstraint false l :: parent.system) = some child ∨
      cellOfSystem? (sideConstraint true l :: parent.system) = some child := by
  simp only [refineCell, List.mem_filterMap, List.mem_cons] at hchild
  obtain ⟨o, ho, hid⟩ := hchild
  rcases ho with ho | ho
  · subst o
    exact Or.inl hid
  · rcases ho with ho | ho
    · subst o
      exact Or.inr hid
    · simp only [List.not_mem_nil] at ho

theorem mem_refineCell_sound {l : ZLine} {parent child : SignCell}
    (hchild : child ∈ refineCell l parent) :
    SatisfiesAll child.system child.sample := by
  rcases mem_refineCell_cellOfSystem hchild with hfalse | htrue
  · obtain ⟨hsystem, hsat⟩ := cellOfSystem_sound hfalse
    rw [hsystem]
    exact hsat
  · obtain ⟨hsystem, hsat⟩ := cellOfSystem_sound htrue
    rw [hsystem]
    exact hsat

/-- Every child keeps every constraint of its parent. -/
theorem mem_system_of_mem_refineCell {q : StrictInequality} {l : ZLine}
    {parent child : SignCell} (hchild : child ∈ refineCell l parent)
    (hq : q ∈ parent.system) : q ∈ child.system := by
  rcases mem_refineCell_system hchild with hfalse | htrue
  · rw [hfalse]
    exact List.mem_cons_of_mem _ hq
  · rw [htrue]
    exact List.mem_cons_of_mem _ hq

/-- A child carries one of the two strict side constraints for the line just processed. -/
theorem sideConstraint_mem_of_mem_refineCell {l : ZLine} {parent child : SignCell}
    (hchild : child ∈ refineCell l parent) :
    sideConstraint false l ∈ child.system ∨ sideConstraint true l ∈ child.system := by
  rcases mem_refineCell_system hchild with hfalse | htrue
  · exact Or.inl (by simp [hfalse])
  · exact Or.inr (by simp [htrue])

/-- A sign cell strictly controls every arrangement line in the supplied list. -/
def Controls (ls : List ZLine) (cell : SignCell) : Prop :=
  ∀ l ∈ ls, sideConstraint false l ∈ cell.system ∨ sideConstraint true l ∈ cell.system

theorem controls_refineCell {done : List ZLine} {l : ZLine} {parent child : SignCell}
    (hcontrols : Controls done parent) (hchild : child ∈ refineCell l parent) :
    Controls (done ++ [l]) child := by
  intro k hk
  rw [List.mem_append] at hk
  rcases hk with hk | hk
  · rcases hcontrols k hk with hfalse | htrue
    · exact Or.inl (mem_system_of_mem_refineCell hchild hfalse)
    · exact Or.inr (mem_system_of_mem_refineCell hchild htrue)
  · have hkl : k = l := by simpa only [List.mem_singleton] using hk
    subst k
    exact sideConstraint_mem_of_mem_refineCell hchild

theorem controls_refineCells {done : List ZLine} {l : ZLine} {cells : List SignCell}
    (hcontrols : ∀ cell ∈ cells, Controls done cell) :
    ∀ child ∈ refineCells l cells, Controls (done ++ [l]) child := by
  intro child hchild
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨parent, hparent, hrefine⟩ := hchild
  exact controls_refineCell (hcontrols parent hparent) hrefine

theorem refineLines_controls_aux {done todo : List ZLine} {cells : List SignCell}
    (hcontrols : ∀ cell ∈ cells, Controls done cell) :
    ∀ child ∈ refineLines cells todo, Controls (done ++ todo) child := by
  induction todo generalizing done cells with
  | nil => simpa only [refineLines, List.foldl_nil, List.append_nil] using hcontrols
  | cons l todo ih =>
      rw [refineLines, List.foldl_cons]
      intro child hchild
      have hnext := ih (done := done ++ [l])
        (controls_refineCells (l := l) hcontrols) child hchild
      simpa only [List.append_assoc, List.singleton_append] using hnext

/-- Every output cell records a strict side for every processed arrangement line. -/
theorem feasibleSignCells_controls {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) : Controls ls cell := by
  unfold feasibleSignCells at hcell
  split at hcell
  · simp only [List.not_mem_nil] at hcell
  · rename_i base hbase
    have h := refineLines_controls_aux (done := []) (todo := ls) (cells := [base])
      (by intro c hc; simp only [List.mem_singleton] at hc; subst c; intro l hl; simp at hl)
      cell hcell
    simpa only [List.nil_append] using h

theorem refineCells_sound {l : ZLine} {cells : List SignCell}
    : ∀ child ∈ refineCells l cells, SatisfiesAll child.system child.sample := by
  intro child hchild
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨parent, _hparent, hrefine⟩ := hchild
  exact mem_refineCell_sound hrefine

theorem refineLines_sound {cells : List SignCell} {ls : List ZLine}
    (hsound : ∀ cell ∈ cells, SatisfiesAll cell.system cell.sample) :
    ∀ child ∈ refineLines cells ls, SatisfiesAll child.system child.sample := by
  induction ls generalizing cells with
  | nil => simpa only [refineLines, List.foldl_nil] using hsound
  | cons l ls ih =>
      rw [refineLines, List.foldl_cons]
      exact ih refineCells_sound

/-- The real realization of every enumerated feasible cell is open, nonempty, and
positive-volume. -/
theorem feasibleSignCell_open_nonempty_measure_ne_zero {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) :
    IsOpen (realCell cell.system) ∧ (realCell cell.system).Nonempty ∧
      volume (realCell cell.system) ≠ 0 := by
  have hsample : sampleToPlane cell.sample ∈ realCell cell.system :=
    (mem_realCell_sampleToPlane_iff cell.system cell.sample).mpr
      (feasibleSignCells_sound hcell)
  have hopen := isOpen_realCell cell.system
  exact ⟨hopen, ⟨sampleToPlane cell.sample, hsample⟩,
    hopen.measure_ne_zero volume ⟨sampleToPlane cell.sample, hsample⟩⟩

/-- Any two points in one enumerated real cell have the same strict sign at every arrangement
line used to build the cell. -/
theorem evalPlane_pos_iff_of_mem_realCell {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) {u v : Plane}
    (hu : u ∈ realCell cell.system) (hv : v ∈ realCell cell.system)
    {l : ZLine} (hl : l ∈ ls) :
    0 < l.evalPlane u ↔ 0 < l.evalPlane v := by
  rcases feasibleSignCells_controls hcell l hl with hfalse | htrue
  · have huNeg := (sideConstraint_false_satisfiesPlane_iff l u).mp (hu _ hfalse)
    have hvNeg := (sideConstraint_false_satisfiesPlane_iff l v).mp (hv _ hfalse)
    constructor <;> intro h <;> linarith
  · have huPos := (sideConstraint_true_satisfiesPlane_iff l u).mp (hu _ htrue)
    have hvPos := (sideConstraint_true_satisfiesPlane_iff l v).mp (hv _ htrue)
    exact iff_of_true huPos hvPos

/-- Two points in one enumerated cell lie on the same strict side of every processed line. -/
theorem sameStrictSign_of_mem_realCell {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) {u v : Plane}
    (hu : u ∈ realCell cell.system) (hv : v ∈ realCell cell.system)
    {l : ZLine} (hl : l ∈ ls) :
    SameStrictSign (l.evalPlane u) (l.evalPlane v) := by
  rcases feasibleSignCells_controls hcell l hl with hfalse | htrue
  · exact Or.inr ⟨(sideConstraint_false_satisfiesPlane_iff l u).mp (hu _ hfalse),
      (sideConstraint_false_satisfiesPlane_iff l v).mp (hv _ hfalse)⟩
  · exact Or.inl ⟨(sideConstraint_true_satisfiesPlane_iff l u).mp (hu _ htrue),
      (sideConstraint_true_satisfiesPlane_iff l v).mp (hv _ htrue)⟩

/-- A cell system is supported by the unit-square constraints and strict sides of the listed
arrangement lines. -/
def SupportedBy (ls : List ZLine) (cell : SignCell) : Prop :=
  ∀ q ∈ cell.system, q ∈ openUnitSquare ∨
    ∃ l ∈ ls, q = sideConstraint false l ∨ q = sideConstraint true l

theorem supportedBy_refineCell {done : List ZLine} {l : ZLine}
    {parent child : SignCell} (hparent : SupportedBy done parent)
    (hchild : child ∈ refineCell l parent) : SupportedBy (done ++ [l]) child := by
  intro q hq
  rcases mem_refineCell_system hchild with hfalse | htrue
  · rw [hfalse] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inr ⟨l, by simp, Or.inl rfl⟩
    · rcases hparent q hq with hunit | ⟨k, hk, hside⟩
      · exact Or.inl hunit
      · exact Or.inr ⟨k, List.mem_append_left _ hk, hside⟩
  · rw [htrue] at hq
    simp only [List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact Or.inr ⟨l, by simp, Or.inr rfl⟩
    · rcases hparent q hq with hunit | ⟨k, hk, hside⟩
      · exact Or.inl hunit
      · exact Or.inr ⟨k, List.mem_append_left _ hk, hside⟩

theorem supportedBy_refineCells {done : List ZLine} {l : ZLine}
    {cells : List SignCell} (hparent : ∀ cell ∈ cells, SupportedBy done cell) :
    ∀ child ∈ refineCells l cells, SupportedBy (done ++ [l]) child := by
  intro child hchild
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨parent, hparentMem, hrefine⟩ := hchild
  exact supportedBy_refineCell (hparent parent hparentMem) hrefine

theorem refineLines_supportedBy_aux {done todo : List ZLine} {cells : List SignCell}
    (hparent : ∀ cell ∈ cells, SupportedBy done cell) :
    ∀ child ∈ refineLines cells todo, SupportedBy (done ++ todo) child := by
  induction todo generalizing done cells with
  | nil => simpa only [refineLines, List.foldl_nil, List.append_nil] using hparent
  | cons l todo ih =>
      rw [refineLines, List.foldl_cons]
      intro child hchild
      have hnext := ih (done := done ++ [l]) (supportedBy_refineCells hparent) child hchild
      simpa only [List.append_assoc, List.singleton_append] using hnext

theorem feasibleSignCells_supportedBy {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) : SupportedBy ls cell := by
  unfold feasibleSignCells at hcell
  split at hcell
  · simp only [List.not_mem_nil] at hcell
  · rename_i base hbase
    have hbaseSystem := (cellOfSystem_sound hbase).1
    have h := refineLines_supportedBy_aux (done := []) (todo := ls) (cells := [base])
      (by
        intro c hc
        simp only [List.mem_singleton] at hc
        subst c
        intro q hq
        rw [hbaseSystem] at hq
        exact Or.inl hq)
      cell hcell
    simpa only [List.nil_append] using h

/-- Select the strict constraint agreeing with the side of a real point. -/
noncomputable def sideConstraintAt (u : Plane) (l : ZLine) : StrictInequality :=
  if 0 < l.evalPlane u then sideConstraint true l else sideConstraint false l

/-- Unit-square constraints followed by all line-side constraints selected at `u`. -/
noncomputable def signSystemAt (ls : List ZLine) (u : Plane) : List StrictInequality :=
  openUnitSquare ++ ls.map (sideConstraintAt u)

theorem mem_realCell_signSystemAt {ls : List ZLine} {u : Plane}
    (hunit : u ∈ realCell openUnitSquare)
    (hoff : ∀ l ∈ ls, l.evalPlane u ≠ 0) :
    u ∈ realCell (signSystemAt ls u) := by
  intro q hq
  rw [signSystemAt, List.mem_append] at hq
  rcases hq with hq | hq
  · exact hunit q hq
  · rw [List.mem_map] at hq
    obtain ⟨l, hl, rfl⟩ := hq
    unfold sideConstraintAt
    by_cases hpos : 0 < l.evalPlane u
    · rw [if_pos hpos]
      exact (sideConstraint_true_satisfiesPlane_iff l u).mpr hpos
    · rw [if_neg hpos]
      apply (sideConstraint_false_satisfiesPlane_iff l u).mpr
      exact lt_of_le_of_ne (le_of_not_gt hpos) (hoff l hl)

/-- Every real point in the open unit square and away from all arrangement lines belongs to a
compiler-enumerated real sign cell.  Density of `ℚ²` supplies the witness consumed by the verified
strict rational feasibility solver. -/
theorem exists_feasibleSignCell_containing_real_point {ls : List ZLine} {u : Plane}
    (hunit : u ∈ realCell openUnitSquare)
    (hoff : ∀ l ∈ ls, l.evalPlane u ≠ 0) :
    ∃ cell ∈ feasibleSignCells ls, u ∈ realCell cell.system := by
  have huSign : u ∈ realCell (signSystemAt ls u) :=
    mem_realCell_signSystemAt hunit hoff
  obtain ⟨p, hp⟩ := exists_rational_point_mem
    (isOpen_realCell (signSystemAt ls u)) ⟨u, huSign⟩
  have hsampleEq : rationalPlanePoint p = sampleToPlane p := by
    rw [rationalPlanePoint_eq]
    rfl
  rw [hsampleEq, mem_realCell_sampleToPlane_iff] at hp
  have hpunit : SatisfiesAll openUnitSquare p := by
    intro q hq
    exact hp q (by exact List.mem_append_left _ hq)
  have hpOff : ∀ l ∈ ls, l.eval p ≠ 0 := by
    intro l hl
    have hselected : sideConstraintAt u l ∈ signSystemAt ls u := by
      rw [signSystemAt, List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨l, hl, rfl⟩)
    have hpSelected := hp _ hselected
    unfold sideConstraintAt at hpSelected
    by_cases hpos : 0 < l.evalPlane u
    · rw [if_pos hpos] at hpSelected
      exact ne_of_gt ((sideConstraint_true_satisfies_iff l p).mp hpSelected)
    · rw [if_neg hpos] at hpSelected
      exact ne_of_lt ((sideConstraint_false_satisfies_iff l p).mp hpSelected)
  obtain ⟨cell, hcell, hpCell⟩ := feasibleSignCells_complete hpunit hpOff
  refine ⟨cell, hcell, ?_⟩
  intro q hq
  rcases feasibleSignCells_supportedBy hcell q hq with hqUnit | ⟨l, hl, hside⟩
  · exact hunit q hqUnit
  · rcases hside with rfl | rfl
    · apply (sideConstraint_false_satisfiesPlane_iff l u).mpr
      have hpNeg := (sideConstraint_false_satisfies_iff l p).mp (hpCell _ hq)
      have hselected : sideConstraintAt u l ∈ signSystemAt ls u := by
        rw [signSystemAt, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨l, hl, rfl⟩)
      have hpSelected := hp _ hselected
      unfold sideConstraintAt at hpSelected
      by_cases hpos : 0 < l.evalPlane u
      · rw [if_pos hpos] at hpSelected
        have hpPos := (sideConstraint_true_satisfies_iff l p).mp hpSelected
        exact (lt_asymm hpNeg hpPos).elim
      · exact lt_of_le_of_ne (le_of_not_gt hpos) (hoff l hl)
    · apply (sideConstraint_true_satisfiesPlane_iff l u).mpr
      have hpPos := (sideConstraint_true_satisfies_iff l p).mp (hpCell _ hq)
      have hselected : sideConstraintAt u l ∈ signSystemAt ls u := by
        rw [signSystemAt, List.mem_append]
        exact Or.inr (List.mem_map.mpr ⟨l, hl, rfl⟩)
      have hpSelected := hp _ hselected
      unfold sideConstraintAt at hpSelected
      by_cases hpos : 0 < l.evalPlane u
      · exact hpos
      · rw [if_neg hpos] at hpSelected
        have hpNeg := (sideConstraint_false_satisfies_iff l p).mp hpSelected
        exact (lt_asymm hpNeg hpPos).elim

/-- Nonzero triangle area forces the first edge to be nontrivial. -/
theorem first_edge_ne_of_twiceAreaQ_ne_zero {t : ZTriangle}
    (harea : twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    t.a ≠ t.b := by
  intro hab
  apply harea
  rw [hab]
  simp [twiceAreaQ]

/-- Nonzero triangle area forces the second edge to be nontrivial. -/
theorem second_edge_ne_of_twiceAreaQ_ne_zero {t : ZTriangle}
    (harea : twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    t.b ≠ t.c := by
  intro hbc
  apply harea
  rw [hbc]
  simp only [twiceAreaQ]
  ring

/-- Nonzero triangle area forces the third edge to be nontrivial. -/
theorem third_edge_ne_of_twiceAreaQ_ne_zero {t : ZTriangle}
    (harea : twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    t.c ≠ t.a := by
  intro hca
  apply harea
  rw [hca]
  simp [twiceAreaQ]

theorem edgeLine_first_mem_arrangementLines {ts : List ZTriangle} {z : ZPoint}
    (hz : z ∈ offsetWindow ts) {t : ZTriangle} (ht : t ∈ ts) :
    edgeLine z t.a t.b ∈ arrangementLines ts := by
  simp only [arrangementLines, List.mem_flatMap]
  exact ⟨z, hz, t, ht, by simp [translatedEdgeLines]⟩

theorem edgeLine_second_mem_arrangementLines {ts : List ZTriangle} {z : ZPoint}
    (hz : z ∈ offsetWindow ts) {t : ZTriangle} (ht : t ∈ ts) :
    edgeLine z t.b t.c ∈ arrangementLines ts := by
  simp only [arrangementLines, List.mem_flatMap]
  exact ⟨z, hz, t, ht, by simp [translatedEdgeLines]⟩

theorem edgeLine_third_mem_arrangementLines {ts : List ZTriangle} {z : ZPoint}
    (hz : z ∈ offsetWindow ts) {t : ZTriangle} (ht : t ∈ ts) :
    edgeLine z t.c t.a ∈ arrangementLines ts := by
  simp only [arrangementLines, List.mem_flatMap]
  exact ⟨z, hz, t, ht, by simp [translatedEdgeLines]⟩

/-- Every arrangement line generated by nondegenerate triangles is genuine. -/
theorem arrangementLine_coefficients_ne_zero {ts : List ZTriangle}
    (harea : ∀ t ∈ ts,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0)
    {l : ZLine} (hl : l ∈ arrangementLines ts) : l.A ≠ 0 ∨ l.B ≠ 0 := by
  rw [arrangementLines, List.mem_flatMap] at hl
  obtain ⟨z, _hz, hl⟩ := hl
  rw [List.mem_flatMap] at hl
  obtain ⟨t, ht, hl⟩ := hl
  simp only [translatedEdgeLines, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact edgeLine_coefficients_ne_zero (first_edge_ne_of_twiceAreaQ_ne_zero (harea t ht))
  · rcases hl with rfl | hl
    · exact edgeLine_coefficients_ne_zero (second_edge_ne_of_twiceAreaQ_ne_zero (harea t ht))
    · rcases hl with rfl | hl
      · exact edgeLine_coefficients_ne_zero (third_edge_ne_of_twiceAreaQ_ne_zero (harea t ht))
      · simp only [List.not_mem_nil] at hl

/-- The generated arrangement boundary is null for a list of nondegenerate triangles. -/
theorem volume_exceptionalSet_arrangementLines {ts : List ZTriangle}
    (harea : ∀ t ∈ ts,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    volume (exceptionalSet (arrangementLines ts)) = 0 := by
  apply volume_exceptionalSet
  intro l hl
  exact arrangementLine_coefficients_ne_zero harea hl

/-- Finite union of the closed triangle carriers represented by an integral triangle list. -/
def triangleUnion (ts : List ZTriangle) : Set Plane :=
  ⋃ t ∈ ts.toFinset, t.carrier

theorem mem_triangleUnion_iff {ts : List ZTriangle} {u : Plane} :
    u ∈ triangleUnion ts ↔ ∃ t ∈ ts, u ∈ t.carrier := by
  simp [triangleUnion]

/-- On a feasible sign cell, executable region membership at the stored rational sample is
exactly semantic membership in the finite triangle union at every real point of the cell. -/
theorem pointInRegion_sample_iff_mem_triangleUnion
    {ts : List ZTriangle}
    (harea : ∀ t ∈ ts,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0)
    {cell : SignCell} (hcell : cell ∈ feasibleSignCells (arrangementLines ts))
    {u : Plane} (hu : u ∈ realCell cell.system)
    {z : ZPoint} (hz : z ∈ offsetWindow ts) :
    pointInRegion ts (addOffset cell.sample z) = true ↔
      u + integerPoint z.toIntegerPlane ∈ triangleUnion ts := by
  have hsample : sampleToPlane cell.sample ∈ realCell cell.system :=
    (mem_realCell_sampleToPlane_iff cell.system cell.sample).mpr
      (feasibleSignCells_sound hcell)
  rw [pointInRegion, List.any_eq_true, mem_triangleUnion_iff]
  constructor
  · rintro ⟨t, ht, hpoint⟩
    refine ⟨t, ht, ?_⟩
    apply (mem_carrier_iff_pointInTriangle_of_same_strict_edge_signs
      (harea t ht) ?_ ?_ ?_).mpr hpoint
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_first_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_second_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_third_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign
  · rintro ⟨t, ht, hmem⟩
    refine ⟨t, ht, ?_⟩
    apply (mem_carrier_iff_pointInTriangle_of_same_strict_edge_signs
      (harea t ht) ?_ ?_ ?_).mp hmem
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_first_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_second_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign
    · have hsign := sameStrictSign_of_mem_realCell hcell hu hsample
        (edgeLine_third_mem_arrangementLines hz ht)
      rwa [ZLine.evalPlane_sampleToPlane] at hsign

/-- Membership in a compiled sample signature is semantic triangle-union membership throughout
the corresponding feasible real cell. -/
theorem ZPoint.toIntegerPlane_injective : Function.Injective ZPoint.toIntegerPlane := by
  intro p q h
  cases p with
  | mk px py =>
      cases q with
      | mk qx qy =>
          apply congrArg (fun v : IntegerPlane => (v 0, v 1)) at h
          simpa [ZPoint.toIntegerPlane] using h

theorem mem_sampleSignature_iff_mem_triangleUnion
    {ts : List ZTriangle}
    (harea : ∀ t ∈ ts,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0)
    {cell : SignCell} (hcell : cell ∈ feasibleSignCells (arrangementLines ts))
    {u : Plane} (hu : u ∈ realCell cell.system) {z : ZPoint} :
    z.toIntegerPlane ∈ sampleSignature ts (offsetWindow ts) cell.sample ↔
      z ∈ offsetWindow ts ∧
        u + integerPoint z.toIntegerPlane ∈ triangleUnion ts := by
  simp only [sampleSignature, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hwEq : w = z := ZPoint.toIntegerPlane_injective hwz
    subst w
    obtain ⟨hz, hpoint⟩ := List.mem_filter.mp hw
    exact ⟨hz,
      (pointInRegion_sample_iff_mem_triangleUnion harea hcell hu hz).mp hpoint⟩
  · rintro ⟨hz, hmem⟩
    refine ⟨z, List.mem_filter.mpr ⟨hz, ?_⟩, rfl⟩
    exact (pointInRegion_sample_iff_mem_triangleUnion harea hcell hu hz).mpr hmem

theorem refineCells_preserves_constraint {q : StrictInequality} {l : ZLine}
    {cells : List SignCell} (hq : ∀ cell ∈ cells, q ∈ cell.system) :
    ∀ child ∈ refineCells l cells, q ∈ child.system := by
  intro child hchild
  simp only [refineCells, List.mem_flatMap] at hchild
  obtain ⟨parent, hparent, hrefine⟩ := hchild
  exact mem_system_of_mem_refineCell hrefine (hq parent hparent)

theorem refineLines_preserves_constraint {q : StrictInequality} {cells : List SignCell}
    {ls : List ZLine} (hq : ∀ cell ∈ cells, q ∈ cell.system) :
    ∀ child ∈ refineLines cells ls, q ∈ child.system := by
  induction ls generalizing cells with
  | nil => simpa only [refineLines, List.foldl_nil] using hq
  | cons l ls ih =>
      rw [refineLines, List.foldl_cons]
      exact ih (refineCells_preserves_constraint hq)

/-- Every feasible cell retains all four open-unit-square constraints. -/
theorem openUnitSquare_subset_feasibleSignCell_system {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) :
    ∀ q ∈ openUnitSquare, q ∈ cell.system := by
  unfold feasibleSignCells at hcell
  split at hcell
  · simp only [List.not_mem_nil] at hcell
  · rename_i base hbase
    intro q hq
    apply refineLines_preserves_constraint (ls := ls) _ cell hcell
    intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    rw [(cellOfSystem_sound hbase).1]
    exact hq

theorem mem_realCell_openUnitSquare_iff {u : Plane} :
    u ∈ realCell openUnitSquare ↔
      0 < u.re ∧ u.re < 1 ∧ 0 < u.im ∧ u.im < 1 := by
  simp only [realCell, openUnitSquare, List.mem_cons, satisfiesPlane]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using h ⟨-1, 0, 0⟩ (by simp)
    · simpa using h ⟨1, 0, 1⟩ (by simp)
    · simpa using h ⟨0, -1, 0⟩ (by simp)
    · simpa using h ⟨0, 1, 1⟩ (by simp)
  · rintro ⟨hx0, hx1, hy0, hy1⟩ q hq
    rcases hq with rfl | hq
    · norm_num
      linarith
    · rcases hq with rfl | hq
      · norm_num
        linarith
      · rcases hq with rfl | hq
        · norm_num
          linarith
        · rcases hq with rfl | hq
          · norm_num
            linarith
          · simp only [List.not_mem_nil] at hq

theorem realCell_subset_closedUnitCell {ls : List ZLine} {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells ls) : realCell cell.system ⊆ closedUnitCell := by
  intro u hu
  have hunit : u ∈ realCell openUnitSquare := by
    intro q hq
    exact hu q (openUnitSquare_subset_feasibleSignCell_system hcell q hq)
  have hb := mem_realCell_openUnitSquare_iff.mp hunit
  rw [closedUnitCell]
  change (u.re, u.im) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1
  simp only [Set.mem_prod, Set.mem_Icc]
  exact ⟨⟨hb.1.le, hb.2.1.le⟩, ⟨hb.2.2.1.le, hb.2.2.2.le⟩⟩

/-- The rational area of every normalized triangle remains nonzero. -/
theorem normalizedTriangle_twiceAreaQ_ne_zero (P : Code.Input) {t : QTriangle}
    (ht : t ∈ P.code.triangleFinset) :
    twiceAreaQ (zpointQ (P.normalizedTriangle t).a)
      (zpointQ (P.normalizedTriangle t).b)
      (zpointQ (P.normalizedTriangle t).c) ≠ 0 := by
  have ha := P.normalizedPoint_toPlane ht (by simp [QTriangle.vertices] : t.a ∈ t.vertices)
  have hb := P.normalizedPoint_toPlane ht (by simp [QTriangle.vertices] : t.b ∈ t.vertices)
  have hc := P.normalizedPoint_toPlane ht (by simp [QTriangle.vertices] : t.c ∈ t.vertices)
  have hD : (P.denominator : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt P.denominator_pos)
  have hscale :
      twiceSignedArea (P.normalizedPoint t.a).toPlane
        (P.normalizedPoint t.b).toPlane (P.normalizedPoint t.c).toPlane =
        (P.denominator : ℝ) ^ 2 *
          twiceSignedArea t.a.toPlane t.b.toPlane t.c.toPlane := by
    rw [ha, hb, hc]
    simp only [twiceSignedArea, Complex.smul_re, Complex.sub_re, QPoint.toPlane_re,
      Complex.smul_im, Complex.sub_im, QPoint.toPlane_im, smul_eq_mul]
    ring
  intro hzero
  have hzeroReal :
      ((twiceAreaQ (zpointQ (P.normalizedTriangle t).a)
        (zpointQ (P.normalizedTriangle t).b)
        (zpointQ (P.normalizedTriangle t).c) : ℚ) : ℝ) = 0 := by
    exact_mod_cast hzero
  rw [twiceAreaQ_zpointQ_cast] at hzeroReal
  change twiceSignedArea (P.normalizedPoint t.a).toPlane
    (P.normalizedPoint t.b).toPlane (P.normalizedPoint t.c).toPlane = 0 at hzeroReal
  rw [hscale] at hzeroReal
  exact P.valid.nondegenerate t ht (by
    apply mul_left_cancel₀ (pow_ne_zero 2 hD)
    simpa only [mul_zero] using hzeroReal)

theorem normalizedTriangles_twiceAreaQ_ne_zero (P : Code.Input) :
    ∀ t ∈ normalizedTriangles P,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0 := by
  intro t ht
  rw [normalizedTriangles, List.mem_map] at ht
  obtain ⟨q, hq, rfl⟩ := ht
  apply normalizedTriangle_twiceAreaQ_ne_zero P
  simpa only [Code.triangleFinset, List.mem_toFinset] using hq

theorem normalizedRegion_support_eq_triangleUnion (P : Code.Input) :
    P.rationalPolygonalRegion.normalizedRegion.support =
      triangleUnion (normalizedTriangles P) := by
  simpa only [triangleUnion] using normalizedRegion_support_eq_list_iUnion P

/-- The four affine lines supporting the boundary of the closed unit cell. -/
def unitBoundaryLines : List ZLine :=
  [⟨1, 0, 0⟩, ⟨1, 0, -1⟩, ⟨0, 1, 0⟩, ⟨0, 1, -1⟩]

theorem volume_unitBoundary : volume (exceptionalSet unitBoundaryLines) = 0 := by
  apply volume_exceptionalSet
  intro l hl
  simp only [unitBoundaryLines, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact Or.inl one_ne_zero
  · rcases hl with rfl | hl
    · exact Or.inl one_ne_zero
    · rcases hl with rfl | hl
      · exact Or.inr one_ne_zero
      · rcases hl with rfl | hl
        · exact Or.inr one_ne_zero
        · simp only [List.not_mem_nil] at hl

theorem mem_exceptionalSet_of_evalPlane_eq_zero {ls : List ZLine} {l : ZLine}
    (hl : l ∈ ls) {u : Plane} (hu : l.evalPlane u = 0) :
    u ∈ exceptionalSet ls := by
  unfold exceptionalSet
  apply Set.mem_iUnion.mpr
  refine ⟨l, Set.mem_iUnion.mpr ⟨List.mem_toFinset.mpr hl, ?_⟩⟩
  change planeEval l.A l.B l.C u = 0
  simpa only [ZLine.evalPlane, planeEval] using hu

/-- Arrangement lines together with the four unit-cell boundary lines. -/
def totalExceptionalSet (ts : List ZTriangle) : Set Plane :=
  exceptionalSet (arrangementLines ts) ∪ exceptionalSet unitBoundaryLines

theorem volume_totalExceptionalSet {ts : List ZTriangle}
    (harea : ∀ t ∈ ts,
      twiceAreaQ (zpointQ t.a) (zpointQ t.b) (zpointQ t.c) ≠ 0) :
    volume (totalExceptionalSet ts) = 0 := by
  exact measure_union_null (volume_exceptionalSet_arrangementLines harea) volume_unitBoundary

theorem exists_mem_not_mem_of_measure_ne_zero_of_measure_zero
    {s n : Set Plane} (hs : volume s ≠ 0) (hn : volume n = 0) :
    ∃ u ∈ s, u ∉ n := by
  by_contra hexists
  have hsubset : s ⊆ n := by
    intro u hu
    by_contra hun
    exact hexists ⟨u, hu, hun⟩
  exact hs (measure_mono_null hsubset hn)

/-- The executable signature stored by a feasible cell is exactly the semantic signature of the
normalized polygonal region at every point of that real cell. -/
theorem sampleSignature_eq_normalizedRegion_signature
    (P : Code.Input)
    {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells (arrangementLines (normalizedTriangles P)))
    {u : Plane} (hu : u ∈ realCell cell.system) :
    sampleSignature (normalizedTriangles P) (offsetWindow (normalizedTriangles P)) cell.sample =
      P.rationalPolygonalRegion.normalizedRegion.signature u := by
  let ts := normalizedTriangles P
  have harea := normalizedTriangles_twiceAreaQ_ne_zero P
  have huClosed : u ∈ closedUnitCell := realCell_subset_closedUnitCell hcell hu
  have huBounds : u.re ∈ Set.Icc (0 : ℝ) 1 ∧ u.im ∈ Set.Icc (0 : ℝ) 1 := by
    rw [closedUnitCell] at huClosed
    exact huClosed
  ext q
  let z : ZPoint := ⟨q 0, q 1⟩
  have hz : z.toIntegerPlane = q := by
    ext i
    fin_cases i <;> rfl
  rw [← hz, mem_sampleSignature_iff_mem_triangleUnion harea hcell hu]
  rw [PolygonalRegion.mem_signature_iff, normalizedRegion_support_eq_triangleUnion]
  constructor
  · exact fun h => h.2
  · intro hmem
    exact ⟨mem_offsetWindow_of_add_mem_triangleUnion huBounds.1 huBounds.2 hmem, hmem⟩

/-- Every compiler-enumerated signature is a positive-measure semantic signature. -/
theorem sampleSignature_mem_relevantSignatures
    (P : Code.Input) {cell : SignCell}
    (hcell : cell ∈ feasibleSignCells (arrangementLines (normalizedTriangles P))) :
    sampleSignature (normalizedTriangles P) (offsetWindow (normalizedTriangles P)) cell.sample ∈
      P.rationalPolygonalRegion.normalizedRegion.relevantSignatures := by
  let K := P.rationalPolygonalRegion.normalizedRegion
  let F := sampleSignature (normalizedTriangles P) (offsetWindow (normalizedTriangles P))
    cell.sample
  have hdata := feasibleSignCell_open_nonempty_measure_ne_zero hcell
  have hsampleMem : sampleToPlane cell.sample ∈ realCell cell.system :=
    (mem_realCell_sampleToPlane_iff cell.system cell.sample).mpr
      (feasibleSignCells_sound hcell)
  have hsampleClosed : sampleToPlane cell.sample ∈ closedUnitCell :=
    realCell_subset_closedUnitCell hcell hsampleMem
  have hsignatureSample : K.signature (sampleToPlane cell.sample) = F := by
    symm
    exact sampleSignature_eq_normalizedRegion_signature P hcell hsampleMem
  rw [PolygonalRegion.mem_relevantSignatures_iff]
  constructor
  · change F ∈ K.candidateSignatures
    rw [← hsignatureSample]
    exact K.signature_mem_candidateSignatures hsampleClosed
  · change volume (K.signatureFiber F) ≠ 0
    intro hfiberZero
    apply hdata.2.2
    apply measure_mono_null _ hfiberZero
    intro u hu
    rw [PolygonalRegion.mem_signatureFiber_iff]
    exact ⟨realCell_subset_closedUnitCell hcell hu,
      (sampleSignature_eq_normalizedRegion_signature P hcell hu).symm⟩

/-- Exact semantic completeness of the compiler's deduplicated signature family. -/
theorem mem_signatureFamily_iff_mem_relevantSignatures
    (P : Code.Input) {F : Finset IntegerPlane} :
    F ∈ signatureFamily (normalizedTriangles P) ↔
      F ∈ P.rationalPolygonalRegion.normalizedRegion.relevantSignatures := by
  let ts := normalizedTriangles P
  let K := P.rationalPolygonalRegion.normalizedRegion
  have harea := normalizedTriangles_twiceAreaQ_ne_zero P
  constructor
  · intro hF
    simp only [signatureFamily, List.mem_eraseDups, List.mem_map] at hF
    obtain ⟨cell, hcell, hcellF⟩ := hF
    rw [← hcellF]
    exact sampleSignature_mem_relevantSignatures P hcell
  · intro hF
    have hmeasure : volume (K.signatureFiber F) ≠ 0 :=
      (PolygonalRegion.mem_relevantSignatures_iff.mp hF).2
    obtain ⟨u, huFiber, huExceptional⟩ :=
      exists_mem_not_mem_of_measure_ne_zero_of_measure_zero hmeasure
        (volume_totalExceptionalSet harea)
    have huClosed : u ∈ closedUnitCell :=
      (PolygonalRegion.mem_signatureFiber_iff.mp huFiber).1
    have huSignature : K.signature u = F :=
      (PolygonalRegion.mem_signatureFiber_iff.mp huFiber).2
    have huNotUnit : u ∉ exceptionalSet unitBoundaryLines := by
      intro hu
      exact huExceptional (Or.inr hu)
    have huBounds : u.re ∈ Set.Icc (0 : ℝ) 1 ∧ u.im ∈ Set.Icc (0 : ℝ) 1 := by
      rw [closedUnitCell] at huClosed
      exact huClosed
    have hx0 : u.re ≠ 0 := by
      intro h
      apply huNotUnit
      apply mem_exceptionalSet_of_evalPlane_eq_zero
        (ls := unitBoundaryLines) (l := ⟨1, 0, 0⟩) (by simp [unitBoundaryLines])
      simp only [ZLine.evalPlane]
      rw [h]
      norm_num
    have hx1 : u.re ≠ 1 := by
      intro h
      apply huNotUnit
      apply mem_exceptionalSet_of_evalPlane_eq_zero
        (ls := unitBoundaryLines) (l := ⟨1, 0, -1⟩) (by simp [unitBoundaryLines])
      simp only [ZLine.evalPlane]
      rw [h]
      norm_num
    have hy0 : u.im ≠ 0 := by
      intro h
      apply huNotUnit
      apply mem_exceptionalSet_of_evalPlane_eq_zero
        (ls := unitBoundaryLines) (l := ⟨0, 1, 0⟩) (by simp [unitBoundaryLines])
      simp only [ZLine.evalPlane]
      rw [h]
      norm_num
    have hy1 : u.im ≠ 1 := by
      intro h
      apply huNotUnit
      apply mem_exceptionalSet_of_evalPlane_eq_zero
        (ls := unitBoundaryLines) (l := ⟨0, 1, -1⟩) (by simp [unitBoundaryLines])
      simp only [ZLine.evalPlane]
      rw [h]
      norm_num
    have huUnit : u ∈ realCell openUnitSquare := by
      rw [mem_realCell_openUnitSquare_iff]
      exact ⟨lt_of_le_of_ne huBounds.1.1 hx0.symm,
        lt_of_le_of_ne huBounds.1.2 hx1,
        lt_of_le_of_ne huBounds.2.1 hy0.symm,
        lt_of_le_of_ne huBounds.2.2 hy1⟩
    have huOff : ∀ l ∈ arrangementLines ts, l.evalPlane u ≠ 0 := by
      intro l hl hzero
      apply huExceptional
      apply Or.inl
      unfold exceptionalSet
      apply Set.mem_iUnion.mpr
      refine ⟨l, Set.mem_iUnion.mpr ⟨List.mem_toFinset.mpr hl, ?_⟩⟩
      change planeEval l.A l.B l.C u = 0
      simpa only [ZLine.evalPlane, planeEval] using hzero
    obtain ⟨cell, hcell, huCell⟩ :=
      exists_feasibleSignCell_containing_real_point huUnit huOff
    simp only [signatureFamily, List.mem_eraseDups, List.mem_map]
    refine ⟨cell, hcell, ?_⟩
    exact (sampleSignature_eq_normalizedRegion_signature P hcell huCell).trans huSignature

/-- The executable family is exactly the semantic finite family, independent of list ordering. -/
theorem signatureFamily_toFinset_eq_relevantSignatures (P : Code.Input) :
    (signatureFamily (normalizedTriangles P)).toFinset =
      P.rationalPolygonalRegion.normalizedRegion.relevantSignatures := by
  ext F
  simpa only [List.mem_toFinset] using
    (mem_signatureFamily_iff_mem_relevantSignatures P (F := F))

end Tiling.RationalPolygonal.Raw.Compiler
