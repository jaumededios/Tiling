import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Measure
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

set_option linter.style.header false

/-!
# Special subsets of the plane

This file defines triangles, axis-parallel rectangles, polygonal sets, and axis-parallel sets in
the real plane.  Polygonal and axis-parallel sets admit finite, pairwise almost-everywhere disjoint
decompositions into their respective nondegenerate pieces.
-/

open MeasureTheory Set

namespace Tiling

/-- The real plane, represented by the complex numbers. -/
abbrev Plane := ℂ

/-- Twice the signed area of the triangle with the given vertices. -/
def twiceSignedArea (a b c : Plane) : ℝ :=
  (b.re - a.re) * (c.im - a.im) - (b.im - a.im) * (c.re - a.re)

/-- A nondegenerate closed triangle in the plane. -/
def IsTriangle (s : Set Plane) : Prop :=
  ∃ a b c : Plane, twiceSignedArea a b c ≠ 0 ∧ s = convexHull ℝ {a, b, c}

/-- A nondegenerate closed axis-parallel rectangle in the plane. -/
def IsRectangle (s : Set Plane) : Prop :=
  ∃ a b : Plane, a.re ≠ b.re ∧ a.im ≠ b.im ∧ s = Complex.Rectangle a b

/-- A finite, almost-everywhere disjoint decomposition of a set into triangles. -/
structure Triangulation (s : Set Plane) where
  /-- The finite collection of triangular pieces. -/
  pieces : Finset (Set Plane)
  /-- Every piece is a nondegenerate triangle. -/
  isTriangle : ∀ t ∈ pieces, IsTriangle t
  /-- Distinct pieces overlap only on a null set. -/
  pairwiseAEDisjoint : (pieces : Set (Set Plane)).Pairwise (AEDisjoint volume)
  /-- The pieces have union exactly `s`. -/
  sUnion_eq : ⋃₀ (pieces : Set (Set Plane)) = s

/-- A finite, almost-everywhere disjoint decomposition of a set into axis-parallel rectangles. -/
structure Rectangulation (s : Set Plane) where
  /-- The finite collection of rectangular pieces. -/
  pieces : Finset (Set Plane)
  /-- Every piece is a nondegenerate axis-parallel rectangle. -/
  isRectangle : ∀ r ∈ pieces, IsRectangle r
  /-- Distinct pieces overlap only on a null set. -/
  pairwiseAEDisjoint : (pieces : Set (Set Plane)).Pairwise (AEDisjoint volume)
  /-- The pieces have union exactly `s`. -/
  sUnion_eq : ⋃₀ (pieces : Set (Set Plane)) = s

/-- A set is polygonal if it admits a triangulation. -/
def IsPolygonal (s : Set Plane) : Prop :=
  Nonempty (Triangulation s)

/-- A set is axis-parallel if it admits a rectangulation. -/
def IsAxisParallel (s : Set Plane) : Prop :=
  Nonempty (Rectangulation s)

/-- The vertices that occur in every triangulation of a polygonal set.  A vertex of a triangle is
understood intrinsically as an extreme point.  Quantifying over every triangulation makes the set
independent of any chosen decomposition.  This definition is intended for sets satisfying
`IsPolygonal`. -/
def vertexSet (s : Set Plane) : Set Plane :=
  {x | ∀ triangulation : Triangulation s,
    ∃ t ∈ triangulation.pieces, x ∈ t.extremePoints ℝ}

/-- A point in the plane whose two coordinates are rational. -/
def IsRationalPoint (z : Plane) : Prop :=
  ∃ x y : ℚ, z.re = x ∧ z.im = y

/-- A polygonal set is rational if all of its triangulation-independent vertices are rational. -/
def IsRational (s : Set Plane) : Prop :=
  IsPolygonal s ∧ ∀ x ∈ vertexSet s, IsRationalPoint x

private theorem volume_convexHull_pair_eq_zero (a b : Plane) :
    volume (convexHull ℝ {a, b}) = 0 := by
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
    have hdim := congrArg (fun s : AffineSubspace ℝ Plane ↦ Module.finrank ℝ s.direction) htop
    rw [direction_affineSpan, vectorSpan_pair_rev, vsub_eq_sub,
      finrank_span_singleton (sub_ne_zero.mpr (Ne.symm hab)), AffineSubspace.direction_top,
      finrank_top, Complex.finrank_real_complex] at hdim
    omega

private theorem rectangle_eq_union_triangles (a b : Plane) :
    Complex.Rectangle a b =
      convexHull ℝ {a, a.re + b.im * Complex.I, b} ∪
        convexHull ℝ {a, b.re + a.im * Complex.I, b} := by
  let c : Plane := a.re + b.im * Complex.I
  let d : Plane := b.re + a.im * Complex.I
  change Complex.Rectangle a b = convexHull ℝ {a, c, b} ∪ convexHull ℝ {a, d, b}
  by_cases hre : a.re = b.re
  · have hc : c = b := by apply Complex.ext <;> simp [c, hre]
    have hd : d = a := by apply Complex.ext <;> simp [d, hre]
    rw [Complex.rectangle_eq_convexHull]
    change convexHull ℝ {a, c, d, b} = convexHull ℝ {a, c, b} ∪ convexHull ℝ {a, d, b}
    simp [hc, hd]
  by_cases him : a.im = b.im
  · have hc : c = a := by apply Complex.ext <;> simp [c, him]
    have hd : d = b := by apply Complex.ext <;> simp [d, him]
    rw [Complex.rectangle_eq_convexHull]
    change convexHull ℝ {a, c, d, b} = convexHull ℝ {a, c, b} ∪ convexHull ℝ {a, d, b}
    simp [hc, hd]
  have hac : a ≠ c := by
    intro h
    apply him
    simpa [c] using congrArg Complex.im h
  have had : a ≠ d := by
    intro h
    apply hre
    simpa [d] using congrArg Complex.re h
  have hab : a ≠ b := fun h ↦ hre (congrArg Complex.re h)
  have hca : c ≠ a := hac.symm
  have hcd : c ≠ d := by
    intro h
    apply hre
    simpa [c, d] using congrArg Complex.re h
  have hcb : c ≠ b := by
    intro h
    apply hre
    simpa [c] using congrArg Complex.re h
  have hda : d ≠ a := had.symm
  have hdc : d ≠ c := hcd.symm
  have hdb : d ≠ b := by
    intro h
    apply him
    simpa [d] using congrArg Complex.im h
  have hba : b ≠ a := hab.symm
  have hbc : b ≠ c := hcb.symm
  have hbd : b ≠ d := hdb.symm
  rw [Complex.rectangle_eq_convexHull]
  change convexHull ℝ {a, c, d, b} = convexHull ℝ {a, c, b} ∪ convexHull ℝ {a, d, b}
  apply Set.Subset.antisymm
  · intro x hx
    have hx' : x ∈ convexHull ℝ (↑({a, c, d, b} : Finset Plane) : Set Plane) := by
      simpa using hx
    obtain ⟨w, hw_nonneg, hw_sum, hwx⟩ := Finset.mem_convexHull'.mp hx'
    have hw_sum' : w a + w c + w d + w b = 1 := by
      simpa [hac, had, hab, hca, hcd, hcb, hda, hdc, hdb, hba, hbc, hbd, add_assoc] using hw_sum
    have hwx' : w a • a + w c • c + w d • d + w b • b = x := by
      simpa [hac, had, hab, hca, hcd, hcb, hda, hdc, hdb, hba, hbc, hbd, add_assoc] using hwx
    have hwa : 0 ≤ w a := hw_nonneg a (by simp)
    have hwc : 0 ≤ w c := hw_nonneg c (by simp)
    have hwd : 0 ≤ w d := hw_nonneg d (by simp)
    have hwb : 0 ≤ w b := hw_nonneg b (by simp)
    have hcorners : a + b = c + d := by apply Complex.ext <;> simp [c, d, add_comm]
    rcases le_total (w c) (w d) with hcdw | hdcw
    · right
      apply mem_convexHull_of_exists_fintype (R := ℝ) ![w a + w c, w d - w c, w b + w c]
        ![a, d, b]
      · intro i
        fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_three]
        linarith [hw_sum']
      · intro i
        fin_cases i <;> simp
      · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]
        calc
          (w a + w c) • a + (w d - w c) • d + (w b + w c) • b =
              w a • a + w c • c + w d • d + w b • b := by
            linear_combination (norm := module) w c • hcorners
          _ = x := hwx'
    · left
      apply mem_convexHull_of_exists_fintype (R := ℝ) ![w a + w d, w c - w d, w b + w d]
        ![a, c, b]
      · intro i
        fin_cases i <;> simp <;> linarith
      · simp [Fin.sum_univ_three]
        linarith [hw_sum']
      · intro i
        fin_cases i <;> simp
      · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two]
        calc
          (w a + w d) • a + (w c - w d) • c + (w b + w d) • b =
              w a • a + w c • c + w d • d + w b • b := by
            linear_combination (norm := module) w d • hcorners
          _ = x := hwx'
  · apply Set.union_subset
    · exact convexHull_mono (by aesop)
    · exact convexHull_mono (by aesop)

private theorem diagonal_triangles_aedisjoint (a b : Plane) :
    AEDisjoint volume (convexHull ℝ {a, a.re + b.im * Complex.I, b})
      (convexHull ℝ {a, b.re + a.im * Complex.I, b}) := by
  classical
  let c : Plane := a.re + b.im * Complex.I
  let d : Plane := b.re + a.im * Complex.I
  change AEDisjoint volume (convexHull ℝ {a, c, b}) (convexHull ℝ {a, d, b})
  by_cases hre : a.re = b.re
  · have hc : c = b := by apply Complex.ext <;> simp [c, hre]
    have hd : d = a := by apply Complex.ext <;> simp [d, hre]
    simp [hc, hd, AEDisjoint]
    simpa only [convexHull_pair] using volume_convexHull_pair_eq_zero a b
  by_cases him : a.im = b.im
  · have hc : c = a := by apply Complex.ext <;> simp [c, him]
    have hd : d = b := by apply Complex.ext <;> simp [d, him]
    simp [hc, hd, AEDisjoint]
    simpa only [convexHull_pair] using volume_convexHull_pair_eq_zero a b
  have hac : a ≠ c := by
    intro h
    apply him
    simpa [c] using congrArg Complex.im h
  have had : a ≠ d := by
    intro h
    apply hre
    simpa [d] using congrArg Complex.re h
  have hab : a ≠ b := fun h ↦ hre (congrArg Complex.re h)
  have hca : c ≠ a := hac.symm
  have hcb : c ≠ b := by
    intro h
    apply hre
    simpa [c] using congrArg Complex.re h
  have hda : d ≠ a := had.symm
  have hdb : d ≠ b := by
    intro h
    apply him
    simpa [d] using congrArg Complex.im h
  have hba : b ≠ a := hab.symm
  have hbc : b ≠ c := hcb.symm
  have hbd : b ≠ d := hdb.symm
  rw [AEDisjoint]
  apply measure_mono_null ?_ (volume_convexHull_pair_eq_zero a b)
  rintro x ⟨hx₁, hx₂⟩
  have hx₁' : x ∈ convexHull ℝ (↑({a, c, b} : Finset Plane) : Set Plane) := by
    simpa using hx₁
  have hx₂' : x ∈ convexHull ℝ (↑({a, d, b} : Finset Plane) : Set Plane) := by
    simpa using hx₂
  obtain ⟨u, hu_nonneg, hu_sum, hux⟩ := Finset.mem_convexHull'.mp hx₁'
  obtain ⟨v, hv_nonneg, hv_sum, hvx⟩ := Finset.mem_convexHull'.mp hx₂'
  have hu_sum' : u a + u c + u b = 1 := by
    simpa [hac, hab, hca, hcb, hba, hbc, add_assoc] using hu_sum
  have hv_sum' : v a + v d + v b = 1 := by
    simpa [had, hab, hda, hdb, hba, hbd, add_assoc] using hv_sum
  have hux' : u a • a + u c • c + u b • b = x := by
    simpa [hac, hab, hca, hcb, hba, hbc, add_assoc] using hux
  have hvx' : v a • a + v d • d + v b • b = x := by
    simpa [had, hab, hda, hdb, hba, hbd, add_assoc] using hvx
  have hux_re : u a * a.re + u c * a.re + u b * b.re = x.re := by
    simpa [c] using congrArg Complex.re hux'
  have hvx_re : v a * a.re + v d * b.re + v b * b.re = x.re := by
    simpa [d] using congrArg Complex.re hvx'
  have hux_im : u a * a.im + u c * b.im + u b * b.im = x.im := by
    simpa [c] using congrArg Complex.im hux'
  have hvx_im : v a * a.im + v d * a.im + v b * b.im = x.im := by
    simpa [d] using congrArg Complex.im hvx'
  have hub : u b = v d + v b := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hre))
    linear_combination hux_re - hvx_re - a.re * hu_sum' + a.re * hv_sum'
  have hucub : u c + u b = v b := by
    apply mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm him))
    linear_combination hux_im - hvx_im - a.im * hu_sum' + a.im * hv_sum'
  have huc : 0 ≤ u c := hu_nonneg c (by simp)
  have hvd : 0 ≤ v d := hv_nonneg d (by simp)
  have huc_zero : u c = 0 := by linarith
  apply mem_convexHull_of_exists_fintype (R := ℝ) ![u a, u b] ![a, b]
  · intro i
    fin_cases i
    · change 0 ≤ u a
      exact hu_nonneg a (by simp)
    · change 0 ≤ u b
      exact hu_nonneg b (by simp)
  · simp [Fin.sum_univ_two]
    linarith [hu_sum']
  · intro i
    fin_cases i <;> simp
  · simpa [Fin.sum_univ_two, huc_zero] using hux'

/-- The canonical triangulation of a nondegenerate axis-parallel rectangle along the diagonal
joining its two defining corners. -/
noncomputable def rectangleDiagonalTriangulation (a b : Plane)
    (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    Triangulation (Complex.Rectangle a b) := by
  classical
  let t₁ := convexHull ℝ {a, a.re + b.im * Complex.I, b}
  let t₂ := convexHull ℝ {a, b.re + a.im * Complex.I, b}
  refine ⟨{t₁, t₂}, ?_, ?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · refine ⟨a, a.re + b.im * Complex.I, b, ?_, rfl⟩
      simpa [twiceSignedArea] using neg_ne_zero.mpr
        (mul_ne_zero (sub_ne_zero.mpr (Ne.symm him)) (sub_ne_zero.mpr (Ne.symm hre)))
    · refine ⟨a, b.re + a.im * Complex.I, b, ?_, rfl⟩
      simpa [twiceSignedArea] using
        mul_ne_zero (sub_ne_zero.mpr (Ne.symm hre)) (sub_ne_zero.mpr (Ne.symm him))
  · simpa only [Finset.coe_insert, Finset.coe_singleton] using
      (Set.pairwise_pair_of_symm.mpr fun _ ↦ diagonal_triangles_aedisjoint a b)
  · simpa [t₁, t₂, Set.sUnion_pair] using (rectangle_eq_union_triangles a b).symm

@[simp] theorem rectangleDiagonalTriangulation_pieces (a b : Plane)
    (hre : a.re ≠ b.re) (him : a.im ≠ b.im) :
    (rectangleDiagonalTriangulation a b hre him).pieces =
      {convexHull ℝ {a, a.re + b.im * Complex.I, b},
        convexHull ℝ {a, b.re + a.im * Complex.I, b}} := rfl

/-- Every axis-parallel rectangle is polygonal. -/
theorem IsRectangle.isPolygonal {s : Set Plane} (hs : IsRectangle s) : IsPolygonal s := by
  obtain ⟨a, b, hre, him, rfl⟩ := hs
  exact ⟨rectangleDiagonalTriangulation a b hre him⟩

end Tiling
