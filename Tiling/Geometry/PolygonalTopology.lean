import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Tiling.Geometry.Plane
import Tiling.Topology.IntersectionGraph

set_option linter.style.header false

/-!
# Topology of polygonal subsets of the plane

Finite triangulations make polygonal sets compact, regular closed, and null on their frontier.
The final declaration isolates the genuinely planar bridge between triangulation-independent
vertices and local straightness of the boundary.
-/

open Filter MeasureTheory Set Topology
open scoped Pointwise

namespace Tiling

/-- The boundary of `s` agrees near `x` with a one-dimensional affine subspace through `x`. -/
def BoundaryLocallyStraightAt (s : Set Plane) (x : Plane) : Prop :=
  ∃ L : AffineSubspace ℝ Plane,
    x ∈ L ∧ Module.finrank ℝ L.direction = 1 ∧
      ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ (L : Set Plane))

private def TriangleBoundaryGerm (t : Set Plane) (x : Plane) : Prop :=
  ∃ f : Plane →ₗ[ℝ] ℝ,
    (∃ u, f u = 1) ∧
    (∀ᶠ y in 𝓝 x, (y ∈ t ↔ 0 ≤ f (y - x))) ∧
    (∀ᶠ y in 𝓝 x, (y ∈ interior t ↔ 0 < f (y - x))) ∧
    ∀ᶠ y in 𝓝 x, (y ∈ frontier t ↔ f (y - x) = 0)

private theorem LinearMap.ker_finrank_of_exists_valueOne (f : Plane →ₗ[ℝ] ℝ)
    (h : ∃ u, f u = 1) : Module.finrank ℝ (LinearMap.ker f) = 1 := by
  obtain ⟨u, hu⟩ := h
  have hsurj : Function.Surjective f := by
    intro r
    refine ⟨r • u, ?_⟩
    rw [map_smul, hu, smul_eq_mul, mul_one]
  have hrank := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self,
    Complex.finrank_real_complex] at hrank
  omega

private theorem LinearMap.ker_le_ker_of_not_exists_pos_pos
    (f g : Plane →ₗ[ℝ] ℝ) (u : Plane) (hfu : f u = 1)
    (hdisj : ¬∃ z, 0 < f z ∧ 0 < g z) : LinearMap.ker f ≤ LinearMap.ker g := by
  intro z hz
  rw [LinearMap.mem_ker] at hz ⊢
  by_contra hgz
  have produces_common_positive {w : Plane} (hfw : f w = 0) (hgw : 0 < g w) : False := by
    let r : ℝ := (|g u| + 1) / g w
    have hgw_ne : g w ≠ 0 := ne_of_gt hgw
    apply hdisj
    refine ⟨r • w + u, ?_, ?_⟩
    · rw [map_add, map_smul, hfw, hfu, smul_zero, zero_add]
      norm_num
    · simp only [map_add, map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hgw_ne]
      linarith [neg_abs_le (g u)]
  rcases lt_or_gt_of_ne hgz with hgz_neg | hgz_pos
  · exact produces_common_positive (w := -z) (by simp [hz]) (by simpa using hgz_neg)
  · exact produces_common_positive hz hgz_pos

private theorem LinearMap.eq_neg_smul_of_not_exists_pos_pos
    (f g : Plane →ₗ[ℝ] ℝ) (u v : Plane) (hfu : f u = 1) (hgv : g v = 1)
    (hdisj : ¬∃ z, 0 < f z ∧ 0 < g z) :
    ∃ c : ℝ, c < 0 ∧ g = c • f := by
  have hker := LinearMap.ker_le_ker_of_not_exists_pos_pos f g u hfu hdisj
  let c := g u
  have hgf : g = c • f := by
    ext z
    have hzker : z - f z • u ∈ LinearMap.ker f := by
      rw [LinearMap.mem_ker]
      rw [map_sub, map_smul, hfu, smul_eq_mul, mul_one, sub_self]
    have hzero := hker hzker
    rw [LinearMap.mem_ker] at hzero
    simp only [map_sub, map_smul, smul_eq_mul] at hzero
    change g z = c * f z
    dsimp only [c]
    linarith
  refine ⟨c, ?_, hgf⟩
  have hc_nonpos : c ≤ 0 := by
    by_contra hc
    exact hdisj ⟨u, by simp [hfu], by simpa [c] using lt_of_not_ge hc⟩
  have hc_ne : c ≠ 0 := by
    intro hc
    have : g = 0 := by simpa [hc] using hgf
    rw [this, LinearMap.zero_apply] at hgv
    exact zero_ne_one hgv
  exact lt_of_le_of_ne hc_nonpos hc_ne

private theorem not_exists_pos_pos_of_aedisjoint {t u : Set Plane} {x : Plane}
    {f g : Plane →ₗ[ℝ] ℝ}
    (ht : ∀ᶠ y in 𝓝 x, (y ∈ interior t ↔ 0 < f (y - x)))
    (hu : ∀ᶠ y in 𝓝 x, (y ∈ interior u ↔ 0 < g (y - x)))
    (hdisj : AEDisjoint volume t u) : ¬∃ z, 0 < f z ∧ 0 < g z := by
  rintro ⟨z, hfz, hgz⟩
  let ray : ℝ → Plane := fun r ↦ r • z + x
  have hray : Tendsto ray (𝓝 0) (𝓝 x) := by
    have : Continuous ray := by fun_prop
    have hzero : ContinuousAt ray (0 : ℝ) := this.continuousAt
    have hray_zero : ray 0 = x := by simp [ray]
    rw [← hray_zero]
    exact hzero
  have hlocal : ∀ᶠ r in 𝓝 (0 : ℝ),
      (ray r ∈ interior t ↔ 0 < f (ray r - x)) ∧
      (ray r ∈ interior u ↔ 0 < g (ray r - x)) :=
    hray.eventually (ht.and hu)
  have hlocal_mem : {r : ℝ |
      (ray r ∈ interior t ↔ 0 < f (ray r - x)) ∧
      (ray r ∈ interior u ↔ 0 < g (ray r - x))} ∈ 𝓝 0 := hlocal
  rw [Metric.mem_nhds_iff] at hlocal_mem
  obtain ⟨ε, hε, hball⟩ := hlocal_mem
  let r := ε / 2
  have hr : 0 < r := div_pos hε (by norm_num)
  have hrball : r ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr]
    dsimp only [r]
    linarith
  have hlocal_r := hball hrball
  have hray_sub : ray r - x = r • z := by simp [ray]
  have hft : 0 < f (ray r - x) := by
    rw [hray_sub, map_smul, smul_eq_mul]
    exact mul_pos hr hfz
  have hgu : 0 < g (ray r - x) := by
    rw [hray_sub, map_smul, smul_eq_mul]
    exact mul_pos hr hgz
  have hinter : (interior t ∩ interior u).Nonempty :=
    ⟨ray r, hlocal_r.1.mpr hft, hlocal_r.2.mpr hgu⟩
  have hne : volume (interior t ∩ interior u) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero volume hinter
  exact hne (measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset) hdisj)

private theorem affineIndependent_of_twiceSignedArea_ne_zero (a b c : Plane)
    (harea : twiceSignedArea a b c ≠ 0) : AffineIndependent ℝ ![a, b, c] := by
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
    rw [twiceSignedArea]
    linear_combination (c.im - a.im) * hgre - (c.re - a.re) * hgim
  have hg1 : g 1 = 0 := by
    apply mul_right_cancel₀ harea
    rw [twiceSignedArea]
    linear_combination -(b.im - a.im) * hgre + (b.re - a.re) * hgim
  fin_cases i
  · exact hg0
  · exact hg1

private noncomputable def triangleAffineBasis (a b c : Plane)
    (harea : twiceSignedArea a b c ≠ 0) : AffineBasis (Fin 3) ℝ Plane where
  toFun := ![a, b, c]
  ind' := affineIndependent_of_twiceSignedArea_ne_zero a b c harea
  tot' := by
    apply (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
      (affineIndependent_of_twiceSignedArea_ne_zero a b c harea)).mpr
    simp [Complex.finrank_real_complex]

@[simp]
private theorem range_triangleAffineBasis (a b c : Plane)
    (harea : twiceSignedArea a b c ≠ 0) :
    Set.range (triangleAffineBasis a b c harea) = {a, b, c} := by
  change Set.range ![a, b, c] = {a, b, c}
  ext z
  simp only [Matrix.range_cons, Matrix.range_empty, Set.singleton_union,
    Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, or_false]

private theorem AffineBasis.point_mem_extremePoints_convexHull_range
    (b : AffineBasis (Fin 3) ℝ Plane) (i : Fin 3) :
    b i ∈ (convexHull ℝ (Set.range b)).extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨subset_convexHull ℝ _ (Set.mem_range_self i), ?_⟩
  intro y hy z hz hsegment
  have hycoord : ∀ j, 0 ≤ b.coord j y := by
    rw [b.convexHull_eq_nonneg_coord] at hy
    exact hy
  have hzcoord : ∀ j, 0 ≤ b.coord j z := by
    rw [b.convexHull_eq_nonneg_coord] at hz
    exact hz
  have hycoord_le_one : b.coord i y ≤ 1 := by
    calc
      b.coord i y ≤ ∑ j, b.coord j y :=
        Finset.single_le_sum (fun j _ ↦ hycoord j) (Finset.mem_univ i)
      _ = 1 := b.sum_coord_apply_eq_one y
  have hzcoord_le_one : b.coord i z ≤ 1 := by
    calc
      b.coord i z ≤ ∑ j, b.coord j z :=
        Finset.single_le_sum (fun j _ ↦ hzcoord j) (Finset.mem_univ i)
      _ = 1 := b.sum_coord_apply_eq_one z
  rw [openSegment_eq_image_lineMap] at hsegment
  obtain ⟨r, hr, hrline⟩ := hsegment
  have hcoordline := congrArg (b.coord i) hrline
  rw [AffineMap.apply_lineMap, b.coord_apply_eq, AffineMap.lineMap_apply_ring] at hcoordline
  have hyi : b.coord i y = 1 := by
    nlinarith [hr.1, hr.2]
  apply b.ext_elem
  intro j
  by_cases hji : j = i
  · subst j
    simp [hyi]
  · rw [b.coord_apply_ne hji]
    have hsum_erase : Finset.sum (Finset.univ.erase i) (fun k ↦ b.coord k y) = 0 := by
      have hsum := b.sum_coord_apply_eq_one y
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hyi] at hsum
      linarith
    exact (Finset.sum_eq_zero_iff_of_nonneg fun k _ ↦ hycoord k).mp hsum_erase j (by simp [hji])

private theorem AffineBasis.eq_point_of_two_coord_eq_zero
    (b : AffineBasis (Fin 3) ℝ Plane) {x : Plane} {i j : Fin 3}
    (hij : i ≠ j) (hi : b.coord i x = 0) (hj : b.coord j x = 0) :
    ∃ k, x = b k := by
  have hsum := b.sum_coord_apply_eq_one x
  simp only [Fin.sum_univ_three] at hsum
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · refine ⟨2, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
    · refine ⟨1, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
  · fin_cases j
    · refine ⟨2, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
    · exact (hij rfl).elim
    · refine ⟨0, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
  · fin_cases j
    · refine ⟨1, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
    · refine ⟨0, ?_⟩
      apply b.ext_elem
      intro n
      fin_cases n <;> simp_all
    · exact (hij rfl).elim

private theorem IsTriangle.boundaryGerm {t : Set Plane} (ht : IsTriangle t) {x : Plane}
    (hx : x ∈ frontier t) (hxextreme : x ∉ t.extremePoints ℝ) :
    TriangleBoundaryGerm t x := by
  obtain ⟨a, b, c, harea, rfl⟩ := ht
  let B := triangleAffineBasis a b c harea
  have hrange : Set.range B = {a, b, c} := range_triangleAffineBasis a b c harea
  rw [← hrange] at hx hxextreme ⊢
  have hclosed : IsClosed (convexHull ℝ (Set.range B)) :=
    (Set.toFinite (Set.range B)).isCompact_convexHull ℝ |>.isClosed
  rw [hclosed.frontier_eq] at hx
  have hxcoord_nonneg : ∀ i, 0 ≤ B.coord i x := by
    rw [B.convexHull_eq_nonneg_coord] at hx
    exact hx.1
  have hxnotint : x ∉ interior (convexHull ℝ (Set.range B)) := hx.2
  rw [B.interior_convexHull] at hxnotint
  simp only [Set.mem_ofPred_eq, not_forall] at hxnotint
  obtain ⟨k, hk_nonpos⟩ := hxnotint
  have hk : B.coord k x = 0 := le_antisymm (le_of_not_gt hk_nonpos) (hxcoord_nonneg k)
  have hother : ∀ j, j ≠ k → 0 < B.coord j x := by
    intro j hjk
    apply lt_of_le_of_ne (hxcoord_nonneg j)
    intro hj
    obtain ⟨m, hxm⟩ := AffineBasis.eq_point_of_two_coord_eq_zero B hjk hj.symm hk
    apply hxextreme
    rw [hxm]
    exact AffineBasis.point_mem_extremePoints_convexHull_range B m
  let f : Plane →ₗ[ℝ] ℝ := (B.coord k).linear
  have hcoord (y : Plane) : B.coord k y = f (y - x) := by
    calc
      B.coord k y = B.coord k y - B.coord k x := by rw [hk, sub_zero]
      _ = f (y - x) := ((B.coord k).linearMap_vsub y x).symm
  have hevent_other : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ k → 0 < B.coord j y := by
    rw [Filter.eventually_all]
    intro j
    by_cases hjk : j = k
    · filter_upwards [] with y
      exact fun h ↦ (h hjk).elim
    · exact ((continuous_barycentric_coord B j).continuousAt.eventually
        (isOpen_Ioi.mem_nhds (hother j hjk))).mono fun _ hy _ ↦ hy
  have hmem : ∀ᶠ y in 𝓝 x,
      (y ∈ convexHull ℝ (Set.range B) ↔ 0 ≤ f (y - x)) := by
    filter_upwards [hevent_other] with y hy
    rw [B.convexHull_eq_nonneg_coord]
    constructor
    · intro h
      simpa only [← hcoord] using h k
    · intro hk' j
      by_cases hjk : j = k
      · simpa only [hjk, hcoord] using hk'
      · exact (hy j hjk).le
  have hinterior : ∀ᶠ y in 𝓝 x,
      (y ∈ interior (convexHull ℝ (Set.range B)) ↔ 0 < f (y - x)) := by
    filter_upwards [hevent_other] with y hy
    rw [B.interior_convexHull]
    constructor
    · intro h
      simpa only [← hcoord] using h k
    · intro hk' j
      by_cases hjk : j = k
      · simpa only [hjk, hcoord] using hk'
      · exact hy j hjk
  refine ⟨f, ?_, hmem, hinterior, ?_⟩
  · refine ⟨B k - x, ?_⟩
    calc
      f (B k - x) = B.coord k (B k) - B.coord k x :=
        (B.coord k).linearMap_vsub (B k) x
      _ = 1 := by rw [B.coord_apply_eq, hk, sub_zero]
  · filter_upwards [hmem, hinterior] with y hymem hyinterior
    rw [hclosed.frontier_eq]
    constructor
    · rintro ⟨hyt, hyi⟩
      have hnonneg := hymem.mp hyt
      have hnotpos : ¬0 < f (y - x) := fun hpos ↦ hyi (hyinterior.mpr hpos)
      exact le_antisymm (le_of_not_gt hnotpos) hnonneg
    · intro hyzero
      refine ⟨hymem.mpr hyzero.symm.le, ?_⟩
      intro hyi
      exact (hyinterior.mp hyi).ne' hyzero

/-- A nondegenerate triangle has nonempty interior. -/
theorem IsTriangle.interior_nonempty {s : Set Plane} (hs : IsTriangle s) :
    (interior s).Nonempty := by
  obtain ⟨a, b, c, harea, rfl⟩ := hs
  rw [interior_convexHull_nonempty_iff_affineSpan_eq_top]
  rw [show ({a, b, c} : Set Plane) = Set.range ![a, b, c] by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Matrix.range_cons,
      Matrix.range_empty, Set.singleton_union]
    aesop]
  apply (AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one
    (affineIndependent_of_twiceSignedArea_ne_zero a b c harea)).mpr
  simp [Complex.finrank_real_complex]

/-- A triangle is compact. -/
theorem IsTriangle.isCompact {s : Set Plane} (hs : IsTriangle s) : IsCompact s := by
  obtain ⟨a, b, c, _, rfl⟩ := hs
  exact Set.toFinite {a, b, c} |>.isCompact_convexHull ℝ

/-- A nondegenerate triangle is the closure of its interior. -/
theorem IsTriangle.closure_interior {s : Set Plane} (hs : IsTriangle s) :
    closure (interior s) = s := by
  obtain ⟨a, b, c, harea, rfl⟩ := hs
  exact Convex.closure_interior_eq_closure_of_nonempty_interior
      (convex_convexHull ℝ ({a, b, c} : Set Plane))
      (IsTriangle.interior_nonempty ⟨a, b, c, harea, rfl⟩) |>.trans
        ((Set.toFinite {a, b, c}).isCompact_convexHull ℝ).isClosed.closure_eq

/-- A polygonal set is compact. -/
theorem IsPolygonal.isCompact {s : Set Plane} (hs : IsPolygonal s) : IsCompact s := by
  obtain ⟨triangulation⟩ := hs
  rw [← triangulation.sUnion_eq]
  exact triangulation.pieces.finite_toSet.isCompact_sUnion fun t ht ↦
    (triangulation.isTriangle t ht).isCompact

/-- A polygonal set is closed. -/
theorem IsPolygonal.isClosed {s : Set Plane} (hs : IsPolygonal s) : IsClosed s :=
  hs.isCompact.isClosed

/-- A polygonal set is bounded. -/
theorem IsPolygonal.isBounded {s : Set Plane} (hs : IsPolygonal s) :
    Bornology.IsBounded s :=
  hs.isCompact.isBounded

/-- A polygonal set is the closure of its interior. -/
theorem IsPolygonal.closure_interior {s : Set Plane} (hs : IsPolygonal s) :
    closure (interior s) = s := by
  obtain ⟨triangulation⟩ := hs
  let f : {t // t ∈ triangulation.pieces} → Set Plane := fun t ↦ t.1
  have hregular : ∀ t, closure (interior (f t)) = f t := fun t ↦
    (triangulation.isTriangle t.1 t.2).closure_interior
  have hunion : ⋃ t, f t = s := calc
    ⋃ t, f t = ⋃₀ (triangulation.pieces : Set (Set Plane)) := by ext x; simp [f]
    _ = s := triangulation.sUnion_eq
  rw [← hunion]
  exact (locallyFinite_of_finite f).closure_interior_iUnion_eq hregular

private theorem frontier_sUnion_subset_biUnion (F : Finset (Set Plane)) :
    frontier (⋃₀ (F : Set (Set Plane))) ⊆ ⋃ s ∈ F, frontier s := by
  induction F using Finset.induction_on with
  | empty => simp
  | @insert s F hs ih =>
      rw [Finset.coe_insert, sUnion_insert, Finset.set_biUnion_insert]
      exact (frontier_union_subset s (⋃₀ (F : Set (Set Plane)))).trans <|
        (Set.union_subset_union inter_subset_left inter_subset_right).trans <|
          Set.union_subset_union Subset.rfl ih

/-- The frontier of a polygonal set has zero planar volume. -/
theorem IsPolygonal.volume_frontier {s : Set Plane} (hs : IsPolygonal s) :
    volume (frontier s) = 0 := by
  obtain ⟨triangulation⟩ := hs
  rw [← triangulation.sUnion_eq]
  apply measure_mono_null (frontier_sUnion_subset_biUnion triangulation.pieces)
  apply (measure_biUnion_null_iff triangulation.pieces.countable_toSet).2
  intro t ht
  obtain ⟨a, b, c, _, rfl⟩ := triangulation.isTriangle t ht
  exact (convex_convexHull ℝ ({a, b, c} : Set Plane)).addHaar_frontier volume

/-- A polygonal set and its interior agree almost everywhere. -/
theorem IsPolygonal.interior_ae_eq {s : Set Plane} (hs : IsPolygonal s) :
    interior s =ᵐ[volume] s :=
  interior_ae_eq_of_null_frontier hs.volume_frontier

/-- A nonempty polygonal set has nonempty interior. -/
theorem IsPolygonal.interior_nonempty {s : Set Plane} (hs : IsPolygonal s)
    (hne : s.Nonempty) : (interior s).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro hinter
  apply hne.ne_empty
  rw [← hs.closure_interior, hinter, closure_empty]

/-- A nonempty polygonal set has positive planar volume. -/
theorem IsPolygonal.volume_pos {s : Set Plane} (hs : IsPolygonal s)
    (hne : s.Nonempty) : 0 < volume s :=
  (isOpen_interior.measure_pos volume (hs.interior_nonempty hne)).trans_le
    (measure_mono interior_subset)

private theorem IsTriangle.extremePoints_finite {s : Set Plane} (hs : IsTriangle s) :
    (s.extremePoints ℝ).Finite := by
  obtain ⟨a, b, c, _, rfl⟩ := hs
  exact (Set.toFinite {a, b, c}).subset extremePoints_convexHull_subset

/-- The triangulation-independent vertex set of a polygonal set is finite. -/
theorem IsPolygonal.vertexSet_finite {s : Set Plane} (hs : IsPolygonal s) :
    (vertexSet s).Finite := by
  obtain ⟨triangulation⟩ := hs
  apply (triangulation.pieces.finite_toSet.biUnion fun t ht ↦
    (triangulation.isTriangle t ht).extremePoints_finite).subset
  intro x hx
  obtain ⟨t, ht, hxt⟩ := hx triangulation
  exact mem_biUnion ht hxt

/-- Translating a triangle preserves nondegeneracy and triangularity. -/
theorem IsTriangle.vadd {s : Set Plane} (hs : IsTriangle s) (a : Plane) :
    IsTriangle (a +ᵥ s) := by
  obtain ⟨p, q, r, harea, rfl⟩ := hs
  refine ⟨a +ᵥ p, a +ᵥ q, a +ᵥ r, ?_, ?_⟩
  · simpa [twiceSignedArea] using harea
  · rw [← convexHull_vadd]
    congr 1
    ext x
    simp only [mem_vadd_set_iff_neg_vadd_mem, Set.mem_insert_iff,
      Set.mem_singleton_iff, vadd_eq_add]
    constructor
    · rintro (h | h | h)
      · left; rw [← h]; abel
      · right; left; rw [← h]; abel
      · right; right; rw [← h]; abel
    · rintro (h | h | h)
      · left; rw [h]; abel
      · right; left; rw [h]; abel
      · right; right; rw [h]; abel

/-- Translating two almost-everywhere disjoint planar sets by the same vector preserves
almost-everywhere disjointness. -/
theorem aedisjoint_vadd {s t : Set Plane} (a : Plane)
    (h : AEDisjoint volume s t) : AEDisjoint volume (a +ᵥ s) (a +ᵥ t) := by
  rw [AEDisjoint]
  have hinter : (a +ᵥ s) ∩ (a +ᵥ t) = a +ᵥ (s ∩ t) := by
    ext x
    simp [mem_vadd_set_iff_neg_vadd_mem]
  rw [hinter]
  have hpreimage : a +ᵥ (s ∩ t) = (fun x : Plane ↦ -a + x) ⁻¹' (s ∩ t) := by
    ext x
    simp [mem_vadd_set_iff_neg_vadd_mem]
  rw [hpreimage, measure_preimage_add]
  exact h

/-- Translate every triangle in a triangulation. -/
noncomputable def Triangulation.vadd {s : Set Plane} (T : Triangulation s) (a : Plane) :
    Triangulation (a +ᵥ s) where
  pieces := T.pieces.image (a +ᵥ ·)
  isTriangle := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact (T.isTriangle u hu).vadd a
  pairwiseAEDisjoint := by
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [Finset.mem_coe, Finset.mem_image] at ht₁ ht₂
    obtain ⟨u₁, hu₁, rfl⟩ := ht₁
    obtain ⟨u₂, hu₂, rfl⟩ := ht₂
    apply aedisjoint_vadd a
    apply T.pairwiseAEDisjoint hu₁ hu₂
    intro h
    apply hne
    rw [h]
  sUnion_eq := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx
      simp only [Finset.mem_coe, Finset.mem_image] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      rw [mem_vadd_set_iff_neg_vadd_mem]
      have : -a +ᵥ x ∈ ⋃₀ (T.pieces : Set (Set Plane)) :=
        Set.mem_sUnion_of_mem
          (by simpa only [mem_vadd_set_iff_neg_vadd_mem] using hxt) hu
      exact (Set.ext_iff.mp T.sUnion_eq (-a +ᵥ x)).mp this
    · intro hx
      rw [mem_vadd_set_iff_neg_vadd_mem] at hx
      have hx' : -a +ᵥ x ∈ ⋃₀ (T.pieces : Set (Set Plane)) :=
        (Set.ext_iff.mp T.sUnion_eq (-a +ᵥ x)).mpr hx
      obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp hx'
      apply Set.mem_sUnion_of_mem (t := a +ᵥ u)
      · simpa only [mem_vadd_set_iff_neg_vadd_mem] using hxu
      · simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨u, hu, rfl⟩

/-- Translating a polygonal set preserves polygonality. -/
theorem IsPolygonal.vadd {s : Set Plane} (hs : IsPolygonal s) (a : Plane) :
    IsPolygonal (a +ᵥ s) := by
  obtain ⟨T⟩ := hs
  exact ⟨T.vadd a⟩

/-- Nonzero real dilation preserves nondegenerate triangularity. -/
theorem IsTriangle.smul {s : Set Plane} (hs : IsTriangle s) (r : ℝ) (hr : r ≠ 0) :
    IsTriangle (r • s) := by
  obtain ⟨a, b, c, harea, rfl⟩ := hs
  refine ⟨r • a, r • b, r • c, ?_, ?_⟩
  · have heq : twiceSignedArea (r • a) (r • b) (r • c) =
        r ^ 2 * twiceSignedArea a b c := by
      simp only [twiceSignedArea, Complex.smul_re, Complex.smul_im, smul_eq_mul]
      ring
    rw [heq]
    exact mul_ne_zero (pow_ne_zero _ hr) harea
  · rw [← convexHull_smul]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨y, (rfl | rfl | rfl), rfl⟩ <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨a, by simp, rfl⟩
      · exact ⟨b, by simp, rfl⟩
      · exact ⟨c, by simp, rfl⟩

/-- Nonzero real dilation preserves almost-everywhere disjointness in the plane. -/
theorem aedisjoint_smul {s t : Set Plane} (r : ℝ) (hr : r ≠ 0)
    (h : AEDisjoint volume s t) : AEDisjoint volume (r • s) (r • t) := by
  rw [AEDisjoint]
  have hinter : (r • s) ∩ (r • t) = r • (s ∩ t) := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, ⟨z, hz, heq⟩⟩
      have hyz : y = z := (smul_right_injective Plane hr) heq.symm
      subst z
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hz⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, ⟨y, hz, rfl⟩⟩
  rw [hinter, Measure.addHaar_smul volume, h]
  simp

/-- Dilate every triangle in a triangulation by one nonzero real scalar. -/
noncomputable def Triangulation.smul {s : Set Plane} (T : Triangulation s)
    (r : ℝ) (hr : r ≠ 0) : Triangulation (r • s) where
  pieces := T.pieces.image (r • ·)
  isTriangle := by
    intro t ht
    simp only [Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    exact (T.isTriangle u hu).smul r hr
  pairwiseAEDisjoint := by
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [Finset.mem_coe, Finset.mem_image] at ht₁ ht₂
    obtain ⟨u₁, hu₁, rfl⟩ := ht₁
    obtain ⟨u₂, hu₂, rfl⟩ := ht₂
    apply aedisjoint_smul r hr
    apply T.pairwiseAEDisjoint hu₁ hu₂
    intro h
    apply hne
    rw [h]
  sUnion_eq := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hx
      simp only [Finset.mem_coe, Finset.mem_image] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      obtain ⟨y, hyu, hyx⟩ := hxt
      refine ⟨y, ?_, hyx⟩
      rw [← T.sUnion_eq]
      exact Set.mem_sUnion_of_mem hyu hu
    · rintro ⟨y, hys, rfl⟩
      have hys' : y ∈ ⋃₀ (T.pieces : Set (Set Plane)) := by rwa [T.sUnion_eq]
      obtain ⟨u, hu, hyu⟩ := Set.mem_sUnion.mp hys'
      apply Set.mem_sUnion_of_mem (t := r • u)
      · exact ⟨y, hyu, rfl⟩
      · simp only [Finset.mem_coe, Finset.mem_image]
        exact ⟨u, hu, rfl⟩

/-- Nonzero real dilation preserves polygonality. -/
theorem IsPolygonal.smul {s : Set Plane} (hs : IsPolygonal s) (r : ℝ) (hr : r ≠ 0) :
    IsPolygonal (r • s) := by
  obtain ⟨T⟩ := hs
  exact ⟨T.smul r hr⟩

private noncomputable def scalarLinearEquiv (r : ℝ) (hr : r ≠ 0) :
    Plane ≃ₗ[ℝ] Plane :=
  DistribMulAction.toLinearEquiv ℝ Plane (Units.mk0 r hr)

/-- Extreme points commute with a nonzero real dilation. -/
private theorem extremePoints_smul (r : ℝ) (hr : r ≠ 0) (s : Set Plane) :
    (r • s).extremePoints ℝ = r • s.extremePoints ℝ := by
  have h := image_extremePoints (scalarLinearEquiv r hr) s
  change (fun x : Plane ↦ r • x) '' extremePoints ℝ s =
    extremePoints ℝ ((fun x : Plane ↦ r • x) '' s) at h
  simpa only [Set.image_smul] using h.symm

private theorem extremePoints_vadd (a : Plane) (s : Set Plane) :
    (a +ᵥ s).extremePoints ℝ = a +ᵥ s.extremePoints ℝ := by
  ext x
  rw [mem_extremePoints_iff_left, mem_vadd_set_iff_neg_vadd_mem,
    mem_vadd_set_iff_neg_vadd_mem, mem_extremePoints_iff_left]
  constructor
  · rintro ⟨hxs, hxext⟩
    refine ⟨hxs, ?_⟩
    intro y₁ hy₁ y₂ hy₂ hseg
    have hseg' : x ∈ openSegment ℝ (a +ᵥ y₁) (a +ᵥ y₂) := by
      rw [← vadd_openSegment ℝ]
      exact ⟨-a +ᵥ x, hseg, by simp⟩
    have heq := hxext (a +ᵥ y₁)
      (by simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hy₁)
      (a +ᵥ y₂)
      (by simpa only [mem_vadd_set_iff_neg_vadd_mem, neg_vadd_vadd] using hy₂) hseg'
    exact vadd_left_cancel a (heq.trans (vadd_neg_vadd a x).symm)
  · rintro ⟨hxs, hxext⟩
    refine ⟨hxs, ?_⟩
    intro z₁ hz₁ z₂ hz₂ hseg
    have hz₁' : -a +ᵥ z₁ ∈ s := by
      simpa only [mem_vadd_set_iff_neg_vadd_mem] using hz₁
    have hz₂' : -a +ᵥ z₂ ∈ s := by
      simpa only [mem_vadd_set_iff_neg_vadd_mem] using hz₂
    have hseg' : -a +ᵥ x ∈ openSegment ℝ (-a +ᵥ z₁) (-a +ᵥ z₂) := by
      rw [← vadd_openSegment ℝ]
      exact ⟨x, hseg, by simp⟩
    have heq := hxext (-a +ᵥ z₁) hz₁' (-a +ᵥ z₂) hz₂' hseg'
    exact vadd_left_cancel (-a) heq

private noncomputable def Triangulation.cast {s t : Set Plane} (h : s = t)
    (T : Triangulation s) : Triangulation t :=
  h ▸ T

@[simp]
private theorem Triangulation.cast_pieces {s t : Set Plane} (h : s = t)
    (T : Triangulation s) :
    (T.cast h).pieces = T.pieces := by
  subst t
  rfl

/-- Intrinsic polygon vertices commute with translation. -/
theorem vertexSet_vadd (a : Plane) (s : Set Plane) :
    vertexSet (a +ᵥ s) = a +ᵥ vertexSet s := by
  ext x
  constructor
  · intro hx
    rw [mem_vadd_set_iff_neg_vadd_mem]
    change ∀ T : Triangulation s,
      ∃ t ∈ T.pieces, -a +ᵥ x ∈ t.extremePoints ℝ
    intro T
    change ∀ T' : Triangulation (a +ᵥ s),
      ∃ t ∈ T'.pieces, x ∈ t.extremePoints ℝ at hx
    obtain ⟨t, ht, hxt⟩ := hx (T.vadd a)
    simp only [Triangulation.vadd, Finset.mem_image] at ht
    obtain ⟨u, hu, rfl⟩ := ht
    refine ⟨u, hu, ?_⟩
    rw [extremePoints_vadd] at hxt
    simpa only [mem_vadd_set_iff_neg_vadd_mem] using hxt
  · intro hx
    rw [mem_vadd_set_iff_neg_vadd_mem] at hx
    change ∀ T : Triangulation s,
      ∃ t ∈ T.pieces, -a +ᵥ x ∈ t.extremePoints ℝ at hx
    change ∀ T' : Triangulation (a +ᵥ s),
      ∃ t ∈ T'.pieces, x ∈ t.extremePoints ℝ
    intro T'
    have hcancel : -a +ᵥ (a +ᵥ s) = s := by
      ext y
      simp only [mem_vadd_set_iff_neg_vadd_mem, vadd_vadd]
      have hz : -(-a + a) = (0 : Plane) := by abel
      rw [hz, zero_vadd]
    let U₀ : Triangulation (-a +ᵥ (a +ᵥ s)) := T'.vadd (-a)
    let U : Triangulation s := U₀.cast hcancel
    obtain ⟨u, hu, hxu⟩ := hx U
    have hu₀ : u ∈ U₀.pieces := by
      change u ∈ (U₀.cast hcancel).pieces at hu
      simpa only [Triangulation.cast_pieces] using hu
    simp only [U₀, Triangulation.vadd, Finset.mem_image] at hu₀
    obtain ⟨t, ht, rfl⟩ := hu₀
    refine ⟨t, ht, ?_⟩
    have hxtranslated : x ∈ a +ᵥ (-a +ᵥ t).extremePoints ℝ := by
      rw [mem_vadd_set_iff_neg_vadd_mem]
      exact hxu
    rw [← extremePoints_vadd] at hxtranslated
    simpa only [vadd_vadd, add_neg_cancel, zero_vadd] using hxtranslated

/-- Intrinsic polygon vertices commute with nonzero real dilation. -/
theorem vertexSet_smul (r : ℝ) (hr : r ≠ 0) (s : Set Plane) :
    vertexSet (r • s) = r • vertexSet s := by
  ext x
  constructor
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · change ∀ T : Triangulation s,
        ∃ t ∈ T.pieces, r⁻¹ • x ∈ t.extremePoints ℝ
      intro T
      change ∀ T' : Triangulation (r • s),
        ∃ t ∈ T'.pieces, x ∈ t.extremePoints ℝ at hx
      obtain ⟨t, ht, hxt⟩ := hx (T.smul r hr)
      simp only [Triangulation.smul, Finset.mem_image] at ht
      obtain ⟨u, hu, rfl⟩ := ht
      rw [extremePoints_smul r hr u] at hxt
      obtain ⟨y, hy, hyx⟩ := hxt
      refine ⟨u, hu, ?_⟩
      have hy_eq : y = r⁻¹ • x := by
        calc
          y = r⁻¹ • (r • y) := by simp [hr]
          _ = r⁻¹ • x := congrArg (fun z : Plane ↦ r⁻¹ • z) hyx
      simpa only [← hy_eq] using hy
    · simp [hr]
  · rintro ⟨y, hy, rfl⟩
    change ∀ T' : Triangulation (r • s),
      ∃ t ∈ T'.pieces, r • y ∈ t.extremePoints ℝ
    intro T'
    have hcancel : r⁻¹ • (r • s) = s := by
      simp [smul_smul, hr]
    let U₀ : Triangulation (r⁻¹ • (r • s)) :=
      T'.smul r⁻¹ (inv_ne_zero hr)
    let U : Triangulation s := U₀.cast hcancel
    change ∀ T : Triangulation s,
      ∃ t ∈ T.pieces, y ∈ t.extremePoints ℝ at hy
    obtain ⟨u, hu, hyu⟩ := hy U
    have hu₀ : u ∈ U₀.pieces := by
      change u ∈ (U₀.cast hcancel).pieces at hu
      simpa only [Triangulation.cast_pieces] using hu
    simp only [U₀, Triangulation.smul, Finset.mem_image] at hu₀
    obtain ⟨t, ht, rfl⟩ := hu₀
    refine ⟨t, ht, ?_⟩
    rw [extremePoints_smul r⁻¹ (inv_ne_zero hr) t] at hyu
    obtain ⟨z, hz, hzy⟩ := hyu
    have hz_eq : z = r • y := by
      calc
        z = r • (r⁻¹ • z) := by simp [hr]
        _ = r • y := congrArg (fun w : Plane ↦ r • w) hzy
    simpa only [← hz_eq] using hz

/-- Away from a triangulation-independent vertex, a polygonal frontier is locally straight.

This is the computational-geometry bridge between the universal triangulation definition of
`vertexSet` and the intrinsic proper boundary vertices used in the sliding argument. -/
theorem IsPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet
    {s : Set Plane} (hs : IsPolygonal s) {x : Plane} (hx : x ∈ frontier s)
    (hxv : x ∉ vertexSet s) : BoundaryLocallyStraightAt s x := by
  classical
  rw [vertexSet, Set.mem_ofPred_eq] at hxv
  push Not at hxv
  obtain ⟨T, hT⟩ := hxv
  have hxs : x ∈ s := by
    have := frontier_subset_closure hx
    rwa [hs.isClosed.closure_eq] at this
  have hxnotint : x ∉ interior s := by
    rw [hs.isClosed.frontier_eq] at hx
    exact hx.2
  have hxsUnion : x ∈ ⋃₀ (T.pieces : Set (Set Plane)) := by
    rwa [T.sUnion_eq]
  obtain ⟨t₀, ht₀, hxt₀⟩ := Set.mem_sUnion.mp hxsUnion
  have ht₀' : t₀ ∈ T.pieces := ht₀
  have piece_subset {t : Set Plane} (ht : t ∈ T.pieces) : t ⊆ s := by
    rw [← T.sUnion_eq]
    exact Set.subset_sUnion_of_mem ht
  have ht₀closed : IsClosed t₀ := (T.isTriangle t₀ ht₀').isCompact.isClosed
  have hxfrontier₀ : x ∈ frontier t₀ := by
    rw [ht₀closed.frontier_eq]
    exact ⟨hxt₀, fun hxi ↦ hxnotint (interior_mono (piece_subset ht₀') hxi)⟩
  obtain ⟨f, hfvalue, hfmem, hfinterior, hffrontier⟩ :=
    IsTriangle.boundaryGerm (T.isTriangle t₀ ht₀') hxfrontier₀ (hT t₀ ht₀')
  have unique_piece_at_x : ∀ t ∈ T.pieces, x ∈ t → t = t₀ := by
    intro t ht hxt
    by_contra hne
    have htclosed : IsClosed t := (T.isTriangle t ht).isCompact.isClosed
    have hxfrontier : x ∈ frontier t := by
      rw [htclosed.frontier_eq]
      exact ⟨hxt, fun hxi ↦ hxnotint (interior_mono (piece_subset ht) hxi)⟩
    obtain ⟨g, hgvalue, hgmem, hginterior, _⟩ :=
      IsTriangle.boundaryGerm (T.isTriangle t ht) hxfrontier (hT t ht)
    have haed : AEDisjoint volume t₀ t :=
      T.pairwiseAEDisjoint ht₀' ht (Ne.symm hne)
    have hnopos : ¬∃ z, 0 < f z ∧ 0 < g z :=
      not_exists_pos_pos_of_aedisjoint hfinterior hginterior haed
    obtain ⟨uf, huf⟩ := hfvalue
    obtain ⟨ug, hug⟩ := hgvalue
    obtain ⟨c, hc, hgf⟩ :=
      LinearMap.eq_neg_smul_of_not_exists_pos_pos f g uf ug huf hug hnopos
    have hunion_mem : ∀ᶠ y in 𝓝 x, y ∈ t₀ ∪ t := by
      filter_upwards [hfmem, hgmem] with y hyf hyg
      by_cases hfy : 0 ≤ f (y - x)
      · exact Or.inl (hyf.mpr hfy)
      · right
        have hgy : 0 ≤ g (y - x) := by
          rw [hgf]
          simp only [LinearMap.smul_apply, smul_eq_mul]
          exact (mul_pos_of_neg_of_neg hc (lt_of_not_ge hfy)).le
        exact hyg.mpr hgy
    have hxinterior_union : x ∈ interior (t₀ ∪ t) :=
      mem_interior_iff_mem_nhds.mpr hunion_mem
    apply hxnotint
    exact interior_mono (union_subset (piece_subset ht₀') (piece_subset ht)) hxinterior_union
  let U : Set Plane := ⋂ t ∈ T.pieces.erase t₀, tᶜ
  have hUopen : IsOpen U := by
    apply isOpen_biInter_finset
    intro t ht
    exact ((T.isTriangle t (Finset.mem_of_mem_erase ht)).isCompact.isClosed).isOpen_compl
  have hxU : x ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_compl_iff]
    intro t ht hxt
    exact (Finset.ne_of_mem_erase ht) (unique_piece_at_x t (Finset.mem_of_mem_erase ht) hxt)
  have hsets_on : Set.EqOn (· ∈ s) (· ∈ t₀) U := by
    intro y hyU
    apply propext
    constructor
    · intro hys
      have hys' : y ∈ ⋃₀ (T.pieces : Set (Set Plane)) := by rwa [T.sUnion_eq]
      obtain ⟨t, ht, hyt⟩ := Set.mem_sUnion.mp hys'
      have ht' : t ∈ T.pieces := ht
      by_cases h : t = t₀
      · simpa [h] using hyt
      · have htErase : t ∈ T.pieces.erase t₀ := Finset.mem_erase.mpr ⟨h, ht'⟩
        have hytc : y ∈ tᶜ := Set.mem_iInter.mp (Set.mem_iInter.mp hyU t) htErase
        exact (hytc hyt).elim
    · exact fun hyt ↦ piece_subset ht₀' hyt
  have hfrontiers : ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ frontier t₀) := by
    filter_upwards [hUopen.eventually_mem hxU] with y hyU
    have heq : s =ᶠ[𝓝 y] t₀ :=
      hsets_on.eventuallyEq_of_mem (hUopen.mem_nhds hyU)
    rw [hs.isClosed.frontier_eq, ht₀closed.frontier_eq]
    constructor
    · rintro ⟨hys, hysi⟩
      exact ⟨Eq.mp (hsets_on hyU) hys, fun hyti ↦ hysi (heq.mem_interior_iff.mpr hyti)⟩
    · rintro ⟨hyt, hyti⟩
      exact ⟨Eq.mpr (hsets_on hyU) hyt, fun hysi ↦ hyti (heq.mem_interior_iff.mp hysi)⟩
  let L : AffineSubspace ℝ Plane := AffineSubspace.mk' x (LinearMap.ker f)
  refine ⟨L, AffineSubspace.self_mem_mk' x (LinearMap.ker f), ?_, ?_⟩
  · dsimp only [L]
    rw [AffineSubspace.direction_mk']
    exact LinearMap.ker_finrank_of_exists_valueOne f hfvalue
  · filter_upwards [hfrontiers, hffrontier] with y hys hyt
    rw [hys, hyt]
    change f (y - x) = 0 ↔ y - x ∈ LinearMap.ker f
    rw [LinearMap.mem_ker]

end Tiling
