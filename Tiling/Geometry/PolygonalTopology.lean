import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Tiling.Geometry.Plane
import Tiling.Geometry.LocalLine
import Tiling.Topology.IntersectionGraph
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Topology of polygonal subsets of the plane

Finite triangulations make polygonal sets compact, regular closed, and null on their frontier.
The closing declarations isolate planar bridges from triangulation-independent vertices to local
boundary straightness, intrinsic vertical edges, and local axis-parallel boundary geometry.
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

private theorem IsPolygonal.exists_vertex_along_vertical_ray
    {D : Set Tiling.Plane} (hD : Tiling.IsPolygonal D) {p v : Tiling.Plane}
    (hp : p ∈ frontier D) (hvne : v ≠ 0) (hvre : v.re = 0)
    (hgerm : ∀ᶠ z in nhds p, z ∈ frontier D ↔ z.re = p.re) :
    ∃ b : ℝ, 0 < b ∧ p + b • v ∈ Tiling.vertexSet D ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b, p + t • v ∈ frontier D := by
  let φ : ℝ → Tiling.Plane := fun t ↦ p + t • v
  have hφ : Continuous φ := by fun_prop
  let F : Set ℝ := φ ⁻¹' frontier D
  have hFclosed : IsClosed F := isClosed_frontier.preimage hφ
  have hzeroF : (0 : ℝ) ∈ F := by simpa [F, φ] using hp
  have hF_bddAbove : BddAbove F := by
    obtain ⟨R, hR⟩ := hD.isBounded.subset_closedBall p
    refine ⟨R / ‖v‖, fun t ht ↦ ?_⟩
    have htD : φ t ∈ D := hD.isClosed.frontier_subset ht
    have hdist := hR htD
    rw [Metric.mem_closedBall] at hdist
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have habs : |t| * ‖v‖ ≤ R := by
      simpa [F, φ, dist_eq_norm, norm_smul, Real.norm_eq_abs] using hdist
    apply (le_div_iff₀ hvnorm).2
    exact (mul_le_mul_of_nonneg_right (le_abs_self t) hvnorm.le).trans habs
  have hparam : {t : ℝ | φ t ∈ frontier D ↔ (φ t).re = p.re} ∈ nhds 0 := by
    change {z | z ∈ frontier D ↔ z.re = p.re} ∈ nhds p at hgerm
    have hgerm' : {z | z ∈ frontier D ↔ z.re = p.re} ∈ nhds (φ 0) := by
      simpa [φ] using hgerm
    exact hφ.continuousAt.preimage_mem_nhds hgerm'
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hparam
  obtain ⟨e, he0, heu⟩ := exists_between hu
  have heF : e ∈ F := by
    have heIoo : e ∈ Set.Ioo l u := ⟨hl.trans he0, heu⟩
    apply (hlu heIoo).mpr
    simp [φ, hvre]
  let J : Set ℝ := connectedComponentIn F 0
  have hzeroJ : (0 : ℝ) ∈ J := mem_connectedComponentIn hzeroF
  have heJ : e ∈ J := by
    refine isPreconnected_Icc.subset_connectedComponentIn
      (left_mem_Icc.mpr he0.le) ?_ (right_mem_Icc.mpr he0.le)
    intro t ht
    have htIoo : t ∈ Set.Ioo l u := ⟨hl.trans_le ht.1, ht.2.trans_lt heu⟩
    apply (hlu htIoo).mpr
    simp [φ, hvre]
  have hJclosed : IsClosed J := by
    dsimp only [J]
    rw [connectedComponentIn_eq_image hzeroF]
    exact hFclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hJ_bddAbove : BddAbove J := hF_bddAbove.mono (connectedComponentIn_subset F 0)
  have hJnonempty : J.Nonempty := ⟨0, hzeroJ⟩
  let b : ℝ := sSup J
  have hbGreatest : IsGreatest J b := hJclosed.isGreatest_csSup hJnonempty hJ_bddAbove
  have hbJ : b ∈ J := hbGreatest.1
  have hbpos : 0 < b := he0.trans_le (hbGreatest.2 heJ)
  have hfrontier_of_mem_J {t : ℝ} (ht : t ∈ J) : φ t ∈ frontier D :=
    connectedComponentIn_subset F 0 ht
  have hbfrontier : φ b ∈ frontier D := hfrontier_of_mem_J hbJ
  have hbvertex : φ b ∈ Tiling.vertexSet D := by
    by_contra hbnotvertex
    have hstraight := hD.boundaryLocallyStraightAt_of_not_mem_vertexSet
      hbfrontier hbnotvertex
    obtain ⟨L, hbL, _hdim, hlocal⟩ := hstraight
    have hlineParam : {t : ℝ | φ t ∈ frontier D ↔ φ t ∈ (L : Set Tiling.Plane)} ∈
        nhds b := hφ.continuousAt.preimage_mem_nhds hlocal
    obtain ⟨l', u', ⟨hl'b, hbu'⟩, hlu'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hlineParam
    obtain ⟨t₁, ht₁l, ht₁b⟩ := exists_between (max_lt hl'b hbpos)
    have ht₁nonneg : 0 ≤ t₁ := (le_max_right l' 0).trans ht₁l.le
    have ht₁J : t₁ ∈ J :=
      isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ⟨ht₁nonneg, ht₁b.le⟩
    have ht₁L : φ t₁ ∈ L :=
      (hlu' ⟨(le_max_left l' 0).trans_lt ht₁l, ht₁b.trans hbu'⟩).mp
        (hfrontier_of_mem_J ht₁J)
    obtain ⟨t₂, hbt₂, ht₂u⟩ := exists_between hbu'
    have lineMap_eq (t : ℝ) :
        AffineMap.lineMap (φ b) (φ t₁) ((t - b) / (t₁ - b)) = φ t := by
      have ht₁bne : t₁ - b ≠ 0 := sub_ne_zero.mpr ht₁b.ne
      simp only [AffineMap.lineMap_apply, φ, vsub_eq_sub, vadd_eq_add]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
        div_mul_cancel₀ (t - b) ht₁bne, sub_smul]
      abel
    have hintervalF : Set.Icc b t₂ ⊆ F := by
      intro t ht
      have htL : φ t ∈ L := by
        rw [← lineMap_eq t]
        exact AffineMap.lineMap_mem _ hbL ht₁L
      have htlocal : t ∈ Set.Ioo l' u' := ⟨hl'b.trans_le ht.1, ht.2.trans_lt ht₂u⟩
      exact (hlu' htlocal).mpr htL
    have ht₂_component_b : t₂ ∈ connectedComponentIn F b :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hbt₂.le) hintervalF (right_mem_Icc.mpr hbt₂.le)
    have hcomponents : J = connectedComponentIn F b := connectedComponentIn_eq hbJ
    have ht₂J : t₂ ∈ J := hcomponents.symm ▸ ht₂_component_b
    exact (not_lt_of_ge (hbGreatest.2 ht₂J)) hbt₂
  refine ⟨b, hbpos, hbvertex, ?_⟩
  intro t ht
  exact hfrontier_of_mem_J
    (isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ht)

/-- A locally straight polygonal frontier contained in a vertical line coincides locally with
that line. -/
theorem IsPolygonal.exists_ball_frontier_iff_verticalLine_of_subset
    {D : Set Plane} (hD : IsPolygonal D) {p : Plane}
    (hp : p ∈ frontier D) (hpnotvertex : p ∉ vertexSet D)
    (hsubset : ∃ r > 0, ∀ z ∈ Metric.ball p r, z ∈ frontier D → z.re = p.re) :
    ∃ r > 0, ∀ z ∈ Metric.ball p r, (z ∈ frontier D ↔ z.re = p.re) := by
  obtain ⟨L, hpL, hLdim, hlocal⟩ :=
    hD.boundaryLocallyStraightAt_of_not_mem_vertexSet hp hpnotvertex
  obtain ⟨v, hv, r₁, hr₁, hgerm⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hpL hLdim hlocal
  obtain ⟨r₂, hr₂, hsub⟩ := hsubset
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  let t : ℝ := r / (2 * ‖v‖)
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < t := div_pos hr (mul_pos zero_lt_two hvnorm)
  let q : Plane := p + t • v
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [q, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp
    linarith
  have hqline : q ∈ affineLine p v := by
    apply (mem_affineLine_iff_exists_smul hv).2
    exact ⟨t, rfl⟩
  have hqfront : q ∈ frontier D :=
    (hgerm q (Metric.ball_subset_ball (min_le_left _ _) hqball)).2 hqline
  have hvre : v.re = 0 := by
    have hqre := hsub q (Metric.ball_subset_ball (min_le_right _ _) hqball) hqfront
    simp only [q, Complex.add_re, Complex.smul_re, smul_eq_mul] at hqre
    exact (mul_eq_zero.mp (by linarith : t * v.re = 0)).resolve_left ht.ne'
  have hvim : v.im ≠ 0 := by
    intro him
    apply hv
    apply Complex.ext <;> simp [hvre, him]
  refine ⟨r, hr, fun z hz ↦ (hgerm z
    (Metric.ball_subset_ball (min_le_left _ _) hz)).trans ?_⟩
  rw [mem_affineLine_iff_exists_smul hv]
  constructor
  · rintro ⟨a, rfl⟩
    simp [hvre]
  · intro hzre
    refine ⟨(z.im - p.im) / v.im, ?_⟩
    apply Complex.ext
    · simpa [hvre] using hzre
    · simp [hvim]

/-- A vertical local boundary germ of a compact polygonal set extends to a nondegenerate open
boundary segment whose endpoints are intrinsic polygonal vertices. -/
theorem IsPolygonal.exists_intrinsic_vertical_edge_of_germ
    {D : Set Tiling.Plane} (hD : Tiling.IsPolygonal D) {p : Tiling.Plane}
    (hp : p ∈ frontier D)
    (hgerm : ∀ᶠ z in nhds p, z ∈ frontier D ↔ z.re = p.re) :
    ∃ v w : Tiling.Plane, v ∈ Tiling.vertexSet D ∧ w ∈ Tiling.vertexSet D ∧
      v ≠ w ∧ v.re = w.re ∧ p ∈ openSegment ℝ v w ∧
      openSegment ℝ v w ⊆ frontier D := by
  obtain ⟨b, hb, hbvertex, hbfrontier⟩ :=
    hD.exists_vertex_along_vertical_ray hp Complex.I_ne_zero (by simp) hgerm
  obtain ⟨a, ha, havertex, hafrontier⟩ :=
    hD.exists_vertex_along_vertical_ray hp (neg_ne_zero.mpr Complex.I_ne_zero)
      (by simp) hgerm
  let v : Tiling.Plane := p + a • (-Complex.I)
  let w : Tiling.Plane := p + b • Complex.I
  have hvre : v.re = p.re := by simp [v]
  have hwre : w.re = p.re := by simp [w]
  have hvw : v ≠ w := by
    intro heq
    have him := congrArg Complex.im heq
    simp only [v, w, Complex.add_im, Complex.smul_im, Complex.neg_im,
      Complex.I_im, smul_eq_mul, mul_neg, mul_one] at him
    linarith
  have hpopen : p ∈ openSegment ℝ v w := by
    have ht : a / (a + b) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos ha (add_pos ha hb)
      · exact (div_lt_one (add_pos ha hb)).2 (lt_add_of_pos_right a hb)
    have hm := lineMap_mem_openSegment ℝ v w ht
    convert hm using 1
    simp only [AffineMap.lineMap_apply, v, w, vsub_eq_sub, vadd_eq_add]
    have hratio : a / (a + b) * (a + b) = a :=
      div_mul_cancel₀ a (ne_of_gt (add_pos ha hb))
    have hvsub : (p + b • Complex.I) - (p + a • -Complex.I) =
        (a + b) • Complex.I := by module
    rw [hvsub, smul_smul, hratio]
    module
  refine ⟨v, w, havertex, hbvertex, hvw, hvre.trans hwre.symm, hpopen, ?_⟩
  intro z hz
  rw [openSegment_eq_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  let t : ℝ := -a + c * (a + b)
  have htupper : t ≤ b := by dsimp only [t]; nlinarith [hc.2]
  have htlower : -a ≤ t := by dsimp only [t]; nlinarith [hc.1]
  have hpoint : AffineMap.lineMap v w c = p + t • Complex.I := by
    simp only [AffineMap.lineMap_apply, v, w, vsub_eq_sub, vadd_eq_add]
    dsimp only [t]
    module
  have hpoint' : (1 - c) • v + c • w = p + t • Complex.I := by
    rw [← hpoint]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  dsimp only at ⊢
  rw [hpoint']
  rcases le_total 0 t with ht | ht
  · exact hbfrontier t ⟨ht, htupper⟩
  · have hneg : -t ∈ Set.Icc (0 : ℝ) a := ⟨neg_nonneg.mpr ht, neg_le.mp htlower⟩
    have := hafrontier (-t) hneg
    simpa using this


private theorem frontier_rectangle_subset_coordinateLines (a b : Plane) :
    frontier (Complex.Rectangle a b) ⊆
      {z | z.re = a.re} ∪ {z | z.re = b.re} ∪
        {z | z.im = a.im} ∪ {z | z.im = b.im} := by
  intro z hz
  unfold Complex.Rectangle at hz
  rw [Complex.frontier_reProdIm] at hz
  simp only [mem_union, mem_ofPred_eq]
  rcases hz with hz | hz
  · rcases le_total a.im b.im with hab | hba
    · rw [uIcc_of_le hab, frontier_Icc hab] at hz
      rcases hz.2 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rw [uIcc_of_ge hba, frontier_Icc hba] at hz
      rcases hz.2 with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inr h)
  · rcases le_total a.re b.re with hab | hba
    · rw [uIcc_of_le hab, frontier_Icc hab] at hz
      rcases hz.1 with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr (by simpa using h)))
    · rw [uIcc_of_ge hba, frontier_Icc hba] at hz
      rcases hz.1 with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inl (Or.inl (by simpa using h)))

private theorem frontier_sUnion_finset_subset (F : Finset (Set Plane)) :
    frontier (⋃₀ (F : Set (Set Plane))) ⊆ ⋃ r ∈ F, frontier r := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert s F hs ih =>
      rw [Finset.coe_insert, sUnion_insert]
      intro z hz
      have hz' := frontier_union_subset s (⋃₀ (F : Set (Set Plane))) hz
      rcases hz' with hz' | hz'
      · exact mem_iUnion_of_mem s (mem_iUnion_of_mem (Finset.mem_insert_self s F) hz'.1)
      · have := ih hz'.2
        simp only [mem_iUnion] at this ⊢
        obtain ⟨t, htF, hzt⟩ := this
        exact ⟨t, Finset.mem_insert_of_mem htF, hzt⟩

/-- The boundary of an axis-parallel set is contained in finitely many vertical and horizontal
coordinate lines. -/
theorem IsAxisParallel.exists_finite_boundary_axisLines {D : Set Plane}
    (hD : IsAxisParallel D) :
    ∃ V H : Finset ℝ, ∀ z ∈ frontier D, z.re ∈ V ∨ z.im ∈ H := by
  classical
  obtain ⟨R⟩ := hD
  let P := {s // s ∈ R.pieces}
  let a : P → Plane := fun s ↦ Classical.choose (R.isRectangle s s.2)
  let b : P → Plane := fun s ↦ Classical.choose (Classical.choose_spec (R.isRectangle s s.2))
  have hab (s : P) : s.1 = Complex.Rectangle (a s) (b s) :=
    (Classical.choose_spec (Classical.choose_spec (R.isRectangle s s.2))).2.2
  let V : Finset ℝ := Finset.univ.biUnion fun s : P => {a s |>.re, b s |>.re}
  let H : Finset ℝ := Finset.univ.biUnion fun s : P => {a s |>.im, b s |>.im}
  refine ⟨V, H, fun z hz ↦ ?_⟩
  have hzpieces : z ∈ ⋃ r ∈ R.pieces, frontier r := by
    apply frontier_sUnion_finset_subset R.pieces
    rwa [R.sUnion_eq]
  simp only [mem_iUnion] at hzpieces
  obtain ⟨s, hs, hzs⟩ := hzpieces
  let s' : P := ⟨s, hs⟩
  change z ∈ frontier (s' : Set Plane) at hzs
  rw [hab s'] at hzs
  have haV : (a s').re ∈ V := Finset.mem_biUnion.mpr
    ⟨s', Finset.mem_univ _, by simp⟩
  have hbV : (b s').re ∈ V := Finset.mem_biUnion.mpr
    ⟨s', Finset.mem_univ _, by simp⟩
  have haH : (a s').im ∈ H := Finset.mem_biUnion.mpr
    ⟨s', Finset.mem_univ _, by simp⟩
  have hbH : (b s').im ∈ H := Finset.mem_biUnion.mpr
    ⟨s', Finset.mem_univ _, by simp⟩
  unfold Complex.Rectangle at hzs
  rw [Complex.frontier_reProdIm] at hzs
  rcases hzs with hzs | hzs
  · right
    have hi := hzs.2
    rcases le_total (a s').im (b s').im with hle | hge
    · rw [uIcc_of_le hle, frontier_Icc hle] at hi
      rcases hi with hi | hi
      · simpa [hi] using haH
      · simpa using hi ▸ hbH
    · rw [uIcc_of_ge hge, frontier_Icc hge] at hi
      rcases hi with hi | hi
      · simpa [hi] using hbH
      · simpa using hi ▸ haH
  · left
    have hr := hzs.1
    rcases le_total (a s').re (b s').re with hle | hge
    · rw [uIcc_of_le hle, frontier_Icc hle] at hr
      rcases hr with hr | hr
      · simpa [hr] using haV
      · simpa using hr ▸ hbV
    · rw [uIcc_of_ge hge, frontier_Icc hge] at hr
      rcases hr with hr | hr
      · simpa [hr] using hbV
      · simpa using hr ▸ haV

namespace IsAxisParallel

/-- Near any point, the frontier of a finite union of axis-parallel rectangles lies in the
coordinate cross through that point. -/
theorem localBoundaryCross {D : Set Plane} (hD : Tiling.IsAxisParallel D) (x : Plane) :
    ∃ r > 0, ∀ z ∈ Metric.ball x r, z ∈ frontier D →
      z.re = x.re ∨ z.im = x.im := by
  classical
  obtain ⟨R⟩ := hD
  have hpiece (s : Set Plane) (hs : s ∈ R.pieces) :
      ∀ᶠ z in nhds x, z ∈ frontier s → z.re = x.re ∨ z.im = x.im := by
    obtain ⟨a, b, _hre, _him, rfl⟩ := R.isRectangle s hs
    have line_eventually (f : Plane → ℝ) (hf : Continuous f) (c : ℝ) :
        ∀ᶠ z in nhds x, f z = c → f z = f x := by
      by_cases hc : f x = c
      · exact Filter.Eventually.of_forall fun z hz ↦ hz.trans hc.symm
      · exact Filter.mem_of_superset
          ((isClosed_singleton.preimage hf).isOpen_compl.mem_nhds hc)
          (fun z hz hzc ↦ False.elim (hz (by simpa using hzc)))
    have haRe := line_eventually Complex.re Complex.continuous_re a.re
    have hbRe := line_eventually Complex.re Complex.continuous_re b.re
    have haIm := line_eventually Complex.im Complex.continuous_im a.im
    have hbIm := line_eventually Complex.im Complex.continuous_im b.im
    filter_upwards [haRe, hbRe, haIm, hbIm] with z hza hzb hzia hzib hzfront
    have hp := frontier_rectangle_subset_coordinateLines a b hzfront
    simp only [mem_union, mem_ofPred_eq] at hp
    rcases hp with ((h | h) | h) | h
    · exact Or.inl (hza h)
    · exact Or.inl (hzb h)
    · exact Or.inr (hzia h)
    · exact Or.inr (hzib h)
  have hall : ∀ᶠ z in nhds x, ∀ s ∈ R.pieces,
      z ∈ frontier s → z.re = x.re ∨ z.im = x.im := by
    exact (eventually_all_finset R.pieces).2 fun s hs ↦ hpiece s hs
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r, hr, fun z hz hzfront ↦ ?_⟩
  have hzpieces : z ∈ ⋃ s ∈ R.pieces, frontier s := by
    apply frontier_sUnion_finset_subset R.pieces
    rw [R.sUnion_eq]
    exact hzfront
  simp only [mem_iUnion] at hzpieces
  obtain ⟨s, hsPieces, hzsFrontier⟩ := hzpieces
  exact hball hz s hsPieces hzsFrontier

end IsAxisParallel

end Tiling

namespace Tiling

private theorem im_eq_of_mem_openSegment_horizontal
    {a b p : Tiling.Plane} (hab : a.im = b.im)
    (hp : p ∈ openSegment ℝ a b) : p.im = a.im := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem exists_nearby_openSegment_point
    {a b p : Tiling.Plane} (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) {r : ℝ} (hr : 0 < r) :
    ∃ q ∈ openSegment ℝ a b, q ≠ p ∧ q ∈ Metric.ball p r := by
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨theta, htheta, rfl⟩ := hp
  let delta := min ((1 - theta) / 2) (r / (2 * dist a b))
  have habDist : 0 < dist a b := dist_pos.mpr hab
  have hdelta : 0 < delta := lt_min (half_pos (sub_pos.mpr htheta.2))
    (div_pos hr (mul_pos zero_lt_two habDist))
  have hthetaDelta : theta + delta ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨htheta.1.trans (lt_add_of_pos_right theta hdelta), ?_⟩
    have hdeltaLe : delta ≤ (1 - theta) / 2 := min_le_left _ _
    linarith [htheta.2]
  refine ⟨AffineMap.lineMap a b (theta + delta),
    lineMap_mem_openSegment (𝕜 := ℝ) a b hthetaDelta, ?_, ?_⟩
  · intro heq
    have hparam := AffineMap.lineMap_injective ℝ hab heq
    linarith
  · rw [Metric.mem_ball, dist_eq_norm]
    have hdiff : AffineMap.lineMap a b (theta + delta) -
        AffineMap.lineMap a b theta = delta • (b - a) := by
      rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module]
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hdelta]
    have hnorm : ‖b - a‖ = dist a b := by
      rw [dist_eq_norm]
      simpa only [norm_neg] using congrArg norm (by abel : b - a = -(a - b))
    rw [hnorm]
    have hdeltaLe : delta ≤ r / (2 * dist a b) := min_le_right _ _
    calc
      delta * dist a b ≤ (r / (2 * dist a b)) * dist a b :=
        mul_le_mul_of_nonneg_right hdeltaLe habDist.le
      _ = r / 2 := by field_simp
      _ < r := half_lt_self hr

private theorem re_eq_of_mem_openSegment_vertical
    {a b p : Tiling.Plane} (hab : a.re = b.re)
    (hp : p ∈ openSegment ℝ a b) : p.re = a.re := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring

/-- Perpendicular nondegenerate boundary segments can meet only at an intrinsic vertex. -/
theorem IsPolygonal.mem_vertexSet_of_perpendicular_openSegments
    {D : Set Plane} (hD : IsPolygonal D) {c d p v w : Tiling.Plane}
    (hcd : c ≠ d) (hcdIm : c.im = d.im)
    (hcdFrontier : openSegment ℝ c d ⊆ frontier D)
    (hpCD : p ∈ openSegment ℝ c d)
    (hvw : v ≠ w) (hvwRe : v.re = w.re)
    (hpVW : p ∈ openSegment ℝ v w)
    (hvwFrontier : openSegment ℝ v w ⊆ frontier D) : p ∈ vertexSet D := by
  by_contra hpNotVertex
  obtain ⟨L, hpL, hLdim, hlocal⟩ :=
    hD.boundaryLocallyStraightAt_of_not_mem_vertexSet
      (hcdFrontier hpCD) hpNotVertex
  obtain ⟨xi, hxi, r, hr, hball⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hpL hLdim hlocal
  obtain ⟨qH, hqHseg, hqHne, hqHball⟩ :=
    exists_nearby_openSegment_point hcd hpCD hr
  obtain ⟨qV, hqVseg, hqVne, hqVball⟩ :=
    exists_nearby_openSegment_point hvw hpVW hr
  have hqHline : qH ∈ Tiling.affineLine p xi :=
    (hball qH hqHball).mp (hcdFrontier hqHseg)
  have hqVline : qV ∈ Tiling.affineLine p xi :=
    (hball qV hqVball).mp (hvwFrontier hqVseg)
  obtain ⟨alpha, hqH⟩ := (Tiling.mem_affineLine_iff_exists_smul hxi).mp hqHline
  obtain ⟨beta, hqV⟩ := (Tiling.mem_affineLine_iff_exists_smul hxi).mp hqVline
  have halpha : alpha ≠ 0 := by
    intro halpha
    apply hqHne
    simpa only [halpha, zero_smul, add_zero] using hqH
  have hbeta : beta ≠ 0 := by
    intro hbeta
    apply hqVne
    simpa only [hbeta, zero_smul, add_zero] using hqV
  have hxiIm : xi.im = 0 := by
    have him := congrArg Complex.im hqH
    have hqHIm := im_eq_of_mem_openSegment_horizontal hcdIm hqHseg
    have hpIm := im_eq_of_mem_openSegment_horizontal hcdIm hpCD
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at him
    have : alpha * xi.im = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left halpha
  have hxiRe : xi.re = 0 := by
    have hre := congrArg Complex.re hqV
    have hqVRe := re_eq_of_mem_openSegment_vertical hvwRe hqVseg
    have hpRe := re_eq_of_mem_openSegment_vertical hvwRe hpVW
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hre
    have : beta * xi.re = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hbeta
  exact hxi (Complex.ext hxiRe hxiIm)


end Tiling

open Function
namespace Tiling

/-- Finite almost-disjoint blocks can be flattened without changing the
geometric content of a triangulation. -/
noncomputable def Triangulation.finiteUnion
    {ι : Type*} [Fintype ι] {s : ι → Set Plane}
    (T : ∀ i, Triangulation (s i))
    (hpair : Pairwise (AEDisjoint volume on s)) :
    Triangulation (⋃ i, s i) where
  pieces := Finset.univ.biUnion (fun i => (T i).pieces)
  isTriangle := by
    intro u hu
    obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
    exact (T i).isTriangle u hui
  pairwiseAEDisjoint := by
    intro u hu v hv huv
    obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hv
    by_cases hij : i = j
    · subst j
      exact (T i).pairwiseAEDisjoint hui hvj huv
    · apply (hpair hij).mono
      · rw [← (T i).sUnion_eq]
        exact Set.subset_sUnion_of_mem hui
      · rw [← (T j).sUnion_eq]
        exact Set.subset_sUnion_of_mem hvj
  sUnion_eq := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp hx
      obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨i,
        (T i).sUnion_eq ▸ Set.mem_sUnion.mpr ⟨u, hui, hxu⟩⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [← (T i).sUnion_eq] at hxi
      obtain ⟨u, hui, hxu⟩ := Set.mem_sUnion.mp hxi
      exact Set.mem_sUnion.mpr ⟨u,
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hui⟩, hxu⟩

/-- The parallel finite-union construction for axis-parallel rectangles. -/
noncomputable def Rectangulation.finiteUnion
    {ι : Type*} [Fintype ι] {s : ι → Set Plane}
    (R : ∀ i, Rectangulation (s i))
    (hpair : Pairwise (AEDisjoint volume on s)) :
    Rectangulation (⋃ i, s i) where
  pieces := Finset.univ.biUnion (fun i => (R i).pieces)
  isRectangle := by
    intro u hu
    obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
    exact (R i).isRectangle u hui
  pairwiseAEDisjoint := by
    intro u hu v hv huv
    obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨j, _, hvj⟩ := Finset.mem_biUnion.mp hv
    by_cases hij : i = j
    · subst j
      exact (R i).pairwiseAEDisjoint hui hvj huv
    · apply (hpair hij).mono
      · rw [← (R i).sUnion_eq]
        exact Set.subset_sUnion_of_mem hui
      · rw [← (R j).sUnion_eq]
        exact Set.subset_sUnion_of_mem hvj
  sUnion_eq := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hxu⟩ := Set.mem_sUnion.mp hx
      obtain ⟨i, _, hui⟩ := Finset.mem_biUnion.mp hu
      exact Set.mem_iUnion.mpr ⟨i,
        (R i).sUnion_eq ▸ Set.mem_sUnion.mpr ⟨u, hui, hxu⟩⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [← (R i).sUnion_eq] at hxi
      obtain ⟨u, hui, hxu⟩ := Set.mem_sUnion.mp hxi
      exact Set.mem_sUnion.mpr ⟨u,
        Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hui⟩, hxu⟩

end Tiling

namespace Tiling
private theorem sub_mem_uIcc_iff_add (a x p q : ℝ) :
    -a + x ∈ Set.uIcc p q ↔ x ∈ Set.uIcc (a + p) (a + q) := by
  simp only [Set.mem_uIcc]
  constructor <;> rintro (h | h) <;> [left; right; left; right] <;>
    constructor <;> linarith

private theorem vadd_rectangle (a p q : Plane) :
    a +ᵥ Complex.Rectangle p q = Complex.Rectangle (a + p) (a + q) := by
  ext z
  simp only [Complex.Rectangle, Set.mem_vadd_set_iff_neg_vadd_mem,
    Complex.mem_reProdIm, vadd_eq_add, Complex.add_re, Complex.add_im,
    Complex.neg_re, Complex.neg_im, sub_mem_uIcc_iff_add]

theorem IsRectangle.vadd {s : Set Plane}
    (hs : Tiling.IsRectangle s) (a : Plane) :
    Tiling.IsRectangle (a +ᵥ s) := by
  obtain ⟨p, q, hre, him, rfl⟩ := hs
  exact ⟨a + p, a + q, by simpa using hre, by simpa using him,
    vadd_rectangle a p q⟩

noncomputable def Rectangulation.vadd {s : Set Plane}
    (R : Tiling.Rectangulation s) (a : Plane) :
    Tiling.Rectangulation (a +ᵥ s) where
  pieces := R.pieces.image (a +ᵥ ·)
  isRectangle := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact IsRectangle.vadd (R.isRectangle v hv) a
  pairwiseAEDisjoint := by
    intro u hu v hv huv
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hv
    apply Tiling.aedisjoint_vadd a
    apply R.pairwiseAEDisjoint hu₀ hv₀
    intro heq
    exact huv (by rw [heq])
  sUnion_eq := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, hzu⟩ := Set.mem_sUnion.mp hz
      obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzu ⊢
      rw [← R.sUnion_eq]
      exact Set.mem_sUnion.mpr ⟨u₀, hu₀, hzu⟩
    · intro hz
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hz
      rw [← R.sUnion_eq] at hz
      obtain ⟨u₀, hu₀, hzu⟩ := Set.mem_sUnion.mp hz
      exact Set.mem_sUnion.mpr ⟨a +ᵥ u₀,
        Finset.mem_image.mpr ⟨u₀, hu₀, rfl⟩,
        by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hzu⟩


end Tiling

/-! Rational-slopes reviewed native additions: proved foundation slice. -/

set_option autoImplicit false
set_option linter.style.header false

open Function Filter MeasureTheory Set
open scoped BigOperators Pointwise Topology

noncomputable section

namespace Tiling

def interiorComponents (s : Set Plane) : Set (Set Plane) :=
  {O | ∃ x ∈ interior s, O = connectedComponentIn (interior s) x}

theorem interiorComponent_basic {s O : Set Plane}
    (hO : O ∈ interiorComponents s) :
    IsOpen O ∧ IsConnected O ∧ O ⊆ interior s := by
  obtain ⟨x, hx, rfl⟩ := hO
  exact ⟨isOpen_interior.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hx, connectedComponentIn_subset _ _⟩

theorem interiorComponent_closure_inter_interior_eq {s O : Set Plane}
    (hO : O ∈ interiorComponents s) :
    closure O ∩ interior s = O := by
  obtain ⟨x, hx, rfl⟩ := hO
  apply Subset.antisymm
  · rintro y ⟨hy, hys⟩
    rw [connectedComponentIn_eq_image hx] at hy ⊢
    have hclosed : IsClosed (connectedComponent (⟨x, hx⟩ : interior s)) :=
      isClosed_connectedComponent
    have hm := (Topology.IsInducing.subtypeVal.isClosed_iff').mp hclosed
    exact ⟨⟨y, hys⟩, hm ⟨y, hys⟩ hy, rfl⟩
  · exact fun y hy ↦ ⟨subset_closure hy, connectedComponentIn_subset _ _ hy⟩

theorem Triangulation.interiorComponent_subfamily {s O : Set Plane}
    (T : Triangulation s) (hO : O ∈ interiorComponents s) :
    ∃ F : Finset (Set Plane), F ⊆ T.pieces ∧
      (∀ t ∈ F, interior t ⊆ O) ∧
      (∀ t ∈ T.pieces, t ∈ F ↔ (interior t ∩ O).Nonempty) ∧
      closure O = ⋃₀ (F : Set (Set Plane)) := by
  classical
  let F := T.pieces.filter fun t ↦ (interior t ∩ O).Nonempty
  have hFT : F ⊆ T.pieces := Finset.filter_subset _ _
  have hts : ∀ t ∈ T.pieces, t ⊆ s := by
    intro t ht x hx
    rw [← T.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨t, ht, hx⟩
  have hsel : ∀ t ∈ F, interior t ⊆ O := by
    intro t ht
    obtain ⟨htT, y, hyt, hyO⟩ := Finset.mem_filter.mp ht
    obtain ⟨x, hx, hOx⟩ := hO
    have hc : IsPreconnected (interior t) := by
      obtain ⟨a, b, c, _, rfl⟩ := T.isTriangle t htT
      exact (convex_convexHull ℝ ({a, b, c} : Set Plane)).interior.isPreconnected
    rw [hOx] at hyO ⊢
    rw [connectedComponentIn_eq hyO]
    exact hc.subset_connectedComponentIn hyt (interior_mono (hts t htT))
  have hCclosed : IsClosed (⋃₀ (F : Set (Set Plane))) :=
    (F.finite_toSet.isCompact_sUnion fun t ht ↦ (T.isTriangle t (hFT ht)).isCompact).isClosed
  let D : Set Plane := ⋃ t : {t // t ∈ T.pieces}, interior (t : Set Plane)
  have hD : closure D = s := by
    dsimp only [D]
    rw [closure_iUnion_of_finite]
    simp_rw [fun t : {t // t ∈ T.pieces} ↦ (T.isTriangle t.1 t.2).closure_interior]
    calc
      (⋃ t : {t // t ∈ T.pieces}, (t : Set Plane)) = ⋃₀ (T.pieces : Set (Set Plane)) := by
        ext x
        simp
      _ = s := T.sUnion_eq
  have hDO : D ∩ O ⊆ ⋃₀ (F : Set (Set Plane)) := by
    rintro x ⟨hxD, hxO⟩
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxD
    exact Set.mem_sUnion.mpr ⟨t.1, Finset.mem_filter.mpr ⟨t.2, x, hxt, hxO⟩,
      interior_subset hxt⟩
  have hOC : O ⊆ ⋃₀ (F : Set (Set Plane)) := by
    intro x hx
    have hxc : x ∈ closure D ∩ O := ⟨hD.symm ▸
      interior_subset ((interiorComponent_basic hO).2.2 hx), hx⟩
    exact closure_minimal hDO hCclosed ((interiorComponent_basic hO).1.closure_inter hxc)
  refine ⟨F, hFT, hsel, ?_, Subset.antisymm (closure_minimal hOC hCclosed) ?_⟩
  · intro t ht
    simp [F, ht]
  · rintro x ⟨t, ht, hxt⟩
    rw [← (T.isTriangle t (hFT ht)).closure_interior] at hxt
    exact closure_mono (hsel t ht) hxt

private theorem component_piece_injection {s : Set Plane} (T : Triangulation s) :
    ∃ f : ↥(interiorComponents s) → {t // t ∈ T.pieces}, Injective f := by
  classical
  have hex : ∀ O : ↥(interiorComponents s),
      ∃ t : {t // t ∈ T.pieces}, interior (t : Set Plane) ⊆ (O : Set Plane) := by
    intro O
    obtain ⟨F, hFT, hsel, _, hF⟩ := T.interiorComponent_subfamily O.2
    obtain ⟨x, hx⟩ := (interiorComponent_basic O.2).2.1.nonempty
    have hxc : x ∈ ⋃₀ (F : Set (Set Plane)) := hF ▸ subset_closure hx
    obtain ⟨t, ht, _⟩ := Set.mem_sUnion.mp hxc
    exact ⟨⟨t, hFT ht⟩, hsel t ht⟩
  choose f hf using hex
  refine ⟨f, ?_⟩
  intro O P heq
  apply Subtype.ext
  obtain ⟨x, hx⟩ := (T.isTriangle (f O).1 (f O).2).interior_nonempty
  have hxP : x ∈ interior ((f P).1) := heq ▸ hx
  obtain ⟨y, hy, hOy⟩ := O.2
  obtain ⟨z, hz, hPz⟩ := P.2
  have hxo := hf O hx
  have hxp := hf P hxP
  rw [hOy] at hxo
  rw [hPz] at hxp
  exact hOy.trans ((connectedComponentIn_eq hxo).trans
    (connectedComponentIn_eq hxp).symm) |>.trans hPz.symm

theorem IsPolygonal.interiorComponents_finite {s : Set Plane} (hs : IsPolygonal s) :
    (interiorComponents s).Finite := by
  obtain ⟨T⟩ := hs
  obtain ⟨f, hf⟩ := component_piece_injection T
  have : Finite ↥(interiorComponents s) := Finite.of_injective f hf
  exact Set.toFinite _

theorem Triangulation.interiorComponents_card_le {s : Set Plane} (T : Triangulation s) :
    Nat.card ↥(interiorComponents s) ≤ T.pieces.card := by
  obtain ⟨f, hf⟩ := component_piece_injection T
  simpa using Nat.card_le_card_of_injective f hf

theorem IsPolygonal.interiorComponent_closure_isPolygonal {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s) :
    IsPolygonal (closure O) := by
  obtain ⟨T⟩ := hs
  obtain ⟨F, hFT, _, _, hF⟩ := T.interiorComponent_subfamily hO
  exact ⟨{
    pieces := F
    isTriangle := fun t ht ↦ T.isTriangle t (hFT ht)
    pairwiseAEDisjoint := T.pairwiseAEDisjoint.mono hFT
    sUnion_eq := hF.symm }⟩

theorem IsPolygonal.interiorComponent_closure_compact_positive {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s) :
    IsCompact (closure O) ∧ 0 < volume (closure O) ∧
      volume (closure O) ≠ ⊤ := by
  have hC := hs.interiorComponent_closure_isPolygonal hO
  have hne := (interiorComponent_basic hO).2.1.nonempty.mono subset_closure
  exact ⟨hC.isCompact, hC.volume_pos hne, hC.isCompact.measure_ne_top⟩

theorem IsPolygonal.interiorComponent_interior_closure_eq {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s) :
    interior (closure O) = O := by
  obtain ⟨ho, _, hos⟩ := interiorComponent_basic hO
  have hCs : closure O ⊆ s := closure_minimal (hos.trans interior_subset) hs.isClosed
  apply Subset.antisymm
  · intro x hx
    rw [← interiorComponent_closure_inter_interior_eq hO]
    exact ⟨interior_subset hx, interior_mono hCs hx⟩
  · exact interior_maximal subset_closure ho

theorem IsPolygonal.iUnion_closure_interiorComponents {s : Set Plane}
    (hs : IsPolygonal s) :
    (⋃ O ∈ interiorComponents s, closure O) = s := by
  have hu : (⋃ O ∈ interiorComponents s, O) = interior s := by
    apply Subset.antisymm
    · rintro x hx
      obtain ⟨O, hO, hxO⟩ := Set.mem_iUnion₂.mp hx
      exact (interiorComponent_basic hO).2.2 hxO
    · intro x hx
      exact Set.mem_iUnion₂.mpr ⟨connectedComponentIn (interior s) x,
        ⟨x, hx, rfl⟩, mem_connectedComponentIn hx⟩
  rw [← (hs.interiorComponents_finite.closure_biUnion fun O ↦ O), hu,
    hs.closure_interior]

theorem IsPolygonal.interiorComponent_frontier_eq {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s) :
    frontier O = frontier (closure O) := by
  rw [frontier, frontier, closure_closure,
    hs.interiorComponent_interior_closure_eq hO,
    (interiorComponent_basic hO).1.interior_eq]

theorem IsPolygonal.interiorComponent_frontier_subset {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s) :
    frontier (closure O) ⊆ frontier s := by
  have hos := (interiorComponent_basic hO).2.2
  have hCs : closure O ⊆ s := closure_minimal (hos.trans interior_subset) hs.isClosed
  rw [frontier, closure_closure,
    hs.interiorComponent_interior_closure_eq hO,
    frontier, hs.isClosed.closure_eq]
  rintro x ⟨hx, hxo⟩
  refine ⟨hCs hx, fun hxi ↦ hxo ?_⟩
  rw [← interiorComponent_closure_inter_interior_eq hO]
  exact ⟨hx, hxi⟩

theorem interiorComponents_pairwiseDisjoint (s : Set Plane) :
    (interiorComponents s).Pairwise (fun O P => Disjoint O P) := by
  rintro O ⟨x, hx, rfl⟩ P ⟨y, hy, rfl⟩ hne
  rw [Set.disjoint_left]
  intro z hzO hzP
  exact hne ((connectedComponentIn_eq hzO).trans (connectedComponentIn_eq hzP).symm)

theorem IsPolygonal.interiorComponentClosures_pairwiseAEDisjoint {s : Set Plane}
    (hs : IsPolygonal s) :
    (interiorComponents s).Pairwise
      (fun O P => AEDisjoint volume (closure O) (closure P)) := by
  intro O hO P hP hne
  apply measure_mono_null _ hs.volume_frontier
  rintro x ⟨hxO, hxP⟩
  have hos := (interiorComponent_basic hO).2.2
  have hCs : closure O ⊆ s := closure_minimal (hos.trans interior_subset) hs.isClosed
  rw [frontier, hs.isClosed.closure_eq]
  refine ⟨hCs hxO, ?_⟩
  intro hxi
  have hxo : x ∈ O := by
    rw [← interiorComponent_closure_inter_interior_eq hO]
    exact ⟨hxO, hxi⟩
  have hxp : x ∈ P := by
    rw [← interiorComponent_closure_inter_interior_eq hP]
    exact ⟨hxP, hxi⟩
  exact Set.disjoint_left.mp (interiorComponents_pairwiseDisjoint s hO hP hne) hxo hxp

private theorem IsPolygonal.exists_vertex_along_ray_rsPrivate
    {D : Set Tiling.Plane} (hD : Tiling.IsPolygonal D) {p v : Tiling.Plane}
    (hp : p ∈ frontier D) (hvne : v ≠ 0)
    (hgerm : ∀ᶠ z in nhds p, z ∈ frontier D ↔ z ∈ affineLine p v) :
    ∃ b : ℝ, 0 < b ∧ p + b • v ∈ Tiling.vertexSet D ∧
      ∀ t ∈ Set.Icc (0 : ℝ) b, p + t • v ∈ frontier D := by
  let φ : ℝ → Tiling.Plane := fun t ↦ p + t • v
  have hφ : Continuous φ := by fun_prop
  let F : Set ℝ := φ ⁻¹' frontier D
  have hFclosed : IsClosed F := isClosed_frontier.preimage hφ
  have hzeroF : (0 : ℝ) ∈ F := by simpa [F, φ] using hp
  have hF_bddAbove : BddAbove F := by
    obtain ⟨R, hR⟩ := hD.isBounded.subset_closedBall p
    refine ⟨R / ‖v‖, fun t ht ↦ ?_⟩
    have htD : φ t ∈ D := hD.isClosed.frontier_subset ht
    have hdist := hR htD
    rw [Metric.mem_closedBall] at hdist
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    have habs : |t| * ‖v‖ ≤ R := by
      simpa [F, φ, dist_eq_norm, norm_smul, Real.norm_eq_abs] using hdist
    apply (le_div_iff₀ hvnorm).2
    exact (mul_le_mul_of_nonneg_right (le_abs_self t) hvnorm.le).trans habs
  have hparam : {t : ℝ | φ t ∈ frontier D ↔ φ t ∈ affineLine p v} ∈ nhds 0 := by
    change {z | z ∈ frontier D ↔ z ∈ affineLine p v} ∈ nhds p at hgerm
    have hgerm' : {z | z ∈ frontier D ↔ z ∈ affineLine p v} ∈ nhds (φ 0) := by
      simpa [φ] using hgerm
    exact hφ.continuousAt.preimage_mem_nhds hgerm'
  obtain ⟨l, u, ⟨hl, hu⟩, hlu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hparam
  obtain ⟨e, he0, heu⟩ := exists_between hu
  have heF : e ∈ F := by
    have heIoo : e ∈ Set.Ioo l u := ⟨hl.trans he0, heu⟩
    apply (hlu heIoo).mpr
    exact vadd_smul_mem_affineLine p v _
  let J : Set ℝ := connectedComponentIn F 0
  have hzeroJ : (0 : ℝ) ∈ J := mem_connectedComponentIn hzeroF
  have heJ : e ∈ J := by
    refine isPreconnected_Icc.subset_connectedComponentIn
      (left_mem_Icc.mpr he0.le) ?_ (right_mem_Icc.mpr he0.le)
    intro t ht
    have htIoo : t ∈ Set.Ioo l u := ⟨hl.trans_le ht.1, ht.2.trans_lt heu⟩
    apply (hlu htIoo).mpr
    exact vadd_smul_mem_affineLine p v _
  have hJclosed : IsClosed J := by
    dsimp only [J]
    rw [connectedComponentIn_eq_image hzeroF]
    exact hFclosed.isClosedMap_subtype_val _ isClosed_connectedComponent
  have hJ_bddAbove : BddAbove J := hF_bddAbove.mono (connectedComponentIn_subset F 0)
  have hJnonempty : J.Nonempty := ⟨0, hzeroJ⟩
  let b : ℝ := sSup J
  have hbGreatest : IsGreatest J b := hJclosed.isGreatest_csSup hJnonempty hJ_bddAbove
  have hbJ : b ∈ J := hbGreatest.1
  have hbpos : 0 < b := he0.trans_le (hbGreatest.2 heJ)
  have hfrontier_of_mem_J {t : ℝ} (ht : t ∈ J) : φ t ∈ frontier D :=
    connectedComponentIn_subset F 0 ht
  have hbfrontier : φ b ∈ frontier D := hfrontier_of_mem_J hbJ
  have hbvertex : φ b ∈ Tiling.vertexSet D := by
    by_contra hbnotvertex
    have hstraight := hD.boundaryLocallyStraightAt_of_not_mem_vertexSet
      hbfrontier hbnotvertex
    obtain ⟨L, hbL, _hdim, hlocal⟩ := hstraight
    have hlineParam : {t : ℝ | φ t ∈ frontier D ↔ φ t ∈ (L : Set Tiling.Plane)} ∈
        nhds b := hφ.continuousAt.preimage_mem_nhds hlocal
    obtain ⟨l', u', ⟨hl'b, hbu'⟩, hlu'⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp hlineParam
    obtain ⟨t₁, ht₁l, ht₁b⟩ := exists_between (max_lt hl'b hbpos)
    have ht₁nonneg : 0 ≤ t₁ := (le_max_right l' 0).trans ht₁l.le
    have ht₁J : t₁ ∈ J :=
      isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ⟨ht₁nonneg, ht₁b.le⟩
    have ht₁L : φ t₁ ∈ L :=
      (hlu' ⟨(le_max_left l' 0).trans_lt ht₁l, ht₁b.trans hbu'⟩).mp
        (hfrontier_of_mem_J ht₁J)
    obtain ⟨t₂, hbt₂, ht₂u⟩ := exists_between hbu'
    have lineMap_eq (t : ℝ) :
        AffineMap.lineMap (φ b) (φ t₁) ((t - b) / (t₁ - b)) = φ t := by
      have ht₁bne : t₁ - b ≠ 0 := sub_ne_zero.mpr ht₁b.ne
      simp only [AffineMap.lineMap_apply, φ, vsub_eq_sub, vadd_eq_add]
      rw [add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
        div_mul_cancel₀ (t - b) ht₁bne, sub_smul]
      abel
    have hintervalF : Set.Icc b t₂ ⊆ F := by
      intro t ht
      have htL : φ t ∈ L := by
        rw [← lineMap_eq t]
        exact AffineMap.lineMap_mem _ hbL ht₁L
      have htlocal : t ∈ Set.Ioo l' u' := ⟨hl'b.trans_le ht.1, ht.2.trans_lt ht₂u⟩
      exact (hlu' htlocal).mpr htL
    have ht₂_component_b : t₂ ∈ connectedComponentIn F b :=
      isPreconnected_Icc.subset_connectedComponentIn
        (left_mem_Icc.mpr hbt₂.le) hintervalF (right_mem_Icc.mpr hbt₂.le)
    have hcomponents : J = connectedComponentIn F b := connectedComponentIn_eq hbJ
    have ht₂J : t₂ ∈ J := hcomponents.symm ▸ ht₂_component_b
    exact (not_lt_of_ge (hbGreatest.2 ht₂J)) hbt₂
  refine ⟨b, hbpos, hbvertex, ?_⟩
  intro t ht
  exact hfrontier_of_mem_J
    (isPreconnected_connectedComponentIn.Icc_subset hzeroJ hbJ ht)

private theorem IsPolygonal.exists_intrinsic_edge_of_germ_rsPrivate
    {D : Set Tiling.Plane} (hD : Tiling.IsPolygonal D) {p d : Tiling.Plane} (hd : d ≠ 0)
    (hp : p ∈ frontier D)
    (hgerm : ∀ᶠ z in nhds p, z ∈ frontier D ↔ z ∈ affineLine p d) :
    ∃ v w : Tiling.Plane, v ∈ Tiling.vertexSet D ∧ w ∈ Tiling.vertexSet D ∧
      v ≠ w ∧ p ∈ openSegment ℝ v w ∧
      openSegment ℝ v w ⊆ frontier D := by
  obtain ⟨b, hb, hbvertex, hbfrontier⟩ :=
    hD.exists_vertex_along_ray_rsPrivate hp hd hgerm
  obtain ⟨a, ha, havertex, hafrontier⟩ :=
    hD.exists_vertex_along_ray_rsPrivate hp (neg_ne_zero.mpr hd) (by
        filter_upwards [hgerm] with z hz
        exact hz.trans (by
          simp only [affineLine, Set.mem_ofPred_eq, signedSide, planarCross,
            Complex.neg_re, Complex.neg_im, neg_mul]
          constructor <;> intro h <;> linarith))
  let v : Tiling.Plane := p + a • (-d)
  let w : Tiling.Plane := p + b • d
  have hvw : v ≠ w := by
    intro heq
    have hzero : (a + b) • d = 0 := by
      calc
        (a + b) • d = w - v := by
          change (a + b) • d = (p + b • d) - (p + a • (-d))
          simp only [add_smul, smul_neg]
          abel
        _ = 0 := sub_eq_zero.mpr heq.symm
    exact (smul_ne_zero (ne_of_gt (add_pos ha hb)) hd) hzero
  have hpopen : p ∈ openSegment ℝ v w := by
    have ht : a / (a + b) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · exact div_pos ha (add_pos ha hb)
      · exact (div_lt_one (add_pos ha hb)).2 (lt_add_of_pos_right a hb)
    have hm := lineMap_mem_openSegment ℝ v w ht
    convert hm using 1
    simp only [AffineMap.lineMap_apply, v, w, vsub_eq_sub, vadd_eq_add]
    have hratio : a / (a + b) * (a + b) = a :=
      div_mul_cancel₀ a (ne_of_gt (add_pos ha hb))
    have hvsub : (p + b • d) - (p + a • -d) =
        (a + b) • d := by module
    rw [hvsub, smul_smul, hratio]
    module
  refine ⟨v, w, havertex, hbvertex, hvw, hpopen, ?_⟩
  intro z hz
  rw [openSegment_eq_image] at hz
  obtain ⟨c, hc, rfl⟩ := hz
  let t : ℝ := -a + c * (a + b)
  have htupper : t ≤ b := by dsimp only [t]; nlinarith [hc.2]
  have htlower : -a ≤ t := by dsimp only [t]; nlinarith [hc.1]
  have hpoint : AffineMap.lineMap v w c = p + t • d := by
    simp only [AffineMap.lineMap_apply, v, w, vsub_eq_sub, vadd_eq_add]
    dsimp only [t]
    module
  have hpoint' : (1 - c) • v + c • w = p + t • d := by
    rw [← hpoint]
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  dsimp only at ⊢
  rw [hpoint']
  rcases le_total 0 t with ht | ht
  · exact hbfrontier t ⟨ht, htupper⟩
  · have hneg : -t ∈ Set.Icc (0 : ℝ) a := ⟨neg_nonneg.mpr ht, neg_le.mp htlower⟩
    have := hafrontier (-t) hneg
    simpa using this

private theorem isPreconnected_punctured_ball_rsPrivate (p : Plane) {r : ℝ} (_hr : 0 < r) :
    IsPreconnected (Metric.ball p r \ {p}) := by
  have hrank : 1 < Module.rank ℝ Plane := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hc : IsPreconnected ((Ioo (0 : ℝ) r) ×ˢ Metric.sphere (0 : Plane) 1) :=
    isPreconnected_Ioo.prod
      (isPathConnected_sphere hrank 0 (by norm_num : (0 : ℝ) ≤ 1)).isConnected.isPreconnected
  let f : ℝ × Plane → Plane := fun x ↦ p + x.1 • x.2
  have hf : Continuous f := by fun_prop
  have heq : f '' ((Ioo (0 : ℝ) r) ×ˢ Metric.sphere (0 : Plane) 1) =
      Metric.ball p r \ {p} := by
    apply Subset.antisymm
    · rintro z ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have hun : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hu
      have hd : dist (f (t, u)) p = t := by
        simp [f, dist_eq_norm, hun, abs_of_pos ht.1]
      refine ⟨Metric.mem_ball.mpr (by rw [hd]; exact ht.2), ?_⟩
      intro hz
      have hz' : f (t, u) = p := Set.mem_singleton_iff.mp hz
      have : t = 0 := by rw [hz', dist_self] at hd; exact hd.symm
      exact ht.1.ne' this
    · rintro z ⟨hz, hzp⟩
      have hne : z - p ≠ 0 := sub_ne_zero.mpr (by simpa using hzp)
      have hn : 0 < ‖z - p‖ := norm_pos_iff.mpr hne
      refine ⟨(‖z - p‖, ‖z - p‖⁻¹ • (z - p)), ⟨?_, ?_⟩, ?_⟩
      · exact ⟨hn, by simpa [Metric.mem_ball, dist_eq_norm] using hz⟩
      · simp [hn.ne']
      · simp [f, hn.ne']
  rw [← heq]
  exact hc.image f hf.continuousOn

private theorem IsPolygonal.frontier_subset_closure_diff_finite_rsPrivate
    {s : Set Plane} (hs : IsPolygonal s) {V : Set Plane} (hV : V.Finite) :
    frontier s ⊆ closure (frontier s \ V) := by
  intro p hp
  by_contra hpc
  have hVclosed : IsClosed (V \ {p}) := hV.sdiff.isClosed
  have hpn : p ∈ (closure (frontier s \ V))ᶜ ∩ (V \ {p})ᶜ := by
    exact ⟨hpc, by simp⟩
  have hopen : IsOpen ((closure (frontier s \ V))ᶜ ∩ (V \ {p})ᶜ) :=
    isClosed_closure.isOpen_compl.inter hVclosed.isOpen_compl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen p hpn
  have hfball : Disjoint (Metric.ball p r \ {p}) (frontier s) := by
    rw [Set.disjoint_left]
    rintro z ⟨hz, hzp⟩ hzf
    have hzN := hball hz
    by_cases hzV : z ∈ V
    · exact hzN.2 ⟨hzV, hzp⟩
    · exact hzN.1 (subset_closure ⟨hzf, hzV⟩)
  obtain ⟨u, hui, hud⟩ := Metric.mem_closure_iff.mp
    (hs.closure_interior.symm ▸ hs.isClosed.frontier_subset hp) r hr
  have hup : u ≠ p := by
    rintro rfl
    exact Set.disjoint_left.mp disjoint_interior_frontier hui hp
  have huB : u ∈ Metric.ball p r \ {p} :=
    ⟨Metric.mem_ball.mpr (by simpa [dist_comm] using hud), by simpa using hup⟩
  have hpc' : p ∈ closure sᶜ := frontier_subset_closure (by simpa using hp : p ∈ frontier sᶜ)
  obtain ⟨w, hwc, hwd⟩ := Metric.mem_closure_iff.mp hpc' r hr
  have hwp : w ≠ p := by rintro rfl; exact hwc (hs.isClosed.frontier_subset hp)
  have hwB : w ∈ Metric.ball p r \ {p} :=
    ⟨Metric.mem_ball.mpr (by simpa [dist_comm] using hwd), by simpa using hwp⟩
  have hcover : Metric.ball p r \ {p} ⊆ interior s ∪ interior sᶜ := by
    intro z hz
    rw [← compl_frontier_eq_union_interior]
    exact Set.disjoint_left.mp hfball hz
  rcases (isPreconnected_punctured_ball_rsPrivate p hr).subset_or_subset
    isOpen_interior isOpen_interior
    (disjoint_of_subset interior_subset interior_subset disjoint_compl_right) hcover with hi | hc
  · exact hwc (interior_subset (hi hwB))
  · exact (interior_subset (hc huB)) (interior_subset hui)

theorem IsPolygonal.exists_finite_intrinsic_boundarySegments {s : Set Plane}
    (hs : IsPolygonal s) :
    ∃ F : Finset (Plane × Plane),
      (∀ e ∈ F, e.1 ≠ e.2 ∧ e.1 ∈ vertexSet s ∧
        e.2 ∈ vertexSet s ∧ segment ℝ e.1 e.2 ⊆ frontier s) ∧
      frontier s = ⋃ e ∈ F, segment ℝ e.1 e.2 := by
  classical
  let V := hs.vertexSet_finite.toFinset
  let F := (V ×ˢ V).filter fun e ↦ e.1 ≠ e.2 ∧ segment ℝ e.1 e.2 ⊆ frontier s
  have hF : ∀ e ∈ F, e.1 ≠ e.2 ∧ e.1 ∈ vertexSet s ∧
      e.2 ∈ vertexSet s ∧ segment ℝ e.1 e.2 ⊆ frontier s := by
    intro e he
    obtain ⟨hev, hne, hsub⟩ := Finset.mem_filter.mp he
    obtain ⟨hv, hw⟩ := Finset.mem_product.mp hev
    exact ⟨hne, hs.vertexSet_finite.mem_toFinset.mp hv,
      hs.vertexSet_finite.mem_toFinset.mp hw, hsub⟩
  have hcover : frontier s \ vertexSet s ⊆ ⋃ e ∈ F, segment ℝ e.1 e.2 := by
    rintro p ⟨hp, hpv⟩
    obtain ⟨L, hpL, hdim, hlocal⟩ := hs.boundaryLocallyStraightAt_of_not_mem_vertexSet hp hpv
    obtain ⟨d, hd, r, hr, hgerm⟩ :=
      AffineSubspace.exists_ball_frontier_iff_affineLine hpL hdim hlocal
    have hevent : ∀ᶠ z in 𝓝 p, z ∈ frontier s ↔ z ∈ affineLine p d :=
      Metric.eventually_nhds_iff.mpr ⟨r, hr, hgerm⟩
    obtain ⟨v, w, hv, hw, hvw, hpseg, hseg⟩ :=
      hs.exists_intrinsic_edge_of_germ_rsPrivate hd hp hevent
    have hclosedseg : segment ℝ v w ⊆ frontier s :=
      segment_subset_closure_openSegment.trans (closure_minimal hseg isClosed_frontier)
    have heF : (v, w) ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hs.vertexSet_finite.mem_toFinset.mpr hv,
        hs.vertexSet_finite.mem_toFinset.mpr hw⟩, hvw, hclosedseg⟩
    exact Set.mem_iUnion₂.mpr ⟨(v, w), heF, openSegment_subset_segment ℝ v w hpseg⟩
  have hCclosed : IsClosed (⋃ e ∈ F, segment ℝ e.1 e.2) :=
    F.finite_toSet.isClosed_biUnion fun e _ ↦ by
      rw [← closure_openSegment e.1 e.2]
      exact isClosed_closure
  refine ⟨F, hF, Subset.antisymm ?_ ?_⟩
  · exact (hs.frontier_subset_closure_diff_finite_rsPrivate hs.vertexSet_finite).trans
      (closure_minimal hcover hCclosed)
  · rintro p hp
    obtain ⟨e, he, hpseg⟩ := Set.mem_iUnion₂.mp hp
    exact (hF e he).2.2.2 hpseg

/-- A transverse coordinate completes any nonzero real linear functional on the plane. -/
theorem exists_transverse_linearFunctional
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ g : Plane →ₗ[ℝ] ℝ,
      Injective (fun z : Plane => (f z, g z)) := by
  let a : ℝ := f 1
  let b : ℝ := f Complex.I
  let g : Plane →ₗ[ℝ] ℝ :=
    -b • Complex.reCLM.toLinearMap + a • Complex.imCLM.toLinearMap
  have hf_formula (z : Plane) : f z = a * z.re + b * z.im := by
    have hz : z = z.re • (1 : Plane) + z.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hz, map_add, map_smul, map_smul]
    simp [a, b, smul_eq_mul, mul_comm]
  have hg_formula (z : Plane) : g z = -b * z.re + a * z.im := by
    simp [g, smul_eq_mul]
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    ext z
    rw [hf_formula]
    simp [h.1, h.2]
  have hpos : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · have hsq : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
      have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
      exact add_pos_of_pos_of_nonneg ha2 (sq_nonneg b)
    · have hsq : b ^ 2 ≠ 0 := pow_ne_zero 2 hb
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
      exact add_pos_of_nonneg_of_pos (sq_nonneg a) hb2
  refine ⟨g, ?_⟩
  intro x y hxy
  have hfx : f x = f y := congrArg Prod.fst hxy
  have hgx : g x = g y := congrArg Prod.snd hxy
  have hfd : f (x - y) = 0 := by rw [map_sub, hfx, sub_self]
  have hgd : g (x - y) = 0 := by rw [map_sub, hgx, sub_self]
  have hre : x.re = y.re := by
    have hcalc : (a ^ 2 + b ^ 2) * (x - y).re = 0 := by
      rw [hf_formula] at hfd
      rw [hg_formula] at hgd
      linear_combination a * hfd - b * hgd
    have hzero : (x - y).re = 0 := (mul_eq_zero.mp hcalc).resolve_left (ne_of_gt hpos)
    exact sub_eq_zero.mp hzero
  have him : x.im = y.im := by
    have hcalc : (a ^ 2 + b ^ 2) * (x - y).im = 0 := by
      rw [hf_formula] at hfd
      rw [hg_formula] at hgd
      linear_combination b * hfd + a * hgd
    have hzero : (x - y).im = 0 := (mul_eq_zero.mp hcalc).resolve_left (ne_of_gt hpos)
    exact sub_eq_zero.mp hzero
  exact Complex.ext hre him

/-- Lexicographic linear minimizers are extreme without requiring convexity of the set. -/
theorem mem_extremePoints_of_lexicographicMin
    {C : Set Plane} {v : Plane} (hv : v ∈ C)
    (f g : Plane →ₗ[ℝ] ℝ)
    (hfg : Injective (fun z : Plane => (f z, g z)))
    (hf : ∀ z ∈ C, f v ≤ f z)
    (hg : ∀ z ∈ C, f z = f v → g v ≤ g z) :
    v ∈ C.extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨hv, ?_⟩
  intro y hy z hz hsegment
  rw [openSegment_eq_image_lineMap] at hsegment
  obtain ⟨r, hr, hline⟩ := hsegment
  have hfv : f v = (1 - r) * f y + r * f z := by
    rw [← hline, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hfy : f v = f y := by
    have hminy := hf y hy
    have hminz := hf z hz
    by_contra hne
    have hlt : f v < f y := lt_of_le_of_ne hminy hne
    have hcoeff : 0 < 1 - r := by linarith [hr.2]
    have hprod : 0 < (1 - r) * (f y - f v) := mul_pos hcoeff (sub_pos.mpr hlt)
    have hnonneg : 0 ≤ r * (f z - f v) :=
      mul_nonneg (le_of_lt hr.1) (sub_nonneg.mpr hminz)
    nlinarith [hprod, hnonneg]
  have hfz : f v = f z := by
    have hminy := hf y hy
    have hminz := hf z hz
    by_contra hne
    have hlt : f v < f z := lt_of_le_of_ne hminz hne
    have hcoeff : 0 < r := hr.1
    have hprod : 0 < r * (f z - f v) := mul_pos hcoeff (sub_pos.mpr hlt)
    have hnonneg : 0 ≤ (1 - r) * (f y - f v) :=
      mul_nonneg (le_of_lt (by linarith [hr.2])) (sub_nonneg.mpr hminy)
    nlinarith [hprod, hnonneg]
  have hgv : g v = (1 - r) * g y + r * g z := by
    rw [← hline, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hgy : g v = g y := by
    have hminy := hg y hy hfy.symm
    have hminz := hg z hz hfz.symm
    by_contra hne
    have hlt : g v < g y := lt_of_le_of_ne hminy hne
    have hcoeff : 0 < 1 - r := by linarith [hr.2]
    have hprod : 0 < (1 - r) * (g y - g v) := mul_pos hcoeff (sub_pos.mpr hlt)
    have hnonneg : 0 ≤ r * (g z - g v) :=
      mul_nonneg (le_of_lt hr.1) (sub_nonneg.mpr hminz)
    nlinarith [hprod, hnonneg]
  have hgz : g v = g z := by
    have hminy := hg y hy hfy.symm
    have hminz := hg z hz hfz.symm
    by_contra hne
    have hlt : g v < g z := lt_of_le_of_ne hminz hne
    have hcoeff : 0 < r := hr.1
    have hprod : 0 < r * (g z - g v) := mul_pos hcoeff (sub_pos.mpr hlt)
    have hnonneg : 0 ≤ (1 - r) * (g y - g v) :=
      mul_nonneg (le_of_lt (by linarith [hr.2])) (sub_nonneg.mpr hminy)
    nlinarith [hprod, hnonneg]
  have hyv : y = v := hfg (Prod.ext hfy.symm hgy.symm)
  have hzv : z = v := hfg (Prod.ext hfz.symm hgz.symm)
  exact hyv

theorem IsPolygonal.exists_interiorComponent_min_vertex {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ v ∈ vertexSet s, v ∈ closure O ∧
      (∀ z ∈ closure O, f v ≤ f z) ∧
      (∀ z ∈ O, f v < f z) := by
  classical
  obtain ⟨g, hfg⟩ := exists_transverse_linearFunctional f hf
  have hfc : Continuous f := f.continuous_of_finiteDimensional
  have hgc : Continuous g := g.continuous_of_finiteDimensional
  have hC := (hs.interiorComponent_closure_compact_positive hO).1
  obtain ⟨ho, hconn, hos⟩ := interiorComponent_basic hO
  have hne : (closure O).Nonempty := hconn.nonempty.mono subset_closure
  obtain ⟨m, hm, hmin⟩ := hC.exists_isMinOn hne hfc.continuousOn
  let M : Set Plane := closure O ∩ f ⁻¹' {f m}
  have hMc : IsCompact M := hC.inter_right (isClosed_singleton.preimage hfc)
  have hmM : m ∈ M := ⟨hm, rfl⟩
  obtain ⟨v, hv, hgmin⟩ := hMc.exists_isMinOn ⟨m, hmM⟩ hgc.continuousOn
  have hvC : v ∈ closure O := hv.1
  have hvfm : f v = f m := hv.2
  have hfv : ∀ z ∈ closure O, f v ≤ f z := by
    intro z hz
    rw [hvfm]
    exact hmin hz
  have hgv : ∀ z ∈ closure O, f z = f v → g v ≤ g z := by
    intro z hz hzf
    exact hgmin ⟨hz, hzf.trans hvfm⟩
  have hvvertex : v ∈ vertexSet s := by
    intro T
    obtain ⟨F, hFT, _, _, hF⟩ := T.interiorComponent_subfamily hO
    have hvF : v ∈ ⋃₀ (F : Set (Set Plane)) := hF ▸ hvC
    obtain ⟨t, ht, hvt⟩ := Set.mem_sUnion.mp hvF
    have htC : t ⊆ closure O := by
      intro z hz
      rw [hF]
      exact Set.mem_sUnion.mpr ⟨t, ht, hz⟩
    refine ⟨t, hFT ht, mem_extremePoints_of_lexicographicMin hvt f g hfg ?_ ?_⟩
    · exact fun z hz ↦ hfv z (htC hz)
    · exact fun z hz hzf ↦ hgv z (htC hz) hzf
  have hw : ∃ w : Plane, f w < 0 := by
    have hex : ∃ w : Plane, f w ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hf (LinearMap.ext fun w ↦ hn w)
    obtain ⟨w, hw⟩ := hex
    rcases lt_or_gt_of_ne hw with hneg | hpos
    · exact ⟨w, hneg⟩
    · exact ⟨-w, by simpa using neg_neg_of_pos hpos⟩
  obtain ⟨w, hw⟩ := hw
  refine ⟨v, hvvertex, hvC, hfv, ?_⟩
  intro z hz
  have hc : Continuous (fun t : ℝ ↦ z + t • w) := by fun_prop
  have hevent : {t : ℝ | z + t • w ∈ O} ∈ 𝓝 0 := by
    have hn : O ∈ 𝓝 (z + (0 : ℝ) • w) := by simpa using ho.mem_nhds hz
    exact hc.continuousAt.preimage_mem_nhds hn
  obtain ⟨l, u, ⟨hl, hu⟩, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp hevent
  obtain ⟨e, he, heu⟩ := exists_between hu
  have hze : z + e • w ∈ O := hI ⟨hl.trans he, heu⟩
  have hbound := hfv (z + e • w) (subset_closure hze)
  have hless : f (z + e • w) < f z := by
    simp only [map_add, map_smul, smul_eq_mul]
    linarith [mul_neg_of_pos_of_neg he hw]
  exact hbound.trans_lt hless

theorem IsPolygonal.exists_interiorComponent_max_vertex {s O : Set Plane}
    (hs : IsPolygonal s) (hO : O ∈ interiorComponents s)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) :
    ∃ v ∈ vertexSet s, v ∈ closure O ∧
      (∀ z ∈ closure O, f z ≤ f v) ∧
      (∀ z ∈ O, f z < f v) := by
  obtain ⟨v, hv, hvC, hmin, hstrict⟩ :=
    hs.exists_interiorComponent_min_vertex hO (-f) (neg_ne_zero.mpr hf)
  refine ⟨v, hv, hvC, ?_, ?_⟩
  · intro z hz
    simpa using hmin z hz
  · intro z hz
    simpa using hstrict z hz

end Tiling

/-! Independently reviewed supplemental lemmas (outside frozen362). -/
namespace Tiling

theorem IsPolygonal.lineSection_finiteClosedIntervals {s : Set Plane} (hs : IsPolygonal s)
    (k u : Plane) (hu : u ≠ 0) :
    ∃ (n : ℕ) (a b : Fin n → ℝ), (∀ i, a i ≤ b i) ∧
      {r : ℝ | k + r • u ∈ s} = ⋃ i, Set.Icc (a i) (b i) := by
  classical
  obtain ⟨F⟩ := hs
  let f : ℝ →ᵃ[ℝ] Plane := AffineMap.lineMap k (k + u)
  have hf (r : ℝ) : f r = k + r • u := by
    simp [f, AffineMap.lineMap_apply_module', add_comm]
  have hfclosed : Topology.IsClosedEmbedding f := by
    have hsmul : Topology.IsClosedEmbedding (fun r : ℝ => r • u) := isClosedEmbedding_smul_left hu
    have h := (Homeomorph.addLeft k).isClosedEmbedding.comp hsmul
    convert h using 1
    funext r
    exact hf r
  let J := {t : {t : Set Plane // t ∈ F.pieces} // (f ⁻¹' t.1).Nonempty}
  have hpresentation (j : J) : ∃ a b : ℝ, a ≤ b ∧ f ⁻¹' j.1.1 = Set.Icc a b := by
    have htriangle := F.isTriangle j.1.1 j.1.2
    have hcompact := hfclosed.isCompact_preimage htriangle.isCompact
    have hconvex : Convex ℝ j.1.1 := by
      obtain ⟨a, b, c, _, heq⟩ := htriangle
      rw [heq]
      exact convex_convexHull ℝ _
    have hconnected : IsConnected (f ⁻¹' j.1.1) :=
      ⟨j.2, (hconvex.affine_preimage f).isPreconnected⟩
    refine ⟨sInf (f ⁻¹' j.1.1), sSup (f ⁻¹' j.1.1), ?_,
      eq_Icc_of_connected_compact hconnected hcompact⟩
    exact (hcompact.isLeast_sInf j.2).2 (hcompact.sSup_mem j.2)
  choose a b hab heq using hpresentation
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, a ∘ e, b ∘ e, fun i => hab (e i), ?_⟩
  ext r
  constructor
  · intro hr
    have hrF : f r ∈ ⋃₀ (F.pieces : Set (Set Plane)) := by
      rw [F.sUnion_eq, hf]
      exact hr
    obtain ⟨t, ht, hrt⟩ := Set.mem_sUnion.mp hrF
    let j : J := ⟨⟨t, ht⟩, ⟨r, hrt⟩⟩
    apply Set.mem_iUnion.mpr
    refine ⟨e.symm j, ?_⟩
    change r ∈ Set.Icc (a (e (e.symm j))) (b (e (e.symm j)))
    rw [e.apply_symm_apply, ← heq j]
    exact hrt
  · intro hr
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hr
    have hri : f r ∈ (e i).1.1 := by
      change r ∈ f ⁻¹' (e i).1.1
      rw [heq (e i)]
      exact hi
    change k + r • u ∈ s
    rw [← hf, ← F.sUnion_eq]
    exact Set.mem_sUnion.mpr ⟨(e i).1.1, (e i).1.2, hri⟩

theorem IsPolygonal.noncriticalSection_frontier_finite
    {s : Set Plane} (hs : IsPolygonal s) (ℓ : Plane →L[ℝ] ℝ) (k u : Plane)
    (hu : u ≠ 0) (hℓu : ℓ u = 0)
    (hcritical : ℓ k ∉ ℓ '' vertexSet s) :
    {r : ℝ | k + r • u ∈ frontier s}.Finite := by
  classical
  obtain ⟨F, hF, hboundary⟩ := hs.exists_finite_intrinsic_boundarySegments
  have hsegment (a b : Plane) (ha : a ∈ vertexSet s)
      (_hb : b ∈ vertexSet s) :
      {r : ℝ | k + r • u ∈ segment ℝ a b}.Finite := by
    apply Set.Subsingleton.finite
    intro r hr s hs
    rw [segment_eq_image_lineMap] at hr hs
    obtain ⟨α, _, hα⟩ := hr
    obtain ⟨β, _, hβ⟩ := hs
    have hline (q : ℝ) : ℓ (k + q • u) = ℓ k := by
      rw [map_add, map_smul, hℓu, smul_zero, add_zero]
    have hαℓ := congrArg ℓ hα
    have hβℓ := congrArg ℓ hβ
    rw [AffineMap.lineMap_apply_module] at hαℓ hβℓ
    simp only [map_add, map_smul, smul_eq_mul, hline] at hαℓ hβℓ
    have hab : ℓ a ≠ ℓ b := by
      intro hab
      have hak : ℓ a = ℓ k := by rw [hab] at hαℓ; nlinarith
      exact hcritical ⟨a, ha, hak⟩
    have hαβ : α = β := by
      have hdiff : (α - β) * (ℓ b - ℓ a) = 0 := by nlinarith [hαℓ, hβℓ]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_right (sub_ne_zero.mpr hab.symm))
    have hrs : k + r • u = k + s • u := by rw [← hα, ← hβ, hαβ]
    exact smul_left_injective ℝ hu (add_left_cancel hrs)
  have hfinite : (⋃ q ∈ F, {r : ℝ | k + r • u ∈ segment ℝ q.1 q.2}).Finite :=
    F.finite_toSet.biUnion fun q hq => hsegment q.1 q.2 (hF q hq).2.1 (hF q hq).2.2.1
  apply hfinite.subset
  intro r hr
  change k + r • u ∈ frontier s at hr
  rw [hboundary, Set.mem_iUnion] at hr
  obtain ⟨q, hq⟩ := hr
  rw [Set.mem_iUnion] at hq
  obtain ⟨hqF, hrq⟩ := hq
  exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqF, hrq⟩⟩

end Tiling
