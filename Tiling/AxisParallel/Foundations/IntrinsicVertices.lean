import Tiling.AxisParallel.Core
import Tiling.Geometry.PolygonalTopology
import Mathlib.Analysis.Convex.Strict.Extreme

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Tiling.AxisParallel.IntrinsicVertices

open Tiling
open Tiling.AxisParallel

/-- The three closed coordinate bands determined by the two sides of a local box. -/
private inductive MasterBand
  | below
  | middle
  | above
  deriving DecidableEq

private instance : Fintype MasterBand where
  elems := {MasterBand.below, MasterBand.middle, MasterBand.above}
  complete x := by cases x <;> simp

/-- Which half of a box is occupied when a straight boundary passes through its interior. -/
private inductive HalfBoxSide
  | left
  | right
  | lower
  | upper
  deriving DecidableEq

/-- A closed axis-parallel box with ordered real-coordinate bounds. -/
def closedAxisBox (x₀ x₁ y₀ y₁ : ℝ) : Set Tiling.Plane :=
  {z | z.re ∈ Set.Icc x₀ x₁ ∧ z.im ∈ Set.Icc y₀ y₁}

/-- The closed half-box cut by the horizontal or vertical line through `v`. -/
private def closedHalfBox (x₀ x₁ y₀ y₁ : ℝ) (v : Tiling.Plane) :
    HalfBoxSide → Set Tiling.Plane
  | .left => {z | z.re ∈ Set.Icc x₀ v.re ∧ z.im ∈ Set.Icc y₀ y₁}
  | .right => {z | z.re ∈ Set.Icc v.re x₁ ∧ z.im ∈ Set.Icc y₀ y₁}
  | .lower => {z | z.re ∈ Set.Icc x₀ x₁ ∧ z.im ∈ Set.Icc y₀ v.im}
  | .upper => {z | z.re ∈ Set.Icc x₀ x₁ ∧ z.im ∈ Set.Icc v.im y₁}

/-- One of the three closed intervals cut out by two ordered coordinates. -/
private def masterBandSet (a b : ℝ) : MasterBand → Set ℝ
  | .below => Set.Iic a
  | .middle => Set.Icc a b
  | .above => Set.Ici b

/-- A cell of the closed `3 × 3` master grid determined by a local box. -/
private def masterGridCell (x₀ x₁ y₀ y₁ : ℝ)
    (i j : MasterBand) : Set Tiling.Plane :=
  {z | z.re ∈ masterBandSet x₀ x₁ i ∧ z.im ∈ masterBandSet y₀ y₁ j}

/-- The eight master-grid cells outside the central local box. -/
private noncomputable def outerMasterCells (x₀ x₁ y₀ y₁ : ℝ) :
    Finset (Set Tiling.Plane) := by
  classical
  exact
    (((Finset.univ : Finset (MasterBand × MasterBand)).filter
      (fun ij => ij ≠ (.middle, .middle))).image
        (fun ij => masterGridCell x₀ x₁ y₀ y₁ ij.1 ij.2))

/-- Nondegenerate intersections of an old rectangulation with the eight outer master cells. -/
private noncomputable def clippedOuterPieces {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) (x₀ x₁ y₀ y₁ : ℝ) :
    Finset (Set Tiling.Plane) := by
  classical
  exact
    (((R.pieces ×ˢ outerMasterCells x₀ x₁ y₀ y₁).filter
      (fun p => Tiling.IsRectangle (p.1 ∩ p.2))).image (fun p => p.1 ∩ p.2))

/-- Replace the central master cell by a supplied nondegenerate rectangle `q`. -/
private noncomputable def localReplacementPieces {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) (x₀ x₁ y₀ y₁ : ℝ)
    (q : Set Tiling.Plane) : Finset (Set Tiling.Plane) :=
  insert q (clippedOuterPieces R x₀ x₁ y₀ y₁)

/-- A rectangulation avoids `v` when `v` is not an extreme point of any rectangle piece. -/
private def RectangulationAvoids {s : Set Tiling.Plane}
    (R : Tiling.Rectangulation s) (v : Tiling.Plane) : Prop :=
  ∀ r ∈ R.pieces, v ∉ r.extremePoints ℝ

/-- A triangulation avoids `v` when `v` is not an extreme point of any triangle piece. -/
private def TriangulationAvoids {s : Set Tiling.Plane}
    (T : Tiling.Triangulation s) (v : Tiling.Plane) : Prop :=
  ∀ t ∈ T.pieces, v ∉ t.extremePoints ℝ

/-- A point avoids every horizontal and vertical line through an intrinsic vertex. -/
def OffVertexCoordinateGrid (K : Region) (x : Tiling.Plane) : Prop :=
  ∀ v ∈ K.vertices, x.re ≠ v.re ∧ x.im ≠ v.im

/-- Two points occupy the same open chamber of the coordinate grid cut out by the intrinsic
vertices, expressed without choosing a sorted enumeration. -/
def SameVertexGridCell (K : Region) (x y : Tiling.Plane) : Prop :=
  (∀ v ∈ K.vertices,
    (x.re < v.re ↔ y.re < v.re)) ∧
  ∀ v ∈ K.vertices,
    (x.im < v.im ↔ y.im < v.im)

/-- A nondegenerate closed grid rectangle whose four supporting coordinate levels occur among
the intrinsic vertices. -/
def IsIntrinsicGridRectangle (K : Region) (r : Set Tiling.Plane) : Prop :=
  ∃ x₀ x₁ y₀ y₁ : ℝ,
    x₀ < x₁ ∧ y₀ < y₁ ∧
    r = closedAxisBox x₀ x₁ y₀ y₁ ∧
    (∃ v ∈ K.vertices, v.re = x₀) ∧
    (∃ v ∈ K.vertices, v.re = x₁) ∧
    (∃ v ∈ K.vertices, v.im = y₀) ∧
    ∃ v ∈ K.vertices, v.im = y₁

/-- The finite intrinsic coordinate-level set in the selected axis. -/
def intrinsicCoordinateLevels (K : Region) (axis : Axis) : Finset ℝ :=
  K.vertexFinset.image (Axis.coord axis)

/-- All adjacent ordered pairs in a finite set of real levels. -/
noncomputable def consecutiveLevelPairs (s : Finset ℝ) : Finset (ℝ × ℝ) := by
  classical
  exact
    ((s ×ˢ s).filter fun p =>
      p.1 < p.2 ∧ ∀ z ∈ s, ¬(p.1 < z ∧ z < p.2))

/-- The canonical finite collection of closures of occupied bounded intrinsic-grid chambers. -/
noncomputable def intrinsicGridPieces (K : Region) : Finset (Set Tiling.Plane) := by
  classical
  let xPairs := consecutiveLevelPairs (intrinsicCoordinateLevels K .horizontal)
  let yPairs := consecutiveLevelPairs (intrinsicCoordinateLevels K .vertical)
  exact
    (((xPairs ×ˢ yPairs).filter fun p =>
      interior (closedAxisBox p.1.1 p.1.2 p.2.1 p.2.2) ⊆ K.openCarrier).image
        fun p => closedAxisBox p.1.1 p.1.2 p.2.1 p.2.2)


private noncomputable def flattenRectangulation
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (T : ∀ r : ↥R.pieces, Tiling.Triangulation (r : Set Tiling.Plane)) :
    Tiling.Triangulation s where
  pieces := R.pieces.attach.biUnion fun r ↦ (T r).pieces
  isTriangle := by
    intro t ht
    obtain ⟨r, _, htr⟩ := Finset.mem_biUnion.mp ht
    exact (T r).isTriangle t htr
  pairwiseAEDisjoint := by
    intro a ha b hb hab
    obtain ⟨r, _, har⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨u, _, hbu⟩ := Finset.mem_biUnion.mp hb
    by_cases hru : (r : Set Tiling.Plane) = u
    · have hru' : r = u := Subtype.ext hru
      subst u
      exact (T r).pairwiseAEDisjoint har hbu hab
    · apply (R.pairwiseAEDisjoint r.property u.property hru).mono
      · intro z hza
        rw [← (T r).sUnion_eq]
        exact ⟨a, har, hza⟩
      · intro z hzb
        rw [← (T u).sUnion_eq]
        exact ⟨b, hbu, hzb⟩
  sUnion_eq := by
    apply Set.Subset.antisymm
    · intro z hz
      obtain ⟨t, ht, hzt⟩ := hz
      obtain ⟨r, _, htr⟩ := Finset.mem_biUnion.mp ht
      rw [← R.sUnion_eq]
      refine ⟨r, r.property, ?_⟩
      rw [← (T r).sUnion_eq]
      exact ⟨t, htr, hzt⟩
    · intro z hzs
      rw [← R.sUnion_eq] at hzs
      obtain ⟨r, hr, hzr⟩ := hzs
      let r' : ↥R.pieces := ⟨r, hr⟩
      have hzr' : z ∈ (r' : Set Tiling.Plane) := hzr
      rw [← (T r').sUnion_eq] at hzr'
      obtain ⟨t, ht, hzt⟩ := hzr'
      refine ⟨t, ?_, hzt⟩
      exact Finset.mem_biUnion.mpr ⟨r', Finset.mem_attach _ _, ht⟩

private theorem normSq_affineCombination_identity
    (a b w : Tiling.Plane) (t : ℝ) :
    Complex.normSq (((1 - t) • a + t • b) - w) =
      (1 - t) * Complex.normSq (a - w) +
        t * Complex.normSq (b - w) -
          t * (1 - t) * Complex.normSq (a - b) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem exists_globalDistanceMaximizers
    {s : Set Tiling.Plane} (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ p ∈ s, ∃ q ∈ s,
      (∀ x ∈ s, ∀ y ∈ s, dist x y ≤ dist p q) ∧
      Metric.diam s = dist p q := by
  have hprod : IsCompact (s ×ˢ s) := hs.prod hs
  have hprodne : (s ×ˢ s).Nonempty := hne.prod hne
  obtain ⟨pq, hpq, hmax⟩ := hprod.exists_isMaxOn hprodne continuous_dist.continuousOn
  refine ⟨pq.1, hpq.1, pq.2, hpq.2, ?_, ?_⟩
  · intro x hx y hy
    exact hmax (show (x, y) ∈ s ×ˢ s from ⟨hx, hy⟩)
  · apply le_antisymm
    · exact Metric.diam_le_of_forall_dist_le dist_nonneg
        (fun x hx y hy => hmax (show (x, y) ∈ s ×ˢ s from ⟨hx, hy⟩))
    · exact Metric.dist_le_diam_of_mem hs.isBounded hpq.1 hpq.2

private theorem triangle_extremePoint_of_globalDistanceMax
    {s t : Set Tiling.Plane} (_ht : Tiling.IsTriangle t) (hts : t ⊆ s)
    {p w : Tiling.Plane} (hpt : p ∈ t)
    (hmax : ∀ x ∈ s, dist x w ≤ dist p w) :
    p ∈ t.extremePoints ℝ := by
  rw [mem_extremePoints_iff_left]
  refine ⟨hpt, ?_⟩
  intro a hat b hbt hpopen
  by_contra hap
  rcases hpopen with ⟨u, v, hu, hv, huv, huvp⟩
  have hab : a ≠ b := by
    intro hab
    subst b
    have : p = a := by
      rw [← huvp]
      rw [← add_smul, huv, one_smul]
    exact hap this.symm
  have hta := hts hat
  have htb := hts hbt
  have hpa := hmax a hta
  have hpb := hmax b htb
  have hnorma : ‖a - w‖ ≤ ‖p - w‖ := by
    simpa [Complex.dist_eq] using hpa
  have hnormb : ‖b - w‖ ≤ ‖p - w‖ := by
    simpa [Complex.dist_eq] using hpb
  have hsqa : Complex.normSq (a - w) ≤ Complex.normSq (p - w) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    nlinarith [norm_nonneg (a - w), norm_nonneg (p - w)]
  have hsqb : Complex.normSq (b - w) ≤ Complex.normSq (p - w) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    nlinarith [norm_nonneg (b - w), norm_nonneg (p - w)]
  have hvlt : v < 1 := by linarith
  have huvform : p = (1 - v) • a + v • b := by
    rw [show u = 1 - v by linarith] at huvp
    exact huvp.symm
  have hid := normSq_affineCombination_identity a b w v
  rw [← huvform] at hid
  have hpos : 0 < v * (1 - v) * Complex.normSq (a - b) := by
    exact mul_pos (mul_pos hv (sub_pos.mpr hvlt))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hab))
  nlinarith

private theorem globalDistanceMaximizers_mem_vertexSet
    {s : Set Tiling.Plane} (_hs : Tiling.IsPolygonal s)
    {p q : Tiling.Plane} (hp : p ∈ s) (hq : q ∈ s)
    (hmax : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ dist p q) :
    p ∈ Tiling.vertexSet s ∧ q ∈ Tiling.vertexSet s := by
  constructor
  · intro triangulation
    have hp' : p ∈ ⋃₀ (triangulation.pieces : Set (Set Tiling.Plane)) := by
      rw [triangulation.sUnion_eq]
      exact hp
    rcases hp' with ⟨t, ht, hpt⟩
    refine ⟨t, ht, triangle_extremePoint_of_globalDistanceMax
      (s := s) (w := q) (triangulation.isTriangle t ht) ?_ hpt ?_⟩
    · intro x hxt
      rw [← triangulation.sUnion_eq]
      exact ⟨t, ht, hxt⟩
    · intro x hxs
      exact hmax x hxs q hq
  · intro triangulation
    have hq' : q ∈ ⋃₀ (triangulation.pieces : Set (Set Tiling.Plane)) := by
      rw [triangulation.sUnion_eq]
      exact hq
    rcases hq' with ⟨t, ht, hqt⟩
    refine ⟨t, ht, triangle_extremePoint_of_globalDistanceMax
      (s := s) (w := p) (triangulation.isTriangle t ht) ?_ hqt ?_⟩
    · intro x hxt
      rw [← triangulation.sUnion_eq]
      exact ⟨t, ht, hxt⟩
    · intro x hxs
      simpa only [dist_comm q p] using hmax x hxs p hp

theorem exists_intrinsicDiameterPair (K : Region) :
    ∃ v ∈ K.vertices, ∃ w ∈ K.vertices,
      (∀ x ∈ K.support, ∀ y ∈ K.support, dist x y ≤ dist v w) ∧
      Metric.diam K.support = dist v w := by
  obtain ⟨p, hp, q, hq, hmax, hdiam⟩ :=
    exists_globalDistanceMaximizers K.isPolygonal.isCompact K.nonempty
  have hpq := globalDistanceMaximizers_mem_vertexSet K.isPolygonal hp hq hmax
  exact ⟨p, hpq.1, q, hpq.2, hmax, hdiam⟩

theorem exists_vertices_controlling_distance
    (K : Region) (x y : Tiling.Plane) (hx : x ∈ K.support) (hy : y ∈ K.support) :
    ∃ v ∈ K.vertices, ∃ w ∈ K.vertices, dist x y ≤ dist v w := by
  obtain ⟨v, hv, w, hw, hmax, _⟩ := exists_intrinsicDiameterPair K
  exact ⟨v, hv, w, hw, hmax x hx y hy⟩

private theorem localReplacement_isRectangle
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) (q : Set Tiling.Plane)
    (hq : Tiling.IsRectangle q) :
    ∀ r ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q,
      Tiling.IsRectangle r := by
  classical
  intro r hr
  rw [localReplacementPieces, Finset.mem_insert] at hr
  rcases hr with rfl | hr
  · exact hq
  · rw [clippedOuterPieces, Finset.mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    exact (Finset.mem_filter.mp hp).2

private theorem localReplacement_avoids
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) (q : Set Tiling.Plane) (v : Tiling.Plane)
    (hx₀ : x₀ < v.re) (hx₁ : v.re < x₁)
    (hy₀ : y₀ < v.im) (hy₁ : v.im < y₁)
    (hqv : v ∉ q.extremePoints ℝ) :
    ∀ r ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q,
      v ∉ r.extremePoints ℝ := by
  classical
  intro r hr hvr
  rw [localReplacementPieces, Finset.mem_insert] at hr
  rcases hr with rfl | hr
  · exact hqv hvr
  · rw [clippedOuterPieces, Finset.mem_image] at hr
    obtain ⟨p, hp, rfl⟩ := hr
    have hvinter : v ∈ p.1 ∩ p.2 := extremePoints_subset hvr
    have hpProd : p ∈ R.pieces ×ˢ outerMasterCells x₀ x₁ y₀ y₁ :=
      (Finset.mem_filter.mp hp).1
    have hpouter : p.2 ∈ outerMasterCells x₀ x₁ y₀ y₁ :=
      (Finset.mem_product.mp hpProd).2
    rw [outerMasterCells, Finset.mem_image] at hpouter
    obtain ⟨ij, hij, hp2⟩ := hpouter
    have hijne := (Finset.mem_filter.mp hij).2
    have hvcell : v ∈ masterGridCell x₀ x₁ y₀ y₁ ij.1 ij.2 := by
      simpa [hp2] using hvinter.2
    rcases ij with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;>
      simp [masterGridCell, masterBandSet] at hvcell hijne <;> linarith

private theorem volume_re_eq_zero (a : ℝ) :
    volume {z : Tiling.Plane | z.re = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.re = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_re continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : z + (ε / 2 : ℝ) ∈ H := interior_subset hw
    have hzH : z.re = a := hzmem
    have hwH : (z + (ε / 2 : ℝ)).re = a := hwmem
    simp only [Complex.add_re, Complex.ofReal_re] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.reLm.isLinear a).addHaar_frontier volume

private theorem volume_im_eq_zero (a : ℝ) :
    volume {z : Tiling.Plane | z.im = a} = 0 := by
  let H : Set Tiling.Plane := {z | z.im = a}
  have hclosed : IsClosed H := isClosed_eq Complex.continuous_im continuous_const
  have hinter : interior H = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    rintro ⟨z, hz⟩
    obtain ⟨ε, hε, hzε⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
    have hw := hzε (show z + (ε / 2 : ℝ) * Complex.I ∈ Metric.ball z ε by
      rw [Metric.mem_ball, Complex.dist_eq]
      simpa [norm_mul, Real.norm_eq_abs, abs_of_pos hε] using half_lt_self hε)
    have hzmem : z ∈ H := interior_subset hz
    have hwmem : z + (ε / 2 : ℝ) * Complex.I ∈ H := interior_subset hw
    have hzH : z.im = a := hzmem
    have hwH : (z + (ε / 2 : ℝ) * Complex.I).im = a := hwmem
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hwH
    linarith
  have hfrontier : frontier H = H := by
    rw [frontier, hclosed.closure_eq, hinter, sdiff_empty]
  change volume H = 0
  rw [← hfrontier]
  exact (convex_hyperplane Complex.imLm.isLinear a).addHaar_frontier volume

private theorem masterBand_inter_subset_singleton
    (a b : ℝ) (hab : a < b) (i k : MasterBand) (hne : i ≠ k) :
    ∃ c : ℝ, masterBandSet a b i ∩ masterBandSet a b k ⊆ {c} := by
  fin_cases i <;> fin_cases k
  all_goals
    first
    | exact (hne rfl).elim
    | refine ⟨a, ?_⟩
      intro z hz
      simp [masterBandSet] at hz ⊢
      linarith
    | refine ⟨b, ?_⟩
      intro z hz
      simp [masterBandSet] at hz ⊢
      linarith

private theorem masterGridCell_aedisjoint_of_ne
    (x₀ x₁ y₀ y₁ : ℝ) (hx : x₀ < x₁) (hy : y₀ < y₁)
    (i j k l : MasterBand) (hne : (i, j) ≠ (k, l)) :
    AEDisjoint volume (masterGridCell x₀ x₁ y₀ y₁ i j)
      (masterGridCell x₀ x₁ y₀ y₁ k l) := by
  have hcoord : i ≠ k ∨ j ≠ l := by
    by_contra hc
    simp only [not_or, Classical.not_not] at hc
    exact hne (Prod.ext hc.1 hc.2)
  rcases hcoord with hik | hjl
  · obtain ⟨c, hc⟩ := masterBand_inter_subset_singleton x₀ x₁ hx i k hik
    change volume (masterGridCell x₀ x₁ y₀ y₁ i j ∩
      masterGridCell x₀ x₁ y₀ y₁ k l) = 0
    apply measure_mono_null ?_ (volume_re_eq_zero c)
    intro z hz
    exact hc ⟨hz.1.1, hz.2.1⟩
  · obtain ⟨c, hc⟩ := masterBand_inter_subset_singleton y₀ y₁ hy j l hjl
    change volume (masterGridCell x₀ x₁ y₀ y₁ i j ∩
      masterGridCell x₀ x₁ y₀ y₁ k l) = 0
    apply measure_mono_null ?_ (volume_im_eq_zero c)
    intro z hz
    exact hc ⟨hz.1.2, hz.2.2⟩

private theorem mem_clippedOuterPieces
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) {r : Set Tiling.Plane}
    (hr : r ∈ clippedOuterPieces R x₀ x₁ y₀ y₁) :
    ∃ old ∈ R.pieces, ∃ i j : MasterBand,
      (i, j) ≠ (MasterBand.middle, MasterBand.middle) ∧
      r = old ∩ masterGridCell x₀ x₁ y₀ y₁ i j := by
  classical
  rw [clippedOuterPieces, Finset.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hpProd := (Finset.mem_filter.mp hp).1
  obtain ⟨hold, hcell⟩ := Finset.mem_product.mp hpProd
  rw [outerMasterCells, Finset.mem_image] at hcell
  obtain ⟨ij, hij, hcellEq⟩ := hcell
  exact ⟨p.1, hold, ij.1, ij.2, (Finset.mem_filter.mp hij).2,
    congrArg (p.1 ∩ ·) hcellEq.symm⟩

private theorem localReplacement_pairwiseAEDisjoint
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) (q : Set Tiling.Plane)
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hq : q ⊆ closedAxisBox x₀ x₁ y₀ y₁) :
    ((localReplacementPieces R x₀ x₁ y₀ y₁ q :
      Finset (Set Tiling.Plane)) : Set (Set Tiling.Plane)).Pairwise
      (AEDisjoint volume) := by
  classical
  intro a ha b hb hab
  change a ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q at ha
  change b ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q at hb
  rw [localReplacementPieces, Finset.mem_insert] at ha hb
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact (hab rfl).elim
    · obtain ⟨old, hold, i, j, hij, rfl⟩ :=
        mem_clippedOuterPieces R x₀ x₁ y₀ y₁ hb
      apply (masterGridCell_aedisjoint_of_ne x₀ x₁ y₀ y₁ hx hy
        .middle .middle i j ?_).mono hq inter_subset_right
      intro heq
      exact hij heq.symm
  · rcases hb with rfl | hb
    · obtain ⟨old, hold, i, j, hij, rfl⟩ :=
        mem_clippedOuterPieces R x₀ x₁ y₀ y₁ ha
      apply (masterGridCell_aedisjoint_of_ne x₀ x₁ y₀ y₁ hx hy
        i j .middle .middle hij).mono inter_subset_right hq
    · obtain ⟨oldA, holdA, i, j, hij, rfl⟩ :=
        mem_clippedOuterPieces R x₀ x₁ y₀ y₁ ha
      obtain ⟨oldB, holdB, k, l, hkl, rfl⟩ :=
        mem_clippedOuterPieces R x₀ x₁ y₀ y₁ hb
      by_cases holdEq : oldA = oldB
      · subst oldB
        have hcellne : (i, j) ≠ (k, l) := by
          intro hpairs
          cases hpairs
          exact hab rfl
        exact (masterGridCell_aedisjoint_of_ne x₀ x₁ y₀ y₁ hx hy i j k l hcellne).mono
          inter_subset_right inter_subset_right
      · exact (R.pairwiseAEDisjoint holdA holdB holdEq).mono
          inter_subset_left inter_subset_left

private theorem closedAxisBox_isRectangle
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    Tiling.IsRectangle (closedAxisBox a b c d) := by
  refine ⟨Complex.mk a c, Complex.mk b d, ?_, ?_, ?_⟩
  · simp [ne_of_lt hab]
  · simp [ne_of_lt hcd]
  · ext z
    simp only [closedAxisBox, Complex.Rectangle, Complex.mem_reProdIm,
mem_ofPred_eq, mem_Icc, uIcc_of_le hab.le, uIcc_of_le hcd.le]

private theorem isRectangle_eq_closedAxisBox
    {r : Set Tiling.Plane} (hr : Tiling.IsRectangle r) :
    ∃ a b c d : ℝ, a < b ∧ c < d ∧ r = closedAxisBox a b c d := by
  obtain ⟨u, v, huvRe, huvIm, rfl⟩ := hr
  refine ⟨min u.re v.re, max u.re v.re, min u.im v.im, max u.im v.im,
    min_lt_max.mpr huvRe, min_lt_max.mpr huvIm, ?_⟩
  rcases le_total u.re v.re with hre | hre
  · rcases le_total u.im v.im with him | him
    · rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him]
      ext z
      simp [closedAxisBox, Complex.Rectangle, Complex.mem_reProdIm,
        uIcc_of_le hre, uIcc_of_le him]
    · rw [min_eq_left hre, max_eq_right hre, min_eq_right him, max_eq_left him]
      ext z
      simp [closedAxisBox, Complex.Rectangle, Complex.mem_reProdIm,
        uIcc_of_le hre, uIcc_of_ge him]
  · rcases le_total u.im v.im with him | him
    · rw [min_eq_right hre, max_eq_left hre, min_eq_left him, max_eq_right him]
      ext z
      simp [closedAxisBox, Complex.Rectangle, Complex.mem_reProdIm,
        uIcc_of_ge hre, uIcc_of_le him]
    · rw [min_eq_right hre, max_eq_left hre, min_eq_right him, max_eq_left him]
      ext z
      simp [closedAxisBox, Complex.Rectangle, Complex.mem_reProdIm,
        uIcc_of_ge hre, uIcc_of_ge him]

private theorem interior_closedAxisBox
    {a b c d : ℝ} (_hab : a < b) (_hcd : c < d) :
    interior (closedAxisBox a b c d) =
      {z : Tiling.Plane | z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d} := by
  change interior (Icc a b ×ℂ Icc c d) = _
  rw [Complex.interior_reProdIm]
  rw [interior_Icc, interior_Icc]
  ext z
  exact Complex.mem_reProdIm

private def masterBandInterior (a b : ℝ) : MasterBand → Set ℝ
  | .below => Iio a
  | .middle => Ioo a b
  | .above => Ioi b

private theorem masterBandInterior_subset (a b : ℝ) (i : MasterBand) :
    masterBandInterior a b i ⊆ masterBandSet a b i := by
  intro x hx
  fin_cases i
  · change x < a at hx
    change x ≤ a
    exact hx.le
  · exact ⟨hx.1.le, hx.2.le⟩
  · change b < x at hx
    change b ≤ x
    exact hx.le

private theorem exists_masterBandInterior
    (a b t : ℝ) (ha : t ≠ a) (hb : t ≠ b) :
    ∃ i : MasterBand, t ∈ masterBandInterior a b i := by
  by_cases hbelow : t < a
  · exact ⟨.below, hbelow⟩
  by_cases habove : b < t
  · exact ⟨.above, habove⟩
  refine ⟨.middle, ?_⟩
  exact ⟨lt_of_le_of_ne (le_of_not_gt hbelow) ha.symm,
    lt_of_le_of_ne (le_of_not_gt habove) hb⟩

private theorem closedAxisBox_inter_masterGridCell_isRectangle
    {a b c d x₀ x₁ y₀ y₁ : ℝ} (hab : a < b) (hcd : c < d)
    (i j : MasterBand) (z : Tiling.Plane)
    (hzbox : z ∈ interior (closedAxisBox a b c d))
    (hzcell : z.re ∈ masterBandInterior x₀ x₁ i ∧
      z.im ∈ masterBandInterior y₀ y₁ j) :
    Tiling.IsRectangle
      (closedAxisBox a b c d ∩ masterGridCell x₀ x₁ y₀ y₁ i j) := by
  rw [interior_closedAxisBox hab hcd] at hzbox
  rcases hzbox with ⟨⟨hza, hzb⟩, hzc, hzd⟩
  rcases hzcell with ⟨hzx, hzy⟩
  fin_cases i <;> fin_cases j
  all_goals simp only [masterBandInterior, mem_Iio, mem_Ioo, mem_Ioi] at hzx hzy
  · convert closedAxisBox_isRectangle (a := a) (b := min b x₀) (c := c) (d := min d y₀)
      (by rw [lt_min_iff]; exact ⟨hab, hza.trans hzx⟩)
      (by rw [lt_min_iff]; exact ⟨hcd, hzc.trans hzy⟩) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Iic, le_min_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := a) (b := min b x₀) (c := max c y₀)
      (d := min d y₁) (by rw [lt_min_iff]; exact ⟨hab, hza.trans hzx⟩)
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Iic, le_min_iff, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := a) (b := min b x₀) (c := max c y₁) (d := d)
      (by rw [lt_min_iff]; exact ⟨hab, hza.trans hzx⟩)
      (by simpa only [max_lt_iff] using And.intro hcd (hzy.trans hzd)) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Ici, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₀) (b := min b x₁) (c := c)
      (d := min d y₀)
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith)
      (by rw [lt_min_iff]; exact ⟨hcd, hzc.trans hzy⟩) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Iic, le_min_iff, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₀) (b := min b x₁) (c := max c y₀)
      (d := min d y₁)
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith)
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, le_min_iff, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₀) (b := min b x₁) (c := max c y₁)
      (d := d)
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith)
      (by simpa only [max_lt_iff] using And.intro hcd (hzy.trans hzd)) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Ici, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₁) (b := b) (c := c) (d := min d y₀)
      (by simpa only [max_lt_iff] using And.intro hab (hzx.trans hzb))
      (by rw [lt_min_iff]; exact ⟨hcd, hzc.trans hzy⟩) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Iic, le_min_iff, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₁) (b := b) (c := max c y₀)
      (d := min d y₁)
      (by simpa only [max_lt_iff] using And.intro hab (hzx.trans hzb))
      (by simp only [max_lt_iff, lt_min_iff]; constructor <;> constructor <;> linarith) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Ici, max_le_iff]
    aesop
  · convert closedAxisBox_isRectangle (a := max a x₁) (b := b) (c := max c y₁) (d := d)
      (by simpa only [max_lt_iff] using And.intro hab (hzx.trans hzb))
      (by simpa only [max_lt_iff] using And.intro hcd (hzy.trans hzd)) using 1
    ext w
    simp only [closedAxisBox, masterGridCell, masterBandSet, mem_inter_iff,
      mem_ofPred_eq, mem_Icc, mem_Ici, max_le_iff]
    aesop

private theorem exists_nondegenerate_outerClip_of_goodPoint
    {r : Set Tiling.Plane} (hr : Tiling.IsRectangle r)
    {x₀ x₁ y₀ y₁ : ℝ} (_hx : x₀ < x₁) (_hy : y₀ < y₁)
    {z : Tiling.Plane} (hzr : z ∈ interior r)
    (hzout : z ∉ closedAxisBox x₀ x₁ y₀ y₁)
    (hcuts : z.re ≠ x₀ ∧ z.re ≠ x₁ ∧ z.im ≠ y₀ ∧ z.im ≠ y₁) :
    ∃ i j : MasterBand,
      (i, j) ≠ (MasterBand.middle, MasterBand.middle) ∧
      z ∈ r ∩ masterGridCell x₀ x₁ y₀ y₁ i j ∧
      Tiling.IsRectangle (r ∩ masterGridCell x₀ x₁ y₀ y₁ i j) := by
  obtain ⟨a, b, c, d, hab, hcd, rfl⟩ := isRectangle_eq_closedAxisBox hr
  rcases hcuts with ⟨hcx₀, hcx₁, hcy₀, hcy₁⟩
  obtain ⟨i, hzi⟩ := exists_masterBandInterior x₀ x₁ z.re hcx₀ hcx₁
  obtain ⟨j, hzj⟩ := exists_masterBandInterior y₀ y₁ z.im hcy₀ hcy₁
  have hzcellInt : z.re ∈ masterBandInterior x₀ x₁ i ∧
      z.im ∈ masterBandInterior y₀ y₁ j := ⟨hzi, hzj⟩
  have hzne : (i, j) ≠ (MasterBand.middle, MasterBand.middle) := by
    intro hij
    have hi : i = MasterBand.middle := congrArg Prod.fst hij
    have hj : j = MasterBand.middle := congrArg Prod.snd hij
    have hzmid : z ∈ closedAxisBox x₀ x₁ y₀ y₁ := by
      rcases hzcellInt with ⟨hzx, hzy⟩
      rw [hi] at hzx
      rw [hj] at hzy
      change (x₀ ≤ z.re ∧ z.re ≤ x₁) ∧ y₀ ≤ z.im ∧ z.im ≤ y₁
      exact ⟨⟨hzx.1.le, hzx.2.le⟩, hzy.1.le, hzy.2.le⟩
    exact hzout hzmid
  have hzcell : z ∈ masterGridCell x₀ x₁ y₀ y₁ i j := by
    rcases hzcellInt with ⟨hzx, hzy⟩
    exact ⟨masterBandInterior_subset x₀ x₁ i hzx,
      masterBandInterior_subset y₀ y₁ j hzy⟩
  refine ⟨i, j, hzne, ⟨interior_subset hzr, hzcell⟩,
    closedAxisBox_inter_masterGridCell_isRectangle hab hcd i j z hzr hzcellInt⟩

private theorem goodPoint_mem_clippedOuterPieces_sUnion
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    {old : Set Tiling.Plane} (hold : old ∈ R.pieces)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    {z : Tiling.Plane} (hzold : z ∈ interior old)
    (hzout : z ∉ closedAxisBox x₀ x₁ y₀ y₁)
    (hcuts : z.re ≠ x₀ ∧ z.re ≠ x₁ ∧ z.im ≠ y₀ ∧ z.im ≠ y₁) :
    z ∈ ⋃₀ (clippedOuterPieces R x₀ x₁ y₀ y₁ : Set (Set Tiling.Plane)) := by
  classical
  obtain ⟨i, j, hij, hzclip, hrect⟩ :=
    exists_nondegenerate_outerClip_of_goodPoint (R.isRectangle old hold) hx hy hzold hzout hcuts
  let cell := masterGridCell x₀ x₁ y₀ y₁ i j
  have hcell : cell ∈ outerMasterCells x₀ x₁ y₀ y₁ := by
    rw [outerMasterCells, Finset.mem_image]
    exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩
  have hclip : old ∩ cell ∈ clippedOuterPieces R x₀ x₁ y₀ y₁ := by
    rw [clippedOuterPieces, Finset.mem_image]
    exact ⟨(old, cell), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hold, hcell⟩, hrect⟩, rfl⟩
  exact ⟨old ∩ cell, hclip, hzclip⟩

private theorem isClosed_closedAxisBox (a b c d : ℝ) :
    IsClosed (closedAxisBox a b c d) := by
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

private theorem closure_interior_closedAxisBox
    {a b c d : ℝ} (hab : a < b) (hcd : c < d) :
    closure (interior (closedAxisBox a b c d)) = closedAxisBox a b c d := by
  rw [interior_closedAxisBox hab hcd]
  change closure (Ioo a b ×ℂ Ioo c d) = Icc a b ×ℂ Icc c d
  rw [Complex.closure_reProdIm, closure_Ioo hab.ne, closure_Ioo hcd.ne]

private theorem IsRectangle.isClosed {r : Set Tiling.Plane} (hr : Tiling.IsRectangle r) :
    IsClosed r := by
  obtain ⟨a, b, c, d, _, _, rfl⟩ := isRectangle_eq_closedAxisBox hr
  exact isClosed_closedAxisBox a b c d

private theorem IsRectangle.mem_closure_interior
    {r : Set Tiling.Plane} (hr : Tiling.IsRectangle r) {z : Tiling.Plane} (hz : z ∈ r) :
    z ∈ closure (interior r) := by
  obtain ⟨a, b, c, d, hab, hcd, rfl⟩ := isRectangle_eq_closedAxisBox hr
  rw [closure_interior_closedAxisBox hab hcd]
  exact hz

private theorem exists_mem_ne_cutLines
    {U : Set Tiling.Plane} (hUopen : IsOpen U) (hUne : U.Nonempty)
    (x₀ x₁ y₀ y₁ : ℝ) :
    ∃ z ∈ U, z.re ≠ x₀ ∧ z.re ≠ x₁ ∧ z.im ≠ y₀ ∧ z.im ≠ y₁ := by
  let cuts : Set Tiling.Plane :=
    {z | z.re = x₀} ∪ {z | z.re = x₁} ∪ {z | z.im = y₀} ∪ {z | z.im = y₁}
  have hcutszero : volume cuts = 0 := by
    dsimp only [cuts]
    exact measure_union_null
      (measure_union_null
        (measure_union_null (volume_re_eq_zero x₀) (volume_re_eq_zero x₁))
        (volume_im_eq_zero y₀))
      (volume_im_eq_zero y₁)
  by_contra h
  push Not at h
  have hsub : U ⊆ cuts := by
    intro z hz
    specialize h z hz
    simp only [cuts, mem_union, mem_ofPred_eq]
    tauto
  have hUzero : volume U = 0 := measure_mono_null hsub hcutszero
  exact hUopen.measure_ne_zero volume hUne hUzero

private theorem isClosed_sUnion_clippedOuterPieces
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) :
    IsClosed (⋃₀ (clippedOuterPieces R x₀ x₁ y₀ y₁ : Set (Set Tiling.Plane))) := by
  classical
  rw [sUnion_eq_biUnion]
  apply isClosed_biUnion_finset
  intro r hr
  rw [clippedOuterPieces, Finset.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  exact IsRectangle.isClosed (Finset.mem_filter.mp hp).2

private theorem oldPoint_outside_mem_clippedOuterPieces_sUnion
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    {old : Set Tiling.Plane} (hold : old ∈ R.pieces)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ < x₁) (hy : y₀ < y₁)
    {z : Tiling.Plane} (hzold : z ∈ old)
    (hzout : z ∉ closedAxisBox x₀ x₁ y₀ y₁) :
    z ∈ ⋃₀ (clippedOuterPieces R x₀ x₁ y₀ y₁ : Set (Set Tiling.Plane)) := by
  let U := ⋃₀ (clippedOuterPieces R x₀ x₁ y₀ y₁ : Set (Set Tiling.Plane))
  have hUclosed : IsClosed U := isClosed_sUnion_clippedOuterPieces R x₀ x₁ y₀ y₁
  change z ∈ U
  rw [← hUclosed.closure_eq]
  rw [mem_closure_iff]
  intro N hNopen hzN
  let W := N ∩ (closedAxisBox x₀ x₁ y₀ y₁)ᶜ
  have hWopen : IsOpen W := hNopen.inter (isClosed_closedAxisBox _ _ _ _).isOpen_compl
  have hzW : z ∈ W := ⟨hzN, hzout⟩
  have hzclosure := IsRectangle.mem_closure_interior (R.isRectangle old hold) hzold
  obtain ⟨w, hwW, hwold⟩ := (mem_closure_iff.mp hzclosure) W hWopen hzW
  let V := W ∩ interior old
  have hVopen : IsOpen V := hWopen.inter isOpen_interior
  have hVne : V.Nonempty := ⟨w, hwW, hwold⟩
  obtain ⟨u, huV, hucuts⟩ := exists_mem_ne_cutLines hVopen hVne x₀ x₁ y₀ y₁
  have huU : u ∈ U := goodPoint_mem_clippedOuterPieces_sUnion R hold hx hy
    huV.2 huV.1.2 hucuts
  exact ⟨u, huV.1.1, huU⟩

private theorem localReplacement_sUnion_eq
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) (q : Set Tiling.Plane)
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hcentral : s ∩ closedAxisBox x₀ x₁ y₀ y₁ = q) :
    ⋃₀ (localReplacementPieces R x₀ x₁ y₀ y₁ q :
      Set (Set Tiling.Plane)) = s := by
  classical
  apply Set.Subset.antisymm
  · rintro z ⟨r, hr, hzr⟩
    change r ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q at hr
    rw [localReplacementPieces, Finset.mem_insert] at hr
    rcases hr with rfl | hr
    · exact (hcentral.symm ▸ hzr).1
    · obtain ⟨old, hold, i, j, hij, rfl⟩ :=
        mem_clippedOuterPieces R x₀ x₁ y₀ y₁ hr
      rw [← R.sUnion_eq]
      exact ⟨old, hold, hzr.1⟩
  · intro z hzs
    have hzoldUnion : z ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := R.sUnion_eq.symm ▸ hzs
    obtain ⟨old, hold, hzold⟩ := hzoldUnion
    by_cases hzbox : z ∈ closedAxisBox x₀ x₁ y₀ y₁
    · refine ⟨q, ?_, ?_⟩
      · change q ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q
        simp [localReplacementPieces]
      · exact hcentral ▸ ⟨hzs, hzbox⟩
    · obtain ⟨r, hr, hzr⟩ := oldPoint_outside_mem_clippedOuterPieces_sUnion
        R hold hx hy hzold hzbox
      refine ⟨r, ?_, hzr⟩
      change r ∈ localReplacementPieces R x₀ x₁ y₀ y₁ q
      rw [localReplacementPieces, Finset.mem_insert]
      exact Or.inr hr

private theorem exists_localReplacementRectangulation
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (x₀ x₁ y₀ y₁ : ℝ) (q : Set Tiling.Plane) (v : Tiling.Plane)
    (hx₀ : x₀ < v.re) (hx₁ : v.re < x₁)
    (hy₀ : y₀ < v.im) (hy₁ : v.im < y₁)
    (hqrect : Tiling.IsRectangle q) (hqv : v ∉ q.extremePoints ℝ)
    (hcentral : s ∩ closedAxisBox x₀ x₁ y₀ y₁ = q) :
    ∃ R' : Tiling.Rectangulation s,
      R'.pieces = localReplacementPieces R x₀ x₁ y₀ y₁ q ∧
      RectangulationAvoids R' v := by
  have hx : x₀ < x₁ := hx₀.trans hx₁
  have hy : y₀ < y₁ := hy₀.trans hy₁
  have hqsub : q ⊆ closedAxisBox x₀ x₁ y₀ y₁ := by
    intro z hz
    exact (hcentral.symm ▸ hz).2
  let R' : Tiling.Rectangulation s :=
    { pieces := localReplacementPieces R x₀ x₁ y₀ y₁ q
      isRectangle := localReplacement_isRectangle R x₀ x₁ y₀ y₁ q hqrect
      pairwiseAEDisjoint := localReplacement_pairwiseAEDisjoint
        R x₀ x₁ y₀ y₁ q hx hy hqsub
      sUnion_eq := localReplacement_sUnion_eq R x₀ x₁ y₀ y₁ q hx hy hcentral }
  refine ⟨R', rfl, ?_⟩
  exact localReplacement_avoids R x₀ x₁ y₀ y₁ q v
    hx₀ hx₁ hy₀ hy₁ hqv

private theorem triangulationAvoids_not_mem_vertexSet
    {s : Set Tiling.Plane} (T : Tiling.Triangulation s) (v : Tiling.Plane)
    (havoid : TriangulationAvoids T v) : v ∉ Tiling.vertexSet s := by
  intro hv
  obtain ⟨t, ht, hvt⟩ := hv T
  exact havoid t ht hvt

private theorem midpoint_not_mem_extremePoints
    {S : Set Tiling.Plane} {v a b : Tiling.Plane}
    (ha : a ∈ S) (hb : b ∈ S) (hav : a ≠ v)
    (hm : (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b = v) :
    v ∉ S.extremePoints ℝ := by
  intro hv
  have hvopen : v ∈ openSegment ℝ a b :=
    ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹, by positivity, by positivity, by norm_num, hm⟩
  exact hav ((mem_extremePoints_iff_left.mp hv).2 a ha b hb hvopen)

set_option linter.style.longLine false in
private theorem cutPoint_not_extremePoint_closedHalfBox
    (x₀ x₁ y₀ y₁ : ℝ) (v : Tiling.Plane) (side : HalfBoxSide)
    (hx₀ : x₀ < v.re) (hx₁ : v.re < x₁)
    (hy₀ : y₀ < v.im) (hy₁ : v.im < y₁) :
    v ∉ (closedHalfBox x₀ x₁ y₀ y₁ v side).extremePoints ℝ := by
  let dx := min (v.re - x₀) (x₁ - v.re) / 2
  let dy := min (v.im - y₀) (y₁ - v.im) / 2
  have hdx : 0 < dx := div_pos (lt_min (sub_pos.mpr hx₀) (sub_pos.mpr hx₁)) zero_lt_two
  have hdy : 0 < dy := div_pos (lt_min (sub_pos.mpr hy₀) (sub_pos.mpr hy₁)) zero_lt_two
  have hdx₀ : dx < v.re - x₀ := by dsimp [dx]; nlinarith [min_le_left (v.re-x₀) (x₁-v.re)]
  have hdx₁ : dx < x₁ - v.re := by dsimp [dx]; nlinarith [min_le_right (v.re-x₀) (x₁-v.re)]
  have hdy₀ : dy < v.im - y₀ := by dsimp [dy]; nlinarith [min_le_left (v.im-y₀) (y₁-v.im)]
  have hdy₁ : dy < y₁ - v.im := by dsimp [dy]; nlinarith [min_le_right (v.im-y₀) (y₁-v.im)]
  cases side
  · apply midpoint_not_mem_extremePoints (a := v - dy * Complex.I) (b := v + dy * Complex.I)
    · exact ⟨⟨(by simpa using hx₀.le), (by simp)⟩, ⟨by simpa using (show y₀ ≤ v.im - dy by linarith), by simpa using (show v.im - dy ≤ y₁ by linarith)⟩⟩
    · exact ⟨⟨(by simpa using hx₀.le), (by simp)⟩, ⟨by simpa using (show y₀ ≤ v.im + dy by linarith), by simpa using (show v.im + dy ≤ y₁ by linarith)⟩⟩
    · intro h; have := congrArg Complex.im h; simp at this; linarith
    · apply Complex.ext <;> simp <;> ring
  · apply midpoint_not_mem_extremePoints (a := v - dy * Complex.I) (b := v + dy * Complex.I)
    · exact ⟨⟨(by simp), (by simpa using hx₁.le)⟩, ⟨by simpa using (show y₀ ≤ v.im - dy by linarith), by simpa using (show v.im - dy ≤ y₁ by linarith)⟩⟩
    · exact ⟨⟨(by simp), (by simpa using hx₁.le)⟩, ⟨by simpa using (show y₀ ≤ v.im + dy by linarith), by simpa using (show v.im + dy ≤ y₁ by linarith)⟩⟩
    · intro h; have := congrArg Complex.im h; simp at this; linarith
    · apply Complex.ext <;> simp <;> ring
  · apply midpoint_not_mem_extremePoints (a := v - dx) (b := v + dx)
    · exact ⟨⟨by simpa using (show x₀ ≤ v.re - dx by linarith), by simpa using (show v.re - dx ≤ x₁ by linarith)⟩, ⟨(by simpa using hy₀.le), (by simp)⟩⟩
    · exact ⟨⟨by simpa using (show x₀ ≤ v.re + dx by linarith), by simpa using (show v.re + dx ≤ x₁ by linarith)⟩, ⟨(by simpa using hy₀.le), (by simp)⟩⟩
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · apply Complex.ext <;> simp <;> ring
  · apply midpoint_not_mem_extremePoints (a := v - dx) (b := v + dx)
    · exact ⟨⟨by simpa using (show x₀ ≤ v.re - dx by linarith), by simpa using (show v.re - dx ≤ x₁ by linarith)⟩, ⟨(by simp), (by simpa using hy₁.le)⟩⟩
    · exact ⟨⟨by simpa using (show x₀ ≤ v.re + dx by linarith), by simpa using (show v.re + dx ≤ x₁ by linarith)⟩, ⟨(by simp), (by simpa using hy₁.le)⟩⟩
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · apply Complex.ext <;> simp <;> ring

set_option linter.style.longLine false in
private theorem interiorPoint_not_extremePoint_closedAxisBox
    (x₀ x₁ y₀ y₁ : ℝ) (v : Tiling.Plane)
    (hx₀ : x₀ < v.re) (hx₁ : v.re < x₁)
    (hy₀ : y₀ < v.im) (hy₁ : v.im < y₁) :
    v ∉ (closedAxisBox x₀ x₁ y₀ y₁).extremePoints ℝ := by
  let dx := min (v.re - x₀) (x₁ - v.re) / 2
  have hdx : 0 < dx := div_pos (lt_min (sub_pos.mpr hx₀) (sub_pos.mpr hx₁)) zero_lt_two
  have hdx₀ : dx < v.re - x₀ := by dsimp [dx]; nlinarith [min_le_left (v.re-x₀) (x₁-v.re)]
  have hdx₁ : dx < x₁ - v.re := by dsimp [dx]; nlinarith [min_le_right (v.re-x₀) (x₁-v.re)]
  apply midpoint_not_mem_extremePoints (a := v - dx) (b := v + dx)
  · exact ⟨⟨by simpa using (show x₀ ≤ v.re - dx by linarith), by simpa using (show v.re - dx ≤ x₁ by linarith)⟩, ⟨(by simpa using hy₀.le), (by simpa using hy₁.le)⟩⟩
  · exact ⟨⟨by simpa using (show x₀ ≤ v.re + dx by linarith), by simpa using (show v.re + dx ≤ x₁ by linarith)⟩, ⟨(by simpa using hy₀.le), (by simpa using hy₁.le)⟩⟩
  · intro h; have := congrArg Complex.re h; simp at this; linarith
  · apply Complex.ext <;> simp <;> ring

private theorem exists_localClosedBox_of_mem_interior :
    ∀ (K : Region) (v : Tiling.Plane), v ∈ interior K.support →
      ∃ x₀ x₁ y₀ y₁ : ℝ,
        x₀ < v.re ∧ v.re < x₁ ∧ y₀ < v.im ∧ v.im < y₁ ∧
        Tiling.IsRectangle (closedAxisBox x₀ x₁ y₀ y₁) ∧
        K.support ∩ closedAxisBox x₀ x₁ y₀ y₁ =
          closedAxisBox x₀ x₁ y₀ y₁ := by
  intro K v hv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hv)
  let d := r / 4
  have hd : 0 < d := div_pos hr (by norm_num)
  refine ⟨v.re - d, v.re + d, v.im - d, v.im + d, by linarith, by linarith,
    by linarith, by linarith, closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
  rw [inter_eq_right]
  intro z hz
  apply interior_subset (hball ?_)
  rw [Metric.mem_ball, dist_eq_norm, Complex.norm_def]
  have hre : |z.re - v.re| ≤ d := by
    rw [abs_le]
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
  have him : |z.im - v.im| ≤ d := by
    rw [abs_le]
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  calc
    √ (Complex.normSq (z - v)) = ‖z - v‖ := Complex.norm_def (z - v) |>.symm
    _ ≤ |(z - v).re| + |(z - v).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ d + d := by simpa using add_le_add hre him
    _ < r := by dsimp [d]; linarith

private theorem mul_sub_nonneg_iff_of_pos {a x y : ℝ} (ha : 0 < a) :
    0 ≤ a * (x - y) ↔ y ≤ x := by
  rw [mul_nonneg_iff_of_pos_left ha, sub_nonneg]

private theorem mul_sub_nonneg_iff_of_neg {a x y : ℝ} (ha : a < 0) :
    0 ≤ a * (x - y) ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hn
    have hp : 0 < x - y := sub_pos.mpr (lt_of_not_ge hn)
    exact (not_lt_of_ge h) (mul_neg_of_neg_of_pos ha hp)
  · intro h
    exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr h)

private theorem mul_sub_nonpos_iff_of_pos {a x y : ℝ} (ha : 0 < a) :
    a * (x - y) ≤ 0 ↔ x ≤ y := by
  constructor
  · intro h
    by_contra hn
    exact (not_lt_of_ge h) (mul_pos ha (sub_pos.mpr (lt_of_not_ge hn)))
  · intro h
    exact mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr h)

private theorem mul_sub_nonpos_iff_of_neg {a x y : ℝ} (ha : a < 0) :
    a * (x - y) ≤ 0 ↔ y ≤ x := by
  constructor
  · intro h
    by_contra hn
    have hs : x - y < 0 := sub_neg.mpr (lt_of_not_ge hn)
    exact (not_lt_of_ge h) (mul_pos_of_neg_of_neg ha hs)
  · intro h
    exact mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr h)

private theorem vertical_halfPlane_iff
    (v d w : Tiling.Plane) (hd : d.re = 0) :
    (w ∈ Tiling.positiveHalfPlane v d ↔ 0 ≤ d.im * (v.re - w.re)) ∧
    (w ∈ Tiling.negativeHalfPlane v d ↔ d.im * (v.re - w.re) ≤ 0) := by
  constructor
  · rw [Tiling.mem_positiveHalfPlane]
    simp only [Tiling.signedSide, Tiling.planarCross, hd, zero_mul, zero_sub]
    constructor <;> intro h <;> linarith
  · rw [Tiling.mem_negativeHalfPlane]
    simp only [Tiling.signedSide, Tiling.planarCross, hd, zero_mul, zero_sub]
    constructor <;> intro h <;> linarith

private theorem horizontal_halfPlane_iff
    (v d w : Tiling.Plane) (hd : d.im = 0) :
    (w ∈ Tiling.positiveHalfPlane v d ↔ 0 ≤ d.re * (w.im - v.im)) ∧
    (w ∈ Tiling.negativeHalfPlane v d ↔ d.re * (w.im - v.im) ≤ 0) := by
  constructor
  · rw [Tiling.mem_positiveHalfPlane]
    simp only [Tiling.signedSide, Tiling.planarCross]
    rw [hd]
    constructor <;> intro h <;> linarith
  · rw [Tiling.mem_negativeHalfPlane]
    simp only [Tiling.signedSide, Tiling.planarCross]
    rw [hd]
    constructor <;> intro h <;> linarith

private theorem exists_localClosedHalfBox :
    ∀ (K : Region) (v : Tiling.Plane),
      v ∈ frontier K.openCarrier →
      Tiling.BoundaryLocallyStraightAt K.openCarrier v →
      ∃ (x₀ x₁ y₀ y₁ : ℝ) (side : HalfBoxSide),
        x₀ < v.re ∧ v.re < x₁ ∧ y₀ < v.im ∧ v.im < y₁ ∧
        Tiling.IsRectangle (closedAxisBox x₀ x₁ y₀ y₁) ∧
        Tiling.IsRectangle (closedHalfBox x₀ x₁ y₀ y₁ v side) ∧
        K.support ∩ closedAxisBox x₀ x₁ y₀ y₁ =
          closedHalfBox x₀ x₁ y₀ y₁ v side := by
  intro K v _hv hstraight
  have heqFrontier : frontier K.openCarrier = frontier K.support := by
    rw [frontier, frontier]
    change closure (interior K.support) \ interior (interior K.support) =
      closure K.support \ interior K.support
    rw [K.isPolygonal.closure_interior, interior_interior,
      K.isPolygonal.isClosed.closure_eq]
  obtain ⟨L, hvL, hdim, hlocal⟩ := hstraight
  obtain ⟨d, hd, r, hr, hfront⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hvL hdim hlocal
  obtain ⟨q, hq, hcross⟩ := K.isAxisParallel.localBoundaryCross v
  let ε := min r q / (2 * (‖d‖ + 1))
  have hmin : 0 < min r q := lt_min hr hq
  have hden : 0 < 2 * (‖d‖ + 1) := mul_pos (by norm_num) (by positivity)
  have hε : 0 < ε := div_pos hmin hden
  let z := v + ε • d
  have hzdist : dist z v < min r q := by
    rw [dist_comm, show dist v z = ‖ε • d‖ by simp [z, dist_eq_norm]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    dsimp [ε]
    have hn : 0 ≤ ‖d‖ := norm_nonneg _
    field_simp
    nlinarith
  have hzfront : z ∈ frontier K.openCarrier :=
    (hfront z (Metric.mem_ball.mpr (lt_of_lt_of_le hzdist (min_le_left _ _)))).2
      (Tiling.vadd_smul_mem_affineLine v d ε)
  have hzaxis := hcross z
    (Metric.mem_ball.mpr (lt_of_lt_of_le hzdist (min_le_right _ _)))
    (heqFrontier ▸ hzfront)
  have halign : d.re = 0 ∨ d.im = 0 := by
    rcases hzaxis with hz | hz
    · left
      have : ε * d.re = 0 := by simpa [z] using hz
      exact (mul_eq_zero.mp this).resolve_left hε.ne'
    · right
      have : ε * d.im = 0 := by simpa [z] using hz
      exact (mul_eq_zero.mp this).resolve_left hε.ne'
  have hregular : closure (interior K.support) = K.support := K.isPolygonal.closure_interior
  have hfrontSupport : ∀ w, w ∈ Metric.ball v r →
      (w ∈ frontier K.support ↔ w ∈ Tiling.affineLine v d) := by
    intro w hw
    rw [← heqFrontier, hfront w hw]
  have hhalf := Tiling.local_eq_closedHalfPlane hd hr hregular hfrontSupport
  let δ := min r q / 4
  have hδ : 0 < δ := div_pos hmin (by norm_num)
  have hboxBall : closedAxisBox (v.re-δ) (v.re+δ) (v.im-δ) (v.im+δ) ⊆
      Metric.ball v r := by
    intro w hw
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖w - v‖ ≤ |(w-v).re| + |(w-v).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ δ + δ := by
        simp only [Complex.sub_re, Complex.sub_im]
        apply add_le_add
        · rw [abs_le]
          exact ⟨by linarith [hw.1.1], by linarith [hw.1.2]⟩
        · rw [abs_le]
          exact ⟨by linarith [hw.2.1], by linarith [hw.2.2]⟩
      _ < r := by dsimp [δ]; nlinarith [min_le_left r q]
  have restrict_half {H : Set Tiling.Plane}
      (hh : K.support ∩ Metric.ball v r = H ∩ Metric.ball v r) :
      K.support ∩ closedAxisBox (v.re-δ) (v.re+δ) (v.im-δ) (v.im+δ) =
        H ∩ closedAxisBox (v.re-δ) (v.re+δ) (v.im-δ) (v.im+δ) := by
    ext w
    have hwball (hw : w ∈ closedAxisBox (v.re-δ) (v.re+δ) (v.im-δ) (v.im+δ)) := hboxBall hw
    constructor <;> rintro ⟨hw, hb⟩
    · exact ⟨((Set.ext_iff.mp hh w).mp ⟨hw, hwball hb⟩).1, hb⟩
    · exact ⟨((Set.ext_iff.mp hh w).mpr ⟨hw, hwball hb⟩).1, hb⟩
  rcases halign with hdre | hdim
  · have hdimne : d.im ≠ 0 := by intro h; apply hd; apply Complex.ext <;> simp [hdre, h]
    rcases lt_or_gt_of_ne hdimne with hneg | hpos
    · rcases hhalf with hh | hh
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .right,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(vertical_halfPlane_iff v d w hdre).1]
        rw [mul_sub_nonneg_iff_of_neg hneg]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .left,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(vertical_halfPlane_iff v d w hdre).2]
        rw [mul_sub_nonpos_iff_of_neg hneg]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
    · rcases hhalf with hh | hh
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .left,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(vertical_halfPlane_iff v d w hdre).1]
        rw [mul_sub_nonneg_iff_of_pos hpos]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .right,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(vertical_halfPlane_iff v d w hdre).2]
        rw [mul_sub_nonpos_iff_of_pos hpos]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
  · have hdrene : d.re ≠ 0 := by intro h; apply hd; apply Complex.ext <;> simp [h, hdim]
    rcases lt_or_gt_of_ne hdrene with hneg | hpos
    · rcases hhalf with hh | hh
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .lower,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(horizontal_halfPlane_iff v d w hdim).1]
        rw [mul_sub_nonneg_iff_of_neg hneg]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .upper,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(horizontal_halfPlane_iff v d w hdim).2]
        rw [mul_sub_nonpos_iff_of_neg hneg]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
    · rcases hhalf with hh | hh
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .upper,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(horizontal_halfPlane_iff v d w hdim).1]
        rw [mul_sub_nonneg_iff_of_pos hpos]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind
      · refine ⟨v.re-δ, v.re+δ, v.im-δ, v.im+δ, .lower,
          by linarith, by linarith, by linarith, by linarith,
          closedAxisBox_isRectangle (by linarith) (by linarith),
          closedAxisBox_isRectangle (by linarith) (by linarith), ?_⟩
        rw [restrict_half hh]
        ext w
        simp only [mem_inter_iff]
        rw [(horizontal_halfPlane_iff v d w hdim).2]
        rw [mul_sub_nonpos_iff_of_pos hpos]
        simp only [closedHalfBox, closedAxisBox, mem_ofPred_eq, mem_Icc]
        grind


private theorem rectangle_corner_mem_extremePoints
    (a b p : Tiling.Plane)
    (hpRe : p.re = a.re ∨ p.re = b.re)
    (hpIm : p.im = a.im ∨ p.im = b.im) :
    p ∈ (Complex.Rectangle a b).extremePoints ℝ := by
  rw [← Complex.equivRealProdCLM.injective.mem_set_image]
  rw [image_extremePoints]
  have himage : Complex.equivRealProdCLM '' Complex.Rectangle a b =
      (uIcc a.re b.re) ×ˢ (uIcc a.im b.im) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact Complex.mem_reProdIm.mp hz
    · intro hq
      refine ⟨q.1 + q.2 * Complex.I, ?_, ?_⟩
      · apply Complex.mem_reProdIm.mpr
        exact ⟨by simpa using hq.1, by simpa using hq.2⟩
      · ext <;> simp
  rw [himage, extremePoints_prod]
  rcases le_total a.re b.re with hab | hba
  · rcases le_total a.im b.im with hcd | hdc
    · simp [uIcc_of_le hab, uIcc_of_le hcd] at *
      aesop
    · simp [uIcc_of_le hab, uIcc_of_ge hdc] at *
      aesop
  · rcases le_total a.im b.im with hcd | hdc
    · simp [uIcc_of_ge hba, uIcc_of_le hcd] at *
      aesop
    · simp [uIcc_of_ge hba, uIcc_of_ge hdc] at *
      aesop

private theorem diagonalTriangle_extremePoints_subset_rectangle
    (a b : Tiling.Plane) :
    (convexHull ℝ {a, a.re + b.im * Complex.I, b}).extremePoints ℝ ⊆
        (Complex.Rectangle a b).extremePoints ℝ ∧
      (convexHull ℝ {a, b.re + a.im * Complex.I, b}).extremePoints ℝ ⊆
        (Complex.Rectangle a b).extremePoints ℝ := by
  constructor <;> intro p hp
  · have hpgen := extremePoints_convexHull_subset hp
    simp only [mem_insert_iff, mem_singleton_iff] at hpgen
    rcases hpgen with hpgen | hpgen | hpgen
    · subst p
      exact rectangle_corner_mem_extremePoints a b a (Or.inl rfl) (Or.inl rfl)
    · subst p
      apply rectangle_corner_mem_extremePoints a b
      · left; simp
      · right; simp
    · subst p
      exact rectangle_corner_mem_extremePoints a b b (Or.inr rfl) (Or.inr rfl)
  · have hpgen := extremePoints_convexHull_subset hp
    simp only [mem_insert_iff, mem_singleton_iff] at hpgen
    rcases hpgen with hpgen | hpgen | hpgen
    · subst p
      exact rectangle_corner_mem_extremePoints a b a (Or.inl rfl) (Or.inl rfl)
    · subst p
      apply rectangle_corner_mem_extremePoints a b
      · right; simp
      · left; simp
    · subst p
      exact rectangle_corner_mem_extremePoints a b b (Or.inr rfl) (Or.inr rfl)

private theorem exists_rectangleCanonicalTriangulation_avoids
    {r : Set Tiling.Plane} (hr : Tiling.IsRectangle r) (v : Tiling.Plane)
    (hv : v ∉ r.extremePoints ℝ) :
    ∃ T : Tiling.Triangulation r, TriangulationAvoids T v := by
  obtain ⟨a, b, hre, him, rfl⟩ := hr
  refine ⟨Tiling.rectangleDiagonalTriangulation a b hre him, ?_⟩
  intro t ht hvt
  rw [Tiling.rectangleDiagonalTriangulation_pieces] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl
  · exact hv ((diagonalTriangle_extremePoints_subset_rectangle a b).1 hvt)
  · exact hv ((diagonalTriangle_extremePoints_subset_rectangle a b).2 hvt)

theorem isPolygonal_of_isAxisParallel :
    ∀ {s : Set Tiling.Plane}, Tiling.IsAxisParallel s → Tiling.IsPolygonal s := by
  intro s haxis
  obtain ⟨R⟩ := haxis
  let T : ∀ r : ↥R.pieces, Tiling.Triangulation (r : Set Tiling.Plane) :=
    fun r ↦ Classical.choice (R.isRectangle r r.property).isPolygonal
  exact ⟨flattenRectangulation R T⟩

private theorem exists_avoidingTriangulation_of_rectangulation :
    ∀ {s : Set Tiling.Plane} (R : Tiling.Rectangulation s) (v : Tiling.Plane),
      RectangulationAvoids R v →
      ∃ T : Tiling.Triangulation s, TriangulationAvoids T v := by
  intro s R v havoid
  let hlocal (r : ↥R.pieces) := exists_rectangleCanonicalTriangulation_avoids
    (R.isRectangle r r.property) v (havoid r r.property)
  let T : ∀ r : ↥R.pieces, Tiling.Triangulation (r : Set Tiling.Plane) :=
    fun r ↦ Classical.choose (hlocal r)
  refine ⟨flattenRectangulation R T, ?_⟩
  intro t ht hvt
  obtain ⟨r, _, htr⟩ := Finset.mem_biUnion.mp ht
  exact (Classical.choose_spec (hlocal r)) t htr hvt

private theorem exists_avoidingTriangulation_of_mem_interior :
    ∀ (K : Region) (v : Tiling.Plane), v ∈ interior K.support →
      ∃ T : Tiling.Triangulation K.support, TriangulationAvoids T v := by
  intro K v hv
  obtain ⟨x₀, x₁, y₀, y₁, hx₀, hx₁, hy₀, hy₁, hrect, hcentral⟩ :=
    exists_localClosedBox_of_mem_interior K v hv
  obtain ⟨R⟩ := K.isAxisParallel
  obtain ⟨R', _, havoid⟩ := exists_localReplacementRectangulation
    R x₀ x₁ y₀ y₁ (closedAxisBox x₀ x₁ y₀ y₁) v
    hx₀ hx₁ hy₀ hy₁ hrect
    (interiorPoint_not_extremePoint_closedAxisBox x₀ x₁ y₀ y₁ v hx₀ hx₁ hy₀ hy₁)
    hcentral
  exact exists_avoidingTriangulation_of_rectangulation R' v havoid

theorem region_vertices_subset_frontier :
    ∀ K : Region, K.vertices ⊆ frontier K.openCarrier := by
  intro K v hv
  have hvs : v ∈ K.support := by
    obtain ⟨T⟩ := K.isPolygonal
    obtain ⟨t, ht, hvt⟩ := hv T
    rw [← T.sUnion_eq]
    exact ⟨t, ht, (mem_extremePoints_iff_left.mp hvt).1⟩
  have hvnotint : v ∉ interior K.support := by
    intro hvint
    obtain ⟨T, havoid⟩ := exists_avoidingTriangulation_of_mem_interior K v hvint
    obtain ⟨t, ht, hvt⟩ := hv T
    exact havoid t ht hvt
  have hvfront : v ∈ frontier K.support := by
    rw [K.isPolygonal.isClosed.frontier_eq]
    exact ⟨hvs, hvnotint⟩
  have heq : frontier K.openCarrier = frontier K.support := by
    rw [frontier, frontier]
    change closure (interior K.support) \ interior (interior K.support) =
      closure K.support \ interior K.support
    rw [K.isPolygonal.closure_interior, interior_interior,
      K.isPolygonal.isClosed.closure_eq]
  exact heq.symm ▸ hvfront

private theorem exists_avoidingTriangulation_of_boundaryLocallyStraightAt :
    ∀ (K : Region) (v : Tiling.Plane),
      v ∈ frontier K.openCarrier →
      Tiling.BoundaryLocallyStraightAt K.openCarrier v →
      ∃ T : Tiling.Triangulation K.support, TriangulationAvoids T v := by
  intro K v hvfront hvstraight
  obtain ⟨x₀, x₁, y₀, y₁, side, hx₀, hx₁, hy₀, hy₁, _, hrect, hcentral⟩ :=
    exists_localClosedHalfBox K v hvfront hvstraight
  obtain ⟨R⟩ := K.isAxisParallel
  obtain ⟨R', _, havoid⟩ := exists_localReplacementRectangulation
    R x₀ x₁ y₀ y₁ (closedHalfBox x₀ x₁ y₀ y₁ v side) v
    hx₀ hx₁ hy₀ hy₁ hrect
    (cutPoint_not_extremePoint_closedHalfBox
      x₀ x₁ y₀ y₁ v side hx₀ hx₁ hy₀ hy₁)
    hcentral
  exact exists_avoidingTriangulation_of_rectangulation R' v havoid

theorem region_vertices_eq_nonStraightBoundary :
    ∀ K : Region,
      K.vertices =
        {x : Tiling.Plane |
          x ∈ frontier K.openCarrier ∧
            ¬Tiling.BoundaryLocallyStraightAt K.openCarrier x} := by
  intro K
  ext x
  constructor
  · intro hx
    refine ⟨region_vertices_subset_frontier K hx, ?_⟩
    intro hstraight
    obtain ⟨T, havoid⟩ :=
      exists_avoidingTriangulation_of_boundaryLocallyStraightAt K x
        (region_vertices_subset_frontier K hx) hstraight
    obtain ⟨t, ht, hxt⟩ := hx T
    exact havoid t ht hxt
  · rintro ⟨hxfront, hxnotstraight⟩
    by_contra hxvertex
    have heq : frontier K.openCarrier = frontier K.support := by
      rw [frontier, frontier]
      change closure (interior K.support) \ interior (interior K.support) =
        closure K.support \ interior K.support
      rw [K.isPolygonal.closure_interior, interior_interior,
        K.isPolygonal.isClosed.closure_eq]
    have hs := K.isPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet
      (heq.symm ▸ hxfront) hxvertex
    apply hxnotstraight
    obtain ⟨L, hxL, hdim, hlocal⟩ := hs
    exact ⟨L, hxL, hdim, by simpa only [heq] using hlocal⟩

private theorem lineMap_injective {a b : Plane} (hab : a ≠ b) :
    Function.Injective (AffineMap.lineMap (k := ℝ) a b) := by
  intro x y h
  rw [AffineMap.lineMap_apply_module, AffineMap.lineMap_apply_module] at h
  by_cases hre : a.re = b.re
  · have him : a.im ≠ b.im := fun him ↦ hab (Complex.ext hre him)
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hi
    have hzero : (x - y) * (b.im - a.im) = 0 := by linear_combination hi
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (sub_ne_zero.mpr him.symm))
  · have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at hr
    have hzero : (x - y) * (b.re - a.re) = 0 := by linear_combination hr
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right
      (sub_ne_zero.mpr (Ne.symm hre)))

private theorem trim_frontierSegment_at_nearest_vertices :
    ∀ {D : Set Plane} {a b p : Plane},
      IsPolygonal D →
      a ∈ vertexSet D → b ∈ vertexSet D → a ≠ b →
      p ∈ openSegment ℝ a b → p ∉ vertexSet D →
      openSegment ℝ a b ⊆ frontier D →
      ∃ a' b' : Plane,
        a' ∈ vertexSet D ∧ b' ∈ vertexSet D ∧
        a' ≠ b' ∧ p ∈ openSegment ℝ a' b' ∧
        openSegment ℝ a' b' ⊆ frontier D \ vertexSet D ∧
        a' ∈ segment ℝ a b ∧ b' ∈ segment ℝ a b := by
  intro D a b p hD ha hb hab hp hpnot hfront
  rw [openSegment_eq_image_lineMap] at hp
  obtain ⟨tp, htp, hpt⟩ := hp
  let V : Set ℝ := {t | AffineMap.lineMap a b t ∈ vertexSet D}
  have hinj := lineMap_injective hab
  have hVfin : V.Finite := by
    apply Set.Finite.preimage (s := vertexSet D) (fun _ _ _ _ h ↦ hinj h) hD.vertexSet_finite
  let Vl : Set ℝ := V ∩ Iic tp
  let Vr : Set ℝ := V ∩ Ici tp
  have hVlfin : Vl.Finite := hVfin.subset inter_subset_left
  have hVrfin : Vr.Finite := hVfin.subset inter_subset_left
  have h0V : 0 ∈ V := by simp [V, ha]
  have h1V : 1 ∈ V := by simp [V, hb]
  have hVlne : Vl.Nonempty := ⟨0, h0V, htp.1.le⟩
  have hVrne : Vr.Nonempty := ⟨1, h1V, htp.2.le⟩
  obtain ⟨tl, htl, htlmax⟩ := Set.exists_max_image Vl id hVlfin hVlne
  obtain ⟨tr, htr, htrmin⟩ := Set.exists_min_image Vr id hVrfin hVrne
  have hlt : tl < tp := lt_of_le_of_ne htl.2 (fun h ↦ hpnot (by rw [← hpt, ← h]; exact htl.1))
  have hgt : tp < tr := lt_of_le_of_ne htr.2 (fun h ↦ hpnot (by rw [← hpt, h]; exact htr.1))
  have htl0 : 0 ≤ tl := by simpa using htlmax 0 ⟨h0V, htp.1.le⟩
  have htr1 : tr ≤ 1 := by simpa using htrmin 1 ⟨h1V, htp.2.le⟩
  refine ⟨AffineMap.lineMap a b tl, AffineMap.lineMap a b tr,
    htl.1, htr.1, ?_, ?_, ?_, ?_, ?_⟩
  · apply hinj.ne
    exact (lt_trans hlt hgt).ne
  · rw [openSegment_eq_image_lineMap]
    refine ⟨(tp - tl) / (tr - tl), ?_, ?_⟩
    · constructor
      · exact div_pos (sub_pos.mpr hlt) (sub_pos.mpr (lt_trans hlt hgt))
      · rw [div_lt_one (sub_pos.mpr (lt_trans hlt hgt))]
        linarith
    · rw [← hpt]
      apply Complex.ext <;> simp only [Complex.add_re, Complex.smul_re, Complex.add_im,
        Complex.smul_im, smul_eq_mul, AffineMap.lineMap_apply_module] <;>
        field_simp [ne_of_gt (sub_pos.mpr (lt_trans hlt hgt))] <;> ring
  · intro z hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    have htltr : tl < tr := lt_trans hlt hgt
    let t := tl + u * (tr - tl)
    have ht_between : tl < t ∧ t < tr := by
      dsimp [t]
      constructor <;> nlinarith [hu.1, hu.2, sub_pos.mpr htltr]
    have hline : AffineMap.lineMap (AffineMap.lineMap a b tl)
        (AffineMap.lineMap a b tr) u = AffineMap.lineMap a b t := by
      simp only [AffineMap.lineMap_apply_module, t]
      module
    rw [hline]
    constructor
    · apply hfront
      rw [openSegment_eq_image_lineMap]
      refine ⟨t, ?_, rfl⟩
      constructor
      · exact lt_of_le_of_lt htl0 ht_between.1
      · exact lt_of_lt_of_le ht_between.2 htr1
    · intro htV
      by_cases htt : t ≤ tp
      · exact (not_lt_of_ge (htlmax t ⟨htV, htt⟩)) ht_between.1
      · exact (not_lt_of_ge (htrmin t ⟨htV, le_of_not_ge htt⟩)) ht_between.2
  · rw [segment_eq_image_lineMap]
    refine ⟨tl, ?_, rfl⟩
    exact ⟨htl0, hlt.le.trans htp.2.le⟩
  · rw [segment_eq_image_lineMap]
    refine ⟨tr, ?_, rfl⟩
    exact ⟨htp.1.le.trans hgt.le, htr1⟩

private theorem one_endpoint_between_parameters
    {ta tb tp tv u : ℝ} (hu : u ∈ Set.Ioo 0 1)
    (hp : tp = (1 - u) * ta + u * tb) (hab : ta ≠ tb)
    (hv : ¬∃ q ∈ Set.Ioo 0 1, tv = (1 - q) * ta + q * tb) :
    (∃ q ∈ Set.Icc 0 1, ta = (1 - q) * tv + q * tp) ∨
      ∃ q ∈ Set.Icc 0 1, tb = (1 - q) * tv + q * tp := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · have hta : ta < tp := by rw [hp]; nlinarith [hu.1, hu.2]
    have htb : tp < tb := by rw [hp]; nlinarith [hu.1, hu.2]
    have hout : tv ≤ ta ∨ tb ≤ tv := by
      by_contra h
      push Not at h
      apply hv
      refine ⟨(tv - ta) / (tb - ta), ?_, ?_⟩
      · constructor
        · exact div_pos (sub_pos.mpr h.1) (sub_pos.mpr hlt)
        · rw [div_lt_one (sub_pos.mpr hlt)]
          linarith
      · field_simp [ne_of_gt (sub_pos.mpr hlt)]
        ring
    rcases hout with hleft | hright
    · left
      refine ⟨(ta - tv) / (tp - tv), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr (hleft.trans hta.le))
        · rw [div_le_one (sub_pos.mpr (lt_of_le_of_lt hleft hta))]
          linarith
      · field_simp [ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hleft hta))]
        ring
    · right
      refine ⟨(tb - tv) / (tp - tv), ?_, ?_⟩
      · have hden : tp - tv < 0 := sub_neg.mpr (htb.trans_le hright)
        constructor
        · exact div_nonneg_iff.2 (Or.inr ⟨sub_nonpos.mpr hright, hden.le⟩)
        · exact (div_le_one_of_neg hden).2 (by linarith)
      · field_simp [ne_of_lt (sub_neg.mpr (htb.trans_le hright))]
        ring
  · have htb : tb < tp := by rw [hp]; nlinarith [hu.1, hu.2]
    have hta : tp < ta := by rw [hp]; nlinarith [hu.1, hu.2]
    have hout : tv ≤ tb ∨ ta ≤ tv := by
      by_contra h
      push Not at h
      apply hv
      refine ⟨(tv - ta) / (tb - ta), ?_, ?_⟩
      · have hden : tb - ta < 0 := sub_neg.mpr hgt
        constructor
        · exact div_pos_of_neg_of_neg (sub_neg.mpr h.2) hden
        · exact (div_lt_one_of_neg hden).2 (by linarith)
      · field_simp [ne_of_lt (sub_neg.mpr hgt)]
        ring
    rcases hout with hleft | hright
    · right
      refine ⟨(tb - tv) / (tp - tv), ?_, ?_⟩
      · constructor
        · exact div_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr (hleft.trans htb.le))
        · rw [div_le_one (sub_pos.mpr (lt_of_le_of_lt hleft htb))]
          linarith
      · field_simp [ne_of_gt (sub_pos.mpr (lt_of_le_of_lt hleft htb))]
        ring
    · left
      refine ⟨(ta - tv) / (tp - tv), ?_, ?_⟩
      · have hden : tp - tv < 0 := sub_neg.mpr (hta.trans_le hright)
        constructor
        · exact div_nonneg_iff.2 (Or.inr ⟨sub_nonpos.mpr hright, hden.le⟩)
        · exact (div_le_one_of_neg hden).2 (by linarith)
      · field_simp [ne_of_lt (sub_neg.mpr (hta.trans_le hright))]
        ring

private theorem trimmed_endpoint_eq_isolatedVertex :
    ∀ {D : Set Tiling.Plane} {a b p a' b' v : Tiling.Plane} {rho : ℝ},
      0 < rho → a ≠ b → p ∈ openSegment ℝ a b →
      a' ∈ Tiling.vertexSet D → b' ∈ Tiling.vertexSet D →
      p ∈ openSegment ℝ a' b' →
      openSegment ℝ a' b' ⊆ frontier D \ Tiling.vertexSet D →
      a' ∈ segment ℝ a b → b' ∈ segment ℝ a b →
      v ∈ Tiling.vertexSet D → v ∈ segment ℝ a b →
      p ∈ Metric.ball v rho → openSegment ℝ v p ⊆ frontier D →
      Tiling.vertexSet D ∩ Metric.ball v rho ⊆ {v} →
      a' = v ∨ b' = v := by
  intro D a b p a' b' v rho hr hab hp ha' hb' hp' hfree ha'ab hb'ab hv hvab
    hpball _hvpfront hisolate
  rw [openSegment_eq_image_lineMap] at hp hp'
  rw [segment_eq_image_lineMap] at ha'ab hb'ab hvab
  obtain ⟨tp, htp, hpt⟩ := hp
  obtain ⟨ta, hta, hata⟩ := ha'ab
  obtain ⟨tb, htb, hatb⟩ := hb'ab
  obtain ⟨tv, htv, hatv⟩ := hvab
  obtain ⟨u, hu, hup⟩ := hp'
  have hinj := lineMap_injective hab
  have hparam : tp = (1 - u) * ta + u * tb := by
    apply hinj
    rw [hpt, ← hup, ← hata, ← hatb]
    simp only [AffineMap.lineMap_apply_module]
    module
  have hatbne : ta ≠ tb := by
    intro h
    have hpopen : p ∈ openSegment ℝ a' b' := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨u, hu, hup⟩
    have hpvertex : p ∈ Tiling.vertexSet D := by
      have hpa : p = a' := by
        rw [← hup, ← hata, ← hatb, h]
        simp
      exact hpa.symm ▸ ha'
    exact (hfree hpopen).2 hpvertex
  have hvnot : ¬∃ q ∈ Set.Ioo 0 1, tv = (1 - q) * ta + q * tb := by
    rintro ⟨q, hq, hqv⟩
    have hvopen : v ∈ openSegment ℝ a' b' := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨q, hq, ?_⟩
      rw [← hata, ← hatb, ← hatv]
      simp only [AffineMap.lineMap_apply_module]
      rw [hqv]
      module
    exact (hfree hvopen).2 hv
  rcases one_endpoint_between_parameters hu hparam hatbne hvnot with hleft | hright
  · left
    obtain ⟨q, hq, hqeq⟩ := hleft
    have ha'vp : a' ∈ segment ℝ v p := by
      rw [segment_eq_image_lineMap]
      refine ⟨q, hq, ?_⟩
      rw [← hata, ← hatv, ← hpt]
      simp only [AffineMap.lineMap_apply_module]
      rw [hqeq]
      module
    have ha'ball := (convex_ball v rho).segment_subset
      (Metric.mem_ball_self hr) hpball ha'vp
    simpa only [mem_singleton_iff] using hisolate ⟨ha', ha'ball⟩
  · right
    obtain ⟨q, hq, hqeq⟩ := hright
    have hb'vp : b' ∈ segment ℝ v p := by
      rw [segment_eq_image_lineMap]
      refine ⟨q, hq, ?_⟩
      rw [← hatb, ← hatv, ← hpt]
      simp only [AffineMap.lineMap_apply_module]
      rw [hqeq]
      module
    have hb'ball := (convex_ball v rho).segment_subset
      (Metric.mem_ball_self hr) hpball hb'vp
    simpa only [mem_singleton_iff] using hisolate ⟨hb', hb'ball⟩

private theorem coordinateSwap_image_eq_preimage_local (s : Set Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap '' s =
      Tiling.AxisParallel.coordinateSwap ⁻¹' s := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨Tiling.AxisParallel.coordinateSwap z, hz,
      Tiling.AxisParallel.coordinateSwap_apply_apply z⟩

private theorem coordinateSwap_frontier_image :
    ∀ D : Set Tiling.Plane,
      frontier (Tiling.AxisParallel.coordinateSwap '' D) =
        Tiling.AxisParallel.coordinateSwap '' frontier D := by
  intro D
  rw [coordinateSwap_image_eq_preimage_local,
    coordinateSwap_image_eq_preimage_local]
  exact Tiling.AxisParallel.coordinateSwap.toHomeomorph.isOpenMap
    |>.preimage_frontier_eq_frontier_preimage
      Tiling.AxisParallel.coordinateSwap.continuous D |>.symm

private theorem coordinateSwap_openSegment :
    ∀ (a b : Tiling.Plane),
      Tiling.AxisParallel.coordinateSwap '' openSegment ℝ a b =
        openSegment ℝ (Tiling.AxisParallel.coordinateSwap a)
          (Tiling.AxisParallel.coordinateSwap b) := by
  intro a b
  exact image_openSegment ℝ
    Tiling.AxisParallel.coordinateSwap.toLinearMap.toAffineMap a b

private def coordinateSwapLIE_local : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := Tiling.AxisParallel.coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem coordinateSwap_image_triangle_local {s : Set Tiling.Plane}
    (hs : Tiling.IsTriangle s) :
    Tiling.IsTriangle (Tiling.AxisParallel.coordinateSwap '' s) := by
  obtain ⟨a, b, c, hnondeg, rfl⟩ := hs
  refine ⟨Tiling.AxisParallel.coordinateSwap a, Tiling.AxisParallel.coordinateSwap b,
    Tiling.AxisParallel.coordinateSwap c, ?_, ?_⟩
  · have harea : Tiling.twiceSignedArea (Tiling.AxisParallel.coordinateSwap a)
        (Tiling.AxisParallel.coordinateSwap b) (Tiling.AxisParallel.coordinateSwap c) =
        -Tiling.twiceSignedArea a b c := by
      simp [Tiling.twiceSignedArea]
    rw [harea]
    exact neg_ne_zero.mpr hnondeg
  · change Tiling.AxisParallel.coordinateSwap.toLinearMap '' convexHull ℝ {a, b, c} =
      convexHull ℝ {Tiling.AxisParallel.coordinateSwap a,
        Tiling.AxisParallel.coordinateSwap b, Tiling.AxisParallel.coordinateSwap c}
    rw [Tiling.AxisParallel.coordinateSwap.toLinearMap.image_convexHull]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop

private noncomputable def coordinateSwapTriangulation_local {s : Set Tiling.Plane}
    (T : Tiling.Triangulation s) :
    Tiling.Triangulation (Tiling.AxisParallel.coordinateSwap '' s) where
  pieces := T.pieces.image (Tiling.AxisParallel.coordinateSwap '' ·)
  isTriangle := by
    intro r hr
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hr
    exact coordinateSwap_image_triangle_local (T.isTriangle q hq)
  pairwiseAEDisjoint := by
    rw [Finset.coe_image]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨q, hq, rfl⟩ hne
    have hrq : r ≠ q := by
      intro heq
      exact hne (by simp [heq])
    have hd := T.pairwiseAEDisjoint hr hq hrq
    change MeasureTheory.AEDisjoint MeasureTheory.volume
      (Tiling.AxisParallel.coordinateSwap '' r) (Tiling.AxisParallel.coordinateSwap '' q)
    rw [coordinateSwap_image_eq_preimage_local, coordinateSwap_image_eq_preimage_local]
    exact hd.preimage coordinateSwapLIE_local.measurePreserving.quasiMeasurePreserving
  sUnion_eq := by
    calc
      ⋃₀ (T.pieces.image (Tiling.AxisParallel.coordinateSwap '' ·) :
          Set (Set Tiling.Plane)) =
          Tiling.AxisParallel.coordinateSwap '' ⋃₀ (T.pieces : Set (Set Tiling.Plane)) := by
        ext z
        constructor
        · rintro ⟨u, hu, hzu⟩
          obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hu
          obtain ⟨w, hw, rfl⟩ := hzu
          exact ⟨w, ⟨q, hq, hw⟩, rfl⟩
        · rintro ⟨w, ⟨q, hq, hw⟩, rfl⟩
          exact ⟨Tiling.AxisParallel.coordinateSwap '' q,
            Finset.mem_image.mpr ⟨q, hq, rfl⟩, ⟨w, hw, rfl⟩⟩
      _ = Tiling.AxisParallel.coordinateSwap '' s :=
        congrArg (Tiling.AxisParallel.coordinateSwap '' ·) T.sUnion_eq

theorem coordinateSwap_image_image (s : Set Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap ''
      (Tiling.AxisParallel.coordinateSwap '' s) = s := by
  ext z
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨Tiling.AxisParallel.coordinateSwap z,
      ⟨z, hz, rfl⟩, Tiling.AxisParallel.coordinateSwap_apply_apply z⟩

private theorem coordinateSwap_extremePoints_iff
    (s : Set Tiling.Plane) (x : Tiling.Plane) :
    x ∈ s.extremePoints ℝ ↔
      Tiling.AxisParallel.coordinateSwap x ∈
        (Tiling.AxisParallel.coordinateSwap '' s).extremePoints ℝ := by
  have hfwd : ∀ (t : Set Tiling.Plane) (z : Tiling.Plane),
      z ∈ t.extremePoints ℝ →
        Tiling.AxisParallel.coordinateSwap z ∈
          (Tiling.AxisParallel.coordinateSwap '' t).extremePoints ℝ := by
    intro t z hz
    rw [← image_extremePoints Tiling.AxisParallel.coordinateSwap t]
    exact ⟨z, hz, rfl⟩
  constructor
  · exact hfwd s x
  · intro hx
    have h := hfwd (Tiling.AxisParallel.coordinateSwap '' s)
      (Tiling.AxisParallel.coordinateSwap x) hx
    rw [coordinateSwap_image_image] at h
    simpa using h

theorem coordinateSwap_vertexSet :
    ∀ D : Set Tiling.Plane,
      Tiling.vertexSet (Tiling.AxisParallel.coordinateSwap '' D) =
        Tiling.AxisParallel.coordinateSwap '' Tiling.vertexSet D := by
  intro D
  ext y
  constructor
  · intro hy
    refine ⟨Tiling.AxisParallel.coordinateSwap y, ?_,
      Tiling.AxisParallel.coordinateSwap_apply_apply y⟩
    intro T
    let U0 := coordinateSwapTriangulation_local T
    obtain ⟨u, hu, hyu⟩ := hy U0
    obtain ⟨t, ht, hut⟩ := Finset.mem_image.mp hu
    subst u
    refine ⟨t, ht, ?_⟩
    exact (coordinateSwap_extremePoints_iff t
      (Tiling.AxisParallel.coordinateSwap y)).2 (by simpa using hyu)
  · rintro ⟨x, hx, rfl⟩
    intro T
    let U0 := coordinateSwapTriangulation_local T
    have hx' : x ∈ Tiling.vertexSet (Tiling.AxisParallel.coordinateSwap ''
        (Tiling.AxisParallel.coordinateSwap '' D)) := by
      rw [coordinateSwap_image_image]
      exact hx
    obtain ⟨u, hu, hxu⟩ := hx' U0
    obtain ⟨t, ht, hut⟩ := Finset.mem_image.mp hu
    subst u
    refine ⟨t, ht, ?_⟩
    exact (coordinateSwap_extremePoints_iff t
      (Tiling.AxisParallel.coordinateSwap x)).2 (by simpa using hxu)

private theorem tendsto_side_plus {d z : Plane} :
    Tendsto (fun n : ℕ => z + (n : ℝ)⁻¹ • (d * Complex.I)) atTop (𝓝 z) := by
  have ht : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  simpa using tendsto_const_nhds.add (Tendsto.smul_const ht (d * Complex.I))

private theorem line_mem_closure_ball_inter_positiveSide
    {a d z c : Plane} {r : ℝ} (hd : d ≠ 0) (hzball : z ∈ Metric.ball c r)
    (hzline : z ∈ affineLine a d) :
    z ∈ closure (Metric.ball c r ∩ positiveSide a d) := by
  let f : ℕ → Plane := fun n => z + (n : ℝ)⁻¹ • (d * Complex.I)
  have hf : Tendsto f atTop (𝓝 z) := tendsto_side_plus
  apply mem_closure_of_tendsto hf
  filter_upwards [hf.eventually (Metric.isOpen_ball.mem_nhds hzball),
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnball hn
  refine ⟨hnball, mem_positiveSide.2 ?_⟩
  have hnpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  have hz0 := mem_affineLine.1 hzline
  simp only [f, signedSide, planarCross] at hz0 ⊢
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
    Complex.mul_im, add_zero, Complex.add_re, Complex.smul_re,
    Complex.add_im, Complex.smul_im, smul_eq_mul]
  have hdpos := Complex.normSq_pos.2 hd
  simp only [Complex.normSq_apply] at hdpos
  nlinarith

private theorem line_mem_closure_ball_inter_negativeSide
    {a d z c : Plane} {r : ℝ} (hd : d ≠ 0) (hzball : z ∈ Metric.ball c r)
    (hzline : z ∈ affineLine a d) :
    z ∈ closure (Metric.ball c r ∩ negativeSide a d) := by
  let f : ℕ → Plane := fun n => z - (n : ℝ)⁻¹ • (d * Complex.I)
  have ht : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hf : Tendsto f atTop (𝓝 z) := by
    change Tendsto (fun n : ℕ => z - (n : ℝ)⁻¹ • (d * Complex.I)) atTop (𝓝 z)
    have hc : Tendsto (fun _ : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
    convert hc.sub (Tendsto.smul_const ht (d * Complex.I)) using 1
    all_goals simp
  apply mem_closure_of_tendsto hf
  filter_upwards [hf.eventually (Metric.isOpen_ball.mem_nhds hzball),
    eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hnball hn
  refine ⟨hnball, mem_negativeSide.2 ?_⟩
  have hnpos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hn)
  have hz0 := mem_affineLine.1 hzline
  simp only [f, signedSide, planarCross] at hz0 ⊢
  simp only [Complex.mul_re, Complex.I_re, mul_zero, Complex.I_im, mul_one,
    Complex.mul_im, add_zero, Complex.sub_re, Complex.smul_re,
    Complex.sub_im, Complex.smul_im, smul_eq_mul]
  have hdpos := Complex.normSq_pos.2 hd
  simp only [Complex.normSq_apply] at hdpos
  nlinarith

private theorem regularClosed_frontier_eventuallyEq_affineLine_of_subset :
    ∀ {D : Set Plane} {v d : Plane},
      closure (interior D) = D → v ∈ frontier D → d ≠ 0 →
      (∃ r > 0, ∀ z ∈ Metric.ball v r,
        z ∈ frontier D → z ∈ affineLine v d) →
      ∀ᶠ z in nhds v, (z ∈ frontier D ↔ z ∈ affineLine v d) := by
  intro D v d hregular hv hd hlocal
  obtain ⟨r, hr, hsub⟩ := hlocal
  have hposDisjoint : Disjoint (Metric.ball v r ∩ positiveSide v d) (frontier D) := by
    refine Set.disjoint_left.2 fun z hz hzf ↦ ?_
    exact (ne_of_gt (mem_positiveSide.1 hz.2)) (mem_affineLine.1 (hsub z hz.1 hzf))
  have hnegDisjoint : Disjoint (Metric.ball v r ∩ negativeSide v d) (frontier D) := by
    refine Set.disjoint_left.2 fun z hz hzf ↦ ?_
    exact (ne_of_lt (mem_negativeSide.1 hz.2)) (mem_affineLine.1 (hsub z hz.1 hzf))
  have hpos := IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    (isPreconnected_ball_inter_positiveSide v d r) hposDisjoint
  have hneg := IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    (isPreconnected_ball_inter_negativeSide v d r) hnegDisjoint
  have hclosed : IsClosed D := by rw [← hregular]; exact isClosed_closure
  have hvD : v ∈ D := hclosed.frontier_subset hv
  have hvcl : v ∈ closure (interior D) := hregular.symm ▸ hvD
  have hr2 : 0 < r / 2 := half_pos hr
  rcases hpos with hposIn | hposOut <;> rcases hneg with hnegIn | hnegOut
  · exfalso
    have hballD : Metric.ball v (r / 2) ⊆ D := by
      intro z hz
      have hzr : z ∈ Metric.ball v r := Metric.ball_subset_ball (half_lt_self hr).le hz
      rcases lt_trichotomy (signedSide v d z) 0 with hn | he | hp
      · exact interior_subset (hnegIn ⟨hzr, mem_negativeSide.2 hn⟩)
      · have hzline : z ∈ affineLine v d := mem_affineLine.2 he
        rw [← hregular]
        exact closure_mono hposIn
          (line_mem_closure_ball_inter_positiveSide hd hzr hzline)
      · exact interior_subset (hposIn ⟨hzr, mem_positiveSide.2 hp⟩)
    have hvint : v ∈ interior D := interior_maximal hballD Metric.isOpen_ball
      (Metric.mem_ball_self hr2)
    exact Set.disjoint_left.1 disjoint_interior_frontier hvint hv
  · filter_upwards [Metric.ball_mem_nhds v hr2] with z hz
    have hzr : z ∈ Metric.ball v r := Metric.ball_subset_ball (half_lt_self hr).le hz
    constructor
    · exact hsub z hzr
    · intro hzline
      rw [frontier]
      have hzD : z ∈ D := by
        rw [← hregular]
        exact closure_mono hposIn
          (line_mem_closure_ball_inter_positiveSide hd hzr hzline)
      refine ⟨subset_closure hzD, ?_⟩
      have hzclc : z ∈ closure Dᶜ := closure_mono interior_subset
        (closure_mono hnegOut
          (line_mem_closure_ball_inter_negativeSide hd hzr hzline))
      rw [closure_compl] at hzclc
      exact hzclc
  · filter_upwards [Metric.ball_mem_nhds v hr2] with z hz
    have hzr : z ∈ Metric.ball v r := Metric.ball_subset_ball (half_lt_self hr).le hz
    constructor
    · exact hsub z hzr
    · intro hzline
      rw [frontier]
      have hzD : z ∈ D := by
        rw [← hregular]
        exact closure_mono hnegIn
          (line_mem_closure_ball_inter_negativeSide hd hzr hzline)
      refine ⟨subset_closure hzD, ?_⟩
      have hzclc : z ∈ closure Dᶜ := closure_mono interior_subset
        (closure_mono hposOut
          (line_mem_closure_ball_inter_positiveSide hd hzr hzline))
      rw [closure_compl] at hzclc
      exact hzclc
  · exfalso
    obtain ⟨z, hzint, hzdist⟩ := (Metric.mem_closure_iff.1 hvcl) (r / 2) hr2
    have hzhalf : z ∈ Metric.ball v (r / 2) := by simpa [dist_comm] using hzdist
    have hzr : z ∈ Metric.ball v r := Metric.ball_subset_ball (half_lt_self hr).le hzhalf
    rcases lt_trichotomy (signedSide v d z) 0 with hn | he | hp
    · exact (interior_subset (hnegOut ⟨hzr, mem_negativeSide.2 hn⟩))
        (interior_subset hzint)
    · have hzline : z ∈ affineLine v d := mem_affineLine.2 he
      have hzclc : z ∈ closure Dᶜ := closure_mono interior_subset
        (closure_mono hposOut
          (line_mem_closure_ball_inter_positiveSide hd hzr hzline))
      rw [closure_compl] at hzclc
      exact hzclc hzint
    · exact (interior_subset (hposOut ⟨hzr, mem_positiveSide.2 hp⟩))
        (interior_subset hzint)

private theorem regularClosed_boundaryLocallyStraight_of_frontier_locally_subset_affineLine :
    ∀ {D : Set Plane} {v d : Plane},
      closure (interior D) = D → v ∈ frontier D → d ≠ 0 →
      (∃ r > 0, ∀ z ∈ Metric.ball v r,
        z ∈ frontier D → z ∈ affineLine v d) →
      BoundaryLocallyStraightAt D v := by
  intro D v d hregular hv hd hlocal
  have heq := regularClosed_frontier_eventuallyEq_affineLine_of_subset
    hregular hv hd hlocal
  refine ⟨AffineSubspace.mk' v (Submodule.span ℝ {d}), by simp, ?_, ?_⟩
  · rw [AffineSubspace.direction_mk']
    exact finrank_span_singleton hd
  · filter_upwards [heq] with z hz
    rw [hz]
    have hzL : z ∈ (AffineSubspace.mk' v (Submodule.span ℝ {d}) : Set Plane) ↔
        z ∈ affineLine v d := by
      rw [mem_affineLine_iff_exists_smul hd]
      simp only [AffineSubspace.mem_mk', Submodule.mem_span_singleton, SetLike.mem_coe]
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t, ?_⟩
        simpa only [vsub_eq_sub, add_comm] using (eq_add_of_sub_eq ht.symm)
      · rintro ⟨t, rfl⟩
        refine ⟨t, ?_⟩
        simp only [vsub_eq_sub]
        abel
    exact hzL.symm

private def axisLineThrough (axis : Axis) (v : Plane) : Set Plane :=
  {z | axis.transverseCoord z = axis.transverseCoord v}

private def axisVector : Axis → Plane
  | .horizontal => 1
  | .vertical => Complex.I

private def transverseAxisVector : Axis → Plane
  | .horizontal => Complex.I
  | .vertical => 1

private theorem axisVector_ne_zero (axis : Axis) : axisVector axis ≠ 0 := by
  cases axis <;> simp [axisVector]

private theorem transverseAxisVector_ne_zero (axis : Axis) :
    transverseAxisVector axis ≠ 0 := by
  cases axis <;> simp [transverseAxisVector]

private theorem mem_affineLine_axisVector_iff (axis : Axis) (v z : Plane) :
    z ∈ affineLine v (axisVector axis) ↔ z ∈ axisLineThrough axis v := by
  cases axis
  · change signedSide v 1 z = 0 ↔ z.im = v.im
    simp only [signedSide, planarCross, Complex.one_re, Complex.one_im, zero_mul,
      sub_zero, one_mul]
    constructor <;> intro h <;> linarith
  · change signedSide v Complex.I z = 0 ↔ z.re = v.re
    simp only [signedSide, planarCross, Complex.I_re, zero_mul, Complex.I_im,
      one_mul, zero_sub]
    constructor <;> intro h <;> linarith

private theorem mem_affineLine_transverseAxisVector_iff (axis : Axis) (v z : Plane) :
    z ∈ affineLine v (transverseAxisVector axis) ↔ axis.coord z = axis.coord v := by
  cases axis
  · change signedSide v Complex.I z = 0 ↔ z.re = v.re
    simp only [signedSide, planarCross, Complex.I_re, zero_mul, Complex.I_im,
      one_mul, zero_sub]
    constructor <;> intro h <;> linarith
  · change signedSide v 1 z = 0 ↔ z.im = v.im
    simp only [signedSide, planarCross, Complex.one_re, Complex.one_im, zero_mul,
      sub_zero, one_mul]
    constructor <;> intro h <;> linarith

private theorem axis_eq_of_coord_eq_of_transverseCoord_eq (axis : Axis) {x y : Plane}
    (hcoord : axis.coord x = axis.coord y)
    (htrans : axis.transverseCoord x = axis.transverseCoord y) : x = y := by
  cases axis
  · exact Complex.ext hcoord htrans
  · exact Complex.ext htrans hcoord

private theorem exists_axisGermPoint_near_nonStraight :
    ∀ {D : Set Plane} {v : Plane},
      closure (interior D) = D → v ∈ frontier D →
      ¬BoundaryLocallyStraightAt D v →
      (∃ r > 0, ∀ z ∈ Metric.ball v r,
        z ∈ frontier D → z.re = v.re ∨ z.im = v.im) →
      ∀ (axis : Axis) (F : Finset Plane) (rho : ℝ), 0 < rho →
        ∃ p ∈ Metric.ball v rho,
          p ∈ frontier D ∧ p ∉ F ∧
          axis.coord p ≠ axis.coord v ∧
          axis.transverseCoord p = axis.transverseCoord v ∧
          openSegment ℝ v p ⊆ frontier D ∧
          ∀ᶠ z in nhds p, (z ∈ frontier D ↔ z ∈ axisLineThrough axis p) := by
  intro D v hregular hv hnotstraight hcross axis F rho hrho
  classical
  obtain ⟨r, hr, hcross⟩ := hcross
  have hUopen : IsOpen (Metric.ball v (min r rho) ∩ ((↑(F.erase v) : Set Plane))ᶜ) :=
    Metric.isOpen_ball.inter (F.erase v).finite_toSet.isClosed.isOpen_compl
  have hvU : v ∈ Metric.ball v (min r rho) ∩ ((↑(F.erase v) : Set Plane))ᶜ := by
    refine ⟨Metric.mem_ball_self (lt_min hr hrho), ?_⟩
    simp
  obtain ⟨delta, hdelta, hdeltaU⟩ := Metric.isOpen_iff.mp hUopen v hvU
  have hex : ∃ p ∈ Metric.ball v delta,
      p ∈ frontier D ∧ axis.transverseCoord p = axis.transverseCoord v ∧
        axis.coord p ≠ axis.coord v := by
    by_contra hn
    have hall : ∀ z ∈ Metric.ball v delta, z ∈ frontier D →
        axis.transverseCoord z = axis.transverseCoord v →
        axis.coord z = axis.coord v := by
      intro z hzball hzfront hztrans
      by_contra hzcoord
      exact hn ⟨z, hzball, hzfront, hztrans, hzcoord⟩
    apply hnotstraight
    apply regularClosed_boundaryLocallyStraight_of_frontier_locally_subset_affineLine
      hregular hv (transverseAxisVector_ne_zero axis)
    refine ⟨delta, hdelta, ?_⟩
    intro z hzball hzfront
    rw [mem_affineLine_transverseAxisVector_iff]
    have hzsmall := hdeltaU hzball |>.1
    have hzCross := hcross z (Metric.ball_subset_ball (min_le_left _ _) hzsmall) hzfront
    cases axis with
    | horizontal =>
        simp only [Axis.coord, Axis.transverseCoord] at hall ⊢
        rcases hzCross with hzre | hzim
        · exact hzre
        · have hzre' := hall z hzball hzfront hzim
          exact hzre'
    | vertical =>
        simp only [Axis.coord, Axis.transverseCoord] at hall ⊢
        rcases hzCross with hzre | hzim
        · exact hall z hzball hzfront hzre
        · exact hzim
  obtain ⟨p, hpdelta, hpfront, hptrans, hpcoord⟩ := hex
  have hpU := hdeltaU hpdelta
  have hprho : p ∈ Metric.ball v rho :=
    Metric.ball_subset_ball (min_le_right _ _) hpU.1
  have hpnotv : p ≠ v := fun h ↦ hpcoord (h ▸ rfl)
  have hpnotF : p ∉ F := by
    intro hpF
    have : p ∈ F.erase v := Finset.mem_erase.mpr ⟨hpnotv, hpF⟩
    exact hpU.2 this
  have hpCrossBall : p ∈ Metric.ball v r :=
    Metric.ball_subset_ball (min_le_left _ _) hpU.1
  have hnearOpen : IsOpen (Metric.ball v r ∩
      {z : Plane | axis.coord z ≠ axis.coord v}) := by
    apply Metric.isOpen_ball.inter
    cases axis <;> simp only [Axis.coord] <;>
      first
      | exact (isClosed_eq Complex.continuous_re continuous_const).isOpen_compl
      | exact (isClosed_eq Complex.continuous_im continuous_const).isOpen_compl
  have hpNear : p ∈ Metric.ball v r ∩ {z : Plane | axis.coord z ≠ axis.coord v} :=
    ⟨hpCrossBall, hpcoord⟩
  obtain ⟨eps, heps, hepsSub⟩ := Metric.isOpen_iff.mp hnearOpen p hpNear
  have hpLineSubset : ∀ z ∈ Metric.ball p eps, z ∈ frontier D →
      z ∈ affineLine p (axisVector axis) := by
    intro z hzball hzfront
    rw [mem_affineLine_axisVector_iff]
    have hzNear := hepsSub hzball
    have hzCross := hcross z hzNear.1 hzfront
    cases axis with
    | horizontal =>
        simp only [Axis.coord, Axis.transverseCoord, axisLineThrough] at hptrans hzNear ⊢
        rcases hzCross with hzre | hzim
        · exact (hzNear.2 hzre).elim
        · exact hzim.trans hptrans.symm
    | vertical =>
        simp only [Axis.coord, Axis.transverseCoord, axisLineThrough] at hptrans hzNear ⊢
        rcases hzCross with hzre | hzim
        · exact hzre.trans hptrans.symm
        · exact (hzNear.2 hzim).elim
  have hpGermLine := regularClosed_frontier_eventuallyEq_affineLine_of_subset
    hregular hpfront (axisVector_ne_zero axis) ⟨eps, heps, hpLineSubset⟩
  have hpGerm : ∀ᶠ z in nhds p,
      (z ∈ frontier D ↔ z ∈ axisLineThrough axis p) := by
    filter_upwards [hpGermLine] with z hz
    exact hz.trans (mem_affineLine_axisVector_iff axis p z)
  let C := Set.Ioc (0 : ℝ) 1
  let phi : C → Plane := fun t ↦ AffineMap.lineMap v p t.1
  let A : Set C := {t | phi t ∈ frontier D}
  have hphi : Continuous phi := by
    apply Continuous.lineMap continuous_const continuous_const
    exact continuous_subtype_val
  have hAclosed : IsClosed A := isClosed_frontier.preimage hphi
  have hAopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have htpos : 0 < t.1 := t.2.1
    have htcoord : axis.coord (phi t) ≠ axis.coord v := by
      intro heq
      have hformula : axis.coord (phi t) =
          (1 - t.1) * axis.coord v + t.1 * axis.coord p := by
        cases axis <;> simp [phi, AffineMap.lineMap_apply_module, Axis.coord]
      rw [hformula] at heq
      apply hpcoord
      cases axis <;> simp only [Axis.coord] at * <;> nlinarith
    have htball : phi t ∈ Metric.ball v r := by
      apply (convex_ball v r).segment_subset (Metric.mem_ball_self hr) hpCrossBall
      rw [segment_eq_image_lineMap]
      exact ⟨t.1, ⟨t.2.1.le, t.2.2⟩, rfl⟩
    have htNear : phi t ∈ Metric.ball v r ∩ {z : Plane | axis.coord z ≠ axis.coord v} :=
      ⟨htball, htcoord⟩
    obtain ⟨eta, heta, hetaSub⟩ := Metric.isOpen_iff.mp hnearOpen (phi t) htNear
    have htSubset : ∀ z ∈ Metric.ball (phi t) eta, z ∈ frontier D →
        z ∈ affineLine (phi t) (axisVector axis) := by
      intro z hzball hzfront
      rw [mem_affineLine_axisVector_iff]
      have hzNear := hetaSub hzball
      have hzCross := hcross z hzNear.1 hzfront
      cases axis with
      | horizontal =>
          simp only [Axis.coord, Axis.transverseCoord, axisLineThrough] at hptrans hzNear ⊢
          have httrans : (phi t).im = v.im := by
            simp [phi, AffineMap.lineMap_apply_module, hptrans]
            ring
          rcases hzCross with hzre | hzim
          · exact False.elim (hzNear.2 (by simpa [Axis.coord] using hzre))
          · exact hzim.trans httrans.symm
      | vertical =>
          simp only [Axis.coord, Axis.transverseCoord, axisLineThrough] at hptrans hzNear ⊢
          have httrans : (phi t).re = v.re := by
            simp [phi, AffineMap.lineMap_apply_module, hptrans]
            ring
          rcases hzCross with hzre | hzim
          · exact hzre.trans httrans.symm
          · exact False.elim (hzNear.2 (by simpa [Axis.coord] using hzim))
    have htGerm := regularClosed_frontier_eventuallyEq_affineLine_of_subset
      hregular ht (axisVector_ne_zero axis) ⟨eta, heta, htSubset⟩
    have htPre := hphi.continuousAt.preimage_mem_nhds htGerm
    filter_upwards [htPre] with u hu
    change phi u ∈ frontier D
    apply hu.2
    apply (mem_affineLine_axisVector_iff axis (phi t) (phi u)).2
    cases axis
    · change (phi u).im = (phi t).im
      change p.im = v.im at hptrans
      dsimp only [phi]
      simp only [AffineMap.lineMap_apply_module, Complex.add_im,
        Complex.smul_im, smul_eq_mul]
      rw [hptrans]
      ring
    · change (phi u).re = (phi t).re
      change p.re = v.re at hptrans
      dsimp only [phi]
      simp only [AffineMap.lineMap_apply_module, Complex.add_re,
        Complex.smul_re, smul_eq_mul]
      rw [hptrans]
      ring
  let _ : PreconnectedSpace C := isPreconnected_iff_preconnectedSpace.mp (by
    simpa only [C] using (isPreconnected_Ioc : IsPreconnected (Set.Ioc (0 : ℝ) 1)))
  have hpA : (⟨1, right_mem_Ioc.mpr zero_lt_one⟩ : C) ∈ A := by
    simpa [A, phi] using hpfront
  have hAuniv : A = Set.univ := (show IsClopen A from ⟨hAclosed, hAopen⟩).eq_univ ⟨_, hpA⟩
  have hsegment : openSegment ℝ v p ⊆ frontier D := by
    intro z hz
    rw [openSegment_eq_image_lineMap] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have htA : (⟨t, ⟨ht.1, ht.2.le⟩⟩ : C) ∈ A := by rw [hAuniv]; trivial
    exact htA
  exact ⟨p, hprho, hpfront, hpnotF, hpcoord, hptrans, hsegment, hpGerm⟩

private theorem exists_intrinsic_axis_edge_of_germ (K : Region) (axis : Axis)
    {p : Plane} (hp : p ∈ frontier K.support)
    (hgerm : ∀ᶠ z in nhds p,
      (z ∈ frontier K.support ↔ z ∈ axisLineThrough axis p)) :
    ∃ a b : Plane,
      a ∈ vertexSet K.support ∧ b ∈ vertexSet K.support ∧ a ≠ b ∧
      axis.transverseCoord a = axis.transverseCoord b ∧
      p ∈ openSegment ℝ a b ∧ openSegment ℝ a b ⊆ frontier K.support := by
  cases axis with
  | vertical =>
      obtain ⟨a, b, ha, hb, hab, hcoord, hpab, habfront⟩ :=
        K.isPolygonal.exists_intrinsic_vertical_edge_of_germ hp (by
          filter_upwards [hgerm] with z hz
          simpa [axisLineThrough, Axis.transverseCoord] using hz)
      exact ⟨a, b, ha, hb, hab, hcoord, hpab, habfront⟩
  | horizontal =>
      let K' := Tiling.AxisParallel.Region.coordinateSwap K
      have hp' : Tiling.AxisParallel.coordinateSwap p ∈ frontier K'.support := by
        rw [show K'.support = Tiling.AxisParallel.coordinateSwap '' K.support by rfl,
          coordinateSwap_frontier_image]
        exact ⟨p, hp, rfl⟩
      have hswapTendsto : Tendsto Tiling.AxisParallel.coordinateSwap
          (nhds (Tiling.AxisParallel.coordinateSwap p)) (nhds p) := by
        rw [← Tiling.AxisParallel.coordinateSwap_apply_apply p]
        exact Tiling.AxisParallel.coordinateSwap.continuous.continuousAt
      have hgerm' : ∀ᶠ z in nhds (Tiling.AxisParallel.coordinateSwap p),
          (z ∈ frontier K'.support ↔ z.re =
            (Tiling.AxisParallel.coordinateSwap p).re) := by
        filter_upwards [hgerm.filter_mono hswapTendsto] with z hz
        rw [show K'.support = Tiling.AxisParallel.coordinateSwap '' K.support by rfl,
          coordinateSwap_frontier_image]
        constructor
        · rintro ⟨q, hq, rfl⟩
          have := hz.mp (by simpa using hq)
          simpa [axisLineThrough, Axis.transverseCoord] using this
        · intro hzre
          refine ⟨Tiling.AxisParallel.coordinateSwap z, ?_,
            Tiling.AxisParallel.coordinateSwap_apply_apply z⟩
          apply hz.mpr
          simpa [axisLineThrough, Axis.transverseCoord] using hzre
      obtain ⟨a, b, ha, hb, hab, habre, hpab, habfront⟩ :=
        K'.isPolygonal.exists_intrinsic_vertical_edge_of_germ hp' hgerm'
      refine ⟨Tiling.AxisParallel.coordinateSwap a,
        Tiling.AxisParallel.coordinateSwap b, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [show K'.support = Tiling.AxisParallel.coordinateSwap '' K.support by rfl,
          coordinateSwap_vertexSet] at ha
        obtain ⟨q, hq, hqa⟩ := ha
        simpa [← hqa] using hq
      · rw [show K'.support = Tiling.AxisParallel.coordinateSwap '' K.support by rfl,
          coordinateSwap_vertexSet] at hb
        obtain ⟨q, hq, hqb⟩ := hb
        simpa [← hqb] using hq
      · exact fun h ↦ hab (Tiling.AxisParallel.coordinateSwap.injective h)
      · simpa [Axis.transverseCoord] using habre
      · have himage : Tiling.AxisParallel.coordinateSwap
            (Tiling.AxisParallel.coordinateSwap p) ∈
            Tiling.AxisParallel.coordinateSwap '' openSegment ℝ a b :=
          ⟨Tiling.AxisParallel.coordinateSwap p, hpab, rfl⟩
        rw [coordinateSwap_openSegment] at himage
        simpa using himage
      · intro z hz
        have hzimage : Tiling.AxisParallel.coordinateSwap z ∈
            Tiling.AxisParallel.coordinateSwap ''
              openSegment ℝ (Tiling.AxisParallel.coordinateSwap a)
                (Tiling.AxisParallel.coordinateSwap b) := ⟨z, hz, rfl⟩
        rw [coordinateSwap_openSegment] at hzimage
        simp only [Tiling.AxisParallel.coordinateSwap_apply_apply] at hzimage
        have hzfront' := habfront hzimage
        rw [show K'.support = Tiling.AxisParallel.coordinateSwap '' K.support by rfl,
          coordinateSwap_frontier_image] at hzfront'
        obtain ⟨q, hq, hqz⟩ := hzfront'
        have hqz' : q = z := Tiling.AxisParallel.coordinateSwap.injective hqz
        simpa [hqz'] using hq

private theorem isolated_collinear_vertex_mem_segment
    {D : Set Plane} (axis : Axis) {v p a b : Plane} {rho : ℝ}
    (hrho : 0 < rho) (hab : a ≠ b)
    (habtrans : axis.transverseCoord a = axis.transverseCoord b)
    (hptrans : axis.transverseCoord p = axis.transverseCoord v)
    (hpab : p ∈ openSegment ℝ a b) (hpball : p ∈ Metric.ball v rho)
    (ha : a ∈ vertexSet D) (hb : b ∈ vertexSet D)
    (hisolate : vertexSet D ∩ Metric.ball v rho ⊆ {v}) :
    v ∈ segment ℝ a b := by
  have hcoordne : axis.coord a ≠ axis.coord b := by
    intro h
    exact hab (axis_eq_of_coord_eq_of_transverseCoord_eq axis h habtrans)
  rw [openSegment_eq_image_lineMap] at hpab
  obtain ⟨tp, htp, hp⟩ := hpab
  let tv := (axis.coord v - axis.coord a) / (axis.coord b - axis.coord a)
  have hvline : v = AffineMap.lineMap a b tv := by
    apply axis_eq_of_coord_eq_of_transverseCoord_eq axis
    · dsimp only [tv]
      cases axis
      · change a.re ≠ b.re at hcoordne
        simp only [Axis.coord, AffineMap.lineMap_apply_module, Complex.add_re,
          Complex.smul_re, smul_eq_mul]
        field_simp [sub_ne_zero.mpr hcoordne.symm]
        ring
      · change a.im ≠ b.im at hcoordne
        simp only [Axis.coord, AffineMap.lineMap_apply_module, Complex.add_im,
          Complex.smul_im, smul_eq_mul]
        field_simp [sub_ne_zero.mpr hcoordne.symm]
        ring
    · have hpLineTrans : axis.transverseCoord p = axis.transverseCoord a := by
        rw [← hp]
        cases axis
        · change a.im = b.im at habtrans
          simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
            Complex.add_im, Complex.smul_im, smul_eq_mul]
          rw [habtrans]
          ring
        · change a.re = b.re at habtrans
          simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
            Complex.add_re, Complex.smul_re, smul_eq_mul]
          rw [habtrans]
          ring
      have hvtrans : axis.transverseCoord v = axis.transverseCoord a :=
        hptrans.symm.trans hpLineTrans
      have hlineTrans : axis.transverseCoord (AffineMap.lineMap a b tv) =
          axis.transverseCoord a := by
        cases axis
        · change a.im = b.im at habtrans
          simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
            Complex.add_im, Complex.smul_im, smul_eq_mul]
          rw [habtrans]
          ring
        · change a.re = b.re at habtrans
          simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
            Complex.add_re, Complex.smul_re, smul_eq_mul]
          rw [habtrans]
          ring
      exact hvtrans.trans hlineTrans.symm
  by_cases htv0 : 0 ≤ tv
  · by_cases htv1 : tv ≤ 1
    · rw [segment_eq_image_lineMap]
      exact ⟨tv, ⟨htv0, htv1⟩, hvline.symm⟩
    · have h1tv : 1 < tv := lt_of_not_ge htv1
      let q := (tv - 1) / (tv - tp)
      have hden : 0 < tv - tp := sub_pos.mpr (htp.2.trans h1tv)
      have hq : q ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (sub_nonneg.mpr h1tv.le) hden.le
        · exact (div_le_one hden).2 (by linarith [htp.2])
      have hbvp : b ∈ segment ℝ v p := by
        rw [segment_eq_image_lineMap]
        refine ⟨q, hq, ?_⟩
        rw [hvline, ← hp]
        have hcompose : AffineMap.lineMap (AffineMap.lineMap a b tv)
            (AffineMap.lineMap a b tp) q =
            AffineMap.lineMap a b ((1 - q) * tv + q * tp) := by
          simp only [AffineMap.lineMap_apply_module]
          module
        rw [hcompose]
        have hparam : (1 - q) * tv + q * tp = 1 := by
          dsimp only [q]
          field_simp [hden.ne']
          ring
        rw [hparam]
        simp
      have hbball := (convex_ball v rho).segment_subset
        (Metric.mem_ball_self hrho) hpball hbvp
      have hbv : b = v := by
        simpa only [mem_singleton_iff] using hisolate ⟨hb, hbball⟩
      rw [← hbv]
      exact right_mem_segment ℝ a b
  · have htvneg : tv < 0 := lt_of_not_ge htv0
    let q := (-tv) / (tp - tv)
    have hden : 0 < tp - tv := sub_pos.mpr (htvneg.trans htp.1)
    have hq : q ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg (neg_nonneg.mpr htvneg.le) hden.le
      · exact (div_le_one hden).2 (by linarith [htp.1])
    have havp : a ∈ segment ℝ v p := by
      rw [segment_eq_image_lineMap]
      refine ⟨q, hq, ?_⟩
      rw [hvline, ← hp]
      have hcompose : AffineMap.lineMap (AffineMap.lineMap a b tv)
          (AffineMap.lineMap a b tp) q =
          AffineMap.lineMap a b ((1 - q) * tv + q * tp) := by
        simp only [AffineMap.lineMap_apply_module]
        module
      rw [hcompose]
      have hparam : (1 - q) * tv + q * tp = 0 := by
        dsimp only [q]
        field_simp [hden.ne']
        ring
      rw [hparam]
      simp
    have haball := (convex_ball v rho).segment_subset
      (Metric.mem_ball_self hrho) hpball havp
    have hav : a = v := by
      simpa only [mem_singleton_iff] using hisolate ⟨ha, haball⟩
    rw [← hav]
    exact left_mem_segment ℝ a b

private theorem transverseCoord_eq_of_mem_segment (axis : Axis) {a b z : Plane}
    (hab : axis.transverseCoord a = axis.transverseCoord b)
    (hz : z ∈ segment ℝ a b) :
    axis.transverseCoord z = axis.transverseCoord a := by
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, _, rfl⟩ := hz
  cases axis
  · change a.im = b.im at hab
    simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
      Complex.add_im, Complex.smul_im, smul_eq_mul]
    rw [hab]
    ring
  · change a.re = b.re at hab
    simp only [Axis.transverseCoord, AffineMap.lineMap_apply_module,
      Complex.add_re, Complex.smul_re, smul_eq_mul]
    rw [hab]
    ring

theorem intrinsicVertex_incident_axisEdge :
    ∀ (K : Region) (axis : Axis) (v : ↥K.vertices),
      ∃ w : ↥K.vertices,
        w.1 ≠ v.1 ∧
        Axis.transverseCoord axis w.1 = Axis.transverseCoord axis v.1 ∧
        openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices := by
  intro K axis v
  classical
  have hvvertex : v.1 ∈ vertexSet K.support := v.2
  have hfrontEq : frontier K.openCarrier = frontier K.support := by
    rw [frontier, frontier]
    change closure (interior K.support) \ interior (interior K.support) =
      closure K.support \ interior K.support
    rw [K.isPolygonal.closure_interior, interior_interior,
      K.isPolygonal.isClosed.closure_eq]
  have hvfront : v.1 ∈ frontier K.support :=
    hfrontEq ▸ region_vertices_subset_frontier K v.2
  have hvnotstraight : ¬BoundaryLocallyStraightAt K.support v.1 := by
    intro hs
    have hnot :=
      (Set.ext_iff.mp (region_vertices_eq_nonStraightBoundary K) v.1).mp v.2 |>.2
    apply hnot
    obtain ⟨L, hvL, hdim, hlocal⟩ := hs
    exact ⟨L, hvL, hdim, by simpa only [hfrontEq] using hlocal⟩
  obtain ⟨rCross, hrCross, hcross⟩ := K.isAxisParallel.localBoundaryCross v.1
  let VF : Finset Plane := K.isPolygonal.vertexSet_finite.toFinset
  have hIsoOpen : IsOpen (((↑(VF.erase v.1) : Set Plane))ᶜ) :=
    (VF.erase v.1).finite_toSet.isClosed.isOpen_compl
  have hvIso : v.1 ∈ ((↑(VF.erase v.1) : Set Plane))ᶜ := by simp
  obtain ⟨rho, hrho, hrhoSub⟩ := Metric.isOpen_iff.mp hIsoOpen v.1 hvIso
  have hisolate : vertexSet K.support ∩ Metric.ball v.1 rho ⊆ {v.1} := by
    rintro z ⟨hzV, hzball⟩
    by_contra hz
    have hzVF : z ∈ VF := by simpa [VF] using hzV
    exact hrhoSub hzball (Finset.mem_erase.mpr ⟨hz, hzVF⟩)
  obtain ⟨p, hpball, hpfront, hpnotVF, hpcoord, hptrans, hvpfront, hpgerm⟩ :=
    exists_axisGermPoint_near_nonStraight K.isPolygonal.closure_interior hvfront
      hvnotstraight ⟨rCross, hrCross, hcross⟩ axis VF rho hrho
  have hpnotvertex : p ∉ vertexSet K.support := by simpa [VF] using hpnotVF
  obtain ⟨a, b, ha, hb, hab, habtrans, hpab, habfront⟩ :=
    exists_intrinsic_axis_edge_of_germ K axis hpfront hpgerm
  have hvab : v.1 ∈ segment ℝ a b :=
    isolated_collinear_vertex_mem_segment axis hrho hab habtrans hptrans hpab hpball
      ha hb hisolate
  obtain ⟨a', b', ha', hb', ha'b', hpab', hfree, ha'ab, hb'ab⟩ :=
    trim_frontierSegment_at_nearest_vertices K.isPolygonal ha hb hab hpab hpnotvertex habfront
  have hend : a' = v.1 ∨ b' = v.1 :=
    trimmed_endpoint_eq_isolatedVertex hrho hab hpab ha' hb' hpab' hfree ha'ab hb'ab
      hvvertex hvab hpball hvpfront hisolate
  have ha'trans := transverseCoord_eq_of_mem_segment axis habtrans ha'ab
  have hb'trans := transverseCoord_eq_of_mem_segment axis habtrans hb'ab
  rcases hend with ha'v | hb'v
  · subst a'
    refine ⟨⟨b', hb'⟩, ha'b'.symm, ?_, hfree⟩
    exact hb'trans.trans ha'trans.symm
  · subst b'
    refine ⟨⟨a', ha'⟩, ha'b', ?_, ?_⟩
    · exact ha'trans.trans hb'trans.symm
    · intro z hz
      have hz' : z ∈ openSegment ℝ a' v.1 := by
        simpa only [openSegment_symm] using hz
      exact hfree hz'

theorem nonvertexFrontier_mem_intrinsicEdge :
    ∀ (K : Region) (x : Plane),
      x ∈ frontier K.support → x ∉ K.vertices →
      ∃ (axis : Axis) (v w : ↥K.vertices),
        v.1 ≠ w.1 ∧
        Axis.transverseCoord axis v.1 = Axis.transverseCoord axis w.1 ∧
        x ∈ openSegment ℝ v.1 w.1 ∧
        openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices := by
  intro K x hx hxnot
  have hxnot' : x ∉ vertexSet K.support := hxnot
  obtain ⟨L, hxL, hdim, hlocal⟩ :=
    K.isPolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hx hxnot'
  obtain ⟨d, hd, r, hr, hfront⟩ :=
    AffineSubspace.exists_ball_frontier_iff_affineLine hxL hdim hlocal
  obtain ⟨q, hq, hcross⟩ := K.isAxisParallel.localBoundaryCross x
  let eps := min r q / (2 * (‖d‖ + 1))
  have hmin : 0 < min r q := lt_min hr hq
  have heps : 0 < eps := div_pos hmin (mul_pos (by norm_num) (by positivity))
  let z := x + eps • d
  have hzdist : dist z x < min r q := by
    rw [dist_comm, show dist x z = ‖eps • d‖ by simp [z, dist_eq_norm]]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos heps]
    dsimp only [eps]
    have hn := norm_nonneg d
    field_simp
    nlinarith
  have hzfront : z ∈ frontier K.support :=
    (hfront z (Metric.mem_ball.mpr (hzdist.trans_le (min_le_left _ _)))).2
      (vadd_smul_mem_affineLine x d eps)
  have hzaxis := hcross z
    (Metric.mem_ball.mpr (hzdist.trans_le (min_le_right _ _))) hzfront
  have halign : d.re = 0 ∨ d.im = 0 := by
    rcases hzaxis with hzre | hzim
    · left
      have : eps * d.re = 0 := by simpa [z] using hzre
      exact (mul_eq_zero.mp this).resolve_left heps.ne'
    · right
      have : eps * d.im = 0 := by simpa [z] using hzim
      exact (mul_eq_zero.mp this).resolve_left heps.ne'
  rcases halign with hdre | hdim'
  · have hdimne : d.im ≠ 0 := by
      intro h
      exact hd (Complex.ext hdre h)
    have hgerm : ∀ᶠ z in nhds x,
        (z ∈ frontier K.support ↔ z ∈ axisLineThrough Axis.vertical x) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
      rw [hfront z hz]
      simp only [axisLineThrough, Axis.transverseCoord, mem_ofPred_eq, affineLine,
        signedSide, planarCross, hdre, zero_mul, zero_sub]
      constructor <;> intro h
      · have h' : -(d.im * (z.re - x.re)) = 0 := by linear_combination h
        exact sub_eq_zero.mp ((mul_eq_zero.mp (neg_eq_zero.mp h')).resolve_left hdimne)
      · rw [h]
        ring
    obtain ⟨a, b, ha, hb, hab, habtrans, hxab, habfront⟩ :=
      exists_intrinsic_axis_edge_of_germ K Axis.vertical hx hgerm
    obtain ⟨a', b', ha', hb', ha'b', hxab', hfree, ha'ab, hb'ab⟩ :=
      trim_frontierSegment_at_nearest_vertices K.isPolygonal ha hb hab hxab hxnot' habfront
    refine ⟨Axis.vertical, ⟨a', ha'⟩, ⟨b', hb'⟩, ha'b', ?_, hxab', hfree⟩
    exact (transverseCoord_eq_of_mem_segment Axis.vertical habtrans ha'ab).trans
      (transverseCoord_eq_of_mem_segment Axis.vertical habtrans hb'ab).symm
  · have hdrene : d.re ≠ 0 := by
      intro h
      exact hd (Complex.ext h hdim')
    have hgerm : ∀ᶠ z in nhds x,
        (z ∈ frontier K.support ↔ z ∈ axisLineThrough Axis.horizontal x) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)] with z hz
      rw [hfront z hz]
      simp only [axisLineThrough, Axis.transverseCoord, mem_ofPred_eq, affineLine,
        signedSide, planarCross, hdim']
      constructor <;> intro h
      · have h' : d.re * (z.im - x.im) = 0 := by linear_combination h
        exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left hdrene)
      · rw [h]
        ring
    obtain ⟨a, b, ha, hb, hab, habtrans, hxab, habfront⟩ :=
      exists_intrinsic_axis_edge_of_germ K Axis.horizontal hx hgerm
    obtain ⟨a', b', ha', hb', ha'b', hxab', hfree, ha'ab, hb'ab⟩ :=
      trim_frontierSegment_at_nearest_vertices K.isPolygonal ha hb hab hxab hxnot' habfront
    refine ⟨Axis.horizontal, ⟨a', ha'⟩, ⟨b', hb'⟩, ha'b', ?_, hxab', hfree⟩
    exact (transverseCoord_eq_of_mem_segment Axis.horizontal habtrans ha'ab).trans
      (transverseCoord_eq_of_mem_segment Axis.horizontal habtrans hb'ab).symm

theorem horizontalSectionEndpoints_intrinsic :
    ∀ (K : Region) {y a b : ℝ},
      (∀ v : ↥K.vertices, v.1.im ≠ y) → a < b →
      Complex.mk a y ∈ frontier K.support →
      Complex.mk b y ∈ frontier K.support →
      (∀ x ∈ Ioo a b, Complex.mk x y ∈ K.openCarrier) →
      ∃ v w : ↥K.vertices, v.1.re = a ∧ w.1.re = b := by
  intro K y a b hgeneric _hab hafront hbfront _hinside
  have endpoint (c : ℝ) (hc : Complex.mk c y ∈ frontier K.support) :
      ∃ v : ↥K.vertices, v.1.re = c := by
    have hcnot : Complex.mk c y ∉ K.vertices := by
      intro hcV
      exact hgeneric ⟨Complex.mk c y, hcV⟩ rfl
    obtain ⟨axis, v, w, hvw, htrans, hcx, _hfree⟩ :=
      nonvertexFrontier_mem_intrinsicEdge K (Complex.mk c y) hc hcnot
    cases axis with
    | horizontal =>
        have hvim : v.1.im = y := by
          have hline := transverseCoord_eq_of_mem_segment Axis.horizontal htrans
            (openSegment_subset_segment ℝ v.1 w.1 hcx)
          simpa [Axis.transverseCoord] using hline.symm
        exact (hgeneric v hvim).elim
    | vertical =>
        have hvre : v.1.re = c := by
          have hline := transverseCoord_eq_of_mem_segment Axis.vertical htrans
            (openSegment_subset_segment ℝ v.1 w.1 hcx)
          simpa [Axis.transverseCoord] using hline.symm
        exact ⟨v, hvre⟩
  obtain ⟨v, hv⟩ := endpoint a hafront
  obtain ⟨w, hw⟩ := endpoint b hbfront
  exact ⟨v, w, hv, hw⟩

theorem frontier_subset_vertexCoordinateGrid :
    ∀ K : Region,
      frontier K.support ⊆
        {x : Plane |
          (∃ v ∈ K.vertices, x.re = v.re) ∨
            ∃ v ∈ K.vertices, x.im = v.im} := by
  intro K x hx
  by_cases hxv : x ∈ K.vertices
  · exact Or.inl ⟨x, hxv, rfl⟩
  obtain ⟨axis, v, w, _hvw, htrans, hxseg, _⟩ :=
    nonvertexFrontier_mem_intrinsicEdge K x hx hxv
  have hxline := transverseCoord_eq_of_mem_segment axis htrans
    (openSegment_subset_segment ℝ v.1 w.1 hxseg)
  cases axis with
  | horizontal =>
      right
      exact ⟨v.1, v.2, by simpa [Axis.transverseCoord] using hxline⟩
  | vertical =>
      left
      exact ⟨v.1, v.2, by simpa [Axis.transverseCoord] using hxline⟩

private theorem segment_coord_ne_of_sameSide {x y : Plane} {c : ℝ}
    (axis : Axis) (hx : axis.coord x ≠ c) (hy : axis.coord y ≠ c)
    (hsame : axis.coord x < c ↔ axis.coord y < c) :
    ∀ z ∈ segment ℝ x y, axis.coord z ≠ c := by
  intro z hz
  rw [segment_eq_image_lineMap] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  have hformula : axis.coord (AffineMap.lineMap x y t) =
      (1 - t) * axis.coord x + t * axis.coord y := by
    cases axis <;> simp [Axis.coord, AffineMap.lineMap_apply_module]
  rw [hformula]
  by_cases hxc : axis.coord x < c
  · have hyc := hsame.mp hxc
    have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    intro heq
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hxc.le),
      mul_nonneg ht.1 (sub_nonneg.mpr hyc.le)]
  · have hcx : c < axis.coord x := lt_of_le_of_ne (le_of_not_gt hxc) hx.symm
    have hcy : c < axis.coord y := by
      have : ¬axis.coord y < c := mt hsame.mpr hxc
      exact lt_of_le_of_ne (le_of_not_gt this) hy.symm
    have hnonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    intro heq
    nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hcx.le),
      mul_nonneg ht.1 (sub_nonneg.mpr hcy.le)]

theorem sameVertexGridCell_openCarrier_iff :
    ∀ (K : Region) (x y : Plane),
      OffVertexCoordinateGrid K x → OffVertexCoordinateGrid K y →
      SameVertexGridCell K x y →
      (x ∈ K.openCarrier ↔ y ∈ K.openCarrier) := by
  intro K x y hxoff hyoff hsame
  have hsegdisj : Disjoint (segment ℝ x y) (frontier K.support) := by
    rw [Set.disjoint_left]
    intro z hzseg hzfront
    rcases frontier_subset_vertexCoordinateGrid K hzfront with
      ⟨v, hv, hzre⟩ | ⟨v, hv, hzim⟩
    · exact (segment_coord_ne_of_sameSide Axis.horizontal
        (hxoff v hv).1 (hyoff v hv).1 (hsame.1 v hv) z hzseg) hzre
    · exact (segment_coord_ne_of_sameSide Axis.vertical
        (hxoff v hv).2 (hyoff v hv).2 (hsame.2 v hv) z hzseg) hzim
  have hchoice := IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
    (convex_segment x y).isPreconnected hsegdisj
  constructor
  · intro hx
    rcases hchoice with hin | hout
    · exact hin (right_mem_segment ℝ x y)
    · have hxout : x ∉ K.support := interior_subset (hout (left_mem_segment ℝ x y))
      exact (hxout (interior_subset hx)).elim
  · intro hy
    rcases hchoice with hin | hout
    · exact hin (left_mem_segment ℝ x y)
    · have hyout : y ∉ K.support := interior_subset (hout (right_mem_segment ℝ x y))
      exact (hyout (interior_subset hy)).elim

/-- Every nonempty open set contains a point off the finite intrinsic coordinate grid. -/
theorem exists_offVertexCoordinateGrid_mem_open (K : Region)
    {U : Set Plane} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, OffVertexCoordinateGrid K z := by
  classical
  let VF := K.vertexFinset
  let bad : Set Plane := ⋃ v : ↥VF,
    ({z : Plane | z.re = v.1.re} ∪ {z : Plane | z.im = v.1.im})
  have hbadzero : volume bad = 0 := by
    dsimp only [bad]
    apply measure_iUnion_null
    intro v
    exact measure_union_null (volume_re_eq_zero v.1.re) (volume_im_eq_zero v.1.im)
  by_contra hn
  push Not at hn
  have hsub : U ⊆ bad := by
    intro z hz
    have hznot := hn z hz
    by_contra hzbad
    apply hznot
    intro v hv
    have hvVF : v ∈ VF := by
      dsimp only [VF]
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    constructor
    · intro hzre
      exact hzbad (mem_iUnion.mpr ⟨⟨v, hvVF⟩, Or.inl hzre⟩)
    · intro hzim
      exact hzbad (mem_iUnion.mpr ⟨⟨v, hvVF⟩, Or.inr hzim⟩)
  have hUzero : volume U = 0 := measure_mono_null hsub hbadzero
  exact hUopen.measure_ne_zero volume hUne hUzero

theorem support_eq_closure_openCarrier_offVertexGrid :
    ∀ K : Region,
      K.support =
        closure {x : Plane | x ∈ K.openCarrier ∧ OffVertexCoordinateGrid K x} := by
  intro K
  apply Set.Subset.antisymm
  · rw [← K.isPolygonal.closure_interior]
    apply closure_minimal
    · intro x hx
      rw [mem_closure_iff]
      intro U hUopen hxU
      obtain ⟨z, hzU, hzoff⟩ := exists_offVertexCoordinateGrid_mem_open K
        (hUopen.inter isOpen_interior) ⟨x, hxU, hx⟩
      exact ⟨z, hzU.1, hzU.2, hzoff⟩
    · exact isClosed_closure
  · apply closure_minimal
    · rintro x ⟨hx, _⟩
      exact interior_subset hx
    · exact K.isPolygonal.isClosed

private theorem segment_inter_frontier_of_mem_interior_not_mem
    {D : Set Plane} {x y : Plane} (hx : x ∈ interior D) (hy : y ∉ D) :
    ∃ z ∈ segment ℝ x y, z ∈ frontier D := by
  by_contra hn
  push Not at hn
  have hdisj : Disjoint (segment ℝ x y) (frontier D) := by
    rw [Set.disjoint_left]
    exact hn
  rcases IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (convex_segment x y).isPreconnected hdisj with hin | hout
  · exact hy (interior_subset (hin (right_mem_segment ℝ x y)))
  · have hxout : x ∉ D := interior_subset (hout (left_mem_segment ℝ x y))
    exact hxout (interior_subset hx)

private theorem exists_intrinsicLevels_around (K : Region) (axis : Axis) {x : Plane}
    (hx : x ∈ K.openCarrier) (hxoff : OffVertexCoordinateGrid K x) :
    (∃ v ∈ K.vertices, axis.coord v < axis.coord x) ∧
      ∃ v ∈ K.vertices, axis.coord x < axis.coord v := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball (0 : Plane)).mp
    K.isPolygonal.isBounded
  let M := |R| + |axis.coord x| + 1
  have hM : 0 < M := by positivity
  let yp := x + M • axisVector axis
  let ym := x - M • axisVector axis
  have hypnot : yp ∉ K.support := by
    intro hyp
    have hyball := hR hyp
    have hdist : ‖yp‖ < R := by simpa [Complex.dist_eq] using hyball
    cases axis with
    | horizontal =>
        have habs := abs_le.mp (Complex.abs_re_le_norm yp |>.trans hdist.le)
        simp only [yp, M, axisVector, Axis.coord, Complex.add_re, Complex.smul_re,
          Complex.one_re, smul_eq_mul, mul_one] at habs
        nlinarith [le_abs_self R, neg_abs_le x.re]
    | vertical =>
        have habs := abs_le.mp (Complex.abs_im_le_norm yp |>.trans hdist.le)
        simp only [yp, M, axisVector, Axis.coord, Complex.add_im, Complex.smul_im,
          Complex.I_im, smul_eq_mul, mul_one] at habs
        nlinarith [le_abs_self R, neg_abs_le x.im]
  have hymnot : ym ∉ K.support := by
    intro hym
    have hyball := hR hym
    have hdist : ‖ym‖ < R := by simpa [Complex.dist_eq] using hyball
    cases axis with
    | horizontal =>
        have habs := abs_le.mp (Complex.abs_re_le_norm ym |>.trans hdist.le)
        simp only [ym, M, axisVector, Axis.coord, Complex.sub_re, Complex.smul_re,
          Complex.one_re, smul_eq_mul, mul_one] at habs
        nlinarith [le_abs_self R, le_abs_self x.re]
    | vertical =>
        have habs := abs_le.mp (Complex.abs_im_le_norm ym |>.trans hdist.le)
        simp only [ym, M, axisVector, Axis.coord, Complex.sub_im, Complex.smul_im,
          Complex.I_im, smul_eq_mul, mul_one] at habs
        nlinarith [le_abs_self R, le_abs_self x.im]
  obtain ⟨zp, hzpseg, hzpfront⟩ :=
    segment_inter_frontier_of_mem_interior_not_mem hx hypnot
  obtain ⟨zm, hzmseg, hzmfront⟩ :=
    segment_inter_frontier_of_mem_interior_not_mem hx hymnot
  have endpoint_coord {y z : Plane} {sgn : ℝ} (hydef : y = x + sgn • axisVector axis)
      (hsgn : sgn ≠ 0) (hzseg : z ∈ segment ℝ x y)
      (hzfront : z ∈ frontier K.support) :
      ∃ v ∈ K.vertices, axis.coord z = axis.coord v := by
    cases axis with
    | horizontal =>
        rcases frontier_subset_vertexCoordinateGrid K hzfront with
          ⟨v, hv, hzre⟩ | ⟨v, hv, hzim⟩
        · exact ⟨v, hv, hzre⟩
        · exfalso
          have hztrans := transverseCoord_eq_of_mem_segment Axis.horizontal (by
            simp [hydef, axisVector, Axis.transverseCoord]) hzseg
          exact (hxoff v hv).2 (by simpa [Axis.transverseCoord] using hztrans.symm.trans hzim)
    | vertical =>
        rcases frontier_subset_vertexCoordinateGrid K hzfront with
          ⟨v, hv, hzre⟩ | ⟨v, hv, hzim⟩
        · exfalso
          have hztrans := transverseCoord_eq_of_mem_segment Axis.vertical (by
            simp [hydef, axisVector, Axis.transverseCoord]) hzseg
          exact (hxoff v hv).1 (by simpa [Axis.transverseCoord] using hztrans.symm.trans hzre)
        · exact ⟨v, hv, hzim⟩
  have hzpcoord : axis.coord x < axis.coord zp := by
    rw [segment_eq_image_lineMap] at hzpseg
    obtain ⟨t, ht, hzt⟩ := hzpseg
    have htpos : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro ht0
      have hzx : zp = x := by rw [← hzt, ← ht0]; simp
      rw [hzx] at hzpfront
      exact hzpfront.2 hx
    rw [← hzt]
    cases axis <;> simp [yp, axisVector, Axis.coord, AffineMap.lineMap_apply_module] <;>
      nlinarith [htpos, hM]
  have hzmcoord : axis.coord zm < axis.coord x := by
    rw [segment_eq_image_lineMap] at hzmseg
    obtain ⟨t, ht, hzt⟩ := hzmseg
    have htpos : 0 < t := by
      apply lt_of_le_of_ne ht.1
      intro ht0
      have hzx : zm = x := by rw [← hzt, ← ht0]; simp
      rw [hzx] at hzmfront
      exact hzmfront.2 hx
    rw [← hzt]
    cases axis <;> simp [ym, axisVector, Axis.coord, AffineMap.lineMap_apply_module] <;>
      nlinarith [htpos, hM]
  obtain ⟨vp, hvp, hzp⟩ := endpoint_coord rfl hM.ne' hzpseg hzpfront
  obtain ⟨vm, hvm, hzm⟩ := endpoint_coord (by simp only [ym, sub_eq_add_neg, neg_smul])
    (neg_ne_zero.mpr hM.ne')
    hzmseg hzmfront
  exact ⟨⟨vm, hvm, by linarith⟩, ⟨vp, hvp, by linarith⟩⟩

private theorem exists_consecutiveLevelPair_around {s : Finset ℝ} {x : ℝ}
    (hx : x ∉ s) (hl : ∃ a ∈ s, a < x) (hu : ∃ b ∈ s, x < b) :
    ∃ a b, (a, b) ∈ consecutiveLevelPairs s ∧ x ∈ Ioo a b := by
  classical
  let L : Set ℝ := {a | a ∈ s ∧ a < x}
  let U : Set ℝ := {b | b ∈ s ∧ x < b}
  have hLfin : L.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  have hUfin : U.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  have hLne : L.Nonempty := by
    obtain ⟨a, ha, hax⟩ := hl
    exact ⟨a, ha, hax⟩
  have hUne : U.Nonempty := by
    obtain ⟨b, hb, hxb⟩ := hu
    exact ⟨b, hb, hxb⟩
  obtain ⟨a, haL, hamax⟩ := Set.exists_max_image L id hLfin hLne
  obtain ⟨b, hbU, hbmin⟩ := Set.exists_min_image U id hUfin hUne
  refine ⟨a, b, ?_, haL.2, hbU.2⟩
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨haL.1, hbU.1⟩, haL.2.trans hbU.2, ?_⟩
  intro z hzs hzbetween
  by_cases hzx : z < x
  · exact (not_lt_of_ge (hamax z ⟨hzs, hzx⟩)) hzbetween.1
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) (Ne.symm (by
        intro h; apply hx; simpa [h] using hzs))
    exact (not_lt_of_ge (hbmin z ⟨hzs, hxz⟩)) hzbetween.2

/-- An off-grid point in the open carrier lies in a consecutive intrinsic grid cell. -/
theorem exists_intrinsicCell_around_offGrid (K : Region) {x : Plane}
    (hx : x ∈ K.openCarrier) (hxoff : OffVertexCoordinateGrid K x) :
    ∃ xp yp,
      xp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.horizontal) ∧
      yp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.vertical) ∧
      x.re ∈ Ioo xp.1 xp.2 ∧ x.im ∈ Ioo yp.1 yp.2 := by
  have haround := exists_intrinsicLevels_around K Axis.horizontal hx hxoff
  have hvaround := exists_intrinsicLevels_around K Axis.vertical hx hxoff
  have hxnot : x.re ∉ intrinsicCoordinateLevels K Axis.horizontal := by
    intro h
    rw [intrinsicCoordinateLevels, Finset.mem_image] at h
    obtain ⟨v, hv, hvx⟩ := h
    have hvV : v ∈ K.vertices := by
      change v ∈ (↑K.vertexFinset : Set Plane) at hv
      simpa only [K.coe_vertexFinset] using hv
    exact (hxoff v hvV).1 (by simpa [Axis.coord] using hvx.symm)
  have hynot : x.im ∉ intrinsicCoordinateLevels K Axis.vertical := by
    intro h
    rw [intrinsicCoordinateLevels, Finset.mem_image] at h
    obtain ⟨v, hv, hvx⟩ := h
    have hvV : v ∈ K.vertices := by
      change v ∈ (↑K.vertexFinset : Set Plane) at hv
      simpa only [K.coe_vertexFinset] using hv
    exact (hxoff v hvV).2 (by simpa [Axis.coord] using hvx.symm)
  obtain ⟨xa, xb, hxp, hxmem⟩ := exists_consecutiveLevelPair_around hxnot (by
    obtain ⟨v, hv, hlt⟩ := haround.1
    refine ⟨v.re, ?_, by simpa [Axis.coord] using hlt⟩
    rw [intrinsicCoordinateLevels, Finset.mem_image]
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact ⟨v, hvf, by simp [Axis.coord]⟩) (by
    obtain ⟨v, hv, hlt⟩ := haround.2
    refine ⟨v.re, ?_, by simpa [Axis.coord] using hlt⟩
    rw [intrinsicCoordinateLevels, Finset.mem_image]
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact ⟨v, hvf, by simp [Axis.coord]⟩)
  obtain ⟨ya, yb, hyp, hymem⟩ := exists_consecutiveLevelPair_around hynot (by
    obtain ⟨v, hv, hlt⟩ := hvaround.1
    refine ⟨v.im, ?_, by simpa [Axis.coord] using hlt⟩
    rw [intrinsicCoordinateLevels, Finset.mem_image]
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact ⟨v, hvf, by simp [Axis.coord]⟩) (by
    obtain ⟨v, hv, hlt⟩ := hvaround.2
    refine ⟨v.im, ?_, by simpa [Axis.coord] using hlt⟩
    rw [intrinsicCoordinateLevels, Finset.mem_image]
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact ⟨v, hvf, by simp [Axis.coord]⟩)
  exact ⟨(xa, xb), (ya, yb), hxp, hyp, hxmem, hymem⟩

private theorem consecutivePair_openIntervals_disjoint {s : Finset ℝ}
    {p q : ℝ × ℝ} (hp : p ∈ consecutiveLevelPairs s)
    (hq : q ∈ consecutiveLevelPairs s) (hpq : p ≠ q) :
    Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2) := by
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp hq
  rw [Set.disjoint_left]
  intro z hzp hzq
  have hpNo := hp.2.2
  have hqNo := hq.2.2
  have hleft : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact (hpNo q.1 hq.1.1 ⟨h, hzq.1.trans hzp.2⟩).elim
    · exact h
    · exact (hqNo p.1 hp.1.1 ⟨h, hzp.1.trans hzq.2⟩).elim
  have hright : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · exact (hqNo p.2 hp.1.2 ⟨hzq.1.trans hzp.2, h⟩).elim
    · exact h
    · exact (hpNo q.2 hq.1.2 ⟨hzp.1.trans hzq.2, h⟩).elim
  exact hpq (Prod.ext hleft hright)

private theorem closedAxisBoxes_aedisjoint_of_open_disjoint
    {a b c d e f g h : ℝ} (hab : a < b) (hcd : c < d)
    (hef : e < f) (hgh : g < h)
    (hdisj : Disjoint (Ioo a b ×ℂ Ioo c d) (Ioo e f ×ℂ Ioo g h)) :
    AEDisjoint volume (closedAxisBox a b c d) (closedAxisBox e f g h) := by
  change volume (closedAxisBox a b c d ∩ closedAxisBox e f g h) = 0
  apply measure_mono_null ?_
    (measure_union_null (closedAxisBox_isRectangle hab hcd).isPolygonal.volume_frontier
      (closedAxisBox_isRectangle hef hgh).isPolygonal.volume_frontier)
  intro z hz
  by_cases hzint : z ∈ interior (closedAxisBox a b c d)
  · right
    rw [(closedAxisBox_isRectangle hef hgh).isPolygonal.isClosed.frontier_eq]
    refine ⟨hz.2, ?_⟩
    intro hzint'
    apply Set.disjoint_left.mp hdisj
      (by
        change z.re ∈ Ioo a b ∧ z.im ∈ Ioo c d
        simpa [interior_closedAxisBox hab hcd] using hzint)
      (by
        change z.re ∈ Ioo e f ∧ z.im ∈ Ioo g h
        simpa [interior_closedAxisBox hef hgh] using hzint')
  · left
    rw [(closedAxisBox_isRectangle hab hcd).isPolygonal.isClosed.frontier_eq]
    exact ⟨hz.1, hzint⟩

/-- Every intrinsic grid piece is a consecutive-level rectangle whose interior lies
    in the open carrier. -/
theorem mem_intrinsicGridPieces (K : Region) {r : Set Plane}
    (hr : r ∈ intrinsicGridPieces K) :
    ∃ xp yp,
      xp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.horizontal) ∧
      yp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.vertical) ∧
      interior (closedAxisBox xp.1 xp.2 yp.1 yp.2) ⊆ K.openCarrier ∧
      r = closedAxisBox xp.1 xp.2 yp.1 yp.2 := by
  classical
  rw [intrinsicGridPieces, Finset.mem_image] at hr
  obtain ⟨p, hp, rfl⟩ := hr
  have hp' := Finset.mem_filter.mp hp
  have hprod := Finset.mem_product.mp hp'.1
  exact ⟨p.1, p.2, hprod.1, hprod.2, hp'.2, rfl⟩

private theorem consecutiveLevelPair_data {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) :
    p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 := by
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2.1⟩

private theorem intrinsicGridPiece_isIntrinsic (K : Region) {r : Set Plane}
    (hr : r ∈ intrinsicGridPieces K) :
    IsIntrinsicGridRectangle K r := by
  obtain ⟨xp, yp, hxp, hyp, _hinside, rfl⟩ := mem_intrinsicGridPieces K hr
  have hx := consecutiveLevelPair_data hxp
  have hy := consecutiveLevelPair_data hyp
  refine ⟨xp.1, xp.2, yp.1, yp.2, hx.2.2, hy.2.2, rfl, ?_, ?_, ?_, ?_⟩
  · have hm := hx.1
    rw [intrinsicCoordinateLevels, Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    refine ⟨v, ?_, by simpa [Axis.coord] using hveq⟩
    change v ∈ (↑K.vertexFinset : Set Plane) at hv
    simpa only [K.coe_vertexFinset] using hv
  · have hm := hx.2.1
    rw [intrinsicCoordinateLevels, Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    refine ⟨v, ?_, by simpa [Axis.coord] using hveq⟩
    change v ∈ (↑K.vertexFinset : Set Plane) at hv
    simpa only [K.coe_vertexFinset] using hv
  · have hm := hy.1
    rw [intrinsicCoordinateLevels, Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    refine ⟨v, ?_, by simpa [Axis.coord] using hveq⟩
    change v ∈ (↑K.vertexFinset : Set Plane) at hv
    simpa only [K.coe_vertexFinset] using hv
  · have hm := hy.2.1
    rw [intrinsicCoordinateLevels, Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    refine ⟨v, ?_, by simpa [Axis.coord] using hveq⟩
    change v ∈ (↑K.vertexFinset : Set Plane) at hv
    simpa only [K.coe_vertexFinset] using hv

private theorem consecutivePair_sameSide {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) {x y : ℝ}
    (hx : x ∈ Ioo p.1 p.2) (hy : y ∈ Ioo p.1 p.2) {c : ℝ} (hc : c ∈ s) :
    x ≠ c ∧ (x < c ↔ y < c) := by
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp
  have hnot : ¬(p.1 < c ∧ c < p.2) := hp.2.2 c hc
  have hout : c ≤ p.1 ∨ p.2 ≤ c := by
    by_contra h
    push Not at h
    exact hnot ⟨h.1, h.2⟩
  rcases hout with hcL | hcR
  · refine ⟨by linarith [hx.1], ?_⟩
    constructor <;> intro h <;> linarith [hx.1, hy.1]
  · refine ⟨by linarith [hx.2], ?_⟩
    constructor <;> intro h <;> linarith [hx.2, hy.2]

private theorem intrinsicCell_interior_uniform (K : Region) {xp yp : ℝ × ℝ}
    (hxp : xp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.horizontal))
    (hyp : yp ∈ consecutiveLevelPairs (intrinsicCoordinateLevels K Axis.vertical))
    {x : Plane} (hxbox : x ∈ interior (closedAxisBox xp.1 xp.2 yp.1 yp.2))
    (hx : x ∈ K.openCarrier) :
    interior (closedAxisBox xp.1 xp.2 yp.1 yp.2) ⊆ K.openCarrier := by
  have hxdata := consecutiveLevelPair_data hxp
  have hydata := consecutiveLevelPair_data hyp
  rw [interior_closedAxisBox hxdata.2.2 hydata.2.2] at hxbox
  intro y hybox
  rw [interior_closedAxisBox hxdata.2.2 hydata.2.2] at hybox
  have hxoff : OffVertexCoordinateGrid K x := by
    intro v hv
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    constructor
    · exact (consecutivePair_sameSide hxp hxbox.1 hybox.1
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
    · exact (consecutivePair_sameSide hyp hxbox.2 hybox.2
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
  have hyoff : OffVertexCoordinateGrid K y := by
    intro v hv
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    constructor
    · exact (consecutivePair_sameSide hxp hybox.1 hxbox.1
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
    · exact (consecutivePair_sameSide hyp hybox.2 hxbox.2
        (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).1
  apply (sameVertexGridCell_openCarrier_iff K x y hxoff hyoff ?_).mp hx
  constructor
  · intro v hv
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact (consecutivePair_sameSide hxp hxbox.1 hybox.1
      (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).2
  · intro v hv
    have hvf : v ∈ K.vertexFinset := by
      change v ∈ (↑K.vertexFinset : Set Plane)
      simpa only [K.coe_vertexFinset] using hv
    exact (consecutivePair_sameSide hyp hxbox.2 hybox.2
      (Finset.mem_image.mpr ⟨v, hvf, by simp [Axis.coord]⟩)).2

theorem exists_intrinsicGridRectangulation :
    ∀ K : Region,
      ∃ R : Rectangulation K.support,
        R.pieces = intrinsicGridPieces K ∧
        ∀ r ∈ R.pieces, IsIntrinsicGridRectangle K r := by
  intro K
  classical
  let P := intrinsicGridPieces K
  have hrect : ∀ r ∈ P, IsRectangle r := by
    intro r hr
    obtain ⟨x₀, x₁, y₀, y₁, hx, hy, rfl, _⟩ :=
      intrinsicGridPiece_isIntrinsic K hr
    exact closedAxisBox_isRectangle hx hy
  have hpair : ((P : Finset (Set Plane)) : Set (Set Plane)).Pairwise (AEDisjoint volume) := by
    intro r hr s hs hrs
    obtain ⟨xp, yp, hxp, hyp, _hrin, hrbox⟩ := mem_intrinsicGridPieces K hr
    obtain ⟨xq, yq, hxq, hyq, _hsin, hsbox⟩ := mem_intrinsicGridPieces K hs
    have hxd := consecutiveLevelPair_data hxp
    have hyd := consecutiveLevelPair_data hyp
    have hxdq := consecutiveLevelPair_data hxq
    have hydq := consecutiveLevelPair_data hyq
    rw [hrbox, hsbox]
    apply closedAxisBoxes_aedisjoint_of_open_disjoint
      hxd.2.2 hyd.2.2 hxdq.2.2 hydq.2.2
    by_cases hxeq : xp = xq
    · have hyeq : yp ≠ yq := by
        intro h
        exact hrs (by rw [hrbox, hsbox, hxeq, h])
      have hydis := consecutivePair_openIntervals_disjoint hyp hyq hyeq
      rw [Set.disjoint_left]
      intro z hz hz'
      exact Set.disjoint_left.mp hydis hz.2 hz'.2
    · have hxdis := consecutivePair_openIntervals_disjoint hxp hxq hxeq
      rw [Set.disjoint_left]
      intro z hz hz'
      exact Set.disjoint_left.mp hxdis hz.1 hz'.1
  have hclosedUnion : IsClosed (⋃₀ (P : Set (Set Plane))) := by
    rw [sUnion_eq_biUnion]
    apply isClosed_biUnion_finset
    intro r hr
    exact IsRectangle.isClosed (hrect r hr)
  have hunion : ⋃₀ (P : Set (Set Plane)) = K.support := by
    apply Set.Subset.antisymm
    · rintro z ⟨r, hr, hzr⟩
      obtain ⟨xp, yp, hxp, hyp, hinside, rfl⟩ := mem_intrinsicGridPieces K hr
      have hxd := consecutiveLevelPair_data hxp
      have hyd := consecutiveLevelPair_data hyp
      have hboxsub : closedAxisBox xp.1 xp.2 yp.1 yp.2 ⊆ K.support := by
        rw [← closure_interior_closedAxisBox hxd.2.2 hyd.2.2]
        exact closure_minimal (fun x hx ↦ interior_subset (hinside hx))
          K.isPolygonal.isClosed
      exact hboxsub hzr
    · rw [support_eq_closure_openCarrier_offVertexGrid K,
        ← hclosedUnion.closure_eq]
      apply closure_mono
      rintro x ⟨hx, hxoff⟩
      obtain ⟨xp, yp, hxp, hyp, hxre, hxim⟩ :=
        exists_intrinsicCell_around_offGrid K hx hxoff
      have hxd := consecutiveLevelPair_data hxp
      have hyd := consecutiveLevelPair_data hyp
      have hxbox : x ∈ interior (closedAxisBox xp.1 xp.2 yp.1 yp.2) := by
        rw [interior_closedAxisBox hxd.2.2 hyd.2.2]
        exact ⟨hxre, hxim⟩
      have hinside := intrinsicCell_interior_uniform K hxp hyp hxbox hx
      have hcell : closedAxisBox xp.1 xp.2 yp.1 yp.2 ∈ P := by
        change closedAxisBox xp.1 xp.2 yp.1 yp.2 ∈ intrinsicGridPieces K
        rw [intrinsicGridPieces, Finset.mem_image]
        refine ⟨(xp, yp), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨hxp, hyp⟩, hinside⟩
      exact ⟨closedAxisBox xp.1 xp.2 yp.1 yp.2, hcell,
        interior_subset hxbox⟩
  let R : Rectangulation K.support :=
    { pieces := P
      isRectangle := hrect
      pairwiseAEDisjoint := hpair
      sUnion_eq := hunion }
  refine ⟨R, rfl, ?_⟩
  intro r hr
  exact intrinsicGridPiece_isIntrinsic K hr


end Tiling.AxisParallel.IntrinsicVertices

namespace Tiling.AxisParallel.Region

theorem vertices_coordinateSwap (K : Tiling.AxisParallel.Region) :
    (K.coordinateSwap).vertices =
      Tiling.AxisParallel.coordinateSwap '' K.vertices := by
  rw [Tiling.AxisParallel.Region.vertices,
    Tiling.AxisParallel.Region.vertices,
    Tiling.AxisParallel.Region.coordinateSwap,
    IntrinsicVertices.coordinateSwap_vertexSet]

end Tiling.AxisParallel.Region

namespace Tiling.AxisParallel
/-- A single intrinsic region has an exact finite boundary-segment
presentation.  The finite-window reduction below leaves the additional task
of clipping these segments after neighbouring tiles cancel portions of them. -/
theorem Region.exists_finite_frontier_intrinsicSegments (K : Region) :
    ∃ G : Set (Set Tiling.Plane), G.Finite ∧
      (∀ g ∈ G, ∃ a b : Tiling.Plane,
        a ≠ b ∧ (a.re = b.re ∨ a.im = b.im) ∧
          g = segment ℝ a b ∧ g ⊆ frontier K.support) ∧
      frontier K.support = ⋃₀ G := by
  classical
  let : Finite ↥K.vertices := K.isPolygonal.vertexSet_finite.to_subtype
  let P : Set (↥K.vertices × ↥K.vertices) :=
    {p | p.1 ≠ p.2 ∧
      (p.1.1.re = p.2.1.re ∨ p.1.1.im = p.2.1.im) ∧
      segment ℝ p.1.1 p.2.1 ⊆ frontier K.support}
  let G : Set (Set Tiling.Plane) :=
    (fun p : ↥K.vertices × ↥K.vertices => segment ℝ p.1.1 p.2.1) '' P
  have hGfinite : G.Finite := (Set.finite_univ.subset (Set.subset_univ P)).image _
  have hseg (v w : ↥K.vertices)
      (hopen : openSegment ℝ v.1 w.1 ⊆ frontier K.support) :
      segment ℝ v.1 w.1 ⊆ frontier K.support := by
    rw [← closure_openSegment v.1 w.1]
    exact closure_minimal hopen isClosed_frontier
  have hcover : frontier K.support ⊆ ⋃₀ G := by
    intro x hx
    by_cases hv : x ∈ K.vertices
    · let v : ↥K.vertices := ⟨x, hv⟩
      obtain ⟨w, hne, halign, hopen⟩ :=
        IntrinsicVertices.intrinsicVertex_incident_axisEdge K Axis.horizontal v
      have hne' : v ≠ w := fun h => hne (congrArg Subtype.val h).symm
      have halign' : v.1.re = w.1.re ∨ v.1.im = w.1.im :=
        Or.inr halign.symm
      have hfront := hseg v w (fun z hz => (hopen hz).1)
      refine Set.mem_sUnion.mpr ⟨segment ℝ v.1 w.1, ?_, ?_⟩
      · exact ⟨(v, w), ⟨hne', halign', hfront⟩, rfl⟩
      · change v.1 ∈ segment ℝ v.1 w.1
        exact left_mem_segment ℝ _ _
    · obtain ⟨axis, v, w, hne, halign, hxseg, hopen⟩ :=
        IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K x hx hv
      have hne' : v ≠ w := fun h => hne (congrArg Subtype.val h)
      have halign' : v.1.re = w.1.re ∨ v.1.im = w.1.im := by
        cases axis with
        | horizontal => exact Or.inr halign
        | vertical => exact Or.inl halign
      have hfront := hseg v w (fun z hz => (hopen hz).1)
      refine Set.mem_sUnion.mpr ⟨segment ℝ v.1 w.1, ?_, ?_⟩
      · exact ⟨(v, w), ⟨hne', halign', hfront⟩, rfl⟩
      · exact openSegment_subset_segment ℝ _ _ hxseg
  refine ⟨G, hGfinite, ?_, ?_⟩
  · intro g hg
    obtain ⟨p, hp, rfl⟩ := hg
    exact ⟨p.1.1, p.2.1, (fun h => hp.1 (Subtype.ext h)),
      hp.2.1, rfl, hp.2.2⟩
  · apply Set.Subset.antisymm hcover
    rintro x ⟨g, hg, hx⟩
    obtain ⟨p, hp, rfl⟩ := hg
    exact hp.2.2 hx


end Tiling.AxisParallel

namespace Tiling.AxisParallel

private theorem horizontal_segment_interval (a b c : ℝ) (hab : a ≤ b) :
    segment ℝ (Complex.mk a c) (Complex.mk b c) =
      {z : ℂ | z.re ∈ Icc a b ∧ z.im = c} := by
  have hprod : (fun x : ℝ => (x, c)) '' Icc a b =
      segment ℝ (a, c) (b, c) := by
    rw [← segment_eq_Icc hab]
    exact Prod.image_mk_segment_left a b c
  calc
    segment ℝ (Complex.mk a c) (Complex.mk b c) =
        Complex.equivRealProdCLM.symm '' segment ℝ (a, c) (b, c) := by
          simpa [Complex.equivRealProdCLM_symm_apply, Complex.mk_eq_add_mul_I] using
            (image_segment ℝ
              (Complex.equivRealProdCLM.symm.toLinearEquiv.toAffineMap)
              (a, c) (b, c)).symm
    _ = Complex.equivRealProdCLM.symm '' ((fun x : ℝ => (x, c)) '' Icc a b) := by
          rw [hprod]
    _ = {z : ℂ | z.re ∈ Icc a b ∧ z.im = c} := by
          ext z
          change z ∈ Complex.equivRealProd.symm '' ((fun x : ℝ => (x, c)) '' Icc a b) ↔ _
          rw [Equiv.image_eq_preimage_symm]
          simp [Complex.equivRealProd_apply, eq_comm]

private theorem vertical_segment_interval (a c d : ℝ) (hcd : c ≤ d) :
    segment ℝ (Complex.mk a c) (Complex.mk a d) =
      {z : ℂ | z.re = a ∧ z.im ∈ Icc c d} := by
  have hprod : (fun y : ℝ => (a, y)) '' Icc c d =
      segment ℝ (a, c) (a, d) := by
    rw [← segment_eq_Icc hcd]
    exact Prod.image_mk_segment_right a c d
  calc
    segment ℝ (Complex.mk a c) (Complex.mk a d) =
        Complex.equivRealProdCLM.symm '' segment ℝ (a, c) (a, d) := by
          simpa [Complex.equivRealProdCLM_symm_apply, Complex.mk_eq_add_mul_I] using
            (image_segment ℝ
              (Complex.equivRealProdCLM.symm.toLinearEquiv.toAffineMap)
              (a, c) (a, d)).symm
    _ = Complex.equivRealProdCLM.symm '' ((fun y : ℝ => (a, y)) '' Icc c d) := by
          rw [hprod]
    _ = {z : ℂ | z.re = a ∧ z.im ∈ Icc c d} := by
          ext z
          change z ∈ Complex.equivRealProd.symm '' ((fun y : ℝ => (a, y)) '' Icc c d) ↔ _
          rw [Equiv.image_eq_preimage_symm]
          simp [Complex.equivRealProd_apply, eq_comm, and_comm]

/-- Clipping an ordered horizontal segment by a closed coordinate box. -/
private theorem horizontalSegment_inter_closedAxisBox
    (a b c x₀ x₁ y₀ y₁ : ℝ)
    (hab : a ≤ b) (hlo : max a x₀ ≤ min b x₁)
    (hc : c ∈ Icc y₀ y₁) :
    segment ℝ (Complex.mk a c) (Complex.mk b c) ∩
        IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁ =
      segment ℝ (Complex.mk (max a x₀) c)
        (Complex.mk (min b x₁) c) := by
  rw [horizontal_segment_interval a b c hab,
    horizontal_segment_interval (max a x₀) (min b x₁) c hlo]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    IntrinsicVertices.closedAxisBox, Set.mem_Icc]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, him⟩, ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩⟩
    constructor
    · constructor
      · exact max_le ha hx₀
      · exact le_min hb hx₁
    · exact him
  · rintro ⟨⟨hlo', hhi'⟩, him⟩
    refine ⟨⟨⟨?_, ?_⟩, him⟩, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · exact le_trans (le_max_left _ _) hlo'
    · exact le_trans hhi' (min_le_left _ _)
    · exact le_trans (le_max_right _ _) hlo'
    · exact le_trans hhi' (min_le_right _ _)
    · simpa [him] using hc

/-- A point of the original segment in the box interior forces its clip to
remain nondegenerate, even when that point is an endpoint of the segment. -/
private theorem horizontalSegment_nontrivial_clip
    (a b c x₀ x₁ y₀ y₁ : ℝ)
    (hab : a < b) (hx : x₀ < x₁) (_hy : y₀ < y₁)
    {z : ℂ}
    (hzseg : z ∈ segment ℝ (Complex.mk a c) (Complex.mk b c))
    (hzbox : z ∈ interior (IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁)) :
    max a x₀ < min b x₁ := by
  have hzseg' := (Set.ext_iff.mp
    (horizontal_segment_interval a b c hab.le) z).mp hzseg
  have hzbox' : z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁ := by
    change z ∈ interior (Icc x₀ x₁ ×ℂ Icc y₀ y₁) at hzbox
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc] at hzbox
    exact hzbox
  rcases hzseg' with ⟨⟨ha, hb⟩, _⟩
  rcases hzbox'.1 with ⟨hx₀, hx₁⟩
  exact max_lt (lt_min hab (ha.trans_lt hx₁))
    (lt_min (hx₀.trans_le hb) hx)

/-- Clipping an ordered vertical segment by a closed coordinate box. -/
private theorem verticalSegment_inter_closedAxisBox
    (a c d x₀ x₁ y₀ y₁ : ℝ)
    (hcd : c ≤ d) (hlo : max c y₀ ≤ min d y₁)
    (ha : a ∈ Icc x₀ x₁) :
    segment ℝ (Complex.mk a c) (Complex.mk a d) ∩
        IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁ =
      segment ℝ (Complex.mk a (max c y₀))
        (Complex.mk a (min d y₁)) := by
  rw [vertical_segment_interval a c d hcd,
    vertical_segment_interval a (max c y₀) (min d y₁) hlo]
  ext z
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    IntrinsicVertices.closedAxisBox, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hre, ⟨hc, hd⟩⟩, ⟨⟨hx₀, hx₁⟩, ⟨hy₀, hy₁⟩⟩⟩
    exact ⟨hre, ⟨max_le hc hy₀, le_min hd hy₁⟩⟩
  · rintro ⟨hre, ⟨hlo', hhi'⟩⟩
    refine ⟨⟨hre, ⟨?_, ?_⟩⟩, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · exact le_trans (le_max_left _ _) hlo'
    · exact le_trans hhi' (min_le_left _ _)
    · simpa [hre] using ha
    · exact le_trans (le_max_right _ _) hlo'
    · exact le_trans hhi' (min_le_right _ _)

/-- The vertical clip remains nondegenerate at any original segment point
strictly inside the box. -/
private theorem verticalSegment_nontrivial_clip
    (a c d x₀ x₁ y₀ y₁ : ℝ)
    (hcd : c < d) (_hx : x₀ < x₁) (hy : y₀ < y₁)
    {z : ℂ}
    (hzseg : z ∈ segment ℝ (Complex.mk a c) (Complex.mk a d))
    (hzbox : z ∈ interior (IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁)) :
    max c y₀ < min d y₁ := by
  have hzseg' := (Set.ext_iff.mp
    (vertical_segment_interval a c d hcd.le) z).mp hzseg
  have hzbox' : z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁ := by
    change z ∈ interior (Icc x₀ x₁ ×ℂ Icc y₀ y₁) at hzbox
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc] at hzbox
    exact hzbox
  rcases hzseg' with ⟨_, ⟨hc, hd⟩⟩
  rcases hzbox'.2 with ⟨hy₀, hy₁⟩
  exact max_lt (lt_min hcd (hc.trans_lt hy₁))
    (lt_min (hy₀.trans_le hd) hy)

/-- An axis segment containing a point in the interior of a coordinate box
has a nondegenerate closed-axis-segment clip by that box. -/
theorem axisSegment_inter_closedAxisBox_of_interiorPoint
    {u v z : ℂ} {x₀ x₁ y₀ y₁ : ℝ}
    (huv : u ≠ v) (haxis : u.re = v.re ∨ u.im = v.im)
    (hx : x₀ < x₁) (hy : y₀ < y₁)
    (hzseg : z ∈ segment ℝ u v)
    (hzbox : z ∈ interior (IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁)) :
    ∃ p q : ℂ, p ≠ q ∧ (p.re = q.re ∨ p.im = q.im) ∧
      segment ℝ u v ∩ IntrinsicVertices.closedAxisBox x₀ x₁ y₀ y₁ =
        segment ℝ p q := by
  have hzbox' : z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁ := by
    change z ∈ interior (Icc x₀ x₁ ×ℂ Icc y₀ y₁) at hzbox
    rw [Complex.interior_reProdIm, interior_Icc, interior_Icc] at hzbox
    exact hzbox
  rcases haxis with hre | him
  · have himne : u.im ≠ v.im := by
      intro h
      exact huv (Complex.ext hre h)
    rcases lt_or_gt_of_ne himne with hcd | hdc
    · have hrepr : segment ℝ u v =
          segment ℝ (Complex.mk u.re u.im) (Complex.mk u.re v.im) := by
        congr 1; apply Complex.ext <;> simp [hre]
      have hstrict : max u.im y₀ < min v.im y₁ :=
        verticalSegment_nontrivial_clip u.re u.im v.im x₀ x₁ y₀ y₁
          hcd hx hy (hrepr ▸ hzseg) hzbox
      have hzfixed : z.re = u.re :=
        ((Set.ext_iff.mp (vertical_segment_interval u.re u.im v.im hcd.le) z).mp
          (hrepr ▸ hzseg)).1
      have hclip := verticalSegment_inter_closedAxisBox u.re u.im v.im
        x₀ x₁ y₀ y₁ hcd.le hstrict.le
        ⟨by rw [← hzfixed]; exact hzbox'.1.1.le,
          by rw [← hzfixed]; exact hzbox'.1.2.le⟩
      refine ⟨Complex.mk u.re (max u.im y₀),
        Complex.mk u.re (min v.im y₁), ?_, Or.inl rfl, ?_⟩
      · intro h
        exact hstrict.ne (by simpa using congrArg Complex.im h)
      · rw [hrepr]
        exact hclip
    · have hrepr : segment ℝ u v =
          segment ℝ (Complex.mk v.re v.im) (Complex.mk v.re u.im) := by
        rw [segment_symm]
        congr 1; apply Complex.ext <;> simp [hre]
      have hstrict : max v.im y₀ < min u.im y₁ :=
        verticalSegment_nontrivial_clip v.re v.im u.im x₀ x₁ y₀ y₁
          hdc hx hy (hrepr ▸ hzseg) hzbox
      have hzfixed : z.re = v.re :=
        ((Set.ext_iff.mp (vertical_segment_interval v.re v.im u.im hdc.le) z).mp
          (hrepr ▸ hzseg)).1
      have hclip := verticalSegment_inter_closedAxisBox v.re v.im u.im
        x₀ x₁ y₀ y₁ hdc.le hstrict.le
        ⟨by rw [← hzfixed]; exact hzbox'.1.1.le,
          by rw [← hzfixed]; exact hzbox'.1.2.le⟩
      refine ⟨Complex.mk v.re (max v.im y₀),
        Complex.mk v.re (min u.im y₁), ?_, Or.inl rfl, ?_⟩
      · intro h
        exact hstrict.ne (by simpa using congrArg Complex.im h)
      · rw [hrepr]
        exact hclip
  · have hrene : u.re ≠ v.re := by
      intro h
      exact huv (Complex.ext h him)
    rcases lt_or_gt_of_ne hrene with hab | hba
    · have hrepr : segment ℝ u v =
          segment ℝ (Complex.mk u.re u.im) (Complex.mk v.re u.im) := by
        congr 1; apply Complex.ext <;> simp [him]
      have hstrict : max u.re x₀ < min v.re x₁ :=
        horizontalSegment_nontrivial_clip u.re v.re u.im x₀ x₁ y₀ y₁
          hab hx hy (hrepr ▸ hzseg) hzbox
      have hzfixed : z.im = u.im :=
        ((Set.ext_iff.mp (horizontal_segment_interval u.re v.re u.im hab.le) z).mp
          (hrepr ▸ hzseg)).2
      have hclip := horizontalSegment_inter_closedAxisBox u.re v.re u.im
        x₀ x₁ y₀ y₁ hab.le hstrict.le
        ⟨by rw [← hzfixed]; exact hzbox'.2.1.le,
          by rw [← hzfixed]; exact hzbox'.2.2.le⟩
      refine ⟨Complex.mk (max u.re x₀) u.im,
        Complex.mk (min v.re x₁) u.im, ?_, Or.inr rfl, ?_⟩
      · intro h
        exact hstrict.ne (by simpa using congrArg Complex.re h)
      · rw [hrepr]
        exact hclip
    · have hrepr : segment ℝ u v =
          segment ℝ (Complex.mk v.re v.im) (Complex.mk u.re v.im) := by
        rw [segment_symm]
        congr 1; apply Complex.ext <;> simp [him]
      have hstrict : max v.re x₀ < min u.re x₁ :=
        horizontalSegment_nontrivial_clip v.re u.re v.im x₀ x₁ y₀ y₁
          hba hx hy (hrepr ▸ hzseg) hzbox
      have hzfixed : z.im = v.im :=
        ((Set.ext_iff.mp (horizontal_segment_interval v.re u.re v.im hba.le) z).mp
          (hrepr ▸ hzseg)).2
      have hclip := horizontalSegment_inter_closedAxisBox v.re u.re v.im
        x₀ x₁ y₀ y₁ hba.le hstrict.le
        ⟨by rw [← hzfixed]; exact hzbox'.2.1.le,
          by rw [← hzfixed]; exact hzbox'.2.2.le⟩
      refine ⟨Complex.mk (max v.re x₀) v.im,
        Complex.mk (min u.re x₁) v.im, ?_, Or.inr rfl, ?_⟩
      · intro h
        exact hstrict.ne (by simpa using congrArg Complex.re h)
      · rw [hrepr]
        exact hclip

end Tiling.AxisParallel
