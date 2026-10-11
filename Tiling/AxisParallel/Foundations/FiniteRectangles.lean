import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.Geometry.LocalLine

/-!
# Finite rectangles and polygonal boundaries

Grid cells convert a bounded open set with finite axis-parallel boundary into a
finite union of rectangles. For regular-open nonempty sets, taking the interior
of that union is exactly the paper's finite-boundary description.
-/

set_option autoImplicit false

open Bornology MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.FiniteRectangles

open Tiling.AxisParallel.IntrinsicVertices (consecutiveLevelPairs)

theorem frontier_finset_union_subset {ι : Type*} (F : Finset ι)
    (f : ι → Set Plane) :
    frontier (⋃ i ∈ F, f i) ⊆ ⋃ i ∈ F, frontier (f i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    simp only [Finset.set_biUnion_insert]
    exact (frontier_union_subset _ _).trans
      (Set.union_subset_union inter_subset_left (inter_subset_right.trans ih))

theorem interior_isRegularOpen_of_isClosed {U : Set Plane} (hU : IsClosed U) :
    interior (closure (interior U)) = interior U := by
  apply subset_antisymm
  · exact interior_mono (closure_minimal interior_subset hU)
  · exact isOpen_interior.subset_interior_closure

def box (p q : ℝ × ℝ) : Set Plane := Icc p.1 p.2 ×ℂ Icc q.1 q.2

def cell (p q : ℝ × ℝ) : Set Plane := Ioo p.1 p.2 ×ℂ Ioo q.1 q.2

theorem box_frontier_axes {p q : ℝ × ℝ} {z : Plane}
    (hz : z ∈ frontier (box p q)) :
    z.re = p.1 ∨ z.re = p.2 ∨ z.im = q.1 ∨ z.im = q.2 := by
  by_cases hp : p.1 ≤ p.2
  · by_cases hq : q.1 ≤ q.2
    · rw [box, Complex.frontier_reProdIm] at hz
      rcases hz with hz | hz
      · have hy : z.im = q.1 ∨ z.im = q.2 := by
          simpa [frontier_Icc hq] using hz.2
        exact Or.inr (Or.inr hy)
      · have hx : z.re = p.1 ∨ z.re = p.2 := by
          simpa [frontier_Icc hp] using hz.1
        exact hx.imp_right (fun h => Or.inl h)
    · simp [box, Icc_eq_empty_of_lt (lt_of_not_ge hq), Complex.reProdIm] at hz
  · simp [box, Icc_eq_empty_of_lt (lt_of_not_ge hp), Complex.reProdIm] at hz

theorem pair_data {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) :
    p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 := by
  classical
  simpa [consecutiveLevelPairs] using
    (show p.1 ∈ s ∧ p.2 ∈ s ∧ p.1 < p.2 from by
      rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨hp.1.1, hp.1.2, hp.2.1⟩)

theorem box_isRectangle {p q : ℝ × ℝ} (hp : p.1 < p.2) (hq : q.1 < q.2) :
    Tiling.IsRectangle (box p q) := by
  refine ⟨Complex.mk p.1 q.1, Complex.mk p.2 q.2, ne_of_lt hp, ne_of_lt hq, ?_⟩
  simp [box, Complex.Rectangle, uIcc_of_le hp.le, uIcc_of_le hq.le]

theorem interior_box (p q : ℝ × ℝ) : interior (box p q) = cell p q := by
  simp [box, cell, Complex.interior_reProdIm, interior_Icc]

theorem closure_cell {p q : ℝ × ℝ} (hp : p.1 < p.2) (hq : q.1 < q.2) :
    closure (cell p q) = box p q := by
  simp [box, cell, Complex.closure_reProdIm, closure_Ioo hp.ne, closure_Ioo hq.ne]

theorem cell_preconnected (p q : ℝ × ℝ) : IsPreconnected (cell p q) := by
  have hconv : Convex ℝ (cell p q) :=
    (convex_Ioo p.1 p.2).linear_preimage Complex.reLm |>.inter
      ((convex_Ioo q.1 q.2).linear_preimage Complex.imLm)
  exact hconv.isPreconnected

theorem pair_around {s : Finset ℝ} {x : ℝ}
    (hx : x ∉ s) (hl : ∃ a ∈ s, a < x) (hu : ∃ b ∈ s, x < b) :
    ∃ a b, (a, b) ∈ consecutiveLevelPairs s ∧ x ∈ Ioo a b := by
  classical
  let L : Set ℝ := {a | a ∈ s ∧ a < x}
  let U : Set ℝ := {b | b ∈ s ∧ x < b}
  have hLfin : L.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  have hUfin : U.Finite := s.finite_toSet.subset (by intro z hz; exact hz.1)
  obtain ⟨a, haL, hamax⟩ := Set.exists_max_image L id hLfin hl
  obtain ⟨b, hbU, hbmin⟩ := Set.exists_min_image U id hUfin hu
  refine ⟨a, b, ?_, haL.2, hbU.2⟩
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨haL.1, hbU.1⟩, haL.2.trans hbU.2, ?_⟩
  intro z hzs hzbetween
  by_cases hzx : z < x
  · exact (not_lt_of_ge (hamax z ⟨hzs, hzx⟩)) hzbetween.1
  · have hxz : x < z := lt_of_le_of_ne (le_of_not_gt hzx) (Ne.symm (by
      intro h; apply hx; simpa [h] using hzs))
    exact (not_lt_of_ge (hbmin z ⟨hzs, hxz⟩)) hzbetween.2

theorem pair_avoids_levels {s : Finset ℝ} {p : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) {x : ℝ} (hx : x ∈ Ioo p.1 p.2) : x ∉ s := by
  classical
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp
  exact fun hxs => hp.2.2 x hxs hx

theorem pair_intervals_disjoint {s : Finset ℝ} {p q : ℝ × ℝ}
    (hp : p ∈ consecutiveLevelPairs s) (hq : q ∈ consecutiveLevelPairs s)
    (hpq : p ≠ q) : Disjoint (Ioo p.1 p.2) (Ioo q.1 q.2) := by
  classical
  rw [consecutiveLevelPairs, Finset.mem_filter, Finset.mem_product] at hp hq
  rw [Set.disjoint_left]
  intro z hzp hzq
  have hleft : p.1 = q.1 := by
    rcases lt_trichotomy p.1 q.1 with h | h | h
    · exact (hp.2.2 q.1 hq.1.1 ⟨h, hzq.1.trans hzp.2⟩).elim
    · exact h
    · exact (hq.2.2 p.1 hp.1.1 ⟨h, hzp.1.trans hzq.2⟩).elim
  have hright : p.2 = q.2 := by
    rcases lt_trichotomy p.2 q.2 with h | h | h
    · exact (hq.2.2 p.2 hp.1.2 ⟨hzq.1.trans hzp.2, h⟩).elim
    · exact h
    · exact (hp.2.2 q.2 hq.1.2 ⟨hzp.1.trans hzq.2, h⟩).elim
  exact hpq (Prod.ext hleft hright)

def offGrid (s t : Finset ℝ) : Set Plane := {z | z.re ∉ s ∧ z.im ∉ t}

theorem offGrid_dense (s t : Finset ℝ) : Dense (offGrid s t) := by
  have hs := (s.finite_toSet.countable.dense_compl ℝ).preimage Complex.isOpenMap_re
  have ht := (t.finite_toSet.countable.dense_compl ℝ).preimage Complex.isOpenMap_im
  have htop : IsOpen (Complex.im ⁻¹' (↑t : Set ℝ)ᶜ) :=
    t.finite_toSet.isClosed.isOpen_compl.preimage Complex.continuous_im
  exact hs.inter_of_isOpen_right ht htop

theorem cell_inside_of_meets {Ω : Set Plane} (hopen : IsOpen Ω)
    (s t : Finset ℝ) (hfront : ∀ z ∈ frontier Ω, z.re ∈ s ∨ z.im ∈ t)
    {p q : ℝ × ℝ} (hp : p ∈ consecutiveLevelPairs s)
    (hq : q ∈ consecutiveLevelPairs t) (hne : (cell p q ∩ Ω).Nonempty) :
    cell p q ⊆ Ω := by
  have hdisj : Disjoint (cell p q) (frontier Ω) := by
    refine Set.disjoint_left.mpr fun z hz hzf => ?_
    rcases hfront z hzf with hx | hy
    · exact pair_avoids_levels hp hz.1 hx
    · exact pair_avoids_levels hq hz.2 hy
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      (cell_preconnected p q) hdisj with hin | hout
  · simpa [hopen.interior_eq] using hin
  · obtain ⟨z, hz, hzΩ⟩ := hne
    exact (interior_subset (hout hz) hzΩ).elim

theorem boxes_aedisjoint {p q p' q' : ℝ × ℝ}
    (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hp' : p'.1 < p'.2) (hq' : q'.1 < q'.2)
    (hdisj : Disjoint (cell p q) (cell p' q')) :
    AEDisjoint volume (box p q) (box p' q') := by
  change volume (box p q ∩ box p' q') = 0
  apply measure_mono_null ?_
    (measure_union_null (box_isRectangle hp hq).isPolygonal.volume_frontier
      (box_isRectangle hp' hq').isPolygonal.volume_frontier)
  intro z hz
  by_cases hzint : z ∈ interior (box p q)
  · right
    rw [(box_isRectangle hp' hq').isPolygonal.isClosed.frontier_eq]
    refine ⟨hz.2, ?_⟩
    intro hzint'
    exact Set.disjoint_left.mp hdisj
      (by simpa [interior_box] using hzint)
      (by simpa [interior_box] using hzint')
  · left
    rw [(box_isRectangle hp hq).isPolygonal.isClosed.frontier_eq]
    exact ⟨hz.1, hzint⟩

theorem rectangulation_of_grid {Ω : Set Plane} (hopen : IsOpen Ω)
    (hbounded : IsBounded Ω) (s t : Finset ℝ)
    (hfront : ∀ z ∈ frontier Ω, z.re ∈ s ∨ z.im ∈ t) :
    Tiling.IsAxisParallel (closure Ω) := by
  classical
  obtain ⟨R, hR⟩ := hbounded.subset_closedBall (0 : Plane)
  let B := |R| + 1
  have hbounds (z : Plane) (hz : z ∈ Ω) :
      -B < z.re ∧ z.re < B ∧ -B < z.im ∧ z.im < B := by
    have hn : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall] using hR hz
    have hre := (Complex.abs_re_le_norm z).trans hn
    have him := (Complex.abs_im_le_norm z).trans hn
    have habs := le_abs_self R
    dsimp [B]
    rcases abs_le.mp hre with ⟨hrel, hrer⟩
    rcases abs_le.mp him with ⟨himl, himr⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  let s' := insert (-B) (insert B s)
  let t' := insert (-B) (insert B t)
  have hs : s ⊆ s' := by intro a ha; simp [s', ha]
  have ht : t ⊆ t' := by intro a ha; simp [t', ha]
  have hfront' : ∀ z ∈ frontier Ω, z.re ∈ s' ∨ z.im ∈ t' := by
    intro z hz
    exact (hfront z hz).imp (fun h => hs h) (fun h => ht h)
  let P := ((consecutiveLevelPairs s' ×ˢ consecutiveLevelPairs t').filter
    fun pq => (cell pq.1 pq.2 ∩ Ω).Nonempty)
  let pieces := P.image fun pq => box pq.1 pq.2
  have hdata {pq : (ℝ × ℝ) × (ℝ × ℝ)} (hpq : pq ∈ P) :
      pq.1 ∈ consecutiveLevelPairs s' ∧ pq.2 ∈ consecutiveLevelPairs t' ∧
        (cell pq.1 pq.2 ∩ Ω).Nonempty := by
    simpa only [P, Finset.mem_filter, Finset.mem_product, and_assoc] using hpq
  have hrect {pq : (ℝ × ℝ) × (ℝ × ℝ)} (hpq : pq ∈ P) :
      Tiling.IsRectangle (box pq.1 pq.2) :=
    box_isRectangle (pair_data (hdata hpq).1).2.2 (pair_data (hdata hpq).2.1).2.2
  have hsub {pq : (ℝ × ℝ) × (ℝ × ℝ)} (hpq : pq ∈ P) :
      box pq.1 pq.2 ⊆ closure Ω := by
    obtain ⟨hp, hq, hne⟩ := hdata hpq
    rw [← closure_cell (pair_data hp).2.2 (pair_data hq).2.2]
    exact closure_mono (cell_inside_of_meets hopen s' t' hfront' hp hq hne)
  have hclosed : IsClosed (⋃ pq ∈ P, box pq.1 pq.2) :=
    P.finite_toSet.isClosed_biUnion fun pq hpq => (hrect hpq).isPolygonal.isClosed
  have hoff : Ω ∩ offGrid s' t' ⊆ ⋃ pq ∈ P, box pq.1 pq.2 := by
    rintro z ⟨hz, hx, hy⟩
    obtain ⟨xa, xb, hxp, hxmem⟩ := pair_around hx
      ⟨-B, by simp [s'], (hbounds z hz).1⟩
      ⟨B, by simp [s'], (hbounds z hz).2.1⟩
    obtain ⟨ya, yb, hyp, hymem⟩ := pair_around hy
      ⟨-B, by simp [t'], (hbounds z hz).2.2.1⟩
      ⟨B, by simp [t'], (hbounds z hz).2.2.2⟩
    refine mem_iUnion.mpr ⟨((xa, xb), (ya, yb)), mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · simp only [P, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hxp, hyp⟩, z, ⟨hxmem, hymem⟩, hz⟩
    · exact ⟨⟨hxmem.1.le, hxmem.2.le⟩, hymem.1.le, hymem.2.le⟩
  have hΩsub : Ω ⊆ ⋃ pq ∈ P, box pq.1 pq.2 :=
    ((offGrid_dense s' t').open_subset_closure_inter hopen).trans
      (closure_minimal hoff hclosed)
  have hunion : (⋃ pq ∈ P, box pq.1 pq.2) = closure Ω := by
    apply subset_antisymm
    · intro z hz
      obtain ⟨pq, hpq⟩ := mem_iUnion.mp hz
      obtain ⟨hpq, hzbox⟩ := mem_iUnion.mp hpq
      exact hsub hpq hzbox
    · exact closure_minimal hΩsub hclosed
  refine ⟨{ pieces := pieces
            isRectangle := ?_
            pairwiseAEDisjoint := ?_
            sUnion_eq := ?_ }⟩
  · intro r hr
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hr
    exact hrect hpq
  · intro r hr u hu hru
    obtain ⟨pq, hpq, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨pq', hpq', rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hp, hq, _⟩ := hdata hpq
    obtain ⟨hp', hq', _⟩ := hdata hpq'
    apply boxes_aedisjoint (pair_data hp).2.2 (pair_data hq).2.2
      (pair_data hp').2.2 (pair_data hq').2.2
    have hpqne : pq ≠ pq' := fun h => hru (congrArg (fun v => box v.1 v.2) h)
    by_cases hpeq : pq.1 = pq'.1
    · have hqne : pq.2 ≠ pq'.2 := fun h => hpqne (Prod.ext hpeq h)
      exact Set.disjoint_left.mpr fun z hz hz' =>
        Set.disjoint_left.mp (pair_intervals_disjoint hq hq' hqne) hz.2 hz'.2
    · exact Set.disjoint_left.mpr fun z hz hz' =>
        Set.disjoint_left.mp (pair_intervals_disjoint hp hp' hpeq) hz.1 hz'.1
  · rw [← hunion]
    ext z
    simp only [pieces, Set.mem_sUnion, Finset.mem_coe, Finset.mem_image, mem_iUnion]
    constructor
    · rintro ⟨r, ⟨pq, hpq, rfl⟩, hz⟩
      exact ⟨pq, hpq, hz⟩
    · rintro ⟨pq, hpq, hz⟩
      exact ⟨box pq.1 pq.2, ⟨pq, hpq, rfl⟩, hz⟩

def orderedBox (a b : Plane) : Set Plane := box (a.re, b.re) (a.im, b.im)

theorem orderedBox_isClosed (a b : Plane) : IsClosed (orderedBox a b) :=
  isClosed_Icc.reProdIm isClosed_Icc

theorem orderedBox_isBounded (a b : Plane) : IsBounded (orderedBox a b) :=
  isCompact_Icc.isBounded.reProdIm isCompact_Icc.isBounded

theorem finite_boxes_frontier_axisLines (F : Finset (Plane × Plane)) :
    ∃ s t : Finset ℝ, ∀ z ∈ frontier (⋃ r ∈ F, orderedBox r.1 r.2),
      z.re ∈ s ∨ z.im ∈ t := by
  classical
  let s := F.biUnion fun r => {r.1.re, r.2.re}
  let t := F.biUnion fun r => {r.1.im, r.2.im}
  refine ⟨s, t, ?_⟩
  intro z hz
  have hz' := frontier_finset_union_subset F (fun r => orderedBox r.1 r.2) hz
  obtain ⟨r, hr⟩ := mem_iUnion.mp hz'
  obtain ⟨hr, hzr⟩ := mem_iUnion.mp hr
  rcases box_frontier_axes hzr with hx | hx | hy | hy
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨r, hr, by simp [hx]⟩)
  · exact Or.inl (Finset.mem_biUnion.mpr ⟨r, hr, by simp [hx]⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨r, hr, by simp [hy]⟩)
  · exact Or.inr (Finset.mem_biUnion.mpr ⟨r, hr, by simp [hy]⟩)

theorem finite_boxes_union_isClosed (F : Finset (Plane × Plane)) :
    IsClosed (⋃ r ∈ F, orderedBox r.1 r.2) :=
  F.finite_toSet.isClosed_biUnion fun r _ => orderedBox_isClosed r.1 r.2

theorem finite_boxes_union_isBounded (F : Finset (Plane × Plane)) :
    IsBounded (⋃ r ∈ F, orderedBox r.1 r.2) :=
  (isBounded_biUnion_finset F).mpr fun r _ => orderedBox_isBounded r.1 r.2

theorem finite_boxes_carrier_axisLines (F : Finset (Plane × Plane)) :
    ∃ s t : Finset ℝ, ∀ z ∈ frontier (interior (⋃ r ∈ F, orderedBox r.1 r.2)),
      z.re ∈ s ∨ z.im ∈ t := by
  obtain ⟨s, t, hfront⟩ := finite_boxes_frontier_axisLines F
  exact ⟨s, t, fun z hz => hfront z (frontier_interior_subset hz)⟩

theorem finite_boxes_carrier_rectangulated (F : Finset (Plane × Plane)) :
    Tiling.IsAxisParallel (closure (interior (⋃ r ∈ F, orderedBox r.1 r.2))) := by
  obtain ⟨s, t, hfront⟩ := finite_boxes_carrier_axisLines F
  exact rectangulation_of_grid isOpen_interior
    ((finite_boxes_union_isBounded F).subset interior_subset) s t hfront

theorem region_rectangle_presentation (K : Tiling.AxisParallel.Region) :
    ∃ F : Finset (Plane × Plane), K.support = ⋃ r ∈ F, orderedBox r.1 r.2 := by
  classical
  obtain ⟨R⟩ := K.isAxisParallel
  choose a b hre him heq using fun r : ↥R.pieces => R.isRectangle r.1 r.2
  let lower (r : ↥R.pieces) : Plane :=
    ⟨min (a r).re (b r).re, min (a r).im (b r).im⟩
  let upper (r : ↥R.pieces) : Plane :=
    ⟨max (a r).re (b r).re, max (a r).im (b r).im⟩
  let F := Finset.univ.image fun r : ↥R.pieces => (lower r, upper r)
  have hbox (r : ↥R.pieces) : orderedBox (lower r) (upper r) = r.1 := by
    rw [heq r]
    rfl
  refine ⟨F, ?_⟩
  rw [← R.sUnion_eq]
  ext z
  constructor
  · rintro ⟨r, hr, hzr⟩
    refine mem_iUnion.mpr ⟨(lower ⟨r, hr⟩, upper ⟨r, hr⟩), mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨⟨r, hr⟩, Finset.mem_univ _, rfl⟩
    · simpa only [hbox] using hzr
  · rintro hz
    obtain ⟨r, hr⟩ := mem_iUnion.mp hz
    obtain ⟨hr, hzr⟩ := mem_iUnion.mp hr
    obtain ⟨r', _, rfl⟩ := Finset.mem_image.mp hr
    exact ⟨r'.1, r'.2, (hbox r') ▸ hzr⟩

theorem region_finite_axis_boundary (K : Tiling.AxisParallel.Region) :
    ∃ edges : Set (Plane × Plane), edges.Finite ∧
      (∀ e ∈ edges, e.1 ≠ e.2 ∧ (e.1.re = e.2.re ∨ e.1.im = e.2.im)) ∧
      frontier K.openCarrier = ⋃ e ∈ edges, segment ℝ e.1 e.2 := by
  classical
  obtain ⟨G, hG, hsegments, hcover⟩ := K.exists_finite_frontier_intrinsicSegments
  let : Fintype ↥G := hG.fintype
  choose a b hne halign heq hsub using fun g : ↥G => hsegments g.1 g.2
  let E := (fun g : ↥G => (a g, b g)) '' univ
  have hfront : frontier K.openCarrier = ⋃₀ G := by
    exact K.frontier_openCarrier_eq_frontier_support.trans hcover
  refine ⟨E, (Set.finite_univ.image _), ?_, ?_⟩
  · rintro e ⟨g, _, rfl⟩
    exact ⟨hne g, halign g⟩
  · rw [hfront]
    ext z
    constructor
    · rintro ⟨g, hg, hz⟩
      refine mem_iUnion.mpr ⟨(a ⟨g, hg⟩, b ⟨g, hg⟩), mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact ⟨⟨g, hg⟩, mem_univ _, rfl⟩
      · rwa [← heq ⟨g, hg⟩]
    · intro hz
      obtain ⟨e, he⟩ := mem_iUnion.mp hz
      obtain ⟨⟨g, _, rfl⟩, hz⟩ := mem_iUnion.mp he
      exact ⟨g.1, g.2, (heq g).symm ▸ hz⟩

theorem finite_rectangle_presentation_iff_boundary (Ω : Set Plane) (hne : Ω.Nonempty) :
    (∃ F : Finset (Plane × Plane), Ω = interior (⋃ r ∈ F, orderedBox r.1 r.2)) ↔
      interior (closure Ω) = Ω ∧ IsBounded Ω ∧
        ∃ edges : Set (Plane × Plane), edges.Finite ∧
          (∀ e ∈ edges, e.1 ≠ e.2 ∧ (e.1.re = e.2.re ∨ e.1.im = e.2.im)) ∧
          frontier Ω = ⋃ e ∈ edges, segment ℝ e.1 e.2 := by
  constructor
  · rintro ⟨F, rfl⟩
    have hregular := interior_isRegularOpen_of_isClosed (finite_boxes_union_isClosed F)
    have haxis := finite_boxes_carrier_rectangulated F
    let K : Region := {
      support := closure (interior (⋃ r ∈ F, orderedBox r.1 r.2))
      isPolygonal := IntrinsicVertices.isPolygonal_of_isAxisParallel haxis
      nonempty := hne.mono subset_closure
      isAxisParallel := haxis }
    refine ⟨hregular, (finite_boxes_union_isBounded F).subset interior_subset, ?_⟩
    have hcarrier : K.openCarrier = interior (⋃ r ∈ F, orderedBox r.1 r.2) := hregular
    simpa only [hcarrier] using region_finite_axis_boundary K
  · rintro ⟨hregular, hbounded, E, hE, hedge, hfront⟩
    classical
    let s := hE.toFinset.image fun e => e.1.re
    let t := hE.toFinset.image fun e => e.1.im
    have hlines : ∀ z ∈ frontier Ω, z.re ∈ s ∨ z.im ∈ t := by
      intro z hz
      rw [hfront] at hz
      obtain ⟨e, hz⟩ := mem_iUnion.mp hz
      obtain ⟨he, hz⟩ := mem_iUnion.mp hz
      rcases (hedge e he).2 with hre | him
      · have hzre : z.re = e.1.re :=
          (convex_hyperplane Complex.reLm.isLinear e.1.re).segment_subset
            rfl hre.symm hz
        exact Or.inl (Finset.mem_image.mpr ⟨e, hE.mem_toFinset.mpr he, hzre.symm⟩)
      · have hzim : z.im = e.1.im :=
          (convex_hyperplane Complex.imLm.isLinear e.1.im).segment_subset
            rfl him.symm hz
        exact Or.inr (Finset.mem_image.mpr ⟨e, hE.mem_toFinset.mpr he, hzim.symm⟩)
    have hopen : IsOpen Ω := hregular ▸ isOpen_interior
    have haxis := rectangulation_of_grid hopen hbounded s t hlines
    let K : Region := {
      support := closure Ω
      isPolygonal := IntrinsicVertices.isPolygonal_of_isAxisParallel haxis
      nonempty := hne.mono subset_closure
      isAxisParallel := haxis }
    obtain ⟨F, hF⟩ := region_rectangle_presentation K
    exact ⟨F, hregular.symm.trans (congrArg interior hF)⟩

end Tiling.AxisParallel.FiniteRectangles
