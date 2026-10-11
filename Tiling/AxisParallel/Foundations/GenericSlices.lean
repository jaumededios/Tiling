import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.OneDimensional.Core
import Tiling.AxisParallel.OneDimensional.FiniteInterval.IntervalGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set Topology

noncomputable section

namespace Tiling.AxisParallel.Foundations.GenericSlices

open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional


/-- Horizontal fibre, parametrized by the fixed imaginary coordinate. -/
def horizontalSlice (K : Region) (y : ℝ) : Set ℝ :=
  {x : ℝ | Complex.mk x y ∈ K.openCarrier}

/-- Vertical fibre, parametrized by the fixed real coordinate. -/
def verticalSlice (K : Region) (x : ℝ) : Set ℝ :=
  {y : ℝ | Complex.mk x y ∈ K.openCarrier}

/-- A generic horizontal fibre with intrinsic tile vertices at every maximal
component endpoint. -/
structure HorizontalGenericSlicePresentation (K : Region) (y : ℝ)
    extends MaximalIntervalPresentation (horizontalSlice K y) where
  generic : ∀ v : ↥K.vertices, v.1.im ≠ y
  leftVertex : Fin n → ↥K.vertices
  rightVertex : Fin n → ↥K.vertices
  leftVertex_coord : ∀ i, (leftVertex i).1.re = left i
  rightVertex_coord : ∀ i, (rightVertex i).1.re = right i

/-- A generic vertical fibre with intrinsic tile vertices at every maximal
component endpoint. -/
structure VerticalGenericSlicePresentation (K : Region) (x : ℝ)
    extends MaximalIntervalPresentation (verticalSlice K x) where
  generic : ∀ v : ↥K.vertices, v.1.re ≠ x
  lowerVertex : Fin n → ↥K.vertices
  upperVertex : Fin n → ↥K.vertices
  lowerVertex_coord : ∀ i, (lowerVertex i).1.im = left i
  upperVertex_coord : ∀ i, (upperVertex i).1.im = right i

private theorem horizontalSupportSection_eq_closureSlice_proof :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      {x : ℝ | Complex.mk x y ∈ K.support} =
        closure (horizontalSlice K y)) := by
  intro K y hy
  obtain ⟨R, hpieces, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  apply subset_antisymm
  · intro x hx
    have hxunion : Complex.mk x y ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hx
    rcases Set.mem_sUnion.1 hxunion with ⟨q, hqpieces, hxq⟩
    have hqfin : q ∈ R.pieces := hqpieces
    obtain ⟨x0, x1, y0, y1, hx01, hy01, rfl,
      _hvx0, _hvx1, hvy0, hvy1⟩ := hintrinsic q hqfin
    have hxy : x ∈ Icc x0 x1 ∧ y ∈ Icc y0 y1 := hxq
    have hy0ne : y ≠ y0 := by
      intro h
      obtain ⟨v, hv, hvy⟩ := hvy0
      apply hy
      apply Finset.mem_image.2
      exact ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [h] using hvy⟩
    have hy1ne : y ≠ y1 := by
      intro h
      obtain ⟨v, hv, hvy⟩ := hvy1
      apply hy
      apply Finset.mem_image.2
      exact ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [h] using hvy⟩
    have hystrict : y ∈ Ioo y0 y1 :=
      ⟨lt_of_le_of_ne hxy.2.1 (Ne.symm hy0ne), lt_of_le_of_ne hxy.2.2 hy1ne⟩
    have hinterval : Ioo x0 x1 ⊆ horizontalSlice K y := by
      intro u hu
      change Complex.mk u y ∈ interior K.support
      apply interior_mono (show Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          x0 x1 y0 y1 ⊆ K.support by
        intro z hz
        rw [← R.sUnion_eq]
        exact Set.mem_sUnion_of_mem hz hqpieces)
      change Complex.mk u y ∈ interior (Icc x0 x1 ×ℂ Icc y0 y1)
      rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
      exact ⟨hu, hystrict⟩
    apply closure_mono hinterval
    rw [closure_Ioo (ne_of_lt hx01)]
    exact hxy.1
  · apply closure_minimal
    · intro x hx
      change Complex.mk x y ∈ interior K.support at hx
      change Complex.mk x y ∈ K.support
      exact interior_subset hx
    · apply K.isPolygonal.isClosed.preimage
      have hc : Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.add (continuous_const.mul continuous_const)
      change Continuous (fun x : ℝ ↦ Complex.mk x y)
      rw [show (fun x : ℝ ↦ Complex.mk x y) =
        (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by
          funext x
          apply Complex.ext <;> simp]
      exact hc

private theorem verticalSupportSection_eq_closureSlice_proof :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      {y : ℝ | Complex.mk x y ∈ K.support} =
        closure (verticalSlice K x)) := by
  intro K x hxgeneric
  obtain ⟨R, hpieces, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  apply subset_antisymm
  · intro y hy
    have hyunion : Complex.mk x y ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hy
    rcases Set.mem_sUnion.1 hyunion with ⟨q, hqpieces, hyq⟩
    have hqfin : q ∈ R.pieces := hqpieces
    obtain ⟨x0, x1, y0, y1, hx01, hy01, rfl,
      hvx0, hvx1, _hvy0, _hvy1⟩ := hintrinsic q hqfin
    have hxy : x ∈ Icc x0 x1 ∧ y ∈ Icc y0 y1 := hyq
    have hx0ne : x ≠ x0 := by
      intro h
      obtain ⟨v, hv, hvx⟩ := hvx0
      apply hxgeneric
      exact Finset.mem_image.2
        ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [h] using hvx⟩
    have hx1ne : x ≠ x1 := by
      intro h
      obtain ⟨v, hv, hvx⟩ := hvx1
      apply hxgeneric
      exact Finset.mem_image.2
        ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [h] using hvx⟩
    have hxstrict : x ∈ Ioo x0 x1 :=
      ⟨lt_of_le_of_ne hxy.1.1 (Ne.symm hx0ne), lt_of_le_of_ne hxy.1.2 hx1ne⟩
    have hinterval : Ioo y0 y1 ⊆ verticalSlice K x := by
      intro u hu
      change Complex.mk x u ∈ interior K.support
      apply interior_mono (show Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          x0 x1 y0 y1 ⊆ K.support by
        intro z hz
        rw [← R.sUnion_eq]
        exact Set.mem_sUnion_of_mem hz hqpieces)
      change Complex.mk x u ∈ interior (Icc x0 x1 ×ℂ Icc y0 y1)
      rw [Complex.interior_reProdIm, interior_Icc, interior_Icc]
      exact ⟨hxstrict, hu⟩
    apply closure_mono hinterval
    rw [closure_Ioo (ne_of_lt hy01)]
    exact hxy.2
  · apply closure_minimal
    · intro y hy
      change Complex.mk x y ∈ interior K.support at hy
      change Complex.mk x y ∈ K.support
      exact interior_subset hy
    · apply K.isPolygonal.isClosed.preimage
      have hc : Continuous (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      change Continuous (fun y : ℝ ↦ Complex.mk x y)
      rw [show (fun y : ℝ ↦ Complex.mk x y) =
        (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by
          funext y
          apply Complex.ext <;> simp]
      exact hc

private theorem horizontalSupportSections_locallyConstant
    (K : Region) {y : ℝ}
    (hy : y ∉ K.vertexFinset.image Complex.im) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - y| < ε →
      {x : ℝ | Complex.mk x s ∈ K.support} =
        {x : ℝ | Complex.mk x y ∈ K.support} := by
  classical
  obtain ⟨R, _hpieces, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  choose x0 x1 y0 y1 hx01 hy01 hq hvx0 hvx1 hvy0 hvy1 using
    fun q : ↑R.pieces => hintrinsic q.1 q.2
  have hy0ne (q : ↑R.pieces) : y ≠ y0 q := by
    intro heq
    obtain ⟨v, hv, hvcoord⟩ := hvy0 q
    apply hy
    exact Finset.mem_image.2
      ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [heq] using hvcoord⟩
  have hy1ne (q : ↑R.pieces) : y ≠ y1 q := by
    intro heq
    obtain ⟨v, hv, hvcoord⟩ := hvy1 q
    apply hy
    exact Finset.mem_image.2
      ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [heq] using hvcoord⟩
  have heach (q : ↑R.pieces) :
      ∀ᶠ s in 𝓝 y, (s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q)) := by
    by_cases hymem : y ∈ Icc (y0 q) (y1 q)
    · have hlow : y0 q < y := lt_of_le_of_ne hymem.1 (Ne.symm (hy0ne q))
      have hupp : y < y1 q := lt_of_le_of_ne hymem.2 (hy1ne q)
      filter_upwards [eventually_gt_nhds hlow, eventually_lt_nhds hupp] with s hs0 hs1
      exact iff_of_true ⟨hs0.le, hs1.le⟩ hymem
    · have hout : y < y0 q ∨ y1 q < y := by
        rcases lt_trichotomy y (y0 q) with h | h | h
        · exact Or.inl h
        · exact False.elim (hy0ne q h)
        · rcases lt_trichotomy y (y1 q) with h' | h' | h'
          · exact False.elim (hymem ⟨h.le, h'.le⟩)
          · exact False.elim (hy1ne q h')
          · exact Or.inr h'
      rcases hout with hout | hout
      · filter_upwards [eventually_lt_nhds hout] with s hs
        exact iff_of_false (fun hm => (not_le_of_gt hs) hm.1) hymem
      · filter_upwards [eventually_gt_nhds hout] with s hs
        exact iff_of_false (fun hm => (not_le_of_gt hs) hm.2) hymem
  have hall : ∀ᶠ s in 𝓝 y, ∀ q : ↑R.pieces,
      (s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q)) := by
    change {s : ℝ | ∀ q : ↑R.pieces,
      (s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q))} ∈ 𝓝 y
    rw [show {s : ℝ | ∀ q : ↑R.pieces,
      (s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q))} =
      ⋂ q : ↑R.pieces, {s : ℝ |
        s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q)} by ext; simp]
    rw [Filter.iInter_mem]
    intro q
    exact heach q
  change {s : ℝ | ∀ q : ↑R.pieces,
    (s ∈ Icc (y0 q) (y1 q) ↔ y ∈ Icc (y0 q) (y1 q))} ∈ 𝓝 y at hall
  obtain ⟨ε, hε, hall⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨ε, hε, ?_⟩
  intro s hs
  ext u
  have hsall := hall (by simpa [Real.dist_eq] using hs)
  constructor
  · intro hus
    have huunion : Complex.mk u s ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hus
    rcases Set.mem_sUnion.1 huunion with ⟨q, hqmem, huq⟩
    let qs : ↑R.pieces := ⟨q, hqmem⟩
    have huq' : Complex.mk u s ∈
        Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by
      rw [← hq qs]
      exact huq
    have huy : Complex.mk u y ∈
        Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          (x0 qs) (x1 qs) (y0 qs) (y1 qs) := ⟨huq'.1, (hsall qs).1 huq'.2⟩
    rw [← R.sUnion_eq]
    have huyq : Complex.mk u y ∈ q := by
      change Complex.mk u y ∈ qs.1
      rw [hq qs]
      exact huy
    exact Set.mem_sUnion_of_mem huyq hqmem
  · intro huy
    have huunion : Complex.mk u y ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact huy
    rcases Set.mem_sUnion.1 huunion with ⟨q, hqmem, huq⟩
    let qs : ↑R.pieces := ⟨q, hqmem⟩
    have huq' : Complex.mk u y ∈
        Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by
      rw [← hq qs]
      exact huq
    have hus : Complex.mk u s ∈
        Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          (x0 qs) (x1 qs) (y0 qs) (y1 qs) := ⟨huq'.1, (hsall qs).2 huq'.2⟩
    rw [← R.sUnion_eq]
    have husq : Complex.mk u s ∈ q := by
      change Complex.mk u s ∈ qs.1
      rw [hq qs]
      exact hus
    exact Set.mem_sUnion_of_mem husq hqmem

private theorem horizontalSlice_eq_interior_supportSection
    (K : Region) {y : ℝ}
    (hy : y ∉ K.vertexFinset.image Complex.im) :
    horizontalSlice K y = interior {x : ℝ | Complex.mk x y ∈ K.support} := by
  obtain ⟨ε, hε, hsections⟩ := horizontalSupportSections_locallyConstant K hy
  apply subset_antisymm
  · intro x hx
    apply mem_interior.2
    refine ⟨horizontalSlice K y, ?_, ?_, hx⟩
    · intro u hu
      change Complex.mk u y ∈ interior K.support at hu
      change Complex.mk u y ∈ K.support
      exact interior_subset hu
    · unfold horizontalSlice Region.openCarrier
        Tiling.RationalPolygonal.PolygonalRegion.openCarrier
      apply isOpen_interior.preimage
      have hc : Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
        Complex.continuous_ofReal.add (continuous_const.mul continuous_const)
      change Continuous (fun x : ℝ ↦ Complex.mk x y)
      rw [show (fun x : ℝ ↦ Complex.mk x y) =
        (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by
          funext x
          apply Complex.ext <;> simp]
      exact hc
  · intro x hx
    rcases mem_interior.1 hx with ⟨U, hUsub, hUopen, hxU⟩
    let W : Set Tiling.Plane := U ×ℂ Ioo (y - ε) (y + ε)
    have hWopen : IsOpen W := hUopen.reProdIm isOpen_Ioo
    have hxyW : Complex.mk x y ∈ W := by
      exact ⟨hxU, ⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩⟩
    have hWsub : W ⊆ K.support := by
      intro z hz
      have hdist : |z.im - y| < ε := by
        rw [abs_lt]
        constructor <;> linarith [hz.2.1, hz.2.2]
      have hzsection : z.re ∈ {u : ℝ | Complex.mk u y ∈ K.support} := hUsub hz.1
      have hzsupport : Complex.mk z.re z.im ∈ K.support := by
        change z.re ∈ {u : ℝ | Complex.mk u z.im ∈ K.support}
        rw [hsections z.im hdist]
        exact hzsection
      simpa only [Complex.eta] using hzsupport
    change Complex.mk x y ∈ interior K.support
    exact mem_interior.2 ⟨W, hWsub, hWopen, hxyW⟩

private theorem horizontalSlice_closedIntervals_proof :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        closure (horizontalSlice K y) = ⋃ i, Icc (a i) (b i) ∧
        horizontalSlice K y = interior (⋃ i, Icc (a i) (b i))) := by
  classical
  intro K y hy
  obtain ⟨R, _hpieces, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  choose x0 x1 y0 y1 hx01 hy01 hq _ _ _ _ using
    fun q : ↑R.pieces => hintrinsic q.1 q.2
  let G := ↑R.pieces
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let pick : Fin (Fintype.card G) → G := e.symm
  let aa : G → ℝ := fun q => if y ∈ Icc (y0 q) (y1 q) then x0 q else 1
  let bb : G → ℝ := fun q => if y ∈ Icc (y0 q) (y1 q) then x1 q else 0
  have hsection : {u : ℝ | Complex.mk u y ∈ K.support} =
      ⋃ q : G, Icc (aa q) (bb q) := by
    ext u
    constructor
    · intro hu
      have huunion : Complex.mk u y ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
        rw [R.sUnion_eq]
        exact hu
      rcases Set.mem_sUnion.1 huunion with ⟨q, hqmem, huq⟩
      let qs : G := ⟨q, hqmem⟩
      have huq' : Complex.mk u y ∈
          Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
            (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by
        rw [← hq qs]
        exact huq
      apply mem_iUnion.2
      refine ⟨qs, ?_⟩
      simp only [aa, bb, if_pos huq'.2]
      exact huq'.1
    · intro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      by_cases hactive : y ∈ Icc (y0 q) (y1 q)
      · have huz : Complex.mk u y ∈
            Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
              (x0 q) (x1 q) (y0 q) (y1 q) := by
          exact ⟨by simpa only [aa, bb, if_pos hactive] using huq, hactive⟩
        rw [← R.sUnion_eq]
        apply Set.mem_sUnion_of_mem (t := q.1) _ q.2
        rw [hq q]
        exact huz
      · exfalso
        have hactive' : ¬(y0 q ≤ y ∧ y ≤ y1 q) := by
          simpa only [mem_Icc] using hactive
        have hbad : (1 : ℝ) ≤ u ∧ u ≤ 0 := by
          simp [aa, bb, hactive'] at huq
        linarith
  refine ⟨Fintype.card G, fun i => aa (pick i), fun i => bb (pick i), ?_, ?_⟩
  · rw [← horizontalSupportSection_eq_closureSlice_proof K hy, hsection]
    ext u
    constructor
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      exact mem_iUnion.2 ⟨e q, by simpa [pick] using huq⟩
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨i, hui⟩
      exact mem_iUnion.2 ⟨pick i, hui⟩
  · rw [horizontalSlice_eq_interior_supportSection K hy, hsection]
    congr 1
    ext u
    constructor
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      exact mem_iUnion.2 ⟨e q, by simpa [pick] using huq⟩
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨i, hui⟩
      exact mem_iUnion.2 ⟨pick i, hui⟩
private theorem verticalSupportSections_locallyConstant
    (K : Region) {x : ℝ} (hx : x ∉ K.vertexFinset.image Complex.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - x| < ε →
      {y : ℝ | Complex.mk s y ∈ K.support} = {y : ℝ | Complex.mk x y ∈ K.support} := by
  classical
  obtain ⟨R, _, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  choose x0 x1 y0 y1 hx01 hy01 hq hvx0 hvx1 _ _ using
    fun q : ↑R.pieces => hintrinsic q.1 q.2
  have hx0ne (q : ↑R.pieces) : x ≠ x0 q := by
    intro heq
    obtain ⟨v, hv, hc⟩ := hvx0 q
    exact hx (Finset.mem_image.2
      ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [heq] using hc⟩)
  have hx1ne (q : ↑R.pieces) : x ≠ x1 q := by
    intro heq
    obtain ⟨v, hv, hc⟩ := hvx1 q
    exact hx (Finset.mem_image.2
      ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, by simpa [heq] using hc⟩)
  have heach (q : ↑R.pieces) : ∀ᶠ s in 𝓝 x,
      (s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q)) := by
    by_cases hm : x ∈ Icc (x0 q) (x1 q)
    · have hl : x0 q < x := lt_of_le_of_ne hm.1 (Ne.symm (hx0ne q))
      have hr : x < x1 q := lt_of_le_of_ne hm.2 (hx1ne q)
      filter_upwards [eventually_gt_nhds hl, eventually_lt_nhds hr] with s hsl hsr
      exact iff_of_true ⟨hsl.le, hsr.le⟩ hm
    · have hout : x < x0 q ∨ x1 q < x := by
        rcases lt_trichotomy x (x0 q) with h | h | h
        · exact .inl h
        · exact False.elim (hx0ne q h)
        · rcases lt_trichotomy x (x1 q) with h' | h' | h'
          · exact False.elim (hm ⟨h.le, h'.le⟩)
          · exact False.elim (hx1ne q h')
          · exact .inr h'
      rcases hout with h | h
      · filter_upwards [eventually_lt_nhds h] with s hs
        exact iff_of_false (fun hm' => (not_le_of_gt hs) hm'.1) hm
      · filter_upwards [eventually_gt_nhds h] with s hs
        exact iff_of_false (fun hm' => (not_le_of_gt hs) hm'.2) hm
  have hall : ∀ᶠ s in 𝓝 x, ∀ q : ↑R.pieces,
      (s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q)) := by
    change {s : ℝ | ∀ q : ↑R.pieces,
      (s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q))} ∈ 𝓝 x
    rw [show {s : ℝ | ∀ q : ↑R.pieces,
      (s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q))} =
      ⋂ q : ↑R.pieces, {s : ℝ |
        s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q)} by ext; simp,
      Filter.iInter_mem]
    exact heach
  change {s : ℝ | ∀ q : ↑R.pieces,
    (s ∈ Icc (x0 q) (x1 q) ↔ x ∈ Icc (x0 q) (x1 q))} ∈ 𝓝 x at hall
  obtain ⟨ε, hε, hall⟩ := Metric.mem_nhds_iff.mp hall
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hsall := hall (by simpa [Real.dist_eq] using hs)
  ext u
  constructor
  · intro hus
    have hu : Complex.mk s u ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hus
    rcases Set.mem_sUnion.1 hu with ⟨q, hqm, huq⟩
    let qs : ↑R.pieces := ⟨q, hqm⟩
    have huq' : Complex.mk s u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
        (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by rw [← hq qs]; exact huq
    have hux : Complex.mk x u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
        (x0 qs) (x1 qs) (y0 qs) (y1 qs) := ⟨(hsall qs).1 huq'.1, huq'.2⟩
    rw [← R.sUnion_eq]
    apply Set.mem_sUnion_of_mem (t := q) _ hqm
    change Complex.mk x u ∈ qs.1
    rw [hq qs]
    exact hux
  · intro hux
    have hu : Complex.mk x u ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
      rw [R.sUnion_eq]
      exact hux
    rcases Set.mem_sUnion.1 hu with ⟨q, hqm, huq⟩
    let qs : ↑R.pieces := ⟨q, hqm⟩
    have huq' : Complex.mk x u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
        (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by rw [← hq qs]; exact huq
    have hus : Complex.mk s u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
        (x0 qs) (x1 qs) (y0 qs) (y1 qs) := ⟨(hsall qs).2 huq'.1, huq'.2⟩
    rw [← R.sUnion_eq]
    apply Set.mem_sUnion_of_mem (t := q) _ hqm
    change Complex.mk s u ∈ qs.1
    rw [hq qs]
    exact hus

private theorem verticalSlice_eq_interior_supportSection
    (K : Region) {x : ℝ} (hx : x ∉ K.vertexFinset.image Complex.re) :
    verticalSlice K x = interior {y : ℝ | Complex.mk x y ∈ K.support} := by
  obtain ⟨ε, hε, hsections⟩ := verticalSupportSections_locallyConstant K hx
  apply subset_antisymm
  · intro y hy
    apply mem_interior.2
    refine ⟨verticalSlice K x, ?_, ?_, hy⟩
    · intro u hu
      change Complex.mk x u ∈ interior K.support at hu
      change Complex.mk x u ∈ K.support
      exact interior_subset hu
    · unfold verticalSlice Region.openCarrier Tiling.RationalPolygonal.PolygonalRegion.openCarrier
      apply isOpen_interior.preimage
      have hc : Continuous (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
        continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
      change Continuous (fun y : ℝ ↦ Complex.mk x y)
      rw [show (fun y : ℝ ↦ Complex.mk x y) =
        (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by funext y; apply Complex.ext <;> simp]
      exact hc
  · intro y hy
    rcases mem_interior.1 hy with ⟨U, hUsub, hUopen, hyU⟩
    let W : Set Tiling.Plane := Ioo (x - ε) (x + ε) ×ℂ U
    have hWopen : IsOpen W := isOpen_Ioo.reProdIm hUopen
    have hxyW : Complex.mk x y ∈ W := ⟨⟨sub_lt_self _ hε, lt_add_of_pos_right _ hε⟩, hyU⟩
    have hWsub : W ⊆ K.support := by
      intro z hz
      have hd : |z.re - x| < ε := by rw [abs_lt]; constructor <;> linarith [hz.1.1, hz.1.2]
      have hsec : z.im ∈ {u : ℝ | Complex.mk x u ∈ K.support} := hUsub hz.2
      have : Complex.mk z.re z.im ∈ K.support := by
        change z.im ∈ {u : ℝ | Complex.mk z.re u ∈ K.support}
        rw [hsections z.re hd]
        exact hsec
      simpa only [Complex.eta] using this
    change Complex.mk x y ∈ interior K.support
    exact mem_interior.2 ⟨W, hWsub, hWopen, hxyW⟩

private theorem verticalSlice_closedIntervals_proof :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        closure (verticalSlice K x) = ⋃ i, Icc (a i) (b i) ∧
        verticalSlice K x = interior (⋃ i, Icc (a i) (b i))) := by
  classical
  intro K x hx
  obtain ⟨R, _, hintrinsic⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicGridRectangulation K
  choose x0 x1 y0 y1 hx01 hy01 hq _ _ _ _ using
    fun q : ↑R.pieces => hintrinsic q.1 q.2
  let G := ↑R.pieces
  let e : G ≃ Fin (Fintype.card G) := Fintype.equivFin G
  let pick : Fin (Fintype.card G) → G := e.symm
  let aa : G → ℝ := fun q => if x ∈ Icc (x0 q) (x1 q) then y0 q else 1
  let bb : G → ℝ := fun q => if x ∈ Icc (x0 q) (x1 q) then y1 q else 0
  have hsection : {u : ℝ | Complex.mk x u ∈ K.support} = ⋃ q : G, Icc (aa q) (bb q) := by
    ext u
    constructor
    · intro hu
      have huunion :
          Complex.mk x u ∈ ⋃₀ (R.pieces : Set (Set Tiling.Plane)) := by
        rw [R.sUnion_eq]
        exact hu
      rcases Set.mem_sUnion.1 huunion with ⟨q, hqm, huq⟩
      let qs : G := ⟨q, hqm⟩
      have huq' : Complex.mk x u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
          (x0 qs) (x1 qs) (y0 qs) (y1 qs) := by rw [← hq qs]; exact huq
      exact mem_iUnion.2 ⟨qs, by simp only [aa, bb, if_pos huq'.1]; exact huq'.2⟩
    · intro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      by_cases hactive : x ∈ Icc (x0 q) (x1 q)
      · have huz : Complex.mk x u ∈ Tiling.AxisParallel.IntrinsicVertices.closedAxisBox
            (x0 q) (x1 q) (y0 q) (y1 q) :=
          ⟨hactive, by simpa only [aa, bb, if_pos hactive] using huq⟩
        rw [← R.sUnion_eq]
        apply Set.mem_sUnion_of_mem (t := q.1) _ q.2
        rw [hq q]
        exact huz
      · exfalso
        have hactive' : ¬(x0 q ≤ x ∧ x ≤ x1 q) := by simpa only [mem_Icc] using hactive
        have hbad : (1 : ℝ) ≤ u ∧ u ≤ 0 := by
          simp [aa, bb, hactive'] at huq
        linarith
  refine ⟨Fintype.card G, fun i => aa (pick i), fun i => bb (pick i), ?_, ?_⟩
  · rw [← verticalSupportSection_eq_closureSlice_proof K hx, hsection]
    ext u
    constructor
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      exact mem_iUnion.2 ⟨e q, by simpa [pick] using huq⟩
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨i, hui⟩
      exact mem_iUnion.2 ⟨pick i, hui⟩
  · rw [verticalSlice_eq_interior_supportSection K hx, hsection]
    congr 1
    ext u
    constructor
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨q, huq⟩
      exact mem_iUnion.2 ⟨e q, by simpa [pick] using huq⟩
    · rintro hu
      rcases mem_iUnion.1 hu with ⟨i, hui⟩
      exact mem_iUnion.2 ⟨pick i, hui⟩

private theorem maximal_left_mem_frontier {B : Set ℝ}
    (P : MaximalIntervalPresentation B) (i : Fin P.n) :
    P.left i ∈ frontier B := by
  have hcl : P.left i ∈ closure B := by
    rw [P.closure_eq]
    exact mem_iUnion.2 ⟨i, ⟨le_rfl, (P.lt i).le⟩⟩
  rw [frontier]
  refine ⟨hcl, ?_⟩
  intro hint
  have hmem : P.left i ∈ B := interior_subset hint
  have hmem' : P.left i ∈ ⋃ j, Ioo (P.left j) (P.right j) :=
    P.union_eq ▸ hmem
  rcases mem_iUnion.1 hmem' with ⟨j, hj⟩
  by_cases hij : i = j
  · subst j
    exact (lt_irrefl _ hj.1)
  · rcases P.pairwise_gap i j hij with hgap | hgap
    · linarith [P.lt i, hj.1]
    · linarith [hj.2]

private theorem maximal_right_mem_frontier {B : Set ℝ}
    (P : MaximalIntervalPresentation B) (i : Fin P.n) :
    P.right i ∈ frontier B := by
  have hcl : P.right i ∈ closure B := by
    rw [P.closure_eq]
    exact mem_iUnion.2 ⟨i, ⟨(P.lt i).le, le_rfl⟩⟩
  rw [frontier]
  refine ⟨hcl, ?_⟩
  intro hint
  have hmem : P.right i ∈ B := interior_subset hint
  have hmem' : P.right i ∈ ⋃ j, Ioo (P.left j) (P.right j) :=
    P.union_eq ▸ hmem
  rcases mem_iUnion.1 hmem' with ⟨j, hj⟩
  by_cases hij : i = j
  · subst j
    exact (lt_irrefl _ hj.2)
  · rcases P.pairwise_gap i j hij with hgap | hgap
    · linarith [hj.1]
    · linarith [P.lt i, hj.2]

private theorem horizontal_frontier_lifts_of_section_eq
    (K : Region) {y a : ℝ}
    (hsection : {x : ℝ | Complex.mk x y ∈ K.support} =
      closure (horizontalSlice K y))
    (ha : a ∈ frontier (horizontalSlice K y)) :
    Complex.mk a y ∈ frontier K.support := by
  have hacl : a ∈ closure (horizontalSlice K y) :=
    frontier_subset_closure ha
  have hasupport : Complex.mk a y ∈ K.support := by
    have : a ∈ {x : ℝ | Complex.mk x y ∈ K.support} := hsection.symm ▸ hacl
    exact this
  apply (mem_frontier_iff_notMem_interior hasupport).2
  intro hainterior
  have haopen : Complex.mk a y ∈ K.openCarrier := hainterior
  have haslice : a ∈ horizontalSlice K y := haopen
  have hopen : IsOpen (horizontalSlice K y) := by
    unfold horizontalSlice Region.openCarrier Tiling.RationalPolygonal.PolygonalRegion.openCarrier
    apply isOpen_interior.preimage
    have hc : Continuous (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
      Complex.continuous_ofReal.add (continuous_const.mul continuous_const)
    rw [show (fun x : ℝ ↦ Complex.mk x y) =
      (fun x : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by
        funext x
        apply Complex.ext <;> simp]
    exact hc
  exact ha.2 (by simpa only [hopen.interior_eq] using haslice)

private theorem vertical_frontier_lifts_of_section_eq
    (K : Region) {x a : ℝ}
    (hsection : {y : ℝ | Complex.mk x y ∈ K.support} =
      closure (verticalSlice K x))
    (ha : a ∈ frontier (verticalSlice K x)) :
    Complex.mk x a ∈ frontier K.support := by
  have hacl : a ∈ closure (verticalSlice K x) :=
    frontier_subset_closure ha
  have hasupport : Complex.mk x a ∈ K.support := by
    have : a ∈ {y : ℝ | Complex.mk x y ∈ K.support} := hsection.symm ▸ hacl
    exact this
  apply (mem_frontier_iff_notMem_interior hasupport).2
  intro hainterior
  have haopen : Complex.mk x a ∈ K.openCarrier := hainterior
  have haslice : a ∈ verticalSlice K x := haopen
  have hopen : IsOpen (verticalSlice K x) := by
    unfold verticalSlice Region.openCarrier Tiling.RationalPolygonal.PolygonalRegion.openCarrier
    apply isOpen_interior.preimage
    have hc : Continuous (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    change Continuous (fun y : ℝ ↦ Complex.mk x y)
    rw [show (fun y : ℝ ↦ Complex.mk x y) =
      (fun y : ℝ ↦ (x : ℂ) + (y : ℂ) * Complex.I) by
        funext y
        apply Complex.ext <;> simp]
    exact hc
  exact ha.2 (by simpa only [hopen.interior_eq] using haslice)

private theorem horizontalSlice_frontier_lifts_proof
    (hsection : (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      {x : ℝ | Complex.mk x y ∈ K.support} =
        closure (horizontalSlice K y))) :
    (∀ (K : Region) {y a : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
    a ∈ frontier (horizontalSlice K y) →
      Complex.mk a y ∈ frontier K.support) := by
  intro K y a hy ha
  exact horizontal_frontier_lifts_of_section_eq K (hsection K hy) ha

private theorem verticalSlice_frontier_lifts_proof
    (hsection : (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      {y : ℝ | Complex.mk x y ∈ K.support} =
        closure (verticalSlice K x))) :
    (∀ (K : Region) {x a : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
    a ∈ frontier (verticalSlice K x) →
      Complex.mk x a ∈ frontier K.support) := by
  intro K x a hx ha
  exact vertical_frontier_lifts_of_section_eq K (hsection K hx) ha

private theorem horizontalSlice_componentEndpoints_proof
    (hlift : (∀ (K : Region) {y a : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
    a ∈ frontier (horizontalSlice K y) →
      Complex.mk a y ∈ frontier K.support)) :
    (∀ (K : Region) {y a b : ℝ},
    y ∉ K.vertexFinset.image Complex.im → a < b →
    Ioo a b ⊆ horizontalSlice K y →
    a ∈ frontier (horizontalSlice K y) →
    b ∈ frontier (horizontalSlice K y) →
      ∃ v w : ↥K.vertices, v.1.re = a ∧ w.1.re = b) := by
  intro K y a b hy hab hinside ha hb
  have hgeneric : ∀ v : ↥K.vertices, v.1.im ≠ y := by
    intro v hv
    exact hy (Finset.mem_image.2
      ⟨v.1, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 v.2, hv⟩)
  exact Tiling.AxisParallel.IntrinsicVertices.horizontalSectionEndpoints_intrinsic K hgeneric hab
    (hlift K hy ha) (hlift K hy hb) hinside

private theorem verticalSlice_componentEndpoints_proof
    (hlift : (∀ (K : Region) {x a : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
    a ∈ frontier (verticalSlice K x) →
      Complex.mk x a ∈ frontier K.support)) :
    (∀ (K : Region) {x a b : ℝ},
    x ∉ K.vertexFinset.image Complex.re → a < b →
    Ioo a b ⊆ verticalSlice K x →
    a ∈ frontier (verticalSlice K x) →
    b ∈ frontier (verticalSlice K x) →
      ∃ v w : ↥K.vertices, v.1.im = a ∧ w.1.im = b) := by
  intro K x a b hx hab _ ha hb
  have ha' := hlift K hx ha
  have hb' := hlift K hx hb
  have haga := Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K ha'
  have hagb := Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K hb'
  rcases haga with ⟨v, hv, hvr⟩ | ⟨v, hv, hvi⟩
  · exact False.elim (hx (Finset.mem_image.2
      ⟨v, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hv, hvr.symm⟩))
  · rcases hagb with ⟨w, hw, hwr⟩ | ⟨w, hw, hwi⟩
    · exact False.elim (hx (Finset.mem_image.2
        ⟨w, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 hw, hwr.symm⟩))
    · exact ⟨⟨v, hv⟩, ⟨w, hw⟩, by simpa using hvi.symm, by simpa using hwi.symm⟩

private theorem horizontalSlice_frontier_lifts_exact :
    (∀ (K : Region) {y a : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
    a ∈ frontier (horizontalSlice K y) →
      Complex.mk a y ∈ frontier K.support) :=
  horizontalSlice_frontier_lifts_proof
    (horizontalSupportSection_eq_closureSlice_proof)

private theorem verticalSlice_frontier_lifts_exact :
    (∀ (K : Region) {x a : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
    a ∈ frontier (verticalSlice K x) →
      Complex.mk x a ∈ frontier K.support) :=
  verticalSlice_frontier_lifts_proof
    (verticalSupportSection_eq_closureSlice_proof)

private theorem horizontalSlice_componentEndpoints_exact :
    (∀ (K : Region) {y a b : ℝ},
    y ∉ K.vertexFinset.image Complex.im → a < b →
    Ioo a b ⊆ horizontalSlice K y →
    a ∈ frontier (horizontalSlice K y) →
    b ∈ frontier (horizontalSlice K y) →
      ∃ v w : ↥K.vertices, v.1.re = a ∧ w.1.re = b) :=
  horizontalSlice_componentEndpoints_proof
    (horizontalSlice_frontier_lifts_exact)

private theorem verticalSlice_componentEndpoints_exact :
    (∀ (K : Region) {x a b : ℝ},
    x ∉ K.vertexFinset.image Complex.re → a < b →
    Ioo a b ⊆ verticalSlice K x →
    a ∈ frontier (verticalSlice K x) →
    b ∈ frontier (verticalSlice K x) →
      ∃ v w : ↥K.vertices, v.1.im = a ∧ w.1.im = b) :=
  verticalSlice_componentEndpoints_proof
    (verticalSlice_frontier_lifts_exact)

private theorem horizontalGenericSlicePresentation_exists_proof :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      Nonempty (HorizontalGenericSlicePresentation K y)) := by
  intro K y hy
  obtain ⟨n, a, b, hclosure, hopen⟩ := horizontalSlice_closedIntervals_proof K hy
  obtain ⟨P⟩ := finiteClosedIntervals_merge a b
  have hB : interior (⋃ i, Icc (a i) (b i)) = horizontalSlice K y := hopen.symm
  let P' : MaximalIntervalPresentation (horizontalSlice K y) := {
    P with
    union_eq := by simpa only [hB] using P.union_eq
    closure_eq := by simpa only [hB, hclosure] using P.closure_eq }
  have hend (i : Fin P'.n) : ∃ v w : ↥K.vertices,
      v.1.re = P'.left i ∧ w.1.re = P'.right i :=
    horizontalSlice_componentEndpoints_exact K hy (P'.lt i)
      (by intro x hx; rw [P'.union_eq]; exact mem_iUnion.2 ⟨i, hx⟩)
      (maximal_left_mem_frontier P' i) (maximal_right_mem_frontier P' i)
  choose lv rv hlv hrv using hend
  exact ⟨{
    toMaximalIntervalPresentation := P'
    generic := by
      intro v hv
      exact hy (Finset.mem_image.2
        ⟨v.1, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 v.2, hv⟩)
    leftVertex := lv
    rightVertex := rv
    leftVertex_coord := hlv
    rightVertex_coord := hrv }⟩

private theorem verticalGenericSlicePresentation_exists_proof :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      Nonempty (VerticalGenericSlicePresentation K x)) := by
  intro K x hx
  obtain ⟨n, a, b, hclosure, hopen⟩ := verticalSlice_closedIntervals_proof K hx
  obtain ⟨P⟩ := finiteClosedIntervals_merge a b
  have hB : interior (⋃ i, Icc (a i) (b i)) = verticalSlice K x := hopen.symm
  let P' : MaximalIntervalPresentation (verticalSlice K x) := {
    P with
    union_eq := by simpa only [hB] using P.union_eq
    closure_eq := by simpa only [hB, hclosure] using P.closure_eq }
  have hend (i : Fin P'.n) : ∃ v w : ↥K.vertices,
      v.1.im = P'.left i ∧ w.1.im = P'.right i :=
    verticalSlice_componentEndpoints_exact K hx (P'.lt i)
      (by intro y hy; rw [P'.union_eq]; exact mem_iUnion.2 ⟨i, hy⟩)
      (maximal_left_mem_frontier P' i) (maximal_right_mem_frontier P' i)
  choose lv rv hlv hrv using hend
  exact ⟨{
    toMaximalIntervalPresentation := P'
    generic := by
      intro v hv
      exact hx (Finset.mem_image.2
        ⟨v.1, (K.isPolygonal.vertexSet_finite.mem_toFinset).2 v.2, hv⟩)
    lowerVertex := lv
    upperVertex := rv
    lowerVertex_coord := hlv
    upperVertex_coord := hrv }⟩

private theorem horizontalSlice_locallyConstant_proof :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - y| < ε →
        horizontalSlice K s = horizontalSlice K y) := by
  classical
  intro K y hy
  obtain ⟨ε, hε, hsections⟩ := horizontalSupportSections_locallyConstant K hy
  have havoid : (K.vertexFinset.image Complex.im : Set ℝ)ᶜ ∈ nhds y :=
    (K.vertexFinset.image Complex.im).isClosed.isOpen_compl.mem_nhds hy
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp havoid
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro s hs
  have hsε : |s - y| < ε := hs.trans_le (min_le_left _ _)
  have hsδ : dist s y < δ := by simpa [Real.dist_eq] using hs.trans_le (min_le_right _ _)
  have hsgeneric : s ∉ K.vertexFinset.image Complex.im := hδsub hsδ
  rw [horizontalSlice_eq_interior_supportSection K hsgeneric,
    horizontalSlice_eq_interior_supportSection K hy, hsections s hsε]

private theorem verticalSlice_locallyConstant_proof :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - x| < ε →
        verticalSlice K r = verticalSlice K x) := by
  classical
  intro K x hx
  obtain ⟨ε, hε, hsections⟩ := verticalSupportSections_locallyConstant K hx
  have havoid : (K.vertexFinset.image Complex.re : Set ℝ)ᶜ ∈ nhds x :=
    (K.vertexFinset.image Complex.re).isClosed.isOpen_compl.mem_nhds hx
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp havoid
  refine ⟨min ε δ, lt_min hε hδ, ?_⟩
  intro r hr
  have hrε : |r - x| < ε := hr.trans_le (min_le_left _ _)
  have hrδ : dist r x < δ := by simpa [Real.dist_eq] using hr.trans_le (min_le_right _ _)
  have hrgeneric : r ∉ K.vertexFinset.image Complex.re := hδsub hrδ
  rw [verticalSlice_eq_interior_supportSection K hrgeneric,
    verticalSlice_eq_interior_supportSection K hx, hsections r hrε]

private theorem horizontalSlice_isFiniteIntervalRegion_proof :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      IsFiniteIntervalRegion (horizontalSlice K y)) := by
  intro K y hy
  obtain ⟨P⟩ := horizontalGenericSlicePresentation_exists_proof K hy
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩

private theorem verticalSlice_isFiniteIntervalRegion_proof :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      IsFiniteIntervalRegion (verticalSlice K x)) := by
  intro K x hx
  obtain ⟨P⟩ := verticalGenericSlicePresentation_exists_proof K hx
  exact ⟨P.n, P.left, P.right, P.lt, P.union_eq⟩


theorem horizontalSupportSection_eq_closureSlice :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      {x : ℝ | Complex.mk x y ∈ K.support} =
        closure (horizontalSlice K y)) :=
  horizontalSupportSection_eq_closureSlice_proof

theorem verticalSupportSection_eq_closureSlice :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      {y : ℝ | Complex.mk x y ∈ K.support} =
        closure (verticalSlice K x)) :=
  verticalSupportSection_eq_closureSlice_proof

theorem horizontalSlice_frontier_lifts :
    (∀ (K : Region) {y a : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
    a ∈ frontier (horizontalSlice K y) →
      Complex.mk a y ∈ frontier K.support) :=
  horizontalSlice_frontier_lifts_exact

theorem verticalSlice_frontier_lifts :
    (∀ (K : Region) {x a : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
    a ∈ frontier (verticalSlice K x) →
      Complex.mk x a ∈ frontier K.support) :=
  verticalSlice_frontier_lifts_exact

theorem horizontalGenericSlicePresentation_exists :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      Nonempty (HorizontalGenericSlicePresentation K y)) :=
  horizontalGenericSlicePresentation_exists_proof

theorem verticalGenericSlicePresentation_exists :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      Nonempty (VerticalGenericSlicePresentation K x)) :=
  verticalGenericSlicePresentation_exists_proof

theorem verticalSlice_closedIntervals :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        closure (verticalSlice K x) = ⋃ i, Icc (a i) (b i) ∧
        verticalSlice K x = interior (⋃ i, Icc (a i) (b i))) :=
  verticalSlice_closedIntervals_proof

theorem horizontalSlice_closedIntervals :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      ∃ (n : ℕ) (a b : Fin n → ℝ),
        closure (horizontalSlice K y) = ⋃ i, Icc (a i) (b i) ∧
        horizontalSlice K y = interior (⋃ i, Icc (a i) (b i))) :=
  horizontalSlice_closedIntervals_proof

theorem horizontalSlice_locallyConstant :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - y| < ε →
        horizontalSlice K s = horizontalSlice K y) :=
  horizontalSlice_locallyConstant_proof

theorem verticalSlice_locallyConstant :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - x| < ε →
        verticalSlice K r = verticalSlice K x) :=
  verticalSlice_locallyConstant_proof

theorem horizontalSlice_isFiniteIntervalRegion :
    (∀ (K : Region) {y : ℝ},
    y ∉ K.vertexFinset.image Complex.im →
      IsFiniteIntervalRegion (horizontalSlice K y)) :=
  horizontalSlice_isFiniteIntervalRegion_proof

theorem verticalSlice_isFiniteIntervalRegion :
    (∀ (K : Region) {x : ℝ},
    x ∉ K.vertexFinset.image Complex.re →
      IsFiniteIntervalRegion (verticalSlice K x)) :=
  verticalSlice_isFiniteIntervalRegion_proof

theorem horizontalSlice_componentEndpoints :
    (∀ (K : Region) {y a b : ℝ},
    y ∉ K.vertexFinset.image Complex.im → a < b →
    Ioo a b ⊆ horizontalSlice K y →
    a ∈ frontier (horizontalSlice K y) →
    b ∈ frontier (horizontalSlice K y) →
      ∃ v w : ↥K.vertices, v.1.re = a ∧ w.1.re = b) :=
  horizontalSlice_componentEndpoints_exact

theorem verticalSlice_componentEndpoints :
    (∀ (K : Region) {x a b : ℝ},
    x ∉ K.vertexFinset.image Complex.re → a < b →
    Ioo a b ⊆ verticalSlice K x →
    a ∈ frontier (verticalSlice K x) →
    b ∈ frontier (verticalSlice K x) →
      ∃ v w : ↥K.vertices, v.1.im = a ∧ w.1.im = b) :=
  verticalSlice_componentEndpoints_exact

end Tiling.AxisParallel.Foundations.GenericSlices
