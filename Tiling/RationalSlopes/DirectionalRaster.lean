import Tiling.RationalSlopes.Earthquake
import Tiling.RationalSlopes.BoundaryGeometry
import Tiling.RationalSlopes.Basic
import Tiling.RationalPolygonal.IntegerReduction
import Tiling.AxisParallel.Discrete.DiscretePlatePeriodicity

/-! Scratch proof implementation of the frozen directional-raster owner.
The final diagnostic commands record owned axioms and exact native dependency boundaries.
Production integration and API changes remain root-only. -/
set_option autoImplicit false
set_option linter.style.header false
open Set
open scoped Pointwise Topology
noncomputable section
namespace Tiling.RationalSlopes.DirectionalRaster
open Tiling.RationalPolygonal (PolygonalRegion IntegerPlane integerPoint)
open Tiling.Polygonal
def verticalDirection : Submodule ℝ Plane := Submodule.span ℝ ({Complex.I} : Set Plane)
def regularizedProjection (U : Set Plane) : Set ℝ := interior (closure (Complex.re '' U))
def gridPoint (h k : ℝ) (z : IntegerPlane) : Plane :=
  h * (z 0 : ℝ) + (k * (z 1 : ℝ)) * Complex.I
def gridCell (h k : ℝ) (z : IntegerPlane) : Set Plane :=
  {x | h * (z 0 : ℝ) ≤ x.re ∧ x.re ≤ h * ((z 0 : ℝ) + 1) ∧
    k * (z 1 : ℝ) ≤ x.im ∧ x.im ≤ k * ((z 1 : ℝ) + 1)}
def cellSupport (h k : ℝ) (F : Finset IntegerPlane) : Set Plane :=
  ⋃ z ∈ F, gridCell h k z
def sampledIndices (K : PolygonalRegion) (h k : ℝ) (u : Plane) : Set IntegerPlane :=
  {z | u + gridPoint h k z ∈ K.openCarrier}
def occupiedColumns (F : Finset IntegerPlane) : Set ℤ := {j | ∃ z ∈ F, z 0 = j}
def vertexReach (K : PolygonalRegion) (T : Set Plane) (s t : Plane) : Prop :=
  Relation.ReflTransGen (fun a b : Plane => a ∈ T ∧ b ∈ T ∧
    ((a +ᵥ vertexSet K.support) ∩ (b +ᵥ vertexSet K.support)).Nonempty) s t

theorem regularized_open_overlap :
  ∀ A B : Set ℝ, IsOpen A → IsOpen B →
    ((A ∩ B).Nonempty ↔
      (interior (closure A) ∩ interior (closure B)).Nonempty)
  := by
  intro A B hA hB
  constructor
  · rintro ⟨x, hxA, hxB⟩
    exact ⟨x, hA.subset_interior_closure hxA, hB.subset_interior_closure hxB⟩
  · intro h
    have h₁ : (closure A ∩ interior (closure B)).Nonempty :=
      h.mono (inter_subset_inter_left _ interior_subset)
    have h₂ : (A ∩ interior (closure B)).Nonempty :=
      (closure_inter_open_nonempty_iff isOpen_interior).mp h₁
    have h₃ : (closure B ∩ A).Nonempty := by
      obtain ⟨x, hxA, hxB⟩ := h₂
      exact ⟨x, interior_subset hxB, hxA⟩
    exact (inter_comm B A) ▸ (closure_inter_open_nonempty_iff hA).mp h₃

private theorem mem_verticalDirection_iff (x : Plane) :
    x ∈ verticalDirection ↔ x.re = 0 := by
  rw [verticalDirection, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨r, rfl⟩
    simp
  · intro hx
    refine ⟨x.im, ?_⟩
    apply Complex.ext <;> simp [hx]

private theorem re_image_vadd (s : Plane) (U : Set Plane) :
    Complex.re '' (s +ᵥ U) = s.re +ᵥ (Complex.re '' U) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hy
    exact Set.mem_vadd_set.mpr ⟨z.re, ⟨z, hz, rfl⟩, by simp⟩
  · intro hx
    obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := Set.mem_vadd_set.mp hx
    exact ⟨s + z, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩, by simp⟩

private theorem vertical_overlap_iff_projection (U V : Set Plane) :
    (U ∩ directionalSaturation verticalDirection V).Nonempty ↔
      ((Complex.re '' U) ∩ (Complex.re '' V)).Nonempty := by
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have heq : x.re = y.re := by
      have hzero := (mem_verticalDirection_iff (x - y)).mp hxy
      simpa using sub_eq_zero.mp hzero
    exact ⟨x.re, ⟨x, hx, rfl⟩, ⟨y, hy, heq.symm⟩⟩
  · rintro ⟨r, ⟨x, hx, hxr⟩, ⟨y, hy, hyr⟩⟩
    refine ⟨x, hx, y, hy, (mem_verticalDirection_iff _).mpr ?_⟩
    simp [hxr, hyr]

theorem directionalOverlap_iff_footprint :
  ∀ (K : PolygonalRegion) (s t : Plane),
    DirectionalOverlap K verticalDirection s t ↔
      ((s.re +ᵥ regularizedProjection K.openCarrier) ∩
        (t.re +ᵥ regularizedProjection K.openCarrier)).Nonempty
  := by
  intro K s t
  rw [DirectionalOverlap, vertical_overlap_iff_projection]
  have hs : IsOpen (Complex.re '' (s +ᵥ K.openCarrier)) :=
    Complex.isOpenMap_re _ (isOpen_interior.vadd s)
  have ht : IsOpen (Complex.re '' (t +ᵥ K.openCarrier)) :=
    Complex.isOpenMap_re _ (isOpen_interior.vadd t)
  rw [regularized_open_overlap _ _ hs ht, re_image_vadd, re_image_vadd,
    closure_vadd, closure_vadd, interior_vadd, interior_vadd]
  rfl

private theorem component_projection_interval (K : PolygonalRegion)
    (O : Set Plane) (hO : O ∈ Tiling.interiorComponents K.support) :
    ∃ v w : Plane, v ∈ vertexSet K.support ∧ w ∈ vertexSet K.support ∧
      v.re < w.re ∧ Complex.re '' O = Set.Ioo v.re w.re := by
  have hre : Complex.reLm ≠ (0 : Plane →ₗ[ℝ] ℝ) := by
    intro heq
    have h := congrArg (fun f : Plane →ₗ[ℝ] ℝ => f 1) heq
    norm_num at h
  obtain ⟨v, hv, hvO, _hmin, hvstrict⟩ :=
    K.isPolygonal.exists_interiorComponent_min_vertex hO Complex.reLm hre
  obtain ⟨w, hw, hwO, _hmax, hwstrict⟩ :=
    K.isPolygonal.exists_interiorComponent_max_vertex hO Complex.reLm hre
  have hbasic := Tiling.interiorComponent_basic hO
  obtain ⟨p, hp⟩ := hbasic.2.1.nonempty
  have hvp : v.re < p.re := hvstrict p hp
  have hpw : p.re < w.re := hwstrict p hp
  refine ⟨v, w, hv, hw, hvp.trans hpw, ?_⟩
  apply Set.Subset.antisymm
  · rintro r ⟨z, hz, rfl⟩
    exact ⟨hvstrict z hz, hwstrict z hz⟩
  · intro r hr
    have hvimage : v.re ∈ closure (Complex.re '' O) :=
      image_closure_subset_closure_image Complex.continuous_re ⟨v, hvO, rfl⟩
    have hwimage : w.re ∈ closure (Complex.re '' O) :=
      image_closure_subset_closure_image Complex.continuous_re ⟨w, hwO, rfl⟩
    obtain ⟨a, har, ha⟩ := mem_closure_iff.mp hvimage (Set.Iio r) isOpen_Iio hr.1
    obtain ⟨b, hrb, hb⟩ := mem_closure_iff.mp hwimage (Set.Ioi r) isOpen_Ioi hr.2
    have hconnected : IsPreconnected (Complex.re '' O) :=
      hbasic.2.1.isPreconnected.image Complex.re Complex.continuous_re.continuousOn
    exact hconnected.ordConnected.out ha hb ⟨har.le, hrb.le⟩

private theorem rawProjection_finite_intervals (K : PolygonalRegion) :
    ∃ J : Finset (ℝ × ℝ), (∀ p ∈ J, p.1 < p.2) ∧
      Complex.re '' K.openCarrier = ⋃ p ∈ J, Set.Ioo p.1 p.2 ∧
      (∀ p ∈ J, ∃ v ∈ vertexSet K.support, ∃ w ∈ vertexSet K.support,
        p.1 = v.re ∧ p.2 = w.re) := by
  classical
  let C := ↥(Tiling.interiorComponents K.support)
  let : Fintype C := (K.isPolygonal.interiorComponents_finite).fintype
  choose v w hv hw hvw hproj using fun O : C => component_projection_interval K O.1 O.2
  let J := Finset.univ.image (fun O : C => ((v O).re, (w O).re))
  refine ⟨J, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨O, _hO, rfl⟩ := Finset.mem_image.mp hp
    exact hvw O
  · ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      let O : C := ⟨connectedComponentIn K.openCarrier x, ⟨x, hx, rfl⟩⟩
      apply Set.mem_iUnion.mpr
      refine ⟨((v O).re, (w O).re), Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨O, Finset.mem_univ _, rfl⟩, ?_⟩⟩
      rw [← hproj O]
      exact ⟨x, mem_connectedComponentIn hx, rfl⟩
    · intro hr
      obtain ⟨p, hp, hpr⟩ := Set.mem_iUnion₂.mp hr
      obtain ⟨O, _hO, rfl⟩ := Finset.mem_image.mp hp
      rw [← hproj O] at hpr
      obtain ⟨x, hx, rfl⟩ := hpr
      exact ⟨x, (Tiling.interiorComponent_basic O.2).2.2 hx, rfl⟩
  · intro p hp
    obtain ⟨O, _hO, rfl⟩ := Finset.mem_image.mp hp
    exact ⟨v O, hv O, w O, hw O, rfl, rfl⟩

private theorem finite_interval_regularization (J : Finset (ℝ × ℝ))
    (hJ : ∀ p ∈ J, p.1 < p.2) :
    ∃ L : Finset (ℝ × ℝ), (∀ p ∈ L, p.1 < p.2) ∧
      interior (closure (⋃ p ∈ J, Set.Ioo p.1 p.2)) = ⋃ p ∈ L, Set.Ioo p.1 p.2 ∧
      (∀ p ∈ L, p.1 ∈ J.image Prod.fst ∪ J.image Prod.snd ∧
        p.2 ∈ J.image Prod.fst ∪ J.image Prod.snd) := by
  classical
  let C := J.image Prod.fst ∪ J.image Prod.snd
  let E := ⋃ p ∈ J, Set.Icc p.1 p.2
  let Q := interior E
  have hclosure : closure (⋃ p ∈ J, Set.Ioo p.1 p.2) = E := by
    rw [Finset.closure_biUnion]
    apply Set.iUnion₂_congr
    intro p hp
    exact closure_Ioo (hJ p hp).ne
  have hleft (p : ℝ × ℝ) (hp : p ∈ J) : p.1 ∈ C :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hright (p : ℝ × ℝ) (hp : p ∈ J) : p.2 ∈ C :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  let L := (C.product C).filter (fun p => p.1 < p.2 ∧ Set.Ioo p.1 p.2 ⊆ Q)
  refine ⟨L, ?_, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.1
  · rw [hclosure]
    ext x
    constructor
    · intro hx
      obtain ⟨l, u, hxl, hnhd⟩ :=
        mem_nhds_iff_exists_Ioo_subset.mp (mem_interior_iff_mem_nhds.mp hx)
      have hyL : (l + x) / 2 ∈ E := hnhd ⟨by linarith [hxl.1], by linarith [hxl.1, hxl.2]⟩
      have hyR : (x + u) / 2 ∈ E := hnhd ⟨by linarith [hxl.1, hxl.2], by linarith [hxl.2]⟩
      obtain ⟨p, hp, hpy⟩ := Set.mem_iUnion₂.mp hyL
      obtain ⟨q, hq, hqy⟩ := Set.mem_iUnion₂.mp hyR
      have hCL : (C.filter (· < x)).Nonempty :=
        ⟨p.1, Finset.mem_filter.mpr ⟨hleft p hp, by linarith [hpy.1, hxl.1]⟩⟩
      have hCR : (C.filter (x < ·)).Nonempty :=
        ⟨q.2, Finset.mem_filter.mpr ⟨hright q hq, by linarith [hqy.2, hxl.2]⟩⟩
      let a := (C.filter (· < x)).max' hCL
      let b := (C.filter (x < ·)).min' hCR
      have ha := Finset.mem_filter.mp (Finset.max'_mem _ hCL)
      have hb := Finset.mem_filter.mp (Finset.min'_mem _ hCR)
      have hbelow : ∀ c ∈ C, c < x → c ≤ a := by
        intro c hc hcx
        exact Finset.le_max' _ c (Finset.mem_filter.mpr ⟨hc, hcx⟩)
      have habove : ∀ c ∈ C, x < c → b ≤ c := by
        intro c hc hxc
        exact Finset.min'_le _ c (Finset.mem_filter.mpr ⟨hc, hxc⟩)
      let yl := (max a l + x) / 2
      let yr := (x + min b u) / 2
      have hayl : a < yl := by dsimp [yl]; linarith [le_max_left a l, ha.2, hxl.1]
      have hylx : yl < x := by dsimp [yl]; linarith [max_lt ha.2 hxl.1]
      have hxyr : x < yr := by dsimp [yr]; linarith [lt_min hb.2 hxl.2]
      have hyrb : yr < b := by dsimp [yr]; linarith [min_le_left b u, hb.2, hxl.2]
      have hylE : yl ∈ E := hnhd ⟨by dsimp [yl]; linarith [le_max_right a l, hxl.1], hylx.trans hxl.2⟩
      have hyrE : yr ∈ E := hnhd ⟨hxl.1.trans hxyr, by dsimp [yr]; linarith [min_le_right b u, hxl.2]⟩
      obtain ⟨p', hp', hpyl⟩ := Set.mem_iUnion₂.mp hylE
      obtain ⟨q', hq', hqyr⟩ := Set.mem_iUnion₂.mp hyrE
      have hp'a : p'.1 ≤ a := hbelow p'.1 (hleft p' hp') (hpyl.1.trans_lt hylx)
      have hxp' : x ≤ p'.2 := by
        by_contra hn
        have hpa := hbelow p'.2 (hright p' hp') (lt_of_not_ge hn)
        linarith [hpyl.2]
      have hq'x : q'.1 ≤ x := by
        by_contra hn
        have hbq := habove q'.1 (hleft q' hq') (lt_of_not_ge hn)
        linarith [hqyr.1]
      have hbq' : b ≤ q'.2 := habove q'.2 (hright q' hq') (hxyr.trans_le hqyr.2)
      have hI : Set.Ioo a b ⊆ E := by
        intro y hy
        by_cases hyx : y ≤ x
        · exact Set.mem_iUnion₂.mpr ⟨p', hp', hp'a.trans hy.1.le, hyx.trans hxp'⟩
        · exact Set.mem_iUnion₂.mpr ⟨q', hq', hq'x.trans (le_of_not_ge hyx), hy.2.le.trans hbq'⟩
      have hIQ : Set.Ioo a b ⊆ Q := isOpen_Ioo.subset_interior_iff.mpr hI
      apply Set.mem_iUnion₂.mpr
      refine ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha.1, hb.1⟩,
        ha.2.trans hb.2, hIQ⟩, ha.2, hb.2⟩
    · intro hx
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hx
      exact (Finset.mem_filter.mp hp).2.2 hxp
  · intro p hp
    exact Finset.mem_product.mp (Finset.mem_filter.mp hp).1

theorem footprint_finite_intervals :
  ∀ K : PolygonalRegion, ∃ J : Finset (ℝ × ℝ),
    (∀ p ∈ J, p.1 < p.2) ∧
    regularizedProjection K.openCarrier = ⋃ p ∈ J, Set.Ioo p.1 p.2 ∧
    (∀ p ∈ J, ∃ v ∈ vertexSet K.support, ∃ w ∈ vertexSet K.support,
      p.1 = v.re ∧ p.2 = w.re)
  := by
  intro K
  obtain ⟨J, hJ, hraw, hend⟩ := rawProjection_finite_intervals K
  obtain ⟨L, hL, hreg, hends⟩ := finite_interval_regularization J hJ
  refine ⟨L, hL, ?_, ?_⟩
  · unfold regularizedProjection
    rw [hraw]
    exact hreg
  · have hvertex : ∀ c ∈ J.image Prod.fst ∪ J.image Prod.snd,
        ∃ v ∈ vertexSet K.support, c = v.re := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨v, hv, w, hw, hvl, hwr⟩ := hend p hp
        exact ⟨v, hv, hvl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨v, hv, w, hw, hvl, hwr⟩ := hend p hp
        exact ⟨w, hw, hwr⟩
    intro p hp
    obtain ⟨v, hv, hvl⟩ := hvertex p.1 (hends p hp).1
    obtain ⟨w, hw, hwr⟩ := hvertex p.2 (hends p hp).2
    exact ⟨v, hv, w, hw, hvl, hwr⟩

/-- Finite critical slabs, hence a uniform positive slice-width lower bound.
No asymptotic uniformity in d is needed by the constructor. -/
private theorem finite_uniform_slice_width (I : Set ℤ) (hI : I.Finite)
    (x : ℤ → ℝ) (U : Set Plane)
    (hslice : ∀ i ∈ I, ∃ a b : ℝ, a < b ∧
      ∀ y ∈ Set.Ioo a b, x i + y * Complex.I ∈ U) :
    ∃ w : ℝ, 0 < w ∧ ∀ i ∈ I, ∃ a b : ℝ, w ≤ b - a ∧
      ∀ y ∈ Set.Ioo a b, x i + y * Complex.I ∈ U := by
  classical
  induction I, hI using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert i I hi hI ih =>
      obtain ⟨a, b, hab, hs⟩ := hslice i (Set.mem_insert i I)
      obtain ⟨w, hw, hwidth⟩ := ih (fun j hj => hslice j (Set.mem_insert_of_mem i hj))
      refine ⟨min w (b - a), lt_min hw (sub_pos.mpr hab), ?_⟩
      intro j hj
      rcases Set.mem_insert_iff.mp hj with rfl | hj
      · exact ⟨a, b, min_le_right _ _, hs⟩
      · obtain ⟨a', b', hwidth', hs'⟩ := hwidth j hj
        exact ⟨a', b', (min_le_left _ _).trans hwidth', hs'⟩

theorem midpoint_slice_width :
  ∀ (K : PolygonalRegion) (d : ℕ), 0 < d →
    (∀ v ∈ vertexSet K.support, ∃ z : IntegerPlane,
      v = (d : ℝ)⁻¹ • integerPoint z) →
    ∃ c : ℝ, 0 < c ∧ ∀ i : ℤ,
      let x := ((i : ℝ) + 1 / 2) / (d : ℝ)
      x ∈ Complex.re '' K.openCarrier →
      ∃ a b : ℝ, c / (d : ℝ) ≤ b - a ∧
        ∀ y ∈ Set.Ioo a b, (x + y * Complex.I) ∈ K.openCarrier
  := by
  intro K d hd _hvertices
  have hdreal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  let x : ℤ → ℝ := fun i => ((i : ℝ) + 1 / 2) / (d : ℝ)
  let I : Set ℤ := {i | x i ∈ Complex.re '' K.openCarrier}
  have hx : Topology.IsClosedEmbedding x := by
    exact ((Homeomorph.mulRight₀ (d : ℝ)⁻¹ (inv_ne_zero hdreal)).isClosedEmbedding.comp
      ((Homeomorph.addRight (1 / 2 : ℝ)).isClosedEmbedding.comp
        Int.isClosedEmbedding_coe_real))
  have hfinite : I.Finite := by
    apply Set.Finite.subset
      ((hx.isCompact_preimage (K.isPolygonal.isCompact.image Complex.continuous_re)).finite_of_discrete)
    intro i hi
    obtain ⟨p, hp, hpx⟩ := hi
    exact ⟨p, interior_subset hp, hpx⟩
  have hslice : ∀ i ∈ I, ∃ a b : ℝ, a < b ∧
      ∀ y ∈ Set.Ioo a b, x i + y * Complex.I ∈ K.openCarrier := by
    intro i hi
    obtain ⟨p, hp, hpx⟩ := hi
    let V : Set ℝ := {y | x i + y * Complex.I ∈ K.openCarrier}
    have hopen : IsOpen V := isOpen_interior.preimage (by fun_prop)
    have hnonempty : V.Nonempty := by
      refine ⟨p.im, ?_⟩
      change (x i : Plane) + p.im * Complex.I ∈ K.openCarrier
      have heq : (x i : Plane) + p.im * Complex.I = p := by
        apply Complex.ext <;> simp [← hpx]
      simpa [heq] using hp
    obtain ⟨a, b, hab, hV⟩ := hopen.exists_Ioo_subset hnonempty
    exact ⟨a, b, hab, hV⟩
  obtain ⟨w, hw, hwidth⟩ := finite_uniform_slice_width I hfinite x K.openCarrier hslice
  refine ⟨(d : ℝ) * w, mul_pos (by exact_mod_cast hd) hw, ?_⟩
  intro i
  dsimp only
  intro hi
  obtain ⟨a, b, hab, hs⟩ := hwidth i hi
  exact ⟨a, b, by simpa [mul_div_cancel_left₀ _ hdreal] using hab, hs⟩

private theorem gridPoint_isClosedEmbedding (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    Topology.IsClosedEmbedding (gridPoint h k) := by
  let hcoords : IntegerPlane ≃ₜ ℤ × ℤ := Homeomorph.finTwoArrow
  have hx := (Homeomorph.mulLeft₀ h hh.ne').isClosedEmbedding.comp
    Int.isClosedEmbedding_coe_real
  have hy := (Homeomorph.mulLeft₀ k hk.ne').isClosedEmbedding.comp
    Int.isClosedEmbedding_coe_real
  have hp := (hx.prodMap hy).comp hcoords.isClosedEmbedding
  have hc := Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding.comp hp
  convert hc using 1
  funext z
  change gridPoint h k z =
    Complex.equivRealProdCLM.symm (h * (z 0 : ℝ), k * (z 1 : ℝ))
  simp [gridPoint, Complex.equivRealProdCLM_symm_apply]

private theorem sampledIndices_finite (K : PolygonalRegion) (h k : ℝ) (u : Plane)
    (hh : 0 < h) (hk : 0 < k) : (sampledIndices K h k u).Finite := by
  have he := (Homeomorph.addLeft u).isClosedEmbedding.comp
    (gridPoint_isClosedEmbedding h k hh hk)
  apply ((he.isCompact_preimage K.isPolygonal.isCompact).finite_of_discrete).subset
  intro z hz
  change u + gridPoint h k z ∈ K.support
  exact interior_subset hz

private theorem sample_segment_offsets_finite (h k : ℝ) (hh : 0 < h)
    (z : IntegerPlane) (a b : Plane) (m : ℤ) (ha : a.re = h * (m : ℝ)) :
    {θ : ℝ | (h / 2 : Plane) + θ * Complex.I + gridPoint h k z ∈
      segment ℝ a b}.Finite := by
  apply Set.Subsingleton.finite
  intro θ hθ η hη
  rw [segment_eq_image_lineMap] at hθ hη
  obtain ⟨s, hs, hsx⟩ := hθ
  obtain ⟨t, ht, htx⟩ := hη
  have hsre : s * (b.re - a.re) + a.re = h / 2 + h * (z 0 : ℝ) := by
    simpa [AffineMap.lineMap_apply_module', gridPoint] using congrArg Complex.re hsx
  have htre : t * (b.re - a.re) + a.re = h / 2 + h * (z 0 : ℝ) := by
    simpa [AffineMap.lineMap_apply_module', gridPoint] using congrArg Complex.re htx
  by_cases hab : a.re = b.re
  · have heq : (z 0 : ℝ) + 1 / 2 = (m : ℝ) := by
      rw [← hab, ha] at hsre
      nlinarith
    have hi : 2 * z 0 + 1 = 2 * m := by
      exact_mod_cast (show 2 * (z 0 : ℝ) + 1 = 2 * (m : ℝ) by linarith)
    omega
  · have hst : s = t := by
      have hmul : (s - t) * (b.re - a.re) = 0 := by nlinarith [hsre, htre]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr (Ne.symm hab)))
    have heq : (h / 2 : Plane) + θ * Complex.I + gridPoint h k z =
        (h / 2 : Plane) + η * Complex.I + gridPoint h k z := by
      rw [← hsx, ← htx, hst]
    simpa using congrArg Complex.im heq

private theorem sample_boundary_offset_exists (K : PolygonalRegion) (h k : ℝ)
    (hh : 0 < h) (hk : 0 < k)
    (hmesh : ∀ a ∈ vertexSet K.support, ∃ m : ℤ, a.re = h * (m : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ θ < k ∧ ∀ z : IntegerPlane,
      (h / 2 : Plane) + θ * Complex.I + gridPoint h k z ∉ frontier K.support := by
  classical
  let Q : Set Plane := (fun p : Plane × ℝ => p.1 - ((h / 2 : Plane) + p.2 * Complex.I)) ''
    (K.support ×ˢ Set.Icc 0 k)
  have hQ : IsCompact Q := (K.isPolygonal.isCompact.prod isCompact_Icc).image (by fun_prop)
  let Z : Set IntegerPlane := gridPoint h k ⁻¹' Q
  have hZ : Z.Finite :=
    ((gridPoint_isClosedEmbedding h k hh hk).isCompact_preimage hQ).finite_of_discrete
  obtain ⟨E, hE, hfront⟩ := K.isPolygonal.exists_finite_intrinsic_boundarySegments
  let B : Set ℝ := ⋃ z ∈ Z, ⋃ e ∈ E,
    {θ : ℝ | (h / 2 : Plane) + θ * Complex.I + gridPoint h k z ∈ segment ℝ e.1 e.2}
  have hB : B.Finite := by
    apply hZ.biUnion
    intro z hz
    apply E.finite_toSet.biUnion
    intro e he
    obtain ⟨m, hm⟩ := hmesh e.1 (hE e he).2.1
    exact sample_segment_offsets_finite h k hh z e.1 e.2 m hm
  obtain ⟨θ, hθ, hθB⟩ := ((Set.Ioo_infinite hk).sdiff hB).nonempty
  refine ⟨θ, hθ.1, hθ.2, ?_⟩
  intro z hz
  have hp : (h / 2 : Plane) + θ * Complex.I + gridPoint h k z ∈ K.support :=
    K.isPolygonal.isCompact.isClosed.closure_eq ▸ frontier_subset_closure hz
  have hzZ : z ∈ Z := by
    refine ⟨((h / 2 : Plane) + θ * Complex.I + gridPoint h k z, θ),
      ⟨hp, hθ.1.le, hθ.2.le⟩, ?_⟩
    dsimp
    abel
  rw [hfront] at hz
  obtain ⟨e, he, hze⟩ := Set.mem_iUnion₂.mp hz
  exact hθB (Set.mem_iUnion₂.mpr ⟨z, hzZ, Set.mem_iUnion₂.mpr ⟨e, he, hze⟩⟩)

private theorem arithmetic_progression_hits_interval (a b θ k : ℝ)
    (hk : 0 < k) (hwidth : k < b - a) :
    ∃ j : ℤ, θ + k * (j : ℝ) ∈ Set.Ioo a b := by
  let j : ℤ := ⌊(a - θ) / k⌋ + 1
  have hlo := Int.lt_floor_add_one ((a - θ) / k)
  have hhi := Int.floor_le ((a - θ) / k)
  have hj : (j : ℝ) = (⌊(a - θ) / k⌋ : ℝ) + 1 := by simp [j]
  refine ⟨j, ?_, ?_⟩
  · have ht : a - θ < k * (j : ℝ) := by
      rw [mul_comm k]
      apply (div_lt_iff₀ hk).mp
      simp [hj]
    linarith
  · have ht : k * ((j : ℝ) - 1) ≤ a - θ := by
      rw [mul_comm k]
      apply (le_div_iff₀ hk).mp
      simpa [hj] using hhi
    nlinarith

theorem sample_grid_exists :
  ∀ (K : PolygonalRegion) (d : ℕ), 0 < d →
    (∀ v ∈ vertexSet K.support, ∃ z : IntegerPlane,
      v = (d : ℝ)⁻¹ • integerPoint z) →
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ,
      0 < θ ∧ θ < ((d * N : ℕ) : ℝ)⁻¹ ∧
      let h := (d : ℝ)⁻¹
      let k := ((d * N : ℕ) : ℝ)⁻¹
      let u := h / 2 + θ * Complex.I
      (∀ z : IntegerPlane, u + gridPoint h k z ∉ frontier K.support) ∧
      (sampledIndices K h k u).Finite ∧
      (sampledIndices K h k u).Nonempty ∧
      (∀ i : ℤ, h * ((i : ℝ) + 1 / 2) ∈ Complex.re '' K.openCarrier ↔
        ∃ z ∈ sampledIndices K h k u, z 0 = i)
  := by
  intro K d hd hvertices
  let h : ℝ := (d : ℝ)⁻¹
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hh : 0 < h := inv_pos.mpr hdR
  have hmesh : ∀ a ∈ vertexSet K.support, ∃ m : ℤ, a.re = h * (m : ℝ) := by
    intro a ha
    obtain ⟨z, rfl⟩ := hvertices a ha
    exact ⟨z 0, by simp [h]⟩
  obtain ⟨c, hc, hwidth⟩ := midpoint_slice_width K d hd hvertices
  obtain ⟨N, hN⟩ := exists_nat_gt c⁻¹
  have hNR : 0 < (N : ℝ) := lt_trans (inv_pos.mpr hc) hN
  have hNpos : 0 < N := by exact_mod_cast hNR
  let k : ℝ := ((d * N : ℕ) : ℝ)⁻¹
  have hk : 0 < k := inv_pos.mpr (by simpa [Nat.cast_mul] using mul_pos hdR hNR)
  have hkc : k < c / (d : ℝ) := by
    have hcn : 1 < c * (N : ℝ) := by
      have ht := mul_lt_mul_of_pos_left hN hc
      simpa [mul_inv_cancel₀ hc.ne'] using ht
    dsimp [k]
    apply (inv_lt_iff_one_lt_mul₀ (by simpa [Nat.cast_mul] using mul_pos hdR hNR)).mpr
    rw [Nat.cast_mul]
    nlinarith [div_mul_cancel₀ c hdR.ne']
  obtain ⟨θ, hθ0, hθk, hθboundary⟩ := sample_boundary_offset_exists K h k hh hk hmesh
  let u : Plane := (h / 2 : Plane) + θ * Complex.I
  have hcol : ∀ i : ℤ, h * ((i : ℝ) + 1 / 2) ∈ Complex.re '' K.openCarrier ↔
      ∃ z ∈ sampledIndices K h k u, z 0 = i := by
    intro i
    constructor
    · intro hi
      have hi' : ((i : ℝ) + 1 / 2) / (d : ℝ) ∈ Complex.re '' K.openCarrier := by
        simpa [h, div_eq_mul_inv, mul_comm] using hi
      obtain ⟨a, b, hab, hslice⟩ := hwidth i hi'
      obtain ⟨j, hj⟩ := arithmetic_progression_hits_interval a b θ k hk (hkc.trans_le hab)
      let z : IntegerPlane := ![i, j]
      refine ⟨z, ?_, rfl⟩
      change u + gridPoint h k z ∈ K.openCarrier
      have heq : u + gridPoint h k z =
          (h * ((i : ℝ) + 1 / 2) : Plane) + (θ + k * (j : ℝ)) * Complex.I := by
        apply Complex.ext <;> simp [u, gridPoint, z] <;> ring
      rw [heq]
      simpa [h, div_eq_mul_inv, mul_comm] using hslice _ hj
    · rintro ⟨z, hz, hzi⟩
      refine ⟨u + gridPoint h k z, hz, ?_⟩
      simp [u, gridPoint, hzi]
      ring
  have hnonempty : (sampledIndices K h k u).Nonempty := by
    obtain ⟨J, hJ, hraw, hend⟩ := rawProjection_finite_intervals K
    obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
    have hxre : x.re ∈ Complex.re '' K.openCarrier := ⟨x, hx, rfl⟩
    rw [hraw] at hxre
    obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp hxre
    obtain ⟨v, hv, w, hw, hvp, hwp⟩ := hend p hp
    obtain ⟨m, hm⟩ := hmesh v hv
    obtain ⟨n, hn⟩ := hmesh w hw
    have hmnR : (m : ℝ) < (n : ℝ) := by
      apply (mul_lt_mul_iff_right₀ hh).mp
      simpa [hvp, hwp, hm, hn] using hJ p hp
    have hmn : m + 1 ≤ n := by
      have hmni : m < n := by exact_mod_cast hmnR
      omega
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hmn
    have hmid : h * ((m : ℝ) + 1 / 2) ∈ Complex.re '' K.openCarrier := by
      rw [hraw]
      apply Set.mem_iUnion₂.mpr
      refine ⟨p, hp, ?_, ?_⟩
      · rw [hvp, hm]
        nlinarith
      · rw [hwp, hn]
        nlinarith
    obtain ⟨z, hz, _⟩ := (hcol m).mp hmid
    exact ⟨z, hz⟩
  exact ⟨N, hNpos, θ, hθ0, hθk, hθboundary,
    sampledIndices_finite K h k u hh hk, hnonempty, hcol⟩

private theorem gridPoint_add (h k : ℝ) (a b : IntegerPlane) :
    gridPoint h k (a + b) = gridPoint h k a + gridPoint h k b := by
  apply Complex.ext <;> simp [gridPoint] <;> ring

private theorem gridPoint_sub (h k : ℝ) (a b : IntegerPlane) :
    gridPoint h k (a - b) = gridPoint h k a - gridPoint h k b := by
  apply Complex.ext <;> simp [gridPoint] <;> ring

private theorem gridPoint_injective (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    Function.Injective (gridPoint h k) := by
  intro a b hab
  have hre : h * (a 0 : ℝ) = h * (b 0 : ℝ) := by
    simpa [gridPoint] using congrArg Complex.re hab
  have him : k * (a 1 : ℝ) = k * (b 1 : ℝ) := by
    simpa [gridPoint] using congrArg Complex.im hab
  have hzero : a 0 = b 0 := by exact_mod_cast mul_left_cancel₀ hh.ne' hre
  have hone : a 1 = b 1 := by exact_mod_cast mul_left_cancel₀ hk.ne' him
  funext i
  fin_cases i <;> assumption

theorem sampled_grid_unique_owner :
  ∀ (K : PolygonalRegion) (h k : ℝ) (u : Plane) (A : Set IntegerPlane),
    0 < h → 0 < k → TilesOn K (gridPoint h k '' A) Set.univ →
    (∀ z : IntegerPlane, u + gridPoint h k z ∉ frontier K.support) →
    ∀ z : IntegerPlane, ∃! a : A,
      u + gridPoint h k z ∈ (gridPoint h k a.1 +ᵥ K.openCarrier)
  := by
  intro K h k u A hh hk htiles havoid z
  let x := u + gridPoint h k z
  have hreg : regularSupport K (gridPoint h k '' A) = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htiles
  have hxclosure : x ∈ closure (openUnion K (gridPoint h k '' A)) := by
    apply interior_subset
    change x ∈ regularSupport K (gridPoint h k '' A)
    rw [hreg]
    trivial
  rw [closure_openUnion_eq_iUnion_support htiles.2.1] at hxclosure
  obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hxclosure
  obtain ⟨a, ha, hga⟩ := s.2
  have hsupport : -gridPoint h k a + x ∈ K.support := by
    simpa [hga, vadd_eq_add] using Set.mem_vadd_set_iff_neg_vadd_mem.mp hxs
  have hreduce : -gridPoint h k a + x = u + gridPoint h k (z - a) := by
    rw [gridPoint_sub]
    dsimp [x]
    abel
  have hopen : -gridPoint h k a + x ∈ K.openCarrier := by
    exact (mem_interior_iff_notMem_frontier hsupport).mpr
      (hreduce ▸ havoid (z - a))
  refine ⟨⟨a, ha⟩, Set.mem_vadd_set_iff_neg_vadd_mem.mpr hopen, ?_⟩
  intro b hb
  apply Subtype.ext
  apply gridPoint_injective h k hh hk
  by_contra hne
  have hdisj := (isPacking_iff_openCarrier_disjoint K _).mp htiles.2.1
    ⟨b.1, b.2, rfl⟩ ⟨a, ha, rfl⟩ hne
  exact Set.disjoint_left.mp hdisj hb
    (Set.mem_vadd_set_iff_neg_vadd_mem.mpr hopen)

theorem sampled_finite_tile_exact :
  ∀ (K : PolygonalRegion) (h k : ℝ) (u : Plane)
    (F : Finset IntegerPlane) (A : Set IntegerPlane),
    0 < h → 0 < k → TilesOn K (gridPoint h k '' A) Set.univ →
    (∀ z : IntegerPlane, u + gridPoint h k z ∉ frontier K.support) →
    (↑F : Set IntegerPlane) = sampledIndices K h k u →
    TranslationalTilings.Tiles F A Set.univ
  := by
  intro K h k u F A hh hk htiles havoid hF
  have hmem (z a : IntegerPlane) :
      u + gridPoint h k z ∈ gridPoint h k a +ᵥ K.openCarrier ↔ z - a ∈ F := by
    rw [← Finset.mem_coe, hF]
    change _ ↔ u + gridPoint h k (z - a) ∈ K.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have heq : -gridPoint h k a + (u + gridPoint h k z) =
        u + gridPoint h k (z - a) := by rw [gridPoint_sub]; abel
    exact heq ▸ Iff.rfl
  apply Tiling.RationalPolygonal.tilesUniverse_of_existsUnique
  intro z
  obtain ⟨a, ha, huniq⟩ := sampled_grid_unique_owner K h k u A hh hk htiles havoid z
  refine ⟨z - a.1, ⟨(hmem z a.1).mp ha, by simp⟩, ?_⟩
  intro f hf
  let b : A := ⟨z - f, hf.2⟩
  have hb : u + gridPoint h k z ∈ gridPoint h k b.1 +ᵥ K.openCarrier :=
    (hmem z b.1).mpr (by simpa [b] using hf.1)
  have hba := congrArg Subtype.val (huniq b hb)
  change z - f = a.1 at hba
  rw [← hba]
  abel

private theorem gridCell_interior_contains (h k : ℝ) (z : IntegerPlane) (x : Plane)
    (hx : h * (z 0 : ℝ) < x.re ∧ x.re < h * ((z 0 : ℝ) + 1) ∧
      k * (z 1 : ℝ) < x.im ∧ x.im < k * ((z 1 : ℝ) + 1)) :
    x ∈ interior (gridCell h k z) := by
  let U : Set Plane := {y | h * (z 0 : ℝ) < y.re ∧ y.re < h * ((z 0 : ℝ) + 1) ∧
      k * (z 1 : ℝ) < y.im ∧ y.im < k * ((z 1 : ℝ) + 1)}
  have hopen : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hsub : U ⊆ gridCell h k z := fun _ hy => ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩
  exact (hopen.subset_interior_iff.mpr hsub) hx

private theorem cellSupport_projection_closure (h k : ℝ) (F : Finset IntegerPlane)
    (hh : 0 < h) (hk : 0 < k) :
    closure (Complex.re '' interior (cellSupport h k F)) =
      ⋃ i ∈ F.image (fun z : IntegerPlane => (z 0 : ℤ)),
        Set.Icc (h * (i : ℝ)) (h * ((i : ℝ) + 1)) := by
  classical
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro r ⟨x, hx, rfl⟩
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (interior_subset hx)
      exact Set.mem_iUnion₂.mpr ⟨z 0, Finset.mem_image.mpr ⟨z, hz, rfl⟩, hxz.1, hxz.2.1⟩
    · exact isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  · intro r hr
    obtain ⟨i, hi, hri⟩ := Set.mem_iUnion₂.mp hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hi
    have hwidth : h * (z 0 : ℝ) < h * ((z 0 : ℝ) + 1) := by nlinarith
    rw [← closure_Ioo hwidth.ne] at hri
    apply closure_mono (t := Complex.re '' interior (cellSupport h k F)) ?_ hri
    intro q hq
    let y : ℝ := k * ((z 1 : ℝ) + 1 / 2)
    let x : Plane := q + (y : Plane) * Complex.I
    refine ⟨x, ?_, by simp [x]⟩
    apply interior_mono (Set.subset_iUnion₂ z hz)
    apply gridCell_interior_contains
    have hxr : x.re = q := by simp [x]
    have hxim : x.im = y := by simp [x]
    rw [hxr, hxim]
    dsimp [y]
    exact ⟨hq.1, hq.2, by nlinarith, by nlinarith⟩

private theorem integer_midpoint_bounds (h : ℝ) (hh : 0 < h) (m n i : ℤ)
    (hmid : h * ((i : ℝ) + 1 / 2) ∈ Set.Ioo (h * (m : ℝ)) (h * (n : ℝ))) :
    m ≤ i ∧ i + 1 ≤ n := by
  have hl : (m : ℝ) < (i : ℝ) + 1 / 2 := (mul_lt_mul_iff_right₀ hh).mp hmid.1
  have hr : (i : ℝ) + 1 / 2 < (n : ℝ) := (mul_lt_mul_iff_right₀ hh).mp hmid.2
  constructor
  · by_contra hn
    have hmi : i + 1 ≤ m := by omega
    have hmi' : (i : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmi
    linarith
  · by_contra hn
    have hni : n ≤ i := by omega
    have hni' : (n : ℝ) ≤ (i : ℝ) := by exact_mod_cast hni
    linarith

private theorem mesh_projection_closure (U : Set Plane) (h : ℝ) (hh : 0 < h)
    (J : Finset (ℝ × ℝ))
    (hraw : Complex.re '' U = ⋃ p ∈ J, Set.Ioo p.1 p.2)
    (hmesh : ∀ p ∈ J, ∃ m n : ℤ, p.1 = h * (m : ℝ) ∧ p.2 = h * (n : ℝ))
    (C : Finset ℤ)
    (hcol : ∀ i : ℤ, h * ((i : ℝ) + 1 / 2) ∈ Complex.re '' U ↔ i ∈ C) :
    closure (Complex.re '' U) =
      ⋃ i ∈ C, Set.Icc (h * (i : ℝ)) (h * ((i : ℝ) + 1)) := by
  classical
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro q hq
      rw [hraw] at hq
      obtain ⟨p, hp, hqp⟩ := Set.mem_iUnion₂.mp hq
      obtain ⟨m, n, hml, hnr⟩ := hmesh p hp
      rw [hml, hnr] at hqp
      let i : ℤ := ⌊q / h⌋
      have hmq : (m : ℝ) < q / h := (lt_div_iff₀ hh).mpr (by nlinarith [hqp.1])
      have hqn : q / h < (n : ℝ) := (div_lt_iff₀ hh).mpr (by nlinarith [hqp.2])
      have hmi : m ≤ i := Int.le_floor.mpr hmq.le
      have hin : i + 1 ≤ n := by
        have hi : i < n := Int.floor_lt.mpr hqn
        omega
      have hmi' : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hmi
      have hin' : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hin
      have hmid : h * ((i : ℝ) + 1 / 2) ∈ Complex.re '' U := by
        rw [hraw]
        apply Set.mem_iUnion₂.mpr
        refine ⟨p, hp, ?_⟩
        rw [hml, hnr]
        constructor <;> nlinarith
      have hl := Int.floor_le (q / h)
      have hr := Int.lt_floor_add_one (q / h)
      have hl' : h * (i : ℝ) ≤ q := by
        have hm := (le_div_iff₀ hh).mp hl
        simpa [i, mul_comm] using hm
      have hr' : q ≤ h * ((i : ℝ) + 1) := by
        have hm := (div_lt_iff₀ hh).mp hr
        simpa [i, mul_comm] using hm.le
      exact Set.mem_iUnion₂.mpr ⟨i, (hcol i).mp hmid, hl', hr'⟩
    · exact isClosed_biUnion_finset (fun _ _ => isClosed_Icc)
  · intro q hq
    obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.mp hq
    have hmid := (hcol i).mpr hi
    rw [hraw] at hmid
    obtain ⟨p, hp, hmidp⟩ := Set.mem_iUnion₂.mp hmid
    obtain ⟨m, n, hml, hnr⟩ := hmesh p hp
    rw [hml, hnr] at hmidp
    obtain ⟨hmi, hin⟩ := integer_midpoint_bounds h hh m n i hmidp
    have hmi' : (m : ℝ) ≤ (i : ℝ) := by exact_mod_cast hmi
    have hin' : (i : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hin
    have hwidth : h * (i : ℝ) < h * ((i : ℝ) + 1) := by nlinarith
    rw [← closure_Ioo hwidth.ne] at hqi
    apply closure_mono (t := Complex.re '' U) ?_ hqi
    intro r hr
    rw [hraw]
    apply Set.mem_iUnion₂.mpr
    refine ⟨p, hp, ?_⟩
    rw [hml, hnr]
    constructor <;> nlinarith [hr.1, hr.2]

theorem sampled_cell_footprint :
  ∀ (K : PolygonalRegion) (d N : ℕ) (θ : ℝ) (F : Finset IntegerPlane),
    0 < d → 0 < N →
    (∀ v ∈ vertexSet K.support, ∃ z : IntegerPlane,
      v = (d : ℝ)⁻¹ • integerPoint z) →
    let h := (d : ℝ)⁻¹
    let k := ((d * N : ℕ) : ℝ)⁻¹
    let u := h / 2 + θ * Complex.I
    (↑F : Set IntegerPlane) = sampledIndices K h k u →
    (∀ i : ℤ, h * ((i : ℝ) + 1 / 2) ∈ Complex.re '' K.openCarrier ↔
      i ∈ occupiedColumns F) →
    regularizedProjection (interior (cellSupport h k F)) =
      regularizedProjection K.openCarrier
  := by
  intro K d N θ F hd hN hvertices
  dsimp only
  intro _hF hcolumns
  have hh : 0 < (d : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hd)
  have hk : 0 < ((d * N : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast Nat.mul_pos hd hN)
  obtain ⟨J, _hJ, hraw, hend⟩ := rawProjection_finite_intervals K
  have hmesh : ∀ p ∈ J, ∃ m n : ℤ,
      p.1 = (d : ℝ)⁻¹ * (m : ℝ) ∧ p.2 = (d : ℝ)⁻¹ * (n : ℝ) := by
    intro p hp
    obtain ⟨v, hv, w, hw, hvl, hwr⟩ := hend p hp
    obtain ⟨z, hz⟩ := hvertices v hv
    obtain ⟨q, hq⟩ := hvertices w hw
    refine ⟨z 0, q 0, ?_, ?_⟩
    · rw [hvl, hz]
      simp
    · rw [hwr, hq]
      simp
  have hC : ∀ i : ℤ, i ∈ occupiedColumns F ↔ i ∈ F.image (fun z => z 0) := by
    intro i
    simp only [occupiedColumns, Set.mem_ofPred_eq, Finset.mem_image]
  have hproj := mesh_projection_closure K.openCarrier (d : ℝ)⁻¹ hh J hraw hmesh
    (F.image (fun z => z 0)) (fun i => (hcolumns i).trans (hC i))
  unfold regularizedProjection
  rw [cellSupport_projection_closure _ _ F hh hk, hproj]

private def flattenTriangulations {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (pieces : ι → Set Plane)
    (T : ∀ i ∈ F, Tiling.Triangulation (pieces i))
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      MeasureTheory.AEDisjoint MeasureTheory.volume (pieces i) (pieces j)) :
    Tiling.Triangulation (⋃ i ∈ F, pieces i) := by
  classical
  refine ⟨F.attach.biUnion (fun i ↦ (T i.1 i.2).pieces), ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
    exact (T i.1 i.2).isTriangle t hti
  · intro a ha b hb hab
    obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb
    by_cases hij : i.1 = j.1
    · have hsub : i = j := Subtype.ext hij
      subst j
      exact (T i.1 i.2).pairwiseAEDisjoint hai hbj hab
    · apply (hdisj i.1 i.2 j.1 j.2 hij).mono
      · intro x hx
        rw [← (T i.1 i.2).sUnion_eq]
        exact Set.mem_sUnion.mpr ⟨a, hai, hx⟩
      · intro x hx
        rw [← (T j.1 j.2).sUnion_eq]
        exact Set.mem_sUnion.mpr ⟨b, hbj, hx⟩
  · ext x
    rw [Set.mem_sUnion]
    simp only [Finset.mem_coe, Finset.mem_biUnion, Finset.mem_attach, Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht, hxt⟩
      obtain ⟨i, _, hti⟩ := ht
      refine ⟨i.1, i.2, ?_⟩
      rw [← (T i.1 i.2).sUnion_eq]
      exact Set.mem_sUnion.mpr ⟨t, hti, hxt⟩
    · rintro ⟨i, hi, hxi⟩
      rw [← (T i hi).sUnion_eq] at hxi
      obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp hxi
      exact ⟨t, ⟨⟨i, hi⟩, True.intro, ht⟩, hxt⟩

private theorem gridCell_eq_rectangle (h k : ℝ) (z : IntegerPlane)
    (hh : 0 < h) (hk : 0 < k) :
    gridCell h k z = Complex.Rectangle
      ((↑(h * (z 0 : ℝ)) : ℂ) + (↑(k * (z 1 : ℝ) : ℝ)) * Complex.I)
      ((↑(h * ((z 0 : ℝ) + 1) : ℝ) : ℂ) +
        (↑(k * ((z 1 : ℝ) + 1) : ℝ)) * Complex.I) := by
  ext x
  have hhle : h * (z 0 : ℝ) ≤ h * ((z 0 : ℝ) + 1) := by
    calc
      h * (z 0 : ℝ) = h * (z 0 : ℝ) + 0 := by ring
      _ ≤ h * (z 0 : ℝ) + h := by linarith
      _ = h * ((z 0 : ℝ) + 1) := by ring
  have hkle : k * (z 1 : ℝ) ≤ k * ((z 1 : ℝ) + 1) := by
    calc
      k * (z 1 : ℝ) = k * (z 1 : ℝ) + 0 := by ring
      _ ≤ k * (z 1 : ℝ) + k := by linarith
      _ = k * ((z 1 : ℝ) + 1) := by ring
  simp only [gridCell, Complex.Rectangle, Complex.mem_reProdIm,
    Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero, add_zero,
    Complex.add_im, Complex.mul_im, Complex.I_im, mul_one, add_zero,
    Complex.ofReal_re, Complex.ofReal_im]
  simp only [sub_self, zero_add, add_zero]
  rw [Set.uIcc_of_le hhle, Set.uIcc_of_le hkle]
  simp only [Set.mem_Icc]
  simp only [and_assoc]
  rfl

private def cellCornerLL (h k : ℝ) (z : IntegerPlane) : Plane :=
  (↑(h * (z 0 : ℝ)) : ℂ) + (↑(k * (z 1 : ℝ) : ℝ)) * Complex.I

private def cellCornerUL (h k : ℝ) (z : IntegerPlane) : Plane :=
  (↑(h * (z 0 : ℝ)) : ℂ) + (↑(k * ((z 1 : ℝ) + 1) : ℝ)) * Complex.I

private def cellCornerLR (h k : ℝ) (z : IntegerPlane) : Plane :=
  (↑(h * ((z 0 : ℝ) + 1) : ℝ) : ℂ) + (↑(k * (z 1 : ℝ) : ℝ)) * Complex.I

private def cellCornerUR (h k : ℝ) (z : IntegerPlane) : Plane :=
  (↑(h * ((z 0 : ℝ) + 1) : ℝ) : ℂ) +
    (↑(k * ((z 1 : ℝ) + 1) : ℝ)) * Complex.I

private theorem cellCornerLL_re (h k : ℝ) (z : IntegerPlane) :
    (cellCornerLL h k z).re = h * (z 0 : ℝ) := by
  simp [cellCornerLL, Complex.ofReal_re, Complex.ofReal_im]
private theorem cellCornerLL_im (h k : ℝ) (z : IntegerPlane) :
    (cellCornerLL h k z).im = k * (z 1 : ℝ) := by
  simp [cellCornerLL, Complex.ofReal_re, Complex.ofReal_im]
private theorem cellCornerUR_re (h k : ℝ) (z : IntegerPlane) :
    (cellCornerUR h k z).re = h * ((z 0 : ℝ) + 1) := by
  simp [cellCornerUR, Complex.ofReal_re, Complex.ofReal_im]
private theorem cellCornerUR_im (h k : ℝ) (z : IntegerPlane) :
    (cellCornerUR h k z).im = k * ((z 1 : ℝ) + 1) := by
  simp [cellCornerUR, Complex.ofReal_re, Complex.ofReal_im]

private noncomputable def gridCellTriangulation (h k : ℝ) (z : IntegerPlane)
    (hh : 0 < h) (hk : 0 < k) : Tiling.Triangulation (gridCell h k z) := by
  let a : Plane := cellCornerLL h k z
  let b : Plane := cellCornerUR h k z
  have hre : a.re ≠ b.re := by
    have ha : a.re = h * (z 0 : ℝ) := by simpa [a] using cellCornerLL_re h k z
    have hb : b.re = h * ((z 0 : ℝ) + 1) := by simpa [b] using cellCornerUR_re h k z
    rw [ha, hb]
    nlinarith [hh]
  have him : a.im ≠ b.im := by
    have ha : a.im = k * (z 1 : ℝ) := by simpa [a] using cellCornerLL_im h k z
    have hb : b.im = k * ((z 1 : ℝ) + 1) := by simpa [b] using cellCornerUR_im h k z
    rw [ha, hb]
    nlinarith [hk]
  have heq : gridCell h k z = Complex.Rectangle a b := by
    simpa [a, b, cellCornerLL, cellCornerUR] using gridCell_eq_rectangle h k z hh hk
  let T := Tiling.rectangleDiagonalTriangulation a b hre him
  refine ⟨T.pieces, T.isTriangle, T.pairwiseAEDisjoint, ?_⟩
  rw [heq]
  exact T.sUnion_eq

private theorem gridCellTriangulation_pieces (h k : ℝ) (z : IntegerPlane)
    (hh : 0 < h) (hk : 0 < k) :
    (gridCellTriangulation h k z hh hk).pieces =
      {convexHull ℝ {cellCornerLL h k z, cellCornerUL h k z, cellCornerUR h k z},
        convexHull ℝ {cellCornerLL h k z, cellCornerLR h k z, cellCornerUR h k z}} := by
  classical
  unfold gridCellTriangulation
  simp only [Tiling.rectangleDiagonalTriangulation_pieces]
  congr 1 <;> ext x <;> simp [cellCornerLL, cellCornerUL, cellCornerLR, cellCornerUR]

private theorem cellSupport_isPolygonal_of_pairwiseAEDisjoint
    (F : Finset IntegerPlane) (h k : ℝ)
    (hh : 0 < h) (hk : 0 < k)
    (hdisj : ∀ z ∈ F, ∀ w ∈ F, z ≠ w →
      MeasureTheory.AEDisjoint MeasureTheory.volume (gridCell h k z) (gridCell h k w)) :
    Tiling.IsPolygonal (cellSupport h k F) := by
  classical
  let T : ∀ z : IntegerPlane, z ∈ F → Tiling.Triangulation (gridCell h k z) :=
    fun z _ ↦ gridCellTriangulation h k z hh hk
  exact ⟨flattenTriangulations F (gridCell h k) T hdisj⟩

private theorem volume_re_eq_zero_cell (c : ℝ) :
    MeasureTheory.volume {x : Plane | x.re = c} = 0 := by
  have hs : {x : Plane | x.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext x
    simp
  rw [hs, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  · exact (measurableSet_singleton c).prod MeasurableSet.univ |>.nullMeasurableSet

private theorem volume_im_eq_zero_cell (c : ℝ) :
    MeasureTheory.volume {x : Plane | x.im = c} = 0 := by
  have hs : {x : Plane | x.im = c} =
      Complex.measurableEquivRealProd ⁻¹' ((Set.univ : Set ℝ) ×ˢ {c}) := by
    ext x
    simp
  rw [hs, Complex.volume_preserving_equiv_real_prod.measure_preimage]
  · rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  · exact MeasurableSet.univ.prod (measurableSet_singleton c) |>.nullMeasurableSet

private theorem gridCells_aedisjoint (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    {z w : IntegerPlane} (hzw : z ≠ w) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (gridCell h k z) (gridCell h k w) := by
  rw [MeasureTheory.AEDisjoint]
  have hsub : gridCell h k z ∩ gridCell h k w ⊆
      ({x : Plane | x.re = h * ((z 0 : ℝ) + 1)} ∪
        {x | x.re = h * ((w 0 : ℝ) + 1)}) ∪
      ({x | x.im = k * ((z 1 : ℝ) + 1)} ∪
        {x | x.im = k * ((w 1 : ℝ) + 1)}) := by
    intro x hx
    rcases hx.1 with ⟨hzlo, hzhi, hzilo, hzihi⟩
    rcases hx.2 with ⟨hwlo, hwhi, hwilo, hwihi⟩
    by_cases h0 : z 0 = w 0
    · have h1 : z 1 ≠ w 1 := by
        intro heq
        apply hzw
        funext j
        fin_cases j
        · exact h0
        · exact heq
      rcases lt_or_gt_of_ne h1 with hlt | hgt
      · have hstep : z 1 + 1 ≤ w 1 := by omega
        have hstep' : (z 1 : ℝ) + 1 ≤ (w 1 : ℝ) := by exact_mod_cast hstep
        have hbound : k * ((z 1 : ℝ) + 1) ≤ k * (w 1 : ℝ) :=
          mul_le_mul_of_nonneg_left hstep' hk.le
        have heq : x.im = k * ((z 1 : ℝ) + 1) := by linarith
        exact Or.inr (Or.inl heq)
      · have hstep : w 1 + 1 ≤ z 1 := by omega
        have hstep' : (w 1 : ℝ) + 1 ≤ (z 1 : ℝ) := by exact_mod_cast hstep
        have hbound : k * ((w 1 : ℝ) + 1) ≤ k * (z 1 : ℝ) :=
          mul_le_mul_of_nonneg_left hstep' hk.le
        have heq : x.im = k * ((w 1 : ℝ) + 1) := by linarith
        exact Or.inr (Or.inr heq)
    · rcases lt_or_gt_of_ne h0 with hlt | hgt
      · have hstep : z 0 + 1 ≤ w 0 := by omega
        have hstep' : (z 0 : ℝ) + 1 ≤ (w 0 : ℝ) := by exact_mod_cast hstep
        have hbound : h * ((z 0 : ℝ) + 1) ≤ h * (w 0 : ℝ) :=
          mul_le_mul_of_nonneg_left hstep' hh.le
        have heq : x.re = h * ((z 0 : ℝ) + 1) := by linarith
        exact Or.inl (Or.inl heq)
      · have hstep : w 0 + 1 ≤ z 0 := by omega
        have hstep' : (w 0 : ℝ) + 1 ≤ (z 0 : ℝ) := by exact_mod_cast hstep
        have hbound : h * ((w 0 : ℝ) + 1) ≤ h * (z 0 : ℝ) :=
          mul_le_mul_of_nonneg_left hstep' hh.le
        have heq : x.re = h * ((w 0 : ℝ) + 1) := by linarith
        exact Or.inl (Or.inr heq)
  apply MeasureTheory.measure_mono_null hsub
  apply MeasureTheory.measure_union_null
  · apply MeasureTheory.measure_union_null <;> exact volume_re_eq_zero_cell _
  · apply MeasureTheory.measure_union_null <;> exact volume_im_eq_zero_cell _

private noncomputable def cellSupportTriangulation (F : Finset IntegerPlane)
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) : Tiling.Triangulation (cellSupport h k F) := by
  classical
  let T : ∀ z : IntegerPlane, z ∈ F → Tiling.Triangulation (gridCell h k z) :=
    fun z _ ↦ gridCellTriangulation h k z hh hk
  exact flattenTriangulations F (gridCell h k) T
    (fun z hz w hw hzw ↦ gridCells_aedisjoint h k hh hk hzw)

private theorem cellSupport_isPolygonal (F : Finset IntegerPlane) (h k : ℝ)
    (hh : 0 < h) (hk : 0 < k) : Tiling.IsPolygonal (cellSupport h k F) :=
  ⟨cellSupportTriangulation F h k hh hk⟩

private theorem cellSupport_vertex_subset_corners (F : Finset IntegerPlane)
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) {v : Plane}
    (hv : v ∈ Tiling.vertexSet (cellSupport h k F)) :
    ∃ z ∈ F, v = cellCornerLL h k z ∨ v = cellCornerUL h k z ∨
      v = cellCornerLR h k z ∨ v = cellCornerUR h k z := by
  classical
  let T := cellSupportTriangulation F h k hh hk
  obtain ⟨t, ht, htv⟩ := hv T
  change t ∈ F.attach.biUnion (fun i ↦ (gridCellTriangulation h k i.1 hh hk).pieces) at ht
  obtain ⟨i, hi, hti⟩ := Finset.mem_biUnion.mp ht
  rw [gridCellTriangulation_pieces] at hti
  simp only [Finset.mem_insert, Finset.mem_singleton] at hti
  refine ⟨i.1, i.2, ?_⟩
  rcases hti with htri | htri
  · rw [htri] at htv
    have hv3 : v ∈ ({cellCornerLL h k i.1, cellCornerUL h k i.1,
      cellCornerUR h k i.1} : Set Plane) := extremePoints_convexHull_subset htv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv3
    rcases hv3 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · rw [htri] at htv
    have hv3 : v ∈ ({cellCornerLL h k i.1, cellCornerLR h k i.1,
      cellCornerUR h k i.1} : Set Plane) := extremePoints_convexHull_subset htv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv3
    rcases hv3 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

private theorem gridCell_strict_mem_interior (h k : ℝ) (z : IntegerPlane) {x : Plane}
    (hx : h * (z 0 : ℝ) < x.re ∧ x.re < h * ((z 0 : ℝ) + 1) ∧
      k * (z 1 : ℝ) < x.im ∧ x.im < k * ((z 1 : ℝ) + 1)) :
    x ∈ interior (gridCell h k z) := by
  let s := Complex.re ⁻¹' Set.Ioo (h * (z 0 : ℝ)) (h * ((z 0 : ℝ) + 1)) ∩
    Complex.im ⁻¹' Set.Ioo (k * (z 1 : ℝ)) (k * ((z 1 : ℝ) + 1))
  have hsopen : IsOpen s := by
    dsimp [s]
    exact (isOpen_Ioo.preimage Complex.continuous_re).inter
      (isOpen_Ioo.preimage Complex.continuous_im)
  have hsub : s ⊆ gridCell h k z := by
    intro y hy
    rcases hy with ⟨⟨hyr0, hyr1⟩, ⟨hyi0, hyi1⟩⟩
    exact ⟨hyr0.le, hyr1.le, hyi0.le, hyi1.le⟩
  apply interior_maximal hsub hsopen
  exact ⟨⟨hx.1, hx.2.1⟩, ⟨hx.2.2.1, hx.2.2.2⟩⟩

private theorem cellSupport_frontier_subset_gridLines (F : Finset IntegerPlane)
    (h k : ℝ) (_hh : 0 < h) (_hk : 0 < k) {x : Plane}
    (hx : x ∈ frontier (cellSupport h k F)) :
    ∃ z ∈ F, x.re = h * (z 0 : ℝ) ∨ x.re = h * ((z 0 : ℝ) + 1) ∨
      x.im = k * (z 1 : ℝ) ∨ x.im = k * ((z 1 : ℝ) + 1) := by
  have hcellClosed : ∀ z, IsClosed (gridCell h k z) := by
    intro z
    rw [gridCell]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le Complex.continuous_re continuous_const).inter
        ((isClosed_le continuous_const Complex.continuous_im).inter
          (isClosed_le Complex.continuous_im continuous_const)))
  have hclosed : IsClosed (cellSupport h k F) := by
    unfold cellSupport
    exact F.finite_toSet.isClosed_biUnion (fun z hz ↦ hcellClosed z)
  have hxs : x ∈ cellSupport h k F := by
    have hxcl := frontier_subset_closure hx
    rwa [hclosed.closure_eq] at hxcl
  have hxnotint : x ∉ interior (cellSupport h k F) := by
    rw [hclosed.frontier_eq] at hx
    exact hx.2
  obtain ⟨z, hxzf, hxz⟩ : ∃ z ∈ F, x ∈ gridCell h k z := by
    simpa [cellSupport] using hxs
  rcases hxz with ⟨hxlo, hxhi, hylo, hyhi⟩
  by_cases hxloeq : x.re = h * (z 0 : ℝ)
  · exact ⟨z, hxzf, Or.inl hxloeq⟩
  by_cases hxhieq : x.re = h * ((z 0 : ℝ) + 1)
  · exact ⟨z, hxzf, Or.inr (Or.inl hxhieq)⟩
  by_cases hyloeq : x.im = k * (z 1 : ℝ)
  · exact ⟨z, hxzf, Or.inr (Or.inr (Or.inl hyloeq))⟩
  by_cases hyhieq : x.im = k * ((z 1 : ℝ) + 1)
  · exact ⟨z, hxzf, Or.inr (Or.inr (Or.inr hyhieq))⟩
  have hstrict : h * (z 0 : ℝ) < x.re ∧ x.re < h * ((z 0 : ℝ) + 1) ∧
      k * (z 1 : ℝ) < x.im ∧ x.im < k * ((z 1 : ℝ) + 1) := by
    refine ⟨lt_of_le_of_ne hxlo ?_, lt_of_le_of_ne hxhi ?_,
      lt_of_le_of_ne hylo ?_, lt_of_le_of_ne hyhi ?_⟩
    · intro heq
      exact hxloeq heq.symm
    · exact hxhieq
    · intro heq
      exact hyloeq heq.symm
    · exact hyhieq
  have hxintCell := gridCell_strict_mem_interior h k z hstrict
  have hcellSub : gridCell h k z ⊆ cellSupport h k F := by
    intro y hy
    change y ∈ ⋃ z ∈ F, gridCell h k z
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hxzf, hy⟩⟩
  have hxintSupport : x ∈ interior (cellSupport h k F) :=
    interior_mono hcellSub hxintCell
  exact (hxnotint hxintSupport).elim

private def cellXLevels (F : Finset IntegerPlane) (h : ℝ) : Finset ℝ :=
  F.image (fun z ↦ h * (z 0 : ℝ)) ∪ F.image (fun z ↦ h * ((z 0 : ℝ) + 1))

private def cellYLevels (F : Finset IntegerPlane) (k : ℝ) : Finset ℝ :=
  F.image (fun z ↦ k * (z 1 : ℝ)) ∪ F.image (fun z ↦ k * ((z 1 : ℝ) + 1))

private theorem cellSupport_frontier_subset_finiteGridLines (F : Finset IntegerPlane)
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) {x : Plane}
    (hx : x ∈ frontier (cellSupport h k F)) :
    (∃ c ∈ cellXLevels F h, x.re = c) ∨ ∃ c ∈ cellYLevels F k, x.im = c := by
  obtain ⟨z, hz, hline | hline | hline | hline⟩ :=
    cellSupport_frontier_subset_gridLines F h k hh hk hx
  · left
    refine ⟨h * (z 0 : ℝ), ?_, hline⟩
    change h * (z 0 : ℝ) ∈
      F.image (fun w ↦ h * (w 0 : ℝ)) ∪ F.image (fun w ↦ h * ((w 0 : ℝ) + 1))
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  · left
    refine ⟨h * ((z 0 : ℝ) + 1), ?_, hline⟩
    change h * ((z 0 : ℝ) + 1) ∈
      F.image (fun w ↦ h * (w 0 : ℝ)) ∪ F.image (fun w ↦ h * ((w 0 : ℝ) + 1))
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  · right
    refine ⟨k * (z 1 : ℝ), ?_, hline⟩
    change k * (z 1 : ℝ) ∈
      F.image (fun w ↦ k * (w 1 : ℝ)) ∪ F.image (fun w ↦ k * ((w 1 : ℝ) + 1))
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
  · right
    refine ⟨k * ((z 1 : ℝ) + 1), ?_, hline⟩
    change k * ((z 1 : ℝ) + 1) ∈
      F.image (fun w ↦ k * (w 1 : ℝ)) ∪ F.image (fun w ↦ k * ((w 1 : ℝ) + 1))
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))

private theorem openSegment_re_injOn {a b : Plane} (hab : a.re ≠ b.re) :
    Set.InjOn Complex.re (openSegment ℝ a b) := by
  intro x hx y hy hxy
  rw [openSegment_eq_image'] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hparam : s = t := by
    have hxy' := hxy
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul, Complex.sub_re] at hxy'
    have hdelta : (b - a).re ≠ 0 := by
      simp only [Complex.sub_re]
      exact sub_ne_zero.mpr (Ne.symm hab)
    have hdelta' : b.re - a.re ≠ 0 := by simpa only [Complex.sub_re] using hdelta
    have heq : s * (b.re - a.re) = t * (b.re - a.re) := by linarith [hxy']
    exact mul_right_cancel₀ hdelta' heq
  subst t
  rfl

private theorem openSegment_im_injOn {a b : Plane} (hab : a.im ≠ b.im) :
    Set.InjOn Complex.im (openSegment ℝ a b) := by
  intro x hx y hy hxy
  rw [openSegment_eq_image'] at hx hy
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨t, ht, rfl⟩ := hy
  have hparam : s = t := by
    have hxy' := hxy
    simp only [Complex.add_im, Complex.smul_im, smul_eq_mul, Complex.sub_im] at hxy'
    have hdelta : (b - a).im ≠ 0 := by
      simp only [Complex.sub_im]
      exact sub_ne_zero.mpr (Ne.symm hab)
    have hdelta' : b.im - a.im ≠ 0 := by simpa only [Complex.sub_im] using hdelta
    have heq : s * (b.im - a.im) = t * (b.im - a.im) := by linarith [hxy']
    exact mul_right_cancel₀ hdelta' heq
  subst t
  rfl

private theorem openSegment_re_fiber_finite {a b : Plane} (hab : a.re ≠ b.re) (c : ℝ) :
    {x : Plane | x ∈ openSegment ℝ a b ∧ x.re = c}.Finite := by
  let S : Set Plane := {x | x ∈ openSegment ℝ a b ∧ x.re = c}
  have himage : Complex.re '' S ⊆ {c} := by
    rintro y ⟨x, hx, rfl⟩
    simp [hx.2]
  have hfinite : (Complex.re '' S).Finite := (Set.toFinite {c}).subset himage
  exact hfinite.of_finite_image (by
    intro x hx y hy hxy
    exact openSegment_re_injOn hab hx.1 hy.1 hxy)

private theorem openSegment_im_fiber_finite {a b : Plane} (hab : a.im ≠ b.im) (c : ℝ) :
    {x : Plane | x ∈ openSegment ℝ a b ∧ x.im = c}.Finite := by
  let S : Set Plane := {x | x ∈ openSegment ℝ a b ∧ x.im = c}
  have himage : Complex.im '' S ⊆ {c} := by
    rintro y ⟨x, hx, rfl⟩
    simp [hx.2]
  have hfinite : (Complex.im '' S).Finite := (Set.toFinite {c}).subset himage
  exact hfinite.of_finite_image (by
    intro x hx y hy hxy
    exact openSegment_im_injOn hab hx.1 hy.1 hxy)

private theorem openSegment_infinite {a b : Plane} (hab : a ≠ b) :
    (openSegment ℝ a b).Infinite := by
  rw [openSegment_eq_image_lineMap]
  exact (Set.Ioo_infinite (by norm_num : (0 : ℝ) < 1)).image
    (AffineMap.lineMap_injective ℝ hab).injOn

private theorem cellSupport_openSegment_axis (F : Finset IntegerPlane) (h k : ℝ)
    (hh : 0 < h) (hk : 0 < k) {a b : Plane} (hab : a ≠ b)
    (hfront : openSegment ℝ a b ⊆ frontier (cellSupport h k F)) :
    a.re = b.re ∨ a.im = b.im := by
  classical
  by_contra hne
  have habre : a.re ≠ b.re := fun heq ↦ hne (Or.inl heq)
  have habim : a.im ≠ b.im := fun heq ↦ hne (Or.inr heq)
  let seg := openSegment ℝ a b
  let V := ⋃ c ∈ cellXLevels F h, {x : Plane | x ∈ seg ∧ x.re = c}
  let H := ⋃ c ∈ cellYLevels F k, {x : Plane | x ∈ seg ∧ x.im = c}
  have hVfinite : V.Finite := by
    dsimp [V]
    apply (cellXLevels F h).finite_toSet.biUnion
    intro c hc
    exact openSegment_re_fiber_finite habre c
  have hHfinite : H.Finite := by
    dsimp [H]
    apply (cellYLevels F k).finite_toSet.biUnion
    intro c hc
    exact openSegment_im_fiber_finite habim c
  have hcover : seg ⊆ V ∪ H := by
    intro x hx
    have hxfront : x ∈ frontier (cellSupport h k F) := hfront hx
    rcases cellSupport_frontier_subset_finiteGridLines F h k hh hk hxfront with
      ⟨c, hc, hxeq⟩ | ⟨c, hc, hyeq⟩
    · left
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ⟨hx, hxeq⟩⟩⟩
    · right
      exact Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ⟨hx, hyeq⟩⟩⟩
  have hfinite : (V ∪ H).Finite := hVfinite.union hHfinite
  exact (openSegment_infinite hab).not_finite (hfinite.subset hcover)

private noncomputable def cellSupportRectangulation (F : Finset IntegerPlane)
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) : Tiling.Rectangulation (cellSupport h k F) := by
  classical
  refine ⟨F.image (gridCell h k), ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨cellCornerLL h k z, cellCornerUR h k z, ?_, ?_, ?_⟩
    · rw [cellCornerLL_re, cellCornerUR_re]
      nlinarith [hh]
    · rw [cellCornerLL_im, cellCornerUR_im]
      nlinarith [hk]
    · exact gridCell_eq_rectangle h k z hh hk
  · intro r hr s hs hrs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hs
    have hzw : z ≠ w := by
      intro hEq
      subst w
      exact hrs rfl
    exact gridCells_aedisjoint h k hh hk hzw
  · ext x
    constructor
    · intro hx
      obtain ⟨r, hr, hxr⟩ := Set.mem_sUnion.mp hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
      exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hxr⟩⟩
    · intro hx
      change x ∈ ⋃ z ∈ F, gridCell h k z at hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨z, hz, hzx⟩ := hx
      exact Set.mem_sUnion.mpr ⟨gridCell h k z,
        Finset.mem_image.mpr ⟨z, hz, rfl⟩, hzx⟩

private noncomputable def cellSupportRegion (F : Finset IntegerPlane)
    (h k : ℝ) (hh : 0 < h) (hk : 0 < k) (hF : F.Nonempty) :
    Tiling.AxisParallel.Region := by
  classical
  let p : Plane := cellCornerLL h k (Classical.choose hF)
  have hp : p ∈ cellSupport h k F := by
    change p ∈ ⋃ z ∈ F, gridCell h k z
    refine Set.mem_iUnion.mpr ⟨Classical.choose hF, ?_⟩
    refine Set.mem_iUnion.mpr ⟨Classical.choose_spec hF, ?_⟩
    change h * (Classical.choose hF 0 : ℝ) ≤ p.re ∧
      p.re ≤ h * ((Classical.choose hF 0 : ℝ) + 1) ∧
      k * (Classical.choose hF 1 : ℝ) ≤ p.im ∧
      p.im ≤ k * ((Classical.choose hF 1 : ℝ) + 1)
    rw [cellCornerLL_re, cellCornerLL_im]
    constructor
    · rfl
    · constructor
      · nlinarith [hh]
      · constructor
        · rfl
        · nlinarith [hk]
  exact {
    toPolygonalRegion := {
      support := cellSupport h k F
      isPolygonal := cellSupport_isPolygonal F h k hh hk
      nonempty := ⟨p, hp⟩
    }
    isAxisParallel := ⟨cellSupportRectangulation F h k hh hk⟩
  }

private theorem rational_inverse_int_mul (m : ℕ) (hm : 0 < m) (z : ℤ) :
    ∃ q : ℚ, (m : ℝ)⁻¹ * (z : ℝ) = q := by
  refine ⟨(z : ℚ) / (m : ℚ), ?_⟩
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hq : (m : ℝ)⁻¹ * (z : ℝ) = ((z : ℚ) / (m : ℚ) : ℚ) := by
    push_cast
    field_simp
  exact hq

private theorem gridCell_corner_rational (d N : ℕ) (hd : 0 < d) (hN : 0 < N)
    (z : IntegerPlane) {v : Plane}
    (hv : v = cellCornerLL (d : ℝ)⁻¹ ((d * N : ℕ) : ℝ)⁻¹ z ∨
      v = cellCornerUL (d : ℝ)⁻¹ ((d * N : ℕ) : ℝ)⁻¹ z ∨
      v = cellCornerLR (d : ℝ)⁻¹ ((d * N : ℕ) : ℝ)⁻¹ z ∨
      v = cellCornerUR (d : ℝ)⁻¹ ((d * N : ℕ) : ℝ)⁻¹ z) :
    Tiling.IsRationalPoint v := by
  have hdN : 0 < d * N := Nat.mul_pos hd hN
  have hxy : ∃ x y : ℚ, v.re = x ∧ v.im = y := by
    rcases hv with hLL | hUL | hLR | hUR
    · subst v
      obtain ⟨x, hx⟩ := rational_inverse_int_mul d hd (z 0)
      obtain ⟨y, hy⟩ := rational_inverse_int_mul (d * N) hdN (z 1)
      exact ⟨x, y, by simpa [cellCornerLL_re] using hx,
        by simpa [cellCornerLL_im] using hy⟩
    · subst v
      obtain ⟨x, hx⟩ := rational_inverse_int_mul d hd (z 0)
      obtain ⟨y, hy⟩ := rational_inverse_int_mul (d * N) hdN (z 1 + 1)
      exact ⟨x, y, by simpa [cellCornerUL, Complex.ofReal_re, Complex.ofReal_im],
        by simpa [cellCornerUL, Complex.ofReal_re, Complex.ofReal_im] using hy⟩
    · subst v
      obtain ⟨x, hx⟩ := rational_inverse_int_mul d hd (z 0 + 1)
      obtain ⟨y, hy⟩ := rational_inverse_int_mul (d * N) hdN (z 1)
      exact ⟨x, y, by simpa [cellCornerLR, Complex.ofReal_re, Complex.ofReal_im] using hx,
        by simpa [cellCornerLR, Complex.ofReal_re, Complex.ofReal_im] using hy⟩
    · subst v
      obtain ⟨x, hx⟩ := rational_inverse_int_mul d hd (z 0 + 1)
      obtain ⟨y, hy⟩ := rational_inverse_int_mul (d * N) hdN (z 1 + 1)
      exact ⟨x, y, by simpa [cellCornerUR_re] using hx,
        by simpa [cellCornerUR_im] using hy⟩
  exact hxy

private theorem rationalPoint_sub {v w : Plane}
    (hv : Tiling.IsRationalPoint v) (hw : Tiling.IsRationalPoint w) :
    Tiling.IsRationalPoint (w - v) := by
  obtain ⟨x, y, hx, hy⟩ := hv
  obtain ⟨x', y', hx', hy'⟩ := hw
  refine ⟨x' - x, y' - y, ?_, ?_⟩
  · rw [Complex.sub_re, hx', hx]
    push_cast
    rfl
  · rw [Complex.sub_im, hy', hy]
    push_cast
    rfl

private theorem cell_normSq_affineCombination_identity
    (a b w : Plane) (t : ℝ) :
    Complex.normSq (((1 - t) • a + t • b) - w) =
      (1 - t) * Complex.normSq (a - w) +
        t * Complex.normSq (b - w) -
          t * (1 - t) * Complex.normSq (a - b) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

private theorem cell_triangle_extremePoint_of_globalDistanceMax
    {s t : Set Plane} (_ht : Tiling.IsTriangle t) (hts : t ⊆ s)
    {p w : Plane} (hpt : p ∈ t)
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
  have hpa := hmax a (hts hat)
  have hpb := hmax b (hts hbt)
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
  have hid := cell_normSq_affineCombination_identity a b w v
  rw [← huvform] at hid
  have hpos : 0 < v * (1 - v) * Complex.normSq (a - b) := by
    exact mul_pos (mul_pos hv (sub_pos.mpr hvlt))
      (Complex.normSq_pos.mpr (sub_ne_zero.mpr hab))
  nlinarith

private theorem cell_globalDistanceMaximizers_mem_vertexSet
    {s : Set Plane} (_hs : Tiling.IsPolygonal s)
    {p q : Plane} (hp : p ∈ s) (hq : q ∈ s)
    (hmax : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ dist p q) :
    p ∈ Tiling.vertexSet s ∧ q ∈ Tiling.vertexSet s := by
  constructor
  · intro triangulation
    have hp' : p ∈ ⋃₀ (triangulation.pieces : Set (Set Plane)) := by
      rw [triangulation.sUnion_eq]
      exact hp
    rcases hp' with ⟨t, ht, hpt⟩
    refine ⟨t, ht, cell_triangle_extremePoint_of_globalDistanceMax
      (s := s) (w := q) (triangulation.isTriangle t ht) ?_ hpt ?_⟩
    · intro x hxt
      rw [← triangulation.sUnion_eq]
      exact ⟨t, ht, hxt⟩
    · intro x hxs
      exact hmax x hxs q hq
  · intro triangulation
    have hq' : q ∈ ⋃₀ (triangulation.pieces : Set (Set Plane)) := by
      rw [triangulation.sUnion_eq]
      exact hq
    rcases hq' with ⟨t, ht, hqt⟩
    refine ⟨t, ht, cell_triangle_extremePoint_of_globalDistanceMax
      (s := s) (w := p) (triangulation.isTriangle t ht) ?_ hqt ?_⟩
    · intro x hxt
      rw [← triangulation.sUnion_eq]
      exact ⟨t, ht, hxt⟩
    · intro x hxs
      simpa only [dist_comm q p] using hmax x hxs p hp

private theorem cell_exists_globalDistanceMaximizers
    {s : Set Plane} (hs : IsCompact s) (hne : s.Nonempty) :
    ∃ p ∈ s, ∃ q ∈ s,
      (∀ x ∈ s, ∀ y ∈ s, dist x y ≤ dist p q) := by
  have hprod : IsCompact (s ×ˢ s) := hs.prod hs
  have hprodne : (s ×ˢ s).Nonempty := hne.prod hne
  obtain ⟨pq, hpq, hmax⟩ := hprod.exists_isMaxOn hprodne continuous_dist.continuousOn
  refine ⟨pq.1, hpq.1, pq.2, hpq.2, ?_⟩
  intro x hx y hy
  exact hmax (show (x, y) ∈ s ×ˢ s from ⟨hx, hy⟩)

theorem cell_region_exists :
  ∀ (F : Finset IntegerPlane) (d N : ℕ), F.Nonempty → 0 < d → 0 < N →
    ∃ R : PolygonalRegion,
      R.support = cellSupport (d : ℝ)⁻¹ ((d * N : ℕ) : ℝ)⁻¹ F ∧
      Tiling.RationalPolygonal.IsRelativelyRational R ∧
      (∀ a b : Plane, a ≠ b → openSegment ℝ a b ⊆ frontier R.support →
        a.re = b.re ∨ a.im = b.im)
  := by
    intro F d N hF hd hN
    let h : ℝ := (d : ℝ)⁻¹
    let k : ℝ := ((d * N : ℕ) : ℝ)⁻¹
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hdNR : (0 : ℝ) < (d * N : ℕ) := by exact_mod_cast (Nat.mul_pos hd hN)
    have hh : 0 < h := by simp [h, hdR]
    have hk : 0 < k := by
      change 0 < ((d * N : ℕ) : ℝ)⁻¹
      exact inv_pos.mpr hdNR
    let K : Tiling.AxisParallel.Region := cellSupportRegion F h k hh hk hF
    obtain ⟨v, hv, w₀, hw₀, hmax⟩ :=
      cell_exists_globalDistanceMaximizers K.isPolygonal.isCompact K.nonempty
    have hvw := cell_globalDistanceMaximizers_mem_vertexSet K.isPolygonal hv hw₀ hmax
    have hv' : v ∈ Tiling.vertexSet (cellSupport h k F) := by
      exact hvw.1
    have hvCorners := cellSupport_vertex_subset_corners F h k hh hk hv'
    obtain ⟨zv, hzv, hvCorner⟩ := hvCorners
    have hvRat : Tiling.IsRationalPoint v := by
      exact gridCell_corner_rational d N hd hN zv (by simpa [h, k] using hvCorner)
    have hrel : Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion := by
      refine ⟨v, hv', ?_⟩
      intro w hw
      have hwCorners := cellSupport_vertex_subset_corners F h k hh hk hw
      obtain ⟨zw, hzw, hwCorner⟩ := hwCorners
      have hwRat : Tiling.IsRationalPoint w := by
        exact gridCell_corner_rational d N hd hN zw (by simpa [h, k] using hwCorner)
      exact rationalPoint_sub hvRat hwRat
    refine ⟨K.toPolygonalRegion, rfl, hrel, ?_⟩
    intro a b hab hseg
    apply cellSupport_openSegment_axis F h k hh hk hab
    change openSegment ℝ a b ⊆ frontier (cellSupport h k F) at hseg
    exact hseg

private noncomputable def tileAt {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) : IntegerPlane :=
  Classical.choose (Tiling.RationalPolygonal.existsUnique_tile_representation hT x)

private theorem tileAt_spec {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) :
    tileAt hT x ∈ F ∧ x - tileAt hT x ∈ A :=
  (Classical.choose_spec (Tiling.RationalPolygonal.existsUnique_tile_representation hT x)).1

private noncomputable def ownerAt {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) : A :=
  ⟨x - tileAt hT x, tileAt_spec hT x |>.2⟩

private theorem ownerAt_repr {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) :
  x = tileAt hT x + (ownerAt hT x : IntegerPlane) := by
  simp only [ownerAt]
  abel

private theorem ownerAt_step {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) :
    Tiling.RationalPolygonal.quakeTransfer F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit
      (ownerAt hT x) (ownerAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) := by
  refine ⟨tileAt hT x, (tileAt_spec hT x).1,
    tileAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit),
    (tileAt_spec hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit)).1, ?_⟩
  have hx := ownerAt_repr hT x
  have hy := ownerAt_repr hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
  change tileAt hT x + (ownerAt hT x : IntegerPlane) +
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit =
    tileAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit) +
      (ownerAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit) : IntegerPlane)
  rw [← hx, ← hy]

private theorem ownerAt_reachable_succ {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
      (ownerAt hT x) (ownerAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) := by
  by_cases heq : ownerAt hT x = ownerAt hT (x + Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
  · rw [heq]
  · rw [SimpleGraph.reachable_iff_reflTransGen]
    apply Relation.ReflTransGen.single
    rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
    exact ⟨heq, Or.inl (ownerAt_step hT x)⟩

private theorem ownerAt_reachable_nat {F : Finset IntegerPlane} {A : Set IntegerPlane}
    (hT : TranslationalTilings.Tiles F A Set.univ) (x : IntegerPlane) (n : ℕ) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
      (ownerAt hT x) (ownerAt hT (x + n • Tiling.AxisParallel.Discrete.verticalDiscreteUnit)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlast := ownerAt_reachable_succ hT
      (x + n • Tiling.AxisParallel.Discrete.verticalDiscreteUnit)
    have hsum : x + n • Tiling.AxisParallel.Discrete.verticalDiscreteUnit +
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit =
      x + (n + 1) • Tiling.AxisParallel.Discrete.verticalDiscreteUnit := by
      simp [add_assoc]
    simpa only [hsum] using ih.trans hlast

theorem backend_common_column_reachable :
  ∀ (F : Finset IntegerPlane) (A : Set IntegerPlane),
    TranslationalTilings.Tiles F A Set.univ → ∀ a b : A,
    (∃ f ∈ F, ∃ g ∈ F, (f + a.1) 0 = (g + b.1) 0) →
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable a b := by
  intro F A hT a b hab
  rcases hab with ⟨f, hf, g, hg, hcoord⟩
  let x := f + (a : IntegerPlane)
  let y := g + (b : IntegerPlane)
  have hownerx : ownerAt hT x = a := by
    apply Subtype.ext
    have huniq := Tiling.RationalPolygonal.existsUnique_tile_representation hT x
    have hfa : f ∈ F ∧ x - f ∈ A := by
      constructor
      · exact hf
      · dsimp [x]
        simp
    have hchosen := (Classical.choose_spec huniq).2 f hfa
    have hchosen' : tileAt hT x = f := hchosen.symm
    simp [ownerAt, hchosen', x]
  have hownery : ownerAt hT y = b := by
    apply Subtype.ext
    have huniq := Tiling.RationalPolygonal.existsUnique_tile_representation hT y
    have hgb : g ∈ F ∧ y - g ∈ A := by
      constructor
      · exact hg
      · dsimp [y]
        simp
    have hchosen := (Classical.choose_spec huniq).2 g hgb
    have hchosen' : tileAt hT y = g := hchosen.symm
    simp [ownerAt, hchosen', y]
  have hfirst : (x : IntegerPlane) 0 = (y : IntegerPlane) 0 := by
    dsimp [x, y]
    simpa only [Pi.add_apply] using hcoord
  have hdiff : x 1 - y 1 = (x - y) 1 := by simp
  have hvertical : x - y = (x 1 - y 1) • Tiling.AxisParallel.Discrete.verticalDiscreteUnit := by
    ext i
    fin_cases i
    · simp only [Pi.sub_apply, Tiling.AxisParallel.Discrete.verticalDiscreteUnit]
      simp [hfirst]
    · simp only [Pi.sub_apply, Tiling.AxisParallel.Discrete.verticalDiscreteUnit]
      simp
  by_cases hxy : y 1 ≤ x 1
  · have hn : (x 1 - y 1 : ℤ) = ((x 1 - y 1).toNat : ℤ) := by omega
    have hpath := ownerAt_reachable_nat hT y ((x 1 - y 1).toNat)
    have hpoint : y + (x 1 - y 1).toNat •
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit = x := by
      ext i
      fin_cases i <;> simp [Tiling.AxisParallel.Discrete.verticalDiscreteUnit] <;> omega
    have hroute : (Tiling.RationalPolygonal.quakeGraph F A
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
        (ownerAt hT y) (ownerAt hT x) := by
      convert hpath using 1
      congr 1
      exact hpoint.symm
    simpa [hownerx, hownery] using hroute.symm
  · have hn : (y 1 - x 1 : ℤ) = ((y 1 - x 1).toNat : ℤ) := by omega
    have hpath := ownerAt_reachable_nat hT x ((y 1 - x 1).toNat)
    have hpoint : x + (y 1 - x 1).toNat •
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit = y := by
      ext i
      fin_cases i <;> simp [Tiling.AxisParallel.Discrete.verticalDiscreteUnit] <;> omega
    have hroute : (Tiling.RationalPolygonal.quakeGraph F A
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
        (ownerAt hT x) (ownerAt hT y) := by
      convert hpath using 1
      congr 1
      exact hpoint.symm
    simpa [hownerx, hownery] using hroute

namespace BackendComponent
open Tiling.RationalPolygonal (integerPoint_re integerPoint_im integerPoint_add)
private def vDirection : Submodule ℝ Plane :=
  Submodule.span ℝ ({Complex.I} : Set Plane)

private def rasterCell (z : IntegerPlane) : Set Plane :=
  {x | (z 0 : ℝ) ≤ x.re ∧ x.re ≤ (z 0 : ℝ) + 1 ∧
    (z 1 : ℝ) ≤ x.im ∧ x.im ≤ (z 1 : ℝ) + 1}

private def rasterSupport (F : Finset IntegerPlane) : Set Plane :=
  ⋃ z ∈ F, rasterCell z

private def rasterCellCenter (z : IntegerPlane) : Plane :=
  integerPoint z + ((1 / 2 : ℝ) + (1 / 2 : ℝ) * Complex.I)

private theorem mem_vDirection_iff_re_eq (x y : Plane) :
    x - y ∈ vDirection ↔ x.re = y.re := by
  constructor
  · intro h
    rw [vDirection, Submodule.mem_span_singleton] at h
    rcases h with ⟨c, hc⟩
    have hre : (x - y).re = 0 := by rw [← hc]; simp
    exact sub_eq_zero.mp (by simpa using hre)
  · intro hxy
    rw [vDirection, Submodule.mem_span_singleton]
    refine ⟨(x - y).im, ?_⟩
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, hxy]

private def integerReals : Set ℝ := Set.range (fun n : ℤ => (n : ℝ))

private theorem exists_noninteger_between (x ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ t ∈ Set.Ioo x (x + ε), t ∉ integerReals := by
  let p := x + ε / 3
  let q := x + (2 * ε) / 3
  have hpintvl : p ∈ Set.Ioo x (x + ε) := by
    dsimp [p]
    constructor <;> linarith
  have hqintvl : q ∈ Set.Ioo x (x + ε) := by
    dsimp [q]
    constructor <;> linarith
  by_cases hp : p ∉ integerReals
  · exact ⟨p, hpintvl, hp⟩
  · by_cases hq : q ∉ integerReals
    · exact ⟨q, hqintvl, hq⟩
    · have hp' : p ∈ integerReals := by simpa using not_not.mp hp
      have hq' : q ∈ integerReals := by simpa using not_not.mp hq
      rcases hp' with ⟨m, hm⟩
      rcases hq' with ⟨n, hn⟩
      have hm' : (m : ℝ) = p := hm
      have hn' : (n : ℝ) = q := hn
      have hdiff : ((n - m : ℤ) : ℝ) = ε / 3 := by
        calc
          ((n - m : ℤ) : ℝ) = (n : ℝ) - (m : ℝ) := by simp
          _ = q - p := by rw [hn', hm']
          _ = ε / 3 := by dsimp [p, q]; ring
      have hpos : (0 : ℤ) < n - m := by
        exact_mod_cast (show (0 : ℝ) < ((n - m : ℤ) : ℝ) by rw [hdiff]; positivity)
      have hlt : n - m < 1 := by
        exact_mod_cast (show ((n - m : ℤ) : ℝ) < (1 : ℝ) by rw [hdiff]; linarith)
      omega

private theorem cell_open_point (z : IntegerPlane) :
    ((z 0 : ℝ) + (1 / 2 : ℝ) + ((z 1 : ℝ) + (1 / 2 : ℝ)) * Complex.I) ∈
      interior (rasterCell z) := by
  rw [mem_interior_iff_mem_nhds]
  let c : Plane := ((z 0 : ℝ) + (1 / 2 : ℝ)) + ((z 1 : ℝ) + (1 / 2 : ℝ)) * Complex.I
  have hball : Metric.ball c (1/2 : ℝ) ⊆ rasterCell z := by
    intro x hx
    simp only [Metric.mem_ball, dist_eq_norm] at hx
    simp only [rasterCell, Set.mem_ofPred_eq]
    constructor
    · have hr := (Complex.abs_re_le_norm (x - c)).trans hx.le
      change (z 0 : ℝ) ≤ x.re
      have hc : c.re = (z 0 : ℝ) + 1/2 := by simp [c]
      change |x.re - c.re| ≤ 1/2 at hr
      rw [hc] at hr
      have hrlo := (abs_le.mp hr).1
      linarith
    · constructor
      · have hr := (Complex.abs_re_le_norm (x - c)).trans hx.le
        have hc : c.re = (z 0 : ℝ) + 1/2 := by simp [c]
        change |x.re - c.re| ≤ 1/2 at hr
        rw [hc] at hr
        have hrhi := (abs_le.mp hr).2
        linarith
      · constructor
        · have hi := (Complex.abs_im_le_norm (x - c)).trans hx.le
          have hc : c.im = (z 1 : ℝ) + 1/2 := by simp [c]
          change |x.im - c.im| ≤ 1/2 at hi
          rw [hc] at hi
          have hilo := (abs_le.mp hi).1
          linarith
        · have hi := (Complex.abs_im_le_norm (x - c)).trans hx.le
          have hc : c.im = (z 1 : ℝ) + 1/2 := by simp [c]
          change |x.im - c.im| ≤ 1/2 at hi
          rw [hc] at hi
          have hihi := (abs_le.mp hi).2
          linarith
  change rasterCell z ∈ 𝓝 c
  exact Filter.mem_of_superset (Metric.ball_mem_nhds c (by norm_num)) hball

private theorem rasterCellCenter_mem (F : Finset IntegerPlane) {z : IntegerPlane}
    (hz : z ∈ F) : rasterCellCenter z ∈ interior (rasterSupport F) := by
  have hcell : rasterCellCenter z ∈ interior (rasterCell z) := by
    have heq : rasterCellCenter z =
        ((z 0 : ℝ) + (1/2:ℝ)) + ((z 1 : ℝ) + (1/2:ℝ)) * Complex.I := by
      apply Complex.ext <;> simp [rasterCellCenter, integerPoint, Complex.add_re,
        Complex.add_im, Complex.mul_re, Complex.mul_im]
    simpa [heq] using cell_open_point z
  apply interior_mono ?_ hcell
  intro x hx
  exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hz, hx⟩⟩

private theorem common_column_implies_overlap
    (F : Finset IntegerPlane) (_A : Set IntegerPlane) (R : PolygonalRegion)
    (hR : R.support = rasterSupport F) {a b : IntegerPlane}
    {f g : IntegerPlane} (hf : f ∈ F) (hg : g ∈ F)
    (hcol : (f + a) 0 = (g + b) 0) :
    DirectionalOverlap R vDirection (integerPoint a) (integerPoint b) := by
  let p := integerPoint a + rasterCellCenter f
  let q := integerPoint b + rasterCellCenter g
  have hfc : rasterCellCenter f ∈ R.openCarrier := by
    change rasterCellCenter f ∈ interior R.support
    rw [hR]
    exact rasterCellCenter_mem F hf
  have hgc : rasterCellCenter g ∈ R.openCarrier := by
    change rasterCellCenter g ∈ interior R.support
    rw [hR]
    exact rasterCellCenter_mem F hg
  have hp : p ∈ integerPoint a +ᵥ R.openCarrier := by
    exact Set.mem_vadd_set.mpr ⟨rasterCellCenter f, hfc, rfl⟩
  have hq : q ∈ integerPoint b +ᵥ R.openCarrier := by
    exact Set.mem_vadd_set.mpr ⟨rasterCellCenter g, hgc, rfl⟩
  refine ⟨p, ⟨hp, ?_⟩⟩
  refine ⟨q, hq, ?_⟩
  apply (mem_vDirection_iff_re_eq p q).2
  have hcol' : (f 0 : ℝ) + a 0 = (g 0 : ℝ) + b 0 := by
    exact_mod_cast hcol
  have hpRe : p.re = (a 0 : ℝ) + (f 0 : ℝ) + 1/2 := by
    simp [p, rasterCellCenter, integerPoint, Complex.add_re, Complex.mul_re,
      Complex.I_re, mul_zero]
    ring
  have hqRe : q.re = (b 0 : ℝ) + (g 0 : ℝ) + 1/2 := by
    simp [q, rasterCellCenter, integerPoint, Complex.add_re, Complex.mul_re,
      Complex.I_re, mul_zero]
    ring
  rw [hpRe, hqRe]
  linarith [hcol']

private theorem overlap_implies_common_column
    (F : Finset IntegerPlane) (_A : Set IntegerPlane) (R : PolygonalRegion)
    (hR : R.support = rasterSupport F) {a b : IntegerPlane}
    (h : DirectionalOverlap R vDirection (integerPoint a) (integerPoint b)) :
    ∃ f ∈ F, ∃ g ∈ F, (f + a) 0 = (g + b) 0 := by
  change ((integerPoint a +ᵥ R.openCarrier) ∩
      Tiling.RationalSlopes.directionalSaturation vDirection
        (integerPoint b +ᵥ R.openCarrier)).Nonempty at h
  rcases h with ⟨p, hp⟩
  rcases hp with ⟨hpA, hpB⟩
  rcases hpB with ⟨q, hqB, hpq⟩
  rcases Set.mem_vadd_set.mp hpA with ⟨x, hx, hpx⟩
  rcases Set.mem_vadd_set.mp hqB with ⟨y, hy, hqy⟩
  have hpeq : p.re = q.re := (mem_vDirection_iff_re_eq p q).mp hpq
  have hrx : IsOpen R.openCarrier := isOpen_interior
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp hrx x hx
  obtain ⟨s, hs, hsball⟩ := Metric.isOpen_iff.mp hrx y hy
  let ε := min r (min s (1/2))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεr : ε ≤ r := by dsimp [ε]; exact min_le_left _ _
  have hεs : ε ≤ s := by dsimp [ε]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hε1 : ε < 1 := by
    dsimp [ε]
    exact lt_of_le_of_lt (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num)
  obtain ⟨t, htI, htNotInt⟩ := exists_noninteger_between p.re ε hε hε1
  let δ : ℝ := t - p.re
  have hδ0 : 0 < δ := by dsimp [δ]; exact sub_pos.mpr htI.1
  have hδε : δ < ε := by dsimp [δ]; linarith [htI.2]
  let x' : Plane := x + (δ : Plane)
  let y' : Plane := y + (δ : Plane)
  have hx'ball : x' ∈ Metric.ball x r := by
    change dist x' x < r
    rw [dist_eq_norm]
    have hδr : δ < r := lt_of_lt_of_le hδε hεr
    simpa [x', sub_eq_add_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ0, add_comm] using hδr
  have hy'ball : y' ∈ Metric.ball y s := by
    change dist y' y < s
    rw [dist_eq_norm]
    have hδs : δ < s := lt_of_lt_of_le hδε hεs
    simpa [y', sub_eq_add_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hδ0, add_comm] using hδs
  have hx' : x' ∈ R.openCarrier := hrball hx'ball
  have hy' : y' ∈ R.openCarrier := hsball hy'ball
  let p' : Plane := p + (δ : Plane)
  let q' : Plane := q + (δ : Plane)
  have hp'form : p' = integerPoint a + x' := by
    dsimp [p', x']
    change integerPoint a + x = p at hpx
    rw [← hpx]
    abel
  have hq'form : q' = integerPoint b + y' := by
    dsimp [q', y']
    change integerPoint b + y = q at hqy
    rw [← hqy]
    abel
  have hp'Supp : x' ∈ rasterSupport F := by
    have hmem : x' ∈ R.support := interior_subset (by simpa [PolygonalRegion.openCarrier] using hx')
    simpa [hR] using hmem
  have hq'Supp : y' ∈ rasterSupport F := by
    have hmem : y' ∈ R.support := interior_subset (by simpa [PolygonalRegion.openCarrier] using hy')
    simpa [hR] using hmem
  -- Decode one occupied cell on each perturbed point.
  rcases Set.mem_iUnion.mp hp'Supp with ⟨f, hfmem⟩
  rcases Set.mem_iUnion.mp hfmem with ⟨hf, hcellf⟩
  rcases Set.mem_iUnion.mp hq'Supp with ⟨g, hgmem⟩
  rcases Set.mem_iUnion.mp hgmem with ⟨hg, hcellg⟩
  have hbf : (f 0 : ℝ) ≤ x'.re ∧ x'.re ≤ (f 0 : ℝ) + 1 := by
    change ((f 0 : ℝ) ≤ x'.re ∧ x'.re ≤ (f 0 : ℝ) + 1 ∧ _ ∧ _) at hcellf
    exact ⟨hcellf.1, hcellf.2.1⟩
  have hbg : (g 0 : ℝ) ≤ y'.re ∧ y'.re ≤ (g 0 : ℝ) + 1 := by
    change ((g 0 : ℝ) ≤ y'.re ∧ y'.re ≤ (g 0 : ℝ) + 1 ∧ _ ∧ _) at hcellg
    exact ⟨hcellg.1, hcellg.2.1⟩
  have hcoord : (integerPoint a + x').re = (integerPoint b + y').re := by
    have hp0 : p.re = (a 0 : ℝ) + x.re := by
      change integerPoint a + x = p at hpx
      have hh := congrArg Complex.re hpx
      simpa [Complex.add_re, integerPoint_re, add_comm] using hh.symm
    have hq0 : q.re = (b 0 : ℝ) + y.re := by
      change integerPoint b + y = q at hqy
      have hh := congrArg Complex.re hqy
      simpa [Complex.add_re, integerPoint_re, add_comm] using hh.symm
    rw [hp0, hq0] at hpeq
    have hx'y' : x'.re = x.re + δ ∧ y'.re = y.re + δ := by
      constructor <;> simp [x', y', Complex.add_re, Complex.ofReal_re]
    rcases hx'y' with ⟨hx'r, hy'r⟩
    simp only [Complex.add_re, integerPoint_re, hx'r, hy'r]
    linarith [hpeq]
  have htX : (integerPoint a + x').re = t := by
    have hpxr : p.re = (integerPoint a).re + x.re := by
      change integerPoint a + x = p at hpx
      have := congrArg Complex.re hpx
      simpa [Complex.add_re, integerPoint_re, add_comm] using this.symm
    have hx'r : x'.re = x.re + δ := by simp [x', Complex.add_re, Complex.ofReal_re]
    rw [Complex.add_re, integerPoint_re, hx'r]
    have hpxr' : p.re = (a 0 : ℝ) + x.re := by simpa [integerPoint_re] using hpxr
    have htδ : p.re + δ = t := by dsimp [δ]; ring
    calc
      (a 0 : ℝ) + (x.re + δ) = ((a 0 : ℝ) + x.re) + δ := by ring
      _ = p.re + δ := by rw [← hpxr']
      _ = t := htδ
  have hXnot : (integerPoint a + x').re ∉ integerReals := by simpa [htX] using htNotInt
  have hlowf : (f 0 : ℝ) + a 0 < (integerPoint a + x').re := by
    have hle : (f 0 : ℝ) ≤ x'.re := hbf.1
    have hsum : (f 0 : ℝ) + a 0 ≤ (integerPoint a + x').re := by
      have hh := add_le_add_left hle (a 0 : ℝ)
      rw [Complex.add_re, integerPoint_re]
      nlinarith [hh]
    by_contra hnot
    have heq : (integerPoint a + x').re = ((f 0 : ℝ) + a 0) := le_antisymm (le_of_not_gt hnot) hsum
    apply hXnot
    refine ⟨f 0 + a 0, ?_⟩
    exact_mod_cast heq.symm
  have hhighf : (integerPoint a + x').re < (f 0 : ℝ) + a 0 + 1 := by
    have hle : x'.re ≤ (f 0 : ℝ) + 1 := hbf.2
    have hsum : (integerPoint a + x').re ≤ (f 0 : ℝ) + a 0 + 1 := by
      have hh := add_le_add_left hle (a 0 : ℝ)
      rw [Complex.add_re, integerPoint_re]
      nlinarith [hh]
    by_contra hnot
    have heq : (integerPoint a + x').re = ((f 0 : ℝ) + a 0 + 1) := le_antisymm hsum (le_of_not_gt hnot)
    apply hXnot
    refine ⟨f 0 + a 0 + 1, ?_⟩
    exact_mod_cast heq.symm
  have hlowg : (g 0 : ℝ) + b 0 < (integerPoint b + y').re := by
    have hle : (g 0 : ℝ) ≤ y'.re := hbg.1
    have hsum : (g 0 : ℝ) + b 0 ≤ (integerPoint b + y').re := by
      have hh := add_le_add_left hle (b 0 : ℝ)
      rw [Complex.add_re, integerPoint_re]
      nlinarith [hh]
    by_contra hnot
    have heq : (integerPoint b + y').re = ((g 0 : ℝ) + b 0) := le_antisymm (le_of_not_gt hnot) hsum
    have hXnot' : (integerPoint b + y').re ∉ integerReals := by simpa [hcoord] using hXnot
    apply hXnot'
    refine ⟨g 0 + b 0, ?_⟩
    exact_mod_cast heq.symm
  have hhighg : (integerPoint b + y').re < (g 0 : ℝ) + b 0 + 1 := by
    have hle : y'.re ≤ (g 0 : ℝ) + 1 := hbg.2
    have hsum : (integerPoint b + y').re ≤ (g 0 : ℝ) + b 0 + 1 := by
      have hh := add_le_add_left hle (b 0 : ℝ)
      rw [Complex.add_re, integerPoint_re]
      nlinarith [hh]
    by_contra hnot
    have heq : (integerPoint b + y').re = ((g 0 : ℝ) + b 0 + 1) := le_antisymm hsum (le_of_not_gt hnot)
    have hXnot' : (integerPoint b + y').re ∉ integerReals := by simpa [hcoord] using hXnot
    apply hXnot'
    refine ⟨g 0 + b 0 + 1, ?_⟩
    exact_mod_cast heq.symm
  have hends : (f 0 : ℝ) + a 0 < (g 0 : ℝ) + b 0 + 1 ∧
      (g 0 : ℝ) + b 0 < (f 0 : ℝ) + a 0 + 1 := by
    constructor <;> linarith
  have hendsZ : f 0 + a 0 = g 0 + b 0 := by
    have h₁ : f 0 + a 0 < g 0 + b 0 + 1 := by exact_mod_cast hends.1
    have h₂ : g 0 + b 0 < f 0 + a 0 + 1 := by exact_mod_cast hends.2
    omega
  exact ⟨f, hf, g, hg, hendsZ⟩

private noncomputable def labelEquiv (A : Set IntegerPlane) :
    A ≃ {x : Plane // x ∈ integerPoint '' A} where
  toFun a := ⟨integerPoint a, ⟨a, a.2, rfl⟩⟩
  invFun x := ⟨Classical.choose x.2, (Classical.choose_spec x.2).1⟩
  left_inv a := by
    apply Subtype.ext
    have hm : integerPoint a ∈ integerPoint '' A := ⟨a, a.2, rfl⟩
    exact Tiling.RationalPolygonal.integerPoint_injective (Classical.choose_spec hm).2
  right_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec x.2).2

private theorem verticalOverlap_comm (R : PolygonalRegion) {s t : Plane} :
    DirectionalOverlap R vDirection s t ↔ DirectionalOverlap R vDirection t s := by
  change ((s +ᵥ R.openCarrier) ∩
      Tiling.RationalSlopes.directionalSaturation vDirection (t +ᵥ R.openCarrier)).Nonempty ↔
    ((t +ᵥ R.openCarrier) ∩
      Tiling.RationalSlopes.directionalSaturation vDirection (s +ᵥ R.openCarrier)).Nonempty
  constructor
  · rintro ⟨p, ⟨hp, hpsat⟩⟩
    rcases hpsat with ⟨q, hq, hpq⟩
    refine ⟨q, ⟨hq, ?_⟩⟩
    refine ⟨p, hp, ?_⟩
    have hqp : q - p ∈ vDirection := by
      convert vDirection.neg_mem hpq using 1
      abel
    exact hqp
  · rintro ⟨p, ⟨hp, hpsat⟩⟩
    rcases hpsat with ⟨q, hq, hpq⟩
    refine ⟨q, ⟨hq, ?_⟩⟩
    refine ⟨p, hp, ?_⟩
    have hqp : q - p ∈ vDirection := by
      convert vDirection.neg_mem hpq using 1
      abel
    exact hqp

private theorem quakeAdj_implies_continuousAdj
    (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion)
    (hR : R.support = rasterSupport F) {a b : A}
    (hadj : (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Adj a b) :
    (Tiling.RationalSlopes.earthquakeGraph R vDirection (integerPoint '' A)).Adj
      (labelEquiv A a) (labelEquiv A b) := by
  rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨hne, hrel | hrel⟩
  · rcases hrel with ⟨f, hf, g, hg, heq⟩
    have hcol : (f + a.1) 0 = (g + b.1) 0 := by
      have hc := congrArg (fun z : IntegerPlane => z 0) heq
      simpa [Tiling.AxisParallel.Discrete.verticalDiscreteUnit, Pi.add_apply] using hc
    have hov := common_column_implies_overlap F A R hR hf hg hcol
    rw [Tiling.RationalSlopes.earthquakeGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro he
      apply hne
      exact (labelEquiv A).injective (Subtype.ext (congrArg Subtype.val he))
    · simpa [labelEquiv] using hov
  · rcases hrel with ⟨f, hf, g, hg, heq⟩
    have hcol : (f + b.1) 0 = (g + a.1) 0 := by
      have hc := congrArg (fun z : IntegerPlane => z 0) heq
      simpa [Tiling.AxisParallel.Discrete.verticalDiscreteUnit, Pi.add_apply] using hc
    have hov := common_column_implies_overlap F A R hR hf hg hcol
    have hov' := (verticalOverlap_comm R).mp hov
    rw [Tiling.RationalSlopes.earthquakeGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ?_⟩
    · intro he
      apply hne
      exact (labelEquiv A).injective (Subtype.ext (congrArg Subtype.val he))
    · simpa [labelEquiv] using hov'

private theorem continuousAdj_implies_quakeReachable
    (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion)
    (hT : TranslationalTilings.Tiles F A Set.univ)
    (hR : R.support = rasterSupport F) {u v : {x : Plane // x ∈ integerPoint '' A}}
    (hadj : (Tiling.RationalSlopes.earthquakeGraph R vDirection (integerPoint '' A)).Adj u v) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
      ((labelEquiv A).symm u) ((labelEquiv A).symm v) := by
  rw [Tiling.RationalSlopes.earthquakeGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨_, hov | hov⟩
  · have hu : u.1 = integerPoint ((labelEquiv A).symm u).1 := by
      have he := congrArg Subtype.val ((labelEquiv A).apply_symm_apply u)
      change integerPoint ((labelEquiv A).symm u).1 = u.1 at he
      exact he.symm
    have hv : v.1 = integerPoint ((labelEquiv A).symm v).1 := by
      have he := congrArg Subtype.val ((labelEquiv A).apply_symm_apply v)
      change integerPoint ((labelEquiv A).symm v).1 = v.1 at he
      exact he.symm
    have hov' : DirectionalOverlap R vDirection
        (integerPoint ((labelEquiv A).symm u).1)
        (integerPoint ((labelEquiv A).symm v).1) := by simpa [hu, hv] using hov
    exact backend_common_column_reachable F A hT _ _
      (overlap_implies_common_column F A R hR hov')
  · have hov := (verticalOverlap_comm R).mpr hov
    have hu : u.1 = integerPoint ((labelEquiv A).symm u).1 := by
      have he := congrArg Subtype.val ((labelEquiv A).apply_symm_apply u)
      change integerPoint ((labelEquiv A).symm u).1 = u.1 at he
      exact he.symm
    have hv : v.1 = integerPoint ((labelEquiv A).symm v).1 := by
      have he := congrArg Subtype.val ((labelEquiv A).apply_symm_apply v)
      change integerPoint ((labelEquiv A).symm v).1 = v.1 at he
      exact he.symm
    have hov' : DirectionalOverlap R vDirection
        (integerPoint ((labelEquiv A).symm u).1)
        (integerPoint ((labelEquiv A).symm v).1) := by simpa [hu, hv] using hov
    exact backend_common_column_reachable F A hT _ _
      (overlap_implies_common_column F A R hR hov')

private theorem continuousWalk_quakeReachable
    (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion)
    (hT : TranslationalTilings.Tiles F A Set.univ)
    (hR : R.support = rasterSupport F)
    {u v : {x : Plane // x ∈ integerPoint '' A}}
    (w : (Tiling.RationalSlopes.earthquakeGraph R vDirection
      (integerPoint '' A)).Walk u v) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable
      ((labelEquiv A).symm u) ((labelEquiv A).symm v) := by
  induction w with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | cons hadj w ih =>
    exact (continuousAdj_implies_quakeReachable F A R hT hR hadj).trans ih

private theorem backend_component_iff_saturation_body :
  ∀ (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion),
    TranslationalTilings.Tiles F A Set.univ →
    R.support = Tiling.RationalSlopes.DirectionalRaster.cellSupport 1 1 F → ∀ a b : A,
    ((Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable a b ↔
      (Tiling.RationalSlopes.earthquakeGraph R
        Tiling.RationalSlopes.DirectionalRaster.verticalDirection
        (integerPoint '' A)).Reachable
        ⟨integerPoint a.1, ⟨a.1, a.2, rfl⟩⟩
        ⟨integerPoint b.1, ⟨b.1, b.2, rfl⟩⟩) := by
  intro F A R hT hR a b
  have hRlocal : R.support = rasterSupport F := by
    simpa [rasterSupport, rasterCell, Tiling.RationalSlopes.DirectionalRaster.cellSupport,
      Tiling.RationalSlopes.DirectionalRaster.gridCell] using hR
  let e := labelEquiv A
  let G := Tiling.RationalPolygonal.quakeGraph F A
    Tiling.AxisParallel.Discrete.verticalDiscreteUnit
  let H := Tiling.RationalSlopes.earthquakeGraph R
    Tiling.RationalSlopes.DirectionalRaster.verticalDirection (integerPoint '' A)
  change (G.Reachable a b ↔ H.Reachable (e a) (e b))
  constructor
  · intro hG
    let hom : G →g H := {
      toFun := e
      map_rel' := by
        intro x y hxy
        exact quakeAdj_implies_continuousAdj F A R hRlocal hxy
    }
    have hma : hom a = e a := rfl
    have hmb : hom b = e b := rfl
    simpa only [hma, hmb] using SimpleGraph.Reachable.map hom hG
  · intro hH
    obtain ⟨w⟩ := hH
    have hr := continuousWalk_quakeReachable F A R hT hRlocal w
    simpa [e] using hr


end BackendComponent

theorem backend_component_iff_saturation :
  ∀ (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion),
    TranslationalTilings.Tiles F A Set.univ →
    R.support = cellSupport 1 1 F → ∀ a b : A,
    ((Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Reachable a b ↔
      (earthquakeGraph R verticalDirection (integerPoint '' A)).Reachable
        ⟨integerPoint a.1, ⟨a.1, a.2, rfl⟩⟩
        ⟨integerPoint b.1, ⟨b.1, b.2, rfl⟩⟩)
  := by exact BackendComponent.backend_component_iff_saturation_body

private theorem gridCell_vadd (h k : ℝ) (a z : IntegerPlane) :
    gridPoint h k a +ᵥ gridCell h k z = gridCell h k (z + a) := by
  ext x
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change (-gridPoint h k a + x ∈ gridCell h k z) ↔ x ∈ gridCell h k (z + a)
  have hxr : (-gridPoint h k a + x).re = x.re - h * (a 0 : ℝ) := by
    simp [gridPoint]; ring
  have hxim : (-gridPoint h k a + x).im = x.im - k * (a 1 : ℝ) := by
    simp [gridPoint]; ring
  simp only [gridCell, Set.mem_ofPred_eq, hxr, hxim, Pi.add_apply, Int.cast_add]
  constructor <;> rintro ⟨h1, h2, h3, h4⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

private theorem cellSupport_vadd (h k : ℝ) (F : Finset IntegerPlane) (a : IntegerPlane) :
    gridPoint h k a +ᵥ cellSupport h k F = ⋃ z ∈ F, gridCell h k (z + a) := by
  simp only [cellSupport, Set.vadd_set_iUnion, gridCell_vadd]

private theorem cell_tiling_packing (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport h k F) :
    IsPacking R.prototileFamily (R.placements (gridPoint h k '' A)) := by
  intro p hp q hq hpq
  obtain ⟨a, ha, hpa⟩ := hp
  obtain ⟨b, hb, hqb⟩ := hq
  have hab : a ≠ b := by
    intro heq
    apply hpq
    apply Prod.ext
    · rw [← hpa, ← hqb, heq]
    · exact Subsingleton.elim _ _
  change MeasureTheory.AEDisjoint MeasureTheory.volume
    (p.1 +ᵥ R.support) (q.1 +ᵥ R.support)
  rw [← hpa, ← hqb, hR, cellSupport_vadd, cellSupport_vadd]
  apply MeasureTheory.AEDisjoint.iUnion_left_iff.mpr
  intro f
  apply MeasureTheory.AEDisjoint.iUnion_left_iff.mpr
  intro hf
  apply MeasureTheory.AEDisjoint.iUnion_right_iff.mpr
  intro g
  apply MeasureTheory.AEDisjoint.iUnion_right_iff.mpr
  intro hg
  apply gridCells_aedisjoint h k hh hk
  intro heq
  exact hab (Tiling.RationalPolygonal.translation_eq_of_eq_representations hT hf ha hg hb heq)

private theorem cell_tiling_support_cover (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport h k F) :
    (⋃ a : (gridPoint h k '' A), (a : Plane) +ᵥ R.support) = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let z : IntegerPlane := ![⌊x.re / h⌋, ⌊x.im / k⌋]
  obtain ⟨f, ⟨hf, hza⟩, _⟩ := Tiling.RationalPolygonal.existsUnique_tile_representation hT z
  let a := z - f
  have hfa : f + a = z := by dsimp [a]; abel
  refine Set.mem_iUnion.mpr ⟨⟨gridPoint h k a, ⟨a, hza, rfl⟩⟩, ?_⟩
  rw [hR, cellSupport_vadd]
  refine Set.mem_iUnion₂.mpr ⟨f, hf, ?_⟩
  rw [hfa]
  change h * (⌊x.re / h⌋ : ℝ) ≤ x.re ∧ x.re ≤ h * ((⌊x.re / h⌋ : ℝ) + 1) ∧
    k * (⌊x.im / k⌋ : ℝ) ≤ x.im ∧ x.im ≤ k * ((⌊x.im / k⌋ : ℝ) + 1)
  have hrlo := (le_div_iff₀ hh).mp (Int.floor_le (x.re / h))
  have hrhi := (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x.re / h))
  have hilo := (le_div_iff₀ hk).mp (Int.floor_le (x.im / k))
  have hihi := (div_lt_iff₀ hk).mp (Int.lt_floor_add_one (x.im / k))
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

private theorem cell_tiling_wholePlane (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport h k F) :
    TilesOn R (gridPoint h k '' A) Set.univ := by
  have hp := cell_tiling_packing F A R h k hh hk hT hR
  have hreg : regularSupport R (gridPoint h k '' A) = Set.univ := by
    unfold regularSupport
    rw [closure_openUnion_eq_iUnion_support hp,
      cell_tiling_support_cover F A R h k hh hk hT hR, interior_univ]
  exact hreg ▸ tilesOn_regularSupport_of_packing hp

private theorem cell_subfamily_regularSupport (F : Finset IntegerPlane) (A S : Set IntegerPlane)
    (R : PolygonalRegion) (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport h k F)
    (hSA : S ⊆ A) : regularSupport R (gridPoint h k '' S) =
      interior (⋃ z : Tiling.RationalPolygonal.discreteCarrier F S, gridCell h k z.1) := by
  have hp : IsPacking R.prototileFamily (R.placements (gridPoint h k '' S)) :=
    (cell_tiling_packing F A R h k hh hk hT hR).mono
      (fun p hs => (show p.1 ∈ gridPoint h k '' A from Set.image_mono hSA hs))
  unfold regularSupport
  rw [closure_openUnion_eq_iUnion_support hp]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hx
    obtain ⟨s, hs, hsa⟩ := a.2
    change x ∈ a.1 +ᵥ R.support at hxa
    rw [← hsa, hR, cellSupport_vadd] at hxa
    obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.mp hxa
    exact Set.mem_iUnion.mpr ⟨⟨f + s, ⟨f, hf, s, hs, rfl⟩⟩, hxf⟩
  · intro hx
    obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨f, hf, s, hs, hzs⟩ := z.2
    refine Set.mem_iUnion.mpr ⟨⟨gridPoint h k s, ⟨s, hs, rfl⟩⟩, ?_⟩
    change x ∈ gridPoint h k s +ᵥ R.support
    rw [hR, cellSupport_vadd]
    exact Set.mem_iUnion₂.mpr ⟨f, hf, hzs ▸ hxz⟩

private theorem cell_carrier_scalarPeriod (F : Finset IntegerPlane) (A S : Set IntegerPlane)
    (R : PolygonalRegion) (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport h k F)
    (hSA : S ⊆ A) (L : ℕ)
    (hperiod : TranslationalTilings.SetScalarPeriodic L (Tiling.RationalPolygonal.discreteCarrier F S))
    (w : IntegerPlane) : gridPoint h k ((L : ℤ) • w) ∈
      periodGroup (regularSupport R (gridPoint h k '' S)) := by
  let p : IntegerPlane := (L : ℤ) • w
  let D := Tiling.RationalPolygonal.discreteCarrier F S
  have hpD : p +ᵥ D = D := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    change -p + z ∈ D ↔ z ∈ D
    have ht := hperiod z (-w)
    simpa [D, p, smul_neg, add_comm] using ht
  rw [periodGroup, AddAction.mem_stabilizer_iff,
    cell_subfamily_regularSupport F A S R h k hh hk hT hR hSA, ← interior_vadd]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨z, hyz⟩ := Set.mem_iUnion.mp hy
    have hpz : z.1 + p ∈ D := by
      rw [← hpD]
      exact Set.mem_vadd_set.mpr ⟨z.1, z.2, by simp [add_comm]⟩
    refine Set.mem_iUnion.mpr ⟨⟨z.1 + p, hpz⟩, ?_⟩
    rw [← gridCell_vadd h k p z.1]
    exact Set.mem_vadd_set.mpr ⟨y, hyz, rfl⟩
  · intro hx
    obtain ⟨z, hxz⟩ := Set.mem_iUnion.mp hx
    have hzp : z.1 - p ∈ D := by
      have ht := hperiod z.1 (-w)
      simpa [D, p, smul_neg, sub_eq_add_neg] using ht.mpr z.2
    have hzEq : z.1 = (z.1 - p) + p := by abel
    rw [hzEq, ← gridCell_vadd h k p (z.1 - p)] at hxz
    obtain ⟨y, hy, hxy⟩ := Set.mem_vadd_set.mp hxz
    exact Set.mem_vadd_set.mpr ⟨y, Set.mem_iUnion.mpr ⟨⟨z.1 - p, hzp⟩, hy⟩, hxy⟩

theorem backend_column_iff_centerColumn :
  ∀ (F : Finset IntegerPlane) (A : Set IntegerPlane) (R : PolygonalRegion),
    TranslationalTilings.Tiles F A Set.univ → R.support = cellSupport 1 1 F →
    ∀ P : Tiling.RationalPolygonal.QuakePlate F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit,
    Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P ↔
      IsCenterColumn R verticalDirection
        (integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P)
  := by
  intro F A R hT hR P
  have hgrid : gridPoint 1 1 = integerPoint := by
    funext z
    simp [gridPoint, Tiling.RationalPolygonal.integerPoint]
  have hwhole : TilesOn R (integerPoint '' A) Set.univ := by
    simpa [hgrid] using cell_tiling_wholePlane F A R 1 1 (by norm_num) (by norm_num) hT hR
  have hdim : Module.finrank ℝ verticalDirection = 1 :=
    finrank_span_singleton Complex.I_ne_zero
  refine P.ind ?_
  intro a
  let P := (Tiling.RationalPolygonal.quakeGraph F A
    Tiling.AxisParallel.Discrete.verticalDiscreteUnit).connectedComponentMk a
  let b : (integerPoint '' A) := ⟨integerPoint a.1, ⟨a.1, a.2, rfl⟩⟩
  let C : EarthquakeComponent R verticalDirection (integerPoint '' A) :=
    (earthquakeGraph R verticalDirection (integerPoint '' A)).connectedComponentMk b
  have hcentres : C.centres = integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := y.2
      have hreach : (earthquakeGraph R verticalDirection (integerPoint '' A)).Reachable y b :=
        SimpleGraph.ConnectedComponent.eq.mp hy
      have hyz : y = ⟨integerPoint z, ⟨z, hz, rfl⟩⟩ := Subtype.ext hzy.symm
      rw [hyz] at hreach
      have hdisc := (backend_component_iff_saturation F A R hT hR ⟨z, hz⟩ a).mpr hreach
      refine ⟨z, ⟨hz, SimpleGraph.ConnectedComponent.eq.mpr hdisc⟩, hzy⟩
    · rintro ⟨z, ⟨hz, hzp⟩, rfl⟩
      have hdisc := SimpleGraph.ConnectedComponent.eq.mp hzp
      have hreach := (backend_component_iff_saturation F A R hT hR ⟨z, hz⟩ a).mp hdisc
      exact ⟨⟨integerPoint z, ⟨z, hz, rfl⟩⟩,
        SimpleGraph.ConnectedComponent.eq.mpr hreach, rfl⟩
  have hsub : integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P ⊆ integerPoint '' A := by
    rintro _ ⟨z, ⟨hz, _⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hpack : IsPacking R.prototileFamily
      (R.placements (integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P)) :=
    hwhole.2.1.mono (fun _ hp => hsub hp)
  have hreg : regularSupport R (integerPoint '' A) = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hwhole
  have hinv : IsInvariantAlong
      (regularSupport R (integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P))
      verticalDirection := by
    rw [← hcentres]
    exact component_isInvariant R verticalDirection (integerPoint '' A) hdim hwhole.2.1
      (by rw [hreg]; intro v hv; simp) C
  have hamem : a.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P :=
    Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨hpack, ⟨integerPoint a.1, ⟨a.1, hamem, rfl⟩⟩, ?_, hinv⟩
    refine ⟨(c : Plane), ?_⟩
    rintro x ⟨z, hz, rfl⟩
    apply (mem_verticalDirection_iff _).mpr
    have hzc : z 0 = c := Set.mem_singleton_iff.mp (hc ▸
      Set.mem_image_of_mem Tiling.AxisParallel.Discrete.firstDiscreteCoordinate hz)
    simp [hzc]
  · rintro ⟨_, _, ⟨q, hline⟩, _⟩
    refine ⟨a.1 0, ?_⟩
    have haq := (mem_verticalDirection_iff _).mp
      (hline (integerPoint a.1) ⟨a.1, hamem, rfl⟩)
    have haq' : (a.1 0 : ℝ) = q.re := by simpa using sub_eq_zero.mp haq
    ext n
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzq := (mem_verticalDirection_iff _).mp
        (hline (integerPoint z) ⟨z, hz, rfl⟩)
      have hzq' : (z 0 : ℝ) = q.re := by simpa using sub_eq_zero.mp hzq
      apply Set.mem_singleton_iff.mpr
      exact_mod_cast hzq'.trans haq'.symm
    · intro hn
      have hn' := Set.mem_singleton_iff.mp hn
      rw [hn']
      exact ⟨a.1, hamem, rfl⟩

private def backendPlateEquiv (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (hT : TranslationalTilings.Tiles F A Set.univ)
    (hR : R.support = cellSupport 1 1 F) :
    Tiling.RationalPolygonal.QuakePlate F A Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃
      EarthquakeComponent R verticalDirection (integerPoint '' A) :=
  Quot.congr (BackendComponent.labelEquiv A)
    (fun a b => backend_component_iff_saturation F A R hT hR a b)

private theorem backendPlateEquiv_centres (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (hT : TranslationalTilings.Tiles F A Set.univ)
    (hR : R.support = cellSupport 1 1 F)
    (P : Tiling.RationalPolygonal.QuakePlate F A Tiling.AxisParallel.Discrete.verticalDiscreteUnit) :
    (backendPlateEquiv F A R hT hR P).centres =
      integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P := by
  refine P.ind ?_
  intro a
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := y.2
    have hreach := SimpleGraph.ConnectedComponent.eq.mp hy
    have hyz : y = ⟨integerPoint z, ⟨z, hz, rfl⟩⟩ := Subtype.ext hzy.symm
    rw [hyz] at hreach
    have hdisc := (backend_component_iff_saturation F A R hT hR ⟨z, hz⟩ a).mpr hreach
    exact ⟨z, ⟨hz, SimpleGraph.ConnectedComponent.eq.mpr hdisc⟩, hzy⟩
  · rintro ⟨z, ⟨hz, hzp⟩, rfl⟩
    have hdisc := SimpleGraph.ConnectedComponent.eq.mp hzp
    have hreach := (backend_component_iff_saturation F A R hT hR ⟨z, hz⟩ a).mp hdisc
    exact ⟨⟨integerPoint z, ⟨z, hz, rfl⟩⟩,
      SimpleGraph.ConnectedComponent.eq.mpr hreach, rfl⟩

private theorem backend_columnPart (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (hT : TranslationalTilings.Tiles F A Set.univ)
    (hR : R.support = cellSupport 1 1 F) :
    columnPart R verticalDirection (integerPoint '' A) =
      integerPoint '' Tiling.AxisParallel.Discrete.discreteColumnUnion F A := by
  let e := backendPlateEquiv F A R hT hR
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let P := e.symm Q.1
    have hcentre : integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P = Q.1.centres := by
      rw [← backendPlateEquiv_centres F A R hT hR P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q.1)
    have hPcol := (backend_column_iff_centerColumn F A R hT hR P).mpr (hcentre.symm ▸ Q.2)
    obtain ⟨a, ha, hax⟩ := hcentre.symm ▸ hxQ
    refine ⟨a, ?_, hax⟩
    exact Set.mem_iUnion₂.mpr ⟨P, hPcol, ha⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨P, hPcol, haP⟩ := Set.mem_iUnion₂.mp ha
    have hcentre := backendPlateEquiv_centres F A R hT hR P
    have hQcol : IsCenterColumn R verticalDirection (e P).centres :=
      hcentre.symm ▸ (backend_column_iff_centerColumn F A R hT hR P).mp hPcol
    exact Set.mem_iUnion.mpr ⟨⟨e P, hQcol⟩, hcentre.symm ▸ Set.mem_image_of_mem integerPoint haP⟩

private theorem unitCell_commonCarrierPeriod (F : Finset IntegerPlane) (A : Set IntegerPlane)
    (R : PolygonalRegion) (hF : F.Nonempty)
    (hT : TranslationalTilings.Tiles F A Set.univ) (hR : R.support = cellSupport 1 1 F) :
    ∃ v : Plane, IsCommonCarrierPeriod R verticalDirection (integerPoint '' A) v := by
  obtain ⟨L, hL, _hdiv, hnonperiod, hcolperiod⟩ :=
    Tiling.AxisParallel.Discrete.exists_discretePlatePeriodicity hF (ell := 1) (by norm_num)
      (by intro x; simp)
      (by intro x z; simp) hT
  let w : IntegerPlane := ![1, 0]
  let v := gridPoint 1 1 ((L : ℤ) • w)
  have hgrid : gridPoint 1 1 = integerPoint := by
    funext z
    simp [gridPoint, Tiling.RationalPolygonal.integerPoint]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hv
    have hre := (mem_verticalDirection_iff v).mp hv
    have hre' : v.re = (L : ℝ) := by simp [v, w, gridPoint]
    rw [hre'] at hre
    exact (by exact_mod_cast hL.ne' : (L : ℝ) ≠ 0) hre
  · rw [backend_columnPart F A R hT hR]
    have hsub : Tiling.AxisParallel.Discrete.discreteColumnUnion F A ⊆ A := by
      intro a ha
      obtain ⟨P, _, haP⟩ := Set.mem_iUnion₂.mp ha
      exact haP.1
    simpa [v, hgrid] using cell_carrier_scalarPeriod F A
      (Tiling.AxisParallel.Discrete.discreteColumnUnion F A) R 1 1 (by norm_num) (by norm_num)
      hT hR hsub L hcolperiod w
  · intro Q hQ
    let e := backendPlateEquiv F A R hT hR
    let P := e.symm Q
    have hcentre : integerPoint '' Tiling.RationalPolygonal.quakePlateTranslations P = Q.centres := by
      rw [← backendPlateEquiv_centres F A R hT hR P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q)
    have hPnot : ¬ Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P := by
      intro hP
      exact hQ (hcentre ▸ (backend_column_iff_centerColumn F A R hT hR P).mp hP)
    have hsub : Tiling.RationalPolygonal.quakePlateTranslations P ⊆ A := fun _ hs => hs.1
    change v ∈ periodGroup (regularSupport R Q.centres)
    rw [← hcentre]
    simpa [v, hgrid] using cell_carrier_scalarPeriod F A
      (Tiling.RationalPolygonal.quakePlateTranslations P) R 1 1 (by norm_num) (by norm_num)
      hT hR hsub L (hnonperiod P hPnot) w

private theorem regularizedProjection_vadd (s : Plane) (U : Set Plane) :
    regularizedProjection (s +ᵥ U) = s.re +ᵥ regularizedProjection U := by
  unfold regularizedProjection
  rw [re_image_vadd, closure_vadd, interior_vadd]

private theorem invariant_preimage_re (E : Set Plane)
    (hE : IsInvariantAlong E verticalDirection) :
    Complex.re ⁻¹' (Complex.re '' E) = E := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hdelta : x - y ∈ verticalDirection :=
      (mem_verticalDirection_iff _).mpr (by simp [hxy])
    rw [← hE (x - y) hdelta]
    exact Set.mem_vadd_set.mpr ⟨y, hy, by simp⟩
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem regularSupport_subset_of_footprint
    (K R : PolygonalRegion) (S : Set Plane)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier)
    (hinv : IsInvariantAlong (regularSupport K S) verticalDirection) :
    regularSupport R S ⊆ regularSupport K S := by
  let E := regularSupport K S
  have hEreg : interior (closure E) = E := interior_closure_idem
  have hpre : Complex.re ⁻¹' regularizedProjection E = E := by
    unfold regularizedProjection
    rw [← Complex.interior_preimage_re, ← Complex.closure_preimage_re,
      invariant_preimage_re E hinv, hEreg]
  have hopenU : IsOpen (openUnion K S) := isOpen_iUnion (fun _ => isOpen_interior.vadd _)
  have hUsub : openUnion K S ⊆ E := hopenU.subset_interior_closure
  have hRsub : openUnion R S ⊆ E := by
    intro x hx
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    have hprojOpen : IsOpen (Complex.re '' (s.1 +ᵥ R.openCarrier)) :=
      Complex.isOpenMap_re _ (isOpen_interior.vadd _)
    have hxQ : x.re ∈ regularizedProjection (s.1 +ᵥ R.openCarrier) :=
      hprojOpen.subset_interior_closure ⟨x, hxs, rfl⟩
    have htile : s.1 +ᵥ K.openCarrier ⊆ E :=
      (Set.subset_iUnion _ s).trans hUsub
    have hQsub : regularizedProjection (s.1 +ᵥ K.openCarrier) ⊆ regularizedProjection E :=
      interior_mono (closure_mono (Set.image_mono htile))
    rw [regularizedProjection_vadd, ← hQ, ← regularizedProjection_vadd] at hxQ
    have hxE : x ∈ Complex.re ⁻¹' regularizedProjection E := hQsub hxQ
    rwa [hpre] at hxE
  exact (interior_mono (closure_mono hRsub)).trans_eq hEreg

private theorem regularSupport_partition_complement (K : PolygonalRegion)
    (T S : Set Plane) (htile : TilesOn K T Set.univ) (hST : S ⊆ T) :
    regularSupport K S = (closure (regularSupport K (T \ S)))ᶜ ∧
      regularSupport K (T \ S) = (closure (regularSupport K S))ᶜ := by
  have hSreg := regularSupport_isRegularOpen K S
  have hWreg := regularSupport_isRegularOpen K (T \ S)
  have hdisj : Disjoint (regularSupport K S) (regularSupport K (T \ S)) := by
    apply regularSupport_disjoint_of_disjoint_subfamilies htile.2.1 hST Set.sdiff_subset
    exact Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hUsub : openUnion K T ⊆ regularSupport K S ∪ regularSupport K (T \ S) := by
    intro x hx
    obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hx
    by_cases ht : t.1 ∈ S
    · apply Or.inl
      apply (isOpen_iUnion (fun _ => isOpen_interior.vadd _)).subset_interior_closure
      exact Set.mem_iUnion.mpr ⟨⟨t.1, ht⟩, hxt⟩
    · apply Or.inr
      apply (isOpen_iUnion (fun _ => isOpen_interior.vadd _)).subset_interior_closure
      exact Set.mem_iUnion.mpr ⟨⟨t.1, t.2, ht⟩, hxt⟩
  have hregT := regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hcover : Set.univ = interior (closure
      (regularSupport K S ∪ regularSupport K (T \ S))) := by
    apply Set.Subset.antisymm
    · rw [← hregT]
      exact interior_mono (closure_mono hUsub)
    · exact Set.subset_univ _
  simpa only [Set.sdiff_eq, Set.univ_inter] using
    regularOpen_disjoint_complement hSreg.1 hSreg.2 hWreg.1 hWreg.2 hdisj hcover

private theorem invariant_closure_compl (E : Set Plane)
    (hinv : IsInvariantAlong E verticalDirection) :
    IsInvariantAlong (closure E)ᶜ verticalDirection := by
  intro u hu
  have hclosure : u +ᵥ closure E = closure E := by rw [← closure_vadd, hinv u hu]
  ext x
  have hx : -u + x ∈ closure E ↔ x ∈ closure E := by
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using Set.ext_iff.mp hclosure x
  simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, Set.mem_compl_iff] using not_congr hx

theorem saturated_subfamily_carrier_eq :
  ∀ (K R : PolygonalRegion) (T S : Set Plane),
    TilesOn K T Set.univ → TilesOn R T Set.univ → S ⊆ T →
    regularizedProjection K.openCarrier = regularizedProjection R.openCarrier →
    IsInvariantAlong (regularSupport K S) verticalDirection →
    regularSupport K S = regularSupport R S
  := by
  intro K R T S hK hR hST hQ hinv
  have hKpart := regularSupport_partition_complement K T S hK hST
  have hRpart := regularSupport_partition_complement R T S hR hST
  have hW : IsInvariantAlong (regularSupport K (T \ S)) verticalDirection := by
    rw [hKpart.2]
    exact invariant_closure_compl _ hinv
  apply Set.Subset.antisymm
  · have hsub := regularSupport_subset_of_footprint K R (T \ S) hQ hW
    rw [hKpart.1, hRpart.1]
    exact Set.compl_subset_compl.mpr (closure_mono hsub)
  · exact regularSupport_subset_of_footprint K R S hQ hinv

private theorem invariant_iff_of_footprint
    (K R : PolygonalRegion) (T S : Set Plane)
    (hK : TilesOn K T Set.univ) (hR : TilesOn R T Set.univ) (hST : S ⊆ T)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier) :
    IsInvariantAlong (regularSupport K S) verticalDirection ↔
      IsInvariantAlong (regularSupport R S) verticalDirection := by
  constructor
  · intro h
    rw [← saturated_subfamily_carrier_eq K R T S hK hR hST hQ h]
    exact h
  · intro h
    rw [← saturated_subfamily_carrier_eq R K T S hR hK hST hQ.symm h]
    exact h

private theorem centerColumn_iff_of_footprint
    (K R : PolygonalRegion) (T S : Set Plane)
    (hK : TilesOn K T Set.univ) (hR : TilesOn R T Set.univ) (hST : S ⊆ T)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier) :
    IsCenterColumn K verticalDirection S ↔ IsCenterColumn R verticalDirection S := by
  have hpK : IsPacking K.prototileFamily (K.placements S) :=
    Set.Pairwise.mono (fun _ hi => hST hi) hK.2.1
  have hpR : IsPacking R.prototileFamily (R.placements S) :=
    Set.Pairwise.mono (fun _ hi => hST hi) hR.2.1
  constructor
  · rintro ⟨_, hne, hline, hinv⟩
    exact ⟨hpR, hne, hline, (invariant_iff_of_footprint K R T S hK hR hST hQ).mp hinv⟩
  · rintro ⟨_, hne, hline, hinv⟩
    exact ⟨hpK, hne, hline, (invariant_iff_of_footprint K R T S hK hR hST hQ).mpr hinv⟩

private theorem frontierLine_direction_eq_of_invariant
    (E : Set Plane) (δ : Submodule ℝ Plane) (hdim : Module.finrank ℝ δ = 1)
    (hinv : IsInvariantAlong E δ) {x : Plane} {L : AffineSubspace ℝ Plane}
    (hx : x ∈ frontier E) (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ frontier E ↔ y ∈ (L : Set Plane)) :
    L.direction = δ := by
  have hδne : δ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hdim
    omega
  obtain ⟨v, hvδ, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδne
  have hfront (w : Plane) : frontier (w +ᵥ E) = w +ᵥ frontier E := by
    rw [frontier, closure_vadd, interior_vadd]
    ext y
    simp only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem, frontier]
  let f : ℝ → Plane := fun r => r • v + x
  have hf : Continuous f := by fun_prop
  have ht : Filter.Tendsto f (𝓝 0) (𝓝 x) := by
    simpa [f] using hf.continuousAt.tendsto (x := (0 : ℝ))
  obtain ⟨a, b, hab, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ht.eventually hlocal)
  let r : ℝ := b / 2
  have hr : 0 < r := by dsimp [r]; linarith [hab.2]
  have hrI : r ∈ Set.Ioo a b := by dsimp [r]; constructor <;> linarith [hab.1, hab.2]
  have hfrontInv : r • v +ᵥ frontier E = frontier E := by
    rw [← hfront, hinv (r • v) (δ.smul_mem r hvδ)]
  have hfr : f r ∈ frontier E := hfrontInv ▸
    Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
  have hfrL : f r ∈ L := (hI hrI).mp hfr
  have hrL : r • v ∈ L.direction := by
    simpa [f, vsub_eq_sub] using L.vsub_mem_direction hfrL hxL
  have hvL : v ∈ L.direction := by
    have h := L.direction.smul_mem r⁻¹ hrL
    simpa [smul_smul, hr.ne'] using h
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hLdim hvL hvne).trans
    (eq_span_singleton_of_mem_of_finrank_eq_one hdim hvδ hvne).symm

private theorem earthquake_component_carrier_nonempty (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) (P : EarthquakeComponent K δ T) :
    P.carrier.Nonempty := by
  obtain ⟨s, hs⟩ := P.nonempty_supp
  obtain ⟨p, hp⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hopen : IsOpen (openUnion K P.centres) :=
    isOpen_iUnion (fun t => isOpen_interior.vadd (t : Plane))
  refine ⟨s.1 + p, hopen.subset_interior_closure ?_⟩
  exact Set.mem_iUnion.mpr ⟨⟨s.1, ⟨s, hs, rfl⟩⟩,
    Set.mem_vadd_set.mpr ⟨p, hp, rfl⟩⟩

private theorem localLine_direction_eq_of_completeLine
    (E : Set Plane) {x : Plane} {L M : AffineSubspace ℝ Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hline : (L : Set Plane) ⊆ frontier E)
    (hxM : x ∈ M) (hMdim : Module.finrank ℝ M.direction = 1)
    (hlocal : ∀ᶠ y in 𝓝 x, y ∈ frontier E ↔ y ∈ (M : Set Plane)) :
    M.direction = L.direction := by
  have hLne : L.direction ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hLdim
    omega
  obtain ⟨v, hvL, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hLne
  let f : ℝ → Plane := fun r => r • v + x
  have hf : Continuous f := by fun_prop
  have ht : Filter.Tendsto f (𝓝 0) (𝓝 x) := by
    simpa [f] using hf.continuousAt.tendsto (x := (0 : ℝ))
  obtain ⟨a, b, hab, hI⟩ := mem_nhds_iff_exists_Ioo_subset.mp (ht.eventually hlocal)
  let r : ℝ := b / 2
  have hr : 0 < r := by dsimp [r]; linarith [hab.2]
  have hrI : r ∈ Set.Ioo a b := by dsimp [r]; constructor <;> linarith [hab.1, hab.2]
  have hfrL : f r ∈ L := L.vadd_mem_of_mem_direction (L.direction.smul_mem r hvL) hxL
  have hfrM : f r ∈ M := (hI hrI).mp (hline hfrL)
  have hrM : r • v ∈ M.direction := by
    simpa [f, vsub_eq_sub] using M.vsub_mem_direction hfrM hxM
  have hvM : v ∈ M.direction := by
    have h := M.direction.smul_mem r⁻¹ hrM
    simpa [smul_smul, hr.ne'] using h
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hMdim hvM hvne).trans
    (eq_span_singleton_of_mem_of_finrank_eq_one hLdim hvL hvne).symm

private theorem exists_properEarthquakeCarrier (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ)
    (hcomponents : ∃ P Q : EarthquakeComponent K δ T, P ≠ Q) :
    ∃ P : EarthquakeComponent K δ T, P.carrier.Nonempty ∧ P.carrier ≠ Set.univ := by
  obtain ⟨P, Q, hPQ⟩ := hcomponents
  refine ⟨P, earthquake_component_carrier_nonempty K δ T P, ?_⟩
  intro hP
  obtain ⟨x, hx⟩ := earthquake_component_carrier_nonempty K δ T Q
  have hd := components_carriers_disjoint K δ T hdim htile.2.1
    (Set.mem_univ P) (Set.mem_univ Q) hPQ
  have hxP : x ∈ P.carrier := by rw [hP]; exact Set.mem_univ x
  exact Set.disjoint_left.mp hd hxP hx

private theorem incident_tile_frontier_ownEarthquakeComponent
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hdim : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (P Q : EarthquakeComponent K δ T) {s x : Plane}
    (hsP : s ∈ P.centres) (hxQ : x ∈ frontier Q.carrier)
    (hxs : x ∈ s +ᵥ K.support) : x ∈ frontier P.carrier := by
  have hopen : IsOpen P.carrier := (regularSupport_isRegularOpen K P.centres).1
  have hopenU : IsOpen (openUnion K P.centres) :=
    isOpen_iUnion (fun t => isOpen_interior.vadd (t : Plane))
  have htileSub : s +ᵥ K.openCarrier ⊆ P.carrier := by
    intro y hy
    exact hopenU.subset_interior_closure
      (Set.mem_iUnion.mpr ⟨⟨s, hsP⟩, hy⟩)
  have hxcl : x ∈ closure P.carrier := by
    apply closure_mono htileSub
    rw [closure_vadd]
    change x ∈ s +ᵥ closure (interior K.support)
    rwa [K.isPolygonal.closure_interior]
  by_cases hPQ : P = Q
  · simpa [hPQ] using hxQ
  · refine ⟨hxcl, ?_⟩
    rw [hopen.interior_eq]
    have hd := components_carriers_disjoint K δ T hdim htile.2.1
      (Set.mem_univ P) (Set.mem_univ Q) hPQ
    have hQsub : Q.carrier ⊆ P.carrierᶜ := Set.disjoint_right.mp hd
    exact closure_minimal hQsub hopen.isClosed_compl hxQ.1

private theorem vertexReach_of_graphReach (K : PolygonalRegion) (T : Set Plane)
    {i j : (K.polygonalProtoTiling T).placements}
    (h : (K.polygonalProtoTiling T).vertexGraph.Reachable i j) :
    vertexReach K T i.1.1 j.1.1 := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail j k hij hjk ih =>
      apply ih.tail
      refine ⟨j.2, k.2, ?_⟩
      exact ((K.polygonalProtoTiling T).vertexGraph_adj j k).mp hjk |>.2

private theorem graphReach_of_vertexReach (K : PolygonalRegion) (T : Set Plane)
    (s t : Plane) (hs : s ∈ T) (ht : t ∈ T) (h : vertexReach K T s t) :
    (K.polygonalProtoTiling T).vertexGraph.Reachable ⟨(s, ()), hs⟩ ⟨(t, ()), ht⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail t u hst htu ih =>
      have h₁ := ih htu.1
      apply h₁.trans
      by_cases htu' : t = u
      · subst u
        exact SimpleGraph.Reachable.refl _
      · apply SimpleGraph.Adj.reachable
        rw [(K.polygonalProtoTiling T).vertexGraph_adj]
        refine ⟨?_, htu.2.2⟩
        intro heq
        exact htu' (congrArg (fun i => i.1.1) heq)

private theorem vertex_class_support (K : PolygonalRegion) (T : Set Plane)
    (hpacking : IsPacking K.prototileFamily (K.placements T))
    (t : Plane) (ht : t ∈ T) :
    regularSupport K {s | s ∈ T ∧ vertexReach K T t s} =
      interior ((K.polygonalProtoTiling T).plateCarrier
        ((K.polygonalProtoTiling T).vertexGraph.connectedComponentMk ⟨(t, ()), ht⟩)) := by
  let S : Set Plane := {s | s ∈ T ∧ vertexReach K T t s}
  have hpS : IsPacking K.prototileFamily (K.placements S) :=
    Set.Pairwise.mono (fun _ hi => hi.1) hpacking
  unfold regularSupport
  rw [closure_openUnion_eq_iUnion_support hpS]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨s, hxs⟩ := Set.mem_iUnion.mp hx
    apply (K.polygonalProtoTiling T).mem_plateCarrier_iff.mpr
    refine ⟨⟨(s.1, ()), s.2.1⟩, ?_, hxs⟩
    exact ((K.polygonalProtoTiling T).samePlate_iff_component_eq _ _).mp
      (graphReach_of_vertexReach K T t s.1 ht s.2.1 s.2.2) |>.symm
  · intro hx
    obtain ⟨i, hi, hxi⟩ := (K.polygonalProtoTiling T).mem_plateCarrier_iff.mp hx
    apply Set.mem_iUnion.mpr
    refine ⟨⟨i.1.1, i.2, ?_⟩, hxi⟩
    apply vertexReach_of_graphReach K T (i := ⟨(t, ()), ht⟩) (j := i)
    apply ((K.polygonalProtoTiling T).samePlate_iff_component_eq _ _).mpr
    exact hi.symm

private theorem affineLine_subset_frontier_of_locallyStraight
    {t : Set Plane} {x : Plane} {L : AffineSubspace ℝ Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hxlocal : ∀ᶠ y in 𝓝 x, (y ∈ frontier t ↔ y ∈ (L : Set Plane)))
    (hstraight : ∀ y, y ∈ frontier t → BoundaryLocallyStraightAt t y) :
    (L : Set Plane) ⊆ frontier t := by
  have hdirection : L.direction ≠ ⊥ := by
    intro hbot
    have : Module.finrank ℝ L.direction = 0 := by rw [hbot]; simp
    omega
  obtain ⟨v, hvL, hv⟩ := (Submodule.ne_bot_iff L.direction).mp hdirection
  let f : ℝ → Plane := fun r ↦ r • v +ᵥ x
  have hf_continuous : Continuous f := by fun_prop
  have hfL : ∀ r, f r ∈ L := by
    intro r
    exact L.vadd_mem_of_mem_direction (L.direction.smul_mem r hvL) hxL
  let a : Set ℝ := f ⁻¹' frontier t
  have ha_closed : IsClosed a :=
    (isClosed_frontier : IsClosed (frontier t)).preimage hf_continuous
  have hzero : (0 : ℝ) ∈ interior a := by
    rw [mem_interior_iff_mem_nhds]
    have htendsto : Filter.Tendsto f (nhds (0 : ℝ)) (nhds x) := by
      have htendsto' : Filter.Tendsto f (nhds (0 : ℝ)) (nhds (f 0)) :=
        hf_continuous.continuousAt
      simpa only [f, zero_smul, zero_vadd] using htendsto'
    have hpull : ∀ᶠ r in nhds (0 : ℝ), f r ∈ frontier t ↔ f r ∈ (L : Set Plane) :=
      htendsto.eventually hxlocal
    filter_upwards [hpull] with r hr
    exact hr.mpr (hfL r)
  have hinterior_closed : IsClosed (interior a) := by
    rw [← closure_subset_iff_isClosed]
    intro r hr
    have hra : r ∈ a := ha_closed.closure_subset (closure_mono interior_subset hr)
    obtain ⟨L', hfrL', hL'dim, hlocal⟩ := hstraight (f r) hra
    by_cases hrint : r ∈ interior a
    · exact hrint
    have hpull : ∀ᶠ q in nhds r, (f q ∈ frontier t ↔ f q ∈ (L' : Set Plane)) :=
      hf_continuous.continuousAt.tendsto.eventually hlocal
    obtain ⟨U, hUsub, hUopen, hrU⟩ := mem_nhds_iff.mp hpull
    obtain ⟨q, hqU, hqint⟩ := (mem_closure_iff.mp hr U hUopen hrU)
    have hqr : q ≠ r := fun h ↦ hrint (h ▸ hqint)
    have hqa : q ∈ a := interior_subset hqint
    have hfqL' : f q ∈ L' := (hUsub hqU).mp hqa
    have hscaled : (q - r) • v ∈ L'.direction := by
      have := L'.vsub_mem_direction hfqL' hfrL'
      simpa only [f, vadd_eq_add, vsub_eq_sub, add_sub_add_right_eq_sub, sub_smul] using this
    have hvL' : v ∈ L'.direction := by
      have := L'.direction.smul_mem (q - r)⁻¹ hscaled
      simpa only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hqr), one_smul] using this
    rw [mem_interior_iff_mem_nhds]
    refine Filter.mem_of_superset hpull ?_
    intro q hq
    apply hq.mpr
    have hdelta : (q - r) • v ∈ L'.direction := L'.direction.smul_mem _ hvL'
    have := L'.vadd_mem_of_mem_direction hdelta hfrL'
    have heq : (q - r) • v +ᵥ f r = f q := by
      simp only [f, vadd_eq_add, sub_smul]
      abel
    rw [heq] at this
    exact this
  have hinterior_univ : interior a = univ :=
    IsClopen.eq_univ ⟨hinterior_closed, isOpen_interior⟩ ⟨0, hzero⟩
  intro y hyL
  have hvsub : y -ᵥ x ∈ L.direction := L.vsub_mem_direction hyL hxL
  obtain ⟨r, hr⟩ := exists_smul_eq_of_finrank_eq_one hLdim
    (show (⟨v, hvL⟩ : L.direction) ≠ 0 by exact Subtype.coe_ne_coe.mp hv)
    (⟨y -ᵥ x, hvsub⟩ : L.direction)
  have hr' : r • v = y -ᵥ x := congrArg Subtype.val hr
  have hyf : f r = y := by simp only [f, hr', vsub_vadd]
  have : r ∈ a := interior_subset (hinterior_univ.symm ▸ mem_univ r)
  simpa only [a, mem_preimage, hyf] using this

private theorem disjoint_regular_left_interior_of_aedisjoint_candidate
    {s t : Set Plane} (hregular : closure (interior s) = s)
    (had : MeasureTheory.AEDisjoint MeasureTheory.volume s t) :
    Disjoint s (interior t) := by
  rw [Set.disjoint_left]
  intro x hxs hxt
  rw [← hregular] at hxs
  obtain ⟨y, hyt, hys⟩ := mem_closure_iff.mp hxs (interior t) isOpen_interior hxt
  have hne : MeasureTheory.volume (interior s ∩ interior t) ≠ 0 :=
    (isOpen_interior.inter isOpen_interior).measure_ne_zero MeasureTheory.volume ⟨y, hys, hyt⟩
  exact hne (MeasureTheory.measure_mono_null
    (Set.inter_subset_inter interior_subset interior_subset) had)

private theorem exists_small_lineMap_candidate (x z : Plane) {r q : ℝ}
    (hr : 0 < r) (hq : 0 < q) :
    ∃ δ : ℝ, 0 < δ ∧
      (AffineMap.lineMap x z) δ ∈ Metric.ball x r ∩ Metric.ball x q ∧
      (AffineMap.lineMap x z) (-δ) ∈ Metric.ball x r ∩ Metric.ball x q := by
  let ρ := min r q
  have hρ : 0 < ρ := lt_min hr hq
  let n := ‖z - x‖
  have hn : 0 ≤ n := norm_nonneg _
  let δ := ρ / (2 * (n + 1))
  have hden : 0 < 2 * (n + 1) := by positivity
  have hδ : 0 < δ := div_pos hρ hden
  have hδn : δ * n < ρ := by
    change (ρ / (2 * (n + 1))) * n < ρ
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    nlinarith
  have hdist_pos : dist ((AffineMap.lineMap x z) δ) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  have hdist_neg : dist ((AffineMap.lineMap x z) (-δ)) x = δ * n := by
    rw [AffineMap.lineMap_apply_module']
    simp [dist_eq_norm, n, abs_of_pos hδ]
  refine ⟨δ, hδ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_pos]
    exact hδn.trans_le (min_le_right _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_left _ _)
  · rw [Metric.mem_ball, hdist_neg]
    exact hδn.trans_le (min_le_right _ _)

private theorem locallyStraight_lines_eq_of_aedisjoint_candidate
    {s t : Set Plane} {x : Plane}
    (hsregular : closure (interior s) = s)
    (htregular : closure (interior t) = t)
    (had : MeasureTheory.AEDisjoint MeasureTheory.volume s t)
    (hxt : x ∈ frontier t)
    {Ls Lt : AffineSubspace ℝ Plane}
    (hxLs : x ∈ Ls) (hLsdim : Module.finrank ℝ Ls.direction = 1)
    (hsline : ∀ᶠ y in 𝓝 x, (y ∈ frontier s ↔ y ∈ (Ls : Set Plane)))
    (hxLt : x ∈ Lt) (hLtdim : Module.finrank ℝ Lt.direction = 1)
    (htline : ∀ᶠ y in 𝓝 x, (y ∈ frontier t ↔ y ∈ (Lt : Set Plane))) :
    Ls = Lt := by
  obtain ⟨rs, hrs, hsball⟩ := Metric.eventually_nhds_iff.mp hsline
  obtain ⟨rt, hrt, htball⟩ := Metric.eventually_nhds_iff.mp htline
  obtain ⟨ψt, hψt⟩ :=
    Tiling.AffineSubspace.exists_levelSet_coordinate Lt x hxLt hLtdim
  have htboundary (y : Plane) (hy : y ∈ Metric.ball x rt) :
      y ∈ frontier t ↔ ψt y = ψt x :=
    (htball hy).trans (hψt y)
  have htclass := Tiling.local_levelSet_dichotomy ψt hrt htregular hxt htboundary
  dsimp only at htclass
  by_contra hne
  have hz : ∃ z, z ∈ Ls ∧ z ∉ Lt := by
    by_contra h
    push Not at h
    have hle : Ls ≤ Lt := fun z hz ↦ h z hz
    have hdir : Ls.direction = Lt.direction :=
      Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le hle)
        (hLsdim.trans hLtdim.symm)
    exact hne
      (AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir ⟨x, hxLs⟩ hle)
  obtain ⟨z, hzLs, hzLt⟩ := hz
  have hzψ : ψt z ≠ ψt x := fun h ↦ hzLt ((hψt z).2 h)
  obtain ⟨δ, hδ, hyposBalls, hynegBalls⟩ := exists_small_lineMap_candidate x z hrs hrt
  let ypos := (AffineMap.lineMap x z) δ
  let yneg := (AffineMap.lineMap x z) (-δ)
  have hyposLs : ypos ∈ Ls := AffineMap.lineMap_mem δ hxLs hzLs
  have hynegLs : yneg ∈ Ls := AffineMap.lineMap_mem (-δ) hxLs hzLs
  have hψline (r : ℝ) :
      ψt ((AffineMap.lineMap x z) r) = ψt x + r * (ψt z - ψt x) := by
    rw [AffineMap.lineMap_apply_module']
    simp only [map_add, map_smul, map_sub]
    ring
  have hsclosed : IsClosed s := by rw [← hsregular]; exact isClosed_closure
  have hdisj : Disjoint s (interior t) :=
    disjoint_regular_left_interior_of_aedisjoint_candidate hsregular had
  have contradict (y : Plane) (hyball : y ∈ Metric.ball x rs)
      (hyLs : y ∈ Ls) (hyt : y ∈ interior t) : False := by
    apply Set.disjoint_left.1 hdisj (hsclosed.frontier_subset ((hsball hyball).2 hyLs)) hyt
  rcases htclass with htpos | htneg
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hynegPos : ψt x < ψt yneg := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htpos.1 ⟨hynegBalls.2, hynegPos⟩)
    · have hyposPos : ψt x < ψt ypos := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htpos.1 ⟨hyposBalls.2, hyposPos⟩)
  · rcases lt_or_gt_of_ne hzψ with hzneg | hzpos
    · have hyposNeg : ψt ypos < ψt x := by
        dsimp only [ypos]
        rw [hψline]
        nlinarith
      exact contradict ypos hyposBalls.1 hyposLs
        (htneg.2 ⟨hyposBalls.2, hyposNeg⟩)
    · have hynegNeg : ψt yneg < ψt x := by
        dsimp only [yneg]
        rw [hψline]
        nlinarith
      exact contradict yneg hynegBalls.1 hynegLs
        (htneg.2 ⟨hynegBalls.2, hynegNeg⟩)

private theorem frontier_vadd_eq_candidate (u : Plane) (E : Set Plane) :
    frontier (u +ᵥ E) = u +ᵥ frontier E := by
  rw [frontier, closure_vadd, interior_vadd]
  ext z
  simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]

private theorem boundaryLocallyStraightAt_vadd_iff_candidate
    (u : Plane) (D : Set Plane) (x : Plane) :
    BoundaryLocallyStraightAt (u +ᵥ D) (u + x) ↔ BoundaryLocallyStraightAt D x := by
  suffices ∀ (v : Plane) (E : Set Plane) (y : Plane),
      BoundaryLocallyStraightAt E y →
        BoundaryLocallyStraightAt (v +ᵥ E) (v + y) by
    constructor
    · intro h
      have h' := this (-u) (u +ᵥ D) (u + x) h
      simpa only [neg_add_cancel_left, neg_vadd_vadd] using h'
    · exact this u D x
  intro v E y h
  obtain ⟨L, hyL, hdim, hlocal⟩ := h
  let L' : AffineSubspace ℝ Plane := AffineSubspace.mk' (v + y) L.direction
  refine ⟨L', AffineSubspace.self_mem_mk' (v + y) L.direction, ?_, ?_⟩
  · dsimp only [L']
    rw [AffineSubspace.direction_mk']
    exact hdim
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hlocal
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨r, hr, fun z hz ↦ ?_⟩
    let z' : Plane := z - v
    have hz' : dist z' y < r := by
      have hzEq : z' - y = z - (v + y) := by dsimp only [z']; abel
      simpa only [dist_eq_norm, hzEq] using hz
    have hsource := hball hz'
    rw [frontier_vadd_eq_candidate]
    change (z ∈ v +ᵥ frontier E) ↔ z ∈ L'
    have hfrontier : z ∈ v +ᵥ frontier E ↔ z' ∈ frontier E := by
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z' := by
          change v + w = z at hwz
          dsimp only [z']
          rw [← hwz]
          abel
        simpa only [this] using hw
      · intro hz'E
        refine ⟨z', hz'E, ?_⟩
        change v + z' = z
        dsimp only [z']
        abel
    rw [hfrontier, hsource]
    rw [show L = AffineSubspace.mk' y L.direction from
      (AffineSubspace.mk'_eq hyL).symm]
    simp only [L', AffineSubspace.mem_mk']
    change (z' - y ∈ L.direction) ↔ (z - (v + y) ∈ L.direction)
    rw [show z' - y = z - (v + y) by dsimp [z']; abel]

private theorem invariant_placementCarrier_frontier_locallyStraight_candidate
    (K : PolygonalRegion) (T : Set Plane) (hTiles : TilesOn K T univ)
    (U : Set (K.polygonalProtoTiling T).placements) (v : Plane) (hv : v ≠ 0)
    (hinv : ∀ r : ℝ,
      r • v +ᵥ (K.polygonalProtoTiling T).placementCarrier U =
        (K.polygonalProtoTiling T).placementCarrier U) :
    ∀ x ∈ frontier ((K.polygonalProtoTiling T).placementCarrier U),
      BoundaryLocallyStraightAt
        ((K.polygonalProtoTiling T).placementCarrier U) x := by
  classical
  let A := K.polygonalProtoTiling T
  let D := A.placementCarrier U
  have hT : K.Tiles T := (tilesOn_univ_iff_tiles K T).mp hTiles
  have hpacking : IsPacking A.prototiles A.placements := hTiles.2.1
  obtain ⟨B, hB⟩ := K.isPolygonal.isBounded.subset_closedBall (0 : Plane)
  have hvertices : (Tiling.vertexSet K.support).Finite := K.isPolygonal.vertexSet_finite
  intro x hx
  by_contra hnot
  have hinfinite :
      (Set.Icc (0 : ℝ) 1).Infinite := Set.Icc_infinite (by norm_num)
  let f : ℝ → Plane := fun r ↦ x + r • v
  have hinj : Function.Injective f := by
    intro s t hst
    apply smul_left_injective ℝ hv
    exact add_left_cancel hst
  let C : Set Plane := f '' Set.Icc (0 : ℝ) 1
  have hCinfinite : C.Infinite := hinfinite.image hinj.injOn
  let R : ℝ := B + ‖v‖ + 1
  have hcenters : (T ∩ Metric.closedBall x R).Finite :=
    (packing_centres_locallyFinite hTiles.2.1).1 _ Metric.isBounded_closedBall
  have hRpos : 0 < R := by
    have hBnonneg : 0 ≤ B := by
      obtain ⟨p, hp⟩ := K.nonempty
      have hdist := hB hp
      have hnorm : ‖p‖ ≤ B := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hdist
      exact (norm_nonneg p).trans hnorm
    dsimp [R]
    positivity
  let V : Set Plane := (fun p : Plane × Plane ↦ p.1 + p.2) ''
    ((T ∩ Metric.closedBall x R) ×ˢ Tiling.vertexSet K.support)
  have hVfinite : V.Finite := (hcenters.prod hvertices).image _
  have hCsub : C ⊆ V := by
    rintro y ⟨r, hr, rfl⟩
    have hw : r • v ∈ Submodule.span ℝ ({v} : Set Plane) :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    have hyfront : f r ∈ frontier D := by
      have hfrontInv : (r • v) +ᵥ frontier D = frontier D := by
        have h := congrArg frontier (hinv r)
        rw [frontier_vadd_eq_candidate] at h
        simpa [D] using h
      rw [← hfrontInv]
      refine ⟨x, hx, ?_⟩
      change r • v + x = f r
      dsimp only [f]
      abel
    have hnotstraight : ¬BoundaryLocallyStraightAt D (f r) := by
      intro hs
      have hs' : BoundaryLocallyStraightAt ((r • v) +ᵥ D) (r • v + f 0) := by
        have hD : (r • v) +ᵥ D = D := by simpa [D] using hinv r
        rw [hD]
        simpa [f, vadd_eq_add, add_comm] using hs
      have hsD :=
        (boundaryLocallyStraightAt_vadd_iff_candidate (r • v) D (f 0)).mp hs'
      apply hnot
      simpa [D, f] using hsD
    obtain ⟨i, hiU, hvertex⟩ :=
      A.exists_vertex_of_not_boundaryLocallyStraightAt hpacking U hyfront hnotstraight
    have hqT : i.1.1 ∈ T := i.2
    have hvertex' : f r ∈ (i.1.1 : Plane) +ᵥ Tiling.vertexSet K.support := by
      rw [← A.vertexSet_placedTile'] at hvertex
      rw [A.vertexSet_placedTile] at hvertex
      simpa [A, PolygonalRegion.polygonalProtoTiling,
        PolygonalRegion.prototileFamily, PolygonalRegion.prototile] using hvertex
    obtain ⟨p, hp, hfp⟩ := Set.mem_vadd_set.mp hvertex'
    have hpSupport : p ∈ K.support := by
      obtain ⟨tri⟩ := K.isPolygonal
      obtain ⟨t, ht, hpt⟩ := hp tri
      rw [← tri.sUnion_eq]
      exact Set.mem_sUnion.mpr ⟨t, ht, hpt.1⟩
    have hnormp : ‖p‖ ≤ B := by
      have h := hB hpSupport
      have h' : dist p 0 ≤ B := Metric.mem_closedBall.mp h
      simpa [dist_eq_norm] using h'
    have hdistyr : dist (f r) x ≤ ‖v‖ := by
      rw [dist_eq_norm]
      dsimp only [f]
      rw [show (x + r • v) - x = r • v by abel, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg hr.1]
      exact mul_le_of_le_one_left (norm_nonneg v) hr.2
    have hdistqi : dist (i.1.1 : Plane) (f r) = ‖p‖ := by
      have hfp' : (i.1.1 : Plane) + p = f r := by simpa [vadd_eq_add] using hfp
      rw [← hfp', dist_eq_norm]
      simp [add_sub_cancel_left]
    have hqball : i.1.1 ∈ Metric.closedBall x R := by
      rw [Metric.mem_closedBall]
      have htri := dist_triangle (i.1.1 : Plane) (f r) x
      rw [hdistqi] at htri
      dsimp [R]
      linarith
    change ∃ z ∈ (T ∩ Metric.closedBall x R) ×ˢ Tiling.vertexSet K.support,
      z.1 + z.2 = f r
    refine ⟨(i.1.1, p), ⟨⟨hqT, hqball⟩, hp⟩, ?_⟩
    have : (i.1.1 : Plane) + p = f r := by simpa [vadd_eq_add] using hfp
    exact this
  exact hCinfinite.not_finite (hVfinite.subset hCsub)

private theorem regularSupport_invariant_frontier_locallyStraight_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T univ)
    (hST : S ⊆ T)
    {δ : Submodule ℝ Plane} {v : Plane} (hv : v ∈ δ) (hvne : v ≠ 0)
    (hinv : IsInvariantAlong (regularSupport K S) δ) :
    ∀ x ∈ frontier (regularSupport K S),
      BoundaryLocallyStraightAt (regularSupport K S) x := by
  classical
  let A := K.polygonalProtoTiling T
  let U : Set A.placements := {i | i.1.1 ∈ S}
  have hpacking : IsPacking A.prototiles A.placements := hTiles.2.1
  have hpackingS : IsPacking K.prototileFamily (K.placements S) :=
    Set.Pairwise.mono (fun _ hi => hST hi) hTiles.2.1
  have hcarrier : A.placementCarrier U = closure (openUnion K S) := by
    rw [closure_openUnion_eq_iUnion_support hpackingS]
    unfold Tiling.PolygonalProtoTiling.placementCarrier
    ext x
    simp [A, PolygonalRegion.polygonalProtoTiling, U,
      PolygonalRegion.prototileFamily, PolygonalRegion.prototile]
    constructor
    · rintro ⟨a, haS, haT, hix⟩
      obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hix
      exact Set.mem_add.mpr ⟨a, haS, p, hp, by simpa [vadd_eq_add] using hpx⟩
    · intro hx
      obtain ⟨a, ha, p, hp, hax⟩ := Set.mem_add.mp hx
      refine ⟨a, ha, hST ha, ?_⟩
      apply Set.mem_vadd_set.mpr
      exact ⟨p, hp, by simpa [vadd_eq_add] using hax⟩
  have hregular : regularSupport K S = interior (A.placementCarrier U) := by
    rw [regularSupport, ← hcarrier]
  have hclosed : IsClosed (A.placementCarrier U) :=
    A.placementCarrier_isClosed hpacking U
  have hregcarrier : closure (interior (A.placementCarrier U)) =
      A.placementCarrier U := A.placementCarrier_closure_interior hpacking U
  have hclosure : closure (regularSupport K S) = A.placementCarrier U := by
    rw [hregular]
    exact hregcarrier
  have hinvCarrier : ∀ r : ℝ,
      r • v +ᵥ A.placementCarrier U = A.placementCarrier U := by
    intro r
    calc
      r • v +ᵥ A.placementCarrier U =
          r • v +ᵥ closure (regularSupport K S) := by rw [hclosure]
      _ = closure (r • v +ᵥ regularSupport K S) := by rw [← closure_vadd]
      _ = closure (regularSupport K S) := by
        rw [hinv (r • v) (δ.smul_mem r hv)]
      _ = A.placementCarrier U := hclosure
  have hstraight := invariant_placementCarrier_frontier_locallyStraight_candidate
    K T hTiles U v hvne hinvCarrier
  have hfrontier : frontier (interior (A.placementCarrier U)) =
      frontier (A.placementCarrier U) := by
    rw [frontier, frontier, interior_interior, hregcarrier, hclosed.closure_eq]
  intro x hx
  have hx' : x ∈ frontier (A.placementCarrier U) := by
    rw [← hfrontier, ← hregular]
    exact hx
  have hlocal := hstraight x hx'
  simpa only [hregular, BoundaryLocallyStraightAt, hfrontier] using hlocal

private theorem invariant_regularSupport_frontierLine_complete_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T univ)
    (hST : S ⊆ T) {δ : Submodule ℝ Plane} {v : Plane}
    (hv : v ∈ δ) (hvne : v ≠ 0)
    (hinv : IsInvariantAlong (regularSupport K S) δ)
    {x : Plane} {L : AffineSubspace ℝ Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hxlocal : ∀ᶠ y in 𝓝 x,
      (y ∈ frontier (regularSupport K S) ↔ y ∈ (L : Set Plane))) :
    (L : Set Plane) ⊆ frontier (regularSupport K S) := by
  have hstraight := regularSupport_invariant_frontier_locallyStraight_candidate
    K T S hTiles hST hv hvne hinv
  exact affineLine_subset_frontier_of_locallyStraight hxL hLdim hxlocal hstraight

private theorem exists_invariant_regularSupport_frontierLine_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T univ)
    (hST : S ⊆ T) {δ : Submodule ℝ Plane} {v : Plane}
    (hv : v ∈ δ) (hvne : v ≠ 0)
    (hinv : IsInvariantAlong (regularSupport K S) δ)
    (hne : (regularSupport K S).Nonempty)
    (hproper : regularSupport K S ≠ univ) :
    ∃ x : Plane, ∃ L : AffineSubspace ℝ Plane,
      x ∈ frontier (regularSupport K S) ∧ x ∈ L ∧
      Module.finrank ℝ L.direction = 1 ∧
      (L : Set Plane) ⊆ frontier (regularSupport K S) := by
  have hfrontier : (frontier (regularSupport K S)).Nonempty := by
    by_contra h
    have hempty : frontier (regularSupport K S) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rcases frontier_eq_empty_iff.mp hempty with hEempty | hEuniv
    · exact (hne.ne_empty hEempty)
    · exact hproper hEuniv
  obtain ⟨x, hx⟩ := hfrontier
  obtain ⟨L, hxL, hLdim, hxlocal⟩ :=
    regularSupport_invariant_frontier_locallyStraight_candidate
      K T S hTiles hST hv hvne hinv x hx
  have hline := invariant_regularSupport_frontierLine_complete_candidate
    K T S hTiles hST hv hvne hinv hxL hLdim hxlocal
  exact ⟨x, L, hx, hxL, hLdim, hline⟩

private theorem exists_opposite_incident_tiles_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T univ)
    (hST : S ⊆ T) {x : Plane}
    (hx : x ∈ frontier (regularSupport K S)) :
    ∃ s ∈ S, ∃ t ∈ T \ S,
      x ∈ frontier (s +ᵥ K.support) ∧ x ∈ frontier (t +ᵥ K.support) := by
  classical
  let A := K.polygonalProtoTiling T
  let U : Set A.placements := {i | i.1.1 ∈ S}
  have hpack : IsPacking A.prototiles A.placements := hTiles.2.1
  have hpackS : IsPacking K.prototileFamily (K.placements S) :=
    Set.Pairwise.mono (fun _ hi => hST hi) hTiles.2.1
  have hcarrier : A.placementCarrier U = closure (openUnion K S) := by
    rw [closure_openUnion_eq_iUnion_support hpackS]
    unfold Tiling.PolygonalProtoTiling.placementCarrier
    ext y
    simp [A, PolygonalRegion.polygonalProtoTiling, U,
      PolygonalRegion.prototileFamily, PolygonalRegion.prototile]
    constructor
    · rintro ⟨a, haS, haT, hax⟩
      obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hax
      exact Set.mem_add.mpr ⟨a, haS, p, hp, by simpa [vadd_eq_add] using hpx⟩
    · intro hy
      obtain ⟨a, ha, p, hp, hay⟩ := Set.mem_add.mp hy
      refine ⟨a, ha, hST ha, ?_⟩
      apply Set.mem_vadd_set.mpr
      exact ⟨p, hp, by simpa [vadd_eq_add] using hay⟩
  have hregular : regularSupport K S = interior (A.placementCarrier U) := by
    rw [regularSupport, ← hcarrier]
  have hclosed : IsClosed (A.placementCarrier U) := A.placementCarrier_isClosed hpack U
  have hregcarrier : closure (interior (A.placementCarrier U)) =
      A.placementCarrier U := A.placementCarrier_closure_interior hpack U
  have hfrontier : frontier (interior (A.placementCarrier U)) =
      frontier (A.placementCarrier U) := by
    rw [frontier, frontier, interior_interior, hregcarrier, hclosed.closure_eq]
  have hxcarrier : x ∈ frontier (A.placementCarrier U) := by
    have hx' : x ∈ frontier (interior (A.placementCarrier U)) := by
      rwa [← hregular]
    exact hfrontier ▸ hx'
  have htiling : IsTiling A.prototiles A.placements := by
    simpa [PolygonalRegion.Tiles, A, PolygonalRegion.polygonalProtoTiling] using
      (tilesOn_univ_iff_tiles K T).mp hTiles
  have hxcompl : x ∈ frontier (A.placementCarrier Uᶜ) := by
    rw [← A.frontier_placementCarrier_compl htiling U]
    exact hxcarrier
  obtain ⟨i, hiU, hxi⟩ := A.mem_placementCarrier_iff.mp
    ((A.placementCarrier_isClosed hpack U).frontier_subset hxcarrier)
  obtain ⟨j, hjU, hxj⟩ := A.mem_placementCarrier_iff.mp
    ((A.placementCarrier_isClosed hpack Uᶜ).frontier_subset hxcompl)
  have hiSub : placedTile A.prototiles i.1 ⊆ A.placementCarrier U := by
    intro y hy
    exact A.mem_placementCarrier_iff.mpr ⟨i, hiU, hy⟩
  have hjSub : placedTile A.prototiles j.1 ⊆ A.placementCarrier Uᶜ := by
    intro y hy
    exact A.mem_placementCarrier_iff.mpr ⟨j, hjU, hy⟩
  have hxiFront : x ∈ frontier (placedTile A.prototiles i.1) := by
    rw [frontier, (A.isClosed_placedTile i.1).closure_eq]
    exact ⟨hxi, fun hxin ↦ hxcarrier.2 (interior_mono hiSub hxin)⟩
  have hxjFront : x ∈ frontier (placedTile A.prototiles j.1) := by
    rw [frontier, (A.isClosed_placedTile j.1).closure_eq]
    exact ⟨hxj, fun hxjn ↦ hxcompl.2 (interior_mono hjSub hxjn)⟩
  have hiS : i.1.1 ∈ S := by simpa [U] using hiU
  have hjT : j.1.1 ∈ T := j.2
  have hjNotS : j.1.1 ∉ S := by simpa [U] using hjU
  refine ⟨i.1.1, hiS, j.1.1, ⟨hjT, hjNotS⟩, ?_, ?_⟩
  · simpa [A, PolygonalRegion.polygonalProtoTiling,
      PolygonalRegion.prototileFamily, PolygonalRegion.prototile] using hxiFront
  · simpa [A, PolygonalRegion.polygonalProtoTiling,
      PolygonalRegion.prototileFamily, PolygonalRegion.prototile] using hxjFront

private theorem vertexClass_frontierLine_complete_candidate
    (K : PolygonalRegion) (T : Set Plane) (htiles : TilesOn K T univ)
    (t : Plane) (ht : t ∈ T) {x : Plane} {L : AffineSubspace ℝ Plane}
    (hxL : x ∈ L) (hLdim : Module.finrank ℝ L.direction = 1)
    (hxlocal : ∀ᶠ y in 𝓝 x,
      (y ∈ frontier (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}) ↔
        y ∈ (L : Set Plane))) :
    (L : Set Plane) ⊆
      frontier (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}) := by
  let A := K.polygonalProtoTiling T
  let C := A.vertexGraph.connectedComponentMk ⟨(t, ()), ht⟩
  have hT : K.Tiles T := (tilesOn_univ_iff_tiles K T).mp htiles
  have hsupport := vertex_class_support K T htiles.2.1 t ht
  have hregular := A.plateCarrier_closure_interior htiles.2.1 C
  have hclosed := A.plateCarrier_isClosed htiles.2.1 C
  have hfrontier : frontier (interior (A.plateCarrier C)) =
      frontier (A.plateCarrier C) := by
    rw [frontier, hregular, interior_interior, hclosed.frontier_eq]
  have hstraight (y : Plane) (hy : y ∈ frontier (interior (A.plateCarrier C))) :
      BoundaryLocallyStraightAt (interior (A.plateCarrier C)) y := by
    have hy' : y ∈ frontier (A.plateCarrier C) := hfrontier ▸ hy
    have hlocal := A.plateCarrier_boundaryLocallyStraightAt hT C hy'
    simpa only [BoundaryLocallyStraightAt, hfrontier] using hlocal
  rw [hsupport] at hxlocal ⊢
  exact affineLine_subset_frontier_of_locallyStraight hxL hLdim hxlocal hstraight

private theorem lineOrbit_mem_iff_of_frontier_orbit
    {E : Set Plane} (hEopen : IsOpen E) (v : Plane)
    (hfrontier : ∀ x ∈ frontier E, ∀ r : ℝ, x + r • v ∈ frontier E)
    (x : Plane) (r : ℝ) :
    (x + r • v ∈ E ↔ x ∈ E) := by
  let f : ℝ → Plane := fun t ↦ x + t • v
  have hf : Continuous f := by fun_prop
  by_cases hcross : ∃ t : ℝ, f t ∈ frontier E
  · obtain ⟨t₀, ht₀⟩ := hcross
    have horbit : ∀ t : ℝ, f t ∈ frontier E := by
      intro t
      have := hfrontier (f t₀) ht₀ (t - t₀)
      have heq : f t₀ + (t - t₀) • v = f t := by
        change x + t₀ • v + (t - t₀) • v = x + t • v
        module
      rw [heq] at this
      exact this
    have hfrontDisj : Disjoint (frontier E) E := by
      rw [Set.disjoint_left]
      intro y hyfront hyE
      rw [frontier, hEopen.interior_eq] at hyfront
      exact hyfront.2 hyE
    have hnot : ∀ t : ℝ, f t ∉ E := by
      intro t ht
      exact (Set.disjoint_left.1 hfrontDisj) (horbit t) ht
    have hxnot : x ∉ E := by simpa [f] using hnot 0
    have hrnot : x + r • v ∉ E := by simpa [f] using hnot r
    exact iff_of_false hrnot hxnot
  · have havoids : ∀ t : ℝ, f t ∉ frontier E := by
      intro t ht
      exact hcross ⟨t, ht⟩
    let U : Set ℝ := f ⁻¹' E
    have hUopen : IsOpen U := hEopen.preimage hf
    have hUcomplOpen : IsOpen Uᶜ := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      have hnotClosure : f t ∉ closure E := by
        intro hcl
        have hfront : f t ∈ frontier E := by
          rw [frontier, hEopen.interior_eq]
          exact ⟨hcl, ht⟩
        exact havoids t hfront
      have hnhds : (closure E)ᶜ ∈ 𝓝 (f t) :=
        (isClosed_closure.isOpen_compl).mem_nhds hnotClosure
      filter_upwards [hf.continuousAt.preimage_mem_nhds hnhds] with s hs
      change f s ∉ E
      exact fun hsE ↦ hs (subset_closure hsE)
    have hUclosed : IsClosed U := by simpa using hUcomplOpen.isClosed_compl
    have hUclopen : IsClopen U := ⟨hUclosed, hUopen⟩
    have hconstMem (s t : ℝ) : (s ∈ U ↔ t ∈ U) := by
      rcases isClopen_iff.mp hUclopen with hUempty | hUuniv
      · simp [hUempty]
      · simp [hUuniv]
    simpa [U, f] using hconstMem r 0

private theorem invariantAlong_of_frontier_orbit_of_rankOne
    {E : Set Plane} {δ : Submodule ℝ Plane} (hEopen : IsOpen E)
    (hδ : Module.finrank ℝ δ = 1) {v : Plane} (hv : v ∈ δ) (hvne : v ≠ 0)
    (hfrontier : ∀ x ∈ frontier E, ∀ r : ℝ, x + r • v ∈ frontier E) :
    IsInvariantAlong E δ := by
  intro u hu
  have hspan : δ = Submodule.span ℝ ({v} : Set Plane) :=
    eq_span_singleton_of_mem_of_finrank_eq_one hδ hv hvne
  rw [hspan] at hu
  rcases Submodule.mem_span_singleton.mp hu with ⟨r, rfl⟩
  ext x
  simp only [mem_vadd_set_iff_neg_vadd_mem]
  have hmem := lineOrbit_mem_iff_of_frontier_orbit hEopen v hfrontier (x - r • v) r
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmem.symm

private theorem affineLines_intersect_of_distinct_direction_candidate
    {L M : AffineSubspace ℝ Plane}
    (hLdim : Module.finrank ℝ L.direction = 1)
    (hMdim : Module.finrank ℝ M.direction = 1)
    (hdirs : L.direction ≠ M.direction)
    (hLne : (L : Set Plane).Nonempty) (hMne : (M : Set Plane).Nonempty) :
    ((L : Set Plane) ∩ M).Nonempty := by
  have hinf : L.direction ⊓ M.direction = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    by_contra hzne
    have hspanL := eq_span_singleton_of_mem_of_finrank_eq_one hLdim hz.1 hzne
    have hspanM := eq_span_singleton_of_mem_of_finrank_eq_one hMdim hz.2 hzne
    exact hdirs (hspanL.trans hspanM.symm)
  have hsupdim : Module.finrank ℝ ↑(L.direction ⊔ M.direction) = 2 := by
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq L.direction M.direction
    rw [hinf, finrank_bot, hLdim, hMdim] at hdim
    omega
  have hsup : L.direction ⊔ M.direction = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa only [Complex.finrank_real_complex] using hsupdim
  obtain ⟨xs, hxs⟩ := hLne
  obtain ⟨xt, hxt⟩ := hMne
  have hdelta : xt -ᵥ xs ∈ L.direction ⊔ M.direction := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨v, hvL, w, hwM, hvw⟩ := Submodule.mem_sup.mp hdelta
  let p : Plane := v +ᵥ xs
  have hp_eq : p = -w +ᵥ xt := by
    dsimp only [p]
    rw [vadd_eq_add, vadd_eq_add, neg_add_eq_sub]
    rw [vsub_eq_sub] at hvw
    calc
      v + xs = (v + w) + xs - w := by abel
      _ = (xt - xs) + xs - w := by rw [hvw]
      _ = xt - w := by abel
  have hpL : p ∈ L := by
    dsimp only [p]
    exact L.vadd_mem_of_mem_direction hvL hxs
  have hpM : p ∈ M := by
    rw [hp_eq]
    exact M.vadd_mem_of_mem_direction (M.direction.neg_mem hwM) hxt
  exact ⟨p, hpL, hpM⟩

private theorem incident_tile_vertex_of_transverse_seams_candidate
    {tile Ccomp Dcomp : Set Plane} {x : Plane}
    (htilePolygonal : IsPolygonal tile)
    (hxTile : x ∈ frontier tile)
    (hCregular : closure (interior Ccomp) = Ccomp)
    (hDregular : closure (interior Dcomp) = Dcomp)
    (hCdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume tile Ccomp)
    (hDdisjoint : MeasureTheory.AEDisjoint MeasureTheory.volume tile Dcomp)
    (hxC : x ∈ frontier Ccomp) (hxD : x ∈ frontier Dcomp)
    {LC LD : AffineSubspace ℝ Plane}
    (hxLC : x ∈ LC) (hLCdim : Module.finrank ℝ LC.direction = 1)
    (hCline : ∀ᶠ y in 𝓝 x,
      (y ∈ frontier Ccomp ↔ y ∈ (LC : Set Plane)))
    (hxLD : x ∈ LD) (hLDdim : Module.finrank ℝ LD.direction = 1)
    (hDline : ∀ᶠ y in 𝓝 x,
      (y ∈ frontier Dcomp ↔ y ∈ (LD : Set Plane)))
    (hdirs : LC.direction ≠ LD.direction) :
    x ∈ Tiling.vertexSet tile := by
  by_contra hxvertex
  obtain ⟨LT, hxLT, hLTdim, hTline⟩ :=
    htilePolygonal.boundaryLocallyStraightAt_of_not_mem_vertexSet hxTile hxvertex
  have hTC : LT = LC :=
    locallyStraight_lines_eq_of_aedisjoint_candidate
      htilePolygonal.closure_interior hCregular hCdisjoint hxC
      hxLT hLTdim hTline hxLC hLCdim hCline
  have hTD : LT = LD :=
    locallyStraight_lines_eq_of_aedisjoint_candidate
      htilePolygonal.closure_interior hDregular hDdisjoint hxD
      hxLT hLTdim hTline hxLD hLDdim hDline
  exact hdirs (by rw [← hTC, hTD])


private theorem component_centres_subset_candidate (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) (P : EarthquakeComponent K δ T) :
    P.centres ⊆ T := by
  rintro x ⟨s, hs, rfl⟩
  exact s.property

private theorem placementCarrier_eq_closure_openUnion_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T Set.univ)
    (hST : S ⊆ T) :
    (K.polygonalProtoTiling T).placementCarrier
        {i | i.1.1 ∈ S} = closure (openUnion K S) := by
  let A := K.polygonalProtoTiling T
  have hpacking : IsPacking K.prototileFamily (K.placements S) :=
    Set.Pairwise.mono (fun _ hi => hST hi) hTiles.2.1
  rw [closure_openUnion_eq_iUnion_support hpacking]
  unfold Tiling.PolygonalProtoTiling.placementCarrier
  ext x
  simp [A, PolygonalRegion.polygonalProtoTiling,
    PolygonalRegion.prototileFamily, PolygonalRegion.prototile]
  constructor
  · rintro ⟨a, haS, haT, hax⟩
    obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hax
    exact Set.mem_add.mpr ⟨a, haS, p, hp, by simpa [vadd_eq_add] using hpx⟩
  · intro hx
    obtain ⟨a, ha, p, hp, hax⟩ := Set.mem_add.mp hx
    refine ⟨a, ha, hST ha, ?_⟩
    apply Set.mem_vadd_set.mpr
    exact ⟨p, hp, by simpa [vadd_eq_add] using hax⟩

private theorem placedTile_aedisjoint_complementCarrier_candidate
    (K : PolygonalRegion) (T S : Set Plane) (hTiles : TilesOn K T univ)
    (hST : S ⊆ T) {s : Plane} (hs : s ∈ S) :
    MeasureTheory.AEDisjoint MeasureTheory.volume (s +ᵥ K.support)
      ((K.polygonalProtoTiling T).placementCarrier {i | i.1.1 ∉ S}) := by
  let A := K.polygonalProtoTiling T
  let i : A.placements := ⟨(s, ()), hST hs⟩
  have hdisj : Disjoint ({i} : Set A.placements) {i | i.1.1 ∉ S} := by
    rw [Set.disjoint_left]
    intro j hj₁ hj₂
    have hji : j = i := by simpa using hj₁
    subst j
    exact hj₂ hs
  have htiling : IsTiling A.prototiles A.placements := by
    simpa [A, PolygonalRegion.polygonalProtoTiling, PolygonalRegion.Tiles] using
      (tilesOn_univ_iff_tiles K T).mp hTiles
  have had := A.placementCarrier_aedisjoint htiling hdisj
  have hsub : s +ᵥ K.support ⊆ A.placementCarrier {i} := by
    intro y hy
    apply A.mem_placementCarrier_iff.mpr
    refine ⟨i, by simp, ?_⟩
    simpa [A, PolygonalRegion.polygonalProtoTiling,
      PolygonalRegion.prototileFamily, PolygonalRegion.prototile] using hy
  exact had.mono hsub (Set.Subset.rfl)

private theorem earthquakeComponent_placementCarrier_candidate
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hTiles : TilesOn K T univ) (P : EarthquakeComponent K δ T) :
    P.carrier = interior ((K.polygonalProtoTiling T).placementCarrier
      {i | i.1.1 ∈ P.centres}) := by
  let A := K.polygonalProtoTiling T
  have hST : P.centres ⊆ T := component_centres_subset_candidate K δ T P
  rw [EarthquakeComponent.carrier, regularSupport,
    ← placementCarrier_eq_closure_openUnion_candidate K T P.centres hTiles hST]

theorem vertex_class_saturated :
  ∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    (∃ P Q : EarthquakeComponent K δ T, P ≠ Q) →
    ∀ t ∈ T, IsInvariantAlong
      (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}) δ
  := by
  intro K δ T hδ hTiles hcomponents t ht
  classical
  let S : Set Plane := {s | s ∈ T ∧ vertexReach K T t s}
  have hST : S ⊆ T := fun _ hs => hs.1
  have htS : t ∈ S := ⟨ht, Relation.ReflTransGen.refl⟩
  by_cases hSeq : S = T
  · have hfull : regularSupport K S = univ := by
      rw [hSeq]
      exact regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTiles
    rw [hfull]
    intro u hu
    ext x
    simp
  · let A := K.polygonalProtoTiling T
    have hpack : IsPacking K.prototileFamily (K.placements T) := hTiles.2.1
    have hT : K.Tiles T := (tilesOn_univ_iff_tiles K T).mp hTiles
    have htiling : IsTiling A.prototiles A.placements := by
      simpa [A, PolygonalRegion.polygonalProtoTiling, PolygonalRegion.Tiles] using hT
    have hE : regularSupport K S =
        interior (A.placementCarrier {i | i.1.1 ∈ S}) := by
      rw [regularSupport, ← placementCarrier_eq_closure_openUnion_candidate
        K T S hTiles hST]
    obtain ⟨Q, hQnonempty, hQproper⟩ :=
      exists_properEarthquakeCarrier K δ T hδ hTiles hcomponents
    have hδne : δ ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hδ
      omega
    obtain ⟨v, hvδ, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδne
    have hfullT : regularSupport K T = univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTiles
    have hInvariantT : IsInvariantAlong (regularSupport K T) δ := by
      intro u hu
      rw [hfullT]
      ext x
      simp
    have hQinv : IsInvariantAlong Q.carrier δ :=
      component_isInvariant K δ T hδ hpack hInvariantT Q
    obtain ⟨xQ, M, hxQM, hxM, hMdim, hMfull⟩ :=
      exists_invariant_regularSupport_frontierLine_candidate K T Q.centres
        hTiles (component_centres_subset_candidate K δ T Q)
        hvδ hvne hQinv hQnonempty hQproper
    obtain ⟨LQ, hxLQ, hLQdim, hLQlocal⟩ :=
      regularSupport_invariant_frontier_locallyStraight_candidate K T Q.centres
        hTiles (component_centres_subset_candidate K δ T Q)
        hvδ hvne hQinv xQ hxQM
    have hMdirection : M.direction = δ := by
      have hlocalEq := localLine_direction_eq_of_completeLine
        Q.carrier hxM hMdim hMfull hxLQ hLQdim hLQlocal
      rw [← hlocalEq]
      exact frontierLine_direction_eq_of_invariant Q.carrier δ hδ hQinv
        hxQM hxLQ hLQdim hLQlocal
    have hQcarrier := earthquakeComponent_placementCarrier_candidate K δ T hTiles Q
    let UQ : Set A.placements := {i | i.1.1 ∈ Q.centres}
    have hQfront : frontier Q.carrier = frontier (A.placementCarrier UQᶜ) := by
      rw [hQcarrier]
      have hreg := A.placementCarrier_closure_interior hpack UQ
      have hclosed := A.placementCarrier_isClosed hpack UQ
      have hfront : frontier (interior (A.placementCarrier UQ)) =
          frontier (A.placementCarrier UQ) := by
        rw [frontier, frontier, interior_interior, hreg, hclosed.closure_eq]
      rw [hfront, A.frontier_placementCarrier_compl htiling UQ]
    have hEopen : IsOpen (regularSupport K S) :=
      (regularSupport_isRegularOpen K S).1
    have hfrontOrbit : ∀ x ∈ frontier (regularSupport K S), ∀ r : ℝ,
        x + r • v ∈ frontier (regularSupport K S) := by
      intro x hx r
      have hclassBoundaryStraight : ∀ y ∈ frontier (regularSupport K S),
          BoundaryLocallyStraightAt (regularSupport K S) y := by
        intro y hy
        let C := A.vertexGraph.connectedComponentMk ⟨(t, ()), ht⟩
        have hclassSupport : regularSupport K S = interior (A.plateCarrier C) := by
          simpa [A, C, S] using vertex_class_support K T hpack t ht
        have hreg := A.plateCarrier_closure_interior hpack C
        have hclosed := A.plateCarrier_isClosed hpack C
        have hfront : frontier (interior (A.plateCarrier C)) =
            frontier (A.plateCarrier C) := by
          rw [frontier, hreg, interior_interior, hclosed.frontier_eq]
        have hy' : y ∈ frontier (A.plateCarrier C) := by
          rw [← hfront, ← hclassSupport]
          exact hy
        have hlocal := A.plateCarrier_boundaryLocallyStraightAt hT C hy'
        rw [hclassSupport]
        simpa only [BoundaryLocallyStraightAt, hfront] using hlocal
      obtain ⟨L, hxL, hLdim, hLlocal⟩ := hclassBoundaryStraight x hx
      have hlineFull := vertexClass_frontierLine_complete_candidate K T hTiles t ht
        hxL hLdim hLlocal
      have hclassDirection : L.direction = δ := by
        by_contra hLδ
        have hdirsLM : L.direction ≠ M.direction := by
          rw [hMdirection]
          exact hLδ
        obtain ⟨p, hpL, hpM⟩ := affineLines_intersect_of_distinct_direction_candidate
          hLdim hMdim hdirsLM ⟨x, hxL⟩ ⟨xQ, hxM⟩
        have hpE : p ∈ frontier (regularSupport K S) := hlineFull hpL
        have hpQ : p ∈ frontier Q.carrier := hMfull hpM
        obtain ⟨Lp, hpLp, hLpdim, hLpLocal⟩ := hclassBoundaryStraight p hpE
        have hLpDirection : Lp.direction = L.direction :=
          localLine_direction_eq_of_completeLine
            (regularSupport K S) hpL hLdim hlineFull hpLp hLpdim hLpLocal
        obtain ⟨s, hsS, t', htNotS, hps, hpt⟩ :=
          exists_opposite_incident_tiles_candidate K T S hTiles hST hpE
        let Ps : EarthquakeComponent K δ T :=
          (earthquakeGraph K δ T).connectedComponentMk ⟨s, hsS.1⟩
        let Pt : EarthquakeComponent K δ T :=
          (earthquakeGraph K δ T).connectedComponentMk ⟨t', htNotS.1⟩
        have hsPs : s ∈ Ps.centres := by
          refine ⟨⟨s, hsS.1⟩, ?_, rfl⟩
          simp [Ps]
        have htPt : t' ∈ Pt.centres := by
          refine ⟨⟨t', htNotS.1⟩, ?_, rfl⟩
          simp [Pt]
        have hpPs : p ∈ frontier Ps.carrier :=
          incident_tile_frontier_ownEarthquakeComponent K δ T hδ hTiles
            Ps Q hsPs hpQ ((K.isPolygonal.vadd s).isClosed.frontier_subset hps)
        have hpPt : p ∈ frontier Pt.carrier :=
          incident_tile_frontier_ownEarthquakeComponent K δ T hδ hTiles
            Pt Q htPt hpQ ((K.isPolygonal.vadd t').isClosed.frontier_subset hpt)
        have hsInv : IsInvariantAlong Ps.carrier δ :=
          component_isInvariant K δ T hδ hpack hInvariantT Ps
        have htInv : IsInvariantAlong Pt.carrier δ :=
          component_isInvariant K δ T hδ hpack hInvariantT Pt
        have hsLocal := regularSupport_invariant_frontier_locallyStraight_candidate
          K T Ps.centres hTiles (component_centres_subset_candidate K δ T Ps)
          hvδ hvne hsInv p hpPs
        obtain ⟨Ls, hpLs, hLsDim, hLsLocal⟩ := hsLocal
        have hLsLocal' : ∀ᶠ y in 𝓝 p,
            (y ∈ frontier Ps.carrier ↔ y ∈ (Ls : Set Plane)) := by
          simpa only [EarthquakeComponent.carrier] using hLsLocal
        have hLsDirection : Ls.direction = δ :=
          frontierLine_direction_eq_of_invariant Ps.carrier δ hδ hsInv
            hpPs hpLs hLsDim hLsLocal
        have htLocal := regularSupport_invariant_frontier_locallyStraight_candidate
          K T Pt.centres hTiles (component_centres_subset_candidate K δ T Pt)
          hvδ hvne htInv p hpPt
        obtain ⟨Lt, hpLt, hLtDim, hLtLocal⟩ := htLocal
        have hLtLocal' : ∀ᶠ y in 𝓝 p,
            (y ∈ frontier Pt.carrier ↔ y ∈ (Lt : Set Plane)) := by
          simpa only [EarthquakeComponent.carrier] using hLtLocal
        have hLtDirection : Lt.direction = δ :=
          frontierLine_direction_eq_of_invariant Pt.carrier δ hδ htInv
            hpPt hpLt hLtDim hLtLocal
        let UC : Set A.placements := {i | i.1.1 ∈ S}
        let US : Set A.placements := {i | i.1.1 ∈ T \ S}
        let UPs : Set A.placements := {i | i.1.1 ∈ Ps.centres}
        let UPt : Set A.placements := {i | i.1.1 ∈ Pt.centres}
        have hEcarrier : A.placementCarrier UC =
            closure (openUnion K S) := by
          exact placementCarrier_eq_closure_openUnion_candidate K T S hTiles hST
        have hCfront : frontier (regularSupport K S) = frontier (A.placementCarrier UC) := by
          rw [hE]
          change frontier (interior (A.placementCarrier UC)) =
            frontier (A.placementCarrier UC)
          have hreg := A.placementCarrier_closure_interior hpack UC
          have hclosed := A.placementCarrier_isClosed hpack UC
          rw [frontier, frontier, interior_interior, hreg, hclosed.closure_eq]
        have hSfront : frontier (regularSupport K S) =
            frontier (A.placementCarrier USᶜ) := by
          have hcomp : USᶜ = UC := by
            ext i
            constructor
            · intro hi
              have hnot : ¬ (i.1.1 ∉ S) := by
                intro hnotS
                exact hi ⟨i.2, hnotS⟩
              exact not_not.mp hnot
            · intro hiS hiDiff
              exact hiDiff.2 hiS
          rw [hcomp, hCfront]
        have hTfront : frontier (regularSupport K S) =
            frontier (A.placementCarrier {i | i.1.1 ∉ S}) := by
          calc
            frontier (regularSupport K S) = frontier (A.placementCarrier UC) := hCfront
            _ = frontier (A.placementCarrier UCᶜ) :=
              A.frontier_placementCarrier_compl htiling UC
            _ = frontier (A.placementCarrier {i | i.1.1 ∉ S}) := by
              have hcomp : UCᶜ = {i | i.1.1 ∉ S} := by
                ext i
                rfl
              rw [hcomp]
        have hPsCarrier := earthquakeComponent_placementCarrier_candidate K δ T hTiles Ps
        have hPtCarrier := earthquakeComponent_placementCarrier_candidate K δ T hTiles Pt
        have hPsFront : frontier Ps.carrier = frontier (A.placementCarrier UPsᶜ) := by
          rw [hPsCarrier]
          have hreg := A.placementCarrier_closure_interior hpack UPs
          have hclosed := A.placementCarrier_isClosed hpack UPs
          have hfront : frontier (interior (A.placementCarrier UPs)) =
              frontier (A.placementCarrier UPs) := by
            rw [frontier, frontier, interior_interior, hreg, hclosed.closure_eq]
          rw [hfront, A.frontier_placementCarrier_compl htiling UPs]
        have hPtFront : frontier Pt.carrier = frontier (A.placementCarrier UPtᶜ) := by
          rw [hPtCarrier]
          have hreg := A.placementCarrier_closure_interior hpack UPt
          have hclosed := A.placementCarrier_isClosed hpack UPt
          have hfront : frontier (interior (A.placementCarrier UPt)) =
              frontier (A.placementCarrier UPt) := by
            rw [frontier, frontier, interior_interior, hreg, hclosed.closure_eq]
          rw [hfront, A.frontier_placementCarrier_compl htiling UPt]
        have hsCcomp : MeasureTheory.AEDisjoint MeasureTheory.volume
            (s +ᵥ K.support) (A.placementCarrier UCᶜ) := by
          have hcomp : {i : A.placements | i.1.1 ∉ S} = UCᶜ := by
            ext i
            rfl
          rw [← hcomp]
          exact placedTile_aedisjoint_complementCarrier_candidate K T S hTiles hST hsS
        have htCcomp : MeasureTheory.AEDisjoint MeasureTheory.volume
            (t' +ᵥ K.support) (A.placementCarrier {i | i.1.1 ∉ T \ S}) :=
          placedTile_aedisjoint_complementCarrier_candidate K T (T \ S) hTiles
            (Set.diff_subset) htNotS
        have hsDcomp := placedTile_aedisjoint_complementCarrier_candidate
          K T Ps.centres hTiles (component_centres_subset_candidate K δ T Ps) hsPs
        have htDcomp := placedTile_aedisjoint_complementCarrier_candidate
          K T Pt.centres hTiles (component_centres_subset_candidate K δ T Pt) htPt
        have hsVertex : p ∈ Tiling.vertexSet (s +ᵥ K.support) := by
          have hdirs : Lp.direction ≠ Ls.direction := by
            rw [hLpDirection, hLsDirection]
            exact hLδ
          have hCline : ∀ᶠ y in 𝓝 p,
              (y ∈ frontier (A.placementCarrier UCᶜ) ↔ y ∈ (Lp : Set Plane)) := by
            filter_upwards [hLpLocal] with y hy
            have hcomp : {i : A.placements | i.1.1 ∉ S} = UCᶜ := by
              ext i
              simp [UC]
            rw [← hcomp, ← hTfront, hy]
          have hDline : ∀ᶠ y in 𝓝 p,
            (y ∈ frontier (A.placementCarrier UPsᶜ) ↔ y ∈ (Ls : Set Plane)) := by
            filter_upwards [hLsLocal'] with y hy
            rw [← hPsFront, hy]
          have hxC : p ∈ frontier (A.placementCarrier UCᶜ) := by
            have hcomp : {i : A.placements | i.1.1 ∉ S} = UCᶜ := by
              ext i
              simp [UC]
            rw [← hcomp, ← hTfront]
            exact hpE
          have hxD : p ∈ frontier (A.placementCarrier UPsᶜ) := by
            rw [← hPsFront]
            exact hpPs
          exact incident_tile_vertex_of_transverse_seams_candidate
            (K.isPolygonal.vadd s) hps
            (A.placementCarrier_closure_interior hpack UCᶜ)
            (A.placementCarrier_closure_interior hpack UPsᶜ)
            hsCcomp hsDcomp
            hxC hxD hpLp hLpdim hCline hpLs hLsDim hDline hdirs
        have htVertex : p ∈ Tiling.vertexSet (t' +ᵥ K.support) := by
          have hdirs : Lp.direction ≠ Lt.direction := by
            rw [hLpDirection, hLtDirection]
            exact hLδ
          have hUeq : {i : A.placements | i.1.1 ∉ T \ S} = UC := by
            ext i
            constructor
            · intro hi
              refine ⟨i.2, ?_⟩
              apply not_not.mp
              intro hiNotS
              exact hi ⟨i.2, fun hiS => hiNotS hiS.2⟩
            · rintro ⟨_, hiS⟩ hiDiff
              exact hiDiff.2 ⟨i.2, hiS⟩
          have hCline : ∀ᶠ y in 𝓝 p,
              (y ∈ frontier (A.placementCarrier {i | i.1.1 ∉ T \ S}) ↔
                y ∈ (Lp : Set Plane)) := by
            filter_upwards [hLpLocal] with y hy
            rw [hUeq, ← hCfront, hy]
          have hDline : ∀ᶠ y in 𝓝 p,
            (y ∈ frontier (A.placementCarrier UPtᶜ) ↔ y ∈ (Lt : Set Plane)) := by
            filter_upwards [hLtLocal'] with y hy
            rw [← hPtFront, hy]
          have hxC : p ∈ frontier (A.placementCarrier {i | i.1.1 ∉ T \ S}) := by
            rw [hUeq, ← hCfront]
            exact hpE
          have hxD : p ∈ frontier (A.placementCarrier UPtᶜ) := by
            rw [← hPtFront]
            exact hpPt
          exact incident_tile_vertex_of_transverse_seams_candidate
            (K.isPolygonal.vadd t') hpt
            (by rw [hUeq]; exact A.placementCarrier_closure_interior hpack UC)
            (A.placementCarrier_closure_interior hpack UPtᶜ)
            htCcomp htDcomp
            hxC hxD hpLp hLpdim hCline hpLt hLtDim hDline hdirs
        have hshared :
            ((s +ᵥ Tiling.vertexSet K.support) ∩
              (t' +ᵥ Tiling.vertexSet K.support)).Nonempty := by
          exact ⟨p, ⟨by simpa only [Tiling.vertexSet_vadd] using hsVertex,
            by simpa only [Tiling.vertexSet_vadd] using htVertex⟩⟩
        have hrel :
            (s ∈ T ∧ t' ∈ T ∧
              ((s +ᵥ Tiling.vertexSet K.support) ∩
                (t' +ᵥ Tiling.vertexSet K.support)).Nonempty) :=
          ⟨hsS.1, htNotS.1, hshared⟩
        have hreach : vertexReach K T t t' := by
          exact (hsS.2.tail hrel)
        exact htNotS.2 ⟨htNotS.1, hreach⟩
      have hrv : r • v ∈ L.direction := by
        rw [hclassDirection]
        exact δ.smul_mem r hvδ
      have hpoint : x + r • v ∈ L := by
        simpa [vadd_eq_add, add_comm] using L.vadd_mem_of_mem_direction hrv hxL
      exact hlineFull hpoint
    simpa [S] using
      invariantAlong_of_frontier_orbit_of_rankOne hEopen hδ hvδ hvne hfrontOrbit

theorem vertex_class_boundary_straight :
  ∀ (K : PolygonalRegion) (T : Set Plane), TilesOn K T Set.univ →
    ∀ t ∈ T, ∀ x ∈ frontier
      (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}),
      BoundaryLocallyStraightAt
        (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}) x
  := by
  intro K T htiles t ht x hx
  let A := K.polygonalProtoTiling T
  let C := A.vertexGraph.connectedComponentMk ⟨(t, ()), ht⟩
  have heq := vertex_class_support K T htiles.2.1 t ht
  change regularSupport K {s | s ∈ T ∧ vertexReach K T t s} = interior (A.plateCarrier C) at heq
  have hclosed := A.plateCarrier_isClosed htiles.2.1 C
  have hregular := A.plateCarrier_closure_interior htiles.2.1 C
  have hfrontier : frontier (interior (A.plateCarrier C)) = frontier (A.plateCarrier C) := by
    rw [frontier, hregular, interior_interior, hclosed.frontier_eq]
  rw [heq, hfrontier] at hx
  have hstraight := A.plateCarrier_boundaryLocallyStraightAt
    ((tilesOn_univ_iff_tiles K T).mp htiles) C hx
  rw [heq]
  simpa only [BoundaryLocallyStraightAt, hfrontier] using hstraight

private theorem prescribed_sliding_direction
    (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane)
    (hδ : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (hcomponents : ∃ P Q : EarthquakeComponent K δ T, P ≠ Q) :
    ∃ v : Plane, v ∈ δ ∧ (K.polygonalProtoTiling T).IsSlidingDirection v := by
  have hδbot : δ ≠ ⊥ := by
    intro heq
    rw [heq, finrank_bot] at hδ
    omega
  obtain ⟨v, hv, hvzero⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hδbot
  refine ⟨v, hv, hvzero, ?_⟩
  intro C r
  obtain ⟨i, hi⟩ := C.nonempty_supp
  have hC : (K.polygonalProtoTiling T).vertexGraph.connectedComponentMk i = C := hi
  have hsupport := vertex_class_support K T htile.2.1 i.1.1 i.2
  have hiunit : i = ⟨(i.1.1, ()), i.2⟩ := by
    apply Subtype.ext
    exact Prod.ext rfl (Subsingleton.elim _ _)
  rw [← hiunit, hC] at hsupport
  have hinv := vertex_class_saturated K δ T hδ htile hcomponents i.1.1 i.2
  have hregular := (K.polygonalProtoTiling T).plateCarrier_closure_interior htile.2.1 C
  rw [AddAction.mem_stabilizer_iff]
  calc
    r • v +ᵥ (K.polygonalProtoTiling T).plateCarrier C =
        r • v +ᵥ closure (regularSupport K {s | s ∈ T ∧ vertexReach K T i.1.1 s}) := by
          rw [hsupport, hregular]
    _ = closure (r • v +ᵥ regularSupport K {s | s ∈ T ∧ vertexReach K T i.1.1 s}) :=
      (closure_vadd _ _).symm
    _ = closure (regularSupport K {s | s ∈ T ∧ vertexReach K T i.1.1 s}) := by
      rw [hinv (r • v) (δ.smul_mem r hv)]
    _ = (K.polygonalProtoTiling T).plateCarrier C := by rw [hsupport, hregular]

theorem vertex_class_contact_alignable :
  ∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Module.finrank ℝ δ = 1 → TilesOn K T Set.univ →
    (∃ P Q : EarthquakeComponent K δ T, P ≠ Q) →
    ∀ t u : Plane, t ∈ T → u ∈ T → ¬vertexReach K T t u →
    (frontier (regularSupport K {s | s ∈ T ∧ vertexReach K T t s}) ∩
      frontier (regularSupport K {s | s ∈ T ∧ vertexReach K T u s})).Nonempty →
    ∃ s q v w : Plane,
      s ∈ T ∧ q ∈ T ∧ vertexReach K T t s ∧ vertexReach K T u q ∧
      v ∈ vertexSet K.support ∧ w ∈ vertexSet K.support ∧ (s + v) - (q + w) ∈ δ
  := by
  intro K δ T hδ htile hcomponents t u ht hu hnot hcontact
  let A := K.polygonalProtoTiling T
  let C := A.vertexGraph.connectedComponentMk ⟨(t, ()), ht⟩
  let D := A.vertexGraph.connectedComponentMk ⟨(u, ()), hu⟩
  have hCD : C ≠ D := by
    intro heq
    apply hnot
    apply vertexReach_of_graphReach K T (i := ⟨(t, ()), ht⟩) (j := ⟨(u, ()), hu⟩)
    exact (A.samePlate_iff_component_eq _ _).mpr heq
  obtain ⟨x, hxC, hxD⟩ := hcontact
  have hsC := vertex_class_support K T htile.2.1 t ht
  have hsD := vertex_class_support K T htile.2.1 u hu
  rw [hsC] at hxC
  rw [hsD] at hxD
  have hxC' : x ∈ A.plateCarrier C := by
    apply (A.plateCarrier_closure_interior htile.2.1 C) ▸ frontier_subset_closure hxC
  have hxD' : x ∈ A.plateCarrier D := by
    apply (A.plateCarrier_closure_interior htile.2.1 D) ▸ frontier_subset_closure hxD
  obtain ⟨vdir, hvdir, hslide⟩ := prescribed_sliding_direction K δ T hδ htile hcomponents
  have hA : IsTiling A.prototiles A.placements := (tilesOn_univ_iff_tiles K T).mp htile
  obtain ⟨i, r, _hr, hir⟩ := A.exists_placedVertex_on_invariant_contact_line hA hslide hCD hxC' hxD'
  obtain ⟨j, p, _hp, hjp⟩ := A.exists_placedVertex_on_invariant_contact_line hA hslide hCD.symm hxD' hxC'
  obtain ⟨v, hv, hvpoint⟩ := Set.mem_vadd_set.mp hir
  obtain ⟨w, hw, hwpoint⟩ := Set.mem_vadd_set.mp hjp
  refine ⟨i.1.1.1, j.1.1.1, v, w, i.1.2, j.1.2, ?_, ?_, hv, hw, ?_⟩
  · apply vertexReach_of_graphReach K T (i := ⟨(t, ()), ht⟩) (j := i.1)
    exact (A.samePlate_iff_component_eq _ _).mpr i.2.symm
  · apply vertexReach_of_graphReach K T (i := ⟨(u, ()), hu⟩) (j := j.1)
    exact (A.samePlate_iff_component_eq _ _).mpr j.2.symm
  · simp only [vadd_eq_add] at hvpoint hwpoint
    rw [hvpoint, hwpoint]
    simpa [sub_smul] using δ.smul_mem (r - p) hvdir

open MeasureTheory in
private theorem shiftedVertex_injective_prescribed
    {K : PolygonalRegion} {T : Set Plane} {v : Plane}
    (hv : (K.polygonalProtoTiling T).IsSlidingDirection v)
    (hT : K.Tiles T)
    (shift : (K.polygonalProtoTiling T).Plate → ℝ) :
    Function.Injective
      ((K.polygonalProtoTiling T).shiftedVertex v shift) := by
  intro i j hij
  let A := K.polygonalProtoTiling T
  let C := A.vertexGraph.connectedComponentMk i
  let D := A.vertexGraph.connectedComponentMk j
  by_cases hCD : C = D
  · exact A.shiftedVertex_injective_of_component_eq v shift hCD hij
  have htileEq :
      placedTile A.prototiles (A.shiftedPlacement v shift i) =
        placedTile A.prototiles (A.shiftedPlacement v shift j) := by
    congr 1
    exact congrArg Subtype.val hij
  have htileNonempty :
      (placedTile A.prototiles (A.shiftedPlacement v shift i)).Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty
    refine ⟨(A.shiftedPlacement v shift i).1 + x, ?_⟩
    change (A.shiftedPlacement v shift i).1 + x ∈
      (A.shiftedPlacement v shift i).1 +ᵥ K.support
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, neg_add_cancel_left] using hx
  have hinterior :
      (interior (placedTile A.prototiles
        (A.shiftedPlacement v shift i))).Nonempty :=
    (A.isPolygonal_placedTile (A.shiftedPlacement v shift i)).interior_nonempty
      htileNonempty
  obtain ⟨x, hx⟩ := hinterior
  have hsubsetC : placedTile A.prototiles (A.shiftedPlacement v shift i) ⊆
      A.plateCarrier C := by
    rw [A.placedTile_shiftedPlacement]
    intro y hy
    rw [← hv.vadd_plateCarrier C (shift C)]
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, A.placedTile_subset_plateCarrier i hz, rfl⟩
  have hsubsetD : placedTile A.prototiles (A.shiftedPlacement v shift i) ⊆
      A.plateCarrier D := by
    rw [htileEq, A.placedTile_shiftedPlacement]
    intro y hy
    rw [← hv.vadd_plateCarrier D (shift D)]
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, A.placedTile_subset_plateCarrier j hz, rfl⟩
  have hxC : x ∈ interior (A.plateCarrier C) := interior_mono hsubsetC hx
  have hxD : x ∈ interior (A.plateCarrier D) := interior_mono hsubsetD hx
  have hpositive : 0 < volume
      (interior (A.plateCarrier C) ∩ interior (A.plateCarrier D)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨x, hxC, hxD⟩
  have hzero : volume
      (interior (A.plateCarrier C) ∩ interior (A.plateCarrier D)) = 0 :=
    measure_mono_null (Set.inter_subset_inter interior_subset interior_subset)
      (A.plateCarrier_aedisjoint hT hCD).eq
  exact (ne_of_gt hpositive hzero).elim

private theorem rational_point_mesh (x : Plane) (hx : IsRationalPoint x) :
    ∃ d : ℕ, 0 < d ∧ ∃ z : IntegerPlane, x = (d : ℝ)⁻¹ • integerPoint z := by
  obtain ⟨a, b, ha, hb⟩ := hx
  refine ⟨a.den * b.den, Nat.mul_pos a.den_pos b.den_pos,
    ![a.num * (b.den : ℤ), b.num * (a.den : ℤ)], ?_⟩
  have ha0 : (a.den : ℝ) ≠ 0 := by exact_mod_cast a.den_pos.ne'
  have hb0 : (b.den : ℝ) ≠ 0 := by exact_mod_cast b.den_pos.ne'
  apply Complex.ext
  · simp only [ha, Complex.smul_re, Tiling.RationalPolygonal.integerPoint_re,
      Fin.isValue, Matrix.cons_val_zero, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
      smul_eq_mul, Rat.cast_def]
    field_simp
  · simp only [hb, Complex.smul_im, Tiling.RationalPolygonal.integerPoint_im,
      Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Int.cast_mul,
      Int.cast_natCast, Nat.cast_mul, smul_eq_mul, Rat.cast_def]
    field_simp

private theorem finite_rational_points_mesh (S : Set Plane) (hS : S.Finite)
    (hRat : ∀ x ∈ S, IsRationalPoint x) :
    ∃ d : ℕ, 0 < d ∧ ∀ x ∈ S, ∃ z : IntegerPlane,
      x = (d : ℝ)⁻¹ • integerPoint z := by
  classical
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x S hx hS ih =>
      obtain ⟨d, hd, hmesh⟩ := ih (fun y hy => hRat y (Set.mem_insert_of_mem x hy))
      obtain ⟨n, hn, z, hz⟩ := rational_point_mesh x (hRat x (Set.mem_insert x S))
      have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      refine ⟨d * n, Nat.mul_pos hd hn, ?_⟩
      intro y hy
      rcases Set.mem_insert_iff.mp hy with rfl | hy
      · refine ⟨d • z, ?_⟩
        rw [hz]
        have hp : integerPoint (d • z) = (d : ℝ) • integerPoint z := by
          simpa using map_nsmul Tiling.RationalPolygonal.integerPointHom d z
        rw [hp, smul_smul]
        congr 1
        push_cast
        field_simp
      · obtain ⟨q, hq⟩ := hmesh y hy
        refine ⟨n • q, ?_⟩
        rw [hq]
        have hp : integerPoint (n • q) = (n : ℝ) • integerPoint q := by
          simpa using map_nsmul Tiling.RationalPolygonal.integerPointHom n q
        rw [hp, smul_smul]
        congr 1
        push_cast
        field_simp

private def gridLinearEquiv (h k : ℝ) (hh : 0 < h) (hk : 0 < k) : Plane ≃L[ℝ] Plane where
  toFun x := ⟨h * x.re, k * x.im⟩
  invFun x := ⟨x.re / h, x.im / k⟩
  left_inv x := by
    apply Complex.ext <;> dsimp <;> field_simp
  right_inv x := by
    apply Complex.ext <;> dsimp <;> field_simp
  map_add' x y := by
    apply Complex.ext <;> simp <;> ring
  map_smul' r x := by
    apply Complex.ext <;> simp <;> ring
  continuous_toFun := by
    change Continuous (fun x : Plane => Complex.equivRealProdCLM.symm (h * x.re, k * x.im))
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((continuous_const.mul Complex.continuous_re).prodMk
        (continuous_const.mul Complex.continuous_im))
  continuous_invFun := by
    change Continuous (fun x : Plane => Complex.equivRealProdCLM.symm (x.re / h, x.im / k))
    exact Complex.equivRealProdCLM.symm.continuous.comp
      ((Complex.continuous_re.div_const h).prodMk (Complex.continuous_im.div_const k))

private theorem gridLinearEquiv_symm_apply (h k : ℝ) (hh : 0 < h) (hk : 0 < k) (x : Plane) :
    (gridLinearEquiv h k hh hk).symm x = ⟨x.re / h, x.im / k⟩ := rfl

private theorem gridLinearEquiv_integerPoint (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (z : IntegerPlane) : gridLinearEquiv h k hh hk (integerPoint z) = gridPoint h k z := by
  apply Complex.ext <;> simp [gridLinearEquiv, gridPoint]

private theorem gridLinearEquiv_gridCell (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (z : IntegerPlane) : gridLinearEquiv h k hh hk '' gridCell 1 1 z = gridCell h k z := by
  let B := gridLinearEquiv h k hh hk
  apply Set.Subset.antisymm
  · rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨hy1, hy2, hy3, hy4⟩
    change h * (z 0 : ℝ) ≤ h * y.re ∧ h * y.re ≤ h * ((z 0 : ℝ) + 1) ∧
      k * (z 1 : ℝ) ≤ k * y.im ∧ k * y.im ≤ k * ((z 1 : ℝ) + 1)
    simp only [one_mul] at hy1 hy2 hy3 hy4
    exact ⟨mul_le_mul_of_nonneg_left hy1 hh.le, mul_le_mul_of_nonneg_left hy2 hh.le,
      mul_le_mul_of_nonneg_left hy3 hk.le, mul_le_mul_of_nonneg_left hy4 hk.le⟩
  · intro x hx
    refine ⟨B.symm x, ?_, B.apply_symm_apply x⟩
    rcases hx with ⟨hx1, hx2, hx3, hx4⟩
    rw [gridLinearEquiv_symm_apply]
    change 1 * (z 0 : ℝ) ≤ x.re / h ∧ x.re / h ≤ 1 * ((z 0 : ℝ) + 1) ∧
      1 * (z 1 : ℝ) ≤ x.im / k ∧ x.im / k ≤ 1 * ((z 1 : ℝ) + 1)
    simp only [one_mul]
    exact ⟨(le_div_iff₀ hh).mpr (by nlinarith), (div_le_iff₀ hh).mpr (by nlinarith),
      (le_div_iff₀ hk).mpr (by nlinarith), (div_le_iff₀ hk).mpr (by nlinarith)⟩

private theorem gridLinearEquiv_cellSupport (h k : ℝ) (hh : 0 < h) (hk : 0 < k)
    (F : Finset IntegerPlane) : gridLinearEquiv h k hh hk '' cellSupport 1 1 F = cellSupport h k F := by
  simp only [cellSupport, Set.image_iUnion, gridLinearEquiv_gridCell]

private theorem gridLinearEquiv_direction (h k : ℝ) (hh : 0 < h) (hk : 0 < k) :
    verticalDirection.map (gridLinearEquiv h k hh hk).toLinearMap = verticalDirection := by
  ext x
  constructor
  · rintro ⟨y, hy, hyx⟩
    apply (mem_verticalDirection_iff x).mpr
    rw [← hyx]
    simp [gridLinearEquiv, (mem_verticalDirection_iff y).mp hy]
  · intro hx
    let B := gridLinearEquiv h k hh hk
    refine Submodule.mem_map.mpr ⟨B.symm x, ?_, B.apply_symm_apply x⟩
    apply (mem_verticalDirection_iff _).mpr
    rw [gridLinearEquiv_symm_apply]
    simp [(mem_verticalDirection_iff x).mp hx]

private theorem placedOpen_linearImage (K : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (s : Plane) :
    B s +ᵥ (affineImage K B 0).openCarrier = B '' (s +ᵥ K.openCarrier) := by
  rw [affineImage_openCarrier]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨z, hz, rfl⟩ := hy
    refine ⟨s + z, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩, ?_⟩
    simp [affineMap, map_add]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := Set.mem_vadd_set.mp hy
    refine Set.mem_vadd_set.mpr ⟨B z, ⟨z, hz, by simp [affineMap]⟩, ?_⟩
    simp [map_add]

private theorem openUnion_linearImage (K : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (S : Set Plane) :
    openUnion (affineImage K B 0) (B '' S) = B '' openUnion K S := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hsx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨t, ht, hts⟩ := s.2
    change x ∈ s.1 +ᵥ (affineImage K B 0).openCarrier at hsx
    rw [← hts, placedOpen_linearImage] at hsx
    obtain ⟨y, hy, hxy⟩ := hsx
    exact ⟨y, Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hy⟩, hxy⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, hyt⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨⟨B t.1, ⟨t.1, t.2, rfl⟩⟩, ?_⟩
    change B y ∈ B t.1 +ᵥ (affineImage K B 0).openCarrier
    rw [placedOpen_linearImage]
    exact ⟨y, hyt, rfl⟩

private theorem regularSupport_linearImage (K : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (S : Set Plane) :
    regularSupport (affineImage K B 0) (B '' S) = B '' regularSupport K S := by
  unfold regularSupport
  rw [openUnion_linearImage]
  change interior (closure (B.toHomeomorph '' openUnion K S)) =
    B.toHomeomorph '' interior (closure (openUnion K S))
  rw [← B.toHomeomorph.image_closure, ← B.toHomeomorph.image_interior]

private theorem directionalOverlap_linearImage (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (s t : Plane) :
    DirectionalOverlap (affineImage K B 0) (δ.map B.toLinearMap) (B s) (B t) ↔
      DirectionalOverlap K δ s t := by
  unfold DirectionalOverlap
  rw [placedOpen_linearImage, placedOpen_linearImage]
  constructor
  · rintro ⟨x, ⟨p, hp, hpx⟩, y, ⟨q, hq, hqy⟩, hxy⟩
    obtain ⟨w, hw, hwxy⟩ := Submodule.mem_map.mp hxy
    have hw' : w = p - q := by
      apply B.injective
      simpa [map_sub, hpx, hqy] using hwxy
    exact ⟨p, hp, q, hq, hw' ▸ hw⟩
  · rintro ⟨p, hp, q, hq, hpq⟩
    refine ⟨B p, ⟨p, hp, rfl⟩, B q, ⟨q, hq, rfl⟩, ?_⟩
    exact Submodule.mem_map.mpr ⟨p - q, hpq, by simp⟩

private def linearCentreEquiv (B : Plane ≃L[ℝ] Plane) (T : Set Plane) : T ≃ (B '' T) where
  toFun t := ⟨B t.1, ⟨t.1, t.2, rfl⟩⟩
  invFun u := ⟨B.symm u.1, by
    obtain ⟨t, ht, htu⟩ := u.2
    simpa [← htu] using ht⟩
  left_inv t := Subtype.ext (B.symm_apply_apply t.1)
  right_inv u := Subtype.ext (B.apply_symm_apply u.1)

private def linearEarthquakeGraphIso (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) :
    earthquakeGraph K δ T ≃g earthquakeGraph (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) where
  toEquiv := linearCentreEquiv B T
  map_rel_iff' := by
    intro s t
    simp only [earthquakeGraph, SimpleGraph.fromRel_adj]
    rw [(linearCentreEquiv B T).injective.ne_iff]
    simp only [linearCentreEquiv, Equiv.coe_fn_mk, directionalOverlap_linearImage]

private theorem linear_component_centres (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) (P : EarthquakeComponent K δ T) :
    EarthquakeComponent.centres ((linearEarthquakeGraphIso K δ B T).connectedComponentEquiv P) = B '' P.centres := by
  refine P.ind ?_
  intro a
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    let e := linearCentreEquiv B T
    let t := e.symm u
    have htu : e t = u := e.apply_symm_apply u
    have hreach := SimpleGraph.ConnectedComponent.eq.mp hu
    have hreach' : (earthquakeGraph K δ T).Reachable t a := by
      apply (linearEarthquakeGraphIso K δ B T).reachable_iff.mp
      change (earthquakeGraph (affineImage K B 0) (δ.map B.toLinearMap) (B '' T)).Reachable (e t) (e a)
      rw [htu]
      exact hreach
    refine ⟨t.1, ⟨t, SimpleGraph.ConnectedComponent.eq.mpr hreach', rfl⟩, ?_⟩
    exact congrArg Subtype.val htu
  · rintro ⟨t, ⟨u, hu, hut⟩, rfl⟩
    have hreach := SimpleGraph.ConnectedComponent.eq.mp hu
    have hreach' := (linearEarthquakeGraphIso K δ B T).reachable_iff.mpr hreach
    refine ⟨linearCentreEquiv B T u, SimpleGraph.ConnectedComponent.eq.mpr hreach', ?_⟩
    exact congrArg B hut

private theorem component_column_iff_lineSupported (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (hdim : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T) : IsCenterColumn K δ P.centres ↔ IsLineSupported P.centres δ := by
  have hsub : P.centres ⊆ T := by rintro _ ⟨t, ht, rfl⟩; exact t.2
  have hp : IsPacking K.prototileFamily (K.placements P.centres) :=
    htile.2.1.mono (fun _ hs => hsub hs)
  obtain ⟨t, ht⟩ := P.nonempty_supp
  have hne : P.centres.Nonempty := ⟨t.1, ⟨t, ht, rfl⟩⟩
  have hreg : regularSupport K T = Set.univ := regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hinv := component_isInvariant K δ T hdim htile.2.1 (by rw [hreg]; intro v hv; simp) P
  exact ⟨fun hc => hc.2.2.1, fun hl => ⟨hp, hne, hl, hinv⟩⟩

private theorem lineSupported_linearImage (S : Set Plane) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) :
    IsLineSupported (B '' S) (δ.map B.toLinearMap) ↔ IsLineSupported S δ := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨B.symm q, ?_⟩
    intro s hs
    obtain ⟨z, hz, hzs⟩ := Submodule.mem_map.mp (hq (B s) ⟨s, hs, rfl⟩)
    have heq : z = s - B.symm q := by
      apply B.injective
      simpa using hzs
    exact heq ▸ hz
  · rintro ⟨q, hq⟩
    refine ⟨B q, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact Submodule.mem_map.mpr ⟨s - q, hq s hs, by simp⟩

private theorem linear_tiles (K : PolygonalRegion) (B : Plane ≃L[ℝ] Plane) (T : Set Plane)
    (hK : TilesOn K T Set.univ) : TilesOn (affineImage K B 0) (B '' T) Set.univ := by
  have ht := (tilesOn_affineImage_iff K B 0 T Set.univ).mpr hK
  have hsurj : Function.Surjective (affineMap B 0) := fun x => ⟨B.symm x, by simp [affineMap]⟩
  rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at ht

private theorem linear_component_column (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (P : EarthquakeComponent K δ T) :
    IsCenterColumn (affineImage K B 0) (δ.map B.toLinearMap)
      (EarthquakeComponent.centres ((linearEarthquakeGraphIso K δ B T).connectedComponentEquiv P)) ↔
      IsCenterColumn K δ P.centres := by
  have hdim' : Module.finrank ℝ (δ.map B.toLinearMap) = 1 := by
    rw [LinearEquiv.finrank_map_eq B.toLinearEquiv δ, hdim]
  rw [component_column_iff_lineSupported _ _ _ hdim' (linear_tiles K B T htile),
    linear_component_centres, lineSupported_linearImage,
    component_column_iff_lineSupported K δ T hdim htile]

private theorem linear_columnPart (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) :
    columnPart (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) = B '' columnPart K δ T := by
  let e := (linearEarthquakeGraphIso K δ B T).connectedComponentEquiv
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let P : EarthquakeComponent K δ T := e.symm Q.1
    have hcentre : B '' P.centres = Q.1.centres := by
      rw [← linear_component_centres K δ B T P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q.1)
    have hPcol : IsCenterColumn K δ P.centres := by
      apply (linear_component_column K δ B T hdim htile P).mp
      change IsCenterColumn (affineImage K B 0) (δ.map B.toLinearMap)
        (EarthquakeComponent.centres (e P))
      rw [show e P = Q.1 from e.apply_symm_apply Q.1]
      exact Q.2
    obtain ⟨s, hs, hBs⟩ := hcentre.symm ▸ hxQ
    exact ⟨s, Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, hs⟩, hBs⟩
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨P, hsP⟩ := Set.mem_iUnion.mp hs
    have hQcol := (linear_component_column K δ B T hdim htile P.1).mpr P.2
    refine Set.mem_iUnion.mpr ⟨⟨e P.1, hQcol⟩, ?_⟩
    rw [linear_component_centres]
    exact ⟨s, hsP, rfl⟩

private theorem linear_period_pullback (B : Plane ≃L[ℝ] Plane) (E : Set Plane)
    (v : Plane) (hv : v ∈ periodGroup (B '' E)) : B.symm v ∈ periodGroup E := by
  have hpg : periodGroup (B '' E) =
      (periodGroup E).map B.toLinearEquiv.toAddEquiv.toAddMonoidHom := by
    have hf : affineMap B 0 = (B : Plane → Plane) := by funext x; simp [affineMap]
    simpa only [hf] using periodGroup_affineImage B 0 E
  rw [hpg] at hv
  obtain ⟨w, hw, hBwv⟩ := hv
  have heq : B.symm v = w := by rw [← hBwv]; simp
  exact heq ▸ hw

private theorem commonCarrierPeriod_linearPullback (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (v : Plane)
    (hv : IsCommonCarrierPeriod (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) v) :
    IsCommonCarrierPeriod K δ T (B.symm v) := by
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    exact hvδ (Submodule.mem_map.mpr ⟨B.symm v, hmem, B.apply_symm_apply v⟩)
  · rw [linear_columnPart K δ B T hdim htile, regularSupport_linearImage] at hvcol
    exact linear_period_pullback B _ v hvcol
  · intro P hP
    let Q : EarthquakeComponent (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) :=
      (linearEarthquakeGraphIso K δ B T).connectedComponentEquiv P
    have hQ : Q ∈ noncolumnComponents (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) := by
      intro hcol
      exact hP ((linear_component_column K δ B T hdim htile P).mp hcol)
    have hvQ := hvnon Q hQ
    change v ∈ periodGroup (regularSupport (affineImage K B 0) Q.centres) at hvQ
    rw [linear_component_centres, regularSupport_linearImage] at hvQ
    exact linear_period_pullback B P.carrier v hvQ

private theorem linear_period_pushforward (B : Plane ≃L[ℝ] Plane) (E : Set Plane)
    (v : Plane) (hv : v ∈ periodGroup E) : B v ∈ periodGroup (B '' E) := by
  have hf : affineMap B 0 = (B : Plane → Plane) := by funext x; simp [affineMap]
  have hpg := periodGroup_affineImage B 0 E
  rw [hf] at hpg
  rw [hpg]
  exact ⟨v, hv, rfl⟩

private theorem commonCarrierPeriod_linearPushforward (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (B : Plane ≃L[ℝ] Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (v : Plane) (hv : IsCommonCarrierPeriod K δ T v) :
    IsCommonCarrierPeriod (affineImage K B 0) (δ.map B.toLinearMap) (B '' T) (B v) := by
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp hmem
    exact hvδ (B.injective hwv ▸ hw)
  · rw [linear_columnPart K δ B T hdim htile, regularSupport_linearImage]
    exact linear_period_pushforward B _ v hvcol
  · intro Q hQ
    let e := (linearEarthquakeGraphIso K δ B T).connectedComponentEquiv
    let P : EarthquakeComponent K δ T := e.symm Q
    have hP : P ∈ noncolumnComponents K δ T := by
      intro hcol
      apply hQ
      have hc := (linear_component_column K δ B T hdim htile P).mpr hcol
      change IsCenterColumn (affineImage K B 0) (δ.map B.toLinearMap)
        (EarthquakeComponent.centres (e P)) at hc
      rwa [e.apply_symm_apply] at hc
    have hc : Q.centres = B '' P.centres := by
      rw [← linear_component_centres K δ B T P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q).symm
    change B v ∈ periodGroup (regularSupport (affineImage K B 0) Q.centres)
    rw [hc, regularSupport_linearImage]
    exact linear_period_pushforward B P.carrier v (hvnon P hP)

private def footprintEarthquakeGraphIso (K R : PolygonalRegion) (T : Set Plane)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier) :
    earthquakeGraph K verticalDirection T ≃g earthquakeGraph R verticalDirection T where
  toEquiv := Equiv.refl T
  map_rel_iff' := by
    intro s t
    simp only [earthquakeGraph, SimpleGraph.fromRel_adj, Equiv.refl_apply,
      directionalOverlap_iff_footprint, hQ]

private theorem footprint_component_centres (K R : PolygonalRegion) (T : Set Plane)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier)
    (P : EarthquakeComponent K verticalDirection T) :
    EarthquakeComponent.centres ((footprintEarthquakeGraphIso K R T hQ).connectedComponentEquiv P) = P.centres := by
  refine P.ind ?_
  intro a
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hr := SimpleGraph.ConnectedComponent.eq.mp hy
    have hr' := (footprintEarthquakeGraphIso K R T hQ).reachable_iff.mp hr
    exact ⟨y, SimpleGraph.ConnectedComponent.eq.mpr hr', rfl⟩
  · rintro ⟨y, hy, rfl⟩
    have hr := SimpleGraph.ConnectedComponent.eq.mp hy
    have hr' := (footprintEarthquakeGraphIso K R T hQ).reachable_iff.mpr hr
    exact ⟨y, SimpleGraph.ConnectedComponent.eq.mpr hr', rfl⟩

private theorem footprint_component_column (K R : PolygonalRegion) (T : Set Plane)
    (hK : TilesOn K T Set.univ) (hR : TilesOn R T Set.univ)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier)
    (P : EarthquakeComponent K verticalDirection T) :
    IsCenterColumn R verticalDirection
      (EarthquakeComponent.centres ((footprintEarthquakeGraphIso K R T hQ).connectedComponentEquiv P)) ↔
      IsCenterColumn K verticalDirection P.centres := by
  have hd : Module.finrank ℝ verticalDirection = 1 := finrank_span_singleton Complex.I_ne_zero
  rw [component_column_iff_lineSupported _ _ _ hd hR, footprint_component_centres,
    component_column_iff_lineSupported K verticalDirection T hd hK]

private theorem footprint_columnPart (K R : PolygonalRegion) (T : Set Plane)
    (hK : TilesOn K T Set.univ) (hR : TilesOn R T Set.univ)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier) :
    columnPart R verticalDirection T = columnPart K verticalDirection T := by
  let e := (footprintEarthquakeGraphIso K R T hQ).connectedComponentEquiv
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let P : EarthquakeComponent K verticalDirection T := e.symm Q.1
    have hc : P.centres = Q.1.centres := by
      rw [← footprint_component_centres K R T hQ P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q.1)
    have hPcol : IsCenterColumn K verticalDirection P.centres := by
      apply (footprint_component_column K R T hK hR hQ P).mp
      change IsCenterColumn R verticalDirection (EarthquakeComponent.centres (e P))
      rw [show e P = Q.1 from e.apply_symm_apply Q.1]
      exact Q.2
    exact Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, hc.symm ▸ hxQ⟩
  · intro hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    have hQcol := (footprint_component_column K R T hK hR hQ P.1).mpr P.2
    refine Set.mem_iUnion.mpr ⟨⟨e P.1, hQcol⟩, ?_⟩
    rw [footprint_component_centres]
    exact hxP

private theorem columnPart_invariant (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane) :
    IsInvariantAlong (regularSupport K (columnPart K δ T)) δ := by
  unfold columnPart
  rw [regularSupport_iUnion]
  intro v hv
  rw [← interior_vadd, ← closure_vadd, Set.vadd_set_iUnion]
  apply congrArg interior
  apply congrArg closure
  congr 1
  funext (P : {P : EarthquakeComponent K δ T // IsCenterColumn K δ P.centres})
  exact P.2.2.2.2 v hv

private theorem commonCarrierPeriod_footprintTransfer (K R : PolygonalRegion) (T : Set Plane)
    (hK : TilesOn K T Set.univ) (hR : TilesOn R T Set.univ)
    (hQ : regularizedProjection K.openCarrier = regularizedProjection R.openCarrier)
    (v : Plane) (hv : IsCommonCarrierPeriod R verticalDirection T v) :
    IsCommonCarrierPeriod K verticalDirection T v := by
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  have hdim : Module.finrank ℝ verticalDirection = 1 := finrank_span_singleton Complex.I_ne_zero
  have hreg : regularSupport K T = Set.univ := regularSupport_eq_of_tilesOn isOpen_univ (by simp) hK
  refine ⟨hvδ, ?_, ?_⟩
  · have hsub : columnPart K verticalDirection T ⊆ T := by
      intro x hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      obtain ⟨t, ht, rfl⟩ := hxP
      exact t.2
    rw [footprint_columnPart K R T hK hR hQ] at hvcol
    rw [saturated_subfamily_carrier_eq K R T _ hK hR hsub hQ (columnPart_invariant K _ T)]
    exact hvcol
  · intro P hP
    let Q : EarthquakeComponent R verticalDirection T :=
      (footprintEarthquakeGraphIso K R T hQ).connectedComponentEquiv P
    have hQnot : Q ∈ noncolumnComponents R verticalDirection T := by
      intro hc
      exact hP ((footprint_component_column K R T hK hR hQ P).mp hc)
    have hvP := hvnon Q hQnot
    have hsub : P.centres ⊆ T := by rintro _ ⟨t, ht, rfl⟩; exact t.2
    have hinv := component_isInvariant K verticalDirection T hdim hK.2.1
      (by rw [hreg]; intro z hz; simp) P
    change v ∈ periodGroup (regularSupport R Q.centres) at hvP
    rw [footprint_component_centres] at hvP
    change v ∈ periodGroup (regularSupport K P.centres)
    rwa [saturated_subfamily_carrier_eq K R T _ hK hR hsub hQ hinv]

private theorem affineImage_refl_support (K : PolygonalRegion) (v : Plane) :
    (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v).support = v +ᵥ K.support := by
  ext x
  simp [affineImage, affineMap, Set.mem_vadd_set]

private theorem affineImage_refl_openCarrier (K : PolygonalRegion) (v : Plane) :
    (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v).openCarrier = v +ᵥ K.openCarrier := by
  change interior _ = v +ᵥ interior K.support
  rw [affineImage_refl_support, interior_vadd]

private theorem affineImage_refl_vertices (K : PolygonalRegion) (v : Plane) :
    vertexSet (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v).support =
      v +ᵥ vertexSet K.support := by
  rw [vertexSet_affineImage]
  ext x
  simp [affineMap, Set.mem_vadd_set]

private theorem affineImage_refl_tiles (K : PolygonalRegion) (v : Plane) (T : Set Plane)
    (hK : TilesOn K T Set.univ) :
    TilesOn (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v) T Set.univ := by
  have ht := (tilesOn_affineImage_iff K (ContinuousLinearEquiv.refl ℝ Plane) v T Set.univ).mpr hK
  have hsurj : Function.Surjective (affineMap (ContinuousLinearEquiv.refl ℝ Plane) v) := by
    intro x
    exact ⟨x - v, by simp [affineMap, sub_eq_add_neg]⟩
  rw [Set.image_univ, Set.range_eq_univ.mpr hsurj] at ht
  simpa using ht

private theorem affineImage_refl_relativelyRational (K : PolygonalRegion) (v : Plane)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K) :
    Tiling.RationalPolygonal.IsRelativelyRational
      (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v) := by
  obtain ⟨a, ha, hr⟩ := hK
  refine ⟨v + a, ?_, ?_⟩
  · rw [affineImage_refl_vertices]
    exact Set.mem_vadd_set.mpr ⟨a, ha, rfl⟩
  · intro w hw
    rw [affineImage_refl_vertices] at hw
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.mp hw
    simpa using hr b hb

private theorem openUnion_tileTranslation (K : PolygonalRegion) (a : Plane) (S : Set Plane) :
    openUnion (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) S = a +ᵥ openUnion K S := by
  unfold openUnion
  rw [Set.vadd_set_iUnion]
  congr 1
  funext t
  rw [affineImage_refl_openCarrier]
  simp only [vadd_vadd, add_comm]

private theorem regularSupport_tileTranslation (K : PolygonalRegion) (a : Plane) (S : Set Plane) :
    regularSupport (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) S =
      a +ᵥ regularSupport K S := by
  unfold regularSupport
  rw [openUnion_tileTranslation, closure_vadd, interior_vadd]

private theorem overlap_tileTranslation (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (s t : Plane) :
    DirectionalOverlap (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ s t ↔
      DirectionalOverlap K δ s t := by
  unfold DirectionalOverlap
  rw [affineImage_refl_openCarrier]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy
    obtain ⟨r, hr, hrp⟩ := Set.mem_vadd_set.mp hp
    obtain ⟨z, hz, hzq⟩ := Set.mem_vadd_set.mp hq
    refine ⟨s + r, Set.mem_vadd_set.mpr ⟨r, hr, rfl⟩,
      t + z, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩, ?_⟩
    convert hxy using 1
    simp only [vadd_eq_add] at hpx hqy hrp hzq
    rw [← hpx, ← hqy, ← hrp, ← hzq]
    abel
  · rintro ⟨p, hp, q, hq, hpq⟩
    obtain ⟨r, hr, hrp⟩ := Set.mem_vadd_set.mp hp
    obtain ⟨z, hz, hzq⟩ := Set.mem_vadd_set.mp hq
    refine ⟨a + p, ?_, a + q, ?_, ?_⟩
    · apply Set.mem_vadd_set.mpr
      refine ⟨a + r, Set.mem_vadd_set.mpr ⟨r, hr, rfl⟩, ?_⟩
      simp only [vadd_eq_add] at hrp ⊢
      rw [← hrp]
      abel
    · apply Set.mem_vadd_set.mpr
      refine ⟨a + z, Set.mem_vadd_set.mpr ⟨z, hz, rfl⟩, ?_⟩
      simp only [vadd_eq_add] at hzq ⊢
      rw [← hzq]
      abel
    · simpa only [add_sub_add_left_eq_sub] using hpq

private def tileTranslationGraphIso (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (T : Set Plane) :
    earthquakeGraph K δ T ≃g
      earthquakeGraph (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ T where
  toEquiv := Equiv.refl T
  map_rel_iff' := by
    intro s t
    simp only [earthquakeGraph, SimpleGraph.fromRel_adj, Equiv.refl_apply,
      overlap_tileTranslation]

private theorem tileTranslation_component_centres (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (T : Set Plane) (P : EarthquakeComponent K δ T) :
    EarthquakeComponent.centres ((tileTranslationGraphIso K a δ T).connectedComponentEquiv P) =
      P.centres := by
  refine P.ind ?_
  intro b
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, SimpleGraph.ConnectedComponent.eq.mpr
      ((tileTranslationGraphIso K a δ T).reachable_iff.mp
        (SimpleGraph.ConnectedComponent.eq.mp hy)), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, SimpleGraph.ConnectedComponent.eq.mpr
      ((tileTranslationGraphIso K a δ T).reachable_iff.mpr
        (SimpleGraph.ConnectedComponent.eq.mp hy)), rfl⟩

private theorem tileTranslation_component_column (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (P : EarthquakeComponent K δ T) :
    IsCenterColumn (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ
      (EarthquakeComponent.centres ((tileTranslationGraphIso K a δ T).connectedComponentEquiv P)) ↔
      IsCenterColumn K δ P.centres := by
  rw [component_column_iff_lineSupported _ _ _ hdim (affineImage_refl_tiles K a T htile),
    tileTranslation_component_centres, component_column_iff_lineSupported K δ T hdim htile]

private theorem tileTranslation_columnPart (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) :
    columnPart (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ T = columnPart K δ T := by
  let e := (tileTranslationGraphIso K a δ T).connectedComponentEquiv
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let P : EarthquakeComponent K δ T := e.symm Q.1
    have hc : P.centres = Q.1.centres := by
      rw [← tileTranslation_component_centres K a δ T P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q.1)
    have hP : IsCenterColumn K δ P.centres := by
      apply (tileTranslation_component_column K a δ T hdim htile P).mp
      change IsCenterColumn _ δ (EarthquakeComponent.centres (e P))
      rw [show e P = Q.1 from e.apply_symm_apply Q.1]
      exact Q.2
    exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hc.symm ▸ hxQ⟩
  · intro hx
    obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨⟨e P.1,
      (tileTranslation_component_column K a δ T hdim htile P.1).mpr P.2⟩, ?_⟩
    rw [tileTranslation_component_centres]
    exact hxP

private theorem periodGroup_tileTranslation (a : Plane) (E : Set Plane) :
    periodGroup (a +ᵥ E) = periodGroup E := by
  have h := periodGroup_affineImage (ContinuousLinearEquiv.refl ℝ Plane) a E
  have he : affineMap (ContinuousLinearEquiv.refl ℝ Plane) a '' E = a +ᵥ E := by
    ext x
    simp [affineMap, Set.mem_vadd_set]
  rw [he] at h
  have hid : (ContinuousLinearEquiv.refl ℝ Plane).toLinearEquiv.toAddEquiv.toAddMonoidHom =
      AddMonoidHom.id Plane := rfl
  rwa [hid, AddSubgroup.map_id] at h

private theorem commonCarrierPeriod_tileTranslation (K : PolygonalRegion) (a : Plane)
    (δ : Submodule ℝ Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (v : Plane)
    (hv : IsCommonCarrierPeriod (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ T v) :
    IsCommonCarrierPeriod K δ T v := by
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  refine ⟨hvδ, ?_, ?_⟩
  · rwa [tileTranslation_columnPart K a δ T hdim htile,
      regularSupport_tileTranslation, periodGroup_tileTranslation] at hvcol
  · intro P hP
    let Q : EarthquakeComponent (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) a) δ T :=
      (tileTranslationGraphIso K a δ T).connectedComponentEquiv P
    have hQ : Q ∈ noncolumnComponents _ δ T := by
      intro hcol
      exact hP ((tileTranslation_component_column K a δ T hdim htile P).mp hcol)
    have hvQ := hvnon Q hQ
    change v ∈ periodGroup (regularSupport _ (EarthquakeComponent.centres
      ((tileTranslationGraphIso K a δ T).connectedComponentEquiv P))) at hvQ
    rwa [tileTranslation_component_centres, regularSupport_tileTranslation,
      periodGroup_tileTranslation] at hvQ

private theorem overlap_centreTranslation (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a s t : Plane) : DirectionalOverlap K δ (a + s) (a + t) ↔ DirectionalOverlap K δ s t := by
  unfold DirectionalOverlap
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy
    refine ⟨s + p, Set.mem_vadd_set.mpr ⟨p, hp, rfl⟩,
      t + q, Set.mem_vadd_set.mpr ⟨q, hq, rfl⟩, ?_⟩
    convert hxy using 1
    simp only [vadd_eq_add] at hpx hqy
    rw [← hpx, ← hqy]
    abel
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine ⟨a + x, ?_, a + y, ?_, by simpa only [add_sub_add_left_eq_sub] using hxy⟩
    · obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hx
      refine Set.mem_vadd_set.mpr ⟨p, hp, ?_⟩
      simp only [vadd_eq_add] at hpx ⊢
      rw [← hpx]
      abel
    · obtain ⟨p, hp, hpy⟩ := Set.mem_vadd_set.mp hy
      refine Set.mem_vadd_set.mpr ⟨p, hp, ?_⟩
      simp only [vadd_eq_add] at hpy ⊢
      rw [← hpy]
      abel

private def centreTranslationEquiv (a : Plane) (T : Set Plane) : T ≃ (a +ᵥ T) where
  toFun t := ⟨a + t.1, Set.mem_vadd_set.mpr ⟨t.1, t.2, rfl⟩⟩
  invFun u := ⟨-a + u.1, by simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using u.2⟩
  left_inv t := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)

private def centreTranslationGraphIso (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a : Plane) (T : Set Plane) : earthquakeGraph K δ T ≃g earthquakeGraph K δ (a +ᵥ T) where
  toEquiv := centreTranslationEquiv a T
  map_rel_iff' := by
    intro s t
    simp only [earthquakeGraph, SimpleGraph.fromRel_adj]
    rw [(centreTranslationEquiv a T).injective.ne_iff]
    simp only [centreTranslationEquiv, Equiv.coe_fn_mk, overlap_centreTranslation]

private theorem centreTranslation_component_centres (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a : Plane) (T : Set Plane) (P : EarthquakeComponent K δ T) :
    EarthquakeComponent.centres ((centreTranslationGraphIso K δ a T).connectedComponentEquiv P) =
      a +ᵥ P.centres := by
  refine P.ind ?_
  intro b
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    let e := centreTranslationEquiv a T
    let t := e.symm u
    have htu : e t = u := e.apply_symm_apply u
    have hreach : (earthquakeGraph K δ T).Reachable t b := by
      apply (centreTranslationGraphIso K δ a T).reachable_iff.mp
      change (earthquakeGraph K δ (a +ᵥ T)).Reachable (e t) (e b)
      rw [htu]
      exact SimpleGraph.ConnectedComponent.eq.mp hu
    refine Set.mem_vadd_set.mpr ⟨t.1, ⟨t, SimpleGraph.ConnectedComponent.eq.mpr hreach, rfl⟩, ?_⟩
    exact congrArg Subtype.val htu
  · intro hx
    obtain ⟨x, ⟨t, ht, htx⟩, rfl⟩ := Set.mem_vadd_set.mp hx
    refine ⟨centreTranslationEquiv a T t,
      SimpleGraph.ConnectedComponent.eq.mpr ((centreTranslationGraphIso K δ a T).reachable_iff.mpr
        (SimpleGraph.ConnectedComponent.eq.mp ht)), ?_⟩
    change a + t.1 = a + x
    rw [htx]

private theorem lineSupported_centreTranslation (δ : Submodule ℝ Plane) (a : Plane) (S : Set Plane) :
    IsLineSupported (a +ᵥ S) δ ↔ IsLineSupported S δ := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b - a, ?_⟩
    intro s hs
    have h := hb (a + s) (Set.mem_vadd_set.mpr ⟨s, hs, rfl⟩)
    convert h using 1
    abel
  · rintro ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Set.mem_vadd_set.mp hx
    simpa only [vadd_eq_add, add_sub_add_left_eq_sub] using hb s hs

private theorem centreTranslation_tiles (K : PolygonalRegion) (a : Plane) (T : Set Plane)
    (htile : TilesOn K T Set.univ) : TilesOn K (a +ᵥ T) Set.univ := by
  simpa using tilesOn_translate htile a

private theorem centreTranslation_component_column (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a : Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (P : EarthquakeComponent K δ T) :
    IsCenterColumn K δ (EarthquakeComponent.centres
      ((centreTranslationGraphIso K δ a T).connectedComponentEquiv P)) ↔
      IsCenterColumn K δ P.centres := by
  rw [component_column_iff_lineSupported _ _ _ hdim (centreTranslation_tiles K a T htile),
    centreTranslation_component_centres, lineSupported_centreTranslation,
    component_column_iff_lineSupported K δ T hdim htile]

private theorem centreTranslation_columnPart (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a : Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ) :
    columnPart K δ (a +ᵥ T) = a +ᵥ columnPart K δ T := by
  let e := (centreTranslationGraphIso K δ a T).connectedComponentEquiv
  ext x
  constructor
  · intro hx
    obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
    let P : EarthquakeComponent K δ T := e.symm Q.1
    have hc : a +ᵥ P.centres = Q.1.centres := by
      rw [← centreTranslation_component_centres K δ a T P]
      exact congrArg EarthquakeComponent.centres (e.apply_symm_apply Q.1)
    have hP : IsCenterColumn K δ P.centres := by
      apply (centreTranslation_component_column K δ a T hdim htile P).mp
      change IsCenterColumn K δ (EarthquakeComponent.centres (e P))
      rw [show e P = Q.1 from e.apply_symm_apply Q.1]
      exact Q.2
    obtain ⟨s, hs, rfl⟩ := Set.mem_vadd_set.mp (hc.symm ▸ hxQ)
    exact Set.mem_vadd_set.mpr ⟨s, Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hs⟩, rfl⟩
  · intro hx
    obtain ⟨s, hs, rfl⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨P, hsP⟩ := Set.mem_iUnion.mp hs
    refine Set.mem_iUnion.mpr ⟨⟨e P.1,
      (centreTranslation_component_column K δ a T hdim htile P.1).mpr P.2⟩, ?_⟩
    rw [centreTranslation_component_centres]
    exact Set.mem_vadd_set.mpr ⟨s, hsP, rfl⟩

private theorem commonCarrierPeriod_centreTranslation (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (a : Plane) (T : Set Plane) (hdim : Module.finrank ℝ δ = 1) (htile : TilesOn K T Set.univ)
    (v : Plane) (hv : IsCommonCarrierPeriod K δ (a +ᵥ T) v) :
    IsCommonCarrierPeriod K δ T v := by
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  refine ⟨hvδ, ?_, ?_⟩
  · rwa [centreTranslation_columnPart K δ a T hdim htile,
      regularSupport_vadd, periodGroup_tileTranslation] at hvcol
  · intro P hP
    let Q : EarthquakeComponent K δ (a +ᵥ T) :=
      (centreTranslationGraphIso K δ a T).connectedComponentEquiv P
    have hQ : Q ∈ noncolumnComponents K δ (a +ᵥ T) := by
      intro hc
      exact hP ((centreTranslation_component_column K δ a T hdim htile P).mp hc)
    have hvQ := hvnon Q hQ
    change v ∈ periodGroup (regularSupport K (EarthquakeComponent.centres
      ((centreTranslationGraphIso K δ a T).connectedComponentEquiv P))) at hvQ
    rwa [centreTranslation_component_centres, regularSupport_vadd,
      periodGroup_tileTranslation] at hvQ

private theorem frontier_vadd_actual (v : Plane) (U : Set Plane) :
    frontier (v +ᵥ U) = v +ᵥ frontier U := by
  rw [frontier, closure_vadd, interior_vadd]
  ext x
  simp only [Set.mem_sdiff, Set.mem_vadd_set_iff_neg_vadd_mem, frontier]

private theorem affineImage_refl_axisBoundary (K : PolygonalRegion) (v : Plane)
    (haxis : ∀ a b : Plane, a ≠ b → openSegment ℝ a b ⊆ frontier K.support →
      a.re = b.re ∨ a.im = b.im) :
    ∀ a b : Plane, a ≠ b →
      openSegment ℝ a b ⊆ frontier (affineImage K (ContinuousLinearEquiv.refl ℝ Plane) v).support →
      a.re = b.re ∨ a.im = b.im := by
  intro a b hab hseg
  have hab' : (-v + a) ≠ (-v + b) := by simpa using hab
  have hseg' : openSegment ℝ (-v + a) (-v + b) ⊆ frontier K.support := by
    intro x hx
    have hx' : v + x ∈ openSegment ℝ a b := by
      have ht : v +ᵥ x ∈ v +ᵥ openSegment ℝ (-v + a) (-v + b) :=
        Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
      rw [vadd_openSegment ℝ] at ht
      simpa only [vadd_eq_add, add_neg_cancel_left] using ht
    have hf := hseg hx'
    rw [affineImage_refl_support, frontier_vadd_actual] at hf
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_cancel_left] using hf
  rcases haxis (-v + a) (-v + b) hab' hseg' with hre | him
  · left
    simpa using hre
  · right
    simpa using him

private theorem relative_vertex_mesh (K : PolygonalRegion)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K) :
    ∃ d : ℕ, 0 < d ∧ ∀ v w : Plane,
      v ∈ vertexSet K.support → w ∈ vertexSet K.support →
      ∃ z : IntegerPlane, v - w = (d : ℝ)⁻¹ • integerPoint z := by
  obtain ⟨a, _ha, hvertices⟩ := hK
  obtain ⟨d, hd, hmesh⟩ := finite_rational_points_mesh
    ((fun v => v - a) '' vertexSet K.support)
    (K.isPolygonal.vertexSet_finite.image _) (by
      rintro x ⟨v, hv, rfl⟩
      exact hvertices v hv)
  refine ⟨d, hd, ?_⟩
  intro v w hv hw
  obtain ⟨z, hz⟩ := hmesh (v - a) ⟨v, hv, rfl⟩
  obtain ⟨q, hq⟩ := hmesh (w - a) ⟨w, hw, rfl⟩
  refine ⟨z - q, ?_⟩
  rw [Tiling.RationalPolygonal.integerPoint_sub, smul_sub, ← hz, ← hq]
  abel

private theorem relativelyRational_linearImage (K : PolygonalRegion) (B : Plane ≃L[ℝ] Plane)
    (hB : IsRationalLinear B) (hK : Tiling.RationalPolygonal.IsRelativelyRational K) :
    Tiling.RationalPolygonal.IsRelativelyRational (affineImage K B 0) := by
  obtain ⟨a, ha, hvertices⟩ := hK
  have hf : affineMap B 0 = (B : Plane → Plane) := by funext x; simp [affineMap]
  have hvertex : vertexSet (affineImage K B 0).support = B '' vertexSet K.support := by
    rw [vertexSet_affineImage, hf]
  refine ⟨B a, hvertex.symm ▸ ⟨a, ha, rfl⟩, ?_⟩
  intro x hx
  rw [hvertex] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [map_sub] using hB (y - a) (hvertices y hy)

private theorem rationalLinear_integer_mesh (B : Plane ≃L[ℝ] Plane) (hB : IsRationalLinear B) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : IntegerPlane, ∃ q : IntegerPlane,
      B (integerPoint z) = (n : ℝ)⁻¹ • integerPoint q := by
  obtain ⟨n, hn, hmesh⟩ := finite_rational_points_mesh
    ({B 1, B Complex.I} : Set Plane) (Set.toFinite _) (by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact hB 1 ⟨1, 0, by norm_num, by norm_num⟩
      · rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact hB Complex.I ⟨0, 1, by norm_num, by norm_num⟩)
  obtain ⟨p, hp⟩ := hmesh (B 1) (by simp)
  obtain ⟨q, hq⟩ := hmesh (B Complex.I) (by simp)
  refine ⟨n, hn, ?_⟩
  intro z
  let w : IntegerPlane := ![z 0 * p 0 + z 1 * q 0, z 0 * p 1 + z 1 * q 1]
  refine ⟨w, ?_⟩
  have hz : integerPoint z = (z 0 : ℝ) • (1 : Plane) + (z 1 : ℝ) • Complex.I := by
    apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint]
  rw [hz, map_add, map_smul, map_smul, hp, hq]
  apply Complex.ext <;> simp [w, Tiling.RationalPolygonal.integerPoint] <;> ring

private theorem gridLinearEquiv_rational (m : ℕ) (hm : 0 < m) :
    IsRationalLinear (gridLinearEquiv (m : ℝ) m (by exact_mod_cast hm) (by exact_mod_cast hm)) := by
  intro x hx
  obtain ⟨p, q, hp, hq⟩ := hx
  exact ⟨(m : ℚ) * p, (m : ℚ) * q, by simp [gridLinearEquiv, hp],
    by simp [gridLinearEquiv, hq]⟩

private theorem integer_vertical_commonCarrierPeriod (K : PolygonalRegion) (T : Set Plane)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hTinteger : T ⊆ Set.range integerPoint) (htile : TilesOn K T Set.univ) :
    ∃ v : Plane, IsCommonCarrierPeriod K verticalDirection T v := by
  classical
  obtain ⟨d, hd, hmesh⟩ := relative_vertex_mesh K hK
  obtain ⟨a, ha, _⟩ := hK
  let K0 := affineImage K (ContinuousLinearEquiv.refl ℝ Plane) (-a)
  have hK0 : TilesOn K0 T Set.univ := affineImage_refl_tiles K (-a) T htile
  have hvertices : ∀ w ∈ vertexSet K0.support, ∃ z : IntegerPlane,
      w = (d : ℝ)⁻¹ • integerPoint z := by
    intro w hw
    rw [affineImage_refl_vertices] at hw
    obtain ⟨b, hb, rfl⟩ := Set.mem_vadd_set.mp hw
    obtain ⟨z, hz⟩ := hmesh b a hb ha
    exact ⟨z, by simpa [sub_eq_add_neg, add_comm] using hz⟩
  obtain ⟨N, hN, θ, _hθ0, _hθk, hboundary, hfinite, hne, hcolumns⟩ :=
    sample_grid_exists K0 d hd hvertices
  let h : ℝ := (d : ℝ)⁻¹
  let k : ℝ := ((d * N : ℕ) : ℝ)⁻¹
  let u : Plane := (h / 2 : Plane) + θ * Complex.I
  let A : Set IntegerPlane := gridPoint h k ⁻¹' T
  have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hd)
  have hk : 0 < k := inv_pos.mpr (by exact_mod_cast Nat.mul_pos hd hN)
  have hAT : gridPoint h k '' A = T := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨q, rfl⟩ := hTinteger hx
      let z : IntegerPlane := ![(d : ℤ) * q 0, ((d * N : ℕ) : ℤ) * q 1]
      have hz : gridPoint h k z = integerPoint q := by
        have hd0 : (d : ℝ) ≠ 0 := by positivity
        have hN0 : (N : ℝ) ≠ 0 := by positivity
        apply Complex.ext <;> simp [gridPoint, z, h, k,
          Tiling.RationalPolygonal.integerPoint] <;> field_simp
      refine ⟨z, ?_, hz⟩
      change gridPoint h k z ∈ T
      rwa [hz]
  let F := hfinite.toFinset
  have hF : (F : Set IntegerPlane) = sampledIndices K0 h k u := hfinite.coe_toFinset
  have hFne : F.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, by simpa [F] using hz⟩
  have hdiscrete : TranslationalTilings.Tiles F A Set.univ :=
    sampled_finite_tile_exact K0 h k u F A hh hk (hAT.symm ▸ hK0) hboundary hF
  obtain ⟨Runit, hRunitsupport, _hRunitrat, _hRunitaxis⟩ :=
    cell_region_exists F 1 1 hFne (by decide) (by decide)
  simp only [Nat.cast_one, inv_one, Nat.one_mul] at hRunitsupport
  obtain ⟨w, hw⟩ := unitCell_commonCarrierPeriod F A Runit hFne hdiscrete hRunitsupport
  have hunit : TilesOn Runit (integerPoint '' A) Set.univ := by
    have hf : gridPoint 1 1 = integerPoint := by
      funext z
      simp [gridPoint, Tiling.RationalPolygonal.integerPoint]
    rw [← hf]
    exact cell_tiling_wholePlane F A Runit 1 1 (by norm_num) (by norm_num) hdiscrete hRunitsupport
  let B := gridLinearEquiv h k hh hk
  let R := affineImage Runit B 0
  have hBδ : verticalDirection.map B.toLinearMap = verticalDirection :=
    gridLinearEquiv_direction h k hh hk
  have hBA : B '' (integerPoint '' A) = T := by
    rw [Set.image_image]
    have hf : (fun z => B (integerPoint z)) = gridPoint h k := by
      funext z
      exact gridLinearEquiv_integerPoint h k hh hk z
    rwa [hf]
  have hRsupport : R.support = cellSupport h k F := by
    change affineMap B 0 '' Runit.support = _
    have hf : affineMap B 0 = (B : Plane → Plane) := by funext x; simp [affineMap]
    rw [hf, hRunitsupport, gridLinearEquiv_cellSupport]
  have hRtile : TilesOn R T Set.univ := by
    exact hBA ▸ linear_tiles Runit B (integerPoint '' A) hunit
  have hQ : regularizedProjection R.openCarrier = regularizedProjection K0.openCarrier := by
    change regularizedProjection (interior R.support) = _
    rw [hRsupport]
    apply sampled_cell_footprint K0 d N θ F hd hN hvertices hF
    intro i
    rw [hcolumns i]
    simp only [occupiedColumns, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨z, hz, hzi⟩ <;> exact ⟨z, by simpa [F] using hz, hzi⟩
  have hwR : IsCommonCarrierPeriod R verticalDirection T (B w) := by
    have hdim : Module.finrank ℝ verticalDirection = 1 := finrank_span_singleton Complex.I_ne_zero
    have hp := commonCarrierPeriod_linearPushforward Runit verticalDirection B
      (integerPoint '' A) hdim hunit w hw
    rwa [hBδ, hBA] at hp
  have hwK0 := commonCarrierPeriod_footprintTransfer K0 R T hK0 hRtile hQ.symm (B w) hwR
  exact ⟨B w, commonCarrierPeriod_tileTranslation K (-a) verticalDirection T
    (finrank_span_singleton Complex.I_ne_zero) htile (B w) hwK0⟩

private theorem commonMesh_commonCarrierPeriod (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hdim : Module.finrank ℝ δ = 1) (hrat : HasRationalDirection δ)
    (htile : TilesOn K T Set.univ) (d : ℕ) (hd : 0 < d) (b : Plane)
    (hmesh : T ⊆ {x | ∃ z : IntegerPlane, x = b + (d : ℝ)⁻¹ • integerPoint z}) :
    ∃ v : Plane, IsCommonCarrierPeriod K δ T v := by
  obtain ⟨B, hBrat, hBδ⟩ := exists_rationalLinear_straighten δ hdim hrat
  change δ.map B.toLinearMap = verticalDirection at hBδ
  obtain ⟨n, hn, hBmesh⟩ := rationalLinear_integer_mesh B hBrat
  let m : ℕ := d * n
  have hm : 0 < m := Nat.mul_pos hd hn
  let C := gridLinearEquiv (m : ℝ) m (by exact_mod_cast hm) (by exact_mod_cast hm)
  let K1 := affineImage K B 0
  let T1 : Set Plane := B '' T
  let a : Plane := -B b
  let T2 : Set Plane := a +ᵥ T1
  let K2 := affineImage K1 C 0
  let T3 : Set Plane := C '' T2
  have hK1 : TilesOn K1 T1 Set.univ := linear_tiles K B T htile
  have hT2 : TilesOn K1 T2 Set.univ := centreTranslation_tiles K1 a T1 hK1
  have hK2 : TilesOn K2 T3 Set.univ := linear_tiles K1 C T2 hT2
  have hrat1 := relativelyRational_linearImage K B hBrat hK
  have hrat2 := relativelyRational_linearImage K1 C (gridLinearEquiv_rational m hm) hrat1
  have hT3 : T3 ⊆ Set.range integerPoint := by
    rintro x ⟨y, hy, rfl⟩
    obtain ⟨u, hu, huy⟩ := Set.mem_vadd_set.mp hy
    obtain ⟨t, ht, htu⟩ := hu
    obtain ⟨z, hz⟩ := hmesh ht
    obtain ⟨q, hq⟩ := hBmesh z
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hBy : B t - B b = (m : ℝ)⁻¹ • integerPoint q := by
      rw [hz, map_add, map_smul, hq]
      simp only [add_sub_cancel_left, smul_smul]
      congr 1
      dsimp [m]
      push_cast
      field_simp
    have hy' : y = (m : ℝ)⁻¹ • integerPoint q := by
      rw [← huy, ← htu]
      change -B b + B t = _
      rw [← hBy]
      abel
    refine ⟨q, ?_⟩
    rw [hy']
    apply Complex.ext <;> simp [C, gridLinearEquiv] <;> field_simp
  obtain ⟨w, hw⟩ := integer_vertical_commonCarrierPeriod K2 T3 hrat2 hT3 hK2
  have hCδ : verticalDirection.map C.toLinearMap = verticalDirection :=
    gridLinearEquiv_direction (m : ℝ) m (by exact_mod_cast hm) (by exact_mod_cast hm)
  have hvertical : Module.finrank ℝ verticalDirection = 1 := finrank_span_singleton Complex.I_ne_zero
  have hw2 : IsCommonCarrierPeriod K1 verticalDirection T2 (C.symm w) := by
    apply commonCarrierPeriod_linearPullback K1 verticalDirection C T2 hvertical hT2 w
    rwa [hCδ]
  have hw1 := commonCarrierPeriod_centreTranslation K1 verticalDirection a T1 hvertical hK1
    (C.symm w) hw2
  refine ⟨B.symm (C.symm w), ?_⟩
  apply commonCarrierPeriod_linearPullback K δ B T hdim htile (C.symm w)
  rwa [hBδ]

private theorem overlap_directionShifts (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (s t s' t' : Plane) (hs : s' - s ∈ δ) (ht : t' - t ∈ δ) :
    DirectionalOverlap K δ s' t' ↔ DirectionalOverlap K δ s t := by
  unfold DirectionalOverlap
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy
    refine ⟨s + p, Set.mem_vadd_set.mpr ⟨p, hp, rfl⟩,
      t + q, Set.mem_vadd_set.mpr ⟨q, hq, rfl⟩, ?_⟩
    have h := δ.add_mem (δ.sub_mem hxy hs) ht
    convert h using 1
    simp only [vadd_eq_add] at hpx hqy
    rw [← hpx, ← hqy]
    abel
  · rintro ⟨x, hx, y, hy, hxy⟩
    obtain ⟨p, hp, hpx⟩ := Set.mem_vadd_set.mp hx
    obtain ⟨q, hq, hqy⟩ := Set.mem_vadd_set.mp hy
    refine ⟨s' + p, Set.mem_vadd_set.mpr ⟨p, hp, rfl⟩,
      t' + q, Set.mem_vadd_set.mpr ⟨q, hq, rfl⟩, ?_⟩
    have h := δ.sub_mem (δ.add_mem hxy hs) ht
    convert h using 1
    simp only [vadd_eq_add] at hpx hqy
    rw [← hpx, ← hqy]
    abel

private def directionShiftGraphIso (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (φ : T → Plane) (hφ : Function.Injective φ)
    (hδ : ∀ t : T, φ t - t.1 ∈ δ) : earthquakeGraph K δ T ≃g earthquakeGraph K δ (Set.range φ) where
  toEquiv := Equiv.ofInjective φ hφ
  map_rel_iff' := by
    intro s t
    simp only [earthquakeGraph, SimpleGraph.fromRel_adj]
    rw [(Equiv.ofInjective φ hφ).injective.ne_iff]
    change (_ ∧ (DirectionalOverlap K δ (φ s) (φ t) ∨ DirectionalOverlap K δ (φ t) (φ s))) ↔ _
    rw [overlap_directionShifts K δ s.1 t.1 (φ s) (φ t) (hδ s) (hδ t),
      overlap_directionShifts K δ t.1 s.1 (φ t) (φ s) (hδ t) (hδ s)]

private theorem directionShift_component_centres (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (φ : T → Plane) (hφ : Function.Injective φ)
    (hδ : ∀ t : T, φ t - t.1 ∈ δ) (P : EarthquakeComponent K δ T)
    (a : Plane) (ha : ∀ t : T, t.1 ∈ P.centres → φ t = a + t.1) :
    EarthquakeComponent.centres ((directionShiftGraphIso K δ T φ hφ hδ).connectedComponentEquiv P) =
      a +ᵥ P.centres := by
  let g := directionShiftGraphIso K δ T φ hφ hδ
  let e := SimpleGraph.ConnectedComponent.isoEquivSupp g P
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    let t := e.symm ⟨u, hu⟩
    have htu : g t.1 = u := congrArg Subtype.val (e.apply_symm_apply ⟨u, hu⟩)
    have hc : t.1.1 ∈ P.centres := ⟨t.1, t.2, rfl⟩
    refine Set.mem_vadd_set.mpr ⟨t.1.1, hc, ?_⟩
    change a + t.1.1 = u.1
    rw [← ha t.1 hc]
    exact congrArg Subtype.val htu
  · intro hx
    obtain ⟨x, ⟨t, ht, htx⟩, rfl⟩ := Set.mem_vadd_set.mp hx
    refine ⟨(e ⟨t, ht⟩).1, (e ⟨t, ht⟩).2, ?_⟩
    change φ t = a + x
    rw [ha t ⟨t, ht, rfl⟩, htx]

private theorem commonCarrierPeriod_directionShift (K : PolygonalRegion) (δ : Submodule ℝ Plane)
    (T : Set Plane) (φ : T → Plane) (hφ : Function.Injective φ)
    (hδ : ∀ t : T, φ t - t.1 ∈ δ) (hdim : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ) (hnew : TilesOn K (Set.range φ) Set.univ)
    (hconstant : ∀ P : EarthquakeComponent K δ T,
      ∃ a : Plane, a ∈ δ ∧ ∀ t : T, t.1 ∈ P.centres → φ t = a + t.1)
    (v : Plane) (hv : IsCommonCarrierPeriod K δ (Set.range φ) v) :
    IsCommonCarrierPeriod K δ T v := by
  let e := (directionShiftGraphIso K δ T φ hφ hδ).connectedComponentEquiv
  have hcar : ∀ P : EarthquakeComponent K δ T,
      regularSupport K (EarthquakeComponent.centres (e P)) = P.carrier := by
    intro P
    obtain ⟨a, haδ, ha⟩ := hconstant P
    rw [directionShift_component_centres K δ T φ hφ hδ P a ha, regularSupport_vadd]
    have hreg : regularSupport K T = Set.univ := regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
    exact component_isInvariant K δ T hdim htile.2.1 (by rw [hreg]; intro w hw; simp) P a haδ
  have hcol : ∀ P : EarthquakeComponent K δ T,
      IsCenterColumn K δ (EarthquakeComponent.centres (e P)) ↔ IsCenterColumn K δ P.centres := by
    intro P
    obtain ⟨a, _haδ, ha⟩ := hconstant P
    rw [component_column_iff_lineSupported K δ (Set.range φ) hdim hnew,
      directionShift_component_centres K δ T φ hφ hδ P a ha, lineSupported_centreTranslation,
      component_column_iff_lineSupported K δ T hdim htile]
  have haggregate : regularSupport K (columnPart K δ (Set.range φ)) =
      regularSupport K (columnPart K δ T) := by
    unfold columnPart
    rw [regularSupport_iUnion, regularSupport_iUnion]
    apply congrArg interior
    apply congrArg closure
    ext x
    constructor
    · intro hx
      obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.mp hx
      let P : EarthquakeComponent K δ T := e.symm Q.1
      have hPQ : e P = Q.1 := e.apply_symm_apply Q.1
      have hPcol : IsCenterColumn K δ P.centres := (hcol P).mp (hPQ.symm ▸ Q.2)
      refine Set.mem_iUnion.mpr ⟨⟨P, hPcol⟩, ?_⟩
      have hc := hcar P
      rw [hPQ] at hc
      change x ∈ P.carrier
      rw [← hc]
      exact hxQ
    · intro hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨⟨e P.1, (hcol P.1).mpr P.2⟩, ?_⟩
      rw [hcar]
      exact hxP
  rcases hv with ⟨hvδ, hvcol, hvnon⟩
  refine ⟨hvδ, haggregate ▸ hvcol, ?_⟩
  intro P hP
  have hQ : e P ∈ noncolumnComponents K δ (Set.range φ) := by
    intro hc
    exact hP ((hcol P).mp hc)
  have hp := hvnon (e P) hQ
  change v ∈ periodGroup (regularSupport K (EarthquakeComponent.centres (e P))) at hp
  rwa [hcar] at hp

private theorem construct_directional_raster (K : PolygonalRegion) (T : Set Plane)
    (hK : Tiling.RationalPolygonal.IsRelativelyRational K)
    (hTinteger : T ⊆ Set.range integerPoint) (htile : TilesOn K T Set.univ) :
    ∃ R : PolygonalRegion, Tiling.RationalPolygonal.IsRelativelyRational R ∧
      (∀ a b : Plane, a ≠ b → openSegment ℝ a b ⊆ frontier R.support →
        a.re = b.re ∨ a.im = b.im) ∧ TilesOn R T Set.univ ∧
      regularizedProjection R.openCarrier = regularizedProjection K.openCarrier := by
  classical
  obtain ⟨d, hd, hmesh⟩ := relative_vertex_mesh K hK
  obtain ⟨v, hv, _⟩ := hK
  let K0 := affineImage K (ContinuousLinearEquiv.refl ℝ Plane) (-v)
  have hK0 : TilesOn K0 T Set.univ := affineImage_refl_tiles K (-v) T htile
  have hvertices : ∀ w ∈ vertexSet K0.support, ∃ z : IntegerPlane,
      w = (d : ℝ)⁻¹ • integerPoint z := by
    intro w hw
    rw [affineImage_refl_vertices] at hw
    obtain ⟨a, ha, rfl⟩ := Set.mem_vadd_set.mp hw
    obtain ⟨z, hz⟩ := hmesh a v ha hv
    exact ⟨z, by simpa [sub_eq_add_neg, add_comm] using hz⟩
  obtain ⟨N, hN, θ, hθ0, hθk, hboundary, hfinite, hne, hcolumns⟩ :=
    sample_grid_exists K0 d hd hvertices
  let h : ℝ := (d : ℝ)⁻¹
  let k : ℝ := ((d * N : ℕ) : ℝ)⁻¹
  let u : Plane := (h / 2 : Plane) + θ * Complex.I
  let A : Set IntegerPlane := gridPoint h k ⁻¹' T
  have hh : 0 < h := inv_pos.mpr (by exact_mod_cast hd)
  have hk : 0 < k := inv_pos.mpr (by exact_mod_cast Nat.mul_pos hd hN)
  have hAT : gridPoint h k '' A = T := by
    apply Set.Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · intro x hx
      obtain ⟨q, rfl⟩ := hTinteger hx
      let z : IntegerPlane := ![(d : ℤ) * q 0, ((d * N : ℕ) : ℤ) * q 1]
      have hz : gridPoint h k z = integerPoint q := by
        have hd0 : (d : ℝ) ≠ 0 := by positivity
        have hN0 : (N : ℝ) ≠ 0 := by positivity
        apply Complex.ext <;> simp [gridPoint, z, h, k,
          Tiling.RationalPolygonal.integerPoint] <;> field_simp
      refine ⟨z, ?_, hz⟩
      change gridPoint h k z ∈ T
      rwa [hz]
  let F := hfinite.toFinset
  have hF : (F : Set IntegerPlane) = sampledIndices K0 h k u := hfinite.coe_toFinset
  have hFne : F.Nonempty := by
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, by simpa [F] using hz⟩
  have hdiscrete : TranslationalTilings.Tiles F A Set.univ :=
    sampled_finite_tile_exact K0 h k u F A hh hk (hAT.symm ▸ hK0) hboundary hF
  obtain ⟨R0, hR0support, hR0rat, hR0axis⟩ := cell_region_exists F d N hFne hd hN
  have hR0tile : TilesOn R0 T Set.univ := hAT ▸
    cell_tiling_wholePlane F A R0 h k hh hk hdiscrete hR0support
  have hQ0 : regularizedProjection R0.openCarrier = regularizedProjection K0.openCarrier := by
    change regularizedProjection (interior R0.support) = _
    rw [hR0support]
    apply sampled_cell_footprint K0 d N θ F hd hN hvertices hF
    intro i
    rw [hcolumns i]
    simp only [occupiedColumns, Set.mem_ofPred_eq]
    constructor <;> rintro ⟨z, hz, hzi⟩ <;> exact ⟨z, by simpa [F] using hz, hzi⟩
  let R := affineImage R0 (ContinuousLinearEquiv.refl ℝ Plane) v
  refine ⟨R, affineImage_refl_relativelyRational R0 v hR0rat,
    affineImage_refl_axisBoundary R0 v hR0axis, affineImage_refl_tiles R0 v T hR0tile, ?_⟩
  rw [affineImage_refl_openCarrier, regularizedProjection_vadd, hQ0,
    affineImage_refl_openCarrier, regularizedProjection_vadd]
  simp

theorem vertex_class_mesh :
  ∀ (K : PolygonalRegion) (T : Set Plane) (d : ℕ), 0 < d →
    (∀ v w : Plane, v ∈ vertexSet K.support → w ∈ vertexSet K.support →
      ∃ z : IntegerPlane, v - w = (d : ℝ)⁻¹ • integerPoint z) →
    ∀ s t : Plane, s ∈ T → t ∈ T → vertexReach K T s t →
      ∃ z : IntegerPlane, s - t = (d : ℝ)⁻¹ • integerPoint z
  := by
  intro K T d _hd hmesh s t _hs _ht hreach
  induction hreach with
  | refl =>
      refine ⟨0, ?_⟩
      simp [Tiling.RationalPolygonal.integerPoint_zero]
  | @tail t u hst htu ih =>
      obtain ⟨z, hz⟩ := ih htu.1
      obtain ⟨x, hxT, hxU⟩ := htu.2.2
      obtain ⟨v, hv, htv⟩ := Set.mem_vadd_set.mp hxT
      obtain ⟨w, hw, huw⟩ := Set.mem_vadd_set.mp hxU
      obtain ⟨q, hq⟩ := hmesh w v hw hv
      refine ⟨z + q, ?_⟩
      rw [Tiling.RationalPolygonal.integerPoint_add, smul_add, ← hz, ← hq]
      simp only [vadd_eq_add] at htv huw
      have htu' : t - u = w - v := by
        calc
          t - u = (t + v) - (u + w) + (w - v) := by abel
          _ = w - v := by rw [htv, huw]; simp
      rw [← htu']
      abel

end Tiling.RationalSlopes.DirectionalRaster


namespace Tiling.RationalSlopes
open Tiling.RationalPolygonal (PolygonalRegion)
open Tiling.Polygonal
private theorem component_centres_eq_of_subsingleton (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane)
    [Subsingleton (EarthquakeComponent K δ T)] (P : EarthquakeComponent K δ T) :
    P.centres = T := by
  ext t
  constructor
  · rintro ⟨s, _hs, rfl⟩
    exact s.2
  · intro ht
    refine ⟨⟨t, ht⟩, ?_, rfl⟩
    change (earthquakeGraph K δ T).connectedComponentMk ⟨t, ht⟩ = P
    exact Subsingleton.elim _ _

private theorem one_component_commonCarrierPeriod (K : PolygonalRegion)
    (δ : Submodule ℝ Plane) (T : Set Plane) (hδ : Module.finrank ℝ δ = 1)
    (htile : TilesOn K T Set.univ)
    [Subsingleton (EarthquakeComponent K δ T)] :
    ∃ v : Plane, IsCommonCarrierPeriod K δ T v := by
  classical
  have hreg : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
  have hT : T.Nonempty := by
    by_contra h
    have hzero : T = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [hzero, regularSupport, openUnion] at hreg
    exact Set.empty_ne_univ hreg
  obtain ⟨t, ht⟩ := hT
  let P₀ : EarthquakeComponent K δ T := (earthquakeGraph K δ T).connectedComponentMk ⟨t, ht⟩
  have htransverse : ∃ v : Plane, v ∉ δ := by
    by_contra h
    push Not at h
    have htop : δ = ⊤ := Submodule.eq_top_iff'.mpr h
    rw [htop, finrank_top, Complex.finrank_real_complex] at hδ
    omega
  obtain ⟨v, hv⟩ := htransverse
  refine ⟨v, hv, ?_, ?_⟩
  · by_cases hcol : IsCenterColumn K δ T
    · have hpart : columnPart K δ T = T := by
        ext x
        constructor
        · intro hx
          obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
          rwa [component_centres_eq_of_subsingleton K δ T P.1] at hxP
        · intro hx
          apply Set.mem_iUnion.mpr
          refine ⟨⟨P₀, ?_⟩, ?_⟩
          · rwa [component_centres_eq_of_subsingleton K δ T P₀]
          · rwa [component_centres_eq_of_subsingleton K δ T P₀]
      rw [hpart, hreg]
      change v ∈ AddAction.stabilizer Plane Set.univ
      simp
    · have hpart : columnPart K δ T = ∅ := by
        ext x
        constructor
        · intro hx
          obtain ⟨P, _hxP⟩ := Set.mem_iUnion.mp hx
          have hcolP := P.2
          rw [component_centres_eq_of_subsingleton K δ T P.1] at hcolP
          exact (hcol hcolP).elim
        · simp
      rw [hpart]
      simp [regularSupport, openUnion, periodGroup]
  · intro P _hP
    change v ∈ periodGroup (regularSupport K P.centres)
    rw [component_centres_eq_of_subsingleton K δ T P, hreg]
    simp [periodGroup]

/-- Stronger raster correspondence, in already integerized vertical coordinates.
This is a conclusion to CONSTRUCT, not a stored premise of a provider package. -/
theorem directionalRaster_correspondence :
  ∀ (K : PolygonalRegion) (T : Set Plane),
    Tiling.RationalPolygonal.IsRelativelyRational K →
    T ⊆ Set.range Tiling.RationalPolygonal.integerPoint →
    TilesOn K T Set.univ →
    ∃ R : PolygonalRegion,
      Tiling.RationalPolygonal.IsRelativelyRational R ∧
      (∀ a b : Plane, a ≠ b →
        openSegment ℝ a b ⊆ frontier R.support →
        a.re = b.re ∨ a.im = b.im) ∧
      TilesOn R T Set.univ ∧
      DirectionalRaster.regularizedProjection R.openCarrier = DirectionalRaster.regularizedProjection K.openCarrier ∧
      (∀ s t : Plane,
        DirectionalOverlap K DirectionalRaster.verticalDirection s t ↔
          DirectionalOverlap R DirectionalRaster.verticalDirection s t) ∧
      (∀ S : Set Plane, S ⊆ T →
        (IsInvariantAlong (regularSupport K S) DirectionalRaster.verticalDirection ↔
          IsInvariantAlong (regularSupport R S) DirectionalRaster.verticalDirection)) ∧
      (∀ S : Set Plane, S ⊆ T →
        IsInvariantAlong (regularSupport K S) DirectionalRaster.verticalDirection →
        regularSupport K S = regularSupport R S) ∧
      (∀ S : Set Plane, S ⊆ T →
        (IsCenterColumn K DirectionalRaster.verticalDirection S ↔
          IsCenterColumn R DirectionalRaster.verticalDirection S))
  := by
  intro K T hK hTinteger htile
  obtain ⟨R, hRrat, hRaxis, hRtile, hQ⟩ :=
    DirectionalRaster.construct_directional_raster K T hK hTinteger htile
  refine ⟨R, hRrat, hRaxis, hRtile, hQ, ?_, ?_, ?_, ?_⟩
  · intro s t
    rw [DirectionalRaster.directionalOverlap_iff_footprint,
      DirectionalRaster.directionalOverlap_iff_footprint, hQ]
  · intro S hST
    exact DirectionalRaster.invariant_iff_of_footprint K R T S htile hRtile hST hQ.symm
  · intro S hST hSinv
    exact DirectionalRaster.saturated_subfamily_carrier_eq K R T S htile hRtile hST hQ.symm hSinv
  · intro S hST
    exact DirectionalRaster.centerColumn_iff_of_footprint K R T S htile hRtile hST hQ.symm

/-- No injective affine map on all points is required: φ labels old centres.
The direction shift is constant per old component, preserving its carrier. -/
theorem earthquake_commonMesh_shift :
  ∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Tiling.RationalPolygonal.IsRelativelyRational K →
    Module.finrank ℝ δ = 1 → HasRationalDirection δ →
    TilesOn K T Set.univ →
    (∃ P Q : EarthquakeComponent K δ T, P ≠ Q) →
    ∃ φ : T → Plane,
      Function.Injective φ ∧ TilesOn K (Set.range φ) Set.univ ∧
      (∀ t : T, φ t - t.1 ∈ δ) ∧
      (∀ P : EarthquakeComponent K δ T,
        ∃ a : Plane, a ∈ δ ∧ ∀ t : T, t.1 ∈ P.centres → φ t = a + t.1) ∧
      (∃ d : ℕ, 0 < d ∧ ∃ b : Plane,
        Set.range φ ⊆ {x | ∃ z : Tiling.RationalPolygonal.IntegerPlane,
          x = b + (d : ℝ)⁻¹ • Tiling.RationalPolygonal.integerPoint z})
  := by
  intro K δ T hK hδ _hδrat htile hcomponents
  classical
  let A := K.polygonalProtoTiling T
  have hnative : K.Tiles T := (tilesOn_univ_iff_tiles K T).mp htile
  obtain ⟨v, hvδ, hvslide⟩ := DirectionalRaster.prescribed_sliding_direction K δ T hδ htile hcomponents
  obtain ⟨shift, hshiftTile, hshiftConnected⟩ :=
    PolygonalProtoTiling.IsSlidingDirection.exists_connected_component_shift A hvslide hnative
  let φ : T → Plane := fun t =>
    (A.shiftedPlacement v shift ⟨(t.1, ()), t.2⟩).1
  have hplacements : K.placements (Set.range φ) = (A.shiftComponents v shift).placements := by
    ext p
    constructor
    · rintro ⟨t, htp⟩
      apply A.mem_shiftComponents_placements_iff.mpr
      refine ⟨⟨(t.1, ()), t.2⟩, ?_⟩
      exact Prod.ext htp (Subsingleton.elim _ _)
    · intro hp
      obtain ⟨i, hip⟩ := A.mem_shiftComponents_placements_iff.mp hp
      refine ⟨⟨i.1.1, i.2⟩, ?_⟩
      have hieq : (⟨(i.1.1, ()), i.2⟩ : A.placements) = i :=
        Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))
      change (A.shiftedPlacement v shift ⟨(i.1.1, ()), i.2⟩).1 = p.1
      rw [hieq, hip]
  have hmodel : K.polygonalProtoTiling (Set.range φ) = A.shiftComponents v shift := by
    change A.withPlacements (K.placements (Set.range φ)) =
      A.withPlacements (A.shiftComponents v shift).placements
    rw [hplacements]
  have hnewnative : K.Tiles (Set.range φ) := by
    change IsTiling (K.polygonalProtoTiling (Set.range φ)).prototiles
      (K.polygonalProtoTiling (Set.range φ)).placements
    rw [hmodel]
    exact hshiftTile
  have hnewtile : TilesOn K (Set.range φ) Set.univ :=
    (tilesOn_univ_iff_tiles K (Set.range φ)).mpr hnewnative
  have hnewconnected : (K.polygonalProtoTiling (Set.range φ)).vertexGraph.Connected := by
    rw [hmodel]
    exact hshiftConnected
  refine ⟨φ, ?_, hnewtile, ?_, ?_, ?_⟩
  · intro t s hφ
    have hshifted : A.shiftedVertex v shift ⟨(t.1, ()), t.2⟩ =
        A.shiftedVertex v shift ⟨(s.1, ()), s.2⟩ :=
      Subtype.ext (Prod.ext hφ (Subsingleton.elim _ _))
    have hi := DirectionalRaster.shiftedVertex_injective_prescribed hvslide hnative shift hshifted
    exact Subtype.ext (congrArg (fun i : A.placements => i.1.1) hi)
  · intro t
    change t.1 + shift (A.vertexGraph.connectedComponentMk ⟨(t.1, ()), t.2⟩) • v - t.1 ∈ δ
    simpa using δ.smul_mem (shift (A.vertexGraph.connectedComponentMk ⟨(t.1, ()), t.2⟩)) hvδ
  · intro P
    obtain ⟨t0, ht0⟩ := P.nonempty_supp
    have ht0P : t0.1 ∈ P.centres := ⟨t0, ht0, rfl⟩
    let S : Set Plane := {s | s ∈ T ∧ DirectionalRaster.vertexReach K T t0.1 s}
    have hSsub : S ⊆ T := fun _ hs => hs.1
    have hSinv := DirectionalRaster.vertex_class_saturated K δ T hδ htile hcomponents t0.1 t0.2
    have hreg : regularSupport K T = Set.univ := regularSupport_eq_of_tilesOn isOpen_univ (by simp) htile
    have hPin : P.centres ⊆ S := by
      rcases invariantSubfamily_isUnionComponents K δ T S hδ htile.2.1
        (by rw [hreg]; intro w hw; simp) hSsub hSinv P with hdis | hsub
      · exact False.elim (Set.disjoint_left.mp hdis ht0P ⟨t0.2, Relation.ReflTransGen.refl⟩)
      · exact hsub
    let C := A.vertexGraph.connectedComponentMk ⟨(t0.1, ()), t0.2⟩
    refine ⟨shift C • v, δ.smul_mem (shift C) hvδ, ?_⟩
    intro t htP
    have hreach := DirectionalRaster.graphReach_of_vertexReach K T t0.1 t.1 t0.2 t.2 (hPin htP).2
    have heq : A.vertexGraph.connectedComponentMk ⟨(t.1, ()), t.2⟩ = C :=
      ((A.samePlate_iff_component_eq _ _).mp hreach).symm
    change t.1 + shift (A.vertexGraph.connectedComponentMk ⟨(t.1, ()), t.2⟩) • v = shift C • v + t.1
    rw [heq, add_comm]
  · obtain ⟨d, hd, hmesh⟩ := DirectionalRaster.relative_vertex_mesh K hK
    obtain ⟨i⟩ := hnewconnected.nonempty
    refine ⟨d, hd, i.1.1, ?_⟩
    intro x hx
    let j : (K.polygonalProtoTiling (Set.range φ)).placements := ⟨(x, ()), hx⟩
    have hreach := hnewconnected j i
    have hvreach := DirectionalRaster.vertexReach_of_graphReach K (Set.range φ) hreach
    obtain ⟨z, hz⟩ := DirectionalRaster.vertex_class_mesh K (Set.range φ) d hd hmesh x i.1.1 hx i.2 hvreach
    refine ⟨z, ?_⟩
    rw [← hz]
    abel


/-- Owner DR: the nontriviality hypothesis is unnecessary for the endpoint;
the one-component branch is elementary and bypasses the mesh constructor. -/
theorem rational_wholePlane_commonCarrierPeriod :
  ∀ (K : PolygonalRegion) (δ : Submodule ℝ Plane) (T : Set Plane),
    Tiling.RationalPolygonal.IsRelativelyRational K →
    Module.finrank ℝ δ = 1 → HasRationalDirection δ →
    TilesOn K T Set.univ →
    ∃ v : Plane, IsCommonCarrierPeriod K δ T v
  := by
  intro K δ T hK hdim hrat htile
  classical
  by_cases hcomponents : ∃ P Q : EarthquakeComponent K δ T, P ≠ Q
  · obtain ⟨φ, hφ, hnew, hδ, hconstant, d, hd, b, hmesh⟩ :=
      earthquake_commonMesh_shift K δ T hK hdim hrat htile hcomponents
    obtain ⟨v, hv⟩ := DirectionalRaster.commonMesh_commonCarrierPeriod K δ (Set.range φ)
      hK hdim hrat hnew d hd b hmesh
    exact ⟨v, DirectionalRaster.commonCarrierPeriod_directionShift K δ T φ hφ hδ hdim
      htile hnew hconstant v hv⟩
  · have : Subsingleton (EarthquakeComponent K δ T) := ⟨by
      intro P Q
      by_contra hPQ
      exact hcomponents ⟨P, Q, hPQ⟩⟩
    exact one_component_commonCarrierPeriod K δ T hdim htile

end Tiling.RationalSlopes
