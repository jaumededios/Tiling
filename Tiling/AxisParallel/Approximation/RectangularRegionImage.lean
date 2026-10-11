import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.IntrinsicVertices

/-- The coordinatewise product of two real homeomorphisms, transported through
`ℂ ≃L[ℝ] ℝ × ℝ`. -/
def coordinateProductHomeomorph (hx hy : ℝ ≃ₜ ℝ) :
    Tiling.Plane ≃ₜ Tiling.Plane :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    ((hx.prodCongr hy).trans Complex.equivRealProdCLM.toHomeomorph.symm)

theorem coordinateProductHomeomorph_apply
    (hx hy : ℝ ≃ₜ ℝ) (z : Tiling.Plane) :
    coordinateProductHomeomorph hx hy z = hx z.re + hy z.im * Complex.I := by
  apply Complex.ext <;> simp [coordinateProductHomeomorph]

private theorem strictMono_image_uIcc (h : ℝ ≃ₜ ℝ) (hh : StrictMono h)
    (a b : ℝ) : h '' Set.uIcc a b = Set.uIcc (h a) (h b) := by
  rcases le_total a b with hab | hba
  · rw [uIcc_of_le hab, uIcc_of_le (hh.monotone hab)]
    exact h.continuous.image_Icc_of_strictMono hh
  · rw [uIcc_of_ge hba, uIcc_of_ge (hh.monotone hba)]
    exact h.continuous.image_Icc_of_strictMono hh

private theorem coordinateProductHomeomorph_image_rectangle
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (a b : Tiling.Plane) :
    coordinateProductHomeomorph hx hy '' Complex.Rectangle a b =
      Complex.Rectangle (coordinateProductHomeomorph hx hy a)
        (coordinateProductHomeomorph hx hy b) := by
  ext z
  simp only [Set.mem_image]
  change (∃ w : Tiling.Plane,
    (w.re ∈ Set.uIcc a.re b.re ∧ w.im ∈ Set.uIcc a.im b.im) ∧ _) ↔ _
  change _ ↔ (z.re ∈ Set.uIcc _ _ ∧ z.im ∈ Set.uIcc _ _)
  rw [coordinateProductHomeomorph_apply,
    coordinateProductHomeomorph_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    zero_add, mul_one]
  constructor
  · rintro ⟨w, ⟨hwre, hwim⟩, rfl⟩
    rw [coordinateProductHomeomorph_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      zero_add, mul_one]
    constructor
    · simpa using (Set.ext_iff.mp (strictMono_image_uIcc hx hhx a.re b.re) _).mp
        ⟨w.re, hwre, rfl⟩
    · simpa using (Set.ext_iff.mp (strictMono_image_uIcc hy hhy a.im b.im) _).mp
        ⟨w.im, hwim, rfl⟩
  · rintro ⟨hzre, hzim⟩
    have hzre' : z.re ∈ hx '' Set.uIcc a.re b.re := by
      rw [strictMono_image_uIcc hx hhx]
      simpa using hzre
    have hzim' : z.im ∈ hy '' Set.uIcc a.im b.im := by
      rw [strictMono_image_uIcc hy hhy]
      simpa using hzim
    obtain ⟨x, hxmem, hxz⟩ := hzre'
    obtain ⟨y, hymem, hyz⟩ := hzim'
    let w : Tiling.Plane := x + y * Complex.I
    refine ⟨w, ⟨?_, ?_⟩, ?_⟩
    · simpa [w] using hxmem
    · simpa [w] using hymem
    · rw [coordinateProductHomeomorph_apply]
      apply Complex.ext <;> simp [w, hxz, hyz]

theorem region_ext_openCarrier (K L : Region)
    (h : K.openCarrier = L.openCarrier) : K = L := by
  have hs : K.support = L.support := by
    rw [← K.isPolygonal.closure_interior, ← L.isPolygonal.closure_interior]
    exact congrArg closure h
  cases K with
  | mk K hK =>
    cases L with
    | mk L hL =>
      rw [Region.mk.injEq, Tiling.RationalPolygonal.PolygonalRegion.mk.injEq]
      exact hs

theorem region_support_image_of_openCarrier_image
    (K L : Region) (H : Tiling.Plane ≃ₜ Tiling.Plane)
    (h : L.openCarrier = H '' K.openCarrier) : L.support = H '' K.support := by
  rw [← L.isPolygonal.closure_interior, ← K.isPolygonal.closure_interior]
  change closure L.openCarrier = H '' closure K.openCarrier
  rw [h, H.image_closure]

theorem connectedComponents_equiv_image
    (H : Tiling.Plane ≃ₜ Tiling.Plane) (s : Set Tiling.Plane) :
    Nonempty (ConnectedComponents ↥s ≃ ConnectedComponents ↥(H '' s)) := by
  let e : ↥s ≃ₜ ↥(H '' s) :=
    { toFun := fun x => ⟨H x, ⟨x, x.2, rfl⟩⟩
      invFun := fun y => ⟨H.symm y, by
        obtain ⟨x, hx, hxy⟩ := y.2
        simpa [← hxy] using hx⟩
      left_inv := fun x => Subtype.ext (H.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (H.apply_symm_apply y)
      continuous_toFun := (H.continuous.comp continuous_subtype_val).subtype_mk
        (fun x => ⟨x, x.2, rfl⟩)
      continuous_invFun := (H.symm.continuous.comp continuous_subtype_val).subtype_mk
        (fun y => by
          obtain ⟨x, hx, hxy⟩ := y.2
          simpa [← hxy] using hx) }
  let he := e.isQuotientMap.isCoinducing
  exact ⟨(he.connectedComponentsHomeomorph (fun y => by
    have hfibre : e ⁻¹' ({y} : Set _) = {e.symm y} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact e.eq_symm_apply.symm
    rw [hfibre]
    exact isConnected_singleton)).toEquiv⟩

private theorem coordinateProductHomeomorph_symm_re
    (hx hy : ℝ ≃ₜ ℝ) (z : Tiling.Plane) :
    ((coordinateProductHomeomorph hx hy).symm z).re = hx.symm z.re := by
  have h := congrArg Complex.re
    (coordinateProductHomeomorph_apply hx hy
      ((coordinateProductHomeomorph hx hy).symm z))
  have hcoord : z.re = hx ((coordinateProductHomeomorph hx hy).symm z).re := by
    simpa using h
  apply hx.injective
  rw [hx.apply_symm_apply]
  exact hcoord.symm

private theorem coordinateProductHomeomorph_symm_im
    (hx hy : ℝ ≃ₜ ℝ) (z : Tiling.Plane) :
    ((coordinateProductHomeomorph hx hy).symm z).im = hy.symm z.im := by
  have h := congrArg Complex.im
    (coordinateProductHomeomorph_apply hx hy
      ((coordinateProductHomeomorph hx hy).symm z))
  have hcoord : z.im = hy ((coordinateProductHomeomorph hx hy).symm z).im := by
    simpa using h
  apply hy.injective
  rw [hy.apply_symm_apply]
  exact hcoord.symm

private theorem inverse_preserves_vertexGridComparisons
    (K : Region) (hx₁ hy₁ hx₂ hy₂ : ℝ ≃ₜ ℝ)
    (hmx₁ : StrictMono hx₁) (hmy₁ : StrictMono hy₁)
    (hmx₂ : StrictMono hx₂) (hmy₂ : StrictMono hy₂)
    (hex : ∀ v ∈ K.vertices, hx₁ v.re = hx₂ v.re)
    (hey : ∀ v ∈ K.vertices, hy₁ v.im = hy₂ v.im)
    (z : Tiling.Plane) :
    (∀ v ∈ K.vertices,
      (((coordinateProductHomeomorph hx₁ hy₁).symm z).re < v.re ↔
        ((coordinateProductHomeomorph hx₂ hy₂).symm z).re < v.re)) ∧
    ∀ v ∈ K.vertices,
      (((coordinateProductHomeomorph hx₁ hy₁).symm z).im < v.im ↔
        ((coordinateProductHomeomorph hx₂ hy₂).symm z).im < v.im) := by
  constructor
  · intro v hv
    rw [coordinateProductHomeomorph_symm_re, coordinateProductHomeomorph_symm_re]
    calc
      hx₁.symm z.re < v.re ↔ z.re < hx₁ v.re := by
        simpa using (hmx₁.lt_iff_lt (a := hx₁.symm z.re) (b := v.re)).symm
      _ ↔ z.re < hx₂ v.re := by rw [hex v hv]
      _ ↔ hx₂.symm z.re < v.re := by
        simpa using hmx₂.lt_iff_lt (a := hx₂.symm z.re) (b := v.re)
  · intro v hv
    rw [coordinateProductHomeomorph_symm_im, coordinateProductHomeomorph_symm_im]
    calc
      hy₁.symm z.im < v.im ↔ z.im < hy₁ v.im := by
        simpa using (hmy₁.lt_iff_lt (a := hy₁.symm z.im) (b := v.im)).symm
      _ ↔ z.im < hy₂ v.im := by rw [hey v hv]
      _ ↔ hy₂.symm z.im < v.im := by
        simpa using hmy₂.lt_iff_lt (a := hy₂.symm z.im) (b := v.im)

private theorem inverse_offVertexGrid_of_target_offGrid
    (K : Region) (hx₁ hy₁ hx₂ hy₂ : ℝ ≃ₜ ℝ)
    (_hmx₁ : StrictMono hx₁) (_hmy₁ : StrictMono hy₁)
    (_hmx₂ : StrictMono hx₂) (_hmy₂ : StrictMono hy₂)
    (hex : ∀ v ∈ K.vertices, hx₁ v.re = hx₂ v.re)
    (hey : ∀ v ∈ K.vertices, hy₁ v.im = hy₂ v.im)
    (z : Tiling.Plane)
    (hoff : ∀ v ∈ K.vertices, z.re ≠ hx₁ v.re ∧ z.im ≠ hy₁ v.im) :
    (∀ v ∈ K.vertices,
      ((coordinateProductHomeomorph hx₁ hy₁).symm z).re ≠ v.re ∧
      ((coordinateProductHomeomorph hx₁ hy₁).symm z).im ≠ v.im) ∧
    ∀ v ∈ K.vertices,
      ((coordinateProductHomeomorph hx₂ hy₂).symm z).re ≠ v.re ∧
      ((coordinateProductHomeomorph hx₂ hy₂).symm z).im ≠ v.im := by
  constructor
  · intro v hv
    rw [coordinateProductHomeomorph_symm_re, coordinateProductHomeomorph_symm_im]
    exact ⟨fun h => (hoff v hv).1 (calc
        z.re = hx₁ (hx₁.symm z.re) := (hx₁.apply_symm_apply z.re).symm
        _ = hx₁ v.re := congrArg hx₁ h),
      fun h => (hoff v hv).2 (calc
        z.im = hy₁ (hy₁.symm z.im) := (hy₁.apply_symm_apply z.im).symm
        _ = hy₁ v.im := congrArg hy₁ h)⟩
  · intro v hv
    rw [coordinateProductHomeomorph_symm_re, coordinateProductHomeomorph_symm_im]
    exact ⟨fun h => (hoff v hv).1 (by
        calc
          z.re = hx₂ (hx₂.symm z.re) := (hx₂.apply_symm_apply z.re).symm
          _ = hx₂ v.re := congrArg hx₂ h
          _ = hx₁ v.re := (hex v hv).symm),
      fun h => (hoff v hv).2 (by
        calc
          z.im = hy₂ (hy₂.symm z.im) := (hy₂.apply_symm_apply z.im).symm
          _ = hy₂ v.im := congrArg hy₂ h
          _ = hy₁ v.im := (hey v hv).symm)⟩

private theorem coordinateProductHomeomorph_rectangulation
    {s : Set Tiling.Plane} (R : Tiling.Rectangulation s)
    (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy) :
    ∃ R' : Tiling.Rectangulation (coordinateProductHomeomorph hx hy '' s),
      R'.pieces = R.pieces.image
        (fun r : Set Tiling.Plane => coordinateProductHomeomorph hx hy '' r) := by
  classical
  let H := coordinateProductHomeomorph hx hy
  let pieces := R.pieces.image (fun r : Set Tiling.Plane => H '' r)
  have himage_inj : Function.Injective (fun r : Set Tiling.Plane => H '' r) := by
    intro r t h
    change H '' r = H '' t at h
    ext x
    constructor <;> intro hx
    · have : H x ∈ H '' r := ⟨x, hx, rfl⟩
      rw [h] at this
      obtain ⟨y, hy, heq⟩ := this
      exact H.injective heq ▸ hy
    · have : H x ∈ H '' t := ⟨x, hx, rfl⟩
      rw [← h] at this
      obtain ⟨y, hy, heq⟩ := this
      exact H.injective heq ▸ hy
  have hrect (u : Set Tiling.Plane) (hu : u ∈ pieces) : Tiling.IsRectangle u := by
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨a, b, hre, him, rfl⟩ := R.isRectangle r hr
    refine ⟨H a, H b, ?_, ?_, ?_⟩
    · simp only [H, coordinateProductHomeomorph_apply, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero]
      simpa using hhx.injective.ne hre
    · simp only [H, coordinateProductHomeomorph_apply, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_im, zero_add, mul_one]
      simpa using hhy.injective.ne him
    · exact coordinateProductHomeomorph_image_rectangle hx hy hhx hhy a b
  have hpair : ((pieces : Finset (Set Tiling.Plane)) : Set (Set Tiling.Plane)).Pairwise
      (AEDisjoint volume) := by
    intro u hu v hv huv
    obtain ⟨r, hr, hru⟩ := Finset.mem_image.mp hu
    obtain ⟨t, ht, htv⟩ := Finset.mem_image.mp hv
    subst u
    subst v
    have hrt : r ≠ t := fun h => huv (h ▸ rfl)
    have hae := R.pairwiseAEDisjoint hr ht hrt
    have hinter : Disjoint (interior r) (interior t) := by
      rw [Set.disjoint_left]
      intro x hxr hxt
      have hopen : IsOpen (interior r ∩ interior t) := isOpen_interior.inter isOpen_interior
      have hpos := hopen.measure_pos volume ⟨x, hxr, hxt⟩
      have hle : volume (interior r ∩ interior t) ≤ volume (r ∩ t) :=
        measure_mono (inter_subset_inter interior_subset interior_subset)
      rw [hae] at hle
      exact (not_lt_of_ge hle) hpos
    have hsub : (H '' r) ∩ (H '' t) ⊆ frontier (H '' r) ∪ frontier (H '' t) := by
      intro x hxin
      by_contra hn
      simp only [Set.mem_union, not_or] at hn
      have hxri : x ∈ interior (H '' r) := (mem_interior_iff_notMem_frontier hxin.1).2 hn.1
      have hxti : x ∈ interior (H '' t) := (mem_interior_iff_notMem_frontier hxin.2).2 hn.2
      rw [← H.image_interior] at hxri hxti
      obtain ⟨xr, hxr, hx⟩ := hxri
      obtain ⟨xt, hxt, hx'⟩ := hxti
      have : xr = xt := H.injective (hx.trans hx'.symm)
      exact (Set.disjoint_left.mp hinter) hxr (this ▸ hxt)
    apply measure_mono_null hsub
    rw [measure_union_null]
    · exact (hrect (H '' r) (Finset.mem_image.mpr ⟨r, hr, rfl⟩)).isPolygonal.volume_frontier
    · exact (hrect (H '' t) (Finset.mem_image.mpr ⟨t, ht, rfl⟩)).isPolygonal.volume_frontier
  refine ⟨{
    pieces := pieces
    isRectangle := hrect
    pairwiseAEDisjoint := hpair
    sUnion_eq := ?_ }, rfl⟩
  change ⋃₀ (pieces : Set (Set Tiling.Plane)) = H '' s
  rw [show (pieces : Set (Set Tiling.Plane)) =
      (fun r : Set Tiling.Plane => H '' r) '' (R.pieces : Set (Set Tiling.Plane)) by
        exact Finset.coe_image]
  rw [← Set.image_sUnion, R.sUnion_eq]

theorem coordinateProductImage_diam_le
    (K L : Region) (H : Tiling.Plane ≃ₜ Tiling.Plane) (δ : ℝ)
    (hδ : 0 ≤ δ) (_hsupport : L.support = H '' K.support)
    (hvertices : L.vertices = H '' K.vertices)
    (hmove : ∀ v ∈ K.vertices, dist (H v) v ≤ δ) :
    Metric.diam L.openCarrier ≤ Metric.diam K.openCarrier + 2 * δ := by
  apply Metric.diam_le_of_forall_dist_le (add_nonneg Metric.diam_nonneg (mul_nonneg zero_le_two hδ))
  intro x hx y hy
  have hxS : x ∈ L.support := interior_subset hx
  have hyS : y ∈ L.support := interior_subset hy
  obtain ⟨v, hv, w, hw, hxy⟩ := exists_vertices_controlling_distance L x y hxS hyS
  rw [hvertices] at hv hw
  obtain ⟨v0, hv0, rfl⟩ := hv
  obtain ⟨w0, hw0, rfl⟩ := hw
  calc
    dist x y ≤ dist (H v0) (H w0) := hxy
    dist (H v0) (H w0) ≤ dist v0 w0 + dist (H v0) v0 + dist (H w0) w0 := by
      calc
        dist (H v0) (H w0) ≤ dist (H v0) v0 + dist v0 w0 + dist w0 (H w0) := by
          exact (dist_triangle4 (H v0) v0 w0 (H w0))
        _ = _ := by rw [dist_comm w0]; ring
    _ ≤ Metric.diam K.support + δ + δ := by
      gcongr
      · apply Metric.dist_le_diam_of_mem K.isPolygonal.isBounded
        · rw [← K.isPolygonal.closure_interior]
          exact frontier_subset_closure (region_vertices_subset_frontier K hv0)
        · rw [← K.isPolygonal.closure_interior]
          exact frontier_subset_closure (region_vertices_subset_frontier K hw0)
      · exact hmove v0 hv0
      · exact hmove w0 hw0
    _ = Metric.diam K.openCarrier + 2 * δ := by
      have hd : Metric.diam K.support = Metric.diam K.openCarrier := by
        change Metric.diam K.support = Metric.diam (interior K.support)
        nth_rewrite 1 [← K.isPolygonal.closure_interior]
        exact Metric.diam_closure _
      rw [hd]
      ring

theorem region_openCarrier_diam_pos (K : Region) :
    0 < Metric.diam K.openCarrier := by
  obtain ⟨T⟩ := K.isPolygonal
  obtain ⟨x, hxK⟩ := K.nonempty
  rw [← T.sUnion_eq] at hxK
  obtain ⟨t, htT, hxt⟩ := Set.mem_sUnion.mp hxK
  have htFin : t ∈ T.pieces := htT
  have htSub : t ⊆ K.support := by
    rw [← T.sUnion_eq]
    exact Set.subset_sUnion_of_mem htT
  obtain ⟨p, hp⟩ := (T.isTriangle t htFin).interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior p hp
  let q : Tiling.Plane := p + (r / 2 : ℝ)
  have hqball : q ∈ Metric.ball p r := by
    rw [Metric.mem_ball, dist_eq_norm]
    simp [q, abs_of_pos hr]
    linarith
  have hpK : p ∈ K.openCarrier := interior_mono htSub hp
  have hqK : q ∈ K.openCarrier := interior_mono htSub (hball hqball)
  have hpq : p ≠ q := by
    intro h
    have := congrArg Complex.re h
    simp [q] at this
    linarith
  exact Metric.diam_pos ⟨p, hpK, q, hqK, hpq⟩
    (K.isPolygonal.isBounded.subset interior_subset)

private theorem region_openCarrier_regular (K : Region) :
    interior (closure K.openCarrier) = K.openCarrier := by
  change interior (closure (interior K.support)) = interior K.support
  rw [K.isPolygonal.closure_interior]

private theorem frontier_openCarrier_eq_support (K : Region) :
    frontier K.openCarrier = frontier K.support := by
  rw [frontier, frontier]
  change closure (interior K.support) \ interior (interior K.support) =
    closure K.support \ interior K.support
  rw [K.isPolygonal.closure_interior, interior_interior,
    K.isPolygonal.isClosed.closure_eq]

private theorem affineLine_eq_horizontal
    {x v : Tiling.Plane} (hv : v ≠ 0) (hvim : v.im = 0) :
    Tiling.affineLine x v = {z | z.im = x.im} := by
  have hvre : v.re ≠ 0 := by
    intro hvre
    apply hv
    apply Complex.ext <;> simp [hvre, hvim]
  ext z
  simp only [Tiling.mem_affineLine, Tiling.signedSide, Tiling.planarCross,
    mem_ofPred_eq, hvim, zero_mul, sub_zero]
  constructor
  · intro h
    apply (mul_left_cancel₀ hvre)
    linarith
  · intro h
    rw [h]
    ring

private theorem affineLine_eq_vertical
    {x v : Tiling.Plane} (hv : v ≠ 0) (hvre : v.re = 0) :
    Tiling.affineLine x v = {z | z.re = x.re} := by
  have hvim : v.im ≠ 0 := by
    intro hvim
    apply hv
    apply Complex.ext <;> simp [hvre, hvim]
  ext z
  simp only [Tiling.mem_affineLine, Tiling.signedSide, Tiling.planarCross,
    mem_ofPred_eq, hvre, zero_mul, zero_sub]
  constructor
  · intro h
    apply (mul_left_cancel₀ hvim)
    linarith
  · intro h
    rw [h]
    ring

private theorem boundaryStraight_axisGerm (K : Region) (x : Tiling.Plane)
    (hstraight : Tiling.BoundaryLocallyStraightAt K.openCarrier x) :
    (∀ᶠ z in nhds x, z ∈ frontier K.openCarrier ↔ z.re = x.re) ∨
      (∀ᶠ z in nhds x, z ∈ frontier K.openCarrier ↔ z.im = x.im) := by
  obtain ⟨L, hxL, hdim, hlocal⟩ := hstraight
  obtain ⟨v, hv, r, hr, hline⟩ :=
    Tiling.AffineSubspace.exists_ball_frontier_iff_affineLine hxL hdim hlocal
  obtain ⟨s, hs, hcross⟩ := K.isAxisParallel.localBoundaryCross x
  have hcross' : ∀ z ∈ Metric.ball x s, z ∈ frontier K.openCarrier →
      z.re = x.re ∨ z.im = x.im := by
    intro z hz hzfront
    apply hcross z hz
    rw [← frontier_openCarrier_eq_support K]
    exact hzfront
  let t : ℝ := min r s / (2 * (‖v‖ + 1))
  have ht : 0 < t := by dsimp only [t]; positivity
  have htNorm : t * ‖v‖ < min r s := by
    dsimp only [t]
    have hvnorm : 0 ≤ ‖v‖ := norm_nonneg v
    have hmin : 0 < min r s := lt_min hr hs
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).2
    nlinarith
  let z : Tiling.Plane := x + t • v
  have hzDist : dist z x = t * ‖v‖ := by
    simp only [z, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht]
  have hzR : z ∈ Metric.ball x r := by
    rw [Metric.mem_ball, hzDist]
    exact htNorm.trans_le (min_le_left r s)
  have hzS : z ∈ Metric.ball x s := by
    rw [Metric.mem_ball, hzDist]
    exact htNorm.trans_le (min_le_right r s)
  have hzFront : z ∈ frontier K.openCarrier :=
    (hline z hzR).2 (Tiling.vadd_smul_mem_affineLine x v t)
  have hvCoord : v.re = 0 ∨ v.im = 0 := by
    rcases hcross' z hzS hzFront with hzre | hzim
    · left
      have : t * v.re = 0 := by
        simpa only [z, Complex.add_re, Complex.smul_re, smul_eq_mul,
          add_eq_left] using hzre
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
    · right
      have : t * v.im = 0 := by
        simpa only [z, Complex.add_im, Complex.smul_im, smul_eq_mul,
          add_eq_left] using hzim
      exact (mul_eq_zero.mp this).resolve_left ht.ne'
  rcases hvCoord with hvre | hvim
  · left
    filter_upwards [Metric.ball_mem_nhds x (lt_min hr hs)] with w hw
    have hwR := Metric.ball_subset_ball (min_le_left r s) hw
    simpa only [affineLine_eq_vertical hv hvre, mem_ofPred_eq] using hline w hwR
  · right
    filter_upwards [Metric.ball_mem_nhds x (lt_min hr hs)] with w hw
    have hwR := Metric.ball_subset_ball (min_le_left r s) hw
    simpa only [affineLine_eq_horizontal hv hvim, mem_ofPred_eq] using hline w hwR

theorem boundaryLocallyStraightAt_coordinateProduct_iff
    (K L : Region) (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy)
    (hopen : L.openCarrier = coordinateProductHomeomorph hx hy '' K.openCarrier)
    (x : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt K.openCarrier x ↔
      Tiling.BoundaryLocallyStraightAt L.openCarrier
        (coordinateProductHomeomorph hx hy x) := by
  let H := coordinateProductHomeomorph hx hy
  have transport (K L : Region) (hx hy : ℝ ≃ₜ ℝ)
      (hhx : StrictMono hx) (hhy : StrictMono hy)
      (hopen : L.openCarrier = coordinateProductHomeomorph hx hy '' K.openCarrier)
      (x : Tiling.Plane) (hstraight : Tiling.BoundaryLocallyStraightAt K.openCarrier x) :
      Tiling.BoundaryLocallyStraightAt L.openCarrier
        (coordinateProductHomeomorph hx hy x) := by
    let H := coordinateProductHomeomorph hx hy
    change Tiling.BoundaryLocallyStraightAt L.openCarrier (H x)
    rcases boundaryStraight_axisGerm K x hstraight with hg | hg
    · let M : AffineSubspace ℝ Tiling.Plane :=
        AffineSubspace.mk' (H x) (ℝ ∙ Complex.I)
      refine ⟨M, AffineSubspace.self_mem_mk' _ _, by
        rw [AffineSubspace.direction_mk']
        exact finrank_span_singleton Complex.I_ne_zero, ?_⟩
      have ht : Filter.Tendsto H.symm (nhds (H x)) (nhds x) :=
        by
          have ht0 := H.symm.continuous.continuousAt (x := H x)
          change Filter.Tendsto H.symm (nhds (H x)) (nhds (H.symm (H x))) at ht0
          rwa [H.symm_apply_apply] at ht0
      filter_upwards [ht.eventually hg] with z hz
      have hfront : z ∈ frontier L.openCarrier ↔ H.symm z ∈ frontier K.openCarrier := by
        rw [hopen, ← H.image_frontier]
        constructor
        · rintro ⟨y, hyf, hyz⟩
          simpa [← hyz] using hyf
        · intro hyf
          exact ⟨H.symm z, hyf, H.apply_symm_apply z⟩
      rw [hfront, hz]
      change (H.symm z).re = x.re ↔ z ∈ M
      rw [coordinateProductHomeomorph_symm_re]
      change hx.symm z.re = x.re ↔ z - H x ∈ ℝ ∙ Complex.I
      rw [Submodule.mem_span_singleton]
      constructor
      · intro hre
        refine ⟨z.im - (H x).im, ?_⟩
        apply Complex.ext
        · have := congrArg hx hre
          simp only [hx.apply_symm_apply] at this
          simp [H, coordinateProductHomeomorph_apply]
          linarith
        · simp
      · rintro ⟨a, ha⟩
        have hzre : z.re = (H x).re := by
          have := congrArg Complex.re ha
          simp at this
          linarith
        apply hx.injective
        simpa [H, coordinateProductHomeomorph_apply] using hzre
    · let M : AffineSubspace ℝ Tiling.Plane :=
        AffineSubspace.mk' (H x) (ℝ ∙ (1 : Tiling.Plane))
      refine ⟨M, AffineSubspace.self_mem_mk' _ _, by
        rw [AffineSubspace.direction_mk']
        exact finrank_span_singleton one_ne_zero, ?_⟩
      have ht : Filter.Tendsto H.symm (nhds (H x)) (nhds x) :=
        by
          have ht0 := H.symm.continuous.continuousAt (x := H x)
          change Filter.Tendsto H.symm (nhds (H x)) (nhds (H.symm (H x))) at ht0
          rwa [H.symm_apply_apply] at ht0
      filter_upwards [ht.eventually hg] with z hz
      have hfront : z ∈ frontier L.openCarrier ↔ H.symm z ∈ frontier K.openCarrier := by
        rw [hopen, ← H.image_frontier]
        constructor
        · rintro ⟨y, hyf, hyz⟩
          simpa [← hyz] using hyf
        · intro hyf
          exact ⟨H.symm z, hyf, H.apply_symm_apply z⟩
      rw [hfront, hz]
      change (H.symm z).im = x.im ↔ z ∈ M
      rw [coordinateProductHomeomorph_symm_im]
      change hy.symm z.im = x.im ↔ z - H x ∈ ℝ ∙ (1 : Tiling.Plane)
      rw [Submodule.mem_span_singleton]
      constructor
      · intro him
        refine ⟨z.re - (H x).re, ?_⟩
        apply Complex.ext
        · simp
        · have := congrArg hy him
          simp only [hy.apply_symm_apply] at this
          simp [H, coordinateProductHomeomorph_apply]
          linarith
      · rintro ⟨a, ha⟩
        have hzim : z.im = (H x).im := by
          have := congrArg Complex.im ha
          simp at this
          linarith
        apply hy.injective
        simpa [H, coordinateProductHomeomorph_apply] using hzim
  constructor
  · exact transport K L hx hy hhx hhy hopen x
  · intro h
    have hInv : coordinateProductHomeomorph hx.symm hy.symm = H.symm := by
      apply Homeomorph.ext
      intro z
      apply H.injective
      apply Complex.ext <;> simp [H, coordinateProductHomeomorph_apply]
    have hinv : K.openCarrier =
        coordinateProductHomeomorph hx.symm hy.symm '' L.openCarrier := by
      rw [hInv, hopen]
      exact (H.symm_image_image K.openCarrier).symm
    have hhx' : StrictMono hx.symm := by
      intro a b hab
      apply (hhx.lt_iff_lt).mp
      simpa using hab
    have hhy' : StrictMono hy.symm := by
      intro a b hab
      apply (hhy.lt_iff_lt).mp
      simpa using hab
    have hback := transport L K hx.symm hy.symm hhx' hhy'
      hinv (H x) h
    rw [hInv] at hback
    simpa [H] using hback

theorem exists_coordinateProductImageRegion
    (K : Region) (hx hy : ℝ ≃ₜ ℝ) (hhx : StrictMono hx) (hhy : StrictMono hy) :
    ∃ L : Region,
      L.support = coordinateProductHomeomorph hx hy '' K.support ∧
      L.openCarrier = coordinateProductHomeomorph hx hy '' K.openCarrier ∧
      L.vertices = coordinateProductHomeomorph hx hy '' K.vertices := by
  let H := coordinateProductHomeomorph hx hy
  obtain ⟨R⟩ := K.isAxisParallel
  obtain ⟨R', hR'⟩ := coordinateProductHomeomorph_rectangulation R hx hy hhx hhy
  let L : Region := {
    support := H '' K.support
    isPolygonal := isPolygonal_of_isAxisParallel ⟨R'⟩
    nonempty := K.nonempty.image H
    isAxisParallel := ⟨R'⟩ }
  have hopen : L.openCarrier = H '' K.openCarrier := by
    change interior (H '' K.support) = H '' interior K.support
    exact (H.image_interior K.support).symm
  refine ⟨L, rfl, hopen, ?_⟩
  rw [region_vertices_eq_nonStraightBoundary L,
    region_vertices_eq_nonStraightBoundary K]
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hzfront, hznot⟩
    have hzfront' : z ∈ H '' frontier K.openCarrier := by
      rw [H.image_frontier, ← hopen]
      exact hzfront
    obtain ⟨x, hxfront, rfl⟩ := hzfront'
    refine ⟨x, ⟨hxfront, ?_⟩, rfl⟩
    intro hs
    exact hznot ((boundaryLocallyStraightAt_coordinateProduct_iff
      K L hx hy hhx hhy hopen x).mp hs)
  · rintro ⟨x, ⟨hxfront, hxnot⟩, rfl⟩
    constructor
    · change H x ∈ frontier L.openCarrier
      rw [hopen, ← H.image_frontier]
      exact ⟨x, hxfront, rfl⟩
    · intro hs
      exact hxnot ((boundaryLocallyStraightAt_coordinateProduct_iff
        K L hx hy hhx hhy hopen x).mpr hs)

private theorem regularOpen_eq_of_eqOn_dense
    {s t d : Set Tiling.Plane}
    (hsOpen : IsOpen s) (hsRegular : interior (closure s) = s)
    (htOpen : IsOpen t) (htRegular : interior (closure t) = t)
    (hd : Dense d) (hEq : ∀ z ∈ d, z ∈ s ↔ z ∈ t) : s = t := by
  apply Set.Subset.antisymm
  · rw [← htRegular]
    apply interior_maximal _ hsOpen
    intro z hz
    apply closure_mono (fun x (hx : x ∈ s ∩ d) => (hEq x hx.2).mp hx.1)
    exact hd.open_subset_closure_inter hsOpen hz
  · rw [← hsRegular]
    apply interior_maximal _ htOpen
    intro z hz
    apply closure_mono (fun x (hx : x ∈ t ∩ d) => (hEq x hx.2).mpr hx.1)
    exact hd.open_subset_closure_inter htOpen hz

theorem coordinateProductImage_openCarrier_unique
    (K : Region) (hx₁ hy₁ hx₂ hy₂ : ℝ ≃ₜ ℝ)
    (hmx₁ : StrictMono hx₁) (hmy₁ : StrictMono hy₁)
    (hmx₂ : StrictMono hx₂) (hmy₂ : StrictMono hy₂)
    (hex : ∀ v ∈ K.vertices, hx₁ v.re = hx₂ v.re)
    (hey : ∀ v ∈ K.vertices, hy₁ v.im = hy₂ v.im) :
    coordinateProductHomeomorph hx₁ hy₁ '' K.openCarrier =
      coordinateProductHomeomorph hx₂ hy₂ '' K.openCarrier := by
  let H1 := coordinateProductHomeomorph hx₁ hy₁
  let H2 := coordinateProductHomeomorph hx₂ hy₂
  let A : Set ℝ := hx₁ '' (Complex.re '' K.vertices)
  let B : Set ℝ := hy₁ '' (Complex.im '' K.vertices)
  let d : Set Tiling.Plane := Complex.re ⁻¹' Aᶜ ∩ Complex.im ⁻¹' Bᶜ
  have hAfin : A.Finite := (K.isPolygonal.vertexSet_finite.image Complex.re).image hx₁
  have hBfin : B.Finite := (K.isPolygonal.vertexSet_finite.image Complex.im).image hy₁
  have hAcomp : Dense Aᶜ := by
    rw [← show (Set.univ : Set ℝ) \ A = Aᶜ by ext; simp]
    exact dense_univ.sdiff_finite hAfin
  have hBcomp : Dense Bᶜ := by
    rw [← show (Set.univ : Set ℝ) \ B = Bᶜ by ext; simp]
    exact dense_univ.sdiff_finite hBfin
  have hdre : Dense (Complex.re ⁻¹' Aᶜ) := hAcomp.preimage Complex.isOpenMap_re
  have hdim : Dense (Complex.im ⁻¹' Bᶜ) := hBcomp.preimage Complex.isOpenMap_im
  have hdreOpen : IsOpen (Complex.re ⁻¹' Aᶜ) :=
    hAfin.isClosed.isOpen_compl.preimage Complex.continuous_re
  have hd : Dense d := hdre.inter_of_isOpen_left hdim hdreOpen
  have hopen1 : IsOpen (H1 '' K.openCarrier) := H1.isOpenMap _ isOpen_interior
  have hopen2 : IsOpen (H2 '' K.openCarrier) := H2.isOpenMap _ isOpen_interior
  have hreg1 : interior (closure (H1 '' K.openCarrier)) = H1 '' K.openCarrier := by
    rw [← H1.image_closure, ← H1.image_interior, region_openCarrier_regular]
  have hreg2 : interior (closure (H2 '' K.openCarrier)) = H2 '' K.openCarrier := by
    rw [← H2.image_closure, ← H2.image_interior, region_openCarrier_regular]
  apply regularOpen_eq_of_eqOn_dense hopen1 hreg1 hopen2 hreg2 hd
  intro z hz
  have hoff : ∀ v ∈ K.vertices, z.re ≠ hx₁ v.re ∧ z.im ≠ hy₁ v.im := by
    intro v hv
    constructor
    · intro h
      exact hz.1 ⟨v.re, ⟨v, hv, rfl⟩, h.symm⟩
    · intro h
      exact hz.2 ⟨v.im, ⟨v, hv, rfl⟩, h.symm⟩
  have hoffinv := inverse_offVertexGrid_of_target_offGrid K hx₁ hy₁ hx₂ hy₂
    hmx₁ hmy₁ hmx₂ hmy₂ hex hey z hoff
  have hsame := inverse_preserves_vertexGridComparisons K hx₁ hy₁ hx₂ hy₂
    hmx₁ hmy₁ hmx₂ hmy₂ hex hey z
  have hmem := sameVertexGridCell_openCarrier_iff K (H1.symm z) (H2.symm z)
    hoffinv.1 hoffinv.2 hsame
  constructor
  · rintro ⟨x, hx, hxz⟩
    have hxinv : H1.symm z ∈ K.openCarrier := by
      rw [← hxz, H1.symm_apply_apply]
      exact hx
    exact ⟨H2.symm z, hmem.mp hxinv, H2.apply_symm_apply z⟩
  · rintro ⟨x, hx, hxz⟩
    have hxinv : H2.symm z ∈ K.openCarrier := by
      rw [← hxz, H2.symm_apply_apply]
      exact hx
    exact ⟨H1.symm z, hmem.mpr hxinv, H1.apply_symm_apply z⟩


end Tiling.AxisParallel.Approximation
