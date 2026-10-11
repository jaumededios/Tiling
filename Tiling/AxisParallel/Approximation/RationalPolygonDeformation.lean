import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.DeformationCore
import Tiling.AxisParallel.Approximation.CoordinateExtension
import Tiling.AxisParallel.Approximation.RectangularRegionImage
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.Geometry.PolygonalTopology
import Mathlib.Topology.Homeomorph.Lemmas

open Set

namespace Tiling.AxisParallel.Approximation

noncomputable section

/-- The planar homeomorphism restricts to an equivalence of the two vertex sets. -/
def CoordinateDeformation.vertexEquiv
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    {v : Tiling.Plane // v ∈ C.region.vertices} ≃
      {w : Tiling.Plane // w ∈ D.deformedRegion.vertices} :=
  Equiv.ofBijective
    (fun v ↦ ⟨D.planarHomeomorph v, by
      rw [D.vertices_image]
      exact ⟨v, v.2, rfl⟩⟩)
    ⟨fun v w h ↦ Subtype.ext (D.planarHomeomorph.injective (congrArg Subtype.val h)),
      fun w ↦ by
        have hw : (w : Tiling.Plane) ∈
            D.planarHomeomorph '' C.region.vertices := by
          rw [← D.vertices_image]
          exact w.2
        obtain ⟨v, hv, hvw⟩ := hw
        refine ⟨⟨v, hv⟩, ?_⟩
        apply Subtype.ext
        exact hvw⟩

theorem CoordinateDeformation.vertexEquiv_apply
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ)
    (v : {v : Tiling.Plane // v ∈ C.region.vertices}) :
    (D.vertexEquiv v : Tiling.Plane) = D.planarHomeomorph v := rfl

/-- A homeomorphism carries the source frontier to the deformed frontier. -/
theorem CoordinateDeformation.frontier_image
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    frontier D.deformedRegion.openCarrier =
      D.planarHomeomorph '' frontier C.region.openCarrier := by
  rw [D.deformedRegion_openCarrier]
  exact (D.planarHomeomorph.image_frontier C.region.openCarrier).symm

private theorem Region.openCarrier_regular (K : Tiling.AxisParallel.Region) :
    interior (closure K.openCarrier) = K.openCarrier := by
  change interior (closure (interior K.support)) = interior K.support
  rw [K.isPolygonal.closure_interior]

private theorem regularOpen_eq_of_eqOn_dense
    {s t d : Set Tiling.Plane}
    (hsOpen : IsOpen s) (hsRegular : interior (closure s) = s)
    (htOpen : IsOpen t) (htRegular : interior (closure t) = t)
    (hd : Dense d) (hEq : ∀ z ∈ d, z ∈ s ↔ z ∈ t) : s = t := by
  apply Set.Subset.antisymm
  · rw [← htRegular]
    apply interior_maximal _ hsOpen
    intro z hz
    have hzClosure : z ∈ closure (s ∩ d) := hd.open_subset_closure_inter hsOpen hz
    apply closure_mono _ hzClosure
    rintro x ⟨hxs, hxd⟩
    exact (hEq x hxd).mp hxs
  · rw [← hsRegular]
    apply interior_maximal _ htOpen
    intro z hz
    have hzClosure : z ∈ closure (t ∩ d) := hd.open_subset_closure_inter htOpen hz
    apply closure_mono _ hzClosure
    rintro x ⟨hxt, hxd⟩
    exact (hEq x hxd).mpr hxt

/-- Two regular-open polygonal carriers agreeing off the source vertex grid are equal. -/
theorem region_eq_of_gridCellCode_eq
    (K L : Tiling.AxisParallel.Region) (H : Tiling.Plane ≃ₜ Tiling.Plane)
    (hcell : ∀ z : Tiling.Plane,
      (∀ v ∈ K.vertices, z.re ≠ v.re ∧ z.im ≠ v.im) →
      (z ∈ K.openCarrier ↔ H z ∈ L.openCarrier)) :
    H '' K.openCarrier = L.openCarrier := by
  let A : Set ℝ := Complex.re '' K.vertices
  let B : Set ℝ := Complex.im '' K.vertices
  let d : Set Tiling.Plane := Complex.re ⁻¹' Aᶜ ∩ Complex.im ⁻¹' Bᶜ
  have hAfin : A.Finite := by
    apply (K.isPolygonal.vertexSet_finite.image Complex.re)
  have hBfin : B.Finite := by
    apply (K.isPolygonal.vertexSet_finite.image Complex.im)
  have hAcomp : Dense Aᶜ := by
    have heq : (Set.univ : Set ℝ) \ A = Aᶜ := by ext; simp
    rw [← heq]
    exact dense_univ.sdiff_finite hAfin
  have hBcomp : Dense Bᶜ := by
    have heq : (Set.univ : Set ℝ) \ B = Bᶜ := by ext; simp
    rw [← heq]
    exact dense_univ.sdiff_finite hBfin
  have hdre : Dense (Complex.re ⁻¹' Aᶜ) :=
    hAcomp.preimage Complex.isOpenMap_re
  have hdim : Dense (Complex.im ⁻¹' Bᶜ) :=
    hBcomp.preimage Complex.isOpenMap_im
  have hdreOpen : IsOpen (Complex.re ⁻¹' Aᶜ) :=
    hAfin.isClosed.isOpen_compl.preimage Complex.continuous_re
  have hd : Dense d := hdre.inter_of_isOpen_left hdim hdreOpen
  have hpreOpen : IsOpen (H ⁻¹' L.openCarrier) :=
    isOpen_interior.preimage H.continuous
  have hpreRegular :
      interior (closure (H ⁻¹' L.openCarrier)) = H ⁻¹' L.openCarrier := by
    rw [← H.preimage_closure, ← H.preimage_interior, Region.openCarrier_regular]
  have hagree : ∀ z ∈ d, z ∈ K.openCarrier ↔ z ∈ H ⁻¹' L.openCarrier := by
    intro z hz
    apply hcell z
    intro v hv
    refine ⟨?_, ?_⟩
    · intro hzv
      exact hz.1 ⟨v, hv, hzv.symm⟩
    · intro hzv
      exact hz.2 ⟨v, hv, hzv.symm⟩
  have hpre : K.openCarrier = H ⁻¹' L.openCarrier :=
    regularOpen_eq_of_eqOn_dense isOpen_interior (Region.openCarrier_regular K)
      hpreOpen hpreRegular hd hagree
  exact (H.toEquiv.eq_preimage_iff_image_eq K.openCarrier L.openCarrier).mp hpre

private theorem openSegment_self_real (x : ℝ) : openSegment ℝ x x = {x} := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    change z = x
    rw [← hz]
    simp only [smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · intro hz
    have hz' : z = x := by simpa using hz
    subst z
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ring

private theorem strictMono_image_openSegment (h : ℝ ≃ₜ ℝ) (hh : StrictMono h)
    (x y : ℝ) :
    h '' openSegment ℝ x y = openSegment ℝ (h x) (h y) := by
  by_cases hxy : x = y
  · subst y
    rw [openSegment_self_real, openSegment_self_real]
    simp
  · rcases lt_or_gt_of_ne hxy with hxy | hyx
    · rw [openSegment_eq_Ioo hxy, openSegment_eq_Ioo (hh hxy)]
      exact h.continuous.image_Ioo_of_strictMono hh
    · rw [openSegment_symm ℝ x y, openSegment_symm ℝ (h x) (h y),
        openSegment_eq_Ioo hyx, openSegment_eq_Ioo (hh hyx)]
      exact h.continuous.image_Ioo_of_strictMono hh

private theorem openSegment_eq_vertical (v w : Tiling.Plane) (h : v.re = w.re) :
    openSegment ℝ v w =
      (fun y : ℝ ↦ (v.re : ℂ) + (y : ℂ) * Complex.I) ''
        openSegment ℝ v.im w.im := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨z.im, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : a * r + b * r = r := by
        rw [← add_mul, hab, one_mul]
      apply Complex.ext <;> simp [h, hweighted]
  · rintro ⟨y, ⟨a, b, ha, hb, hab, hy⟩, rfl⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hweighted (r : ℝ) : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    apply Complex.ext
    · simp [h, hweighted]
    · simpa using hy

private theorem openSegment_eq_horizontal (v w : Tiling.Plane) (h : v.im = w.im) :
    openSegment ℝ v w =
      (fun x : ℝ ↦ (x : ℂ) + (v.im : ℂ) * Complex.I) ''
        openSegment ℝ v.re w.re := by
  ext z
  constructor
  · rintro ⟨a, b, ha, hb, hab, hz⟩
    refine ⟨z.re, ⟨a, b, ha, hb, hab, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : a * r + b * r = r := by
        rw [← add_mul, hab, one_mul]
      apply Complex.ext <;> simp [h, hweighted]
  · rintro ⟨x, ⟨a, b, ha, hb, hab, hx⟩, rfl⟩
    refine ⟨a, b, ha, hb, hab, ?_⟩
    have hweighted (r : ℝ) : a * r + b * r = r := by
      rw [← add_mul, hab, one_mul]
    apply Complex.ext
    · simpa using hx
    · simp [h, hweighted]

/-- A coordinatewise increasing deformation maps every axis-aligned open segment exactly. -/
theorem CoordinateDeformation.image_openSegment_of_axisAligned
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (v w : Tiling.Plane)
    (haxis : v.re = w.re ∨ v.im = w.im) :
    D.planarHomeomorph '' openSegment ℝ v w =
      openSegment ℝ (D.planarHomeomorph v) (D.planarHomeomorph w) := by
  rcases haxis with hre | him
  · have hre' : (D.planarHomeomorph v).re = (D.planarHomeomorph w).re := by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp [hre]
    rw [openSegment_eq_vertical v w hre,
      openSegment_eq_vertical (D.planarHomeomorph v) (D.planarHomeomorph w) hre',
      Set.image_image]
    calc
      (D.planarHomeomorph ∘ fun y : ℝ ↦ (v.re : ℂ) + (y : ℂ) * Complex.I) ''
          openSegment ℝ v.im w.im =
          (fun y : ℝ ↦ (D.firstHomeomorph v.re : ℂ) +
            (D.secondHomeomorph y : ℂ) * Complex.I) '' openSegment ℝ v.im w.im := by
            congr 1
            funext y
            rw [Function.comp_apply, D.planarHomeomorph_apply]
            apply Complex.ext <;> simp
      _ = (fun y : ℝ ↦ (D.firstHomeomorph v.re : ℂ) + (y : ℂ) * Complex.I) ''
          (D.secondHomeomorph '' openSegment ℝ v.im w.im) := by
            rw [Set.image_image]
      _ = (fun y : ℝ ↦ (D.firstHomeomorph v.re : ℂ) + (y : ℂ) * Complex.I) ''
          openSegment ℝ (D.secondHomeomorph v.im) (D.secondHomeomorph w.im) := by
            rw [strictMono_image_openSegment D.secondHomeomorph
              D.secondHomeomorph_strictMono]
      _ = (fun y : ℝ ↦ ((D.planarHomeomorph v).re : ℂ) + (y : ℂ) * Complex.I) ''
          openSegment ℝ (D.planarHomeomorph v).im (D.planarHomeomorph w).im := by
            congr 1
            · funext y
              rw [D.planarHomeomorph_apply]
              simp
            · congr 2 <;> rw [D.planarHomeomorph_apply] <;> simp
  · have him' : (D.planarHomeomorph v).im = (D.planarHomeomorph w).im := by
      rw [D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp [him]
    rw [openSegment_eq_horizontal v w him,
      openSegment_eq_horizontal (D.planarHomeomorph v) (D.planarHomeomorph w) him',
      Set.image_image]
    calc
      (D.planarHomeomorph ∘ fun x : ℝ ↦ (x : ℂ) + (v.im : ℂ) * Complex.I) ''
          openSegment ℝ v.re w.re =
          (fun x : ℝ ↦ (D.firstHomeomorph x : ℂ) +
            (D.secondHomeomorph v.im : ℂ) * Complex.I) '' openSegment ℝ v.re w.re := by
            congr 1
            funext x
            rw [Function.comp_apply, D.planarHomeomorph_apply]
            apply Complex.ext <;> simp
      _ = (fun x : ℝ ↦ (x : ℂ) +
          (D.secondHomeomorph v.im : ℂ) * Complex.I) ''
          (D.firstHomeomorph '' openSegment ℝ v.re w.re) := by
            rw [Set.image_image]
      _ = (fun x : ℝ ↦ (x : ℂ) +
          (D.secondHomeomorph v.im : ℂ) * Complex.I) ''
          openSegment ℝ (D.firstHomeomorph v.re) (D.firstHomeomorph w.re) := by
            rw [strictMono_image_openSegment D.firstHomeomorph
              D.firstHomeomorph_strictMono]
      _ = (fun x : ℝ ↦ (x : ℂ) +
          ((D.planarHomeomorph v).im : ℂ) * Complex.I) ''
          openSegment ℝ (D.planarHomeomorph v).re (D.planarHomeomorph w).re := by
            congr 1
            · funext x
              rw [D.planarHomeomorph_apply]
              simp
            · congr 2 <;> rw [D.planarHomeomorph_apply] <;> simp

end

noncomputable section

universe u

private def coordinateLevels (K : Region) (axis : Axis) : Finset ℝ :=
  K.vertexFinset.image (Axis.coord axis)

private def vertexCoordinateLevel (K : Region) (axis : Axis)
    (v : ↥K.vertices) : ↥(coordinateLevels K axis) := by
  refine ⟨Axis.coord axis v.1, ?_⟩
  rw [coordinateLevels, Finset.mem_image]
  refine ⟨v.1, ?_, rfl⟩
  change v.1 ∈ (K.vertexFinset : Set Tiling.Plane)
  rw [K.coe_vertexFinset]
  exact v.2

/-- Coordinate deformation preserves and reflects intrinsic horizontal boundary sides. -/
public theorem intrinsicHorizontalSide_transport
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (v w : C.region.vertices) :
    (v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
      openSegment ℝ v.1 w.1 ⊆ frontier C.region.support \ C.region.vertices) ↔
      ∃ _hv : Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v.1 v.2) ∈ D.deformedRegion.vertices,
      ∃ _hw : Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w.1 w.2) ∈ D.deformedRegion.vertices,
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) ≠
          Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) ∧
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2)).im =
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2)).im ∧
          openSegment ℝ
              (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2))
              (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2)) ⊆
            frontier D.deformedRegion.support \ D.deformedRegion.vertices) := by
  have hfrontier : frontier D.deformedRegion.support =
      D.planarHomeomorph '' frontier C.region.support := by
    rw [region_support_image_of_openCarrier_image C.region D.deformedRegion
      D.planarHomeomorph D.deformedRegion_openCarrier]
    exact (D.planarHomeomorph.image_frontier C.region.support).symm
  have hvD : Tiling.AxisParallel.Approximation.mapPoint phi
      (C.vertexPoint v.1 v.2) ∈ D.deformedRegion.vertices := by
    rw [← D.vertex_agreement v.1 v.2, D.vertices_image]
    exact ⟨v.1, v.2, rfl⟩
  have hwD : Tiling.AxisParallel.Approximation.mapPoint phi
      (C.vertexPoint w.1 w.2) ∈ D.deformedRegion.vertices := by
    rw [← D.vertex_agreement w.1 w.2, D.vertices_image]
    exact ⟨w.1, w.2, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro ⟨hvw, him, hside⟩
    refine ⟨hvD, hwD, ?_, ?_, ?_⟩
    · intro heq
      have hplanar : D.planarHomeomorph v.1 = D.planarHomeomorph w.1 := by
        rw [D.vertex_agreement v.1 v.2, D.vertex_agreement w.1 w.2]
        exact heq
      exact hvw (D.planarHomeomorph.injective hplanar)
    · rw [← D.vertex_agreement v.1 v.2,
        ← D.vertex_agreement w.1 w.2,
        D.planarHomeomorph_apply, D.planarHomeomorph_apply]
      simp [him]
    · intro z hz
      have himage : z ∈ D.planarHomeomorph '' openSegment ℝ v.1 w.1 := by
        rw [D.image_openSegment_of_axisAligned v.1 w.1 (Or.inr him)]
        simpa only [D.vertex_agreement v.1 v.2,
          D.vertex_agreement w.1 w.2] using hz
      obtain ⟨x, hxseg, hxz⟩ := himage
      have hxside := hside hxseg
      constructor
      · rw [hfrontier]
        refine ⟨x, ?_, hxz⟩
        exact hxside.1
      · intro hzvertex
        rw [D.vertices_image] at hzvertex
        obtain ⟨y, hyvertex, hyz⟩ := hzvertex
        have hxy : x = y := D.planarHomeomorph.injective (hxz.trans hyz.symm)
        exact hxside.2 (hxy ▸ hyvertex)
  · rintro ⟨_hv, _hw, hmappedNe, hmappedIm, hmappedSide⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hvw
      apply hmappedNe
      rw [← D.vertex_agreement v.1 v.2,
        ← D.vertex_agreement w.1 w.2, hvw]
    · have hsecond : D.secondHomeomorph v.1.im =
          D.secondHomeomorph w.1.im := by
        change (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2)).im =
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2)).im at hmappedIm
        rw [← D.vertex_agreement v.1 v.2,
          ← D.vertex_agreement w.1 w.2,
          D.planarHomeomorph_apply, D.planarHomeomorph_apply] at hmappedIm
        simpa using hmappedIm
      exact D.secondHomeomorph.injective hsecond
    · intro x hx
      have him : v.1.im = w.1.im := by
        have hsecond : D.secondHomeomorph v.1.im =
            D.secondHomeomorph w.1.im := by
          change (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2)).im =
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2)).im at hmappedIm
          rw [← D.vertex_agreement v.1 v.2,
            ← D.vertex_agreement w.1 w.2,
            D.planarHomeomorph_apply, D.planarHomeomorph_apply] at hmappedIm
          simpa using hmappedIm
        exact D.secondHomeomorph.injective hsecond
      have hzseg : D.planarHomeomorph x ∈
          openSegment ℝ
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2))
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2)) := by
        rw [← D.vertex_agreement v.1 v.2,
          ← D.vertex_agreement w.1 w.2,
          ← D.image_openSegment_of_axisAligned v.1 w.1 (Or.inr him)]
        exact ⟨x, hx, rfl⟩
      have hzside := hmappedSide hzseg
      constructor
      · have hzfront := hzside.1
        rw [hfrontier] at hzfront
        obtain ⟨y, hyfront, hyx⟩ := hzfront
        have hy : y = x := D.planarHomeomorph.injective hyx
        simpa only [hy] using hyfront
      · intro hxvertex
        apply hzside.2
        rw [D.vertices_image]
        exact ⟨x, hxvertex, rfl⟩

private theorem mappedCoord_sub
    {C : ApproximationContext.{u}} (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (axis : Axis) (v w : Tiling.Plane) (hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices) :
    Axis.coord axis
        (mapPoint φ (C.vertexPoint v hv) - mapPoint φ (C.vertexPoint w hw)) =
      Axis.coord axis (mapPoint φ (C.vertexPoint v hv)) -
        Axis.coord axis (mapPoint φ (C.vertexPoint w hw)) := by
  cases axis <;> simp [Axis.coord]

private theorem sourceCoord_sub (axis : Axis) (v w : Tiling.Plane) :
    Axis.coord axis (v - w) = Axis.coord axis v - Axis.coord axis w := by
  cases axis <;> simp [Axis.coord]

private theorem positive_of_same_sign {x y : ℝ}
    (h : Real.sign x = Real.sign y) (hy : 0 < y) : 0 < x := by
  rw [Real.sign_of_pos hy] at h
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx] at h
    norm_num at h
  · simp at h
  · exact hx

private theorem exists_strictMono_vertexCoordinateMap
    (C : ApproximationContext.{u}) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hφ : IsGoodApproximation C φ) (axis : Axis) :
    ∃ f : ↥(coordinateLevels C.region axis) → ℝ,
      StrictMono f ∧ ∀ v : ↥C.region.vertices,
        f (vertexCoordinateLevel C.region axis v) =
          Axis.coord axis (mapPoint φ (C.vertexPoint v.1 v.2)) := by
  classical
  let repVal : ↥(coordinateLevels C.region axis) → Tiling.Plane := fun x =>
    Classical.choose (Finset.mem_image.mp x.2)
  have repVal_mem (x) : repVal x ∈ C.region.vertexFinset :=
    (Classical.choose_spec (Finset.mem_image.mp x.2)).1
  let rep : ↥(coordinateLevels C.region axis) → ↥C.region.vertices := fun x =>
    ⟨repVal x, by
      rw [← C.region.coe_vertexFinset]
      exact repVal_mem x⟩
  let f : ↥(coordinateLevels C.region axis) → ℝ := fun x =>
    Axis.coord axis (mapPoint φ (C.vertexPoint (rep x).1 (rep x).2))
  have hrep (x) : Axis.coord axis (rep x).1 = x.1 := by
    dsimp [rep]
    exact (Classical.choose_spec (Finset.mem_image.mp x.2)).2
  have hind (v w : ↥C.region.vertices)
      (hvw : Axis.coord axis v.1 = Axis.coord axis w.1) :
      Axis.coord axis (mapPoint φ (C.vertexPoint v.1 v.2)) =
        Axis.coord axis (mapPoint φ (C.vertexPoint w.1 w.2)) := by
    have hs := hφ.preservesVertexCoordinateSign axis v.1 w.1 v.2 w.2
    rw [mappedCoord_sub, sourceCoord_sub, hvw, sub_self, Real.sign_zero] at hs
    exact sub_eq_zero.mp (Real.sign_eq_zero_iff.mp hs)
  refine ⟨f, ?_, ?_⟩
  · intro x y hxy
    have hs := hφ.preservesVertexCoordinateSign axis (rep y).1 (rep x).1
      (rep y).2 (rep x).2
    rw [mappedCoord_sub, sourceCoord_sub, hrep y, hrep x,
      Real.sign_of_pos (sub_pos.mpr hxy)] at hs
    have hs' : Real.sign (f y - f x) = Real.sign (1 : ℝ) := by
      simpa [f] using hs
    change f x < f y
    exact sub_pos.mp (positive_of_same_sign hs' zero_lt_one)
  · intro v
    apply hind (rep (vertexCoordinateLevel C.region axis v)) v
    exact hrep _

theorem exists_increasingCoordinateExtension
    (C : ApproximationContext.{u}) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hφ : IsGoodApproximation C φ) (axis : Axis) :
    ∃ h : ℝ ≃ₜ ℝ, StrictMono h ∧ ∀ (v : Tiling.Plane) (hv : v ∈ C.region.vertices),
      h (Axis.coord axis v) = Axis.coord axis (mapPoint φ (C.vertexPoint v hv)) := by
  obtain ⟨f, hf, hfv⟩ := exists_strictMono_vertexCoordinateMap C φ hφ axis
  obtain ⟨h, hh, hext⟩ := exists_strictMonoHomeomorph_extension
    (coordinateLevels C.region axis) f hf
  refine ⟨h, hh, ?_⟩
  intro v hv
  simpa [vertexCoordinateLevel] using
    (hext (vertexCoordinateLevel C.region axis ⟨v, hv⟩)).trans (hfv ⟨v, hv⟩)

theorem exists_rationalPolygonDeformation
    (C : ApproximationContext.{u}) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hφ : IsGoodApproximation C φ) : Nonempty (CoordinateDeformation C φ) := by
  classical
  obtain ⟨hx, hhx, hxv⟩ := exists_increasingCoordinateExtension C φ hφ .horizontal
  obtain ⟨hy, hhy, hyv⟩ := exists_increasingCoordinateExtension C φ hφ .vertical
  let H₁ := coordinateProductHomeomorph hx (Homeomorph.refl ℝ)
  let H := coordinateProductHomeomorph hx hy
  obtain ⟨K₁, hK₁support, hK₁open, hK₁vertices⟩ :=
    exists_coordinateProductImageRegion C.region hx (Homeomorph.refl ℝ) hhx strictMono_id
  obtain ⟨K, hKsupport, hKopen, hKvertices⟩ :=
    exists_coordinateProductImageRegion C.region hx hy hhx hhy
  have hH₁ (z : Tiling.Plane) : H₁ z = hx z.re + z.im * Complex.I := by
    change coordinateProductHomeomorph hx (Homeomorph.refl ℝ) z = _
    rw [coordinateProductHomeomorph_apply]
    rfl
  have hH (z : Tiling.Plane) : H z = hx z.re + hy z.im * Complex.I :=
    coordinateProductHomeomorph_apply hx hy z
  have hagree₁ (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      H₁ v = mapFirstPoint φ (C.vertexPoint v hv) := by
    rw [hH₁]
    apply Complex.ext
    · convert hxv v hv using 1 <;>
        simp [Axis.coord, mapPoint, mapFirstPoint, ApproximationContext.vertexPoint]
    · simp [mapFirstPoint, ApproximationContext.vertexPoint]
  have hagree (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      H v = mapPoint φ (C.vertexPoint v hv) := by
    rw [hH]
    apply Complex.ext
    · simpa [Axis.coord, mapPoint, ApproximationContext.vertexPoint] using hxv v hv
    · simpa [Axis.coord, mapPoint, ApproximationContext.vertexPoint] using hyv v hv
  have hcomp : ConnectedComponents ↥C.region.openCarrier ≃
      ConnectedComponents ↥K.openCarrier := by
    let e := Classical.choice (connectedComponents_equiv_image H C.region.openCarrier)
    rw [hKopen]
    exact e
  have hcompc : ConnectedComponents ↥(C.region.openCarrier)ᶜ ≃
      ConnectedComponents ↥(K.openCarrier)ᶜ := by
    let e := Classical.choice (connectedComponents_equiv_image H (C.region.openCarrier)ᶜ)
    have heq : H '' (C.region.openCarrier)ᶜ = (H '' C.region.openCarrier)ᶜ :=
      H.image_compl _
    rw [hKopen]
    rw [← heq]
    exact e
  refine ⟨{
    source_good := hφ
    firstHomeomorph := hx
    firstHomeomorph_strictMono := hhx
    secondHomeomorph := hy
    secondHomeomorph_strictMono := hhy
    firstPlanarHomeomorph := H₁
    firstPlanarHomeomorph_apply := hH₁
    planarHomeomorph := H
    planarHomeomorph_apply := hH
    firstRegion := K₁
    deformedRegion := K
    firstRegion_openCarrier := hK₁open
    deformedRegion_openCarrier := hKopen
    first_vertex_agreement := hagree₁
    vertex_agreement := hagree
    vertices_image := hKvertices
    componentEquiv := hcomp
    complementComponentEquiv := hcompc
    rational_vertices := ?_ }⟩
  intro w hw
  rw [hKvertices] at hw
  obtain ⟨v, hv, rfl⟩ := hw
  rw [hagree v hv]
  refine ⟨φ ⟨v.re, C.vertex_re_mem v hv⟩,
    φ ⟨v.im, C.vertex_im_mem v hv⟩, ?_, ?_⟩
  · simp [mapPoint, mapScalar, ApproximationContext.vertexPoint]
  · simp [mapPoint, mapScalar, ApproximationContext.vertexPoint]

theorem boundaryLocallyStraightAt_iff
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (x : Tiling.Plane) :
    Tiling.BoundaryLocallyStraightAt C.region.openCarrier x ↔
      Tiling.BoundaryLocallyStraightAt D.deformedRegion.openCarrier
        (D.planarHomeomorph x) := by
  have hD : D.planarHomeomorph =
      coordinateProductHomeomorph D.firstHomeomorph D.secondHomeomorph := by
    apply Homeomorph.ext
    intro z
    rw [D.planarHomeomorph_apply,
      coordinateProductHomeomorph_apply D.firstHomeomorph D.secondHomeomorph z]
  rw [hD]
  have hopen := D.deformedRegion_openCarrier
  rw [hD] at hopen
  exact boundaryLocallyStraightAt_coordinateProduct_iff C.region D.deformedRegion
    D.firstHomeomorph D.secondHomeomorph D.firstHomeomorph_strictMono
    D.secondHomeomorph_strictMono hopen x

theorem rationalPolygonDeformation_wellDefined
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D₁ D₂ : CoordinateDeformation C φ) : D₁.deformedRegion = D₂.deformedRegion := by
  have hD₁ : D₁.planarHomeomorph =
      coordinateProductHomeomorph D₁.firstHomeomorph D₁.secondHomeomorph := by
    apply Homeomorph.ext
    intro z
    rw [D₁.planarHomeomorph_apply,
      coordinateProductHomeomorph_apply D₁.firstHomeomorph D₁.secondHomeomorph z]
  have hD₂ : D₂.planarHomeomorph =
      coordinateProductHomeomorph D₂.firstHomeomorph D₂.secondHomeomorph := by
    apply Homeomorph.ext
    intro z
    rw [D₂.planarHomeomorph_apply,
      coordinateProductHomeomorph_apply D₂.firstHomeomorph D₂.secondHomeomorph z]
  apply region_ext_openCarrier
  rw [D₁.deformedRegion_openCarrier, D₂.deformedRegion_openCarrier]
  rw [hD₁, hD₂]
  apply coordinateProductImage_openCarrier_unique C.region
    D₁.firstHomeomorph D₁.secondHomeomorph D₂.firstHomeomorph D₂.secondHomeomorph
    D₁.firstHomeomorph_strictMono D₁.secondHomeomorph_strictMono
    D₂.firstHomeomorph_strictMono D₂.secondHomeomorph_strictMono
  · intro v hv
    have h := D₁.vertex_agreement v hv
    have h' := D₂.vertex_agreement v hv
    rw [D₁.planarHomeomorph_apply] at h
    rw [D₂.planarHomeomorph_apply] at h'
    simpa using congrArg Complex.re (h.trans h'.symm)
  · intro v hv
    have h := D₁.vertex_agreement v hv
    have h' := D₂.vertex_agreement v hv
    rw [D₁.planarHomeomorph_apply] at h
    rw [D₂.planarHomeomorph_apply] at h'
    simpa using congrArg Complex.im (h.trans h'.symm)

theorem rationalPolygonDeformation_preservesBoundaryData
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    (∀ v : {v : Tiling.Plane // v ∈ C.region.vertices},
      (D.vertexEquiv v : Tiling.Plane) = mapPoint φ (C.vertexPoint v.1 v.2)) ∧
    D.deformedRegion.vertices = D.planarHomeomorph '' C.region.vertices ∧
    frontier D.deformedRegion.openCarrier =
      D.planarHomeomorph '' frontier C.region.openCarrier ∧
    (∀ v w : Tiling.Plane, v.re = w.re ∨ v.im = w.im →
      D.planarHomeomorph '' openSegment ℝ v w =
        openSegment ℝ (D.planarHomeomorph v) (D.planarHomeomorph w)) ∧
    (∀ x : Tiling.Plane, Tiling.BoundaryLocallyStraightAt C.region.openCarrier x ↔
      Tiling.BoundaryLocallyStraightAt D.deformedRegion.openCarrier
        (D.planarHomeomorph x)) ∧
    ∀ v ∈ D.deformedRegion.vertices, Tiling.IsRationalPoint v := by
  refine ⟨fun v => D.vertexEquiv_apply v |>.trans (D.vertex_agreement v.1 v.2),
    D.vertices_image, D.frontier_image, D.image_openSegment_of_axisAligned,
    boundaryLocallyStraightAt_iff D, D.rational_vertices⟩

private theorem epsilonApproximation_of_le {C : ApproximationContext.{u}}
    {ε δ : ℝ} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (hφ : IsEpsilonApproximation C ε φ) (hεδ : ε ≤ δ) :
    IsEpsilonApproximation C δ φ where
  epsilon_pos := hφ.epsilon_pos.trans_le hεδ
  fixesRational := hφ.fixesRational
  basis_close j := (hφ.basis_close j).trans_le hεδ

theorem rationalPolygonDeformation_uniformlyClose
    (C : ApproximationContext.{u}) (η : ℝ) (hη : 0 < η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C ε₀ φ → ∀ D : CoordinateDeformation C φ,
        (∀ (v : Tiling.Plane) (hv : v ∈ C.region.vertices),
          dist (mapPoint φ (C.vertexPoint v hv)) v < η) ∧
        Metric.diam D.deformedRegion.openCarrier ≤
          2 * Metric.diam C.region.openCarrier := by
  classical
  let d := Metric.diam C.region.openCarrier
  have hd : 0 < d := region_openCarrier_diam_pos C.region
  let τ := min (η / 2) (d / 4)
  have hτ : 0 < τ := lt_min (half_pos hη) (div_pos hd (by norm_num))
  let V := C.region.vertexFinset.attach
  let Zr : Finset C.coordinateSpace := V.image fun v =>
    ⟨v.1.re, C.vertex_re_mem v.1 (by
      rw [← C.region.coe_vertexFinset]
      exact v.2)⟩
  let Zi : Finset C.coordinateSpace := V.image fun v =>
    ⟨v.1.im, C.vertex_im_mem v.1 (by
      rw [← C.region.coe_vertexFinset]
      exact v.2)⟩
  obtain ⟨εr, hεr, hr⟩ := approximation_uniformOn_finset C Zr τ hτ
  obtain ⟨εi, hεi, hi⟩ := approximation_uniformOn_finset C Zi τ hτ
  obtain ⟨εg, hεg, hg⟩ := isGoodApproximation_of_sufficientlyFine C
  let ε₀ := min εg (min εr εi)
  have hε₀ : 0 < ε₀ := lt_min hεg (lt_min hεr hεi)
  refine ⟨ε₀, hε₀, ?_⟩
  intro φ hφ D
  have hφg := epsilonApproximation_of_le hφ (min_le_left _ _)
  have hφr := epsilonApproximation_of_le hφ
    ((min_le_right εg (min εr εi)).trans (min_le_left _ _))
  have hφi := epsilonApproximation_of_le hφ
    ((min_le_right εg (min εr εi)).trans (min_le_right _ _))
  have hverr (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      |mapScalar φ ⟨v.re, C.vertex_re_mem v hv⟩ - v.re| < τ := by
    apply hr φ hφr
    apply Finset.mem_image.mpr
    refine ⟨⟨v, ?_⟩, by simp [V], rfl⟩
    change v ∈ (C.region.vertexFinset : Set Tiling.Plane)
    rw [C.region.coe_vertexFinset]
    exact hv
  have hveri (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      |mapScalar φ ⟨v.im, C.vertex_im_mem v hv⟩ - v.im| < τ := by
    apply hi φ hφi
    apply Finset.mem_image.mpr
    refine ⟨⟨v, ?_⟩, by simp [V], rfl⟩
    change v ∈ (C.region.vertexFinset : Set Tiling.Plane)
    rw [C.region.coe_vertexFinset]
    exact hv
  have hdist (v : Tiling.Plane) (hv : v ∈ C.region.vertices) :
      dist (mapPoint φ (C.vertexPoint v hv)) v < η ∧
      dist (D.planarHomeomorph v) v ≤ d / 2 := by
    have hre := hverr v hv
    have him := hveri v hv
    have hnorm : dist (mapPoint φ (C.vertexPoint v hv)) v < 2 * τ := by
      rw [dist_eq_norm]
      calc
        ‖mapPoint φ (C.vertexPoint v hv) - v‖ ≤
            |(mapPoint φ (C.vertexPoint v hv) - v).re| +
              |(mapPoint φ (C.vertexPoint v hv) - v).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ < τ + τ := by
          gcongr <;> simpa [mapPoint, mapScalar, ApproximationContext.vertexPoint]
        _ = 2 * τ := by ring
    constructor
    · exact hnorm.trans_le (by dsimp [τ]; exact (mul_le_mul_of_nonneg_left
        (min_le_left _ _) (by norm_num)).trans_eq (by ring))
    · rw [D.vertex_agreement v hv]
      exact hnorm.le.trans (by
        dsimp [τ, d]
        have := min_le_right (η / 2) (Metric.diam C.region.openCarrier / 4)
        linarith)
  refine ⟨fun v hv => (hdist v hv).1, ?_⟩
  have hsupp : D.deformedRegion.support =
      D.planarHomeomorph '' C.region.support :=
    region_support_image_of_openCarrier_image C.region D.deformedRegion
      D.planarHomeomorph D.deformedRegion_openCarrier
  have hdiam := coordinateProductImage_diam_le C.region D.deformedRegion
    D.planarHomeomorph (d / 2) (le_of_lt (half_pos hd)) hsupp D.vertices_image
    (fun v hv => (hdist v hv).2)
  dsimp [d] at hdiam ⊢
  linarith

end

end Tiling.AxisParallel.Approximation
