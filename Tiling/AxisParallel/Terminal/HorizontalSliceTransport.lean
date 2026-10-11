import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.ControlledPeriodLifting
import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Terminal.RationalFinerStructure
import Tiling.AxisParallel.Terminal.NoGapSliceGeometry
import Tiling.AxisParallel.Terminal.VerticalPackingsNoColumn
import Tiling.AxisParallel.Terminal.VerticalPackingsWithColumn

/-!
# T09 dependency-independent prefix

Scratch-only proof of the maximal T09 prefix that does not invoke the pending
T06/T07 axis-local engines.  No theorem-valued dependency premise is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false
set_option linter.unusedVariables false

open Bornology Function Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private abbrev ControlledPlane (C : ApproximationContext.{0}) :=
  {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace}

private def indexedPreimage {C : ApproximationContext.{0}}
    (Tphi : ↥C.centres ↪ Tiling.Plane) (A : Set Tiling.Plane) :
    Set ↥C.centres :=
  {t | Tphi t ∈ A}

private theorem regularSupport_mono
    (K : Region) {S T : Set Tiling.Plane} (hST : S ⊆ T) :
    regularSupport K S ⊆ regularSupport K T := by
  apply interior_mono
  apply closure_mono
  intro z hz
  rw [Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz ⊢
  obtain ⟨s, hs⟩ := hz
  exact ⟨⟨s.1, hST s.2⟩, hs⟩

private theorem horizontalColumn_supportShape
    {K : Region} {S : Set Tiling.Plane}
    (hS : IsCenterColumn Axis.horizontal K S) :
    ∃ Y : Set ℝ, Y.Nonempty ∧ Bornology.IsBounded Y ∧
      IsOpen Y ∧ interior (closure Y) = Y ∧
      regularSupport K S = {z : Tiling.Plane | z.im ∈ Y} := by
  obtain ⟨c, hSne, hline, hsupport⟩ := centerColumn_regularSupport hS
  let B : Set ℝ := c +ᵥ (Complex.im '' K.openCarrier)
  let Y : Set ℝ := interior (closure B)
  have hKne : K.openCarrier.Nonempty :=
    K.isPolygonal.interior_nonempty K.nonempty
  have hBne : B.Nonempty := by
    obtain ⟨k, hk⟩ := hKne
    exact ⟨c + k.im, ⟨k.im, ⟨k, hk, rfl⟩, by simp [vadd_eq_add]⟩⟩
  have hBopen : IsOpen B := by
    have himopen : IsOpen (Complex.im '' K.openCarrier) :=
      Complex.isOpenMap_im K.openCarrier isOpen_interior
    simpa only [B] using himopen.vadd c
  have hYne : Y.Nonempty := by
    obtain ⟨b, hb⟩ := hBne
    exact ⟨b, hBopen.subset_interior_closure hb⟩
  have hcarrierBounded : Bornology.IsBounded K.openCarrier :=
    K.isPolygonal.isBounded.subset interior_subset
  have himBounded : Bornology.IsBounded (Complex.im '' K.openCarrier) :=
    hcarrierBounded.image Complex.imCLM
  have hBbounded : Bornology.IsBounded B := by
    simpa only [B] using himBounded.vadd c
  have hYbounded : Bornology.IsBounded Y := by
    exact hBbounded.closure.subset interior_subset
  refine ⟨Y, hYne, hYbounded, isOpen_interior, ?_, ?_⟩
  · simp [Y]
  · simpa only [B, Y, Axis.transverseCoord] using hsupport

private theorem horizontalStrip_ne_univ
    {Y : Set ℝ} (hY : Bornology.IsBounded Y) :
    {z : Tiling.Plane | z.im ∈ Y} ≠ Set.univ := by
  obtain ⟨R, hR⟩ := hY.subset_closedBall 0
  intro hfull
  let z : Tiling.Plane := ((|R| + 1 : ℝ) : ℂ) * Complex.I
  have hz : z ∈ {w : Tiling.Plane | w.im ∈ Y} := by rw [hfull]; exact Set.mem_univ z
  have hzR := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq] at hzR
  simp only [z, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
    Complex.ofReal_im, Complex.I_re, mul_one, zero_mul, add_zero] at hzR
  rw [sub_zero, abs_of_nonneg (by positivity)] at hzR
  linarith [le_abs_self R]

/-- A horizontal centre column cannot lie inside an irreducible vertical carrier. -/
theorem irreducibleRegion_noHorizontalRow
    {K : Tiling.AxisParallel.Region} {P S : Set Tiling.Plane}
    (hNonempty : P.Nonempty) (hSP : S ⊆ P) (hS : S.Nonempty)
    (X : Set ℝ)
    (hCarrier : Tiling.AxisParallel.regularSupport K P =
      {z : Tiling.Plane | z.re ∈ X})
    (hIrreducible : X = Set.univ →
      ∀ A : Set Tiling.Plane, A.Nonempty → A ⊆ P →
        (∀ r : ℝ, (r : Tiling.Plane) +ᵥ
          Tiling.AxisParallel.regularSupport K A =
            Tiling.AxisParallel.regularSupport K A) → A = P) :
    ¬ Tiling.AxisParallel.IsCenterColumn
      Tiling.AxisParallel.Axis.horizontal K S := by
  intro hColumn
  obtain ⟨Y, hYne, hYbounded, _hYopen, _hYregular, hSupportS⟩ :=
    horizontalColumn_supportShape hColumn
  have hSupportSub : regularSupport K S ⊆ regularSupport K P :=
    regularSupport_mono K hSP
  by_cases hX : X = Set.univ
  · have hSPeq : S = P := hIrreducible hX S hS hSP hColumn.2.2.2
    have hplane : regularSupport K S = Set.univ := by
      rw [hSPeq, hCarrier, hX]
      ext z
      simp
    exact horizontalStrip_ne_univ hYbounded (hSupportS.symm.trans hplane)
  · obtain ⟨x, hx⟩ := (Set.ne_univ_iff_exists_notMem X).mp hX
    obtain ⟨y, hy⟩ := hYne
    let z : Tiling.Plane := (x : ℂ) + (y : ℂ) * Complex.I
    have hzS : z ∈ regularSupport K S := by
      rw [hSupportS]
      simpa [z] using hy
    have hzP := hSupportSub hzS
    rw [hCarrier] at hzP
    exact hx (by simpa [z] using hzP)

/-- Exact data extracted for a base phase and one signed transverse phase. -/
private structure HorizontalPhasePair
    (C : ApproximationContext.{0}) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (m : ℤ) where
  S₀ : Set ↥C.centres
  S₁ : Set ↥C.centres
  S₀_eq : S₀ = indexedPreimage Tphi (Q.centres (Dcmp.part i))
  S₁_eq : S₁ = indexedPreimage Tphi
    ((Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i))
  source₀_eq : originalSlice i Q = Subtype.val '' S₀
  source₁_eq : originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
    Subtype.val '' S₁
  image₀_eq : deformedCenterCarrierOn Tphi S₀ = Q.centres (Dcmp.part i)
  image₁_eq : deformedCenterCarrierOn Tphi S₁ =
    (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i)
  nonempty : S₀.Nonempty ∧ S₁.Nonempty
  linked : Linked (60 * Metric.diam C.region.openCarrier)
      (Subtype.val '' S₀) ∧
    Linked (60 * Metric.diam C.region.openCarrier) (Subtype.val '' S₁)
  packings :
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)) ∧
    Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S₁)) ∧
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S₀)) ∧
    Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S₁))
  horizontal_lines :
    (∃ c, ∀ s : S₀, Axis.horizontal.transverseCoord (Tphi s.1) = c) ∧
    (∃ c, ∀ s : S₁, Axis.horizontal.transverseCoord (Tphi s.1) = c)
  common_image_period :
    (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi S₀ =
        deformedCenterCarrierOn Tphi S₀ ∧
      (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi S₁ =
        deformedCenterCarrierOn Tphi S₁
  target_support_shift :
    regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
      m • Dcmp.gamma.toPlane +ᵥ
        regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀)

private theorem horizontalPhasePair_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ} {D : CoordinateDeformation C phi}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hImagePacking : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        indexedPreimage Tphi (Q.centres (Dcmp.part i)))
    (i : Fin Dcmp.numberOfParts)
    (hHorizontal : (Dcmp.direction i).toPlane.im = 0)
    (Q : RationalSlice (Dcmp.direction i))
    (hNoGap : ∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i)
        (60 * Metric.diam C.region.openCarrier)) :
    ∀ m : ℤ,
      Nonempty (HorizontalPhasePair C phi D Tphi Dcmp originalSlice i Q m) := by
  intro m
  let Qm := Q.vadd (m • Dcmp.gamma.toPlane)
  let S₀ := indexedPreimage Tphi (Q.centres (Dcmp.part i))
  let S₁ := indexedPreimage Tphi (Qm.centres (Dcmp.part i))
  have hphase₀ : Q ∈ (Dcmp.orbit i).phases := by
    simpa [RationalSlice.vadd] using (hNoGap 0).1
  have hphase₁ : Qm ∈ (Dcmp.orbit i).phases := (hNoGap m).1
  have hpart : Dcmp.part i ⊆ Set.range Tphi := by
    intro z hz
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.mpr ⟨i, hz⟩
  have image_eq (R : RationalSlice (Dcmp.direction i)) :
      deformedCenterCarrierOn Tphi (indexedPreimage Tphi (R.centres (Dcmp.part i))) =
        R.centres (Dcmp.part i) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hz
      obtain ⟨t, rfl⟩ := hpart hz.1
      exact ⟨t, hz, rfl⟩
  have hImage₀ : deformedCenterCarrierOn Tphi S₀ = Q.centres (Dcmp.part i) :=
    image_eq Q
  have hImage₁ : deformedCenterCarrierOn Tphi S₁ = Qm.centres (Dcmp.part i) :=
    image_eq Qm
  have nonempty_of_phase (R : RationalSlice (Dcmp.direction i))
      (hR : R ∈ (Dcmp.orbit i).phases) :
      (indexedPreimage Tphi (R.centres (Dcmp.part i))).Nonempty := by
    obtain ⟨z, hz⟩ := ((Dcmp.orbit i).phase_iff_nonempty R).mp hR
    obtain ⟨t, rfl⟩ := hpart hz.1
    exact ⟨t, hz⟩
  have hSne₀ : S₀.Nonempty := nonempty_of_phase Q hphase₀
  have hSne₁ : S₁.Nonempty := nonempty_of_phase Qm hphase₁
  have hSource₀ : originalSlice i Q = Subtype.val '' S₀ := hPreimage i Q hphase₀
  have hSource₁ : originalSlice i Qm = Subtype.val '' S₁ := hPreimage i Qm hphase₁
  have hLinked₀ : Linked (60 * Metric.diam C.region.openCarrier)
      (Subtype.val '' S₀) := by
    have hnotGap : ¬IsGappedSlice (60 * Metric.diam C.region.openCarrier)
        (originalSlice i Q) := by
      intro hgap
      exact (hNoGap 0).2 ⟨by simpa [RationalSlice.vadd] using hphase₀,
        by simpa [RationalSlice.vadd] using hgap⟩
    rw [← hSource₀]
    exact (linked_iff_not_isGappedSlice (by
      rw [hPreimage i Q hphase₀]
      exact hSne₀.image Subtype.val)).2 hnotGap
  have hLinked₁ : Linked (60 * Metric.diam C.region.openCarrier)
      (Subtype.val '' S₁) := by
    have hnotGap : ¬IsGappedSlice (60 * Metric.diam C.region.openCarrier)
        (originalSlice i Qm) := by
      intro hgap
      exact (hNoGap m).2 ⟨hphase₁, hgap⟩
    rw [← hSource₁]
    exact (linked_iff_not_isGappedSlice (by
      rw [hPreimage i Qm hphase₁]
      exact hSne₁.image Subtype.val)).2 hnotGap
  have source_subset (S : Set ↥C.centres) : Subtype.val '' S ⊆ C.centres := by
    rintro z ⟨t, ht, rfl⟩
    exact t.2
  have source_pack (S : Set ↥C.centres) :
      Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
        (C.region.toPolygonalRegion.placements (Subtype.val '' S)) := by
    intro a ha b hb hab
    exact P.source_tilesOn.2.1 (source_subset S ha) (source_subset S hb) hab
  have image_pack (S : Set ↥C.centres) :
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements
          (deformedCenterCarrierOn Tphi S)) := by
    intro a ha b hb hab
    apply hImagePacking
    · change a.1 ∈ deformedCenterCarrierOn Tphi S at ha
      change a.1 ∈ Set.range Tphi
      rcases ha with ⟨t, ht, hat⟩
      exact ⟨t, hat⟩
    · change b.1 ∈ deformedCenterCarrierOn Tphi S at hb
      change b.1 ∈ Set.range Tphi
      rcases hb with ⟨t, ht, hbt⟩
      exact ⟨t, hbt⟩
    · exact hab
  have line_constant (R : RationalSlice (Dcmp.direction i))
      {S : Set ↥C.centres}
      (hSimage : deformedCenterCarrierOn Tphi S = R.centres (Dcmp.part i))
      (hSne : S.Nonempty) :
      ∃ c, ∀ s : S, Axis.horizontal.transverseCoord (Tphi s.1) = c := by
    obtain ⟨s₀, hs₀⟩ := hSne
    refine ⟨(Tphi s₀).im, ?_⟩
    intro s
    have hsR : Tphi s.1 ∈ R.carrier := by
      have : Tphi s.1 ∈ deformedCenterCarrierOn Tphi S := ⟨s.1, s.2, rfl⟩
      rw [hSimage] at this
      exact this.2
    have hs₀R : Tphi s₀ ∈ R.carrier := by
      have : Tphi s₀ ∈ deformedCenterCarrierOn Tphi S := ⟨s₀, hs₀, rfl⟩
      rw [hSimage] at this
      exact this.2
    change (Tphi s.1).im = (Tphi s₀).im
    change QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i)) (Tphi s.1) = R at hsR
    change QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i)) (Tphi s₀) = R at hs₀R
    obtain ⟨r, hr⟩ := QuotientAddGroup.eq_iff_sub_mem.mp (hsR.trans hs₀R.symm)
    have him := congrArg Complex.im hr
    simp only [Complex.sub_im, Complex.smul_im, smul_eq_mul] at him
    rw [hHorizontal, mul_zero] at him
    linarith
  have hPeriod₀ : (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi S₀ =
      deformedCenterCarrierOn Tphi S₀ := by
    rw [hImage₀]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic Q hphase₀)
  have hPeriod₁ : (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi S₁ =
      deformedCenterCarrierOn Tphi S₁ := by
    rw [hImage₁]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic Qm hphase₁)
  have hShift := (rationalSlices_shiftTransport Dcmp i Q hphase₀ m).2
  have hSupportShift :
      regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₁) =
        m • Dcmp.gamma.toPlane +ᵥ
          regularSupport D.deformedRegion (deformedCenterCarrierOn Tphi S₀) := by
    rw [hImage₀, hImage₁]
    exact hShift.symm
  exact ⟨⟨S₀, S₁, rfl, rfl, hSource₀, hSource₁, hImage₀, hImage₁,
    ⟨hSne₀, hSne₁⟩, ⟨hLinked₀, hLinked₁⟩,
    ⟨source_pack S₀, source_pack S₁, image_pack S₀, image_pack S₁⟩,
    ⟨line_constant Q hImage₀ hSne₀, line_constant Qm hImage₁ hSne₁⟩,
    ⟨hPeriod₀, hPeriod₁⟩, hSupportShift⟩⟩

private theorem horizontalPeriodRecoveryScale_exists
    (C : ApproximationContext.{0}) : ∃ r : ℝ, 0 < r ∧
    ∀ (P : FLCControlPackage C), r < P.scale →
      60 * Metric.diam C.region.openCarrier < P.scale ∧
      60 * Metric.diam C.region.openCarrier + P.localError < P.scale / 2 ∧
      Metric.diam C.region.openCarrier < P.controlRadius := by
  let d := Metric.diam C.region.openCarrier
  refine ⟨120 * d + 3, by
    have hd : 0 ≤ d := Metric.diam_nonneg
    linarith, ?_⟩
  intro P hscale
  have hd : 0 ≤ d := Metric.diam_nonneg
  have hs3 : 3 < P.scale := by linarith
  have hinv : P.scale⁻¹ < (3 : ℝ)⁻¹ :=
    (inv_lt_inv₀ P.scale_pos (by norm_num)).2 hs3
  rw [P.localError_eq]
  constructor
  · dsimp only [d] at hscale ⊢
    linarith
  constructor
  · dsimp only [d] at hscale ⊢
    norm_num at hinv
    linarith
  · exact lt_trans (by dsimp only [d] at hscale ⊢; linarith) P.scale_lt_controlRadius

private theorem horizontalPeriodLifts_synchronize
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (S₀ S₁ : Set ↥C.centres) (imagePeriod eta : Tiling.Plane)
    (alpha₀ alpha₁ : ControlledPlane C)
    (hmap₀ : mapPoint phi alpha₀ = imagePeriod)
    (hmap₁ : mapPoint phi alpha₁ = imagePeriod)
    (hperiod₀ : alpha₀.1 +ᵥ Subtype.val '' S₀ = Subtype.val '' S₀)
    (hperiod₁ : alpha₁.1 +ᵥ Subtype.val '' S₁ = Subtype.val '' S₁)
    (beta : ControlledPlane C)
    (hbeta : mapPoint phi beta = eta)
    (hsupport : regularSupport C.region (Subtype.val '' S₁) =
      beta.1 +ᵥ regularSupport C.region (Subtype.val '' S₀))
    (hproper : properVertices
      (regularSupport C.region (Subtype.val '' S₀)) ≠ ∅)
    (hpacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' S₀)))
    (hradius : Metric.diam C.region.openCarrier < P.controlRadius) :
    alpha₀ = alpha₁ := by
  apply periodLifts_eq_of_properVertexShift P phi hphi S₀ S₁
    alpha₀ alpha₁ beta imagePeriod hmap₀ hmap₁
    hperiod₀ hperiod₁
    (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn S₀)
    (properVertices_regularSupport_image_subset_translatedVertices C P.source_tilesOn S₁)
  · intro w hw
    rw [hsupport, properVertices_vadd_eq]
    exact Set.mem_vadd_set.mpr ⟨w, hw, rfl⟩
  · exact Set.nonempty_iff_ne_empty.mpr hproper

/-- The common horizontal period is recovered from exact phase data and phasewise
support translations; it is not inferred from injectivity of `mapPoint`. -/
private theorem horizontalOrbit_assemble
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (hImagePacking : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        indexedPreimage Tphi (Q.centres (Dcmp.part i)))
    (i : Fin Dcmp.numberOfParts)
    (hHorizontal : (Dcmp.direction i).toPlane.im = 0)
    (Q : RationalSlice (Dcmp.direction i))
    (hNoGap : ∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i)
        (60 * Metric.diam C.region.openCarrier))
    (hScale : 60 * Metric.diam C.region.openCarrier < P.scale)
    (hMargin : 60 * Metric.diam C.region.openCarrier + P.localError < P.scale / 2)
    (hRadius : Metric.diam C.region.openCarrier < P.controlRadius)
    (hBeta : ∀ m : ℤ, ∃ beta : ControlledPlane C,
      regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
        beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
      mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
      properVertices (regularSupport C.region (originalSlice i Q)) ≠ ∅ ∧
      properVertices (regularSupport C.region
        (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅) :
    ∃ alpha : ControlledPlane C, alpha.1 ≠ 0 ∧ alpha.1.im = 0 ∧
      mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ, alpha.1 +ᵥ originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ, ∃ beta : ControlledPlane C,
        regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  classical
  have hDirNe : (Dcmp.direction i).toPlane ≠ 0 := by
    intro hz
    apply (Dcmp.direction i).2
    funext j
    fin_cases j
    · have h := congrArg Complex.re hz
      have h' : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
        simpa [RationalDirection.toPlane] using h
      exact_mod_cast h'
    · have h := congrArg Complex.im hz
      have h' : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
        simpa [RationalDirection.toPlane] using h
      exact_mod_cast h'
  let pair (m : ℤ) : HorizontalPhasePair C phi D Tphi Dcmp originalSlice i Q m :=
    Classical.choice (horizontalPhasePair_exists P Tphi hImagePacking Dcmp
      originalSlice hPreimage i hHorizontal Q hNoGap m)
  let base := pair 0
  obtain ⟨alpha, hAlphaNe, hAlphaHorizontal, hAlphaMap, hAlphaPeriod⟩ :=
    connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi Axis.horizontal
      base.S₀ (60 * Metric.diam C.region.openCarrier)
      base.nonempty.1 base.linked.1.2 base.horizontal_lines.1 hScale hMargin
      (Dcmp.direction i).toPlane hDirNe hHorizontal base.common_image_period.1
  have hPeriods (m : ℤ) :
      alpha.1 +ᵥ originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) := by
    let phase := pair m
    obtain ⟨alpha_m, _hNe_m, _hHoriz_m, hMap_m, hPeriod_m⟩ :=
      connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi Axis.horizontal
        phase.S₁ (60 * Metric.diam C.region.openCarrier)
        phase.nonempty.2 phase.linked.2.2 phase.horizontal_lines.2 hScale hMargin
        (Dcmp.direction i).toPlane hDirNe hHorizontal phase.common_image_period.2
    obtain ⟨beta, hSupport, hMapBeta, hProperBase, _hProperPhase⟩ := hBeta m
    have hS₀ : base.S₀ = phase.S₀ := by
      rw [base.S₀_eq, phase.S₀_eq]
    have hSupport' : regularSupport C.region (Subtype.val '' phase.S₁) =
        beta.1 +ᵥ regularSupport C.region (Subtype.val '' base.S₀) := by
      rw [← phase.source₁_eq, ← base.source₀_eq]
      exact hSupport
    have hProperBase' : properVertices
        (regularSupport C.region (Subtype.val '' base.S₀)) ≠ ∅ := by
      rw [← base.source₀_eq]
      exact hProperBase
    have hEq : alpha = alpha_m :=
      horizontalPeriodLifts_synchronize P phi hphi Tphi hTphi base.S₀
        phase.S₁ (Dcmp.direction i).toPlane (m • Dcmp.gamma.toPlane)
        alpha alpha_m hAlphaMap hMap_m hAlphaPeriod hPeriod_m beta hMapBeta
        hSupport' hProperBase' base.packings.1 hRadius
    calc
      alpha.1 +ᵥ originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
          alpha.1 +ᵥ Subtype.val '' phase.S₁ := by rw [phase.source₁_eq]
      _ = Subtype.val '' phase.S₁ := by rw [hEq]; exact hPeriod_m
      _ = originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) :=
        phase.source₁_eq.symm
  refine ⟨alpha, hAlphaNe, hAlphaHorizontal, hAlphaMap, hPeriods, ?_⟩
  intro m
  obtain ⟨beta, hSupport, hMapBeta, _hProperBase, hProperPhase⟩ := hBeta m
  exact ⟨beta, hSupport, hMapBeta, hProperPhase⟩

/-- Horizontal no-gap orbit transport from literal image packing, assembled
from the actual axis-local engines on the original context. -/
theorem horizontalNoGapOrbitTransport_of_imagePacking :
    ∀ {C : ApproximationContext.{0}} (hFLC : HasFLC C.centres),
      ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
        ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C P.threshold phi →
        ∀ (D : CoordinateDeformation C phi)
          (Tphi : ↥C.centres ↪ Tiling.Plane),
          (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
          Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
            (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) →
        ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion
            (Set.range Tphi))
          (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
            RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
          (∀ i Q, Q ∈ (Dcmp.orbit i).phases →
            originalSlice i Q = Set.image Subtype.val
              {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
        ∀ (i : Fin Dcmp.numberOfParts),
          (Dcmp.direction i).toPlane.im = 0 →
        ∀ (Q : RationalSlice (Dcmp.direction i)),
          (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
            (Dcmp.orbit i).noGapPhases (originalSlice i)
              (60 * Metric.diam C.region.openCarrier)) →
          ((∃ Row : Set Tiling.Plane,
            IsCenterColumn Axis.horizontal C.region Row) →
            ¬ IsCenterColumn Axis.horizontal C.region (originalSlice i Q)) →
          ∃ alpha : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
              z.im ∈ C.coordinateSpace},
            alpha.1 ≠ 0 ∧ alpha.1.im = 0 ∧
            mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
            (∀ m : ℤ, alpha.1 +ᵥ
              originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
                originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
            ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
                z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
              regularSupport C.region
                (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
                  beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
              mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
              properVertices (regularSupport C.region
                (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  classical
  intro C hFLC
  obtain ⟨rRoom, hRoomPos, hRoom⟩ := horizontalPeriodRecoveryScale_exists C
  by_cases hCol : ∃ Row : Set Tiling.Plane,
      IsCenterColumn Axis.horizontal C.region Row
  · obtain ⟨rEngine, hEnginePos, hEngine⟩ :=
      columnableAxisLocalTransport hFLC Axis.horizontal hCol
    refine ⟨max rEngine rRoom,
      lt_of_lt_of_le hEnginePos (le_max_left _ _), ?_⟩
    intro P hP phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice
      hPreimage i hHorizontal Q hNoGap hRowNo
    obtain ⟨hScale, hMargin, hRadius⟩ :=
      hRoom P (lt_of_le_of_lt (le_max_right _ _) hP)
    have hEngineP := hEngine P (lt_of_le_of_lt (le_max_left _ _) hP)
      phi hphi D Tphi hTphi
    have hBeta (m : ℤ) : ∃ beta : ControlledPlane C,
        regularSupport C.region
            (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region (originalSlice i Q)) ≠ ∅ ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
      let pair := Classical.choice (horizontalPhasePair_exists P Tphi
        hImagePacking Dcmp originalSlice hPreimage i hHorizontal Q hNoGap m)
      have hNotColumn : ¬ IsCenterColumn Axis.horizontal C.region
          (Subtype.val '' pair.S₀) := by
        rw [← pair.source₀_eq]
        exact hRowNo hCol
      obtain ⟨beta, hSupport, hMap, hProper₀, hProper₁⟩ :=
        hEngineP pair.S₀ pair.S₁
          (60 * Metric.diam C.region.openCarrier) rfl pair.packings
          pair.nonempty pair.horizontal_lines pair.linked
          (Dcmp.direction i).toPlane (by
            intro hz
            apply (Dcmp.direction i).2
            funext j
            fin_cases j
            · have h := congrArg Complex.re hz
              have h' : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
                simpa [RationalDirection.toPlane] using h
              exact_mod_cast h'
            · have h := congrArg Complex.im hz
              have h' : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
                simpa [RationalDirection.toPlane] using h
              exact_mod_cast h')
          hHorizontal pair.common_image_period hNotColumn
          (m • Dcmp.gamma.toPlane) pair.target_support_shift
      refine ⟨beta, ?_, hMap, ?_, ?_⟩
      · rw [pair.source₁_eq, pair.source₀_eq]
        exact hSupport
      · rw [pair.source₀_eq]
        exact hProper₀
      · rw [pair.source₁_eq]
        exact hProper₁
    exact horizontalOrbit_assemble P phi hphi D Tphi hTphi hImagePacking
      Dcmp originalSlice hPreimage i hHorizontal Q hNoGap
      hScale hMargin hRadius hBeta
  · obtain ⟨rEngine, hEnginePos, hEngine⟩ :=
      nonColumnableAxisLocalTransport hFLC Axis.horizontal hCol
    refine ⟨max rEngine rRoom,
      lt_of_lt_of_le hEnginePos (le_max_left _ _), ?_⟩
    intro P hP phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice
      hPreimage i hHorizontal Q hNoGap _hRowNo
    obtain ⟨hScale, hMargin, hRadius⟩ :=
      hRoom P (lt_of_le_of_lt (le_max_right _ _) hP)
    have hEngineP := hEngine P (lt_of_le_of_lt (le_max_left _ _) hP)
      phi hphi D Tphi hTphi
    have hBeta (m : ℤ) : ∃ beta : ControlledPlane C,
        regularSupport C.region
            (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region (originalSlice i Q)) ≠ ∅ ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
      let pair := Classical.choice (horizontalPhasePair_exists P Tphi
        hImagePacking Dcmp originalSlice hPreimage i hHorizontal Q hNoGap m)
      obtain ⟨beta, _alpha, hSupport, hMap, _hAlphaNe, _hAlphaHorizontal,
        _hPeriod₀, _hPeriod₁, _hMapAlpha, hProper₀, hProper₁⟩ :=
        hEngineP pair.S₀ pair.S₁
          (60 * Metric.diam C.region.openCarrier) rfl pair.packings
          pair.nonempty pair.horizontal_lines pair.linked
          (Dcmp.direction i).toPlane (by
            intro hz
            apply (Dcmp.direction i).2
            funext j
            fin_cases j
            · have h := congrArg Complex.re hz
              have h' : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
                simpa [RationalDirection.toPlane] using h
              exact_mod_cast h'
            · have h := congrArg Complex.im hz
              have h' : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
                simpa [RationalDirection.toPlane] using h
              exact_mod_cast h')
          hHorizontal pair.common_image_period
          (m • Dcmp.gamma.toPlane) pair.target_support_shift
      refine ⟨beta, ?_, hMap, ?_, ?_⟩
      · rw [pair.source₁_eq, pair.source₀_eq]
        exact hSupport
      · rw [pair.source₀_eq]
        exact hProper₀
      · rw [pair.source₁_eq]
        exact hProper₁
    exact horizontalOrbit_assemble P phi hphi D Tphi hTphi hImagePacking
      Dcmp originalSlice hPreimage i hHorizontal Q hNoGap
      hScale hMargin hRadius hBeta

/-- Historical horizontal no-gap orbit transport for proper periodic bands. -/
theorem horizontalNoGapOrbitTransport :
    ∀ {C : ApproximationContext.{0}} (hFLC : HasFLC C.centres),
      ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
        ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
        ∀ (B : PeriodicBandData C), IsPeriodicBandFineness B P.threshold →
        ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
          IsEpsilonApproximation C P.threshold phi →
        ∀ (D : CoordinateDeformation C phi)
          (Tphi : ↥C.centres ↪ Tiling.Plane),
          (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
        ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion
            (Set.range Tphi))
          (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
            RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
          (∀ i Q, Q ∈ (Dcmp.orbit i).phases →
            originalSlice i Q = Set.image Subtype.val
              {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
        ∀ (i : Fin Dcmp.numberOfParts),
          (Dcmp.direction i).toPlane.im = 0 →
        ∀ (Q : RationalSlice (Dcmp.direction i)),
          (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
            (Dcmp.orbit i).noGapPhases (originalSlice i)
              (60 * Metric.diam C.region.openCarrier)) →
          ((∃ Row : Set Tiling.Plane,
            IsCenterColumn Axis.horizontal C.region Row) →
            ¬ IsCenterColumn Axis.horizontal C.region (originalSlice i Q)) →
          ∃ alpha : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧
              z.im ∈ C.coordinateSpace},
            alpha.1 ≠ 0 ∧ alpha.1.im = 0 ∧
            mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
            (∀ m : ℤ, alpha.1 +ᵥ
              originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
                originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
            ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
                z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
              regularSupport C.region
                (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
                  beta.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
              mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
              properVertices (regularSupport C.region
                (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C hFLC
  obtain ⟨recoveryScale, hScalePos, hTransport⟩ :=
    horizontalNoGapOrbitTransport_of_imagePacking hFLC
  refine ⟨recoveryScale, hScalePos, ?_⟩
  intro P hScale B hFine phi hphi D Tphi hTphi Dcmp originalSlice hPreimage
    i hHorizontal Q hNoGap hNoColumn
  obtain ⟨Tφ, Xφ, αφ, hTφ, _hOpen, _hRegular, _hNonempty, _hProper,
      _hAlphaEq, _hAlphaPos, _hPeriod, _hFrontier, _hOccupied, hTiles,
      _hSupport⟩ := periodicBandDeformation B P.threshold hFine phi hphi D
  have hEmb : Tφ = Tphi := by
    ext t
    exact (hTφ t).trans (hTphi t).symm
  have hImagePacking : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) := by
    rw [hEmb] at hTiles
    exact hTiles.2.1
  exact hTransport P hScale phi hphi D Tphi hTphi hImagePacking Dcmp
    originalSlice hPreimage i hHorizontal Q hNoGap hNoColumn

end Tiling.AxisParallel.Terminal
