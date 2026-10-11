import Tiling.AxisParallel.Continuous.HorizontalComplexityCore
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false

/-!
# Finite horizontal complexity and finite alphabets

This module records the native bounded-difference consequences of horizontal FLC and the finite
Hamel-alphabet estimates used by later deformation arguments.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Continuous

theorem horizontalCentreProjection_eq
    (T : Set Tiling.Plane) :
    horizontalCentreProjection T = Complex.re '' T :=
  rfl

theorem horizontalTranslatedVertices_eq
    (K : Region) (T : Set Tiling.Plane) :
    horizontalTranslatedVertices K T =
      {x : ℝ | ∃ v ∈ K.vertices, ∃ t ∈ T,
        x = (v + t).re} :=
  rfl

theorem hasFiniteHorizontalComplexity_iff
    (T : Set Tiling.Plane) :
    HasFiniteHorizontalComplexity T ↔ HasFLC (horizontalCentreProjection T) :=
  Iff.rfl

theorem horizontalBoundedDifferences_eq
    (A : Set ℝ) (R : ℝ) :
    horizontalBoundedDifferences A R =
      {d : ℝ | ∃ a ∈ A, ∃ b ∈ A,
        d = b - a ∧ |d| ≤ R} :=
  rfl

theorem horizontalGapSet_eq
    {A : Set ℝ} (order : HorizontalOrderData A) :
    horizontalGapSet order =
      {g : ℝ | ∃ i : ℤ, g = order.point (i + 1) - order.point i} :=
  rfl

theorem horizontalTranslatedVertices_eq_projection_add_vertices
    (K : Region) (T : Set Tiling.Plane) :
    horizontalTranslatedVertices K T =
      horizontalCentreProjection T +
        ((K.vertexFinset.image Complex.re : Finset ℝ) : Set ℝ) := by
  classical
  ext x
  constructor
  · rintro ⟨v, hv, t, ht, rfl⟩
    refine ⟨t.re, ⟨t, ht, rfl⟩, v.re, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨v, ?_, rfl⟩
      have : v ∈ (K.vertexFinset : Set Tiling.Plane) := by
        rw [K.coe_vertexFinset]
        exact hv
      exact this
    · simp only [Complex.add_re]
      ring
  · rintro ⟨d, ⟨t, ht, rfl⟩, f, hf, rfl⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hf
    have hv' : v ∈ K.vertices := by
      rw [← K.coe_vertexFinset]
      exact hv
    exact ⟨v, hv', t, ht, by simp [add_comm]⟩

theorem horizontalBoundedDifferences_finite
    {K : Region} {T : Set Tiling.Plane}
    (hFHC : HasFiniteHorizontalComplexity T)
    (R : ℝ) :
    (horizontalBoundedDifferences
      (horizontalTranslatedVertices K T) R).Finite := by
  classical
  let F : Finset ℝ := K.vertexFinset.image Complex.re
  have htranslated : HasFLC (horizontalTranslatedVertices K T) := by
    rw [horizontalTranslatedVertices_eq_projection_add_vertices]
    exact hFHC.add_finset F
  let R' : ℝ := max R 0 + 1
  have hR' : 0 < R' := by
    dsimp [R']
    linarith [le_max_right R 0]
  apply (htranslated.2 R' hR').subset
  rintro d ⟨a, ha, b, hb, rfl, hba⟩
  refine ⟨⟨b, hb, a, ha, rfl⟩, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq]
  have hRR' : R ≤ R' := by
    dsimp [R']
    linarith [le_max_left R 0]
  simpa only [sub_zero] using hba.trans hRR'

theorem approximation_uniformOnHorizontalAlphabet
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (G : Finset ℝ)
    (hG : ∀ g ∈ G, g ∈ C.coordinateSpace)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
      Tiling.AxisParallel.Approximation.IsEpsilonApproximation
        C epsilon phi →
      ∀ (g : ℝ) (hg : g ∈ G),
      |Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨g, hG g hg⟩ - g| < eta := by
  classical
  let lift : {g : ℝ // g ∈ G} → C.coordinateSpace :=
    fun g ↦ ⟨(g : ℝ), hG (g : ℝ) g.property⟩
  let Z : Finset C.coordinateSpace := G.attach.image lift
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    Tiling.AxisParallel.Approximation.approximation_uniformOn_finset
      C Z eta heta
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi g hg
  apply hcontrol phi hphi ⟨g, hG g hg⟩
  let g' : {x // x ∈ G} := ⟨g, hg⟩
  exact Finset.mem_image.mpr
    ⟨g', Finset.mem_attach G g', Subtype.ext rfl⟩

theorem approximation_separatesHorizontalAlphabet
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (G : Finset ℝ)
    (hG : ∀ g ∈ G, g ∈ C.coordinateSpace) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
      Tiling.AxisParallel.Approximation.IsEpsilonApproximation
        C epsilon phi →
      ∀ (g : ℝ) (hg : g ∈ G),
      ∀ (g' : ℝ) (hg' : g' ∈ G),
      g ≠ g' →
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨g, hG g hg⟩ ≠
        Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨g', hG g' hg'⟩ := by
  classical
  let Z : Finset C.coordinateSpace :=
    (G.attach.product G.attach).image fun p ↦
      ⟨(p.1 : ℝ) - (p.2 : ℝ),
        C.coordinateSpace.sub_mem
          (hG (p.1 : ℝ) p.1.property) (hG (p.2 : ℝ) p.2.property)⟩
  obtain ⟨epsilon, hepsilon, hsign⟩ :=
    Tiling.AxisParallel.Approximation.approximation_preservesSign_finset C Z
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi g hg g' hg' hgg' hEq
  let z : C.coordinateSpace :=
    ⟨g - g', C.coordinateSpace.sub_mem (hG g hg) (hG g' hg')⟩
  have hz : z ∈ Z := by
    apply Finset.mem_image.mpr
    refine ⟨(⟨g, hg⟩, ⟨g', hg'⟩), ?_, rfl⟩
    exact Finset.mem_product.mpr ⟨by simp, by simp⟩
  have hs := hsign phi hphi z hz
  have hmapZero : Tiling.AxisParallel.Approximation.mapScalar phi z = 0 := by
    change ((phi z : ℚ) : ℝ) = 0
    have hsub : phi z =
        phi ⟨g, hG g hg⟩ - phi ⟨g', hG g' hg'⟩ := by
      rw [← map_sub]
      rfl
    rw [hsub, Rat.cast_sub, sub_eq_zero]
    exact hEq
  rw [hmapZero, Real.sign_zero] at hs
  have hzval : (z : ℝ) = 0 := Real.sign_eq_zero_iff.mp hs.symm
  exact hgg' (sub_eq_zero.mp hzval)

theorem boundedGapSubset_alphabet_finite
    {A B : Set ℝ}
    (hBA : B ⊆ A)
    (hboundedDiff : ∀ R : ℝ,
      (horizontalBoundedDifferences A R).Finite)
    (order : HorizontalOrderData B)
    {R₀ : ℝ} (_hR₀ : 0 < R₀)
    (hgap : ∀ i : ℤ,
      order.point (i + 1) - order.point i ≤ R₀) :
    (horizontalGapSet order).Finite := by
  apply (hboundedDiff R₀).subset
  rintro g ⟨i, rfl⟩
  have hi : i < i + 1 := by omega
  have hpos : 0 < order.point (i + 1) - order.point i :=
    sub_pos.mpr (order.point_strictMono hi)
  refine ⟨order.point i, ?_, order.point (i + 1), ?_, rfl, ?_⟩
  · apply hBA
    exact Eq.mp
      (congrArg (fun S : Set ℝ ↦ order.point i ∈ S) order.point_range)
      (Set.mem_range_self i)
  · apply hBA
    exact Eq.mp
      (congrArg (fun S : Set ℝ ↦ order.point (i + 1) ∈ S) order.point_range)
      (Set.mem_range_self (i + 1))
  · rw [abs_of_pos hpos]
    exact hgap i


private theorem horizontalTranslatedVertices_hasFLC
    {K : Region} {T : Set Tiling.Plane}
    (hFHC : HasFiniteHorizontalComplexity T) :
    HasFLC (horizontalTranslatedVertices K T) := by
  classical
  let F : Finset ℝ := K.vertexFinset.image Complex.re
  rw [horizontalTranslatedVertices_eq_projection_add_vertices]
  exact hFHC.add_finset F

private theorem projectedCentres_relativelyDense
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ,
      ∃ d ∈ horizontalCentreProjection T, |d - x| < L := by
  obtain ⟨D, hD⟩ :=
    K.isPolygonal.isBounded.subset_closedBall (0 : Tiling.Plane)
  let L : ℝ := max D 0 + 1
  refine ⟨L, by dsimp [L]; linarith [le_max_right D 0], fun x ↦ ?_⟩
  let z : Tiling.Plane := (x : ℂ)
  have hcover : ∀ᵐ q ∂MeasureTheory.volume,
      ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    filter_upwards [hTile.2.2] with q hq
    exact hq.mp (Set.mem_univ q)
  have hex : ∃ q ∈ Metric.ball z 1,
      ∃ t : ↥T, q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) := by
    by_contra hn
    push Not at hn
    have hballnull : MeasureTheory.volume (Metric.ball z 1) = 0 := by
      apply MeasureTheory.measure_mono_null
        (t := {q | ¬ ∃ t : ↥T,
          q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier)})
      · intro q hq
        change ¬ ∃ t : ↥T,
          q ∈ ((t.1 : Tiling.Plane) +ᵥ K.openCarrier)
        rintro ⟨t, ht⟩
        exact hn q hq t ht
      · exact MeasureTheory.ae_iff.mp hcover
    exact (Metric.measure_ball_pos MeasureTheory.volume z zero_lt_one).ne'
      hballnull
  obtain ⟨q, hqball, t, hqt⟩ := hex
  refine ⟨t.1.re, ⟨t.1, t.2, rfl⟩, ?_⟩
  rw [mem_vadd_set] at hqt
  obtain ⟨k, hk, hkq⟩ := hqt
  have hkclosed : k ∈ Metric.closedBall (0 : Tiling.Plane) D :=
    hD (interior_subset hk)
  have hkbound : ‖k‖ ≤ max D 0 := by
    have : ‖k‖ ≤ D := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hkclosed
    exact this.trans (le_max_left _ _)
  have hqbound : ‖q - z‖ < 1 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hqball
  have hreal : |t.1.re - x| ≤ ‖(t.1 : Tiling.Plane) - z‖ := by
    simpa [z] using
      Complex.abs_re_le_norm ((t.1 : Tiling.Plane) - z)
  calc
    |t.1.re - x| ≤ ‖(t.1 : Tiling.Plane) - z‖ := hreal
    _ = ‖q - k - z‖ := by rw [← hkq]; simp
    _ ≤ ‖k‖ + ‖q - z‖ := by
      rw [show q - k - z = (q - z) - k by abel, norm_sub_rev]
      exact norm_sub_le _ _
    _ < max D 0 + 1 := add_lt_add_of_le_of_lt hkbound hqbound
    _ = L := rfl

private theorem region_vertices_nonempty (K : Region) :
    K.vertices.Nonempty := by
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  exact ⟨v, hv⟩

private theorem horizontalTranslatedVertices_relativelyDense
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) :
    ∃ L : ℝ, 0 < L ∧ ∀ x : ℝ,
      ∃ a ∈ horizontalTranslatedVertices K T, |a - x| < L := by
  obtain ⟨v, hv⟩ := region_vertices_nonempty K
  obtain ⟨L, hL, hdense⟩ := projectedCentres_relativelyDense hTile
  refine ⟨L, hL, fun x ↦ ?_⟩
  obtain ⟨d, ⟨t, ht, htd⟩, hd⟩ := hdense (x - v.re)
  refine ⟨(v + t).re, ⟨v, hv, t, ht, rfl⟩, ?_⟩
  rw [← htd] at hd
  rw [Complex.add_re]
  have heq : v.re + t.re - x = t.re - (x - v.re) := by ring
  rw [heq]
  exact hd

theorem horizontalTranslatedVertices_delone
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hFHC : HasFiniteHorizontalComplexity T) :
    (∃ delta : ℝ, 0 < delta ∧
      ∀ x ∈ horizontalTranslatedVertices K T,
      ∀ y ∈ horizontalTranslatedVertices K T,
        x ≠ y → delta ≤ |x - y|) ∧
    (∃ L : ℝ, 0 < L ∧
      ∀ x : ℝ, ∃ a ∈ horizontalTranslatedVertices K T,
        |a - x| < L) := by
  refine ⟨?_, horizontalTranslatedVertices_relativelyDense hTile⟩
  obtain ⟨delta, hdelta, hseparated⟩ :=
    (horizontalTranslatedVertices_hasFLC hFHC).uniformlyDiscrete
  refine ⟨delta, hdelta, ?_⟩
  intro x hx y hy hxy
  simpa only [Real.dist_eq] using hseparated x hx y hy hxy

private theorem locallyFinite_twoSided_integerEnumeration
    {A : Set ℝ}
    (hLocal : ∀ a b : ℝ, (A ∩ Set.Icc a b).Finite)
    (hAbove : ¬ BddAbove A) (hBelow : ¬ BddBelow A) :
    ∃ point : ℤ → ℝ, StrictMono point ∧ Set.range point = A := by
  let _ : Nonempty A := (nonempty_of_not_bddAbove hAbove).to_subtype
  let _ : LocallyFiniteOrder A := LocallyFiniteOrder.ofFiniteIcc fun a b ↦ by
    have hFinite := hLocal a.1 b.1
    apply (Set.Finite.preimage Subtype.val_injective.injOn hFinite).subset
    intro x hx
    exact ⟨x.2, hx⟩
  let _ : SuccOrder A := LinearLocallyFiniteOrder.succOrder A
  let _ : PredOrder A := LinearLocallyFiniteOrder.predOrder A
  let _ : NoMaxOrder A := ⟨fun a ↦ by
    obtain ⟨x, hxA, hax⟩ := not_bddAbove_iff.mp hAbove a.1
    exact ⟨⟨x, hxA⟩, hax⟩⟩
  let _ : NoMinOrder A := ⟨fun a ↦ by
    obtain ⟨x, hxA, hxa⟩ := not_bddBelow_iff.mp hBelow a.1
    exact ⟨⟨x, hxA⟩, hxa⟩⟩
  let e : A ≃o ℤ := orderIsoIntOfLinearSuccPredArch
  let point : ℤ → ℝ := fun n ↦ (e.symm n).1
  refine ⟨point, ?_, ?_⟩
  · intro m n hmn
    exact e.symm.strictMono hmn
  · ext x
    constructor
    · rintro ⟨n, rfl⟩
      exact (e.symm n).2
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      exact congrArg Subtype.val (e.symm_apply_apply ⟨x, hx⟩)

private theorem adjacentGaps_bounded_of_relativeDense
    {A : Set ℝ} (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = A) :
    ∀ {L : ℝ}, 0 < L →
      (∀ x : ℝ, ∃ a ∈ A, |a - x| < L) →
      ∀ i : ℤ, 0 < point (i + 1) - point i ∧
        point (i + 1) - point i < 2 * L := by
  intro L hL hdense i
  have hstep : point i < point (i + 1) := hmono (by omega)
  refine ⟨sub_pos.mpr hstep, ?_⟩
  by_contra hgap
  have hwide : 2 * L ≤ point (i + 1) - point i := le_of_not_gt hgap
  let midpoint : ℝ := (point i + point (i + 1)) / 2
  obtain ⟨a, haA, ha⟩ := hdense midpoint
  obtain ⟨j, rfl⟩ : ∃ j, point j = a := by
    exact hrange.symm.subset haA
  have ha' := abs_lt.mp ha
  have hij : point i < point j := by
    dsimp [midpoint] at ha'
    linarith
  have hji : point j < point (i + 1) := by
    dsimp [midpoint] at ha'
    linarith
  have hij' : i < j := hmono.lt_iff_lt.mp hij
  have hji' : j < i + 1 := hmono.lt_iff_lt.mp hji
  omega

theorem delone_has_integerOrderData
    {A : Set ℝ}
    (_hseparated : ∃ delta : ℝ, 0 < delta ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y → delta ≤ |x - y|)
    (hdense : ∃ L : ℝ, 0 < L ∧
      ∀ x : ℝ, ∃ a ∈ A, |a - x| < L)
    (hboundedDiff : ∀ R : ℝ,
      (horizontalBoundedDifferences A R).Finite) :
    Nonempty (HorizontalOrderData A) := by
  classical
  obtain ⟨L, hL, hdense⟩ := hdense
  obtain ⟨a₀, ha₀A, _ha₀⟩ := hdense 0
  have hLocal : ∀ a b : ℝ, (A ∩ Set.Icc a b).Finite := by
    intro a b
    let R : ℝ := max (b - a₀) (a₀ - a)
    have hpre : ((fun x : ℝ ↦ x - a₀) ⁻¹'
        horizontalBoundedDifferences A R).Finite :=
      (hboundedDiff R).preimage sub_left_injective.injOn
    apply hpre.subset
    intro x hx
    change x - a₀ ∈ horizontalBoundedDifferences A R
    refine ⟨a₀, ha₀A, x, hx.1, rfl, ?_⟩
    exact abs_sub_le_max_sub hx.2.1 hx.2.2 a₀
  have hAbove : ¬ BddAbove A := by
    rw [not_bddAbove_iff]
    intro b
    obtain ⟨a, haA, ha⟩ := hdense (b + L)
    refine ⟨a, haA, ?_⟩
    have := (abs_lt.mp ha).1
    linarith
  have hBelow : ¬ BddBelow A := by
    rw [not_bddBelow_iff]
    intro b
    obtain ⟨a, haA, ha⟩ := hdense (b - L)
    refine ⟨a, haA, ?_⟩
    have := (abs_lt.mp ha).2
    linarith
  obtain ⟨point, hmono, hrange⟩ :=
    locallyFinite_twoSided_integerEnumeration hLocal hAbove hBelow
  have hgap := adjacentGaps_bounded_of_relativeDense point hmono hrange hL hdense
  let G : Set ℝ :=
    {g : ℝ | ∃ i : ℤ, g = point (i + 1) - point i}
  have hGfinite : G.Finite := by
    apply (hboundedDiff (2 * L)).subset
    intro g hg
    obtain ⟨i, rfl⟩ := hg
    have hiA : point i ∈ A := by
      rw [← hrange]
      exact Set.mem_range_self i
    have hi1A : point (i + 1) ∈ A := by
      rw [← hrange]
      exact Set.mem_range_self (i + 1)
    refine ⟨point i, hiA, point (i + 1), hi1A, rfl, ?_⟩
    rw [abs_of_pos (hgap i).1]
    exact (hgap i).2.le
  let gapAlphabet : Finset ℝ := hGfinite.toFinset
  refine ⟨{
    point := point
    point_strictMono := hmono
    point_range := hrange
    gapAlphabet := gapAlphabet
    gap_mem := ?_
    gap_pos := ?_
    gap_complete := ?_ }⟩
  · intro i
    exact hGfinite.mem_toFinset.mpr ⟨i, rfl⟩
  · intro g hg
    have hgG : g ∈ G := hGfinite.mem_toFinset.mp hg
    obtain ⟨i, rfl⟩ := hgG
    exact (hgap i).1
  · intro g hg
    have hgG : g ∈ G := hGfinite.mem_toFinset.mp hg
    exact hgG

theorem horizontalGapAlphabet_finite
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (hFHC : HasFiniteHorizontalComplexity T) :
    Nonempty (HorizontalOrderData (horizontalTranslatedVertices K T)) := by
  exact delone_has_integerOrderData
    (horizontalTranslatedVertices_delone hTile hFHC).1
    (horizontalTranslatedVertices_delone hTile hFHC).2
    (horizontalBoundedDifferences_finite hFHC)

theorem finitePositiveGaps_control_indexedDifferences
    {A : Set ℝ} (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (order : HorizontalOrderData A)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (pointLift : ℤ → C.coordinateSpace)
    (hpointLift : ∀ i,
      ((pointLift i : C.coordinateSpace) : ℝ) = order.point i)
    (gapLift : ↑order.gapAlphabet → C.coordinateSpace)
    (hgapLift : ∀ g : ↑order.gapAlphabet,
      ((gapLift g : C.coordinateSpace) : ℝ) = (g : ℝ))
    (hlower : ∀ g : ↑order.gapAlphabet,
      (1 / 2 : ℝ) * (g : ℝ) <
        Tiling.AxisParallel.Approximation.mapScalar phi (gapLift g))
    (hupper : ∀ g : ↑order.gapAlphabet,
      Tiling.AxisParallel.Approximation.mapScalar phi (gapLift g) <
        2 * (g : ℝ)) :
    ∀ i j : ℤ, i < j →
      (1 / 2 : ℝ) * (order.point j - order.point i) <
          Tiling.AxisParallel.Approximation.mapScalar phi (pointLift j) -
            Tiling.AxisParallel.Approximation.mapScalar phi (pointLift i) ∧
        Tiling.AxisParallel.Approximation.mapScalar phi (pointLift j) -
            Tiling.AxisParallel.Approximation.mapScalar phi (pointLift i) <
          2 * (order.point j - order.point i) := by
  let mapped : ℤ → ℝ := fun i ↦
    Tiling.AxisParallel.Approximation.mapScalar phi (pointLift i)
  have hstep : ∀ i : ℤ,
      (1 / 2 : ℝ) * (order.point (i + 1) - order.point i) <
          mapped (i + 1) - mapped i ∧
        mapped (i + 1) - mapped i <
          2 * (order.point (i + 1) - order.point i) := by
    intro i
    let g : ↑order.gapAlphabet :=
      ⟨order.point (i + 1) - order.point i, order.gap_mem i⟩
    have hlift : pointLift (i + 1) - pointLift i = gapLift g := by
      apply Subtype.ext
      simp [g, hpointLift, hgapLift]
    have hmapped : mapped (i + 1) - mapped i =
        Tiling.AxisParallel.Approximation.mapScalar phi (gapLift g) := by
      dsimp [mapped, Tiling.AxisParallel.Approximation.mapScalar]
      rw [← Rat.cast_sub, ← map_sub, hlift]
    rw [hmapped]
    exact ⟨hlower g, hupper g⟩
  have hnat : ∀ n : ℕ, 0 < n → ∀ i : ℤ,
      (1 / 2 : ℝ) *
          (order.point (i + (n : ℤ)) - order.point i) <
            mapped (i + (n : ℤ)) - mapped i ∧
        mapped (i + (n : ℤ)) - mapped i <
          2 * (order.point (i + (n : ℤ)) - order.point i) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        intro _hn i
        by_cases hn : n = 0
        · subst n
          simpa using hstep i
        · have hprev := ih (Nat.pos_of_ne_zero hn) i
          have hnext := hstep (i + (n : ℤ))
          have hidx : i + ((n + 1 : ℕ) : ℤ) = i + (n : ℤ) + 1 := by
            push_cast
            ring
          rw [hidx]
          constructor <;> linarith
  intro i j hij
  let n : ℕ := (j - i).toNat
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hncast : (n : ℤ) = j - i := by
    dsimp [n]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hij.le)
  have h := hnat n hn i
  rw [hncast] at h
  simpa [mapped] using h

theorem approximation_preservesGlobalHorizontalOrder
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (hFHC : HasFiniteHorizontalComplexity C.centres) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
      Tiling.AxisParallel.Approximation.IsEpsilonApproximation C epsilon phi →
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
      (v.1 + (s : Tiling.Plane)).re < (w.1 + (t : Tiling.Plane)).re →
      (1 / 2 : ℝ) * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) <
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re ∧
      (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re <
        2 * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) := by
  classical
  let A : Set ℝ := horizontalTranslatedVertices C.region C.centres
  let order : HorizontalOrderData A :=
    Classical.choice (horizontalGapAlphabet_finite hTile hFHC)
  have hpointMem : ∀ i : ℤ, order.point i ∈ C.coordinateSpace := by
    intro i
    have hiA : order.point i ∈ A := by
      exact Eq.mp
        (congrArg (fun S : Set ℝ ↦ order.point i ∈ S) order.point_range)
        (Set.mem_range_self i)
    obtain ⟨v, hv, t, ht, hit⟩ := hiA
    rw [hit, Complex.add_re]
    exact C.coordinateSpace.add_mem
      (C.vertex_re_mem v hv) (C.centre_re_mem t ht)
  let pointLift : ℤ → C.coordinateSpace :=
    fun i ↦ ⟨order.point i, hpointMem i⟩
  have hgapMem : ∀ g ∈ order.gapAlphabet, g ∈ C.coordinateSpace := by
    intro g hg
    obtain ⟨i, hi⟩ := order.gap_complete g hg
    rw [hi]
    exact C.coordinateSpace.sub_mem (hpointMem (i + 1)) (hpointMem i)
  let gapLift : ↑order.gapAlphabet → C.coordinateSpace :=
    fun g ↦ ⟨(g : ℝ), hgapMem g g.2⟩
  have hGnonempty : order.gapAlphabet.Nonempty :=
    ⟨order.point (0 + 1) - order.point 0, order.gap_mem 0⟩
  let gmin : ℝ := order.gapAlphabet.min' hGnonempty
  have hgmin_mem : gmin ∈ order.gapAlphabet := by
    exact order.gapAlphabet.min'_mem hGnonempty
  have hgmin_pos : 0 < gmin := order.gap_pos gmin hgmin_mem
  obtain ⟨epsilon, hepsilon, hcontrol⟩ :=
    approximation_uniformOnHorizontalAlphabet C order.gapAlphabet hgapMem
      (half_pos hgmin_pos)
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi
  have hgapLower : ∀ g : ↑order.gapAlphabet,
      (1 / 2 : ℝ) * (g : ℝ) <
        Tiling.AxisParallel.Approximation.mapScalar phi (gapLift g) := by
    intro g
    have herr := hcontrol phi hphi (g : ℝ) g.2
    have hminle : gmin ≤ (g : ℝ) :=
      order.gapAlphabet.min'_le (g : ℝ) g.2
    have hpos := order.gap_pos (g : ℝ) g.2
    dsimp [gapLift] at herr ⊢
    have herr' := (abs_lt.mp herr).1
    linarith
  have hgapUpper : ∀ g : ↑order.gapAlphabet,
      Tiling.AxisParallel.Approximation.mapScalar phi (gapLift g) <
        2 * (g : ℝ) := by
    intro g
    have herr := hcontrol phi hphi (g : ℝ) g.2
    have hminle : gmin ≤ (g : ℝ) :=
      order.gapAlphabet.min'_le (g : ℝ) g.2
    have hpos := order.gap_pos (g : ℝ) g.2
    dsimp [gapLift] at herr ⊢
    have herr' := (abs_lt.mp herr).2
    linarith
  have hindexed := finitePositiveGaps_control_indexedDifferences
    C order phi pointLift (fun _ ↦ rfl) gapLift (fun _ ↦ rfl)
      hgapLower hgapUpper
  intro v w s t hvw
  have hvA : (v.1 + (s : Tiling.Plane)).re ∈ A :=
    ⟨v.1, v.2, s.1, s.2, rfl⟩
  have hwA : (w.1 + (t : Tiling.Plane)).re ∈ A :=
    ⟨w.1, w.2, t.1, t.2, rfl⟩
  obtain ⟨i, hi⟩ : ∃ i, order.point i =
      (v.1 + (s : Tiling.Plane)).re := by
    exact order.point_range.symm.subset hvA
  obtain ⟨j, hj⟩ : ∃ j, order.point j =
      (w.1 + (t : Tiling.Plane)).re := by
    exact order.point_range.symm.subset hwA
  have hij : i < j := order.point_strictMono.lt_iff_lt.mp
    (hi.trans_lt (hvw.trans_eq hj.symm))
  have hbounds := hindexed i j hij
  have hpointi : pointLift i =
      ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
        ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ := by
    apply Subtype.ext
    simp [pointLift, hi, Complex.add_re]
  have hpointj : pointLift j =
      ⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ +
        ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
    apply Subtype.ext
    simp [pointLift, hj, Complex.add_re]
  have hmapi : Tiling.AxisParallel.Approximation.mapScalar phi (pointLift i) =
      (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2) +
        Tiling.AxisParallel.Approximation.mapPoint phi
            (C.centrePoint s.1 s.2)).re := by
    have hadd : Tiling.AxisParallel.Approximation.mapScalar phi
          (⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
            ⟨s.1.re, C.centre_re_mem s.1 s.2⟩) =
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ := by
      change ((↑(phi (_ + _)) : ℝ)) = (↑(phi _) : ℝ) + (↑(phi _) : ℝ)
      rw [map_add, Rat.cast_add]
    rw [hpointi]
    rw [hadd]
    simp [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint]
  have hmapj : Tiling.AxisParallel.Approximation.mapScalar phi (pointLift j) =
      (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2) +
        Tiling.AxisParallel.Approximation.mapPoint phi
            (C.centrePoint t.1 t.2)).re := by
    have hadd : Tiling.AxisParallel.Approximation.mapScalar phi
          (⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ +
            ⟨t.1.re, C.centre_re_mem t.1 t.2⟩) =
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ +
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      change ((↑(phi (_ + _)) : ℝ)) = (↑(phi _) : ℝ) + (↑(phi _) : ℝ)
      rw [map_add, Rat.cast_add]
    rw [hpointj]
    rw [hadd]
    simp [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint]
  rw [hi, hj, hmapi, hmapj] at hbounds
  exact hbounds

theorem approximation_preservesGlobalHorizontalSign
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (hFHC : HasFiniteHorizontalComplexity C.centres) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      ∀ phi : C.coordinateSpace →ₗ[ℚ] ℚ,
      Tiling.AxisParallel.Approximation.IsEpsilonApproximation C epsilon phi →
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
      Real.sign ((w.1 + (t : Tiling.Plane)).re -
        (v.1 + (s : Tiling.Plane)).re) =
      Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re) := by
  obtain ⟨epsilon, hepsilon, horder⟩ :=
    approximation_preservesGlobalHorizontalOrder C hTile hFHC
  refine ⟨epsilon, hepsilon, ?_⟩
  intro phi hphi v w s t
  let originalDifference : ℝ :=
    (w.1 + (t : Tiling.Plane)).re - (v.1 + (s : Tiling.Plane)).re
  let mappedDifference : ℝ :=
    (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w.1 w.2) +
        Tiling.AxisParallel.Approximation.mapPoint phi
          (C.centrePoint t.1 t.2)).re -
      (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v.1 v.2) +
        Tiling.AxisParallel.Approximation.mapPoint phi
          (C.centrePoint s.1 s.2)).re
  change Real.sign originalDifference = Real.sign mappedDifference
  rcases lt_trichotomy originalDifference 0 with hneg | hzero | hpos
  · have hswapped :
        (w.1 + (t : Tiling.Plane)).re <
          (v.1 + (s : Tiling.Plane)).re := by
      change (w.1 + (t : Tiling.Plane)).re -
        (v.1 + (s : Tiling.Plane)).re < 0 at hneg
      exact sub_neg.mp hneg
    have hbounds := horder phi hphi w v t s hswapped
    have hmappedneg : mappedDifference < 0 := by
      have hsourcepos : 0 <
          (v.1 + (s : Tiling.Plane)).re -
            (w.1 + (t : Tiling.Plane)).re := sub_pos.mpr hswapped
      have hmapdiffpos : 0 <
          (Tiling.AxisParallel.Approximation.mapPoint phi
                (C.vertexPoint v.1 v.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi
                (C.centrePoint s.1 s.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi
                (C.vertexPoint w.1 w.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi
                (C.centrePoint t.1 t.2)).re := by
        linarith [hbounds.1]
      change
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re < 0
      linarith
    rw [Real.sign_of_neg hneg, Real.sign_of_neg hmappedneg]
  · have hcoord :
        (⟨w.1.re, C.vertex_re_mem w.1 w.2⟩ : C.coordinateSpace) +
            ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ =
          ⟨v.1.re, C.vertex_re_mem v.1 v.2⟩ +
            ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ := by
      apply Subtype.ext
      change (w.1.re + t.1.re) - (v.1.re + s.1.re) = 0 at hzero
      change w.1.re + t.1.re = v.1.re + s.1.re
      linarith
    have hmapcoord := congrArg phi hcoord
    have hmapcoordReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hmapcoord
    simp only [map_add, Rat.cast_add] at hmapcoordReal
    have hmappedzero : mappedDifference = 0 := by
      dsimp [mappedDifference]
      simp only [Tiling.AxisParallel.Approximation.mapPoint,
        Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
        Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact sub_eq_zero.mpr hmapcoordReal
    rw [hzero, hmappedzero, Real.sign_zero]
  · have horiginal :
        (v.1 + (s : Tiling.Plane)).re <
          (w.1 + (t : Tiling.Plane)).re := by
      change 0 < (w.1 + (t : Tiling.Plane)).re -
        (v.1 + (s : Tiling.Plane)).re at hpos
      exact sub_pos.mp hpos
    have hbounds := horder phi hphi v w s t horiginal
    have hmappedpos : 0 < mappedDifference := by
      have hsourcepos : 0 <
          (w.1 + (t : Tiling.Plane)).re -
            (v.1 + (s : Tiling.Plane)).re := sub_pos.mpr horiginal
      change 0 <
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re
      linarith [hbounds.1]
    rw [Real.sign_of_pos hpos, Real.sign_of_pos hmappedpos]

end Tiling.AxisParallel.Continuous
