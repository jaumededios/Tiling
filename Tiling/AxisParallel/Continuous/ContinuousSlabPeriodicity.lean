import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.OneDimensional.PeriodicPointEnumeration
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalFLCAlphabet
import Tiling.AxisParallel.Continuous.ApproximationPreservesEarthquakes
import Tiling.AxisParallel.Continuous.RationalSlabPeriodicity

/-!
# Continuous slab boundary words

The intrinsic labelled boundary-word API and the algebraic reflection of a rationalized period
through an approximation which separates the original adjacent-gap alphabet.
-/

open Set

namespace Tiling.AxisParallel.Continuous

structure SlabBoundaryWord
    (K : Region) (T : Set Tiling.Plane) where
  boundary : Set ℝ
  position : ℤ → ℝ
  position_strictMono : StrictMono position
  position_range : Set.range position = boundary
  label : ℤ → Set Tiling.Plane
  label_is_component : ∀ i : ℤ,
    (label i = verticalColumnCentres K T ∧
      (verticalColumnCentres K T).Nonempty) ∨
    ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ label i = P.centres
  strip_in_labelSupport : ∀ i : ℤ,
    Complex.re ⁻¹' Set.Ioo (position i) (position (i + 1)) ⊆
      regularSupport K (label i)
  boundary_exact :
    boundary =
      frontier {x : ℝ | (x : ℂ) ∈
        regularSupport K (verticalColumnCentres K T)} ∪
      ⋃ P : {P : VerticalPlate K T | ¬ IsVerticalColumn P},
        frontier P.1.base

def SlabBoundaryWord.gapSet
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) : Set ℝ :=
  {g : ℝ | ∃ i : ℤ, g = W.position (i + 1) - W.position i}

def SlabBoundaryWord.IsPeriodic
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) (k : ℕ) (beta : ℝ) : Prop :=
  0 < k ∧ 0 < beta ∧
    ∀ i : ℤ,
      W.position (i + k) = W.position i + beta ∧
      W.label (i + k) = W.label i

theorem SlabBoundaryWord.gapSet_eq
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) :
    W.gapSet =
      {g : ℝ | ∃ i : ℤ,
        g = W.position (i + 1) - W.position i} :=
  rfl

theorem SlabBoundaryWord.isPeriodic_iff
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) (k : ℕ) (beta : ℝ) :
    W.IsPeriodic k beta ↔
      0 < k ∧ 0 < beta ∧
      ∀ i : ℤ,
        W.position (i + k) = W.position i + beta ∧
        W.label (i + k) = W.label i :=
  Iff.rfl

private theorem mapScalar_sub
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    {x y : ℝ} (hx : x ∈ C.coordinateSpace) (hy : y ∈ C.coordinateSpace) :
    Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨x - y, C.coordinateSpace.sub_mem hx hy⟩ =
      Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hx⟩ -
        Tiling.AxisParallel.Approximation.mapScalar phi ⟨y, hy⟩ := by
  have hsub :
      (⟨x - y, C.coordinateSpace.sub_mem hx hy⟩ : C.coordinateSpace) =
        ⟨x, hx⟩ - ⟨y, hy⟩ := rfl
  simp only [Tiling.AxisParallel.Approximation.mapScalar]
  rw [hsub, map_sub, Rat.cast_sub]

theorem secondApproximation_reflectsSlabBoundaryPeriod
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (_P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (_hFHC : HasFiniteHorizontalComplexity C.centres)
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ,
      W.position i ∈ C.coordinateSpace)
    {k : ℕ} (hk : 0 < k)
    (hInjective : ∀ i j : ℤ,
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨W.position (i + 1) - W.position i,
          C.coordinateSpace.sub_mem
            (hBoundaryMem (i + 1)) (hBoundaryMem i)⟩ =
        Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨W.position (j + 1) - W.position j,
          C.coordinateSpace.sub_mem
            (hBoundaryMem (j + 1)) (hBoundaryMem j)⟩ →
      W.position (i + 1) - W.position i =
        W.position (j + 1) - W.position j)
    (hImagePeriod : ∃ b : ℝ, 0 < b ∧
      ∀ i : ℤ,
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position i, hBoundaryMem i⟩ + b =
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position (i + k), hBoundaryMem (i + k)⟩ ∧
        W.label (i + k) = W.label i) :
    ∃ beta : ℝ, 0 < beta ∧ W.IsPeriodic k beta := by
  obtain ⟨b, _hb, hperiod⟩ := hImagePeriod
  have hgap (i : ℤ) :
      W.position (i + 1) - W.position i =
        W.position ((i + k) + 1) - W.position (i + k) := by
    apply hInjective i (i + k)
    rw [mapScalar_sub C phi (hBoundaryMem (i + 1)) (hBoundaryMem i)]
    rw [mapScalar_sub C phi (hBoundaryMem ((i + k) + 1))
      (hBoundaryMem (i + k))]
    have hi := (hperiod i).1
    have hi1 := (hperiod (i + 1)).1
    have hindex : i + 1 + (k : ℤ) = (i + (k : ℤ)) + 1 := by omega
    rw [hindex] at hi1
    linarith
  let displacement : ℤ → ℝ :=
    fun i ↦ W.position (i + k) - W.position i
  have hdisplacement_succ (i : ℤ) :
      displacement (i + 1) = displacement i := by
    dsimp [displacement]
    have hindex : i + 1 + (k : ℤ) = (i + (k : ℤ)) + 1 := by omega
    rw [hindex]
    linarith [hgap i]
  have hdisplacement (i : ℤ) : displacement i = displacement 0 := by
    refine Int.inductionOn' i 0 rfl ?_ ?_
    · intro j _hj hj
      exact (hdisplacement_succ j).trans hj
    · intro j _hj hj
      calc
        displacement (j - 1) = displacement ((j - 1) + 1) :=
          (hdisplacement_succ (j - 1)).symm
        _ = displacement j := by congr 1; omega
        _ = displacement 0 := hj
  let beta : ℝ := W.position (k : ℤ) - W.position 0
  have hkInt : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
  have hbeta : 0 < beta := by
    exact sub_pos.mpr (W.position_strictMono hkInt)
  refine ⟨beta, hbeta, hk, hbeta, ?_⟩
  intro i
  constructor
  · have hi := hdisplacement i
    dsimp only [displacement] at hi
    simp only [zero_add] at hi
    dsimp only [beta]
    linarith
  · exact (hperiod i).2

end Tiling.AxisParallel.Continuous

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped Pointwise

noncomputable section

namespace Tiling.AxisParallel.Continuous

universe u

private def totalSlabBoundary (K : Region) (T : Set Tiling.Plane) : Set ℝ :=
  frontier {x : ℝ | (x : ℂ) ∈
      regularSupport K (verticalColumnCentres K T)} ∪
    ⋃ P : {P : VerticalPlate K T | ¬ IsVerticalColumn P},
      frontier P.1.base

private def slabComponentFamily (K : Region) (T : Set Tiling.Plane) :
    Set (Set Tiling.Plane) :=
  {S | (S = verticalColumnCentres K T ∧ S.Nonempty) ∨
    ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ S = P.centres}

private def SlabPeriodicityConclusion
    (K : Region) (T : Set Tiling.Plane) (beta : ℝ) : Prop :=
  Tiling.RationalPolygonal.SetPeriodicBy
      (regularSupport K (verticalColumnCentres K T)) ((beta : ℝ) : ℂ) ∧
    ∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
      Tiling.RationalPolygonal.SetPeriodicBy P.support ((beta : ℝ) : ℂ)

private def IsCommonBoundaryWitnessHeight
    (K : Region) (T : Set Tiling.Plane) (y : ℝ) : Prop :=
  (∀ (t : T) (a b : K.vertices),
      a.1.im = b.1.im →
      openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
          (b.1 + (t.1 : Tiling.Plane)) ⊆
        frontier ((t.1 : Tiling.Plane) +ᵥ K.support) \
          ((t.1 : Tiling.Plane) +ᵥ K.vertices) →
      y ≠ (a.1 + (t.1 : Tiling.Plane)).im) ∧
    ∀ x ∈ totalSlabBoundary K T,
      ∃ (t : T) (a b : K.vertices),
        a.1 ≠ b.1 ∧ a.1.re = b.1.re ∧
        x = (a.1 + (t.1 : Tiling.Plane)).re ∧
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
            (b.1 + (t.1 : Tiling.Plane)) ∧
        openSegment ℝ (a.1 + (t.1 : Tiling.Plane))
            (b.1 + (t.1 : Tiling.Plane)) ⊆
          frontier ((t.1 : Tiling.Plane) +ᵥ K.support) \
            ((t.1 : Tiling.Plane) +ᵥ K.vertices)

private theorem carrier_translation_image
    {K : Region} (v₀ : Tiling.Plane) (C : Approximation.ApproximationContext)
    (hcarrier : C.region.openCarrier = (-v₀) +ᵥ K.openCarrier) :
    K.openCarrier = positiveSimilarity 1 v₀ '' C.region.openCarrier := by
  rw [hcarrier, positiveSimilarity_image_eq_vadd_smul, one_smul]
  simp only [vadd_vadd, add_neg_cancel, zero_vadd]

private theorem centres_translation_image
    {T : Set Tiling.Plane} (t₀ : Tiling.Plane)
    (C : Approximation.ApproximationContext)
    (hcentres : C.centres = (-t₀) +ᵥ T) :
    T = positiveSimilarity 1 t₀ '' C.centres := by
  rw [hcentres, positiveSimilarity_image_eq_vadd_smul, one_smul]
  simp only [vadd_vadd, add_neg_cancel, zero_vadd]

private theorem verticalColumnSupport_verticalInvariant
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (y : ℝ) :
    (((y : ℂ) * Complex.I) +ᵥ
        regularSupport K (verticalColumnCentres K T)) =
      regularSupport K (verticalColumnCentres K T) := by
  rw [verticalColumnCentres_eq, regularSupport_iUnion]
  rw [← interior_vadd, ← closure_vadd]
  congr 2
  ext z
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
  constructor
  · rintro ⟨P, hzP⟩
    refine ⟨P, ?_⟩
    have hinv := (VerticalPlate.isCenterColumn_of_isVerticalColumn
      hTile P.1 P.2).2.2.2 y
    have hmem := Set.ext_iff.mp hinv z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
    exact hmem.mp hzP
  · rintro ⟨P, hzP⟩
    refine ⟨P, ?_⟩
    have hinv := (VerticalPlate.isCenterColumn_of_isVerticalColumn
      hTile P.1 P.2).2.2.2 y
    have hmem := Set.ext_iff.mp hinv z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hmem
    exact hmem.mpr hzP

private theorem verticalInvariant_realSection_vadd
    (D : Set Tiling.Plane)
    (hD : ∀ y : ℝ, (((y : ℂ) * Complex.I) +ᵥ D) = D)
    (g : Tiling.Plane) :
    {x : ℝ | (x : ℂ) ∈ g +ᵥ D} =
      g.re +ᵥ {x : ℝ | (x : ℂ) ∈ D} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_vadd_set_iff_neg_vadd_mem]
  have mem_iff_real (z : Tiling.Plane) : z ∈ D ↔ (z.re : ℂ) ∈ D := by
    have hm := Set.ext_iff.mp (hD (-z.im)) (z.re : ℂ)
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem] at hm
    have heq : -( ((-z.im : ℝ) : ℂ) * Complex.I) +ᵥ (z.re : ℂ) = z := by
      apply Complex.ext <;> simp
    rwa [heq] at hm
  rw [mem_iff_real]
  simp only [vadd_eq_add, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
    add_comm]

private theorem real_affine_image_eq_vadd (a : ℝ) (S : Set ℝ) :
    (fun x : ℝ ↦ x + a) '' S = a +ᵥ S := by
  ext x
  simp only [Set.mem_image, Set.mem_vadd_set_iff_neg_vadd_mem]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [add_comm] using hy
  · intro hx
    refine ⟨x - a, ?_, by ring⟩
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hx

private theorem normalization_geometryTransport_core
    {K : Region} {T : Set Tiling.Plane} (v₀ t₀ : Tiling.Plane)
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hcarrier : C.region.openCarrier = (-v₀) +ᵥ K.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ T) (_hTile : TilesOn K T Set.univ) :
    ∃ e : VerticalPlate C.region C.centres ≃ VerticalPlate K T,
      (∀ P, (e P).centres = t₀ +ᵥ P.centres) ∧
      (∀ P, IsVerticalColumn (e P) ↔ IsVerticalColumn P) ∧
      (∀ P, (e P).support = (v₀ + t₀) +ᵥ P.support) ∧
      verticalColumnCentres K T =
        t₀ +ᵥ verticalColumnCentres C.region C.centres ∧
      regularSupport K (verticalColumnCentres K T) =
        (v₀ + t₀) +ᵥ
          regularSupport C.region (verticalColumnCentres C.region C.centres) := by
  have hK := carrier_translation_image v₀ C hcarrier
  have hT := centres_translation_image t₀ C hcentres
  subst T
  let e : VerticalPlate C.region C.centres ≃
      VerticalPlate K (positiveSimilarity 1 t₀ '' C.centres) :=
    verticalPlate_positiveSimilarityEquiv (by norm_num) hK t₀
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro P
    rw [verticalPlate_positiveSimilarityEquiv_centres_image]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  · intro P
    exact (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      (by norm_num) hK t₀ P).symm
  · intro P
    rw [verticalPlate_positiveSimilarityEquiv_support_image]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  · rw [verticalColumnCentres_positiveSimilarity_image (by norm_num) hK]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  · rw [verticalColumnSupport_positiveSimilarity_image (by norm_num) hK]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]

private theorem normalization_geometryTransport
    {K : Region} {T : Set Tiling.Plane} (v₀ t₀ : Tiling.Plane)
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hcarrier : C.region.openCarrier = (-v₀) +ᵥ K.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ T) (hTile : TilesOn K T Set.univ) :
    ∃ e : VerticalPlate C.region C.centres ≃ VerticalPlate K T,
      (∀ P, (e P).centres = t₀ +ᵥ P.centres) ∧
      (∀ P, IsVerticalColumn (e P) ↔ IsVerticalColumn P) ∧
      (∀ P, (e P).support = (v₀ + t₀) +ᵥ P.support) ∧
      verticalColumnCentres K T =
        t₀ +ᵥ verticalColumnCentres C.region C.centres ∧
      regularSupport K (verticalColumnCentres K T) =
        (v₀ + t₀) +ᵥ
          regularSupport C.region (verticalColumnCentres C.region C.centres) ∧
      totalSlabBoundary K T =
        (v₀ + t₀).re +ᵥ totalSlabBoundary C.region C.centres := by
  have hK := carrier_translation_image v₀ C hcarrier
  have hT := centres_translation_image t₀ C hcentres
  subst T
  let e : VerticalPlate C.region C.centres ≃
      VerticalPlate K (positiveSimilarity 1 t₀ '' C.centres) :=
    verticalPlate_positiveSimilarityEquiv (by norm_num) hK t₀
  have heCentres (P : VerticalPlate C.region C.centres) :
      (e P).centres = t₀ +ᵥ P.centres := by
    rw [verticalPlate_positiveSimilarityEquiv_centres_image]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  have heColumn (P : VerticalPlate C.region C.centres) :
      IsVerticalColumn (e P) ↔ IsVerticalColumn P :=
    (verticalPlate_positiveSimilarityEquiv_isVerticalColumn
      (by norm_num) hK t₀ P).symm
  have heSupport (P : VerticalPlate C.region C.centres) :
      (e P).support = (v₀ + t₀) +ᵥ P.support := by
    rw [verticalPlate_positiveSimilarityEquiv_support_image]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  have hcolumns :
      verticalColumnCentres K (positiveSimilarity 1 t₀ '' C.centres) =
        t₀ +ᵥ verticalColumnCentres C.region C.centres := by
    rw [verticalColumnCentres_positiveSimilarity_image (by norm_num) hK]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  have hcolumnSupport :
      regularSupport K
          (verticalColumnCentres K (positiveSimilarity 1 t₀ '' C.centres)) =
        (v₀ + t₀) +ᵥ regularSupport C.region
          (verticalColumnCentres C.region C.centres) := by
    rw [verticalColumnSupport_positiveSimilarity_image (by norm_num) hK]
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
  refine ⟨e, heCentres, heColumn, heSupport, hcolumns, hcolumnSupport, ?_⟩
  have hCTile : TilesOn C.region C.centres Set.univ := by
    have himageTarget : positiveSimilarity 1 (v₀ + t₀) '' Set.univ =
        (Set.univ : Set Tiling.Plane) := by
      rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
      simp
    apply (tilesOn_positiveSimilarity_iff (by norm_num) hK).mp
    rw [himageTarget]
    exact hTile
  let a : ℝ := (v₀ + t₀).re
  have hcolumnBase :
      {x : ℝ | (x : ℂ) ∈ regularSupport K
        (verticalColumnCentres K (positiveSimilarity 1 t₀ '' C.centres))} =
        a +ᵥ {x : ℝ | (x : ℂ) ∈
          regularSupport C.region (verticalColumnCentres C.region C.centres)} := by
    rw [hcolumnSupport]
    exact verticalInvariant_realSection_vadd _
      (verticalColumnSupport_verticalInvariant hCTile) (v₀ + t₀)
  have hplateBase (P : VerticalPlate C.region C.centres) :
      (e P).base = a +ᵥ P.base := by
    change (verticalPlate_positiveSimilarityEquiv
      (by norm_num) hK t₀ P).base = _
    rw [verticalPlate_positiveSimilarityEquiv_base_affine_real_image]
    have h := real_affine_image_eq_vadd a P.base
    simpa [a] using h
  have hnoncolumn :
      (⋃ Q : {Q : VerticalPlate K (positiveSimilarity 1 t₀ '' C.centres) |
        ¬ IsVerticalColumn Q}, frontier Q.1.base) =
        a +ᵥ (⋃ P : {P : VerticalPlate C.region C.centres |
          ¬ IsVerticalColumn P}, frontier P.1.base) := by
    ext x
    constructor
    · rw [Set.mem_iUnion]
      rintro ⟨Q, hxQ⟩
      let P : VerticalPlate C.region C.centres := e.symm Q.1
      have hPnoncol : ¬ IsVerticalColumn P := by
        intro hP
        apply Q.2
        have : IsVerticalColumn (e P) := (heColumn P).mpr hP
        simpa [P] using this
      rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
      refine ⟨⟨P, hPnoncol⟩, ?_⟩
      have hb := hplateBase P
      have htranslate := (Homeomorph.addLeft a).image_frontier P.base
      simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
      rw [show Q.1 = e P by simp [P], hb, ← htranslate] at hxQ
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem] using hxQ
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_iUnion]
      rintro ⟨P, hxP⟩
      rw [Set.mem_iUnion]
      have heNoncol : ¬ IsVerticalColumn (e P.1) := fun h ↦ P.2 ((heColumn P.1).mp h)
      refine ⟨⟨e P.1, heNoncol⟩, ?_⟩
      have htranslate := (Homeomorph.addLeft a).image_frontier P.1.base
      simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
      rw [hplateBase P.1, ← htranslate]
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem]
  unfold totalSlabBoundary
  have htranslate := (Homeomorph.addLeft a).image_frontier
    {x : ℝ | (x : ℂ) ∈ regularSupport C.region
      (verticalColumnCentres C.region C.centres)}
  simp only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd] at htranslate
  rw [hcolumnBase, ← htranslate]
  rw [hnoncolumn]
  ext x
  simp only [Set.mem_union, Set.mem_vadd_set_iff_neg_vadd_mem, a]

private theorem normalizedContext_exists :
    ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      HasFiniteHorizontalComplexity T →
      ∃ (v₀ t₀ : Tiling.Plane) (_hv₀ : v₀ ∈ K.vertices) (_ht₀ : t₀ ∈ T)
        (C : Tiling.AxisParallel.Approximation.ApproximationContext.{u}),
        C.region.openCarrier = (-v₀) +ᵥ K.openCarrier ∧
        C.centres = (-t₀) +ᵥ T ∧ C.target = Set.univ ∧
        TilesOn C.region C.centres Set.univ ∧
        HasFiniteHorizontalComplexity C.centres ∧
        ∀ beta : ℝ, SlabPeriodicityConclusion C.region C.centres beta →
          SlabPeriodicityConclusion K T beta := by
  intro K T hTile hFHC
  obtain ⟨v₀, hv₀, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
  obtain ⟨z, hz⟩ := hTile.2.2.exists
  obtain ⟨t₀, _hzt₀⟩ := hz.mp (Set.mem_univ z)
  obtain ⟨C, hCcarrier, hCcentres, hCtarget, hCtile⟩ :=
    Tiling.AxisParallel.Approximation.normalizeApproximationContext
      K T Set.univ v₀ hv₀ t₀.1 t₀.2
  have htarget : C.target = Set.univ := by
    rw [hCtarget]
    simp
  have hCTile : TilesOn C.region C.centres Set.univ := by
    rw [← htarget]
    exact hCtile.mp hTile
  have hprojection : horizontalCentreProjection C.centres =
      (-t₀.1.re) +ᵥ horizontalCentreProjection T := by
    ext x
    rw [horizontalCentreProjection, horizontalCentreProjection, hCcentres]
    constructor
    · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨s.re, ⟨s, hs, rfl⟩, ?_⟩
      simp
    · rintro ⟨r, ⟨s, hs, rfl⟩, rfl⟩
      refine ⟨-t₀.1 + s, ⟨s, hs, by simp⟩, ?_⟩
      simp
  have hCFHC : HasFiniteHorizontalComplexity C.centres := by
    unfold HasFiniteHorizontalComplexity
    rw [hprojection]
    exact hFHC.vadd (-t₀.1.re)
  refine ⟨v₀, t₀.1, hv₀, t₀.2, C, hCcarrier, hCcentres,
    htarget, hCTile, hCFHC, ?_⟩
  intro beta hperiod
  obtain ⟨e, _heCentres, heColumn, heSupport, _hcolumns, hcolumnSupport,
      _hboundary⟩ :=
    normalization_geometryTransport v₀ t₀.1 C hCcarrier hCcentres hTile
  refine ⟨?_, ?_⟩
  · rw [hcolumnSupport]
    exact Tiling.RationalPolygonal.setPeriodicBy_vadd (v₀ + t₀.1) hperiod.1
  · intro P hP
    let Q : VerticalPlate C.region C.centres := e.symm P
    have hQ : ¬ IsVerticalColumn Q := by
      intro h
      apply hP
      have : IsVerticalColumn (e Q) := (heColumn Q).mpr h
      simpa [Q] using this
    have hs := heSupport Q
    have hp := Tiling.RationalPolygonal.setPeriodicBy_vadd (v₀ + t₀.1)
      (hperiod.2 Q hQ)
    rw [show P = e Q by simp [Q], hs]
    exact hp

theorem verticalColumnCentres_subset
    (K : Region) (T : Set Tiling.Plane) : verticalColumnCentres K T ⊆ T := by
  rw [verticalColumnCentres_eq]
  rintro x hx
  rw [Set.mem_iUnion] at hx
  obtain ⟨P, t, _htP, rfl⟩ := hx
  exact t.2

private theorem regularSupport_mono_local
    (K : Region) {S U : Set Tiling.Plane} (hSU : S ⊆ U) :
    regularSupport K S ⊆ regularSupport K U := by
  unfold regularSupport Tiling.Polygonal.regularSupport
  exact interior_mono (closure_mono (by
    intro x hx
    rw [Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hxs⟩ := hx
    exact ⟨⟨s.1, hSU s.2⟩, hxs⟩))

private theorem verticalColumnSupport_isVerticalSlab
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K (verticalColumnCentres K T) = Complex.re ⁻¹' X := by
  obtain ⟨X, hX⟩ := (verticalInvariant_iff_product
    (regularSupport K (verticalColumnCentres K T))).mp
      (verticalColumnSupport_verticalInvariant hTile)
  have hreg := (regularSupport_isRegularOpen K
    (verticalColumnCentres K T)).2
  change regularSupport K (verticalColumnCentres K T) = Complex.re ⁻¹' X at hX
  rw [hX, Complex.closure_preimage_re, Complex.interior_preimage_re] at hreg
  refine ⟨X, ?_, hX⟩
  ext x
  have hx := Set.ext_iff.mp hreg (x : ℂ)
  simpa using hx.symm

private theorem slabComponents_partition
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    (∀ S ∈ slabComponentFamily K T, S ⊆ T) ∧
    (∀ S ∈ slabComponentFamily K T,
      ∃ X : Set ℝ, X = interior (closure X) ∧
        regularSupport K S = Complex.re ⁻¹' X) ∧
    (∀ S ∈ slabComponentFamily K T,
      ∀ U ∈ slabComponentFamily K T, S ≠ U →
        Disjoint (regularSupport K S) (regularSupport K U)) ∧
    (⋃ S : slabComponentFamily K T,
      regularSupport K (S : Set Tiling.Plane)) =ᵐ[MeasureTheory.volume] Set.univ := by
  have hplateSubset (P : VerticalPlate K T) : P.centres ⊆ T := by
    rintro x ⟨t, _ht, rfl⟩
    exact t.2
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨p, hp⟩ := P.nonempty_supp
    refine ⟨p, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P p).1 hp
  have hplatePartition := regularSupport_pairwiseDisjoint
    (@VerticalPlate.centres K T) (verticalPlateCentres_pairwiseDisjoint K T)
      (iUnion_verticalPlateCentres K T) hTile
  have hcolumnNoncolumn (P : VerticalPlate K T) (hP : ¬ IsVerticalColumn P) :
      Disjoint (regularSupport K (verticalColumnCentres K T)) P.support := by
    let parts : Bool → Set Tiling.Plane
      | false => verticalColumnCentres K T
      | true => T \ verticalColumnCentres K T
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact Set.disjoint_left.2 fun _ hx hy ↦ hy.2 hx
      · exact Set.disjoint_left.2 fun _ hx hy ↦ hx.2 hy
      · exact (hij rfl).elim
    have hunion : (⋃ i, parts i) = T := by
      ext x
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi⟩
        cases i
        · exact verticalColumnCentres_subset K T hi
        · exact hi.1
      · intro hx
        by_cases hc : x ∈ verticalColumnCentres K T
        · exact ⟨false, hc⟩
        · exact ⟨true, hx, hc⟩
    have hdisj := (regularSupport_pairwiseDisjoint parts hparts hunion hTile).1
      (Set.mem_univ false) (Set.mem_univ true) (by decide)
    have hPcomp : P.centres ⊆ T \ verticalColumnCentres K T := by
      intro x hx
      refine ⟨hplateSubset P hx, ?_⟩
      intro hxc
      rw [verticalColumnCentres_eq, Set.mem_iUnion] at hxc
      obtain ⟨Q, hxQ⟩ := hxc
      have hmeet : (P.centres ∩ Q.1.centres).Nonempty := ⟨x, hx, hxQ⟩
      have : P = Q.1 := by
        by_contra hne
        have hd := verticalPlateCentres_pairwiseDisjoint K T
          (Set.mem_univ P) (Set.mem_univ Q.1) hne
        exact Set.not_nonempty_iff_eq_empty.mpr hd.inter_eq hmeet
      exact hP (this ▸ Q.2)
    exact hdisj.mono_right (regularSupport_mono_local K hPcomp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    rcases hS with ⟨rfl, _⟩ | ⟨P, _hP, rfl⟩
    · exact verticalColumnCentres_subset K T
    · exact hplateSubset P
  · intro S hS
    rcases hS with ⟨rfl, _⟩ | ⟨P, _hP, rfl⟩
    · exact verticalColumnSupport_isVerticalSlab hTile
    · exact ⟨P.base, (P.support_isVerticalSlab hTile).1,
        (P.support_isVerticalSlab hTile).2⟩
  · intro S hS U hU hSU
    rcases hS with ⟨rfl, _⟩ | ⟨P, hP, rfl⟩
    · rcases hU with ⟨hU, _⟩ | ⟨Q, hQ, rfl⟩
      · exact (hSU hU.symm).elim
      · exact hcolumnNoncolumn Q hQ
    · rcases hU with ⟨rfl, _⟩ | ⟨Q, hQ, rfl⟩
      · exact (hcolumnNoncolumn P hP).symm
      · have hPQ : P ≠ Q := by
          intro heq
          apply hSU
          rw [heq]
        exact hplatePartition.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
  · filter_upwards [hplatePartition.2] with x hx
    apply propext
    constructor
    · intro _
      exact Set.mem_univ x
    · intro _
      change x ∈ ⋃ S : slabComponentFamily K T,
        regularSupport K (S : Set Tiling.Plane)
      have hxmem : x ∈ ⋃ P : VerticalPlate K T,
          regularSupport K P.centres := by
        change (⋃ P : VerticalPlate K T, regularSupport K P.centres) x
        rw [hx]
        trivial
      rw [Set.mem_iUnion] at hxmem ⊢
      obtain ⟨P, hxP⟩ := hxmem
      by_cases hP : IsVerticalColumn P
      · have hcolNe : (verticalColumnCentres K T).Nonempty := by
          obtain ⟨p, hp⟩ := P.nonempty_supp
          have hpCentres : p.1 ∈ P.centres := ⟨p, hp, rfl⟩
          exact ⟨p.1, Set.mem_iUnion.2 ⟨⟨P, hP⟩, hpCentres⟩⟩
        refine ⟨⟨verticalColumnCentres K T, Or.inl ⟨rfl, hcolNe⟩⟩, ?_⟩
        exact regularSupport_mono_local K (by
          intro z hz
          exact Set.mem_iUnion.2 ⟨⟨P, hP⟩, hz⟩) hxP
      · exact ⟨⟨P.centres, Or.inr ⟨P, hP, rfl⟩⟩, hxP⟩

private theorem boundaryPoint_excludedFromOpenUnion
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∀ S ∈ slabComponentFamily K T, ∀ x : ℝ,
      x ∈ frontier {r : ℝ | (r : ℂ) ∈ regularSupport K S} →
      ∀ y : ℝ, (x : ℂ) + (y : ℂ) * Complex.I ∉ openUnion K T := by
  classical
  intro S hS x hx y hzOpen
  obtain ⟨X, hXreg, hSsupport⟩ := (slabComponents_partition hTile).2.1 S hS
  have hbase : {r : ℝ | (r : ℂ) ∈ regularSupport K S} = X := by
    rw [hSsupport]
    ext r
    simp
  have hxFront : x ∈ frontier X := hbase ▸ hx
  let z : Tiling.Plane := (x : ℂ) + (y : ℂ) * Complex.I
  have hzClosureS : z ∈ closure (regularSupport K S) := by
    rw [hSsupport, Complex.closure_preimage_re]
    simpa [z] using frontier_subset_closure hxFront
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzOpen
  obtain ⟨t, hzt⟩ := hzOpen
  let P : VerticalPlate K T := VerticalPlate.ofCentre t
  have htP : (t.1 : Tiling.Plane) ∈ P.centres := VerticalPlate.mem_centres_ofCentre t
  let U : Set Tiling.Plane := if hP : IsVerticalColumn P then
      verticalColumnCentres K T else P.centres
  have hU : U ∈ slabComponentFamily K T := by
    dsimp [U]
    split_ifs with hP
    · left
      refine ⟨rfl, ?_⟩
      exact ⟨t.1, Set.mem_iUnion.2 ⟨⟨P, hP⟩, htP⟩⟩
    · exact Or.inr ⟨P, hP, rfl⟩
  have htU : (t.1 : Tiling.Plane) ∈ U := by
    dsimp [U]
    split_ifs with hP
    · exact Set.mem_iUnion.2 ⟨⟨P, hP⟩, htP⟩
    · exact htP
  have hzU : z ∈ regularSupport K U := by
    unfold regularSupport
    have hopen : IsOpen (openUnion K U) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
      exact isOpen_iUnion fun r : U ↦
        (Homeomorph.addLeft (r : Tiling.Plane)).isOpenMap _ isOpen_interior
    apply hopen.subset_interior_closure
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨t.1, htU⟩, hzt⟩
  by_cases hUS : U = S
  · rw [hUS, hSsupport] at hzU
    have hxX : x ∈ X := by simpa [z] using hzU
    have hXopen : IsOpen X := by rw [hXreg]; exact isOpen_interior
    exact hxFront.2 (mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hxX))
  · have hdisj := (slabComponents_partition hTile).2.2.1 U hU S hS hUS
    exact Set.disjoint_left.1
      (hdisj.closure_right (regularSupport_isRegularOpen K U).1)
      hzU hzClosureS

private theorem totalBoundary_mem_componentFrontier
    {K : Region} {T : Set Tiling.Plane} {x : ℝ}
    (hTile : TilesOn K T Set.univ) (hx : x ∈ totalSlabBoundary K T) :
    ∃ S ∈ slabComponentFamily K T,
      x ∈ frontier {r : ℝ | (r : ℂ) ∈ regularSupport K S} := by
  rcases hx with hx | hx
  · have hne : (verticalColumnCentres K T).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty] at hx
      have hsupp : regularSupport K (∅ : Set Tiling.Plane) = ∅ := by
        unfold regularSupport Tiling.Polygonal.regularSupport Tiling.Polygonal.openUnion
        simp
      rw [hsupp] at hx
      simp at hx
    exact ⟨verticalColumnCentres K T, Or.inl ⟨rfl, hne⟩, hx⟩
  · rw [Set.mem_iUnion] at hx
    obtain ⟨P, hxP⟩ := hx
    refine ⟨P.1.centres, Or.inr ⟨P.1, P.2, rfl⟩, ?_⟩
    have hbase : {r : ℝ | (r : ℂ) ∈ regularSupport K P.1.centres} = P.1.base := by
      change {r : ℝ | (r : ℂ) ∈ P.1.support} = P.1.base
      rw [(P.1.support_isVerticalSlab hTile).2]
      ext r
      simp
    rwa [hbase]

private theorem boundaryPoint_hasPlacedFrontierWitness
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∀ x ∈ totalSlabBoundary K T, ∀ y : ℝ,
      ∃ t : T, (x : ℂ) + (y : ℂ) * Complex.I ∈
        frontier ((t.1 : Tiling.Plane) +ᵥ K.support) := by
  intro x hx y
  obtain ⟨S, hS, hxS⟩ := totalBoundary_mem_componentFrontier hTile hx
  have hzNotOpen := boundaryPoint_excludedFromOpenUnion hTile S hS x hxS y
  let z : Tiling.Plane := (x : ℂ) + (y : ℂ) * Complex.I
  have hzClosure : z ∈ closure (openUnion K T) := by
    have hwhole : regularSupport K T = Set.univ :=
      regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion] at hwhole
    exact interior_subset (hwhole.symm ▸ Set.mem_univ z)
  rw [closure_openUnion_eq_iUnion_support hTile.2.1] at hzClosure
  rw [Set.mem_iUnion] at hzClosure
  obtain ⟨t, hzt⟩ := hzClosure
  refine ⟨t, ?_⟩
  rw [(K.isPolygonal.vadd t.1).isClosed.frontier_eq]
  refine ⟨hzt, ?_⟩
  intro hzInterior
  apply hzNotOpen
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  refine ⟨t, ?_⟩
  rw [interior_vadd] at hzInterior
  exact hzInterior

private theorem segment_re_eq_local {a b z : Tiling.Plane}
    (hab : a.re = b.re) (hz : z ∈ segment ℝ a b) : z.re = a.re := by
  rw [segment_eq_image] at hz
  obtain ⟨r, _hr, rfl⟩ := hz
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring

private theorem segment_im_eq_local {a b z : Tiling.Plane}
    (hab : a.im = b.im) (hz : z ∈ segment ℝ a b) : z.im = a.im := by
  rw [segment_eq_image] at hz
  obtain ⟨r, _hr, rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem exists_commonGenericBoundaryHeight
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∃ y : ℝ, IsCommonBoundaryWitnessHeight K T y := by
  let _ : Countable T := hTile.1.to_subtype
  have hVfinite : K.vertices.Finite := by
    simpa only [Region.vertices] using K.isPolygonal.vertexSet_finite
  let _ : Countable K.vertices := hVfinite.countable.to_subtype
  let forbidden : Set ℝ := Set.range fun p : T × K.vertices ↦ p.1.1.im + p.2.1.im
  have hcount : forbidden.Countable := Set.countable_range _
  have hne : forbidden ≠ Set.univ := by
    intro h
    apply Cardinal.not_countable_real
    rw [← h]
    exact hcount
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem forbidden).mp hne
  refine ⟨y, ?_, ?_⟩
  · intro t a b hab _hedge heq
    apply hy
    refine ⟨(t, a), ?_⟩
    simpa [Complex.add_im, add_comm] using heq.symm
  · intro x hx
    obtain ⟨t, hztFront⟩ := boundaryPoint_hasPlacedFrontierWitness hTile x hx y
    let z : Tiling.Plane := (x : ℂ) + (y : ℂ) * Complex.I
    let p : Tiling.Plane := z - t.1
    have hpFront : p ∈ frontier K.support := by
      rw [frontier_vadd_eq] at hztFront
      simpa [p, Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg,
        add_comm] using hztFront
    have hpNotVertex : p ∉ K.vertices := by
      intro hp
      apply hy
      refine ⟨(t, ⟨p, hp⟩), ?_⟩
      norm_num [p, z]
    obtain ⟨axis, a, b, hab, hcoord, hpseg, hedge⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
        K p hpFront hpNotVertex
    cases axis with
    | horizontal =>
        exfalso
        apply hy
        refine ⟨(t, a), ?_⟩
        have hpim := segment_im_eq_local hcoord
          (openSegment_subset_segment ℝ a.1 b.1 hpseg)
        norm_num [p, z] at hpim
        linarith
    | vertical =>
        have hpre := segment_re_eq_local hcoord
          (openSegment_subset_segment ℝ a.1 b.1 hpseg)
        refine ⟨t, a, b, hab, hcoord, ?_, ?_, ?_⟩
        · norm_num [p, z] at hpre
          simp only [Complex.add_re]
          linarith
        · have hzseg : t.1 +ᵥ p ∈
              openSegment ℝ (t.1 +ᵥ a.1) (t.1 +ᵥ b.1) := by
            rw [← vadd_openSegment ℝ]
            exact ⟨p, hpseg, rfl⟩
          simpa [p, z, vadd_eq_add, add_comm] using hzseg
        · rw [frontier_vadd_eq]
          rw [show a.1 + t.1 = t.1 +ᵥ a.1 by simp [vadd_eq_add, add_comm],
            show b.1 + t.1 = t.1 +ᵥ b.1 by simp [vadd_eq_add, add_comm],
            ← vadd_openSegment ℝ]
          rintro q ⟨r, hr, rfl⟩
          refine ⟨⟨r, (hedge hr).1, rfl⟩, ?_⟩
          intro hv
          rcases hv with ⟨q, hq, heq⟩
          have : q = r := by
            simpa using add_left_cancel heq
          exact (hedge hr).2 (this ▸ hq)

private theorem relevantTilesFinite
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (Q : Set Tiling.Plane) (hQ : Bornology.IsBounded Q) :
    {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty}.Finite := by
  let C : Set Tiling.Plane := Q - K.support
  have hC : Bornology.IsBounded C := hQ.sub K.isPolygonal.isBounded
  apply ((Tiling.AxisParallel.IsPacking.locallyFinite_centres hTile.2.1).1 C hC).subset
  rintro t ⟨ht, z, hzt, hzQ⟩
  refine ⟨ht, ?_⟩
  rw [Set.mem_sub]
  rw [Set.mem_vadd_set] at hzt
  obtain ⟨k, hk, rfl⟩ := hzt
  exact ⟨t + k, hzQ, k, hk, by simp⟩

private theorem compactBoundary_finite_of_commonHeight
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    {y : ℝ} (hy : IsCommonBoundaryWitnessHeight K T y) :
    ∀ a b : ℝ, (totalSlabBoundary K T ∩ Set.Icc a b).Finite := by
  intro a b
  let f : ℝ → Tiling.Plane := fun x ↦ (x : ℂ) + (y : ℂ) * Complex.I
  let Q : Set Tiling.Plane := f '' Set.Icc a b
  have hf : Continuous f := by fun_prop
  have hQcompact : IsCompact Q := (isCompact_Icc.image hf)
  let F : Set Tiling.Plane :=
    {t : Tiling.Plane | t ∈ T ∧ ((t +ᵥ K.support) ∩ Q).Nonempty}
  have hF : F.Finite := relevantTilesFinite hTile Q hQcompact.isBounded
  have hV : K.vertices.Finite := by
    simpa only [Region.vertices] using K.isPolygonal.vertexSet_finite
  let coords : Set ℝ :=
    (fun p : Tiling.Plane × Tiling.Plane ↦ (p.1 + p.2).re) '' (K.vertices ×ˢ F)
  have hcoords : coords.Finite := (hV.prod hF).image _
  apply hcoords.subset
  rintro x ⟨hxB, hxIcc⟩
  obtain ⟨t, v, w, _hvw, _hre, hxcoord, hzseg, hedge⟩ := hy.2 x hxB
  have hztSupport : f x ∈ t.1 +ᵥ K.support := by
    exact (K.isPolygonal.vadd t.1).isClosed.frontier_subset (hedge hzseg).1
  have htF : t.1 ∈ F := by
    refine ⟨t.2, f x, hztSupport, ?_⟩
    exact ⟨x, hxIcc, rfl⟩
  refine ⟨(v.1, t.1), ⟨v.2, htF⟩, ?_⟩
  simpa [coords, add_comm] using hxcoord.symm

private theorem totalSlabBoundary_horizontalTranslatedVertices
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    totalSlabBoundary K T ⊆ horizontalTranslatedVertices K T := by
  intro x hx
  obtain ⟨y, hy⟩ := exists_commonGenericBoundaryHeight hTile
  obtain ⟨t, a, _b, _hab, _hre, hxcoord, _hz, _hedge⟩ := hy.2 x hx
  exact ⟨a.1, a.2, t.1, t.2, hxcoord⟩

private theorem totalSlabBoundary_coordinate :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T Set.univ →
      totalSlabBoundary K T ⊆ horizontalTranslatedVertices K T) ∧
    (∀ (C : Tiling.AxisParallel.Approximation.ApproximationContext.{u}),
      TilesOn C.region C.centres Set.univ →
      totalSlabBoundary C.region C.centres ⊆ C.coordinateSpace) := by
  constructor
  · exact fun hTile ↦ totalSlabBoundary_horizontalTranslatedVertices hTile
  · intro C hTile x hx
    obtain ⟨v, hv, t, ht, hcoord⟩ :=
      (show totalSlabBoundary C.region C.centres ⊆
        horizontalTranslatedVertices C.region C.centres from
          (by
            intro q hq
            exact (show ∀ {K : Region} {T : Set Tiling.Plane},
              TilesOn K T Set.univ → totalSlabBoundary K T ⊆
                horizontalTranslatedVertices K T from by
                  intro K T hT
                  obtain ⟨y, hy⟩ := exists_commonGenericBoundaryHeight hT
                  intro r hr
                  obtain ⟨s, a, _b, _hab, _hre, hc, _hz, _he⟩ := hy.2 r hr
                  exact ⟨a.1, a.2, s.1, s.2, hc⟩) hTile hq)) hx
    rw [hcoord]
    exact C.coordinateSpace.add_mem (C.vertex_re_mem v hv) (C.centre_re_mem t ht)

private theorem totalSlabBoundary_locallyFinite
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    ∀ a b : ℝ, (totalSlabBoundary K T ∩ Set.Icc a b).Finite := by
  obtain ⟨y, hy⟩ := exists_commonGenericBoundaryHeight hTile
  exact compactBoundary_finite_of_commonHeight hTile hy

private theorem verticalPlate_base_nonempty_local
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T) :
    P.base.Nonempty := by
  obtain ⟨t, ht⟩ := P.nonempty_supp
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  refine ⟨(t.1 + u).re, t.1 + u, ?_, rfl⟩
  change t.1 + u ∈ regularSupport K P.centres
  unfold regularSupport
  have hopen : IsOpen (openUnion K P.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
    exact isOpen_iUnion fun s : P.centres ↦ isOpen_interior.vadd s.1
  apply hopen.subset_interior_closure
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  refine ⟨⟨t.1, ⟨t, ht, rfl⟩⟩, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  have hu' : u ∈ K.openCarrier := by
    rw [← K.openCarrier_regularOpen.2,
      show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
    exact hu
  simpa only [vadd_eq_add, neg_add_cancel_left] using hu'

private theorem totalSlabBoundary_nonempty
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (hNoFull : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hNotColumns : T ≠ verticalColumnCentres K T) :
    (totalSlabBoundary K T).Nonempty := by
  have hcolSub := verticalColumnCentres_subset K T
  obtain ⟨t, htT, htCol⟩ : ∃ t, t ∈ T ∧ t ∉ verticalColumnCentres K T := by
    by_contra h
    push Not at h
    exact hNotColumns (Set.Subset.antisymm h hcolSub)
  let tT : T := ⟨t, htT⟩
  let P : VerticalPlate K T := VerticalPlate.ofCentre tT
  have htP : t ∈ P.centres := VerticalPlate.mem_centres_ofCentre tT
  have hPnoncol : ¬ IsVerticalColumn P := by
    intro hP
    apply htCol
    exact Set.mem_iUnion.2 ⟨⟨P, hP⟩, htP⟩
  have hPproper : P.base ≠ Set.univ := by
    intro hbase
    have hfull : P.support = Set.univ := by
      rw [(P.support_isVerticalSlab hTile).2, hbase]
      simp
    exact hNoFull ⟨P, hPnoncol, plate_centres_eq_of_support_eq_univ hTile P hfull⟩
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr
    ⟨verticalPlate_base_nonempty_local P, hPproper⟩
  exact ⟨x, Or.inr (Set.mem_iUnion_of_mem ⟨P, hPnoncol⟩ hx)⟩

private theorem normalization_wordTransport
    {K : Region} {T : Set Tiling.Plane} (v₀ t₀ : Tiling.Plane)
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hcarrier : C.region.openCarrier = (-v₀) +ᵥ K.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ T) (hTile : TilesOn K T Set.univ)
    (W : SlabBoundaryWord C.region C.centres) :
    ∃ W₀ : SlabBoundaryWord K T,
      (∀ i : ℤ, W₀.position i = W.position i + (v₀ + t₀).re) ∧
      (∀ i : ℤ, W₀.label i = t₀ +ᵥ W.label i) ∧
      W₀.boundary = (v₀ + t₀).re +ᵥ W.boundary ∧
      W₀.gapSet = W.gapSet ∧
      ∀ R : ℝ, (∀ i : ℤ, W.position (i + 1) - W.position i < R) →
        ∀ i : ℤ, W₀.position (i + 1) - W₀.position i < R := by
  obtain ⟨e, heCentres, heColumn, _heSupport, hcolumns, _hcolumnSupport,
      hboundary⟩ := normalization_geometryTransport v₀ t₀ C hcarrier hcentres hTile
  have hK := carrier_translation_image v₀ C hcarrier
  have hT := centres_translation_image t₀ C hcentres
  have hsupport (S : Set Tiling.Plane) :
      regularSupport K (t₀ +ᵥ S) =
        (v₀ + t₀) +ᵥ regularSupport C.region S := by
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using
      (positiveSimilarity_regularSupport_image (c := t₀) (S := S) (by norm_num) hK)
  let pos : ℤ → ℝ := fun i ↦ W.position i + (v₀ + t₀).re
  let lab : ℤ → Set Tiling.Plane := fun i ↦ t₀ +ᵥ W.label i
  let B : Set ℝ := (v₀ + t₀).re +ᵥ W.boundary
  have hmono : StrictMono pos := by
    intro i j hij
    dsimp [pos]
    linarith [W.position_strictMono hij]
  have hrange : Set.range pos = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      have hi : W.position i ∈ W.boundary := by
        rw [← W.position_range]
        exact ⟨i, rfl⟩
      exact ⟨W.position i, hi, by simp [pos, add_comm]⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨i, rfl⟩ := W.position_range ▸ hq
      exact ⟨i, by simp [pos, add_comm]⟩
  have hlabel (i : ℤ) :
      (lab i = verticalColumnCentres K T ∧
        (verticalColumnCentres K T).Nonempty) ∨
      ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ lab i = P.centres := by
    rcases W.label_is_component i with ⟨h, hne⟩ | ⟨P, hP, h⟩
    · left
      refine ⟨?_, ?_⟩
      · dsimp [lab]
        rw [h, ← hcolumns]
      · rw [hcolumns]
        obtain ⟨q, hq⟩ := hne
        exact ⟨t₀ + q, q, hq, rfl⟩
    · right
      refine ⟨e P, (heColumn P).not.mpr hP, ?_⟩
      dsimp [lab]
      rw [h]
      exact (heCentres P).symm
  have hstrip (i : ℤ) :
      Complex.re ⁻¹' Set.Ioo (pos i) (pos (i + 1)) ⊆ regularSupport K (lab i) := by
    rw [hsupport]
    intro z hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    apply W.strip_in_labelSupport i
    change (-((v₀ + t₀).re) + z.re) ∈ Set.Ioo (W.position i) (W.position (i + 1))
    dsimp [pos] at hz
    norm_num at hz ⊢
    constructor <;> linarith
  let W₀ : SlabBoundaryWord K T :=
    { boundary := B
      position := pos
      position_strictMono := hmono
      position_range := hrange
      label := lab
      label_is_component := hlabel
      strip_in_labelSupport := hstrip
      boundary_exact := by
        change B = totalSlabBoundary K T
        rw [hboundary]
        exact congrArg ((v₀ + t₀).re +ᵥ ·) W.boundary_exact }
  refine ⟨W₀, fun _ ↦ rfl, fun _ ↦ rfl, rfl, ?_, ?_⟩
  · ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, by dsimp [W₀, pos]; ring⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, by dsimp [W₀, pos]; ring⟩
  · intro R hR i
    simpa only [W₀, pos] using (show
      W.position (i + 1) + (v₀ + t₀).re -
        (W.position i + (v₀ + t₀).re) < R by linarith [hR i])

private theorem slabGapSet_subset_horizontalBoundedDifferences
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (W : SlabBoundaryWord K T) {R₀ : ℝ}
    (hBoundary : W.boundary = totalSlabBoundary K T)
    (hGap : ∀ i : ℤ, 0 < W.position (i + 1) - W.position i ∧
      W.position (i + 1) - W.position i < R₀) :
    W.gapSet ⊆ horizontalBoundedDifferences
      (horizontalTranslatedVertices K T) R₀ := by
  rintro g ⟨i, rfl⟩
  have hi : W.position i ∈ totalSlabBoundary K T := by
    rw [← hBoundary, ← W.position_range]
    exact Set.mem_range_self i
  have hi1 : W.position (i + 1) ∈ totalSlabBoundary K T := by
    rw [← hBoundary, ← W.position_range]
    exact Set.mem_range_self (i + 1)
  refine ⟨W.position i, totalSlabBoundary_horizontalTranslatedVertices hTile hi,
    W.position (i + 1),
    totalSlabBoundary_horizontalTranslatedVertices hTile hi1, rfl, ?_⟩
  rw [abs_of_pos (hGap i).1]
  exact (hGap i).2.le

theorem slabBoundaryGapAlphabet_finite
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hFHC : HasFiniteHorizontalComplexity T)
    (W : SlabBoundaryWord K T) {R₀ : ℝ} (_hR₀ : 0 < R₀)
    (hGap : ∀ i : ℤ, W.position (i + 1) - W.position i < R₀) :
    W.gapSet.Finite := by
  apply (horizontalBoundedDifferences_finite hFHC R₀).subset
  apply slabGapSet_subset_horizontalBoundedDifferences hTile W W.boundary_exact
  intro i
  exact ⟨sub_pos.mpr (W.position_strictMono (by omega)), hGap i⟩

private noncomputable def strictMono_orderIso_image
    {A : Set ℝ} (f : A → ℝ) (hf : StrictMono f) :
    A ≃o {y : ℝ | ∃ x : A, y = f x} := by
  let inv : {y : ℝ | ∃ x : A, y = f x} → A := fun y ↦
    Classical.choose y.2
  have hinv (y : {y : ℝ | ∃ x : A, y = f x}) :
      (y : ℝ) = f (inv y) := Classical.choose_spec y.2
  exact
    { toFun := fun x ↦ ⟨f x, x, rfl⟩
      invFun := inv
      left_inv := by
        intro x
        apply hf.injective
        exact (hinv ⟨f x, x, rfl⟩).symm
      right_inv := by
        intro y
        exact Subtype.ext (hinv y).symm
      map_rel_iff' := by
        intro x y
        exact hf.le_iff_le }

private theorem baseFrontier_periodic_of_supportPeriodic
    {S : Set Tiling.Plane} {b : ℝ}
    (hper : Tiling.RationalPolygonal.SetPeriodicBy S ((b : ℝ) : ℂ)) :
    ∀ y : ℝ,
      y ∈ frontier {x : ℝ | (x : ℂ) ∈ S} ↔
        y + b ∈ frontier {x : ℝ | (x : ℂ) ∈ S} := by
  let A : Set ℝ := {x : ℝ | (x : ℂ) ∈ S}
  have hshift : b +ᵥ A = A := by
    ext x
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_add_eq_sub]
    change x - b ∈ A ↔ x ∈ A
    change (((x - b : ℝ) : ℂ) ∈ S) ↔ ((x : ℝ) : ℂ) ∈ S
    have hp := hper (((x - b : ℝ) : ℂ))
    simpa using hp.symm
  have hfrontier : b +ᵥ frontier A = frontier A := by
    simpa only [Homeomorph.coe_addLeft, ← vadd_eq_add, Set.image_vadd, hshift]
      using (Homeomorph.addLeft b).image_frontier A
  intro y
  constructor
  · intro hy
    have : b + y ∈ b +ᵥ frontier A := ⟨y, hy, rfl⟩
    rw [hfrontier] at this
    simpa [A, add_comm] using this
  · intro hy
    have hy' : y + b ∈ b +ᵥ frontier A := by
      rw [hfrontier]
      simpa [A] using hy
    obtain ⟨z, hz, hbz⟩ := hy'
    have : z = y := by simpa [vadd_eq_add, add_comm] using hbz
    simpa [A, this] using hz

private theorem iUnion_baseFrontier_periodic
    {families : Set (Set Tiling.Plane)} {targetSupport : Set Tiling.Plane → Set Tiling.Plane}
    {b : ℝ}
    (hper : ∀ S ∈ families,
      Tiling.RationalPolygonal.SetPeriodicBy (targetSupport S) ((b : ℝ) : ℂ)) :
    ∀ y : ℝ,
      y ∈ ⋃ S ∈ families,
          frontier {x : ℝ | (x : ℂ) ∈ targetSupport S} ↔
        y + b ∈ ⋃ S ∈ families,
          frontier {x : ℝ | (x : ℂ) ∈ targetSupport S} := by
  intro y
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨S, hSf, hyS⟩
    exact ⟨S, hSf, (baseFrontier_periodic_of_supportPeriodic (hper S hSf) y).mp hyS⟩
  · simp only [Set.mem_iUnion]
    rintro ⟨S, hSf, hyS⟩
    exact ⟨S, hSf, (baseFrontier_periodic_of_supportPeriodic (hper S hSf) y).mpr hyS⟩

private theorem deformedComponentSupport_periodic
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    {b : ℝ}
    (hperiod :
      Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport D.deformedRegion
            (verticalColumnCentres D.deformedRegion
              (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters)))
          ((b : ℝ) : ℂ) ∧
        ∀ Q : VerticalPlate D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters),
          ¬ IsVerticalColumn Q →
            Tiling.RationalPolygonal.SetPeriodicBy Q.support ((b : ℝ) : ℂ)) :
    ∀ S ∈ slabComponentFamily C.region C.centres,
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Tiling.Plane) ∈ S})) ((b : ℝ) : ℂ) := by
  let hContact := deformation_preservesProperHorizontalContact C phi D P hHorizontalSign
  let e := deformation_verticalPlateEquiv C phi D P hContact
  intro S hS
  rcases hS with ⟨rfl, _hcolne⟩ | ⟨Q, hQnoncol, rfl⟩
  · have hcarrier :
        Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Tiling.Plane) ∈
              verticalColumnCentres C.region C.centres} =
          verticalColumnCentres D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
      ext y
      constructor
      · rintro ⟨t, ht, rfl⟩
        rw [verticalColumnCentres_eq] at ht ⊢
        obtain ⟨Q, htQ⟩ := Set.mem_iUnion.mp ht
        let Q' := e Q.1
        have hQ' : IsVerticalColumn Q' :=
          (deformation_preservesColumns C phi D P hContact hHorizontalSign Q.1).mp Q.2
        refine Set.mem_iUnion.mpr ⟨⟨Q', hQ'⟩, ?_⟩
        rw [deformation_verticalPlateEquiv_centres C phi D P hContact Q.1]
        exact ⟨t, htQ, rfl⟩
      · intro hy
        rw [verticalColumnCentres_eq] at hy ⊢
        obtain ⟨Q', hyQ'⟩ := Set.mem_iUnion.mp hy
        let Q := e.symm Q'.1
        have hQ : IsVerticalColumn Q := by
          apply (deformation_preservesColumns C phi D P hContact hHorizontalSign Q).mpr
          have heq : e Q = Q'.1 := by simp [Q]
          rw [heq]
          exact Q'.2
        have hcentres := deformation_verticalPlateEquiv_centres C phi D P hContact Q
        have heq : e Q = Q'.1 := by simp [Q, e]
        rw [heq] at hcentres
        rw [hcentres] at hyQ'
        obtain ⟨t, htQ, rfl⟩ := hyQ'
        refine ⟨t, ?_, rfl⟩
        change (t : Tiling.Plane) ∈ verticalColumnCentres C.region C.centres
        rw [verticalColumnCentres_eq, Set.mem_iUnion]
        exact ⟨⟨Q, hQ⟩, htQ⟩
    rw [hcarrier]
    exact hperiod.1
  · have hcarrier := deformation_verticalPlateEquiv_centres C phi D P hContact Q
    rw [← hcarrier]
    rw [← VerticalPlate.support_eq_regularSupport]
    exact hperiod.2 (e Q)
      (fun hcol ↦ hQnoncol
        ((deformation_preservesColumns C phi D P hContact hHorizontalSign Q).mpr hcol))

private theorem deformedTotalBoundary_periodic_core
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    (families : Set (Set Tiling.Plane))
    (hFamiliesSub : ∀ S ∈ families, S ⊆ C.centres)
    (hFamiliesSlab : ∀ S ∈ families, ∃ X : Set ℝ,
      X = interior (closure X) ∧ regularSupport C.region S = Complex.re ⁻¹' X)
    (B : Set ℝ) (hBmem : ∀ x ∈ B, x ∈ C.coordinateSpace)
    (hB : B = ⋃ S ∈ families,
      frontier {x : ℝ | (x : ℂ) ∈ regularSupport C.region S})
    {b : ℝ} (_hb : 0 < b)
    (hTargetPeriodic : ∀ S ∈ families,
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Tiling.Plane) ∈ S})) ((b : ℝ) : ℂ)) :
    ∀ y : ℝ,
        y ∈ {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ B,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBmem x hx⟩} ↔
        y + b ∈ {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ B,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBmem x hx⟩} := by
  have htransport := deformation_transportsOrderedBoundaryCode C phi D P
    hHorizontalSign families hFamiliesSub hFamiliesSlab B hBmem hB
  rw [htransport.1]
  exact iUnion_baseFrontier_periodic hTargetPeriodic

private theorem firstApproximation_boundsBoundaryGaps_core
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T)
    (mappedGap : ℤ → ℝ)
    (hLower : ∀ i : ℤ,
      (1 / 2 : ℝ) * (W.position (i + 1) - W.position i) < mappedGap i)
    (hMappedBound : ∃ R : ℝ, 0 < R ∧ ∀ i : ℤ, mappedGap i < R) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ i : ℤ, 0 < W.position (i + 1) - W.position i ∧
        W.position (i + 1) - W.position i < R₀ := by
  obtain ⟨R, hR, hMappedBound⟩ := hMappedBound
  refine ⟨2 * R, by positivity, ?_⟩
  intro i
  constructor
  · exact sub_pos.mpr (W.position_strictMono (by omega))
  · linarith [hLower i, hMappedBound i]

private theorem deformedTotalBoundary_periodic_at
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    (b : ℝ) (hb : 0 < b)
    (hRationalPeriod : SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b) :
      ∀ y : ℝ,
        y ∈ {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} ↔
        y + b ∈ {y : ℝ | ∃ x : ℝ,
          ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} := by
  have hTile := P.source_tilesOn
  have hparts := slabComponents_partition hTile
  have hBoundaryFamily :
      totalSlabBoundary C.region C.centres =
        ⋃ S ∈ slabComponentFamily C.region C.centres,
          frontier {x : ℝ | (x : ℂ) ∈ regularSupport C.region S} := by
    ext x
    constructor
    · intro hx
      obtain ⟨S, hS, hxS⟩ := totalBoundary_mem_componentFrontier hTile hx
      exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hS, hxS⟩⟩
    · intro hx
      obtain ⟨S, hxS⟩ := Set.mem_iUnion.1 hx
      obtain ⟨hSfamily, hxS⟩ := Set.mem_iUnion.1 hxS
      rcases hSfamily with ⟨rfl, _⟩ | ⟨Q, hQ, rfl⟩
      · exact Or.inl hxS
      · apply Or.inr
        rw [Set.mem_iUnion]
        refine ⟨⟨Q, hQ⟩, ?_⟩
        have hbase : {r : ℝ | (r : ℂ) ∈ regularSupport C.region Q.centres} = Q.base := by
          change {r : ℝ | (r : ℂ) ∈ Q.support} = Q.base
          rw [(Q.support_isVerticalSlab hTile).2]
          ext r
          simp
        rwa [hbase] at hxS
  apply deformedTotalBoundary_periodic_core C phi D P hHorizontalSign
    (slabComponentFamily C.region C.centres) hparts.1 hparts.2.1
    (totalSlabBoundary C.region C.centres) hBoundaryMem hBoundaryFamily hb
  exact deformedComponentSupport_periodic C phi D P hHorizontalSign hRationalPeriod

private theorem deformedTotalBoundary_periodic
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    (hRationalPeriod : ∃ b : ℝ, 0 < b ∧
      SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b) :
    ∃ b : ℝ, 0 < b ∧
      ∀ y : ℝ,
        y ∈ {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} ↔
        y + b ∈ {y : ℝ | ∃ x : ℝ,
          ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
          y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} := by
  obtain ⟨b, hb, hperiod⟩ := hRationalPeriod
  exact ⟨b, hb, deformedTotalBoundary_periodic_at C phi D P hBoundaryMem
    hHorizontalSign b hb hperiod⟩

private theorem verticalPlate_eq_of_common_centre
    {K : Region} {T : Set Tiling.Plane} {P Q : VerticalPlate K T}
    {t : Tiling.Plane} (htP : t ∈ P.centres) (htQ : t ∈ Q.centres) : P = Q := by
  obtain ⟨s, hsP, rfl⟩ := htP
  obtain ⟨u, huQ, hsu⟩ := htQ
  have hsu' : s = u := Subtype.ext hsu.symm
  subst u
  exact (show (verticalPlateGraph K T).connectedComponentMk s = P from hsP).symm.trans
    (show (verticalPlateGraph K T).connectedComponentMk s = Q from huQ)

private theorem whole_regularSupport_eq_univ
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    regularSupport K T = Set.univ :=
  Tiling.AxisParallel.regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile

private theorem slabBoundaryWord_of_orderAndLabels
    {K : Region} {T : Set Tiling.Plane} {B : Set ℝ}
    (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = B)
    (label : ℤ → Set Tiling.Plane)
    (hlabel : ∀ i : ℤ,
      (label i = verticalColumnCentres K T ∧
        (verticalColumnCentres K T).Nonempty) ∨
      ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ label i = P.centres)
    (hstrip : ∀ i : ℤ,
      Complex.re ⁻¹' Set.Ioo (point i) (point (i + 1)) ⊆
        regularSupport K (label i))
    (hboundary : B =
      frontier {x : ℝ | (x : ℂ) ∈
        regularSupport K (verticalColumnCentres K T)} ∪
      ⋃ P : {P : VerticalPlate K T | ¬ IsVerticalColumn P},
        frontier P.1.base) :
    ∃ W : SlabBoundaryWord K T,
      W.boundary = B ∧ W.position = point ∧ W.label = label := by
  let W : SlabBoundaryWord K T :=
    { boundary := B
      position := point
      position_strictMono := hmono
      position_range := hrange
      label := label
      label_is_component := hlabel
      strip_in_labelSupport := hstrip
      boundary_exact := hboundary }
  exact ⟨W, rfl, rfl, rfl⟩

private theorem boundaryWord_base_eq_iUnion_of_componentPartition
    {K : Region} {T : Set Tiling.Plane} (W : SlabBoundaryWord K T)
    (Family : Set (Set Tiling.Plane))
    (hlabel : ∀ i : ℤ, W.label i ∈ Family)
    (hdisjoint : ∀ S ∈ Family, ∀ U ∈ Family, S ≠ U →
      Disjoint (regularSupport K S) (regularSupport K U))
    (hboundary : W.boundary =
      ⋃ S : {S : Set Tiling.Plane // S ∈ Family},
        frontier {x : ℝ | (x : ℂ) ∈ regularSupport K S.1})
    (hbracket : ∀ x : ℝ, x ∉ W.boundary →
      ∃! i : ℤ, x ∈ Set.Ioo (W.position i) (W.position (i + 1))) :
    ∀ S ∈ Family,
      {x : ℝ | (x : ℂ) ∈ regularSupport K S} =
        ⋃ i : {i : ℤ // W.label i = S},
          Set.Ioo (W.position i) (W.position (i + 1)) := by
  intro S hSF
  let base : (Set Tiling.Plane) → Set ℝ :=
    fun U ↦ {x : ℝ | (x : ℂ) ∈ regularSupport K U}
  have hopen (U : Set Tiling.Plane) : IsOpen (base U) :=
    isOpen_interior.preimage Complex.continuous_ofReal
  have hbaseDisjoint (U : Set Tiling.Plane) (hUF : U ∈ Family) (hSU : S ≠ U) :
      Disjoint (base S) (base U) := by
    rw [Set.disjoint_left]
    intro x hxS hxU
    exact Set.disjoint_left.1 (hdisjoint S hSF U hUF hSU) hxS hxU
  apply Set.Subset.antisymm
  · intro x hxS
    have hxBoundary : x ∉ W.boundary := by
      rw [hboundary, Set.mem_iUnion]
      rintro ⟨U, hxU⟩
      by_cases hSU : S = U.1
      · rw [← hSU] at hxU
        rw [(hopen S).frontier_eq] at hxU
        exact hxU.2 hxS
      · have hd := (hbaseDisjoint U.1 U.2 hSU).closure_right (hopen S)
        exact Set.disjoint_left.1 hd hxS (frontier_subset_closure hxU)
    obtain ⟨i, hi, -⟩ := hbracket x hxBoundary
    have hxLabel : (x : ℂ) ∈ regularSupport K (W.label i) :=
      W.strip_in_labelSupport i hi
    have hlabelEq : W.label i = S := by
      by_contra hne
      exact Set.disjoint_left.1 (hdisjoint S hSF (W.label i) (hlabel i) (Ne.symm hne))
        hxS hxLabel
    exact Set.mem_iUnion.mpr ⟨⟨i, hlabelEq⟩, hi⟩
  · rw [Set.iUnion_subset_iff]
    intro i x hx
    exact i.2 ▸ W.strip_in_labelSupport i.1 hx

private theorem exists_mem_open_of_ae_local
    {U : Set Tiling.Plane} {P : Tiling.Plane → Prop}
    (hU : IsOpen U) (hUne : U.Nonempty) (hP : ∀ᵐ z ∂MeasureTheory.volume, P z) :
    ∃ z ∈ U, P z := by
  have hμ : MeasureTheory.volume.restrict U ≠ 0 := by
    intro hz
    have hzero : MeasureTheory.volume U = 0 := by
      rw [← MeasureTheory.Measure.restrict_apply_univ U, hz]
      simp
    exact hU.measure_ne_zero MeasureTheory.volume hUne hzero
  let hne : (MeasureTheory.ae (MeasureTheory.volume.restrict U)).NeBot :=
    MeasureTheory.ae_neBot.mpr hμ
  have hP' : ∀ᵐ z ∂MeasureTheory.volume.restrict U, P z :=
    hP.filter_mono MeasureTheory.ae_restrict_le
  rcases @Filter.Eventually.exists Tiling.Plane _
      (MeasureTheory.ae (MeasureTheory.volume.restrict U)) hne
      (hP'.and (MeasureTheory.ae_restrict_mem hU.measurableSet)) with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private theorem stripLabel_exists
    {K : Region} {B : Set ℝ}
    (Family : Set (Set Tiling.Plane))
    (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = B)
    (hslab : ∀ S ∈ Family, ∃ X : Set ℝ,
      X = interior (closure X) ∧ regularSupport K S = Complex.re ⁻¹' X)
    (hfrontier : ∀ S ∈ Family, ∀ X : Set ℝ,
      regularSupport K S = Complex.re ⁻¹' X → frontier X ⊆ B)
    (hcover : (⋃ S : {S : Set Tiling.Plane // S ∈ Family},
      regularSupport K S.1) =ᵐ[MeasureTheory.volume] Set.univ) :
    ∀ i : ℤ, ∃ S ∈ Family,
      Complex.re ⁻¹' Set.Ioo (point i) (point (i + 1)) ⊆ regularSupport K S := by
  intro i
  have hii : point i < point (i + 1) := hmono (by omega)
  let U : Set Tiling.Plane := Complex.re ⁻¹' Set.Ioo (point i) (point (i + 1))
  have hUopen : IsOpen U := isOpen_Ioo.preimage Complex.continuous_re
  have hUne : U.Nonempty := by
    refine ⟨(((point i + point (i + 1)) / 2 : ℝ) : ℂ), ?_⟩
    change (point i + point (i + 1)) / 2 ∈ Set.Ioo (point i) (point (i + 1))
    constructor <;> linarith
  have hae : ∀ᵐ z ∂MeasureTheory.volume,
      z ∈ ⋃ S : {S : Set Tiling.Plane // S ∈ Family}, regularSupport K S.1 := by
    filter_upwards [hcover] with z hz
    exact hz.mpr (Set.mem_univ z)
  obtain ⟨z, hzU, hzCover⟩ := exists_mem_open_of_ae_local hUopen hUne hae
  rw [Set.mem_iUnion] at hzCover
  obtain ⟨S, hzS⟩ := hzCover
  obtain ⟨X, hXreg, hSX⟩ := hslab S.1 S.2
  refine ⟨S.1, S.2, ?_⟩
  have hIfront : Disjoint (Set.Ioo (point i) (point (i + 1))) (frontier X) := by
    rw [Set.disjoint_left]
    intro x hxI hxF
    have hxB : x ∈ B := hfrontier S.1 S.2 X hSX hxF
    obtain ⟨j, hj⟩ := hrange.symm.subset hxB
    rw [← hj] at hxI
    by_cases hji : j ≤ i
    · exact (not_lt_of_ge (hmono.monotone hji)) hxI.1
    · have hij : i + 1 ≤ j := by omega
      exact (not_lt_of_ge (hmono.monotone hij)) hxI.2
  have hbase : Set.Ioo (point i) (point (i + 1)) ⊆ X := by
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
        isPreconnected_Ioo hIfront with hin | hout
    · exact hin.trans interior_subset
    · have hzX : z.re ∈ X := by simpa [hSX] using hzS
      have hzI : z.re ∈ Set.Ioo (point i) (point (i + 1)) := hzU
      exact False.elim ((interior_subset (hout hzI)) hzX)
  intro w hw
  rw [hSX]
  exact hbase hw

private theorem vadd_eq_of_mem_add_iff
    {B : Set ℝ} {b : ℝ} (hperiod : ∀ x : ℝ, x ∈ B ↔ x + b ∈ B) :
    b +ᵥ B = B := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [add_comm] using (hperiod y).mp hy
  · intro hx
    refine ⟨x - b, ?_, by simp⟩
    exact (hperiod (x - b)).mpr (by simpa using hx)

private theorem strictMono_int_cobounded_of_locallyFinite
    {B : Set ℝ} {point : ℤ → ℝ}
    (hmono : StrictMono point) (hrange : Set.range point = B)
    (hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite) :
    (∀ x : ℝ, ∃ i : ℤ, point i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < point i) := by
  constructor
  · intro x
    by_contra h
    push Not at h
    have hsubset : Set.range (fun n : ℕ ↦ point (-(n : ℤ))) ⊆
        B ∩ Set.Icc x (point 0) := by
      rintro y ⟨n, rfl⟩
      refine ⟨hrange ▸ ⟨-(n : ℤ), rfl⟩, h _, ?_⟩
      exact hmono.monotone (neg_nonpos.mpr (Int.natCast_nonneg n))
    have hinj : Function.Injective (fun n : ℕ ↦ point (-(n : ℤ))) := by
      intro m n hmn
      have : -(m : ℤ) = -(n : ℤ) := hmono.injective hmn
      exact_mod_cast (neg_inj.mp this)
    exact Set.infinite_range_of_injective hinj
      ((hlocal x (point 0)).subset hsubset)
  · intro x
    by_contra h
    push Not at h
    have hsubset : Set.range (fun n : ℕ ↦ point (n : ℤ)) ⊆
        B ∩ Set.Icc (point 0) x := by
      rintro y ⟨n, rfl⟩
      refine ⟨hrange ▸ ⟨(n : ℤ), rfl⟩, ?_, h _⟩
      exact hmono.monotone (Int.natCast_nonneg n)
    have hinj : Function.Injective (fun n : ℕ ↦ point (n : ℤ)) := by
      intro m n hmn
      exact_mod_cast hmono.injective hmn
    exact Set.infinite_range_of_injective hinj
      ((hlocal (point 0) x).subset hsubset)

private theorem strictMono_int_complementPartition
    {B : Set ℝ} {point : ℤ → ℝ}
    (hmono : StrictMono point) (hrange : Set.range point = B)
    (hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite) :
    ∀ x : ℝ, x ∉ B →
      ∃! i : ℤ, x ∈ Set.Ioo (point i) (point (i + 1)) := by
  intro x hx
  obtain ⟨hbelow, habove⟩ :=
    strictMono_int_cobounded_of_locallyFinite hmono hrange hlocal
  obtain ⟨lo, hlo⟩ := hbelow x
  obtain ⟨hi, hhi⟩ := habove x
  have hlohi : lo < hi := by
    by_contra h
    have := hmono.monotone (le_of_not_gt h)
    linarith
  let P : ℕ → Prop := fun n ↦ point (hi - (n : ℤ)) < x
  have hP : ∃ n, P n := by
    refine ⟨(Int.toNat (hi - lo)), ?_⟩
    have hnonneg : 0 ≤ hi - lo := sub_nonneg.mpr hlohi.le
    have hcast : (Int.toNat (hi - lo) : ℤ) = hi - lo :=
      Int.toNat_of_nonneg hnonneg
    simpa [P, hcast] using hlo
  let n := Nat.find hP
  have hnP : point (hi - (n : ℤ)) < x := Nat.find_spec hP
  have hn0 : 0 < n := by
    by_contra hn
    have hnEq : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hnEq] at hnP
    simp only [Nat.cast_zero, sub_zero] at hnP
    linarith
  let i : ℤ := hi - (n : ℤ)
  have hprev : x < point (i + 1) := by
    have hnot := Nat.find_min hP (Nat.pred_lt (ne_of_gt hn0))
    have hpred : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    have hindex : hi - ((n - 1 : ℕ) : ℤ) = i + 1 := by
      simp only [hpred, i]
      ring
    change ¬point (hi - ((n - 1 : ℕ) : ℤ)) < x at hnot
    rw [hindex] at hnot
    exact lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm (fun heq ↦ hx (hrange ▸ ⟨i + 1, heq⟩)))
  refine ⟨i, ⟨hnP, hprev⟩, ?_⟩
  intro j hj
  by_contra hij
  rcases lt_or_gt_of_ne hij with hji | hij
  · have hle : j + 1 ≤ i := by omega
    have := hmono.monotone hle
    linarith [hj.2, hnP]
  · have hle : i + 1 ≤ j := by omega
    have := hmono.monotone hle
    linarith [hprev, hj.1]

private theorem totalSlabBoundary_integerOrder
    {B B' : Set ℝ} (e : B ≃o B') {b : ℝ}
    (hB' : B'.Nonempty) (hb : 0 < b)
    (hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite)
    (hlocal' : ∀ a c : ℝ, (B' ∩ Set.Icc a c).Finite)
    (hperiod : ∀ x : ℝ, x ∈ B' ↔ x + b ∈ B') :
    ∃ point : ℤ → ℝ, StrictMono point ∧ Set.range point = B ∧
      (∀ x : ℝ, ∃ i : ℤ, point i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < point i) := by
  have hbounded : ∀ Q : Set ℝ, Bornology.IsBounded Q → (B' ∩ Q).Finite := by
    intro Q hQ
    exact (hlocal' (sInf Q) (sSup Q)).subset
      (inter_subset_inter_right B' hQ.subset_Icc_sInf_sSup)
  let E := Tiling.AxisParallel.OneDimensional.periodicIntEnumeration_exists
    B' b hb hB' hbounded (vadd_eq_of_mem_add_iff hperiod)
  let enum := E.some
  have hpoint_mem (i : ℤ) : enum.point i ∈ B' := by
    exact enum.point_range.subset (Set.mem_range_self i)
  let point : ℤ → ℝ := fun i ↦ e.symm ⟨enum.point i,
    hpoint_mem i⟩
  have hmono : StrictMono point := e.symm.strictMono.comp enum.point_strictMono
  have hrange : Set.range point = B := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (e.symm ⟨enum.point i, hpoint_mem i⟩).property
    · intro hx
      obtain ⟨i, hi⟩ := enum.point_range.symm.subset (e ⟨x, hx⟩).property
      have hsub : e.symm ⟨enum.point i, hpoint_mem i⟩ = ⟨x, hx⟩ := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext hi
      refine ⟨i, ?_⟩
      simpa [point] using congrArg Subtype.val hsub
  exact ⟨point, hmono, hrange,
    (strictMono_int_cobounded_of_locallyFinite hmono hrange hlocal).1,
    (strictMono_int_cobounded_of_locallyFinite hmono hrange hlocal).2⟩

private theorem periodicLocallyFiniteSet_boundedGaps
    {B : Set ℝ} {b : ℝ} (_hB : B.Nonempty) (hb : 0 < b)
    (_hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite)
    (hperiod : ∀ x : ℝ, x ∈ B ↔ x + b ∈ B)
    (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = B) :
    ∃ R : ℝ, 0 < R ∧ ∀ i : ℤ, point (i + 1) - point i < R := by
  refine ⟨b + 1, by linarith, ?_⟩
  intro i
  have hmem : point i + b ∈ B := (hperiod (point i)).mp (hrange ▸ ⟨i, rfl⟩)
  obtain ⟨j, hj⟩ := hrange.symm.subset hmem
  have hij : i < j := by
    apply (hmono.lt_iff_lt).mp
    rw [hj]
    linarith
  have hsucc : i + 1 ≤ j := by omega
  have := hmono.monotone hsucc
  rw [hj] at this
  linarith

private theorem labelledIntervals_periodic
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) {k : ℕ} {beta : ℝ}
    (_hk : 0 < k) (_hbeta : 0 < beta) (hper : W.IsPeriodic k beta)
    (S : Set Tiling.Plane) :
    Tiling.RationalPolygonal.SetPeriodicBy
      (Complex.re ⁻¹' (⋃ i : {i : ℤ // W.label i = S},
        Set.Ioo (W.position i) (W.position (i + 1))))
      ((beta : ℝ) : ℂ) := by
  intro z
  change z.re + beta ∈
      ⋃ i : {i : ℤ // W.label i = S},
        Set.Ioo (W.position i) (W.position (i + 1)) ↔
    z.re ∈ ⋃ i : {i : ℤ // W.label i = S},
      Set.Ioo (W.position i) (W.position (i + 1))
  constructor
  · rw [Set.mem_iUnion]
    rintro ⟨i, hi⟩
    let j : ℤ := i.1 - (k : ℤ)
    have hji : j + (k : ℤ) = i.1 := by omega
    have hjlabel : W.label j = S := by
      rw [← i.2, ← hji]
      exact (hper.2.2 j).2.symm
    refine Set.mem_iUnion.mpr ⟨⟨j, hjlabel⟩, ?_⟩
    have hpj := (hper.2.2 j).1
    have hpj1 := (hper.2.2 (j + 1)).1
    have hsucc : j + 1 + (k : ℤ) = i.1 + 1 := by omega
    rw [hji] at hpj
    rw [hsucc] at hpj1
    constructor <;> linarith [hi.1, hi.2]
  · rw [Set.mem_iUnion]
    rintro ⟨i, hi⟩
    have hilabel : W.label (i.1 + (k : ℤ)) = S :=
      (hper.2.2 i.1).2.trans i.2
    refine Set.mem_iUnion.mpr ⟨⟨i.1 + (k : ℤ), hilabel⟩, ?_⟩
    have hpi := (hper.2.2 i.1).1
    have hpi1 := (hper.2.2 (i.1 + 1)).1
    have hsucc : i.1 + 1 + (k : ℤ) = i.1 + (k : ℤ) + 1 := by omega
    rw [hsucc] at hpi1
    constructor <;> linarith [hi.1, hi.2]

private theorem supportPeriodic_of_periodic_of_decoder
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) {k : ℕ} {beta : ℝ}
    (hk : 0 < k) (hbeta : 0 < beta) (hper : W.IsPeriodic k beta)
    (hdecoder : ∀ S : Set Tiling.Plane,
      ((S = verticalColumnCentres K T ∧ S.Nonempty) ∨
        ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ S = P.centres) →
      regularSupport K S =
        Complex.re ⁻¹' (⋃ i : {i : ℤ // W.label i = S},
          Set.Ioo (W.position i) (W.position (i + 1)))) :
    SlabPeriodicityConclusion K T beta := by
  have hdecodedPeriodic (S : Set Tiling.Plane)
      (hS : (S = verticalColumnCentres K T ∧ S.Nonempty) ∨
        ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ S = P.centres) :
      Tiling.RationalPolygonal.SetPeriodicBy (regularSupport K S)
        ((beta : ℝ) : ℂ) := by
    rw [hdecoder S hS]
    exact labelledIntervals_periodic W hk hbeta hper S
  constructor
  · by_cases hcol : (verticalColumnCentres K T).Nonempty
    · exact hdecodedPeriodic _ (Or.inl ⟨rfl, hcol⟩)
    · have hempty : verticalColumnCentres K T = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hcol
      simp [hempty, Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
        Tiling.Polygonal.openUnion, Tiling.RationalPolygonal.SetPeriodicBy]
  · intro P hP
    rw [VerticalPlate.support_eq_regularSupport]
    exact hdecodedPeriodic P.centres (Or.inr ⟨P, hP, rfl⟩)

private theorem singleNoncolumn_degenerate
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (hfull : ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T) :
    SlabPeriodicityConclusion K T 1 := by
  obtain ⟨P, hPnoncol, hPT⟩ := hfull
  have hPsupport : P.support = Set.univ := by
    rw [VerticalPlate.support_eq_regularSupport, hPT]
    exact whole_regularSupport_eq_univ hTile
  have hcols : verticalColumnCentres K T = ∅ := by
    rw [verticalColumnCentres_eq]
    apply Set.iUnion_eq_empty.mpr
    intro Q
    ext t
    simp only [Set.mem_empty_iff_false, iff_false]
    intro htQ
    obtain ⟨q, hqQ, rfl⟩ := htQ
    have hqP : (q : Tiling.Plane) ∈ P.centres := hPT.symm ▸ q.2
    have hQP : Q.1 = P := verticalPlate_eq_of_common_centre ⟨q, hqQ, rfl⟩ hqP
    exact hPnoncol (hQP ▸ Q.2)
  constructor
  · simp [hcols, Tiling.AxisParallel.regularSupport, Tiling.Polygonal.regularSupport,
      Tiling.Polygonal.openUnion, Tiling.RationalPolygonal.SetPeriodicBy]
  · intro Q hQ
    have hQP : Q = P := by
      obtain ⟨s, hs⟩ := Q.nonempty_supp
      have hsQ : (s : Tiling.Plane) ∈ Q.centres := ⟨s, hs, rfl⟩
      have hsP : (s : Tiling.Plane) ∈ P.centres := hPT.symm ▸ s.2
      exact verticalPlate_eq_of_common_centre hsQ hsP
    rw [hQP, hPsupport]
    simp [Tiling.RationalPolygonal.SetPeriodicBy]

private theorem allColumns_degenerate
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (hcols : T = verticalColumnCentres K T) :
    SlabPeriodicityConclusion K T 1 := by
  constructor
  · rw [← hcols, whole_regularSupport_eq_univ hTile]
    simp [Tiling.RationalPolygonal.SetPeriodicBy]
  · intro P hP
    exfalso
    obtain ⟨s, hs⟩ := P.nonempty_supp
    have hsP : (s : Tiling.Plane) ∈ P.centres := ⟨s, hs, rfl⟩
    have hscol : (s : Tiling.Plane) ∈ verticalColumnCentres K T := by
      have hsT : (s : Tiling.Plane) ∈ T := s.2
      exact hcols.subset hsT
    rw [verticalColumnCentres_eq, Set.mem_iUnion] at hscol
    obtain ⟨Q, hsQ⟩ := hscol
    have hPQ : P = Q.1 := verticalPlate_eq_of_common_centre hsP hsQ
    exact hP (hPQ ▸ Q.2)

private theorem boundaryWord_complementPartition
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) (hTile : TilesOn K T Set.univ) :
    ∀ x : ℝ, x ∉ W.boundary →
      ∃! i : ℤ, x ∈ Set.Ioo (W.position i) (W.position (i + 1)) := by
  apply strictMono_int_complementPartition W.position_strictMono W.position_range
  intro a c
  rw [W.boundary_exact]
  exact totalSlabBoundary_locallyFinite hTile a c

private theorem boundaryWord_base_eq_iUnion_labelledIntervals
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) (hTile : TilesOn K T Set.univ)
    (S : Set Tiling.Plane)
    (hS : (S = verticalColumnCentres K T ∧ S.Nonempty) ∨
      ∃ P : VerticalPlate K T, ¬ IsVerticalColumn P ∧ S = P.centres) :
    {x : ℝ | (x : ℂ) ∈ regularSupport K S} =
      ⋃ i : {i : ℤ // W.label i = S},
        Set.Ioo (W.position i) (W.position (i + 1)) := by
  apply boundaryWord_base_eq_iUnion_of_componentPartition W
    (slabComponentFamily K T)
    (by
      intro i
      rcases W.label_is_component i with hcol | ⟨P, hP, hlabel⟩
      · exact Or.inl ⟨hcol.1, hcol.1 ▸ hcol.2⟩
      · exact Or.inr ⟨P, hP, hlabel⟩)
    (slabComponents_partition hTile).2.2.1
  · rw [W.boundary_exact]
    ext x
    constructor
    · intro hx
      obtain ⟨U, hU, hxU⟩ := totalBoundary_mem_componentFrontier hTile hx
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩
    · intro hx
      obtain ⟨U, hxU⟩ := Set.mem_iUnion.1 hx
      rcases U.2 with hU | ⟨P, hP, hU⟩
      · exact Or.inl (by simpa [hU.1] using hxU)
      · apply Or.inr
        rw [Set.mem_iUnion]
        refine ⟨⟨P, hP⟩, ?_⟩
        have hbase :
            {r : ℝ | (r : ℂ) ∈ regularSupport K P.centres} = P.base := by
          change {r : ℝ | (r : ℂ) ∈ P.support} = P.base
          rw [(P.support_isVerticalSlab hTile).2]
          ext r
          simp
        simpa [hU, hbase] using hxU
  · exact boundaryWord_complementPartition W hTile
  · exact hS

theorem SlabBoundaryWord.supportPeriodic_of_periodic
    {K : Region} {T : Set Tiling.Plane}
    (W : SlabBoundaryWord K T) (hTile : TilesOn K T Set.univ)
    {k : ℕ} {beta : ℝ} (hk : 0 < k) (hbeta : 0 < beta)
    (hper : W.IsPeriodic k beta) :
    SlabPeriodicityConclusion K T beta := by
  apply supportPeriodic_of_periodic_of_decoder W hk hbeta hper
  intro S hS
  have hbase := boundaryWord_base_eq_iUnion_labelledIntervals W hTile S hS
  obtain ⟨X, _hXregular, hsupport⟩ :=
    (slabComponents_partition hTile).2.1 S hS
  have hXbase : X = {x : ℝ | (x : ℂ) ∈ regularSupport K S} := by
    ext x
    rw [hsupport]
    simp
  rw [hsupport, hXbase, hbase]

private theorem approximationGapBound_reflects
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace)
    (hLower : ∀ i : ℤ,
      (1 / 2 : ℝ) * (W.position (i + 1) - W.position i) <
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position (i + 1), hBoundaryMem (i + 1)⟩ -
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position i, hBoundaryMem i⟩)
    (hMapped : ∃ R : ℝ, 0 < R ∧ ∀ i : ℤ,
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨W.position (i + 1), hBoundaryMem (i + 1)⟩ -
        Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨W.position i, hBoundaryMem i⟩ < R) :
    ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ i : ℤ, W.position (i + 1) - W.position i < R₀ := by
  obtain ⟨R, hR, hMapped⟩ := hMapped
  refine ⟨2 * R, by positivity, ?_⟩
  intro i
  have hLoweri := hLower i
  have hMappedi := hMapped i
  linarith

private theorem slabGapFinset_exists
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace)
    (hFinite : W.gapSet.Finite) :
    ∃ G : Finset ℝ, (G : Set ℝ) = W.gapSet ∧
      ∀ g ∈ G, g ∈ C.coordinateSpace := by
  let G : Finset ℝ := hFinite.toFinset
  refine ⟨G, hFinite.coe_toFinset, ?_⟩
  intro g hg
  have hgSet : g ∈ W.gapSet := by
    exact hFinite.mem_toFinset.mp hg
  obtain ⟨i, rfl⟩ := hgSet
  exact C.coordinateSpace.sub_mem (hBoundaryMem (i + 1)) (hBoundaryMem i)

private theorem secondApproximation_imageShift_core
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace)
    (k : ℕ) (hk : 0 < k) (b : ℝ) (hb : 0 < b)
    (hPositionShift : ∀ i : ℤ,
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨W.position i, hBoundaryMem i⟩ + b =
        Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨W.position (i + k), hBoundaryMem (i + k)⟩)
    (hLabelShift : ∀ i : ℤ, W.label (i + k) = W.label i) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℝ, 0 < b ∧
      ∀ i : ℤ,
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position i, hBoundaryMem i⟩ + b =
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position (i + k), hBoundaryMem (i + k)⟩ ∧
        W.label (i + k) = W.label i := by
  exact ⟨k, hk, b, hb, fun i ↦ ⟨hPositionShift i, hLabelShift i⟩⟩

private theorem firstApproximation_orderAndGapBound_core
    {B B' : Set ℝ} (e : B ≃o B') {b : ℝ}
    (hB' : B'.Nonempty) (hb : 0 < b)
    (hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite)
    (hlocal' : ∀ a c : ℝ, (B' ∩ Set.Icc a c).Finite)
    (hperiod : ∀ x : ℝ, x ∈ B' ↔ x + b ∈ B')
    (hLower : ∀ (point : ℤ → ℝ) (_hmono : StrictMono point)
      (hrange : Set.range point = B),
      ∀ i : ℤ, (1 / 2 : ℝ) * (point (i + 1) - point i) <
        (e ⟨point (i + 1), by
          rw [← hrange]
          exact Set.mem_range_self (i + 1)⟩ : ℝ) -
        (e ⟨point i, by
          rw [← hrange]
          exact Set.mem_range_self i⟩ : ℝ)) :
    ∃ point : ℤ → ℝ, StrictMono point ∧ Set.range point = B ∧
      (∀ x : ℝ, ∃ i : ℤ, point i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < point i) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧
      ∀ i : ℤ, 0 < point (i + 1) - point i ∧
          point (i + 1) - point i < R₀ := by
  obtain ⟨point, hmono, hrange, hbelow, habove⟩ :=
    totalSlabBoundary_integerOrder e hB' hb hlocal hlocal' hperiod
  have hpointMem (i : ℤ) : point i ∈ B := by
    rw [← hrange]
    exact Set.mem_range_self i
  let mapped : ℤ → ℝ := fun i ↦ e ⟨point i, hpointMem i⟩
  have hmappedMono : StrictMono mapped := e.strictMono.comp hmono
  have hmappedRange : Set.range mapped = B' := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (e ⟨point i, hpointMem i⟩).2
    · intro hy
      obtain ⟨i, hi⟩ := hrange.symm.subset (e.symm ⟨y, hy⟩).2
      refine ⟨i, ?_⟩
      have hsource : (⟨point i, hpointMem i⟩ : B) = e.symm ⟨y, hy⟩ :=
        Subtype.ext hi
      have heq : e ⟨point i, hpointMem i⟩ = ⟨y, hy⟩ := by
        calc
          e ⟨point i, hpointMem i⟩ = e (e.symm ⟨y, hy⟩) := congrArg e hsource
          _ = ⟨y, hy⟩ := e.apply_symm_apply ⟨y, hy⟩
      exact congrArg Subtype.val heq
  obtain ⟨R, hR, hmappedGap⟩ := periodicLocallyFiniteSet_boundedGaps
    hB' hb hlocal' hperiod mapped hmappedMono hmappedRange
  refine ⟨point, hmono, hrange, hbelow, habove, 2 * R, by positivity, ?_⟩
  intro i
  refine ⟨sub_pos.mpr (hmono (by omega)), ?_⟩
  have hlower := hLower point hmono hrange i
  change (1 / 2 : ℝ) * (point (i + 1) - point i) <
    mapped (i + 1) - mapped i at hlower
  linarith [hmappedGap i]

private theorem deformedRegion_relativelyRational
    {C : Tiling.AxisParallel.Approximation.ApproximationContext}
    {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi) :
    Tiling.RationalPolygonal.IsRelativelyRational D.deformedRegion.toPolygonalRegion := by
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair D.deformedRegion
  refine ⟨v, hv, ?_⟩
  intro w hw
  obtain ⟨wx, wy, hwre, hwim⟩ := D.rational_vertices w hw
  obtain ⟨vx, vy, hvre, hvim⟩ := D.rational_vertices v hv
  refine ⟨wx - vx, wy - vy, ?_, ?_⟩
  · simp only [Complex.sub_re, hwre, hvre, Rat.cast_sub]
  · simp only [Complex.sub_im, hwim, hvim, Rat.cast_sub]

private theorem deformedSlabComponentFamily_eq_image
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) :
    slabComponentFamily D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) =
      (fun S : Set Tiling.Plane ↦
        Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t : Tiling.Plane) ∈ S}) ''
        slabComponentFamily C.region C.centres := by
  let hContact := deformation_preservesProperHorizontalContact C phi D P hHorizontalSign
  let e := deformation_verticalPlateEquiv C phi D P hContact
  have hcolumn (Q : VerticalPlate C.region C.centres) :
      IsVerticalColumn Q ↔ IsVerticalColumn (e Q) :=
    deformation_preservesColumns C phi D P hContact hHorizontalSign Q
  have hcolumns :
      Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t : Tiling.Plane) ∈
            verticalColumnCentres C.region C.centres} =
        verticalColumnCentres D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [verticalColumnCentres_eq] at ht ⊢
      obtain ⟨Q, htQ⟩ := Set.mem_iUnion.mp ht
      refine Set.mem_iUnion.mpr ⟨⟨e Q.1, (hcolumn Q.1).mp Q.2⟩, ?_⟩
      rw [deformation_verticalPlateEquiv_centres C phi D P hContact Q.1]
      exact ⟨t, htQ, rfl⟩
    · intro hy
      rw [verticalColumnCentres_eq] at hy ⊢
      obtain ⟨Q', hyQ'⟩ := Set.mem_iUnion.mp hy
      let Q := e.symm Q'.1
      have hQ : IsVerticalColumn Q := by
        apply (hcolumn Q).mpr
        have heq : e Q = Q'.1 := by simp [Q, e]
        rw [heq]
        exact Q'.2
      have hc := deformation_verticalPlateEquiv_centres C phi D P hContact Q
      have heq : e Q = Q'.1 := by simp [Q, e]
      rw [heq] at hc
      rw [hc] at hyQ'
      obtain ⟨t, htQ, rfl⟩ := hyQ'
      change (t : Tiling.Plane) ∈ Q.centres at htQ
      refine ⟨t, ?_, rfl⟩
      change (t : Tiling.Plane) ∈
        ⋃ R : {R : VerticalPlate C.region C.centres // IsVerticalColumn R}, R.1.centres
      exact Set.mem_iUnion_of_mem
        (⟨Q, hQ⟩ : {R : VerticalPlate C.region C.centres // IsVerticalColumn R}) htQ
  ext S
  constructor
  · intro hS
    rcases hS with ⟨rfl, hne⟩ | ⟨Q', hQ', rfl⟩
    · have hsourceNe :
          (verticalColumnCentres C.region C.centres).Nonempty := by
        rw [← hcolumns] at hne
        obtain ⟨y, t, ht, rfl⟩ := hne
        exact ⟨t, ht⟩
      refine ⟨verticalColumnCentres C.region C.centres,
        Or.inl ⟨rfl, hsourceNe⟩, hcolumns⟩
    · let Q := e.symm Q'
      have hQ : ¬ IsVerticalColumn Q := by
        intro h
        apply hQ'
        have heq : e Q = Q' := by simp [Q, e]
        rw [← heq]
        exact (hcolumn Q).mp h
      refine ⟨Q.centres, Or.inr ⟨Q, hQ, rfl⟩, ?_⟩
      have hc := deformation_verticalPlateEquiv_centres C phi D P hContact Q
      simpa [Q, e] using hc.symm
  · rintro ⟨S, hS, rfl⟩
    rcases hS with ⟨rfl, hne⟩ | ⟨Q, hQ, rfl⟩
    · refine Or.inl ⟨hcolumns, ?_⟩
      obtain ⟨t, ht⟩ := hne
      let tC : C.centres := ⟨t, verticalColumnCentres_subset C.region C.centres ht⟩
      exact ⟨P.fullCenters tC, tC, ht, rfl⟩
    · refine Or.inr ⟨e Q, (hcolumn Q).not.mp hQ, ?_⟩
      exact (deformation_verticalPlateEquiv_centres C phi D P hContact Q).symm

private theorem totalSlabBoundary_eq_iUnion_componentFrontier
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ) :
    totalSlabBoundary K T =
      ⋃ S ∈ slabComponentFamily K T,
        frontier {x : ℝ | (x : ℂ) ∈ regularSupport K S} := by
  ext x
  constructor
  · intro hx
    obtain ⟨S, hS, hxS⟩ := totalBoundary_mem_componentFrontier hTile hx
    exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hS, hxS⟩⟩
  · intro hx
    obtain ⟨S, hS⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hSfamily, hxS⟩ := Set.mem_iUnion.1 hS
    rcases hSfamily with ⟨rfl, _⟩ | ⟨Q, hQ, rfl⟩
    · exact Or.inl hxS
    · apply Or.inr
      rw [Set.mem_iUnion]
      refine ⟨⟨Q, hQ⟩, ?_⟩
      have hbase :
          {r : ℝ | (r : ℂ) ∈ regularSupport K Q.centres} = Q.base := by
        change {r : ℝ | (r : ℂ) ∈ Q.support} = Q.base
        rw [(Q.support_isVerticalSlab hTile).2]
        ext r
        simp
      rwa [hbase] at hxS

private theorem deformedComponentFrontierUnion_eq_totalSlabBoundary
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) :
    (⋃ S ∈ slabComponentFamily C.region C.centres,
      frontier {x : ℝ | (x : ℂ) ∈
        regularSupport D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Tiling.Plane) ∈ S})}) =
      totalSlabBoundary D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
  rw [totalSlabBoundary_eq_iUnion_componentFrontier P.full_tilesOn]
  have hfamily := deformedSlabComponentFamily_eq_image C phi D P hHorizontalSign
  ext x
  constructor
  · intro hx
    obtain ⟨S, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hS, hxS⟩ := Set.mem_iUnion.1 hx
    refine Set.mem_iUnion.2 ⟨_, Set.mem_iUnion.2 ⟨?_, hxS⟩⟩
    rw [hfamily]
    exact ⟨S, hS, rfl⟩
  · intro hx
    obtain ⟨U, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hU, hxU⟩ := Set.mem_iUnion.1 hx
    rw [hfamily] at hU
    obtain ⟨S, hS, hSU⟩ := hU
    subst U
    exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hS, hxU⟩⟩

private theorem deformedBoundaryImage_locallyFinite
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) :
    ∀ a c : ℝ,
      ({y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
        y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} ∩
        Set.Icc a c).Finite := by
  have hparts := slabComponents_partition P.source_tilesOn
  have htransport := deformation_transportsOrderedBoundaryCode C phi D P
    hHorizontalSign (slabComponentFamily C.region C.centres) hparts.1 hparts.2.1
    (totalSlabBoundary C.region C.centres) hBoundaryMem
    (totalSlabBoundary_eq_iUnion_componentFrontier P.source_tilesOn)
  have himage :
      {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
        y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBoundaryMem x hx⟩} =
      totalSlabBoundary D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
    rw [htransport.1]
    exact deformedComponentFrontierUnion_eq_totalSlabBoundary C phi D P hHorizontalSign
  intro a c
  rw [himage]
  exact totalSlabBoundary_locallyFinite P.full_tilesOn a c

private theorem normalizedDeformationData_exists
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (hFHC : HasFiniteHorizontalComplexity C.centres) :
    ∃ (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
      (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D),
      (∀ v w : C.region.vertices, ∀ s t : C.centres,
        (v.1 + (s : Tiling.Plane)).re < (w.1 + (t : Tiling.Plane)).re →
        (1 / 2 : ℝ) * ((w.1 + (t : Tiling.Plane)).re -
            (v.1 + (s : Tiling.Plane)).re) <
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re) ∧
      (∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) ∧
      ∃ b : ℝ, 0 < b ∧ SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b := by
  obtain ⟨eg, heg, hgood⟩ :=
    Tiling.AxisParallel.Approximation.isGoodApproximation_of_sufficientlyFine C
  obtain ⟨eo, heo, horder⟩ :=
    approximation_preservesGlobalHorizontalOrder C hTile hFHC
  obtain ⟨es, hes, hsign⟩ :=
    approximation_preservesGlobalHorizontalSign C hTile hFHC
  let eps := min eg (min eo es)
  have heps : 0 < eps := lt_min heg (lt_min heo hes)
  obtain ⟨phi, hphi⟩ :=
    Tiling.AxisParallel.Approximation.exists_epsilonApproximation C eps heps
  have hphig := hphi.of_le (min_le_left eg (min eo es))
  have hphio := hphi.of_le
    (le_trans (min_le_right eg (min eo es)) (min_le_left eo es))
  have hphis := hphi.of_le
    (le_trans (min_le_right eg (min eo es)) (min_le_right eo es))
  let D := Classical.choice
    (Tiling.AxisParallel.Approximation.exists_rationalPolygonDeformation C phi (hgood phi hphig))
  let P := Classical.choice
    (Tiling.AxisParallel.Approximation.exists_twoStageDeformationSupportTransport C phi D hTile)
  obtain ⟨b, hb, hper⟩ := rationalVerticalPlateSupport_periodic P.full_tilesOn
    (deformedRegion_relativelyRational D)
  exact ⟨phi, D, P, fun v w s t hlt ↦ (horder phi hphio v w s t hlt).1,
    hsign phi hphis, b, hb, hper⟩

private theorem finiteGapInjectiveDeformationData_exists
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (hFHC : HasFiniteHorizontalComplexity C.centres)
    (G : Finset ℝ) (hG : ∀ g ∈ G, g ∈ C.coordinateSpace) :
    ∃ (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
      (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D),
      (∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) ∧
      (∃ b : ℝ, 0 < b ∧ SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b) ∧
      ∀ (g : ℝ) (hg : g ∈ G) (g' : ℝ) (hg' : g' ∈ G),
        Tiling.AxisParallel.Approximation.mapScalar phi ⟨g, hG g hg⟩ =
          Tiling.AxisParallel.Approximation.mapScalar phi ⟨g', hG g' hg'⟩ →
        g = g' := by
  obtain ⟨eg, heg, hgood⟩ :=
    Tiling.AxisParallel.Approximation.isGoodApproximation_of_sufficientlyFine C
  obtain ⟨eo, heo, _horder⟩ :=
    approximation_preservesGlobalHorizontalOrder C hTile hFHC
  obtain ⟨es, hes, hsign⟩ :=
    approximation_preservesGlobalHorizontalSign C hTile hFHC
  obtain ⟨eSep, heSep, hseparates⟩ :=
    approximation_separatesHorizontalAlphabet C G hG
  let eps := min eg (min eo (min es eSep))
  have heps : 0 < eps := lt_min heg (lt_min heo (lt_min hes heSep))
  obtain ⟨phi, hphi⟩ :=
    Tiling.AxisParallel.Approximation.exists_epsilonApproximation C eps heps
  have hphig := hphi.of_le
    (min_le_left eg (min eo (min es eSep)))
  have hphis := hphi.of_le
    (le_trans (min_le_right eg (min eo (min es eSep)))
      (le_trans (min_le_right eo (min es eSep)) (min_le_left es eSep)))
  have hphiSep := hphi.of_le
    (le_trans (min_le_right eg (min eo (min es eSep)))
      (le_trans (min_le_right eo (min es eSep)) (min_le_right es eSep)))
  let D := Classical.choice
    (Tiling.AxisParallel.Approximation.exists_rationalPolygonDeformation C phi (hgood phi hphig))
  let P := Classical.choice
    (Tiling.AxisParallel.Approximation.exists_twoStageDeformationSupportTransport C phi D hTile)
  obtain ⟨b, hb, hper⟩ := rationalVerticalPlateSupport_periodic P.full_tilesOn
    (deformedRegion_relativelyRational D)
  refine ⟨phi, D, P, hsign phi hphis, ⟨b, hb, hper⟩, ?_⟩
  intro g hg g' hg' heq
  by_contra hne
  exact (hseparates phi hphiSep g hg g' hg' hne) heq

private theorem mappedBoundary_lower
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hOrder : ∀ v w : C.region.vertices, ∀ s t : C.centres,
      (v.1 + (s : Tiling.Plane)).re < (w.1 + (t : Tiling.Plane)).re →
      (1 / 2 : ℝ) * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) <
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re) :
    ∀ x y : totalSlabBoundary C.region C.centres, x < y →
      (1 / 2 : ℝ) * ((y : ℝ) - (x : ℝ)) <
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨y.1, hBoundaryMem y.1 y.2⟩ -
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨x.1, hBoundaryMem x.1 x.2⟩ := by
  intro x y hxy
  obtain ⟨v, hv, s, hs, hx⟩ :=
    totalSlabBoundary_horizontalTranslatedVertices hTile x.2
  obtain ⟨w, hw, t, ht, hy⟩ :=
    totalSlabBoundary_horizontalTranslatedVertices hTile y.2
  let v' : C.region.vertices := ⟨v, hv⟩
  let w' : C.region.vertices := ⟨w, hw⟩
  let s' : C.centres := ⟨s, hs⟩
  let t' : C.centres := ⟨t, ht⟩
  have hlt : (v + s).re < (w + t).re := by
    rw [← hx, ← hy]
    exact hxy
  have hlower := hOrder v' w' s' t' (by simpa [v', w', s', t'] using hlt)
  have hxmap :
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨x.1, hBoundaryMem x.1 x.2⟩ =
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v hv) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s hs)).re := by
    have hcoord :
        (⟨x.1, hBoundaryMem x.1 x.2⟩ : C.coordinateSpace) =
          ⟨v.re, C.vertex_re_mem v hv⟩ + ⟨s.re, C.centre_re_mem s hs⟩ := by
      apply Subtype.ext
      change x.1 = v.re + s.re
      simpa only [Complex.add_re] using hx
    simp only [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_zero, add_zero]
    rw [hcoord, map_add, Rat.cast_add]
  have hymap :
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨y.1, hBoundaryMem y.1 y.2⟩ =
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w hw) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t ht)).re := by
    have hcoord :
        (⟨y.1, hBoundaryMem y.1 y.2⟩ : C.coordinateSpace) =
          ⟨w.re, C.vertex_re_mem w hw⟩ + ⟨t.re, C.centre_re_mem t ht⟩ := by
      apply Subtype.ext
      change y.1 = w.re + t.re
      simpa only [Complex.add_re] using hy
    simp only [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_zero, add_zero]
    rw [hcoord, map_add, Rat.cast_add]
  have hlower' :
      (1 / 2 : ℝ) * ((w + t).re - (v + s).re) <
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w hw) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t ht)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v hv) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s hs)).re := by
    simpa [v', w', s', t'] using hlower
  rw [hxmap, hymap]
  simpa [hx, hy] using hlower'

private theorem mappedBoundary_strictMono
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hOrder : ∀ v w : C.region.vertices, ∀ s t : C.centres,
      (v.1 + (s : Tiling.Plane)).re < (w.1 + (t : Tiling.Plane)).re →
      (1 / 2 : ℝ) * ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) <
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
            Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re) :
    StrictMono (fun x : totalSlabBoundary C.region C.centres ↦
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨x.1, hBoundaryMem x.1 x.2⟩) := by
  intro x y hxy
  have h := mappedBoundary_lower C hTile phi hBoundaryMem hOrder x y hxy
  have hpos : 0 < (1 / 2 : ℝ) * ((y : ℝ) - (x : ℝ)) :=
    mul_pos (by norm_num) (sub_pos.mpr hxy)
  linarith

private theorem mappedBoundary_strictMono_of_sign
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hBoundaryMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace)
    (hSign : ∀ v w : C.region.vertices, ∀ s t : C.centres,
      Real.sign ((w.1 + (t : Tiling.Plane)).re -
        (v.1 + (s : Tiling.Plane)).re) =
      Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) :
    StrictMono (fun x : totalSlabBoundary C.region C.centres ↦
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨x.1, hBoundaryMem x.1 x.2⟩) := by
  intro x y hxy
  obtain ⟨v, hv, s, hs, hx⟩ :=
    totalSlabBoundary_horizontalTranslatedVertices hTile x.2
  obtain ⟨w, hw, t, ht, hy⟩ :=
    totalSlabBoundary_horizontalTranslatedVertices hTile y.2
  let v' : C.region.vertices := ⟨v, hv⟩
  let w' : C.region.vertices := ⟨w, hw⟩
  let s' : C.centres := ⟨s, hs⟩
  let t' : C.centres := ⟨t, ht⟩
  have hsource : 0 < (w + t).re - (v + s).re := by
    rw [← hx, ← hy]
    exact sub_pos.mpr hxy
  have hsigned := hSign v' w' s' t'
  have hmapped : 0 <
      (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w hw) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t ht)).re -
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v hv) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s hs)).re := by
    have hsource' : 0 <
        (w'.1 + (t' : Tiling.Plane)).re -
          (v'.1 + (s' : Tiling.Plane)).re := by
      simpa [v', w', s', t'] using hsource
    have hsigned' := hsigned
    rw [Real.sign_of_pos hsource'] at hsigned'
    have hsigned'' : Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w hw) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t ht)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v hv) +
              Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s hs)).re) = 1 := by
      simpa [v', w', s', t'] using hsigned'.symm
    by_contra hn
    have hle := le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hneg
    · rw [heq, Real.sign_zero] at hsigned''
      norm_num at hsigned''
    · rw [Real.sign_of_neg hneg] at hsigned''
      norm_num at hsigned''
  have hxmap :
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨x.1, hBoundaryMem x.1 x.2⟩ =
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v hv) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s hs)).re := by
    have hcoord :
        (⟨x.1, hBoundaryMem x.1 x.2⟩ : C.coordinateSpace) =
          ⟨v.re, C.vertex_re_mem v hv⟩ + ⟨s.re, C.centre_re_mem s hs⟩ := by
      apply Subtype.ext
      change x.1 = v.re + s.re
      simpa only [Complex.add_re] using hx
    simp only [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_zero, add_zero]
    rw [hcoord, map_add, Rat.cast_add]
  have hymap :
      Tiling.AxisParallel.Approximation.mapScalar phi
          ⟨y.1, hBoundaryMem y.1 y.2⟩ =
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w hw) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t ht)).re := by
    have hcoord :
        (⟨y.1, hBoundaryMem y.1 y.2⟩ : C.coordinateSpace) =
          ⟨w.re, C.vertex_re_mem w hw⟩ + ⟨t.re, C.centre_re_mem t ht⟩ := by
      apply Subtype.ext
      change y.1 = w.re + t.re
      simpa only [Complex.add_re] using hy
    simp only [Tiling.AxisParallel.Approximation.mapScalar,
      Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
      Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, neg_zero, add_zero]
    rw [hcoord, map_add, Rat.cast_add]
  change Tiling.AxisParallel.Approximation.mapScalar phi
      ⟨x.1, hBoundaryMem x.1 x.2⟩ <
    Tiling.AxisParallel.Approximation.mapScalar phi
      ⟨y.1, hBoundaryMem y.1 y.2⟩
  rw [hxmap, hymap]
  exact sub_pos.mp hmapped

private theorem normalizedSlabBoundaryWord_exists
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (hTile : TilesOn C.region C.centres Set.univ)
    (hFHC : HasFiniteHorizontalComplexity C.centres)
    (hNoFull : ¬ ∃ P : VerticalPlate C.region C.centres,
      ¬ IsVerticalColumn P ∧ P.centres = C.centres)
    (hNotColumns : C.centres ≠ verticalColumnCentres C.region C.centres) :
    ∃ W : SlabBoundaryWord C.region C.centres,
      W.boundary = totalSlabBoundary C.region C.centres ∧
      (∀ x : ℝ, ∃ i : ℤ, W.position i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < W.position i) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ i : ℤ, 0 < W.position (i + 1) - W.position i ∧
          W.position (i + 1) - W.position i < R₀ := by
  let B := totalSlabBoundary C.region C.centres
  have hBmem : ∀ x ∈ B, x ∈ C.coordinateSpace :=
    totalSlabBoundary_coordinate.2 C hTile
  obtain ⟨phi, D, P, hOrder, hSign, b, hb, hTargetPeriod⟩ :=
    normalizedDeformationData_exists C hTile hFHC
  let f : B → ℝ := fun x ↦
    Tiling.AxisParallel.Approximation.mapScalar phi ⟨x.1, hBmem x.1 x.2⟩
  have hf : StrictMono f :=
    mappedBoundary_strictMono C hTile phi hBmem hOrder
  let B' : Set ℝ := {y : ℝ | ∃ x : B, y = f x}
  let e : B ≃o B' := strictMono_orderIso_image f hf
  obtain ⟨x₀, hx₀⟩ := totalSlabBoundary_nonempty hTile hNoFull hNotColumns
  have hB'ne : B'.Nonempty := ⟨f ⟨x₀, hx₀⟩, ⟨⟨x₀, hx₀⟩, rfl⟩⟩
  let b' := b
  have hb' : 0 < b' := hb
  have hperiod := deformedTotalBoundary_periodic_at C phi D P hBmem hSign
    b hb hTargetPeriod
  have hperiod' : ∀ x : ℝ, x ∈ B' ↔ x + b' ∈ B' := by
    simpa [B', f, B] using hperiod
  have hlocal : ∀ a c : ℝ, (B ∩ Set.Icc a c).Finite := by
    intro a c
    exact totalSlabBoundary_locallyFinite hTile a c
  have hlocal' : ∀ a c : ℝ, (B' ∩ Set.Icc a c).Finite := by
    simpa [B', f, B] using
      deformedBoundaryImage_locallyFinite C phi D P hBmem hSign
  have hLower : ∀ (point : ℤ → ℝ) (hmono : StrictMono point)
      (hrange : Set.range point = B), ∀ i : ℤ,
        (1 / 2 : ℝ) * (point (i + 1) - point i) <
          (e ⟨point (i + 1), by
            rw [← hrange]
            exact Set.mem_range_self (i + 1)⟩ : ℝ) -
          (e ⟨point i, by
            rw [← hrange]
            exact Set.mem_range_self i⟩ : ℝ) := by
    intro point hmono hrange i
    let xi : B := ⟨point i, hrange ▸ Set.mem_range_self i⟩
    let xj : B := ⟨point (i + 1), hrange ▸ Set.mem_range_self (i + 1)⟩
    have hij : xi < xj := hmono (by omega)
    have hl := mappedBoundary_lower C hTile phi hBmem hOrder xi xj hij
    simpa [e, f, xi, xj, strictMono_orderIso_image] using hl
  obtain ⟨point, hmono, hrange, hbelow, habove, R₀, hR₀, hgap⟩ :=
    firstApproximation_orderAndGapBound_core e hB'ne hb' hlocal hlocal' hperiod' hLower
  have hparts := slabComponents_partition hTile
  have hfrontier : ∀ S ∈ slabComponentFamily C.region C.centres, ∀ X : Set ℝ,
      regularSupport C.region S = Complex.re ⁻¹' X → frontier X ⊆ B := by
    intro S hS X hSX x hx
    change x ∈ totalSlabBoundary C.region C.centres
    rw [totalSlabBoundary_eq_iUnion_componentFrontier hTile]
    refine Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hS, ?_⟩⟩
    have hbase : {r : ℝ | (r : ℂ) ∈ regularSupport C.region S} = X := by
      ext r
      simp [hSX]
    rwa [hbase]
  have hlabels := stripLabel_exists (slabComponentFamily C.region C.centres)
    point hmono hrange hparts.2.1 hfrontier hparts.2.2.2
  choose label hlabel hstrip using hlabels
  have hlabel' (i : ℤ) :
      (label i = verticalColumnCentres C.region C.centres ∧
        (verticalColumnCentres C.region C.centres).Nonempty) ∨
      ∃ P : VerticalPlate C.region C.centres,
        ¬ IsVerticalColumn P ∧ label i = P.centres := by
    rcases hlabel i with ⟨hi, hne⟩ | hplate
    · exact Or.inl ⟨hi, hi ▸ hne⟩
    · exact Or.inr hplate
  obtain ⟨W, hWB, hWpoint, _hWlabel⟩ :=
    slabBoundaryWord_of_orderAndLabels point hmono hrange label hlabel' hstrip rfl
  refine ⟨W, hWB, ?_, ?_, R₀, hR₀, ?_⟩
  · simpa [hWpoint] using hbelow
  · simpa [hWpoint] using habove
  · intro i
    simpa [hWpoint] using hgap i

private theorem slabBoundaryWordAndGap_exists
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hFHC : HasFiniteHorizontalComplexity T)
    (hNoFull : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hNotColumns : T ≠ verticalColumnCentres K T) :
    ∃ W : SlabBoundaryWord K T,
      W.boundary = totalSlabBoundary K T ∧
      (∀ x : ℝ, ∃ i : ℤ, W.position i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < W.position i) ∧
      ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ i : ℤ, 0 < W.position (i + 1) - W.position i ∧
          W.position (i + 1) - W.position i < R₀ := by
  obtain ⟨v₀, t₀, hv₀, ht₀, C, hcarrier, hcentres, _htarget,
      hCTile, hCFHC, _hperiodTransport⟩ :=
    @normalizedContext_exists.{0} K T hTile hFHC
  obtain ⟨e, heCentres, heColumn, _heSupport, hcolumns, _hcolumnSupport,
      _hboundary⟩ :=
    normalization_geometryTransport v₀ t₀ C hcarrier hcentres hTile
  have hT : t₀ +ᵥ C.centres = T := by
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using
      (centres_translation_image t₀ C hcentres).symm
  have hCNoFull : ¬ ∃ P : VerticalPlate C.region C.centres,
      ¬ IsVerticalColumn P ∧ P.centres = C.centres := by
    rintro ⟨P, hP, hPC⟩
    apply hNoFull
    refine ⟨e P, (heColumn P).not.mpr hP, ?_⟩
    rw [heCentres P, hPC, hT]
  have hCNotColumns :
      C.centres ≠ verticalColumnCentres C.region C.centres := by
    intro h
    apply hNotColumns
    calc
      T = t₀ +ᵥ C.centres := hT.symm
      _ = t₀ +ᵥ verticalColumnCentres C.region C.centres := congrArg (t₀ +ᵥ ·) h
      _ = verticalColumnCentres K T := hcolumns.symm
  obtain ⟨W, hWB, hbelow, habove, R₀, hR₀, hgap⟩ :=
    normalizedSlabBoundaryWord_exists C hCTile hCFHC hCNoFull hCNotColumns
  obtain ⟨W₀, hpos, _hlabel, hboundary, _hgapEq, hgapTransport⟩ :=
    normalization_wordTransport v₀ t₀ C hcarrier hcentres hTile W
  refine ⟨W₀, ?_, ?_, ?_, R₀, hR₀, ?_⟩
  · rw [hboundary, hWB]
    exact _hboundary.symm
  · intro x
    obtain ⟨i, hi⟩ := hbelow (x - (v₀ + t₀).re)
    refine ⟨i, ?_⟩
    rw [hpos i]
    linarith
  · intro x
    obtain ⟨i, hi⟩ := habove (x - (v₀ + t₀).re)
    refine ⟨i, ?_⟩
    rw [hpos i]
    linarith
  · intro i
    refine ⟨sub_pos.mpr (W₀.position_strictMono (by omega)), ?_⟩
    exact hgapTransport R₀ (fun j ↦ (hgap j).2) i

private theorem slabBoundaryWord_exists
    {K : Region} {T : Set Tiling.Plane} (hTile : TilesOn K T Set.univ)
    (hFHC : HasFiniteHorizontalComplexity T)
    (hNoFull : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hNotColumns : T ≠ verticalColumnCentres K T) :
    ∃ W : SlabBoundaryWord K T,
      W.boundary = totalSlabBoundary K T ∧
      (∀ x : ℝ, ∃ i : ℤ, W.position i < x) ∧
      (∀ x : ℝ, ∃ i : ℤ, x < W.position i) := by
  obtain ⟨W, hWB, hbelow, habove, _R, _hR, _hgap⟩ :=
    slabBoundaryWordAndGap_exists hTile hFHC hNoFull hNotColumns
  exact ⟨W, hWB, hbelow, habove⟩

theorem firstApproximation_boundsBoundaryGaps
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hFHC : HasFiniteHorizontalComplexity T)
    (hNoFull : ¬ ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T)
    (hNotColumns : T ≠ verticalColumnCentres K T) :
    ∃ W : SlabBoundaryWord K T,
      ∃ R₀ : ℝ, 0 < R₀ ∧
        ∀ i : ℤ, 0 < W.position (i + 1) - W.position i ∧
          W.position (i + 1) - W.position i < R₀ := by
  obtain ⟨W, _hWB, _hbelow, _habove, R₀, hR₀, hgap⟩ :=
    slabBoundaryWordAndGap_exists hTile hFHC hNoFull hNotColumns
  exact ⟨W, R₀, hR₀, hgap⟩

private theorem periodicOrderedEnumeration_indexShift
    {B : Set ℝ} {b : ℝ} (hb : 0 < b)
    (hperiod : ∀ x : ℝ, x ∈ B ↔ x + b ∈ B)
    (point : ℤ → ℝ) (hmono : StrictMono point)
    (hrange : Set.range point = B) :
    ∃ k : ℕ, 0 < k ∧ ∀ i : ℤ, point i + b = point (i + k) := by
  have himage (i : ℤ) : point i + b ∈ B :=
    (hperiod (point i)).mp (hrange ▸ Set.mem_range_self i)
  choose f hf using fun i ↦ hrange.symm.subset (himage i)
  have hf_strict : StrictMono f := by
    intro i j hij
    apply (hmono.lt_iff_lt).mp
    rw [hf i, hf j]
    simpa [add_comm] using add_lt_add_right (hmono hij) b
  have hf_succ (i : ℤ) : f (i + 1) = f i + 1 := by
    have hlt : f i < f (i + 1) := hf_strict (by omega)
    apply le_antisymm
    · by_contra h
      have hbetween : f i + 1 < f (i + 1) := by omega
      have hleft : point i + b < point (f i + 1) := by
        rw [← hf i]
        exact hmono (by omega)
      have hright : point (f i + 1) < point (i + 1) + b := by
        rw [← hf (i + 1)]
        exact hmono hbetween
      have hback : point (f i + 1) - b ∈ B := by
        apply (hperiod (point (f i + 1) - b)).mpr
        simpa using (hrange ▸ Set.mem_range_self (f i + 1))
      obtain ⟨j, hj⟩ := hrange.symm.subset hback
      have hij : i < j := by
        apply (hmono.lt_iff_lt).mp
        rw [hj]
        linarith
      have hji : j < i + 1 := by
        apply (hmono.lt_iff_lt).mp
        rw [hj]
        linarith
      omega
    · omega
  let displacement : ℤ → ℤ := fun i ↦ f i - i
  have hdisp_succ (i : ℤ) : displacement (i + 1) = displacement i := by
    dsimp [displacement]
    rw [hf_succ]
    omega
  have hdisp (i : ℤ) : displacement i = displacement 0 := by
    refine Int.inductionOn' i 0 rfl ?_ ?_
    · intro j _hj hj
      exact (hdisp_succ j).trans hj
    · intro j _hj hj
      calc
        displacement (j - 1) = displacement ((j - 1) + 1) :=
          (hdisp_succ (j - 1)).symm
        _ = displacement j := by congr 1; omega
        _ = displacement 0 := hj
  have hf_eq (i : ℤ) : f i = i + f 0 := by
    have := hdisp i
    dsimp [displacement] at this
    omega
  have hf0pos : 0 < f 0 := by
    apply (hmono.lt_iff_lt).mp
    rw [hf 0]
    linarith
  let k : ℕ := Int.toNat (f 0)
  have hkcast : (k : ℤ) = f 0 := Int.toNat_of_nonneg hf0pos.le
  have hk : 0 < k := by
    by_contra h
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos h
    rw [hk0] at hkcast
    simp only [Nat.cast_zero] at hkcast
    omega
  refine ⟨k, hk, ?_⟩
  intro i
  calc
    point i + b = point (f i) := (hf i).symm
    _ = point (i + k) := by rw [hf_eq, hkcast]

private theorem boundaryWord_labels_shift_of_transportedStrips
    {K : Region} {T : Set Tiling.Plane} (W : SlabBoundaryWord K T)
    {k : ℕ}
    (targetStrip : ℤ → Set Tiling.Plane)
    (targetSupport : Set Tiling.Plane → Set Tiling.Plane)
    (Family : Set (Set Tiling.Plane))
    (hlabel : ∀ i : ℤ, W.label i ∈ Family)
    (htransport : ∀ (i : ℤ) (S : Set Tiling.Plane), (hS : S ∈ Family) →
      Complex.re ⁻¹' Set.Ioo (W.position i) (W.position (i + 1)) ⊆
          regularSupport K S ↔
        targetStrip i ⊆ targetSupport S)
    (hperiod : ∀ (i : ℤ) (S : Set Tiling.Plane), (hS : S ∈ Family) →
      targetStrip i ⊆ targetSupport S →
        targetStrip (i + k) ⊆ targetSupport S)
    (hnonempty : ∀ i : ℤ, (targetStrip i).Nonempty)
    (hdisjoint : ∀ S ∈ Family, ∀ U ∈ Family, S ≠ U →
      Disjoint (targetSupport S) (targetSupport U)) :
    ∀ i : ℤ, W.label (i + k) = W.label i := by
  intro i
  have hi : targetStrip i ⊆ targetSupport (W.label i) :=
    (htransport i (W.label i) (hlabel i)).mp (W.strip_in_labelSupport i)
  have hshiftOld : targetStrip (i + k) ⊆ targetSupport (W.label i) :=
    hperiod i (W.label i) (hlabel i) hi
  have hshiftNew : targetStrip (i + k) ⊆ targetSupport (W.label (i + k)) :=
    (htransport (i + k) (W.label (i + k)) (hlabel (i + k))).mp
      (W.strip_in_labelSupport (i + k))
  by_contra hne
  obtain ⟨z, hz⟩ := hnonempty (i + k)
  exact Set.disjoint_left.1
    (hdisjoint (W.label i) (hlabel i) (W.label (i + k))
      (hlabel (i + k)) (Ne.symm hne)) (hshiftOld hz) (hshiftNew hz)

private theorem secondApproximation_positionShift
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace)
    (hRationalPeriod : ∃ b : ℝ, 0 < b ∧
      SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℝ, 0 < b ∧
      SlabPeriodicityConclusion D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b ∧
      ∀ i : ℤ,
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position i, hBoundaryMem i⟩ + b =
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position (i + k), hBoundaryMem (i + k)⟩ := by
  have hTotalMem : ∀ x ∈ totalSlabBoundary C.region C.centres,
      x ∈ C.coordinateSpace := by
    intro x hx
    have hxW : x ∈ W.boundary := by
      rw [W.boundary_exact]
      exact hx
    obtain ⟨i, rfl⟩ := W.position_range.symm.subset hxW
    exact hBoundaryMem i
  let mapped : ℤ → ℝ := fun i ↦
    Tiling.AxisParallel.Approximation.mapScalar phi
      ⟨W.position i, hBoundaryMem i⟩
  have hmappedMono : StrictMono mapped := by
    have hmono := mappedBoundary_strictMono_of_sign C P.source_tilesOn phi
      hTotalMem hHorizontalSign
    intro i j hij
    let xi : totalSlabBoundary C.region C.centres :=
      ⟨W.position i, by
        unfold totalSlabBoundary
        rw [← W.boundary_exact, ← W.position_range]
        exact Set.mem_range_self i⟩
    let xj : totalSlabBoundary C.region C.centres :=
      ⟨W.position j, by
        unfold totalSlabBoundary
        rw [← W.boundary_exact, ← W.position_range]
        exact Set.mem_range_self j⟩
    have h := hmono (show xi < xj from W.position_strictMono hij)
    simpa [mapped, xi, xj] using h
  let B' : Set ℝ := Set.range mapped
  obtain ⟨b, hb, hSlabPeriod⟩ := hRationalPeriod
  have hperiod := deformedTotalBoundary_periodic_at C phi D P hTotalMem
    hHorizontalSign b hb hSlabPeriod
  have hperiod' : ∀ x : ℝ, x ∈ B' ↔ x + b ∈ B' := by
    let imageBoundary : Set ℝ :=
      {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ totalSlabBoundary C.region C.centres,
        y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hTotalMem x hx⟩}
    have hEq : B' = imageBoundary := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        have hi : W.position i ∈ totalSlabBoundary C.region C.centres := by
          unfold totalSlabBoundary
          rw [← W.boundary_exact, ← W.position_range]
          exact Set.mem_range_self i
        exact ⟨W.position i, hi, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        have hxW : x ∈ W.boundary := by
          rw [W.boundary_exact]
          exact hx
        obtain ⟨i, rfl⟩ := W.position_range.symm.subset hxW
        exact ⟨i, rfl⟩
    rw [hEq]
    exact hperiod
  obtain ⟨k, hk, hshift⟩ :=
    periodicOrderedEnumeration_indexShift hb hperiod' mapped hmappedMono rfl
  exact ⟨k, hk, b, hb, hSlabPeriod, hshift⟩

private theorem deformedComponentSupports_pairwiseDisjoint
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re)) :
    ∀ S ∈ slabComponentFamily C.region C.centres,
      ∀ U ∈ slabComponentFamily C.region C.centres, S ≠ U →
        Disjoint
          (regularSupport D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
              {t : C.centres | (t : Tiling.Plane) ∈ S}))
          (regularSupport D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
              {t : C.centres | (t : Tiling.Plane) ∈ U})) := by
  let imageFamily (S : Set Tiling.Plane) : Set Tiling.Plane :=
    Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
      {t : C.centres | (t : Tiling.Plane) ∈ S}
  have himage := deformedSlabComponentFamily_eq_image C phi D P hHorizontalSign
  have hparts := slabComponents_partition P.full_tilesOn
  intro S hS U hU hSU
  have hSmem : imageFamily S ∈ slabComponentFamily D.deformedRegion
      (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
    rw [himage]
    exact ⟨S, hS, rfl⟩
  have hUmem : imageFamily U ∈ slabComponentFamily D.deformedRegion
      (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) := by
    rw [himage]
    exact ⟨U, hU, rfl⟩
  have hne : imageFamily S ≠ imageFamily U := by
    intro heq
    apply hSU
    ext x
    constructor
    · intro hx
      have hxS : P.fullCenters ⟨x, (slabComponents_partition P.source_tilesOn).1 S hS hx⟩ ∈
          imageFamily S := ⟨_, hx, rfl⟩
      rw [heq] at hxS
      obtain ⟨u, hu, heu⟩ := hxS
      have : (⟨x, (slabComponents_partition P.source_tilesOn).1 S hS hx⟩ : C.centres) = u :=
        P.fullCenters.injective heu.symm
      have hval : x = (u : Tiling.Plane) := congrArg Subtype.val this
      change (u : Tiling.Plane) ∈ U at hu
      rwa [← hval] at hu
    · intro hx
      have hxU : P.fullCenters ⟨x, (slabComponents_partition P.source_tilesOn).1 U hU hx⟩ ∈
          imageFamily U := ⟨_, hx, rfl⟩
      rw [← heq] at hxU
      obtain ⟨u, hu, heu⟩ := hxU
      have : (⟨x, (slabComponents_partition P.source_tilesOn).1 U hU hx⟩ : C.centres) = u :=
        P.fullCenters.injective heu.symm
      have hval : x = (u : Tiling.Plane) := congrArg Subtype.val this
      change (u : Tiling.Plane) ∈ S at hu
      rwa [← hval] at hu
  exact hparts.2.2.1 (imageFamily S) hSmem (imageFamily U) hUmem hne

private theorem secondApproximation_imageShift
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
      ∀ v w : C.region.vertices, ∀ s t : C.centres,
        Real.sign ((w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint w.1 w.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint t.1 t.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint v.1 v.2) +
                Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint s.1 s.2)).re))
    (W : SlabBoundaryWord C.region C.centres)
    (hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace)
    (hRationalPeriod : ∃ b : ℝ, 0 < b ∧
      SlabPeriodicityConclusion D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) b) :
    ∃ k : ℕ, 0 < k ∧ ∃ b : ℝ, 0 < b ∧
      ∀ i : ℤ,
        Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position i, hBoundaryMem i⟩ + b =
          Tiling.AxisParallel.Approximation.mapScalar phi
            ⟨W.position (i + k), hBoundaryMem (i + k)⟩ ∧
        W.label (i + k) = W.label i := by
  obtain ⟨k, hk, b, hb, hSlabPeriod, hshift⟩ :=
    secondApproximation_positionShift C phi D P hHorizontalSign W hBoundaryMem hRationalPeriod
  let mapped : ℤ → ℝ := fun i ↦ Tiling.AxisParallel.Approximation.mapScalar phi
    ⟨W.position i, hBoundaryMem i⟩
  let targetStrip : ℤ → Set Tiling.Plane := fun i ↦
    Complex.re ⁻¹' Set.Ioo (mapped i) (mapped (i + 1))
  let targetSupport : Set Tiling.Plane → Set Tiling.Plane := fun S ↦
    regularSupport D.deformedRegion
      (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
        {t : C.centres | (t : Tiling.Plane) ∈ S})
  have hparts := slabComponents_partition P.source_tilesOn
  have hcode := deformation_transportsOrderedBoundaryCode C phi D P hHorizontalSign
    (slabComponentFamily C.region C.centres) hparts.1 hparts.2.1
    (totalSlabBoundary C.region C.centres)
    (by
      intro x hx
      have hxW : x ∈ W.boundary := by rw [W.boundary_exact]; exact hx
      obtain ⟨i, rfl⟩ := W.position_range.symm.subset hxW
      exact hBoundaryMem i)
    (totalSlabBoundary_eq_iUnion_componentFrontier P.source_tilesOn)
  have htransport : ∀ (i : ℤ) (S : Set Tiling.Plane),
      (hS : S ∈ slabComponentFamily C.region C.centres) →
      Complex.re ⁻¹' Set.Ioo (W.position i) (W.position (i + 1)) ⊆
          regularSupport C.region S ↔ targetStrip i ⊆ targetSupport S := by
    intro i S hS
    let x : totalSlabBoundary C.region C.centres := ⟨W.position i, by
      unfold totalSlabBoundary
      rw [← W.boundary_exact, ← W.position_range]
      exact Set.mem_range_self i⟩
    let x' : totalSlabBoundary C.region C.centres := ⟨W.position (i + 1), by
      unfold totalSlabBoundary
      rw [← W.boundary_exact, ← W.position_range]
      exact Set.mem_range_self (i + 1)⟩
    apply hcode.2 S hS x x'
    · exact W.position_strictMono (by omega)
    · ext y
      constructor
      · rintro ⟨hyIoo, hyB⟩
        have hyW : y ∈ W.boundary := by rw [W.boundary_exact]; exact hyB
        obtain ⟨j, rfl⟩ := W.position_range.symm.subset hyW
        have hij : i < j := (W.position_strictMono.lt_iff_lt).mp hyIoo.1
        have hji : j < i + 1 := (W.position_strictMono.lt_iff_lt).mp hyIoo.2
        omega
      · simp
  have hperiod : ∀ (i : ℤ) (S : Set Tiling.Plane),
      (hS : S ∈ slabComponentFamily C.region C.centres) →
      targetStrip i ⊆ targetSupport S → targetStrip (i + k) ⊆ targetSupport S := by
    intro i S hS hi z hz
    have hSperiod := deformedComponentSupport_periodic C phi D P hHorizontalSign hSlabPeriod S hS
    have hzstrip : z - (b : ℝ) ∈ targetStrip i := by
      change (z - (b : ℝ)).re ∈ Set.Ioo (mapped i) (mapped (i + 1))
      change z.re ∈ Set.Ioo (mapped (i + k)) (mapped (i + k + 1)) at hz
      dsimp [mapped] at hz ⊢
      have hs := hshift (i + 1)
      have hind : i + k + 1 = i + 1 + k := by omega
      rw [hind, ← hs, ← hshift i] at hz
      constructor <;> linarith [hz.1, hz.2]
    have := hi hzstrip
    have hp := hSperiod (z - (b : ℝ))
    simpa using hp.mpr this
  have hnonempty : ∀ i : ℤ, (targetStrip i).Nonempty := by
    intro i
    have hlt : mapped i < mapped (i + 1) := by
      have htotal : ∀ x ∈ totalSlabBoundary C.region C.centres, x ∈ C.coordinateSpace := by
        intro x hx
        have hxW : x ∈ W.boundary := by rw [W.boundary_exact]; exact hx
        obtain ⟨j, rfl⟩ := W.position_range.symm.subset hxW
        exact hBoundaryMem j
      have hm := mappedBoundary_strictMono_of_sign C P.source_tilesOn phi htotal hHorizontalSign
      let xi : totalSlabBoundary C.region C.centres := ⟨W.position i, by
        unfold totalSlabBoundary
        rw [← W.boundary_exact, ← W.position_range]
        exact Set.mem_range_self i⟩
      let xj : totalSlabBoundary C.region C.centres := ⟨W.position (i + 1), by
        unfold totalSlabBoundary
        rw [← W.boundary_exact, ← W.position_range]
        exact Set.mem_range_self (i + 1)⟩
      simpa [mapped, xi, xj] using hm (show xi < xj from W.position_strictMono (by omega))
    refine ⟨(((mapped i + mapped (i + 1)) / 2 : ℝ) : ℂ), ?_⟩
    change (mapped i + mapped (i + 1)) / 2 ∈ Set.Ioo (mapped i) (mapped (i + 1))
    constructor <;> linarith
  have hlabel := boundaryWord_labels_shift_of_transportedStrips W targetStrip targetSupport
    (slabComponentFamily C.region C.centres) (by
      intro i
      unfold slabComponentFamily
      change (W.label i = verticalColumnCentres C.region C.centres ∧ (W.label i).Nonempty) ∨ _
      rcases W.label_is_component i with ⟨heq, hne⟩ | hplate
      · exact Or.inl ⟨heq, heq.symm ▸ hne⟩
      · exact Or.inr hplate) htransport hperiod hnonempty
    (deformedComponentSupports_pairwiseDisjoint C phi D P hHorizontalSign)
  exact secondApproximation_imageShift_core C phi W hBoundaryMem k hk b hb hshift hlabel

theorem continuousVerticalPlateSupport_periodic
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hFHC : HasFiniteHorizontalComplexity T) :
    ∃ beta : ℝ, 0 < beta ∧ SlabPeriodicityConclusion K T beta := by
  by_cases hsingle : ∃ P : VerticalPlate K T,
      ¬ IsVerticalColumn P ∧ P.centres = T
  · exact ⟨1, by norm_num, singleNoncolumn_degenerate hTile hsingle⟩
  by_cases hcolumns : T = verticalColumnCentres K T
  · exact ⟨1, by norm_num, allColumns_degenerate hTile hcolumns⟩
  obtain ⟨v₀, t₀, _hv₀, _ht₀, C, hcarrier, hcentres, _htarget,
      hCTile, hCFHC, hperiodTransport⟩ :=
    @normalizedContext_exists.{0} K T hTile hFHC
  obtain ⟨e, heCentres, heColumn, _heSupport, hcolsTransport, _hcolSupport,
      _hboundary⟩ :=
    normalization_geometryTransport v₀ t₀ C hcarrier hcentres hTile
  have hT : t₀ +ᵥ C.centres = T := by
    simpa only [positiveSimilarity_image_eq_vadd_smul, one_smul] using
      (centres_translation_image t₀ C hcentres).symm
  have hCNoFull : ¬ ∃ P : VerticalPlate C.region C.centres,
      ¬ IsVerticalColumn P ∧ P.centres = C.centres := by
    rintro ⟨P, hP, hPC⟩
    apply hsingle
    refine ⟨e P, (heColumn P).not.mpr hP, ?_⟩
    rw [heCentres P, hPC, hT]
  have hCNotColumns : C.centres ≠ verticalColumnCentres C.region C.centres := by
    intro h
    apply hcolumns
    calc
      T = t₀ +ᵥ C.centres := hT.symm
      _ = t₀ +ᵥ verticalColumnCentres C.region C.centres := congrArg (t₀ +ᵥ ·) h
      _ = verticalColumnCentres K T := hcolsTransport.symm
  obtain ⟨W, hWB, _hbelow, _habove, R₀, hR₀, hgap⟩ :=
    normalizedSlabBoundaryWord_exists C hCTile hCFHC hCNoFull hCNotColumns
  have hfinite : W.gapSet.Finite :=
    slabBoundaryGapAlphabet_finite hCTile hCFHC W hR₀ (fun i ↦ (hgap i).2)
  have hBoundaryMem : ∀ i : ℤ, W.position i ∈ C.coordinateSpace := by
    intro i
    apply (totalSlabBoundary_coordinate.2 C hCTile)
    rw [← hWB, ← W.position_range]
    exact Set.mem_range_self i
  obtain ⟨G, hGset, hG⟩ := slabGapFinset_exists C W hBoundaryMem hfinite
  obtain ⟨phi, D, P, hSign, hRatPeriod, hInjectG⟩ :=
    finiteGapInjectiveDeformationData_exists C hCTile hCFHC G hG
  obtain ⟨k, hk, b, hb, hImage⟩ :=
    secondApproximation_imageShift C phi D P hSign W hBoundaryMem hRatPeriod
  have hInject : ∀ i j : ℤ,
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨W.position (i + 1) - W.position i,
          C.coordinateSpace.sub_mem (hBoundaryMem (i + 1)) (hBoundaryMem i)⟩ =
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨W.position (j + 1) - W.position j,
          C.coordinateSpace.sub_mem (hBoundaryMem (j + 1)) (hBoundaryMem j)⟩ →
      W.position (i + 1) - W.position i =
        W.position (j + 1) - W.position j := by
    intro i j heq
    have hgiSet : W.position (i + 1) - W.position i ∈ W.gapSet := ⟨i, rfl⟩
    have hgjSet : W.position (j + 1) - W.position j ∈ W.gapSet := ⟨j, rfl⟩
    have hgi : W.position (i + 1) - W.position i ∈ G := by
      rw [← Finset.mem_coe, hGset]
      exact hgiSet
    have hgj : W.position (j + 1) - W.position j ∈ G := by
      rw [← Finset.mem_coe, hGset]
      exact hgjSet
    apply hInjectG _ hgi _ hgj
    simpa using heq
  obtain ⟨beta, hbeta, hWperiod⟩ :=
    secondApproximation_reflectsSlabBoundaryPeriod C phi D P hCFHC W
      hBoundaryMem hk hInject ⟨b, hb, hImage⟩
  exact ⟨beta, hbeta,
    hperiodTransport beta (W.supportPeriodic_of_periodic hCTile hk hbeta hWperiod)⟩

end Tiling.AxisParallel.Continuous
