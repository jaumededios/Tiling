import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.HorizontalFLCAlphabet
import Tiling.AxisParallel.Continuous.IntrinsicHorizontalContact

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.header false

/-!
# Transport of earthquake components under coordinate deformation

This file contains the consequences that follow directly from the indexed two-stage transport and
an explicit preserve-and-reflect certificate for proper horizontal contacts.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Continuous

theorem deformation_preservesVerticalEdgeOrder
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi _D)
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    (v w : C.region.vertices)
    (s t : C.centres) :
    Real.sign ((w.1 + (t : Tiling.Plane)).re -
      (v.1 + (s : Tiling.Plane)).re) =
    Real.sign
      ((Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2) +
          P.firstCenters t).re -
        (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2) +
          P.firstCenters s).re) := by
  rw [P.firstCenters_apply t, P.firstCenters_apply s]
  simpa [Tiling.AxisParallel.Approximation.mapFirstPoint,
    Tiling.AxisParallel.Approximation.mapPoint] using hHorizontalSign v w s t

theorem mappedCentres_injective
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D) :
    Function.Injective P.fullCenters :=
  P.fullCenters.injective

private noncomputable def deformation_verticalPlateGraphIso
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hContact : ∀ s t : C.centres,
      HorizontalProperContact C.region s t ↔
        HorizontalProperContact D.deformedRegion
          (P.fullCenters s) (P.fullCenters t)) :
    verticalPlateGraph C.region C.centres ≃g
      verticalPlateGraph D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) where
  toEquiv :=
    Tiling.AxisParallel.Approximation.deformedCenterEquivCarrier P.fullCenters
  map_rel_iff' := by
    intro s t
    rw [verticalPlateGraph_adj_iff, verticalPlateGraph_adj_iff]
    exact and_congr
      (Tiling.AxisParallel.Approximation.deformedCenterEquivCarrier
        P.fullCenters).injective.eq_iff.not
      (hContact s t).symm

noncomputable def deformation_verticalPlateEquiv
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hContact : ∀ s t : C.centres,
      HorizontalProperContact C.region s t ↔
        HorizontalProperContact D.deformedRegion
          (P.fullCenters s) (P.fullCenters t)) :
    VerticalPlate C.region C.centres ≃
      VerticalPlate D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters) :=
  (deformation_verticalPlateGraphIso C phi D P hContact).connectedComponentEquiv

theorem deformation_verticalPlateEquiv_centres
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hContact : ∀ s t : C.centres,
      HorizontalProperContact C.region s t ↔
        HorizontalProperContact D.deformedRegion
          (P.fullCenters s) (P.fullCenters t))
    (Q : VerticalPlate C.region C.centres) :
    (deformation_verticalPlateEquiv C phi D P hContact Q).centres =
      Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
        {t : C.centres | (t : Tiling.Plane) ∈ Q.centres} := by
  let graphIso := deformation_verticalPlateGraphIso C phi D P hContact
  change Subtype.val '' (graphIso.connectedComponentEquiv Q).supp =
    P.fullCenters '' {t : C.centres | (t : Tiling.Plane) ∈ Q.centres}
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨t, ht⟩ := a.2
    have hat : a = graphIso t := by
      apply Subtype.ext
      exact ht.symm
    subst a
    refine ⟨t, ?_, rfl⟩
    change (t : Tiling.Plane) ∈ Q.centres
    refine ⟨t, ?_, rfl⟩
    have ha' :
        @SimpleGraph.connectedComponentMk _
            (verticalPlateGraph D.deformedRegion
              (Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters))
            (graphIso t) =
          graphIso.connectedComponentEquiv Q := ha
    exact (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
      (φ := graphIso) (v := t) (C := Q)).mp ha'
  · rintro ⟨t, ht, rfl⟩
    let a : Tiling.AxisParallel.Approximation.deformedCenterCarrier P.fullCenters := graphIso t
    refine ⟨a, ?_, rfl⟩
    change (t : Tiling.Plane) ∈ Q.centres at ht
    rcases ht with ⟨u, hu, hut⟩
    have htu : t = u := Subtype.ext hut.symm
    subst u
    have hu' :
        (verticalPlateGraph C.region C.centres).connectedComponentMk t = Q := hu
    have hout :=
      (SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp
        (φ := graphIso) (v := t) (C := Q)).mpr hu'
    exact hout

private def IsIntrinsicHorizontalSide (K : Region) (v w : K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ v.1.im = w.1.im ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices

private def IsIntrinsicVerticalSide (K : Region) (v w : K.vertices) : Prop :=
  v.1 ≠ w.1 ∧ v.1.re = w.1.re ∧
    openSegment ℝ v.1 w.1 ⊆ frontier K.support \ K.vertices

private def translatedHorizontalInterval (v w : Tiling.Plane)
    (s : Tiling.Plane) : Set ℝ :=
  Set.Ioo (min v.re w.re + s.re) (max v.re w.re + s.re)

private def translatedVerticalInterval (v w : Tiling.Plane)
    (s : Tiling.Plane) : Set ℝ :=
  Set.Ioo (min v.im w.im + s.im) (max v.im w.im + s.im)

private def IsVerticalGapChain (K : Region) (bottom top : ℝ)
    (n : ℕ) (a b : Fin n → K.vertices) : Prop :=
  0 < n ∧ (∀ i : Fin n, (a i).1.im < (b i).1.im) ∧
    top - bottom = ∑ i : Fin n, ((b i).1.im - (a i).1.im)

private theorem exists_mem_Ioo_of_ae {P : ℝ → Prop} {u v : ℝ}
    (huv : u < v) (hP : ∀ᵐ x ∂MeasureTheory.volume, P x) :
    ∃ x ∈ Ioo u v, P x := by
  have hmeasure : MeasureTheory.volume (Ioo u v) ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr huv)]
  exact MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hmeasure
    (hP.filter_mono MeasureTheory.ae_restrict_le)

private theorem goodHorizontalSlice_exists
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    {lo hi : ℝ} (hlohi : lo < hi) :
    ∃ q ∈ Set.Ioo lo hi,
      q ∉ {y : ℝ | ∃ v : K.vertices, ∃ t : T,
        y = (v.1 + (t : Tiling.Plane)).im} ∧
      ∀ᵐ x : ℝ ∂MeasureTheory.volume,
        ∃ t : T, (x : ℂ) + (q : ℂ) * Complex.I ∈
          (t : Tiling.Plane) +ᵥ K.openCarrier := by
  let bad : Set ℝ := {y : ℝ | ∃ v : K.vertices, ∃ t : T,
    y = (v.1 + (t : Tiling.Plane)).im}
  have hTcountable : T.Countable :=
    (IsPacking.locallyFinite_centres hTile.2.1).2
  have hVcountable : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable T := hTcountable.to_subtype
  let _ : Countable K.vertices := hVcountable.to_subtype
  have hbad : bad.Countable := by
    let f : K.vertices × T → ℝ := fun p ↦
      (p.1.1 + (p.2 : Tiling.Plane)).im
    apply (Set.countable_range f).mono
    rintro y ⟨v, t, rfl⟩
    exact ⟨(v, t), rfl⟩
  have hplane : ∀ᵐ z : Tiling.Plane ∂MeasureTheory.volume,
      ∃ t : T, z ∈ (t : Tiling.Plane) +ᵥ K.openCarrier := by
    filter_upwards [hTile.2.2] with z hz
    exact hz.mp (Set.mem_univ z)
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hswap :=
    MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpull
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) hswap
  have hgood : ∀ᵐ q : ℝ ∂MeasureTheory.volume,
      q ∉ bad ∧ ∀ᵐ x : ℝ ∂MeasureTheory.volume,
        ∃ t : T, (x : ℂ) + (q : ℂ) * Complex.I ∈
          (t : Tiling.Plane) +ᵥ K.openCarrier := by
    filter_upwards [hbad.ae_notMem MeasureTheory.volume, hslices] with q hqbad hq
    refine ⟨hqbad, ?_⟩
    filter_upwards [hq] with x hx
    have heq : (x : ℂ) + (q : ℂ) * Complex.I =
        Complex.measurableEquivRealProd.symm (q, x).swap := by
      apply Complex.ext <;> simp
    rw [heq]
    exact hx
  obtain ⟨q, hqI, hqbad, hqcover⟩ :=
    exists_mem_Ioo_of_ae hlohi hgood
  exact ⟨q, hqI, hqbad, hqcover⟩

private theorem eventually_goodHorizontalSlice
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) :
    ∀ᵐ q : ℝ ∂MeasureTheory.volume,
      q ∉ {y : ℝ | ∃ v : K.vertices, ∃ t : T,
        y = (v.1 + (t : Tiling.Plane)).im} ∧
      ∀ᵐ x : ℝ ∂MeasureTheory.volume,
        ∃ t : T, (x : ℂ) + (q : ℂ) * Complex.I ∈
          (t : Tiling.Plane) +ᵥ K.openCarrier := by
  let bad : Set ℝ := {y : ℝ | ∃ v : K.vertices, ∃ t : T,
    y = (v.1 + (t : Tiling.Plane)).im}
  have hTcountable : T.Countable :=
    (IsPacking.locallyFinite_centres hTile.2.1).2
  have hVcountable : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable T := hTcountable.to_subtype
  let _ : Countable K.vertices := hVcountable.to_subtype
  have hbad : bad.Countable := by
    let f : K.vertices × T → ℝ := fun p ↦
      (p.1.1 + (p.2 : Tiling.Plane)).im
    apply (Set.countable_range f).mono
    rintro y ⟨v, t, rfl⟩
    exact ⟨(v, t), rfl⟩
  have hplane : ∀ᵐ z : Tiling.Plane ∂MeasureTheory.volume,
      ∃ t : T, z ∈ (t : Tiling.Plane) +ᵥ K.openCarrier := by
    filter_upwards [hTile.2.2] with z hz
    exact hz.mp (Set.mem_univ z)
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hswap :=
    MeasureTheory.Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpull
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) hswap
  filter_upwards [hbad.ae_notMem MeasureTheory.volume, hslices] with q hqbad hq
  refine ⟨hqbad, ?_⟩
  filter_upwards [hq] with x hx
  have heq : (x : ℂ) + (q : ℂ) * Complex.I =
      Complex.measurableEquivRealProd.symm (q, x).swap := by
    apply Complex.ext <;> simp
  rw [heq]
  exact hx

private theorem openSegment_eq_vertical
    (v w : Tiling.Plane) (h : v.re = w.re) :
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

private theorem verticalSide_sliceEndpoint
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (v w : K.vertices) (s : T) {q : ℝ}
    (hvw : v.1 ≠ w.1) (hvertical : v.1.re = w.1.re)
    (hedge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (w.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ K.support) \
          ((s : Tiling.Plane) +ᵥ K.vertices))
    (hq : q ∈ translatedVerticalInterval v.1 w.1 s)
    (hcover : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      ∃ t : T, (x : ℂ) + (q : ℂ) * Complex.I ∈
        (t : Tiling.Plane) +ᵥ K.openCarrier) :
    (v.1 + (s : Tiling.Plane)).re ∈
      Tiling.AxisParallel.Foundations.FilledSliceChains.sliceEndpointSet
        K T Axis.horizontal q := by
  let x : ℝ := (v.1 + (s : Tiling.Plane)).re
  let p : Tiling.Plane := (x : ℂ) + (q : ℂ) * Complex.I
  have himne : v.1.im ≠ w.1.im := by
    intro him
    apply hvw
    exact Complex.ext hvertical him
  have hpseg : p ∈ openSegment ℝ (v.1 + (s : Tiling.Plane))
      (w.1 + (s : Tiling.Plane)) := by
    rw [openSegment_eq_vertical _ _ (by simp [hvertical])]
    refine ⟨q, ?_, ?_⟩
    · rw [openSegment_eq_Ioo' (by simpa using himne)]
      simpa [translatedVerticalInterval, Complex.add_im,
        min_add_add_right, max_add_add_right] using hq
    · apply Complex.ext <;> simp [p, x]
  have hpfront := (hedge hpseg).1
  have hpSupport : p ∈ (s : Tiling.Plane) +ᵥ K.support := by
    have hclosed := K.isPolygonal.isClosed.vadd (s : Tiling.Plane)
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hpfront
  have hpclosure : p ∈ closure ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
    rw [closure_vadd, show closure K.openCarrier = K.support by
      exact K.isPolygonal.closure_interior]
    exact hpSupport
  have hpnot : p ∉ openUnion K T := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    rintro ⟨t, hpt⟩
    by_cases hts : t = s
    · subst t
      apply hpfront.2
      rw [interior_vadd]
      exact hpt
    · have hcent : (t : Tiling.Plane) ≠ (s : Tiling.Plane) := by
        intro h
        exact hts (Subtype.ext h)
      have hdisj : Disjoint
          ((t : Tiling.Plane) +ᵥ K.openCarrier)
          ((s : Tiling.Plane) +ᵥ K.openCarrier) :=
        (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
          t.2 s.2 hcent
      have hmeet := mem_closure_iff.mp hpclosure
        ((t : Tiling.Plane) +ᵥ K.openCarrier)
        (isOpen_interior.vadd _) hpt
      rw [Set.disjoint_left] at hdisj
      obtain ⟨z, hzt, hzs⟩ := hmeet
      exact hdisj hzt hzs
  let U : Set ℝ := {r : ℝ |
    (r : ℂ) + (q : ℂ) * Complex.I ∈ openUnion K T}
  have hUae : ∀ᵐ r : ℝ ∂MeasureTheory.volume, r ∈ U := by
    filter_upwards [hcover] with r hr
    change (r : ℂ) + (q : ℂ) * Complex.I ∈ openUnion K T
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact hr
  have hUdense : Dense U :=
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).dense_of_ae hUae
  have hxnotU : x ∉ U := by
    intro hxU
    exact hpnot hxU
  change x ∈ frontier U
  refine ⟨?_, ?_⟩
  · rw [hUdense.closure_eq]
    exact Set.mem_univ x
  · intro hxint
    exact hxnotU (interior_subset hxint)

private theorem sum_fin_succ_sub_castSucc
    (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (x i.succ - x i.castSucc) = x (Fin.last n) - x 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      let y : Fin (n + 1) → ℝ := fun i ↦ x i.succ
      have htail := ih y
      dsimp [y] at htail
      have htail' : ∑ i : Fin n,
          (x i.succ.succ - x i.succ.castSucc) =
            x (Fin.last (n + 1)) - x 1 := by
        rw [← htail]
        apply Finset.sum_congr rfl
        intro i _hi
        congr 2
      rw [htail']
      have hs0 : (Fin.succ 0 : Fin (n + 2)) = 1 := Fin.ext rfl
      have hc0 : (Fin.castSucc 0 : Fin (n + 2)) = 0 := Fin.ext rfl
      rw [hs0, hc0]
      ring

private theorem genericHorizontalSlice_finiteChain
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (v v' w w' : K.vertices) (s t : T) {q : ℝ}
    (hvv' : v.1 ≠ v'.1) (hww' : w.1 ≠ w'.1)
    (hvVertical : v.1.re = v'.1.re) (hwVertical : w.1.re = w'.1.re)
    (hvEdge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (v'.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ K.support) \
          ((s : Tiling.Plane) +ᵥ K.vertices))
    (hwEdge : openSegment ℝ (w.1 + (t : Tiling.Plane))
      (w'.1 + (t : Tiling.Plane)) ⊆
        frontier ((t : Tiling.Plane) +ᵥ K.support) \
          ((t : Tiling.Plane) +ᵥ K.vertices))
    (hqv : q ∈ translatedVerticalInterval v.1 v'.1 s)
    (hqw : q ∈ translatedVerticalInterval w.1 w'.1 t)
    (hx : (v.1 + (s : Tiling.Plane)).re <
      (w.1 + (t : Tiling.Plane)).re)
    (_hq : q ∉ {y : ℝ | ∃ v : K.vertices, ∃ t : T,
      y = (v.1 + (t : Tiling.Plane)).im})
    (_hcover : ∀ᵐ x : ℝ ∂MeasureTheory.volume,
      ∃ t : T, (x : ℂ) + (q : ℂ) * Complex.I ∈
        (t : Tiling.Plane) +ᵥ K.openCarrier) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin n → K.vertices,
      (∀ i : Fin n, (a i).1.re < (b i).1.re) ∧
      (w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re =
        ∑ i : Fin n, ((b i).1.re - (a i).1.re) := by
  classical
  let lo : ℝ := max (min v.1.im v'.1.im + (s : Tiling.Plane).im)
    (min w.1.im w'.1.im + (t : Tiling.Plane).im)
  let hi : ℝ := min (max v.1.im v'.1.im + (s : Tiling.Plane).im)
    (max w.1.im w'.1.im + (t : Tiling.Plane).im)
  have hlohi : lo < hi := by
    have hloq : lo < q := max_lt hqv.1 hqw.1
    have hqhi : q < hi := lt_min hqv.2 hqw.2
    exact hloq.trans hqhi
  have hchainEvent :=
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints
      K T hTile Axis.horizontal
  obtain ⟨q', hq'I, hq'good, hchain'⟩ := exists_mem_Ioo_of_ae hlohi
    ((eventually_goodHorizontalSlice hTile).and hchainEvent)
  have hq'v : q' ∈ translatedVerticalInterval v.1 v'.1 s := by
    refine ⟨?_, ?_⟩
    · exact (le_max_left _ _).trans_lt hq'I.1
    · exact hq'I.2.trans_le (min_le_left _ _)
  have hq'w : q' ∈ translatedVerticalInterval w.1 w'.1 t := by
    refine ⟨?_, ?_⟩
    · exact (le_max_right _ _).trans_lt hq'I.1
    · exact hq'I.2.trans_le (min_le_right _ _)
  have hleft := verticalSide_sliceEndpoint hTile v v' s hvv' hvVertical
    hvEdge hq'v hq'good.2
  have hright := verticalSide_sliceEndpoint hTile w w' t hww' hwVertical
    hwEdge hq'w hq'good.2
  obtain ⟨n, hn, x, owner, hx0, hxlast, hfilled⟩ :=
    hchain' _ hleft _ hright hx
  have hpiece : ∀ i : Fin n, ∃ a b : K.vertices,
      x i.castSucc = (a.1 + (owner i : Tiling.Plane)).re ∧
      x i.succ = (b.1 + (owner i : Tiling.Plane)).re ∧
      a.1.re < b.1.re := by
    intro i
    obtain ⟨a, b, ha, hb, hxa, hxb, hpos, _hinside⟩ := hfilled.2 i
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hxa, hxb, ?_⟩
    simpa [Axis.coord, Complex.sub_re] using hpos
  let a : Fin n → K.vertices := fun i ↦ (hpiece i).choose
  let b : Fin n → K.vertices := fun i ↦ (hpiece i).choose_spec.choose
  have hab (i : Fin n) :
      x i.castSucc = ((a i).1 + (owner i : Tiling.Plane)).re ∧
      x i.succ = ((b i).1 + (owner i : Tiling.Plane)).re ∧
      (a i).1.re < (b i).1.re :=
    (hpiece i).choose_spec.choose_spec
  refine ⟨n, hn, a, b, fun i ↦ (hab i).2.2, ?_⟩
  rw [← hx0, ← hxlast, ← sum_fin_succ_sub_castSucc]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hab i).1, (hab i).2.1]
  simp only [Complex.add_re]
  ring

theorem horizontalCrossSection_chain
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (v v' w w' : K.vertices) (s t : T)
    (hvv' : v.1 ≠ v'.1) (hww' : w.1 ≠ w'.1)
    (hvVertical : v.1.re = v'.1.re) (hwVertical : w.1.re = w'.1.re)
    (hvEdge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (v'.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ K.support) \
          ((s : Tiling.Plane) +ᵥ K.vertices))
    (hwEdge : openSegment ℝ (w.1 + (t : Tiling.Plane))
      (w'.1 + (t : Tiling.Plane)) ⊆
        frontier ((t : Tiling.Plane) +ᵥ K.support) \
          ((t : Tiling.Plane) +ᵥ K.vertices))
    (hOverlap :
      max (min v.1.im v'.1.im + (s : Tiling.Plane).im)
          (min w.1.im w'.1.im + (t : Tiling.Plane).im) <
        min (max v.1.im v'.1.im + (s : Tiling.Plane).im)
          (max w.1.im w'.1.im + (t : Tiling.Plane).im))
    (hOrder : (v.1 + (s : Tiling.Plane)).re <
      (w.1 + (t : Tiling.Plane)).re) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b : Fin n → K.vertices,
      (∀ i : Fin n, (a i).1.re < (b i).1.re) ∧
      (w.1 + (t : Tiling.Plane)).re -
          (v.1 + (s : Tiling.Plane)).re =
        ∑ i : Fin n, ((b i).1.re - (a i).1.re) := by
  obtain ⟨q, hqI, hqbad, hqcover⟩ := goodHorizontalSlice_exists hTile hOverlap
  have hqv : q ∈ translatedVerticalInterval v.1 v'.1 s := by
    exact ⟨(le_max_left _ _).trans_lt hqI.1,
      hqI.2.trans_le (min_le_left _ _)⟩
  have hqw : q ∈ translatedVerticalInterval w.1 w'.1 t := by
    exact ⟨(le_max_right _ _).trans_lt hqI.1,
      hqI.2.trans_le (min_le_right _ _)⟩
  exact genericHorizontalSlice_finiteChain hTile v v' w w' s t
    hvv' hww' hvVertical hwVertical hvEdge hwEdge hqv hqw hOrder hqbad hqcover

private theorem eventually_goodVerticalSlice
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) :
    ∀ᵐ q : ℝ ∂MeasureTheory.volume,
      q ∉ {x : ℝ | ∃ v : K.vertices, ∃ t : T,
        x = (v.1 + (t : Tiling.Plane)).re} ∧
      ∀ᵐ y : ℝ ∂MeasureTheory.volume,
        ∃ t : T, (q : ℂ) + (y : ℂ) * Complex.I ∈
          (t : Tiling.Plane) +ᵥ K.openCarrier := by
  let bad : Set ℝ := {x : ℝ | ∃ v : K.vertices, ∃ t : T,
    x = (v.1 + (t : Tiling.Plane)).re}
  have hTcountable : T.Countable :=
    (IsPacking.locallyFinite_centres hTile.2.1).2
  have hVcountable : K.vertices.Countable := by
    rw [← K.coe_vertexFinset]
    exact K.vertexFinset.finite_toSet.countable
  let _ : Countable T := hTcountable.to_subtype
  let _ : Countable K.vertices := hVcountable.to_subtype
  have hbad : bad.Countable := by
    let f : K.vertices × T → ℝ := fun p ↦
      (p.1.1 + (p.2 : Tiling.Plane)).re
    apply (Set.countable_range f).mono
    rintro x ⟨v, t, rfl⟩
    exact ⟨(v, t), rfl⟩
  have hplane : ∀ᵐ z : Tiling.Plane ∂MeasureTheory.volume,
      ∃ t : T, z ∈ (t : Tiling.Plane) +ᵥ K.openCarrier := by
    filter_upwards [hTile.2.2] with z hz
    exact hz.mp (Set.mem_univ z)
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
    (μ := MeasureTheory.volume) (ν := MeasureTheory.volume) hpull
  filter_upwards [hbad.ae_notMem MeasureTheory.volume, hslices] with q hqbad hq
  refine ⟨hqbad, ?_⟩
  filter_upwards [hq] with y hy
  have heq : (q : ℂ) + (y : ℂ) * Complex.I =
      Complex.measurableEquivRealProd.symm (q, y) := by
    apply Complex.ext <;> simp
  rw [heq]
  exact hy

private theorem openSegment_eq_horizontal
    (v w : Tiling.Plane) (h : v.im = w.im) :
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

private theorem horizontalSide_sliceEndpoint
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (v w : K.vertices) (s : T) {q : ℝ}
    (hvw : v.1 ≠ w.1) (hhorizontal : v.1.im = w.1.im)
    (hedge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (w.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ K.support) \
          ((s : Tiling.Plane) +ᵥ K.vertices))
    (hq : q ∈ translatedHorizontalInterval v.1 w.1 s)
    (hcover : ∀ᵐ y : ℝ ∂MeasureTheory.volume,
      ∃ t : T, (q : ℂ) + (y : ℂ) * Complex.I ∈
        (t : Tiling.Plane) +ᵥ K.openCarrier) :
    (v.1 + (s : Tiling.Plane)).im ∈
      Tiling.AxisParallel.Foundations.FilledSliceChains.sliceEndpointSet
        K T Axis.vertical q := by
  let y : ℝ := (v.1 + (s : Tiling.Plane)).im
  let p : Tiling.Plane := (q : ℂ) + (y : ℂ) * Complex.I
  have hrene : v.1.re ≠ w.1.re := by
    intro hre
    apply hvw
    exact Complex.ext hre hhorizontal
  have hpseg : p ∈ openSegment ℝ (v.1 + (s : Tiling.Plane))
      (w.1 + (s : Tiling.Plane)) := by
    rw [openSegment_eq_horizontal _ _ (by simp [hhorizontal])]
    refine ⟨q, ?_, ?_⟩
    · rw [openSegment_eq_Ioo' (by simpa using hrene)]
      simpa [translatedHorizontalInterval, Complex.add_re,
        min_add_add_right, max_add_add_right] using hq
    · apply Complex.ext <;> simp [p, y]
  have hpfront := (hedge hpseg).1
  have hpSupport : p ∈ (s : Tiling.Plane) +ᵥ K.support := by
    have hclosed := K.isPolygonal.isClosed.vadd (s : Tiling.Plane)
    rw [← hclosed.closure_eq]
    exact frontier_subset_closure hpfront
  have hpclosure : p ∈ closure ((s : Tiling.Plane) +ᵥ K.openCarrier) := by
    rw [closure_vadd, show closure K.openCarrier = K.support by
      exact K.isPolygonal.closure_interior]
    exact hpSupport
  have hpnot : p ∉ openUnion K T := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    rintro ⟨t, hpt⟩
    by_cases hts : t = s
    · subst t
      apply hpfront.2
      rw [interior_vadd]
      exact hpt
    · have hcent : (t : Tiling.Plane) ≠ (s : Tiling.Plane) := by
        intro h
        exact hts (Subtype.ext h)
      have hdisj : Disjoint
          ((t : Tiling.Plane) +ᵥ K.openCarrier)
          ((s : Tiling.Plane) +ᵥ K.openCarrier) :=
        (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
          t.2 s.2 hcent
      have hmeet := mem_closure_iff.mp hpclosure
        ((t : Tiling.Plane) +ᵥ K.openCarrier)
        (isOpen_interior.vadd _) hpt
      rw [Set.disjoint_left] at hdisj
      obtain ⟨z, hzt, hzs⟩ := hmeet
      exact hdisj hzt hzs
  let U : Set ℝ := {r : ℝ |
    (q : ℂ) + (r : ℂ) * Complex.I ∈ openUnion K T}
  have hUae : ∀ᵐ r : ℝ ∂MeasureTheory.volume, r ∈ U := by
    filter_upwards [hcover] with r hr
    change (q : ℂ) + (r : ℂ) * Complex.I ∈ openUnion K T
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact hr
  have hUdense : Dense U :=
    (MeasureTheory.volume : MeasureTheory.Measure ℝ).dense_of_ae hUae
  have hynotU : y ∉ U := by
    intro hyU
    exact hpnot hyU
  change y ∈ frontier U
  refine ⟨?_, ?_⟩
  · rw [hUdense.closure_eq]
    exact Set.mem_univ y
  · intro hyint
    exact hynotU (interior_subset hyint)

private theorem verticalCrossSection_chain
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    (v v' w w' : K.vertices) (s t : T)
    (hvv' : v.1 ≠ v'.1) (hww' : w.1 ≠ w'.1)
    (hvHorizontal : v.1.im = v'.1.im)
    (hwHorizontal : w.1.im = w'.1.im)
    (hvEdge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (v'.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ K.support) \
          ((s : Tiling.Plane) +ᵥ K.vertices))
    (hwEdge : openSegment ℝ (w.1 + (t : Tiling.Plane))
      (w'.1 + (t : Tiling.Plane)) ⊆
        frontier ((t : Tiling.Plane) +ᵥ K.support) \
          ((t : Tiling.Plane) +ᵥ K.vertices))
    (hOverlap :
      max (min v.1.re v'.1.re + (s : Tiling.Plane).re)
          (min w.1.re w'.1.re + (t : Tiling.Plane).re) <
        min (max v.1.re v'.1.re + (s : Tiling.Plane).re)
          (max w.1.re w'.1.re + (t : Tiling.Plane).re))
    (hOrder : (v.1 + (s : Tiling.Plane)).im <
      (w.1 + (t : Tiling.Plane)).im) :
    ∃ n : ℕ, ∃ a b : Fin n → K.vertices,
      IsVerticalGapChain K (v.1 + (s : Tiling.Plane)).im
        (w.1 + (t : Tiling.Plane)).im n a b := by
  classical
  have hchainEvent :=
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints
      K T hTile Axis.vertical
  obtain ⟨q, hqI, hqgood, hchain⟩ := exists_mem_Ioo_of_ae hOverlap
    ((eventually_goodVerticalSlice hTile).and hchainEvent)
  have hqv : q ∈ translatedHorizontalInterval v.1 v'.1 s := by
    exact ⟨(le_max_left _ _).trans_lt hqI.1,
      hqI.2.trans_le (min_le_left _ _)⟩
  have hqw : q ∈ translatedHorizontalInterval w.1 w'.1 t := by
    exact ⟨(le_max_right _ _).trans_lt hqI.1,
      hqI.2.trans_le (min_le_right _ _)⟩
  have hbottom := horizontalSide_sliceEndpoint hTile v v' s hvv'
    hvHorizontal hvEdge hqv hqgood.2
  have htop := horizontalSide_sliceEndpoint hTile w w' t hww'
    hwHorizontal hwEdge hqw hqgood.2
  obtain ⟨n, hn, x, owner, hx0, hxlast, hfilled⟩ :=
    hchain _ hbottom _ htop hOrder
  have hpiece : ∀ i : Fin n, ∃ a b : K.vertices,
      x i.castSucc = (a.1 + (owner i : Tiling.Plane)).im ∧
      x i.succ = (b.1 + (owner i : Tiling.Plane)).im ∧
      a.1.im < b.1.im := by
    intro i
    obtain ⟨a, b, ha, hb, hxa, hxb, hpos, _hinside⟩ := hfilled.2 i
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hxa, hxb, ?_⟩
    simpa [Axis.coord, Complex.sub_im] using hpos
  let a : Fin n → K.vertices := fun i ↦ (hpiece i).choose
  let b : Fin n → K.vertices := fun i ↦ (hpiece i).choose_spec.choose
  have hab (i : Fin n) :
      x i.castSucc = ((a i).1 + (owner i : Tiling.Plane)).im ∧
      x i.succ = ((b i).1 + (owner i : Tiling.Plane)).im ∧
      (a i).1.im < (b i).1.im :=
    (hpiece i).choose_spec.choose_spec
  refine ⟨n, a, b, hn, fun i ↦ (hab i).2.2, ?_⟩
  rw [← hx0, ← hxlast, ← sum_fin_succ_sub_castSucc]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [(hab i).1, (hab i).2.1]
  simp only [Complex.add_im]
  ring

private theorem goodApproximation_preservesVerticalGapChain
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    {bottom top : ℝ} {n : ℕ}
    {a b : Fin n → C.region.vertices}
    (hchain : IsVerticalGapChain C.region bottom top n a b) :
    0 < ∑ i : Fin n,
      ((Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (b i).1 (b i).2)).im -
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (a i).1 (a i).2)).im) := by
  have hterm : ∀ i : Fin n, 0 <
      (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (b i).1 (b i).2)).im -
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (a i).1 (a i).2)).im := by
    intro i
    have hsource : 0 < (b i).1.im - (a i).1.im :=
      sub_pos.mpr (hchain.2.1 i)
    have hs := D.source_good.preservesVertexCoordinateSign Axis.vertical
      (b i).1 (a i).1 (b i).2 (a i).2
    simp only [Axis.coord, Complex.sub_im] at hs
    have hsMapped : Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint (b i).1 (b i).2)).im -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint (a i).1 (a i).2)).im) = 1 := by
      rw [hs, Real.sign_of_pos hsource]
    by_contra hnot
    have hnonpos :
        (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint (b i).1 (b i).2)).im -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint (a i).1 (a i).2)).im ≤ 0 := le_of_not_gt hnot
    rcases hnonpos.eq_or_lt with hzero | hneg
    · rw [hzero, Real.sign_zero] at hsMapped
      norm_num at hsMapped
    · rw [Real.sign_of_neg hneg] at hsMapped
      norm_num at hsMapped
  let _ : Nonempty (Fin n) := ⟨⟨0, hchain.1⟩⟩
  exact Finset.sum_pos (fun i _hi ↦ hterm i) Finset.univ_nonempty

private theorem mappedVerticalDifference_eq_gapSum
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (v w : C.region.vertices) (s t : C.centres)
    {n : ℕ} {a b : Fin n → C.region.vertices}
    (hchain : IsVerticalGapChain C.region
      (v.1 + (s : Tiling.Plane)).im
      (w.1 + (t : Tiling.Plane)).im n a b) :
    (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
      (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v.1 v.2) + P.fullCenters s).im =
    ∑ i : Fin n,
      ((Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (b i).1 (b i).2)).im -
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint (a i).1 (a i).2)).im) := by
  have hlinear :
      (⟨w.1.im, C.vertex_im_mem w.1 w.2⟩ : C.coordinateSpace) +
          ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ -
        (⟨v.1.im, C.vertex_im_mem v.1 v.2⟩ +
          ⟨s.1.im, C.centre_im_mem s.1 s.2⟩) =
      ∑ i : Fin n,
        ((⟨(b i).1.im, C.vertex_im_mem (b i).1 (b i).2⟩ : C.coordinateSpace) -
          ⟨(a i).1.im, C.vertex_im_mem (a i).1 (a i).2⟩) := by
    apply Subtype.ext
    change C.coordinateSpace.subtype
        ((⟨w.1.im, C.vertex_im_mem w.1 w.2⟩ : C.coordinateSpace) +
          ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ -
          (⟨v.1.im, C.vertex_im_mem v.1 v.2⟩ +
            ⟨s.1.im, C.centre_im_mem s.1 s.2⟩)) =
      C.coordinateSpace.subtype
        (∑ i : Fin n,
          ((⟨(b i).1.im, C.vertex_im_mem (b i).1 (b i).2⟩ : C.coordinateSpace) -
            ⟨(a i).1.im, C.vertex_im_mem (a i).1 (a i).2⟩))
    rw [map_sub, map_add, map_add, map_sum]
    simp only [Submodule.subtype_apply, Submodule.coe_sub]
    simpa only [Complex.add_im] using hchain.2.2
  have hmap := congrArg phi hlinear
  have hmapReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hmap
  rw [P.fullCenters_apply t, P.fullCenters_apply s]
  simpa only [map_sub, map_add, map_sum, Rat.cast_sub, Rat.cast_add,
    Rat.cast_sum, Tiling.AxisParallel.Approximation.mapPoint,
    Tiling.AxisParallel.Approximation.mapScalar, Complex.add_im,
    Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
    Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
    Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, mul_one, zero_add, add_zero] using hmapReal

theorem deformation_preservesHorizontalEdgeOrder
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (v v' w w' : C.region.vertices) (s t : C.centres)
    (hvv' : v.1 ≠ v'.1) (hww' : w.1 ≠ w'.1)
    (hvHorizontal : v.1.im = v'.1.im)
    (hwHorizontal : w.1.im = w'.1.im)
    (hvEdge : openSegment ℝ (v.1 + (s : Tiling.Plane))
      (v'.1 + (s : Tiling.Plane)) ⊆
        frontier ((s : Tiling.Plane) +ᵥ C.region.support) \
          ((s : Tiling.Plane) +ᵥ C.region.vertices))
    (hwEdge : openSegment ℝ (w.1 + (t : Tiling.Plane))
      (w'.1 + (t : Tiling.Plane)) ⊆
        frontier ((t : Tiling.Plane) +ᵥ C.region.support) \
          ((t : Tiling.Plane) +ᵥ C.region.vertices))
    (hOverlap :
      max (min v.1.re v'.1.re + (s : Tiling.Plane).re)
          (min w.1.re w'.1.re + (t : Tiling.Plane).re) <
        min (max v.1.re v'.1.re + (s : Tiling.Plane).re)
          (max w.1.re w'.1.re + (t : Tiling.Plane).re)) :
    Real.sign ((w.1 + (t : Tiling.Plane)).im -
      (v.1 + (s : Tiling.Plane)).im) =
    Real.sign
      ((Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v.1 v.2) + P.fullCenters s).im) := by
  let sourceDifference : ℝ :=
    (w.1 + (t : Tiling.Plane)).im - (v.1 + (s : Tiling.Plane)).im
  let mappedDifference : ℝ :=
    (Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
      (Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint v.1 v.2) + P.fullCenters s).im
  change Real.sign sourceDifference = Real.sign mappedDifference
  rcases lt_trichotomy sourceDifference 0 with hneg | hzero | hpos
  · have hOrder : (w.1 + (t : Tiling.Plane)).im <
        (v.1 + (s : Tiling.Plane)).im := by
      change (w.1 + (t : Tiling.Plane)).im -
        (v.1 + (s : Tiling.Plane)).im < 0 at hneg
      exact sub_neg.mp hneg
    have hOverlap' :
        max (min w.1.re w'.1.re + (t : Tiling.Plane).re)
            (min v.1.re v'.1.re + (s : Tiling.Plane).re) <
          min (max w.1.re w'.1.re + (t : Tiling.Plane).re)
            (max v.1.re v'.1.re + (s : Tiling.Plane).re) := by
      simpa only [max_comm, min_comm] using hOverlap
    obtain ⟨n, a, b, hchain⟩ := verticalCrossSection_chain
      P.source_tilesOn w w' v v' t s hww' hvv' hwHorizontal hvHorizontal
        hwEdge hvEdge hOverlap' hOrder
    have hsumpos := goodApproximation_preservesVerticalGapChain C phi D hchain
    have heq := mappedVerticalDifference_eq_gapSum C phi D P w v t s hchain
    have hmappedneg : mappedDifference < 0 := by
      have hreverse : 0 <
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) + P.fullCenters s).im -
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) + P.fullCenters t).im := by
        rw [heq]
        exact hsumpos
      change
        (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2) + P.fullCenters s).im < 0
      exact sub_neg.mpr (sub_pos.mp hreverse)
    rw [Real.sign_of_neg hneg, Real.sign_of_neg hmappedneg]
  · have hcoord :
        (⟨w.1.im, C.vertex_im_mem w.1 w.2⟩ : C.coordinateSpace) +
            ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ =
          ⟨v.1.im, C.vertex_im_mem v.1 v.2⟩ +
            ⟨s.1.im, C.centre_im_mem s.1 s.2⟩ := by
      apply Subtype.ext
      change (w.1.im + t.1.im) - (v.1.im + s.1.im) = 0 at hzero
      change w.1.im + t.1.im = v.1.im + s.1.im
      linarith
    have hmapcoord := congrArg phi hcoord
    have hmapcoordReal := congrArg (fun q : ℚ ↦ (q : ℝ)) hmapcoord
    simp only [map_add, Rat.cast_add] at hmapcoordReal
    have hmappedzero : mappedDifference = 0 := by
      dsimp [mappedDifference]
      rw [P.fullCenters_apply t, P.fullCenters_apply s]
      simp only [Tiling.AxisParallel.Approximation.mapPoint,
        Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
        Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint,
        Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, zero_add, add_zero]
      exact sub_eq_zero.mpr hmapcoordReal
    rw [hzero, hmappedzero, Real.sign_zero]
  · have hOrder : (v.1 + (s : Tiling.Plane)).im <
        (w.1 + (t : Tiling.Plane)).im := by
      change 0 < (w.1 + (t : Tiling.Plane)).im -
        (v.1 + (s : Tiling.Plane)).im at hpos
      exact sub_pos.mp hpos
    obtain ⟨n, a, b, hchain⟩ := verticalCrossSection_chain
      P.source_tilesOn v v' w w' s t hvv' hww' hvHorizontal hwHorizontal
        hvEdge hwEdge hOverlap hOrder
    have hsumpos := goodApproximation_preservesVerticalGapChain C phi D hchain
    have heq := mappedVerticalDifference_eq_gapSum C phi D P v w s t hchain
    have hmappedpos : 0 < mappedDifference := by
      change 0 <
        (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2) + P.fullCenters s).im
      rw [heq]
      exact hsumpos
    rw [Real.sign_of_pos hpos, Real.sign_of_pos hmappedpos]







private theorem re_eq_of_mem_openSegment_vertical
    {a b p : Tiling.Plane} (hab : a.re = b.re)
    (hp : p ∈ openSegment ℝ a b) : p.re = a.re := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, _hr, rfl⟩ := hp
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring


private theorem mem_openSegment_sub_iff
    {a b t z : Tiling.Plane} :
    z ∈ openSegment ℝ (a - t) (b - t) ↔ z + t ∈ openSegment ℝ a b := by
  rw [show a = t +ᵥ (a - t) by simp [vadd_eq_add, sub_eq_add_neg],
    show b = t +ᵥ (b - t) by simp [vadd_eq_add, sub_eq_add_neg],
    ← vadd_openSegment ℝ]
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  constructor <;> intro h
  · simpa [add_assoc] using h
  · simpa [add_assoc] using h

private theorem lt_iff_of_sign_sub_eq {a b A B : ℝ}
    (h : Real.sign (b - a) = Real.sign (B - A)) :
    a < b ↔ A < B := by
  have forward {x y X Y : ℝ}
      (hsign : Real.sign (y - x) = Real.sign (Y - X))
      (hxy : x < y) : X < Y := by
    have hsource : Real.sign (y - x) = 1 :=
      Real.sign_of_pos (sub_pos.mpr hxy)
    have htarget : Real.sign (Y - X) = 1 := hsign.symm.trans hsource
    by_contra hnot
    have hle : Y - X ≤ 0 := sub_nonpos.mpr (le_of_not_gt hnot)
    rcases hle.eq_or_lt with hzero | hneg
    · rw [hzero, Real.sign_zero] at htarget
      norm_num at htarget
    · rw [Real.sign_of_neg hneg] at htarget
      norm_num at htarget
  exact ⟨forward h, forward h.symm⟩

private theorem horizontalIntervalOverlap_transport
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (P₁ : C.centres → Tiling.Plane)
    (hP₁ : ∀ s : C.centres,
      P₁ s = Tiling.AxisParallel.Approximation.mapPoint phi
        (C.centrePoint s.1 s.2))
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    (v v' w w' : C.region.vertices) (s t : C.centres) :
    (translatedHorizontalInterval v.1 v'.1 s ∩
      translatedHorizontalInterval w.1 w'.1 t).Nonempty ↔
    (translatedHorizontalInterval
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v.1 v.2))
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint v'.1 v'.2)) (P₁ s) ∩
      translatedHorizontalInterval
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w.1 w.2))
        (Tiling.AxisParallel.Approximation.mapPoint phi
          (C.vertexPoint w'.1 w'.2)) (P₁ t)).Nonempty := by
  have hlt (a b : C.region.vertices) (p q : C.centres) :
      (a.1 + (p : Tiling.Plane)).re <
          (b.1 + (q : Tiling.Plane)).re ↔
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint a.1 a.2) + P₁ p).re <
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint b.1 b.2) + P₁ q).re := by
    apply lt_iff_of_sign_sub_eq
    simpa only [hP₁ p, hP₁ q] using hHorizontalSign a b p q
  have hlt' (a b : C.region.vertices) (p q : C.centres) :
      a.1.re + (p : Tiling.Plane).re <
          b.1.re + (q : Tiling.Plane).re ↔
        (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint a.1 a.2)).re + (P₁ p).re <
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint b.1 b.2)).re + (P₁ q).re := by
    simpa only [Complex.add_re] using hlt a b p q
  simp only [translatedHorizontalInterval, ← min_add_add_right,
    ← max_add_add_right, Set.Ioo_inter_Ioo,
    Set.nonempty_Ioo, max_lt_iff, lt_min_iff, min_lt_iff, lt_max_iff]
  simp only [hlt']

private theorem mappedCentre_firstCoordinate_eq_iff
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re)) :
    ∀ s t : C.centres,
      (s : Tiling.Plane).re = (t : Tiling.Plane).re ↔
        (P.fullCenters s).re = (P.fullCenters t).re := by
  obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair C.region
  let vC : C.region.vertices := ⟨v, hv⟩
  intro s t
  have hsign := hHorizontalSign vC vC t s
  rw [P.fullCenters_apply s, P.fullCenters_apply t]
  have hsign' :
      Real.sign ((s : Tiling.Plane).re - (t : Tiling.Plane).re) =
        Real.sign
          ((Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint s.1 s.2)).re -
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.centrePoint t.1 t.2)).re) := by
    simpa only [Complex.add_re, add_sub_add_left_eq_sub] using hsign
  constructor
  · intro hst
    have hsource : Real.sign ((s : Tiling.Plane).re - (t : Tiling.Plane).re) = 0 := by
      rw [hst, sub_self, Real.sign_zero]
    have htarget := hsign'.symm.trans hsource
    exact sub_eq_zero.mp (Real.sign_eq_zero_iff.mp htarget)
  · intro hst
    have htarget : Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi
            (C.centrePoint s.1 s.2)).re -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.centrePoint t.1 t.2)).re) = 0 := by
      rw [hst, sub_self, Real.sign_zero]
    have hsource := hsign'.trans htarget
    exact sub_eq_zero.mp (Real.sign_eq_zero_iff.mp hsource)

private theorem vertexEquiv_val_eq_mapPoint
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (v : C.region.vertices) :
    (D.vertexEquiv v : Tiling.Plane) =
      Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint v.1 v.2) :=
  D.vertexEquiv_apply v |>.trans (D.vertex_agreement v.1 v.2)

private theorem intrinsicHorizontalSide_vertexEquiv_iff
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (v w : C.region.vertices) :
    IsIntrinsicHorizontalSide C.region v w ↔
      IsIntrinsicHorizontalSide D.deformedRegion (D.vertexEquiv v) (D.vertexEquiv w) := by
  unfold IsIntrinsicHorizontalSide
  rw [Tiling.AxisParallel.Approximation.intrinsicHorizontalSide_transport C phi D v w]
  constructor
  · rintro ⟨_hv, _hw, hside⟩
    simpa only [vertexEquiv_val_eq_mapPoint] using hside
  · intro hside
    refine ⟨?_, ?_, ?_⟩
    · rw [← vertexEquiv_val_eq_mapPoint C phi D v]
      exact (D.vertexEquiv v).2
    · rw [← vertexEquiv_val_eq_mapPoint C phi D w]
      exact (D.vertexEquiv w).2
    · simpa only [vertexEquiv_val_eq_mapPoint] using hside

theorem deformation_preservesProperHorizontalContact
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    (s t : C.centres) :
    HorizontalProperContact C.region s t ↔
      HorizontalProperContact D.deformedRegion (P.fullCenters s) (P.fullCenters t) := by
  rw [horizontalProperContact_iff_exists_intrinsicSides,
    horizontalProperContact_iff_exists_intrinsicSides]
  constructor
  · rintro ⟨v, v', w, w', hvv, hww, hheight, hoverlap⟩
    refine ⟨D.vertexEquiv v, D.vertexEquiv v', D.vertexEquiv w,
      D.vertexEquiv w',
      (intrinsicHorizontalSide_vertexEquiv_iff C phi D v v').mp hvv,
      (intrinsicHorizontalSide_vertexEquiv_iff C phi D w w').mp hww, ?_, ?_⟩
    · have hedge := deformation_preservesHorizontalEdgeOrder C phi D P
        v v' w w' s t hvv.1 hww.1 hvv.2.1 hww.2.1
        (by
          intro z hz
          have hzEdge := hvv.2.2 (by
            rw [show v.1 + (s : Tiling.Plane) =
                (s : Tiling.Plane) +ᵥ v.1 by simp [add_comm],
              show v'.1 + (s : Tiling.Plane) =
                (s : Tiling.Plane) +ᵥ v'.1 by simp [add_comm],
              ← vadd_openSegment ℝ] at hz
            simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
              neg_add_eq_sub] using hz)
          exact ⟨(by
            simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
              vadd_eq_add, neg_add_eq_sub] using hzEdge.1), by
            rw [Set.mem_vadd_set_iff_neg_vadd_mem]
            simpa [sub_eq_add_neg, add_comm] using hzEdge.2⟩)
        (by
          intro z hz
          have hzEdge := hww.2.2 (by
            rw [show w.1 + (t : Tiling.Plane) =
                (t : Tiling.Plane) +ᵥ w.1 by simp [add_comm],
              show w'.1 + (t : Tiling.Plane) =
                (t : Tiling.Plane) +ᵥ w'.1 by simp [add_comm],
              ← vadd_openSegment ℝ] at hz
            simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
              neg_add_eq_sub] using hz)
          exact ⟨(by
            simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
              vadd_eq_add, neg_add_eq_sub] using hzEdge.1), by
            rw [Set.mem_vadd_set_iff_neg_vadd_mem]
            simpa [sub_eq_add_neg, add_comm] using hzEdge.2⟩)
        (by
          simpa only [translatedHorizontalInterval, Set.Ioo_inter_Ioo,
            Set.nonempty_Ioo] using hoverlap)
      have hsource : Real.sign
          ((w.1 + (t : Tiling.Plane)).im -
            (v.1 + (s : Tiling.Plane)).im) = 0 := by
        rw [hheight, sub_self, Real.sign_zero]
      have htarget := hedge.symm.trans hsource
      have heq := sub_eq_zero.mp (Real.sign_eq_zero_iff.mp htarget)
      simpa only [vertexEquiv_val_eq_mapPoint] using heq.symm
    · simpa only [translatedHorizontalInterval, vertexEquiv_val_eq_mapPoint,
        P.fullCenters_apply] using
        (horizontalIntervalOverlap_transport C phi P.fullCenters
          P.fullCenters_apply hHorizontalSign v v' w w' s t).mp hoverlap
  · rintro ⟨V, V', W, W', hVV, hWW, hheight, hoverlap⟩
    let v := D.vertexEquiv.symm V
    let v' := D.vertexEquiv.symm V'
    let w := D.vertexEquiv.symm W
    let w' := D.vertexEquiv.symm W'
    have hVMap : Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint v.1 v.2) = V.1 := by
      rw [← vertexEquiv_val_eq_mapPoint C phi D v]
      exact congrArg Subtype.val (D.vertexEquiv.apply_symm_apply V)
    have hV'Map : Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint v'.1 v'.2) = V'.1 := by
      rw [← vertexEquiv_val_eq_mapPoint C phi D v']
      exact congrArg Subtype.val (D.vertexEquiv.apply_symm_apply V')
    have hWMap : Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint w.1 w.2) = W.1 := by
      rw [← vertexEquiv_val_eq_mapPoint C phi D w]
      exact congrArg Subtype.val (D.vertexEquiv.apply_symm_apply W)
    have hW'Map : Tiling.AxisParallel.Approximation.mapPoint phi
        (C.vertexPoint w'.1 w'.2) = W'.1 := by
      rw [← vertexEquiv_val_eq_mapPoint C phi D w']
      exact congrArg Subtype.val (D.vertexEquiv.apply_symm_apply W')
    have hvv : IsIntrinsicHorizontalSide C.region v v' :=
      (intrinsicHorizontalSide_vertexEquiv_iff C phi D v v').mpr (by
        simpa only [IsIntrinsicHorizontalSide, v, v', D.vertexEquiv.apply_symm_apply] using hVV)
    have hww : IsIntrinsicHorizontalSide C.region w w' :=
      (intrinsicHorizontalSide_vertexEquiv_iff C phi D w w').mpr (by
        simpa only [IsIntrinsicHorizontalSide, w, w', D.vertexEquiv.apply_symm_apply] using hWW)
    have hoverlap' :
        (translatedHorizontalInterval v.1 v'.1 s ∩
          translatedHorizontalInterval w.1 w'.1 t).Nonempty := by
      apply (horizontalIntervalOverlap_transport C phi P.fullCenters
        P.fullCenters_apply hHorizontalSign v v' w w' s t).mpr
      simpa only [translatedHorizontalInterval, hVMap, hV'Map, hWMap, hW'Map] using hoverlap
    refine ⟨v, v', w, w', hvv, hww, ?_, hoverlap'⟩
    have hedge := deformation_preservesHorizontalEdgeOrder C phi D P
      v v' w w' s t hvv.1 hww.1 hvv.2.1 hww.2.1
      (by
        intro z hz
        have hzEdge := hvv.2.2 (by
          rw [show v.1 + (s : Tiling.Plane) =
              (s : Tiling.Plane) +ᵥ v.1 by simp [add_comm],
            show v'.1 + (s : Tiling.Plane) =
              (s : Tiling.Plane) +ᵥ v'.1 by simp [add_comm],
            ← vadd_openSegment ℝ] at hz
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_eq_sub] using hz)
        exact ⟨(by
          simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
            vadd_eq_add, neg_add_eq_sub] using hzEdge.1), by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [sub_eq_add_neg, add_comm] using hzEdge.2⟩)
      (by
        intro z hz
        have hzEdge := hww.2.2 (by
          rw [show w.1 + (t : Tiling.Plane) =
              (t : Tiling.Plane) +ᵥ w.1 by simp [add_comm],
            show w'.1 + (t : Tiling.Plane) =
              (t : Tiling.Plane) +ᵥ w'.1 by simp [add_comm],
            ← vadd_openSegment ℝ] at hz
          simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            neg_add_eq_sub] using hz)
        exact ⟨(by
          simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
            vadd_eq_add, neg_add_eq_sub] using hzEdge.1), by
          rw [Set.mem_vadd_set_iff_neg_vadd_mem]
          simpa [sub_eq_add_neg, add_comm] using hzEdge.2⟩)
      (by
        simpa only [translatedHorizontalInterval, Set.Ioo_inter_Ioo,
          Set.nonempty_Ioo] using hoverlap')
    have htarget : Real.sign
        ((Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint w.1 w.2) + P.fullCenters t).im -
          (Tiling.AxisParallel.Approximation.mapPoint phi
            (C.vertexPoint v.1 v.2) + P.fullCenters s).im) = 0 := by
      have hEq :
          (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint v.1 v.2) + P.fullCenters s).im =
            (Tiling.AxisParallel.Approximation.mapPoint phi
              (C.vertexPoint w.1 w.2) + P.fullCenters t).im := by
        simpa only [hVMap, hWMap] using hheight
      rw [hEq, sub_self, Real.sign_zero]
    have hsource := hedge.trans htarget
    exact sub_eq_zero.mp (Real.sign_eq_zero_iff.mp hsource) |>.symm

theorem deformation_preservesColumns
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport
      C phi D)
    (hContact : ∀ s t : C.centres,
      HorizontalProperContact C.region s t ↔
        HorizontalProperContact D.deformedRegion
          (P.fullCenters s) (P.fullCenters t))
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    (Q : VerticalPlate C.region C.centres) :
    IsVerticalColumn Q ↔
      IsVerticalColumn (deformation_verticalPlateEquiv C phi D P hContact Q) := by
  rw [isVerticalColumn_iff, isVerticalColumn_iff]
  have hcoord := mappedCentre_firstCoordinate_eq_iff C phi D P hHorizontalSign
  have hcentres := deformation_verticalPlateEquiv_centres C phi D P hContact Q
  obtain ⟨q, hq⟩ := Q.nonempty_supp
  have hqQ : (q : Tiling.Plane) ∈ Q.centres := ⟨q, hq, rfl⟩
  constructor
  · rintro ⟨_x, hx⟩
    refine ⟨(P.fullCenters q).re, ?_⟩
    intro z hz
    rw [hcentres] at hz
    obtain ⟨r, hrQ, rfl⟩ := hz
    have hqr : (q : Tiling.Plane).re = (r : Tiling.Plane).re := by
      rw [hx hqQ, hx hrQ]
    exact (hcoord q r).mp hqr |>.symm
  · rintro ⟨_x, hx⟩
    refine ⟨(q : Tiling.Plane).re, ?_⟩
    rintro _z ⟨r, hrQ, rfl⟩
    have hqTarget : (P.fullCenters q : Tiling.Plane) ∈
        (deformation_verticalPlateEquiv C phi D P hContact Q).centres := by
      rw [hcentres]
      exact ⟨q, hqQ, rfl⟩
    have hrTarget : (P.fullCenters r : Tiling.Plane) ∈
        (deformation_verticalPlateEquiv C phi D P hContact Q).centres := by
      rw [hcentres]
      exact ⟨r, ⟨r, hrQ, rfl⟩, rfl⟩
    exact (hcoord q r).mpr ((hx hqTarget).trans (hx hrTarget).symm) |>.symm

private theorem vertical_point_mem_openSegment_iff
    {a b : Tiling.Plane} (_hab : a ≠ b) (hh : a.re = b.re) (y : ℝ) :
    (a.re + y * Complex.I) ∈ openSegment ℝ a b ↔
      y ∈ openSegment ℝ a.im b.im := by
  rw [openSegment_eq_image, openSegment_eq_image]
  constructor <;> rintro ⟨r, hr, h⟩
  · refine ⟨r, hr, ?_⟩
    simpa using congrArg Complex.im h
  · refine ⟨r, hr, ?_⟩
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im, mul_one,
        sub_zero,
        Complex.smul_re, smul_eq_mul]
      rw [hh]
      ring
    · simpa using congrArg id h

private theorem im_mem_openSegment_of_mem
    {a b p : Tiling.Plane} (hp : p ∈ openSegment ℝ a b) :
    p.im ∈ openSegment ℝ a.im b.im := by
  rw [openSegment_eq_image] at hp ⊢
  obtain ⟨r, hr, h⟩ := hp
  refine ⟨r, hr, ?_⟩
  simpa using congrArg Complex.im h


private theorem labelledSides_giveVerticalIncidence
    {K : Region} {s t : Tiling.Plane}
    {a b a' b' : K.vertices}
    (_hab : a.1 ≠ b.1) (_habRe : a.1.re = b.1.re)
    (habEdge : openSegment ℝ a.1 b.1 ⊆ frontier K.support \ K.vertices)
    (_ha'b' : a'.1 ≠ b'.1) (_ha'b'Re : a'.1.re = b'.1.re)
    (ha'b'Edge : openSegment ℝ a'.1 b'.1 ⊆ frontier K.support \ K.vertices)
    (u v : Tiling.Plane) (_huv : u ≠ v) (_huvRe : u.re = v.re)
    (hoverlap : openSegment ℝ u v ⊆
      openSegment ℝ (a.1 + s) (b.1 + s) ∩
        openSegment ℝ (a'.1 + t) (b'.1 + t)) :
    openSegment ℝ u v ⊆
      (frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)) \
        ((s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices)) := by
  intro z hz
  have hzBoth := hoverlap hz
  have hzFirst : z - s ∈ openSegment ℝ a.1 b.1 := by
    rw [show a.1 + s = s +ᵥ a.1 by simp [add_comm],
      show b.1 + s = s +ᵥ b.1 by simp [add_comm], ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.1
  have hzSecond : z - t ∈ openSegment ℝ a'.1 b'.1 := by
    rw [show a'.1 + t = t +ᵥ a'.1 by simp [add_comm],
      show b'.1 + t = t +ᵥ b'.1 by simp [add_comm], ← vadd_openSegment ℝ] at hzBoth
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzBoth.2
  have hzFirstEdge := habEdge hzFirst
  have hzSecondEdge := ha'b'Edge hzSecond
  refine ⟨⟨(by
    simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using hzFirstEdge.1),
    (by
      simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hzSecondEdge.1)⟩, ?_⟩
  intro hzVertices
  rcases hzVertices with hzVertices | hzVertices
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
    exact hzFirstEdge.2 (by simpa [sub_eq_add_neg, add_comm] using hzVertices)
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzVertices
    exact hzSecondEdge.2 (by simpa [sub_eq_add_neg, add_comm] using hzVertices)

private theorem properVerticalIncidence_intrinsicSides
    (K : Region) {Sₗ Sᵣ : Set Tiling.Plane}
    {Xₗ Xᵣ : Set ℝ} {x delta : ℝ}
    (_hdelta : 0 < delta)
    (_hSupportₗ : regularSupport K Sₗ = Complex.re ⁻¹' Xₗ)
    (_hSupportᵣ : regularSupport K Sᵣ = Complex.re ⁻¹' Xᵣ)
    (_hLeft : Complex.re ⁻¹' Set.Ioo (x - delta) x ⊆ regularSupport K Sₗ)
    (_hRight : Complex.re ⁻¹' Set.Ioo x (x + delta) ⊆ regularSupport K Sᵣ) :
    ((∃ s ∈ Sₗ, ∃ t ∈ Sᵣ, ∃ a b : Tiling.Plane,
      a ≠ b ∧ a.re = b.re ∧ a.re = x ∧
      openSegment ℝ a b ⊆
        (frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)) \
          ((s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices))) ↔
    ∃ s ∈ Sₗ, ∃ t ∈ Sᵣ,
      ∃ v v' w w' : K.vertices,
        IsIntrinsicVerticalSide K v v' ∧ IsIntrinsicVerticalSide K w w' ∧
        (v.1 + s).re = x ∧ (w.1 + t).re = x ∧
        (translatedVerticalInterval v.1 v'.1 s ∩
          translatedVerticalInterval w.1 w'.1 t).Nonempty) := by
  constructor
  · rintro ⟨s, hsS, t, htS, a, b, hab, habRe, haRe, hcontact⟩
    let p : Tiling.Plane := midpoint ℝ a b
    have hpAB : p ∈ openSegment ℝ a b := midpoint_mem_openSegment a b
    have hpContact := hcontact hpAB
    have hpSFrontier : p - s ∈ frontier K.support :=
      by
        simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
          vadd_eq_add, neg_add_eq_sub] using hpContact.1.1
    have hpSNotVertex : p - s ∉ K.vertices := by
      intro hpVertex
      apply hpContact.2
      left
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
    have hpTFrontier : p - t ∈ frontier K.support :=
      by
        simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
          vadd_eq_add, neg_add_eq_sub] using hpContact.1.2
    have hpTNotVertex : p - t ∉ K.vertices := by
      intro hpVertex
      apply hpContact.2
      right
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpVertex
    obtain ⟨axisS, v, v', hvv, hvvCoord, hpVV, hvvEdge⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
        K (p - s) hpSFrontier hpSNotVertex
    have hvvRe : v.1.re = v'.1.re := by
      cases axisS with
      | vertical => exact hvvCoord
      | horizontal =>
          exfalso
          apply hpSNotVertex
          apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
            (c := v.1) (d := v'.1) (p := p - s)
            (v := a - s) (w := b - s)
          · exact hvv
          · exact hvvCoord
          · exact fun z hz ↦ (hvvEdge hz).1
          · exact hpVV
          · exact fun h ↦ hab (sub_left_inj.mp h)
          · simp only [Complex.sub_re]
            linarith
          · apply mem_openSegment_sub_iff.mpr
            simpa using hpAB
          · intro z hz
            have hzPlaced := mem_openSegment_sub_iff.mp hz
            simpa [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
              vadd_eq_add, neg_add_eq_sub] using (hcontact hzPlaced).1.1
    obtain ⟨axisT, w, w', hww, hwwCoord, hpWW, hwwEdge⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
        K (p - t) hpTFrontier hpTNotVertex
    have hwwRe : w.1.re = w'.1.re := by
      cases axisT with
      | vertical => exact hwwCoord
      | horizontal =>
          exfalso
          apply hpTNotVertex
          apply K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
            (c := w.1) (d := w'.1) (p := p - t)
            (v := a - t) (w := b - t)
          · exact hww
          · exact hwwCoord
          · exact fun z hz ↦ (hwwEdge hz).1
          · exact hpWW
          · exact fun h ↦ hab (sub_left_inj.mp h)
          · simp only [Complex.sub_re]
            linarith
          · apply mem_openSegment_sub_iff.mpr
            simpa using hpAB
          · intro z hz
            have hzPlaced := mem_openSegment_sub_iff.mp hz
            simpa [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
              vadd_eq_add, neg_add_eq_sub] using (hcontact hzPlaced).1.2
    have hpVVPlaced : p ∈ openSegment ℝ (v.1 + s) (v'.1 + s) := by
      rw [show v.1 + s = s +ᵥ v.1 by simp [add_comm],
        show v'.1 + s = s +ᵥ v'.1 by simp [add_comm], ← vadd_openSegment ℝ]
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hpVV
    have hpWWPlaced : p ∈ openSegment ℝ (w.1 + t) (w'.1 + t) := by
      rw [show w.1 + t = t +ᵥ w.1 by simp [add_comm],
        show w'.1 + t = t +ᵥ w'.1 by simp [add_comm], ← vadd_openSegment ℝ]
      simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
        neg_add_eq_sub] using hpWW
    refine ⟨s, hsS, t, htS, v, v', w, w', ⟨hvv, hvvRe, hvvEdge⟩,
      ⟨hww, hwwRe, hwwEdge⟩, ?_, ?_, ⟨p.im, ?_, ?_⟩⟩
    · have hpRawRe := re_eq_of_mem_openSegment_vertical habRe hpAB
      have hpSideRe := re_eq_of_mem_openSegment_vertical hvvRe hpVV
      simp only [Complex.sub_re, Complex.add_re] at hpSideRe ⊢
      linarith
    · have hpRawRe := re_eq_of_mem_openSegment_vertical habRe hpAB
      have hpSideRe := re_eq_of_mem_openSegment_vertical hwwRe hpWW
      simp only [Complex.sub_re, Complex.add_re] at hpSideRe ⊢
      linarith
    · have hvvIm : v.1.im ≠ v'.1.im := fun him ↦ hvv (Complex.ext hvvRe him)
      have hvvPlacedIm : (v.1 + s).im ≠ (v'.1 + s).im := by
        simp only [Complex.add_im]
        exact fun h ↦ hvvIm (add_right_cancel h)
      have him := im_mem_openSegment_of_mem hpVVPlaced
      rw [openSegment_eq_Ioo' hvvPlacedIm] at him
      simpa only [translatedVerticalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_im] using him
    · have hwwIm : w.1.im ≠ w'.1.im := fun him ↦ hww (Complex.ext hwwRe him)
      have hwwPlacedIm : (w.1 + t).im ≠ (w'.1 + t).im := by
        simp only [Complex.add_im]
        exact fun h ↦ hwwIm (add_right_cancel h)
      have him := im_mem_openSegment_of_mem hpWWPlaced
      rw [openSegment_eq_Ioo' hwwPlacedIm] at him
      simpa only [translatedVerticalInterval, ← min_add_add_right,
        ← max_add_add_right, Complex.add_im] using him
  · rintro ⟨s, hsS, t, htS, v, v', w, w', ⟨hvv, hvvRe, hvvEdge⟩,
      ⟨hww, hwwRe, hwwEdge⟩, hvx, hwx, hoverlap⟩
    rw [translatedVerticalInterval, translatedVerticalInterval,
      Set.Ioo_inter_Ioo, Set.nonempty_Ioo] at hoverlap
    let lo := max (min v.1.im v'.1.im + s.im)
      (min w.1.im w'.1.im + t.im)
    let hi := min (max v.1.im v'.1.im + s.im)
      (max w.1.im w'.1.im + t.im)
    have hlohi : lo < hi := hoverlap
    let u : Tiling.Plane := (x : ℂ) + lo * Complex.I
    let z : Tiling.Plane := (x : ℂ) + hi * Complex.I
    have huz : u ≠ z := by
      intro h
      have him := congrArg Complex.im h
      simp only [u, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
        zero_add, add_zero] at him
      exact hlohi.ne him
    have huzRe : u.re = z.re := by simp [u, z]
    have huRe : u.re = x := by simp [u]
    have hEdge := labelledSides_giveVerticalIncidence hvv hvvRe hvvEdge
      hww hwwRe hwwEdge u z huz huzRe (by
          intro q hq
          have hqRe := re_eq_of_mem_openSegment_vertical huzRe hq
          have hqImRaw := im_mem_openSegment_of_mem hq
          have hlohiNe : lo ≠ hi := hlohi.ne
          have hqIm : q.im ∈ Set.Ioo lo hi := by
            simp only [u, z, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
              zero_add, add_zero, openSegment_eq_Ioo' hlohiNe,
              min_eq_left hlohi.le, max_eq_right hlohi.le] at hqImRaw
            exact hqImRaw
          have hqFirstInterval : q.im ∈ translatedVerticalInterval v.1 v'.1 s :=
            ⟨(le_max_left _ _).trans_lt hqIm.1,
              hqIm.2.trans_le (min_le_left _ _)⟩
          have hqSecondInterval : q.im ∈ translatedVerticalInterval w.1 w'.1 t :=
            ⟨(le_max_right _ _).trans_lt hqIm.1,
              hqIm.2.trans_le (min_le_right _ _)⟩
          have hvvIm : v.1.im ≠ v'.1.im := fun him ↦ hvv (Complex.ext hvvRe him)
          have hvvPlaced : v.1 + s ≠ v'.1 + s := fun h ↦ hvv (add_right_cancel h)
          have hvvPlacedRe : (v.1 + s).re = (v'.1 + s).re := by
            simp only [Complex.add_re, hvvRe]
          have hqAsFirst : (v.1 + s).re + q.im * Complex.I = q := by
            apply Complex.ext
            · have hqRe' : q.re = x := hqRe.trans huRe
              simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
                Complex.ofReal_im, Complex.I_re, mul_zero, Complex.I_im,
                mul_one, zero_sub, neg_zero, add_zero, hvx] using hqRe'.symm
            · simp
          have hqFirst : q ∈ openSegment ℝ (v.1 + s) (v'.1 + s) := by
            rw [← hqAsFirst,
              vertical_point_mem_openSegment_iff hvvPlaced hvvPlacedRe]
            have hvvPlacedIm : (v.1 + s).im ≠ (v'.1 + s).im := by
              simp only [Complex.add_im]
              exact fun h ↦ hvvIm (add_right_cancel h)
            rw [openSegment_eq_Ioo' hvvPlacedIm]
            simpa only [translatedVerticalInterval, ← min_add_add_right,
              ← max_add_add_right, Complex.add_im] using hqFirstInterval
          have hwwIm : w.1.im ≠ w'.1.im := fun him ↦ hww (Complex.ext hwwRe him)
          have hwwPlaced : w.1 + t ≠ w'.1 + t := fun h ↦ hww (add_right_cancel h)
          have hwwPlacedRe : (w.1 + t).re = (w'.1 + t).re := by
            simp only [Complex.add_re, hwwRe]
          have hqAsSecond : (w.1 + t).re + q.im * Complex.I = q := by
            rw [hwx, ← hvx]
            exact hqAsFirst
          have hqSecond : q ∈ openSegment ℝ (w.1 + t) (w'.1 + t) := by
            rw [← hqAsSecond,
              vertical_point_mem_openSegment_iff hwwPlaced hwwPlacedRe]
            have hwwPlacedIm : (w.1 + t).im ≠ (w'.1 + t).im := by
              simp only [Complex.add_im]
              exact fun h ↦ hwwIm (add_right_cancel h)
            rw [openSegment_eq_Ioo' hwwPlacedIm]
            simpa only [translatedVerticalInterval, ← min_add_add_right,
              ← max_add_add_right, Complex.add_im] using hqSecondInterval
          exact ⟨hqFirst, hqSecond⟩)
    exact ⟨s, hsS, t, htS, u, z, huz, huzRe, huRe, hEdge⟩

private theorem familyBoundaryUnion_transport
    {B : Set ℝ} {f : B → ℝ}
    {families : Set (Set ℝ)} {mapped : Set (Set ℝ)}
    (hB : B = ⋃ X ∈ families, frontier X)
    (hForward : ∀ X ∈ families, ∃ Xphi ∈ mapped,
      frontier Xphi = f '' {x : B | (x : ℝ) ∈ frontier X})
    (hReverse : ∀ Xphi ∈ mapped, ∃ X ∈ families,
      frontier Xphi = f '' {x : B | (x : ℝ) ∈ frontier X}) :
    Set.range f = ⋃ Xphi ∈ mapped, frontier Xphi := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have hxUnion : (x : ℝ) ∈ ⋃ X ∈ families, frontier X := hB ▸ x.2
    rw [Set.mem_iUnion] at hxUnion
    obtain ⟨X, hxUnion⟩ := hxUnion
    rw [Set.mem_iUnion] at hxUnion
    obtain ⟨hX, hxFrontier⟩ := hxUnion
    obtain ⟨Xphi, hXphi, hfront⟩ := hForward X hX
    rw [Set.mem_iUnion]
    refine ⟨Xphi, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨hXphi, hfront.symm ▸ ?_⟩
    exact ⟨x, hxFrontier, rfl⟩
  · intro hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨Xphi, hy⟩ := hy
    rw [Set.mem_iUnion] at hy
    obtain ⟨hXphi, hyFrontier⟩ := hy
    obtain ⟨X, _hX, hfront⟩ := hReverse Xphi hXphi
    rw [hfront] at hyFrontier
    obtain ⟨x, _hx, rfl⟩ := hyFrontier
    exact Set.mem_range_self x

private theorem totalBoundaryMap_strictMono
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    {B : Set ℝ} (hBsub : B ⊆ horizontalTranslatedVertices C.region C.centres)
    (hBmem : ∀ x ∈ B, x ∈ C.coordinateSpace) :
    StrictMono (fun x : B ↦
      Tiling.AxisParallel.Approximation.mapScalar phi
        ⟨x.1, hBmem x.1 x.2⟩) := by
  intro x y hxy
  have hxMem := hBsub x.2
  have hyMem := hBsub y.2
  rw [horizontalTranslatedVertices_eq] at hxMem hyMem
  obtain ⟨v, hv, s, hs, hxEq⟩ := hxMem
  obtain ⟨w, hw, t, ht, hyEq⟩ := hyMem
  let vC : C.region.vertices := ⟨v, hv⟩
  let wC : C.region.vertices := ⟨w, hw⟩
  let sC : C.centres := ⟨s, hs⟩
  let tC : C.centres := ⟨t, ht⟩
  have horder := (lt_iff_of_sign_sub_eq (hHorizontalSign vC wC sC tC)).mp (by
    rw [← hxEq, ← hyEq]
    exact hxy)
  have map_eq (z : ℝ) (hz : z ∈ C.coordinateSpace)
      (a : Tiling.Plane) (ha : a ∈ C.region.vertices)
      (b : Tiling.Plane) (hb : b ∈ C.centres)
      (hza : z = (a + b).re) :
      Tiling.AxisParallel.Approximation.mapScalar phi ⟨z, hz⟩ =
        (Tiling.AxisParallel.Approximation.mapPoint phi (C.vertexPoint a ha) +
          Tiling.AxisParallel.Approximation.mapPoint phi (C.centrePoint b hb)).re := by
    have hsum : a.re + b.re ∈ C.coordinateSpace :=
      C.coordinateSpace.add_mem (C.vertex_re_mem a ha) (C.centre_re_mem b hb)
    have hsubtype : (⟨z, hz⟩ : C.coordinateSpace) =
        ⟨a.re + b.re, hsum⟩ := by
      apply Subtype.ext
      simpa only [Complex.add_re] using hza
    rw [hsubtype]
    simp only [Tiling.AxisParallel.Approximation.mapPoint,
      Tiling.AxisParallel.Approximation.mapScalar, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, Complex.I_im, mul_one,
      sub_zero, add_zero, Tiling.AxisParallel.Approximation.ApproximationContext.vertexPoint,
      Tiling.AxisParallel.Approximation.ApproximationContext.centrePoint]
    norm_cast
    rw [← map_add]
    rfl
  have hxMap := map_eq x.1 (hBmem x.1 x.2) v hv s hs hxEq
  have hyMap := map_eq y.1 (hBmem y.1 y.2) w hw t ht hyEq
  exact hxMap.trans_lt (horder.trans_eq hyMap.symm)

private theorem same_set_membership_of_uIcc_disjoint_frontier
    {S : Set ℝ} {a b : ℝ}
    (hdisj : Disjoint (Set.uIcc a b) (frontier S))
    (ha : a ∈ S) : b ∈ S := by
  have hab : b ∈ Set.uIcc a b := by simp [Set.uIcc]
  rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_uIcc hdisj with hinside | houtside
  · exact interior_subset (hinside hab)
  · have haIcc : a ∈ Set.uIcc a b := by simp [Set.uIcc]
    exact False.elim (interior_subset (houtside haIcc) ha)

private theorem regularOpen_chambers_transport_of_orderedSuperBoundary
    {B : Set ℝ} {f : B → ℝ} (hf : StrictMono f)
    {X : Set ℝ} (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X)
    (hfront : frontier X ⊆ B)
    (H : ℝ ≃ₜ ℝ) (hHmono : StrictMono H)
    (hHf : ∀ x : ↥(frontier X),
      H x.1 = f ⟨x.1, hfront x.2⟩) :
    ∀ x x' : B, x.1 < x'.1 → Set.Ioo x.1 x'.1 ∩ B = ∅ →
      (Set.Ioo x.1 x'.1 ⊆ X ↔
        Set.Ioo (f x) (f x') ⊆ H '' X) := by
  intro x x' hxx' hgap
  have no_frontier_between (z : ℝ) (hz : z ∈ Set.Ioo x.1 x'.1)
      (y : ℝ) (hy : y ∈ Set.Ioo (f x) (f x')) :
      Disjoint (Set.uIcc (H z) y) (frontier (H '' X)) := by
    rw [← H.image_frontier]
    refine Set.disjoint_left.2 ?_
    rintro q hqIcc ⟨r, hrFrontier, hrq⟩
    subst q
    have hrB : r ∈ B := hfront hrFrontier
    let rB : B := ⟨r, hrB⟩
    have hrOutside : r ≤ x.1 ∨ x'.1 ≤ r := by
      by_contra hnot
      push Not at hnot
      have hrGap : r ∈ Set.Ioo x.1 x'.1 ∩ B := ⟨⟨hnot.1, hnot.2⟩, hrB⟩
      rw [hgap] at hrGap
      exact hrGap
    have hHr : H r = f rB := hHf ⟨r, hrFrontier⟩
    rw [Set.uIcc] at hqIcc
    rcases hrOutside with hrLeft | hrRight
    · have hqHz : H r < H z := by
        calc
          H r ≤ H x.1 := hHmono.monotone hrLeft
          _ < H z := hHmono hz.1
      have hqY : H r < y := by
        calc
          H r = f rB := hHr
          _ ≤ f x := hf.monotone hrLeft
          _ < y := hy.1
      exact (not_lt_of_ge hqIcc.1) (lt_min hqHz hqY)
    · have hHzq : H z < H r := by
        calc
          H z < H x'.1 := hHmono hz.2
          _ ≤ H r := hHmono.monotone hrRight
      have hyq : y < H r := by
        calc
          y < f x' := hy.2
          _ ≤ f rB := hf.monotone hrRight
          _ = H r := hHr.symm
      exact (not_lt_of_ge hqIcc.2) (max_lt hHzq hyq)
  constructor
  · intro hsource y hy
    let z := (x.1 + x'.1) / 2
    have hz : z ∈ Set.Ioo x.1 x'.1 := by
      dsimp only [z]
      constructor <;> linarith
    have hHz : H z ∈ H '' X := ⟨z, hsource hz, rfl⟩
    exact same_set_membership_of_uIcc_disjoint_frontier
      (no_frontier_between z hz y hy) hHz
  · intro htarget z hz
    let y := (f x + f x') / 2
    have hfxx' : f x < f x' := hf hxx'
    have hy : y ∈ Set.Ioo (f x) (f x') := by
      dsimp only [y]
      constructor <;> linarith
    have hyTarget : y ∈ H '' X := htarget hy
    have hHzTarget : H z ∈ H '' X :=
      same_set_membership_of_uIcc_disjoint_frontier
        (by simpa only [Set.uIcc_comm] using no_frontier_between z hz y hy)
        hyTarget
    obtain ⟨w, hwX, hwz⟩ := hHzTarget
    exact H.injective hwz |>.symm ▸ hwX


private theorem c03_coordinateSwap_frontier_image (A : Set Tiling.Plane) :
    frontier (Tiling.AxisParallel.coordinateSwap '' A) =
      Tiling.AxisParallel.coordinateSwap '' frontier A := by
  exact Tiling.AxisParallel.coordinateSwap.toHomeomorph.image_frontier A |>.symm

private theorem c03_coordinateSwap_openSegment (a b : Tiling.Plane) :
    Tiling.AxisParallel.coordinateSwap '' openSegment ℝ a b =
      openSegment ℝ (Tiling.AxisParallel.coordinateSwap a)
        (Tiling.AxisParallel.coordinateSwap b) := by
  exact image_openSegment ℝ
    Tiling.AxisParallel.coordinateSwap.toLinearMap.toAffineMap a b

private theorem c03_verticalSubsegment_avoiding_finite
    {a b : Tiling.Plane} (hab : a ≠ b) (hv : a.re = b.re)
    {V : Set Tiling.Plane} (hV : V.Finite) :
    ∃ a' b' : Tiling.Plane, a' ≠ b' ∧ a'.re = b'.re ∧
      openSegment ℝ a' b' ⊆ openSegment ℝ a b \ V := by
  let f : ℝ → Tiling.Plane := AffineMap.lineMap a b
  have hf : Function.Injective f := AffineMap.lineMap_injective ℝ hab
  have hpre : (f ⁻¹' V).Finite := hV.preimage hf.injOn
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ f ⁻¹' V).Nonempty :=
    ((Set.Ioo_infinite (show (0 : ℝ) < 1 by norm_num)).sdiff hpre).nonempty
  obtain ⟨u, huI, huV⟩ := hdiff
  have hopen : Set.Ioo (0 : ℝ) 1 \ f ⁻¹' V ∈ nhds u :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds huI)
      (hpre.isClosed.isOpen_compl.mem_nhds huV)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hopen
  let c := u - ε / 2
  let d := u + ε / 2
  have hcball : c ∈ Metric.ball u ε := by
    simp only [Metric.mem_ball, Real.dist_eq]
    dsimp [c]
    rw [abs_of_nonpos] <;> linarith
  have hdball : d ∈ Metric.ball u ε := by
    simp only [Metric.mem_ball, Real.dist_eq, d]
    rw [add_sub_cancel_left, abs_of_nonneg] <;> linarith
  have hc := hball hcball
  have hd := hball hdball
  have hcd : c < d := by dsimp [c, d]; linarith
  refine ⟨AffineMap.lineMap a b c, AffineMap.lineMap a b d, ?_, ?_, ?_⟩
  · intro heq
    exact (ne_of_lt hcd) (hf heq)
  · simp [AffineMap.lineMap_apply, hv]
  · rw [← image_openSegment ℝ (AffineMap.lineMap a b) c d]
    rintro z ⟨t, ht, rfl⟩
    rw [openSegment_eq_Ioo hcd] at ht
    have htball : t ∈ Metric.ball u ε := by
      rw [Real.ball_eq_Ioo]
      dsimp [c, d] at ht ⊢
      have hhalf : ε / 2 < ε := half_lt_self hε
      exact ⟨(sub_lt_sub_left hhalf u).trans ht.1,
        ht.2.trans (by simpa [add_comm] using add_lt_add_left hhalf u)⟩
    have ht' := hball htball
    exact ⟨lineMap_mem_openSegment (𝕜 := ℝ) a b ht'.1, ht'.2⟩

private theorem c03_verticalSupportBoundary_containsTileEdge
    {K : Region} {T E S : Set Tiling.Plane}
    (hTile : TilesOn K T E) (hST : S ⊆ T)
    {a b : Tiling.Plane} (hab : a ≠ b) (hv : a.re = b.re)
    (hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S)) :
    ∃ s ∈ S, ∃ a' b' : Tiling.Plane,
      a' ≠ b' ∧ a'.re = b'.re ∧
      openSegment ℝ a' b' ⊆ openSegment ℝ a b ∧
      openSegment ℝ a' b' ⊆
        frontier (s +ᵥ K.support) \ (s +ᵥ K.vertices) := by
  let σ := Tiling.AxisParallel.coordinateSwap
  have hSwapTile : TilesOn K.coordinateSwap (σ '' T) (σ '' E) :=
    Tiling.AxisParallel.tilesOn_coordinateSwap hTile
  have hSwapBoundary : openSegment ℝ (σ a) (σ b) ⊆
      frontier (regularSupport K.coordinateSwap (σ '' S)) := by
    change openSegment ℝ (Tiling.AxisParallel.coordinateSwap a)
        (Tiling.AxisParallel.coordinateSwap b) ⊆
      frontier (regularSupport K.coordinateSwap
        (Tiling.AxisParallel.coordinateSwap '' S))
    rw [Tiling.AxisParallel.regularSupport_coordinateSwap,
      c03_coordinateSwap_frontier_image,
      ← c03_coordinateSwap_openSegment]
    exact Set.image_mono hBoundary
  have hSwapNe : σ a ≠ σ b := σ.injective.ne hab
  have hSwapHorizontal : (σ a).im = (σ b).im := by simpa [σ] using hv
  obtain ⟨s', hs', c, d, hcd, _hcdHorizontal, hcdSub, hcdFrontier⟩ :=
    horizontalSupportBoundary_containsTileEdge hSwapTile (Set.image_mono hST)
      hSwapNe hSwapHorizontal hSwapBoundary
  obtain ⟨s, hs, rfl⟩ := hs'
  have hPlaced : σ s +ᵥ K.coordinateSwap.support = σ '' (s +ᵥ K.support) := by
    change σ s +ᵥ (σ '' K.support) = σ '' (s +ᵥ K.support)
    exact Tiling.AxisParallel.coordinateSwap_image_vadd s K.support |>.symm
  have hBackFrontier : openSegment ℝ (σ c) (σ d) ⊆
      frontier (s +ᵥ K.support) := by
    intro z hz
    have hzImage : σ z ∈ openSegment ℝ c d := by
      have hz' : Tiling.AxisParallel.coordinateSwap z ∈
          Tiling.AxisParallel.coordinateSwap ''
            openSegment ℝ (Tiling.AxisParallel.coordinateSwap c)
              (Tiling.AxisParallel.coordinateSwap d) :=
        ⟨z, by simpa [σ] using hz, rfl⟩
      rw [c03_coordinateSwap_openSegment] at hz'
      simpa [σ] using hz'
    have hzFrontier := (hcdFrontier hzImage).1
    rw [hPlaced, c03_coordinateSwap_frontier_image] at hzFrontier
    obtain ⟨w, hw, hwz⟩ := hzFrontier
    have hwEq : w = z := Tiling.AxisParallel.coordinateSwap.injective (by
      simpa [σ] using hwz)
    exact hwEq ▸ hw
  have hBackSub : openSegment ℝ (σ c) (σ d) ⊆ openSegment ℝ a b := by
    intro z hz
    have hzImage : σ z ∈ openSegment ℝ c d := by
      have hz' : Tiling.AxisParallel.coordinateSwap z ∈
          Tiling.AxisParallel.coordinateSwap ''
            openSegment ℝ (Tiling.AxisParallel.coordinateSwap c)
              (Tiling.AxisParallel.coordinateSwap d) :=
        ⟨z, by simpa [σ] using hz, rfl⟩
      rw [c03_coordinateSwap_openSegment] at hz'
      simpa [σ] using hz'
    have hzOuter := hcdSub hzImage
    rw [← c03_coordinateSwap_openSegment] at hzOuter
    obtain ⟨w, hw, hwz⟩ := hzOuter
    have hwEq : w = z := Tiling.AxisParallel.coordinateSwap.injective (by
      simpa [σ] using hwz)
    exact hwEq ▸ hw
  have hBackNe : σ c ≠ σ d := σ.injective.ne hcd
  have hBackVertical : (σ c).re = (σ d).re := by
    simpa [σ] using _hcdHorizontal
  have hvertices : (s +ᵥ K.vertices).Finite := by
    simpa only [Region.vertices, singleton_vadd] using
      (Set.finite_singleton s).vadd K.isPolygonal.vertexSet_finite
  obtain ⟨a', b', hab', hv', hav⟩ :=
    c03_verticalSubsegment_avoiding_finite hBackNe hBackVertical hvertices
  refine ⟨s, hs, a', b', hab', hv', ?_, ?_⟩
  · exact fun z hz ↦ hBackSub (hav hz).1
  · exact fun z hz ↦ ⟨hBackFrontier (hav hz).1, (hav hz).2⟩

private theorem twoSidedStrip_forcesVerticalIncidence
    {K : Region} {T Sₗ Sᵣ : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hSₗ : Sₗ ⊆ T) (hSᵣ : Sᵣ ⊆ T)
    {Xₗ Xᵣ : Set ℝ}
    (hSupportₗ : regularSupport K Sₗ = Complex.re ⁻¹' Xₗ)
    (hSupportᵣ : regularSupport K Sᵣ = Complex.re ⁻¹' Xᵣ)
    {x delta : ℝ} (_hdelta : 0 < delta)
    (hxₗ : x ∈ frontier Xₗ) (hxᵣ : x ∈ frontier Xᵣ)
    (_hLeft : Complex.re ⁻¹' Set.Ioo (x - delta) x ⊆ regularSupport K Sₗ)
    (_hRight : Complex.re ⁻¹' Set.Ioo x (x + delta) ⊆ regularSupport K Sᵣ) :
    ∃ s ∈ Sₗ, ∃ t ∈ Sᵣ, ∃ a b : Tiling.Plane,
      a ≠ b ∧ a.re = b.re ∧ a.re = x ∧
      openSegment ℝ a b ⊆
        (frontier (s +ᵥ K.support) ∩ frontier (t +ᵥ K.support)) \
          ((s +ᵥ K.vertices) ∪ (t +ᵥ K.vertices)) := by
  let a : Tiling.Plane := x - Complex.I
  let b : Tiling.Plane := x + Complex.I
  have hab : a ≠ b := by
    intro h
    have := congrArg Complex.im h
    norm_num [a, b] at this
  have hv : a.re = b.re := by simp [a, b]
  have hBoundaryₗ : openSegment ℝ a b ⊆ frontier (regularSupport K Sₗ) := by
    rw [hSupportₗ]
    change openSegment ℝ a b ⊆ frontier ({z : Tiling.Plane | z.re ∈ Xₗ})
    rw [Tiling.AxisParallel.frontier_verticalCylinder]
    intro z hz
    change z.re ∈ frontier Xₗ
    have hzSeg := openSegment_subset_segment ℝ a b hz
    rw [segment_eq_image] at hzSeg
    obtain ⟨q, hq, rfl⟩ := hzSeg
    convert hxₗ using 1
    simp [a, b]
    ring
  obtain ⟨s, hs, c, d, hcd, hcdv, hcdSub, hcdBoundaryₗ⟩ :=
    c03_verticalSupportBoundary_containsTileEdge hTile hSₗ hab hv hBoundaryₗ
  have hBoundaryᵣ : openSegment ℝ c d ⊆ frontier (regularSupport K Sᵣ) := by
    rw [hSupportᵣ]
    change openSegment ℝ c d ⊆ frontier ({z : Tiling.Plane | z.re ∈ Xᵣ})
    rw [Tiling.AxisParallel.frontier_verticalCylinder]
    intro z hz
    change z.re ∈ frontier Xᵣ
    have hzSeg := openSegment_subset_segment ℝ a b (hcdSub hz)
    rw [segment_eq_image] at hzSeg
    obtain ⟨q, hq, rfl⟩ := hzSeg
    convert hxᵣ using 1
    simp [a, b]
    ring
  obtain ⟨t, ht, e, f, hef, hefv, hefSub, hefBoundaryᵣ⟩ :=
    c03_verticalSupportBoundary_containsTileEdge hTile hSᵣ hcd hcdv hBoundaryᵣ
  refine ⟨s, hs, t, ht, e, f, hef, hefv, ?_, ?_⟩
  · have hmidSub := hcdSub (hefSub (midpoint_mem_openSegment (𝕜 := ℝ) e f))
    have hmidSeg := openSegment_subset_segment ℝ a b hmidSub
    have hmidRe : (midpoint ℝ e f).re = x := by
      rw [segment_eq_image] at hmidSeg
      obtain ⟨q, hq, heq⟩ := hmidSeg
      rw [← heq]
      simp [a, b]
      ring
    rw [midpoint, AffineMap.lineMap_apply] at hmidRe
    norm_num at hmidRe
    linarith [hefv]
  · intro z hz
    have hzᵣ := hefBoundaryᵣ hz
    have hzₗ := hcdBoundaryₗ (hefSub hz)
    exact ⟨⟨hzₗ.1, hzᵣ.1⟩, fun hzV ↦ hzV.elim hzₗ.2 hzᵣ.2⟩

private theorem slabBoundary_mem_horizontalTranslatedVertices
    {K : Region} {T S : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ) (hS : S ⊆ T)
    {X : Set ℝ} (_hXopen : IsOpen X)
    (_hXregular : interior (closure X) = X)
    (hSupport : regularSupport K S = Complex.re ⁻¹' X) :
    frontier X ⊆ horizontalTranslatedVertices K T := by
  intro x hx
  let a : Tiling.Plane := x - Complex.I
  let b : Tiling.Plane := x + Complex.I
  have hab : a ≠ b := by
    intro h
    have := congrArg Complex.im h
    norm_num [a, b] at this
  have hv : a.re = b.re := by simp [a, b]
  have hBoundary : openSegment ℝ a b ⊆ frontier (regularSupport K S) := by
    rw [hSupport]
    change openSegment ℝ a b ⊆ frontier ({z : Tiling.Plane | z.re ∈ X})
    rw [Tiling.AxisParallel.frontier_verticalCylinder]
    intro z hz
    change z.re ∈ frontier X
    have hzSeg := openSegment_subset_segment ℝ a b hz
    rw [segment_eq_image] at hzSeg
    obtain ⟨q, hq, rfl⟩ := hzSeg
    convert hx using 1
    simp [a, b]
    ring
  obtain ⟨s, hs, c, d, hcd, hcdRe, hcdSub, hcdBoundary⟩ :=
    c03_verticalSupportBoundary_containsTileEdge hTile hS hab hv hBoundary
  let p : Tiling.Plane := midpoint ℝ c d
  have hpCD : p ∈ openSegment ℝ c d := midpoint_mem_openSegment c d
  have hpPlaced := hcdBoundary hpCD
  have hpFrontier : p - s ∈ frontier K.support :=
    by
      simpa only [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
        vadd_eq_add, neg_add_eq_sub] using hpPlaced.1
  have hpNotVertex : p - s ∉ K.vertices := by
    intro hpV
    apply hpPlaced.2
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hpV
  obtain ⟨axis, v, w, hvw, hvwCoord, hpVW, hvwEdge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge
      K (p - s) hpFrontier hpNotVertex
  have hcdSubFrontier : openSegment ℝ (c - s) (d - s) ⊆ frontier K.support := by
    intro z hz
    simpa [frontier_vadd_eq, Set.mem_vadd_set_iff_neg_vadd_mem,
      vadd_eq_add, neg_add_eq_sub] using
      (hcdBoundary (mem_openSegment_sub_iff.mp hz)).1
  have hpCDSub : p - s ∈ openSegment ℝ (c - s) (d - s) :=
    mem_openSegment_sub_iff.mpr (by simpa using hpCD)
  have hcdSubNe : c - s ≠ d - s := by
    intro h
    apply hcd
    have h' := congrArg (fun z : Tiling.Plane ↦ z + s) h
    simpa [sub_eq_add_neg, add_assoc] using h'
  have hcdSubRe : (c - s).re = (d - s).re := by
    simp only [Complex.sub_re, hcdRe]
  have hvwRe : v.1.re = w.1.re := by
    cases axis with
    | vertical => exact hvwCoord
    | horizontal =>
        exfalso
        apply hpNotVertex
        exact K.isPolygonal.mem_vertexSet_of_perpendicular_openSegments
          hvw hvwCoord (fun z hz ↦ (hvwEdge hz).1) hpVW
          hcdSubNe hcdSubRe hpCDSub hcdSubFrontier
  have hpRe : p.re = x := by
    have hpOuter := hcdSub hpCD
    have hpSeg := openSegment_subset_segment ℝ a b hpOuter
    rw [segment_eq_image] at hpSeg
    obtain ⟨q, hq, hpq⟩ := hpSeg
    rw [← hpq]
    simp [a, b]
    ring
  rw [horizontalTranslatedVertices_eq]
  refine ⟨v.1, v.2, s, hS hs, ?_⟩
  have hpMinusRe : (p - s).re = v.1.re :=
    re_eq_of_mem_openSegment_vertical hvwRe hpVW
  rw [Complex.sub_re] at hpMinusRe
  simp only [Complex.add_re]
  linarith

private theorem c03_verticalCylinderBase_isOpen_of_regularSupport
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (hSupport : regularSupport K S = Complex.re ⁻¹' X) : IsOpen X := by
  have hopen : IsOpen (Complex.re ⁻¹' X) := by
    rw [← hSupport]
    exact (Tiling.AxisParallel.regularSupport_isRegularOpen K S).1
  have hsection : Continuous (fun x : ℝ ↦ (x : ℂ)) := by fun_prop
  have hopen' := hopen.preimage hsection
  convert hopen' using 1
  ext x
  simp

private theorem c03_verticalCylinderBase_isRegularOpen_of_regularSupport
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (hSupport : regularSupport K S = Complex.re ⁻¹' X) :
    interior (closure X) = X := by
  have hregular := (Tiling.AxisParallel.regularSupport_isRegularOpen K S).2
  rw [hSupport] at hregular
  change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X at hregular
  rw [Complex.closure_preimage_re, Complex.interior_preimage_re] at hregular
  ext x
  have hx := Set.ext_iff.mp hregular (x : ℂ)
  simpa using hx

private theorem oneSidedStrip_transport
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres) {X Xphi : Set ℝ}
    (hSupport : regularSupport C.region S = Complex.re ⁻¹' X)
    (_hSupportPhi : regularSupport D.deformedRegion
      (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
        {t : C.centres | (t : Tiling.Plane) ∈ S}) = Complex.re ⁻¹' Xphi)
    {x : ℝ} (hx : x ∈ frontier X) (hxMem : x ∈ C.coordinateSpace)
    {delta : ℝ} (hdelta : 0 < delta) :
    (Complex.re ⁻¹' Set.Ioo (x - delta) x ⊆ regularSupport C.region S →
      ∃ deltaPhi : ℝ, 0 < deltaPhi ∧
        Complex.re ⁻¹' Set.Ioo
            (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ - deltaPhi)
            (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩) ⊆
          regularSupport D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
              {t : C.centres | (t : Tiling.Plane) ∈ S})) ∧
    (Complex.re ⁻¹' Set.Ioo x (x + delta) ⊆ regularSupport C.region S →
      ∃ deltaPhi : ℝ, 0 < deltaPhi ∧
        Complex.re ⁻¹' Set.Ioo
            (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩)
            (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ + deltaPhi) ⊆
          regularSupport D.deformedRegion
            (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
              {t : C.centres | (t : Tiling.Plane) ∈ S})) := by
  have hXopen := c03_verticalCylinderBase_isOpen_of_regularSupport hSupport
  have hXregular := c03_verticalCylinderBase_isRegularOpen_of_regularSupport hSupport
  obtain ⟨boundaryLift, H, hlift, hHmono, hHboundary, hTargetSupport⟩ :=
    Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph
      P S hS X hXopen hXregular hSupport
  let xFrontier : ↑(frontier X) := ⟨x, hx⟩
  have hliftCanonical : boundaryLift xFrontier = ⟨x, hxMem⟩ := by
    apply Subtype.ext
    exact hlift xFrontier
  have hHx : H x = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ := by
    rw [← hliftCanonical]
    exact hHboundary xFrontier
  constructor
  · intro hLeft
    have hBase : Set.Ioo (x - delta) x ⊆ X := by
      intro y hy
      have hy' := hLeft (show (y : ℂ) ∈ Complex.re ⁻¹' Set.Ioo (x - delta) x by
        simpa using hy)
      rw [hSupport] at hy'
      simpa using hy'
    let deltaPhi := H x - H (x - delta)
    have hdeltaPhi : 0 < deltaPhi := sub_pos.mpr (hHmono (sub_lt_self x hdelta))
    refine ⟨deltaPhi, hdeltaPhi, ?_⟩
    rw [hTargetSupport]
    intro z hz
    change z.re ∈ H '' X
    have hzInterval : z.re ∈ Set.Ioo (H (x - delta)) (H x) := by
      simpa [deltaPhi, hHx] using hz
    let y := H.symm z.re
    have hyInterval : y ∈ Set.Ioo (x - delta) x := by
      constructor
      · apply hHmono.lt_iff_lt.mp
        simpa [y] using hzInterval.1
      · apply hHmono.lt_iff_lt.mp
        simpa [y] using hzInterval.2
    exact ⟨y, hBase hyInterval, by simp [y]⟩
  · intro hRight
    have hBase : Set.Ioo x (x + delta) ⊆ X := by
      intro y hy
      have hy' := hRight (show (y : ℂ) ∈ Complex.re ⁻¹' Set.Ioo x (x + delta) by
        simpa using hy)
      rw [hSupport] at hy'
      simpa using hy'
    let deltaPhi := H (x + delta) - H x
    have hdeltaPhi : 0 < deltaPhi := sub_pos.mpr (hHmono (lt_add_of_pos_right x hdelta))
    refine ⟨deltaPhi, hdeltaPhi, ?_⟩
    rw [hTargetSupport]
    intro z hz
    change z.re ∈ H '' X
    have hzInterval : z.re ∈ Set.Ioo (H x) (H (x + delta)) := by
      simpa [deltaPhi, hHx] using hz
    let y := H.symm z.re
    have hyInterval : y ∈ Set.Ioo x (x + delta) := by
      constructor
      · apply hHmono.lt_iff_lt.mp
        simpa [y] using hzInterval.1
      · apply hHmono.lt_iff_lt.mp
        simpa [y] using hzInterval.2
    exact ⟨y, hBase hyInterval, by simp [y]⟩

theorem deformation_preservesTwoSidedVerticalIncidence
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (_hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    {Sₗ Sᵣ : Set Tiling.Plane} (hSₗ : Sₗ ⊆ C.centres) (hSᵣ : Sᵣ ⊆ C.centres)
    {Xₗ Xᵣ : Set ℝ}
    (hSupportₗ : regularSupport C.region Sₗ = Complex.re ⁻¹' Xₗ)
    (hSupportᵣ : regularSupport C.region Sᵣ = Complex.re ⁻¹' Xᵣ)
    {x : ℝ} (hxₗ : x ∈ frontier Xₗ) (hxᵣ : x ∈ frontier Xᵣ)
    (hxMem : x ∈ C.coordinateSpace) {delta : ℝ} (hdelta : 0 < delta)
    (hLeft : Complex.re ⁻¹' Set.Ioo (x - delta) x ⊆ regularSupport C.region Sₗ)
    (hRight : Complex.re ⁻¹' Set.Ioo x (x + delta) ⊆ regularSupport C.region Sᵣ) :
    (∃ s : C.centres, (s : Tiling.Plane) ∈ Sₗ ∧
      ∃ t : C.centres, (t : Tiling.Plane) ∈ Sᵣ ∧
      ∃ a b : Tiling.Plane, a ≠ b ∧ a.re = b.re ∧ a.re = x ∧
        openSegment ℝ a b ⊆
          (frontier ((s : Tiling.Plane) +ᵥ C.region.support) ∩
              frontier ((t : Tiling.Plane) +ᵥ C.region.support)) \
            (((s : Tiling.Plane) +ᵥ C.region.vertices) ∪
              ((t : Tiling.Plane) +ᵥ C.region.vertices))) ↔
    (∃ s : C.centres, (s : Tiling.Plane) ∈ Sₗ ∧
      ∃ t : C.centres, (t : Tiling.Plane) ∈ Sᵣ ∧
      ∃ a b : Tiling.Plane, a ≠ b ∧ a.re = b.re ∧
        a.re = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ ∧
        openSegment ℝ a b ⊆
          (frontier (P.fullCenters s +ᵥ D.deformedRegion.support) ∩
              frontier (P.fullCenters t +ᵥ D.deformedRegion.support)) \
            ((P.fullCenters s +ᵥ D.deformedRegion.vertices) ∪
              (P.fullCenters t +ᵥ D.deformedRegion.vertices))) := by
  have hSourcePlane := twoSidedStrip_forcesVerticalIncidence
    P.source_tilesOn hSₗ hSᵣ hSupportₗ hSupportᵣ hdelta hxₗ hxᵣ hLeft hRight
  obtain ⟨s₀, hs₀, t₀, ht₀, a₀, b₀, hab₀, hre₀, hx₀, hedge₀⟩ := hSourcePlane
  let s : C.centres := ⟨s₀, hSₗ hs₀⟩
  let t : C.centres := ⟨t₀, hSᵣ ht₀⟩
  have hSource : ∃ s : C.centres, (s : Tiling.Plane) ∈ Sₗ ∧
      ∃ t : C.centres, (t : Tiling.Plane) ∈ Sᵣ ∧
      ∃ a b : Tiling.Plane, a ≠ b ∧ a.re = b.re ∧ a.re = x ∧
        openSegment ℝ a b ⊆
          (frontier ((s : Tiling.Plane) +ᵥ C.region.support) ∩
              frontier ((t : Tiling.Plane) +ᵥ C.region.support)) \
            (((s : Tiling.Plane) +ᵥ C.region.vertices) ∪
              ((t : Tiling.Plane) +ᵥ C.region.vertices)) := by
    exact ⟨s, hs₀, t, ht₀, a₀, b₀, hab₀, hre₀, hx₀, hedge₀⟩
  have hXₗopen := c03_verticalCylinderBase_isOpen_of_regularSupport hSupportₗ
  have hXₗregular := c03_verticalCylinderBase_isRegularOpen_of_regularSupport hSupportₗ
  obtain ⟨liftₗ, Hₗ, hliftₗ, hHₗmono, hHₗboundary, hTargetSupportₗ⟩ :=
    Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph
      P Sₗ hSₗ Xₗ hXₗopen hXₗregular hSupportₗ
  have hXᵣopen := c03_verticalCylinderBase_isOpen_of_regularSupport hSupportᵣ
  have hXᵣregular := c03_verticalCylinderBase_isRegularOpen_of_regularSupport hSupportᵣ
  obtain ⟨liftᵣ, Hᵣ, hliftᵣ, hHᵣmono, hHᵣboundary, hTargetSupportᵣ⟩ :=
    Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph
      P Sᵣ hSᵣ Xᵣ hXᵣopen hXᵣregular hSupportᵣ
  let xₗFrontier : ↑(frontier Xₗ) := ⟨x, hxₗ⟩
  let xᵣFrontier : ↑(frontier Xᵣ) := ⟨x, hxᵣ⟩
  have hliftₗCanonical : liftₗ xₗFrontier = ⟨x, hxMem⟩ := by
    apply Subtype.ext
    exact hliftₗ xₗFrontier
  have hliftᵣCanonical : liftᵣ xᵣFrontier = ⟨x, hxMem⟩ := by
    apply Subtype.ext
    exact hliftᵣ xᵣFrontier
  have hHₗx : Hₗ x = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ := by
    rw [← hliftₗCanonical]
    exact hHₗboundary xₗFrontier
  have hHᵣx : Hᵣ x = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ := by
    rw [← hliftᵣCanonical]
    exact hHᵣboundary xᵣFrontier
  obtain ⟨deltaₗ, hdeltaₗ, hLeftPhi⟩ :=
    (oneSidedStrip_transport C phi D P hSₗ hSupportₗ hTargetSupportₗ
      hxₗ hxMem hdelta).1 hLeft
  obtain ⟨deltaᵣ, hdeltaᵣ, hRightPhi⟩ :=
    (oneSidedStrip_transport C phi D P hSᵣ hSupportᵣ hTargetSupportᵣ
      hxᵣ hxMem hdelta).2 hRight
  let deltaPhi := min deltaₗ deltaᵣ
  have hdeltaPhi : 0 < deltaPhi := lt_min hdeltaₗ hdeltaᵣ
  have hLeftPhi' : Complex.re ⁻¹' Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ - deltaPhi)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩) ⊆
      regularSupport D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t : Tiling.Plane) ∈ Sₗ}) := by
    intro z hz
    apply hLeftPhi
    change z.re ∈ Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ - deltaₗ)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩)
    change z.re ∈ Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ - min deltaₗ deltaᵣ)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩) at hz
    have hzLeft := hz.1
    have hmin := min_le_left deltaₗ deltaᵣ
    exact ⟨by linarith, hz.2⟩
  have hRightPhi' : Complex.re ⁻¹' Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ + deltaPhi) ⊆
      regularSupport D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t : Tiling.Plane) ∈ Sᵣ}) := by
    intro z hz
    apply hRightPhi
    change z.re ∈ Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ + deltaᵣ)
    change z.re ∈ Set.Ioo
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩)
      (Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ + min deltaₗ deltaᵣ) at hz
    have hzRight := hz.2
    have hmin := min_le_right deltaₗ deltaᵣ
    exact ⟨hz.1, by linarith⟩
  have hxₗPhi : Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ ∈
      frontier (Hₗ '' Xₗ) := by
    rw [← hHₗx, ← Hₗ.image_frontier]
    exact ⟨x, hxₗ, rfl⟩
  have hxᵣPhi : Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ ∈
      frontier (Hᵣ '' Xᵣ) := by
    rw [← hHᵣx, ← Hᵣ.image_frontier]
    exact ⟨x, hxᵣ, rfl⟩
  let SₗPhi := Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
    {t : C.centres | (t : Tiling.Plane) ∈ Sₗ}
  let SᵣPhi := Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
    {t : C.centres | (t : Tiling.Plane) ∈ Sᵣ}
  have hSₗPhi : SₗPhi ⊆ Set.range P.fullCenters := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩
  have hSᵣPhi : SᵣPhi ⊆ Set.range P.fullCenters := by
    rintro z ⟨u, hu, rfl⟩
    exact ⟨u, rfl⟩
  have hTargetPlane := twoSidedStrip_forcesVerticalIncidence
    P.full_tilesOn hSₗPhi hSᵣPhi hTargetSupportₗ hTargetSupportᵣ hdeltaPhi
      hxₗPhi hxᵣPhi hLeftPhi' hRightPhi'
  obtain ⟨sPhi, hsPhi, tPhi, htPhi, aPhi, bPhi, habPhi, hrePhi,
    hxPhi, hedgePhi⟩ := hTargetPlane
  obtain ⟨sTarget, hsTarget, hsEq⟩ := hsPhi
  obtain ⟨tTarget, htTarget, htEq⟩ := htPhi
  have hTarget : ∃ s : C.centres, (s : Tiling.Plane) ∈ Sₗ ∧
      ∃ t : C.centres, (t : Tiling.Plane) ∈ Sᵣ ∧
      ∃ a b : Tiling.Plane, a ≠ b ∧ a.re = b.re ∧
        a.re = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hxMem⟩ ∧
        openSegment ℝ a b ⊆
          (frontier (P.fullCenters s +ᵥ D.deformedRegion.support) ∩
              frontier (P.fullCenters t +ᵥ D.deformedRegion.support)) \
            ((P.fullCenters s +ᵥ D.deformedRegion.vertices) ∪
              (P.fullCenters t +ᵥ D.deformedRegion.vertices)) := by
    subst sPhi
    subst tPhi
    exact ⟨sTarget, hsTarget, tTarget, htTarget, aPhi, bPhi,
      habPhi, hrePhi, hxPhi, hedgePhi⟩
  exact ⟨fun _ ↦ hTarget, fun _ ↦ hSource⟩

private theorem c03_verticalCylinder_subset_iff {A B : Set ℝ} :
    Complex.re ⁻¹' A ⊆ Complex.re ⁻¹' B ↔ A ⊆ B := by
  constructor
  · intro h x hx
    have hx' := h (show (x : ℂ) ∈ Complex.re ⁻¹' A by simpa using hx)
    simpa using hx'
  · exact Set.preimage_mono

theorem deformation_transportsOrderedBoundaryCode
    (C : Tiling.AxisParallel.Approximation.ApproximationContext)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : Tiling.AxisParallel.Approximation.CoordinateDeformation C phi)
    (P : Tiling.AxisParallel.Approximation.TwoStageDeformationSupportTransport C phi D)
    (hHorizontalSign :
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
                (C.centrePoint s.1 s.2)).re))
    (families : Set (Set Tiling.Plane))
    (hFamiliesSub : ∀ S ∈ families, S ⊆ C.centres)
    (hFamiliesSlab : ∀ S ∈ families, ∃ X : Set ℝ,
      X = interior (closure X) ∧ regularSupport C.region S = Complex.re ⁻¹' X)
    (B : Set ℝ) (hBmem : ∀ x ∈ B, x ∈ C.coordinateSpace)
    (hB : B = ⋃ S ∈ families,
      frontier {x : ℝ | (x : ℂ) ∈ regularSupport C.region S}) :
    {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ B,
      y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBmem x hx⟩} =
      (⋃ S ∈ families, frontier {x : ℝ | (x : ℂ) ∈
        regularSupport D.deformedRegion
          (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
            {t : C.centres | (t : Tiling.Plane) ∈ S})}) ∧
    ∀ S ∈ families, ∀ x x' : B, (x : ℝ) < (x' : ℝ) →
      Set.Ioo (x : ℝ) (x' : ℝ) ∩ B = ∅ →
      (Complex.re ⁻¹' Set.Ioo (x : ℝ) (x' : ℝ) ⊆ regularSupport C.region S ↔
        Complex.re ⁻¹' Set.Ioo
          (Tiling.AxisParallel.Approximation.mapScalar phi ⟨(x : ℝ), hBmem x x.2⟩)
          (Tiling.AxisParallel.Approximation.mapScalar phi ⟨(x' : ℝ), hBmem x' x'.2⟩) ⊆
            regularSupport D.deformedRegion
              (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
                {t : C.centres | (t : Tiling.Plane) ∈ S})) := by
  let sourceBase (S : Set Tiling.Plane) : Set ℝ :=
    {x : ℝ | (x : ℂ) ∈ regularSupport C.region S}
  let targetBase (S : Set Tiling.Plane) : Set ℝ :=
    {x : ℝ | (x : ℂ) ∈
      regularSupport D.deformedRegion
        (Tiling.AxisParallel.Approximation.deformedCenterCarrierOn P.fullCenters
          {t : C.centres | (t : Tiling.Plane) ∈ S})}
  have hB' : B = ⋃ S ∈ families, frontier (sourceBase S) := by
    simpa only [sourceBase] using hB
  have sourceData (S : Set Tiling.Plane) (hSf : S ∈ families) :
      ∃ X : Set ℝ, IsOpen X ∧ interior (closure X) = X ∧
        regularSupport C.region S = Complex.re ⁻¹' X ∧ sourceBase S = X := by
    obtain ⟨X, hXregular, hSupport⟩ := hFamiliesSlab S hSf
    have hXregular' : interior (closure X) = X := hXregular.symm
    have hXopen := c03_verticalCylinderBase_isOpen_of_regularSupport hSupport
    refine ⟨X, hXopen, hXregular', hSupport, ?_⟩
    ext x
    simp only [sourceBase, Set.mem_ofPred_eq]
    rw [hSupport]
    simp
  have hBsub : B ⊆ horizontalTranslatedVertices C.region C.centres := by
    intro x hx
    rw [hB'] at hx
    obtain ⟨S, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hSf, hxFrontier⟩ := Set.mem_iUnion.1 hx
    obtain ⟨X, hXopen, hXregular, hSupport, hSourceBase⟩ := sourceData S hSf
    have hxX : x ∈ frontier X := by simpa [hSourceBase] using hxFrontier
    exact slabBoundary_mem_horizontalTranslatedVertices P.source_tilesOn
      (hFamiliesSub S hSf) hXopen hXregular hSupport hxX
  let f : B → ℝ := fun x ↦
    Tiling.AxisParallel.Approximation.mapScalar phi ⟨x.1, hBmem x.1 x.2⟩
  have hf : StrictMono f :=
    totalBoundaryMap_strictMono C phi hHorizontalSign hBsub hBmem
  have boundaryTransport (S : Set Tiling.Plane) (hSf : S ∈ families) :
      frontier (targetBase S) =
        f '' {x : B | (x : ℝ) ∈ frontier (sourceBase S)} := by
    obtain ⟨X, hXopen, hXregular, hSupport, hSourceBase⟩ := sourceData S hSf
    obtain ⟨boundaryLift, H, hlift, hHmono, hHboundary, hTargetSupport⟩ :=
      Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph
        P S (hFamiliesSub S hSf) X hXopen hXregular hSupport
    have hTargetBase : targetBase S = H '' X := by
      ext y
      simp only [targetBase, Set.mem_ofPred_eq]
      rw [hTargetSupport]
      simp
    rw [hTargetBase, ← H.image_frontier, hSourceBase]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzB : z ∈ B := by
        rw [hB']
        exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hSf, by simpa [hSourceBase] using hz⟩⟩
      let zB : B := ⟨z, hzB⟩
      refine ⟨zB, by simpa [zB, hSourceBase] using hz, ?_⟩
      have hliftCanonical : boundaryLift ⟨z, hz⟩ =
          ⟨z, hBmem z hzB⟩ := by
        apply Subtype.ext
        exact hlift ⟨z, hz⟩
      calc
        f zB = Tiling.AxisParallel.Approximation.mapScalar phi ⟨z, hBmem z hzB⟩ := rfl
        _ = Tiling.AxisParallel.Approximation.mapScalar phi (boundaryLift ⟨z, hz⟩) :=
          congrArg (Tiling.AxisParallel.Approximation.mapScalar phi) hliftCanonical.symm
        _ = H z := (hHboundary ⟨z, hz⟩).symm
    · rintro ⟨zB, hzFrontier, rfl⟩
      have hz : (zB : ℝ) ∈ frontier X := by
        simpa [hSourceBase] using hzFrontier
      refine ⟨(zB : ℝ), hz, ?_⟩
      have hliftCanonical : boundaryLift ⟨(zB : ℝ), hz⟩ =
          ⟨(zB : ℝ), hBmem zB zB.2⟩ := by
        apply Subtype.ext
        exact hlift ⟨(zB : ℝ), hz⟩
      calc
        H (zB : ℝ) = Tiling.AxisParallel.Approximation.mapScalar phi
            (boundaryLift ⟨(zB : ℝ), hz⟩) := hHboundary ⟨(zB : ℝ), hz⟩
        _ = f zB := congrArg (Tiling.AxisParallel.Approximation.mapScalar phi)
          hliftCanonical
  have hLeftRange : {y : ℝ | ∃ x : ℝ, ∃ hx : x ∈ B,
      y = Tiling.AxisParallel.Approximation.mapScalar phi ⟨x, hBmem x hx⟩} =
      Set.range f := by
    ext y
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨x, hx⟩, hy.symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
  constructor
  · rw [hLeftRange]
    change Set.range f = ⋃ S ∈ families, frontier (targetBase S)
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hxUnion : (x : ℝ) ∈ ⋃ S ∈ families, frontier (sourceBase S) := hB' ▸ x.2
      obtain ⟨S, hxUnion⟩ := Set.mem_iUnion.1 hxUnion
      obtain ⟨hSf, hxFrontier⟩ := Set.mem_iUnion.1 hxUnion
      rw [Set.mem_iUnion]
      refine ⟨S, Set.mem_iUnion.2 ⟨hSf, ?_⟩⟩
      rw [boundaryTransport S hSf]
      exact ⟨x, hxFrontier, rfl⟩
    · intro hy
      obtain ⟨S, hy⟩ := Set.mem_iUnion.1 hy
      obtain ⟨hSf, hyFrontier⟩ := Set.mem_iUnion.1 hy
      rw [boundaryTransport S hSf] at hyFrontier
      obtain ⟨x, hx, rfl⟩ := hyFrontier
      exact Set.mem_range_self x
  · intro S hSf x x' hxx' hgap
    obtain ⟨X, hXopen, hXregular, hSupport, hSourceBase⟩ := sourceData S hSf
    obtain ⟨boundaryLift, H, hlift, hHmono, hHboundary, hTargetSupport⟩ :=
      Tiling.AxisParallel.Approximation.coordinateDeformation_subfamilySupport_homeomorph
        P S (hFamiliesSub S hSf) X hXopen hXregular hSupport
    have hfront : frontier X ⊆ B := by
      intro z hz
      rw [hB']
      exact Set.mem_iUnion.2 ⟨S, Set.mem_iUnion.2 ⟨hSf, by simpa [hSourceBase] using hz⟩⟩
    have hHf : ∀ z : ↑(frontier X), H z.1 = f ⟨z.1, hfront z.2⟩ := by
      intro z
      have hliftCanonical : boundaryLift z = ⟨z.1, hBmem z.1 (hfront z.2)⟩ := by
        apply Subtype.ext
        exact hlift z
      rw [hHboundary z, hliftCanonical]
    have hchambers := regularOpen_chambers_transport_of_orderedSuperBoundary
      hf hXopen hXregular hfront H hHmono hHf x x' hxx' hgap
    rw [hSupport, hTargetSupport, c03_verticalCylinder_subset_iff,
      c03_verticalCylinder_subset_iff]
    simpa only [f] using hchambers

end Tiling.AxisParallel.Continuous
