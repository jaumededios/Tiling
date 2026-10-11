import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Filter.Basic
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.OneDimensional.ColumnSlices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.PeriodConsequences

set_option linter.style.header false

open Filter Function MeasureTheory Set
open scoped ENNReal Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

/-- A region is a product when its regular-open carrier is the product of its regularized
coordinate projections.  This is the native formulation used by the rigidity arguments. -/
def IsProductRegion (K : Tiling.AxisParallel.Region) : Prop :=
  K.openCarrier =
    {z : Tiling.Plane |
      z.re ∈ interior (closure (Complex.re '' K.openCarrier)) ∧
      z.im ∈ interior (closure (Complex.im '' K.openCarrier))}

theorem isProductRegion_iff_regularizedProjections
    (K : Tiling.AxisParallel.Region) :
    IsProductRegion K ↔
      K.openCarrier =
        {z : Tiling.Plane |
          z.re ∈ interior (closure (Complex.re '' K.openCarrier)) ∧
          z.im ∈ interior (closure (Complex.im '' K.openCarrier))} :=
  Iff.rfl


universe u

open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.OneDimensional

private def horizontalFactor (K : Region) : Set ℝ :=
  interior (closure (Complex.re '' K.openCarrier))

private def verticalFactor (K : Region) : Set ℝ :=
  interior (closure (Complex.im '' K.openCarrier))

private def factorProduct (K : Region) : Set Tiling.Plane :=
  {z | z.re ∈ horizontalFactor K ∧ z.im ∈ verticalFactor K}

private def axisCentreFibre (T : Set Tiling.Plane) (a : ℝ) : Set Tiling.Plane :=
  {z | z ∈ T ∧ z.re = a}

private def columnAxisSet (K : Region) (T : Set Tiling.Plane) : Set ℝ :=
  {a | ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}}

private def horizontalActiveAxes
    (K : Region) (T : Set Tiling.Plane) (y : ℝ) : Set ℝ :=
  {a | ∃ t ∈ T, t.re = a ∧ y - t.im ∈ verticalFactor K}

private def coordinateSwapLIE_local : Tiling.Plane ≃ₗᵢ[ℝ] Tiling.Plane where
  toLinearEquiv := coordinateSwap.toLinearEquiv
  norm_map' z := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp [Complex.normSq_apply]
    ring

private theorem exists_mem_open_of_ae {U : Set Tiling.Plane} {P : Tiling.Plane → Prop}
    (hU : IsOpen U) (hUne : U.Nonempty) (hP : ∀ᵐ z ∂volume, P z) :
    ∃ z ∈ U, P z := by
  have hμ : volume.restrict U ≠ 0 := by
    intro hz
    have hzero : volume U = 0 := by
      rw [← Measure.restrict_apply_univ U, hz]
      simp
    exact hU.measure_ne_zero volume hUne hzero
  let hne : (ae (volume.restrict U)).NeBot := ae_neBot.mpr hμ
  have hP' : ∀ᵐ z ∂volume.restrict U, P z := hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists Tiling.Plane _ (ae (volume.restrict U)) hne
      (hP'.and (ae_restrict_mem hU.measurableSet)) with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private theorem openCarrier_subset_factorProduct :
    (∀ K : Region, K.openCarrier ⊆ factorProduct K) := by
  intro K z hz
  change z.re ∈ interior (closure (Complex.re '' K.openCarrier)) ∧
    z.im ∈ interior (closure (Complex.im '' K.openCarrier))
  constructor
  · apply interior_maximal subset_closure
      (Complex.isOpenMap_re K.openCarrier K.openCarrier_regularOpen.1)
    exact ⟨z, hz, rfl⟩
  · apply interior_maximal subset_closure
      (Complex.isOpenMap_im K.openCarrier K.openCarrier_regularOpen.1)
    exact ⟨z, hz, rfl⟩

private theorem factorProduct_regularOpen :
    (∀ K : Region, IsOpen (factorProduct K) ∧
    interior (closure (factorProduct K)) = factorProduct K) := by
  intro K
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let B : Set ℝ := interior (closure (Complex.im '' K.openCarrier))
  let E : Tiling.Plane ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
  have hpre : ({z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B}) = E ⁻¹' (A ×ˢ B) := by
    ext z
    rfl
  change IsOpen {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B} ∧
    interior (closure {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B}) =
      {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B}
  rw [hpre]
  constructor
  · exact (isOpen_interior.prod isOpen_interior).preimage E.continuous
  · rw [← E.preimage_closure, ← E.preimage_interior,
      closure_prod_eq, interior_prod_eq]
    rw [show interior (closure A) = A by
          exact interior_closure_idem,
      show interior (closure B) = B by
          exact interior_closure_idem]
private theorem coordinateDeformation_factorImages :
    (∀ (C : ApproximationContext.{u})
      {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
      (D : CoordinateDeformation C phi),
    horizontalFactor D.deformedRegion =
        D.firstHomeomorph '' horizontalFactor C.region ∧
    verticalFactor D.deformedRegion =
        D.secondHomeomorph '' verticalFactor C.region) := by
  intro C phi D
  constructor
  · change interior (closure (Complex.re '' D.deformedRegion.openCarrier)) =
      D.firstHomeomorph ''
        interior (closure (Complex.re '' C.region.openCarrier))
    have hproj : Complex.re '' D.deformedRegion.openCarrier =
        D.firstHomeomorph '' (Complex.re '' C.region.openCarrier) := by
      rw [D.deformedRegion_openCarrier]
      ext x
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨z.re, ⟨z, hz, rfl⟩, ?_⟩
        rw [D.planarHomeomorph_apply]
        simp
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨D.planarHomeomorph z, ⟨z, hz, rfl⟩, ?_⟩
        rw [D.planarHomeomorph_apply]
        simp
    rw [hproj, ← D.firstHomeomorph.image_closure,
      ← D.firstHomeomorph.image_interior]
  · change interior (closure (Complex.im '' D.deformedRegion.openCarrier)) =
      D.secondHomeomorph ''
        interior (closure (Complex.im '' C.region.openCarrier))
    have hproj : Complex.im '' D.deformedRegion.openCarrier =
        D.secondHomeomorph '' (Complex.im '' C.region.openCarrier) := by
      rw [D.deformedRegion_openCarrier]
      ext y
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨z.im, ⟨z, hz, rfl⟩, ?_⟩
        rw [D.planarHomeomorph_apply]
        simp
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨D.planarHomeomorph z, ⟨z, hz, rfl⟩, ?_⟩
        rw [D.planarHomeomorph_apply]
        simp
    rw [hproj, ← D.secondHomeomorph.image_closure,
      ← D.secondHomeomorph.image_interior]

private theorem productRegion_of_coordinateDeformation :
    (∀ (C : ApproximationContext.{u})
      {phi : C.coordinateSpace →ₗ[ℚ] ℚ}
      (D : CoordinateDeformation C phi),
    Tiling.AxisParallel.Structure.IsProductRegion D.deformedRegion →
      Tiling.AxisParallel.Structure.IsProductRegion C.region) := by
  intro C phi D hproduct
  have hfirst : interior (closure (Complex.re '' D.deformedRegion.openCarrier)) =
      D.firstHomeomorph ''
        interior (closure (Complex.re '' C.region.openCarrier)) :=
    (coordinateDeformation_factorImages C D).1
  have hsecond : interior (closure (Complex.im '' D.deformedRegion.openCarrier)) =
      D.secondHomeomorph ''
        interior (closure (Complex.im '' C.region.openCarrier)) :=
    (coordinateDeformation_factorImages C D).2
  rw [Tiling.AxisParallel.Structure.isProductRegion_iff_regularizedProjections] at hproduct ⊢
  apply (Set.image_eq_image D.planarHomeomorph.injective).mp
  rw [← D.deformedRegion_openCarrier, hproduct]
  ext z
  constructor
  · intro hz
    change z.re ∈ interior (closure (Complex.re '' D.deformedRegion.openCarrier)) ∧
      z.im ∈ interior (closure (Complex.im '' D.deformedRegion.openCarrier)) at hz
    rw [hfirst, hsecond] at hz
    obtain ⟨⟨x, hx, hxeq⟩, ⟨y, hy, hyeq⟩⟩ := hz
    refine ⟨(x : ℂ) + (y : ℂ) * Complex.I, ⟨by simpa, by simpa⟩, ?_⟩
    rw [D.planarHomeomorph_apply]
    apply Complex.ext
    · simpa using hxeq
    · simpa using hyeq
  · rintro ⟨w, hw, rfl⟩
    rw [D.planarHomeomorph_apply]
    simp only [Set.mem_ofPred_eq]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero,
      Complex.add_im, Complex.mul_im, zero_add]
    rw [hfirst, hsecond]
    exact ⟨⟨w.re, hw.1, rfl⟩, ⟨w.im, hw.2, rfl⟩⟩

theorem productRegion_of_deformations :
    (∀ (C : ApproximationContext.{u})
    (epsilon : ℕ → ℝ) (_hepsilon_pos : ∀ n, 0 < epsilon n)
    (_hepsilon_zero : Tendsto epsilon atTop (nhds 0))
    (phi : (n : ℕ) → C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hphi : ∀ n, IsEpsilonApproximation C (epsilon n) (phi n))
    (D : (n : ℕ) → CoordinateDeformation C (phi n)),
    (∀ n, Tiling.AxisParallel.Structure.IsProductRegion (D n).deformedRegion) →
      Tiling.AxisParallel.Structure.IsProductRegion C.region) := by
  intro C epsilon _hepsilon_pos _hepsilon_zero phi _hphi D hproduct
  exact productRegion_of_coordinateDeformation C (D 0) (hproduct 0)

private theorem centerColumnFibre_isColumnAxis :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    ∀ c : ℝ,
      IsCenterColumn Axis.vertical K (axisCentreFibre T c) →
      c ∈ columnAxisSet K T) := by
  intro K T hTile c hC
  let C : Set Tiling.Plane := {z | z ∈ T ∧ z.re = c}
  change IsCenterColumn Axis.vertical K C at hC
  change ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = c}
  have hCsub : C ⊆ T := fun _ hz ↦ hz.1
  obtain ⟨d, hCnonempty, hdcoord, hCsupport⟩ := centerColumn_regularSupport hC
  obtain ⟨t, htC⟩ := hCnonempty
  have hdc : d = c := by
    have hd := hdcoord t htC
    change t.re = d at hd
    exact hd.symm.trans htC.2
  subst d
  have hCslab : ∃ X : Set ℝ, X = interior (closure X) ∧
      regularSupport K C = Complex.re ⁻¹' X := by
    refine ⟨interior (closure (c +ᵥ (Complex.re '' K.openCarrier))), ?_, ?_⟩
    · exact interior_closure_idem.symm
    · exact hCsupport.trans (by ext z; rfl)
  have hminimal : Continuous.IsMinimalVerticalSlabSubfamily K T C := by
    rw [Continuous.isMinimalVerticalSlabSubfamily_iff]
    refine ⟨⟨t, htC⟩, hCsub, hCslab, ?_⟩
    intro Q hQnonempty hQsub hQslab
    have hQsubT : Q ⊆ T := hQsub.trans hCsub
    obtain ⟨X, hXregular, hQsupport⟩ := hQslab
    have hQpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements Q) := by
      intro p hp q hq hpq
      exact hC.1 (hQsub hp) (hQsub hq) hpq
    have hQcolumn : IsCenterColumn Axis.vertical K Q := by
      refine ⟨hQpacking, hQnonempty, ⟨c, ?_⟩, ?_⟩
      · intro z hz
        exact (hQsub hz).2
      · intro a
        rw [hQsupport]
        ext z
        simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage,
          vadd_eq_add, Complex.neg_re, Complex.add_re,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_self,
          neg_zero, zero_add]
    obtain ⟨e, _, hecoord, hQformula⟩ := centerColumn_regularSupport hQcolumn
    obtain ⟨q, hqQ⟩ := hQnonempty
    have hec : e = c := by
      have he := hecoord q hqQ
      change q.re = e at he
      exact he.symm.trans (hQsub hqQ).2
    subst e
    have hsupportEq : regularSupport K Q = regularSupport K C := by
      rw [hQformula, hCsupport]
    have hTileC : TilesOn K C (regularSupport K C) := by
      refine ⟨hTile.1.mono hCsub, hC.1, ?_⟩
      filter_upwards [openUnion_aeEq_regularSupport hC.1] with z hz
      constructor
      · intro hs
        have hu : z ∈ openUnion K C := Eq.mp hz.symm hs
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hu
        exact hu
      · intro he
        have hu : z ∈ openUnion K C := by
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
          exact he
        exact Eq.mp hz hu
    let parts : Bool → Set Tiling.Plane
      | false => Q
      | true => C \ Q
    have hparts : Set.PairwiseDisjoint Set.univ parts := by
      intro i _ j _ hij
      cases i <;> cases j
      · exact (hij rfl).elim
      · exact Set.disjoint_left.2 fun _ hxQ hxD ↦ hxD.2 hxQ
      · exact Set.disjoint_left.2 fun _ hxD hxQ ↦ hxD.2 hxQ
      · exact (hij rfl).elim
    have hunion : (⋃ i, parts i) = C := by
      ext z
      constructor
      · simp only [Set.mem_iUnion]
        rintro ⟨i, hi⟩
        cases i
        · exact hQsub hi
        · exact hi.1
      · intro hzC
        by_cases hzQ : z ∈ Q
        · exact Set.mem_iUnion.2 ⟨false, hzQ⟩
        · exact Set.mem_iUnion.2 ⟨true, hzC, hzQ⟩
    have hdisjoint : Disjoint (regularSupport K Q) (regularSupport K (C \ Q)) := by
      have hp := (regularSupport_pairwiseDisjoint parts hparts hunion hTileC).1
        (Set.mem_univ false) (Set.mem_univ true) (by decide)
      exact hp
    apply Set.Subset.antisymm hQsub
    intro z hzC
    by_contra hzQ
    have hzD : z ∈ C \ Q := ⟨hzC, hzQ⟩
    obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
    let w : Tiling.Plane := z + k
    have hwCraw : w ∈ openUnion K C := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨z, hzC⟩, k, hk, rfl⟩
    have hwDraw : w ∈ openUnion K (C \ Q) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨⟨z, hzD⟩, k, hk, rfl⟩
    have hopenC : IsOpen (openUnion K C) :=
      isOpen_iUnion fun s ↦ K.openCarrier_regularOpen.1.vadd s.1
    have hopenD : IsOpen (openUnion K (C \ Q)) :=
      isOpen_iUnion fun s ↦ K.openCarrier_regularOpen.1.vadd s.1
    have hwCsupport : w ∈ regularSupport K C :=
      interior_maximal subset_closure hopenC hwCraw
    have hwDsupport : w ∈ regularSupport K (C \ Q) :=
      interior_maximal subset_closure hopenD hwDraw
    exact Set.disjoint_left.1 hdisjoint (hsupportEq ▸ hwCsupport) hwDsupport
  have hrange : C ∈ Set.range (@Continuous.VerticalPlate.centres K T) := by
    rw [Continuous.verticalPlates_intrinsic hTile]
    exact hminimal
  obtain ⟨P, hPC⟩ := hrange
  refine ⟨P, ?_, ?_⟩
  · exact ⟨c, hPC ▸ fun _ hz ↦ hz.2⟩
  · intro z hz
    rw [hPC] at hz
    exact hz.2

private theorem horizontalActiveAxes_lineTiles_ae_raw :
    ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
      Tiling.AxisParallel.Structure.IsProductRegion K →
      ∀ᵐ y : ℝ ∂volume,
        LineTiles (interior (closure (Complex.re '' K.openCarrier)))
          {a | ∃ t ∈ T, t.re = a ∧
            y - t.im ∈ interior (closure (Complex.im '' K.openCarrier))} := by
  intro K T hTile hproduct
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let B : Set ℝ := interior (closure (Complex.im '' K.openCarrier))
  have hK : K.openCarrier = {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B} := by
    exact (Tiling.AxisParallel.Structure.isProductRegion_iff_regularizedProjections K).mp hproduct
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume, z ∈ openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    have hex : ∃ t : T, z ∈ (t.1 +ᵥ K.openCarrier) :=
      hz.mp (Set.mem_univ z)
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact hex
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hxy : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      (x : ℂ) + (y : ℂ) * Complex.I ∈ openUnion K T := by
    have hprod := MeasureTheory.Measure.ae_ae_of_ae_prod hpull
    filter_upwards [hprod] with x hx
    filter_upwards [hx] with y hy
    have heq : ({ re := x, im := y } : ℂ) =
        (x : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rwa [← heq]
  have hmeas : MeasurableSet {p : ℝ × ℝ |
      (p.1 : ℂ) + (p.2 : ℂ) * Complex.I ∈ openUnion K T} := by
    have hopen : IsOpen (openUnion K T) :=
      isOpen_iUnion fun t ↦ K.openCarrier_regularOpen.1.vadd t.1
    exact hopen.measurableSet.preimage (by fun_prop)
  have hyx := (MeasureTheory.Measure.ae_ae_comm hmeas).mp hxy
  filter_upwards [hyx] with y hcover
  change LineTiles A
    {a | ∃ t ∈ T, t.re = a ∧ y - t.im ∈ B}
  refine ⟨isOpen_interior.measurableSet, MeasurableSet.univ, ?_, ?_, ?_⟩
  · apply (hTile.1.image Complex.re).mono
    rintro a ⟨t, ht, rfl, -⟩
    exact ⟨t, ht, rfl⟩
  · intro a ha b hb hab
    apply Disjoint.aedisjoint
    rw [Set.disjoint_left]
    intro x hxa hxb
    obtain ⟨t, htT, hta, hty⟩ := ha
    obtain ⟨s, hsT, hsb, hsy⟩ := hb
    have hts : t ≠ s := by
      intro hts
      apply hab
      rw [← hta, ← hsb, hts]
    have hpack := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      htT hsT hts
    refine (Set.disjoint_left.1 hpack)
      (a := (x : ℂ) + (y : ℂ) * Complex.I)
      ?_ ?_
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [hK]
      constructor
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxa
        simpa [hta] using hxa
      · simpa [sub_eq_add_neg, add_comm] using hty
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      rw [hK]
      constructor
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxb
        simpa [hsb] using hxb
      · simpa [sub_eq_add_neg, add_comm] using hsy
  · filter_upwards [hcover] with x hx
    simp only [Set.mem_univ, true_iff]
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hx
    obtain ⟨t, ht⟩ := hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, hK] at ht
    refine ⟨⟨t.1.re, ⟨t.1, t.2, rfl, ?_⟩⟩, ?_⟩
    · simpa [sub_eq_add_neg, add_comm] using ht.2
    · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa using ht.1

private theorem horizontalActiveAxes_lineTiles_ae :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    Tiling.AxisParallel.Structure.IsProductRegion K →
    ∀ᵐ y : ℝ ∂volume,
      LineTiles (horizontalFactor K) (horizontalActiveAxes K T y)) := by
  intro K T hTile hproduct
  change ∀ᵐ y : ℝ ∂volume,
    LineTiles (interior (closure (Complex.re '' K.openCarrier)))
      {a | ∃ t ∈ T, t.re = a ∧
        y - t.im ∈ interior (closure (Complex.im '' K.openCarrier))}
  exact horizontalActiveAxes_lineTiles_ae_raw hTile hproduct

private theorem exists_mem_Ioo_of_ae_real {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hP : ∀ᵐ x : ℝ ∂volume, P x) :
    ∃ x ∈ Ioo a b, P x := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    intro hz
    have hz' : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo a b), hz]
      simp
    rw [Real.volume_Ioo] at hz'
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at hz'
  let hne : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hμ
  have hP' : ∀ᵐ x ∂volume.restrict (Ioo a b), P x :=
    hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (hP'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, hxP, hxI⟩
  exact ⟨x, hxI, hxP⟩

private theorem columnAxis_active_ae_raw :
    ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
      Tiling.AxisParallel.Structure.IsProductRegion K →
      ∀ a, (∃ P : Continuous.VerticalPlate K T,
        Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}) →
        ∀ᵐ y : ℝ ∂volume, ∃ t ∈ T, t.re = a ∧
          y - t.im ∈ interior (closure (Complex.im '' K.openCarrier)) := by
  intro K T hTile hproduct a ha
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let B : Set ℝ := interior (closure (Complex.im '' K.openCarrier))
  have hK : K.openCarrier = {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B} :=
    (Tiling.AxisParallel.Structure.isProductRegion_iff_regularizedProjections K).mp hproduct
  change ∃ P : Continuous.VerticalPlate K T,
      Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a} at ha
  obtain ⟨P, hPcolumn, hPaxis⟩ := ha
  have hPsubT : P.centres ⊆ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hPpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    intro p hp q hq hpq
    exact hTile.2.1 (hPsubT hp) (hPsubT hq) hpq
  obtain ⟨hPbase, hPsupport⟩ :=
    Continuous.verticalColumn_regularSupport hTile P hPcolumn hPaxis
  have hsum : (Complex.re '' K.openCarrier) + ({a} : Set ℝ) =
      a +ᵥ (Complex.re '' K.openCarrier) := by
    ext x
    constructor
    · rintro ⟨u, hu, v, rfl, rfl⟩
      exact ⟨u, hu, by simp [vadd_eq_add, add_comm]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, a, rfl, by simp [vadd_eq_add, add_comm]⟩
  have hbase : P.base = a +ᵥ A := by
    rw [hPbase, hsum, closure_vadd, interior_vadd]
  have hsupport : P.support = Complex.re ⁻¹' (a +ᵥ A) := by
    rw [hPsupport, hbase]
  have hae := openUnion_aeEq_regularSupport hPpacking
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hae
  have hgood : ∀ᵐ x : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      (((x : ℂ) + (y : ℂ) * Complex.I ∈ openUnion K P.centres) ↔
        (x : ℂ) + (y : ℂ) * Complex.I ∈ P.support) := by
    have hprod := MeasureTheory.Measure.ae_ae_of_ae_prod hpull
    filter_upwards [hprod] with x hx
    filter_upwards [hx] with y hy
    have heq : ({ re := x, im := y } : ℂ) =
        (x : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    change (({ re := x, im := y } : ℂ) ∈ openUnion K P.centres) =
      (({ re := x, im := y } : ℂ) ∈ P.support) at hy
    rw [heq] at hy
    exact Iff.of_eq hy
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hkA : k.re ∈ A := by
    apply interior_maximal subset_closure
      (Complex.isOpenMap_re K.openCarrier K.openCarrier_regularOpen.1)
    exact ⟨k, hk, rfl⟩
  obtain ⟨l, r, hlr, hlrA⟩ :=
    (isOpen_interior.vadd a).exists_Ioo_subset ⟨a + k.re, ⟨k.re, hkA, rfl⟩⟩
  obtain ⟨x, hxI, hxgood⟩ := exists_mem_Ioo_of_ae_real hlr hgood
  have hxaxis : x ∈ a +ᵥ A := hlrA hxI
  filter_upwards [hxgood] with y hy
  change ∃ t ∈ T, t.re = a ∧ y - t.im ∈ B
  have hzsupport : (x : ℂ) + (y : ℂ) * Complex.I ∈ P.support := by
    rw [hsupport]
    simpa using hxaxis
  have hzraw := hy.mpr hzsupport
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzraw
  obtain ⟨t, ht⟩ := hzraw
  refine ⟨t.1, hPsubT t.2, hPaxis t.2, ?_⟩
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, hK] at ht
  simpa [sub_eq_add_neg, add_comm] using ht.2

private theorem columnAxis_active_ae :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    Tiling.AxisParallel.Structure.IsProductRegion K →
    ∀ a ∈ columnAxisSet K T,
      ∀ᵐ y : ℝ ∂volume, a ∈ horizontalActiveAxes K T y) := by
  intro K T hTile hproduct a ha
  change ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a} at ha
  change ∀ᵐ y : ℝ ∂volume, ∃ t ∈ T, t.re = a ∧
    y - t.im ∈ interior (closure (Complex.im '' K.openCarrier))
  exact columnAxis_active_ae_raw hTile hproduct a ha

private theorem commonLinePeriod_repeatsColumnAxes :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    Tiling.AxisParallel.Structure.IsProductRegion K →
    ∀ {beta : ℝ}, 0 < beta →
      (∀ L : Set ℝ, LineTiles (horizontalFactor K) L → beta +ᵥ L = L) →
      beta +ᵥ columnAxisSet K T = columnAxisSet K T) := by
  intro K T hTile hproduct beta hbeta hperiod
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let B : Set ℝ := interior (closure (Complex.im '' K.openCarrier))
  let axes : Set ℝ := {a | ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}}
  let active (y : ℝ) : Set ℝ :=
    {a | ∃ t ∈ T, t.re = a ∧ y - t.im ∈ B}
  have hK : K.openCarrier = {z : Tiling.Plane | z.re ∈ A ∧ z.im ∈ B} :=
    (Tiling.AxisParallel.Structure.isProductRegion_iff_regularizedProjections K).mp hproduct
  have hlines : ∀ᵐ y : ℝ ∂volume, LineTiles A (active y) := by
    simpa only [A, B, active] using
      horizontalActiveAxes_lineTiles_ae_raw hTile hproduct
  have haxisActive : ∀ a ∈ axes, ∀ᵐ y : ℝ ∂volume, a ∈ active y := by
    intro a ha
    simpa only [B, active, Set.mem_ofPred_eq] using
      columnAxis_active_ae_raw hTile hproduct a ha
  obtain ⟨k, hk⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hkA : k.re ∈ A := by
    apply interior_maximal subset_closure
      (Complex.isOpenMap_re K.openCarrier K.openCarrier_regularOpen.1)
    exact ⟨k, hk, rfl⟩
  have axis_of_ae_active : ∀ c : ℝ,
      (∀ᵐ y : ℝ ∂volume, c ∈ active y) → c ∈ axes := by
    intro c hcactive
    let C : Set Tiling.Plane := {z | z ∈ T ∧ z.re = c}
    let Y : Set ℝ := Complex.im '' C
    have hCeq : C = {z : Tiling.Plane | z.re = c ∧ z.im ∈ Y} := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.2, ⟨z, hz, rfl⟩⟩
      · rintro ⟨hzre, w, hwC, hwim⟩
        have hwz : w = z := Complex.ext (hwC.2.trans hzre.symm) hwim
        simpa [hwz] using hwC
    have hYnonempty : Y.Nonempty := by
      obtain ⟨y, hy⟩ := hcactive.exists
      obtain ⟨t, htT, htc, -⟩ := hy
      refine ⟨t.im, t, ?_, rfl⟩
      exact ⟨htT, htc⟩
    have hCsub : C ⊆ T := fun _ hz ↦ hz.1
    have hCpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements C) := by
      intro p hp q hq hpq
      exact hTile.2.1 (hCsub hp) (hCsub hq) hpq
    have hYcountable : Y.Countable := (hTile.1.mono hCsub).image Complex.im
    have hLineB : LineTiles B Y := by
      refine ⟨isOpen_interior.measurableSet, MeasurableSet.univ,
        hYcountable, ?_, ?_⟩
      · intro y₁ hy₁ y₂ hy₂ hyne
        apply Disjoint.aedisjoint
        rw [Set.disjoint_left]
        intro q hq₁ hq₂
        obtain ⟨t₁, ht₁C, ht₁im⟩ := hy₁
        obtain ⟨t₂, ht₂C, ht₂im⟩ := hy₂
        have htne : t₁ ≠ t₂ := by
          intro h
          apply hyne
          exact ht₁im.symm.trans ((congrArg Complex.im h).trans ht₂im)
        have hpack := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
          (hCsub ht₁C) (hCsub ht₂C) htne
        refine (Set.disjoint_left.1 hpack)
          (a := ((c + k.re : ℝ) : ℂ) + (q : ℂ) * Complex.I) ?_ ?_
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem, hK]
          constructor
          · simpa [ht₁C.2] using hkA
          · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hq₁
            simpa [ht₁im, sub_eq_add_neg, add_comm] using hq₁
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem, hK]
          constructor
          · simpa [ht₂C.2] using hkA
          · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hq₂
            simpa [ht₂im, sub_eq_add_neg, add_comm] using hq₂
      · filter_upwards [hcactive] with y hy
        simp only [Set.mem_univ, true_iff]
        obtain ⟨t, htT, htc, hty⟩ := hy
        refine ⟨⟨t.im, ⟨t, ⟨htT, htc⟩, rfl⟩⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simpa [sub_eq_add_neg, add_comm] using hty
    have hgeneric : ∀ r : ℝ,
        r ∉ K.vertexFinset.image Complex.re →
        (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r).Nonempty →
          LineTiles (Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r) Y := by
      intro r _ hrslice
      obtain ⟨y, hy⟩ := hrslice
      have hry : (r : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier := by
        simpa [Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice] using hy
      rw [hK] at hry
      have hslice : Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice K r = B := by
        ext s
        simp only [Tiling.AxisParallel.OneDimensional.ColumnSlices.verticalSlice,
          Set.mem_ofPred_eq]
        rw [hK]
        constructor
        · exact fun hs ↦ by simpa using hs.2
        · exact fun hs ↦ ⟨by simpa using hry.1, by simpa using hs⟩
      simpa only [hslice] using hLineB
    have hCenter : IsCenterColumn Axis.vertical K C :=
      (Tiling.AxisParallel.Foundations.centerColumn_iff_genericSlices
        hCeq hYnonempty hCpacking).mpr hgeneric
    change c ∈ {a | ∃ P : Continuous.VerticalPlate K T,
      Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}}
    exact centerColumnFibre_isColumnAxis hTile c hCenter
  have shift_forward : ∀ a ∈ axes, a + beta ∈ axes := by
    intro a ha
    apply axis_of_ae_active
    filter_upwards [haxisActive a ha, hlines] with y hay hline
    have heq := hperiod (active y) hline
    rw [← heq]
    exact ⟨a, hay, by simp [vadd_eq_add, add_comm]⟩
  have shift_backward : ∀ a ∈ axes, a - beta ∈ axes := by
    intro a ha
    apply axis_of_ae_active
    filter_upwards [haxisActive a ha, hlines] with y hay hline
    have heq := hperiod (active y) hline
    have haimage : a ∈ beta +ᵥ active y := heq.symm ▸ hay
    obtain ⟨q, hq, hqa⟩ := haimage
    have hqeq : q = a - beta := by
      simpa [vadd_eq_add] using congrArg (fun x : ℝ ↦ x - beta) hqa
    simpa [hqeq] using hq
  change beta +ᵥ axes = axes
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [add_comm] using shift_forward a ha
  · intro hx
    refine ⟨x - beta, shift_backward x hx, ?_⟩
    simp [vadd_eq_add]

private theorem verticalColumnCentres_support_eq_axisCylinders_raw :
    ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
      Tiling.AxisParallel.Structure.IsProductRegion K →
      regularSupport K (Continuous.verticalColumnCentres K T) =
        interior (closure
          ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
            ((({a | ∃ P : Continuous.VerticalPlate K T,
                Continuous.IsVerticalColumn P ∧
                P.centres ⊆ {z | z.re = a}} +
              interior (closure (Complex.re '' K.openCarrier))) : Set ℝ) ×ˢ
                (univ : Set ℝ)))) := by
  intro K T hTile hproduct
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let axes : Set ℝ := {a | ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}}
  let U : Set Tiling.Plane := openUnion K (Continuous.verticalColumnCentres K T)
  let V : Set Tiling.Plane := {z | z.re ∈ axes + A}
  have hK : K.openCarrier ⊆ {z : Tiling.Plane | z.re ∈ A} := by
    intro z hz
    exact (openCarrier_subset_factorProduct K hz).1
  have hUV : U ⊆ V := by
    intro z hz
    change z ∈ openUnion K (Continuous.verticalColumnCentres K T) at hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hz
    obtain ⟨s, k, hk, rfl⟩ := hz
    have hs := s.2
    change (s : Tiling.Plane) ∈
      ⋃ P : {P : Continuous.VerticalPlate K T | Continuous.IsVerticalColumn P},
        P.1.centres at hs
    rw [Set.mem_iUnion] at hs
    obtain ⟨P, hsP⟩ := hs
    obtain ⟨a, hPa⟩ := P.2
    have haaxes : a ∈ axes := ⟨P.1, P.2, hPa⟩
    have hkA : k.re ∈ A := hK hk
    change (s.1 + k).re ∈ axes + A
    refine ⟨a, haaxes, k.re, hkA, ?_⟩
    have hsa : (s : Tiling.Plane).re = a := hPa hsP
    rw [Complex.add_re, hsa]
  have hVU : V ⊆ closure U := by
    intro z hz
    obtain ⟨a, haaxes, r, hrA, hzre⟩ := hz
    obtain ⟨P, hPcolumn, hPaxis⟩ := haaxes
    obtain ⟨hPbase, hPsupport⟩ :=
      Continuous.verticalColumn_regularSupport hTile P hPcolumn hPaxis
    have hsum : (Complex.re '' K.openCarrier) + ({a} : Set ℝ) =
        a +ᵥ (Complex.re '' K.openCarrier) := by
      ext x
      constructor
      · rintro ⟨u, hu, v, rfl, rfl⟩
        exact ⟨u, hu, by simp [vadd_eq_add, add_comm]⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, a, rfl, by simp [vadd_eq_add, add_comm]⟩
    have hbase : P.base = a +ᵥ A := by
      rw [hPbase, hsum, closure_vadd, interior_vadd]
    have hzP : z ∈ P.support := by
      rw [hPsupport, hbase]
      refine ⟨r, hrA, ?_⟩
      simpa [vadd_eq_add, add_comm] using hzre
    have hzclP : z ∈ closure (openUnion K P.centres) :=
      interior_subset hzP
    apply closure_mono ?_ hzclP
    intro w hw
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hw
    change w ∈ openUnion K (Continuous.verticalColumnCentres K T)
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    obtain ⟨s, hs⟩ := hw
    refine ⟨⟨s.1, ?_⟩, hs⟩
    rw [Continuous.verticalColumnCentres_eq, Set.mem_iUnion]
    exact ⟨⟨P, hPcolumn⟩, s.2⟩
  have hclosure : closure U = closure V := Set.Subset.antisymm
    (closure_mono hUV) (closure_minimal hVU isClosed_closure)
  have hVimage : V =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        ((axes + A) ×ˢ (univ : Set ℝ)) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨hz, Set.mem_univ _⟩, ?_⟩
      apply Complex.ext <;> simp
    · rintro ⟨p, hp, rfl⟩
      simpa only [V, Set.mem_ofPred_eq, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero] using hp.1
  change interior (closure U) = interior (closure _)
  rw [hclosure, hVimage]

private theorem verticalColumnCentres_support_eq_axisCylinders :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    Tiling.AxisParallel.Structure.IsProductRegion K →
    regularSupport K (Continuous.verticalColumnCentres K T) =
      interior (closure
        ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
          (((columnAxisSet K T + horizontalFactor K) : Set ℝ) ×ˢ (univ : Set ℝ))))) := by
  intro K T hTile hproduct
  change regularSupport K (Continuous.verticalColumnCentres K T) =
    interior (closure
      ((fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        ((({a | ∃ P : Continuous.VerticalPlate K T,
            Continuous.IsVerticalColumn P ∧
            P.centres ⊆ {z | z.re = a}} +
          interior (closure (Complex.re '' K.openCarrier))) : Set ℝ) ×ˢ
            (univ : Set ℝ))))
  exact verticalColumnCentres_support_eq_axisCylinders_raw hTile hproduct

private theorem columnAxisPeriod_givesColumnSupportPeriod_raw :
    ∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
      Tiling.AxisParallel.Structure.IsProductRegion K →
      ∀ {beta : ℝ},
        beta +ᵥ {a | ∃ P : Continuous.VerticalPlate K T,
          Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}} =
          {a | ∃ P : Continuous.VerticalPlate K T,
            Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}} →
        Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport K (Continuous.verticalColumnCentres K T))
          ((beta : ℝ) : ℂ) := by
  intro K T hTile hproduct beta haxes
  let A : Set ℝ := interior (closure (Complex.re '' K.openCarrier))
  let axes : Set ℝ := {a | ∃ P : Continuous.VerticalPlate K T,
    Continuous.IsVerticalColumn P ∧ P.centres ⊆ {z | z.re = a}}
  let V : Set Tiling.Plane := {z | z.re ∈ axes + A}
  have haxis : beta +ᵥ axes = axes := haxes
  have hbase : beta +ᵥ (axes + A) = axes + A := by
    ext x
    constructor
    · rintro ⟨u, ⟨a, ha, r, hr, haur⟩, hux⟩
      have hab : a + beta ∈ axes := by
        rw [← haxis]
        exact ⟨a, ha, by simp [vadd_eq_add, add_comm]⟩
      refine ⟨a + beta, hab, r, hr, ?_⟩
      rw [← hux, ← haur]
      simp only [vadd_eq_add]
      ring
    · intro hx
      obtain ⟨a, ha, r, hr, har⟩ := hx
      have ha' : a - beta ∈ axes := by
        have haimage : a ∈ beta +ᵥ axes := haxis.symm ▸ ha
        obtain ⟨q, hq, hqa⟩ := haimage
        have hqeq : q = a - beta := by
          simpa [vadd_eq_add] using congrArg (fun y : ℝ ↦ y - beta) hqa
        simpa only [hqeq] using hq
      refine ⟨(a - beta) + r, ⟨a - beta, ha', r, hr, rfl⟩, ?_⟩
      rw [← har]
      simp only [vadd_eq_add]
      ring
  have hVperiod : ((beta : ℝ) : ℂ) +ᵥ V = V := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change ((beta : ℂ) + w).re ∈ axes + A
      rw [Complex.add_re, Complex.ofReal_re]
      rw [← hbase]
      exact ⟨w.re, hw, by simp [vadd_eq_add]⟩
    · intro hz
      have hzbase : z.re ∈ beta +ᵥ (axes + A) := hbase.symm ▸ hz
      obtain ⟨r, hr, hrz⟩ := hzbase
      let w : ℂ := z - beta
      refine ⟨w, ?_, ?_⟩
      · change w.re ∈ axes + A
        change (z - (beta : ℂ)).re ∈ axes + A
        rw [Complex.sub_re, Complex.ofReal_re]
        have hreq : r = z.re - beta := by
          simpa [vadd_eq_add] using congrArg (fun y : ℝ ↦ y - beta) hrz
        simpa only [← hreq] using hr
      · change (beta : ℂ) + w = z
        simp [w]
  have hVimage : V =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
        ((axes + A) ×ˢ (univ : Set ℝ)) := by
    ext z
    constructor
    · intro hz
      refine ⟨(z.re, z.im), ⟨hz, Set.mem_univ _⟩, ?_⟩
      apply Complex.ext <;> simp
    · rintro ⟨p, hp, rfl⟩
      simpa only [V, Set.mem_ofPred_eq, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_zero, add_zero] using hp.1
  have hsupport : regularSupport K (Continuous.verticalColumnCentres K T) =
      interior (closure V) := by
    rw [hVimage]
    exact verticalColumnCentres_support_eq_axisCylinders_raw hTile hproduct
  have hsupportPeriod : ((beta : ℝ) : ℂ) +ᵥ
      regularSupport K (Continuous.verticalColumnCentres K T) =
        regularSupport K (Continuous.verticalColumnCentres K T) := by
    rw [hsupport, ← interior_vadd, ← closure_vadd, hVperiod]
  intro x
  constructor
  · intro hx
    have hxshift : x + (beta : ℂ) ∈
        ((beta : ℝ) : ℂ) +ᵥ
          regularSupport K (Continuous.verticalColumnCentres K T) := by
      rw [hsupportPeriod]
      exact hx
    obtain ⟨y, hy, hyx⟩ := hxshift
    have : y = x := by
      apply add_right_cancel (b := (beta : ℂ))
      simpa [vadd_eq_add, add_comm] using hyx
    simpa only [this] using hy
  · intro hx
    have hxshift : x + (beta : ℂ) ∈
        ((beta : ℝ) : ℂ) +ᵥ
          regularSupport K (Continuous.verticalColumnCentres K T) := by
      refine ⟨x, hx, ?_⟩
      simp [vadd_eq_add, add_comm]
    rw [hsupportPeriod] at hxshift
    exact hxshift

private theorem columnAxisPeriod_givesColumnSupportPeriod :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    Tiling.AxisParallel.Structure.IsProductRegion K →
    ∀ {beta : ℝ}, beta +ᵥ columnAxisSet K T = columnAxisSet K T →
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (Continuous.verticalColumnCentres K T)) ((beta : ℝ) : ℂ)) := by
  intro K T hTile hproduct beta haxes
  apply columnAxisPeriod_givesColumnSupportPeriod_raw hTile hproduct
  exact haxes

private theorem horizontalFactor_isFiniteIntervalRegion
    (K : Region) : IsFiniteIntervalRegion
      (interior (closure (Complex.re '' K.openCarrier))) := by
  classical
  obtain ⟨R⟩ := K.isAxisParallel
  let E := {s : Set Tiling.Plane // s ∈ R.pieces}
  let _ : Fintype E := Fintype.ofFinite E
  let e : Fin (Fintype.card E) ≃ E := Fintype.equivFin E |>.symm
  let piece : Fin (Fintype.card E) → Set Tiling.Plane := fun i ↦ (e i).1
  have hpiece (i : Fin (Fintype.card E)) : piece i ∈ R.pieces := (e i).2
  choose p q hre him hpq using fun i ↦ R.isRectangle (piece i) (hpiece i)
  let a : Fin (Fintype.card E) → ℝ := fun i ↦ min (p i).re (q i).re
  let b : Fin (Fintype.card E) → ℝ := fun i ↦ max (p i).re (q i).re
  have himagePiece (i : Fin (Fintype.card E)) :
      Complex.re '' piece i = Icc (a i) (b i) := by
    rw [hpq i]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im) at hz
      have hzre : z.re ∈ Set.uIcc (p i).re (q i).re := hz.1
      simpa only [a, b, Set.uIcc] using hzre
    · intro hx
      let z : ℂ := Complex.mk x (p i).im
      refine ⟨z, ?_, by simp [z]⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im)
      constructor
      · change z.re ∈ Set.uIcc (p i).re (q i).re
        simpa only [z, a, b, Set.uIcc] using hx
      · change z.im ∈ Set.uIcc (p i).im (q i).im
        change (p i).im ∈ Set.uIcc (p i).im (q i).im
        exact left_mem_uIcc
  have hprojectionSupport : Complex.re '' K.support =
      ⋃ i, Complex.re '' piece i := by
    rw [← R.sUnion_eq]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, hsR, hzs⟩ := Set.mem_sUnion.mp hz
      let es : E := ⟨s, hsR⟩
      exact Set.mem_iUnion.2 ⟨Fintype.equivFin E es, by
        refine ⟨z, ?_, rfl⟩
        simpa [piece, e, es] using hzs⟩
    · rintro hx
      obtain ⟨i, z, hzi, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨z, Set.mem_sUnion.2 ⟨piece i, hpiece i, hzi⟩, rfl⟩
  have hprojectionClosure : closure (Complex.re '' K.openCarrier) =
      Complex.re '' K.support := by
    apply Set.Subset.antisymm
    · apply closure_minimal
      · exact Set.image_mono interior_subset
      · exact (K.isPolygonal.isCompact.image Complex.continuous_re).isClosed
    · rw [← K.isPolygonal.closure_interior]
      exact image_closure_subset_closure_image Complex.continuous_re
  have hclosedIntervals : closure (Complex.re '' K.openCarrier) =
      ⋃ i, Icc (a i) (b i) := by
    rw [hprojectionClosure, hprojectionSupport]
    apply iUnion_congr
    exact himagePiece
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  refine ⟨P.n, P.left, P.right, P.lt, ?_⟩
  rw [hclosedIntervals]
  exact P.union_eq

private theorem verticalFactor_isFiniteIntervalRegion
    (K : Region) : IsFiniteIntervalRegion
      (interior (closure (Complex.im '' K.openCarrier))) := by
  classical
  obtain ⟨R⟩ := K.isAxisParallel
  let E := {s : Set Tiling.Plane // s ∈ R.pieces}
  let _ : Fintype E := Fintype.ofFinite E
  let e : Fin (Fintype.card E) ≃ E := Fintype.equivFin E |>.symm
  let piece : Fin (Fintype.card E) → Set Tiling.Plane := fun i ↦ (e i).1
  have hpiece (i : Fin (Fintype.card E)) : piece i ∈ R.pieces := (e i).2
  choose p q hre him hpq using fun i ↦ R.isRectangle (piece i) (hpiece i)
  let a : Fin (Fintype.card E) → ℝ := fun i ↦ min (p i).im (q i).im
  let b : Fin (Fintype.card E) → ℝ := fun i ↦ max (p i).im (q i).im
  have himagePiece (i : Fin (Fintype.card E)) :
      Complex.im '' piece i = Icc (a i) (b i) := by
    rw [hpq i]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im) at hz
      have hzim : z.im ∈ Set.uIcc (p i).im (q i).im := hz.2
      simpa only [a, b, Set.uIcc] using hzim
    · intro hx
      let z : ℂ := Complex.mk (p i).re x
      refine ⟨z, ?_, by simp [z]⟩
      change z ∈ Complex.reProdIm
        (Set.uIcc (p i).re (q i).re) (Set.uIcc (p i).im (q i).im)
      constructor
      · change (p i).re ∈ Set.uIcc (p i).re (q i).re
        exact left_mem_uIcc
      · change x ∈ Set.uIcc (p i).im (q i).im
        simpa only [a, b, Set.uIcc] using hx
  have hprojectionSupport : Complex.im '' K.support =
      ⋃ i, Complex.im '' piece i := by
    rw [← R.sUnion_eq]
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨s, hsR, hzs⟩ := Set.mem_sUnion.mp hz
      let es : E := ⟨s, hsR⟩
      exact Set.mem_iUnion.2 ⟨Fintype.equivFin E es, by
        refine ⟨z, ?_, rfl⟩
        simpa [piece, e, es] using hzs⟩
    · rintro hx
      obtain ⟨i, z, hzi, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨z, Set.mem_sUnion.2 ⟨piece i, hpiece i, hzi⟩, rfl⟩
  have hprojectionClosure : closure (Complex.im '' K.openCarrier) =
      Complex.im '' K.support := by
    apply Set.Subset.antisymm
    · apply closure_minimal
      · exact Set.image_mono interior_subset
      · exact (K.isPolygonal.isCompact.image Complex.continuous_im).isClosed
    · rw [← K.isPolygonal.closure_interior]
      exact image_closure_subset_closure_image Complex.continuous_im
  have hclosedIntervals : closure (Complex.im '' K.openCarrier) =
      ⋃ i, Icc (a i) (b i) := by
    rw [hprojectionClosure, hprojectionSupport]
    apply iUnion_congr
    exact himagePiece
  obtain ⟨P⟩ := Tiling.AxisParallel.Foundations.GenericSlices.finiteClosedIntervals_merge a b
  refine ⟨P.n, P.left, P.right, P.lt, ?_⟩
  rw [hclosedIntervals]
  exact P.union_eq

private theorem productFactors_geometry :
    (∀ K : Region,
      IsOpen (horizontalFactor K) ∧
      interior (closure (horizontalFactor K)) = horizontalFactor K ∧
      (horizontalFactor K).Nonempty ∧ Bornology.IsBounded (horizontalFactor K) ∧
      IsFiniteIntervalRegion (horizontalFactor K) ∧
      0 < (volume (horizontalFactor K)).toReal ∧
      IsOpen (verticalFactor K) ∧
      interior (closure (verticalFactor K)) = verticalFactor K ∧
      (verticalFactor K).Nonempty ∧ Bornology.IsBounded (verticalFactor K) ∧
      IsFiniteIntervalRegion (verticalFactor K) ∧
      0 < (volume (verticalFactor K)).toReal) := by
  intro K
  have hKne : K.openCarrier.Nonempty := K.isPolygonal.interior_nonempty K.nonempty
  have hAfinite := horizontalFactor_isFiniteIntervalRegion K
  have hBfinite := verticalFactor_isFiniteIntervalRegion K
  have hAopen : IsOpen (horizontalFactor K) := isOpen_interior
  have hBopen : IsOpen (verticalFactor K) := isOpen_interior
  have hAne : (horizontalFactor K).Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    exact ⟨z.re, openCarrier_subset_factorProduct K hz |>.1⟩
  have hBne : (verticalFactor K).Nonempty := by
    obtain ⟨z, hz⟩ := hKne
    exact ⟨z.im, openCarrier_subset_factorProduct K hz |>.2⟩
  rcases hAfinite with ⟨nA, aA, bA, hAlt, hAeq⟩
  rcases hBfinite with ⟨nB, aB, bB, hBlt, hBeq⟩
  have hAbounded : Bornology.IsBounded (horizontalFactor K) := by
    change Bornology.IsBounded (interior (closure (Complex.re '' K.openCarrier)))
    rw [hAeq]
    exact Bornology.isBounded_iUnion.mpr fun i ↦ Metric.isBounded_Ioo (aA i) (bA i)
  have hBbounded : Bornology.IsBounded (verticalFactor K) := by
    change Bornology.IsBounded (interior (closure (Complex.im '' K.openCarrier)))
    rw [hBeq]
    exact Bornology.isBounded_iUnion.mpr fun i ↦ Metric.isBounded_Ioo (aB i) (bB i)
  have hAfinite' : IsFiniteIntervalRegion (horizontalFactor K) :=
    ⟨nA, aA, bA, hAlt, hAeq⟩
  have hBfinite' : IsFiniteIntervalRegion (verticalFactor K) :=
    ⟨nB, aB, bB, hBlt, hBeq⟩
  refine ⟨hAopen, interior_closure_idem, hAne, hAbounded, hAfinite', ?_,
    hBopen, interior_closure_idem, hBne, hBbounded, hBfinite', ?_⟩
  · apply ENNReal.toReal_pos
    · exact hAopen.measure_ne_zero volume hAne
    · exact hAbounded.measure_lt_top.ne
  · apply ENNReal.toReal_pos
    · exact hBopen.measure_ne_zero volume hBne
    · exact hBbounded.measure_lt_top.ne

private theorem transverseColumns_commonCentre_aeProduct :
    (∀ {K : Region} {T : Set Tiling.Plane}, TilesOn K T univ →
    ∀ (P : Continuous.VerticalPlate K T), Continuous.IsVerticalColumn P →
    ∀ (Q : Continuous.VerticalPlate K.coordinateSwap (coordinateSwap '' T)),
      Continuous.IsVerticalColumn Q →
    ∃ t : ↥T,
      (t.1 : Tiling.Plane) ∈ P.centres ∧ coordinateSwap t.1 ∈ Q.centres ∧
      (t.1 +ᵥ K.openCarrier) =ᵐ[volume]
        ((t.1.re +ᵥ horizontalFactor K) ×ˢ
          (t.1.im +ᵥ verticalFactor K) : Set (ℝ × ℝ)).preimage
            (fun z : Tiling.Plane => (z.re, z.im))) := by
  intro K T hTile P hPcol Q hQcol
  obtain ⟨a, hPa⟩ := hPcol
  obtain ⟨b, hQb⟩ := hQcol
  have hPsub : P.centres ⊆ T := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hQsub : Q.centres ⊆ coordinateSwap '' T := by
    rintro _ ⟨q, -, rfl⟩
    exact q.2
  have hPpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    intro p hp q hq hpq
    exact hTile.2.1 (hPsub hp) (hPsub hq) hpq
  have hSwapTile : TilesOn K.coordinateSwap (coordinateSwap '' T) univ := by
    have h := Tiling.AxisParallel.tilesOn_coordinateSwap hTile
    simpa only [Set.image_univ_of_surjective coordinateSwap.surjective] using h
  have hQpack : Tiling.IsPacking K.coordinateSwap.toPolygonalRegion.prototileFamily
      (K.coordinateSwap.toPolygonalRegion.placements Q.centres) := by
    intro p hp q hq hpq
    exact hSwapTile.2.1 (hQsub hp) (hQsub hq) hpq
  obtain ⟨hPbase, hPsupport⟩ :=
    Continuous.verticalColumn_regularSupport hTile P ⟨a, hPa⟩ hPa
  obtain ⟨hQbase, hQsupport⟩ :=
    Continuous.verticalColumn_regularSupport hSwapTile Q ⟨b, hQb⟩ hQb
  have hsumA : (Complex.re '' K.openCarrier) + ({a} : Set ℝ) =
      a +ᵥ Complex.re '' K.openCarrier := by
    ext x
    constructor
    · rintro ⟨u, hu, v, rfl, rfl⟩
      exact ⟨u, hu, by simp [vadd_eq_add, add_comm]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, a, rfl, by simp [vadd_eq_add, add_comm]⟩
  have hsumB : (Complex.re '' K.coordinateSwap.openCarrier) + ({b} : Set ℝ) =
      b +ᵥ Complex.im '' K.openCarrier := by
    rw [Tiling.AxisParallel.coordinateSwap_openCarrier]
    have himage : Complex.re '' (coordinateSwap '' K.openCarrier) =
        Complex.im '' K.openCarrier := by
      ext x
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨z, hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨coordinateSwap z, ⟨z, hz, rfl⟩, rfl⟩
    rw [himage]
    ext x
    constructor
    · rintro ⟨u, hu, v, rfl, rfl⟩
      exact ⟨u, hu, by simp [vadd_eq_add, add_comm]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, b, rfl, by simp [vadd_eq_add, add_comm]⟩
  have hPbase' : P.base = a +ᵥ horizontalFactor K := by
    rw [hPbase, hsumA, closure_vadd, interior_vadd]
    rfl
  have hQbase' : Q.base = b +ᵥ verticalFactor K := by
    rw [hQbase, hsumB, closure_vadd, interior_vadd]
    rfl
  let X : Set Tiling.Plane := {z | z.re ∈ a +ᵥ horizontalFactor K ∧
    z.im ∈ b +ᵥ verticalFactor K}
  have hXopen : IsOpen X :=
    ((isOpen_interior.vadd a).preimage Complex.continuous_re).inter
      ((isOpen_interior.vadd b).preimage Complex.continuous_im)
  have hXne : X.Nonempty := by
    obtain ⟨_, _, hAne, _, _, _, _, _, hBne, _⟩ := productFactors_geometry K
    obtain ⟨x, hx⟩ := hAne
    obtain ⟨y, hy⟩ := hBne
    refine ⟨⟨a + x, b + y⟩, ?_, ?_⟩
    · exact ⟨x, hx, by simp [vadd_eq_add]⟩
    · exact ⟨y, hy, by simp [vadd_eq_add]⟩
  have hPae := openUnion_aeEq_regularSupport hPpack
  have hQae0 := openUnion_aeEq_regularSupport hQpack
  have hQae : ∀ᵐ z ∂volume,
      (coordinateSwap z ∈ openUnion K.coordinateSwap Q.centres) =
        (coordinateSwap z ∈ Q.support) :=
    coordinateSwapLIE_local.measurePreserving.quasiMeasurePreserving.ae hQae0
  have hamb := hTile.2.2
  have hgood : ∀ᵐ z ∂volume,
      ((z ∈ openUnion K P.centres) = (z ∈ P.support)) ∧
      ((coordinateSwap z ∈ openUnion K.coordinateSwap Q.centres) =
        (coordinateSwap z ∈ Q.support)) ∧
      (z ∈ univ ↔ ∃ s : T, z ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) := by
    filter_upwards [hPae, hQae, hamb] with z hp hq ha
    exact ⟨hp, hq, ha⟩
  obtain ⟨z, hzX, hzPae, hzQae, hzamb⟩ := exists_mem_open_of_ae hXopen hXne
    hgood
  have hzPsupport : z ∈ P.support := by
    rw [hPsupport, hPbase']
    exact hzX.1
  have hzQsupport : coordinateSwap z ∈ Q.support := by
    rw [hQsupport, hQbase']
    simpa using hzX.2
  have hzPraw : z ∈ openUnion K P.centres := hzPae.mpr hzPsupport
  have hzQraw : coordinateSwap z ∈ openUnion K.coordinateSwap Q.centres :=
    hzQae.mpr hzQsupport
  rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzPraw hzQraw
  obtain ⟨p, hzp⟩ := hzPraw
  obtain ⟨q, hzq⟩ := hzQraw
  obtain ⟨s, hsT, hsq⟩ := hQsub q.2
  have hzs : z ∈ s +ᵥ K.openCarrier := by
    rw [Tiling.AxisParallel.coordinateSwap_openCarrier] at hzq
    obtain ⟨_, ⟨k, hk, rfl⟩, heq⟩ := hzq
    refine ⟨k, hk, ?_⟩
    have := congrArg coordinateSwap heq
    simpa [vadd_eq_add, ← hsq] using this
  have hps : (p.1 : Tiling.Plane) = s := by
    by_contra hne
    have hd := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      (hPsub p.property) hsT hne
    exact Set.disjoint_left.1 hd hzp hzs
  let t : T := ⟨p.1, hPsub p.property⟩
  have htP : (t.1 : Tiling.Plane) ∈ P.centres := p.2
  have htQ : coordinateSwap t.1 ∈ Q.centres := by
    have : coordinateSwap (p.1 : Tiling.Plane) = q.1 := by rw [hps, hsq]
    simp [t, this]
  have hta : t.1.re = a := hPa htP
  have htb : t.1.im = b := by simpa using hQb htQ
  refine ⟨t, htP, htQ, ?_⟩
  have htileSub : t.1 +ᵥ K.openCarrier ⊆ X := by
    rintro w ⟨k, hk, rfl⟩
    constructor
    · refine ⟨k.re, ?_, ?_⟩
      · exact openCarrier_subset_factorProduct K hk |>.1
      · simp [vadd_eq_add, hta]
    · refine ⟨k.im, ?_, ?_⟩
      · exact openCarrier_subset_factorProduct K hk |>.2
      · simp [vadd_eq_add, htb]
  filter_upwards [hPae, hQae] with w hwP hwQ
  change (w ∈ t.1 +ᵥ K.openCarrier) =
    (w.re ∈ t.1.re +ᵥ horizontalFactor K ∧
      w.im ∈ t.1.im +ᵥ verticalFactor K)
  rw [hta, htb]
  change (w ∈ t.1 +ᵥ K.openCarrier) = (w ∈ X)
  apply propext
  constructor
  · exact fun hw ↦ htileSub hw
  · intro hwX
    have hwPs : w ∈ P.support := by rw [hPsupport, hPbase']; exact hwX.1
    have hwPr := hwP.mpr hwPs
    change w ∈ ⋃ s : P.centres, (s : Tiling.Plane) +ᵥ K.openCarrier at hwPr
    rw [Set.mem_iUnion] at hwPr
    obtain ⟨r, hwr⟩ := hwPr
    have hrt : (r.1 : Tiling.Plane) = t.1 := by
      have := hPa r.2
      have htt := hPa htP
      apply Complex.ext
      · exact this.trans htt.symm
      · have hwQs : coordinateSwap w ∈ Q.support := by
          rw [hQsupport, hQbase']
          simpa using hwX.2
        have hwQr := hwQ.mpr hwQs
        rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hwQr
        obtain ⟨rQ, hwrQ⟩ := hwQr
        obtain ⟨r0, hr0T, hr0eq⟩ := hQsub rQ.2
        have hwr0 : w ∈ r0 +ᵥ K.openCarrier := by
          rw [Tiling.AxisParallel.coordinateSwap_openCarrier] at hwrQ
          obtain ⟨_, ⟨k, hk, rfl⟩, heq⟩ := hwrQ
          refine ⟨k, hk, ?_⟩
          have := congrArg coordinateSwap heq
          simpa [vadd_eq_add, ← hr0eq] using this
        have hrr0 : (r.1 : Tiling.Plane) = r0 := by
          by_contra hne
          exact Set.disjoint_left.1
            ((isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
              (hPsub r.property) hr0T hne)
              hwr hwr0
        have hQim := hQb rQ.2
        have htQim := hQb htQ
        change rQ.1.re = b at hQim
        change (coordinateSwap t.1).re = b at htQim
        calc
          (r.1 : Tiling.Plane).im = (coordinateSwap r.1).re := rfl
          _ = rQ.1.re := by rw [hrr0, hr0eq]
          _ = (coordinateSwap t.1).re := hQim.trans htQim.symm
          _ = t.1.im := rfl
    rw [hrt] at hwr
    exact hwr

theorem productRegion_of_transverseColumns :
    ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T univ →
    ∀ (verticalColumn : Continuous.VerticalPlate K T),
      Continuous.IsVerticalColumn verticalColumn →
    ∀ (horizontalColumn : Continuous.VerticalPlate
      K.coordinateSwap (coordinateSwap '' T)),
      Continuous.IsVerticalColumn horizontalColumn →
      Tiling.AxisParallel.Structure.IsProductRegion K := by
  intro K T hTile P hP Q hQ
  obtain ⟨t, _, _, hae⟩ :=
    transverseColumns_commonCentre_aeProduct hTile P hP Q hQ
  have hrect :
      ((t.1.re +ᵥ horizontalFactor K) ×ˢ
        (t.1.im +ᵥ verticalFactor K) : Set (ℝ × ℝ)).preimage
          (fun z : Tiling.Plane => (z.re, z.im)) =
        t.1 +ᵥ factorProduct K := by
    ext z
    constructor
    · rintro ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
      refine ⟨⟨x, y⟩, ⟨hx, hy⟩, ?_⟩
      apply Complex.ext
      · simpa [vadd_eq_add] using hxz
      · simpa [vadd_eq_add] using hyz
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w.re, hw.1, by simp [vadd_eq_add]⟩,
        ⟨w.im, hw.2, by simp [vadd_eq_add]⟩⟩
  rw [hrect] at hae
  have hfactor := factorProduct_regularOpen K
  have heq : t.1 +ᵥ K.openCarrier = t.1 +ᵥ factorProduct K :=
    regularOpen_eq_of_aeEq
      (K.openCarrier_regularOpen.1.vadd t.1)
      (by rw [closure_vadd, interior_vadd, K.openCarrier_regularOpen.2])
      (hfactor.1.vadd t.1)
      (by rw [closure_vadd, interior_vadd, hfactor.2]) hae
  have hcarrier : K.openCarrier = factorProduct K := by
    ext z
    constructor
    · intro hz
      have : t.1 + z ∈ t.1 +ᵥ K.openCarrier := ⟨z, hz, by simp [vadd_eq_add]⟩
      rw [heq] at this
      obtain ⟨w, hw, hwz⟩ := this
      have : w = z := by simpa [vadd_eq_add] using add_left_cancel hwz
      simpa [this] using hw
    · intro hz
      have : t.1 + z ∈ t.1 +ᵥ factorProduct K :=
        ⟨z, hz, by simp [vadd_eq_add]⟩
      rw [← heq] at this
      obtain ⟨w, hw, hwz⟩ := this
      have : w = z := by simpa [vadd_eq_add] using add_left_cancel hwz
      simpa [this] using hw
  exact (isProductRegion_iff_regularizedProjections K).2 hcarrier

theorem productRegion_columnUnion_horizontalPeriodic :
    ∀ (K : Region), Tiling.AxisParallel.Structure.IsProductRegion K →
    ∃ beta : ℝ, 0 < beta ∧
      ∀ (T : Set Tiling.Plane), TilesOn K T univ →
        (Continuous.verticalColumnCentres K T).Nonempty →
        Tiling.RationalPolygonal.SetPeriodicBy
          (regularSupport K (Continuous.verticalColumnCentres K T)) ((beta : ℝ) : ℂ) := by
  intro K hproduct
  obtain ⟨_, _, _, _, hAfinite, hApositive, _⟩ := productFactors_geometry K
  obtain ⟨beta, hbeta, _, hcommon⟩ :=
    Tiling.AxisParallel.OneDimensional.FiniteInterval.exists_commonLinePeriod
      hAfinite hApositive
  refine ⟨beta, hbeta, ?_⟩
  intro T hTile _hcolumns
  apply columnAxisPeriod_givesColumnSupportPeriod hTile hproduct
  exact commonLinePeriod_repeatsColumnAxes hTile hproduct hbeta hcommon

end Tiling.AxisParallel.Structure
