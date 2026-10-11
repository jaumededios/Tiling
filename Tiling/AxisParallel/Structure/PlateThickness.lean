import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Foundations.GenericSlices
import Tiling.AxisParallel.Structure.HorizontalBoundaryChains
import Tiling.AxisParallel.Structure.OneSidedPlates
import Tiling.Geometry.PolygonalTopology
import Mathlib.MeasureTheory.Measure.Real

/-!
# S03 PlateThickness

This module contains the complete frozen S03 PlateThickness declarations,
including the finite noncolumn family estimate and quantitative thickness
theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Structure

open Tiling.AxisParallel

/-- The union of the one-dimensional frontiers of all vertical-plate bases. -/
def componentBoundarySet
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) : Set ℝ :=
  ⋃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T, frontier P.base

theorem componentBoundarySet_eq
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) :
    componentBoundarySet K T =
      ⋃ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        frontier P.base :=
  rfl

private def horizontalFootprint (K : Region) : Set ℝ :=
  interior (closure (Complex.re '' K.openCarrier))

private def footprintDiameter (K : Region) : ℝ :=
  Metric.diam (closure (horizontalFootprint K))

private def horizontalSlice (K : Region) (y : ℝ) : Set ℝ :=
  {x : ℝ | (x : ℂ) + (y : ℂ) * Complex.I ∈ K.openCarrier}

private structure ThinPlateSplit
    (K : Region) (T : Set Tiling.Plane)
    (P : Continuous.VerticalPlate K T) (x : ℝ) where
  leftCentres : Set Tiling.Plane
  rightCentres : Set Tiling.Plane
  left_spec : ∀ t : Tiling.Plane,
    t ∈ leftCentres ↔ t ∈ P.centres ∧
      (({t.re} : Set ℝ) + horizontalFootprint K) ⊆
        Iic (x + 2 * footprintDiameter K)
  right_spec : ∀ t : Tiling.Plane,
    t ∈ rightCentres ↔ t ∈ P.centres ∧
      (({t.re} : Set ℝ) + horizontalFootprint K) ⊆
        Ici (x + 6 * footprintDiameter K)
  left_subset : leftCentres ⊆ P.centres
  right_subset : rightCentres ⊆ P.centres
  partition : leftCentres ∪ rightCentres = P.centres
  disjoint : Disjoint leftCentres rightCentres
  left_nonempty : leftCentres.Nonempty
  right_nonempty : rightCentres.Nonempty
  left_proper : leftCentres ≠ P.centres
  right_proper : rightCentres ≠ P.centres
  leftBase : Set ℝ
  rightBase : Set ℝ
  leftBase_open : IsOpen leftBase
  rightBase_open : IsOpen rightBase
  leftBase_regular : interior (closure leftBase) = leftBase
  rightBase_regular : interior (closure rightBase) = rightBase
  left_support : regularSupport K leftCentres = Complex.re ⁻¹' leftBase
  right_support : regularSupport K rightCentres = Complex.re ⁻¹' rightBase
  leftBase_bound : leftBase ⊆ Iic (x + 2 * footprintDiameter K)
  rightBase_bound : rightBase ⊆ Ici (x + 6 * footprintDiameter K)


private theorem singleton_add_eq_vadd (a : ℝ) (S : Set ℝ) :
    ({a} : Set ℝ) + S = a +ᵥ S := by
  ext y
  constructor
  · rintro ⟨b, hb, c, hc, hbc⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_add_eq_sub]
    have hyc : y - a = c := by nlinarith [hbc]
    rwa [hyc]
  · intro hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    refine ⟨a, Set.mem_singleton a, y - a, ?_, ?_⟩
    · simpa only [vadd_eq_add, neg_add_eq_sub] using hy
    · ring

private theorem regularSupport_partition_of_horizontal_gap
    (K : Region) {P L R : Set Tiling.Plane} {X : Set ℝ} {a b : ℝ}
    (hXOpen : IsOpen X)
    (hPartition : L ∪ R = P)
    (hPSupport : regularSupport K P = Complex.re ⁻¹' X)
    (hLRaw : openUnion K L ⊆ Complex.re ⁻¹' Iic a)
    (hRRaw : openUnion K R ⊆ Complex.re ⁻¹' Ici b)
    (hab : a < b) :
    regularSupport K L = Complex.re ⁻¹' (X ∩ Iio a) ∧
      regularSupport K R = Complex.re ⁻¹' (X ∩ Ioi b) := by
  have hOpenUnionMono {A B : Set Tiling.Plane} (hAB : A ⊆ B) :
      openUnion K A ⊆ openUnion K B := by
    intro z hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz ⊢
    obtain ⟨s, hzs⟩ := hz
    exact ⟨⟨s, hAB s.2⟩, hzs⟩
  have hOpenUnionPartition :
      openUnion K P = openUnion K L ∪ openUnion K R := by
    apply Set.Subset.antisymm
    · intro z hz
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
      obtain ⟨s, hzs⟩ := hz
      have hs : (s : Tiling.Plane) ∈ L ∪ R := by
        rw [hPartition]
        exact s.2
      rcases hs with hsL | hsR
      · exact Or.inl (by
          rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
          exact ⟨⟨s, hsL⟩, hzs⟩)
      · exact Or.inr (by
          rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
          exact ⟨⟨s, hsR⟩, hzs⟩)
    · exact Set.union_subset
        (hOpenUnionMono (by rw [← hPartition]; exact subset_union_left))
        (hOpenUnionMono (by rw [← hPartition]; exact subset_union_right))
  have hLClosure :
      closure (openUnion K L) ⊆ Complex.re ⁻¹' Iic a :=
    closure_minimal hLRaw (isClosed_Iic.preimage Complex.continuous_re)
  have hRClosure :
      closure (openUnion K R) ⊆ Complex.re ⁻¹' Ici b :=
    closure_minimal hRRaw (isClosed_Ici.preimage Complex.continuous_re)
  have hLSubsetP : regularSupport K L ⊆ regularSupport K P := by
    exact interior_mono (closure_mono
      (hOpenUnionMono (by rw [← hPartition]; exact subset_union_left)))
  have hRSubsetP : regularSupport K R ⊆ regularSupport K P := by
    exact interior_mono (closure_mono
      (hOpenUnionMono (by rw [← hPartition]; exact subset_union_right)))
  have hLBound : regularSupport K L ⊆ Complex.re ⁻¹' Iio a := by
    intro z hz
    have hz' := interior_mono hLClosure hz
    simpa only [Complex.interior_preimage_re, interior_Iic] using hz'
  have hRBound : regularSupport K R ⊆ Complex.re ⁻¹' Ioi b := by
    intro z hz
    have hz' := interior_mono hRClosure hz
    simpa only [Complex.interior_preimage_re, interior_Ici] using hz'
  constructor
  · apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_preimage, Set.mem_inter_iff]
      exact ⟨show z ∈ Complex.re ⁻¹' X by rw [← hPSupport]; exact hLSubsetP hz,
        hLBound hz⟩
    · rw [Set.preimage_inter]
      apply interior_maximal
      · intro z hz
        have hzP : z ∈ closure (openUnion K P) := by
          have hzRegular : z ∈ regularSupport K P := by
            rw [hPSupport]
            exact hz.1
          exact interior_subset hzRegular
        rw [hOpenUnionPartition, closure_union] at hzP
        rcases hzP with hzL | hzR
        · exact hzL
        · have hzRight := hRClosure hzR
          exact False.elim
            ((not_lt_of_ge (show b ≤ z.re from hzRight)) (hz.2.trans hab))
      · exact hXOpen.inter isOpen_Iio |>.preimage Complex.continuous_re
  · apply Set.Subset.antisymm
    · intro z hz
      rw [Set.mem_preimage, Set.mem_inter_iff]
      exact ⟨show z ∈ Complex.re ⁻¹' X by rw [← hPSupport]; exact hRSubsetP hz,
        hRBound hz⟩
    · rw [Set.preimage_inter]
      apply interior_maximal
      · intro z hz
        have hzP : z ∈ closure (openUnion K P) := by
          have hzRegular : z ∈ regularSupport K P := by
            rw [hPSupport]
            exact hz.1
          exact interior_subset hzRegular
        rw [hOpenUnionPartition, closure_union] at hzP
        rcases hzP with hzL | hzR
        · have hzLeft := hLClosure hzL
          exact False.elim
            ((not_lt_of_ge (show z.re ≤ a from hzLeft)) (hab.trans hz.2))
        · exact hzR
      · exact hXOpen.inter isOpen_Ioi |>.preimage Complex.continuous_re

private theorem horizontalFootprint_geometry :
      ∀ K : Region,
    IsOpen (horizontalFootprint K) ∧
    interior (closure (horizontalFootprint K)) = horizontalFootprint K ∧
    (horizontalFootprint K).Nonempty ∧
    Bornology.IsBounded (horizontalFootprint K) ∧
    0 < (volume (horizontalFootprint K)).toReal ∧
    0 < footprintDiameter K ∧
    (volume (horizontalFootprint K)).toReal ≤ footprintDiameter K ∧
    ∀ x : ℝ,
      (volume (Ioo x (x + 8 * footprintDiameter K))).toReal =
        8 * footprintDiameter K := by
  intro K
  let A : Set ℝ := horizontalFootprint K
  have hCarrierOpen : IsOpen K.openCarrier := isOpen_interior
  have hCarrierNonempty : K.openCarrier.Nonempty := by
    exact K.isPolygonal.interior_nonempty K.nonempty
  have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re K.openCarrier hCarrierOpen
  have hProjectionNonempty : (Complex.re '' K.openCarrier).Nonempty :=
    hCarrierNonempty.image Complex.re
  have hCarrierBounded : Bornology.IsBounded K.openCarrier :=
    K.isPolygonal.isBounded.subset interior_subset
  have hProjectionBounded : Bornology.IsBounded (Complex.re '' K.openCarrier) :=
    RCLike.lipschitzWith_re.isBounded_image hCarrierBounded
  have hAOpen : IsOpen A := by
    simp only [A, horizontalFootprint]
    exact isOpen_interior
  have hARegular : interior (closure A) = A := by
    simp only [A, horizontalFootprint]
    exact interior_closure_idem
  have hANonempty : A.Nonempty := by
    apply hProjectionNonempty.mono
    simpa only [A, horizontalFootprint] using
      hProjectionOpen.subset_interior_closure
  have hABounded : Bornology.IsBounded A := by
    apply hProjectionBounded.closure.subset
    simpa only [A, horizontalFootprint] using
      (interior_subset : interior (closure (Complex.re '' K.openCarrier)) ⊆
        closure (Complex.re '' K.openCarrier))
  have hVolumePosENN : 0 < volume A := hAOpen.measure_pos volume hANonempty
  have hVolumeNeTop : volume A ≠ ⊤ :=
    (hABounded.measure_lt_top (μ := volume)).ne
  have hVolumePos : 0 < (volume A).toReal :=
    ENNReal.toReal_pos hVolumePosENN.ne' hVolumeNeTop
  have hANontrivial : A.Nontrivial := by
    rw [← Set.not_subsingleton_iff]
    intro hsub
    have hzero : volume A = 0 := hsub.measure_zero volume
    exact hVolumePosENN.ne' hzero
  have hDiameterPos : 0 < footprintDiameter K := by
    apply Metric.diam_pos
    · exact hANontrivial.mono subset_closure
    · simpa only [A, footprintDiameter] using hABounded.closure
  have hVolumeLeDiameter : (volume A).toReal ≤ footprintDiameter K := by
    rw [footprintDiameter, Metric.diam_closure]
    exact ENNReal.toReal_mono hABounded.ediam_ne_top (Real.volume_le_diam A)
  refine ⟨?_, ?_, hANonempty, ?_, ?_, hDiameterPos, ?_, ?_⟩
  · simpa only [A] using hAOpen
  · simpa only [A] using hARegular
  · simpa only [A] using hABounded
  · simpa only [A] using hVolumePos
  · simpa only [A] using hVolumeLeDiameter
  · intro x
    rw [Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal]
    · ring
    · nlinarith

private theorem footprint_translate_classified
    (K : Region) (t x : ℝ)
    (hAvoid :
      (t +ᵥ horizontalFootprint K) ∩
        Ioo (x + 2 * footprintDiameter K)
          (x + 6 * footprintDiameter K) = ∅) :
    t +ᵥ horizontalFootprint K ⊆
        Iic (x + 2 * footprintDiameter K) ∨
      t +ᵥ horizontalFootprint K ⊆
        Ici (x + 6 * footprintDiameter K) := by
  obtain ⟨-, -, hFootprintNonempty, hFootprintBounded, -, hDiameterPos, -, -⟩ :=
    horizontalFootprint_geometry K
  obtain ⟨u, hu⟩ := hFootprintNonempty
  have htu : t + u ∈ t +ᵥ horizontalFootprint K := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_add_eq_sub]
    convert hu using 1
    ring
  have outside (y : ℝ) (hy : y ∈ t +ᵥ horizontalFootprint K) :
      y ≤ x + 2 * footprintDiameter K ∨
        x + 6 * footprintDiameter K ≤ y := by
    by_cases hyLeft : y ≤ x + 2 * footprintDiameter K
    · exact Or.inl hyLeft
    · right
      by_contra hyRight
      have hyMiddle : y ∈ Ioo (x + 2 * footprintDiameter K)
          (x + 6 * footprintDiameter K) :=
        ⟨lt_of_not_ge hyLeft, lt_of_not_ge hyRight⟩
      have : y ∈ (∅ : Set ℝ) := by
        rw [← hAvoid]
        exact ⟨hy, hyMiddle⟩
      exact this
  have distance_bound (y z : ℝ)
      (hy : y ∈ t +ᵥ horizontalFootprint K)
      (hz : z ∈ t +ᵥ horizontalFootprint K) :
      dist y z ≤ footprintDiameter K := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy hz
    have hdist := Metric.dist_le_diam_of_mem hFootprintBounded.closure
      (subset_closure hy) (subset_closure hz)
    simpa only [vadd_eq_add, neg_add_eq_sub, dist_sub_right,
      footprintDiameter] using hdist
  rcases outside (t + u) htu with hLeft | hRight
  · left
    intro y hy
    rcases outside y hy with hyLeft | hyRight
    · exact hyLeft
    · have hdist := distance_bound (t + u) y htu hy
      rw [Real.dist_eq, abs_of_nonpos] at hdist
      · nlinarith
      · nlinarith
  · right
    intro y hy
    rcases outside y hy with hyLeft | hyRight
    · have hdist := distance_bound y (t + u) hy htu
      rw [Real.dist_eq, abs_of_nonpos] at hdist
      · nlinarith
      · nlinarith
    · exact hyRight

private theorem base_regular_of_regularSupport_eq_preimage
    (K : Region) (S : Set Tiling.Plane) (X : Set ℝ)
    (hSupport : regularSupport K S = Complex.re ⁻¹' X) :
    interior (closure X) = X := by
  have hPreimage :
      Complex.re ⁻¹' interior (closure X) = Complex.re ⁻¹' X := by
    calc
      Complex.re ⁻¹' interior (closure X) =
          interior (closure (Complex.re ⁻¹' X)) := by
        rw [Complex.closure_preimage_re, Complex.interior_preimage_re]
      _ = interior (closure (regularSupport K S)) := by rw [hSupport]
      _ = regularSupport K S := (regularSupport_isRegularOpen K S).2
      _ = Complex.re ⁻¹' X := hSupport
  apply (Set.preimage_injective.mpr ?_) hPreimage
  intro r
  exact ⟨(r : ℂ), by simp⟩

private theorem plateCentre_footprint_subset_base :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T) (t : Tiling.Plane),
      t ∈ P.centres →
        (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ P.base := by
  intro K T hTile P t ht r hr
  obtain ⟨hBaseRegular, hSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hOpenUnion : IsOpen (openUnion K P.centres) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
    exact isOpen_iUnion fun q : P.centres ↦
      (Homeomorph.addLeft (q : Tiling.Plane)).isOpenMap _ isOpen_interior
  have hRawShift : t.re +ᵥ (Complex.re '' K.openCarrier) ⊆ P.base := by
    intro y hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hy
    obtain ⟨w, hw, hwre⟩ := hy
    have htwOpen : t + w ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      refine ⟨⟨t, ht⟩, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa only [vadd_eq_add, neg_add_cancel_left] using hw
    have htwSupport : t + w ∈ P.support := by
      rw [Continuous.VerticalPlate.support_eq_regularSupport, regularSupport]
      exact hOpenUnion.subset_interior_closure htwOpen
    rw [hSupport] at htwSupport
    have htre : y = (t + w).re := by
      rw [Complex.add_re]
      simp only [vadd_eq_add, neg_add_eq_sub] at hwre
      nlinarith [hwre]
    rwa [Set.mem_preimage, ← htre] at htwSupport
  have hr' : r ∈ t.re +ᵥ horizontalFootprint K := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    rcases hr with ⟨a, ha, b, hb, hab⟩
    rw [Set.mem_singleton_iff] at ha
    subst a
    simp only [vadd_eq_add, neg_add_eq_sub]
    have hrb : r - t.re = b := by nlinarith [hab]
    rwa [hrb]
  rw [hBaseRegular]
  apply interior_mono (closure_mono hRawShift)
  rw [closure_vadd, interior_vadd]
  simpa only [horizontalFootprint] using hr'

private theorem centralBasePoint_hasFootprintWitness :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T) (x z : ℝ),
      z ∈ P.base ∩
        Ioo (x + 2 * footprintDiameter K) (x + 6 * footprintDiameter K) →
      ∃ t : Tiling.Plane,
        t ∈ P.centres ∧
        (({t.re} : Set ℝ) + horizontalFootprint K) ⊆
          P.base ∩ Ioo x (x + 8 * footprintDiameter K) := by
  intro K T hTile P x z hz
  obtain ⟨-, -, -, hFootprintBounded, -, hDiameterPos, -, -⟩ :=
    horizontalFootprint_geometry K
  obtain ⟨-, hSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hCentres : P.centres ⊆ T := by
    rintro s ⟨q, -, rfl⟩
    exact q.2
  have hPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (isPacking_iff_openCarrier_disjoint K P.centres).mpr
    exact fun s hs t ht hst ↦
      (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hCentres hs) (hCentres ht) hst
  let q : Tiling.Plane := ⟨z, 0⟩
  have hqSupport : q ∈ P.support := by
    rw [hSupport]
    exact hz.1
  have hqClosure : q ∈ closure (openUnion K P.centres) := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport, regularSupport] at hqSupport
    exact interior_subset hqSupport
  rw [closure_openUnion_eq_iUnion_support hPacking] at hqClosure
  obtain ⟨t, hqt⟩ := Set.mem_iUnion.mp hqClosure
  refine ⟨t, t.2, ?_⟩
  intro y hy
  refine ⟨plateCentre_footprint_subset_base hTile P t t.2 hy, ?_⟩
  have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re K.openCarrier isOpen_interior
  have hClosureFootprint :
      closure (horizontalFootprint K) = closure (Complex.re '' K.openCarrier) := by
    apply Set.Subset.antisymm
    · rw [horizontalFootprint]
      simpa only [closure_closure] using
        closure_mono (interior_subset :
          interior (closure (Complex.re '' K.openCarrier)) ⊆
            closure (Complex.re '' K.openCarrier))
    · exact closure_mono hProjectionOpen.subset_interior_closure
  rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hqt
  have hTileClosure : -t.1 +ᵥ q ∈ closure K.openCarrier := by
    rw [show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
    exact hqt
  have hProjectedClosure : (-t.1 +ᵥ q).re ∈
      closure (Complex.re '' K.openCarrier) := by
    exact image_closure_subset_closure_image Complex.continuous_re
      ⟨-t.1 +ᵥ q, hTileClosure, rfl⟩
  have hzClosure : z - t.1.re ∈ closure (horizontalFootprint K) := by
    rw [hClosureFootprint]
    convert hProjectedClosure using 1
    simp [q, vadd_eq_add]
    ring
  have hyShift : y - t.1.re ∈ horizontalFootprint K := by
    rcases hy with ⟨a, ha, b, hb, hab⟩
    rw [Set.mem_singleton_iff] at ha
    subst a
    have hyb : y - t.1.re = b := by nlinarith [hab]
    rwa [hyb]
  have hdist : dist (y - t.1.re) (z - t.1.re) ≤ footprintDiameter K := by
    simpa only [footprintDiameter] using
      Metric.dist_le_diam_of_mem hFootprintBounded.closure
        (subset_closure hyShift) hzClosure
  rw [Real.dist_eq] at hdist
  have habs : |y - z| ≤ footprintDiameter K := by
    convert hdist using 1
    congr 1
    ring
  obtain ⟨hlower, hupper⟩ := abs_le.mp habs
  constructor <;> nlinarith [hz.2.1, hz.2.2, hDiameterPos]

private theorem thinBase_centralStrip_empty :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T) (x : ℝ),
      (volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K))).toReal ≤
        (1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal →
      P.base ∩
        Ioo (x + 2 * footprintDiameter K) (x + 6 * footprintDiameter K) = ∅ := by
  intro K T hTile P x hThin
  by_contra hne
  have hMiddleNonempty :
      (P.base ∩ Ioo (x + 2 * footprintDiameter K)
        (x + 6 * footprintDiameter K)).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨z, hz⟩ := hMiddleNonempty
  obtain ⟨t, ht, hTranslateSubset⟩ :=
    centralBasePoint_hasFootprintWitness hTile P x z hz
  have hWindowBounded : Bornology.IsBounded
      (P.base ∩ Ioo x (x + 8 * footprintDiameter K)) :=
    (Metric.isBounded_Ioo x (x + 8 * footprintDiameter K)).subset inter_subset_right
  have hMeasureMono :
      volume (({t.re} : Set ℝ) + horizontalFootprint K) ≤
        volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K)) :=
    measure_mono hTranslateSubset
  have hToRealMono :
      (volume (({t.re} : Set ℝ) + horizontalFootprint K)).toReal ≤
        (volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K))).toReal :=
    ENNReal.toReal_mono
      (hWindowBounded.measure_lt_top (μ := volume)).ne hMeasureMono
  have hTranslateMeasure :
      volume (({t.re} : Set ℝ) + horizontalFootprint K) =
        volume (horizontalFootprint K) := by
    rw [singleton_add_eq_vadd, MeasureTheory.measure_vadd]
  rw [hTranslateMeasure] at hToRealMono
  have hFootprintPositive :
      0 < (volume (horizontalFootprint K)).toReal :=
    (horizontalFootprint_geometry K).2.2.2.2.1
  nlinarith

private theorem thinNoncolumnPlate_constructsProperSlabSplit
    (oneSidedColumn :
      ∀ {K : Region} {T : Set Tiling.Plane},
        TilesOn K T Set.univ →
        ∀ (P : Continuous.VerticalPlate K T),
          (BddBelow P.base ∨ BddAbove P.base) →
            Continuous.IsVerticalColumn P) :
    ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T),
      ¬ Continuous.IsVerticalColumn P →
      ∀ x : ℝ,
        (volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K))).toReal ≤
          (1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal →
        Nonempty (ThinPlateSplit K T P x) := by
  intro K T hTile P hNoncolumn x hThin
  let D : ℝ := footprintDiameter K
  let a : ℝ := x + 2 * D
  let b : ℝ := x + 6 * D
  let L : Set Tiling.Plane :=
    {t | t ∈ P.centres ∧
      (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ Iic a}
  let R : Set Tiling.Plane :=
    {t | t ∈ P.centres ∧
      (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ Ici b}
  obtain ⟨hFootprintOpen, -, hFootprintNonempty, -, -, hDPos, -, -⟩ :=
    horizontalFootprint_geometry K
  have hab : a < b := by
    simp only [a, b, D]
    nlinarith
  have hMiddleEmpty : P.base ∩ Ioo a b = ∅ := by
    simpa only [a, b, D] using
      thinBase_centralStrip_empty hTile P x hThin
  have hClassify (t : Tiling.Plane) (ht : t ∈ P.centres) :
      (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ Iic a ∨
        (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ Ici b := by
    have hTranslateBase := plateCentre_footprint_subset_base hTile P t ht
    have hAvoid :
        (t.re +ᵥ horizontalFootprint K) ∩ Ioo a b = ∅ := by
      apply Set.Subset.antisymm
      · intro y hy
        have hyEmpty : y ∈ P.base ∩ Ioo a b := by
          refine ⟨hTranslateBase ?_, hy.2⟩
          rw [singleton_add_eq_vadd]
          exact hy.1
        rw [hMiddleEmpty] at hyEmpty
        exact hyEmpty
      · exact empty_subset _
    simpa only [singleton_add_eq_vadd, a, b, D] using
      footprint_translate_classified K t.re x hAvoid
  have hLSubset : L ⊆ P.centres := fun _ ht ↦ ht.1
  have hRSubset : R ⊆ P.centres := fun _ ht ↦ ht.1
  have hPartition : L ∪ R = P.centres := by
    apply Set.Subset.antisymm
    · exact Set.union_subset hLSubset hRSubset
    · intro t ht
      rcases hClassify t ht with hLeft | hRight
      · exact Or.inl ⟨ht, hLeft⟩
      · exact Or.inr ⟨ht, hRight⟩
  have hDisjoint : Disjoint L R := by
    rw [Set.disjoint_left]
    intro t htL htR
    obtain ⟨u, hu⟩ := hFootprintNonempty
    have htu : t.re + u ∈ ({t.re} : Set ℝ) + horizontalFootprint K :=
      ⟨t.re, Set.mem_singleton _, u, hu, rfl⟩
    have hLeft := htL.2 htu
    have hRight := htR.2 htu
    exact (not_lt_of_ge (hRight.trans hLeft)) hab
  have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
    Complex.isOpenMap_re K.openCarrier isOpen_interior
  have hRawSide
      (S : Set Tiling.Plane) (hS : S ⊆ P.centres)
      (hSide : ∀ t ∈ S,
        (({t.re} : Set ℝ) + horizontalFootprint K) ⊆ Iic a) :
      openUnion K S ⊆ Complex.re ⁻¹' Iic a := by
    intro z hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
    obtain ⟨t, hzt⟩ := hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
    have hProjected : (-t.1 +ᵥ z).re ∈ Complex.re '' K.openCarrier :=
      ⟨-t.1 +ᵥ z, hzt, rfl⟩
    have hProjectedFootprint :
        (-t.1 +ᵥ z).re ∈ horizontalFootprint K := by
      exact hProjectionOpen.subset_interior_closure hProjected
    have hzTranslate :
        z.re ∈ ({t.1.re} : Set ℝ) + horizontalFootprint K := by
      rw [singleton_add_eq_vadd, Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa only [vadd_eq_add, neg_add_eq_sub, Complex.sub_re] using
        hProjectedFootprint
    exact hSide t.1 t.2 hzTranslate
  have hLRaw : openUnion K L ⊆ Complex.re ⁻¹' Iic a :=
    hRawSide L hLSubset (fun _ ht ↦ ht.2)
  have hRRaw : openUnion K R ⊆ Complex.re ⁻¹' Ici b := by
    intro z hz
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz
    obtain ⟨t, hzt⟩ := hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzt
    have hProjected : (-t.1 +ᵥ z).re ∈ Complex.re '' K.openCarrier :=
      ⟨-t.1 +ᵥ z, hzt, rfl⟩
    have hProjectedFootprint :
        (-t.1 +ᵥ z).re ∈ horizontalFootprint K :=
      hProjectionOpen.subset_interior_closure hProjected
    have hzTranslate :
        z.re ∈ ({t.1.re} : Set ℝ) + horizontalFootprint K := by
      rw [singleton_add_eq_vadd, Set.mem_vadd_set_iff_neg_vadd_mem]
      simpa only [vadd_eq_add, neg_add_eq_sub, Complex.sub_re] using
        hProjectedFootprint
    exact t.2.2 hzTranslate
  obtain ⟨hPRegular, hPSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hPBaseOpen : IsOpen P.base := by
    rw [hPRegular]
    exact isOpen_interior
  have hPSupport' : regularSupport K P.centres = Complex.re ⁻¹' P.base := by
    simpa only [Continuous.VerticalPlate.support_eq_regularSupport] using hPSupport
  obtain ⟨hLSupport, hRSupport⟩ :=
    regularSupport_partition_of_horizontal_gap K hPBaseOpen hPartition
      hPSupport' hLRaw hRRaw hab
  let leftBase : Set ℝ := P.base ∩ Iio a
  let rightBase : Set ℝ := P.base ∩ Ioi b
  have hLeftBaseOpen : IsOpen leftBase := hPBaseOpen.inter isOpen_Iio
  have hRightBaseOpen : IsOpen rightBase := hPBaseOpen.inter isOpen_Ioi
  have hLSupport' : regularSupport K L = Complex.re ⁻¹' leftBase := by
    simpa only [leftBase] using hLSupport
  have hRSupport' : regularSupport K R = Complex.re ⁻¹' rightBase := by
    simpa only [rightBase] using hRSupport
  have hLeftBaseRegular : interior (closure leftBase) = leftBase :=
    base_regular_of_regularSupport_eq_preimage K L leftBase hLSupport'
  have hRightBaseRegular : interior (closure rightBase) = rightBase :=
    base_regular_of_regularSupport_eq_preimage K R rightBase hRSupport'
  have hLNonempty : L.Nonempty := by
    by_contra hLNot
    have hLEmpty : L = ∅ := not_nonempty_iff_eq_empty.mp hLNot
    have hRP : R = P.centres := by
      have := hPartition
      rwa [hLEmpty, empty_union] at this
    have hBaseEq : P.base = rightBase := by
      apply (Set.preimage_injective.mpr ?_)
      · calc
          Complex.re ⁻¹' P.base = regularSupport K P.centres := hPSupport'.symm
          _ = regularSupport K R := by rw [hRP]
          _ = Complex.re ⁻¹' rightBase := hRSupport'
      · intro r
        exact ⟨(r : ℂ), by simp⟩
    have hBddBelow : BddBelow P.base := by
      refine ⟨b, ?_⟩
      intro y hy
      have hyRight : y ∈ rightBase := by rwa [← hBaseEq]
      exact hyRight.2.le
    exact hNoncolumn (oneSidedColumn hTile P (Or.inl hBddBelow))
  have hRNonempty : R.Nonempty := by
    by_contra hRNot
    have hREmpty : R = ∅ := not_nonempty_iff_eq_empty.mp hRNot
    have hLP : L = P.centres := by
      have := hPartition
      rwa [hREmpty, union_empty] at this
    have hBaseEq : P.base = leftBase := by
      apply (Set.preimage_injective.mpr ?_)
      · calc
          Complex.re ⁻¹' P.base = regularSupport K P.centres := hPSupport'.symm
          _ = regularSupport K L := by rw [hLP]
          _ = Complex.re ⁻¹' leftBase := hLSupport'
      · intro r
        exact ⟨(r : ℂ), by simp⟩
    have hBddAbove : BddAbove P.base := by
      refine ⟨a, ?_⟩
      intro y hy
      have hyLeft : y ∈ leftBase := by rwa [← hBaseEq]
      exact hyLeft.2.le
    exact hNoncolumn (oneSidedColumn hTile P (Or.inr hBddAbove))
  have hLProper : L ≠ P.centres := by
    intro hEq
    obtain ⟨t, htR⟩ := hRNonempty
    have htL : t ∈ L := by rw [hEq]; exact hRSubset htR
    exact Set.disjoint_left.mp hDisjoint htL htR
  have hRProper : R ≠ P.centres := by
    intro hEq
    obtain ⟨t, htL⟩ := hLNonempty
    have htR : t ∈ R := by rw [hEq]; exact hLSubset htL
    exact Set.disjoint_left.mp hDisjoint htL htR
  refine ⟨{
    leftCentres := L
    rightCentres := R
    left_spec := ?_
    right_spec := ?_
    left_subset := hLSubset
    right_subset := hRSubset
    partition := hPartition
    disjoint := hDisjoint
    left_nonempty := hLNonempty
    right_nonempty := hRNonempty
    left_proper := hLProper
    right_proper := hRProper
    leftBase := leftBase
    rightBase := rightBase
    leftBase_open := hLeftBaseOpen
    rightBase_open := hRightBaseOpen
    leftBase_regular := hLeftBaseRegular
    rightBase_regular := hRightBaseRegular
    left_support := hLSupport'
    right_support := hRSupport'
    leftBase_bound := ?_
    rightBase_bound := ?_ }⟩
  · intro t
    rfl
  · intro t
    rfl
  · intro y hy
    exact (show y < a from hy.2).le
  · intro y hy
    exact (show b < y from hy.2).le

private theorem thinPlateSplit_contradictsMinimality :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T) (x : ℝ),
      ThinPlateSplit K T P x → False := by
  intro K T hTile P x S
  have hMinimal := Continuous.VerticalPlate.minimal hTile P
  have hEq : S.leftCentres = P.centres :=
    hMinimal.2.2.2 S.leftCentres S.left_nonempty S.left_subset
      ⟨S.leftBase, S.leftBase_regular.symm, S.left_support⟩
  exact S.left_proper hEq

theorem noncolumnPlate_thickness :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ (P : Continuous.VerticalPlate K T),
      ¬ Continuous.IsVerticalColumn P →
      ∀ x : ℝ,
        (1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal <
          (volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K))).toReal := by
  intro K T hTile P hNoncolumn x
  by_contra hNot
  have hThin :
      (volume (P.base ∩ Ioo x (x + 8 * footprintDiameter K))).toReal ≤
        (1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal :=
    le_of_not_gt hNot
  obtain ⟨split⟩ := thinNoncolumnPlate_constructsProperSlabSplit
    Continuous.VerticalPlate.isColumn_of_oneSidedBase hTile P hNoncolumn x hThin
  exact thinPlateSplit_contradictsMinimality hTile P x split

private theorem verticalPlateBases_pairwiseDisjoint :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ P Q : Continuous.VerticalPlate K T,
      P ≠ Q → Disjoint P.base Q.base := by
  intro K T hTile P Q hPQ
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (Continuous.VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ Continuous.VerticalPlate.ofCentre (K := K) t)
    intro R
    obtain ⟨r, hr⟩ := R.nonempty_supp
    refine ⟨r, ?_⟩
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff R r).1 hr
  have hSupportDisjoint : Disjoint P.support Q.support := by
    have hPartition := regularSupport_pairwiseDisjoint
      (@Continuous.VerticalPlate.centres K T)
      (Continuous.verticalPlateCentres_pairwiseDisjoint K T)
      (Continuous.iUnion_verticalPlateCentres K T) hTile
    exact hPartition.1 (Set.mem_univ P) (Set.mem_univ Q) hPQ
  obtain ⟨-, hPSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  obtain ⟨-, hQSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile Q
  rw [Set.disjoint_left]
  intro z hzP hzQ
  let q : Tiling.Plane := ⟨z, 0⟩
  have hqP : q ∈ P.support := by
    rw [hPSupport]
    exact hzP
  have hqQ : q ∈ Q.support := by
    rw [hQSupport]
    exact hzQ
  exact Set.disjoint_left.mp hSupportDisjoint hqP hqQ

private theorem finiteNoncolumnPlateFamily_card_bound :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    ∀ F : Finset (Continuous.VerticalPlate K T),
      (∀ P ∈ F, ¬ Continuous.IsVerticalColumn P) →
      (F.card : ℝ) * (volume (horizontalFootprint K)).toReal <
        16 * footprintDiameter K := by
  intro K T hTile F hNoncolumn
  obtain ⟨-, -, -, -, hFootprintPos, hDiameterPos, -, hWindowMeasure⟩ :=
    horizontalFootprint_geometry K
  by_cases hFNonempty : F.Nonempty
  · let W : Set ℝ := Ioo 0 (0 + 8 * footprintDiameter K)
    let f : Continuous.VerticalPlate K T → Set ℝ := fun P ↦ P.base ∩ W
    have hPairwise : Set.Pairwise (↑F) (fun P Q ↦ Disjoint (f P) (f Q)) := by
      intro P hPF Q hQF hPQ
      rw [Set.disjoint_left]
      intro y hyP hyQ
      exact Set.disjoint_left.mp
        (verticalPlateBases_pairwiseDisjoint hTile P Q hPQ) hyP.1 hyQ.1
    have hMeasurable : ∀ P ∈ F, MeasurableSet (f P) := by
      intro P hPF
      obtain ⟨hPRegular, -⟩ :=
        Continuous.VerticalPlate.support_isVerticalSlab hTile P
      have hPBaseOpen : IsOpen P.base := by
        rw [hPRegular]
        exact isOpen_interior
      exact (hPBaseOpen.inter isOpen_Ioo).measurableSet
    have hEachFinite : ∀ P ∈ F, volume (f P) ≠ ⊤ := by
      intro P hPF
      apply ne_of_lt
      apply lt_of_le_of_lt (measure_mono inter_subset_right)
      exact (Metric.isBounded_Ioo 0
        (0 + 8 * footprintDiameter K)).measure_lt_top
    have hMeasureEq :
        (volume (⋃ P ∈ F, f P)).toReal =
          ∑ P ∈ F, (volume (f P)).toReal := by
      simpa only [MeasureTheory.measureReal_def] using
        (MeasureTheory.measureReal_biUnion_finset (μ := volume)
          hPairwise hMeasurable hEachFinite)
    have hUnionSubset : (⋃ P ∈ F, f P) ⊆ W := by
      intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨P, hy⟩ := hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨hPF, hy⟩ := hy
      exact hy.2
    have hWindowFinite : volume W ≠ ⊤ :=
      (Metric.isBounded_Ioo 0
        (0 + 8 * footprintDiameter K)).measure_lt_top.ne
    have hUnionLe :
        (volume (⋃ P ∈ F, f P)).toReal ≤ (volume W).toReal :=
      ENNReal.toReal_mono hWindowFinite (measure_mono hUnionSubset)
    have hEach (P : Continuous.VerticalPlate K T) (hPF : P ∈ F) :
        (1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal <
          (volume (f P)).toReal := by
      simpa only [f, W, zero_add] using
        noncolumnPlate_thickness hTile P (hNoncolumn P hPF) 0
    have hSumLower :
        ∑ P ∈ F,
            ((1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal) <
          ∑ P ∈ F, (volume (f P)).toReal :=
      Finset.sum_lt_sum_of_nonempty hFNonempty hEach
    have hWindowEq : (volume W).toReal = 8 * footprintDiameter K := by
      simpa only [W, zero_add] using hWindowMeasure 0
    rw [← hMeasureEq] at hSumLower
    rw [hWindowEq] at hUnionLe
    have hCore :
        (F.card : ℝ) *
            ((1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal) <
          8 * footprintDiameter K := by
      calc
        (F.card : ℝ) *
            ((1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal) =
            ∑ _P ∈ F,
              ((1 / 2 : ℝ) * (volume (horizontalFootprint K)).toReal) := by
                simp
        _ < (volume (⋃ P ∈ F, f P)).toReal := hSumLower
        _ ≤ 8 * footprintDiameter K := hUnionLe
    nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hFNonempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    nlinarith

private theorem setFinite_of_finset_card_lt_real :
      ∀ {α : Type*} (S : Set α) (B : ℝ),
    (∀ F : Finset α, (F : Set α) ⊆ S → (F.card : ℝ) < B) →
      S.Finite := by
  intro α S B hBound
  by_contra hInfinite
  have hSInfinite : S.Infinite := hInfinite
  obtain ⟨n : ℕ, hn⟩ := exists_nat_gt B
  obtain ⟨F, hFS, hFcard⟩ := hSInfinite.exists_subset_card_eq n
  have hFB := hBound F hFS
  rw [hFcard] at hFB
  exact (not_lt_of_ge hn.le) hFB

theorem noncolumnVerticalPlates_finite :
      ∀ {K : Region} {T : Set Tiling.Plane},
    TilesOn K T Set.univ →
    (Continuous.nonColumnVerticalPlates K T).Finite ∧
      ((Continuous.nonColumnVerticalPlates K T).ncard : ℝ) *
          (volume (horizontalFootprint K)).toReal <
        16 * footprintDiameter K := by
  intro K T hTile
  let S : Set (Continuous.VerticalPlate K T) :=
    Continuous.nonColumnVerticalPlates K T
  obtain ⟨-, -, -, -, hFootprintPos, -, -, -⟩ :=
    horizontalFootprint_geometry K
  have hFinite : S.Finite := by
    apply setFinite_of_finset_card_lt_real S
      (16 * footprintDiameter K /
        (volume (horizontalFootprint K)).toReal)
    intro F hFS
    have hNoncolumn : ∀ P ∈ F, ¬ Continuous.IsVerticalColumn P := by
      intro P hPF
      exact hFS hPF
    have hBound := finiteNoncolumnPlateFamily_card_bound hTile F hNoncolumn
    exact (lt_div_iff₀ hFootprintPos).2 (by
      simpa only [mul_comm] using hBound)
  refine ⟨hFinite, ?_⟩
  have hBound := finiteNoncolumnPlateFamily_card_bound hTile hFinite.toFinset
    (by
      intro P hP
      exact (Set.Finite.mem_toFinset hFinite).mp hP)
  change (S.ncard : ℝ) * (volume (horizontalFootprint K)).toReal <
    16 * footprintDiameter K
  rw [Set.ncard_eq_toFinset_card S hFinite]
  exact hBound

private theorem horizontalStepAlphabet_hasPositiveLowerBound :
    ∀ K : Region, ∃ rho : ℝ, 0 < rho ∧
      ∀ d ∈ K.horizontalStepAlphabet, rho ≤ d := by
  intro K
  let rho : ℝ := K.horizontalStepAlphabet.min'
    (K.horizontalStepAlphabet_nonempty)
  refine ⟨rho, ?_, ?_⟩
  · exact K.horizontalStepAlphabet_pos
      (K.horizontalStepAlphabet.min'_mem K.horizontalStepAlphabet_nonempty)
  · intro d hd
    exact K.horizontalStepAlphabet.min'_le d hd

private theorem boundedWindowFinite_isClosed :
    ∀ S : Set ℝ,
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (S ∩ Q).Finite) → IsClosed S := by
  intro S hLocal
  apply isClosed_of_closure_subset
  intro x hx
  let Q : Set ℝ := Metric.closedBall x 1
  have hQBounded : Bornology.IsBounded Q := Metric.isBounded_closedBall
  have hFinite : (S ∩ Q).Finite := hLocal Q hQBounded
  have hxLocalClosure : x ∈ closure (S ∩ Q) := by
    rw [Metric.mem_closure_iff]
    intro epsilon hEpsilon
    have hRadius : 0 < min epsilon (1 / 2 : ℝ) :=
      lt_min hEpsilon (by norm_num)
    obtain ⟨y, hyS, hxy⟩ :=
      Metric.mem_closure_iff.mp hx (min epsilon (1 / 2 : ℝ)) hRadius
    refine ⟨y, ⟨hyS, ?_⟩, hxy.trans_le (min_le_left _ _)⟩
    change y ∈ Metric.closedBall x 1
    rw [Metric.mem_closedBall]
    rw [dist_comm]
    exact hxy.le.trans (by
      calc
        min epsilon (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
        _ ≤ 1 := by norm_num)
  rw [hFinite.isClosed.closure_eq] at hxLocalClosure
  exact hxLocalClosure.1

private theorem trivialDecomposition_componentBoundarySet_empty :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      componentBoundarySet K T = ∅ := by
  intro K T hTile
  rintro ⟨P, -, hPT⟩
  have hWholeSupport : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
  have hPSupport : P.support = Set.univ := by
    rw [Continuous.VerticalPlate.support_eq_regularSupport, hPT, hWholeSupport]
  have hPBase : P.base = Set.univ := by
    rw [Continuous.VerticalPlate.base_eq, hPSupport]
    simpa only [Set.image_univ] using Complex.range_re
  have hAllPlates (Q : Continuous.VerticalPlate K T) : Q = P := by
    obtain ⟨q, hq⟩ := Q.nonempty_supp
    have hqP : (q : Tiling.Plane) ∈ P.centres := by
      rw [hPT]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := hqP
    have hpqSubtype : p = q := Subtype.ext hpq
    subst p
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex hq hp
  rw [componentBoundarySet_eq]
  simp_rw [hAllPlates]
  simp only [hPBase, frontier_univ, iUnion_empty]


private theorem segment_re_eq_of_mem
    {a b z : Tiling.Plane} (hab : a.re = b.re)
    (hz : z ∈ segment ℝ a b) : z.re = a.re := by
  rw [segment_eq_image] at hz
  obtain ⟨r, _hr, rfl⟩ := hz
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  rw [hab]
  ring

private theorem segment_im_eq_of_mem
    {a b z : Tiling.Plane} (hab : a.im = b.im)
    (hz : z ∈ segment ℝ a b) : z.im = a.im := by
  rw [segment_eq_image] at hz
  obtain ⟨r, _hr, rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  rw [hab]
  ring

private theorem componentBoundary_hasTranslatedVerticalEdge :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      (¬ ∃ P : Continuous.VerticalPlate K T,
        ¬ Continuous.IsVerticalColumn P ∧ P.centres = T) →
      ∀ c ∈ componentBoundarySet K T,
        ∃ (P : Continuous.VerticalPlate K T) (t : ↥T)
          (v w : ↥K.vertices),
          c ∈ frontier P.base ∧
          (t.1 : Tiling.Plane) ∈ P.centres ∧
          v.1 ≠ w.1 ∧ v.1.re = w.1.re ∧
          c = v.1.re + t.1.re ∧
          openSegment ℝ (t.1 + v.1) (t.1 + w.1) ⊆
            frontier (t.1 +ᵥ K.support) := by
  intro K T hTile _hNontrivial c hc
  rw [componentBoundarySet_eq] at hc
  obtain ⟨P, hcP⟩ := Set.mem_iUnion.mp hc
  let _ : Countable T := hTile.1.to_subtype
  have hVerticesFinite : K.vertices.Finite := by
    simpa only [Region.vertices] using K.isPolygonal.vertexSet_finite
  let _ : Countable (↑K.vertices) :=
    hVerticesFinite.countable.to_subtype
  let forbidden : Set ℝ :=
    Set.range fun p : T × ↑K.vertices ↦ p.1.1.im + p.2.1.im
  have hForbiddenCountable : forbidden.Countable := Set.countable_range _
  have hForbiddenNe : forbidden ≠ Set.univ := by
    intro hEq
    apply Cardinal.not_countable_real
    rw [← hEq]
    exact hForbiddenCountable
  obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem forbidden).mp hForbiddenNe
  let q : Tiling.Plane := ⟨c, y⟩
  obtain ⟨-, hPSupport⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hqFrontier : q ∈ frontier P.support := by
    rw [hPSupport]
    change q ∈ frontier ({z : Tiling.Plane | z.re ∈ P.base} : Set Tiling.Plane)
    rw [Tiling.AxisParallel.frontier_verticalCylinder]
    exact hcP
  have hCentresSubset : P.centres ⊆ T := by
    rintro s ⟨t, -, rfl⟩
    exact t.2
  have hPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements P.centres) := by
    apply (isPacking_iff_openCarrier_disjoint K P.centres).mpr
    exact fun s hs t ht hst ↦
      (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
        (hCentresSubset hs) (hCentresSubset ht) hst
  have hqClosure : q ∈ closure (openUnion K P.centres) := by
    have hqSupportClosure : q ∈ closure P.support :=
      frontier_subset_closure hqFrontier
    rw [Continuous.VerticalPlate.support_eq_regularSupport,
      regularSupport] at hqSupportClosure
    simpa only [closure_closure] using
      closure_mono (interior_subset :
        interior (closure (openUnion K P.centres)) ⊆
          closure (openUnion K P.centres)) hqSupportClosure
  rw [closure_openUnion_eq_iUnion_support hPacking] at hqClosure
  obtain ⟨s, hqs⟩ := Set.mem_iUnion.mp hqClosure
  obtain ⟨t, htP, hts⟩ := s.2
  let p : Tiling.Plane := q - s.1
  have hqp : q = s.1 + p := by simp [p]
  have hpSupport : p ∈ K.support := by
    simpa [p, Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg,
      add_comm] using hqs
  have hpNotInterior : p ∉ interior K.support := by
    intro hpInterior
    have hqOpen : q ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
      refine ⟨s, ?_⟩
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change -s.1 + q ∈ interior K.support
      simpa only [hqp, neg_add_cancel_left] using hpInterior
    have hOpenUnion : IsOpen (openUnion K P.centres) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact isOpen_iUnion fun r : P.centres ↦
        (Homeomorph.addLeft (r : Tiling.Plane)).isOpenMap _ isOpen_interior
    have hqPlateSupport : q ∈ P.support := by
      rw [Continuous.VerticalPlate.support_eq_regularSupport, regularSupport]
      exact hOpenUnion.subset_interior_closure hqOpen
    have hPSupportOpen : IsOpen P.support := by
      rw [Continuous.VerticalPlate.support_eq_regularSupport]
      exact isOpen_interior
    have hqInterior : q ∈ interior P.support := by
      rwa [hPSupportOpen.interior_eq]
    exact hqFrontier.2 hqInterior
  have hpFrontier : p ∈ frontier K.support := by
    rw [K.isPolygonal.isClosed.frontier_eq]
    exact ⟨hpSupport, hpNotInterior⟩
  have hpNotVertex : p ∉ K.vertices := by
    intro hpVertex
    apply hy
    refine ⟨(t, ⟨p, hpVertex⟩), ?_⟩
    have him := congrArg Complex.im hqp
    have htsIm := congrArg Complex.im hts
    simp only [q, Complex.add_im] at him
    linarith
  obtain ⟨axis, v, w, hvw, hTransverse, hpSegment, hEdge⟩ :=
    Tiling.AxisParallel.IntrinsicVertices.nonvertexFrontier_mem_intrinsicEdge K p
      hpFrontier hpNotVertex
  cases axis with
  | horizontal =>
      have hvwIm : v.1.im = w.1.im := hTransverse
      have hpIm : p.im = v.1.im :=
        segment_im_eq_of_mem hvwIm
          (openSegment_subset_segment ℝ v.1 w.1 hpSegment)
      exfalso
      apply hy
      refine ⟨(t, v), ?_⟩
      have him := congrArg Complex.im hqp
      have htsIm := congrArg Complex.im hts
      simp only [q, Complex.add_im] at him
      linarith
  | vertical =>
      have hvwRe : v.1.re = w.1.re := hTransverse
      have hpRe : p.re = v.1.re :=
        segment_re_eq_of_mem hvwRe
          (openSegment_subset_segment ℝ v.1 w.1 hpSegment)
      have htCentre : (t.1 : Tiling.Plane) ∈ P.centres := ⟨t, htP, rfl⟩
      refine ⟨P, t, v, w, hcP, htCentre, hvw, hvwRe, ?_, ?_⟩
      · have hre := congrArg Complex.re hqp
        have htsRe := congrArg Complex.re hts
        simp only [q, Complex.add_re] at hre
        linarith
      · rw [Tiling.AxisParallel.frontier_vadd_eq]
        change openSegment ℝ (t.1 +ᵥ v.1) (t.1 +ᵥ w.1) ⊆
          t.1 +ᵥ frontier K.support
        rw [← vadd_openSegment ℝ]
        rintro z ⟨r, hr, rfl⟩
        exact ⟨r, (hEdge hr).1, rfl⟩

private theorem translatedVertexCoordinates_locallyFinite :
    ∀ (K : Region) (T : Set Tiling.Plane),
      (∀ Q : Set ℝ, Bornology.IsBounded Q →
        (Complex.re '' T ∩ Q).Finite) →
      ∀ Q : Set ℝ, Bornology.IsBounded Q →
        ({c : ℝ | ∃ v ∈ K.vertices, ∃ t ∈ T,
          c = v.re + t.re} ∩ Q).Finite := by
  intro K T hLocal Q hQBounded
  let A : ↑K.vertexFinset → Set ℝ := fun v ↦
    (fun r : ℝ ↦ v.1.re + r) ''
      ((Complex.re '' T) ∩ ((-v.1.re) +ᵥ Q))
  have hShiftBounded (v : ↑K.vertexFinset) :
      Bornology.IsBounded ((-v.1.re) +ᵥ Q) := hQBounded.vadd _
  have hAFinite (v : ↑K.vertexFinset) : (A v).Finite := by
    apply Set.Finite.image
    exact hLocal ((-v.1.re) +ᵥ Q) (hShiftBounded v)
  apply (Set.finite_iUnion hAFinite).subset
  rintro c ⟨⟨v, hv, t, ht, hct⟩, hcQ⟩
  have hvFinset : v ∈ K.vertexFinset := by
    change v ∈ (K.vertexFinset : Set Tiling.Plane)
    simpa only [K.coe_vertexFinset] using hv
  rw [Set.mem_iUnion]
  refine ⟨⟨v, hvFinset⟩, ?_⟩
  refine ⟨t.re, ⟨⟨t, ht, rfl⟩, ?_⟩, ?_⟩
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add, neg_neg]
    convert hcQ using 1
    linarith [hct]
  · exact hct.symm

theorem componentBoundarySet_locallyFinite :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ Q : Set ℝ, Bornology.IsBounded Q →
        (componentBoundarySet K T ∩ Q).Finite := by
  intro K T hTile Q hQBounded
  by_cases hTrivial : ∃ P : Continuous.VerticalPlate K T,
      ¬ Continuous.IsVerticalColumn P ∧ P.centres = T
  · rw [trivialDecomposition_componentBoundarySet_empty hTile hTrivial]
    simp only [empty_inter, Set.finite_empty]
  · have hProjectedLocal :=
      (Tiling.AxisParallel.Structure.projectedCentres_closedLocallyFinite hTile hTrivial).2
    have hOffsetLocal := translatedVertexCoordinates_locallyFinite K T
      hProjectedLocal Q hQBounded
    apply hOffsetLocal.subset
    rintro c ⟨hcBoundary, hcQ⟩
    obtain ⟨P, t, v, w, hcP, htP, hvw, hvwRe, hcEq, hEdge⟩ :=
      componentBoundary_hasTranslatedVerticalEdge hTile hTrivial c hcBoundary
    exact ⟨⟨v.1, v.2, t.1, t.2, hcEq⟩, hcQ⟩

theorem componentBoundarySet_closed :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      IsClosed (componentBoundarySet K T) := by
  intro K T hTile
  exact boundedWindowFinite_isClosed _
    (componentBoundarySet_locallyFinite hTile)

theorem componentBoundary_not_mem_plateBase
    {K : Region} {T : Set Tiling.Plane}
    (hTile : TilesOn K T Set.univ)
    {c : ℝ} (hc : c ∈ componentBoundarySet K T)
    (P : Continuous.VerticalPlate K T) : c ∉ P.base := by
  rw [componentBoundarySet_eq] at hc
  obtain ⟨Q, hcQ⟩ := Set.mem_iUnion.mp hc
  obtain ⟨hPRegular, -⟩ :=
    Continuous.VerticalPlate.support_isVerticalSlab hTile P
  have hPBaseOpen : IsOpen P.base := by
    rw [hPRegular]
    exact isOpen_interior
  by_cases hPQ : P = Q
  · subst Q
    intro hcP
    exact hcQ.2 (by rwa [hPBaseOpen.interior_eq])
  · intro hcP
    have hMeet : (P.base ∩ Q.base).Nonempty :=
      (mem_closure_iff.mp (frontier_subset_closure hcQ))
        P.base hPBaseOpen hcP
    obtain ⟨z, hzP, hzQ⟩ := hMeet
    exact Set.disjoint_left.mp
      (verticalPlateBases_pairwiseDisjoint hTile P Q hPQ) hzP hzQ

private theorem genericHeight_near
    (K : Region) (y ε : ℝ) (hε : 0 < ε) :
    ∃ y', y' ∈ Ioo (y - ε / 2) (y + ε / 2) ∧
      y' ∉ K.vertexFinset.image Complex.im := by
  let J : Set ℝ := Ioo (y - ε / 2) (y + ε / 2)
  have hJNotCountable : ¬ J.Countable := by
    change ¬ (Ioo (y - ε / 2) (y + ε / 2)).Countable
    rw [Cardinal.Real.Ioo_countable_iff]
    linarith
  by_contra hNo
  push Not at hNo
  have hSubset : J ⊆ (K.vertexFinset.image Complex.im : Set ℝ) := by
    intro z hz
    exact hNo z hz
  exact hJNotCountable
    ((K.vertexFinset.image Complex.im).finite_toSet.countable.mono hSubset)

private theorem componentBoundaryGap_hasTileSliceWitness :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∀ a b : ℝ,
        a ∈ componentBoundarySet K T →
        b ∈ componentBoundarySet K T →
        a < b →
        Ioo a b ∩ componentBoundarySet K T = ∅ →
        ∃ (t : ↥T) (v w : ↥K.vertices) (y : ℝ),
          y ∉ K.vertexFinset.image Complex.im ∧
          v.1.re < w.1.re ∧
          w.1.re - v.1.re ∈ K.horizontalStepAlphabet ∧
          Ioo v.1.re w.1.re ⊆ horizontalSlice K y ∧
          Ioo (v.1.re + t.1.re) (w.1.re + t.1.re) ⊆ Ioo a b := by
  intro K T hTile a b ha hb hab hGap
  let D : Set Tiling.Plane := Complex.re ⁻¹' Ioo a b
  let x : Tiling.Plane := ⟨(a + b) / 2, 0⟩
  have hDOpen : IsOpen D := isOpen_Ioo.preimage Complex.continuous_re
  have hxD : x ∈ D := by
    change (a + b) / 2 ∈ Ioo a b
    constructor <;> linarith
  have hRegularUniv : regularSupport K T = Set.univ :=
    regularSupport_eq_of_tilesOn isOpen_univ (by simp) hTile
  have hxClosure : x ∈ closure (openUnion K T) := by
    have hxRegular : x ∈ regularSupport K T := by
      rw [hRegularUniv]
      exact Set.mem_univ x
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion] at hxRegular
    exact interior_subset hxRegular
  have hMeet : (D ∩ openUnion K T).Nonempty :=
    (mem_closure_iff.mp hxClosure) D hDOpen hxD
  obtain ⟨q, hqD, hqOpen⟩ := hMeet
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hqOpen
  obtain ⟨t, hqt⟩ := hqOpen
  let p : Tiling.Plane := q - t.1
  have hqp : q = t.1 + p := by simp [p]
  have hpOpen : p ∈ K.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hqt
    simpa only [p, vadd_eq_add, neg_add_eq_sub] using hqt
  obtain ⟨ε, hε, hBall⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) p hpOpen
  obtain ⟨y, hyNear, hyGeneric⟩ := genericHeight_near K p.im ε hε
  let p' : Tiling.Plane := Complex.mk p.re y
  have hp'Ball : p' ∈ Metric.ball p ε := by
    rw [Metric.mem_ball, Complex.dist_of_re_eq]
    · rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hyNear.1, hyNear.2]
    · rfl
  have hp'Open : p' ∈ K.openCarrier := hBall hp'Ball
  obtain ⟨H⟩ :=
    Tiling.AxisParallel.Foundations.GenericSlices.horizontalGenericSlicePresentation_exists
      K hyGeneric
  have hp'Slice : p.re ∈
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
    change Complex.mk p.re y ∈ K.openCarrier
    exact hp'Open
  rw [H.union_eq, Set.mem_iUnion] at hp'Slice
  obtain ⟨i, hpi⟩ := hp'Slice
  let v : ↑K.vertices := H.leftVertex i
  let w : ↑K.vertices := H.rightVertex i
  have hvCoord : v.1.re = H.left i := H.leftVertex_coord i
  have hwCoord : w.1.re = H.right i := H.rightVertex_coord i
  have hvw : v.1.re < w.1.re := by
    rw [hvCoord, hwCoord]
    exact H.lt i
  have hStep : w.1.re - v.1.re ∈ K.horizontalStepAlphabet := by
    apply (K.mem_horizontalStepAlphabet_iff _).2
    exact ⟨v.1, v.2, w.1, w.2, rfl, sub_pos.mpr hvw⟩
  have hSlice : Ioo v.1.re w.1.re ⊆ horizontalSlice K y := by
    intro r hr
    have hr' : r ∈ Ioo (H.left i) (H.right i) := by
      rwa [← hvCoord, ← hwCoord]
    have : r ∈
        Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice K y := by
      rw [H.union_eq, Set.mem_iUnion]
      exact ⟨i, hr'⟩
    simpa only [horizontalSlice,
      Tiling.AxisParallel.Foundations.GenericSlices.horizontalSlice,
      Complex.mk_eq_add_mul_I] using this
  let P : Continuous.VerticalPlate K T :=
    Continuous.VerticalPlate.ofCentre (K := K) t
  have htP : (t.1 : Tiling.Plane) ∈ P.centres :=
    Continuous.VerticalPlate.mem_centres_ofCentre t
  have hTranslatedSliceBase :
      Ioo (v.1.re + t.1.re) (w.1.re + t.1.re) ⊆ P.base := by
    intro r hr
    have hrSource : r - t.1.re ∈ Ioo v.1.re w.1.re := by
      constructor <;> linarith [hr.1, hr.2]
    have hrCarrier := hSlice hrSource
    have hrProjection : r - t.1.re ∈ Complex.re '' K.openCarrier := by
      refine ⟨Complex.mk (r - t.1.re) y, ?_, rfl⟩
      change ((r - t.1.re : ℝ) : ℂ) + (y : ℂ) * Complex.I ∈
        K.openCarrier at hrCarrier
      simpa only [Complex.mk_eq_add_mul_I] using hrCarrier
    have hProjectionOpen : IsOpen (Complex.re '' K.openCarrier) :=
      Complex.isOpenMap_re K.openCarrier isOpen_interior
    have hrFootprint : r - t.1.re ∈ horizontalFootprint K := by
      exact hProjectionOpen.subset_interior_closure hrProjection
    apply plateCentre_footprint_subset_base hTile P t.1 htP
    refine ⟨t.1.re, Set.mem_singleton _, r - t.1.re, hrFootprint, ?_⟩
    ring
  have haNotBase : a ∉ P.base := componentBoundary_not_mem_plateBase hTile ha P
  have hbNotBase : b ∉ P.base := componentBoundary_not_mem_plateBase hTile hb P
  have hqReGap : q.re ∈ Ioo a b := hqD
  have hpReInterval : p.re ∈ Ioo v.1.re w.1.re := by
    rwa [hvCoord, hwCoord]
  have hqReInterval : q.re ∈
      Ioo (v.1.re + t.1.re) (w.1.re + t.1.re) := by
    have hqRe := congrArg Complex.re hqp
    simp only [Complex.add_re] at hqRe
    constructor <;> linarith [hpReInterval.1, hpReInterval.2]
  have hTranslatedInside :
      Ioo (v.1.re + t.1.re) (w.1.re + t.1.re) ⊆ Ioo a b := by
    intro r hr
    constructor
    · by_contra hra
      apply haNotBase
      apply hTranslatedSliceBase
      exact ⟨by linarith [hr.1], by linarith [hqReInterval.2, hqReGap.1]⟩
    · by_contra hrb
      apply hbNotBase
      apply hTranslatedSliceBase
      exact ⟨by linarith [hqReInterval.1, hqReGap.2], by linarith [hr.2]⟩
  exact ⟨t, v, w, y, hyGeneric, hvw, hStep, hSlice, hTranslatedInside⟩

theorem componentBoundaryGaps_boundedBelow :
    ∀ {K : Region} {T : Set Tiling.Plane},
      TilesOn K T Set.univ →
      ∃ rho : ℝ, 0 < rho ∧
        ∀ a b : ℝ,
          a ∈ componentBoundarySet K T →
          b ∈ componentBoundarySet K T →
          a < b →
          Ioo a b ∩ componentBoundarySet K T = ∅ →
          rho ≤ b - a := by
  intro K T hTile
  obtain ⟨rho, hRho, hRhoLower⟩ := horizontalStepAlphabet_hasPositiveLowerBound K
  refine ⟨rho, hRho, ?_⟩
  intro a b ha hb hab hGap
  obtain ⟨t, v, w, y, hy, hvw, hStep, hSlice, hInside⟩ :=
    componentBoundaryGap_hasTileSliceWitness hTile a b ha hb hab hGap
  have hTranslatedLt : v.1.re + t.1.re < w.1.re + t.1.re := by
    linarith
  obtain ⟨hLeft, hRight⟩ :=
    (Set.Ioo_subset_Ioo_iff hTranslatedLt).mp hInside
  have hWidth : w.1.re - v.1.re ≤ b - a := by
    linarith
  exact (hRhoLower _ hStep).trans hWidth






end Tiling.AxisParallel.Structure
