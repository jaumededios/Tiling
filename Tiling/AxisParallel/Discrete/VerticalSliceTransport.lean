import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Discrete.PeriodicDirectionalLayers
import Tiling.RationalPolygonal.DiscreteCarrier

/-!
# Uniform transport of vertical slices

This module specializes the public Greenfeld--Tao slice-transport input to the first directional
layer of an arbitrary vertical earthquake.  All slice and carrier notions are the existing
project definitions.
-/

open Set
open TranslationalTilings

namespace Tiling.AxisParallel.Discrete

private theorem indicator_eq_iff_membership {G : Type*}
    (S : Set G) (x y : G) :
    TranslationalTilings.setIndicator S x =
        TranslationalTilings.setIndicator S y ↔ (x ∈ S ↔ y ∈ S) := by
  classical
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S <;>
    simp [TranslationalTilings.setIndicator, hx, hy]

private theorem shiftedFirstLayer_periodic
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {k : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit) :
    Tiling.RationalPolygonal.DiscretePeriodicBy
      (shiftedDirectionalLayerCentres D order shift
        ⟨0, D.number_pos⟩)
      ((k : ℤ) • verticalDiscreteUnit) := by
  intro x
  simp only [shiftedDirectionalLayerCentres, Set.mem_iUnion]
  constructor
  · rintro ⟨P, hxP⟩
    refine ⟨P, ?_⟩
    have hp := (quakeShift_preservesDirectionalDecomposition D order shift P).2.2
      ⟨0, D.number_pos⟩ x
    rw [hfirst] at hp
    exact hp.mp hxP
  · rintro ⟨P, hxP⟩
    refine ⟨P, ?_⟩
    have hp := (quakeShift_preservesDirectionalDecomposition D order shift P).2.2
      ⟨0, D.number_pos⟩ x
    rw [hfirst] at hp
    exact hp.mpr hxP

private theorem shiftedFirstLayer_subset_quakeShifted
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ) :
    shiftedDirectionalLayerCentres D order shift
        ⟨0, D.number_pos⟩ ⊆
      Tiling.RationalPolygonal.quakeShiftedTranslations shift := by
  intro x hx
  obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
  have hxPlate : x ∈ TranslationalTilings.translateSet
      ((shift P) • verticalDiscreteUnit)
      (Tiling.RationalPolygonal.quakePlateTranslations P) := by
    rw [← (quakeShift_preservesDirectionalDecomposition D order shift P).2.1]
    exact Set.mem_iUnion.mpr ⟨⟨0, D.number_pos⟩, hxP⟩
  change x - (shift P) • verticalDiscreteUnit ∈
    Tiling.RationalPolygonal.quakePlateTranslations P at hxPlate
  obtain ⟨haA, haComp⟩ := hxPlate
  let a : A := ⟨x - (shift P) • verticalDiscreteUnit, haA⟩
  refine ⟨a, ?_⟩
  have hP :
      (Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a =
        P := haComp
  change shift
      ((Tiling.RationalPolygonal.quakeGraph F A verticalDiscreteUnit).connectedComponentMk a) •
        verticalDiscreteUnit + (a : TranslationalTilings.Plane) = x
  rw [hP]
  dsimp only [a]
  abel

set_option linter.unusedVariables false in
theorem exists_uniformVerticalSliceTransport
    {F : Finset TranslationalTilings.Plane}
    {A E : Set TranslationalTilings.Plane} {ell k M : ℕ}
    (hF : F.Nonempty) (hell : 0 < ell)
    (hEVertical : Tiling.RationalPolygonal.DiscretePeriodicBy
      E verticalDiscreteUnit)
    (hEPeriodic : TranslationalTilings.SetScalarPeriodic ell E)
    (hTile : TranslationalTilings.Tiles F A E)
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (hk : 0 < k)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit)
    (hM : 0 < M)
    (hShiftedFirst : ∀ shift : Tiling.RationalPolygonal.QuakePlate
        F A verticalDiscreteUnit → ℤ,
      TranslationalTilings.SetScalarPeriodic M
        (Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift
            ⟨0, D.number_pos⟩))) :
    ∃ K : ℕ,
      K = TranslationalTilings.indicatorDilationModulus M F.card * k *
        TranslationalTilings.slicingLCM F verticalDiscreteUnit ∧
      0 < K ∧
      ∀ (shift : Tiling.RationalPolygonal.QuakePlate
          F A verticalDiscreteUnit → ℤ)
        (x d : ℤ),
        TranslationalTilings.translateSet
            ((d * (K : ℤ)) • horizontalDiscreteUnit)
            (Tiling.RationalPolygonal.discreteCarrier F
              (shiftedDirectionalLayerCentres D order shift
                  ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre x)) =
          Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order shift
                ⟨0, D.number_pos⟩ ∩
              verticalDiscreteFibre (x + d * (K : ℤ))) := by
  let K := TranslationalTilings.indicatorDilationModulus M F.card * k *
    TranslationalTilings.slicingLCM F verticalDiscreteUnit
  refine ⟨K, rfl, ?_, ?_⟩
  · dsimp only [K]
    exact Nat.mul_pos
      (Nat.mul_pos
        (by simpa [TranslationalTilings.indicatorDilationModulus] using
          (TranslationalTilings.dilationModulus_pos
            (oscillation := 1) (tileCard := F.card) hM))
        hk)
      (TranslationalTilings.slicingLCM_pos F verticalDiscreteUnit)
  · intro shift x d
    let C := shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩
    have hCperiod : Tiling.RationalPolygonal.DiscretePeriodicBy C
        ((k : ℤ) • verticalDiscreteUnit) :=
      shiftedFirstLayer_periodic D order shift hfirst
    have hCperiodMk : Tiling.RationalPolygonal.DiscretePeriodicBy C
        (((M * k : ℕ) : ℤ) • verticalDiscreteUnit) := by
      convert hCperiod.zsmul (M : ℤ) using 1
      push_cast
      module
    have hCindicator : Function.Periodic
        (TranslationalTilings.setIndicator C)
        (((M * k : ℕ) : ℤ) • verticalDiscreteUnit) := by
      intro z
      apply (indicator_eq_iff_membership C _ _).2
      exact hCperiodMk z
    have hShiftTile := tilesOn_quakeShiftedTranslations hF hTile hEVertical shift
    have hCsubset : C ⊆ Tiling.RationalPolygonal.quakeShiftedTranslations shift :=
      shiftedFirstLayer_subset_quakeShifted D order shift
    have hconv : TranslationalTilings.ScalarPeriodic M
        (TranslationalTilings.tileConv F
          (TranslationalTilings.setIndicator C)) := by
      rw [Tiling.RationalPolygonal.tileConv_indicator_eq_indicator_discreteCarrier
        hShiftTile hCsubset]
      intro z v
      apply (indicator_eq_iff_membership
        (Tiling.RationalPolygonal.discreteCarrier F C) _ _).2
      exact hShiftedFirst shift z v
    have htransport := Tiling.AxisParallel.Foundations.gtSliceTransport
      hM hk (h := verticalDiscreteUnit) (by
        constructor
        · intro hv
          have := congrFun hv 1
          simp at this
        · decide)
      hCindicator hconv
      (QuotientAddGroup.mk' (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
        (x • horizontalDiscreteUnit))
      (d • horizontalDiscreteUnit)
    have hslice (y : ℤ) :
        TranslationalTilings.slicePattern verticalDiscreteUnit
            (QuotientAddGroup.mk'
              (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
              (y • horizontalDiscreteUnit)) C =
          C ∩ verticalDiscreteFibre y := by
      have hcoset : TranslationalTilings.quotientCoset
          (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
          (QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
            (y • horizontalDiscreteUnit)) =
          TranslationalTilings.addCoset
            (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
            (y • horizontalDiscreteUnit) := by
        ext z
        exact QuotientAddGroup.eq_iff_sub_mem
      rw [TranslationalTilings.slicePattern, hcoset]
      rfl
    have hline :
        QuotientAddGroup.mk'
              (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
              (x • horizontalDiscreteUnit) +
            QuotientAddGroup.mk'
              (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
              (((TranslationalTilings.indicatorDilationModulus M F.card * k *
                  TranslationalTilings.slicingLCM F verticalDiscreteUnit : ℕ) : ℤ) •
                (d • horizontalDiscreteUnit)) =
          QuotientAddGroup.mk'
            (TranslationalTilings.directionSubgroup verticalDiscreteUnit)
            ((x + d * (K : ℤ)) • horizontalDiscreteUnit) := by
      rw [← map_add]
      congr 1
      dsimp only [K]
      push_cast
      module
    rw [hline, hslice x, hslice (x + d * (K : ℤ))] at htransport
    have hvector :
        (((TranslationalTilings.indicatorDilationModulus M F.card * k *
              TranslationalTilings.slicingLCM F verticalDiscreteUnit : ℕ) : ℤ) •
            (d • horizontalDiscreteUnit)) =
          (d * (K : ℤ)) • horizontalDiscreteUnit := by
      dsimp only [K]
      push_cast
      module
    rw [hvector] at htransport
    simpa only [C] using htransport

set_option linter.unusedVariables false in
theorem verticalSliceOrbit_scalarPeriodic
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {k K L : ℕ}
    (D : Tiling.RationalPolygonal.UniformQuakePeriodicDecomposition
      F A verticalDiscreteUnit)
    (order : Equiv.Perm (Fin D.numberOfParts))
    (hk : 0 < k)
    (hfirst : D.period (order ⟨0, D.number_pos⟩) =
      (k : ℤ) • verticalDiscreteUnit)
    (shift : Tiling.RationalPolygonal.QuakePlate
      F A verticalDiscreteUnit → ℤ)
    (hK : 0 < K)
    (hTransport : ∀ (x d : ℤ),
      TranslationalTilings.translateSet
          ((d * (K : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.discreteCarrier F
            (shiftedDirectionalLayerCentres D order shift
                ⟨0, D.number_pos⟩ ∩ verticalDiscreteFibre x)) =
        Tiling.RationalPolygonal.discreteCarrier F
          (shiftedDirectionalLayerCentres D order shift
              ⟨0, D.number_pos⟩ ∩
            verticalDiscreteFibre (x + d * (K : ℤ))))
    (hL : 0 < L) (hKL : K ∣ L) (hkL : k ∣ L) (x : ℤ) :
    TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F
        (shiftedDirectionalLayerCentres D order shift
            ⟨0, D.number_pos⟩ ∩
          verticalDiscreteCongruenceClass x L)) := by
  let C := shiftedDirectionalLayerCentres D order shift ⟨0, D.number_pos⟩
  let S := Tiling.RationalPolygonal.discreteCarrier F
    (C ∩ verticalDiscreteCongruenceClass x L)
  have hCperiod : Tiling.RationalPolygonal.DiscretePeriodicBy C
      ((k : ℤ) • verticalDiscreteUnit) :=
    shiftedFirstLayer_periodic D order shift hfirst
  obtain ⟨qK, hqK⟩ := hKL
  obtain ⟨qk, hqk⟩ := hkL
  have hHorizontalForward (z : TranslationalTilings.Plane) (u : ℤ)
      (hz : z ∈ S) :
      z + (u * (L : ℤ)) • horizontalDiscreteUnit ∈ S := by
    obtain ⟨f, hfF, a, ⟨haC, haClass⟩, hzfa⟩ := hz
    obtain ⟨n, han⟩ := (mem_verticalDiscreteCongruenceClass_iff a x L).mp haClass
    have haFibre : a ∈ verticalDiscreteFibre (x + n * (L : ℤ)) :=
      (mem_verticalDiscreteFibre_iff a _).mpr han
    have hzSlice : z ∈ Tiling.RationalPolygonal.discreteCarrier F
        (C ∩ verticalDiscreteFibre (x + n * (L : ℤ))) :=
      ⟨f, hfF, a, ⟨haC, haFibre⟩, hzfa⟩
    let d : ℤ := u * (qK : ℤ)
    have hzTranslated : z + (d * (K : ℤ)) • horizontalDiscreteUnit ∈
        TranslationalTilings.translateSet
          ((d * (K : ℤ)) • horizontalDiscreteUnit)
          (Tiling.RationalPolygonal.discreteCarrier F
            (C ∩ verticalDiscreteFibre (x + n * (L : ℤ))) ) := by
      change z + (d * (K : ℤ)) • horizontalDiscreteUnit -
          (d * (K : ℤ)) • horizontalDiscreteUnit ∈
        Tiling.RationalPolygonal.discreteCarrier F
          (C ∩ verticalDiscreteFibre (x + n * (L : ℤ)))
      simpa only [add_sub_cancel_right] using hzSlice
    rw [hTransport (x + n * (L : ℤ)) d] at hzTranslated
    have hindex : x + n * (L : ℤ) + d * (K : ℤ) =
        x + (n + u) * (L : ℤ) := by
      dsimp only [d]
      rw [hqK]
      push_cast
      ring
    rw [hindex] at hzTranslated
    obtain ⟨g, hgF, b, ⟨hbC, hbFibre⟩, hzg⟩ := hzTranslated
    refine ⟨g, hgF, b, ⟨hbC, ?_⟩, ?_⟩
    · apply (mem_verticalDiscreteCongruenceClass_iff b x L).mpr
      exact ⟨n + u, (mem_verticalDiscreteFibre_iff b _).mp hbFibre⟩
    · rw [← hzg]
      congr 1
      dsimp only [d]
      rw [hqK]
      push_cast
      module
  have hHorizontal (z : TranslationalTilings.Plane) (u : ℤ) :
      z + (u * (L : ℤ)) • horizontalDiscreteUnit ∈ S ↔ z ∈ S := by
    constructor
    · intro hz
      have := hHorizontalForward
        (z + (u * (L : ℤ)) • horizontalDiscreteUnit) (-u) hz
      convert this using 1
      module
    · exact hHorizontalForward z u
  have hVerticalForward (z : TranslationalTilings.Plane) (u : ℤ)
      (hz : z ∈ S) :
      z + (u * (L : ℤ)) • verticalDiscreteUnit ∈ S := by
    obtain ⟨f, hfF, a, ⟨haC, haClass⟩, hzfa⟩ := hz
    have hCmultiple : Tiling.RationalPolygonal.DiscretePeriodicBy C
        ((u * (qk : ℤ)) • ((k : ℤ) • verticalDiscreteUnit)) :=
      hCperiod.zsmul (u * (qk : ℤ))
    have haC' : a + (u * (L : ℤ)) • verticalDiscreteUnit ∈ C := by
      have hperiodVector :
          (u * (qk : ℤ)) • ((k : ℤ) • verticalDiscreteUnit) =
            (u * (L : ℤ)) • verticalDiscreteUnit := by
        rw [hqk]
        push_cast
        module
      rw [← hperiodVector]
      exact (hCmultiple a).2 haC
    have haClass' : a + (u * (L : ℤ)) • verticalDiscreteUnit ∈
        verticalDiscreteCongruenceClass x L := by
      apply (mem_verticalDiscreteCongruenceClass_iff _ x L).mpr
      obtain ⟨n, han⟩ :=
        (mem_verticalDiscreteCongruenceClass_iff a x L).mp haClass
      refine ⟨n, ?_⟩
      simpa [firstDiscreteCoordinate, verticalDiscreteUnit] using han
    refine ⟨f, hfF, a + (u * (L : ℤ)) • verticalDiscreteUnit,
      ⟨haC', haClass'⟩, ?_⟩
    rw [hzfa]
    abel
  have hVertical (z : TranslationalTilings.Plane) (u : ℤ) :
      z + (u * (L : ℤ)) • verticalDiscreteUnit ∈ S ↔ z ∈ S := by
    constructor
    · intro hz
      have := hVerticalForward
        (z + (u * (L : ℤ)) • verticalDiscreteUnit) (-u) hz
      convert this using 1
      module
    · exact hVerticalForward z u
  intro z v
  change z + (L : ℤ) • v ∈ S ↔ z ∈ S
  have hvectors : z + (L : ℤ) • v =
      (z + (v 0 * (L : ℤ)) • horizontalDiscreteUnit) +
        (v 1 * (L : ℤ)) • verticalDiscreteUnit := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    fin_cases i <;>
      simp [horizontalDiscreteUnit, verticalDiscreteUnit] <;> ring
  rw [hvectors, hVertical, hHorizontal]

end Tiling.AxisParallel.Discrete
