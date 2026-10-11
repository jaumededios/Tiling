import Mathlib.Topology.Connected.Basic
import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Continuous.PositiveSimilarityPlates
import Tiling.AxisParallel.Discrete.Core
import Tiling.AxisParallel.Discrete.DiscreteTilingsAndPlates
import Tiling.AxisParallel.Discrete.DiscreteBandTilings
import Tiling.RationalPolygonal.Earthquake
import Tiling.RationalPolygonal.Raster
import TranslationalTilings.Slicing
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry
import Tiling.AxisParallel.Foundations.FilledSliceChains
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Continuous.EarthquakePlates
import Tiling.AxisParallel.Continuous.RationalSlabPeriodicity
import Tiling.RationalPolygonal.Basic
import Tiling.AxisParallel.Foundations.RationalMeshRaster
import Tiling.AxisParallel.Continuous.IntrinsicHorizontalContact
import Tiling.RationalPolygonal.RawInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

open Set
open Bornology
open Filter MeasureTheory
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal









/-!
# Rational slabs in a periodic vertical carrier

This module begins the target-relative integerization argument.  It exposes the carrier and phase
data directly in terms of native sets and the existing discrete and continuous plate graphs.
-/

open Set
open scoped Pointwise

noncomputable section

/-- A nonnull regular-open periodic subset of the horizontal line. -/
structure PeriodicVerticalCarrier where
  base : Set ℝ
  base_open : IsOpen base
  base_regular : interior (closure base) = base
  base_nonnull : MeasureTheory.volume base ≠ 0
  period : ℝ
  period_pos : 0 < period
  base_periodic : period +ᵥ base = base

/-- The planar vertical carrier over a periodic line set. -/
def PeriodicVerticalCarrier.carrier (X : PeriodicVerticalCarrier) : Set Tiling.Plane :=
  Complex.re ⁻¹' X.base

/-- Equality modulo the embedded integer subgroup. -/
def SameIntegerPhase (x y : ℝ) : Prop :=
  ∃ n : ℤ, x - y = n

/-- A literal phase partition of centres and of their target carrier. -/
structure IsCarrierPhaseDecomposition
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) (phases : Set ℝ)
    (phaseBase : ℝ → Set ℝ) (phaseCentres : ℝ → Set Tiling.Plane) : Prop where
  phases_nonempty : phases.Nonempty
  phaseBase_open : ∀ c ∈ phases, IsOpen (phaseBase c)
  phaseBase_regular : ∀ c ∈ phases,
    interior (closure (phaseBase c)) = phaseBase c
  phaseCentres_nonempty : ∀ c ∈ phases, (phaseCentres c).Nonempty
  phaseCentres_pairwise : Set.PairwiseDisjoint phases phaseCentres
  phaseCentres_union : (⋃ c : phases, phaseCentres c) = T
  phase_tiles : ∀ c ∈ phases,
    Tiling.AxisParallel.TilesOn K (phaseCentres c) (Complex.re ⁻¹' phaseBase c)
  phaseBases_pairwise : Set.PairwiseDisjoint phases phaseBase
  phaseBases_cover : interior (closure (⋃ c : phases, phaseBase c)) = X.base
  centre_phase : ∀ c ∈ phases, ∀ t ∈ phaseCentres c, SameIntegerPhase t.re c
  boundary_phase : ∀ c ∈ phases, ∀ x ∈ frontier (phaseBase c), SameIntegerPhase x c
  phase_representatives : ∀ c ∈ phases, ∀ d ∈ phases,
    SameIntegerPhase c d → c = d
  plate_has_unique_phase :
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ∃! c : ℝ, c ∈ phases ∧ P.centres ⊆ phaseCentres c

/-- Regularized union of the open unit cells indexed by a discrete carrier. -/
def relativeRasterSupport (S : Set TranslationalTilings.Plane) : Set Tiling.Plane :=
  interior (closure {z : Tiling.Plane | ∃ q ∈ S,
    (q 0 : ℝ) < z.re ∧ z.re < (q 0 : ℝ) + 1 ∧
    (q 1 : ℝ) < z.im ∧ z.im < (q 1 : ℝ) + 1})

/-- A target-relative bridge from a continuous plate tiling to an integral discrete tiling. -/
structure RelativePlateIntegerization
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane) (base : Set ℝ) where
  shift : Tiling.AxisParallel.Continuous.VerticalPlate K T → ℝ
  integerTile : Finset TranslationalTilings.Plane
  integerTile_nonempty : integerTile.Nonempty
  integerCentres : Set TranslationalTilings.Plane
  integerBase : Set ℤ
  integerBase_eq : integerBase =
    {n : ℤ | Set.Ioo (n : ℝ) ((n : ℝ) + 1) ⊆ base}
  shiftedCentres_eq :
    Tiling.RationalPolygonal.integerPoint '' integerCentres =
      Tiling.AxisParallel.Continuous.shiftVerticalPlates K T shift
  integerTiles : TranslationalTilings.Tiles integerTile integerCentres
    (Tiling.AxisParallel.Discrete.verticalDiscreteCylinder integerBase)
  graphEquiv :
    Tiling.RationalPolygonal.quakeGraph integerTile integerCentres
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃g
      Tiling.AxisParallel.Continuous.verticalPlateGraph K T
  plateEquiv :
    Tiling.RationalPolygonal.QuakePlate integerTile integerCentres
        Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃
      Tiling.AxisParallel.Continuous.VerticalPlate K T
  plateEquiv_mem : ∀ P, ∀ z : integerCentres,
    z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P ↔
      ((graphEquiv z : T) : Tiling.Plane) ∈ (plateEquiv P).centres
  centre_apply : ∀ z : integerCentres,
    ((graphEquiv z : T) : Tiling.Plane) =
      (-((shift (Tiling.AxisParallel.Continuous.VerticalPlate.ofCentre
        (graphEquiv z)) : ℂ) * Complex.I)) +
        Tiling.RationalPolygonal.integerPoint z
  plateCentres : ∀ P,
    Tiling.RationalPolygonal.integerPoint ''
        Tiling.RationalPolygonal.quakePlateTranslations P =
      (((shift (plateEquiv P) : ℝ) : ℂ) * Complex.I) +ᵥ
        (plateEquiv P).centres
  supportBridge : ∀ P,
    relativeRasterSupport
        (Tiling.RationalPolygonal.discreteCarrier integerTile
          (Tiling.RationalPolygonal.quakePlateTranslations P)) =
      (plateEquiv P).support

/-- The carrier projection is definitionally the full vertical preimage of its base. -/
theorem periodicVerticalCarrier_carrier_eq (X : PeriodicVerticalCarrier) :
    X.carrier = Complex.re ⁻¹' X.base :=
  rfl

/-- `SameIntegerPhase` is literal equality modulo an integer. -/
theorem sameIntegerPhase_iff (x y : ℝ) :
    SameIntegerPhase x y ↔ ∃ n : ℤ, x - y = n :=
  Iff.rfl

/-- The relative raster support expands to its native regularized unit-cell union. -/
theorem relativeRasterSupport_eq (S : Set TranslationalTilings.Plane) :
    relativeRasterSupport S = interior (closure
      {z : Tiling.Plane | ∃ q ∈ S,
        (q 0 : ℝ) < z.re ∧ z.re < (q 0 : ℝ) + 1 ∧
        (q 1 : ℝ) < z.im ∧ z.im < (q 1 : ℝ) + 1}) :=
  rfl

/-- A scalar period of a discrete carrier becomes the corresponding horizontal period of its
regularized unit-cell raster. -/
theorem discretePeriod_liftsContinuous
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {base : Set ℝ}
    (I : RelativePlateIntegerization K T base)
    {S : Set TranslationalTilings.Plane} {L : ℕ}
    (hperiod : TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier I.integerTile S)) :
    Tiling.RationalPolygonal.SetPeriodicBy
      (relativeRasterSupport
        (Tiling.RationalPolygonal.discreteCarrier I.integerTile S)) (L : ℂ) := by
  let A : Set TranslationalTilings.Plane :=
    Tiling.RationalPolygonal.discreteCarrier I.integerTile S
  change TranslationalTilings.SetScalarPeriodic L A at hperiod
  let e₀ : TranslationalTilings.Plane := ![1, 0]
  let U : Set Tiling.Plane := {z : Tiling.Plane | ∃ q ∈ A,
    (q 0 : ℝ) < z.re ∧ z.re < (q 0 : ℝ) + 1 ∧
    (q 1 : ℝ) < z.im ∧ z.im < (q 1 : ℝ) + 1}
  have hUperiod (z : Tiling.Plane) : z + (L : ℂ) ∈ U ↔ z ∈ U := by
    constructor
    · rintro ⟨q, hq, hq₀, hz₀, hq₁, hz₁⟩
      let q' := q - (L : ℤ) • e₀
      have hq' : q' ∈ A := by
        apply (hperiod q' e₀).mp
        simpa only [q', sub_add_cancel] using hq
      refine ⟨q', hq', ?_, ?_, ?_, ?_⟩
      · dsimp [q', e₀]
        norm_num at ⊢
        norm_num at hq₀
        linarith
      · dsimp [q', e₀]
        norm_num at ⊢
        norm_num at hz₀
        linarith
      · dsimp [q', e₀]
        simpa using hq₁
      · dsimp [q', e₀]
        simpa using hz₁
    · rintro ⟨q, hq, hq₀, hz₀, hq₁, hz₁⟩
      let q' := q + (L : ℤ) • e₀
      have hq' : q' ∈ A := (hperiod q e₀).mpr hq
      refine ⟨q', hq', ?_, ?_, ?_, ?_⟩
      · dsimp [q', e₀]
        norm_num at ⊢
        linarith
      · dsimp [q', e₀]
        norm_num at ⊢
        linarith
      · dsimp [q', e₀]
        simpa using hq₁
      · dsimp [q', e₀]
        simpa using hz₁
  have hUshift : ((L : ℂ) +ᵥ U) = U := by
    ext z
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (hUperiod (z - (L : ℂ))).symm
  have hRshift : ((L : ℂ) +ᵥ interior (closure U)) = interior (closure U) := by
    calc
      (L : ℂ) +ᵥ interior (closure U) = interior ((L : ℂ) +ᵥ closure U) := by
        rw [interior_vadd]
      _ = interior (closure ((L : ℂ) +ᵥ U)) := by
        rw [closure_vadd]
      _ = interior (closure U) := by rw [hUshift]
  intro z
  change z + (L : ℂ) ∈ interior (closure U) ↔ z ∈ interior (closure U)
  have hz := Set.ext_iff.mp hRshift (z + (L : ℂ))
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using hz.symm

/-- The integerization equivalence preserves and reflects the column predicate. -/
theorem relativePlateEquiv_preservesColumns
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {base : Set ℝ}
    (I : RelativePlateIntegerization K T base) :
    ∀ P,
      Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P ↔
        Tiling.AxisParallel.Continuous.IsVerticalColumn
          (I.plateEquiv P) := by
  have graphEquiv_re (z : I.integerCentres) :
      ((I.graphEquiv z : T) : Tiling.Plane).re = (z.1 0 : ℝ) := by
    have h := congrArg Complex.re (I.centre_apply z)
    simpa [Tiling.RationalPolygonal.integerPoint] using h
  intro P
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨(c : ℝ), ?_⟩
    rintro y ⟨t, ht, rfl⟩
    let z : I.integerCentres := I.graphEquiv.symm t
    have hzt : I.graphEquiv z = t := I.graphEquiv.apply_symm_apply t
    have hzPlate : z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
      apply (I.plateEquiv_mem P z).mpr
      rw [hzt]
      exact ⟨t, ht, rfl⟩
    have hzImage :
        Tiling.AxisParallel.Discrete.firstDiscreteCoordinate z.1 ∈
          Tiling.AxisParallel.Discrete.firstDiscreteCoordinate ''
            Tiling.RationalPolygonal.quakePlateTranslations P :=
      ⟨z.1, hzPlate, rfl⟩
    rw [hc] at hzImage
    have hzc : z.1 0 = c := by
      simpa [Tiling.AxisParallel.Discrete.firstDiscreteCoordinate] using hzImage
    change (t : Tiling.Plane).re = (c : ℝ)
    rw [← hzt, graphEquiv_re z, hzc]
  · rintro ⟨x, hx⟩
    obtain ⟨z₀, hz₀Supp⟩ := P.nonempty_supp
    have hz₀Plate : z₀.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P :=
      ⟨z₀.2, (SimpleGraph.ConnectedComponent.mem_supp_iff P z₀).mp hz₀Supp⟩
    have hz₀Continuous :
        ((I.graphEquiv z₀ : T) : Tiling.Plane) ∈ (I.plateEquiv P).centres :=
      (I.plateEquiv_mem P z₀).mp hz₀Plate
    refine ⟨z₀.1 0, ?_⟩
    ext c
    constructor
    · rintro ⟨zRaw, ⟨hzMem, hzComponent⟩, rfl⟩
      let z : I.integerCentres := ⟨zRaw, hzMem⟩
      have hzPlate : z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P :=
        ⟨hzMem, hzComponent⟩
      have hzContinuous :
          ((I.graphEquiv z : T) : Tiling.Plane) ∈ (I.plateEquiv P).centres :=
        (I.plateEquiv_mem P z).mp hzPlate
      have hzReal : (z.1 0 : ℝ) = x := (graphEquiv_re z).symm.trans (hx hzContinuous)
      have hz₀Real : (z₀.1 0 : ℝ) = x :=
        (graphEquiv_re z₀).symm.trans (hx hz₀Continuous)
      have hcast : (zRaw 0 : ℝ) = (z₀.1 0 : ℝ) :=
        hzReal.trans hz₀Real.symm
      have hint : zRaw 0 = z₀.1 0 := by exact_mod_cast hcast
      simp [Tiling.AxisParallel.Discrete.firstDiscreteCoordinate, hint]
    · intro hc
      have hc' : c = z₀.1 0 := by simpa using hc
      subst c
      exact ⟨z₀.1, hz₀Plate, rfl⟩

end


open Bornology Set
open scoped Pointwise



open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal

private def IsCarrierComponent (X : PeriodicVerticalCarrier) (a b : ℝ) : Prop :=
  a < b ∧
    a ∈ frontier X.base ∧
    b ∈ frontier X.base ∧
    Ioo a b ⊆ X.base ∧
    Ioo a b ∩ frontier X.base = ∅

private theorem carrierComponent_periodTranslate :
  ∀ (X : PeriodicVerticalCarrier) {a b : ℝ},
    IsCarrierComponent X a b → ∀ n : ℤ,
      IsCarrierComponent X
        (a + (n : ℝ) * X.period) (b + (n : ℝ) * X.period) := by
  intro X a b hab n
  rcases hab with ⟨hablt, haf, hbf, habase, hdisj⟩
  let d : ℝ := (n : ℝ) * X.period
  have hbase_fun : Function.Periodic (fun x : ℝ ↦ x ∈ X.base) X.period := by
    intro x
    apply propext
    have hm : x + X.period ∈ X.period +ᵥ X.base ↔ x + X.period ∈ X.base := by
      rw [X.base_periodic]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hm
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hm.symm
  have hbase_shift (x : ℝ) : x + d ∈ X.base ↔ x ∈ X.base := by
    have h := (hbase_fun.int_mul n) x
    simpa [d, zsmul_eq_mul] using h
  have hfront : d +ᵥ frontier X.base = frontier X.base := by
    exact Tiling.AxisParallel.OneDimensional.FiniteInterval.frontier_periodic_zsmul
      X.base_periodic n
  have hfront_shift (x : ℝ) : x + d ∈ frontier X.base ↔ x ∈ frontier X.base := by
    constructor
    · intro hx
      have hx' : x + d ∈ d +ᵥ frontier X.base := by
        rw [hfront]
        exact hx
      simpa [Set.mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hx'
    · intro hx
      have hx' : d + x ∈ d +ᵥ frontier X.base := ⟨x, hx, rfl⟩
      have hx'' : d + x ∈ frontier X.base := by
        rw [← hfront]
        exact hx'
      simpa [add_comm] using hx''
  have haf' : a + d ∈ frontier X.base := (hfront_shift a).mpr haf
  have hbf' : b + d ∈ frontier X.base := (hfront_shift b).mpr hbf
  have hablt' : a + d < b + d := by linarith
  have habase' : Ioo (a + d) (b + d) ⊆ X.base := by
    intro x hx
    have hy : x - d ∈ Ioo a b := by
      constructor <;> linarith [hx.1, hx.2]
    have hybase : x - d ∈ X.base := habase hy
    have hshifted := (hbase_shift (x - d)).mpr hybase
    simpa [sub_add_cancel] using hshifted
  have hdisj' : Ioo (a + d) (b + d) ∩ frontier X.base = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have hy : x - d ∈ Ioo a b := by
      constructor <;> linarith [hx.1.1, hx.1.2]
    have hyfront : x - d ∈ frontier X.base := (hfront_shift (x - d)).mp (by
      simpa [sub_add_cancel] using hx.2)
    have hcontra : x - d ∈ Ioo a b ∩ frontier X.base := ⟨hy, hyfront⟩
    rw [hdisj] at hcontra
    exact hcontra
  exact ⟨hablt', haf', hbf', habase', hdisj'⟩

open Set
open scoped Pointwise



open Tiling.AxisParallel.Terminal

private theorem sameIntegerPhase_equivalence : Equivalence SameIntegerPhase := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ⟨0, by norm_num⟩
  · intro x y hxy
    rcases hxy with ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    rw [sub_eq_iff_eq_add] at hn ⊢
    rw [hn]
    norm_num
  · intro x y z hxy hyz
    rcases hxy with ⟨m, hm⟩
    rcases hyz with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    calc
      x - z = (x - y) + (y - z) := by ring
      _ = (m : ℝ) + (n : ℝ) := by rw [hm, hn]
      _ = ((m + n : ℤ) : ℝ) := by norm_num

open Set



open Tiling.AxisParallel

private theorem tilesOn_openUnion_subset_regularTarget
    {K : Region} {S D : Set Tiling.Plane}
    (hDopen : IsOpen D) (hDregular : interior (closure D) = D)
    (hTile : TilesOn K S D) :
    openUnion K S ⊆ D := by
  have hsupp : regularSupport K S = D :=
    regularSupport_eq_of_tilesOn hDopen hDregular hTile
  rw [← hsupp]
  have hopen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    change IsOpen ((Homeomorph.addLeft (s : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
  exact hopen.subset_interior_closure

open Filter MeasureTheory Set
open scoped Pointwise



open Tiling.AxisParallel
open Tiling.AxisParallel.Foundations.FilledSliceChains
open Tiling.AxisParallel.Terminal

private theorem carrier_openUnion_subset
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    openUnion K T ⊆ X.carrier := by
  have hopen : IsOpen X.carrier := X.base_open.preimage Complex.continuous_re
  have hregular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      X.base_regular]
  have hsupp : regularSupport K T = X.carrier :=
    regularSupport_eq_of_tilesOn hopen hregular hTile
  have hopenUnion : IsOpen (openUnion K T) := by
    apply isOpen_iUnion
    intro t
    exact isOpen_interior.vadd t.1
  rw [← hsupp]
  exact hopenUnion.subset_interior_closure

private theorem eventually_carrier_horizontal_slice
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      x ∈ X.base → slicePoint Axis.horizontal q x ∈ openUnion K T := by
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      z ∈ X.carrier → z ∈ openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    exact fun hcarrier => by
      rw [openUnion, Tiling.Polygonal.openUnion,
        ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact hz.mp hcarrier
  have hpull :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae
      hplane
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hpull
  have hslices := Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) hswap
  filter_upwards [hslices] with q hq
  filter_upwards [hq] with x hx
  have heq : slicePoint Axis.horizontal q x =
      Complex.measurableEquivRealProd.symm (q, x).swap := by
    apply Complex.ext <;> simp [slicePoint]
  rw [heq]
  exact hx

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
  have hp' : ∀ᵐ x ∂volume.restrict (Ioo a b), P x :=
    hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, hp, hx⟩
  exact ⟨x, hx, hp⟩

private theorem interval_subset_closure_of_local_ae
    {U : Set ℝ} {a b : ℝ}
    (hfull : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo a b → x ∈ U) :
    Ioo a b ⊆ closure U := by
  have hdense : Dense {x : ℝ | x ∈ Ioo a b → x ∈ U} :=
    volume.dense_of_ae hfull
  intro x hx
  rw [mem_closure_iff]
  intro V hVopen hxV
  have hVOopen : IsOpen (V ∩ Ioo a b) := hVopen.inter isOpen_Ioo
  have hVOne : (V ∩ Ioo a b).Nonempty := ⟨x, hxV, hx⟩
  obtain ⟨y, hy, hyVO⟩ := hdense.exists_mem_open hVOopen hVOne
  exact ⟨y, hyVO.1, hy hyVO.2⟩

private theorem endpoint_mem_frontier_of_local_ae
    {U : Set ℝ} {a b : ℝ} (X : PeriodicVerticalCarrier) (hab : a < b)
    (hfull : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo a b → x ∈ U)
    (hUsub : U ⊆ X.base) (ha : a ∈ frontier X.base) :
    a ∈ frontier U := by
  have hcl : Ioo a b ⊆ closure U :=
    interval_subset_closure_of_local_ae hfull
  have haI : a ∈ closure (Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact left_mem_Icc.mpr (le_of_lt hab)
  have haClosure : a ∈ closure U :=
    (closure_minimal hcl isClosed_closure) haI
  have haNotBase : a ∉ X.base := by
    intro haBase
    have haInterior : a ∈ interior X.base := by
      rw [X.base_open.interior_eq]
      exact haBase
    exact Set.disjoint_left.mp disjoint_interior_frontier haInterior ha
  have haNotU : a ∉ U := fun haU => haNotBase (hUsub haU)
  rw [frontier]
  exact ⟨haClosure, fun haInt => haNotU (interior_subset haInt)⟩

private theorem filledChain_vertex_re_integer
    {K : Region}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    ∀ v : K.vertices, ∃ z : ℤ, v.1.re = z := by
  intro v
  obtain ⟨m, n, hv⟩ := hIntegral v.1 v.2
  refine ⟨m, ?_⟩
  simpa using congrArg Complex.re hv

/-- Every endpoint of a heterogeneous generic horizontal chain has an integral
offset from its first endpoint.  The proof only uses the chain's intrinsic
vertex witnesses; no fixed one-dimensional prototile is introduced. -/
private theorem filledChain_prefix_integer
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner) :
    ∀ k : Fin (n + 1), ∃ z : ℤ, x k - x 0 = z := by
  have hVertexRe := filledChain_vertex_re_integer hIntegral
  obtain ⟨_hmono, hsteps⟩ := hchain
  have hstep (i : Fin n) : ∃ z : ℤ,
      x i.succ - x i.castSucc = z := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _hgap⟩ := hsteps i
    obtain ⟨zv, hzv⟩ := hVertexRe ⟨v, hv⟩
    obtain ⟨zw, hzw⟩ := hVertexRe ⟨w, hw⟩
    refine ⟨zw - zv, ?_⟩
    simp only [Axis.coord, Complex.add_re] at hleft hright
    rw [Int.cast_sub]
    linarith
  intro k
  refine Fin.induction ?_ (fun k ih ↦ ?_) k
  · exact ⟨0, by simp⟩
  · obtain ⟨e, he⟩ := hstep k
    obtain ⟨p, hp⟩ := ih
    refine ⟨p + e, ?_⟩
    calc
      x k.succ - x 0 = (x k.castSucc - x 0) +
          (x k.succ - x k.castSucc) := by ring
      _ = (p : ℝ) + (e : ℝ) := by rw [hp, he]
      _ = (p + e : ℤ) := by exact (Int.cast_add p e).symm

/-- The total displacement of a heterogeneous finite chain is integral. -/
private theorem filledChain_difference_integer
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner) :
    ∃ z : ℤ, x (Fin.last n) - x 0 = z :=
  filledChain_prefix_integer hIntegral hchain (Fin.last n)

private theorem chain_endpoint_difference_integer
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner)
    {a b : ℝ} (hfirst : x 0 = a) (hlast : x (Fin.last n) = b) :
    ∃ z : ℤ, b - a = z := by
  obtain ⟨z, hz⟩ := filledChain_difference_integer hIntegral hchain
  refine ⟨z, ?_⟩
  simpa [hfirst, hlast] using hz

private theorem chain_endpoint_positive_nat
    {a b : ℝ} (hab : a < b) (hz : ∃ z : ℤ, b - a = z) :
    ∃ n : ℕ, 0 < n ∧ b - a = n := by
  obtain ⟨z, hz⟩ := hz
  have hzpos : 0 < z := by
    have hzpos' : (0 : ℝ) < (z : ℝ) := by
      rw [← hz]
      linarith
    exact_mod_cast hzpos'
  have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (le_of_lt hzpos)
  have hzNatPos : 0 < z.toNat := by
    by_contra hn
    have hn0 : z.toNat = 0 := Nat.eq_zero_of_not_pos hn
    have hz0 : z = 0 := by simpa [hn0] using hzcast.symm
    linarith
  refine ⟨z.toNat, hzNatPos, ?_⟩
  have hzcastR : (z.toNat : ℝ) = (z : ℝ) := by exact_mod_cast hzcast
  exact hz.trans hzcastR.symm

private theorem strictMono_exists_gap {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) {u : ℝ} (hleft : x 0 < u)
    (hright : u < x (Fin.last n)) (hne : ∀ k, u ≠ x k) :
    ∃ i : Fin n, u ∈ Ioo (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => exfalso; simpa using (lt_asymm hleft hright)
  | succ n ih =>
      rcases lt_trichotomy u (x 1) with hu | hu | hu
      · exact ⟨⟨0, Nat.succ_pos _⟩, hleft, hu⟩
      · exact False.elim (hne 1 hu)
      · let y : Fin (n + 1) → ℝ := fun k ↦ x k.succ
        have hy : StrictMono y := by
          intro i j hij
          apply hx
          simpa using hij
        have hylast : u < y (Fin.last n) := by
          simpa [y] using hright
        have hyne : ∀ k, u ≠ y k := fun k ↦ hne k.succ
        obtain ⟨i, hi⟩ := ih y hy hu hylast hyne
        refine ⟨i.succ, ?_⟩
        simpa [y] using hi

private theorem filledChain_owner_eq_of_mem
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hTile : TilesOn K T X.carrier)
    {q : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ} {owner : Fin n → T}
    (hchain : IsFilledIndexedSliceChain K T Axis.horizontal q x owner)
    (i : Fin n) (t : T) {z : Tiling.Plane}
    (hzi : z ∈ axisInterval Axis.horizontal q (x i.castSucc) (x i.succ))
    (hzt : z ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier) :
    owner i = t := by
  by_contra hne
  have hd := (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
    (owner i).2 t.2 (fun h ↦ hne (Subtype.ext h))
  obtain ⟨_v, _w, _hv, _hw, _hleft, _hright, _hpositive, hinside⟩ :=
    hchain.2 i
  exact Set.disjoint_left.mp hd (hinside hzi) hzt

theorem integralRegion_genericSections :
  ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
      (X : PeriodicVerticalCarrier),
    Tiling.AxisParallel.TilesOn K T X.carrier →
    (∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) →
    ∀ {a b : ℝ}, a < b →
      a ∈ frontier X.base → b ∈ frontier X.base →
      (Ioo a b ⊆ X.base ∧ Ioo a b ∩ frontier X.base = ∅) →
      ∀ {t : T},
        ((t.1 +ᵥ K.openCarrier) ∩
          {z : Tiling.Plane | z.re ∈ Ioo a b}).Nonempty →
        (∃ n : ℤ, t.1.re = a + n) ∧
          ∃ n : ℕ, 0 < n ∧ b - a = n := by
  intro K T X hTile hIntegral a b hab ha hb hcomponent t hmeets
  rcases hmeets with ⟨z, hzt, hzab⟩
  let f : ℝ → Tiling.Plane :=
    fun q ↦ (z.re : ℂ) + (q : ℂ) * Complex.I
  have hf : Continuous f := by fun_prop
  have hfz : f z.im = z := by
    apply Complex.ext <;> simp [f]
  have hfnhds : f ⁻¹' ((t.1 : Tiling.Plane) +ᵥ K.openCarrier) ∈
      𝓝 z.im := by
    apply hf.continuousAt.preimage_mem_nhds
    rw [hfz]
    exact (isOpen_interior.vadd t.1).mem_nhds hzt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hfnhds
  let J : Set ℝ := Ioo (z.im - δ / 2) (z.im + δ / 2)
  have hJ : volume J ≠ 0 := by
    rw [Real.volume_Ioo]
    simp [ENNReal.ofReal_eq_zero]
    linarith
  have hgood := eventually_carrier_horizontal_slice X hTile
  have hchain := genericSliceChain_betweenEndpoints_of_local_ae
    (K := K) (S := T) hTile.2.1 Axis.horizontal
  have hex := exists_mem_Ioo_of_ae_real
      (a := z.im - δ / 2) (b := z.im + δ / 2)
      (by linarith)
      (hgood.and hchain)
  obtain ⟨q, hqJ, hq⟩ := hex
  obtain ⟨hqgood, hqchain⟩ := hq
  have hqball : q ∈ Metric.ball z.im δ := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hqJ.1, hqJ.2]
  have hqtile : f q ∈ (t.1 : Tiling.Plane) +ᵥ K.openCarrier :=
    hδsub hqball
  have hqpoint : slicePoint Axis.horizontal q z.re ∈
      (t.1 : Tiling.Plane) +ᵥ K.openCarrier := by
    simpa [f, slicePoint] using hqtile
  let U : Set ℝ := {x : ℝ |
    slicePoint Axis.horizontal q x ∈ openUnion K T}
  have hUopen : IsOpen U := by
    change IsOpen ((slicePoint Axis.horizontal q) ⁻¹' openUnion K T)
    apply IsOpen.preimage
    · unfold slicePoint
      fun_prop
    · apply isOpen_iUnion
      intro s
      exact isOpen_interior.vadd s.1
  have hUsub : U ⊆ X.base := by
    intro x hx
    have hcarrier := carrier_openUnion_subset X hTile hx
    change (slicePoint Axis.horizontal q x).re ∈ X.base at hcarrier
    simpa [slicePoint] using hcarrier
  have hfull : ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo a b → slicePoint Axis.horizontal q x ∈ openUnion K T := by
    filter_upwards [hqgood] with x hx
    intro hxI
    exact hx (hcomponent.1 hxI)
  have haE : a ∈ sliceEndpointSet K T Axis.horizontal q := by
    rw [sliceEndpointSet]
    change a ∈ frontier U
    exact endpoint_mem_frontier_of_local_ae X hab hfull hUsub ha
  have hbE : b ∈ sliceEndpointSet K T Axis.horizontal q := by
    have hbClosure : b ∈ closure U := by
      have hcl : Ioo a b ⊆ closure U :=
        interval_subset_closure_of_local_ae hfull
      have hbI : b ∈ closure (Ioo a b) := by
        rw [closure_Ioo (ne_of_lt hab)]
        exact right_mem_Icc.mpr (le_of_lt hab)
      exact (closure_minimal hcl isClosed_closure) hbI
    have hbNotBase : b ∉ X.base := by
      intro hbBase
      have hbInterior : b ∈ interior X.base := by
        rw [X.base_open.interior_eq]
        exact hbBase
      exact Set.disjoint_left.mp disjoint_interior_frontier hbInterior hb
    have hbNotU : b ∉ U := fun hbU => hbNotBase (hUsub hbU)
    rw [sliceEndpointSet]
    change b ∈ frontier U
    rw [frontier]
    exact ⟨hbClosure, fun hbInt => hbNotU (interior_subset hbInt)⟩
  obtain ⟨n, _hn, x, owner, hx0, hxlast, hfilled, hendpoints⟩ :=
    hqchain a haE b hbE hab hfull
  have hzU : z.re ∈ U := by
    change slicePoint Axis.horizontal q z.re ∈ openUnion K T
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨t, hqpoint⟩
  have hne : ∀ k, z.re ≠ x k := by
    intro k heq
    have hkE : x k ∈ sliceEndpointSet K T Axis.horizontal q := hendpoints k
    have hkFront : x k ∈ frontier U := by
      simpa [sliceEndpointSet, U] using hkE
    have hzFront : z.re ∈ frontier U := by simpa [heq] using hkFront
    have hzInterior : z.re ∈ interior U := by
      rw [hUopen.interior_eq]
      exact hzU
    exact Set.disjoint_left.mp disjoint_interior_frontier hzInterior hzFront
  have hleft : x 0 < z.re := by rw [hx0]; exact hzab.1
  have hright : z.re < x (Fin.last n) := by rw [hxlast]; exact hzab.2
  obtain ⟨i, hi⟩ := strictMono_exists_gap x hfilled.1 hleft hright hne
  have hzi : slicePoint Axis.horizontal q z.re ∈
      axisInterval Axis.horizontal q (x i.castSucc) (x i.succ) := by
    exact ⟨by simp [slicePoint], by simpa [slicePoint] using hi⟩
  have howner : owner i = t :=
    filledChain_owner_eq_of_mem hTile hfilled i t hzi hqpoint
  obtain ⟨v, w, hv, hw, hleftv, _hrightv, _hpositive, _hinside⟩ :=
    hfilled.2 i
  obtain ⟨p, hp⟩ := filledChain_prefix_integer hIntegral hfilled i.castSucc
  obtain ⟨zv, hzv⟩ := filledChain_vertex_re_integer hIntegral ⟨v, hv⟩
  have htphase : ∃ m : ℤ, t.1.re = a + m := by
    refine ⟨p - zv, ?_⟩
    rw [Int.cast_sub]
    rw [howner] at hleftv
    simp only [Axis.coord, Complex.add_re] at hleftv
    linarith [hp, hx0, hzv]
  have hdiff := chain_endpoint_difference_integer hIntegral hfilled hx0 hxlast
  exact ⟨htphase, chain_endpoint_positive_nat hab hdiff⟩

open Bornology Set
open scoped Pointwise
open MeasureTheory



open Tiling.AxisParallel
open Tiling.AxisParallel.Terminal

private theorem sameIntegerPhase_symm_local {x y : ℝ} :
    SameIntegerPhase x y → SameIntegerPhase y x := by
  rintro ⟨n, hn⟩
  refine ⟨-n, ?_⟩
  rw [sub_eq_iff_eq_add] at hn ⊢
  rw [hn]
  norm_num

private theorem sameIntegerPhase_trans_local {x y z : ℝ} :
    SameIntegerPhase x y → SameIntegerPhase y z → SameIntegerPhase x z := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (m : ℝ) + (n : ℝ) := by rw [hm, hn]
    _ = ((m + n : ℤ) : ℝ) := by norm_num

private theorem phase_openUnion_subset
    {K : Region} {S : Set Tiling.Plane} {D : Set Tiling.Plane}
    (hDopen : IsOpen D) (hDregular : interior (closure D) = D)
    (hTile : TilesOn K S D) :
    openUnion K S ⊆ D := by
  have hsupp : regularSupport K S = D :=
    regularSupport_eq_of_tilesOn hDopen hDregular hTile
  rw [← hsupp]
  have hopen : IsOpen (openUnion K S) := by
    apply isOpen_iUnion
    intro s
    change IsOpen ((Homeomorph.addLeft (s : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (s : Tiling.Plane)).isOpenMap _ isOpen_interior
  exact hopen.subset_interior_closure

private theorem phaseDecomposition_tiles :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    TilesOn K T X.carrier := by
  intro K T X phases phaseBase phaseCentres hPhase
  let I := {c // c ∈ phases}
  have hphaseDopen (c : I) :
      IsOpen (Complex.re ⁻¹' phaseBase c.1) := by
    exact (hPhase.phaseBase_open c.1 c.2).preimage Complex.continuous_re
  have hphaseDregular (c : I) :
      interior (closure (Complex.re ⁻¹' phaseBase c.1)) =
        Complex.re ⁻¹' phaseBase c.1 := by
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      hPhase.phaseBase_regular c.1 c.2]
  have hphaseSubset (c : I) :
      ∀ {s : Tiling.Plane}, s ∈ phaseCentres c.1 →
        s +ᵥ K.openCarrier ⊆ Complex.re ⁻¹' phaseBase c.1 := by
    intro s hs z hz
    apply phase_openUnion_subset (hphaseDopen c) (hphaseDregular c)
      (hPhase.phase_tiles c.1 c.2)
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    exact ⟨⟨s, hs⟩, hz⟩
  have hpack :
      Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements T) := by
    apply (isPacking_iff_openCarrier_disjoint K T).2
    intro s hs t ht hst
    have hs' : s ∈ ⋃ c : I, phaseCentres c.1 := by
      have hs0 : s ∈ ⋃ c : phases, phaseCentres c := by
        rw [hPhase.phaseCentres_union]
        exact hs
      simpa [I] using hs0
    have ht' : t ∈ ⋃ c : I, phaseCentres c.1 := by
      have ht0 : t ∈ ⋃ c : phases, phaseCentres c := by
        rw [hPhase.phaseCentres_union]
        exact ht
      simpa [I] using ht0
    rw [Set.mem_iUnion] at hs' ht'
    obtain ⟨c, hsc⟩ := hs'
    obtain ⟨d, htd⟩ := ht'
    by_cases hcd : c = d
    · subst d
      exact (isPacking_iff_openCarrier_disjoint K (phaseCentres c.1)).mp
        (hPhase.phase_tiles c.1 c.2).2.1 hsc htd hst
    · have hcd' : c.1 ≠ d.1 := by
        intro h
        exact hcd (Subtype.ext h)
      have hdis : Disjoint (phaseBase c.1) (phaseBase d.1) :=
        hPhase.phaseBases_pairwise c.2 d.2 hcd'
      change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
      rw [Set.disjoint_left]
      intro z hzs hzt
      exact Set.disjoint_left.1 hdis
        ((hphaseSubset c hsc) hzs) ((hphaseSubset d htd) hzt)
  have hTcount : T.Countable :=
    (IsPacking.locallyFinite_centres hpack).2
  let pick : I → Tiling.Plane := fun c =>
    Classical.choose (hPhase.phaseCentres_nonempty c.1 c.2)
  have pick_mem (c : I) : pick c ∈ phaseCentres c.1 := by
    exact Classical.choose_spec (hPhase.phaseCentres_nonempty c.1 c.2)
  have pick_mem_T (c : I) : pick c ∈ T := by
    rw [← hPhase.phaseCentres_union]
    exact mem_iUnion.mpr ⟨c, pick_mem c⟩
  have pick_inj : Function.Injective pick := by
    intro c d hcd
    by_contra hne
    have hne' : c.1 ≠ d.1 := by
      intro h
      exact hne (Subtype.ext h)
    have hdis := hPhase.phaseCentres_pairwise c.2 d.2 hne'
    exact Set.disjoint_left.1 hdis (pick_mem c) (hcd ▸ pick_mem d)
  have hIcount : (Set.univ : Set I).Countable := by
    apply Set.countable_of_injective_of_countable_image
      (Set.injOn_of_injective pick_inj)
    apply hTcount.mono
    rintro z ⟨c, -, rfl⟩
    exact pick_mem_T c
  let _ : Countable (Set.univ : Set I) := hIcount.to_subtype
  let _ : Countable I := Countable.of_equiv (Set.univ : Set I)
    (Equiv.Set.univ I)
  have hparts : Set.PairwiseDisjoint (Set.univ : Set I)
      (fun c : I => phaseCentres c.1) := by
    intro c hc d hd hcd
    have hcd' : c.1 ≠ d.1 := by
      intro h
      exact hcd (Subtype.ext h)
    exact hPhase.phaseCentres_pairwise c.2 d.2 hcd'
  have hVeq :
      (⋃ c : I, Complex.re ⁻¹' phaseBase c.1) =
        Complex.re ⁻¹' (⋃ c : phases, phaseBase c) := by
    ext z
    simp [I]
  have hsupport : regularSupport K T = X.carrier := by
    have hUnion : (⋃ c : I, phaseCentres c.1) = T := by
      simpa [I] using hPhase.phaseCentres_union
    rw [← hUnion, regularSupport_iUnion]
    rw [show (⋃ c : I, regularSupport K (phaseCentres c.1)) =
      ⋃ c : I, Complex.re ⁻¹' phaseBase c.1 by
      apply iUnion_congr
      intro c
      exact regularSupport_eq_of_tilesOn (hphaseDopen c) (hphaseDregular c)
        (hPhase.phase_tiles c.1 c.2)]
    rw [hVeq]
    change interior (closure (Complex.re ⁻¹' (⋃ c : phases, phaseBase c))) =
      Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      hPhase.phaseBases_cover]
  refine ⟨hTcount, hpack, ?_⟩
  have hAE := openUnion_aeEq_regularSupport hpack
  rw [hsupport] at hAE
  filter_upwards [hAE] with z hz
  constructor
  · intro hzC
    have hzU : z ∈ openUnion K T := (iff_of_eq hz).mpr hzC
    rw [openUnion] at hzU
    exact Set.mem_iUnion.mp hzU
  · intro hzU
    have hzU' : z ∈ openUnion K T := by
      rw [openUnion]
      exact Set.mem_iUnion.mpr hzU
    exact (iff_of_eq hz).mp hzU'

private theorem phase_frontier_locallyFinite :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ a b : ℝ, (frontier X.base ∩ Icc a b).Finite := by
  intro K T X phases phaseBase phaseCentres _ hPhase a b
  have hTile : TilesOn K T X.carrier :=
    phaseDecomposition_tiles hPhase
  have hfinite := hTile.verticalCylinder_frontier_locallyFinite
    X.base_open X.base_regular (Icc a b) isCompact_Icc
  simpa [inter_comm] using hfinite

private theorem phaseBase_subset_carrier :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ c ∈ phases, phaseBase c ⊆ X.base := by
  intro K T X phases phaseBase phaseCentres hPhase c hc
  rw [← hPhase.phaseBases_cover]
  apply interior_maximal
  · intro x hx
    apply subset_closure
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩
  · exact hPhase.phaseBase_open c hc

private theorem frontier_regularSupport_subset_tileFrontiers
    {K : Region} {T S : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hTile : TilesOn K T X.carrier) (hST : S ⊆ T) :
    frontier (regularSupport K S) ⊆
      ⋃ s : S, frontier ((s.1 : Tiling.Plane) +ᵥ K.support) := by
  have hpackingS : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S) := by
    apply (isPacking_iff_openCarrier_disjoint K S).mpr
    intro s hs t ht hst
    exact (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      (hST hs) (hST ht) hst
  intro p hp
  have hpclosure : p ∈ closure (openUnion K S) := by
    have hp' := frontier_interior_subset hp
    simpa only [closure_closure] using frontier_subset_closure hp'
  rw [closure_openUnion_eq_iUnion_support hpackingS] at hpclosure
  obtain ⟨s, hps⟩ := Set.mem_iUnion.mp hpclosure
  apply Set.mem_iUnion_of_mem s
  rw [frontier, (K.isPolygonal.vadd s.1).isClosed.closure_eq]
  refine ⟨hps, ?_⟩
  intro hpint
  have hpreg : p ∈ regularSupport K S := by
    apply interior_mono ?_ hpint
    rw [closure_openUnion_eq_iUnion_support hpackingS]
    exact subset_iUnion (fun q : S ↦ (q.1 : Tiling.Plane) +ᵥ K.support) s
  rw [frontier] at hp
  apply hp.2
  change p ∈ interior (interior (closure (openUnion K S)))
  simpa only [regularSupport, Tiling.Polygonal.regularSupport,
    ← openUnion.eq_def, interior_interior] using hpreg

private theorem phaseBoundary_exists_tileFrontier
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    {phases : Set ℝ} {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    (hTile : TilesOn K T X.carrier)
    {c : ℝ} (hc : c ∈ phases) {x : ℝ} (hx : x ∈ frontier (phaseBase c))
    (y : ℝ) :
    ∃ s ∈ phaseCentres c,
      Complex.mk x y ∈ frontier ((s : Tiling.Plane) +ᵥ K.support) := by
  have hreg : regularSupport K (phaseCentres c) =
      (Complex.re ⁻¹' phaseBase c) :=
    regularSupport_eq_of_tilesOn
      ((hPhase.phaseBase_open c hc).preimage Complex.continuous_re)
      (by
        rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
          hPhase.phaseBase_regular c hc])
      (hPhase.phase_tiles c hc)
  have hp : Complex.mk x y ∈ frontier (regularSupport K (phaseCentres c)) := by
    rw [hreg]
    change Complex.mk x y ∈
      frontier ({z : Tiling.Plane | z.re ∈ phaseBase c} : Set Tiling.Plane)
    rw [frontier_verticalCylinder]
    exact hx
  have hsub := frontier_regularSupport_subset_tileFrontiers hTile
    (by intro s hs; rw [← hPhase.phaseCentres_union]; exact mem_iUnion.mpr ⟨⟨c, hc⟩, hs⟩) hp
  rw [Set.mem_iUnion] at hsub
  obtain ⟨s, hs⟩ := hsub
  exact ⟨s.1, s.2, hs⟩

private theorem translated_frontier_vertexGrid
    {K : Region} {s z : Tiling.Plane}
    (hz : z ∈ frontier (s +ᵥ K.support)) :
    (∃ v ∈ K.vertices, z.re = s.re + v.re) ∨
      ∃ v ∈ K.vertices, z.im = s.im + v.im := by
  have hz' : z - s ∈ frontier K.support := by
    have hzfront := hz
    rw [frontier_vadd_eq] at hzfront
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_eq_sub] using hzfront
  rcases Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid K hz' with h | h
  · left
    rcases h with ⟨v, hv, hvre⟩
    refine ⟨v, hv, ?_⟩
    have := hvre
    simpa only [Complex.sub_re, sub_eq_iff_eq_add, add_comm] using this
  · right
    rcases h with ⟨v, hv, hvim⟩
    refine ⟨v, hv, ?_⟩
    have := hvim
    simpa only [Complex.sub_im, sub_eq_iff_eq_add, add_comm] using this

private theorem phaseBoundaries_locallyFinite :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ Q : Set ℝ, IsBounded Q →
      ({x : ℝ | ∃ c ∈ phases, x ∈ frontier (phaseBase c)} ∩ Q).Finite := by
  intro K T X phases phaseBase phaseCentres hPhase Q hQ
  have hTile : TilesOn K T X.carrier :=
    phaseDecomposition_tiles hPhase
  let R : ℝ := Classical.choose (hQ.subset_closedBall (0 : ℝ))
  have hQR : Q ⊆ Icc (-R) R := by
    intro x hx
    have hxR := Classical.choose_spec (hQ.subset_closedBall (0 : ℝ)) hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hxR
    exact abs_le.mp hxR
  let C : Set Tiling.Plane :=
    (fun p : ℝ × ℝ => Complex.mk p.1 p.2) ''
      (Icc (-R) R ×ˢ Icc (-1 : ℝ) 1)
  have hC : IsCompact C := by
    apply (isCompact_Icc.prod isCompact_Icc).image
    have heq : (fun p : ℝ × ℝ => Complex.mk p.1 p.2) =
        (fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) := by
      funext p
      apply Complex.ext <;> simp
    rw [heq]
    fun_prop
  let P := K.polygonalProtoTiling T
  let F : Set P.placements :=
    {i | (Tiling.placedTile P.prototiles i.1 ∩ C).Nonempty}
  have hF : F.Finite := by
    exact (P.locallyFinite_placedTile hTile.2.1).finite_nonempty_inter_compact hC
  have hV : K.vertices.Finite := by
    simpa only [Region.vertices] using K.isPolygonal.vertexSet_finite
  let bad : Set ℝ :=
    (fun p : P.placements × Tiling.Plane => p.1.1.1.im + p.2.im) ''
      (F ×ˢ K.vertices)
  have hbad : bad.Finite := by
    exact (hF.prod hV).image _
  obtain ⟨y, hyI, hybad⟩ : ∃ y ∈ Ioo (-1 : ℝ) 1, y ∉ bad := by
    by_contra h
    push Not at h
    have hsub : Ioo (-1 : ℝ) 1 ⊆ bad := h
    exact (Set.Ioo_infinite (by norm_num)).not_finite (hbad.subset hsub)
  let coords : Set ℝ :=
    (fun p : P.placements × Tiling.Plane => p.1.1.1.re + p.2.re) ''
      (F ×ˢ K.vertices)
  have hcoords : coords.Finite := by
    exact (hF.prod hV).image _
  apply hcoords.subset
  rintro x ⟨⟨c, hc, hx⟩, hQx⟩
  have hxR : x ∈ Icc (-R) R := hQR hQx
  have hzC : Complex.mk x y ∈ C := by
    exact ⟨(x, y), ⟨hxR, ⟨le_of_lt hyI.1, le_of_lt hyI.2⟩⟩, rfl⟩
  obtain ⟨s, hs, hfront⟩ := phaseBoundary_exists_tileFrontier
    hPhase hTile hc hx y
  have hsT : s ∈ T := by
    rw [← hPhase.phaseCentres_union]
    exact mem_iUnion.mpr ⟨⟨c, hc⟩, hs⟩
  let sT : T := ⟨s, hsT⟩
  let i : P.placements := {
    val := ((sT : Tiling.Plane), ())
    property := sT.2 }
  have hiF : i ∈ F := by
    dsimp [F]
    refine ⟨Complex.mk x y, ?_, hzC⟩
    have hzsupport : Complex.mk x y ∈ (s : Tiling.Plane) +ᵥ K.support := by
      rw [← (K.isPolygonal.vadd s).isClosed.closure_eq]
      exact frontier_subset_closure hfront
    change Complex.mk x y ∈ (sT : Tiling.Plane) +ᵥ K.support
    simpa [sT] using hzsupport
  obtain hgrid | hgrid := translated_frontier_vertexGrid hfront
  · obtain ⟨v, hv, hvx⟩ := hgrid
    have hvx' : s.re + v.re = x := by simpa using hvx.symm
    exact ⟨⟨i, v⟩, ⟨hiF, hv⟩, by simpa [i, sT] using hvx'⟩
  · obtain ⟨v, hv, hvy⟩ := hgrid
    exfalso
    apply hybad
    exact ⟨⟨i, v⟩, ⟨hiF, hv⟩, hvy.symm⟩

private theorem phaseBase_no_internal_boundary
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {phases : Set ℝ}
    {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    {c : ℝ} (hc : c ∈ phases) {x : ℝ}
    (hxbase : x ∈ X.base) (hxfront : x ∈ frontier (phaseBase c)) : False := by
  let U : Set ℝ := ⋃ d : phases, phaseBase d.1
  have hxint : x ∈ interior (closure U) := by
    rw [show U = ⋃ d : phases, phaseBase d.1 by rfl,
      hPhase.phaseBases_cover]
    exact hxbase
  have hxcl : x ∈ closure U := interior_subset hxint
  have hxnotU : x ∉ U := by
    intro hxU
    rw [Set.mem_iUnion] at hxU
    obtain ⟨d, hxd⟩ := hxU
    by_cases hcd : c = d.1
    · have hxd' : x ∈ phaseBase c := hcd ▸ hxd
      exact (disjoint_interior_frontier.le_bot ⟨
        (by rw [(hPhase.phaseBase_open c hc).interior_eq]; exact hxd'), hxfront⟩)
    · have hdis : Disjoint (phaseBase c) (phaseBase d.1) :=
        hPhase.phaseBases_pairwise hc d.2 hcd
      have hxccl : x ∈ closure (phaseBase c) := frontier_subset_closure hxfront
      exact Set.disjoint_left.mp (hdis.closure_left
        (hPhase.phaseBase_open d.1 d.2)) hxccl hxd
  have hfinite := phaseBoundaries_locallyFinite hPhase
    (Icc (x - 1) (x + 1)) (Metric.isBounded_Icc _ _)
  let B : Set ℝ := {z : ℝ | ∃ d ∈ phases, z ∈ frontier (phaseBase d)}
  have hB : (B ∩ Icc (x - 1) (x + 1)).Finite := by
    simpa [B] using hfinite
  let F : Set ℝ := (B ∩ Icc (x - 1) (x + 1)) \ {x}
  have hF : F.Finite := hB.sdiff
  have hxF : x ∉ F := by
    intro h
    exact h.2 (mem_singleton x)
  have hFnhds : Fᶜ ∈ nhds x := hF.isClosed.isOpen_compl.mem_nhds hxF
  rcases Metric.mem_nhds_iff.mp hFnhds with ⟨ε, hε, hεF⟩
  rcases Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hxint) with
    ⟨η, hη, hηint⟩
  let d : ℝ := min ε (min η 1) / 8
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdε : 8 * d ≤ ε := by
    dsimp [d]
    nlinarith [min_le_left ε (min η 1)]
  have hdη : 8 * d ≤ η := by
    dsimp [d]
    nlinarith [min_le_right ε (min η 1), min_le_left η 1]
  have hd1 : 8 * d ≤ 1 := by
    dsimp [d]
    nlinarith [min_le_right ε (min η 1), min_le_right η 1]
  have hnoB : ∀ {z : ℝ}, z ∈ Ioo (x - 3 * d) (x + 3 * d) →
      z ∈ B → z = x := by
    intro z hz hzB
    by_contra hzx
    have hzIcc : z ∈ Icc (x - 1) (x + 1) := by
      constructor <;> nlinarith [hz.1, hz.2, hd1]
    have hzF : z ∈ F := ⟨⟨hzB, hzIcc⟩, by simpa using hzx⟩
    have hzε : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hz.1, hz.2, hdε, hε]
    exact (hεF hzε) hzF
  have hwLcl : x - 2 * d ∈ closure U := by
    apply interior_subset
    apply hηint
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> nlinarith [hdη]
  have hwRcl : x + 2 * d ∈ closure U := by
    apply interior_subset
    apply hηint
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> nlinarith [hdη]
  obtain ⟨yL, ⟨hyLball, hyLU⟩⟩ :=
    mem_closure_iff.mp hwLcl (Metric.ball (x - 2 * d) d)
      Metric.isOpen_ball (Metric.mem_ball_self hd)
  obtain ⟨yR, ⟨hyRball, hyRU⟩⟩ :=
    mem_closure_iff.mp hwRcl (Metric.ball (x + 2 * d) d)
      Metric.isOpen_ball (Metric.mem_ball_self hd)
  rw [Set.mem_iUnion] at hyLU hyRU
  obtain ⟨cL, hyLc⟩ := hyLU
  obtain ⟨cR, hyRc⟩ := hyRU
  have hyLbounds : x - 3 * d < yL ∧ yL < x - d := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyLball
    constructor <;> nlinarith
  have hyRbounds : x + d < yR ∧ yR < x + 3 * d := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyRball
    constructor <;> nlinarith
  have hsideL : Ioo yL x ⊆ phaseBase cL.1 := by
    intro z hz
    have hdis : Disjoint (Icc yL z) (frontier (phaseBase cL.1)) := by
      rw [Set.disjoint_left]
      intro q hq hqfront
      have hqB : q ∈ B := ⟨cL.1, cL.2, hqfront⟩
      have hqbounds : q ∈ Ioo (x - 3 * d) (x + 3 * d) := by
        constructor
        · linarith [hyLbounds.1, hq.1]
        · linarith [hq.2, hz.2]
      have hqx : q = x := hnoB hqbounds hqB
      subst q
      exact (not_lt_of_ge hq.2 hz.2)
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Icc hdis with hin | hout
    · exact interior_subset (hin ⟨le_of_lt hz.1, le_rfl⟩)
    · exfalso
      exact (interior_subset (hout ⟨le_rfl, le_of_lt hz.1⟩)) hyLc
  have hsideR : Ioo x yR ⊆ phaseBase cR.1 := by
    intro z hz
    have hdis : Disjoint (Icc z yR) (frontier (phaseBase cR.1)) := by
      rw [Set.disjoint_left]
      intro q hq hqfront
      have hqB : q ∈ B := ⟨cR.1, cR.2, hqfront⟩
      have hqbounds : q ∈ Ioo (x - 3 * d) (x + 3 * d) := by
        constructor
        · linarith [hz.1, hq.1]
        · linarith [hq.2, hyRbounds.2]
      have hqx : q = x := hnoB hqbounds hqB
      subst q
      exact (not_lt_of_ge hq.1 hz.1)
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Icc hdis with hin | hout
    · exact interior_subset (hin ⟨le_rfl, le_of_lt hz.2⟩)
    · exfalso
      exact (interior_subset (hout ⟨le_of_lt hz.2, le_rfl⟩)) hyRc
  have hxclL : x ∈ closure (phaseBase cL.1) := by
    apply closure_mono hsideL
    rw [closure_Ioo (ne_of_lt (by linarith [hyLbounds.2]))]
    exact ⟨le_of_lt (by linarith [hyLbounds.2, hd]), le_rfl⟩
  have hxclR : x ∈ closure (phaseBase cR.1) := by
    apply closure_mono hsideR
    rw [closure_Ioo (ne_of_lt (by linarith [hyRbounds.1]))]
    exact ⟨le_rfl, le_of_lt (by linarith [hyRbounds.1, hd])⟩
  have hxfrontL : x ∈ frontier (phaseBase cL.1) := by
    rw [frontier]
    refine ⟨hxclL, ?_⟩
    intro hxintL
    exact hxnotU (Set.mem_iUnion.mpr ⟨cL, interior_subset hxintL⟩)
  have hxfrontR : x ∈ frontier (phaseBase cR.1) := by
    rw [frontier]
    refine ⟨hxclR, ?_⟩
    intro hxintR
    exact hxnotU (Set.mem_iUnion.mpr ⟨cR, interior_subset hxintR⟩)
  have hsame : SameIntegerPhase cL.1 cR.1 :=
    sameIntegerPhase_trans_local
      (sameIntegerPhase_symm_local (hPhase.boundary_phase cL.1 cL.2 x hxfrontL))
      (hPhase.boundary_phase cR.1 cR.2 x hxfrontR)
  have hlabels : cL.1 = cR.1 :=
    hPhase.phase_representatives cL.1 cL.2 cR.1 cR.2 hsame
  have hcRe : cR = cL := Subtype.ext hlabels.symm
  subst cR
  have hxintL : x ∈ interior (closure (phaseBase cL.1)) := by
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨d, hd, ?_⟩
    intro z hz
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hz
    by_cases hzx : z = x
    · subst z
      exact hxclL
    by_cases hzx' : z < x
    · exact subset_closure (hsideL ⟨by linarith [hyLbounds.2, hz.1], hzx'⟩)
    · have hzx'' : x < z := lt_of_le_of_ne (le_of_not_gt hzx') (Ne.symm hzx)
      exact subset_closure (hsideR ⟨hzx'', by linarith [hyRbounds.1, hz.2]⟩)
  have hxphase : x ∈ phaseBase cL.1 := by
    rw [← hPhase.phaseBase_regular cL.1 cL.2]
    exact hxintL
  exact hxnotU (Set.mem_iUnion.mpr ⟨cL, hxphase⟩)

private theorem carrier_base_subset_phase_union
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {phases : Set ℝ}
    {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres) :
    X.base ⊆ ⋃ c : phases, phaseBase c.1 := by
  let U : Set ℝ := ⋃ c : phases, phaseBase c.1
  intro x hxbase
  have hxint : x ∈ interior (closure U) := by
    rw [show U = ⋃ c : phases, phaseBase c.1 by rfl,
      hPhase.phaseBases_cover]
    exact hxbase
  have hxcl : x ∈ closure U := interior_subset hxint
  by_contra hxnot
  have hfinite := phaseBoundaries_locallyFinite hPhase
    (Icc (x - 1) (x + 1)) (Metric.isBounded_Icc _ _)
  let B : Set ℝ := {z : ℝ | ∃ c ∈ phases, z ∈ frontier (phaseBase c)}
  have hB : (B ∩ Icc (x - 1) (x + 1)).Finite := by
    simpa [B] using hfinite
  let F : Set ℝ := (B ∩ Icc (x - 1) (x + 1)) \ {x}
  have hF : F.Finite := hB.sdiff
  have hxF : x ∉ F := by
    intro h
    exact h.2 (mem_singleton x)
  have hFnhds : Fᶜ ∈ nhds x := hF.isClosed.isOpen_compl.mem_nhds hxF
  rcases Metric.mem_nhds_iff.mp hFnhds with ⟨ε, hε, hεF⟩
  let d : ℝ := min ε 1 / 4
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hdε : 4 * d ≤ ε := by
    dsimp [d]
    nlinarith [min_le_left ε 1]
  have hd1 : 4 * d ≤ 1 := by
    dsimp [d]
    nlinarith [min_le_right ε 1]
  have hnoB : ∀ {z : ℝ}, z ∈ Ioo (x - d) (x + d) →
      z ∈ B → z = x := by
    intro z hz hzB
    by_contra hzx
    have hzIcc : z ∈ Icc (x - 1) (x + 1) := by
      constructor <;> nlinarith [hz.1, hz.2, hd1]
    have hzF : z ∈ F := ⟨⟨hzB, hzIcc⟩, by simpa using hzx⟩
    have hzε : z ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> nlinarith [hz.1, hz.2, hdε, hε]
    exact (hεF hzε) hzF
  obtain ⟨y, ⟨hyball, hyU⟩⟩ :=
    mem_closure_iff.mp hxcl (Metric.ball x d)
      Metric.isOpen_ball (Metric.mem_ball_self hd)
  have hyne : y ≠ x := by
    intro h
    exact hxnot (h ▸ hyU)
  rw [Set.mem_iUnion] at hyU
  obtain ⟨c₀, hyc₀⟩ := hyU
  have hybounds : x - d < y ∧ y < x + d := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hyball
    constructor <;> linarith [hyball.1, hyball.2]
  rcases lt_or_gt_of_ne hyne with hleft | hright
  · have hside : Ioo y x ⊆ phaseBase c₀.1 := by
      intro z hz
      have hdis : Disjoint (Icc y z) (frontier (phaseBase c₀.1)) := by
        rw [Set.disjoint_left]
        intro q hq hqfront
        have hqB : q ∈ B := ⟨c₀.1, c₀.2, hqfront⟩
        have hqbounds : q ∈ Ioo (x - d) (x + d) := by
          constructor <;> linarith [hybounds.1, hybounds.2, hq.1, hq.2, hz.1, hz.2]
        have hqx := hnoB hqbounds hqB
        subst q
        exact (not_lt_of_ge hq.2 hz.2)
      rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
        isPreconnected_Icc hdis with hin | hout
      · exact interior_subset (hin ⟨le_of_lt hz.1, le_rfl⟩)
      · exact False.elim ((interior_subset (hout ⟨le_rfl, le_of_lt hz.1⟩)) hyc₀)
    have hxclc : x ∈ closure (phaseBase c₀.1) := by
      apply closure_mono hside
      rw [closure_Ioo (ne_of_lt hleft)]
      exact ⟨le_of_lt hleft, le_rfl⟩
    have hxfront : x ∈ frontier (phaseBase c₀.1) := by
      rw [frontier]
      refine ⟨hxclc, ?_⟩
      intro hxintc
      exact hxnot (Set.mem_iUnion.mpr ⟨c₀, interior_subset hxintc⟩)
    exact phaseBase_no_internal_boundary hPhase c₀.2 hxbase hxfront
  · have hside : Ioo x y ⊆ phaseBase c₀.1 := by
      intro z hz
      have hdis : Disjoint (Icc z y) (frontier (phaseBase c₀.1)) := by
        rw [Set.disjoint_left]
        intro q hq hqfront
        have hqB : q ∈ B := ⟨c₀.1, c₀.2, hqfront⟩
        have hqbounds : q ∈ Ioo (x - d) (x + d) := by
          constructor <;> linarith [hybounds.1, hybounds.2, hq.1, hq.2, hz.1, hz.2]
        have hqx := hnoB hqbounds hqB
        subst q
        exact (not_lt_of_ge hq.1 hz.1)
      rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
        isPreconnected_Icc hdis with hin | hout
      · exact interior_subset (hin ⟨le_rfl, le_of_lt hz.2⟩)
      · exact False.elim ((interior_subset (hout ⟨le_of_lt hz.2, le_rfl⟩)) hyc₀)
    have hxclc : x ∈ closure (phaseBase c₀.1) := by
      apply closure_mono hside
      rw [closure_Ioo (ne_of_lt hright)]
      exact ⟨le_rfl, le_of_lt hright⟩
    have hxfront : x ∈ frontier (phaseBase c₀.1) := by
      rw [frontier]
      refine ⟨hxclc, ?_⟩
      intro hxintc
      exact hxnot (Set.mem_iUnion.mpr ⟨c₀, interior_subset hxintc⟩)
    exact phaseBase_no_internal_boundary hPhase c₀.2 hxbase hxfront

private theorem one_phase_contains_interval
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {phases : Set ℝ}
    {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    {a b : ℝ} (hab : a < b)
    (hcover : Ioo a b ⊆ ⋃ c : phases, phaseBase c.1) :
    ∃ c : phases, Ioo a b ⊆ phaseBase c.1 := by
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Ioo a b := by
    dsimp [m]
    constructor <;> linarith
  obtain ⟨c, hmc⟩ := Set.mem_iUnion.mp (hcover hm)
  let V : Set ℝ := ⋃ d : {d : phases // d ≠ c}, phaseBase d.1.1
  have hVopen : IsOpen V := by
    apply isOpen_iUnion
    intro d
    exact hPhase.phaseBase_open d.1.1 d.1.2
  have hdis : Disjoint (phaseBase c.1) V := by
    rw [Set.disjoint_left]
    intro z hzc hzV
    obtain ⟨d, hzd⟩ := Set.mem_iUnion.mp hzV
    have hne : c.1 ≠ d.1.1 := by
      intro h
      exact d.2 (Subtype.ext h.symm)
    exact Set.disjoint_left.mp
      (hPhase.phaseBases_pairwise c.2 d.1.2 hne) hzc hzd
  have hcover' : Ioo a b ⊆ phaseBase c.1 ∪ V := by
    intro z hz
    obtain ⟨d, hzd⟩ := Set.mem_iUnion.mp (hcover hz)
    by_cases hdc : d = c
    · exact Or.inl (hdc ▸ hzd)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨d, hdc⟩, hzd⟩)
  rcases isPreconnected_Ioo.subset_or_subset
      (hPhase.phaseBase_open c.1 c.2) hVopen hdis hcover' with hc | hV
  · exact ⟨c, hc⟩
  · exfalso
    exact Set.disjoint_left.mp hdis hmc (hV hm)

private theorem carrierComponent_has_unique_phase :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ {a b : ℝ}, IsCarrierComponent X a b →
      ∃! c : ℝ, c ∈ phases ∧ Ioo a b ⊆ phaseBase c := by
  intro K T X phases phaseBase phaseCentres _ hPhase a b hab
  rcases hab with ⟨hablt, _, _, hsubset, _⟩
  have hcover : Ioo a b ⊆ ⋃ c : phases, phaseBase c.1 := by
    intro x hx
    exact carrier_base_subset_phase_union hPhase (hsubset hx)
  obtain ⟨c, hc⟩ := one_phase_contains_interval hPhase hablt hcover
  refine ⟨c.1, ⟨c.2, hc⟩, ?_⟩
  intro d hd
  rcases hd with ⟨hd, hsubd⟩
  by_contra hne
  let m : ℝ := (a + b) / 2
  have hm : m ∈ Ioo a b := by
    dsimp [m]
    constructor <;> linarith
  have hmc : m ∈ phaseBase c.1 := hc hm
  have hmd : m ∈ phaseBase d := hsubd hm
  exact Set.disjoint_left.mp (hPhase.phaseBases_pairwise c.2 hd (Ne.symm hne)) hmc hmd

private theorem exists_frontier_mem_uIcc_local
    {S : Set ℝ} (hSopen : IsOpen S) {x y : ℝ}
    (hne : ¬ (x ∈ S ↔ y ∈ S)) :
    (frontier S ∩ uIcc x y).Nonempty := by
  by_contra hempty
  have hsub : uIcc x y ⊆ (frontier S)ᶜ := by
    intro z hz hzfront
    exact hempty ⟨z, hzfront, hz⟩
  have hunion : uIcc x y ⊆ S ∪ interior Sᶜ := by
    intro z hz
    have hz' := hsub hz
    rw [compl_frontier_eq_union_interior, hSopen.interior_eq] at hz'
    exact hz'
  have hdisj : Disjoint S (interior Sᶜ) :=
    Set.disjoint_of_subset_right interior_subset disjoint_compl_right
  rcases em (x ∈ S) with hx | hx
  · have hxint : (uIcc x y ∩ S).Nonempty := ⟨x, left_mem_uIcc, hx⟩
    have hall := ordConnected_uIcc.isPreconnected.subset_left_of_subset_union
      hSopen isOpen_interior hdisj hunion hxint
    exact hne ⟨(fun _ => hall right_mem_uIcc), fun _ => hx⟩
  · have hy : y ∈ S := by
      by_contra hy
      exact hne ⟨(fun h => False.elim (hx h)), fun h => False.elim (hy h)⟩
    have hyint : (uIcc x y ∩ S).Nonempty := ⟨y, right_mem_uIcc, hy⟩
    have hall := ordConnected_uIcc.isPreconnected.subset_left_of_subset_union
      hSopen isOpen_interior hdisj hunion hyint
    exact hx (hall left_mem_uIcc)

private theorem exists_component_at
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {phases : Set ℝ}
    {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hproper : X.base ≠ Set.univ)
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    {x : ℝ} (hx : x ∈ X.base) :
    ∃ a b : ℝ, IsCarrierComponent X a b ∧ x ∈ Ioo a b := by
  have hbase_fun : Function.Periodic (fun z : ℝ => z ∈ X.base) X.period := by
    intro z
    apply propext
    have hm : z + X.period ∈ X.period +ᵥ X.base ↔ z + X.period ∈ X.base := by
      rw [X.base_periodic]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hm
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hm.symm
  have hshift (z : ℝ) (n : ℤ) :
      z + (n : ℝ) * X.period ∈ X.base ↔ z ∈ X.base := by
    have h := hbase_fun.int_mul n z
    simpa [zsmul_eq_mul] using h
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∉ X.base := by
    by_contra h
    apply hproper
    exact Set.eq_univ_of_forall (by
      intro y
      by_contra hy
      exact h ⟨y, hy⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - y₀) / X.period)
  obtain ⟨m, hm⟩ := exists_nat_gt ((y₀ - x) / X.period)
  let yR : ℝ := y₀ + (n : ℝ) * X.period
  let yL : ℝ := y₀ - (m : ℝ) * X.period
  have hyR : x < yR := by
    dsimp [yR]
    have hmul := mul_lt_mul_of_pos_right hn X.period_pos
    have hmul' : x - y₀ < (n : ℝ) * X.period := by
      simpa [div_mul_cancel₀ _ (ne_of_gt X.period_pos)] using hmul
    linarith
  have hyL : yL < x := by
    dsimp [yL]
    have hmul := mul_lt_mul_of_pos_right hm X.period_pos
    have hmul' : y₀ - x < (m : ℝ) * X.period := by
      simpa [div_mul_cancel₀ _ (ne_of_gt X.period_pos)] using hmul
    linarith
  have hyRnot : yR ∉ X.base := by
    intro h
    exact hy₀ ((hshift y₀ (n : ℤ)).mp (by simpa [yR] using h))
  have hyLnot : yL ∉ X.base := by
    intro h
    have hs := hshift y₀ (-(m : ℤ))
    apply hy₀
    apply hs.mp
    simpa [yL, Int.cast_neg, sub_eq_add_neg, mul_neg] using h
  have hneL : ¬ (yL ∈ X.base ↔ x ∈ X.base) := by simp [hyLnot, hx]
  have hneR : ¬ (x ∈ X.base ↔ yR ∈ X.base) := by simp [hyRnot, hx]
  have hxint : x ∈ interior X.base := by
    rw [X.base_open.interior_eq]
    exact hx
  obtain ⟨a₀, ha₀F, ha₀I⟩ :=
    exists_frontier_mem_uIcc_local X.base_open hneL
  obtain ⟨b₀, hb₀F, hb₀I⟩ :=
    exists_frontier_mem_uIcc_local X.base_open hneR
  have ha₀I' : a₀ ∈ Icc yL x := by simpa [uIcc_of_le hyL.le] using ha₀I
  have hb₀I' : b₀ ∈ Icc x yR := by simpa [uIcc_of_le hyR.le] using hb₀I
  have hax : a₀ < x := by
    exact lt_of_le_of_ne ha₀I'.2 (by
      intro h
      subst a₀
      exact (disjoint_interior_frontier.le_bot ⟨
        hxint, ha₀F⟩))
  have hxb : x < b₀ := by
    exact lt_of_le_of_ne hb₀I'.1 (by
      intro h
      subst b₀
      exact (disjoint_interior_frontier.le_bot ⟨
        hxint, hb₀F⟩).elim)
  have hfiniteL := phase_frontier_locallyFinite hproper hPhase yL x
  have hfiniteR := phase_frontier_locallyFinite hproper hPhase x yR
  let FL : Set ℝ := frontier X.base ∩ Icc yL x
  let FR : Set ℝ := frontier X.base ∩ Icc x yR
  have hFL : FL.Finite := by simpa [FL] using hfiniteL
  have hFR : FR.Finite := by simpa [FR] using hfiniteR
  have hFLne : FL.Nonempty := ⟨a₀, ha₀F, ha₀I'⟩
  have hFRne : FR.Nonempty := ⟨b₀, hb₀F, hb₀I'⟩
  let a : ℝ := sSup FL
  let b : ℝ := sInf FR
  have ha : a ∈ FL := by
    dsimp [a]
    exact hFLne.csSup_mem hFL
  have hb : b ∈ FR := by
    dsimp [b]
    exact hFRne.csInf_mem hFR
  have haa : a < x := lt_of_le_of_ne ha.2.2 (by
    intro h
    have hfront : x ∈ frontier X.base := h ▸ ha.1
    exact (disjoint_interior_frontier.le_bot ⟨
      hxint, hfront⟩))
  have hbb : x < b := lt_of_le_of_ne hb.2.1 (by
    intro h
    have hfront : x ∈ frontier X.base := h ▸ hb.1
    exact (disjoint_interior_frontier.le_bot ⟨
      hxint, hfront⟩).elim)
  have hgap : Ioo a b ∩ frontier X.base = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases lt_trichotomy z x with hzx | rfl | hxz
    · have hzFL : z ∈ FL := by
        refine ⟨hz.2, ?_⟩
        exact ⟨le_of_lt (lt_of_le_of_lt ha.2.1 hz.1.1), le_of_lt hzx⟩
      exact (not_lt_of_ge (le_csSup hFL.bddAbove hzFL)) hz.1.1
    · exact (disjoint_interior_frontier.le_bot ⟨
        hxint, hz.2⟩)
    · have hzFR : z ∈ FR := by
        refine ⟨hz.2, ?_⟩
        exact ⟨le_of_lt hxz, le_of_lt (lt_of_lt_of_le hz.1.2 hb.2.2)⟩
      exact (not_lt_of_ge (csInf_le hFR.bddBelow hzFR)) hz.1.2
  have hdis : Disjoint (Ioo a b) (frontier X.base) := by
    rw [Set.disjoint_left]
    intro z hz hzfront
    have hz' : z ∈ Ioo a b ∩ frontier X.base := ⟨hz, hzfront⟩
    rw [hgap] at hz'
    exact hz'
  have hsubset : Ioo a b ⊆ X.base := by
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hdis with hin | hout
    · exact hin.trans interior_subset
    · exact False.elim ((interior_subset (hout ⟨haa, hbb⟩)) hx)
  refine ⟨a, b, ⟨haa.trans hbb, ha.1, hb.1, hsubset, hgap⟩, ⟨haa, hbb⟩⟩

private theorem phase_has_component :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ c ∈ phases, ∃ a b : ℝ,
      IsCarrierComponent X a b ∧
      Ioo a b ⊆ phaseBase c ∧ SameIntegerPhase a c := by
  intro K T X phases phaseBase phaseCentres hproper hPhase c hc
  obtain ⟨s, hs⟩ := hPhase.phaseCentres_nonempty c hc
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change z ∈ K.openCarrier at hz
  have hzphase : (s + z).re ∈ phaseBase c := by
    apply phase_openUnion_subset
      ((hPhase.phaseBase_open c hc).preimage Complex.continuous_re)
      (by
        rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
          hPhase.phaseBase_regular c hc])
      (hPhase.phase_tiles c hc)
    rw [openUnion]
    exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, by
      exact ⟨z, hz, rfl⟩⟩
  have hzbase : (s + z).re ∈ X.base :=
        phaseBase_subset_carrier hPhase c hc hzphase
  obtain ⟨a, b, hab, habmem⟩ :=
    exists_component_at hproper hPhase hzbase
  obtain ⟨d, ⟨hd, hdu⟩, huniq⟩ :=
    carrierComponent_has_unique_phase hproper hPhase hab
  have hxd : (s + z).re ∈ phaseBase d := hdu habmem
  have hdc : d = c := by
    by_contra hne
    exact Set.disjoint_left.mp (hPhase.phaseBases_pairwise hd hc hne) hxd hzphase
  have hsub : Ioo a b ⊆ phaseBase c := by
    simpa [hdc] using hdu
  have hafront : a ∈ frontier (phaseBase c) := by
    rw [frontier]
    refine ⟨?_, ?_⟩
    · apply closure_mono hsub
      rw [closure_Ioo (ne_of_lt hab.1)]
      exact ⟨le_rfl, le_of_lt hab.1⟩
    · intro haint
      have hacarrier : a ∈ X.base :=
        phaseBase_subset_carrier hPhase c hc (interior_subset haint)
      have haintbase : a ∈ interior X.base := by
        rw [X.base_open.interior_eq]
        exact hacarrier
      exact disjoint_interior_frontier.le_bot ⟨haintbase, hab.2.1⟩
  refine ⟨a, b, hab, hsub, hPhase.boundary_phase c hc a hafront⟩

private theorem component_phase_left_boundary
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {phases : Set ℝ}
    {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    {c : ℝ} (hc : c ∈ phases) {a b : ℝ}
    (hab : IsCarrierComponent X a b) (hsub : Ioo a b ⊆ phaseBase c) :
    SameIntegerPhase a c := by
  have hafront : a ∈ frontier (phaseBase c) := by
    rw [frontier]
    refine ⟨?_, ?_⟩
    · apply closure_mono hsub
      rw [closure_Ioo (ne_of_lt hab.1)]
      exact ⟨le_rfl, le_of_lt hab.1⟩
    · intro haint
      have hacarrier : a ∈ X.base :=
        phaseBase_subset_carrier hPhase c hc (interior_subset haint)
      have haintbase : a ∈ interior X.base := by
        rw [X.base_open.interior_eq]
        exact hacarrier
      exact disjoint_interior_frontier.le_bot ⟨haintbase, hab.2.1⟩
  exact hPhase.boundary_phase c hc a hafront

private theorem phaseBase_eq_componentsOfPhase :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ c ∈ phases,
      phaseBase c = {x : ℝ | ∃ a b : ℝ,
        IsCarrierComponent X a b ∧
        SameIntegerPhase a c ∧ x ∈ Ioo a b} := by
  intro K T X phases phaseBase phaseCentres hproper hPhase c hc
  ext x
  constructor
  · intro hx
    have hxbase : x ∈ X.base :=
      phaseBase_subset_carrier hPhase c hc hx
    obtain ⟨a, b, hab, hxI⟩ := exists_component_at hproper hPhase hxbase
    obtain ⟨d, ⟨hd, hdu⟩, huniq⟩ :=
      carrierComponent_has_unique_phase hproper hPhase hab
    have hxd : x ∈ phaseBase d := hdu hxI
    have hdc : d = c := by
      by_contra hne
      exact Set.disjoint_left.mp (hPhase.phaseBases_pairwise hd hc hne) hxd hx
    have hsub : Ioo a b ⊆ phaseBase c := by simpa [hdc] using hdu
    exact ⟨a, b, hab, component_phase_left_boundary hPhase hc hab hsub, hxI⟩
  · rintro ⟨a, b, hab, hac, hxI⟩
    obtain ⟨d, ⟨hd, hdu⟩, huniq⟩ :=
      carrierComponent_has_unique_phase hproper hPhase hab
    have hxd : x ∈ phaseBase d := hdu hxI
    have had : SameIntegerPhase a d :=
      component_phase_left_boundary hPhase hd hab hdu
    have hcd : c = d := hPhase.phase_representatives c hc d hd
      (sameIntegerPhase_trans_local (sameIntegerPhase_symm_local hac) had)
    simpa [hcd] using hxd

open Bornology Set
open scoped Pointwise



open Tiling.AxisParallel Tiling.AxisParallel.Terminal

theorem relativePlate_localFinite
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    T.Countable ∧
      (∀ Q : Set Tiling.Plane, IsBounded Q → (T ∩ Q).Finite) ∧
      openUnion K T ⊆ X.carrier ∧ regularSupport K T = X.carrier ∧
      ∀ a b : ℝ, (frontier X.base ∩ Icc a b).Finite := by
  have hcarrierOpen : IsOpen X.carrier := by
    exact X.base_open.preimage Complex.continuous_re
  have hcarrierRegular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, X.base_regular]
  have hsupp : regularSupport K T = X.carrier :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hopenUnion : IsOpen (openUnion K T) := by
    apply isOpen_iUnion
    intro t
    change IsOpen ((Homeomorph.addLeft (t : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ isOpen_interior
  have hlocal := IsPacking.locallyFinite_centres hTile.2.1
  refine ⟨hTile.1, hlocal.1, ?_, hsupp, ?_⟩
  · rw [← hsupp]
    exact hopenUnion.subset_interior_closure
  · intro a b
    have hfinite := hTile.verticalCylinder_frontier_locallyFinite
      X.base_open X.base_regular (Icc a b) isCompact_Icc
    simpa [inter_comm] using hfinite

private theorem frontier_finite_periodCell
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) :
    (frontier X.base ∩ Icc 0 X.period).Finite :=
  (relativePlate_localFinite X hTile).2.2.2.2 0 X.period

open Bornology Set
open scoped Pointwise



open Tiling.AxisParallel
open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.Terminal

theorem relativePlateGraph_minimality :
  ∀ {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier),
    TilesOn K T X.carrier →
    (∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧ P.support = Complex.re ⁻¹' P.base) ∧
    (∀ P : VerticalPlate K T, IsMinimalVerticalSlabSubfamily K T P.centres) ∧
    Set.range (@VerticalPlate.centres K T) =
      {S : Set Tiling.Plane | IsMinimalVerticalSlabSubfamily K T S} := by
  intro K T X hTile
  have h := relativeCarrier_verticalPlates hTile (by rfl)
    X.base_regular.symm (fun a b ↦ by
      simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
        X.base_open X.base_regular (Icc a b) isCompact_Icc)
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem relativePlate_verticalSliding :
  ∀ {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier),
    TilesOn K T X.carrier → ∀ shift : VerticalPlate K T → ℝ,
    TilesOn K (shiftVerticalPlates K T shift) X.carrier ∧
      (∀ P : VerticalPlate K T,
        regularSupport K ((((shift P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) =
          P.support) ∧
      ∀ Q : Set (VerticalPlate K T),
        regularSupport K
            (⋃ P : Q, ((((shift P.1 : ℝ) : ℂ) * Complex.I) +ᵥ P.1.centres)) =
          regularSupport K (⋃ P : Q, P.1.centres) := by
  intro K T X hTile shift
  have hboundary (a b : ℝ) : (frontier X.base ∩ Icc a b).Finite := by
    simpa only [inter_comm] using hTile.verticalCylinder_frontier_locallyFinite
      X.base_open X.base_regular (Icc a b) isCompact_Icc
  have hslab : ∀ P : VerticalPlate K T,
      P.base = interior (closure P.base) ∧
        P.support = Complex.re ⁻¹' P.base :=
    (relativeCarrier_verticalPlates hTile (by rfl)
      X.base_regular.symm hboundary).1
  have hshiftTile := tilesOn_shiftVerticalPlates hTile (by rfl)
    X.base_regular.symm hboundary shift
  have hcentres (P : VerticalPlate K T) : P.centres ⊆ T := by
    rintro s ⟨q, -, rfl⟩
    exact q.2
  have hplateTile (P : VerticalPlate K T) :
      TilesOn K P.centres P.support := by
    have hpacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements P.centres) := by
      apply (isPacking_iff_openCarrier_disjoint K P.centres).mpr
      exact fun s hs t ht hst ↦
        (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
          (hcentres P hs) (hcentres P ht) hst
    refine ⟨hTile.1.mono (hcentres P), hpacking, ?_⟩
    have hae := openUnion_aeEq_regularSupport hpacking
    filter_upwards [hae] with x hx
    have hunion : (∃ s : P.centres,
        x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) ↔
        x ∈ openUnion K P.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion,
        ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    change x ∈ P.support ↔ ∃ s : P.centres, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier
    rw [hunion]
    exact iff_of_eq hx.symm
  have hsupport (P : VerticalPlate K T) :
      regularSupport K ((((shift P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) =
        P.support := by
    let gamma (P : VerticalPlate K T) : Tiling.Plane :=
      ((shift P : ℝ) : ℂ) * Complex.I
    have hsupportInv (P : VerticalPlate K T) :
        gamma P +ᵥ P.support = P.support := by
      rw [(hslab P).2]
      ext z
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage,
        vadd_eq_add, gamma]
      simp
    have hshiftedTile :
        TilesOn K (gamma P +ᵥ P.centres) P.support := by
      have h := tilesOn_translate (hplateTile P) (gamma P)
      rwa [hsupportInv] at h
    have hPopen : IsOpen P.support := by
      rw [(hslab P).2]
      have hbaseOpen : IsOpen P.base := by
        rw [(hslab P).1]
        exact isOpen_interior
      exact hbaseOpen.preimage Complex.continuous_re
    have hPreg : interior (closure P.support) = P.support := by
      rw [(hslab P).2, Complex.closure_preimage_re,
        Complex.interior_preimage_re, ← (hslab P).1]
    simpa [gamma] using
      (regularSupport_eq_of_tilesOn hPopen hPreg hshiftedTile)
  have hsubfamily (Q : Set (VerticalPlate K T)) :
      regularSupport K
          (⋃ P : Q, ((((shift P.1 : ℝ) : ℂ) * Complex.I) +ᵥ P.1.centres)) =
        regularSupport K (⋃ P : Q, P.1.centres) := by
    have hu :
        (⋃ P : Q, regularSupport K
            ((((shift P.1 : ℝ) : ℂ) * Complex.I) +ᵥ P.1.centres)) =
          ⋃ P : Q, regularSupport K P.1.centres := by
      apply Set.iUnion_congr
      intro P
      exact hsupport P.1
    rw [regularSupport_iUnion, regularSupport_iUnion]
    exact congrArg (fun S : Set Tiling.Plane => interior (closure S)) hu
  exact ⟨hshiftTile, hsupport, hsubfamily⟩

open Tiling.AxisParallel

private theorem unitCellGraphIso_of_contact
    {K : Region} {T : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane}
    (e : A ≃ T)
    (hcontact : ∀ z w : A,
      (Tiling.RationalPolygonal.quakeGraph F A
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Adj z w ↔
        (Tiling.AxisParallel.Continuous.verticalPlateGraph K T).Adj (e z) (e w)) :
    Nonempty
      (Tiling.RationalPolygonal.quakeGraph F A
          Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃g
        Tiling.AxisParallel.Continuous.verticalPlateGraph K T) :=
  ⟨{ toEquiv := e, map_rel_iff' := fun {z w} ↦ (hcontact z w).symm }⟩

open Set



private def rationalHomothety (q : ℕ) (z : Tiling.Plane) : Tiling.Plane :=
  (q : ℝ) * z

private theorem homothety_pullback_period :
    ∀ {q : ℕ}, 0 < q → ∀ {A : Set Tiling.Plane} {b : ℝ},
      0 < b →
      Tiling.RationalPolygonal.SetPeriodicBy
        (rationalHomothety q '' A) (b : ℂ) →
      Tiling.RationalPolygonal.SetPeriodicBy A ((b / q : ℝ) : ℂ) := by
  intro q hq A b hb hperiod x
  have hqR : (q : ℝ) ≠ 0 := by positivity
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqR
  have hinjective : Function.Injective (rationalHomothety q) := by
    intro u v huv
    exact mul_left_cancel₀ hqC huv
  have hforward :
      rationalHomothety q (x + ((b / q : ℝ) : ℂ)) =
        rationalHomothety q x + (b : ℂ) := by
    apply Complex.ext
    · simp [rationalHomothety]
      field_simp
    · simp [rationalHomothety]
  constructor
  · intro hx
    have himage : rationalHomothety q (x + ((b / q : ℝ) : ℂ)) ∈
        rationalHomothety q '' A := by
      exact ⟨x + ((b / q : ℝ) : ℂ), hx, rfl⟩
    have himage' : rationalHomothety q x + (b : ℂ) ∈
        rationalHomothety q '' A := by
      rw [hforward] at himage
      exact himage
    have hscaled : rationalHomothety q x ∈ rationalHomothety q '' A :=
      (hperiod (rationalHomothety q x)).mp himage'
    rcases hscaled with ⟨y, hy, hxy⟩
    have hyx : y = x := hinjective hxy
    simpa [hyx] using hy
  · intro hx
    have himage : rationalHomothety q x ∈ rationalHomothety q '' A := by
      exact ⟨x, hx, rfl⟩
    have himage' : rationalHomothety q x + (b : ℂ) ∈
        rationalHomothety q '' A := by
      exact (hperiod (rationalHomothety q x)).mpr himage
    rcases himage' with ⟨y, hy, hxy⟩
    have hyx : y = x + ((b / q : ℝ) : ℂ) := by
      apply hinjective
      rw [hforward]
      exact hxy
    simpa [hyx] using hy

/-! Later closed targets: component phase agreement, finite-period alternatives,
    normalized carriers, and plate saturation. -/

private theorem samePhase_of_tile_meets_two_components :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
      (X : PeriodicVerticalCarrier),
    Tiling.AxisParallel.TilesOn K T X.carrier →
    (∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) →
    ∀ {a b c d : ℝ}, IsCarrierComponent X a b →
      IsCarrierComponent X c d →
      ∀ {t : T},
        ((t.1 +ᵥ K.openCarrier) ∩
          {z : Tiling.Plane | z.re ∈ Ioo a b}).Nonempty →
        ((t.1 +ᵥ K.openCarrier) ∩
          {z : Tiling.Plane | z.re ∈ Ioo c d}).Nonempty →
        SameIntegerPhase a c := by
  intro K T X hTile hIntegral a b c d hab hcd t hmeetAB hmeetCD
  rcases hab with ⟨hablt, haf, hbf, habase, hdisj⟩
  rcases hcd with ⟨hcdlt, hcf, hdf, hcdase, hcdsj⟩
  have hA := integralRegion_genericSections X hTile hIntegral hablt haf hbf
    ⟨habase, hdisj⟩ hmeetAB
  have hC := integralRegion_genericSections X hTile hIntegral hcdlt hcf hdf
    ⟨hcdase, hcdsj⟩ hmeetCD
  obtain ⟨n, hn⟩ := hA.1
  obtain ⟨m, hm⟩ := hC.1
  refine ⟨m - n, ?_⟩
  norm_num [Int.cast_sub]
  have hEq : a + (n : ℝ) = c + (m : ℝ) := hn.symm.trans hm
  linear_combination hEq

private theorem periodRepresentative_mem_Ico_local {p x : ℝ} (hp : 0 < p) :
    x - (Int.floor (x / p) : ℝ) * p ∈ Ico 0 p := by
  have hlo : (Int.floor (x / p) : ℝ) ≤ x / p := Int.floor_le _
  have hhi : x / p < (Int.floor (x / p) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  constructor
  · exact sub_nonneg.mpr ((le_div_iff₀ hp).mp hlo)
  · have hlt : x < (Int.floor (x / p) : ℝ) * p + p := by
      have h' := (div_lt_iff₀ hp).mp hhi
      nlinarith
    linarith

private theorem finite_componentOrbitRepresentatives :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∃ A : Finset ℝ,
      (∀ r ∈ A, r ∈ Ico 0 X.period) ∧
      ∀ {a b : ℝ}, IsCarrierComponent X a b →
        ∃ r ∈ A, ∃ n : ℤ, a = r + (n : ℝ) * X.period := by
  intro K T X phases phaseBase phaseCentres hproper hPhase
  classical
  have hfront := phase_frontier_locallyFinite hproper hPhase 0 X.period
  let E : Set ℝ := frontier X.base ∩ Ico 0 X.period
  have hE : E.Finite := by
    apply hfront.subset
    intro x hx
    exact ⟨hx.1, ⟨hx.2.1, hx.2.2.le⟩⟩
  let A : Finset ℝ := hE.toFinset
  refine ⟨A, ?_, ?_⟩
  · intro r hr
    exact (hE.mem_toFinset.mp hr).2
  · intro a b hab
    let n : ℤ := -Int.floor (a / X.period)
    let r : ℝ := a + (n : ℝ) * X.period
    have hrI : r ∈ Ico 0 X.period := by
      have hri := periodRepresentative_mem_Ico_local (p := X.period) (x := a)
        X.period_pos
      constructor
      · simpa [r, n, Int.cast_neg, neg_mul] using hri.1
      · dsimp [r, n]
        norm_num [Int.cast_neg, neg_mul]
        linarith [hri.2]
    have htr := carrierComponent_periodTranslate X hab n
    have hrE : r ∈ E := ⟨htr.2.1, hrI⟩
    refine ⟨r, hE.mem_toFinset.mpr hrE, -n, ?_⟩
    dsimp [r]
    norm_num [Int.cast_neg]

private theorem finite_of_residue_embedding_local
    {phases : Set ℝ} {A : Finset ℝ} {q : ℕ}
    (embed : {c // c ∈ phases} → A × Fin q)
    (hinj : Function.Injective embed) :
    phases.Finite := by
  have : Finite {c // c ∈ phases} := Finite.of_injective embed hinj
  exact Set.toFinite phases

private theorem phase_base_period_of_component_translate
    {X : PeriodicVerticalCarrier} {phaseBase : ℝ → Set ℝ}
    {c : ℝ} {q l : ℕ}
    (hnormal : ∀ x, x ∈ phaseBase c ↔
      ∃ a b : ℝ, IsCarrierComponent X a b ∧
        SameIntegerPhase a c ∧ x ∈ Ioo a b)
    (hql : q * X.period = l) :
    (l : ℝ) +ᵥ phaseBase c = phaseBase c := by
  ext x
  constructor
  · intro hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
    have hx' : x - (l : ℝ) ∈ phaseBase c := by
      simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hx
    obtain ⟨a, b, hab, hac, hyI⟩ := (hnormal (x - (l : ℝ))).mp hx'
    refine (hnormal x).2 ⟨a + (q : ℤ) * X.period, b + (q : ℤ) * X.period,
      carrierComponent_periodTranslate X hab q, ?_, ?_⟩
    · have hshift : SameIntegerPhase (a + (q : ℝ) * X.period) a := by
        refine ⟨(l : ℤ), ?_⟩
        have hql' : (q : ℝ) * X.period = (l : ℝ) := by simpa using hql
        calc
          a + (q : ℝ) * X.period - a = (l : ℝ) := by rw [hql']; ring
          _ = ((l : ℤ) : ℝ) := by norm_num
      exact sameIntegerPhase_trans_local hshift hac
    · have hql' : ((q : ℤ) : ℝ) * X.period = (l : ℝ) := by
        norm_num
        exact hql
      constructor <;> linarith [hyI.1, hyI.2, hql']
  · intro hx
    obtain ⟨a, b, hab, hac, hxI⟩ := (hnormal x).mp hx
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    have htr := carrierComponent_periodTranslate X hab (-q)
    have htr' : IsCarrierComponent X (a - (q : ℝ) * X.period)
        (b - (q : ℝ) * X.period) := by
      convert htr using 1 <;> push_cast <;> ring
    have hgoal : x - (l : ℝ) ∈ phaseBase c := by
      refine (hnormal (x - (l : ℝ))).2 ⟨a - (q : ℝ) * X.period,
        b - (q : ℝ) * X.period, htr', ?_, ?_⟩
      · have hshift : SameIntegerPhase (a - (q : ℝ) * X.period) a := by
          apply sameIntegerPhase_symm_local
          refine ⟨(l : ℤ), ?_⟩
          have hql' : (q : ℝ) * X.period = (l : ℝ) := by simpa using hql
          calc
            a - (a - (q : ℝ) * X.period) = (l : ℝ) := by rw [hql']; ring
            _ = ((l : ℤ) : ℝ) := by norm_num
        exact sameIntegerPhase_trans_local hshift hac
      · have hql' : (q : ℝ) * X.period = (l : ℝ) := by simpa using hql
        constructor <;> linarith [hxI.1, hxI.2, hql']
    simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hgoal

private theorem finite_phase_residues_of_rational_period :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ {q l : ℕ}, 0 < q → 0 < l → q * X.period = l →
      phases.Finite ∧ ∀ c ∈ phases,
        (l : ℝ) +ᵥ phaseBase c = phaseBase c := by
  intro K T X phases phaseBase phaseCentres hproper hPhase q l hq hl hql
  classical
  obtain ⟨A, hA, hAcomp⟩ :=
    finite_componentOrbitRepresentatives hproper hPhase
  have hqz : 0 < (q : ℤ) := by exact_mod_cast hq
  let remVal (n : ℤ) : Fin q :=
    ⟨(n % (q : ℤ)).toNat, by
      apply (Int.toNat_lt (Int.emod_nonneg _ (ne_of_gt hqz))).2
      simpa using (Int.emod_lt_of_pos n hqz)⟩
  have hcompW (c : {c // c ∈ phases}) :
      ∃ a b : ℝ, IsCarrierComponent X a b ∧
        Ioo a b ⊆ phaseBase c.1 ∧ SameIntegerPhase a c.1 :=
    phase_has_component hproper hPhase c.1 c.2
  let aa (c : {c // c ∈ phases}) : ℝ := Classical.choose (hcompW c)
  let bb (c : {c // c ∈ phases}) : ℝ :=
    Classical.choose (Classical.choose_spec (hcompW c))
  have haa (c : {c // c ∈ phases}) : IsCarrierComponent X (aa c) (bb c) :=
    (Classical.choose_spec (Classical.choose_spec (hcompW c))).1
  have hac (c : {c // c ∈ phases}) : SameIntegerPhase (aa c) c.1 :=
    (Classical.choose_spec (Classical.choose_spec (hcompW c))).2.2
  let rr (c : {c // c ∈ phases}) : ℝ := Classical.choose (hAcomp (haa c))
  have hrr (c : {c // c ∈ phases}) : rr c ∈ A :=
    (Classical.choose_spec (hAcomp (haa c))).1
  let nn (c : {c // c ∈ phases}) : ℤ :=
    (Classical.choose_spec (hAcomp (haa c))).2.choose
  have hann (c : {c // c ∈ phases}) :
      aa c = rr c + (nn c : ℝ) * X.period :=
    (Classical.choose_spec (hAcomp (haa c))).2.choose_spec
  let embed : {c // c ∈ phases} → A × Fin q :=
    fun c => (⟨rr c, hrr c⟩, remVal (nn c))
  have hinj : Function.Injective embed := by
    intro c d hcd
    have hrr_eq : rr c = rr d := congrArg (fun z => (z.1 : ℝ)) hcd
    have hrem_nat : (nn c % (q : ℤ)).toNat = (nn d % (q : ℤ)).toNat :=
      congrArg (fun z => z.2.1) hcd
    have hrem : nn c % (q : ℤ) = nn d % (q : ℤ) := by
      have hc0 : 0 ≤ nn c % (q : ℤ) := Int.emod_nonneg _ (ne_of_gt hqz)
      have hd0 : 0 ≤ nn d % (q : ℤ) := Int.emod_nonneg _ (ne_of_gt hqz)
      apply (Int.toNat_of_nonneg hc0).symm.trans
      rw [hrem_nat, Int.toNat_of_nonneg hd0]
    have hdiv : (q : ℤ) ∣ nn c - nn d :=
      Int.dvd_of_emod_eq_zero
        ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hrem)
    rcases hdiv with ⟨k, hk⟩
    have haa_diff : SameIntegerPhase (aa c) (aa d) := by
      refine ⟨k * l, ?_⟩
      rw [hann c, hann d, hrr_eq]
      have hk' : (nn c : ℝ) - (nn d : ℝ) = (q : ℝ) * (k : ℝ) := by
        exact_mod_cast hk
      calc
        rr d + (nn c : ℝ) * X.period -
            (rr d + (nn d : ℝ) * X.period) =
            ((nn c : ℝ) - (nn d : ℝ)) * X.period := by ring
        _ = (q : ℝ) * (k : ℝ) * X.period := by rw [hk']
        _ = (k : ℝ) * (l : ℝ) := by
          calc
            (q : ℝ) * (k : ℝ) * X.period =
                (k : ℝ) * ((q : ℝ) * X.period) := by ring
            _ = (k : ℝ) * (l : ℝ) := by
              rw [show (q : ℝ) * X.period = (l : ℝ) by simpa using hql]
        _ = ((k * l : ℤ) : ℝ) := by norm_num
    have hcdphase : SameIntegerPhase c.1 d.1 :=
      sameIntegerPhase_trans_local (sameIntegerPhase_symm_local (hac c))
        (sameIntegerPhase_trans_local haa_diff (hac d))
    have hval : c.1 = d.1 :=
      hPhase.phase_representatives c.1 c.2 d.1 d.2 hcdphase
    exact Subtype.ext hval
  have hfinite : phases.Finite := finite_of_residue_embedding_local embed hinj
  refine ⟨hfinite, ?_⟩
  intro c hc
  apply phase_base_period_of_component_translate (X := X) (c := c) (q := q) (l := l)
  · intro x
    rw [phaseBase_eq_componentsOfPhase hproper hPhase c hc]
    simp only [Set.mem_ofPred_eq]
  · exact hql

private theorem no_integer_period_no_repeated_orbit_phase_local
    (X : PeriodicVerticalCarrier)
    (hno : ¬ ∃ q l : ℕ, 0 < q ∧ 0 < l ∧ q * X.period = l)
    (r : ℝ) {n m : ℤ}
    (hphase : SameIntegerPhase
      (r + (n : ℝ) * X.period)
      (r + (m : ℝ) * X.period)) :
    n = m := by
  rcases hphase with ⟨k, hk⟩
  by_contra hnm
  have hEq : ((n - m : ℤ) : ℝ) * X.period = (k : ℝ) := by
    calc
      ((n - m : ℤ) : ℝ) * X.period =
          (r + (n : ℝ) * X.period) -
            (r + (m : ℝ) * X.period) := by
          norm_num [Int.cast_sub]
          ring
      _ = (k : ℝ) := hk
  have hk_ne : k ≠ 0 := by
    intro hk0
    have hz : ((n - m : ℤ) : ℝ) * X.period = 0 := by simpa [hk0] using hEq
    have hcoef : ((n - m : ℤ) : ℝ) = 0 := by
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt X.period_pos)
    apply hnm
    have hsub : n - m = 0 := by exact_mod_cast hcoef
    exact sub_eq_zero.mp hsub
  let q : ℕ := (n - m).natAbs
  let l : ℕ := k.natAbs
  have hq : 0 < q := Int.natAbs_pos.mpr (sub_ne_zero.mpr hnm)
  have hl : 0 < l := Int.natAbs_pos.mpr hk_ne
  have hAbs := congrArg abs hEq
  rw [abs_mul, abs_of_pos X.period_pos] at hAbs
  have hqcast : (q : ℝ) = |((n - m : ℤ) : ℝ)| := by
    norm_num [q, Int.natCast_natAbs]
  have hlcast : (l : ℝ) = |(k : ℝ)| := by
    norm_num [l, Int.natCast_natAbs]
  apply hno
  refine ⟨q, l, hq, hl, ?_⟩
  rw [hqcast, hlcast]
  exact hAbs

private theorem component_right_unique_local
    {X : PeriodicVerticalCarrier} {a b d : ℝ}
    (hab : IsCarrierComponent X a b)
    (had : IsCarrierComponent X a d) : b = d := by
  rcases hab with ⟨hablt, haf, hbf, hbase, hdisj⟩
  rcases had with ⟨hadlt, haf', hdf, hbase', hdisj'⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbd | hdb
  · have hcontra : b ∈ Ioo a d ∩ frontier X.base := ⟨⟨hablt, hbd⟩, hbf⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj') b hcontra
  · have hcontra : d ∈ Ioo a b ∩ frontier X.base := ⟨⟨hadlt, hdb⟩, hdf⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hdisj) d hcontra

private theorem bounded_phase_of_no_integer_period :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    (¬ ∃ q l : ℕ, 0 < q ∧ 0 < l ∧ q * X.period = l) →
      ∀ c ∈ phases, IsBounded (phaseBase c) := by
  intro K T X phases phaseBase phaseCentres hproper hPhase hno c hc
  classical
  obtain ⟨A, hA, hAcomp⟩ := finite_componentOrbitRepresentatives hproper hPhase
  let C : Set (ℝ × ℝ) := {p | IsCarrierComponent X p.1 p.2 ∧
    SameIntegerPhase p.1 c}
  have hCfin : C.Finite := by
    let aa : C → ℝ := fun p => Classical.choose (hAcomp p.property.1)
    let nn : C → ℤ := fun p =>
      Classical.choose (Classical.choose_spec (hAcomp p.property.1)).2
    have haa (p : C) : p.1.1 = aa p + (nn p : ℝ) * X.period :=
      Classical.choose_spec (Classical.choose_spec (hAcomp p.property.1)).2
    have haa_mem (p : C) : aa p ∈ A :=
      (Classical.choose_spec (hAcomp p.property.1)).1
    let f : C → A := fun p => ⟨aa p, haa_mem p⟩
    have hf : Function.Injective f := by
      intro p q hpq
      have haa_eq : aa p = aa q := congrArg (fun z : A => (z : ℝ)) hpq
      have hphase : SameIntegerPhase p.1.1 q.1.1 :=
        sameIntegerPhase_trans_local p.property.2
          (sameIntegerPhase_symm_local q.property.2)
      have hphase' : SameIntegerPhase
          (aa p + (nn p : ℝ) * X.period)
          (aa p + (nn q : ℝ) * X.period) := by
        have hphase2 := hphase
        rw [haa p, haa q] at hphase2
        simpa [haa_eq] using hphase2
      have hnn : nn p = nn q :=
        no_integer_period_no_repeated_orbit_phase_local X hno (aa p) hphase'
      have hleft : p.1.1 = q.1.1 := by
        rw [haa p, haa q, haa_eq, hnn]
      have hright : p.1.2 = q.1.2 := by
        apply component_right_unique_local p.property.1
        simpa [hleft] using q.property.1
      apply Subtype.ext
      apply Prod.ext hleft
      exact hright
    have : Finite C := Finite.of_injective f hf
    exact Set.toFinite C
  let _ : Fintype C := hCfin.fintype
  have hbounded : IsBounded (⋃ p : C, Ioo p.1.1 p.1.2) := by
    apply isBounded_iUnion.mpr
    intro p
    exact Metric.isBounded_Ioo _ _
  have heq : phaseBase c = ⋃ p : C, Ioo p.1.1 p.1.2 := by
    rw [phaseBase_eq_componentsOfPhase hproper hPhase c hc]
    ext x
    constructor
    · rintro ⟨a, b, hab, hac, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨(a, b), ⟨hab, hac⟩⟩, hx⟩
    · intro hx
      obtain ⟨p, hxp⟩ := Set.mem_iUnion.mp hx
      exact ⟨p.1.1, p.1.2, p.property.1, p.property.2, hxp⟩
  rw [heq]
  exact hbounded

theorem carrierPeriod_rationalOrIrrational :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ}
      {phaseCentres : ℝ → Set Tiling.Plane},
    X.base ≠ Set.univ →
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ((∃ q l : ℕ, 0 < q ∧ 0 < l ∧ q * X.period = l) ∧
        phases.Finite ∧ ∃ L : ℕ, 0 < L ∧ ∀ c ∈ phases,
          (L : ℝ) +ᵥ phaseBase c = phaseBase c) ∨
      ((¬ ∃ q l : ℕ, 0 < q ∧ 0 < l ∧ q * X.period = l) ∧
        ∀ c ∈ phases, IsBounded (phaseBase c)) := by
  intro K T X phases phaseBase phaseCentres hproper hPhase
  classical
  by_cases hrat : ∃ q l : ℕ, 0 < q ∧ 0 < l ∧ q * X.period = l
  · rcases hrat with ⟨q, l, hq, hl, hql⟩
    left
    refine ⟨⟨q, l, hq, hl, hql⟩, ?_⟩
    obtain ⟨hfinite, hperiod⟩ :=
      finite_phase_residues_of_rational_period hproper hPhase hq hl hql
    exact ⟨hfinite, l, hl, hperiod⟩
  · right
    refine ⟨hrat, ?_⟩
    exact bounded_phase_of_no_integer_period hproper hPhase hrat

private structure NormalizedCarrierPhase
    (K : Region) (T : Set Tiling.Plane) (X : PeriodicVerticalCarrier)
    (phases : Set ℝ) (phaseBase : ℝ → Set ℝ)
    (phaseCentres : ℝ → Set Tiling.Plane) (c : ℝ) where
  normalizedBase : Set ℝ
  normalizedCentres : Set Tiling.Plane
  normalizedBase_eq : normalizedBase = (-c) +ᵥ phaseBase c
  normalizedCentres_eq : normalizedCentres = ((-c : ℝ) : ℂ) +ᵥ phaseCentres c
  base_open : IsOpen normalizedBase
  base_regular : interior (closure normalizedBase) = normalizedBase
  tiles : TilesOn K normalizedCentres (Complex.re ⁻¹' normalizedBase)
  centres_integral : ∀ t ∈ normalizedCentres, ∃ n : ℤ, t.re = n
  boundary_integral : ∀ x ∈ frontier normalizedBase, ∃ n : ℤ, x = n

private theorem normalizedCarrierPhase_exists :
    ∀ {K : Region} {T : Set Tiling.Plane}
      {X : PeriodicVerticalCarrier} {phases : Set ℝ}
      {phaseBase : ℝ → Set ℝ} {phaseCentres : ℝ → Set Tiling.Plane},
    IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres →
    ∀ c ∈ phases,
      Nonempty (NormalizedCarrierPhase K T X phases phaseBase phaseCentres c) := by
  intro K T X phases phaseBase phaseCentres hPhase c hc
  let normalizedBase : Set ℝ := (-c) +ᵥ phaseBase c
  let normalizedCentres : Set Tiling.Plane :=
    ((-c : ℝ) : ℂ) +ᵥ phaseCentres c
  have hbase_open : IsOpen normalizedBase := by
    exact (hPhase.phaseBase_open c hc).vadd _
  have hbase_regular : interior (closure normalizedBase) = normalizedBase := by
    dsimp [normalizedBase]
    rw [closure_vadd, interior_vadd, hPhase.phaseBase_regular c hc]
  have htarget :
      ((-c : ℝ) : ℂ) +ᵥ (Complex.re ⁻¹' phaseBase c) =
        Complex.re ⁻¹' normalizedBase := by
    ext z
    dsimp [normalizedBase]
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_preimage, vadd_eq_add,
      Complex.add_re, Complex.neg_re]
    norm_num
  have htiles : TilesOn K normalizedCentres
      (Complex.re ⁻¹' normalizedBase) := by
    have htranslated := Tiling.AxisParallel.tilesOn_translate
      (hPhase.phase_tiles c hc) ((-c : ℝ) : ℂ)
    rw [htarget] at htranslated
    exact htranslated
  have hcentres_integral :
      ∀ t ∈ normalizedCentres, ∃ n : ℤ, t.re = n := by
    intro t ht
    have ht' : ((c : ℝ) : ℂ) + t ∈ phaseCentres c := by
      have ht'' : t ∈ ((-c : ℝ) : ℂ) +ᵥ phaseCentres c := ht
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at ht''
      simpa [vadd_eq_add] using ht''
    rcases hPhase.centre_phase c hc ((c : ℝ) + t) ht' with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    simpa using hn
  have hboundary_integral :
      ∀ x ∈ frontier normalizedBase, ∃ n : ℤ, x = n := by
    intro x hx
    have hx' : x ∈ (-c) +ᵥ frontier (phaseBase c) := by
      change x ∈ (Homeomorph.addLeft (-c)) '' frontier (phaseBase c)
      rw [(Homeomorph.addLeft (-c)).image_frontier]
      exact hx
    have hcx : c + x ∈ frontier (phaseBase c) := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx'
      simpa using hx'
    rcases hPhase.boundary_phase c hc (c + x) hcx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    linarith
  exact ⟨{
    normalizedBase := normalizedBase
    normalizedCentres := normalizedCentres
    normalizedBase_eq := rfl
    normalizedCentres_eq := rfl
    base_open := hbase_open
    base_regular := hbase_regular
    tiles := htiles
    centres_integral := hcentres_integral
    boundary_integral := hboundary_integral
  }⟩

private theorem phaseCentres_plateSaturated
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    {phases : Set ℝ} {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane}
    (hPhase : IsCarrierPhaseDecomposition
      K T X phases phaseBase phaseCentres) :
    ∀ c ∈ phases,
      phaseCentres c ⊆ T ∧
      ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
        P.centres ⊆ phaseCentres c ∨ Disjoint P.centres (phaseCentres c) := by
  intro c hc
  constructor
  · intro z hz
    rw [← hPhase.phaseCentres_union]
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hz⟩
  · intro P
    obtain ⟨d, ⟨hd, hPd⟩, _⟩ := hPhase.plate_has_unique_phase P
    by_cases hcd : c = d
    · left
      simpa [hcd] using hPd
    · right
      apply Set.disjoint_left.2
      intro z hzP hzC
      exact Set.disjoint_left.1
        (hPhase.phaseCentres_pairwise hc hd hcd) hzC (hPd hzP)

private theorem sameIntegerPhase_refl (x : ℝ) : SameIntegerPhase x x := by
  exact ⟨0, by norm_num⟩

private theorem sameIntegerPhase_symm {x y : ℝ} :
    SameIntegerPhase x y → SameIntegerPhase y x := by
  rintro ⟨n, hn⟩
  refine ⟨-n, ?_⟩
  rw [sub_eq_iff_eq_add] at hn ⊢
  rw [hn]
  norm_num

private theorem sameIntegerPhase_trans {x y z : ℝ} :
    SameIntegerPhase x y → SameIntegerPhase y z → SameIntegerPhase x z := by
  rintro ⟨m, hm⟩ ⟨n, hn⟩
  refine ⟨m + n, ?_⟩
  calc
    x - z = (x - y) + (y - z) := by ring
    _ = (m : ℝ) + (n : ℝ) := by rw [hm, hn]
    _ = ((m + n : ℤ) : ℝ) := by norm_num

private def sameIntegerPhaseSetoid : Setoid ℝ where
  r := SameIntegerPhase
  iseqv := ⟨sameIntegerPhase_refl, sameIntegerPhase_symm, sameIntegerPhase_trans⟩

private instance sameIntegerPhaseSetoid_inst : Setoid ℝ := sameIntegerPhaseSetoid

private abbrev PhaseQuotient := Quotient sameIntegerPhaseSetoid

private def phaseClass (x : ℝ) : PhaseQuotient := Quotient.mk' x

private def ActiveEndpoint
    (K : Tiling.AxisParallel.Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) : Type :=
  {a : ℝ // ∃ b : ℝ, IsCarrierComponent X a b ∧ ∃ t : T,
    ((t.1 +ᵥ K.openCarrier) ∩
      {z : Tiling.Plane | z.re ∈ Ioo a b}).Nonempty}

private def activePhaseClasses
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} : Set PhaseQuotient :=
  {q | ∃ a : ActiveEndpoint K T X, phaseClass a.1 = q}

private noncomputable def activePhaseRep
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (q : {q : PhaseQuotient // q ∈ activePhaseClasses (K := K) (T := T) (X := X)}) : ℝ :=
  (Classical.choose q.2).1

private theorem activePhaseRep_class
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (q : {q : PhaseQuotient // q ∈ activePhaseClasses (K := K) (T := T) (X := X)}) :
    phaseClass (activePhaseRep q) = q.1 := by
  exact Classical.choose_spec q.2

private def activePhases
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} : Set ℝ :=
  Set.range (activePhaseRep (K := K) (T := T) (X := X))

private noncomputable def endpointRight
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (a : ActiveEndpoint K T X) : ℝ :=
  Classical.choose a.2

private theorem endpointRight_spec
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (a : ActiveEndpoint K T X) :
    IsCarrierComponent X a.1 (endpointRight a) ∧ ∃ t : T,
      ((t.1 +ᵥ K.openCarrier) ∩
        {z : Tiling.Plane | z.re ∈ Ioo a.1 (endpointRight a)}).Nonempty := by
  exact Classical.choose_spec a.2

private noncomputable def endpointTile
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (a : ActiveEndpoint K T X) : T :=
  Classical.choose (endpointRight_spec a).2

private theorem endpointTile_spec
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (a : ActiveEndpoint K T X) :
    ((endpointTile a).1 +ᵥ K.openCarrier) ∩
        {z : Tiling.Plane | z.re ∈ Ioo a.1 (endpointRight a)} |>.Nonempty := by
  exact Classical.choose_spec (endpointRight_spec a).2

private def activePhaseBase
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
  {X : PeriodicVerticalCarrier} (c : ℝ) : Set ℝ :=
  ⋃ a : {a : ActiveEndpoint K T X // phaseClass a.1 = phaseClass c},
    Ioo a.1.1 (endpointRight a.1)

private def activePhaseCentres
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
  {X : PeriodicVerticalCarrier} (c : ℝ) : Set Tiling.Plane :=
  {z₀ | ∃ a : ActiveEndpoint K T X, ∃ t : T, z₀ = t.1 ∧
    phaseClass a.1 = phaseClass c ∧
      ((t.1 +ᵥ K.openCarrier) ∩
        {z : Tiling.Plane | z.re ∈ Ioo a.1 (endpointRight a)}).Nonempty}

private theorem activePhaseBase_open
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (c : ℝ) :
    IsOpen (activePhaseBase (K := K) (T := T) (X := X) c) := by
  exact isOpen_iUnion (fun a ↦ isOpen_Ioo)

private theorem activePhaseCentres_nonempty
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {c : ℝ}
    (hc : c ∈ activePhases (K := K) (T := T) (X := X)) :
    (activePhaseCentres (K := K) (T := T) (X := X) c).Nonempty := by
  obtain ⟨q, rfl⟩ := hc
  obtain ⟨a, ha⟩ := q.2
  refine ⟨(endpointTile a).1, a, endpointTile a, rfl, ?_⟩
  exact ⟨ha.trans (activePhaseRep_class q).symm, endpointTile_spec a⟩

private theorem activeEndpoint_class_eq_of_tile_meets
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (hTile : Tiling.AxisParallel.TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (a b : ActiveEndpoint K T X) (t : T)
    (ha : ((t.1 +ᵥ K.openCarrier) ∩
      {z : Tiling.Plane | z.re ∈ Ioo a.1 (endpointRight a)}).Nonempty)
    (hb : ((t.1 +ᵥ K.openCarrier) ∩
      {z : Tiling.Plane | z.re ∈ Ioo b.1 (endpointRight b)}).Nonempty) :
    phaseClass a.1 = phaseClass b.1 := by
  apply Quotient.sound
  exact samePhase_of_tile_meets_two_components X hTile hIntegral
    (endpointRight_spec a).1 (endpointRight_spec b).1 ha hb

private theorem activePhaseBase_subset_carrier
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (c : ℝ) :
    activePhaseBase (K := K) (T := T) (X := X) c ⊆ X.base := by
  intro x hx
  obtain ⟨a, hx⟩ := Set.mem_iUnion.mp hx
  exact (endpointRight_spec a.1).1.2.2.2.1 hx

private theorem activePhaseCentres_centre_phase
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} (hTile : Tiling.AxisParallel.TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {c : ℝ} (_hc : c ∈ activePhases (K := K) (T := T) (X := X))
    {z₀ : Tiling.Plane}
    (hz : z₀ ∈ activePhaseCentres (K := K) (T := T) (X := X) c) :
    SameIntegerPhase z₀.re c := by
  obtain ⟨a, t, rfl, hac, hmeet⟩ := hz
  obtain ⟨n, hn⟩ :=
    (integralRegion_genericSections X hTile hIntegral
      (endpointRight_spec a).1.1
      (endpointRight_spec a).1.2.1
      (endpointRight_spec a).1.2.2.1
      ⟨(endpointRight_spec a).1.2.2.2.1,
        (endpointRight_spec a).1.2.2.2.2⟩ hmeet).1
  apply sameIntegerPhase_trans
    (x := t.1.re) (y := a.1) (z := c)
  · refine ⟨n, ?_⟩
    rw [hn]
    ring
  · exact Quotient.exact hac

private theorem carrierComponent_intervals_disjoint_of_phase_ne
    {X : PeriodicVerticalCarrier} {a b c d : ℝ}
    (hab : IsCarrierComponent X a b) (hcd : IsCarrierComponent X c d)
    (hphase : phaseClass a ≠ phaseClass c) :
    Disjoint (Ioo a b) (Ioo c d) := by
  rw [Set.disjoint_left]
  intro x hxa hxc
  have hac : a ≠ c := by
    intro h
    apply hphase
    exact congrArg phaseClass h
  rcases lt_or_gt_of_ne hac with hac | hca
  · have hcb : c < b := lt_trans hxc.1 hxa.2
    exact Set.eq_empty_iff_forall_notMem.mp hab.2.2.2.2 c
      ⟨⟨hac, hcb⟩, hcd.2.1⟩
  · have hab' : a < d := lt_trans hxa.1 hxc.2
    exact Set.eq_empty_iff_forall_notMem.mp hcd.2.2.2.2 a
      ⟨⟨hca, hab'⟩, hab.2.1⟩

private theorem carrierComponent_eq_of_intersect
    {X : PeriodicVerticalCarrier} {a b c d : ℝ}
    (hab : IsCarrierComponent X a b) (hcd : IsCarrierComponent X c d)
    {x : ℝ} (hxa : x ∈ Ioo a b) (hxc : x ∈ Ioo c d) : a = c ∧ b = d := by
  have hac : a = c := by
    rcases eq_or_ne a c with rfl | hac
    · rfl
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exfalso
        have hcb : c < b := lt_trans hxc.1 hxa.2
        exact Set.eq_empty_iff_forall_notMem.mp hab.2.2.2.2 c
          ⟨⟨hac, hcb⟩, hcd.2.1⟩
      · exfalso
        have hab' : a < d := lt_trans hxa.1 hxc.2
        exact Set.eq_empty_iff_forall_notMem.mp hcd.2.2.2.2 a
          ⟨⟨hca, hab'⟩, hab.2.1⟩
  subst c
  have hbd : b = d := by
    rcases eq_or_ne b d with rfl | hbd
    · rfl
    · rcases lt_or_gt_of_ne hbd with hbd | hdb
      · exfalso
        exact Set.eq_empty_iff_forall_notMem.mp hcd.2.2.2.2 b
          ⟨⟨hab.1, hbd⟩, hab.2.2.1⟩
      · exfalso
        exact Set.eq_empty_iff_forall_notMem.mp hab.2.2.2.2 d
          ⟨⟨lt_trans hxc.1 hxc.2, hdb⟩, hcd.2.2.1⟩
  exact ⟨rfl, hbd⟩

private theorem carrierComponent_right_unique
    {X : PeriodicVerticalCarrier} {a b d : ℝ}
    (hab : IsCarrierComponent X a b) (had : IsCarrierComponent X a d) : b = d := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hbd | hdb
  · exact Set.eq_empty_iff_forall_notMem.mp had.2.2.2.2 b
      ⟨⟨hab.1, hbd⟩, hab.2.2.1⟩
  · exact Set.eq_empty_iff_forall_notMem.mp hab.2.2.2.2 d
      ⟨⟨had.1, hdb⟩, had.2.2.1⟩

private theorem activePhaseRep_injective
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    {q r : {q : PhaseQuotient // q ∈ activePhaseClasses (K := K) (T := T) (X := X)}}
    (h : SameIntegerPhase (activePhaseRep q) (activePhaseRep r)) : q = r := by
  apply Subtype.ext
  rw [← activePhaseRep_class q, ← activePhaseRep_class r]
  exact Quotient.sound h

private theorem activePhases_phase_representatives
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} :
    ∀ c ∈ activePhases (K := K) (T := T) (X := X),
      ∀ d ∈ activePhases (K := K) (T := T) (X := X),
        SameIntegerPhase c d → c = d := by
  rintro c ⟨q, rfl⟩ d ⟨r, rfl⟩ h
  have hqr := activePhaseRep_injective h
  exact congrArg activePhaseRep hqr

private theorem frontier_localFinite_from_tiles
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) (a b : ℝ) :
    (frontier X.base ∩ Icc a b).Finite := by
  have hfinite := hTile.verticalCylinder_frontier_locallyFinite
    X.base_open X.base_regular (Icc a b) isCompact_Icc
  simpa [inter_comm] using hfinite


private theorem exists_component_at_from_tile
    {K : Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ)
    (hTile : TilesOn K T X.carrier)
    {x : ℝ} (hx : x ∈ X.base) :
    ∃ a b : ℝ, IsCarrierComponent X a b ∧ x ∈ Ioo a b := by
  have hbase_fun : Function.Periodic (fun z : ℝ => z ∈ X.base) X.period := by
    intro z
    apply propext
    have hm : z + X.period ∈ X.period +ᵥ X.base ↔ z + X.period ∈ X.base := by
      rw [X.base_periodic]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hm
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hm.symm
  have hshift (z : ℝ) (n : ℤ) :
      z + (n : ℝ) * X.period ∈ X.base ↔ z ∈ X.base := by
    have h := hbase_fun.int_mul n z
    simpa [zsmul_eq_mul] using h
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℝ, y₀ ∉ X.base := by
    by_contra h
    apply hproper
    exact Set.eq_univ_of_forall (by
      intro y
      by_contra hy
      exact h ⟨y, hy⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt ((x - y₀) / X.period)
  obtain ⟨m, hm⟩ := exists_nat_gt ((y₀ - x) / X.period)
  let yR : ℝ := y₀ + (n : ℝ) * X.period
  let yL : ℝ := y₀ - (m : ℝ) * X.period
  have hyR : x < yR := by
    dsimp [yR]
    have hmul := mul_lt_mul_of_pos_right hn X.period_pos
    have hmul' : x - y₀ < (n : ℝ) * X.period := by
      simpa [div_mul_cancel₀ _ (ne_of_gt X.period_pos)] using hmul
    linarith
  have hyL : yL < x := by
    dsimp [yL]
    have hmul := mul_lt_mul_of_pos_right hm X.period_pos
    have hmul' : y₀ - x < (m : ℝ) * X.period := by
      simpa [div_mul_cancel₀ _ (ne_of_gt X.period_pos)] using hmul
    linarith
  have hyRnot : yR ∉ X.base := by
    intro h
    exact hy₀ ((hshift y₀ (n : ℤ)).mp (by simpa [yR] using h))
  have hyLnot : yL ∉ X.base := by
    intro h
    have hs := hshift y₀ (-(m : ℤ))
    apply hy₀
    apply hs.mp
    simpa [yL, Int.cast_neg, sub_eq_add_neg, mul_neg] using h
  have hneL : ¬ (yL ∈ X.base ↔ x ∈ X.base) := by simp [hyLnot, hx]
  have hneR : ¬ (x ∈ X.base ↔ yR ∈ X.base) := by simp [hyRnot, hx]
  have hxint : x ∈ interior X.base := by
    rw [X.base_open.interior_eq]
    exact hx
  obtain ⟨a₀, ha₀F, ha₀I⟩ :=
    exists_frontier_mem_uIcc_local X.base_open hneL
  obtain ⟨b₀, hb₀F, hb₀I⟩ :=
    exists_frontier_mem_uIcc_local X.base_open hneR
  have ha₀I' : a₀ ∈ Icc yL x := by simpa [uIcc_of_le hyL.le] using ha₀I
  have hb₀I' : b₀ ∈ Icc x yR := by simpa [uIcc_of_le hyR.le] using hb₀I
  have hax : a₀ < x := by
    exact lt_of_le_of_ne ha₀I'.2 (by
      intro h
      subst a₀
      exact (disjoint_interior_frontier.le_bot ⟨
        hxint, ha₀F⟩))
  have hxb : x < b₀ := by
    exact lt_of_le_of_ne hb₀I'.1 (by
      intro h
      subst b₀
      exact (disjoint_interior_frontier.le_bot ⟨
        hxint, hb₀F⟩).elim)
  have hfiniteL := frontier_localFinite_from_tiles X hTile yL x
  have hfiniteR := frontier_localFinite_from_tiles X hTile x yR
  let FL : Set ℝ := frontier X.base ∩ Icc yL x
  let FR : Set ℝ := frontier X.base ∩ Icc x yR
  have hFL : FL.Finite := by simpa [FL] using hfiniteL
  have hFR : FR.Finite := by simpa [FR] using hfiniteR
  have hFLne : FL.Nonempty := ⟨a₀, ha₀F, ha₀I'⟩
  have hFRne : FR.Nonempty := ⟨b₀, hb₀F, hb₀I'⟩
  let a : ℝ := sSup FL
  let b : ℝ := sInf FR
  have ha : a ∈ FL := by
    dsimp [a]
    exact hFLne.csSup_mem hFL
  have hb : b ∈ FR := by
    dsimp [b]
    exact hFRne.csInf_mem hFR
  have haa : a < x := lt_of_le_of_ne ha.2.2 (by
    intro h
    have hfront : x ∈ frontier X.base := h ▸ ha.1
    exact (disjoint_interior_frontier.le_bot ⟨
      hxint, hfront⟩))
  have hbb : x < b := lt_of_le_of_ne hb.2.1 (by
    intro h
    have hfront : x ∈ frontier X.base := h ▸ hb.1
    exact (disjoint_interior_frontier.le_bot ⟨
      hxint, hfront⟩).elim)
  have hgap : Ioo a b ∩ frontier X.base = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rcases lt_trichotomy z x with hzx | rfl | hxz
    · have hzFL : z ∈ FL := by
        refine ⟨hz.2, ?_⟩
        exact ⟨le_of_lt (lt_of_le_of_lt ha.2.1 hz.1.1), le_of_lt hzx⟩
      exact (not_lt_of_ge (le_csSup hFL.bddAbove hzFL)) hz.1.1
    · exact (disjoint_interior_frontier.le_bot ⟨
        hxint, hz.2⟩)
    · have hzFR : z ∈ FR := by
        refine ⟨hz.2, ?_⟩
        exact ⟨le_of_lt hxz, le_of_lt (lt_of_lt_of_le hz.1.2 hb.2.2)⟩
      exact (not_lt_of_ge (csInf_le hFR.bddBelow hzFR)) hz.1.2
  have hdis : Disjoint (Ioo a b) (frontier X.base) := by
    rw [Set.disjoint_left]
    intro z hz hzfront
    have hz' : z ∈ Ioo a b ∩ frontier X.base := ⟨hz, hzfront⟩
    rw [hgap] at hz'
    exact hz'
  have hsubset : Ioo a b ⊆ X.base := by
    rcases Tiling.IsPreconnected.subset_interior_or_subset_interior_compl_of_disjoint_frontier
      isPreconnected_Ioo hdis with hin | hout
    · exact hin.trans interior_subset
    · exact False.elim ((interior_subset (hout ⟨haa, hbb⟩)) hx)
  refine ⟨a, b, ⟨haa.trans hbb, ha.1, hb.1, hsubset, hgap⟩, ⟨haa, hbb⟩⟩

private theorem openUnion_subset_carrier_from_tiles
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) : openUnion K T ⊆ X.carrier := by
  have hopen : IsOpen X.carrier := X.base_open.preimage Complex.continuous_re
  have hregular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      X.base_regular]
  have hsupp := regularSupport_eq_of_tilesOn hopen hregular hTile
  have hopenUnion : IsOpen (openUnion K T) := by
    apply isOpen_iUnion
    intro t
    change IsOpen ((Homeomorph.addLeft (t : Tiling.Plane)) '' K.openCarrier)
    exact (Homeomorph.addLeft (t : Tiling.Plane)).isOpenMap _ isOpen_interior
  rw [← hsupp]
  exact hopenUnion.subset_interior_closure

private theorem tilesOn_centres_nonempty
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier) : T.Nonempty := by
  have hbase : X.base.Nonempty :=
    MeasureTheory.nonempty_of_measure_ne_zero X.base_nonnull
  have hcarrier : X.carrier.Nonempty := by
    obtain ⟨x, hx⟩ := hbase
    refine ⟨(x : ℂ), ?_⟩
    change x ∈ X.base
    exact hx
  by_contra hT
  have hTeq : T = ∅ := Set.not_nonempty_iff_eq_empty.mp hT
  have hopen : IsOpen X.carrier := X.base_open.preimage Complex.continuous_re
  have hregular : interior (closure X.carrier) = X.carrier := by
    change interior (closure (Complex.re ⁻¹' X.base)) = Complex.re ⁻¹' X.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      X.base_regular]
  have hsupp := regularSupport_eq_of_tilesOn hopen hregular hTile
  have hEmpty : X.carrier = ∅ := by
    rw [← hsupp, hTeq]
    simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
  exact hcarrier.ne_empty hEmpty

private theorem activePhaseClasses_nonempty
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier) :
    (activePhaseClasses (K := K) (T := T) (X := X)).Nonempty := by
  obtain ⟨t, ht⟩ := tilesOn_centres_nonempty X hTile
  let tSub : T := ⟨t, ht⟩
  obtain ⟨z, hz⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change z ∈ K.openCarrier at hz
  have hzcar := openUnion_subset_carrier_from_tiles X hTile
    (Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ⟨z, hz, rfl⟩⟩)
  change (t.1 + z).re ∈ X.base at hzcar
  obtain ⟨a, b, hab, hx⟩ :=
    exists_component_at_from_tile hproper hTile hzcar
  let e : ActiveEndpoint K T X := ⟨a, ⟨b, hab, ?_⟩⟩
  · refine ⟨phaseClass e.1, e, rfl⟩
  · refine ⟨tSub, ?_⟩
    refine ⟨tSub.1 + z, ?_, ?_⟩
    · exact ⟨z, hz, rfl⟩
    · simpa using hx

private theorem activePhases_nonempty
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier) :
    (activePhases (K := K) (T := T) (X := X)).Nonempty := by
  obtain ⟨q, hq⟩ := activePhaseClasses_nonempty hproper hTile
  let q' : {q : PhaseQuotient //
      q ∈ activePhaseClasses (K := K) (T := T) (X := X)} := ⟨q, hq⟩
  exact ⟨activePhaseRep q', ⟨q', rfl⟩⟩

private theorem activePhaseBase_regular
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier)
    {c : ℝ} (_hc : c ∈ activePhases (K := K) (T := T) (X := X)) :
    interior (closure (activePhaseBase (K := K) (T := T) (X := X) c)) =
      activePhaseBase (K := K) (T := T) (X := X) c := by
  let V : Set ℝ := activePhaseBase (K := K) (T := T) (X := X) c
  have hVopen : IsOpen V := activePhaseBase_open c
  have hVsub : V ⊆ X.base := activePhaseBase_subset_carrier c
  have hVint : interior (closure V) ⊆ X.base := by
    have hcl : closure V ⊆ closure X.base := closure_mono hVsub
    have hint := interior_mono hcl
    rw [X.base_regular] at hint
    exact hint
  apply Set.Subset.antisymm
  · intro x hx
    have hxbase : x ∈ X.base := hVint hx
    obtain ⟨a, b, hab, hxab⟩ :=
      exists_component_at_from_tile hproper hTile hxbase
    have hxcl : x ∈ closure V := interior_subset hx
    have hxa : 0 < x - a := sub_pos.mpr hxab.1
    have hbx : 0 < b - x := sub_pos.mpr hxab.2
    let ε : ℝ := min (x - a) (b - x) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hεa : ε ≤ x - a := by
      dsimp [ε]
      nlinarith [min_le_left (x - a) (b - x)]
    have hεb : ε ≤ b - x := by
      dsimp [ε]
      nlinarith [min_le_right (x - a) (b - x)]
    have hxJ : x ∈ Ioo (x - ε) (x + ε) := by
      constructor <;> linarith
    have hJsub : Ioo (x - ε) (x + ε) ⊆ Ioo a b := by
      intro y hy
      constructor <;> linarith [hy.1, hy.2]
    obtain ⟨y, hyJ, hyV⟩ :=
      mem_closure_iff.mp hxcl (Ioo (x - ε) (x + ε)) isOpen_Ioo hxJ
    obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hyV
    have hyeab : y ∈ Ioo a b := hJsub hyJ
    have heq := carrierComponent_eq_of_intersect hab
      (endpointRight_spec e.1).1 hyeab hye
    have hxe : x ∈ Ioo e.1.1 (endpointRight e.1) := by
      simpa [heq.1, heq.2] using hxab
    exact Set.mem_iUnion.mpr ⟨e, hxe⟩
  · intro x hx
    exact hVopen.subset_interior_closure hx

private theorem activePhaseCentres_union
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier) :
    (⋃ c : activePhases (K := K) (T := T) (X := X),
      activePhaseCentres (K := K) (T := T) (X := X) c) = T := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨c, hzc⟩ := Set.mem_iUnion.mp hz
    obtain ⟨a, t, rfl, _hac, _hmeet⟩ := hzc
    exact t.2
  · intro z hz
    obtain ⟨z₀, hz₀⟩ := K.isPolygonal.interior_nonempty K.nonempty
    change z₀ ∈ K.openCarrier at hz₀
    have hzcar := openUnion_subset_carrier_from_tiles X hTile
      (Set.mem_iUnion.mpr ⟨⟨z, hz⟩, ⟨z₀, hz₀, rfl⟩⟩)
    change (z + z₀).re ∈ X.base at hzcar
    obtain ⟨a, b, hab, hxab⟩ :=
      exists_component_at_from_tile hproper hTile hzcar
    let e : ActiveEndpoint K T X := ⟨a, ⟨b, hab, ?_⟩⟩
    · let q : {q : PhaseQuotient //
        q ∈ activePhaseClasses (K := K) (T := T) (X := X)} :=
        ⟨phaseClass e.1, ⟨e, rfl⟩⟩
      let c : activePhases (K := K) (T := T) (X := X) :=
        ⟨activePhaseRep q, ⟨q, rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨c, ?_⟩
      have hecomp := (endpointRight_spec e).1
      change IsCarrierComponent X a (endpointRight e) at hecomp
      have heq : endpointRight e = b :=
        carrierComponent_right_unique hecomp hab
      refine ⟨e, ⟨z, hz⟩, rfl, ?_, ?_⟩
      · exact (activePhaseRep_class q).symm
      · exact ⟨z + z₀, ⟨z₀, hz₀, rfl⟩, by simpa [heq] using hxab⟩
    · refine ⟨⟨z, hz⟩, ?_⟩
      refine ⟨z + z₀, ?_, ?_⟩
      · exact ⟨z₀, hz₀, rfl⟩
      · simpa using hxab

private theorem activePhaseCentres_pairwise
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    Set.PairwiseDisjoint (activePhases (K := K) (T := T) (X := X))
      (activePhaseCentres (K := K) (T := T) (X := X)) := by
  intro c hc d hd hcd
  change Disjoint
    (activePhaseCentres (K := K) (T := T) (X := X) c)
    (activePhaseCentres (K := K) (T := T) (X := X) d)
  rw [Set.disjoint_left]
  intro z hzc hzd
  obtain ⟨a, t₀, hzt₀, hac, hmeetA⟩ := hzc
  obtain ⟨b, t₁, hzt₁, hbd, hmeetB⟩ := hzd
  have htEq : t₀.1 = t₁.1 := hzt₀.symm.trans hzt₁
  have hmeetB' := hmeetB
  rw [← htEq] at hmeetB'
  have hphase := activeEndpoint_class_eq_of_tile_meets
    hTile hIntegral a b t₀ hmeetA hmeetB'
  have hclasses : phaseClass c = phaseClass d :=
    hac.symm.trans (hphase.trans hbd)
  exact hcd (activePhases_phase_representatives c hc d hd (Quotient.exact hclasses))

private theorem activeRaw_subset_phaseCarrier
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {c : ℝ} {z : Tiling.Plane}
    (hz : z ∈ openUnion K
      (activePhaseCentres (K := K) (T := T) (X := X) c)) :
    z.re ∈ activePhaseBase (K := K) (T := T) (X := X) c := by
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hz
  obtain ⟨s, hzs⟩ := hz
  obtain ⟨a, t, hst, hac, hmeetA⟩ := s.2
  have hztile : z ∈ (t.1 +ᵥ K.openCarrier) := by
    simpa [hst] using hzs
  have hambient : z ∈ openUnion K T :=
    Set.mem_iUnion.mpr ⟨⟨t.1, t.2⟩, hztile⟩
  have hcarrier := openUnion_subset_carrier_from_tiles X hTile
    hambient
  change z.re ∈ X.base at hcarrier
  obtain ⟨u, v, huv, hzuv⟩ :=
    exists_component_at_from_tile hproper hTile hcarrier
  let e : ActiveEndpoint K T X := ⟨u, ⟨v, huv, ?_⟩⟩
  · have hecomp := (endpointRight_spec e).1
    change IsCarrierComponent X u (endpointRight e) at hecomp
    have hev : endpointRight e = v := carrierComponent_right_unique hecomp huv
    have hmeetE : ((t.1 +ᵥ K.openCarrier) ∩
        {w : Tiling.Plane | w.re ∈ Ioo e.1 (endpointRight e)}).Nonempty := by
      refine ⟨z, hztile, ?_⟩
      simpa [hev] using hzuv
    have hclassE := activeEndpoint_class_eq_of_tile_meets
      hTile hIntegral a e t hmeetA hmeetE
    have hclass : phaseClass e.1 = phaseClass c :=
      hclassE.symm.trans hac
    refine Set.mem_iUnion.mpr ⟨⟨e, hclass⟩, ?_⟩
    simpa [hev] using hzuv
  · refine ⟨t, ?_⟩
    exact ⟨z, hztile, hzuv⟩

private theorem ambientRaw_phaseBase_subset_activeRaw
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    {c : ℝ} {z : Tiling.Plane}
    (hzBase : z.re ∈ activePhaseBase (K := K) (T := T) (X := X) c)
    (hzRaw : z ∈ openUnion K T) :
    z ∈ openUnion K
      (activePhaseCentres (K := K) (T := T) (X := X) c) := by
  obtain ⟨e, hzI⟩ := Set.mem_iUnion.mp hzBase
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hzRaw
  obtain ⟨t, hztile⟩ := hzRaw
  have ht : t.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) c := by
    exact ⟨e.1, t, rfl, e.2, ⟨z, hztile, hzI⟩⟩
  rw [openUnion, Tiling.Polygonal.openUnion,
    ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
  exact ⟨⟨t.1, ht⟩, hztile⟩

private theorem activePhaseCentres_subset
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    {c : ℝ} :
    activePhaseCentres (K := K) (T := T) (X := X) c ⊆ T := by
  intro t ht
  obtain ⟨a, t₀, rfl, _hac, _hmeet⟩ := ht
  exact t₀.2

private theorem activePhase_tiles
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {c : ℝ} (_hc : c ∈ activePhases (K := K) (T := T) (X := X)) :
    TilesOn K
      (activePhaseCentres (K := K) (T := T) (X := X) c)
      (Complex.re ⁻¹' activePhaseBase (K := K) (T := T) (X := X) c) := by
  have hsub : activePhaseCentres (K := K) (T := T) (X := X) c ⊆ T :=
    activePhaseCentres_subset
  have hcount : (activePhaseCentres (K := K) (T := T) (X := X) c).Countable :=
    hTile.1.mono hsub
  have hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements
        (activePhaseCentres (K := K) (T := T) (X := X) c)) := by
    apply (isPacking_iff_openCarrier_disjoint K _).2
    intro s hs t ht hst
    exact (isPacking_iff_openCarrier_disjoint K T).mp hTile.2.1
      (hsub hs) (hsub ht) hst
  refine ⟨hcount, hpack, ?_⟩
  filter_upwards [hTile.2.2] with z hz
  constructor
  · intro hzBase
    have hzCarrier : z ∈ X.carrier := by
      change z.re ∈ X.base
      exact activePhaseBase_subset_carrier c hzBase
    obtain ⟨t, hztile⟩ := hz.mp hzCarrier
    have hselected := ambientRaw_phaseBase_subset_activeRaw hzBase
      (Set.mem_iUnion.mpr ⟨t, hztile⟩)
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hselected
    exact hselected
  · intro hzRaw
    have hzPhase := activeRaw_subset_phaseCarrier
      (X := X) hproper hTile hIntegral
      (Set.mem_iUnion.mpr hzRaw)
    exact hzPhase

private theorem activePhaseBases_cover
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier) :
    (⋃ c : activePhases (K := K) (T := T) (X := X),
      activePhaseBase (K := K) (T := T) (X := X) c) = X.base := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨c, hxc⟩ := Set.mem_iUnion.mp hx
    exact activePhaseBase_subset_carrier c hxc
  · intro x hx
    obtain ⟨a, b, hab, hxab⟩ :=
      exists_component_at_from_tile hproper hTile hx
    have hgood := eventually_carrier_horizontal_slice X hTile
    obtain ⟨q, _hqI, hqgood⟩ :=
      exists_mem_Ioo_of_ae_real (a := (-1 : ℝ)) (b := 1) (by norm_num) hgood
    have hqgood' : ∀ᵐ y : ℝ ∂volume,
        y ∈ Ioo a b → slicePoint Axis.horizontal q y ∈ openUnion K T := by
      filter_upwards [hqgood] with y hy hyab
      exact hy (hab.2.2.2.1 hyab)
    obtain ⟨y, hyab, hyopen0⟩ := exists_mem_Ioo_of_ae_real hab.1 hqgood'
    have hyopen := hyopen0 hyab
    rw [openUnion, Tiling.Polygonal.openUnion,
      ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at hyopen
    obtain ⟨t, hty⟩ := hyopen
    let e : ActiveEndpoint K T X := ⟨a, ⟨b, hab, ?_⟩⟩
    · have hecomp := (endpointRight_spec e).1
      change IsCarrierComponent X a (endpointRight e) at hecomp
      have hev : endpointRight e = b := carrierComponent_right_unique hecomp hab
      let q' : {q : PhaseQuotient //
          q ∈ activePhaseClasses (K := K) (T := T) (X := X)} :=
        ⟨phaseClass e.1, ⟨e, rfl⟩⟩
      let c : activePhases (K := K) (T := T) (X := X) :=
        ⟨activePhaseRep q', ⟨q', rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨c, ?_⟩
      have hclass : phaseClass e.1 = phaseClass (activePhaseRep q') :=
        (activePhaseRep_class q').symm
      refine Set.mem_iUnion.mpr ⟨⟨e, hclass⟩, ?_⟩
      simpa [hev] using hxab
    · refine ⟨t, ?_⟩
      refine ⟨slicePoint Axis.horizontal q y, hty, ?_⟩
      simpa [slicePoint] using hyab


private theorem activePhaseBase_boundary_phase
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {c : ℝ} (_hc : c ∈ activePhases (K := K) (T := T) (X := X))
    {x : ℝ} (hx : x ∈ frontier
      (activePhaseBase (K := K) (T := T) (X := X) c)) :
    SameIntegerPhase x c := by
  let V : Set ℝ := activePhaseBase (K := K) (T := T) (X := X) c
  have hVopen : IsOpen V := activePhaseBase_open c
  have hVsub : V ⊆ X.base := activePhaseBase_subset_carrier c
  rw [frontier] at hx
  have hxnotbase : x ∉ X.base := by
    intro hxbase
    obtain ⟨a, b, hab, hxab⟩ :=
      exists_component_at_from_tile hproper hTile hxbase
    have hxa : 0 < x - a := sub_pos.mpr hxab.1
    have hbx : 0 < b - x := sub_pos.mpr hxab.2
    let ε : ℝ := min (x - a) (b - x) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hεa : ε ≤ x - a := by
      dsimp [ε]
      nlinarith [min_le_left (x - a) (b - x)]
    have hεb : ε ≤ b - x := by
      dsimp [ε]
      nlinarith [min_le_right (x - a) (b - x)]
    have hxJ : x ∈ Ioo (x - ε) (x + ε) := by
      constructor <;> linarith
    have hJsub : Ioo (x - ε) (x + ε) ⊆ Ioo a b := by
      intro y hy
      constructor <;> linarith [hy.1, hy.2]
    obtain ⟨y, hyJ, hyV⟩ :=
      mem_closure_iff.mp hx.1 (Ioo (x - ε) (x + ε)) isOpen_Ioo hxJ
    obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hyV
    have hyeab : y ∈ Ioo a b := hJsub hyJ
    have heq := carrierComponent_eq_of_intersect hab
      (endpointRight_spec e.1).1 hyeab hye
    have hxe : x ∈ Ioo e.1.1 (endpointRight e.1) := by
      simpa [heq.1, heq.2] using hxab
    have hxV : x ∈ V := by
      exact Set.mem_iUnion.mpr ⟨e, hxe⟩
    apply hx.2
    rw [hVopen.interior_eq]
    exact hxV
  have hxcl : x ∈ closure X.base := closure_mono hVsub hx.1
  have hxnotint : x ∉ interior X.base := by
    intro hxint
    exact hxnotbase (interior_subset hxint)
  have hxfront : x ∈ frontier X.base := ⟨hxcl, hxnotint⟩
  have hfinite := frontier_localFinite_from_tiles X hTile (x - 1) (x + 1)
  let F : Set ℝ := frontier X.base ∩ Icc (x - 1) (x + 1)
  have hF : F.Finite := by simpa [F] using hfinite
  have hxF : x ∈ F := ⟨hxfront, ⟨by linarith, by linarith⟩⟩
  let F' : Set ℝ := F \ {x}
  have hF' : F'.Finite := hF.sdiff
  have hxF' : x ∉ F' := by
    intro h
    exact h.2 (Set.mem_singleton x)
  have hnhds : F'ᶜ ∈ 𝓝 x := hF'.isClosed.isOpen_compl.mem_nhds hxF'
  obtain ⟨ε₀, hε₀, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  let ε : ℝ := min ε₀ 1 / 2
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hε₀' : ε ≤ ε₀ := by
    dsimp [ε]
    nlinarith [min_le_left ε₀ 1]
  have hε1 : ε ≤ 1 := by
    dsimp [ε]
    nlinarith [min_le_right ε₀ 1]
  have hxJ : x ∈ Ioo (x - ε) (x + ε) := by
    constructor <;> linarith
  obtain ⟨y, hyJ, hyV⟩ :=
    mem_closure_iff.mp hx.1 (Ioo (x - ε) (x + ε)) isOpen_Ioo hxJ
  obtain ⟨e, hye⟩ := Set.mem_iUnion.mp hyV
  have hecomp := (endpointRight_spec e.1).1
  have hyne : y ≠ x := by
    intro h
    exact hxnotbase (h ▸ hVsub hyV)
  have hendpoint : x = e.1.1 ∨ x = endpointRight e.1 := by
    rcases lt_or_gt_of_ne hyne with hyx | hxy
    · have hnotint : x ∉ Ioo e.1.1 (endpointRight e.1) := by
        intro hxi
        exact hxnotbase (hecomp.2.2.2.1 hxi)
      have hle : endpointRight e.1 ≤ x := by
        by_contra hlt
        have hlt' : x < endpointRight e.1 := lt_of_not_ge hlt
        exact hnotint ⟨lt_trans hye.1 hyx, hlt'⟩
      have hFpoint : endpointRight e.1 ∈ F := by
        refine ⟨hecomp.2.2.1, ?_⟩
        constructor
        · linarith [hyJ.1, hye.2, hε1]
        · linarith [hle]
      have hball : endpointRight e.1 ∈ Metric.ball x ε₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [hyJ.1, hye.2, hε₀']
        · linarith [hle, hε₀]
      have hnotF' : endpointRight e.1 ∉ F' := hεsub hball
      have heqx : endpointRight e.1 = x := by
        by_contra hne
        exact hnotF' ⟨hFpoint, hne⟩
      exact Or.inr heqx.symm
    · have hnotint : x ∉ Ioo e.1.1 (endpointRight e.1) := by
        intro hxi
        exact hxnotbase (hecomp.2.2.2.1 hxi)
      have hle : x ≤ e.1.1 := by
        by_contra hlt
        have hlt' : e.1.1 < x := lt_of_not_ge hlt
        exact hnotint ⟨hlt', lt_trans hxy hye.2⟩
      have hFpoint : e.1.1 ∈ F := by
        refine ⟨hecomp.2.1, ?_⟩
        constructor
        · linarith [hle]
        · linarith [hye.1, hyJ.2, hε1]
      have hball : e.1.1 ∈ Metric.ball x ε₀ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor
        · linarith [hle, hε₀]
        · linarith [hye.1, hyJ.2, hε₀']
      have hnotF' : e.1.1 ∉ F' := hεsub hball
      have heqx : e.1.1 = x := by
        by_contra hne
        exact hnotF' ⟨hFpoint, hne⟩
      exact Or.inl heqx.symm
  rcases hendpoint with hleft | hright
  · have heclass := Quotient.exact e.2
    change SameIntegerPhase e.1.1 c at heclass
    simpa [hleft] using heclass
  · obtain ⟨n, _hnpos, hdiff⟩ :=
      (integralRegion_genericSections X hTile hIntegral
        hecomp.1 hecomp.2.1 hecomp.2.2.1
        ⟨hecomp.2.2.2.1, hecomp.2.2.2.2⟩
        (endpointTile_spec e.1)).2
    have hba : SameIntegerPhase
        (endpointRight e.1) e.1.1 := ⟨n, hdiff⟩
    simpa [hright] using sameIntegerPhase_trans hba (Quotient.exact e.2)

private theorem openSegment_eq_horizontal_local
    {a b : Tiling.Plane} (him : a.im = b.im) :
    openSegment ℝ a b =
      (fun x : ℝ ↦ (x : ℂ) + (a.im : ℂ) * Complex.I) ''
        openSegment ℝ a.re b.re := by
  ext z
  constructor
  · rintro ⟨u, v, hu, hv, huv, hz⟩
    refine ⟨z.re, ⟨u, v, hu, hv, huv, ?_⟩, ?_⟩
    · rw [← hz]
      simp
    · rw [← hz]
      have hweighted (r : ℝ) : u * r + v * r = r := by
        rw [← add_mul, huv, one_mul]
      apply Complex.ext <;> simp [him, hweighted]
  · rintro ⟨x, ⟨u, v, hu, hv, huv, hx⟩, rfl⟩
    refine ⟨u, v, hu, hv, huv, ?_⟩
    have hweighted (r : ℝ) : u * r + v * r = r := by
      rw [← add_mul, huv, one_mul]
    apply Complex.ext
    · simpa using hx
    · simp [him, hweighted]

private theorem placedSupport_subset_closure_regularSupport_local
    (K : Region) {A : Set Tiling.Plane} {s : Tiling.Plane} (hs : s ∈ A) :
    s +ᵥ K.support ⊆ closure (regularSupport K A) := by
  rw [K.isPolygonal.closure_interior.symm,
    ← closure_vadd s (interior K.support)]
  apply closure_mono
  intro z hz
  rw [regularSupport]
  apply
    (isOpen_iUnion
      (fun i : A ↦ isOpen_interior.vadd (i : Tiling.Plane))).subset_interior_closure
  change z ∈ ⋃ i : A, (i : Tiling.Plane) +ᵥ K.openCarrier
  exact Set.mem_iUnion_of_mem ⟨s, hs⟩ hz

private theorem activePhase_plate_has_unique_phase
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (hproper : X.base ≠ Set.univ) (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    ∀ P : Tiling.AxisParallel.Continuous.VerticalPlate K T,
      ∃! c : ℝ, c ∈ activePhases (K := K) (T := T) (X := X) ∧
        P.centres ⊆ activePhaseCentres (K := K) (T := T) (X := X) c := by
  have hphase_mem : ∀ t : T, ∃ c : ℝ,
      c ∈ activePhases (K := K) (T := T) (X := X) ∧
        t.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) c := by
    intro t
    have ht : t.1 ∈ T := t.2
    have hUnion := activePhaseCentres_union hproper hTile
    have ht' : t.1 ∈ ⋃ c : activePhases (K := K) (T := T) (X := X),
        activePhaseCentres (K := K) (T := T) (X := X) c := by
      rw [hUnion]
      exact ht
    obtain ⟨c, htc⟩ := Set.mem_iUnion.mp ht'
    exact ⟨c.1, c.2, htc⟩
  have hphase_adj : ∀ {s t : T},
      (Tiling.AxisParallel.Continuous.verticalPlateGraph K T).Adj s t →
      ∀ {c d : ℝ}, c ∈ activePhases (K := K) (T := T) (X := X) →
        d ∈ activePhases (K := K) (T := T) (X := X) →
        s.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) c →
        t.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) d →
        SameIntegerPhase c d := by
    intro s t hst c d hc hd hsc htd
    obtain ⟨es, ts, hstile, hscs, hmeetS⟩ := hsc
    obtain ⟨et, tt, httile, htdt, hmeetT⟩ := htd
    have hstile' : ts.1 = s.1 := hstile.symm
    have httile' : tt.1 = t.1 := httile.symm
    have hcontact := (Tiling.AxisParallel.Continuous.verticalPlateGraph_adj_iff s t).mp hst
    obtain ⟨hp, hq, hpq, him, hseg⟩ := hcontact.2
    have hre : hp.re ≠ hq.re := by
      intro h
      exact hpq (Complex.ext h him)
    let F : Set ℝ := frontier X.base ∩ uIcc hp.re hq.re
    have hF : F.Finite := by
      apply (frontier_localFinite_from_tiles X hTile
        (min hp.re hq.re) (max hp.re hq.re)).subset
      intro x hx
      refine ⟨hx.1, ?_⟩
      simpa only [uIcc] using hx.2
    have hJsub : openSegment ℝ hp.re hq.re ⊆ uIcc hp.re hq.re := by
      intro x hx
      have hseg := openSegment_subset_segment ℝ hp.re hq.re hx
      simpa only [segment_eq_uIcc] using hseg
    have hJinf : (openSegment ℝ hp.re hq.re).Infinite := by
      rcases lt_or_gt_of_ne hre with hpq' | hqp'
      · rw [openSegment_eq_Ioo hpq']
        exact Set.Ioo_infinite hpq'
      · rw [openSegment_symm, openSegment_eq_Ioo hqp']
        exact Set.Ioo_infinite hqp'
    obtain ⟨x, hxJ, hxnotF⟩ : ∃ x ∈ openSegment ℝ hp.re hq.re, x ∉ F := by
      by_contra h
      push Not at h
      exact hJinf.not_finite (hF.subset h)
    have hxnotfront : x ∉ frontier X.base := by
      intro hxf
      exact hxnotF ⟨hxf, hJsub hxJ⟩
    let z : Tiling.Plane := (x : ℂ) + (hp.im : ℂ) * Complex.I
    have hzseg : z ∈ openSegment ℝ hp hq := by
      rw [openSegment_eq_horizontal_local him]
      exact ⟨x, hxJ, rfl⟩
    have hzfrontS := hseg hzseg
    have hzfrontT := hseg hzseg
    have hreg : regularSupport K T = X.carrier := by
      exact regularSupport_eq_of_tilesOn
        (X.base_open.preimage Complex.continuous_re)
        (by
          change interior (closure (Complex.re ⁻¹' X.base)) =
            Complex.re ⁻¹' X.base
          rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
            X.base_regular])
        hTile
    have hzsupportS : z ∈ s.1 +ᵥ K.support := by
      rw [← (K.isPolygonal.isClosed.vadd s.1).closure_eq]
      exact frontier_subset_closure hzfrontS.1.1
    have hzsupportT : z ∈ t.1 +ᵥ K.support := by
      rw [← (K.isPolygonal.isClosed.vadd t.1).closure_eq]
      exact frontier_subset_closure hzfrontT.1.2
    have hzclS : z ∈ closure (regularSupport K T) :=
      placedSupport_subset_closure_regularSupport_local K s.2 hzsupportS
    have hzclT : z ∈ closure (regularSupport K T) :=
      placedSupport_subset_closure_regularSupport_local K t.2 hzsupportT
    have hxcl : x ∈ closure X.base := by
      have hzcl : z ∈ closure X.carrier := by simpa [hreg] using hzclS
      change z ∈ closure (Complex.re ⁻¹' X.base) at hzcl
      rw [Complex.closure_preimage_re] at hzcl
      simpa [z] using hzcl
    have hxint : x ∈ interior X.base := by
      by_contra hxint
      exact hxnotfront ⟨hxcl, hxint⟩
    have hxbase : x ∈ X.base := by
      rw [X.base_open.interior_eq] at hxint
      exact hxint
    obtain ⟨a, b, hab, hxab⟩ :=
      exists_component_at_from_tile hproper hTile hxbase
    have hopenComp : IsOpen {w : Tiling.Plane | w.re ∈ Ioo a b} :=
      isOpen_Ioo.preimage Complex.continuous_re
    have hzab : z ∈ {w : Tiling.Plane | w.re ∈ Ioo a b} := by
      change z.re ∈ Ioo a b
      simpa [z] using hxab
    have hzclOpenS : z ∈ closure (s.1 +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change z ∈ s.1 +ᵥ closure K.openCarrier
      rw [show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
      exact hzsupportS
    have hzclOpenT : z ∈ closure (t.1 +ᵥ K.openCarrier) := by
      rw [closure_vadd]
      change z ∈ t.1 +ᵥ closure K.openCarrier
      rw [show closure K.openCarrier = K.support from K.isPolygonal.closure_interior]
      exact hzsupportT
    have hmeetS' : ((s.1 +ᵥ K.openCarrier) ∩
        {w : Tiling.Plane | w.re ∈ Ioo a b}).Nonempty := by
      obtain ⟨w, hwab, hwS⟩ := mem_closure_iff.mp hzclOpenS _ hopenComp hzab
      exact ⟨w, hwS, hwab⟩
    have hmeetT' : ((t.1 +ᵥ K.openCarrier) ∩
        {w : Tiling.Plane | w.re ∈ Ioo a b}).Nonempty := by
      obtain ⟨w, hwab, hwT⟩ := mem_closure_iff.mp hzclOpenT _ hopenComp hzab
      exact ⟨w, hwT, hwab⟩
    let g : ActiveEndpoint K T X := ⟨a, ⟨b, hab, ⟨s, hmeetS'⟩⟩⟩
    have hgright : endpointRight g = b :=
      carrierComponent_right_unique (endpointRight_spec g).1 hab
    have hmeetSg : ((ts.1 +ᵥ K.openCarrier) ∩
        {z : Tiling.Plane | z.re ∈ Ioo g.1 (endpointRight g)}).Nonempty := by
      simpa [g, hgright, hstile'] using hmeetS'
    have hmeetTg : ((tt.1 +ᵥ K.openCarrier) ∩
        {z : Tiling.Plane | z.re ∈ Ioo g.1 (endpointRight g)}).Nonempty := by
      simpa [g, hgright, httile'] using hmeetT'
    have hsg : phaseClass es.1 = phaseClass g.1 := by
      apply activeEndpoint_class_eq_of_tile_meets hTile hIntegral es g ts
        hmeetS hmeetSg
    have htg : phaseClass et.1 = phaseClass g.1 := by
      apply activeEndpoint_class_eq_of_tile_meets hTile hIntegral et g tt
        hmeetT hmeetTg
    have hclasses : phaseClass c = phaseClass d := by
      exact hscs.symm.trans (hsg.trans (htg.symm.trans htdt))
    have hcd : SameIntegerPhase c d := by
      have hq := Quotient.exact hclasses
      change SameIntegerPhase c d at hq
      exact hq
    exact hcd
  intro P
  obtain ⟨s, hs⟩ := SimpleGraph.ConnectedComponent.nonempty_supp P
  obtain ⟨c, hc, hsc⟩ := hphase_mem s
  have hsP : s.1 ∈ P.centres := ⟨s, hs, rfl⟩
  let hphaseOf : T → ℝ := fun t => Classical.choose (hphase_mem t)
  have hphaseOf_spec (t : T) :
      hphaseOf t ∈ activePhases (K := K) (T := T) (X := X) ∧
        t.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) (hphaseOf t) :=
    by simpa [hphaseOf] using Classical.choose_spec (hphase_mem t)
  have hphaseOf_adj {u v : T}
      (huv : (Tiling.AxisParallel.Continuous.verticalPlateGraph K T).Adj u v) :
      hphaseOf u = hphaseOf v := by
    apply activePhases_phase_representatives (hphaseOf u) (hphaseOf_spec u).1
      (hphaseOf v) (hphaseOf_spec v).1
    exact hphase_adj huv (hphaseOf_spec u).1 (hphaseOf_spec v).1
      (hphaseOf_spec u).2 (hphaseOf_spec v).2
  have hphaseOf_walk {u v : T} :
      ∀ p : (Tiling.AxisParallel.Continuous.verticalPlateGraph K T).Walk u v,
        hphaseOf u = hphaseOf v := by
    intro p
    induction p with
    | nil => rfl
    | cons h q ih => exact (hphaseOf_adj h).trans ih
  refine ⟨hphaseOf s, ⟨(hphaseOf_spec s).1, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := ht
    have p := P.reachable_of_mem_supp hs ht'
    have hphase : hphaseOf s = hphaseOf t' :=
      p.elim (fun q => hphaseOf_walk q)
    rw [hphase]
    exact (hphaseOf_spec t').2
  · rintro d ⟨hd, hPd⟩
    have hcommon : s.1 ∈ activePhaseCentres (K := K) (T := T) (X := X) d := hPd hsP
    by_contra hne
    have hne' : hphaseOf s ≠ d := fun h => hne h.symm
    exact Set.disjoint_left.mp
      (activePhaseCentres_pairwise hTile hIntegral (hphaseOf_spec s).1 hd hne')
      (hphaseOf_spec s).2 hcommon

private theorem activePhaseBase_pairwise
    {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
    {X : PeriodicVerticalCarrier} {c d : ℝ}
    (hc : c ∈ activePhases (K := K) (T := T) (X := X))
    (hd : d ∈ activePhases (K := K) (T := T) (X := X))
    (hcd : c ≠ d) :
    Disjoint (activePhaseBase (K := K) (T := T) (X := X) c)
      (activePhaseBase (K := K) (T := T) (X := X) d) := by
  have hclass : phaseClass c ≠ phaseClass d := by
    intro h
    apply hcd
    exact activePhases_phase_representatives c hc d hd (Quotient.exact h)
  rw [Set.disjoint_left]
  intro x hxc hxd
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxc
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxd
  have hab : IsCarrierComponent X a.1.1 (endpointRight a.1) :=
    (endpointRight_spec a.1).1
  have hbb : IsCarrierComponent X b.1.1 (endpointRight b.1) :=
    (endpointRight_spec b.1).1
  have hphase : phaseClass a.1.1 ≠ phaseClass b.1.1 := by
    intro h
    apply hclass
    exact a.2.symm.trans (h.trans b.2)
  exact Set.disjoint_left.mp
    (carrierComponent_intervals_disjoint_of_phase_ne hab hbb hphase)
    hxa hxb

theorem carrierPhaseDecomposition :
    ∀ {K : Tiling.AxisParallel.Region} {T : Set Tiling.Plane}
      (X : PeriodicVerticalCarrier),
    X.base ≠ Set.univ →
    Tiling.AxisParallel.TilesOn K T X.carrier →
    (∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) →
    ∃ (phases : Set ℝ) (phaseBase : ℝ → Set ℝ)
        (phaseCentres : ℝ → Set Tiling.Plane),
      IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres := by
  intro K T X hproper hTile hIntegral
  refine ⟨activePhases (K := K) (T := T) (X := X),
    activePhaseBase (K := K) (T := T) (X := X),
    activePhaseCentres (K := K) (T := T) (X := X), ?_⟩
  refine {
    phases_nonempty := activePhases_nonempty hproper hTile
    phaseBase_open := by
      intro c _
      exact activePhaseBase_open c
    phaseBase_regular := by
      intro c hc
      exact activePhaseBase_regular hproper hTile hc
    phaseCentres_nonempty := by
      intro c hc
      exact activePhaseCentres_nonempty hc
    phaseCentres_pairwise := activePhaseCentres_pairwise hTile hIntegral
    phaseCentres_union := activePhaseCentres_union hproper hTile
    phase_tiles := by
      intro c hc
      exact activePhase_tiles hproper hTile hIntegral hc
    phaseBases_pairwise := by
      intro c hc d hd hcd
      exact activePhaseBase_pairwise hc hd hcd
    phaseBases_cover := by
      rw [activePhaseBases_cover hproper hTile]
      exact X.base_regular
    centre_phase := by
      intro c hc z hz
      exact activePhaseCentres_centre_phase hTile hIntegral hc hz
    boundary_phase := by
      intro c hc x hx
      exact activePhaseBase_boundary_phase hproper hTile hIntegral hc hx
    phase_representatives := by
      intro c hc d hd hcd
      exact activePhases_phase_representatives c hc d hd hcd
    plate_has_unique_phase :=
      activePhase_plate_has_unique_phase hproper hTile hIntegral }

private theorem setPeriodicBy_iUnion_local
    {ι : Sort*} {A : ι → Set Tiling.Plane} {v : Tiling.Plane}
    (hA : ∀ i, Tiling.RationalPolygonal.SetPeriodicBy (A i) v) :
    Tiling.RationalPolygonal.SetPeriodicBy (⋃ i, A i) v := by
  intro x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (hA i x).mp hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (hA i x).mpr hi⟩

private theorem setPeriodicBy_interior_closure_local
    {A : Set Tiling.Plane} {v : Tiling.Plane}
    (hA : Tiling.RationalPolygonal.SetPeriodicBy A v) :
    Tiling.RationalPolygonal.SetPeriodicBy (interior (closure A)) v := by
  intro x
  have hperiodic : Function.Periodic (fun y : Tiling.Plane ↦ y ∈ A) v :=
    fun y ↦ propext (hA y)
  have hvadd : v +ᵥ A = A := by
    ext y
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
    simpa [add_comm, add_left_comm, add_assoc] using
      (hperiodic (-v + y)).symm
  have hvadd_regular : v +ᵥ interior (closure A) = interior (closure A) := by
    calc
      v +ᵥ interior (closure A) = interior (v +ᵥ closure A) := by
        rw [interior_vadd]
      _ = interior (closure (v +ᵥ A)) := by rw [closure_vadd]
      _ = interior (closure A) := by rw [hvadd]
  have hx := Set.ext_iff.mp hvadd_regular (x + v)
  simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
    add_comm, add_left_comm, add_assoc] using hx.symm

private def finitePhasePeriods_commonStatement : Prop :=
  ∀ {K : Tiling.AxisParallel.Region} {phases : Set ℝ}
      (_hfinite : phases.Finite) (S : ℝ → Set Tiling.Plane) (L : ℝ → ℕ),
    (∀ c ∈ phases, 0 < L c) →
    (∀ c ∈ phases, Tiling.RationalPolygonal.SetPeriodicBy
      (Tiling.AxisParallel.regularSupport K (S c)) ((L c : ℝ) : ℂ)) →
    ∃ M : ℕ, 0 < M ∧
      (∀ c ∈ phases, Tiling.RationalPolygonal.SetPeriodicBy
        (Tiling.AxisParallel.regularSupport K (S c)) ((M : ℝ) : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (Tiling.AxisParallel.regularSupport K (⋃ c : phases, S c.1)) ((M : ℝ) : ℂ)

private theorem finitePhasePeriods_common :
    finitePhasePeriods_commonStatement := by
  intro K phases hfinite S L hLpos hLperiod
  classical
  let M : ℕ := ∏ c ∈ hfinite.toFinset, L c
  have hMpos : 0 < M := by
    dsimp [M]
    exact Finset.prod_pos fun c hc ↦ hLpos c (hfinite.mem_toFinset.mp hc)
  have hphasePeriod : ∀ c ∈ phases,
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (S c)) ((M : ℝ) : ℂ) := by
    intro c hc
    have hdiv : L c ∣ M := by
      dsimp [M]
      exact Finset.dvd_prod_of_mem (fun x ↦ L x) (hfinite.mem_toFinset.mpr hc)
    obtain ⟨m, hm⟩ := hdiv
    have hperiodic : Function.Periodic
        (fun z : Tiling.Plane ↦ z ∈ regularSupport K (S c)) ((L c : ℝ) : ℂ) :=
      fun z ↦ propext (hLperiod c hc z)
    have hperiodM : ((M : ℝ) : ℂ) = m • (((L c : ℝ) : ℂ)) := by
      rw [hm]
      norm_num
      ring
    rw [hperiodM]
    exact fun z ↦ eq_iff_iff.mp (hperiodic.nsmul m z)
  refine ⟨M, hMpos, hphasePeriod, ?_⟩
  rw [regularSupport_iUnion]
  apply setPeriodicBy_interior_closure_local
  apply setPeriodicBy_iUnion_local
  intro c
  exact hphasePeriod c.1 c.2

open Tiling.AxisParallel.Discrete

/-- A nonempty carrier confined to a finite horizontal base cannot have a
positive scalar period. -/
private theorem finiteBase_not_positiveScalarPeriodic
    {F : Finset TranslationalTilings.Plane}
    {S : Set TranslationalTilings.Plane} {B : Set ℤ} {L : ℕ}
    (hF : F.Nonempty) (hB : B.Finite) (hS : S.Nonempty) (hL : 0 < L)
    (hsub : Tiling.RationalPolygonal.discreteCarrier F S ⊆
      verticalDiscreteCylinder B) :
    ¬ TranslationalTilings.SetScalarPeriodic L
      (Tiling.RationalPolygonal.discreteCarrier F S) := by
  intro hperiod
  obtain ⟨f, hf⟩ := hF
  obtain ⟨s, hs⟩ := hS
  let x : TranslationalTilings.Plane := f + s
  have hx : x ∈ Tiling.RationalPolygonal.discreteCarrier F S :=
    ⟨f, hf, s, hs, rfl⟩
  have hxB : firstDiscreteCoordinate x ∈ B :=
    (mem_verticalDiscreteCylinder_iff x B).mp (hsub hx)
  let C : Finset ℤ := hB.toFinset
  have hxC : firstDiscreteCoordinate x ∈ C := by
    simpa [C] using hxB
  let n : ℤ := C.max' ⟨firstDiscreteCoordinate x, hxC⟩ -
    firstDiscreteCoordinate x + 1
  let w : TranslationalTilings.Plane := n • horizontalDiscreteUnit
  have hxshift : x + (L : ℤ) • w ∈
      Tiling.RationalPolygonal.discreteCarrier F S :=
    (hperiod x w).2 hx
  have hshiftB : firstDiscreteCoordinate (x + (L : ℤ) • w) ∈ B :=
    (mem_verticalDiscreteCylinder_iff _ B).mp (hsub hxshift)
  have hshiftC : firstDiscreteCoordinate (x + (L : ℤ) • w) ∈ C := by
    simpa [C] using hshiftB
  have hle := C.le_max' _ hshiftC
  have hn : (0 : ℤ) < n := by
    dsimp [n]
    have := C.le_max' _ hxC
    omega
  have hLz : (1 : ℤ) ≤ (L : ℤ) := by exact_mod_cast hL
  have hge : n ≤ (L : ℤ) * n := by nlinarith
  have hcoord : firstDiscreteCoordinate (x + (L : ℤ) • w) =
      firstDiscreteCoordinate x + (L : ℤ) * n := by
    simp [w, firstDiscreteCoordinate]
  have hle' : firstDiscreteCoordinate x + (L : ℤ) * n ≤
      C.max' ⟨firstDiscreteCoordinate x, hxC⟩ := by
    calc
      _ = firstDiscreteCoordinate (x + (L : ℤ) • w) := hcoord.symm
      _ ≤ _ := hle
  dsimp [n] at hle'
  omega

private def repeatedDiscreteSet (N : ℕ) (S : Set TranslationalTilings.Plane) :
    Set TranslationalTilings.Plane :=
  ⋃ k : ℤ, TranslationalTilings.translateSet
    ((k * (N : ℤ)) • horizontalDiscreteUnit) S

private structure FiniteCarrierPeriodization
    (F : Finset TranslationalTilings.Plane) (A : Set TranslationalTilings.Plane)
    (B : Set ℤ) where
  spacing : ℕ
  spacing_pos : 0 < spacing
  periodicCentres : Set TranslationalTilings.Plane
  periodicTarget : Set TranslationalTilings.Plane
  periodicCentres_eq : periodicCentres = repeatedDiscreteSet spacing A
  periodicTarget_eq : periodicTarget = repeatedDiscreteSet spacing
    (verticalDiscreteCylinder B)
  tiles : TranslationalTilings.Tiles F periodicCentres periodicTarget
  vertical_period : Tiling.RationalPolygonal.DiscretePeriodicBy periodicTarget
    verticalDiscreteUnit
  horizontal_period : TranslationalTilings.SetScalarPeriodic spacing periodicTarget
  plateEquiv :
    (Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit × ℤ) ≃
    Tiling.RationalPolygonal.QuakePlate F periodicCentres verticalDiscreteUnit
  plateTranslations : ∀ P k,
    Tiling.RationalPolygonal.quakePlateTranslations (plateEquiv (P, k)) =
      TranslationalTilings.translateSet
        ((k * (spacing : ℤ)) • horizontalDiscreteUnit)
        (Tiling.RationalPolygonal.quakePlateTranslations P)
  column_iff : ∀ P k,
    IsDiscreteVerticalColumn (plateEquiv (P, k)) ↔ IsDiscreteVerticalColumn P

private theorem finiteBand_spacing
    (B : Finset ℤ) :
    ∃ R : ℕ, 0 < R ∧
      ∀ p : ℤ × ℤ, p.1 ≠ p.2 →
        Disjoint
          (TranslationalTilings.translateSet
            ((p.1 * (R : ℤ)) • horizontalDiscreteUnit)
            (verticalDiscreteCylinder (B : Set ℤ)))
          (TranslationalTilings.translateSet
            ((p.2 * (R : ℤ)) • horizontalDiscreteUnit)
            (verticalDiscreteCylinder (B : Set ℤ))) := by
  classical
  by_cases hB : B.Nonempty
  · exact Tiling.AxisParallel.Discrete.exists_bandSpacing B hB
  · refine ⟨1, by omega, ?_⟩
    intro p hp
    rw [Set.disjoint_left]
    intro z hz _
    have hz' := (mem_verticalDiscreteCylinder_iff
      (z - (p.1 * (1 : ℤ)) • horizontalDiscreteUnit) (B : Set ℤ)).mp hz
    exact hB ⟨_, hz'⟩

private theorem finiteCarrierPeriodization_exists
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {B : Set ℤ}
    (hF : F.Nonempty) (hB : B.Finite)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B)) :
    Nonempty (FiniteCarrierPeriodization F A B) := by
  classical
  let BF : Finset ℤ := hB.toFinset
  have hBF : (BF : Set ℤ) = B := by ext; simp [BF]
  have hTileF : TranslationalTilings.Tiles F A
      (verticalDiscreteCylinder (BF : Set ℤ)) := by simpa [hBF] using hTile
  obtain ⟨R, hR, hCopies⟩ := finiteBand_spacing BF
  obtain ⟨hTile', hVert, hHoriz⟩ :=
    periodizeFiniteBand_tiles_general hTileF hR hCopies
  obtain ⟨plateEquiv, hplate⟩ :=
    periodizeFiniteBand_verticalPlates_general hF hTileF hR hCopies
  refine ⟨{
    spacing := R
    spacing_pos := hR
    periodicCentres := ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit) A
    periodicTarget := ⋃ d : ℤ, TranslationalTilings.translateSet
      ((d * (R : ℤ)) • horizontalDiscreteUnit)
        (verticalDiscreteCylinder (BF : Set ℤ))
    periodicCentres_eq := rfl
    periodicTarget_eq := by simp [repeatedDiscreteSet, hBF]
    tiles := ?_
    vertical_period := ?_
    horizontal_period := ?_
    plateEquiv := ?_
    plateTranslations := ?_
    column_iff := ?_ }⟩
  · exact hTile'
  · exact hVert
  · exact hHoriz
  · exact plateEquiv
  · intro P k
    exact (hplate P k).1
  · intro P k
    exact (hplate P k).2

theorem finiteDiscreteCarrier_allColumns
    {F : Finset TranslationalTilings.Plane}
    {A : Set TranslationalTilings.Plane} {B : Set ℤ}
    (hF : F.Nonempty) (hB : B.Finite)
    (hTile : TranslationalTilings.Tiles F A (verticalDiscreteCylinder B)) :
    ∀ P : Tiling.RationalPolygonal.QuakePlate F A verticalDiscreteUnit,
      IsDiscreteVerticalColumn P := by
  classical
  obtain ⟨D⟩ := finiteCarrierPeriodization_exists hF hB hTile
  intro P
  by_contra hnon
  let Q := D.plateEquiv (P, (0 : ℤ))
  have hQnon : ¬ IsDiscreteVerticalColumn Q := fun hQ ↦
    hnon ((D.column_iff P 0).mp hQ)
  obtain ⟨L, hL, _hspacing, hperiod, _hcolumns⟩ :=
    exists_discretePlatePeriodicity hF D.spacing_pos D.vertical_period
      D.horizontal_period D.tiles
  have hQperiod := hperiod Q hQnon
  have hQP : Tiling.RationalPolygonal.quakePlateTranslations Q =
      Tiling.RationalPolygonal.quakePlateTranslations P := by
    rw [D.plateTranslations P 0]
    ext z
    simp [TranslationalTilings.translateSet]
  obtain ⟨t, ht⟩ :
      (Tiling.RationalPolygonal.quakePlateTranslations P).Nonempty := by
    refine P.ind ?_
    intro a
    exact ⟨a, Tiling.RationalPolygonal.mem_quakePlateTranslations_mk a⟩
  have hsub : Tiling.RationalPolygonal.discreteCarrier F
      (Tiling.RationalPolygonal.quakePlateTranslations P) ⊆
      verticalDiscreteCylinder B := by
    intro x hx
    apply Tiling.AxisParallel.Discrete.discreteCarrier_subset_target hTile
    rcases hx with ⟨f, hf, a, ha, rfl⟩
    exact ⟨f, hf, a, ha.1, rfl⟩
  apply finiteBase_not_positiveScalarPeriodic hF hB ⟨t, ht⟩ hL hsub
  simpa [hQP] using hQperiod


private theorem base_regular_of_support_cylinder
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T)
    (hP : P.support = Complex.re ⁻¹' P.base) :
    interior (closure P.base) = P.base := by
  have hpreimage :
      Complex.re ⁻¹' interior (closure P.base) = Complex.re ⁻¹' P.base := by
    calc
      Complex.re ⁻¹' interior (closure P.base) =
          interior (closure (Complex.re ⁻¹' P.base)) := by
            rw [Complex.closure_preimage_re, Complex.interior_preimage_re]
      _ = interior (closure P.support) := by rw [hP]
      _ = P.support := (regularSupport_isRegularOpen K P.centres).2
      _ = Complex.re ⁻¹' P.base := hP
  apply (Set.preimage_injective.mpr ?_) hpreimage
  intro r
  exact ⟨(r : ℂ), by simp⟩

private theorem shiftedSupport_eq
    {K : Region} {T : Set Tiling.Plane} (P : VerticalPlate K T) (r : ℝ)
    (hP : P.support = Complex.re ⁻¹' P.base) :
    regularSupport K ((((r : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) = P.support := by
  rw [regularSupport_vadd, ← VerticalPlate.support_eq_regularSupport, hP]
  ext z
  simp [Set.mem_vadd_set_iff_neg_vadd_mem]

private theorem shiftedPlateContact_iff :
    ∀ {K : Region} {T : Set Tiling.Plane}
        (shift : VerticalPlate K T → ℝ),
      (∀ P : VerticalPlate K T, P.support = Complex.re ⁻¹' P.base) →
      (∀ P Q : VerticalPlate K T, P ≠ Q → Disjoint P.support Q.support) →
      (∀ (P : VerticalPlate K T) (s t : P.centres),
        HorizontalProperContact K
            ((((shift P : ℝ) : ℂ) * Complex.I) + s.1)
            ((((shift P : ℝ) : ℂ) * Complex.I) + t.1) ↔
          HorizontalProperContact K s.1 t.1) ∧
      ∀ (P Q : VerticalPlate K T), P ≠ Q →
        ∀ (s : P.centres) (t : Q.centres),
          ¬ HorizontalProperContact K
            ((((shift P : ℝ) : ℂ) * Complex.I) + s.1)
            ((((shift Q : ℝ) : ℂ) * Complex.I) + t.1) := by
  intro K T shift hslab hdisj
  constructor
  · intro P s t
    have hcarrier : K.openCarrier = positiveSimilarity 1 0 '' K.openCarrier := by
      rw [positiveSimilarity_image_eq_vadd_smul, one_smul, zero_vadd]
    simpa [positiveSimilarity, vadd_eq_add, add_comm] using
      (horizontalProperContact_positiveSimilarity_iff
        (K := K) (R := K) (s := 1) (r := 0)
        (c := ((shift P : ℝ) : ℂ) * Complex.I) (by norm_num)
        hcarrier s.1 t.1).symm
  · intro P Q hPQ s t
    let A := (((shift P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres
    let B := (((shift Q : ℝ) : ℂ) * Complex.I) +ᵥ Q.centres
    have hA : regularSupport K A = Complex.re ⁻¹' P.base := by
      change regularSupport K
        ((((shift P : ℝ) : ℂ) * Complex.I) +ᵥ P.centres) = _
      rw [shiftedSupport_eq P (shift P) (hslab P), hslab P]
    have hB : regularSupport K B = Complex.re ⁻¹' Q.base := by
      change regularSupport K
        ((((shift Q : ℝ) : ℂ) * Complex.I) +ᵥ Q.centres) = _
      rw [shiftedSupport_eq Q (shift Q) (hslab Q), hslab Q]
    have hAB : Disjoint (regularSupport K A) (regularSupport K B) := by
      rw [hA, ← hslab P, hB, ← hslab Q]
      exact hdisj P Q hPQ
    apply Tiling.AxisParallel.Continuous.plateSlide_noCrossing
      (base_regular_of_support_cylinder P (hslab P))
      (base_regular_of_support_cylinder Q (hslab Q)) hAB hA hB
    · exact ⟨s.1, s.2, rfl⟩
    · exact ⟨t.1, t.2, rfl⟩

private structure NormalizedPhasePlateTransport
    (K : Region) (T : Set Tiling.Plane) (phaseCentres : Set Tiling.Plane)
    (c : ℝ) (normalizedCentres : Set Tiling.Plane) where
  normalizedCentres_eq : normalizedCentres = ((-c : ℝ) : ℂ) +ᵥ phaseCentres
  plateEquiv :
    {P : VerticalPlate K T // P.centres ⊆ phaseCentres} ≃
      VerticalPlate K normalizedCentres
  centres_eq : ∀ P,
    (plateEquiv P).centres = ((-c : ℝ) : ℂ) +ᵥ P.1.centres
  support_eq : ∀ P,
    (plateEquiv P).support = ((-c : ℝ) : ℂ) +ᵥ P.1.support
  column_iff : ∀ P, IsVerticalColumn (plateEquiv P) ↔ IsVerticalColumn P.1


private theorem walk_support_reachable_from_start
    {V : Type*} {G : SimpleGraph V} {a b x : V}
    (p : G.Walk a b) (hx : x ∈ p.support) : G.Reachable a x := by
  induction p with
  | nil =>
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hx
      subst x
      exact SimpleGraph.Reachable.refl _
  | @cons a d b hadj p ih =>
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact SimpleGraph.Reachable.refl _
      · exact hadj.reachable.trans (ih hx)

private def phaseInclusionHom
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T) :
    verticalPlateGraph K A →g verticalPlateGraph K T where
  toFun z := ⟨z.1, hAT z.2⟩
  map_rel' := by
    intro s t hst
    rw [verticalPlateGraph_adj_iff] at hst ⊢
    exact ⟨fun h => hst.1 (Subtype.ext (congrArg (fun z : T => z.1) h)), hst.2⟩

private def phaseInducedIso
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T) :
    verticalPlateGraph K A ≃g
      (verticalPlateGraph K T).induce {t : T | t.1 ∈ A} where
  toEquiv :=
    { toFun := fun z => ⟨⟨z.1, hAT z.2⟩, z.2⟩
      invFun := fun z => ⟨z.1.1, z.2⟩
      left_inv := fun z => by ext; rfl
      right_inv := fun z => by ext; rfl }
  map_rel_iff' := by
    intro s t
    simp only [SimpleGraph.induce_adj, verticalPlateGraph_adj_iff]
    constructor <;> rintro ⟨hne, hc⟩
    · exact ⟨fun h => hne (by subst t; rfl), hc⟩
    · exact ⟨fun h => hne (by
        apply Subtype.ext
        exact congrArg (fun z : T => z.val) h), hc⟩

private def phasePlateEmbedding
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T) :
    VerticalPlate K A → VerticalPlate K T :=
  fun Q => SimpleGraph.ConnectedComponent.map (phaseInclusionHom K hAT) Q

private theorem phasePlateEmbedding_bijective
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T)
    (hsat : ∀ P : VerticalPlate K T,
      P.centres ⊆ A ∨ Disjoint P.centres A) :
    Function.Bijective (fun Q : VerticalPlate K A =>
      (⟨phasePlateEmbedding K hAT Q, by
        obtain ⟨q, hq⟩ := Q.nonempty_supp
        let P := phasePlateEmbedding K hAT Q
        have hqP : (q.1 : Tiling.Plane) ∈ P.centres := by
          refine ⟨(phaseInclusionHom K hAT) q, ?_, rfl⟩
          unfold P phasePlateEmbedding
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
          have hqeq := (SimpleGraph.ConnectedComponent.mem_supp_iff Q q).mp hq
          calc
            _ = SimpleGraph.ConnectedComponent.map (phaseInclusionHom K hAT)
                ((verticalPlateGraph K A).connectedComponentMk q) := by
                  rw [SimpleGraph.ConnectedComponent.map_mk]
            _ = _ := congrArg _ hqeq
        rcases hsat P with hsub | hdisj
        · exact hsub
        · exact False.elim (Set.disjoint_left.mp hdisj hqP q.2)⟩ :
        {P : VerticalPlate K T // P.centres ⊆ A})) := by
  constructor
  · intro Q R hQR
    apply (phaseInducedIso K hAT).connectedComponentEquiv.injective
    induction Q using SimpleGraph.ConnectedComponent.ind with | _ q => ?_
    induction R using SimpleGraph.ConnectedComponent.ind with | _ r => ?_
    simp only [phasePlateEmbedding, SimpleGraph.ConnectedComponent.map_mk] at hQR ⊢
    have hamb : (verticalPlateGraph K T).Reachable
        ((phaseInclusionHom K hAT) q) ((phaseInclusionHom K hAT) r) :=
      SimpleGraph.ConnectedComponent.exact (congrArg Subtype.val hQR)
    obtain ⟨p⟩ := hamb
    let P : VerticalPlate K T :=
      (verticalPlateGraph K T).connectedComponentMk ((phaseInclusionHom K hAT) q)
    have hPsub : P.centres ⊆ A := by
      rcases hsat P with hsub | hdisj
      · exact hsub
      · exfalso
        apply Set.disjoint_left.mp hdisj
          (VerticalPlate.mem_centres_ofCentre ((phaseInclusionHom K hAT) q)) q.2
    have hpA : ∀ x ∈ p.support, x.1 ∈ A := by
      intro x hx
      apply hPsub
      refine ⟨x, ?_, rfl⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact SimpleGraph.ConnectedComponent.sound
        (walk_support_reachable_from_start (x := x) p hx).symm
    exact SimpleGraph.ConnectedComponent.sound
      ((p.induce {t : T | t.1 ∈ A} hpA).reachable)
  · rintro ⟨P, hPsub⟩
    obtain ⟨t, ht⟩ := P.nonempty_supp
    let a : A := ⟨t.1, hPsub ⟨t, ht, rfl⟩⟩
    refine ⟨(verticalPlateGraph K A).connectedComponentMk a, ?_⟩
    apply Subtype.ext
    simp only [phasePlateEmbedding, SimpleGraph.ConnectedComponent.map_mk]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff P t).mp ht

private def phasePlateEquiv
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T)
    (hsat : ∀ P : VerticalPlate K T,
      P.centres ⊆ A ∨ Disjoint P.centres A) :
    VerticalPlate K A ≃ {P : VerticalPlate K T // P.centres ⊆ A} :=
  Equiv.ofBijective _ (phasePlateEmbedding_bijective K hAT hsat)

private theorem phasePlateEmbedding_centres
    (K : Region) {T A : Set Tiling.Plane} (hAT : A ⊆ T)
    (hsat : ∀ P : VerticalPlate K T,
      P.centres ⊆ A ∨ Disjoint P.centres A)
    (Q : VerticalPlate K A) :
    (phasePlateEmbedding K hAT Q).centres = Q.centres := by
  obtain ⟨q, hq⟩ := Q.nonempty_supp
  have hqP : (q.1 : Tiling.Plane) ∈ (phasePlateEmbedding K hAT Q).centres := by
    refine ⟨(phaseInclusionHom K hAT) q, ?_, rfl⟩
    change (phaseInclusionHom K hAT) q ∈
      (show (verticalPlateGraph K T).ConnectedComponent from
        phasePlateEmbedding K hAT Q).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hqeq : (verticalPlateGraph K A).connectedComponentMk q = Q :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff Q q).mp hq
    calc
      _ = SimpleGraph.ConnectedComponent.map (phaseInclusionHom K hAT)
          ((verticalPlateGraph K A).connectedComponentMk q) := by
            rw [SimpleGraph.ConnectedComponent.map_mk]
      _ = _ := congrArg _ hqeq
  have hPsub : (phasePlateEmbedding K hAT Q).centres ⊆ A := by
    rcases hsat (phasePlateEmbedding K hAT Q) with hsub | hdisj
    · exact hsub
    · exact False.elim (Set.disjoint_left.mp hdisj hqP q.2)
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    let a : A := ⟨t.1, hPsub ⟨t, ht, rfl⟩⟩
    refine ⟨a, ?_, rfl⟩
    change a ∈ (show (verticalPlateGraph K A).ConnectedComponent from Q).supp
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    have htP : (verticalPlateGraph K T).connectedComponentMk t =
        (show (verticalPlateGraph K T).ConnectedComponent from
          phasePlateEmbedding K hAT Q) := by
      change t ∈ (show (verticalPlateGraph K T).ConnectedComponent from
        phasePlateEmbedding K hAT Q).supp at ht
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff _ t).mp ht
    have hqeq : (verticalPlateGraph K A).connectedComponentMk q =
        (show (verticalPlateGraph K A).ConnectedComponent from Q) :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ q).mp hq
    have hamb : (verticalPlateGraph K T).Reachable
        ((phaseInclusionHom K hAT) a) ((phaseInclusionHom K hAT) q) := by
      apply SimpleGraph.ConnectedComponent.exact
      have hat : (phaseInclusionHom K hAT) a = t := Subtype.ext rfl
      rw [hat, htP, ← hqeq]
      exact SimpleGraph.ConnectedComponent.map_mk (phaseInclusionHom K hAT) q
    obtain ⟨p⟩ := hamb
    have hpA : ∀ x ∈ p.support, x.1 ∈ A := by
      intro x hx
      apply hPsub
      refine ⟨x, ?_, rfl⟩
      change x ∈ (show (verticalPlateGraph K T).ConnectedComponent from
        phasePlateEmbedding K hAT Q).supp
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [← htP]
      exact SimpleGraph.ConnectedComponent.sound
        (walk_support_reachable_from_start (x := x) p hx).symm
    have pA := (p.induce {x : T | x.1 ∈ A} hpA).map
      (phaseInducedIso K hAT).symm.toHom
    rw [← hqeq]
    simpa [phaseInducedIso, phaseInclusionHom] using
      (SimpleGraph.ConnectedComponent.sound pA.reachable)
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(phaseInclusionHom K hAT) a, ?_, rfl⟩
    induction Q using SimpleGraph.ConnectedComponent.ind with | _ q => ?_
    simp only [phasePlateEmbedding, SimpleGraph.ConnectedComponent.map_mk]
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
    exact SimpleGraph.ConnectedComponent.sound
      ((SimpleGraph.ConnectedComponent.exact ha).map (phaseInclusionHom K hAT))



private theorem normalizedPhasePlateTransport_exists :
  ∀ {K : Region} {T phaseCentres : Set Tiling.Plane} {c : ℝ}
      {normalizedCentres : Set Tiling.Plane},
    phaseCentres ⊆ T →
    (∀ P : VerticalPlate K T,
      P.centres ⊆ phaseCentres ∨ Disjoint P.centres phaseCentres) →
    normalizedCentres = ((-c : ℝ) : ℂ) +ᵥ phaseCentres →
    Nonempty (NormalizedPhasePlateTransport K T phaseCentres c normalizedCentres) := by
  intro K T A c B hAT hsat hB
  let u : Tiling.Plane := ((-c : ℝ) : ℂ)
  have hB' : B = positiveSimilarity 1 u '' A := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul]
    exact hB
  rw [hB'] at hB ⊢
  have hcarrier : K.openCarrier = positiveSimilarity 1 0 '' K.openCarrier := by
    rw [positiveSimilarity_image_eq_vadd_smul, one_smul, zero_vadd]
  let ePhase := phasePlateEquiv K hAT hsat
  let eTrans := verticalPlate_positiveSimilarityEquiv
    (K := K) (R := K) (T := A) (s := 1) (r := 0) (by norm_num) hcarrier u
  let e : {P : VerticalPlate K T // P.centres ⊆ A} ≃
      VerticalPlate K (positiveSimilarity 1 u '' A) :=
    ePhase.symm.trans eTrans
  have hcentres : ∀ P, (e P).centres = u +ᵥ P.1.centres := by
    intro P
    change (eTrans (ePhase.symm P)).centres =
      u +ᵥ P.1.centres
    rw [verticalPlate_positiveSimilarityEquiv_centres_image,
      positiveSimilarity_image_eq_vadd_smul, one_smul]
    congr 1
    rw [← phasePlateEmbedding_centres K hAT hsat (ePhase.symm P)]
    exact congrArg
      (fun Q : {P : VerticalPlate K T // P.centres ⊆ A} => Q.1.centres)
      (ePhase.apply_symm_apply P)
  refine ⟨{
    normalizedCentres_eq := hB
    plateEquiv := e
    centres_eq := ?_
    support_eq := ?_
    column_iff := ?_ }⟩
  · intro P
    exact hcentres P
  · intro P
    change regularSupport K (e P).centres = u +ᵥ regularSupport K P.1.centres
    rw [hcentres P]
    exact regularSupport_vadd K P.1.centres u
  · intro P
    change (∃ x : ℝ, (e P).centres ⊆ {z : Tiling.Plane | z.re = x}) ↔
      ∃ x : ℝ, P.1.centres ⊆ {z : Tiling.Plane | z.re = x}
    rw [hcentres P]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x - u.re, ?_⟩
      intro z hz
      have := hx ⟨z, hz, rfl⟩
      change (u + z).re = x at this
      simp only [Complex.add_re] at this
      change z.re = x - u.re
      linarith
    · rintro ⟨x, hx⟩
      refine ⟨u.re + x, ?_⟩
      rintro z ⟨w, hw, rfl⟩
      change (u + w).re = u.re + x
      have hwx : w.re = x := hx hw
      simp only [Complex.add_re, hwx]


end Tiling.AxisParallel.Terminal





set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel.Continuous
open Tiling.AxisParallel.RationalMesh

private theorem integral_contact_im_difference
    {K : Region} (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {s t : Tiling.Plane} (hcontact : HorizontalProperContact K s t) :
    ∃ n : ℤ, s.im - t.im = n := by
  obtain ⟨v, _, w, _, _, _, hheight, _⟩ :=
    (horizontalProperContact_iff_exists_intrinsicSides K s t).mp hcontact
  obtain ⟨_, nv, hv⟩ := hIntegral v.1 v.2
  obtain ⟨_, nw, hw⟩ := hIntegral w.1 w.2
  have hvim : v.1.im = (nv : ℝ) := by rw [hv]; simp
  have hwim : w.1.im = (nw : ℝ) := by rw [hw]; simp
  refine ⟨nw - nv, ?_⟩
  simp only [Complex.add_im, hvim, hwim] at hheight
  push_cast
  linarith

private theorem integral_walk_im_difference
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    {s t : T} (p : (verticalPlateGraph K T).Walk s t) :
    ∃ n : ℤ, s.1.im - t.1.im = n := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | @cons s u t hsu p ih =>
    obtain ⟨m, hm⟩ := integral_contact_im_difference hIntegral
      ((verticalPlateGraph_adj_iff s u).mp hsu).2
    obtain ⟨n, hn⟩ := ih
    refine ⟨m + n, ?_⟩
    push_cast
    linarith

/-- Integral horizontal sides synchronize imaginary coordinates modulo the integers
throughout each connected plate. -/
private theorem integral_plate_im_difference
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (P : VerticalPlate K T) {s t : Tiling.Plane}
    (hs : s ∈ P.centres) (ht : t ∈ P.centres) :
    ∃ n : ℤ, s.im - t.im = n := by
  obtain ⟨s', hs', rfl⟩ := hs
  obtain ⟨t', ht', rfl⟩ := ht
  have hcomp : (verticalPlateGraph K T).connectedComponentMk s' =
      (verticalPlateGraph K T).connectedComponentMk t' :=
    ((SimpleGraph.ConnectedComponent.mem_supp_iff P s').mp hs').trans
      ((SimpleGraph.ConnectedComponent.mem_supp_iff P t').mp ht').symm
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.eq.mp hcomp
  exact integral_walk_im_difference hIntegral p

/-- One vertical shift per plate puts every centre on the unit lattice. -/
private theorem exists_integral_plate_shift
    {K : Region} {T : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (hFirst : ∀ t ∈ T, ∃ n : ℤ, t.re = n) :
    ∃ shift : VerticalPlate K T → ℝ,
      ∀ t ∈ shiftVerticalPlates K T shift,
        ∃ m n : ℤ, t = (m : ℝ) + (n : ℝ) * Complex.I := by
  classical
  let anchor (P : VerticalPlate K T) : T := P.nonempty_supp.choose
  have hanchor (P : VerticalPlate K T) : (anchor P).1 ∈ P.centres :=
    ⟨anchor P, P.nonempty_supp.choose_spec, rfl⟩
  refine ⟨fun P ↦ -(anchor P).1.im, ?_⟩
  intro t ht
  obtain ⟨P, htP⟩ := Set.mem_iUnion.mp ht
  obtain ⟨s, hs, rfl⟩ := htP
  obtain ⟨s', _, rfl⟩ := hs
  obtain ⟨m, hm⟩ := hFirst s'.1 s'.2
  obtain ⟨n, hn⟩ := integral_plate_im_difference hIntegral P
    (show s'.1 ∈ P.centres from ⟨s', by assumption, rfl⟩) (hanchor P)
  refine ⟨m, n, ?_⟩
  apply Complex.ext
  · simpa using hm
  · simpa [sub_eq_add_neg, add_comm] using hn

/-- Independent vertical shifts give a bijection of centres whenever the plate
supports are disjoint vertical cylinders. -/
private theorem plate_shift_bijective
    {K : Region} {T : Set Tiling.Plane}
    (shift : VerticalPlate K T → ℝ)
    (hslab : ∀ P : VerticalPlate K T, P.support = Complex.re ⁻¹' P.base)
    (hdisj : ∀ P Q : VerticalPlate K T, P ≠ Q → Disjoint P.support Q.support) :
    Function.Bijective (fun t : T ↦
      (⟨((shift (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I + t.1,
        Set.mem_iUnion.mpr ⟨VerticalPlate.ofCentre t, t.1,
          VerticalPlate.mem_centres_ofCentre t, rfl⟩⟩ :
        shiftVerticalPlates K T shift)) := by
  let f (t : T) : shiftVerticalPlates K T shift :=
    ⟨((shift (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I + t.1,
      Set.mem_iUnion.mpr ⟨VerticalPlate.ofCentre t, t.1,
        VerticalPlate.mem_centres_ofCentre t, rfl⟩⟩
  change Function.Bijective f
  have hplaced {P : VerticalPlate K T} {s : Tiling.Plane}
      (hs : s ∈ P.centres) {x : Tiling.Plane} (hx : x ∈ K.openCarrier) :
      ((shift P : ℝ) : ℂ) * Complex.I + s + x ∈ P.support := by
    have hraw : s + x ∈ P.support := by
      apply (isOpen_iUnion fun t : P.centres ↦
        K.openCarrier_regularOpen.1.vadd t.1).subset_interior_closure
      exact Set.mem_iUnion.mpr ⟨⟨s, hs⟩, x, hx, rfl⟩
    rw [hslab P] at hraw ⊢
    simpa using hraw
  constructor
  · intro s t hst
    have hval : ((shift (VerticalPlate.ofCentre s) : ℝ) : ℂ) * Complex.I + s.1 =
        ((shift (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I + t.1 :=
      congrArg Subtype.val hst
    have hP : VerticalPlate.ofCentre (K := K) s = VerticalPlate.ofCentre t := by
      by_contra hne
      obtain ⟨x, hx⟩ := K.isPolygonal.interior_nonempty K.nonempty
      have hs := hplaced (VerticalPlate.mem_centres_ofCentre s) hx
      have ht := hplaced (VerticalPlate.mem_centres_ofCentre t) hx
      rw [hval] at hs
      exact Set.disjoint_left.mp (hdisj _ _ hne) hs ht
    apply Subtype.ext
    rw [hP] at hval
    exact add_left_cancel hval
  · intro y
    obtain ⟨P, hy⟩ := Set.mem_iUnion.mp y.2
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨s, hs, rfl⟩ := ht
    have hsP : VerticalPlate.ofCentre s = P :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff P s).mp hs
    refine ⟨s, Subtype.ext ?_⟩
    change ((shift (VerticalPlate.ofCentre s) : ℝ) : ℂ) * Complex.I + s.1 = y.1
    rw [hsP]
    exact hty

/-- At unit scale, the historical rational mesh embedding is the integer embedding. -/
private theorem rationalScale_one_eq_integerPoint :
    rationalScale 1 = Tiling.RationalPolygonal.integerPoint := by
  funext q
  apply Complex.ext <;> norm_num [rationalScale, Tiling.RationalPolygonal.integerPoint]

private theorem integral_set_on_unitMesh {S : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ S, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) : OnRationalMesh 1 S := by
  intro v hv
  obtain ⟨m, n, rfl⟩ := hIntegral v hv
  refine ⟨![m, n], ?_⟩
  apply Complex.ext <;> norm_num [rationalScale]

private theorem integerImage_of_integral {S : Set Tiling.Plane}
    (hIntegral : ∀ v ∈ S, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    Tiling.RationalPolygonal.integerPoint ''
      {q | Tiling.RationalPolygonal.integerPoint q ∈ S} = S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    exact hq
  · intro v hv
    obtain ⟨m, n, rfl⟩ := hIntegral v hv
    have hpoint : Tiling.RationalPolygonal.integerPoint ![m, n] =
        (m : ℝ) + (n : ℝ) * Complex.I := by
      apply Complex.ext <;> simp [Tiling.RationalPolygonal.integerPoint]
    refine ⟨![m, n], ?_, hpoint⟩
    change Tiling.RationalPolygonal.integerPoint ![m, n] ∈ S
    rwa [hpoint]

private theorem unitRaster_verticalCarrier_eq (base : Set ℝ) :
    rasterCells 1 (Complex.re ⁻¹' base) =
      Tiling.AxisParallel.Discrete.verticalDiscreteCylinder
        {n : ℤ | Set.Ioo (n : ℝ) ((n : ℝ) + 1) ⊆ base} := by
  ext q
  constructor
  · intro hq
    refine Set.mem_iUnion.mpr ⟨⟨q 0, ?_⟩, ?_⟩
    · intro x hx
      apply hq (show Complex.mk x ((q 1 : ℝ) + 1 / 2) ∈ meshCell 1 q from ?_)
      norm_num [meshCell, rationalScale]
      exact hx
    · rw [Tiling.AxisParallel.Discrete.mem_verticalDiscreteFibre_iff]
      rfl
  · intro hq
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hq
    have hq0 : q 0 = n.1 :=
      (Tiling.AxisParallel.Discrete.mem_verticalDiscreteFibre_iff q n.1).mp hn
    intro x hx
    apply n.2
    norm_num [meshCell, rationalScale] at hx
    simpa [hq0] using And.intro hx.1 hx.2.1

/-- Exact unit rasterization of an integral-centre tiling of a vertical carrier. -/
private theorem exists_integral_carrier_raster
    {K : Region} {S : Set Tiling.Plane} (base : Set ℝ)
    (hopen : IsOpen base) (hregular : interior (closure base) = base)
    (htile : TilesOn K S (Complex.re ⁻¹' base))
    (hK : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (hS : ∀ v ∈ S, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    ∃ F : Finset TranslationalTilings.Plane,
      F.Nonempty ∧ (F : Set TranslationalTilings.Plane) = rasterCells 1 K.openCarrier ∧
      TranslationalTilings.Tiles F
        {q | Tiling.RationalPolygonal.integerPoint q ∈ S}
        (Tiling.AxisParallel.Discrete.verticalDiscreteCylinder
          {n : ℤ | Set.Ioo (n : ℝ) ((n : ℝ) + 1) ⊆ base}) := by
  let A := {q | Tiling.RationalPolygonal.integerPoint q ∈ S}
  have himage : rationalScale 1 '' A = S := by
    rw [rationalScale_one_eq_integerPoint]
    exact integerImage_of_integral hS
  have hEopen := hopen.preimage Complex.continuous_re
  have hEregular : interior (closure (Complex.re ⁻¹' base)) =
      Complex.re ⁻¹' base := by
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hregular]
  have hEraster := target_eq_regularizedRaster (by decide : 0 < 1)
    (integral_set_on_unitMesh hK) (integral_set_on_unitMesh hS) hEopen hEregular htile
  obtain ⟨F, hFne, hF, hiff⟩ := tilesOn_rationalScale_image_iff_raster
    (A := A) (by decide : 0 < 1) (integral_set_on_unitMesh hK)
    hEopen hEregular hEraster
  refine ⟨F, hFne, hF, ?_⟩
  rw [← unitRaster_verticalCarrier_eq]
  apply hiff.mp
  rwa [himage]

/-- The ordinary connected-component equivalence of a graph isomorphism already
provides the exact native plate membership bridge. -/
private theorem graphIso_plate_mem
    {K : Region} {T : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (e : Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃g verticalPlateGraph K T)
    (P : Tiling.RationalPolygonal.QuakePlate F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit) (z : A) :
    z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P ↔
      (e z).1 ∈ VerticalPlate.centres (e.connectedComponentEquiv P : VerticalPlate K T) := by
  have hleft : z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P ↔ z ∈ P.supp := by
    constructor
    · rintro ⟨hz, hp⟩
      exact hp
    · intro hz
      exact ⟨z.2, hz⟩
  have hright : (e z).1 ∈ VerticalPlate.centres (e.connectedComponentEquiv P : VerticalPlate K T) ↔
      e z ∈ (e.connectedComponentEquiv P).supp := by
    constructor
    · rintro ⟨t, ht, heq⟩
      have htEq : t = e z := Subtype.ext heq
      rwa [htEq] at ht
    · intro hz
      exact ⟨e z, hz, rfl⟩
  rw [hleft, hright, SimpleGraph.ConnectedComponent.mem_supp_iff,
    SimpleGraph.ConnectedComponent.mem_supp_iff]
  exact SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.symm

private theorem relativeRasterSupport_eq_unit_regularized (S : Set TranslationalTilings.Plane) :
    relativeRasterSupport S = regularizedCellUnion 1 S := by
  unfold relativeRasterSupport regularizedCellUnion
  apply congrArg interior
  apply congrArg closure
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨q, hq, h0, h1, h2, h3⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    simpa [meshCell, rationalScale] using And.intro h0 (And.intro h1 (And.intro h2 h3))
  · rintro ⟨q, hq⟩
    refine ⟨q.1, q.2, ?_⟩
    simpa [meshCell, rationalScale] using hq

/-- Convert the within-plate/cross-plate contact facts to the canonical shift map. -/
private theorem canonical_plate_shift_contact
    {K : Region} {T : Set Tiling.Plane} (shift : VerticalPlate K T → ℝ)
    (hsame : ∀ (P : VerticalPlate K T) (s t : P.centres),
      HorizontalProperContact K (((shift P : ℝ) : ℂ) * Complex.I + s.1)
          (((shift P : ℝ) : ℂ) * Complex.I + t.1) ↔ HorizontalProperContact K s.1 t.1)
    (hcross : ∀ (P Q : VerticalPlate K T), P ≠ Q →
      ∀ (s : P.centres) (t : Q.centres),
        ¬ HorizontalProperContact K (((shift P : ℝ) : ℂ) * Complex.I + s.1)
          (((shift Q : ℝ) : ℂ) * Complex.I + t.1)) (s t : T) :
    HorizontalProperContact K
        (((shift (VerticalPlate.ofCentre s) : ℝ) : ℂ) * Complex.I + s.1)
        (((shift (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I + t.1) ↔
      HorizontalProperContact K s.1 t.1 := by
  by_cases hP : VerticalPlate.ofCentre (K := K) s = VerticalPlate.ofCentre t
  · have ht : t.1 ∈ (VerticalPlate.ofCentre (K := K) s).centres := by
      rw [hP]
      exact VerticalPlate.mem_centres_ofCentre t
    rw [← hP]
    exact hsame _ ⟨s.1, VerticalPlate.mem_centres_ofCentre s⟩ ⟨t.1, ht⟩
  · constructor
    · intro hcontact
      exact False.elim (hcross _ _ hP ⟨s.1, VerticalPlate.mem_centres_ofCentre s⟩
        ⟨t.1, VerticalPlate.mem_centres_ofCentre t⟩ hcontact)
    · intro hcontact
      by_cases hst : s = t
      · exact False.elim (hP (congrArg (VerticalPlate.ofCentre (K := K)) hst))
      · exact False.elim (hP (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          ((verticalPlateGraph_adj_iff s t).mpr ⟨hst, hcontact⟩)))

private theorem graphIso_plate_integerCentres
    {K : Region} {T : Set Tiling.Plane}
    {F : Finset TranslationalTilings.Plane} {A : Set TranslationalTilings.Plane}
    (e : Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃g verticalPlateGraph K T)
    (shift : VerticalPlate K T → ℝ)
    (hcentre : ∀ z : A, Tiling.RationalPolygonal.integerPoint z.1 =
      ((shift (VerticalPlate.ofCentre (e z)) : ℝ) : ℂ) * Complex.I + (e z).1)
    (P : Tiling.RationalPolygonal.QuakePlate F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit) :
    Tiling.RationalPolygonal.integerPoint ''
      Tiling.RationalPolygonal.quakePlateTranslations P =
      ((shift (e.connectedComponentEquiv P) : ℝ) : ℂ) * Complex.I +ᵥ
        VerticalPlate.centres (e.connectedComponentEquiv P : VerticalPlate K T) := by
  let Q : VerticalPlate K T := e.connectedComponentEquiv P
  have hof {z : A} (hz : z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P) :
      VerticalPlate.ofCentre (e z) = Q := by
    have hmem := (graphIso_plate_mem e P z).mp hz
    obtain ⟨t, ht, heq⟩ := hmem
    have htz : t = e z := Subtype.ext heq
    rw [htz] at ht
    exact ht
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    let zz : A := ⟨z, hz.choose⟩
    refine ⟨(e zz).1, (graphIso_plate_mem e P zz).mp hz, ?_⟩
    change ((shift Q : ℝ) : ℂ) * Complex.I + (e zz).1 =
      Tiling.RationalPolygonal.integerPoint zz.1
    rw [hcentre zz, hof hz]
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨t, ht, rfl⟩ := hy
    let z : A := e.symm t
    have hez : e z = t := e.apply_symm_apply t
    have hz : z.1 ∈ Tiling.RationalPolygonal.quakePlateTranslations P := by
      apply (graphIso_plate_mem e P z).mpr
      rw [hez]
      exact ⟨t, ht, rfl⟩
    refine ⟨z.1, hz, ?_⟩
    rw [hcentre z, hof hz, hez]
    exact hxy

private theorem unitRaster_plate_support_bridge
    {K : Region} {T : Set Tiling.Plane} {F : Finset TranslationalTilings.Plane}
    (hmesh : OnRationalMesh 1 K.vertices)
    (hF : (F : Set TranslationalTilings.Plane) = rasterCells 1 K.openCarrier)
    (S : Set TranslationalTilings.Plane) (P : VerticalPlate K T) (r : ℝ)
    (hcentres : Tiling.RationalPolygonal.integerPoint '' S =
      (r : ℂ) * Complex.I +ᵥ P.centres)
    (hslab : P.support = Complex.re ⁻¹' P.base) :
    relativeRasterSupport (Tiling.RationalPolygonal.discreteCarrier F S) = P.support := by
  rw [relativeRasterSupport_eq_unit_regularized,
    ← regularSupport_rationalScale_image (by decide : 0 < 1) hmesh F hF S,
    rationalScale_one_eq_integerPoint, hcentres, regularSupport_vadd]
  change (r : ℂ) * Complex.I +ᵥ P.support = P.support
  rw [hslab]
  ext z
  simp [Set.mem_vadd_set_iff_neg_vadd_mem]

end Tiling.AxisParallel.Terminal



set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Set
open scoped Topology ComplexOrder

noncomputable section

namespace Tiling.AxisParallel.RationalMesh

private theorem meshCell_disjoint_regularizedCellUnion_of_not_mem {d : ℕ} (hd : 0 < d)
    (F : Set ZPlane) (q : ZPlane) (hq : q ∉ F) :
    Disjoint (meshCell d q) (regularizedCellUnion d F) := by
  have hraw : Disjoint (meshCell d q) (⋃ z : F, meshCell d z.1) := by
    rw [Set.disjoint_iUnion_right]
    intro z
    exact meshCell_pairwiseDisjoint hd (Set.mem_univ q) (Set.mem_univ z.1)
      (fun h => hq (h ▸ z.property))
  exact (hraw.closure_right (isOpen_meshCell d q)).mono_right interior_subset

private theorem unit_meshCell_closure (q : ZPlane) :
    closure (meshCell 1 q) =
      Complex.reProdIm (Icc (q 0 : ℝ) ((q 0 : ℝ) + 1))
        (Icc (q 1 : ℝ) ((q 1 : ℝ) + 1)) := by
  have hcell : meshCell 1 q =
      Complex.reProdIm (Ioo (q 0 : ℝ) ((q 0 : ℝ) + 1))
        (Ioo (q 1 : ℝ) ((q 1 : ℝ) + 1)) := by
    ext z
    simp [meshCell, rationalScale, Complex.reProdIm, and_assoc]
  rw [hcell, Complex.closure_reProdIm, closure_Ioo (by linarith :
    (q 0 : ℝ) ≠ (q 0 : ℝ) + 1), closure_Ioo (by linarith :
      (q 1 : ℝ) ≠ (q 1 : ℝ) + 1)]

private theorem mem_frontier_of_adjacent_closures {U V S : Set Tiling.Plane}
    (hU : U ⊆ S) (hV : Disjoint V S) {z : Tiling.Plane}
    (hzU : z ∈ closure U) (hzV : z ∈ closure V) : z ∈ frontier S := by
  refine ⟨closure_mono hU hzU, ?_⟩
  exact Set.disjoint_left.mp
    ((hV.mono_right interior_subset).closure_left isOpen_interior) hzV

/-- The common open horizontal edge of selected and unselected vertical neighbors is boundary. -/
private theorem unit_horizontal_edge_mem_frontier {F : Set ZPlane} {q r : ZPlane}
    (hq : q ∈ F) (hr : r ∉ F) (hr0 : r 0 = q 0) (hr1 : r 1 = q 1 + 1)
    {x : ℝ} (hx0 : (q 0 : ℝ) < x) (hx1 : x < (q 0 : ℝ) + 1) :
    Complex.mk x ((q 1 : ℝ) + 1) ∈ frontier (regularizedCellUnion 1 F) := by
  apply mem_frontier_of_adjacent_closures
    ((meshCell_subset_regularizedCellUnion_iff (by decide) F q).mpr hq)
    (meshCell_disjoint_regularizedCellUnion_of_not_mem (by decide) F r hr)
  · rw [unit_meshCell_closure]
    exact ⟨⟨hx0.le, hx1.le⟩, ⟨by dsimp; linarith, le_rfl⟩⟩
  · rw [unit_meshCell_closure]
    change ((r 0 : ℝ) ≤ x ∧ x ≤ (r 0 : ℝ) + 1) ∧
      ((r 1 : ℝ) ≤ (q 1 : ℝ) + 1 ∧ (q 1 : ℝ) + 1 ≤ (r 1 : ℝ) + 1)
    simp only [hr0, hr1, Int.cast_add, Int.cast_one]
    exact ⟨⟨hx0.le, hx1.le⟩, ⟨le_rfl, by linarith⟩⟩

private theorem unit_horizontal_edge_mem_frontier_of_upper_selected {F : Set ZPlane}
    {q r : ZPlane} (hq : q ∉ F) (hr : r ∈ F)
    (hr0 : r 0 = q 0) (hr1 : r 1 = q 1 + 1)
    {x : ℝ} (hx0 : (q 0 : ℝ) < x) (hx1 : x < (q 0 : ℝ) + 1) :
    Complex.mk x ((q 1 : ℝ) + 1) ∈ frontier (regularizedCellUnion 1 F) := by
  apply mem_frontier_of_adjacent_closures
    ((meshCell_subset_regularizedCellUnion_iff (by decide) F r).mpr hr)
    (meshCell_disjoint_regularizedCellUnion_of_not_mem (by decide) F q hq)
  · rw [unit_meshCell_closure]
    change ((r 0 : ℝ) ≤ x ∧ x ≤ (r 0 : ℝ) + 1) ∧
      ((r 1 : ℝ) ≤ (q 1 : ℝ) + 1 ∧ (q 1 : ℝ) + 1 ≤ (r 1 : ℝ) + 1)
    simp only [hr0, hr1, Int.cast_add, Int.cast_one]
    exact ⟨⟨hx0.le, hx1.le⟩, ⟨le_rfl, by linarith⟩⟩
  · rw [unit_meshCell_closure]
    exact ⟨⟨hx0.le, hx1.le⟩, ⟨by dsimp; linarith, le_rfl⟩⟩

end Tiling.AxisParallel.RationalMesh






set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

open Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal.UnitContact

open Tiling.AxisParallel Tiling.AxisParallel.RationalMesh
open Tiling.AxisParallel.Continuous

private theorem unitMeshCell_closure (q : ZPlane) :
    closure (meshCell 1 q) =
      {p : Tiling.Plane | (q 0 : ℝ) ≤ p.re ∧ p.re ≤ (q 0 : ℝ) + 1 ∧
        (q 1 : ℝ) ≤ p.im ∧ p.im ≤ (q 1 : ℝ) + 1} := by
  rw [unit_meshCell_closure]
  ext p
  simp only [Complex.mem_reProdIm, mem_Icc, mem_ofPred_eq, and_assoc]

private theorem unitRaster_support_owner {K : Region} {F : Finset ZPlane}
    (hreg : K.openCarrier = regularizedCellUnion 1 F)
    {p : Tiling.Plane} (hp : p ∈ K.support) :
    ∃ q ∈ F, p ∈ closure (meshCell 1 q) := by
  have hsupp : K.support ⊆ closure (⋃ q : (F : Set ZPlane), meshCell 1 q.1) := by
    rw [← K.isPolygonal.closure_interior]
    change closure K.openCarrier ⊆ _
    rw [hreg]
    exact closure_minimal interior_subset isClosed_closure
  have howner := hsupp hp
  rw [closure_iUnion_of_finite] at howner
  obtain ⟨q, hq⟩ := mem_iUnion.mp howner
  exact ⟨q.1, q.2, hq⟩

private theorem meshOne_vertex_integral {K : Region}
    (hmesh : OnRationalMesh 1 K.vertices) (v : K.vertices) :
    ∃ n m : ℤ, v.1.re = n ∧ v.1.im = m := by
  obtain ⟨q, hq⟩ := hmesh v.2
  refine ⟨q 0, q 1, ?_, ?_⟩ <;> rw [← hq] <;> simp [rationalScale]

private theorem horizontal_mem_openSegment
    {a b : Tiling.Plane} (hh : a.im = b.im) {x : ℝ}
    (hx : min a.re b.re < x ∧ x < max a.re b.re) :
    Complex.mk x a.im ∈ openSegment ℝ a b := by
  have hxseg : x ∈ openSegment ℝ a.re b.re := by
    rw [openSegment_eq_Ioo' (by
      intro h
      simp [h] at hx
      linarith [hx.1, hx.2] : a.re ≠ b.re)]
    exact hx
  rw [openSegment_eq_image] at hxseg ⊢
  obtain ⟨r, hr, h⟩ := hxseg
  refine ⟨r, hr, ?_⟩
  apply Complex.ext
  · simpa using h
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    change (1 - r) * a.im + r * b.im = a.im
    rw [hh]
    ring

private theorem integralContact_exists_unitEdge {K : Region}
    (hmesh : OnRationalMesh 1 K.vertices) (s t : ZPlane)
    (hcontact : HorizontalProperContact K
      (Tiling.RationalPolygonal.integerPoint s)
      (Tiling.RationalPolygonal.integerPoint t)) :
    ∃ n m : ℤ, ∀ x : ℝ, (n : ℝ) < x → x < (n : ℝ) + 1 →
      Complex.mk x m ∈
        (frontier (Tiling.RationalPolygonal.integerPoint s +ᵥ K.support) ∩
          frontier (Tiling.RationalPolygonal.integerPoint t +ᵥ K.support)) \
          ((Tiling.RationalPolygonal.integerPoint s +ᵥ K.vertices) ∪
            (Tiling.RationalPolygonal.integerPoint t +ᵥ K.vertices)) := by
  obtain ⟨v, v', w, w', hv, hw, him, x, hxv, hxw⟩ :=
    (horizontalProperContact_iff_exists_intrinsicSides K _ _).mp hcontact
  obtain ⟨a, b, hav, hbv⟩ := meshOne_vertex_integral hmesh v
  obtain ⟨a', b', hav', hbv'⟩ := meshOne_vertex_integral hmesh v'
  obtain ⟨c, d, hcw, hdw⟩ := meshOne_vertex_integral hmesh w
  obtain ⟨c', d', hcw', hdw'⟩ := meshOne_vertex_integral hmesh w'
  let n : ℤ := max (min a a' + s 0) (min c c' + t 0)
  let m : ℤ := b + s 1
  have hvlo : (min a a' + s 0 : ℤ) < min a a' + s 0 + 1 := by omega
  have hvl : (min a a' + s 0 : ℤ) < max a a' + s 0 := by
    have hx := hxv
    simp only [hav, hav', Tiling.RationalPolygonal.integerPoint_re,
      ← Int.cast_min, ← Int.cast_max, ← Int.cast_add] at hx
    exact_mod_cast hx.1.trans hx.2
  have hwl : (min c c' + t 0 : ℤ) < max c c' + t 0 := by
    have hx := hxw
    simp only [hcw, hcw', Tiling.RationalPolygonal.integerPoint_re,
      ← Int.cast_min, ← Int.cast_max, ← Int.cast_add] at hx
    exact_mod_cast hx.1.trans hx.2
  have hnhi : n + 1 ≤ max a a' + s 0 ∧ n + 1 ≤ max c c' + t 0 := by
    have hcross₁ : min c c' + t 0 < max a a' + s 0 := by
      have hh := hxw.1.trans hxv.2
      simp only [hav', hav, hcw, hcw', Tiling.RationalPolygonal.integerPoint_re,
        ← Int.cast_min, ← Int.cast_max, ← Int.cast_add] at hh
      exact_mod_cast hh
    have hcross₂ : min a a' + s 0 < max c c' + t 0 := by
      have hh := hxv.1.trans hxw.2
      simp only [hav', hav, hcw, hcw', Tiling.RationalPolygonal.integerPoint_re,
        ← Int.cast_min, ← Int.cast_max, ← Int.cast_add] at hh
      exact_mod_cast hh
    dsimp [n]
    omega
  have hm : (m : ℝ) = (v.1 + Tiling.RationalPolygonal.integerPoint s).im := by
    simp [m, hbv, Tiling.RationalPolygonal.integerPoint]
  refine ⟨n, m, ?_⟩
  intro y hylo hyhi
  have hys : Complex.mk y m - Tiling.RationalPolygonal.integerPoint s ∈
      openSegment ℝ v.1 v'.1 := by
    have hnlo : min a a' + s 0 ≤ n := le_max_left _ _
    have hlo : (min a a' : ℝ) < y - (s 0 : ℝ) := by
      have hh : ((min a a' + s 0 : ℤ) : ℝ) ≤ n := by exact_mod_cast hnlo
      push_cast at hh
      linarith
    have hhi : y - (s 0 : ℝ) < (max a a' : ℝ) := by
      have hh : ((n + 1 : ℤ) : ℝ) ≤ max a a' + s 0 := by exact_mod_cast hnhi.1
      push_cast at hh
      linarith
    have hpoint : Complex.mk y m - Tiling.RationalPolygonal.integerPoint s =
        Complex.mk (y - (s 0 : ℝ)) v.1.im := by
      apply Complex.ext
      · simp [Tiling.RationalPolygonal.integerPoint]
      · simp [m, hbv, Tiling.RationalPolygonal.integerPoint]
    rw [hpoint]
    apply horizontal_mem_openSegment hv.2.1
    simpa [hav, hav', ← Int.cast_min, ← Int.cast_max] using And.intro hlo hhi
  have hyt : Complex.mk y m - Tiling.RationalPolygonal.integerPoint t ∈
      openSegment ℝ w.1 w'.1 := by
    have hnlo : min c c' + t 0 ≤ n := le_max_right _ _
    have hlo : (min c c' : ℝ) < y - (t 0 : ℝ) := by
      have hh : ((min c c' + t 0 : ℤ) : ℝ) ≤ n := by exact_mod_cast hnlo
      push_cast at hh
      linarith
    have hhi : y - (t 0 : ℝ) < (max c c' : ℝ) := by
      have hh : ((n + 1 : ℤ) : ℝ) ≤ max c c' + t 0 := by exact_mod_cast hnhi.2
      push_cast at hh
      linarith
    have hpoint : Complex.mk y m - Tiling.RationalPolygonal.integerPoint t =
        Complex.mk (y - (t 0 : ℝ)) w.1.im := by
      apply Complex.ext
      · simp [Tiling.RationalPolygonal.integerPoint]
      · have hh := him
        simp [Tiling.RationalPolygonal.integerPoint, hbv] at hh
        simp [m, Tiling.RationalPolygonal.integerPoint]
        linarith
    rw [hpoint]
    apply horizontal_mem_openSegment hw.2.1
    simpa [hcw, hcw', ← Int.cast_min, ← Int.cast_max] using And.intro hlo hhi
  have hvs := hv.2.2 hys
  have hwt := hw.2.2 hyt
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [frontier, closure_vadd, interior_vadd]
    simp only [Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    have hh := hvs.1
    change _ ∈ closure K.support ∧ _ ∉ interior K.support at hh
    simpa only [vadd_eq_add, neg_add_eq_sub] using hh
  · rw [frontier, closure_vadd, interior_vadd]
    simp only [Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    have hh := hwt.1
    change _ ∈ closure K.support ∧ _ ∉ interior K.support at hh
    simpa only [vadd_eq_add, neg_add_eq_sub] using hh
  · intro hvertex
    rcases hvertex with hs | ht
    · rw [mem_vadd_set_iff_neg_vadd_mem] at hs
      exact hvs.2 (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using hs)
    · rw [mem_vadd_set_iff_neg_vadd_mem] at ht
      exact hwt.2 (by simpa [vadd_eq_add, sub_eq_add_neg, add_comm] using ht)

private theorem discreteTile_owner_unique {F : Finset ZPlane} {A R : Set ZPlane}
    (htile : TranslationalTilings.Tiles F A R)
    {f g s t : ZPlane} (hf : f ∈ F) (hg : g ∈ F)
    (hs : s ∈ A) (ht : t ∈ A) (heq : f + s = g + t) : s = t := by
  classical
  have hcount := (TranslationalTilings.tilesAtLevel_iff_representation_count
    F A R 1).mp htile (f + s)
  have hcard : (F.filter fun u ↦ f + s - u ∈ A).card ≤ 1 := by
    rw [hcount]
    split_ifs <;> omega
  have hfmem : f ∈ F.filter fun u ↦ f + s - u ∈ A := by
    simpa only [Finset.mem_filter, hf, true_and, add_sub_cancel_left] using hs
  have hgmem : g ∈ F.filter fun u ↦ f + s - u ∈ A := by
    simpa only [Finset.mem_filter, hg, true_and, heq, add_sub_cancel_left] using ht
  have hfg := Finset.card_le_one.mp hcard f hfmem g hgmem
  rw [hfg] at heq
  exact add_left_cancel heq

private theorem midpoint_cell_owner {q s : ZPlane} {n m : ℤ}
    (hp : Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
      Tiling.RationalPolygonal.integerPoint s ∈ closure (meshCell 1 q)) :
    (q + s) 0 = n ∧ ((q + s) 1 = m - 1 ∨ (q + s) 1 = m) := by
  rw [unitMeshCell_closure] at hp
  change (q 0 : ℝ) ≤ (Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
    Tiling.RationalPolygonal.integerPoint s).re ∧
    (Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
    Tiling.RationalPolygonal.integerPoint s).re ≤ (q 0 : ℝ) + 1 ∧
    (q 1 : ℝ) ≤ (Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
    Tiling.RationalPolygonal.integerPoint s).im ∧
    (Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
    Tiling.RationalPolygonal.integerPoint s).im ≤ (q 1 : ℝ) + 1 at hp
  simp only [Tiling.RationalPolygonal.integerPoint, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero, zero_add] at hp
  change q 0 + s 0 = n ∧ (q 1 + s 1 = m - 1 ∨ q 1 + s 1 = m)
  have h₀ : (q 0 + s 0 : ℤ) ≤ n := by
    have hh : ((q 0 + s 0 : ℤ) : ℝ) < ((n + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [hp.1]
    have hi : q 0 + s 0 < n + 1 := by exact_mod_cast hh
    omega
  have h₁ : n ≤ q 0 + s 0 := by
    have hh : (n : ℝ) < ((q 0 + s 0 + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [hp.2.1]
    have hi : n < q 0 + s 0 + 1 := by exact_mod_cast hh
    omega
  have hylo : q 1 + s 1 ≤ m := by
    have hh : ((q 1 + s 1 : ℤ) : ℝ) ≤ m := by
      push_cast
      linarith [hp.2.2.1]
    exact_mod_cast hh
  have hyhi : m ≤ q 1 + s 1 + 1 := by
    have hh : (m : ℝ) ≤ ((q 1 + s 1 + 1 : ℤ) : ℝ) := by
      push_cast
      linarith [hp.2.2.2]
    exact_mod_cast hh
  omega

private theorem horizontalContact_implies_quakeAdj {K : Region} {F : Finset ZPlane}
    {A R : Set ZPlane} (hmesh : OnRationalMesh 1 K.vertices)
    (hreg : K.openCarrier = regularizedCellUnion 1 F)
    (htile : TranslationalTilings.Tiles F A R) (s t : A)
    (hne : s ≠ t)
    (hc : HorizontalProperContact K (Tiling.RationalPolygonal.integerPoint s.1)
      (Tiling.RationalPolygonal.integerPoint t.1)) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Adj s t := by
  obtain ⟨n, m, hedge⟩ := integralContact_exists_unitEdge hmesh s.1 t.1 hc
  have hp := (hedge ((n : ℝ) + 1 / 2) (by linarith) (by linarith)).1
  have hsfront : Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
      Tiling.RationalPolygonal.integerPoint s.1 ∈ frontier K.support := by
    simpa only [frontier, closure_vadd, interior_vadd, Set.mem_sdiff,
      mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hp.1
  have htfront : Complex.mk ((n : ℝ) + 1 / 2) (m : ℝ) -
      Tiling.RationalPolygonal.integerPoint t.1 ∈ frontier K.support := by
    simpa only [frontier, closure_vadd, interior_vadd, Set.mem_sdiff,
      mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hp.2
  obtain ⟨f, hf, hfp⟩ := unitRaster_support_owner hreg
    (by simpa only [K.isPolygonal.isClosed.closure_eq] using hsfront.1)
  obtain ⟨g, hg, hgp⟩ := unitRaster_support_owner hreg
    (by simpa only [K.isPolygonal.isClosed.closure_eq] using htfront.1)
  obtain ⟨hfx, hfy | hfy⟩ := midpoint_cell_owner hfp
  · obtain ⟨hgx, hgy | hgy⟩ := midpoint_cell_owner hgp
    · have hsame : f + s.1 = g + t.1 := by
        funext i
        fin_cases i
        · exact hfx.trans hgx.symm
        · exact hfy.trans hgy.symm
      exact (hne (Subtype.ext (discreteTile_owner_unique htile hf hg s.2 t.2 hsame))).elim
    · rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
      refine ⟨hne, Or.inl ⟨f, hf, g, hg, ?_⟩⟩
      funext i
      fin_cases i
      · simpa [Tiling.AxisParallel.Discrete.verticalDiscreteUnit] using hfx.trans hgx.symm
      · simp only [Pi.add_apply, Tiling.AxisParallel.Discrete.verticalDiscreteUnit]
        change f 1 + s.1 1 + 1 = g 1 + t.1 1
        change f 1 + s.1 1 = m - 1 at hfy
        change g 1 + t.1 1 = m at hgy
        omega
  · obtain ⟨hgx, hgy | hgy⟩ := midpoint_cell_owner hgp
    · rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
      refine ⟨hne, Or.inr ⟨g, hg, f, hf, ?_⟩⟩
      funext i
      fin_cases i
      · simpa [Tiling.AxisParallel.Discrete.verticalDiscreteUnit] using hgx.trans hfx.symm
      · simp only [Pi.add_apply, Tiling.AxisParallel.Discrete.verticalDiscreteUnit]
        change g 1 + t.1 1 + 1 = f 1 + s.1 1
        change g 1 + t.1 1 = m - 1 at hgy
        change f 1 + s.1 1 = m at hfy
        omega
    · have hsame : f + s.1 = g + t.1 := by
        funext i
        fin_cases i
        · exact hfx.trans hgx.symm
        · exact hfy.trans hgy.symm
      exact (hne (Subtype.ext (discreteTile_owner_unique htile hf hg s.2 t.2 hsame))).elim

private theorem horizontalUnitSegment_coordinates {n m : ℤ} {p : Tiling.Plane}
    (hp : p ∈ openSegment ℝ (Complex.mk (n : ℝ) (m : ℝ))
      (Complex.mk ((n : ℝ) + 1) (m : ℝ))) :
    (n : ℝ) < p.re ∧ p.re < (n : ℝ) + 1 ∧ p.im = m := by
  rw [openSegment_eq_image] at hp
  obtain ⟨r, hr, rfl⟩ := hp
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    smul_eq_mul]
  change (n : ℝ) < (1 - r) * (n : ℝ) + r * ((n : ℝ) + 1) ∧
    (1 - r) * (n : ℝ) + r * ((n : ℝ) + 1) < (n : ℝ) + 1 ∧
    (1 - r) * (m : ℝ) + r * (m : ℝ) = (m : ℝ)
  constructor
  · nlinarith [hr.1]
  constructor
  · nlinarith [hr.2]
  · ring

private theorem unitInterval_not_integer {n : ℤ} {x : ℝ}
    (hx0 : (n : ℝ) < x) (hx1 : x < (n : ℝ) + 1) :
    ∀ a : ℤ, x ≠ a := by
  intro a ha
  rw [ha] at hx0 hx1
  have h₀ : n < a := by exact_mod_cast hx0
  have h₁ : a < n + 1 := by exact_mod_cast hx1
  omega

private theorem commonUnitEdge_givesContact {K : Region}
    (hmesh : OnRationalMesh 1 K.vertices) {s t : ZPlane} {n m : ℤ}
    (hedge : ∀ x : ℝ, (n : ℝ) < x → x < (n : ℝ) + 1 →
      Complex.mk x m ∈
        frontier (Tiling.RationalPolygonal.integerPoint s +ᵥ K.support) ∩
          frontier (Tiling.RationalPolygonal.integerPoint t +ᵥ K.support)) :
    HorizontalProperContact K (Tiling.RationalPolygonal.integerPoint s)
      (Tiling.RationalPolygonal.integerPoint t) := by
  refine ⟨Complex.mk (n : ℝ) (m : ℝ), Complex.mk ((n : ℝ) + 1) (m : ℝ),
    ?_, rfl, ?_⟩
  · intro h
    have hh := congrArg Complex.re h
    change (n : ℝ) = (n : ℝ) + 1 at hh
    linarith
  · intro p hp
    obtain ⟨hp0, hp1, hpim⟩ := horizontalUnitSegment_coordinates hp
    have hpdef : p = Complex.mk p.re m := by
      exact Complex.ext rfl hpim
    refine ⟨?_, ?_⟩
    · rw [hpdef]
      exact hedge p.re hp0 hp1
    · intro hvertices
      rcases hvertices with hv | hv
      · obtain ⟨v, hv, hvp⟩ := hv
        obtain ⟨a, b, ha, _hb⟩ := meshOne_vertex_integral hmesh ⟨v, hv⟩
        change v.re = (a : ℝ) at ha
        have hpre : p.re = ((a + s 0 : ℤ) : ℝ) := by
          have hh := congrArg Complex.re hvp
          simpa [vadd_eq_add, ha, Tiling.RationalPolygonal.integerPoint, add_comm] using hh.symm
        exact unitInterval_not_integer hp0 hp1 (a + s 0) hpre
      · obtain ⟨v, hv, hvp⟩ := hv
        obtain ⟨a, b, ha, _hb⟩ := meshOne_vertex_integral hmesh ⟨v, hv⟩
        change v.re = (a : ℝ) at ha
        have hpre : p.re = ((a + t 0 : ℤ) : ℝ) := by
          have hh := congrArg Complex.re hvp
          simpa [vadd_eq_add, ha, Tiling.RationalPolygonal.integerPoint, add_comm] using hh.symm
        exact unitInterval_not_integer hp0 hp1 (a + t 0) hpre

private theorem transfer_implies_horizontalContact {K : Region} {F : Finset ZPlane}
    {A R : Set ZPlane} (hmesh : OnRationalMesh 1 K.vertices)
    (hreg : K.openCarrier = regularizedCellUnion 1 F)
    (htile : TranslationalTilings.Tiles F A R) (s t : A) (hne : s ≠ t)
    (htransfer : Tiling.RationalPolygonal.quakeTransfer F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit s t) :
    HorizontalProperContact K (Tiling.RationalPolygonal.integerPoint s.1)
      (Tiling.RationalPolygonal.integerPoint t.1) := by
  obtain ⟨f, hf, g, hg, heq⟩ := htransfer
  let v : ZPlane := ![0, 1]
  change f + s.1 + v = g + t.1 at heq
  have hupper : f + v ∉ F := by
    intro hfv
    have hsamt : s.1 = t.1 := discreteTile_owner_unique htile hfv hg s.2 t.2
      (by simpa only [add_assoc, add_left_comm, add_comm] using heq)
    exact hne (Subtype.ext hsamt)
  have hlower : g - v ∉ F := by
    intro hgv
    have htsam : t.1 = s.1 := discreteTile_owner_unique htile hgv hf t.2 s.2
      (by
        calc
          g - v + t.1 = (g + t.1) - v := by abel
          _ = (f + s.1 + v) - v := by rw [heq]
          _ = f + s.1 := by abel)
    exact hne (Subtype.ext htsam.symm)
  let n : ℤ := f 0 + s.1 0
  let m : ℤ := f 1 + s.1 1 + 1
  apply commonUnitEdge_givesContact hmesh (n := n) (m := m)
  intro x hx0 hx1
  have heq0 : f 0 + s.1 0 = g 0 + t.1 0 := by
    simpa [v] using congrFun heq 0
  have heq1 : f 1 + s.1 1 + 1 = g 1 + t.1 1 := by
    simpa [v] using congrFun heq 1
  have hxs0 : (f 0 : ℝ) < x - (s.1 0 : ℝ) := by
    dsimp [n] at hx0
    push_cast at hx0
    linarith
  have hxs1 : x - (s.1 0 : ℝ) < (f 0 : ℝ) + 1 := by
    dsimp [n] at hx1
    push_cast at hx1
    linarith
  have hxt0 : ((g - v) 0 : ℝ) < x - (t.1 0 : ℝ) := by
    have hh : (n : ℝ) = (g 0 : ℝ) + (t.1 0 : ℝ) := by exact_mod_cast heq0
    simp only [Pi.sub_apply, v, Matrix.cons_val_zero, sub_zero]
    linarith
  have hxt1 : x - (t.1 0 : ℝ) < ((g - v) 0 : ℝ) + 1 := by
    have hh : (n : ℝ) = (g 0 : ℝ) + (t.1 0 : ℝ) := by exact_mod_cast heq0
    simp only [Pi.sub_apply, v, Matrix.cons_val_zero, sub_zero]
    linarith
  have hsfront : Complex.mk (x - (s.1 0 : ℝ)) ((f 1 : ℝ) + 1) ∈
      frontier K.support := by
    rw [← K.frontier_openCarrier_eq_frontier_support, hreg]
    exact unit_horizontal_edge_mem_frontier hf hupper
      (by simp [v]) (by simp [v]) hxs0 hxs1
  have htfront : Complex.mk (x - (t.1 0 : ℝ)) (((g - v) 1 : ℝ) + 1) ∈
      frontier K.support := by
    rw [← K.frontier_openCarrier_eq_frontier_support, hreg]
    exact unit_horizontal_edge_mem_frontier_of_upper_selected hlower hg
      (by simp [v]) (by simp [v]) hxt0 hxt1
  have hspoint : Complex.mk x m - Tiling.RationalPolygonal.integerPoint s.1 =
      Complex.mk (x - (s.1 0 : ℝ)) ((f 1 : ℝ) + 1) := by
    apply Complex.ext
    · simp [Tiling.RationalPolygonal.integerPoint]
    · simp [m, Tiling.RationalPolygonal.integerPoint]
      ring
  have htpoint : Complex.mk x m - Tiling.RationalPolygonal.integerPoint t.1 =
      Complex.mk (x - (t.1 0 : ℝ)) (((g - v) 1 : ℝ) + 1) := by
    apply Complex.ext
    · simp [Tiling.RationalPolygonal.integerPoint]
    · have hh : (m : ℝ) = (g 1 : ℝ) + (t.1 1 : ℝ) := by exact_mod_cast heq1
      simp [Tiling.RationalPolygonal.integerPoint, v]
      linarith
  constructor
  · rw [frontier, closure_vadd, interior_vadd]
    simp only [Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
      hspoint]
    exact hsfront
  · rw [frontier, closure_vadd, interior_vadd]
    simp only [Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub,
      htpoint]
    exact htfront

private theorem quakeAdj_iff_horizontalContact {K : Region} {F : Finset ZPlane}
    {A R : Set ZPlane} (hmesh : OnRationalMesh 1 K.vertices)
    (hreg : K.openCarrier = regularizedCellUnion 1 F)
    (htile : TranslationalTilings.Tiles F A R) (s t : A) :
    (Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit).Adj s t ↔
      s ≠ t ∧ HorizontalProperContact K (Tiling.RationalPolygonal.integerPoint s.1)
        (Tiling.RationalPolygonal.integerPoint t.1) := by
  constructor
  · rw [Tiling.RationalPolygonal.quakeGraph, SimpleGraph.fromRel_adj]
    rintro ⟨hne, h | h⟩
    · exact ⟨hne, transfer_implies_horizontalContact hmesh hreg htile s t hne h⟩
    · have hh := transfer_implies_horizontalContact hmesh hreg htile t s hne.symm h
      obtain ⟨a, b, hab, him, hseg⟩ := hh
      refine ⟨hne, a, b, hab, him, ?_⟩
      simpa only [inter_comm, union_comm] using hseg
  · rintro ⟨hne, hc⟩
    exact horizontalContact_implies_quakeAdj hmesh hreg htile s t hne hc

end Tiling.AxisParallel.Terminal.UnitContact

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel.Continuous Tiling.AxisParallel.RationalMesh
private theorem integral_base_frontier_locallyFinite {base : Set ℝ}
    (hboundary : ∀ x ∈ frontier base, ∃ n : ℤ, x = n) :
    ∀ a b : ℝ, (frontier base ∩ Icc a b).Finite := by
  intro a b
  apply ((Set.finite_Icc ⌈a⌉ ⌊b⌋).image (fun n : ℤ ↦ (n : ℝ))).subset
  rintro x ⟨hx, hxab⟩
  obtain ⟨n, rfl⟩ := hboundary x hx
  exact ⟨n, ⟨Int.ceil_le.mpr hxab.1, Int.le_floor.mpr hxab.2⟩, rfl⟩

theorem exists_relativePlateIntegerization
    {K : Region} {T : Set Tiling.Plane} (base : Set ℝ)
    (hbase_open : IsOpen base)
    (hbase_regular : interior (closure base) = base)
    (hTile : TilesOn K T (Complex.re ⁻¹' base))
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (hFirstCoordinates : ∀ t ∈ T, ∃ n : ℤ, t.re = n)
    (hBoundaryCoordinates : ∀ x ∈ frontier base, ∃ n : ℤ, x = n) :
    Nonempty (RelativePlateIntegerization K T base) := by
  classical
  obtain ⟨shift, hshiftIntegral⟩ := exists_integral_plate_shift hIntegral hFirstCoordinates
  let S := shiftVerticalPlates K T shift
  let A : Set TranslationalTilings.Plane :=
    {q | Tiling.RationalPolygonal.integerPoint q ∈ S}
  have hboundary := integral_base_frontier_locallyFinite hBoundaryCoordinates
  have hslab := (relativeCarrier_verticalPlates hTile rfl hbase_regular.symm hboundary).1
  let _ : Countable T := hTile.1.to_subtype
  let _ : Countable (VerticalPlate K T) := by
    apply Function.Surjective.countable
      (f := fun t : T ↦ VerticalPlate.ofCentre (K := K) t)
    intro P
    obtain ⟨t, ht⟩ := P.nonempty_supp
    exact ⟨t, ht⟩
  have hdisj : ∀ P Q : VerticalPlate K T, P ≠ Q → Disjoint P.support Q.support := by
    intro P Q hPQ
    exact (regularSupport_pairwiseDisjoint (@VerticalPlate.centres K T)
      (verticalPlateCentres_pairwiseDisjoint K T) (iUnion_verticalPlateCentres K T) hTile).1
        (Set.mem_univ P) (Set.mem_univ Q) hPQ
  have hSTile : TilesOn K S (Complex.re ⁻¹' base) :=
    tilesOn_shiftVerticalPlates hTile rfl hbase_regular.symm hboundary shift
  obtain ⟨F, hFne, hF, hFTile⟩ := exists_integral_carrier_raster base
    hbase_open hbase_regular hSTile hIntegral hshiftIntegral
  have hmesh := integral_set_on_unitMesh hIntegral
  have hKreg : K.openCarrier = regularizedCellUnion 1 F := by
    obtain ⟨G, _, hG, _, hreg⟩ := exists_regionRaster (by decide : 0 < 1) hmesh
    rw [hG.trans hF.symm] at hreg
    exact hreg
  let eShift : T ≃ S := Equiv.ofBijective
    (fun t : T ↦ ⟨((shift (VerticalPlate.ofCentre t) : ℝ) : ℂ) * Complex.I + t.1,
      Set.mem_iUnion.mpr ⟨VerticalPlate.ofCentre t, t.1,
        VerticalPlate.mem_centres_ofCentre t, rfl⟩⟩)
    (plate_shift_bijective shift (fun P ↦ (hslab P).2) hdisj)
  have himage : Tiling.RationalPolygonal.integerPoint '' A = S :=
    integerImage_of_integral hshiftIntegral
  let eInt : A ≃ S := Equiv.ofBijective
    (fun z : A ↦ ⟨Tiling.RationalPolygonal.integerPoint z.1, z.2⟩) (by
      constructor
      · intro z w hzw
        exact Subtype.ext (Tiling.RationalPolygonal.integerPoint_injective
          (congrArg Subtype.val hzw))
      · intro s
        have hs : s.1 ∈ Tiling.RationalPolygonal.integerPoint '' A := by
          rw [himage]
          exact s.2
        obtain ⟨z, hz, hzs⟩ := hs
        exact ⟨⟨z, hz⟩, Subtype.ext hzs⟩)
  let e : A ≃ T := eInt.trans eShift.symm
  have hcentre : ∀ z : A, Tiling.RationalPolygonal.integerPoint z.1 =
      ((shift (VerticalPlate.ofCentre (e z)) : ℝ) : ℂ) * Complex.I + (e z).1 := by
    intro z
    exact (congrArg Subtype.val (eShift.apply_symm_apply (eInt z))).symm
  have hshiftContact := shiftedPlateContact_iff shift (fun P ↦ (hslab P).2) hdisj
  let g : Tiling.RationalPolygonal.quakeGraph F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃g verticalPlateGraph K T :=
    { toEquiv := e
      map_rel_iff' := by
        intro z w
        rw [verticalPlateGraph_adj_iff, UnitContact.quakeAdj_iff_horizontalContact
          hmesh hKreg hFTile z w]
        rw [hcentre z, hcentre w,
          canonical_plate_shift_contact shift hshiftContact.1 hshiftContact.2]
        exact and_congr e.injective.ne_iff Iff.rfl }
  let pEquiv : Tiling.RationalPolygonal.QuakePlate F A
      Tiling.AxisParallel.Discrete.verticalDiscreteUnit ≃ VerticalPlate K T :=
    g.connectedComponentEquiv
  have hcentres : ∀ P, Tiling.RationalPolygonal.integerPoint ''
      Tiling.RationalPolygonal.quakePlateTranslations P =
      ((shift (pEquiv P) : ℝ) : ℂ) * Complex.I +ᵥ (pEquiv P).centres :=
    graphIso_plate_integerCentres g shift hcentre
  refine ⟨{
    shift := shift
    integerTile := F
    integerTile_nonempty := hFne
    integerCentres := A
    integerBase := {n : ℤ | Ioo (n : ℝ) ((n : ℝ) + 1) ⊆ base}
    integerBase_eq := rfl
    shiftedCentres_eq := himage
    integerTiles := hFTile
    graphEquiv := g
    plateEquiv := pEquiv
    plateEquiv_mem := graphIso_plate_mem g
    centre_apply := ?_
    plateCentres := hcentres
    supportBridge := ?_ }⟩
  · intro z
    have hz := hcentre z
    change (e z).1 = -(((shift (VerticalPlate.ofCentre (e z)) : ℝ) : ℂ) * Complex.I) +
      Tiling.RationalPolygonal.integerPoint z.1
    rw [hz]
    abel
  · intro P
    exact unitRaster_plate_support_bridge hmesh hF
      (Tiling.RationalPolygonal.quakePlateTranslations P) (pEquiv P)
      (shift (pEquiv P)) (hcentres P) (hslab (pEquiv P)).2

private theorem normalizedCarrierPhase_integerization
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    {phases : Set ℝ} {phaseBase : ℝ → Set ℝ}
    {phaseCentres : ℝ → Set Tiling.Plane} {c : ℝ}
    (_hPhase : IsCarrierPhaseDecomposition K T X phases phaseBase phaseCentres)
    (_hc : c ∈ phases)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I)
    (N : NormalizedCarrierPhase K T X phases phaseBase phaseCentres c) :
    ∃ I : RelativePlateIntegerization K N.normalizedCentres N.normalizedBase,
      ∀ P, Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P ↔
        IsVerticalColumn (I.plateEquiv P) := by
  obtain ⟨I⟩ := exists_relativePlateIntegerization N.normalizedBase N.base_open
    N.base_regular N.tiles hIntegral N.centres_integral N.boundary_integral
  exact ⟨I, relativePlateEquiv_preservesColumns I⟩

private theorem integerization_columnAggregateSupport
    {K : Region} {T : Set Tiling.Plane} {base : Set ℝ}
    (I : RelativePlateIntegerization K T base) :
    relativeRasterSupport
        (Tiling.RationalPolygonal.discreteCarrier I.integerTile
          (Tiling.AxisParallel.Discrete.discreteColumnUnion
            I.integerTile I.integerCentres)) =
      regularSupport K (verticalColumnCentres K T) := by
  classical
  let C := {P : Tiling.RationalPolygonal.QuakePlate I.integerTile I.integerCentres
    Tiling.AxisParallel.Discrete.verticalDiscreteUnit //
      Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P}
  let A (P : C) := Tiling.RationalPolygonal.discreteCarrier I.integerTile
    (Tiling.RationalPolygonal.quakePlateTranslations P.1)
  have hcarrier : Tiling.RationalPolygonal.discreteCarrier I.integerTile
      (Tiling.AxisParallel.Discrete.discreteColumnUnion
        I.integerTile I.integerCentres) = ⋃ P : C, A P := by
    ext q
    constructor
    · rintro ⟨f, hf, a, ha, rfl⟩
      obtain ⟨P, haP⟩ := Set.mem_iUnion.mp ha
      obtain ⟨hP, haP⟩ := Set.mem_iUnion.mp haP
      exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, f, hf, a, haP, rfl⟩
    · intro hq
      obtain ⟨P, f, hf, a, ha, rfl⟩ := Set.mem_iUnion.mp hq
      exact ⟨f, hf, a, Set.mem_iUnion_of_mem P.1
        (Set.mem_iUnion_of_mem P.2 ha), rfl⟩
  let U (P : C) : Set Tiling.Plane := ⋃ q : A P, meshCell 1 q.1
  have hUopen (P : C) : IsOpen (U P) :=
    isOpen_iUnion fun q ↦ isOpen_meshCell 1 q.1
  have hraw : (⋃ q : (⋃ P : C, A P), meshCell 1 q.1) = ⋃ P : C, U P := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, hzq⟩ := Set.mem_iUnion.mp hz
      obtain ⟨P, hqP⟩ := Set.mem_iUnion.mp q.2
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨⟨q.1, hqP⟩, hzq⟩⟩
    · intro hz
      obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hz
      obtain ⟨q, hzq⟩ := Set.mem_iUnion.mp hzP
      exact Set.mem_iUnion.mpr ⟨⟨q.1, Set.mem_iUnion.mpr ⟨P, q.2⟩⟩, hzq⟩
  have hjoin : relativeRasterSupport (⋃ P : C, A P) =
      interior (closure (⋃ P : C, relativeRasterSupport (A P))) := by
    simp_rw [relativeRasterSupport_eq_unit_regularized, regularizedCellUnion]
    rw [hraw]
    exact interior_closure_iUnion_interior_closure U hUopen
  have hsupports : (⋃ P : C, (I.plateEquiv P.1).support) =
      ⋃ Q : {Q : VerticalPlate K T // IsVerticalColumn Q}, Q.1.support := by
    ext z
    constructor
    · intro hz
      obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨⟨I.plateEquiv P.1,
        (relativePlateEquiv_preservesColumns I P.1).mp P.2⟩, hzP⟩
    · intro hz
      obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hz
      let P := I.plateEquiv.symm Q.1
      have hP : Tiling.AxisParallel.Discrete.IsDiscreteVerticalColumn P := by
        apply (relativePlateEquiv_preservesColumns I P).mpr
        simpa [P] using Q.2
      exact Set.mem_iUnion.mpr ⟨⟨P, hP⟩, by simpa [P] using hzQ⟩
  rw [hcarrier, hjoin]
  have hbridge : (⋃ P : C, relativeRasterSupport (A P)) =
      ⋃ P : C, (I.plateEquiv P.1).support := by
    apply Set.iUnion_congr
    intro P
    exact I.supportBridge P.1
  rw [hbridge, hsupports, verticalColumnCentres_eq, regularSupport_iUnion]
  rfl

private theorem relativeIntegerization_platePeriodicity
    {K : Region} {T : Set Tiling.Plane} {base : Set ℝ}
    (I : RelativePlateIntegerization K T base) {ell : ℕ}
    (hell : 0 < ell) (hbase : (ell : ℝ) +ᵥ base = base) :
    ∃ L : ℕ, 0 < L ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (L : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (L : ℂ) := by
  have hbaseFun : Function.Periodic (fun x : ℝ ↦ x ∈ base) (ell : ℝ) := by
    intro x
    apply propext
    have h := Set.ext_iff.mp hbase (x + (ell : ℝ))
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using h.symm
  have hB : Function.Periodic (fun n : ℤ ↦ n ∈ I.integerBase) (ell : ℤ) := by
    intro n
    apply propext
    rw [I.integerBase_eq]
    constructor
    · intro h x hx
      have hxs : x + (ell : ℝ) ∈ Ioo ((n + ell : ℤ) : ℝ)
          (((n + ell : ℤ) : ℝ) + 1) := by
        push_cast
        constructor <;> linarith [hx.1, hx.2]
      exact (eq_iff_iff.mp (hbaseFun x)).mp (h hxs)
    · intro h x hx
      have hxs : x - (ell : ℝ) ∈ Ioo (n : ℝ) ((n : ℝ) + 1) := by
        push_cast at hx
        constructor <;> linarith [hx.1, hx.2]
      have hh := (eq_iff_iff.mp (hbaseFun (x - (ell : ℝ)))).mpr (h hxs)
      simpa only [sub_add_cancel] using hh
  have hVert : Tiling.RationalPolygonal.DiscretePeriodicBy
      (Discrete.verticalDiscreteCylinder I.integerBase) Discrete.verticalDiscreteUnit := by
    intro z
    simp [Discrete.mem_verticalDiscreteCylinder_iff, Discrete.firstDiscreteCoordinate,
      Discrete.verticalDiscreteUnit, Matrix.vecHead]
  have hScalar : TranslationalTilings.SetScalarPeriodic ell
      (Discrete.verticalDiscreteCylinder I.integerBase) := by
    intro z w
    simp only [Discrete.mem_verticalDiscreteCylinder_iff,
      Discrete.firstDiscreteCoordinate, Pi.add_apply, zsmul_eq_mul]
    have h := hB.int_mul (w 0) (z 0)
    simpa [zsmul_eq_mul, mul_comm] using eq_iff_iff.mp h
  obtain ⟨L, hL, _hdiv, hplates, hcolumns⟩ :=
    Discrete.exists_discretePlatePeriodicity I.integerTile_nonempty hell hVert
      hScalar I.integerTiles
  refine ⟨L, hL, ?_, ?_⟩
  · intro P hP
    let Q := I.plateEquiv.symm P
    have hQ : ¬ Discrete.IsDiscreteVerticalColumn Q := by
      intro hQ
      apply hP
      simpa [Q] using (relativePlateEquiv_preservesColumns I Q).mp hQ
    have h := discretePeriod_liftsContinuous I (hplates Q hQ)
    rw [I.supportBridge Q] at h
    simpa [Q] using h
  · have h := discretePeriod_liftsContinuous I hcolumns
    rw [integerization_columnAggregateSupport I] at h
    exact h

private theorem relativeIntegerBase_finite
    {K : Region} {T : Set Tiling.Plane} {base : Set ℝ}
    (I : RelativePlateIntegerization K T base) (hbase : IsBounded base) :
    I.integerBase.Finite := by
  obtain ⟨a, ha⟩ := hbase.bddBelow
  obtain ⟨b, hb⟩ := hbase.bddAbove
  apply (Set.finite_Icc ⌈a - 1⌉ ⌊b⌋).subset
  intro n hn
  have hcell : Ioo (n : ℝ) ((n : ℝ) + 1) ⊆ base := by
    rw [I.integerBase_eq] at hn
    exact hn
  have hmid : (n : ℝ) + 1 / 2 ∈ base := hcell ⟨by linarith, by linarith⟩
  exact ⟨Int.ceil_le.mpr (by linarith [ha hmid]),
    Int.le_floor.mpr (by linarith [hb hmid])⟩

theorem integralPeriodicCarrierPlate_periodic
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (hIntegral : ∀ v ∈ K.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I) :
    ∃ b : ℝ, 0 < b ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (b : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (b : ℂ) := by
  classical
  by_cases hwhole : X.base = Set.univ
  · have hTileWhole : TilesOn K T Set.univ := by
      simpa [PeriodicVerticalCarrier.carrier, hwhole] using hTile
    obtain ⟨v, hv, _w, _hw, _hmax, _hdiam⟩ :=
      Tiling.AxisParallel.IntrinsicVertices.exists_intrinsicDiameterPair K
    have hrelative : Tiling.RationalPolygonal.IsRelativelyRational K.toPolygonalRegion := by
      refine ⟨v, hv, ?_⟩
      intro w hw
      obtain ⟨m, n, rfl⟩ := hIntegral w hw
      obtain ⟨p, q, rfl⟩ := hIntegral v hv
      refine ⟨(m - p : ℤ), (n - q : ℤ), ?_, ?_⟩ <;> simp
    obtain ⟨b, hb, hcolumns, hplates⟩ :=
      rationalVerticalPlateSupport_periodic hTileWhole hrelative
    exact ⟨b, hb, hplates, hcolumns⟩
  obtain ⟨phases, phaseBase, phaseCentres, hPhase⟩ :=
    carrierPhaseDecomposition X hwhole hTile hIntegral
  rcases carrierPeriod_rationalOrIrrational hwhole hPhase with hrat | hirr
  · obtain ⟨_hrat, hfinite, ell, hell, hperiod⟩ := hrat
    let S (c : ℝ) : Set Tiling.Plane :=
      ⋃ P : {P : VerticalPlate K T //
        P.centres ⊆ phaseCentres c ∧ IsVerticalColumn P}, P.1.centres
    have hphase : ∀ c ∈ phases, ∃ L : ℕ, 0 < L ∧
        (∀ P : VerticalPlate K T, P.centres ⊆ phaseCentres c →
          ¬ IsVerticalColumn P →
          Tiling.RationalPolygonal.SetPeriodicBy P.support (L : ℂ)) ∧
        Tiling.RationalPolygonal.SetPeriodicBy (regularSupport K (S c)) (L : ℂ) := by
      intro c hc
      obtain ⟨N⟩ := normalizedCarrierPhase_exists hPhase c hc
      obtain ⟨I, _hIcolumns⟩ := normalizedCarrierPhase_integerization hPhase hc hIntegral N
      obtain ⟨hsub, hsat⟩ := phaseCentres_plateSaturated hPhase c hc
      obtain ⟨H⟩ := normalizedPhasePlateTransport_exists hsub hsat N.normalizedCentres_eq
      have hNperiod : (ell : ℝ) +ᵥ N.normalizedBase = N.normalizedBase := by
        rw [N.normalizedBase_eq]
        calc
          (ell : ℝ) +ᵥ ((-c) +ᵥ phaseBase c) =
              (-c) +ᵥ ((ell : ℝ) +ᵥ phaseBase c) := by
                simp only [vadd_vadd]
                congr 1
                ring
          _ = (-c) +ᵥ phaseBase c := by rw [hperiod c hc]
      obtain ⟨L, hL, hplates, hcolumns⟩ :=
        relativeIntegerization_platePeriodicity I hell hNperiod
      have hcolCentres : verticalColumnCentres K N.normalizedCentres =
          ((-c : ℝ) : ℂ) +ᵥ S c := by
        rw [verticalColumnCentres_eq]
        ext z
        constructor
        · intro hz
          obtain ⟨Q, hzQ⟩ := Set.mem_iUnion.mp hz
          obtain ⟨P, hPQ⟩ := H.plateEquiv.surjective Q.1
          have hPcol : IsVerticalColumn P.1 := (H.column_iff P).mp (hPQ ▸ Q.2)
          rw [← hPQ, H.centres_eq P] at hzQ
          obtain ⟨t, ht, rfl⟩ := hzQ
          exact ⟨t, Set.mem_iUnion.mpr ⟨⟨P.1, P.2, hPcol⟩, ht⟩, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          obtain ⟨P, htP⟩ := Set.mem_iUnion.mp ht
          let Q := H.plateEquiv ⟨P.1, P.2.1⟩
          refine Set.mem_iUnion.mpr ⟨⟨Q, (H.column_iff ⟨P.1, P.2.1⟩).mpr P.2.2⟩, ?_⟩
          rw [H.centres_eq]
          exact ⟨t, htP, rfl⟩
      refine ⟨L, hL, ?_, ?_⟩
      · intro P hPc hPnon
        let Q := H.plateEquiv ⟨P, hPc⟩
        have hQnon : ¬ IsVerticalColumn Q := fun hQ ↦
          hPnon ((H.column_iff ⟨P, hPc⟩).mp hQ)
        have hQperiod := hplates Q hQnon
        rw [H.support_eq] at hQperiod
        simpa [vadd_vadd] using Tiling.RationalPolygonal.setPeriodicBy_vadd
          (c : ℂ) hQperiod
      · rw [hcolCentres, regularSupport_vadd] at hcolumns
        simpa [vadd_vadd] using Tiling.RationalPolygonal.setPeriodicBy_vadd
          (c : ℂ) hcolumns
    let _ : Fintype phases := hfinite.fintype
    choose L hLpos hLplates hLcolumns using fun c : phases ↦ hphase c.1 c.2
    let M : ℕ := ∏ c : phases, L c
    have hMpos : 0 < M := Finset.prod_pos fun c _ ↦ hLpos c
    have hmultiple (A : Set Tiling.Plane) (c : phases)
        (hA : Tiling.RationalPolygonal.SetPeriodicBy A (L c : ℂ)) :
        Tiling.RationalPolygonal.SetPeriodicBy A (M : ℂ) := by
      have hdiv : L c ∣ M := Finset.dvd_prod_of_mem L (Finset.mem_univ c)
      obtain ⟨m, hm⟩ := hdiv
      have hp : Function.Periodic (fun z : Tiling.Plane ↦ z ∈ A) (L c : ℂ) :=
        fun z ↦ propext (hA z)
      have hcast : (M : ℂ) = m • (L c : ℂ) := by
        rw [hm]
        simp only [Nat.cast_mul, nsmul_eq_mul, mul_comm]
      rw [hcast]
      exact fun z ↦ eq_iff_iff.mp (hp.nsmul m z)
    have hcolumnUnion : (⋃ c : phases, S c.1) = verticalColumnCentres K T := by
      rw [verticalColumnCentres_eq]
      ext z
      constructor
      · intro hz
        obtain ⟨c, hzS⟩ := Set.mem_iUnion.mp hz
        obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hzS
        exact Set.mem_iUnion.mpr ⟨⟨P.1, P.2.2⟩, hzP⟩
      · intro hz
        obtain ⟨P, hzP⟩ := Set.mem_iUnion.mp hz
        obtain ⟨c, ⟨hc, hPc⟩, _hunique⟩ := hPhase.plate_has_unique_phase P.1
        exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩,
          Set.mem_iUnion.mpr ⟨⟨P.1, hPc, P.2⟩, hzP⟩⟩
    refine ⟨(M : ℝ), by exact_mod_cast hMpos, ?_, ?_⟩
    · intro P hPnon
      obtain ⟨c, ⟨hc, hPc⟩, _hunique⟩ := hPhase.plate_has_unique_phase P
      exact hmultiple P.support ⟨c, hc⟩ (hLplates ⟨c, hc⟩ P hPc hPnon)
    · rw [← hcolumnUnion, regularSupport_iUnion]
      apply setPeriodicBy_interior_closure_local
      apply setPeriodicBy_iUnion_local
      intro c
      exact hmultiple (regularSupport K (S c.1)) c (hLcolumns c)
  · obtain ⟨_hirr, hbounded⟩ := hirr
    have hallColumns (P : VerticalPlate K T) : IsVerticalColumn P := by
      obtain ⟨c, ⟨hc, hPc⟩, _hunique⟩ := hPhase.plate_has_unique_phase P
      obtain ⟨N⟩ := normalizedCarrierPhase_exists hPhase c hc
      obtain ⟨I, hIcolumns⟩ := normalizedCarrierPhase_integerization hPhase hc hIntegral N
      obtain ⟨hsub, hsat⟩ := phaseCentres_plateSaturated hPhase c hc
      obtain ⟨H⟩ := normalizedPhasePlateTransport_exists hsub hsat N.normalizedCentres_eq
      have hNbounded : IsBounded N.normalizedBase := by
        rw [N.normalizedBase_eq]
        exact (hbounded c hc).vadd (-c)
      let Q := I.plateEquiv.symm (H.plateEquiv ⟨P, hPc⟩)
      have hQcol := finiteDiscreteCarrier_allColumns I.integerTile_nonempty
        (relativeIntegerBase_finite I hNbounded) I.integerTiles Q
      have hNcol := (hIcolumns Q).mp hQcol
      apply (H.column_iff ⟨P, hPc⟩).mp
      simpa [Q] using hNcol
    have hcolumns : verticalColumnCentres K T = T := by
      rw [verticalColumnCentres_eq]
      apply Set.Subset.antisymm
      · intro z hz
        obtain ⟨P, t, _ht, rfl⟩ := Set.mem_iUnion.mp hz
        exact t.2
      · intro z hz
        let t : T := ⟨z, hz⟩
        exact Set.mem_iUnion.mpr ⟨⟨VerticalPlate.ofCentre t,
          hallColumns (VerticalPlate.ofCentre t)⟩, VerticalPlate.mem_centres_ofCentre t⟩
    refine ⟨X.period, X.period_pos, fun P hP ↦ (hP (hallColumns P)).elim, ?_⟩
    rw [hcolumns, (relativePlate_localFinite X hTile).2.2.2.1]
    intro z
    change z.re + X.period ∈ X.base ↔ z.re ∈ X.base
    have h := Set.ext_iff.mp X.base_periodic (z.re + X.period)
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      add_comm, add_left_comm, add_assoc] using h.symm

private structure RationalHomothetyData
    (K : Region) (T : Set Tiling.Plane)
    (X : PeriodicVerticalCarrier) (q : ℕ) where
  scaledRegion : Region
  scaledCentres : Set Tiling.Plane
  scaledCarrier : PeriodicVerticalCarrier
  q_pos : 0 < q
  scaledCentres_eq : scaledCentres = rationalHomothety q '' T
  scaledCarrier_base : scaledCarrier.base =
    (fun x : ℝ ↦ (q : ℝ) * x) '' X.base
  scaledCarrier_period : scaledCarrier.period = (q : ℝ) * X.period
  openCarrier_eq : scaledRegion.openCarrier =
    rationalHomothety q '' K.openCarrier
  vertices_eq : scaledRegion.vertices =
    rationalHomothety q '' K.vertices
  plateEquiv : VerticalPlate K T ≃ VerticalPlate scaledRegion scaledCentres
  plate_support : ∀ P,
    (plateEquiv P).support = rationalHomothety q '' P.support
  plate_column : ∀ P,
    IsVerticalColumn (plateEquiv P) ↔ IsVerticalColumn P
  columnCentres_eq :
    verticalColumnCentres scaledRegion scaledCentres =
      rationalHomothety q '' verticalColumnCentres K T
  columnSupport_eq :
    regularSupport scaledRegion
        (rationalHomothety q '' verticalColumnCentres K T) =
      rationalHomothety q '' regularSupport K (verticalColumnCentres K T)

private theorem rationalHomothetyData_exists :
    ∀ {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier),
      TilesOn K T X.carrier →
      (∀ v ∈ K.vertices, Tiling.IsRationalPoint v) →
      ∃ q : ℕ, ∃ H : RationalHomothetyData K T X q,
        TilesOn H.scaledRegion H.scaledCentres H.scaledCarrier.carrier ∧
        (∀ v ∈ H.scaledRegion.vertices, ∃ m n : ℤ,
          v = (m : ℝ) + (n : ℝ) * Complex.I) := by
  classical
  intro K T X hTile hRational
  let V : Finset Tiling.Plane := K.vertexFinset
  let coord : Tiling.Plane → ℚ × ℚ := fun v =>
    if hv : v ∈ K.vertices then
      let h := hRational v hv
      (Classical.choose h, Classical.choose (Classical.choose_spec h))
    else (0, 0)
  have hcoord (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (v.re = (coord v).1) ∧ (v.im = (coord v).2) := by
    dsimp [coord]
    rw [dif_pos hv]
    let h := hRational v hv
    exact Classical.choose_spec (Classical.choose_spec h)
  let q : ℕ := ∏ v ∈ V, (coord v).1.den * (coord v).2.den
  have hqpos : 0 < q := by
    dsimp [q]
    exact Finset.prod_pos fun v hv =>
      Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)
  have hvV (v : Tiling.Plane) (hv : v ∈ K.vertices) : v ∈ V := by
    dsimp [V]
    change v ∈ (K.vertexFinset : Set Tiling.Plane)
    rw [K.coe_vertexFinset]
    exact hv
  have hdenRe (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (coord v).1.den ∣ q := by
    dsimp [q]
    exact (dvd_mul_right _ _).trans
      (Finset.dvd_prod_of_mem (fun w => (coord w).1.den * (coord w).2.den)
        (hvV v hv))
  have hdenIm (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      (coord v).2.den ∣ q := by
    dsimp [q]
    apply (dvd_mul_right _ _).trans
    simpa [Nat.mul_comm] using
      (Finset.dvd_prod_of_mem (fun w => (coord w).1.den * (coord w).2.den)
        (hvV v hv))
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  let hx : ℝ ≃ₜ ℝ := Homeomorph.smulOfNeZero (q : ℝ) hqR
  have hmx : StrictMono hx := by
    intro x y hxy
    change (q : ℝ) * x < (q : ℝ) * y
    exact mul_lt_mul_of_pos_left hxy (by exact_mod_cast hqpos)
  obtain ⟨R, _hRsupport, hRopen, hRvertices⟩ :=
    Tiling.AxisParallel.Approximation.exists_coordinateProductImageRegion K hx hx hmx hmx
  have hH (z : Tiling.Plane) :
      Tiling.AxisParallel.Approximation.coordinateProductHomeomorph hx hx z =
        rationalHomothety q z := by
    rw [Tiling.AxisParallel.Approximation.coordinateProductHomeomorph_apply]
    apply Complex.ext <;> simp [hx, rationalHomothety, Complex.mul_re,
      Complex.mul_im]
  have hPoint (z : Tiling.Plane) :
      rationalHomothety q z =
        Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 z := by
    simp [rationalHomothety, Tiling.AxisParallel.positiveSimilarity]
  have hOpen : R.openCarrier =
      Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' K.openCarrier := by
    rw [hRopen]
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, by simpa [Tiling.AxisParallel.positiveSimilarity,
        rationalHomothety] using (hH w).symm⟩
    · rintro ⟨w, hw, hzw⟩
      exact ⟨w, hw, (hH w).trans ((hPoint w).trans hzw)⟩
  have hVertices (v : Tiling.Plane) (hv : v ∈ K.vertices) :
      Tiling.RationalPolygonal.IsIntegerPoint
        (rationalHomothety q v) := by
    rw [Tiling.RationalPolygonal.IsIntegerPoint]
    apply Tiling.RationalPolygonal.mem_integerLattice_iff.mpr
    let z : TranslationalTilings.Plane := fun i =>
      if i = 0 then
        Tiling.RationalPolygonal.Raw.scaledCoordinate q (coord v).1
      else Tiling.RationalPolygonal.Raw.scaledCoordinate q (coord v).2
    refine ⟨z, ?_⟩
    apply Complex.ext
    · rw [Tiling.RationalPolygonal.integerPoint_re]
      simp [z, Tiling.RationalPolygonal.Raw.scaledCoordinate_cast (hdenRe v hv),
        (hcoord v hv).1, rationalHomothety]
    · rw [Tiling.RationalPolygonal.integerPoint_im]
      simp [z, Tiling.RationalPolygonal.Raw.scaledCoordinate_cast (hdenIm v hv),
        (hcoord v hv).2, rationalHomothety]
  let X' : PeriodicVerticalCarrier := {
    base := (fun x : ℝ => (q : ℝ) * x) '' X.base
    base_open := by
      change IsOpen (hx '' X.base)
      exact hx.isOpenMap _ X.base_open
    base_regular := by
      change interior (closure (hx '' X.base)) = hx '' X.base
      rw [← hx.image_closure, ← hx.image_interior, X.base_regular]
    base_nonnull := by
      have hXne : X.base.Nonempty := by
        by_contra hne
        have hempty : X.base = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
        apply X.base_nonnull
        simp [hempty]
      have hX'ne : (hx '' X.base).Nonempty := hXne.image hx
      have hX'open : IsOpen (hx '' X.base) := hx.isOpenMap _ X.base_open
      exact hX'open.measure_ne_zero MeasureTheory.volume hX'ne
    period := (q : ℝ) * X.period
    period_pos := mul_pos hqRpos X.period_pos
    base_periodic := by
      have hscale :
          (fun x : ℝ => (q : ℝ) * x) '' (X.period +ᵥ X.base) =
            ((q : ℝ) * X.period) +ᵥ
              ((fun x : ℝ => (q : ℝ) * x) '' X.base) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          rcases Set.mem_vadd_set.mp hx with ⟨a, ha, rfl⟩
          refine Set.mem_vadd_set.mpr ⟨(q : ℝ) * a, ⟨a, ha, rfl⟩, ?_⟩
          simp only [vadd_eq_add]
          ring
        · rintro hy
          rcases Set.mem_vadd_set.mp hy with ⟨a, ha, rfl⟩
          rcases ha with ⟨b, hb, rfl⟩
          refine ⟨X.period + b, Set.mem_vadd_set.mpr ⟨b, hb, rfl⟩, ?_⟩
          simp only [vadd_eq_add]
          ring
      calc
        ((q : ℝ) * X.period) +ᵥ
            ((fun x : ℝ => (q : ℝ) * x) '' X.base) =
          (fun x : ℝ => (q : ℝ) * x) '' (X.period +ᵥ X.base) := hscale.symm
        _ = (fun x : ℝ => (q : ℝ) * x) '' X.base := by
          rw [X.base_periodic] }
  have hCarrier : X'.carrier =
      Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' X.carrier := by
    ext z
    change z.re ∈ (fun x : ℝ => (q : ℝ) * x) '' X.base ↔
      z ∈ Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 ''
        (Complex.re ⁻¹' X.base)
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · intro hz
      rcases hz with ⟨x, hx, hxz⟩
      let w : Tiling.Plane := x + (z.im / (q : ℝ)) * Complex.I
      have hw : w ∈ Complex.re ⁻¹' X.base := by
        change w.re ∈ X.base
        simpa [w] using hx
      have hwz : Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 w = z := by
        apply Complex.ext
        · simp [w, Tiling.AxisParallel.positiveSimilarity, hxz]
        · simp [w, Tiling.AxisParallel.positiveSimilarity]
          field_simp [hqR]
      exact ⟨w, hw, hwz⟩
    · rintro ⟨w, hw, hzw⟩
      have hwre : (q : ℝ) * w.re = z.re := by
        simpa [Tiling.AxisParallel.positiveSimilarity, Complex.real_smul] using
          congrArg Complex.re hzw
      exact ⟨w.re, hw, hwre⟩
  have hImage (A : Set Tiling.Plane) :
      Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' A =
        rationalHomothety q '' A := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, hPoint w⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hPoint w).symm⟩
  let e₀ := Tiling.AxisParallel.Continuous.verticalPlate_positiveSimilarityEquiv
    hqRpos hOpen 0 (T := T)
  have hScaledTile : TilesOn R
      (Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' T) X'.carrier := by
    have htransport :=
      (Tiling.AxisParallel.tilesOn_positiveSimilarity_iff hqRpos hOpen
        (r := (0 : Tiling.Plane)) (c := (0 : Tiling.Plane))).mpr hTile
    rw [hCarrier]
    simpa only [zero_add] using htransport
  have hScaledCentres :
      Tiling.AxisParallel.Continuous.verticalColumnCentres R
        (Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' T) =
        rationalHomothety q ''
          Tiling.AxisParallel.Continuous.verticalColumnCentres K T := by
    rw [Tiling.AxisParallel.Continuous.verticalColumnCentres_positiveSimilarity_image
      hqRpos hOpen (0 : Tiling.Plane)]
    exact hImage _
  have hScaledSupport :
      Tiling.AxisParallel.regularSupport R
        (rationalHomothety q ''
          Tiling.AxisParallel.Continuous.verticalColumnCentres K T) =
        rationalHomothety q ''
          Tiling.AxisParallel.regularSupport K
            (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) := by
    calc
      regularSupport R (rationalHomothety q ''
          Tiling.AxisParallel.Continuous.verticalColumnCentres K T) =
        regularSupport R (Tiling.AxisParallel.Continuous.verticalColumnCentres R
          (Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' T)) := by rw [hScaledCentres]
      _ = Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 ''
          regularSupport K (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) := by
        simpa only [zero_add] using
          (Tiling.AxisParallel.Continuous.verticalColumnSupport_positiveSimilarity_image
            hqRpos hOpen (0 : Tiling.Plane))
      _ = rationalHomothety q ''
          regularSupport K (Tiling.AxisParallel.Continuous.verticalColumnCentres K T) :=
        hImage _
  have hRvertices' : R.vertices = rationalHomothety q '' K.vertices := by
    rw [hRvertices]
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hH w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, hH w⟩
  have hScaledVertices : ∀ v ∈ R.vertices, ∃ m n : ℤ,
      v = (m : ℝ) + (n : ℝ) * Complex.I := by
    intro v hv
    rw [hRvertices'] at hv
    simp only [Set.mem_image] at hv
    obtain ⟨w, hw, hvw⟩ := hv
    have hvEq : v = rationalHomothety q w := hvw.symm
    obtain ⟨m, hm⟩ :=
      Tiling.RationalPolygonal.mem_integerLattice_iff.mp (hVertices w hw)
    refine ⟨m 0, m 1, ?_⟩
    rw [hvEq, ← hm]
    simp [Tiling.RationalPolygonal.integerPoint]
  refine ⟨q, ?_, ?_, ?_⟩
  · refine ⟨R, Tiling.AxisParallel.positiveSimilarity (q : ℝ) 0 '' T,
      X', hqpos, ?_, ?_, ?_, ?_, ?_, e₀,
      ?_, ?_, ?_, ?_⟩
    · exact hImage T
    · rfl
    · rfl
    · simpa only [hImage K.openCarrier] using hOpen
    · exact hRvertices'
    · intro P
      rw [Tiling.AxisParallel.Continuous.verticalPlate_positiveSimilarityEquiv_support_image
        hqRpos hOpen (0 : Tiling.Plane) P]
      simpa only [zero_add] using hImage P.support
    · intro P
      exact (Tiling.AxisParallel.Continuous.verticalPlate_positiveSimilarityEquiv_isVerticalColumn
        hqRpos hOpen (0 : Tiling.Plane) P).symm
    · exact hScaledCentres
    · simpa [hScaledCentres] using hScaledSupport
  · exact hScaledTile
  · exact hScaledVertices

theorem rationalPeriodicCarrierPlate_periodic
    {K : Region} {T : Set Tiling.Plane} (X : PeriodicVerticalCarrier)
    (hTile : TilesOn K T X.carrier)
    (hRational : ∀ v ∈ K.vertices, Tiling.IsRationalPoint v) :
    ∃ b : ℝ, 0 < b ∧
      (∀ P : VerticalPlate K T, ¬ IsVerticalColumn P →
        Tiling.RationalPolygonal.SetPeriodicBy P.support (b : ℂ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (regularSupport K (verticalColumnCentres K T)) (b : ℂ) := by
  obtain ⟨q, H, hscaledTile, hscaledVertices⟩ :=
    rationalHomothetyData_exists X hTile hRational
  obtain ⟨b, hb, hplates, hcolumns⟩ :=
    integralPeriodicCarrierPlate_periodic H.scaledCarrier hscaledTile hscaledVertices
  refine ⟨b / (q : ℝ), div_pos hb (by exact_mod_cast H.q_pos), ?_, ?_⟩
  · intro P hP
    apply homothety_pullback_period H.q_pos hb
    have hPnon : ¬ IsVerticalColumn (H.plateEquiv P) := fun hcol ↦
      hP ((H.plate_column P).mp hcol)
    have hscaled := hplates (H.plateEquiv P) hPnon
    rw [H.plate_support P] at hscaled
    exact hscaled
  · apply homothety_pullback_period H.q_pos hb
    rw [H.columnCentres_eq, H.columnSupport_eq] at hcolumns
    exact hcolumns








end Tiling.AxisParallel.Terminal
