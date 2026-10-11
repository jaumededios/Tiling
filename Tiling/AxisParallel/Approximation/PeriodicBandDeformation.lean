import Tiling.AxisParallel.OneDimensional.PeriodicPointEnumeration
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.Geometry.PackingTopology
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.OneDimensional.FiniteInterval.TargetGeometry
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Filter.AtTopBot.Ring
import Tiling.AxisParallel.Approximation.CoordinateExtension


open Set
open Function MeasureTheory
open scoped Pointwise

namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval

universe u

noncomputable section

private theorem periodic_mem_of_vadd_eq {S : Set ℝ} {a : ℝ}
    (h : a +ᵥ S = S) : Function.Periodic (fun x => x ∈ S) a := by
  intro x
  apply propext
  constructor
  · intro hx
    have hx' : a + x ∈ S := by simpa [add_comm] using hx
    rw [← h] at hx'
    obtain ⟨y, hy, hay⟩ := hx'
    have : y = x := by simpa using hay
    simpa [this] using hy
  · intro hx
    have hx' : a + x ∈ a +ᵥ S := ⟨x, hx, rfl⟩
    rw [h] at hx'
    simpa [add_comm] using hx'

/-- Coupled boundary, occupancy, and finite-gap data for a proper periodic vertical band. -/
structure PeriodicBandData (C : ApproximationContext) where
  base : Set ℝ
  base_nonempty : base.Nonempty
  base_open : IsOpen base
  base_regular : interior (closure base) = base
  base_proper : base ≠ Set.univ
  period : ℝ
  period_pos : 0 < period
  base_periodic : period +ᵥ base = base
  target_eq : C.target = {z : Tiling.Plane | z.re ∈ base}
  source_tilesOn : Tiling.AxisParallel.TilesOn C.region C.centres C.target
  boundary_mem_coordinateSpace :
    ∀ x ∈ frontier base, x ∈ C.coordinateSpace
  period_mem_coordinateSpace : period ∈ C.coordinateSpace
  numberOfBoundaryPoints : ℕ
  numberOfBoundaryPoints_pos : 0 < numberOfBoundaryPoints
  boundary : ℤ → ℝ
  boundary_strictMono : StrictMono boundary
  boundary_range : Set.range boundary = frontier base
  boundary_value_mem_coordinateSpace :
    ∀ j : ℤ, boundary j ∈ C.coordinateSpace
  boundary_period : ∀ j : ℤ,
    boundary (j + Int.ofNat numberOfBoundaryPoints) = boundary j + period
  occupied : ℤ → Bool
  occupied_iff : ∀ j : ℤ,
    occupied j = true ↔ Set.Ioo (boundary j) (boundary (j + 1)) ⊆ base
  occupied_periodic : ∀ j : ℤ,
    occupied (j + Int.ofNat numberOfBoundaryPoints) = occupied j
  boundaryRepresentatives : Finset ℝ
  boundaryRepresentatives_eq :
    (boundaryRepresentatives : Set ℝ) = frontier base ∩ Set.Ico 0 period
  boundaryRepresentatives_indexed :
    ∀ x : ℝ, x ∈ boundaryRepresentatives ↔
      ∃ i : Fin numberOfBoundaryPoints, x = boundary (Int.ofNat i)
  gapAlphabet : Finset ℝ
  gapAlphabet_indexed :
    ∀ g : ℝ, g ∈ gapAlphabet ↔ ∃ i : Fin numberOfBoundaryPoints,
      g = boundary (Int.ofNat i + 1) - boundary (Int.ofNat i)
  gap_mem_coordinateSpace :
    ∀ g ∈ gapAlphabet, g ∈ C.coordinateSpace

private theorem exists_periodicBandData_of_boundaryWitness
    (C : ApproximationContext.{u}) (X : Set ℝ) (alpha : ℝ)
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (hXproper : X ≠ Set.univ)
    (halpha : 0 < alpha) (hXperiod : alpha +ᵥ X = X)
    (htarget : C.target = {z : Tiling.Plane | z.re ∈ X})
    (htiles : TilesOn C.region C.centres C.target)
    (hboundary : ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ C.region.vertices)
      (t : Tiling.Plane) (_ht : t ∈ C.centres), x = (v + t).re) :
    ∃ P : PeriodicBandData C, P.base = X ∧ P.period = alpha := by
  classical
  have htilesCylinder :
      TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ X} := by
    simpa [htarget] using htiles
  have hfrontlocal : ∀ Q : Set ℝ, Bornology.IsBounded Q →
      (frontier X ∩ Q).Finite := by
    intro Q hQ
    obtain ⟨R, hQsub⟩ := hQ.subset_closedBall 0
    have hfin := TilesOn.verticalCylinder_frontier_locallyFinite htilesCylinder
      hXopen hXregular (Metric.closedBall 0 R) (isCompact_closedBall 0 R)
    apply hfin.subset
    intro x hx
    exact ⟨hQsub hx.2, hx.1⟩
  have hfrontne : (frontier X).Nonempty :=
    frontier_nonempty_of_nonempty_proper_regularOpen hXnonempty hXopen
      hXregular hXproper
  have hfrontperiod : alpha +ᵥ frontier X = frontier X := frontier_periodic hXperiod
  obtain ⟨E⟩ := periodicIntEnumeration_exists (frontier X) alpha halpha hfrontne
    hfrontlocal hfrontperiod
  have hboundaryCoord : ∀ x ∈ frontier X, x ∈ C.coordinateSpace := by
    intro x hx
    obtain ⟨v, hv, t, ht, hvt⟩ := hboundary x hx
    rw [hvt]
    simpa only [Complex.add_re] using
      C.coordinateSpace.add_mem (C.vertex_re_mem v hv) (C.centre_re_mem t ht)
  have halphaCoord : alpha ∈ C.coordinateSpace := by
    obtain ⟨x, hx⟩ := hfrontne
    have hxshift : x + alpha ∈ frontier X := by
      rw [← hfrontperiod]
      exact Set.mem_vadd_set.mpr
        ⟨x, hx, by simp only [vadd_eq_add, add_comm]⟩
    have hdiff : (x + alpha) - x ∈ C.coordinateSpace :=
      C.coordinateSpace.sub_mem (hboundaryCoord (x + alpha) hxshift)
        (hboundaryCoord x hx)
    simpa [add_sub_cancel_left] using hdiff
  have hrepfin : (frontier X ∩ Ico 0 alpha).Finite := by
    have hfin := TilesOn.verticalCylinder_frontier_locallyFinite htilesCylinder
      hXopen hXregular (Icc 0 alpha) isCompact_Icc
    apply hfin.subset
    intro x hx
    exact ⟨⟨hx.2.1, le_of_lt hx.2.2⟩, hx.1⟩
  let reps : Finset ℝ := hrepfin.toFinset
  have hreps : (reps : Set ℝ) = frontier X ∩ Ico 0 alpha := hrepfin.coe_toFinset
  have hocc_shift (j : ℤ) :
      Ioo (E.point j) (E.point (j + 1)) ⊆ X ↔
        Ioo (E.point (j + E.count)) (E.point (j + E.count + 1)) ⊆ X := by
    have hinter (a b : ℝ) : alpha +ᵥ Ioo a b = Ioo (a + alpha) (b + alpha) := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        simp only [vadd_eq_add]
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      · intro hz
        refine ⟨z - alpha, ?_, ?_⟩
        · exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
        · simp
    have hbase :
        Ioo (E.point j + alpha) (E.point (j + 1) + alpha) =
          Ioo (E.point (j + E.count)) (E.point (j + E.count + 1)) := by
      rw [← E.point_period j, ← E.point_period (j + 1)]
      congr 2
      all_goals (simp; ring)
    have hsub (S : Set ℝ) : S ⊆ X ↔ alpha +ᵥ S ⊆ X := by
      constructor
      · intro hS z hz
        obtain ⟨y, hy, rfl⟩ := hz
        simpa only [vadd_eq_add, add_comm] using
          ((periodic_mem_of_vadd_eq hXperiod) y).mpr (hS hy)
      · intro hS y hy
        have hyshift : y + alpha ∈ X := hS
          (Set.mem_vadd_set.mpr ⟨y, hy, by simp [vadd_eq_add, add_comm]⟩)
        exact ((periodic_mem_of_vadd_eq hXperiod) y).mp hyshift
    calc
      Ioo (E.point j) (E.point (j + 1)) ⊆ X ↔
          alpha +ᵥ Ioo (E.point j) (E.point (j + 1)) ⊆ X :=
        hsub _
      _ ↔ Ioo (E.point j + alpha) (E.point (j + 1) + alpha) ⊆ X := by
        rw [hinter]
      _ ↔ Ioo (E.point (j + E.count)) (E.point (j + E.count + 1)) ⊆ X := by
        rw [hbase]
  have hboundaryCoord' (j : ℤ) : E.point j ∈ C.coordinateSpace := by
    apply hboundaryCoord _
    have hrange : E.point j ∈ Set.range E.point := ⟨j, rfl⟩
    exact Eq.mp (congrArg (fun S : Set ℝ => E.point j ∈ S) E.point_range) hrange
  let occupied : ℤ → Bool := fun j =>
    decide (Ioo (E.point j) (E.point (j + 1)) ⊆ X)
  let gaps : Finset ℝ := Finset.univ.image
    (fun i : Fin E.count => E.point (Int.ofNat i + 1) - E.point (Int.ofNat i))
  have hgapmem (g : ℝ) (hg : g ∈ gaps) : g ∈ C.coordinateSpace := by
    simp only [gaps, Finset.mem_image, Finset.mem_univ, true_and] at hg
    obtain ⟨i, rfl⟩ := hg
    exact C.coordinateSpace.sub_mem
      (hboundaryCoord' (Int.ofNat i + 1)) (hboundaryCoord' (Int.ofNat i))
  let P : PeriodicBandData C := {
    base := X
    base_nonempty := hXnonempty
    base_open := hXopen
    base_regular := hXregular
    base_proper := hXproper
    period := alpha
    period_pos := halpha
    base_periodic := hXperiod
    target_eq := htarget
    source_tilesOn := htiles
    boundary_mem_coordinateSpace := hboundaryCoord
    period_mem_coordinateSpace := halphaCoord
    numberOfBoundaryPoints := E.count
    numberOfBoundaryPoints_pos := E.count_pos
    boundary := E.point
    boundary_strictMono := E.point_strictMono
    boundary_range := E.point_range
    boundary_value_mem_coordinateSpace := hboundaryCoord'
    boundary_period := E.point_period
    occupied := occupied
    occupied_iff := by
      intro j
      change decide (Ioo (E.point j) (E.point (j + 1)) ⊆ X) = true ↔ _
      exact ⟨of_decide_eq_true, decide_eq_true⟩
    occupied_periodic := by
      intro j
      apply Bool.decide_congr
      simpa only [Int.ofNat_eq_natCast] using (hocc_shift j).symm
    boundaryRepresentatives := reps
    boundaryRepresentatives_eq := hreps
    boundaryRepresentatives_indexed := by
      intro x
      change x ∈ (reps : Set ℝ) ↔ _
      rw [hreps, E.fundamental_eq]
      simp only [Set.mem_range]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨i, hi.symm⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    gapAlphabet := gaps
    gapAlphabet_indexed := by
      intro g
      simp only [gaps, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨i, rfl⟩
    gap_mem_coordinateSpace := hgapmem }
  exact ⟨P, rfl, rfl⟩


private def verticalCylinder_boundaryCoordinateWitnessStatement : Prop :=
  ∀ (C : ApproximationContext.{u}) (X : Set ℝ), IsOpen X →
    interior (closure X) = X →
    TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ X} →
    ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ C.region.vertices)
      (t : Tiling.Plane) (_ht : t ∈ C.centres), x = (v + t).re

private theorem support_mem_of_cylinder_frontier
    (C : ApproximationContext.{u}) (X : Set ℝ) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X)
    (hTile : TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ X})
    (x q : ℝ) (hx : x ∈ frontier X) :
    ∃ t : ↥C.centres,
      (Complex.mk x q : Tiling.Plane) ∈ (t : Tiling.Plane) +ᵥ C.region.support := by
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport C.region C.centres =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hxf : (Complex.mk x q : Tiling.Plane) ∈
      frontier ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
    rw [frontier_verticalCylinder]
    simpa using hx
  have hOpenUnion : IsOpen (openUnion C.region C.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _
  have hcloseEq : closure (regularSupport C.region C.centres) =
      closure (openUnion C.region C.centres) := by
    rw [regularSupport]
    apply le_antisymm
    · exact closure_minimal
        (interior_subset : interior (closure (openUnion C.region C.centres)) ⊆
          closure (openUnion C.region C.centres)) isClosed_closure
    · exact closure_mono (interior_maximal subset_closure hOpenUnion)
  have hxclosure : (Complex.mk x q : Tiling.Plane) ∈
      closure (openUnion C.region C.centres) := by
    rw [← hcloseEq, hsupport]
    exact frontier_subset_closure hxf
  rw [closure_openUnion_eq_iUnion_support hTile.2.1] at hxclosure
  exact Set.mem_iUnion.mp hxclosure

private theorem translated_vertex_levels_countable
    {C : ApproximationContext.{u}}
    (hpacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements C.centres)) :
    (Set.range fun p : ↥C.centres × ↥C.region.vertices =>
      ((p.1 : Tiling.Plane) + p.2.1).im).Countable := by
  have hS : C.centres.Countable := (IsPacking.locallyFinite_centres hpacking).2
  have hV : C.region.vertices.Countable := by
    rw [← C.region.coe_vertexFinset]
    exact C.region.vertexFinset.finite_toSet.countable
  let _ : Countable ↥C.centres := hS.to_subtype
  let _ : Countable ↥C.region.vertices := hV.to_subtype
  exact Set.countable_range _

private theorem verticalCylinder_boundaryCoordinateWitnessStatement_proof :
    verticalCylinder_boundaryCoordinateWitnessStatement := by
  intro C X hXopen hXregular hTile x hx
  let levels : Set ℝ := Set.range fun p : ↥C.centres × ↥C.region.vertices =>
    ((p.1 : Tiling.Plane) + p.2.1).im
  have hlevels : levels.Countable := by
    exact translated_vertex_levels_countable hTile.2.1
  have hdiff : (Set.Ioo (0 : ℝ) 1 \ levels).Nonempty := by
    by_contra hne
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ levels := by
      intro q hq
      by_contra hqbad
      exact hne ⟨q, hq, hqbad⟩
    have hzero : volume (Set.Ioo (0 : ℝ) 1) = 0 :=
      measure_mono_null hsub (hlevels.measure_zero volume)
    exact (isOpen_Ioo.measure_ne_zero volume ⟨(1 / 2 : ℝ), by norm_num⟩) hzero
  obtain ⟨q, hqIoo, hqbad⟩ := hdiff
  obtain ⟨t, hzt⟩ := support_mem_of_cylinder_frontier C X hXopen hXregular
    hTile x q hx
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) :=
    hXopen.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ X} := by
    change interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hXregular]
  have hsupport : regularSupport C.region C.centres =
      {z : Tiling.Plane | z.re ∈ X} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hfront : (Complex.mk x q : Tiling.Plane) ∈
      frontier ((t : Tiling.Plane) +ᵥ C.region.support) := by
    rw [frontier]
    refine ⟨subset_closure hzt, ?_⟩
    intro hzint
    have hzopen : (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ C.region.openCarrier := by
      change (Complex.mk x q : Tiling.Plane) ∈
        (t : Tiling.Plane) +ᵥ interior C.region.support
      simpa only [interior_vadd] using hzint
    have hzunion : (Complex.mk x q : Tiling.Plane) ∈
        openUnion C.region C.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨t, hzopen⟩
    have hOpenUnion : IsOpen (openUnion C.region C.centres) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier]
      exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _
    have hopenSub : openUnion C.region C.centres ⊆
        regularSupport C.region C.centres := by
      rw [regularSupport]
      exact interior_maximal subset_closure hOpenUnion
    have hztarget : (Complex.mk x q : Tiling.Plane) ∈
        ({z : Tiling.Plane | z.re ∈ X} : Set Tiling.Plane) := by
      rw [← hsupport]
      exact hopenSub hzunion
    have hxin : x ∈ X := by simpa using hztarget
    have hxint : x ∈ interior X :=
      mem_interior_iff_mem_nhds.mpr (hXopen.mem_nhds hxin)
    exact (Set.disjoint_left.1 disjoint_interior_frontier hxint hx)
  have hsource : (Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane) ∈
      frontier C.region.support := by
    have hvaddfront : frontier ((t : Tiling.Plane) +ᵥ C.region.support) =
        (t : Tiling.Plane) +ᵥ frontier C.region.support := by
      rw [frontier, closure_vadd, interior_vadd]
      ext z
      simp only [frontier, Set.mem_sdiff, mem_vadd_set_iff_neg_vadd_mem]
    rw [hvaddfront] at hfront
    simpa only [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] using hfront
  have hgrid :=
    Tiling.AxisParallel.IntrinsicVertices.frontier_subset_vertexCoordinateGrid
      C.region hsource
  change ((∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).re = v.re) ∨
    ∃ v ∈ C.region.vertices,
      ((Complex.mk x q : Tiling.Plane) - (t : Tiling.Plane)).im = v.im) at hgrid
  obtain hgrid | hgrid := hgrid
  · obtain ⟨v, hv, hvr⟩ := hgrid
    refine ⟨v, hv, t.1, t.2, ?_⟩
    have hvr' : x - (t : Tiling.Plane).re = v.re := by
      simpa only [Complex.sub_re] using hvr
    rw [Complex.add_re]
    linarith
  · obtain ⟨v, hv, hvi⟩ := hgrid
    have hvi' : q - (t : Tiling.Plane).im = v.im := by
      simpa only [Complex.sub_im] using hvi
    have hqbad' : q = ((t : Tiling.Plane) + v).im := by
      rw [Complex.add_im]
      linarith
    exact (hqbad ⟨⟨t, ⟨v, hv⟩⟩, hqbad'.symm⟩).elim
/-- Construct periodic band data for a proper periodic cylinder. -/
theorem exists_periodicBandData
    (C : ApproximationContext) (X : Set ℝ) (alpha : ℝ)
    (hXnonempty : X.Nonempty) (hXopen : IsOpen X)
    (hXregular : interior (closure X) = X) (hXproper : X ≠ Set.univ)
    (halpha : 0 < alpha) (hXperiodic : alpha +ᵥ X = X)
    (htarget : C.target = {z : Tiling.Plane | z.re ∈ X})
    (htiles : TilesOn C.region C.centres C.target) :
    ∃ P : PeriodicBandData C, P.base = X ∧ P.period = alpha := by
  have htilesCylinder :
      TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ X} := by
    simpa [htarget] using htiles
  have hboundary : ∀ x ∈ frontier X, ∃ (v : Tiling.Plane)
      (hv : v ∈ C.region.vertices) (t : Tiling.Plane)
      (ht : t ∈ C.centres), x = (v + t).re :=
    verticalCylinder_boundaryCoordinateWitnessStatement_proof
      C X hXopen hXregular htilesCylinder
  exact exists_periodicBandData_of_boundaryWitness C X alpha hXnonempty hXopen
    hXregular hXproper halpha hXperiodic htarget htiles hboundary

/-- A threshold which controls both the tile shape and every proper-band gap. -/
structure IsPeriodicBandFineness {C : ApproximationContext}
    (P : PeriodicBandData C) (ε : ℝ) : Prop where
  epsilon_pos : 0 < ε
  forces_good : ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C ε φ → IsGoodApproximation C φ
  preserves_gap_positivity : ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C ε φ → ∀ (g : ℝ) (hg : g ∈ P.gapAlphabet),
      0 < mapScalar φ ⟨g, P.gap_mem_coordinateSpace g hg⟩

/-- The image of the `j`-th boundary coordinate under a rational approximation. -/
def PeriodicBandData.deformedBoundary
    {C : ApproximationContext} (P : PeriodicBandData C)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (j : ℤ) : ℝ :=
  mapScalar φ ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩

/-- The finite alphabet of consecutive deformed gaps in one period. -/
def PeriodicBandData.deformedGapAlphabet
    {C : ApproximationContext} (P : PeriodicBandData C)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) : Finset ℝ :=
  Finset.univ.image fun i : Fin P.numberOfBoundaryPoints ↦
    P.deformedBoundary φ (Int.ofNat i + 1) - P.deformedBoundary φ (Int.ofNat i)

private theorem positive_of_sign_eq_of_positive {x y : ℝ}
    (hxy : Real.sign x = Real.sign y) (hy : 0 < y) : 0 < x := by
  rw [Real.sign_of_pos hy] at hxy
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx] at hxy
    norm_num at hxy
  · simp at hxy
  · exact hx

theorem PeriodicBandData.boundaryRepresentatives_finite
    {C : ApproximationContext} (P : PeriodicBandData C) :
    (frontier P.base ∩ Set.Ico 0 P.period).Finite := by
  rw [← P.boundaryRepresentatives_eq]
  exact P.boundaryRepresentatives.finite_toSet

theorem exists_deformedBandPeriod
    {C : ApproximationContext} (P : PeriodicBandData C) :
    ∃ ε₀ : ℝ, IsPeriodicBandFineness P ε₀ ∧
      ∀ (φ : C.coordinateSpace →ₗ[ℚ] ℚ), IsEpsilonApproximation C ε₀ φ →
        ∃ αφ : ℝ, αφ = mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ ∧
          0 < αφ ∧ ∃ q : ℚ, αφ = (q : ℝ) := by
  classical
  let gapScalars : Finset C.coordinateSpace := P.gapAlphabet.attach.image
    fun g : {x : ℝ // x ∈ P.gapAlphabet} ↦
    ⟨(g : ℝ), P.gap_mem_coordinateSpace g.1 g.2⟩
  let periodScalar : C.coordinateSpace := ⟨P.period, P.period_mem_coordinateSpace⟩
  let scalars : Finset C.coordinateSpace := insert periodScalar gapScalars
  obtain ⟨εgood, hεgood, hgood⟩ := isGoodApproximation_of_sufficientlyFine C
  obtain ⟨εsign, hεsign, hsign⟩ := approximation_preservesSign_finset C scalars
  let ε₀ := min εgood εsign
  have hε₀ : 0 < ε₀ := lt_min hεgood hεsign
  have hleGood : ε₀ ≤ εgood := min_le_left _ _
  have hleSign : ε₀ ≤ εsign := min_le_right _ _
  have hFine : IsPeriodicBandFineness P ε₀ := by
    refine ⟨hε₀, ?_, ?_⟩
    · intro φ hφ
      exact hgood φ (hφ.of_le hleGood)
    · intro φ hφ g hg
      let gs : C.coordinateSpace := ⟨g, P.gap_mem_coordinateSpace g hg⟩
      have hgs : gs ∈ scalars := by
        apply Finset.mem_insert_of_mem
        refine Finset.mem_image.mpr
          ⟨(⟨g, hg⟩ : {x : ℝ // x ∈ P.gapAlphabet}), ?_, ?_⟩
        · simp
        · rfl
      have hsgn := hsign φ (hφ.of_le hleSign) gs hgs
      apply positive_of_sign_eq_of_positive hsgn
      obtain ⟨i, rfl⟩ := (P.gapAlphabet_indexed g).mp hg
      exact sub_pos.mpr (P.boundary_strictMono (by omega))
  refine ⟨ε₀, hFine, ?_⟩
  intro φ hφ
  let αφ := mapScalar φ periodScalar
  have hpMem : periodScalar ∈ scalars := Finset.mem_insert_self _ _
  have hpSign := hsign φ (hφ.of_le hleSign) periodScalar hpMem
  have hpPos : 0 < αφ := positive_of_sign_eq_of_positive hpSign P.period_pos
  exact ⟨αφ, rfl, hpPos, ⟨φ periodScalar, rfl⟩⟩

/-- Periodic boundary increments are transported linearly and remain positive. -/
theorem periodicBandDeformation_preservesGapAlphabet
    {C : ApproximationContext} (P : PeriodicBandData C)
    (ε : ℝ) (hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (hφ : IsEpsilonApproximation C ε φ) :
    (∀ j : ℤ,
      P.deformedBoundary φ (j + Int.ofNat P.numberOfBoundaryPoints) =
        P.deformedBoundary φ j +
          mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩) ∧
    (∀ i : Fin P.numberOfBoundaryPoints,
      0 < P.deformedBoundary φ (Int.ofNat i + 1) -
        P.deformedBoundary φ (Int.ofNat i)) ∧
    (∀ i : Fin P.numberOfBoundaryPoints,
      P.deformedBoundary φ (Int.ofNat i + 1) -
          P.deformedBoundary φ (Int.ofNat i) =
        mapScalar φ
          ⟨P.boundary (Int.ofNat i + 1) - P.boundary (Int.ofNat i),
            C.coordinateSpace.sub_mem
              (P.boundary_value_mem_coordinateSpace (Int.ofNat i + 1))
              (P.boundary_value_mem_coordinateSpace (Int.ofNat i))⟩) ∧
    (∀ g : ℝ, g ∈ P.deformedGapAlphabet φ ↔
      ∃ i : Fin P.numberOfBoundaryPoints,
        g = P.deformedBoundary φ (Int.ofNat i + 1) -
          P.deformedBoundary φ (Int.ofNat i)) := by
  have hperiod : ∀ j : ℤ,
      P.deformedBoundary φ (j + Int.ofNat P.numberOfBoundaryPoints) =
        P.deformedBoundary φ j +
          mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ := by
    intro j
    simp only [PeriodicBandData.deformedBoundary, mapScalar]
    norm_cast
    rw [← map_add]
    congr 1
    apply Subtype.ext
    exact P.boundary_period j
  have hgap : ∀ i : Fin P.numberOfBoundaryPoints,
      P.deformedBoundary φ (Int.ofNat i + 1) -
          P.deformedBoundary φ (Int.ofNat i) =
        mapScalar φ
          ⟨P.boundary (Int.ofNat i + 1) - P.boundary (Int.ofNat i),
            C.coordinateSpace.sub_mem
              (P.boundary_value_mem_coordinateSpace (Int.ofNat i + 1))
              (P.boundary_value_mem_coordinateSpace (Int.ofNat i))⟩ := by
    intro i
    simp only [PeriodicBandData.deformedBoundary, mapScalar]
    norm_cast
    rw [← map_sub]
    rfl
  refine ⟨hperiod, ?_, hgap, ?_⟩
  · intro i
    rw [hgap i]
    apply hFine.preserves_gap_positivity φ hφ
    exact (P.gapAlphabet_indexed _).mpr ⟨i, rfl⟩
  · intro g
    simp only [PeriodicBandData.deformedGapAlphabet, Finset.mem_image,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, rfl⟩

end

end Tiling.AxisParallel.Approximation

open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains
open Tiling.AxisParallel.Foundations.FilledSliceChains
open Tiling.AxisParallel.Foundations.FilledSliceChains
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations
open Tiling.AxisParallel.Foundations.GenericSlices
open Tiling.AxisParallel.Foundations.FilledSliceChains

private theorem continuous_slicePoint (axis : Axis) (q : ℝ) :
    Continuous (slicePoint axis q) := by
  cases axis <;> unfold slicePoint <;> fun_prop

private theorem exists_mem_Ioo_of_ae_real {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hP : ∀ᵐ x : ℝ ∂volume, P x) :
    ∃ x ∈ Ioo a b, P x := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    intro hz
    have : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo a b), hz]
      simp
    rw [Real.volume_Ioo] at this
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at this
  let hne : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hμ
  have _hp' : ∀ᵐ x ∂volume.restrict (Ioo a b), P x :=
    hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (_hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, _hp, hx⟩
  exact ⟨x, hx, _hp⟩

private def IsSourceBandSliceChain
    (C : ApproximationContext) (q : ℝ) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) : Prop :=
  (∀ i, (xLift i : ℝ) = x i) ∧ StrictMono x ∧
    ∀ i : Fin n, ∃ v w : Tiling.Plane,
      v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
      x i.castSucc = (v + (owner i : Tiling.Plane)).re ∧
      x i.succ = (w + (owner i : Tiling.Plane)).re ∧
      0 < (w - v).re ∧
      {z : Tiling.Plane | z.im = q ∧ z.re ∈ Ioo (x i.castSucc) (x i.succ)} ⊆
        (owner i : Tiling.Plane) +ᵥ C.region.openCarrier

private def sourceBand_chamberChainsSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
    ∀ᵐ q : ℝ ∂volume, ∀ j : ℤ, P.occupied j = true →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
          IsSourceBandSliceChain C q x xLift owner

/-- Exact missing lower-layer seam: the existing production chain theorem only
    proves this with `TilesOn ... univ`; A04 needs it for each occupied source
    chamber of the proper cylinder. -/
private theorem horizontal_coordinate_lift
    {C : ApproximationContext.{u}} {q : ℝ} {n : ℕ}
    (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
    (owner : Fin n → ↥C.centres)
    (hchain : IsFilledIndexedSliceChain C.region C.centres
      Axis.horizontal q x owner) :
    ∃ xLift : Fin (n + 1) → C.coordinateSpace,
      ∀ i, (xLift i : ℝ) = x i := by
  have xmem : ∀ i : Fin (n + 1), x i ∈ C.coordinateSpace := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · let j : Fin n := ⟨n - 1, Nat.sub_lt _hn (by omega)⟩
      have hjsucc : j.succ = Fin.last n := by
        ext
        simp [j]
        omega
      obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 j
      rw [← hjsucc, hright]
      exact C.coordinateSpace.add_mem
        (C.vertex_re_mem w hw) (C.centre_re_mem _ (owner j).2)
    · obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 j
      rw [hleft]
      exact C.coordinateSpace.add_mem
        (C.vertex_re_mem v _hv) (C.centre_re_mem _ (owner j).2)
  exact ⟨fun i ↦ ⟨x i, xmem i⟩, fun _ ↦ rfl⟩

/-- Exact remaining interface for closing source chamber chains: boundary membership
and fibrewise local coverage at the same Fubini-good height. -/
private def sourceBand_chamberChainsBoundaryBridge : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
    ∀ᵐ q : ℝ ∂volume,
      (∀ j : ℤ, P.occupied j = true →
        P.boundary j ∈ sliceEndpointSet C.region C.centres Axis.horizontal q ∧
        P.boundary (j + 1) ∈ sliceEndpointSet C.region C.centres Axis.horizontal q) ∧
      (∀ j : ℤ, P.occupied j = true →
        ∀ᵐ x : ℝ ∂volume,
          x ∈ Ioo (P.boundary j) (P.boundary (j + 1)) →
            slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)

private theorem sourceBand_chamberChains_of_boundaryBridge
    (hbridge : ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
      ∀ᵐ q : ℝ ∂volume,
        (∀ j : ℤ, P.occupied j = true →
          P.boundary j ∈ sliceEndpointSet C.region C.centres Axis.horizontal q ∧
          P.boundary (j + 1) ∈ sliceEndpointSet C.region C.centres Axis.horizontal q) ∧
        (∀ j : ℤ, P.occupied j = true →
          ∀ᵐ x : ℝ ∂volume,
            x ∈ Ioo (P.boundary j) (P.boundary (j + 1)) →
              slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)) :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
      ∀ᵐ q : ℝ ∂volume, ∀ j : ℤ, P.occupied j = true →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
          IsSourceBandSliceChain C q x xLift owner := by
  intro C P
  have hpack := P.source_tilesOn.2.1
  filter_upwards [hbridge P,
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints_of_local_ae
      C.region C.centres hpack Axis.horizontal] with q hq hchains
  intro j hj
  obtain ⟨hend, hlocal⟩ := hq
  obtain ⟨hl, hr⟩ := hend j hj
  obtain ⟨n, _hn, x, owner, hx0, hxlast, hchain, _hendpoints⟩ :=
    hchains (P.boundary j) hl (P.boundary (j + 1)) hr
      (P.boundary_strictMono (by omega)) (hlocal j hj)
  obtain ⟨xLift, hLift⟩ := horizontal_coordinate_lift _hn x owner hchain
  refine ⟨n, _hn, x, xLift, owner, hx0, hxlast, hLift, hchain.1, ?_⟩
  intro i
  obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ := hchain.2 i
  exact ⟨v, w, _hv, hw, by simpa [Axis.coord] using hleft,
    by simpa [Axis.coord] using hright,
    by simpa [Axis.coord] using hpositive, by
      simpa only [Tiling.AxisParallel.Foundations.FilledSliceChains.axisInterval] using hinside⟩
private theorem source_target_eq_openUnion_ae
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) :
    ∀ᵐ z : Tiling.Plane ∂volume,
      z ∈ C.target ↔ z ∈ openUnion C.region C.centres := by
  filter_upwards [P.source_tilesOn.2.2] with z hz
  change z ∈ C.target ↔ ∃ t : ↥C.centres,
    z ∈ (t : Tiling.Plane) +ᵥ C.region.openCarrier at hz
  simpa only [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion] using hz

private theorem source_target_eq_openUnion_slice_ae
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) :
    ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      slicePoint Axis.horizontal q x ∈ C.target ↔
        slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres := by
  have htargetMeas : MeasurableSet C.target := by
    rw [P.target_eq]
    exact P.base_open.measurableSet.preimage Complex.continuous_re.measurable
  have hopen : IsOpen (openUnion C.region C.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _
  let g : ℝ × ℝ → Tiling.Plane := fun p ↦
    (p.2 : ℂ) + (p.1 : ℂ) * Complex.I
  let A : Set (ℝ × ℝ) := g ⁻¹' C.target
  let B : Set (ℝ × ℝ) := g ⁻¹' openUnion C.region C.centres
  have hA : MeasurableSet A := by
    exact htargetMeas.preimage (by fun_prop)
  have hB : MeasurableSet B := by
    exact hopen.measurableSet.preimage (by fun_prop)
  let rel : ℝ × ℝ → Prop := fun p ↦ g p ∈ C.target ↔
    g p ∈ openUnion C.region C.centres
  have hrel : MeasurableSet {p : ℝ × ℝ | rel p} := by
    have heq : {p : ℝ × ℝ | rel p} = (A ∩ B) ∪ (Aᶜ ∩ Bᶜ) := by
      ext p
      change ((g p ∈ C.target ↔ g p ∈ openUnion C.region C.centres) ↔
        ((g p ∈ C.target ∧ g p ∈ openUnion C.region C.centres) ∨
          (g p ∉ C.target ∧ g p ∉ openUnion C.region C.centres)))
      by_cases htarget : g p ∈ C.target <;>
        by_cases hopen : g p ∈ openUnion C.region C.centres <;>
        simp [htarget, hopen]
    rw [heq]
    exact (hA.inter hB).union (hA.compl.inter hB.compl)
  have hplane :=
    Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae
      (source_target_eq_openUnion_ae P)
  have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, rel p := by
    have hswap :=
      (Measure.measurePreserving_swap (μ := volume) (ν := volume)).quasiMeasurePreserving.ae
        hplane
    filter_upwards [hswap] with p _hp
    change g p ∈ C.target ↔ g p ∈ openUnion C.region C.centres
    have hg : g p = (Complex.mk p.2 p.1 : Tiling.Plane) := by
      apply Complex.ext <;> simp [g]
    rw [hg]
    exact _hp
  have hprod' : ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume, rel (q, x) :=
    (Measure.ae_prod_iff_ae_ae hrel).mp hprod
  filter_upwards [hprod'] with q hq
  filter_upwards [hq] with x hx
  simpa [rel, g, slicePoint] using hx

private theorem sliceEndpoint_of_interval_ae
    {C : ApproximationContext.{u}} {a b q : ℝ}
    (hab : a < b)
    (hlocal : ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo a b → slicePoint Axis.horizontal q x ∈
        openUnion C.region C.centres)
    (haout : slicePoint Axis.horizontal q a ∉ openUnion C.region C.centres) :
    a ∈ sliceEndpointSet C.region C.centres Axis.horizontal q := by
  rw [sliceEndpointSet]
  have hclosure : a ∈ closure {x : ℝ |
      slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (ε / 2) ((b - a) / 2)
    have _hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hab))
    let J : Set ℝ := Ioo a (a + δ)
    have hJpos : volume J ≠ 0 := by
      apply isOpen_Ioo.measure_ne_zero volume
      refine ⟨a + δ / 2, ?_⟩
      change a < a + δ / 2 ∧ a + δ / 2 < a + δ
      constructor <;> linarith
    have hbad : volume {x : ℝ |
        ¬ (x ∈ Ioo a b →
          slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)} = 0 :=
      ae_iff.mp hlocal
    have hJnot : ¬ J ⊆ {x : ℝ |
        ¬ (x ∈ Ioo a b →
          slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)} := by
      intro hsub
      exact hJpos (measure_mono_null hsub hbad)
    obtain ⟨x, hxJ, hxgood⟩ := Set.not_subset.mp hJnot
    have hxab : x ∈ Ioo a b := by
      refine ⟨hxJ.1, ?_⟩
      have hxupper : x < a + δ := hxJ.2
      have hδb : δ ≤ (b - a) / 2 := min_le_right _ _
      linarith
    have hxgood' : x ∈ Ioo a b →
        slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres := by
      simpa only [Set.mem_ofPred_eq, not_not] using hxgood
    refine ⟨x, hxgood' hxab, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hxupper : x < a + δ := hxJ.2
    have _hδε : δ ≤ ε / 2 := min_le_left _ _
    constructor <;> linarith [hxJ.1, hxupper, _hδε]
  rw [frontier]
  refine ⟨hclosure, ?_⟩
  intro hxint
  have haU : a ∈ {x : ℝ |
      slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} :=
    interior_subset hxint
  exact haout haU

private theorem sliceEndpoint_of_interval_ae_right
    {C : ApproximationContext.{u}} {a b q : ℝ}
    (hab : a < b)
    (hlocal : ∀ᵐ x : ℝ ∂volume,
      x ∈ Ioo a b → slicePoint Axis.horizontal q x ∈
        openUnion C.region C.centres)
    (hbout : slicePoint Axis.horizontal q b ∉ openUnion C.region C.centres) :
    b ∈ sliceEndpointSet C.region C.centres Axis.horizontal q := by
  rw [sliceEndpointSet]
  have hclosure : b ∈ closure {x : ℝ |
      slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (ε / 2) ((b - a) / 2)
    have _hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (half_pos hε) (half_pos (sub_pos.mpr hab))
    let J : Set ℝ := Ioo (b - δ) b
    have hJpos : volume J ≠ 0 := by
      apply isOpen_Ioo.measure_ne_zero volume
      refine ⟨b - δ / 2, ?_⟩
      change b - δ < b - δ / 2 ∧ b - δ / 2 < b
      constructor <;> linarith
    have hbad : volume {x : ℝ |
        ¬ (x ∈ Ioo a b →
          slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)} = 0 :=
      ae_iff.mp hlocal
    have hJnot : ¬ J ⊆ {x : ℝ |
        ¬ (x ∈ Ioo a b →
          slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres)} := by
      intro hsub
      exact hJpos (measure_mono_null hsub hbad)
    obtain ⟨x, hxJ, hxgood⟩ := Set.not_subset.mp hJnot
    have hxab : x ∈ Ioo a b := by
      refine ⟨?_, hxJ.2⟩
      have hxlower : b - δ < x := hxJ.1
      have hδa : δ ≤ (b - a) / 2 := min_le_right _ _
      linarith
    have hxgood' : x ∈ Ioo a b →
        slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres := by
      simpa only [Set.mem_ofPred_eq, not_not] using hxgood
    refine ⟨x, hxgood' hxab, ?_⟩
    rw [Real.dist_eq, abs_lt]
    have hxlower : b - δ < x := hxJ.1
    have _hδε : δ ≤ ε / 2 := min_le_left _ _
    constructor <;> linarith [hxJ.2, hxlower, _hδε]
  rw [frontier]
  refine ⟨hclosure, ?_⟩
  intro hxint
  have hbU : b ∈ {x : ℝ |
      slicePoint Axis.horizontal q x ∈ openUnion C.region C.centres} :=
    interior_subset hxint
  exact hbout hbU

private theorem source_openUnion_subset_target
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (hTile : TilesOn C.region C.centres
      {z : Tiling.Plane | z.re ∈ P.base}) :
    openUnion C.region C.centres ⊆ C.target := by
  have hcarrierOpen : IsOpen ({z : Tiling.Plane | z.re ∈ P.base} : Set Tiling.Plane) :=
    P.base_open.preimage Complex.continuous_re
  have hcarrierRegular :
      interior (closure ({z : Tiling.Plane | z.re ∈ P.base} : Set Tiling.Plane)) =
        {z : Tiling.Plane | z.re ∈ P.base} := by
    change interior (closure (Complex.re ⁻¹' P.base)) = Complex.re ⁻¹' P.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, P.base_regular]
  have hsupport : regularSupport C.region C.centres =
      {z : Tiling.Plane | z.re ∈ P.base} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTile
  have hopen : IsOpen (openUnion C.region C.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun _ => (Region.openCarrier_regularOpen C.region).1.vadd _
  have hopenSub : openUnion C.region C.centres ⊆
      regularSupport C.region C.centres := by
    rw [regularSupport]
    exact interior_maximal subset_closure hopen
  intro z hz
  rw [P.target_eq]
  exact hsupport ▸ hopenSub hz

private theorem sourceBand_chamberChainsBoundaryBridge_impl :
    sourceBand_chamberChainsBoundaryBridge := by
  intro C P
  have htilesCylinder :
      TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ P.base} := by
    simpa [P.target_eq] using P.source_tilesOn
  have hopenSub : openUnion C.region C.centres ⊆ C.target :=
    source_openUnion_subset_target P htilesCylinder
  filter_upwards [source_target_eq_openUnion_slice_ae P] with q hq
  constructor
  · intro j hj
    let a : ℝ := P.boundary j
    let b : ℝ := P.boundary (j + 1)
    have hab : a < b := by
      dsimp [a, b]
      exact P.boundary_strictMono (by omega)
    have hlocal : ∀ᵐ x : ℝ ∂volume,
        x ∈ Ioo a b → slicePoint Axis.horizontal q x ∈
          openUnion C.region C.centres := by
      filter_upwards [hq] with x hx
      intro hxi
      have hbase : x ∈ P.base := by
        apply (P.occupied_iff j).mp hj
        simpa [a, b] using hxi
      have htarget : slicePoint Axis.horizontal q x ∈ C.target := by
        rw [P.target_eq]
        simpa [slicePoint] using hbase
      exact hx.mp htarget
    have hboundary_mem (k : ℤ) : P.boundary k ∈ frontier P.base := by
      rw [← P.boundary_range]
      exact ⟨k, rfl⟩
    have haout : slicePoint Axis.horizontal q a ∉
        openUnion C.region C.centres := by
      intro haU
      have haT : slicePoint Axis.horizontal q a ∈ C.target := hopenSub haU
      have haBase : a ∈ P.base := by
        rw [P.target_eq] at haT
        simpa [slicePoint] using haT
      have haInt : a ∈ interior P.base :=
        mem_interior_iff_mem_nhds.mpr (P.base_open.mem_nhds haBase)
      exact Set.disjoint_left.1 disjoint_interior_frontier haInt
        (hboundary_mem j)
    have hbout : slicePoint Axis.horizontal q b ∉
        openUnion C.region C.centres := by
      intro hbU
      have hbT : slicePoint Axis.horizontal q b ∈ C.target := hopenSub hbU
      have hbBase : b ∈ P.base := by
        rw [P.target_eq] at hbT
        simpa [slicePoint] using hbT
      have hbInt : b ∈ interior P.base :=
        mem_interior_iff_mem_nhds.mpr (P.base_open.mem_nhds hbBase)
      exact Set.disjoint_left.1 disjoint_interior_frontier hbInt
        (hboundary_mem (j + 1))
    refine ⟨?_, ?_⟩
    · exact sliceEndpoint_of_interval_ae (a := a) (b := b) hab hlocal haout
    · exact sliceEndpoint_of_interval_ae_right (a := a) (b := b) hab hlocal hbout
  · intro j hj
    let a : ℝ := P.boundary j
    let b : ℝ := P.boundary (j + 1)
    have hlocal : ∀ᵐ x : ℝ ∂volume,
        x ∈ Ioo a b → slicePoint Axis.horizontal q x ∈
          openUnion C.region C.centres := by
      filter_upwards [hq] with x hx
      intro hxi
      have hbase : x ∈ P.base := by
        apply (P.occupied_iff j).mp hj
        simpa [a, b] using hxi
      have htarget : slicePoint Axis.horizontal q x ∈ C.target := by
        rw [P.target_eq]
        simpa [slicePoint] using hbase
      exact hx.mp htarget
    exact hlocal

private theorem sourceBand_chamberChains_unconditional_impl :
    sourceBand_chamberChainsSpec := by
  exact sourceBand_chamberChains_of_boundaryBridge
    sourceBand_chamberChainsBoundaryBridge_impl

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

private def IsSourceBandGlobalSliceChain
    (C : ApproximationContext) (P : PeriodicBandData C) (q : ℝ) {n : ℕ}
    (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
    (step : Fin n → Sum ↥C.centres ℤ) : Prop :=
  (∀ i, (xLift i : ℝ) = x i) ∧ StrictMono x ∧
    ∀ i : Fin n,
      match step i with
      | .inl t => ∃ v w : Tiling.Plane,
          v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
          x i.castSucc = (v + (t : Tiling.Plane)).re ∧
          x i.succ = (w + (t : Tiling.Plane)).re ∧
          0 < (w - v).re ∧
          {z : Tiling.Plane | z.im = q ∧ z.re ∈ Ioo (x i.castSucc) (x i.succ)} ⊆
            (t : Tiling.Plane) +ᵥ C.region.openCarrier
      | .inr j => P.occupied j = false ∧
          x i.castSucc = P.boundary j ∧ x i.succ = P.boundary (j + 1)


private theorem append_source_global_chain
    {C : ApproximationContext.{u}} {P : PeriodicBandData C} {q : ℝ}
    {n m : ℕ}
    {x : Fin (n + 1) → ℝ}
    {xLift : Fin (n + 1) → C.coordinateSpace}
    {step : Fin n → Sum ↥C.centres ℤ}
    {y : Fin (m + 1) → ℝ}
    {yLift : Fin (m + 1) → C.coordinateSpace}
    {step' : Fin m → Sum ↥C.centres ℤ}
    (hx : IsSourceBandGlobalSliceChain C P q x xLift step)
    (hy : IsSourceBandGlobalSliceChain C P q y yLift step')
    (hm : 0 < m)
    (hend : x (Fin.last n) = y 0) :
    ∃ (z : Fin (n + m + 1) → ℝ)
      (zLift : Fin (n + m + 1) → C.coordinateSpace)
      (zstep : Fin (n + m) → Sum ↥C.centres ℤ),
      IsSourceBandGlobalSliceChain C P q z zLift zstep ∧
        z 0 = x 0 ∧ z (Fin.last (n + m)) = y (Fin.last m) := by
  rcases hx with ⟨hxLift, hxMono, hxSteps⟩
  rcases hy with ⟨hyLift, hyMono, hySteps⟩
  have hnm : n + m + 1 = (n + 1) + m := by omega
  let castNM (i : Fin (n + m + 1)) : Fin ((n + 1) + m) :=
    Fin.cast hnm i
  let z0 : Fin ((n + 1) + m) → ℝ :=
    Fin.addCases x (fun i : Fin m => y i.succ)
  let zLift0 : Fin ((n + 1) + m) → C.coordinateSpace :=
    Fin.addCases xLift (fun i : Fin m => yLift i.succ)
  let z : Fin (n + m + 1) → ℝ := fun i => z0 (castNM i)
  let zLift : Fin (n + m + 1) → C.coordinateSpace :=
    fun i => zLift0 (castNM i)
  let zstep : Fin (n + m) → Sum ↥C.centres ℤ :=
    Fin.addCases step step'
  have hzLift0 (i : Fin ((n + 1) + m)) :
      (zLift0 i : ℝ) = z0 i := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [zLift0, z0, Fin.addCases_left] using hxLift j
    · intro j
      simpa only [zLift0, z0, Fin.addCases_right] using hyLift j.succ
  have hzLift (i : Fin (n + m + 1)) : (zLift i : ℝ) = z i := by
    exact hzLift0 (castNM i)
  have hcast_left (j : Fin n) :
      castNM (Fin.castAdd m j).castSucc = Fin.castAdd m j.castSucc := by
    apply Fin.ext
    simp [castNM]
  have hcast_left_succ (j : Fin n) :
      castNM (Fin.castAdd m j).succ = Fin.castAdd m j.succ := by
    apply Fin.ext
    simp [castNM]
  have hzMono : StrictMono z := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      rw [show z (Fin.castAdd m j).castSucc = x j.castSucc by
        simp [z, z0, hcast_left j],
        show z (Fin.castAdd m j).succ = x j.succ by
          simp [z, z0, hcast_left_succ j]]
      exact Fin.strictMono_iff_lt_succ.mp hxMono j
    · intro j
      change z (Fin.natAdd n j.castSucc) < z (Fin.natAdd n j.succ)
      by_cases hj0 : j.val = 0
      · let j0 : Fin m := ⟨0, by omega⟩
        have hj : j = j0 := by ext; exact hj0
        have hleft : z (Fin.natAdd n j0.castSucc) = x (Fin.last n) := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j0.castSucc) =
              Fin.castAdd m (Fin.last n) by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        have hright : z (Fin.natAdd n j0.succ) = y j0.succ := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j0.succ) =
              Fin.natAdd (n + 1) j0 by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        rw [hj, hleft, hright, hend]
        exact Fin.strictMono_iff_lt_succ.mp hyMono j0
      · let k : Fin m := ⟨j.val - 1, by omega⟩
        have hj : k.succ = j.castSucc := by
          apply Fin.ext
          change (j.val - 1) + 1 = j.val
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)
        have hleft : z (Fin.natAdd n j.castSucc) = y k.succ := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j.castSucc) =
              Fin.natAdd (n + 1) k by
            apply Fin.ext
            simp [castNM, k]
            omega]
          simp [z0]
        have hright : z (Fin.natAdd n j.succ) = y j.succ := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j.succ) =
              Fin.natAdd (n + 1) j by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        rw [hleft, hright]
        simpa [hj] using Fin.strictMono_iff_lt_succ.mp hyMono j
  have hzSteps (i : Fin (n + m)) :
      match zstep i with
      | .inl t => ∃ v w : Tiling.Plane,
          v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
          z i.castSucc = (v + (t : Tiling.Plane)).re ∧
          z i.succ = (w + (t : Tiling.Plane)).re ∧
          0 < (w - v).re ∧
          {p : Tiling.Plane | p.im = q ∧ p.re ∈ Ioo (z i.castSucc) (z i.succ)} ⊆
            (t : Tiling.Plane) +ᵥ C.region.openCarrier
      | .inr j => P.occupied j = false ∧
          z i.castSucc = P.boundary j ∧ z i.succ = P.boundary (j + 1) := by
    refine Fin.addCases ?_ ?_ i
    · intro j
      have hleft : z (Fin.castAdd m j).castSucc = x j.castSucc := by
        simp [z, z0, hcast_left j]
      have hright : z (Fin.castAdd m j).succ = x j.succ := by
        simp [z, z0, hcast_left_succ j]
      simp only [zstep, Fin.addCases_left]
      rw [hleft, hright]
      exact hxSteps j
    · intro j
      simp only [zstep, Fin.addCases_right]
      change match step' j with
        | .inl t => ∃ v w : Tiling.Plane,
            v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
            z (Fin.natAdd n j.castSucc) = (v + (t : Tiling.Plane)).re ∧
            z (Fin.natAdd n j.succ) = (w + (t : Tiling.Plane)).re ∧
            0 < (w - v).re ∧
            {p : Tiling.Plane | p.im = q ∧
              p.re ∈ Ioo (z (Fin.natAdd n j.castSucc))
                (z (Fin.natAdd n j.succ))} ⊆
              (t : Tiling.Plane) +ᵥ C.region.openCarrier
        | .inr r => P.occupied r = false ∧
            z (Fin.natAdd n j.castSucc) = P.boundary r ∧
            z (Fin.natAdd n j.succ) = P.boundary (r + 1)
      by_cases hj0 : j.val = 0
      · let j0 : Fin m := ⟨0, by omega⟩
        have hj : j = j0 := by ext; exact hj0
        have hleft : z (Fin.natAdd n j.castSucc) = x (Fin.last n) := by
          rw [hj]
          dsimp [z]
          rw [show castNM (Fin.natAdd n j0.castSucc) =
              Fin.castAdd m (Fin.last n) by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        have hright : z (Fin.natAdd n j.succ) = y j0.succ := by
          rw [hj]
          dsimp [z]
          rw [show castNM (Fin.natAdd n j0.succ) =
              Fin.natAdd (n + 1) j0 by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        rw [hj] at hleft hright ⊢
        rw [hleft, hright, hend]
        exact hySteps j0
      · let k : Fin m := ⟨j.val - 1, by omega⟩
        have hj : k.succ = j.castSucc := by
          apply Fin.ext
          change (j.val - 1) + 1 = j.val
          exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)
        have hleft : z (Fin.natAdd n j.castSucc) = y k.succ := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j.castSucc) =
              Fin.natAdd (n + 1) k by
            apply Fin.ext
            simp [castNM, k]
            omega]
          simp [z0]
        have hright : z (Fin.natAdd n j.succ) = y j.succ := by
          dsimp [z]
          rw [show castNM (Fin.natAdd n j.succ) =
              Fin.natAdd (n + 1) j by
            apply Fin.ext
            simp [castNM]
            omega]
          simp [z0]
        rw [hleft, hright]
        simpa [hj] using hySteps j
  refine ⟨z, zLift, zstep, ⟨hzLift, hzMono, hzSteps⟩, ?_, ?_⟩
  · dsimp [z]
    rw [show castNM 0 = Fin.castAdd m (0 : Fin (n + 1)) by
      apply Fin.ext
      simp [castNM]
      ]
    simp [z0]
  · dsimp [z]
    let kLast : Fin m := ⟨m - 1, by omega⟩
    rw [show castNM (Fin.last (n + m)) =
        Fin.natAdd (n + 1) kLast by
      apply Fin.ext
      simp [castNM, kLast]
      omega]
    have hkLast : kLast.succ = Fin.last m := by
      apply Fin.ext
      simp [kLast]
      omega
    simp [z0, Fin.addCases_right, hkLast]

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private theorem source_boundary_cofinal
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) :
    ∀ z : ℝ, ∃ j : ℤ,
      P.boundary j ≤ z ∧ z < P.boundary (j + 1) := by
  let n : ℕ := P.numberOfBoundaryPoints
  have _hn : 0 < n := P.numberOfBoundaryPoints_pos
  let p : ℝ := P.period
  have _hp : 0 < p := P.period_pos
  have hshift : ∀ j : ℤ,
      P.boundary (j + Int.ofNat n) = P.boundary j + p := by
    simpa [n, p] using P.boundary_period
  intro z
  let b : ℝ := P.boundary 0
  let q : ℤ := ⌊(z - b) / p⌋
  have hqlo : (q : ℝ) ≤ (z - b) / p := Int.floor_le _
  have hqhi : (z - b) / p < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hshift' (r j : ℤ) :
      P.boundary (j + r * Int.ofNat n) = P.boundary j + (r : ℝ) * p := by
    simpa [n] using periodic_shift_iterate (f := P.boundary) (n := n)
      hshift r j
  have hlo : b + (q : ℝ) * p ≤ z := by
    have h := (le_div_iff₀ _hp).mp hqlo
    linarith
  have hhi : z < b + ((q : ℝ) + 1) * p := by
    have h := (div_lt_iff₀ _hp).mp hqhi
    linarith
  let Q : ℤ → Prop := fun j => z < P.boundary j
  have hQlower : ∀ k : ℤ, Q k → q * Int.ofNat n ≤ k := by
    intro k hk
    by_contra hnot
    have hlt : k < q * Int.ofNat n := lt_of_not_ge hnot
    have hboundary : P.boundary k < P.boundary (q * Int.ofNat n) := by
      apply P.boundary_strictMono
      simpa using hlt
    rw [show q * Int.ofNat n = 0 + q * Int.ofNat n by ring,
      hshift' q 0] at hboundary
    linarith
  have hQinh : ∃ k : ℤ, Q k := by
    refine ⟨(q + 1) * Int.ofNat n, ?_⟩
    change z < P.boundary ((q + 1) * Int.ofNat n)
    rw [show (q + 1) * Int.ofNat n = 0 + (q + 1) * Int.ofNat n by ring,
      hshift' (q + 1) 0]
    simpa [b] using hhi
  obtain ⟨k, hk, hkleast⟩ := Int.exists_least_of_bdd
    ⟨q * Int.ofNat n, hQlower⟩ hQinh
  have hnot : ¬ Q (k - 1) := by
    intro hprev
    have hle := hkleast (k - 1) hprev
    omega
  refine ⟨k - 1, ?_, ?_⟩
  · exact le_of_not_gt hnot
  · simpa using hk

private def sourceBand_globalSliceChainsSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
    ∀ᵐ q : ℝ ∂volume, ∀ a b : ℝ, a < b →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (step : Fin n → Sum ↥C.centres ℤ),
        x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
          IsSourceBandGlobalSliceChain C P q x xLift step

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private theorem source_global_segment
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) (q : ℝ)
    (hchains : ∀ j : ℤ, P.occupied j = true →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
          IsSourceBandSliceChain C q x xLift owner)
    (j : ℤ) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
      (xLift : Fin (n + 1) → C.coordinateSpace)
      (step : Fin n → Sum ↥C.centres ℤ),
      IsSourceBandGlobalSliceChain C P q x xLift step ∧
        x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) := by
  by_cases hj : P.occupied j = true
  · obtain ⟨n, _hn, x, xLift, owner, hx0, hxlast, hsource⟩ := hchains j hj
    let step : Fin n → Sum ↥C.centres ℤ := fun i => .inl (owner i)
    refine ⟨n, _hn, x, xLift, step, ?_, hx0, hxlast⟩
    rcases hsource with ⟨hLift, hmono, hsteps⟩
    refine ⟨hLift, hmono, ?_⟩
    intro i
    simp only [step]
    exact hsteps i
  · let x : Fin (1 + 1) → ℝ :=
      Fin.cases (P.boundary j) (fun _ => P.boundary (j + 1))
    let xLift : Fin (1 + 1) → C.coordinateSpace :=
      Fin.cases
        ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩
        (fun _ => ⟨P.boundary (j + 1),
          P.boundary_value_mem_coordinateSpace (j + 1)⟩)
    let step : Fin 1 → Sum ↥C.centres ℤ := fun _ => .inr j
    refine ⟨1, by omega, x, xLift, step, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun k => ?_) i
        · rfl
        · have hk : k = 0 := Subsingleton.elim _ _
          subst k
          rfl
      · apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change P.boundary j < P.boundary (j + 1)
        exact P.boundary_strictMono (show j < j + 1 by omega)
      · intro i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        change P.occupied j = false ∧
          P.boundary j = P.boundary j ∧
          P.boundary (j + 1) = P.boundary (j + 1)
        exact ⟨Bool.eq_false_of_not_eq_true hj, rfl, rfl⟩
    · simp [x]
    · change P.boundary (j + 1) = P.boundary (j + 1)
      rfl

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private theorem source_global_walk
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) (q : ℝ)
    (hsegments : ∀ j : ℤ,
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (step : Fin n → Sum ↥C.centres ℤ),
        IsSourceBandGlobalSliceChain C P q x xLift step ∧
          x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1))
    (j : ℤ) :
    ∀ m : ℕ, 0 < m →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (step : Fin n → Sum ↥C.centres ℤ),
        IsSourceBandGlobalSliceChain C P q x xLift step ∧
          x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + m) := by
  intro m hm
  induction m generalizing j with
  | zero => omega
  | succ m ih =>
      by_cases hm0 : m = 0
      · subst m
        simpa using hsegments j
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
        obtain ⟨n₁, _hn₁, x₁, xLift₁, step₁, h₁, hx₁₀, hx₁last⟩ :=
          ih j hmpos
        obtain ⟨n₂, _hn₂, x₂, xLift₂, step₂, h₂, hx₂₀, hx₂last⟩ :=
          hsegments (j + m)
        obtain ⟨z, zLift, zstep, hz, hz₀, hzlast⟩ :=
          append_source_global_chain h₁ h₂ _hn₂ (hx₁last.trans hx₂₀.symm)
        refine ⟨n₁ + n₂, ?_, z, zLift, zstep, hz, hz₀.trans hx₁₀, ?_⟩
        · exact Nat.add_pos_left _hn₁ _
        · simpa [Nat.cast_succ, add_assoc] using hzlast.trans hx₂last

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private theorem sourceBand_globalSliceChains_impl :
    sourceBand_globalSliceChainsSpec := by
  intro C P
  filter_upwards [sourceBand_chamberChains_unconditional_impl P] with q hq
  intro a b hab
  obtain ⟨ja, hja, haj⟩ := source_boundary_cofinal P a
  obtain ⟨jb, hjb, hbj⟩ := source_boundary_cofinal P b
  have hlast : P.boundary ja < P.boundary (jb + 1) := by
    exact lt_of_le_of_lt hja (lt_trans hab hbj)
  have hjlt : ja < jb + 1 :=
    P.boundary_strictMono.lt_iff_lt.mp hlast
  let d : ℤ := jb + 1 - ja
  have hdpos : 0 < d := by
    dsimp [d]
    omega
  have hdnonneg : 0 ≤ d := le_of_lt hdpos
  let m : ℕ := d.toNat
  have hmpos : 0 < m := by
    by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    have hd0 : d = 0 := by
      rw [← Int.toNat_of_nonneg hdnonneg]
      simp [m, hm0]
    linarith
  have hdm : (m : ℤ) = d := by
    simpa [m] using Int.toNat_of_nonneg hdnonneg
  have hjend : ja + (m : ℤ) = jb + 1 := by
    dsimp [d] at hdm
    linarith
  have hsegments : ∀ j : ℤ,
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (step : Fin n → Sum ↥C.centres ℤ),
        IsSourceBandGlobalSliceChain C P q x xLift step ∧
          x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) := by
    intro j
    exact source_global_segment P q (fun k hk => hq k hk) j
  obtain ⟨n, _hn, x, xLift, step, hwalk, hx0, hxlast⟩ :=
    source_global_walk P q hsegments ja m hmpos
  refine ⟨n, _hn, x, xLift, step, ?_, ?_, hwalk⟩
  · rw [hx0]
    exact hja
  · rw [hxlast, hjend]
    exact le_of_lt hbj

end Tiling.AxisParallel.Approximation


namespace Tiling.AxisParallel.Approximation
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
universe u
private def firstStageRunningMap {C : ApproximationContext}
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (_D : CoordinateDeformation C φ)
    (t : ↥C.centres) (x : ℝ) : ℝ :=
  mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ +
    _D.firstHomeomorph (x - t.1.re)

private def deformedBandBase {C : ApproximationContext} (P : PeriodicBandData C)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) : Set ℝ :=
  ⋃ j : {j : ℤ // P.occupied j = true},
    Ioo (P.deformedBoundary φ j.1) (P.deformedBoundary φ (j.1 + 1))
private theorem endpoint_formula
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (_D : CoordinateDeformation C φ) (v : Tiling.Plane)
    (_hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).re) :
    mapScalar φ xLift = _D.firstHomeomorph v.re +
      (mapFirstPoint φ (C.centrePoint t.1 t.2)).re := by
  let vr : C.coordinateSpace := ⟨v.re, C.vertex_re_mem v _hv⟩
  let tr : C.coordinateSpace := ⟨t.1.re, C.centre_re_mem t.1 t.2⟩
  have hxl : xLift = vr + tr := by
    apply Subtype.ext
    simp [vr, tr, hLift, hx]
  have hvertex := congrArg Complex.re (_D.first_vertex_agreement v _hv)
  have hvertex' : mapScalar φ vr = _D.firstHomeomorph v.re := by
    simpa [vr, mapFirstPoint, ApproximationContext.vertexPoint,
      _D.firstPlanarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((φ vr : ℚ) : ℝ) = mapScalar φ vr by rfl, hvertex']
  congr 1
  simp [tr, mapFirstPoint, mapScalar, ApproximationContext.centrePoint]

private theorem gap_transport
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (_D : CoordinateDeformation C φ) {q x₀ x₁ : ℝ}
    (xLift₀ xLift₁ : C.coordinateSpace) (t : ↥C.centres)
    (v w : Tiling.Plane) (_hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hlift₀ : (xLift₀ : ℝ) = x₀) (hlift₁ : (xLift₁ : ℝ) = x₁)
    (hleft : x₀ = (v + (t : Tiling.Plane)).re)
    (hright : x₁ = (w + (t : Tiling.Plane)).re)
    (hinside : {z : Tiling.Plane | z.im = q ∧ z.re ∈ Ioo x₀ x₁} ⊆
      (t : Tiling.Plane) +ᵥ C.region.openCarrier) :
    {z : Tiling.Plane | z.im = q ∧
      z.re ∈ Ioo (mapScalar φ xLift₀) (mapScalar φ xLift₁)} ⊆
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier := by
  intro z hz
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  rw [_D.firstRegion_openCarrier]
  let c := mapFirstPoint φ (C.centrePoint t.1 t.2)
  let r : ℝ := _D.firstHomeomorph.symm (z.re - c.re)
  let p : Tiling.Plane := (r : ℂ) + ((q - t.1.im : ℝ) : ℂ) * Complex.I
  have hend₀ := endpoint_formula _D v _hv t x₀ xLift₀ hlift₀ hleft
  have hend₁ := endpoint_formula _D w hw t x₁ xLift₁ hlift₁ hright
  have hzre : z.re ∈ Ioo (mapScalar φ xLift₀) (mapScalar φ xLift₁) := hz.2
  have hvr : v.re < r := by
    apply _D.firstHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzre.1, hend₀]
  have hrw : r < w.re := by
    apply _D.firstHomeomorph_strictMono.lt_iff_lt.mp
    simp only [r, Homeomorph.apply_symm_apply]
    linarith [hzre.2, hend₁]
  have _hp : p ∈ C.region.openCarrier := by
    have hs : (t : Tiling.Plane) + p ∈ {z : Tiling.Plane |
        z.im = q ∧ z.re ∈ Ioo x₀ x₁} := by
      constructor
      · simp [p]
      · rw [hleft, hright]
        simp only [p, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
          zero_mul, sub_zero]
        constructor <;> linarith
    have := hinside hs
    simpa only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
      neg_add_cancel_left] using this
  refine ⟨p, _hp, ?_⟩
  rw [_D.firstPlanarHomeomorph_apply]
  apply Complex.ext
  · simp [p, r, c]
    ring
  · have hzq : z.im = q := hz.1
    simp [p, mapFirstPoint, ApproximationContext.centrePoint, hzq]
    ring

private theorem deformedBoundary_strictMono_impl
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ) :
    StrictMono (P.deformedBoundary φ) := by
  obtain ⟨hperiod, hfund, _hgap, _hindexed⟩ :=
    periodicBandDeformation_preservesGapAlphabet P ε _hFine φ _hφ
  let n : ℤ := Int.ofNat P.numberOfBoundaryPoints
  let a : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have _hn : 0 < n := by
    dsimp [n]
    exact_mod_cast P.numberOfBoundaryPoints_pos
  have hperiod' (j : ℤ) :
      P.deformedBoundary φ (j + n) = P.deformedBoundary φ j + a := by
    simpa [n, a] using hperiod j
  let y : ℤ → ℝ := P.deformedBoundary φ
  let d : ℤ → ℝ := fun j => y (j + 1) - y j
  have hdperiod (j : ℤ) : d (j + n) = d j := by
    dsimp [d, y]
    rw [show (j + n) + 1 = (j + 1) + n by ring, hperiod' (j + 1),
      hperiod' j]
    ring
  have hdshift (q j : ℤ) : d (j + q * n) = d j := by
    induction q using Int.induction_on with
    | zero => simp
    | @succ q ih =>
        rw [show j + (q + 1) * n = (j + q * n) + n by ring,
          hdperiod (j + q * n)]
        exact ih
    | @pred q ih =>
        rw [← hdperiod (j + (-(q : ℤ) - 1) * n)]
        convert ih using 1
        · ring_nf
  have hsucc : ∀ j : ℤ, y j < y (j + 1) := by
    intro j
    let r : ℤ := j % n
    let q : ℤ := j / n
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg _ (ne_of_gt _hn)
    have hrn : r < n := by
      dsimp [r]
      exact Int.emod_lt_of_pos _ _hn
    let i : Fin P.numberOfBoundaryPoints :=
      ⟨r.toNat, by
        have : r.toNat < n.toNat := (Int.toNat_lt hr0).2 hrn
        simpa [n] using this⟩
    have hir : (i : ℤ) = r := by
      change (r.toNat : ℤ) = r
      exact Int.toNat_of_nonneg hr0
    have hj : j = (i : ℤ) + q * n := by
      have hdecomp : r + n * q = j := by
        exact Int.emod_add_mul_ediv j n
      rw [← hdecomp, ← hir]
      ring
    have hdj : d j = d (i : ℤ) := by
      rw [hj, hdshift]
    have hfund' : 0 < d (i : ℤ) := by
      dsimp [d, y]
      simpa using hfund i
    have : 0 < d j := by simpa [hdj] using hfund'
    exact sub_pos.mp this
  exact strictMono_int_of_lt_succ hsucc

private theorem sourceBand_globalSliceChain_transport_impl :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ) (q : ℝ) {n : ℕ}
      (x : Fin (n + 1) → ℝ)
      (xLift : Fin (n + 1) → C.coordinateSpace)
      (step : Fin n → Sum ↥C.centres ℤ),
      IsSourceBandGlobalSliceChain C P q x xLift step →
        StrictMono (fun i ↦ mapScalar φ (xLift i)) ∧
        ∀ i : Fin n,
          match step i with
          | .inl t =>
              {z : Tiling.Plane | z.im = q ∧
                z.re ∈ Ioo (mapScalar φ (xLift i.castSucc))
                  (mapScalar φ (xLift i.succ))} ⊆
                mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
                  _D.firstRegion.openCarrier
          | .inr _ =>
              Ioo (mapScalar φ (xLift i.castSucc))
                  (mapScalar φ (xLift i.succ)) ∩ deformedBandBase P φ = ∅ := by
  intro C P ε _hFine φ _hφ _D q n x xLift step hchain
  rcases hchain with ⟨hLift, hmono, hsteps⟩
  have hdeformed := deformedBoundary_strictMono_impl P ε _hFine φ _hφ
  constructor
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    cases hs : step i with
    | inl t =>
        obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ :=
          hs ▸ hsteps i
        have hvw : v.re < w.re := by
          have hpositive' : 0 < w.re - v.re := by simpa using hpositive
          linarith
        rw [endpoint_formula _D v _hv t (x i.castSucc) (xLift i.castSucc)
          (hLift i.castSucc) hleft,
          endpoint_formula _D w hw t (x i.succ) (xLift i.succ)
          (hLift i.succ) hright]
        simpa [add_comm] using
          (add_lt_add_right (_D.firstHomeomorph_strictMono hvw)
            (mapFirstPoint φ (C.centrePoint t.1 t.2)).re)
    | inr j =>
        have hstep := hs ▸ hsteps i
        have hleft : x i.castSucc = P.boundary j := hstep.2.1
        have hright : x i.succ = P.boundary (j + 1) := hstep.2.2
        have hxl : xLift i.castSucc =
            ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩ := by
          apply Subtype.ext
          simp [hLift i.castSucc, hleft]
        have hxr : xLift i.succ =
            ⟨P.boundary (j + 1), P.boundary_value_mem_coordinateSpace (j + 1)⟩ := by
          apply Subtype.ext
          simp [hLift i.succ, hright]
        rw [hxl, hxr]
        exact hdeformed (by omega)
  · intro i
    cases hs : step i with
    | inl t =>
        obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ :=
          hs ▸ hsteps i
        exact gap_transport _D (xLift i.castSucc) (xLift i.succ) t v w _hv hw
          (hLift i.castSucc) (hLift i.succ) hleft hright hinside
    | inr j =>
        have hstep := hs ▸ hsteps i
        have hocc : P.occupied j = false := hstep.1
        have hleft : xLift i.castSucc =
            ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩ := by
          apply Subtype.ext
          simp [hLift i.castSucc, hstep.2.1]
        have hright : xLift i.succ =
            ⟨P.boundary (j + 1), P.boundary_value_mem_coordinateSpace (j + 1)⟩ := by
          apply Subtype.ext
          simp [hLift i.succ, hstep.2.2]
        rw [hleft, hright]
        change Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) ∩
          deformedBandBase P φ = ∅
        apply Set.Subset.antisymm
        · intro z hz
          exfalso
          rw [deformedBandBase] at hz
          rcases Set.mem_iUnion.mp hz.2 with ⟨k, hk⟩
          have hkj : k.1 < j + 1 :=
            (hdeformed.lt_iff_lt.mp (hk.1.trans hz.1.2))
          have hjk : j < k.1 + 1 :=
            (hdeformed.lt_iff_lt.mp (hz.1.1.trans hk.2))
          have hEq : k.1 = j := by omega
          have htrue : P.occupied j = true := by simpa [hEq] using k.2
          have hfalseTrue : (false : Bool) = true := hocc.symm.trans htrue
          cases hfalseTrue
        · exact Set.empty_subset _

end Tiling.AxisParallel.Approximation

namespace Tiling.AxisParallel.Approximation
open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains
universe u

private def firstStage_properCylinderSlicesSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ),
    (∀ t : ↥C.centres,
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier ⊆
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) ∧
    (∀ s t : ↥C.centres, s ≠ t →
      Disjoint
        (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier)
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier)) ∧
    (∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      (x ∈ deformedBandBase P φ ↔
        ∃ t : ↥C.centres,
          slicePoint Axis.horizontal q x ∈
            mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
              _D.firstRegion.openCarrier))

private def periodicBand_firstStageTilesOnSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ),
    ∃ T₁ : ↥C.centres ↪ Tiling.Plane,
      (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) ∧
      TilesOn _D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}

private def placedAxisSlice (K : Region) (t : Tiling.Plane)
    (axis : Axis) (q : ℝ) : Set ℝ :=
  {x | slicePoint axis q x ∈ t +ᵥ K.openCarrier}

private def firstStage_globalGenericSliceOrderSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ),
    ∀ᵐ q : ℝ ∂volume, ∀ s t : ↥C.centres, ∀ x y : ℝ,
      x ∈ placedAxisSlice C.region s.1 Axis.horizontal q →
      y ∈ placedAxisSlice C.region t.1 Axis.horizontal q →
      x < y → firstStageRunningMap φ _D s x < firstStageRunningMap φ _D t y

private def firstStageCentreMap_injectiveSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ),
    Function.Injective
      (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2))

private def firstStage_properCylinderSlices_parameterizedSpec : Prop :=
  firstStage_globalGenericSliceOrderSpec.{u} →
    firstStageCentreMap_injectiveSpec.{u} →
      firstStage_properCylinderSlicesSpec.{u}

private theorem firstStage_allSectionComponents_transport_impl :
    ∀ {C : ApproximationContext.{u}}
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (_D : CoordinateDeformation C φ)
      (t : ↥C.centres) (q : ℝ),
      placedAxisSlice _D.firstRegion
          (mapFirstPoint φ (C.centrePoint t.1 t.2)) Axis.horizontal q =
        firstStageRunningMap φ _D t ''
          placedAxisSlice C.region t.1 Axis.horizontal q := by
  intro C φ _D t q
  let c : Tiling.Plane := mapFirstPoint φ (C.centrePoint t.1 t.2)
  let tr : C.coordinateSpace := ⟨t.1.re, C.centre_re_mem t.1 t.2⟩
  have hc_re : c.re = mapScalar φ tr := by
    simp [c, tr, mapFirstPoint, ApproximationContext.centrePoint]
  have hc_im : c.im = t.1.im := by
    simp [c, mapFirstPoint, ApproximationContext.centrePoint]
  have hpoint (x : ℝ) (k : Tiling.Plane)
      (hk : k = -t.1 + slicePoint Axis.horizontal q x) :
      slicePoint Axis.horizontal q (firstStageRunningMap φ _D t x) =
        c + _D.firstPlanarHomeomorph k := by
    rw [_D.firstPlanarHomeomorph_apply]
    apply Complex.ext
    · simp only [slicePoint, firstStageRunningMap, c, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, Complex.ofReal_im, zero_mul, sub_zero, hc_re]
      have hkre : k.re = x - t.1.re := by
        simp [hk, slicePoint]
        ring
      rw [hkre]
      ring
    · simp only [slicePoint, firstStageRunningMap, c, Complex.add_im,
        Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, Complex.ofReal_im, zero_mul, hc_im]
      have hkim : k.im = q - t.1.im := by
        simp [hk, slicePoint]
        ring
      rw [hkim]
      ring
  ext x
  constructor
  · intro hx
    change slicePoint Axis.horizontal q x ∈
      c +ᵥ _D.firstRegion.openCarrier at hx
    have hk0 : -c + slicePoint Axis.horizontal q
        x ∈ _D.firstRegion.openCarrier := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      exact hx
    rw [_D.firstRegion_openCarrier] at hk0
    obtain ⟨k, hk, hkmap⟩ := hk0
    have hmapre : _D.firstHomeomorph k.re = x - c.re := by
      have := congrArg Complex.re hkmap
      simp only [_D.firstPlanarHomeomorph_apply, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        mul_zero, Complex.ofReal_im, zero_mul, sub_zero] at this
      calc
        _D.firstHomeomorph k.re = -c.re + x := by simpa [c, slicePoint] using this
        _ = x - c.re := by ring
    have hkim : k.im = q - t.1.im := by
      have := congrArg Complex.im hkmap
      simp only [_D.firstPlanarHomeomorph_apply, Complex.add_im,
        Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, Complex.ofReal_im, zero_mul] at this
      calc
        k.im = -c.im + q := by simpa [c, slicePoint] using this
        _ = q - t.1.im := by rw [hc_im]; ring
    let x₀ : ℝ := t.1.re + k.re
    have hsource : slicePoint Axis.horizontal q x₀ = t.1 + k := by
      apply Complex.ext
      · simp [slicePoint, x₀]
      · simp [slicePoint, hkim]
    have hmap : firstStageRunningMap φ _D t x₀ = x := by
      simp only [firstStageRunningMap, x₀]
      rw [show x₀ - t.1.re = k.re by simp [x₀]]
      rw [hmapre, hc_re]
      ring
    refine ⟨x₀, ?_, hmap⟩
    change slicePoint Axis.horizontal q x₀ ∈ t.1 +ᵥ C.region.openCarrier
    rw [hsource]
    exact ⟨k, hk, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change slicePoint Axis.horizontal q (firstStageRunningMap φ _D t x) ∈
      c +ᵥ _D.firstRegion.openCarrier
    have hk : -t.1 + slicePoint Axis.horizontal q x ∈ C.region.openCarrier := by
      change slicePoint Axis.horizontal q x ∈ t.1 +ᵥ C.region.openCarrier at hx
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hx
      exact hx
    rw [hpoint x (-t.1 + slicePoint Axis.horizontal q x) rfl]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, _D.firstRegion_openCarrier]
    simp only [vadd_eq_add, neg_add_cancel_left]
    exact ⟨-t.1 + slicePoint Axis.horizontal q x, hk, rfl⟩

private theorem source_openUnion_subset_base
    {C : ApproximationContext.{u}} (P : PeriodicBandData C) :
    openUnion C.region C.centres ⊆
      {z : Tiling.Plane | z.re ∈ P.base} := by
  have hDopen : IsOpen ({z : Tiling.Plane | z.re ∈ P.base} : Set Tiling.Plane) :=
    P.base_open.preimage Complex.continuous_re
  have hDregular : interior (closure ({z : Tiling.Plane | z.re ∈ P.base} :
      Set Tiling.Plane)) = {z : Tiling.Plane | z.re ∈ P.base} := by
    change interior (closure (Complex.re ⁻¹' P.base)) = Complex.re ⁻¹' P.base
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re,
      P.base_regular]
  have htiles : TilesOn C.region C.centres
      {z : Tiling.Plane | z.re ∈ P.base} := by
    simpa [P.target_eq] using P.source_tilesOn
  have hsupp := regularSupport_eq_of_tilesOn hDopen hDregular htiles
  have hopen : IsOpen (openUnion C.region C.centres) := by
    rw [openUnion]
    exact isOpen_iUnion fun _ => C.region.openCarrier_regularOpen.1.vadd _
  intro z hz
  rw [← hsupp]
  rw [regularSupport]
  exact interior_maximal subset_closure hopen hz

private theorem mapScalar_range_countable
    {C : ApproximationContext.{u}}
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) :
    (Set.range (mapScalar φ)).Countable := by
  apply (Set.countable_range (fun r : ℚ => (r : ℝ))).mono
  rintro y ⟨x, rfl⟩
  exact ⟨φ x, rfl⟩

private theorem exists_mem_Ioo_avoiding_finset_local {a b : ℝ} (hab : a < b)
    (F : Finset ℝ) : ∃ x ∈ Ioo a b, x ∉ F := by
  by_contra h
  push Not at h
  have hsub : Ioo a b ⊆ (F : Set ℝ) := fun x hx => h x hx
  exact Set.Ioo_infinite hab ((F.finite_toSet).subset hsub)

private theorem source_occupied_chamber_of_mem_base
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    {r : ℝ} (hr : r ∈ P.base) :
    ∃ j : ℤ, P.occupied j = true ∧
      r ∈ Ioo (P.boundary j) (P.boundary (j + 1)) := by
  obtain ⟨j, hjl, hjr⟩ := source_boundary_cofinal P r
  have hjlt : P.boundary j < r := by
    rcases hjl.lt_or_eq with h | h
    · exact h
    · exfalso
      have hjfront : P.boundary j ∈ frontier P.base := by
        rw [← P.boundary_range]
        exact ⟨j, rfl⟩
      exact Set.disjoint_left.1 disjoint_interior_frontier
        (mem_interior_iff_mem_nhds.mpr (P.base_open.mem_nhds hr))
        (h ▸ hjfront)
  have hfront : Disjoint (Ioo (P.boundary j) (P.boundary (j + 1)))
      (frontier P.base) := by
    rw [Set.disjoint_left]
    intro z hz hzf
    obtain ⟨k, rfl⟩ := P.boundary_range ▸ hzf
    have hjk : j < k :=
      (P.boundary_strictMono.lt_iff_lt).mp hz.1
    have hkj : k < j + 1 :=
      (P.boundary_strictMono.lt_iff_lt).mp hz.2
    omega
  have hsub : Ioo (P.boundary j) (P.boundary (j + 1)) ⊆ interior P.base :=
    Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
      isPreconnected_Ioo hfront ⟨hjlt, hjr⟩ hr
  refine ⟨j, (P.occupied_iff j).2 (hsub.trans interior_subset), ⟨hjlt, hjr⟩⟩

private theorem deformed_boundary_cofinal_pre
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ) :
    ∀ z : ℝ, ∃ j : ℤ,
      P.deformedBoundary φ j ≤ z ∧ z < P.deformedBoundary φ (j + 1) := by
  obtain ⟨hperiod, _hfund, _hgap, _hindexed⟩ :=
    periodicBandDeformation_preservesGapAlphabet P ε _hFine φ _hφ
  let n : ℤ := Int.ofNat P.numberOfBoundaryPoints
  have _hn : 0 < n := by
    dsimp [n]
    exact_mod_cast P.numberOfBoundaryPoints_pos
  let p : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have _hp : 0 < p := by
    have hm := deformedBoundary_strictMono_impl P ε _hFine φ _hφ
    have hh := hm (show (0 : ℤ) < n by exact_mod_cast _hn)
    have hh' : P.deformedBoundary φ n =
        P.deformedBoundary φ 0 + p := by
      simpa [n, p] using hperiod 0
    rw [hh'] at hh
    linarith
  have hshift : ∀ j : ℤ,
      P.deformedBoundary φ (j + n) =
        P.deformedBoundary φ j + p := by
    simpa [n, p] using hperiod
  have hshift' (r j : ℤ) :
      P.deformedBoundary φ (j + r * n) =
        P.deformedBoundary φ j + (r : ℝ) * p := by
    simpa [n] using periodic_shift_iterate
      (f := P.deformedBoundary φ) (n := P.numberOfBoundaryPoints) (p := p)
      hshift r j
  intro z
  let b : ℝ := P.deformedBoundary φ 0
  let q : ℤ := ⌊(z - b) / p⌋
  have hqlo : (q : ℝ) ≤ (z - b) / p := Int.floor_le _
  have hqhi : (z - b) / p < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hlo : b + (q : ℝ) * p ≤ z := by
    have h := (le_div_iff₀ _hp).mp hqlo
    linarith
  have hhi : z < b + ((q : ℝ) + 1) * p := by
    have h := (div_lt_iff₀ _hp).mp hqhi
    linarith
  let Q : ℤ → Prop := fun j => z < P.deformedBoundary φ j
  have hQlower : ∀ k : ℤ, Q k → q * n ≤ k := by
    intro k hk
    by_contra hnot
    have hlt : k < q * n := lt_of_not_ge hnot
    have hboundary : P.deformedBoundary φ k <
        P.deformedBoundary φ (q * n) :=
      (deformedBoundary_strictMono_impl P ε _hFine φ _hφ) hlt
    rw [show q * n = 0 + q * n by ring, hshift' q 0] at hboundary
    linarith
  have hQinh : ∃ k : ℤ, Q k := by
    refine ⟨(q + 1) * n, ?_⟩
    change z < P.deformedBoundary φ ((q + 1) * n)
    rw [show (q + 1) * n = 0 + (q + 1) * n by ring, hshift' (q + 1) 0]
    simpa [b] using hhi
  obtain ⟨k, hk, hkleast⟩ := Int.exists_least_of_bdd
    ⟨q * n, hQlower⟩ hQinh
  have hnot : ¬ Q (k - 1) := by
    intro hprev
    have hle := hkleast (k - 1) hprev
    omega
  refine ⟨k - 1, ?_, ?_⟩
  · exact le_of_not_gt hnot
  · simpa using hk


private theorem strictMono_exists_gap {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) {a : ℝ} (hleft : x 0 < a)
    (hright : a < x (Fin.last n)) (hne : ∀ k, a ≠ x k) :
    ∃ i : Fin n, a ∈ Ioo (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => exfalso; simpa using (lt_asymm hleft hright)
  | succ n ih =>
      rcases lt_trichotomy a (x 1) with ha | ha | ha
      · exact ⟨⟨0, Nat.succ_pos _⟩, hleft, ha⟩
      · exact False.elim (hne 1 ha)
      · let y : Fin (n + 1) → ℝ := fun k => x k.succ
        have hy : StrictMono y := by
          intro i j hij
          apply hx
          simpa using hij
        have hylast : a < y (Fin.last n) := by
          simpa [y] using hright
        have hyne : ∀ k, a ≠ y k := fun k => hne k.succ
        obtain ⟨i, hi⟩ := ih y hy ha hylast hyne
        refine ⟨i.succ, ?_⟩
        simpa [y] using hi

private theorem firstStage_forward_slice_ae_of_globalOrder
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ)
    (hOrder : firstStage_globalGenericSliceOrderSpec.{u}) :
    ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
      x ∈ deformedBandBase P φ →
        ∃ t : ↥C.centres,
          slicePoint Axis.horizontal q x ∈
            mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
              _D.firstRegion.openCarrier := by
  have havoid : ∀ᵐ x : ℝ ∂volume,
      x ∉ Set.range (mapScalar φ) :=
    (mapScalar_range_countable φ).ae_notMem volume
  filter_upwards [hOrder P ε _hFine φ _hφ _D,
    sourceBand_chamberChains_unconditional_impl P] with q hqOrder hqCh
  filter_upwards [havoid] with x hxavoid
  intro hxbase
  obtain ⟨j, hjlo, hjhi⟩ := deformed_boundary_cofinal_pre P ε _hFine φ _hφ x
  have hjl : P.deformedBoundary φ j < x := by
    rcases hjlo.lt_or_eq with hjlt | hjeq
    · exact hjlt
    · exfalso
      apply hxavoid
      refine ⟨⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩, ?_⟩
      simpa [PeriodicBandData.deformedBoundary, hjeq]
  have hjr : x < P.deformedBoundary φ (j + 1) := hjhi
  have hsourcegap : P.boundary j < P.boundary (j + 1) :=
    P.boundary_strictMono (by omega)
  obtain ⟨n, _hn, y, yLift, step, hchain, hy0, hylast⟩ :=
    source_global_segment P q (fun k hk => hqCh k hk) j
  have htrans := sourceBand_globalSliceChain_transport_impl P ε _hFine φ _hφ _D q
    y yLift step hchain
  have hy0' : yLift 0 =
      ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩ := by
    apply Subtype.ext
    simp [hy0, hchain.1 0]
  have hylast' : yLift (Fin.last n) =
      ⟨P.boundary (j + 1), P.boundary_value_mem_coordinateSpace (j + 1)⟩ := by
    apply Subtype.ext
    simp [hylast, hchain.1 (Fin.last n)]
  have hleft : mapScalar φ (yLift 0) < x := by
    rw [hy0']
    simpa [PeriodicBandData.deformedBoundary] using hjl
  have hright : x < mapScalar φ (yLift (Fin.last n)) := by
    rw [hylast']
    simpa [PeriodicBandData.deformedBoundary] using hjr
  have hpne : ∀ k, x ≠ mapScalar φ (yLift k) := by
    intro k hk
    apply hxavoid
    exact ⟨yLift k, hk.symm⟩
  obtain ⟨i, hi⟩ := strictMono_exists_gap
    (fun k => mapScalar φ (yLift k)) htrans.1 hleft hright hpne
  cases hs : step i with
  | inl t =>
      refine ⟨t, ?_⟩
      have hz : slicePoint Axis.horizontal q x ∈
          {z : Tiling.Plane | z.im = q ∧ z.re ∈
            Ioo (mapScalar φ (yLift i.castSucc))
              (mapScalar φ (yLift i.succ))} := by
        exact ⟨by simp [slicePoint], by simpa [slicePoint] using hi⟩
      exact (hs ▸ htrans.2 i) hz
  | inr k =>
      have hempty : Ioo (mapScalar φ (yLift i.castSucc))
          (mapScalar φ (yLift i.succ)) ∩ deformedBandBase P φ = ∅ := by
        simpa [hs] using htrans.2 i
      have hz : x ∈ Ioo (mapScalar φ (yLift i.castSucc))
          (mapScalar φ (yLift i.succ)) ∩ deformedBandBase P φ :=
        ⟨hi, hxbase⟩
      rw [hempty] at hz
      exact hz.elim



end Tiling.AxisParallel.Approximation

namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private def periodicAffineInterpolationSpec : Prop :=
  ∀ (n : ℕ) (p q : ℝ) (x y : ℤ → ℝ),
    0 < n → 0 < p → 0 < q →
    StrictMono x → StrictMono y →
    (∀ j : ℤ, x (j + Int.ofNat n) = x j + p) →
    (∀ j : ℤ, y (j + Int.ofNat n) = y j + q) →
    (∀ z : ℝ, ∃ j : ℤ, x j ≤ z ∧ z < x (j + 1)) →
    (∀ z : ℝ, ∃ j : ℤ, y j ≤ z ∧ z < y (j + 1)) →
    ∃ H : ℝ ≃ₜ ℝ,
      StrictMono H ∧
      (∀ j : ℤ, H (x j) = y j) ∧
      (∀ z : ℝ, H (z + p) = H z + q)

private theorem periodicAffineInterpolation_core :
    periodicAffineInterpolationSpec := by
  intro n p q x y hn hp hq hx hy hxp hyp hxc hyc
  exact Tiling.AxisParallel.Approximation.exists_periodic_strictMonoHomeomorph_extension
    n p q x y hn hp hq hx hy hxp hyp hxc hyc

private theorem periodicAffineInterpolation_proof :
    periodicAffineInterpolationSpec := periodicAffineInterpolation_core


private def periodicBoundaryHomeomorph_existsSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ),
    ∃ H : ℝ ≃ₜ ℝ,
      StrictMono H ∧
      (∀ j : ℤ, H (P.boundary j) = P.deformedBoundary φ j) ∧
      (∀ x : ℝ, H (x + P.period) = H x +
        mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩)

theorem periodic_strictMono_cofinal {f : ℤ → ℝ} {n : ℕ} {p : ℝ}
    (_hn : 0 < n) (_hp : 0 < p) (hf : StrictMono f)
    (hshift : ∀ j : ℤ, f (j + Int.ofNat n) = f j + p) :
    ∀ z : ℝ, ∃ j : ℤ, f j ≤ z ∧ z < f (j + 1) := by
  intro z
  let nz : ℤ := Int.ofNat n
  let b : ℝ := f 0
  let q : ℤ := ⌊(z - b) / p⌋
  have hqlo : (q : ℝ) ≤ (z - b) / p := Int.floor_le _
  have hqhi : (z - b) / p < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hqlo' : b + (q : ℝ) * p ≤ z := by
    have h := (le_div_iff₀ _hp).mp hqlo
    linarith
  have hqhi' : z < b + ((q : ℝ) + 1) * p := by
    have h := (div_lt_iff₀ _hp).mp hqhi
    linarith
  have hshift' (r j : ℤ) :
      f (j + r * nz) = f j + (r : ℝ) * p := by
    simpa [nz] using periodic_shift_iterate (f := f) (n := n) hshift r j
  let Q : ℤ → Prop := fun k => z < f k
  have hQlower : ∀ k : ℤ, Q k → q * nz ≤ k := by
    intro k hk
    by_contra hnot
    have hlt : k < q * nz := lt_of_not_ge hnot
    have hboundary : f k < f (q * nz) := by
      apply hf
      simpa using hlt
    rw [show q * nz = 0 + q * nz by ring, hshift' q 0] at hboundary
    linarith
  have hQinh : ∃ k : ℤ, Q k := by
    refine ⟨(q + 1) * nz, ?_⟩
    change z < f ((q + 1) * nz)
    rw [show (q + 1) * nz = 0 + (q + 1) * nz by ring,
      hshift' (q + 1) 0]
    simpa using hqhi'
  obtain ⟨k, hk, hkleast⟩ := Int.exists_least_of_bdd ⟨q * nz, hQlower⟩ hQinh
  have hnot : ¬ Q (k - 1) := by
    intro hprev
    have hle := hkleast (k - 1) hprev
    omega
  refine ⟨k - 1, ?_, ?_⟩
  · exact le_of_not_gt hnot
  · simpa using hk

private theorem deformedBoundary_strictMono_impl_geometry_copy
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ) :
    StrictMono (P.deformedBoundary φ) := by
  obtain ⟨hperiod, hfund, _hgap, _hindexed⟩ :=
    periodicBandDeformation_preservesGapAlphabet P ε _hFine φ _hφ
  let n : ℤ := Int.ofNat P.numberOfBoundaryPoints
  let a : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have _hn : 0 < n := by
    dsimp [n]
    exact_mod_cast P.numberOfBoundaryPoints_pos
  have hperiod' (j : ℤ) :
      P.deformedBoundary φ (j + n) = P.deformedBoundary φ j + a := by
    simpa [n, a] using hperiod j
  let y : ℤ → ℝ := P.deformedBoundary φ
  let d : ℤ → ℝ := fun j => y (j + 1) - y j
  have hdperiod (j : ℤ) : d (j + n) = d j := by
    dsimp [d, y]
    rw [show (j + n) + 1 = (j + 1) + n by ring,
      hperiod' (j + 1), hperiod' j]
    ring
  have hdshift (q j : ℤ) : d (j + q * n) = d j := by
    induction q using Int.induction_on with
    | zero => simp
    | @succ q ih =>
        rw [show j + (q + 1) * n = (j + q * n) + n by ring,
          hdperiod (j + q * n)]
        exact ih
    | @pred q ih =>
        rw [← hdperiod (j + (-(q : ℤ) - 1) * n)]
        convert ih using 1
        ring_nf
  have hsucc : ∀ j : ℤ, y j < y (j + 1) := by
    intro j
    let r : ℤ := j % n
    let q : ℤ := j / n
    have hr0 : 0 ≤ r := by
      dsimp [r]
      exact Int.emod_nonneg _ (ne_of_gt _hn)
    have hrn : r < n := by
      dsimp [r]
      exact Int.emod_lt_of_pos _ _hn
    let i : Fin P.numberOfBoundaryPoints :=
      ⟨r.toNat, by
        have : r.toNat < n.toNat := (Int.toNat_lt hr0).2 hrn
        simpa [n] using this⟩
    have hir : (i : ℤ) = r := by
      change (r.toNat : ℤ) = r
      exact Int.toNat_of_nonneg hr0
    have hj : j = (i : ℤ) + q * n := by
      have hdecomp : r + n * q = j := Int.emod_add_mul_ediv j n
      rw [← hdecomp, ← hir]
      ring_nf
    have hdj : d j = d (i : ℤ) := by
      rw [hj, hdshift]
    have hfund' : 0 < d (i : ℤ) := by
      dsimp [d, y]
      simpa using hfund i
    have : 0 < d j := by simpa [hdj] using hfund'
    exact sub_pos.mp this
  exact strictMono_int_of_lt_succ hsucc

private theorem periodicBoundaryHomeomorph_exists_impl :
    periodicBoundaryHomeomorph_existsSpec := by
  intro C P ε _hFine φ _hφ
  obtain ⟨hperiod, _hfund, _hgap, _hindexed⟩ :=
    periodicBandDeformation_preservesGapAlphabet P ε _hFine φ _hφ
  let n : ℕ := P.numberOfBoundaryPoints
  let p : ℝ := P.period
  let q : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have _hn : 0 < n := P.numberOfBoundaryPoints_pos
  have _hp : 0 < p := by simpa [p] using P.period_pos
  have hxs : ∀ j : ℤ, P.boundary (j + Int.ofNat n) = P.boundary j + p := by
    simpa [n, p] using P.boundary_period
  have hys : ∀ j : ℤ,
      P.deformedBoundary φ (j + Int.ofNat n) =
        P.deformedBoundary φ j + q := by
    simpa [n, q] using hperiod
  have hy : StrictMono (P.deformedBoundary φ) :=
    deformedBoundary_strictMono_impl P ε _hFine φ _hφ
  have hq : 0 < q := by
    have hlt : P.deformedBoundary φ 0 < P.deformedBoundary φ (0 + Int.ofNat n) := by
      apply hy
      have hz : (0 : ℤ) < Int.ofNat n := by
        change (0 : ℤ) < (n : ℤ)
        exact_mod_cast _hn
      simpa only [zero_add] using hz
    rw [hys 0] at hlt
    linarith
  have hxc : ∀ z : ℝ, ∃ j : ℤ,
      P.boundary j ≤ z ∧ z < P.boundary (j + 1) :=
    periodic_strictMono_cofinal (f := P.boundary) _hn _hp P.boundary_strictMono hxs
  have hyc : ∀ z : ℝ, ∃ j : ℤ,
      P.deformedBoundary φ j ≤ z ∧ z < P.deformedBoundary φ (j + 1) :=
    periodic_strictMono_cofinal (f := P.deformedBoundary φ) _hn hq hy hys
  obtain ⟨H, hHmono, hHknots, hHperiod⟩ :=
    periodicAffineInterpolation_proof n p q P.boundary (P.deformedBoundary φ)
      _hn _hp hq P.boundary_strictMono hy hxs hys hxc hyc
  refine ⟨H, hHmono, hHknots, ?_⟩
  simpa [p, q] using hHperiod

private def deformedBandBase_eq_imageSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (H : ℝ ≃ₜ ℝ),
    StrictMono H →
    (∀ j : ℤ, H (P.boundary j) = P.deformedBoundary φ j) →
      deformedBandBase P φ = H '' P.base

private theorem deformedBandBase_eq_image_impl : deformedBandBase_eq_imageSpec := by
  intro C P φ H hH hHboundary
  let n : ℤ := Int.ofNat P.numberOfBoundaryPoints
  let p : ℝ := P.period
  have _hn : 0 < n := by
    dsimp [n]
    exact_mod_cast P.numberOfBoundaryPoints_pos
  have _hp : 0 < p := P.period_pos
  have hshift : ∀ (q j : ℤ),
      P.boundary (j + q * n) = P.boundary j + q * p := by
    intro q
    induction q using Int.induction_on with
    | zero => intro j; simp
    | @succ q ih =>
        intro j
        rw [show j + (q + 1) * n = (j + q * n) + n by ring,
          show n = Int.ofNat P.numberOfBoundaryPoints by rfl,
          P.boundary_period (j + q * n), ih]
        push_cast
        ring
    | @pred q ih =>
        intro j
        have hprev := P.boundary_period (j + (-(q : ℤ) - 1) * n)
        have hprev' :
            P.boundary (j + (-(q : ℤ) - 1) * n) =
              P.boundary (j + (-(q : ℤ)) * n) - p := by
          rw [show n = Int.ofNat P.numberOfBoundaryPoints by rfl] at hprev
          rw [show j + (-(q : ℤ) - 1) * n + n =
            j + (-(q : ℤ)) * n by ring] at hprev
          dsimp [p]
          linarith
        rw [show j + (-(q : ℤ) - (1 : ℤ)) * n =
          j + (-(q : ℤ) - 1) * n by ring, hprev']
        rw [ih]
        push_cast
        ring
  have hcofinal : ∀ x : ℝ, ∃ j : ℤ,
      P.boundary j ≤ x ∧ x < P.boundary (j + 1) := by
    intro x
    let b : ℝ := P.boundary 0
    let q : ℤ := ⌊(x - b) / p⌋
    have hqlo : (q : ℝ) ≤ (x - b) / p := by
      exact Int.floor_le _
    have hqhi : (x - b) / p < (q : ℝ) + 1 := by
      exact Int.lt_floor_add_one _
    have hqlo'' : (q : ℝ) * p ≤ x - b := (le_div_iff₀ _hp).mp hqlo
    have hqlo' : b + (q : ℝ) * p ≤ x := by
      linarith
    have hqhi'' : x - b < ((q : ℝ) + 1) * p := (div_lt_iff₀ _hp).mp hqhi
    have hqhi' : x < b + ((q : ℝ) + 1) * p := by
      linarith
    let Q : ℤ → Prop := fun k => x < P.boundary k
    have hQlower : ∀ k : ℤ, Q k → q * n ≤ k := by
      intro k hk
      by_contra hnot
      have hlt : k < q * n := lt_of_not_ge hnot
      have hboundary : P.boundary k < P.boundary (q * n) :=
        P.boundary_strictMono hlt
      rw [show q * n = 0 + q * n by ring, hshift q 0] at hboundary
      linarith
    have hQinh : ∃ k : ℤ, Q k := by
      refine ⟨(q + 1) * n, ?_⟩
      change x < P.boundary ((q + 1) * n)
      rw [show (q + 1) * n = 0 + (q + 1) * n by ring,
        hshift (q + 1) 0]
      simpa using hqhi'
    obtain ⟨k, hk, hkleast⟩ := Int.exists_least_of_bdd ⟨q * n, hQlower⟩ hQinh
    have hnot : ¬ Q (k - 1) := by
      intro hprev
      have hle := hkleast (k - 1) hprev
      omega
    refine ⟨k - 1, ?_, ?_⟩
    · exact le_of_not_gt hnot
    · simpa using hk
  have hbase_union : P.base = ⋃ j : {j : ℤ // P.occupied j = true},
      Ioo (P.boundary j.1) (P.boundary (j.1 + 1)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hjl, hjr⟩ := hcofinal x
      have hxint : x ∈ interior P.base :=
        mem_interior_iff_mem_nhds.mpr (P.base_open.mem_nhds hx)
      have hjl' : P.boundary j < x := by
        rcases hjl.lt_or_eq with hjlt | hj_eq
        · exact hjlt
        · exfalso
          have hjfront : P.boundary j ∈ frontier P.base := by
            rw [← P.boundary_range]
            exact ⟨j, rfl⟩
          exact Set.disjoint_left.1 disjoint_interior_frontier hxint
            (hj_eq ▸ hjfront)
      have hjfront : Disjoint (Ioo (P.boundary j) (P.boundary (j + 1)))
          (frontier P.base) := by
        rw [disjoint_left]
        intro y hy hfront
        obtain ⟨k, hk⟩ := P.boundary_range ▸ hfront
        have hkj : j < k := (P.boundary_strictMono.lt_iff_lt).mp (by simpa [hk] using hy.1)
        have hkj' : k < j + 1 :=
          (P.boundary_strictMono.lt_iff_lt).mp (by simpa [hk] using hy.2)
        omega
      have hsubset : Ioo (P.boundary j) (P.boundary (j + 1)) ⊆ interior P.base :=
        Tiling.IsPreconnected.subset_interior_of_disjoint_frontier_of_mem
          isPreconnected_Ioo hjfront ⟨hjl', hjr⟩ hx
      have hocc : P.occupied j = true := by
        apply (P.occupied_iff j).2
        exact hsubset.trans interior_subset
      exact mem_iUnion.mpr ⟨⟨j, hocc⟩, ⟨hjl', hjr⟩⟩
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact (P.occupied_iff j.1).1 j.2 hj
  have hHmono : Monotone H := hH.monotone
  have hHsymm : StrictMono H.symm := by
    intro a b hab
    apply lt_of_not_ge
    intro hle
    have : b ≤ a := by
      simpa using hHmono hle
    exact (not_le_of_gt hab) this
  let E : ℝ ≃o ℝ := H.toEquiv.toOrderIso hHmono hHsymm.monotone
  rw [deformedBandBase, hbase_union, image_iUnion]
  apply iUnion_congr
  intro j
  change Ioo (P.deformedBoundary φ j.1) (P.deformedBoundary φ (j.1 + 1)) =
    E '' Ioo (P.boundary j.1) (P.boundary (j.1 + 1))
  rw [E.image_Ioo]
  have hEj (k : ℤ) : E (P.boundary k) = P.deformedBoundary φ k := by
    change H (P.boundary k) = P.deformedBoundary φ k
    exact hHboundary k
  rw [hEj, hEj]

private def deformedBandBase_geometrySpec : Prop :=
  ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ),
    IsOpen (deformedBandBase P φ) ∧
    interior (closure (deformedBandBase P φ)) = deformedBandBase P φ ∧
    (deformedBandBase P φ).Nonempty ∧
    deformedBandBase P φ ≠ Set.univ ∧
    0 < mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ ∧
    mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ +ᵥ
      deformedBandBase P φ = deformedBandBase P φ ∧
    frontier (deformedBandBase P φ) = Set.range (P.deformedBoundary φ) ∧
    ∀ j : ℤ, P.occupied j = true ↔
      Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) ⊆
        deformedBandBase P φ


private theorem deformedBandBase_geometry_impl : deformedBandBase_geometrySpec := by
  intro C P ε _hFine φ _hφ
  obtain ⟨H, hHmono, hHknots, hHperiod⟩ :=
    periodicBoundaryHomeomorph_exists_impl P ε _hFine φ _hφ
  have himage : deformedBandBase P φ = H '' P.base :=
    deformedBandBase_eq_image_impl P φ H hHmono hHknots
  have hopen : IsOpen (deformedBandBase P φ) := by
    rw [himage]
    exact H.isOpenMap P.base P.base_open
  have hregular : interior (closure (deformedBandBase P φ)) =
      deformedBandBase P φ := by
    rw [himage, ← H.image_closure, ← H.image_interior, P.base_regular]
  have hnonempty : (deformedBandBase P φ).Nonempty := by
    rw [himage]
    exact P.base_nonempty.image H
  have hproper : deformedBandBase P φ ≠ Set.univ := by
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x ∉ P.base := by
      by_contra h
      apply P.base_proper
      ext x
      by_cases hx : x ∈ P.base
      · constructor <;> intro <;> trivial
      · exact False.elim (h ⟨x, hx⟩)
    intro h
    have hx' : H x ∉ H '' P.base := by
      intro hx'
      obtain ⟨z, hz, hzx⟩ := hx'
      exact hx (H.injective hzx ▸ hz)
    apply hx'
    rw [← himage, h]
    trivial
  let q : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have hq : 0 < q := by
    have hshift := P.boundary_period 0
    have hlt := P.boundary_strictMono
      (show (0 : ℤ) < Int.ofNat P.numberOfBoundaryPoints by
        change (0 : ℤ) < (P.numberOfBoundaryPoints : ℤ)
        exact_mod_cast P.numberOfBoundaryPoints_pos)
    have hsource : P.boundary (Int.ofNat P.numberOfBoundaryPoints) =
        P.boundary 0 + P.period := by simpa using hshift
    have htargetlt : P.deformedBoundary φ 0 <
        P.deformedBoundary φ (Int.ofNat P.numberOfBoundaryPoints) := by
      simpa [hHknots] using hHmono hlt
    have hperiod := (periodicBandDeformation_preservesGapAlphabet P ε _hFine φ _hφ).1
    have hperiod' : P.deformedBoundary φ (Int.ofNat P.numberOfBoundaryPoints) =
        P.deformedBoundary φ 0 + q := by
      simpa [q] using hperiod 0
    linarith
  have hperiodic : q +ᵥ deformedBandBase P φ = deformedBandBase P φ := by
    rw [himage]
    ext z
    constructor
    · intro hz
      rcases Set.mem_vadd_set.mp hz with ⟨w, hw, hzw⟩
      rcases hw with ⟨u, hu, rfl⟩
      have hu' : u + P.period ∈ P.base := by
        rw [← P.base_periodic]
        exact Set.mem_vadd_set.mpr ⟨u, hu, by simp [vadd_eq_add, add_comm]⟩
      refine ⟨u + P.period, hu', ?_⟩
      have hzw' : q + H u = z := by simpa [vadd_eq_add] using hzw
      calc
        H (u + P.period) = H u + q := by simpa [q] using hHperiod u
        _ = q + H u := by ring
        _ = z := hzw'
    · intro hz
      rcases hz with ⟨u, hu, rfl⟩
      have hu' : u - P.period ∈ P.base := by
        have hu'' : u ∈ P.period +ᵥ P.base := by
          rw [P.base_periodic]
          exact hu
        rcases Set.mem_vadd_set.mp hu'' with ⟨v, _hv, hvu⟩
        have hvu' : P.period + v = u := by simpa [vadd_eq_add] using hvu
        have : v = u - P.period := by linarith [hvu']
        simpa [this] using _hv
      refine Set.mem_vadd_set.mpr ⟨H (u - P.period), ⟨u - P.period, hu', rfl⟩, ?_⟩
      rw [vadd_eq_add]
      calc
        q + H (u - P.period) = H (u - P.period) + q := by ring
        _ = H ((u - P.period) + P.period) := by simpa using (hHperiod (u - P.period)).symm
        _ = H u := by congr 1; ring
  have hfrontier : frontier (deformedBandBase P φ) =
      Set.range (P.deformedBoundary φ) := by
    rw [himage, ← H.image_frontier, ← P.boundary_range]
    ext z
    constructor
    · rintro ⟨x, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, (hHknots j).symm⟩
    · rintro ⟨j, rfl⟩
      exact ⟨P.boundary j, ⟨j, rfl⟩, hHknots j⟩
  have hchamber : ∀ j : ℤ, P.occupied j = true ↔
      Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) ⊆
        deformedBandBase P φ := by
    intro j
    have hHsymm : StrictMono H.symm := by
      intro a b hab
      apply lt_of_not_ge
      intro hle
      have : H (H.symm b) ≤ H (H.symm a) := hHmono.monotone hle
      have : b ≤ a := by simpa using this
      exact (not_le_of_gt hab) this
    let E : ℝ ≃o ℝ := H.toEquiv.toOrderIso hHmono.monotone hHsymm.monotone
    have hinterval :
        H '' Ioo (P.boundary j) (P.boundary (j + 1)) =
          Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) := by
      change E '' Ioo (P.boundary j) (P.boundary (j + 1)) = _
      have hEj (k : ℤ) : E (P.boundary k) = P.deformedBoundary φ k := by
        change H (P.boundary k) = P.deformedBoundary φ k
        exact hHknots k
      rw [E.image_Ioo, hEj, hEj]
    constructor
    · intro hocc x hx
      have hx' : x ∈ H '' Ioo (P.boundary j) (P.boundary (j + 1)) := by
        rw [hinterval]
        exact hx
      obtain ⟨z, hz, hzx⟩ := hx'
      have hzbase : z ∈ P.base := by
        apply (P.occupied_iff j).1 hocc
        exact hz
      rw [himage]
      exact ⟨z, hzbase, hzx⟩
    · intro hsub
      apply (P.occupied_iff j).2
      intro z hz
      have hz' : H z ∈ deformedBandBase P φ := by
        apply hsub
        rw [← hinterval]
        exact ⟨z, hz, rfl⟩
      rw [himage] at hz'
      obtain ⟨w, hw, hwz⟩ := hz'
      have : w = z := H.injective hwz
      simpa [this] using hw
  refine ⟨hopen, hregular, hnonempty, hproper, ?_, hperiodic, hfrontier, hchamber⟩
  simpa [q] using hq


private theorem firstStageRunningMap_gap_bounds_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (_D : CoordinateDeformation C φ) (s : ↥C.centres)
    {a b r : ℝ} {xLift₀ xLift₁ : C.coordinateSpace}
    (hLift₀ : (xLift₀ : ℝ) = a) (hLift₁ : (xLift₁ : ℝ) = b)
    (v w : Tiling.Plane) (_hv : v ∈ C.region.vertices)
    (hw : w ∈ C.region.vertices)
    (hleft : a = (v + (s : Tiling.Plane)).re)
    (hright : b = (w + (s : Tiling.Plane)).re)
    (hr : r ∈ Ioo a b) :
    mapScalar φ xLift₀ < firstStageRunningMap φ _D s r ∧
      firstStageRunningMap φ _D s r < mapScalar φ xLift₁ := by
  have hvarg : v.re < r - s.1.re := by
    rw [hleft] at hr
    simp only [Complex.add_re] at hr
    linarith [hr.1]
  have hwarg : r - s.1.re < w.re := by
    rw [hright] at hr
    simp only [Complex.add_re] at hr
    linarith [hr.2]
  have hvl := _D.firstHomeomorph_strictMono hvarg
  have hwr := _D.firstHomeomorph_strictMono hwarg
  have hleftMap := endpoint_formula _D v _hv s a xLift₀ hLift₀ hleft
  have hrightMap := endpoint_formula _D w hw s b xLift₁ hLift₁ hright
  have hcenter :
      (mapFirstPoint φ (C.centrePoint s.1 s.2)).re =
        mapScalar φ ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ := by
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  rw [hcenter] at hleftMap hrightMap
  constructor
  · rw [hleftMap]
    dsimp [firstStageRunningMap]
    simpa [mapFirstPoint, ApproximationContext.centrePoint, add_comm,
      sub_eq_add_neg] using
      (add_lt_add_right hvl
        (mapFirstPoint φ (C.centrePoint s.1 s.2)).re)
  · rw [hrightMap]
    dsimp [firstStageRunningMap]
    simpa [mapFirstPoint, ApproximationContext.centrePoint, add_comm,
      sub_eq_add_neg] using
      (add_lt_add_right hwr
        (mapFirstPoint φ (C.centrePoint s.1 s.2)).re)

private theorem firstStage_target_base_of_globalChain_gap
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ)
    (_hgeom : deformedBandBase_geometrySpec.{u})
    {q : ℝ} {n : ℕ} (x : Fin (n + 1) → ℝ)
    (xLift : Fin (n + 1) → C.coordinateSpace)
    (step : Fin n → Sum ↥C.centres ℤ)
    (hchain : IsSourceBandGlobalSliceChain C P q x xLift step)
    (j : ℤ) (hjocc : P.occupied j = true)
    (hx0 : x 0 = P.boundary j)
    (hxlast : x (Fin.last n) = P.boundary (j + 1))
    (t : ↥C.centres) {r : ℝ}
    (hrsource : slicePoint Axis.horizontal q r ∈
      t.1 +ᵥ C.region.openCarrier)
    (hrgap : ∃ i : Fin n, r ∈ Ioo (x i.castSucc) (x i.succ)) :
    firstStageRunningMap φ _D t r ∈
      Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) := by
  obtain ⟨i, hri⟩ := hrgap
  have htrans := sourceBand_globalSliceChain_transport_impl P ε _hFine φ _hφ _D q
    x xLift step hchain
  have hleft0 : x 0 ≤ x i.castSucc := hchain.2.1.monotone (Fin.zero_le _)
  have hright0 : x i.succ ≤ x (Fin.last n) :=
    hchain.2.1.monotone (Fin.le_last _)
  have hxi0 : x 0 < x i.castSucc ∨ x 0 = x i.castSucc :=
    lt_or_eq_of_le hleft0
  have hxilast : x i.succ < x (Fin.last n) ∨
      x i.succ = x (Fin.last n) := lt_or_eq_of_le hright0
  have hxlift0 : xLift 0 =
      ⟨P.boundary j, P.boundary_value_mem_coordinateSpace j⟩ := by
    apply Subtype.ext
    simp [hchain.1 0, hx0]
  have hxLiftlast : xLift (Fin.last n) =
      ⟨P.boundary (j + 1), P.boundary_value_mem_coordinateSpace (j + 1)⟩ := by
    apply Subtype.ext
    simp [hchain.1 (Fin.last n), hxlast]
  have hmap0 : mapScalar φ (xLift 0) = P.deformedBoundary φ j := by
    rw [hxlift0]
    rfl
  have hmaplast : mapScalar φ (xLift (Fin.last n)) =
      P.deformedBoundary φ (j + 1) := by
    rw [hxLiftlast]
    rfl
  cases hs : step i with
  | inr k =>
      have hstep := hs ▸ hchain.2.2 i
      have hkr : P.boundary k < r ∧ r < P.boundary (k + 1) := by
        constructor
        · simpa [hstep.2.1] using hri.1
        · simpa [hstep.2.2] using hri.2
      have hkj : k = j := by
        have hjr : P.boundary j < r := by
          rw [← hx0]
          exact lt_of_le_of_lt hleft0 hri.1
        have hrj : r < P.boundary (j + 1) := by
          rw [← hxlast]
          exact lt_of_lt_of_le hri.2 hright0
        have hkj' : k < j + 1 :=
          (P.boundary_strictMono.lt_iff_lt.mp (lt_trans hkr.1 hrj))
        have hjk' : j < k + 1 :=
          (P.boundary_strictMono.lt_iff_lt.mp (lt_trans hjr hkr.2))
        omega
      have : P.occupied j = false := by simpa [hkj] using hstep.1
      have hbad : (false : Bool) = true := this.symm.trans hjocc
      cases hbad
  | inl u =>
      obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ :=
        hs ▸ hchain.2.2 i
      have hru : slicePoint Axis.horizontal q r ∈
          u.1 +ᵥ C.region.openCarrier := hinside
            ⟨by simp [slicePoint], by simpa [slicePoint] using hri⟩
      have hut : u = t := by
        by_contra hne
        exact Set.disjoint_left.mp
          ((isPacking_iff_openCarrier_disjoint C.region C.centres).mp
            P.source_tilesOn.2.1 u.2 t.2 (fun h => hne (Subtype.ext h)))
          hru hrsource
      subst u
      have hbounds := firstStageRunningMap_gap_bounds_local (_D := _D) (s := t)
        (a := x i.castSucc) (b := x i.succ) (r := r)
        (xLift₀ := xLift i.castSucc) (xLift₁ := xLift i.succ)
        (hLift₀ := hchain.1 i.castSucc) (hLift₁ := hchain.1 i.succ)
        (v := v) (_hv := _hv) (w := w) (hw := hw)
        (hleft := hleft) (hright := hright) (hr := hri)
      have hlow : mapScalar φ (xLift 0) <
          firstStageRunningMap φ _D t r :=
        lt_of_le_of_lt (htrans.1.monotone (Fin.zero_le _)) hbounds.1
      have hhigh : mapScalar φ (xLift i.succ) ≤
          mapScalar φ (xLift (Fin.last n)) :=
        htrans.1.monotone (Fin.le_last _)
      have htarget : firstStageRunningMap φ _D t r ∈ Ioo
          (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) := by
        rw [← hmap0, ← hmaplast]
        exact ⟨hlow, lt_of_lt_of_le hbounds.2 hhigh⟩
      exact htarget

private theorem firstStage_generic_target_point_in_base
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ)
    (_hgeom : deformedBandBase_geometrySpec.{u})
    {q : ℝ} (hqCh : ∀ j : ℤ, P.occupied j = true →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (xLift : Fin (n + 1) → C.coordinateSpace)
        (owner : Fin n → ↥C.centres),
        x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
          IsSourceBandSliceChain C q x xLift owner)
    (t : ↥C.centres) (r : ℝ)
    (hrsource : slicePoint Axis.horizontal q r ∈
      t.1 +ᵥ C.region.openCarrier) :
    firstStageRunningMap φ _D t r ∈ deformedBandBase P φ := by
  have hopen : IsOpen (placedAxisSlice C.region t.1 Axis.horizontal q) := by
    change IsOpen {x : ℝ | slicePoint Axis.horizontal q x ∈
      t.1 +ᵥ C.region.openCarrier}
    exact (C.region.openCarrier_regularOpen.1.vadd t.1).preimage
      (continuous_slicePoint Axis.horizontal q)
  have hrsource' : r ∈ placedAxisSlice C.region t.1 Axis.horizontal q := hrsource
  obtain ⟨δ, _hδ, hball⟩ := Metric.isOpen_iff.1 hopen r hrsource'
  have hrbase' := source_openUnion_subset_base P (by
      rw [openUnion]
      exact Set.mem_iUnion.mpr ⟨t, hrsource⟩)
  have hrbase : r ∈ P.base := by
    simpa [slicePoint] using hrbase'
  obtain ⟨j, hjocc, hrch⟩ := source_occupied_chamber_of_mem_base P hrbase
  obtain ⟨n, _hn, x, xLift, step, hchain, hx0, hxlast⟩ :=
    source_global_segment P q hqCh j
  let F : Finset ℝ := Finset.univ.image x
  have hη : 0 < min (δ / 2)
      (min ((r - P.boundary j) / 2)
        ((P.boundary (j + 1) - r) / 2)) := by
    apply lt_min
    · linarith
    · apply lt_min
      · linarith [hrch.1]
      · linarith [hrch.2]
  let η : ℝ := min (δ / 2)
      (min ((r - P.boundary j) / 2)
        ((P.boundary (j + 1) - r) / 2))
  have hηpos : 0 < η := by
    dsimp [η]
    exact hη
  obtain ⟨rleft, hrleftI, hrleftF⟩ :=
    exists_mem_Ioo_avoiding_finset_local (a := r - η) (b := r)
      (sub_lt_self r hηpos) F
  obtain ⟨rright, hrrightI, hrrightF⟩ :=
    exists_mem_Ioo_avoiding_finset_local (a := r) (b := r + η)
      (lt_add_of_pos_right r hηpos) F
  have hrleft : rleft ∈ Ioo (r - η) r := hrleftI
  have hrright : rright ∈ Ioo r (r + η) := by
    simpa [sub_eq_add_neg, add_comm] using hrrightI
  have hrleftch : rleft ∈ Ioo (P.boundary j) (P.boundary (j + 1)) := by
    constructor
    · have hη' : η ≤ (r - P.boundary j) / 2 :=
        le_trans (min_le_right _ _) (min_le_left _ _)
      linarith [hrleft.1]
    · linarith [hrleft.2, hrch.2]
  have hrrightch : rright ∈ Ioo (P.boundary j) (P.boundary (j + 1)) := by
    constructor
    · linarith [hrright.1, hrch.1]
    · have hη' : η ≤ (P.boundary (j + 1) - r) / 2 :=
        le_trans (min_le_right _ _) (min_le_right _ _)
      linarith [hrright.2]
  have hnear (s : ℝ) (hs : s ∈ Ioo (r - η) (r + η)) :
      s ∈ placedAxisSlice C.region t.1 Axis.horizontal q := by
    apply hball
    change dist s r < δ
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2, show η ≤ δ / 2 from min_le_left _ _]
  have hnot (s : ℝ) (hs : s ∉ F) : ∀ k, s ≠ x k := by
    intro k heq
    apply hs
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, heq.symm⟩
  have hgap (s : ℝ) (hs : s ∈ Ioo (P.boundary j) (P.boundary (j + 1)))
      (hsF : s ∉ F) : ∃ i : Fin n, s ∈ Ioo (x i.castSucc) (x i.succ) := by
    apply strictMono_exists_gap (fun i => x i) hchain.2.1
    · calc x 0 = P.boundary j := hx0
         _ < s := hs.1
    · calc s < P.boundary (j + 1) := hs.2
         _ = x (Fin.last n) := hxlast.symm
    · exact hnot s hsF
  have hleft := firstStage_target_base_of_globalChain_gap P ε _hFine φ _hφ _D
    _hgeom x xLift step hchain j hjocc hx0 hxlast t
    (hnear rleft ⟨hrleft.1, by linarith [hrleft.2, hη]⟩)
    (hgap rleft hrleftch hrleftF)
  have hright := firstStage_target_base_of_globalChain_gap P ε _hFine φ _hφ _D
    _hgeom x xLift step hchain j hjocc hx0 hxlast t
    (hnear rright ⟨by linarith [hrright.1, hη], hrright.2⟩)
    (hgap rright hrrightch hrrightF)
  have hrunmono : StrictMono (fun s : ℝ => firstStageRunningMap φ _D t s) := by
    intro a b hab
    change mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ +
      _D.firstHomeomorph (a - t.1.re) <
      mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ +
        _D.firstHomeomorph (b - t.1.re)
    simpa [add_comm] using add_lt_add_left
      (_D.firstHomeomorph_strictMono (sub_lt_sub_right hab t.1.re))
      (mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩)
  have hrsand : firstStageRunningMap φ _D t r ∈
      Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) := by
    exact ⟨lt_trans hleft.1 (hrunmono hrleft.2),
      lt_trans (hrunmono hrright.1) hright.2⟩
  obtain ⟨_, _, _, _, _, _, _, hchamber⟩ := _hgeom (C := C) P ε _hFine φ _hφ
  exact hchamber j |>.1 hjocc hrsand

private theorem firstStage_enclosure_of_chamberChains
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ)
    (_hgeom : deformedBandBase_geometrySpec.{u}) :
    ∀ t : ↥C.centres,
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier ⊆
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
  intro t z hz
  have hopen : IsOpen
      (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier) :=
    _D.firstRegion.openCarrier_regularOpen.1.vadd _
  obtain ⟨δ, _hδ, hball⟩ := Metric.isOpen_iff.1 hopen z hz
  have hgood : ∀ᵐ q : ℝ ∂volume,
      ∀ j : ℤ, P.occupied j = true →
        ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
          (xLift : Fin (n + 1) → C.coordinateSpace)
          (owner : Fin n → ↥C.centres),
          x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
            IsSourceBandSliceChain C q x xLift owner :=
    sourceBand_chamberChains_unconditional_impl P
  obtain ⟨q, hqJ, hqgood⟩ :=
    exists_mem_Ioo_of_ae_real (a := z.im - δ / 2) (b := z.im + δ / 2)
      (by linarith [_hδ]) hgood
  have hzq : slicePoint Axis.horizontal q z.re ∈
      mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier := by
    apply hball
    change dist (slicePoint Axis.horizontal q z.re) z < δ
    rw [dist_eq_norm]
    have heq : slicePoint Axis.horizontal q z.re - z =
        ((q - z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [slicePoint]
    rw [heq]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one]
    have : |q - z.im| < δ := by
      rw [abs_lt]
      constructor <;> linarith [hqJ.1, hqJ.2]
    exact this
  have hzq' : z.re ∈ placedAxisSlice _D.firstRegion
      (mapFirstPoint φ (C.centrePoint t.1 t.2)) Axis.horizontal q := hzq
  rw [firstStage_allSectionComponents_transport_impl φ _D t q] at hzq'
  obtain ⟨r, hrsource, hrun⟩ := hzq'
  have hrbase := firstStage_generic_target_point_in_base P ε _hFine φ _hφ _D
    _hgeom hqgood t r hrsource
  change z.re ∈ deformedBandBase P φ
  rw [← hrun]
  exact hrbase

private theorem firstStage_disjoint_of_globalOrder
    {C : ApproximationContext.{u}} (P : PeriodicBandData C)
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (_D : CoordinateDeformation C φ)
    (hOrder : firstStage_globalGenericSliceOrderSpec.{u}) :
    ∀ s t : ↥C.centres, s ≠ t →
      Disjoint
        (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier)
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro z hzs hzt
  have hopen : IsOpen
      ((mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier) ∩
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier)) :=
    (_D.firstRegion.openCarrier_regularOpen.1.vadd _).inter
      (_D.firstRegion.openCarrier_regularOpen.1.vadd _)
  have hzinter : z ∈
      (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier) ∩
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier) :=
    ⟨hzs, hzt⟩
  obtain ⟨δ, _hδ, hball⟩ := Metric.isOpen_iff.1 hopen z hzinter
  have hgood := hOrder P ε _hFine φ _hφ _D
  obtain ⟨q, hqI, hqgood⟩ := exists_mem_Ioo_of_ae_real
    (a := z.im - δ / 2) (b := z.im + δ / 2) (by linarith [_hδ]) hgood
  have hzq : slicePoint Axis.horizontal q z.re ∈
      (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier) ∩
        (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier) := by
    apply hball
    change dist (slicePoint Axis.horizontal q z.re) z < δ
    rw [dist_eq_norm]
    have heq : slicePoint Axis.horizontal q z.re - z =
        ((q - z.im : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [slicePoint]
    rw [heq]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one]
    rw [abs_lt]
    constructor <;> linarith [hqI.1, hqI.2]
  have hsq : z.re ∈ placedAxisSlice _D.firstRegion
      (mapFirstPoint φ (C.centrePoint s.1 s.2)) Axis.horizontal q := hzq.1
  have htq : z.re ∈ placedAxisSlice _D.firstRegion
      (mapFirstPoint φ (C.centrePoint t.1 t.2)) Axis.horizontal q := hzq.2
  rw [firstStage_allSectionComponents_transport_impl φ _D s q] at hsq
  rw [firstStage_allSectionComponents_transport_impl φ _D t q] at htq
  obtain ⟨a, hsa, hsaRun⟩ := hsq
  obtain ⟨b, htb, htbRun⟩ := htq
  have hab : a = b := by
    by_contra habne
    rcases lt_or_gt_of_ne habne with hablt | hblt
    · have hlt := hqgood s t a b hsa htb hablt
      exact (ne_of_lt hlt) (hsaRun.trans htbRun.symm)
    · have hlt := hqgood t s b a htb hsa hblt
      exact (ne_of_lt hlt) (htbRun.trans hsaRun.symm)
  subst b
  exact Set.disjoint_left.mp
    ((isPacking_iff_openCarrier_disjoint C.region C.centres).mp
      P.source_tilesOn.2.1 s.2 t.2 (fun h => hst (Subtype.ext h))) hsa htb

private theorem exists_four_points_in_two_open_sections_local
    {C : ApproximationContext.{u}} {q : ℝ}
    (s t : ↥C.centres) {x y : ℝ}
    (hx : x ∈ placedAxisSlice C.region s.1 Axis.horizontal q)
    (hy : y ∈ placedAxisSlice C.region t.1 Axis.horizontal q)
    (hxy : x < y) (F : Finset ℝ) :
    ∃ x' y', x < x' ∧ x' < y' ∧ y' < y ∧
      x' ∈ placedAxisSlice C.region s.1 Axis.horizontal q ∧
      y' ∈ placedAxisSlice C.region t.1 Axis.horizontal q ∧
      x' ∉ (F : Set ℝ) ∧ y' ∉ (F : Set ℝ) := by
  have hsopen : IsOpen (placedAxisSlice C.region s.1 Axis.horizontal q) := by
    change IsOpen ((slicePoint Axis.horizontal q) ⁻¹'
      (s.1 +ᵥ C.region.openCarrier))
    exact (C.region.openCarrier_regularOpen.1.vadd s.1).preimage
      (continuous_slicePoint Axis.horizontal q)
  have htopen : IsOpen (placedAxisSlice C.region t.1 Axis.horizontal q) := by
    change IsOpen ((slicePoint Axis.horizontal q) ⁻¹'
      (t.1 +ᵥ C.region.openCarrier))
    exact (C.region.openCarrier_regularOpen.1.vadd t.1).preimage
      (continuous_slicePoint Axis.horizontal q)
  obtain ⟨δs, hδs, hballS⟩ := Metric.isOpen_iff.1 hsopen x hx
  obtain ⟨δt, hδt, hballT⟩ := Metric.isOpen_iff.1 htopen y hy
  let u := min y (x + δs / 2)
  have hxu : x < u := by
    dsimp [u]
    exact lt_min hxy (by linarith)
  obtain ⟨x', hx'I, hx'F⟩ :=
    exists_mem_Ioo_avoiding_finset_local hxu F
  let l := max x' (y - δt / 2)
  have hly : l < y := by
    dsimp [l]
    apply max_lt
    · exact lt_of_lt_of_le hx'I.2 (min_le_left _ _)
    · linarith
  obtain ⟨y', hy'I, hy'F⟩ :=
    exists_mem_Ioo_avoiding_finset_local hly F
  have hx'close : dist x' x < δs := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx'I.1, hx'I.2, min_le_right y (x + δs / 2)]
  have hy'close : dist y' y < δt := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy'I.1, hy'I.2, le_max_right x' (y - δt / 2)]
  refine ⟨x', y', hx'I.1, ?_, hy'I.2, ?_, ?_, hx'F, hy'F⟩
  · exact lt_of_le_of_lt (le_max_left x' (y - δt / 2)) hy'I.1
  · exact hballS hx'close
  · exact hballT hy'close

private theorem firstStageRunningMap_strictMono_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (_D : CoordinateDeformation C φ) (s : ↥C.centres) :
    StrictMono (firstStageRunningMap φ _D s) := by
  intro a b hab
  dsimp [firstStageRunningMap]
  simpa [add_comm] using
    (add_lt_add_left (_D.firstHomeomorph_strictMono
      (sub_lt_sub_right hab s.1.re))
      (mapScalar φ ⟨s.1.re, C.centre_re_mem s.1 s.2⟩))

private theorem source_slice_mem_of_vertical_perturbation
    {C : ApproximationContext.{u}} (s : ↥C.centres) (p : Tiling.Plane)
    (_hp : p ∈ C.region.openCarrier) {q : ℝ} (δ : ℝ) (_hδ : 0 < δ)
    (hball : Metric.ball (s.1 + p) δ ⊆ s.1 +ᵥ C.region.openCarrier)
    (hq : |q - (s.1.im + p.im)| < δ) :
    s.1.re + p.re ∈ placedAxisSlice C.region s.1 Axis.horizontal q := by
  change slicePoint Axis.horizontal q (s.1.re + p.re) ∈
    s.1 +ᵥ C.region.openCarrier
  have hclose : dist (slicePoint Axis.horizontal q (s.1.re + p.re)) (s.1 + p) < δ := by
    rw [dist_eq_norm]
    have heq : slicePoint Axis.horizontal q (s.1.re + p.re) - (s.1 + p) =
        ((q - (s.1.im + p.im) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [slicePoint]
    rw [heq]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one]
    exact hq
  exact hball hclose

private theorem firstStageCentreMap_injective_impl
    (horder : firstStage_globalGenericSliceOrderSpec.{u}) :
    firstStageCentreMap_injectiveSpec.{u} := by
  intro C P ε _hFine φ _hφ _D s t heq
  obtain ⟨p, _hp⟩ := C.region.isPolygonal.interior_nonempty C.region.nonempty
  have hgood := horder P ε _hFine φ _hφ _D
  have hsp : s.1 + p ∈ s.1 +ᵥ C.region.openCarrier := ⟨p, _hp, rfl⟩
  obtain ⟨δ, _hδ, hball⟩ := Metric.isOpen_iff.1
    (C.region.openCarrier_regularOpen.1.vadd s.1) (s.1 + p) hsp
  have him : s.1.im = t.1.im := by
    have him' := congrArg Complex.im heq
    simpa [mapFirstPoint, ApproximationContext.centrePoint] using him'
  have htp : t.1 + p ∈ t.1 +ᵥ C.region.openCarrier := ⟨p, _hp, rfl⟩
  obtain ⟨δt, hδt, hballt⟩ := Metric.isOpen_iff.1
    (C.region.openCarrier_regularOpen.1.vadd t.1) (t.1 + p) htp
  let η : ℝ := min δ δt
  have hη : 0 < η := lt_min _hδ hδt
  have hwidth : s.1.im + p.im - η < s.1.im + p.im + η := by linarith
  obtain ⟨q, hqI, hqgood⟩ := exists_mem_Ioo_of_ae_real hwidth hgood
  have hsr : s.1.re = t.1.re := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hst | hts
    · let x : ℝ := s.1.re + p.re
      let y : ℝ := t.1.re + p.re
      have hx : x ∈ placedAxisSlice C.region s.1 Axis.horizontal q := by
        dsimp [x]
        exact source_slice_mem_of_vertical_perturbation s p _hp η hη
          (fun _ hz => hball (lt_of_lt_of_le hz (min_le_left δ δt))) (by
          apply abs_lt.mpr
          constructor <;> linarith [hqI.1, hqI.2])
      have hy : y ∈ placedAxisSlice C.region t.1 Axis.horizontal q := by
        dsimp [y]
        exact source_slice_mem_of_vertical_perturbation t p _hp η hη
          (fun _ hz => hballt (lt_of_lt_of_le hz (min_le_right δ δt))) (by
          apply abs_lt.mpr
          constructor <;> linarith [hqI.1, hqI.2])
      have hlt := hqgood s t x y hx hy (by dsimp [x, y]; linarith)
      have heqr : mapScalar φ ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ =
          mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
        simpa [mapFirstPoint, ApproximationContext.centrePoint] using congrArg Complex.re heq
      have hEqRun : firstStageRunningMap φ _D s x =
          firstStageRunningMap φ _D t y := by
        dsimp [firstStageRunningMap, x, y]
        rw [heqr]
        congr 1
        simp
      exact (ne_of_lt hlt) hEqRun
    · let x : ℝ := t.1.re + p.re
      let y : ℝ := s.1.re + p.re
      have hx : x ∈ placedAxisSlice C.region t.1 Axis.horizontal q := by
        dsimp [x]
        exact source_slice_mem_of_vertical_perturbation t p _hp η hη
          (fun _ hz => hballt (lt_of_lt_of_le hz (min_le_right δ δt))) (by
          apply abs_lt.mpr
          constructor <;> linarith [hqI.1, hqI.2])
      have hy : y ∈ placedAxisSlice C.region s.1 Axis.horizontal q := by
        dsimp [y]
        exact source_slice_mem_of_vertical_perturbation s p _hp η hη
          (fun _ hz => hball (lt_of_lt_of_le hz (min_le_left δ δt))) (by
          apply abs_lt.mpr
          constructor <;> linarith [hqI.1, hqI.2])
      have hlt := hqgood t s x y hx hy (by dsimp [x, y]; linarith)
      have heqr : mapScalar φ ⟨s.1.re, C.centre_re_mem s.1 s.2⟩ =
          mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
        simpa [mapFirstPoint, ApproximationContext.centrePoint] using congrArg Complex.re heq
      have hEqRun : firstStageRunningMap φ _D t x =
          firstStageRunningMap φ _D s y := by
        dsimp [firstStageRunningMap, x, y]
        rw [heqr]
        congr 1
        simp
      exact (ne_of_lt hlt) hEqRun
  apply Subtype.ext
  apply Complex.ext <;> assumption

private theorem firstStage_globalGenericSliceOrder_impl :
    firstStage_globalGenericSliceOrderSpec.{u} := by
  intro C P ε _hFine φ _hφ _D
  filter_upwards [sourceBand_globalSliceChains_impl P] with q hglobal
  intro s t x y hx hy hxy
  obtain ⟨n, _hn, z, zLift, step, hzleft, hzright, hwalk⟩ :=
    hglobal (x - 1) (y + 1) (by linarith)
  let nodes : Finset ℝ := Finset.univ.image z
  obtain ⟨x', y', hxx', hxy', hy'y, hx', hy', hx'node, hy'node⟩ :=
    exists_four_points_in_two_open_sections_local s t hx hy hxy nodes
  have hnode (r : ℝ) (hr : r = x' ∨ r = y') : r ∉ Set.range z := by
    intro hrange
    obtain ⟨i, hi⟩ := hrange
    rcases hr with hr | hr
    · apply hx'node
      change x' ∈ Finset.image z Finset.univ
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans hr⟩
    · apply hy'node
      change y' ∈ Finset.image z Finset.univ
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans hr⟩
  obtain ⟨ix, hix⟩ := strictMono_exists_gap z hwalk.2.1
    (lt_of_le_of_lt hzleft (lt_trans (by linarith) hxx'))
      (lt_of_lt_of_le (lt_trans hxy' (lt_trans hy'y (by linarith))) hzright)
    (fun i hi => hnode x' (Or.inl rfl) ⟨i, hi.symm⟩)
  obtain ⟨iy, hiy⟩ := strictMono_exists_gap z hwalk.2.1
    (lt_of_le_of_lt hzleft (lt_trans (by linarith) hxy'))
      (lt_of_lt_of_le hy'y (le_trans (by linarith) hzright))
    (fun i hi => hnode y' (Or.inr rfl) ⟨i, hi.symm⟩)
  have htrans := sourceBand_globalSliceChain_transport_impl P ε _hFine φ _hφ _D q
    z zLift step hwalk
  have hsourceBase (r : ℝ)
      (hr : r ∈ placedAxisSlice C.region s.1 Axis.horizontal q) : r ∈ P.base := by
    have hrU : slicePoint Axis.horizontal q r ∈ openUnion C.region C.centres := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
      exact ⟨s, hr⟩
    simpa [slicePoint] using source_openUnion_subset_base P hrU
  have howner (u : ↥C.centres) (r : ℝ)
      (hrS : r ∈ placedAxisSlice C.region s.1 Axis.horizontal q)
      (hrU : r ∈ placedAxisSlice C.region u.1 Axis.horizontal q) : u = s := by
    by_contra hus
    have hdisj := (isPacking_iff_openCarrier_disjoint C.region C.centres).mp
      P.source_tilesOn.2.1 u.2 s.2 (fun heq => hus (Subtype.ext heq))
    exact Set.disjoint_left.mp hdisj hrU hrS
  have hixowner : step ix = .inl s := by
    cases hsx : step ix with
    | inl u =>
        obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ :=
          hsx ▸ hwalk.2.2 ix
        have _hp : slicePoint Axis.horizontal q x' ∈
            (u : Tiling.Plane) +ᵥ C.region.openCarrier := by
          apply hinside
          exact ⟨by simp [slicePoint], by simpa [slicePoint] using hix⟩
        exact congrArg Sum.inl (howner u x' hx' _hp)
    | inr j =>
        have hstep := hsx ▸ hwalk.2.2 ix
        have hbase := hsourceBase x' hx'
        obtain ⟨k, hkocc, hkint⟩ := source_occupied_chamber_of_mem_base P hbase
        have hxj : x' ∈ Ioo (P.boundary j) (P.boundary (j + 1)) := by
          simpa [hstep.2.1, hstep.2.2] using hix
        have hkj : k = j := by
          have h1 : k < j + 1 :=
            (P.boundary_strictMono.lt_iff_lt.mp
              (lt_trans hkint.1 hxj.2))
          have h2 : j < k + 1 :=
            (P.boundary_strictMono.lt_iff_lt.mp
              (lt_trans hxj.1 hkint.2))
          omega
        have : P.occupied j = false := by simpa [hkj] using hstep.1
        have htrue : P.occupied j = true := by simpa [hkj] using hkocc
        have hbad : (false : Bool) = true := this.symm.trans htrue
        cases hbad
  have hiyowner : step iy = .inl t := by
    cases hsy : step iy with
    | inl u =>
        obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ :=
          hsy ▸ hwalk.2.2 iy
        have _hp : slicePoint Axis.horizontal q y' ∈
            (u : Tiling.Plane) +ᵥ C.region.openCarrier := by
          apply hinside
          exact ⟨by simp [slicePoint], by simpa [slicePoint] using hiy⟩
        have hu : u = t := by
          by_contra hut
          have hdisj := (isPacking_iff_openCarrier_disjoint C.region C.centres).mp
            P.source_tilesOn.2.1 u.2 t.2 (fun heq => hut (Subtype.ext heq))
          exact Set.disjoint_left.mp hdisj _hp hy'
        exact congrArg Sum.inl hu
    | inr j =>
        have hstep := hsy ▸ hwalk.2.2 iy
        have hbase : y' ∈ P.base := by
          have hrU : slicePoint Axis.horizontal q y' ∈ openUnion C.region C.centres := by
            rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
            exact ⟨t, hy'⟩
          simpa [slicePoint] using source_openUnion_subset_base P hrU
        obtain ⟨k, hkocc, hkint⟩ := source_occupied_chamber_of_mem_base P hbase
        have hxj : y' ∈ Ioo (P.boundary j) (P.boundary (j + 1)) := by
          simpa [hstep.2.1, hstep.2.2] using hiy
        have hkj : k = j := by
          have h1 : k < j + 1 :=
            (P.boundary_strictMono.lt_iff_lt.mp
              (lt_trans hkint.1 hxj.2))
          have h2 : j < k + 1 :=
            (P.boundary_strictMono.lt_iff_lt.mp
              (lt_trans hxj.1 hkint.2))
          omega
        have : P.occupied j = false := by simpa [hkj] using hstep.1
        have htrue : P.occupied j = true := by simpa [hkj] using hkocc
        have hbad : (false : Bool) = true := this.symm.trans htrue
        cases hbad
  have hixiy : ix ≤ iy := by
    by_contra hnot
    have hlt : iy < ix := lt_of_not_ge hnot
    have hfin : iy.succ ≤ ix.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    have hzord : z iy.succ ≤ z ix.castSucc := hwalk.2.1.monotone hfin
    linarith [hiy.2, hix.1]
  have hsourceMap : firstStageRunningMap φ _D s x' <
      firstStageRunningMap φ _D t y' := by
    by_cases heq : ix = iy
    · subst iy
      have hst : s = t := by
        have hsum := hixowner
        rw [hiyowner] at hsum
        exact (Sum.inl.inj hsum).symm
      subst t
      exact firstStageRunningMap_strictMono_local _D s hxy'
    · have hlt : ix < iy := lt_of_le_of_ne hixiy heq
      obtain ⟨vx, wx, hvx, hwx, hxl, hxr, hxp, hinsidex⟩ :=
        hixowner ▸ hwalk.2.2 ix
      obtain ⟨vy, wy, hvy, hwy, hyl, hyr, hyp, hinsidey⟩ :=
        hiyowner ▸ hwalk.2.2 iy
      have hbx := firstStageRunningMap_gap_bounds_local (_D := _D) (s := s)
        (a := z ix.castSucc) (b := z ix.succ) (r := x')
        (xLift₀ := zLift ix.castSucc) (xLift₁ := zLift ix.succ)
        (hLift₀ := hwalk.1 ix.castSucc) (hLift₁ := hwalk.1 ix.succ)
        (v := vx) (_hv := hvx) (w := wx) (hw := hwx)
        (hleft := hxl) (hright := hxr) (hr := hix)
      have hby := firstStageRunningMap_gap_bounds_local (_D := _D) (s := t)
        (a := z iy.castSucc) (b := z iy.succ) (r := y')
        (xLift₀ := zLift iy.castSucc) (xLift₁ := zLift iy.succ)
        (hLift₀ := hwalk.1 iy.castSucc) (hLift₁ := hwalk.1 iy.succ)
        (v := vy) (_hv := hvy) (w := wy) (hw := hwy)
        (hleft := hyl) (hright := hyr) (hr := hiy)
      have hchain : mapScalar φ (zLift ix.succ) ≤ mapScalar φ (zLift iy.castSucc) := by
        apply htrans.1.monotone
        apply Fin.mk_le_mk.mpr
        omega
      exact lt_trans hbx.2 (lt_of_le_of_lt hchain hby.1)
  exact lt_trans (firstStageRunningMap_strictMono_local _D s hxx')
    (lt_trans hsourceMap (firstStageRunningMap_strictMono_local _D t hy'y))

private theorem firstStage_properCylinderSlices_parameterized_impl :
    firstStage_properCylinderSlices_parameterizedSpec.{u} := by
  intro hOrder hInjective C P ε _hFine φ _hφ _D
  obtain ⟨Hopen, Hregular, Hnonempty, Hproper, Hperiod, Hperiodic,
      Hfrontier, Hchamber⟩ := deformedBandBase_geometry_impl P ε _hFine φ _hφ
  let _hgeom : deformedBandBase_geometrySpec.{u} :=
    deformedBandBase_geometry_impl
  have henclosure := firstStage_enclosure_of_chamberChains
    P ε _hFine φ _hφ _D _hgeom
  have hdisjoint := firstStage_disjoint_of_globalOrder
    P ε _hFine φ _hφ _D hOrder
  have hforward := firstStage_forward_slice_ae_of_globalOrder
    P ε _hFine φ _hφ _D hOrder
  refine ⟨henclosure, hdisjoint, ?_⟩
  filter_upwards [hforward] with q hq
  filter_upwards [hq] with x hx
  constructor
  · exact hx
  · rintro ⟨t, _ht⟩
    have _ht' := henclosure t _ht
    simpa [slicePoint] using _ht'

private theorem firstStage_properCylinderSlices_unconditional_impl :
    firstStage_properCylinderSlicesSpec.{u} := by
  have hOrder : firstStage_globalGenericSliceOrderSpec.{u} :=
    firstStage_globalGenericSliceOrder_impl
  have hInjective : firstStageCentreMap_injectiveSpec.{u} :=
    firstStageCentreMap_injective_impl hOrder
  intro C P ε _hFine φ _hφ _D
  exact firstStage_properCylinderSlices_parameterized_impl hOrder hInjective
    P ε _hFine φ _hφ _D




end Tiling.AxisParallel.Approximation

namespace Tiling.AxisParallel.Approximation

universe u

open Tiling.AxisParallel
open Tiling.AxisParallel.OneDimensional
open Tiling.AxisParallel.OneDimensional.FiniteInterval
open Tiling.AxisParallel.Foundations.FilledSliceChains

private theorem tilesOn_of_axisSlices_impl :
    ∀ (K : Region) (S _D : Set Tiling.Plane) (axis : Axis),
      MeasurableSet _D →
      S.Countable →
      Set.Pairwise S
        (Disjoint on ((· +ᵥ K.openCarrier) : Tiling.Plane → Set Tiling.Plane)) →
      (∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
        (slicePoint axis q x ∈ _D ↔
          ∃ s : ↥S, slicePoint axis q x ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier)) →
      TilesOn K S _D := by
  intro K S _D axis hD hcount hpack hslice
  refine ⟨hcount, (isPacking_iff_openCarrier_disjoint K S).2 hpack, ?_⟩
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion fun s : S ↦ K.openCarrier_regularOpen.1.vadd (s : Tiling.Plane)
  cases axis with
  | vertical =>
      let P : ℝ → ℝ → Prop := fun q x =>
        (slicePoint Axis.vertical q x ∈ _D ↔
          ∃ s : ↥S, slicePoint Axis.vertical q x ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier)
      let g : ℝ × ℝ → Tiling.Plane := fun p ↦
        (p.1 : ℂ) + (p.2 : ℂ) * Complex.I
      have hg : Measurable g := by
        fun_prop
      let A : Set (ℝ × ℝ) := g ⁻¹' _D
      let B : Set (ℝ × ℝ) := {p | ∃ s : ↥S, g p ∈
        (s : Tiling.Plane) +ᵥ K.openCarrier}
      have hA : MeasurableSet A := hD.preimage hg
      have hB0 : MeasurableSet (g ⁻¹' openUnion K S) := hopen.measurableSet.preimage hg
      have hBeq : B = g ⁻¹' openUnion K S := by
        ext p
        change (∃ s : ↥S, g p ∈ (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
          g p ∈ openUnion K S
        constructor
        · rintro ⟨s, hs⟩
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
          exact ⟨s, hs⟩
        · intro _hp
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at _hp
          obtain ⟨s, hs⟩ := _hp
          exact ⟨s, hs⟩
      have hB : MeasurableSet B := hBeq ▸ hB0
      have hP : MeasurableSet {p : ℝ × ℝ | P p.1 p.2} := by
        have heq : {p : ℝ × ℝ | P p.1 p.2} = (A ∩ B) ∪ (Aᶜ ∩ Bᶜ) := by
          ext p
          change ((g p ∈ _D ↔ ∃ s : ↥S, g p ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
            ((g p ∈ _D ∧ (∃ s : ↥S, g p ∈
              (s : Tiling.Plane) +ᵥ K.openCarrier)) ∨
              (g p ∉ _D ∧ ¬ (∃ s : ↥S, g p ∈
                (s : Tiling.Plane) +ᵥ K.openCarrier))))
          by_cases hd : g p ∈ _D <;> by_cases hu :
              ∃ s : ↥S, g p ∈ (s : Tiling.Plane) +ᵥ K.openCarrier <;>
            simp [hd, hu]
        rw [heq]
        exact (hA.inter hB).union (hA.compl.inter hB.compl)
      have hPae : ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume, P q x := by
        simpa [P] using hslice
      have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, P p.1 p.2 :=
        (Measure.ae_prod_iff_ae_ae hP).2 hPae
      have hplane :=
        Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprod
      filter_upwards [hplane] with z hz
      simpa [P, g, slicePoint, Region.openCarrier] using hz
  | horizontal =>
      let P : ℝ → ℝ → Prop := fun q x =>
        (slicePoint Axis.horizontal q x ∈ _D ↔
          ∃ s : ↥S, slicePoint Axis.horizontal q x ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier)
      let g : ℝ × ℝ → Tiling.Plane := fun p ↦
        (p.2 : ℂ) + (p.1 : ℂ) * Complex.I
      have hg : Measurable g := by
        fun_prop
      let A : Set (ℝ × ℝ) := g ⁻¹' _D
      let B : Set (ℝ × ℝ) := {p | ∃ s : ↥S, g p ∈
        (s : Tiling.Plane) +ᵥ K.openCarrier}
      have hA : MeasurableSet A := hD.preimage hg
      have hB0 : MeasurableSet (g ⁻¹' openUnion K S) := hopen.measurableSet.preimage hg
      have hBeq : B = g ⁻¹' openUnion K S := by
        ext p
        change (∃ s : ↥S, g p ∈ (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
          g p ∈ openUnion K S
        constructor
        · rintro ⟨s, hs⟩
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
          exact ⟨s, hs⟩
        · intro _hp
          rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion] at _hp
          obtain ⟨s, hs⟩ := _hp
          exact ⟨s, hs⟩
      have hB : MeasurableSet B := hBeq ▸ hB0
      have hP : MeasurableSet {p : ℝ × ℝ | P p.1 p.2} := by
        have heq : {p : ℝ × ℝ | P p.1 p.2} = (A ∩ B) ∪ (Aᶜ ∩ Bᶜ) := by
          ext p
          change ((g p ∈ _D ↔ ∃ s : ↥S, g p ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier) ↔
            ((g p ∈ _D ∧ (∃ s : ↥S, g p ∈
              (s : Tiling.Plane) +ᵥ K.openCarrier)) ∨
              (g p ∉ _D ∧ ¬ (∃ s : ↥S, g p ∈
                (s : Tiling.Plane) +ᵥ K.openCarrier))))
          by_cases hd : g p ∈ _D <;> by_cases hu :
              ∃ s : ↥S, g p ∈ (s : Tiling.Plane) +ᵥ K.openCarrier <;>
            simp [hd, hu]
        rw [heq]
        exact (hA.inter hB).union (hA.compl.inter hB.compl)
      have hPae : ∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume, P q x := by
        simpa [P] using hslice
      have hprod : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, P p.1 p.2 :=
        (Measure.ae_prod_iff_ae_ae hP).2 hPae
      have hprodSwap : ∀ᵐ p : ℝ × ℝ ∂volume.prod volume, P p.2 p.1 := by
        have hs :=
          (Measure.measurePreserving_swap (μ := volume) (ν := volume)).quasiMeasurePreserving.ae
            hprod
        simpa [Function.comp_def, Prod.swap] using hs
      have hplane :=
        Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving.ae hprodSwap
      filter_upwards [hplane] with z hz
      simpa [P, g, slicePoint, Region.openCarrier] using hz


private theorem sourceBand_chamberChain_transport_impl :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ) (q : ℝ) {n : ℕ}
      (x : Fin (n + 1) → ℝ)
      (xLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      IsSourceBandSliceChain C q x xLift owner →
        StrictMono (fun i ↦ mapScalar φ (xLift i)) ∧
        ∀ i : Fin n,
          {z : Tiling.Plane | z.im = q ∧
            z.re ∈ Ioo (mapScalar φ (xLift i.castSucc))
              (mapScalar φ (xLift i.succ))} ⊆
            mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ
              _D.firstRegion.openCarrier := by
  intro C P ε _hFine φ _hφ _D q n x xLift owner hchain
  rcases hchain with ⟨hLift, hmono, hsteps⟩
  constructor
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ := hsteps i
    have hvw : v.re < w.re := by
      have hpositive' : 0 < w.re - v.re := by simpa using hpositive
      linarith
    rw [endpoint_formula _D v _hv (owner i) (x i.castSucc) (xLift i.castSucc)
      (hLift i.castSucc) hleft,
      endpoint_formula _D w hw (owner i) (x i.succ) (xLift i.succ)
      (hLift i.succ) hright]
    simpa [add_comm] using
      (add_lt_add_right (_D.firstHomeomorph_strictMono hvw)
        (mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2)).re)
  · intro i
    obtain ⟨v, w, _hv, hw, hleft, hright, hpositive, hinside⟩ := hsteps i
    exact gap_transport _D (xLift i.castSucc) (xLift i.succ) (owner i) v w _hv hw
      (hLift i.castSucc) (hLift i.succ) hleft hright hinside


private theorem tilesOn_of_axisSlices :
    ∀ (K : Region) (S _D : Set Tiling.Plane) (axis : Axis),
      MeasurableSet _D →
      S.Countable →
      Set.Pairwise S
        (Disjoint on ((· +ᵥ K.openCarrier) : Tiling.Plane → Set Tiling.Plane)) →
      (∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
        (slicePoint axis q x ∈ _D ↔
          ∃ s : ↥S, slicePoint axis q x ∈
            (s : Tiling.Plane) +ᵥ K.openCarrier)) →
      TilesOn K S _D := by
  exact tilesOn_of_axisSlices_impl

private theorem periodicIntEnumeration_exists :
    ∀ (E : Set ℝ) (p : ℝ), 0 < p → E.Nonempty →
      (∀ Q : Set ℝ, Bornology.IsBounded Q → (E ∩ Q).Finite) →
      p +ᵥ E = E → Nonempty (PeriodicIntEnumeration E p) := by
  intro E p _hp hE hfinite hperiod
  exact Tiling.AxisParallel.OneDimensional.periodicIntEnumeration_exists
    E p _hp hE hfinite hperiod

private theorem verticalCylinder_boundaryCoordinateWitness :
    ∀ (C : ApproximationContext.{u}) (X : Set ℝ), IsOpen X →
      interior (closure X) = X →
      TilesOn C.region C.centres {z : Tiling.Plane | z.re ∈ X} →
      ∀ x ∈ frontier X, ∃ (v : Tiling.Plane) (_hv : v ∈ C.region.vertices)
        (t : Tiling.Plane) (_ht : t ∈ C.centres), x = (v + t).re := by
  exact verticalCylinder_boundaryCoordinateWitnessStatement_proof

private theorem bandPeriod_mem_coordinateSpace :
    ∀ (C : ApproximationContext.{u}) (X : Set ℝ) (p : ℝ),
      (frontier X).Nonempty → p +ᵥ frontier X = frontier X →
      (∀ x ∈ frontier X, x ∈ C.coordinateSpace) → p ∈ C.coordinateSpace := by
  intro C X p hne hperiod hmem
  obtain ⟨x, hx⟩ := hne
  have hxshift : x + p ∈ frontier X := by
    rw [← hperiod]
    exact Set.mem_vadd_set.mpr
      ⟨x, hx, by simp only [vadd_eq_add, add_comm]⟩
  have hxp : x + p ∈ C.coordinateSpace := hmem (x + p) hxshift
  have hdiff : (x + p) - x ∈ C.coordinateSpace :=
    C.coordinateSpace.sub_mem hxp (hmem x hx)
  simpa [add_sub_cancel_left] using hdiff

private theorem deformedBoundary_strictMono :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ),
      IsEpsilonApproximation C ε φ → StrictMono (P.deformedBoundary φ) := by
  intro C P ε _hFine φ _hφ
  exact deformedBoundary_strictMono_impl P ε _hFine φ _hφ

private theorem periodicBoundaryHomeomorph_exists :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ),
      ∃ H : ℝ ≃ₜ ℝ, StrictMono H ∧
        (∀ j : ℤ, H (P.boundary j) = P.deformedBoundary φ j) ∧
        (∀ x : ℝ, H (x + P.period) = H x +
          mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩) := by
  exact periodicBoundaryHomeomorph_exists_impl

private theorem deformedBandBase_eq_image :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (H : ℝ ≃ₜ ℝ),
      StrictMono H →
      (∀ j : ℤ, H (P.boundary j) = P.deformedBoundary φ j) →
        deformedBandBase P φ = H '' P.base := by
  exact deformedBandBase_eq_image_impl

private theorem deformedBandBase_geometry :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ),
      IsOpen (deformedBandBase P φ) ∧
      interior (closure (deformedBandBase P φ)) = deformedBandBase P φ ∧
      (deformedBandBase P φ).Nonempty ∧
      deformedBandBase P φ ≠ Set.univ ∧
      0 < mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ ∧
      mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ +ᵥ
        deformedBandBase P φ = deformedBandBase P φ ∧
      frontier (deformedBandBase P φ) = Set.range (P.deformedBoundary φ) ∧
      ∀ j : ℤ, P.occupied j = true ↔
        Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) ⊆
          deformedBandBase P φ := by
  exact deformedBandBase_geometry_impl

private theorem sourceBand_chamberChains :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
      ∀ᵐ q : ℝ ∂volume, ∀ j : ℤ, P.occupied j = true →
        ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
          (xLift : Fin (n + 1) → C.coordinateSpace)
          (owner : Fin n → ↥C.centres),
          x 0 = P.boundary j ∧ x (Fin.last n) = P.boundary (j + 1) ∧
            IsSourceBandSliceChain C q x xLift owner := by
  exact sourceBand_chamberChains_unconditional_impl

private theorem sourceBand_chamberChain_transport :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ) (q : ℝ) {n : ℕ}
      (x : Fin (n + 1) → ℝ) (xLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      IsSourceBandSliceChain C q x xLift owner →
        StrictMono (fun i ↦ mapScalar φ (xLift i)) ∧
        ∀ i : Fin n,
          {z : Tiling.Plane | z.im = q ∧
            z.re ∈ Ioo (mapScalar φ (xLift i.castSucc))
              (mapScalar φ (xLift i.succ))} ⊆
            mapFirstPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ
              _D.firstRegion.openCarrier := by
  exact sourceBand_chamberChain_transport_impl

private theorem sourceBand_globalSliceChains :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C),
      ∀ᵐ q : ℝ ∂volume, ∀ a b : ℝ, a < b →
        ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
          (xLift : Fin (n + 1) → C.coordinateSpace)
          (step : Fin n → Sum ↥C.centres ℤ),
          x 0 ≤ a ∧ b ≤ x (Fin.last n) ∧
            IsSourceBandGlobalSliceChain C P q x xLift step := by
  exact sourceBand_globalSliceChains_impl

private theorem sourceBand_globalSliceChain_transport :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ) (q : ℝ) {n : ℕ}
      (x : Fin (n + 1) → ℝ)
      (xLift : Fin (n + 1) → C.coordinateSpace)
      (step : Fin n → Sum ↥C.centres ℤ),
      IsSourceBandGlobalSliceChain C P q x xLift step →
        StrictMono (fun i ↦ mapScalar φ (xLift i)) ∧
        ∀ i : Fin n,
          match step i with
          | .inl t =>
              {z : Tiling.Plane | z.im = q ∧
                z.re ∈ Ioo (mapScalar φ (xLift i.castSucc))
                  (mapScalar φ (xLift i.succ))} ⊆
                mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
                  _D.firstRegion.openCarrier
          | .inr _ =>
              Ioo (mapScalar φ (xLift i.castSucc))
                (mapScalar φ (xLift i.succ)) ∩ deformedBandBase P φ = ∅ := by
  exact sourceBand_globalSliceChain_transport_impl

private theorem firstStage_allSectionComponents_transport :
    ∀ {C : ApproximationContext.{u}}
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (_D : CoordinateDeformation C φ)
      (t : ↥C.centres) (q : ℝ),
      placedAxisSlice _D.firstRegion
          (mapFirstPoint φ (C.centrePoint t.1 t.2)) Axis.horizontal q =
        firstStageRunningMap φ _D t ''
          placedAxisSlice C.region t.1 Axis.horizontal q := by
  exact firstStage_allSectionComponents_transport_impl

private theorem firstStage_globalGenericSliceOrder :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ),
      ∀ᵐ q : ℝ ∂volume, ∀ s t : ↥C.centres, ∀ x y : ℝ,
        x ∈ placedAxisSlice C.region s.1 Axis.horizontal q →
        y ∈ placedAxisSlice C.region t.1 Axis.horizontal q →
        x < y → firstStageRunningMap φ _D s x < firstStageRunningMap φ _D t y := by
  exact firstStage_globalGenericSliceOrder_impl

private theorem firstStageCentreMap_injective :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ),
      Function.Injective
        (fun t : ↥C.centres => mapFirstPoint φ (C.centrePoint t.1 t.2)) := by
  exact firstStageCentreMap_injective_impl firstStage_globalGenericSliceOrder_impl

private theorem firstStage_properCylinderSlices :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ),
      (∀ t : ↥C.centres,
        mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier ⊆
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) ∧
      (∀ s t : ↥C.centres, s ≠ t →
        Disjoint
          (mapFirstPoint φ (C.centrePoint s.1 s.2) +ᵥ _D.firstRegion.openCarrier)
          (mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier)) ∧
      (∀ᵐ q : ℝ ∂volume, ∀ᵐ x : ℝ ∂volume,
        (x ∈ deformedBandBase P φ ↔
          ∃ t : ↥C.centres,
            slicePoint Axis.horizontal q x ∈
              mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ
                _D.firstRegion.openCarrier)) := by
  exact firstStage_properCylinderSlices_unconditional_impl

private theorem periodicBand_firstStageTilesOn :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (_D : CoordinateDeformation C φ),
      ∃ T₁ : ↥C.centres ↪ Tiling.Plane,
        (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn _D.firstRegion (deformedCenterCarrier T₁)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
  intro C P ε _hFine φ _hφ _D
  have hproper := firstStage_properCylinderSlices P ε _hFine φ _hφ _D
  have _hgeom := deformedBandBase_geometry P ε _hFine φ _hφ
  have hinj := firstStageCentreMap_injective P ε _hFine φ _hφ _D
  let f : ↥C.centres → Tiling.Plane :=
    fun t => mapFirstPoint φ (C.centrePoint t.1 t.2)
  let T₁ : ↥C.centres ↪ Tiling.Plane :=
    ⟨f, by
      intro s t hst
      exact hinj hst⟩
  refine ⟨T₁, ?_, ?_⟩
  · intro t
    rfl
  · apply tilesOn_of_axisSlices _D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} Axis.horizontal
    · exact _hgeom.1.measurableSet.preimage Complex.continuous_re.measurable
    · let _ : Countable ↥C.centres := P.source_tilesOn.1.to_subtype
      exact Set.countable_range T₁
    · intro s hs t _ht hst
      obtain ⟨s, rfl⟩ := hs
      obtain ⟨t, rfl⟩ := _ht
      exact hproper.2.1 s t (by
        intro heq
        exact hst (congrArg T₁ heq))
    · filter_upwards [hproper.2.2] with q hq
      filter_upwards [hq] with x hx
      constructor
      · intro hxD
        have hxbase : x ∈ deformedBandBase P φ := by
          simpa [slicePoint] using hxD
        obtain ⟨t, _ht⟩ := hx.mp hxbase
        refine ⟨⟨T₁ t, ⟨t, rfl⟩⟩, ?_⟩
        change slicePoint Axis.horizontal q x ∈
          mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier
        exact _ht
      · rintro ⟨s, hs⟩
        rcases s.property with ⟨t, ht⟩
        rw [← ht] at hs
        change slicePoint Axis.horizontal q x ∈
          mapFirstPoint φ (C.centrePoint t.1 t.2) +ᵥ _D.firstRegion.openCarrier at hs
        have hbase := hx.mpr ⟨t, hs⟩
        simpa [slicePoint] using hbase

private def secondStageRunningMap {C : ApproximationContext}
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C φ)
    (t : ↥C.centres) (y : ℝ) : ℝ :=
  mapScalar φ ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ +
    D.secondHomeomorph (y - t.1.im)

private theorem second_endpoint_formula
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).im) :
    mapScalar φ xLift = D.secondHomeomorph v.im +
      (mapPoint φ (C.centrePoint t.1 t.2)).im := by
  let vi : C.coordinateSpace := ⟨v.im, C.vertex_im_mem v hv⟩
  let ti : C.coordinateSpace := ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
  have hxl : xLift = vi + ti := by
    apply Subtype.ext
    simp [vi, ti, hLift, hx]
  have hvertex := congrArg Complex.im (D.vertex_agreement v hv)
  have hvertex' : mapScalar φ vi = D.secondHomeomorph v.im := by
    simpa [vi, mapPoint, ApproximationContext.vertexPoint,
      D.planarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((φ vi : ℚ) : ℝ) = mapScalar φ vi by rfl, hvertex']
  congr 1
  simp [ti, mapPoint, mapScalar, ApproximationContext.centrePoint]

private theorem secondStage_allSectionComponents_transport :
    ∀ {C : ApproximationContext.{u}}
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C φ)
      (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (t : ↥C.centres) (q : ℝ),
      placedAxisSlice D.deformedRegion
          (mapPoint φ (C.centrePoint t.1 t.2)) Axis.vertical q =
        secondStageRunningMap φ D t ''
          placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q := by
  intro C φ D T₁ _hT₁ t q
  let c₁ : Tiling.Plane := T₁ t
  let c₂ : Tiling.Plane := mapPoint φ (C.centrePoint t.1 t.2)
  have hc₁ : c₁ = mapFirstPoint φ (C.centrePoint t.1 t.2) := _hT₁ t
  have hc₁_re : c₁.re = mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
    rw [hc₁]
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  have hc₁_im : c₁.im = t.1.im := by
    rw [hc₁]
    simp [mapFirstPoint, ApproximationContext.centrePoint]
  have hc₂_re : c₂.re = c₁.re := by
    rw [hc₁]
    simp [c₂, mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  have hc₂_im : c₂.im = mapScalar φ
      ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := by
    simp [c₂, mapPoint, ApproximationContext.centrePoint]
  ext y
  constructor
  · intro hy
    change slicePoint Axis.vertical q y ∈ c₂ +ᵥ D.deformedRegion.openCarrier at hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier] at hy
    obtain ⟨k, hk, hkmap⟩ := hy
    let y' := c₁.im + k.im
    have hkim : D.secondHomeomorph k.im = y - c₂.im := by
      have h := congrArg Complex.im hkmap
      simp only [D.planarHomeomorph_apply, Complex.add_im,
        Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, Complex.ofReal_im, zero_mul] at h
      convert h using 1
      all_goals
        simp [slicePoint] <;> try ring
    have hrun : secondStageRunningMap φ D t y' = y := by
      dsimp [secondStageRunningMap, y']
      rw [← hc₂_im]
      rw [show c₁.im + k.im - t.1.im = k.im by rw [hc₁_im]; ring]
      rw [hkim]
      ring
    refine ⟨y', ?_, hrun⟩
    change slicePoint Axis.vertical q y' ∈ c₁ +ᵥ D.firstRegion.openCarrier
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.firstRegion_openCarrier]
    refine ⟨k, hk, ?_⟩
    apply Complex.ext
    · have h := congrArg Complex.re hkmap
      rw [D.firstPlanarHomeomorph_apply]
      simp only [Complex.add_re,
        D.planarHomeomorph_apply, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im,
        mul_zero, Complex.ofReal_im, zero_mul, sub_zero, vadd_eq_add] at h
      simp only [vadd_eq_add, slicePoint,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, zero_mul, sub_zero]
      have h' : D.firstHomeomorph k.re = q - c₂.re := by
        convert h using 1
        all_goals
          simp [slicePoint] <;> try ring
      rw [hc₂_re] at h'
      convert h' using 1
      all_goals
        simp <;> try ring
    · rw [D.firstPlanarHomeomorph_apply]
      simp [vadd_eq_add, slicePoint, y']
  · rintro ⟨y, hy, rfl⟩
    change slicePoint Axis.vertical
      q (secondStageRunningMap φ D t y) ∈ c₂ +ᵥ D.deformedRegion.openCarrier
    change slicePoint Axis.vertical q y ∈ c₁ +ᵥ D.firstRegion.openCarrier at hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.firstRegion_openCarrier] at hy
    obtain ⟨k, hk, hkmap⟩ := hy
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier]
    refine ⟨k, hk, ?_⟩
    apply Complex.ext
    · have h := congrArg Complex.re hkmap
      have hkreal : D.firstHomeomorph k.re = q - c₁.re := by
        simp only [D.firstPlanarHomeomorph_apply, Complex.add_re,
          Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          mul_zero, Complex.ofReal_im, zero_mul, sub_zero] at h
        convert h using 1
        all_goals
          simp [slicePoint] <;> try ring
      rw [D.planarHomeomorph_apply]
      simp [slicePoint, hkreal, hc₂_re]
      ring
    · have h := congrArg Complex.im hkmap
      have hsecond : k.im = y - c₁.im := by
        rw [D.firstPlanarHomeomorph_apply] at h
        simp only [Complex.add_im,
          Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
          mul_one, Complex.ofReal_im, zero_mul] at h
        convert h using 1
        all_goals
          simp [slicePoint] <;> try ring
      rw [D.planarHomeomorph_apply]
      simp only [Complex.add_im,
        Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        mul_one, Complex.ofReal_im, zero_mul]
      have hrun : secondStageRunningMap φ D t y =
          c₂.im + D.secondHomeomorph (y - c₁.im) := by
        simp [secondStageRunningMap, hc₂_im, hc₁_im]
      simp [slicePoint, hrun, hsecond]
private def IsSecondStageBandSliceChain
    (C : ApproximationContext) (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (q : ℝ) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (yLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres) : Prop :=
  (∀ i, (yLift i : ℝ) = y i) ∧ StrictMono y ∧
    ∀ i : Fin n, ∃ v w : Tiling.Plane,
      v ∈ C.region.vertices ∧ w ∈ C.region.vertices ∧
      y i.castSucc = (v + (owner i : Tiling.Plane)).im ∧
      y i.succ = (w + (owner i : Tiling.Plane)).im ∧
      0 < (w - v).im ∧
      {z : Tiling.Plane |
          z.re = q ∧ z.im ∈ Ioo (y i.castSucc) (y i.succ)} ⊆
        T₁ (owner i) +ᵥ D.firstRegion.openCarrier

private def secondStage_sourceSliceChainsSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
    (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
    ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
      ∀ a b : ℝ, a < b →
        ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
          (yLift : Fin (n + 1) → C.coordinateSpace)
          (owner : Fin n → ↥C.centres),
          y 0 ≤ a ∧ b ≤ y (Fin.last n) ∧
            IsSecondStageBandSliceChain C φ D T₁ q y yLift owner

private def secondStage_targetExhaustingSliceChainsSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
    ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
      ∀ a b : ℝ, a < b →
        ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
          (yLift : Fin (n + 1) → C.coordinateSpace)
          (owner : Fin n → ↥C.centres),
          mapScalar φ (yLift 0) ≤ a ∧
            b ≤ mapScalar φ (yLift (Fin.last n)) ∧
            IsSecondStageBandSliceChain C φ D T₁ q y yLift owner

private theorem secondStage_vertical_fibre_ae
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
    (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) :
    ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
      {y : ℝ | slicePoint Axis.vertical q y ∈
        openUnion D.firstRegion (deformedCenterCarrier T₁)} =ᵐ[volume] univ := by
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      z.re ∈ deformedBandBase P φ →
        z ∈ openUnion D.firstRegion (deformedCenterCarrier T₁) := by
    filter_upwards [_hTiles.2.2] with z hz hzbase
    exact Set.mem_iUnion.mpr (hz.mp hzbase)
  have hpull := Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae hplane
  have hslices := MeasureTheory.Measure.ae_ae_of_ae_prod
    (μ := volume) (ν := volume) hpull
  filter_upwards [hslices] with q _hq
  intro _hqbase
  filter_upwards [_hq] with y hy
  apply propext
  constructor
  · intro _
    exact Set.mem_univ y
  · intro _
    change slicePoint Axis.vertical q y ∈
      openUnion D.firstRegion (deformedCenterCarrier T₁)
    have heq : slicePoint Axis.vertical q y =
        Complex.measurableEquivRealProd.symm (q, y) := by
      apply Complex.ext <;> simp [slicePoint]
    rw [heq]
    exact hy _hqbase

private theorem secondStage_endpoint_formula
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (v : Tiling.Plane)
    (hv : v ∈ C.region.vertices) (t : ↥C.centres)
    (x : ℝ) (xLift : C.coordinateSpace) (hLift : (xLift : ℝ) = x)
    (hx : x = (v + (t : Tiling.Plane)).im) :
    mapScalar φ xLift = D.secondHomeomorph v.im +
      (mapPoint φ (C.centrePoint t.1 t.2)).im := by
  let vi : C.coordinateSpace := ⟨v.im, C.vertex_im_mem v hv⟩
  let ti : C.coordinateSpace := ⟨t.1.im, C.centre_im_mem t.1 t.2⟩
  have hxl : xLift = vi + ti := by
    apply Subtype.ext
    simp [vi, ti, hLift, hx]
  have hvertex := congrArg Complex.im (D.vertex_agreement v hv)
  have hvertex' : mapScalar φ vi = D.secondHomeomorph v.im := by
    simpa [vi, mapPoint, ApproximationContext.vertexPoint,
      D.planarHomeomorph_apply] using hvertex.symm
  rw [hxl, mapScalar, map_add, Rat.cast_add]
  rw [show ((φ vi : ℚ) : ℝ) = mapScalar φ vi by rfl, hvertex']
  congr 1
  simp [ti, mapPoint, mapScalar, ApproximationContext.centrePoint]

private theorem secondStage_chain_of_indexed
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
    (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ})
    {q a b : ℝ} (_hq : q ∈ deformedBandBase P φ) (_hab : a < b)
    (hindexed : ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
      (ownerA : Fin n → ↥(deformedCenterCarrier T₁)),
      y 0 ≤ a ∧ b ≤ y (Fin.last n) ∧
        IsFilledIndexedSliceChain D.firstRegion
          (deformedCenterCarrier T₁) Axis.vertical q y ownerA) :
    ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
      (yLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      y 0 ≤ a ∧ b ≤ y (Fin.last n) ∧
        IsSecondStageBandSliceChain C φ D T₁ q y yLift owner := by
  obtain ⟨n, hn, y, ownerA, hya, hyb, hchain⟩ := hindexed
  let carrierEquiv := deformedCenterEquivCarrier T₁
  let owner : Fin n → ↥C.centres := fun i => carrierEquiv.symm (ownerA i)
  have howner (i : Fin n) :
      T₁ (owner i) = (ownerA i : Tiling.Plane) := by
    have h := carrierEquiv.apply_symm_apply (ownerA i)
    exact congrArg Subtype.val h
  have sourceVertex (v : Tiling.Plane) (hv : v ∈ D.firstRegion.vertices) :
      ∃ v₀ ∈ C.region.vertices, D.firstPlanarHomeomorph v₀ = v := by
    have himage : D.firstRegion.vertices =
        D.firstPlanarHomeomorph '' C.region.vertices := by
      obtain ⟨L, _hsupport, hopen, hvertices⟩ :=
        exists_coordinateProductImageRegion C.region D.firstHomeomorph
          (Homeomorph.refl ℝ) D.firstHomeomorph_strictMono strictMono_id
      have hplanar : coordinateProductHomeomorph
          D.firstHomeomorph (Homeomorph.refl ℝ) = D.firstPlanarHomeomorph := by
        ext z
        rw [D.firstPlanarHomeomorph_apply]
        apply Complex.ext <;> simp [coordinateProductHomeomorph]
      have hregion : L = D.firstRegion := by
        apply region_ext_openCarrier
        rw [hopen, hplanar, D.firstRegion_openCarrier]
      rw [← hregion, hvertices, hplanar]
    rw [himage] at hv
    simpa only [Set.mem_image] using hv
  have endpoint_mem (i : Fin (n + 1)) : y i ∈ C.coordinateSpace := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · let j : Fin n := ⟨n - 1, by omega⟩
      obtain ⟨v, w, hv, hw, hleft, hright, _hpos, hins⟩ := hchain.2 j
      obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
      have hi : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (ownerA j : Tiling.Plane).im = (owner j : Tiling.Plane).im := by
        rw [← howner j]
        simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
      rw [show Fin.last n = j.succ by
        apply Fin.ext
        simp [j, Nat.sub_add_cancel hn]]
      rw [hright, ← hwmap]
      change (D.firstPlanarHomeomorph w₀).im +
        (ownerA j : Tiling.Plane).im ∈ C.coordinateSpace
      rw [hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem w₀ hw₀)
        (C.centre_im_mem _ (owner j).2)
    · obtain ⟨v, w, hv, hw, hleft, hright, _hpos, hins⟩ := hchain.2 j
      obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
      have hi : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (ownerA j : Tiling.Plane).im = (owner j : Tiling.Plane).im := by
        rw [← howner j]
        simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
      rw [hleft, ← hvmap]
      change (D.firstPlanarHomeomorph v₀).im +
        (ownerA j : Tiling.Plane).im ∈ C.coordinateSpace
      rw [hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₀ hv₀)
        (C.centre_im_mem _ (owner j).2)
  let yLift : Fin (n + 1) → C.coordinateSpace := fun i => ⟨y i, endpoint_mem i⟩
  refine ⟨n, hn, y, yLift, owner, hya, hyb, ?_⟩
  refine ⟨?_, hchain.1, ?_⟩
  · intro i
    rfl
  · intro i
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, hins⟩ := hchain.2 i
    obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
    obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
    have hvim : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
      rw [D.firstPlanarHomeomorph_apply]
      simp
    have hwim : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
      rw [D.firstPlanarHomeomorph_apply]
      simp
    have htim : (ownerA i : Tiling.Plane).im = (owner i : Tiling.Plane).im := by
      rw [← howner i]
      simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
    refine ⟨v₀, w₀, hv₀, hw₀, ?_, ?_, ?_, ?_⟩
    · simpa [← hvmap, htim, Axis.coord, Complex.add_im, hvim] using hleft
    · simpa [← hwmap, htim, Axis.coord, Complex.add_im, hwim] using hright
    · simpa [← hvmap, ← hwmap, Axis.coord, Complex.sub_im, hvim, hwim] using _hpos
    · rw [howner i]
      exact hins

private theorem secondStage_chain_of_exact_indexed
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
    (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ})
    {q : ℝ} {n : ℕ} (hn : 0 < n) (y : Fin (n + 1) → ℝ)
    (ownerA : Fin n → ↥(deformedCenterCarrier T₁))
    (hchain : IsFilledIndexedSliceChain D.firstRegion
      (deformedCenterCarrier T₁) Axis.vertical q y ownerA) :
    ∃ (yLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      (∀ i, (yLift i : ℝ) = y i) ∧
        IsSecondStageBandSliceChain C φ D T₁ q y yLift owner := by
  let carrierEquiv := deformedCenterEquivCarrier T₁
  let owner : Fin n → ↥C.centres := fun i => carrierEquiv.symm (ownerA i)
  have howner (i : Fin n) :
      T₁ (owner i) = (ownerA i : Tiling.Plane) := by
    have h := carrierEquiv.apply_symm_apply (ownerA i)
    exact congrArg Subtype.val h
  have sourceVertex (v : Tiling.Plane) (hv : v ∈ D.firstRegion.vertices) :
      ∃ v₀ ∈ C.region.vertices, D.firstPlanarHomeomorph v₀ = v := by
    have himage : D.firstRegion.vertices =
        D.firstPlanarHomeomorph '' C.region.vertices := by
      obtain ⟨L, _hsupport, hopen, hvertices⟩ :=
        exists_coordinateProductImageRegion C.region D.firstHomeomorph
          (Homeomorph.refl ℝ) D.firstHomeomorph_strictMono strictMono_id
      have hplanar : coordinateProductHomeomorph
          D.firstHomeomorph (Homeomorph.refl ℝ) = D.firstPlanarHomeomorph := by
        ext z
        rw [D.firstPlanarHomeomorph_apply]
        apply Complex.ext <;> simp [coordinateProductHomeomorph]
      have hregion : L = D.firstRegion := by
        apply region_ext_openCarrier
        rw [hopen, hplanar, D.firstRegion_openCarrier]
      rw [← hregion, hvertices, hplanar]
    rw [himage] at hv
    simpa only [Set.mem_image] using hv
  have endpoint_mem (i : Fin (n + 1)) : y i ∈ C.coordinateSpace := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · let j : Fin n := ⟨n - 1, by omega⟩
      obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ := hchain.2 j
      obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
      have hi : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (ownerA j : Tiling.Plane).im = (owner j : Tiling.Plane).im := by
        rw [← howner j]
        simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
      rw [show Fin.last n = j.succ by
        apply Fin.ext
        simp [j, Nat.sub_add_cancel hn]]
      rw [hright, ← hwmap]
      change (D.firstPlanarHomeomorph w₀).im +
        (ownerA j : Tiling.Plane).im ∈ C.coordinateSpace
      rw [hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem w₀ hw₀)
        (C.centre_im_mem _ (owner j).2)
    · obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ := hchain.2 j
      obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
      have hi : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have ht : (ownerA j : Tiling.Plane).im = (owner j : Tiling.Plane).im := by
        rw [← howner j]
        simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
      rw [hleft, ← hvmap]
      change (D.firstPlanarHomeomorph v₀).im +
        (ownerA j : Tiling.Plane).im ∈ C.coordinateSpace
      rw [hi, ht]
      exact C.coordinateSpace.add_mem (C.vertex_im_mem v₀ hv₀)
        (C.centre_im_mem _ (owner j).2)
  let yLift : Fin (n + 1) → C.coordinateSpace := fun i => ⟨y i, endpoint_mem i⟩
  refine ⟨yLift, owner, ?_, ?_⟩
  · intro i
    rfl
  · refine ⟨?_, hchain.1, ?_⟩
    · intro i
      rfl
    · intro i
      obtain ⟨v, w, hv, hw, hleft, hright, _hpos, hins⟩ := hchain.2 i
      obtain ⟨v₀, hv₀, hvmap⟩ := sourceVertex v hv
      obtain ⟨w₀, hw₀, hwmap⟩ := sourceVertex w hw
      have hvim : (D.firstPlanarHomeomorph v₀).im = v₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have hwim : (D.firstPlanarHomeomorph w₀).im = w₀.im := by
        rw [D.firstPlanarHomeomorph_apply]
        simp
      have htim : (ownerA i : Tiling.Plane).im = (owner i : Tiling.Plane).im := by
        rw [← howner i]
        simp [_hT₁, mapFirstPoint, ApproximationContext.centrePoint]
      refine ⟨v₀, w₀, hv₀, hw₀, ?_, ?_, ?_, ?_⟩
      · simpa [← hvmap, htim, Axis.coord, Complex.add_im, hvim] using hleft
      · simpa [← hwmap, htim, Axis.coord, Complex.add_im, hwim] using hright
      · simpa [← hvmap, ← hwmap, Axis.coord, Complex.sub_im, hvim, hwim] using _hpos
      · rw [howner i]
        exact hins

private theorem secondStage_sourceSliceChains_impl :
    secondStage_sourceSliceChainsSpec.{u} := by
  intro C P φ D T₁ _hT₁ _hTiles
  filter_upwards [
    genericIndexedSliceChain_of_ae_univ
      D.firstRegion (deformedCenterCarrier T₁) _hTiles.2.1 Axis.vertical,
    secondStage_vertical_fibre_ae D T₁ _hTiles] with q hindexed hfull
  intro _hq a b _hab
  have hfull' := hfull _hq
  obtain ⟨n, hn, y, ownerA, hya, hyb, hchain, _hendpoints⟩ :=
    hindexed hfull' a b _hab
  exact secondStage_chain_of_indexed D T₁ _hT₁ _hTiles _hq _hab
    ⟨n, hn, y, ownerA, hya, hyb, hchain⟩
private theorem continuous_slicePoint_local (axis : Axis) (q : ℝ) :
    Continuous (slicePoint axis q) := by
  cases axis <;> unfold slicePoint <;> fun_prop

private theorem secondStage_exists_mem_Ioo_avoiding_finset_local {a b : ℝ} (_hab : a < b)
    (F : Finset ℝ) : ∃ x ∈ Ioo a b, x ∉ F := by
  by_contra h
  push Not at h
  have hsub : Ioo a b ⊆ (F : Set ℝ) := fun x hx => h x hx
  exact Set.Ioo_infinite _hab ((F.finite_toSet).subset hsub)

private theorem secondStageRunningMap_strictMono_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) :
    StrictMono (secondStageRunningMap φ D t) := by
  intro a b _hab
  dsimp [secondStageRunningMap]
  have hsub : a - t.1.im < b - t.1.im := sub_lt_sub_right _hab _
  simpa [add_comm] using add_lt_add_left (D.secondHomeomorph_strictMono hsub)
    (mapScalar φ ⟨t.1.im, C.centre_im_mem t.1 t.2⟩)

private theorem secondStage_chain_mapped_strictMono_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) {q : ℝ} {n : ℕ}
    (T₁ : ↥C.centres ↪ Tiling.Plane)
    (y : Fin (n + 1) → ℝ) (yLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres)
    (hchain : IsSecondStageBandSliceChain C φ D T₁ q y yLift owner) :
    StrictMono (fun i => mapScalar φ (yLift i)) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ := hchain.2.2 i
  have hvw : v.im < w.im := by simpa [Complex.sub_im] using _hpos
  rw [secondStage_endpoint_formula D v hv (owner i) (y i.castSucc)
      (yLift i.castSucc) (hchain.1 _) hleft,
    secondStage_endpoint_formula D w hw (owner i) (y i.succ)
      (yLift i.succ) (hchain.1 _) hright]
  simpa [add_comm] using
    add_lt_add_left (D.secondHomeomorph_strictMono hvw)
      (mapPoint φ (C.centrePoint (owner i).1 (owner i).2)).im

private theorem secondStageRunningMap_gap_bounds_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (s : ↥C.centres)
    {a b r : ℝ} {xLift₀ xLift₁ : C.coordinateSpace}
    (hLift₀ : (xLift₀ : ℝ) = a) (hLift₁ : (xLift₁ : ℝ) = b)
    {v w : Tiling.Plane} (hv : v ∈ C.region.vertices) (hw : w ∈ C.region.vertices)
    (_hpos : 0 < (w - v).im)
    (hleft : a = (v + (s : Tiling.Plane)).im)
    (hright : b = (w + (s : Tiling.Plane)).im)
    (hr : r ∈ Ioo a b) :
    mapScalar φ xLift₀ < secondStageRunningMap φ D s r ∧
      secondStageRunningMap φ D s r < mapScalar φ xLift₁ := by
  have h0 := secondStage_endpoint_formula D v hv s a xLift₀ hLift₀ hleft
  have h1 := secondStage_endpoint_formula D w hw s b xLift₁ hLift₁ hright
  dsimp [secondStageRunningMap]
  rw [h0, h1]
  have hc : mapScalar φ ⟨s.1.im, C.centre_im_mem s.1 s.2⟩ =
      (mapPoint φ (C.centrePoint s.1 s.2)).im := by
    simp [mapPoint, ApproximationContext.centrePoint]
  rw [hc]
  constructor
  · have hvr : v.im < r - s.1.im := by
      have h := hr.1
      rw [hleft] at h
      have ha : a = v.im + s.1.im := by simpa [Complex.add_im] using hleft
      linarith
    simpa [add_comm] using
      add_lt_add_left (D.secondHomeomorph_strictMono hvr)
        (mapPoint φ (C.centrePoint s.1 s.2)).im
  · have hrw : r - s.1.im < w.im := by
      have h := hr.2
      rw [hright] at h
      have hb : b = w.im + s.1.im := by simpa [Complex.add_im] using hright
      linarith
    simpa [add_comm] using
      add_lt_add_left (D.secondHomeomorph_strictMono hrw)
        (mapPoint φ (C.centrePoint s.1 s.2)).im

private theorem exists_four_points_in_two_open_vertical_sections_local
    {q : ℝ} (K : Region) (s t : Tiling.Plane) {x y : ℝ}
    (hx : x ∈ placedAxisSlice K s Axis.vertical q)
    (hy : y ∈ placedAxisSlice K t Axis.vertical q)
    (hxy : x < y) (F : Finset ℝ) :
    ∃ x' y', x < x' ∧ x' < y' ∧ y' < y ∧
      x' ∈ placedAxisSlice K s Axis.vertical q ∧
      y' ∈ placedAxisSlice K t Axis.vertical q ∧
      x' ∉ (F : Set ℝ) ∧ y' ∉ (F : Set ℝ) := by
  have hsopen : IsOpen (placedAxisSlice K s Axis.vertical q) := by
    change IsOpen ((slicePoint Axis.vertical q) ⁻¹'
      (s +ᵥ K.openCarrier))
    exact (K.openCarrier_regularOpen.1.vadd s).preimage
      (continuous_slicePoint_local Axis.vertical q)
  have htopen : IsOpen (placedAxisSlice K t Axis.vertical q) := by
    change IsOpen ((slicePoint Axis.vertical q) ⁻¹'
      (t +ᵥ K.openCarrier))
    exact (K.openCarrier_regularOpen.1.vadd t).preimage
      (continuous_slicePoint_local Axis.vertical q)
  obtain ⟨δs, hδs, hballS⟩ := Metric.isOpen_iff.1 hsopen x hx
  obtain ⟨δt, hδt, hballT⟩ := Metric.isOpen_iff.1 htopen y hy
  let u := min y (x + δs / 2)
  have hxu : x < u := by
    dsimp [u]
    exact lt_min hxy (by linarith)
  obtain ⟨x', hx'I, hx'F⟩ :=
    secondStage_exists_mem_Ioo_avoiding_finset_local hxu F
  let l := max x' (y - δt / 2)
  have hly : l < y := by
    dsimp [l]
    apply max_lt
    · exact lt_of_lt_of_le hx'I.2 (min_le_left _ _)
    · linarith
  obtain ⟨y', hy'I, hy'F⟩ :=
    secondStage_exists_mem_Ioo_avoiding_finset_local hly F
  have hx'close : dist x' x < δs := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hx'I.1, hx'I.2, min_le_right y (x + δs / 2)]
  have hy'close : dist y' y < δt := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy'I.1, hy'I.2, le_max_right x' (y - δt / 2)]
  refine ⟨x', y', hx'I.1, ?_, hy'I.2, ?_, ?_, hx'F, hy'F⟩
  · exact lt_of_le_of_lt (le_max_left x' (y - δt / 2)) hy'I.1
  · exact hballS hx'close
  · exact hballT hy'close

private theorem strictMono_exists_gap_local {n : ℕ} (x : Fin (n + 1) → ℝ)
    (hx : StrictMono x) {a : ℝ} (hleft : x 0 < a)
    (hright : a < x (Fin.last n)) (hne : ∀ k, a ≠ x k) :
    ∃ i : Fin n, a ∈ Ioo (x i.castSucc) (x i.succ) := by
  induction n with
  | zero => exfalso; simpa using (lt_asymm hleft hright)
  | succ n ih =>
      rcases lt_trichotomy a (x 1) with ha | ha | ha
      · exact ⟨⟨0, Nat.succ_pos _⟩, hleft, ha⟩
      · exact False.elim (hne 1 ha)
      · let y : Fin (n + 1) → ℝ := fun k => x k.succ
        have hy : StrictMono y := by
          intro i j hij
          apply hx
          simpa using hij
        have hylast : a < y (Fin.last n) := by
          simpa [y] using hright
        have hyne : ∀ k, a ≠ y k := fun k => hne k.succ
        obtain ⟨i, hi⟩ := ih y hy ha hylast hyne
        refine ⟨i.succ, ?_⟩
        simpa [y] using hi

private def secondStage_globalGenericSliceOrderSpec : Prop :=
  ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
    ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
      ∀ s t : ↥C.centres, ∀ x y : ℝ,
        x ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q →
        y ∈ placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q →
        x < y →
          secondStageRunningMap φ D s x < secondStageRunningMap φ D t y

private theorem secondStage_globalGenericSliceOrder_impl :
    secondStage_globalGenericSliceOrderSpec.{u} := by
  intro C P ε _hFine φ _hφ D T₁ _hT₁ _hTiles
  filter_upwards [secondStage_sourceSliceChains_impl
    (C := C) (P := P) (φ := φ) D T₁ _hT₁ _hTiles] with q hsource
  intro _hq s t x y hx hy hxy
  obtain ⟨n, hn, z, zLift, owner, hzleft, hzright, hwalk⟩ :=
    hsource _hq (x - 1) (y + 1) (by linarith)
  let nodes : Finset ℝ := Finset.univ.image z
  obtain ⟨x', y', hxx', hxy', hy'y, hx', hy', hx'node, hy'node⟩ :=
    exists_four_points_in_two_open_vertical_sections_local D.firstRegion
      (T₁ s) (T₁ t) hx hy hxy nodes
  have hnode (r : ℝ) (hr : r = x' ∨ r = y') : r ∉ Set.range z := by
    intro hrange
    obtain ⟨i, hi⟩ := hrange
    rcases hr with hr | hr
    · apply hx'node
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans hr⟩
    · apply hy'node
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi.trans hr⟩
  obtain ⟨ix, hix⟩ := strictMono_exists_gap_local z hwalk.2.1
    (lt_of_le_of_lt hzleft (lt_trans (by linarith) hxx'))
    (lt_of_lt_of_le (lt_trans hxy' (lt_trans hy'y (by linarith))) hzright)
    (fun i hi => hnode x' (Or.inl rfl) ⟨i, hi.symm⟩)
  obtain ⟨iy, hiy⟩ := strictMono_exists_gap_local z hwalk.2.1
    (lt_of_le_of_lt hzleft (lt_trans (by linarith) hxy'))
    (lt_of_lt_of_le hy'y (le_trans (by linarith) hzright))
    (fun i hi => hnode y' (Or.inr rfl) ⟨i, hi.symm⟩)
  have howner (u : ↥C.centres) (r : ℝ)
      (hrS : r ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q)
      (hrU : r ∈ placedAxisSlice D.firstRegion (T₁ u) Axis.vertical q) :
      u = s := by
    by_contra hus
    have hdisj := (isPacking_iff_openCarrier_disjoint D.firstRegion
      (deformedCenterCarrier T₁)).mp _hTiles.2.1
      (show T₁ u ∈ deformedCenterCarrier T₁ from ⟨u, rfl⟩)
      (show T₁ s ∈ deformedCenterCarrier T₁ from ⟨s, rfl⟩) (by
      intro heq
      exact hus (T₁.injective heq))
    exact Set.disjoint_left.mp hdisj hrU hrS
  have hixowner : owner ix = s := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpositive, hinside⟩ := hwalk.2.2 ix
    apply howner (owner ix) x' hx'
    apply hinside
    exact ⟨by simp [slicePoint], by simpa [slicePoint] using hix⟩
  have hiyowner : owner iy = t := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpositive, hinside⟩ := hwalk.2.2 iy
    have hown : owner iy = t := by
      by_contra hne
      have hdisj := (isPacking_iff_openCarrier_disjoint D.firstRegion
        (deformedCenterCarrier T₁)).mp _hTiles.2.1
        (show T₁ (owner iy) ∈ deformedCenterCarrier T₁ from ⟨owner iy, rfl⟩)
        (show T₁ t ∈ deformedCenterCarrier T₁ from ⟨t, rfl⟩) (by
          intro heq
          exact hne (T₁.injective heq))
      exact Set.disjoint_left.mp hdisj
        (hinside ⟨by simp [slicePoint], by simpa [slicePoint] using hiy⟩) hy'
    exact hown
  have hixiy : ix ≤ iy := by
    by_contra hnot
    have hlt : iy < ix := lt_of_not_ge hnot
    have hfin : iy.succ ≤ ix.castSucc := by
      apply Fin.mk_le_mk.mpr
      omega
    have hzord : z iy.succ ≤ z ix.castSucc := hwalk.2.1.monotone hfin
    linarith [hiy.2, hix.1]
  have hmapmono := secondStage_chain_mapped_strictMono_local D T₁ z zLift owner hwalk
  have hsourceMap : secondStageRunningMap φ D s x' <
      secondStageRunningMap φ D t y' := by
    by_cases heq : ix = iy
    · subst iy
      rw [hixowner] at hiyowner
      subst t
      exact secondStageRunningMap_strictMono_local D s hxy'
    · have hlt : ix < iy := lt_of_le_of_ne hixiy heq
      obtain ⟨vx, wx, hvx, hwx, hxl, hxr, hxp, _⟩ := hixowner ▸ hwalk.2.2 ix
      obtain ⟨vy, wy, hvy, hwy, hyl, hyr, hyp, _⟩ := hiyowner ▸ hwalk.2.2 iy
      have hbx := secondStageRunningMap_gap_bounds_local D s
        (hLift₀ := hwalk.1 ix.castSucc) (hLift₁ := hwalk.1 ix.succ)
        hvx hwx hxp hxl hxr hix
      have hby := secondStageRunningMap_gap_bounds_local D t
        (hLift₀ := hwalk.1 iy.castSucc) (hLift₁ := hwalk.1 iy.succ)
        hvy hwy hyp hyl hyr hiy
      have hchain : mapScalar φ (zLift ix.succ) ≤
          mapScalar φ (zLift iy.castSucc) := by
        apply hmapmono.monotone
        apply Fin.mk_le_mk.mpr
        omega
      exact lt_trans hbx.2 (lt_of_le_of_lt hchain hby.1)
  exact lt_trans (secondStageRunningMap_strictMono_local D s hxx')
    (lt_trans hsourceMap (secondStageRunningMap_strictMono_local D t hy'y))

private theorem finite_step_cofinal_local
    {E : Set ℝ} {f : E → ℝ} (m L : ℝ) (hm : 0 < m) (hL : 0 < L)
    (hE : E.Nonempty)
    (hupper : ∀ _a : E, ∀ r : ℝ, ∃ b : E, r < b.1)
    (hlower : ∀ _a : E, ∀ r : ℝ, ∃ b : E, b.1 < r)
    (hstep : ∀ a b : E, a.1 < b.1 →
      ∃ n : ℕ, 0 < n ∧ b.1 - a.1 ≤ (n : ℝ) * L ∧
        f a + (n : ℝ) * m ≤ f b) :
    ¬ BddAbove (Set.range f) ∧ ¬ BddBelow (Set.range f) := by
  constructor
  · intro hbound
    obtain ⟨M, hM⟩ := hbound
    let a : E := ⟨hE.choose, hE.choose_spec⟩
    obtain ⟨N, hN⟩ := exists_nat_gt ((M - f a) / m)
    obtain ⟨b, hb⟩ := hupper a (a.1 + (N : ℝ) * L)
    have hNLnonneg : 0 ≤ (N : ℝ) * L :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hL)
    obtain ⟨n, hn, hspan, hfspan⟩ := hstep a b
      (lt_of_le_of_lt (le_add_of_nonneg_right hNLnonneg) hb)
    have hnN : (N : ℝ) < n := by
      have hNL : (N : ℝ) * L < b.1 - a.1 := by linarith
      nlinarith
    have hNm : M - f a < (N : ℝ) * m := by
      exact (div_lt_iff₀ hm).mp hN
    have hnm : (N : ℝ) * m ≤ (n : ℝ) * m := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hnN) (le_of_lt hm)
    have hfb : f b ≤ M := hM ⟨b, rfl⟩
    linarith
  · intro hbound
    obtain ⟨M, hM⟩ := hbound
    let a : E := ⟨hE.choose, hE.choose_spec⟩
    obtain ⟨N, hN⟩ := exists_nat_gt ((f a - M) / m)
    obtain ⟨b, hb⟩ := hlower a (a.1 - (N : ℝ) * L)
    have hNLnonneg : 0 ≤ (N : ℝ) * L :=
      mul_nonneg (Nat.cast_nonneg _) (le_of_lt hL)
    obtain ⟨n, hn, hspan, hfspan⟩ := hstep b a
      (lt_of_lt_of_le hb (sub_le_self _ hNLnonneg))
    have hnN : (N : ℝ) < n := by
      have hNL : (N : ℝ) * L < a.1 - b.1 := by linarith
      nlinarith
    have hNm : f a - M < (N : ℝ) * m := by
      exact (div_lt_iff₀ hm).mp hN
    have hnm : (N : ℝ) * m ≤ (n : ℝ) * m := by
      exact mul_le_mul_of_nonneg_right (le_of_lt hnN) (le_of_lt hm)
    have hfb : M ≤ f b := hM ⟨b, rfl⟩
    linarith

private theorem fin_sum_step_sub_local {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (x i.succ - x i.castSucc) =
      x (Fin.last n) - x 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hi := ih (fun i : Fin (n + 1) => x i.castSucc)
      rw [Fin.sum_univ_castSucc]
      calc
        (∑ i : Fin n, (x i.castSucc.succ - x i.castSucc.castSucc)) +
            (x (Fin.last n).succ - x (Fin.last n).castSucc) =
            (x (Fin.last n).castSucc - x 0) +
              (x (Fin.last n).succ - x (Fin.last n).castSucc) := by
                rw [show (∑ i : Fin n,
                  (x i.castSucc.succ - x i.castSucc.castSucc)) =
                    x (Fin.last n).castSucc - x 0 by
                  simpa using hi]
        _ = x (Fin.last (n + 1)) - x 0 := by
          have hlast : (Fin.last n).succ = Fin.last (n + 1) := by
            apply Fin.ext
            rfl
          rw [hlast]
          ring

private theorem secondStage_mappedEndpointCofinality_local :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
        ∃ lift : ↥(sliceEndpointSet D.firstRegion
            (deformedCenterCarrier T₁) Axis.vertical q) → C.coordinateSpace,
          (∀ a, (lift a : ℝ) = a.1) ∧
          StrictMono (fun a => mapScalar φ (lift a)) ∧
          ¬ BddAbove (Set.range (fun a => mapScalar φ (lift a))) ∧
          ¬ BddBelow (Set.range (fun a => mapScalar φ (lift a))) := by
  intro C P φ D T₁ _hT₁ _hTiles
  filter_upwards [
    genericIndexedSliceChain_of_ae_univ D.firstRegion
      (deformedCenterCarrier T₁) _hTiles.2.1 Axis.vertical,
    secondStage_vertical_fibre_ae D T₁ _hTiles,
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints_of_local_ae
      D.firstRegion
      (deformedCenterCarrier T₁) _hTiles.2.1 Axis.vertical] with
      q hindexed hfull hbetween
  intro _hq
  have hfull' := hfull _hq
  have hindexed' := hindexed hfull'
  let E : Set ℝ := sliceEndpointSet D.firstRegion
    (deformedCenterCarrier T₁) Axis.vertical q
  have hcover : ∀ a b : ℝ, a < b →
      ∀ᵐ x : ℝ ∂volume, x ∈ Ioo a b →
        slicePoint Axis.vertical q x ∈
          openUnion D.firstRegion (deformedCenterCarrier T₁) := by
    intro a b _hab
    filter_upwards [hfull'] with x hx hxI
    exact hx.mpr (Set.mem_univ x)
  have hbetween' : ∀ a ∈ E, ∀ b ∈ E, a < b →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (ownerA : Fin n → ↥(deformedCenterCarrier T₁)),
        x 0 = a ∧ x (Fin.last n) = b ∧
          IsFilledIndexedSliceChain D.firstRegion
            (deformedCenterCarrier T₁) Axis.vertical q x ownerA ∧
          (∀ i, x i ∈ E) := by
    intro a ha b hb _hab
    exact hbetween a ha b hb _hab (hcover a b _hab)
  have hE : E.Nonempty := by
    obtain ⟨n, hn, y, ownerA, hya, hyb, hchain, hendpoints⟩ :=
      hindexed' 0 1 zero_lt_one
    exact ⟨y 0, hendpoints _⟩
  have hupper : ∀ a : E, ∀ r : ℝ, ∃ b : E, r < b.1 := by
    intro a r
    obtain ⟨n, hn, y, ownerA, hya, hyb, hchain, hendpoints⟩ :=
      hindexed' (r + 1) (r + 2) (by linarith)
    refine ⟨⟨y (Fin.last n), hendpoints _⟩, ?_⟩
    exact lt_of_lt_of_le (by linarith) hyb
  have hlower : ∀ a : E, ∀ r : ℝ, ∃ b : E, b.1 < r := by
    intro a r
    obtain ⟨n, hn, y, ownerA, hya, hyb, hchain, hendpoints⟩ :=
      hindexed' (r - 2) (r - 1) (by linarith)
    refine ⟨⟨y 0, hendpoints _⟩, ?_⟩
    exact lt_of_le_of_lt hya (by linarith)
  let a₀ : E := ⟨hE.choose, hE.choose_spec⟩
  obtain ⟨b₀, hb₀⟩ := hupper a₀ a₀.1
  obtain ⟨n₀, hn₀, y₀, ownerA₀, hy₀, hy₀last, hchain₀, _⟩ :=
    hbetween' a₀.1 a₀.2 b₀.1 b₀.2 hb₀
  obtain ⟨n₀, hn₀, y₀, yLift₀, owner₀, _, _, hsource₀⟩ :=
    secondStage_chain_of_indexed D T₁ _hT₁ _hTiles _hq hb₀
      ⟨n₀, hn₀, y₀, ownerA₀, hy₀.le, hy₀last.symm.le, hchain₀⟩
  let pairs : Finset (↥C.region.vertexFinset × ↥C.region.vertexFinset) :=
    (Finset.univ.product Finset.univ).filter fun vw => vw.1.1.im < vw.2.1.im
  let rawGaps : Finset ℝ := pairs.image fun vw => vw.2.1.im - vw.1.1.im
  let mappedGaps : Finset ℝ := pairs.image fun vw =>
    D.secondHomeomorph vw.2.1.im - D.secondHomeomorph vw.1.1.im
  have hrawNonempty : rawGaps.Nonempty := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ :=
      hsource₀.2.2 ⟨0, hn₀⟩
    have hvF : v ∈ C.region.vertexFinset :=
      (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
    have hwF : w ∈ C.region.vertexFinset :=
      (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
    have hvw : v.im < w.im := by
      simpa [Axis.coord, Complex.sub_im] using _hpos
    refine ⟨w.im - v.im, ?_⟩
    exact Finset.mem_image.mpr ⟨(⟨v, hvF⟩, ⟨w, hwF⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hvw⟩,
      rfl⟩
  have hmappedNonempty : mappedGaps.Nonempty := by
    obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ :=
      hsource₀.2.2 ⟨0, hn₀⟩
    have hvF : v ∈ C.region.vertexFinset :=
      (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
    have hwF : w ∈ C.region.vertexFinset :=
      (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
    have hvw : v.im < w.im := by
      simpa [Axis.coord, Complex.sub_im] using _hpos
    refine ⟨D.secondHomeomorph w.im - D.secondHomeomorph v.im, ?_⟩
    exact Finset.mem_image.mpr ⟨(⟨v, hvF⟩, ⟨w, hwF⟩),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hvw⟩,
      rfl⟩
  let L : ℝ := rawGaps.max' hrawNonempty
  let m : ℝ := mappedGaps.min' hmappedNonempty
  have hL : 0 < L := by
    dsimp [L]
    obtain ⟨d, hd⟩ := hrawNonempty
    exact lt_of_lt_of_le (by
      obtain ⟨vw, hvw, rfl⟩ := Finset.mem_image.mp hd
      exact sub_pos.mpr (Finset.mem_filter.mp hvw).2) (Finset.le_max' _ _ hd)
  have hm : 0 < m := by
    dsimp [m]
    obtain ⟨vw, hvw, hEq⟩ := Finset.mem_image.mp
      (Finset.min'_mem mappedGaps hmappedNonempty)
    rw [← hEq]
    exact sub_pos.mpr (D.secondHomeomorph_strictMono (Finset.mem_filter.mp hvw).2)
  have endpoint_mem (a : E) : a.1 ∈ C.coordinateSpace := by
    obtain ⟨b, hb⟩ := hupper a a.1
    obtain ⟨n, hn, y, ownerA, hy₀, hy₁, hchain, _⟩ :=
      hbetween' a.1 a.2 b.1 b.2 hb
    obtain ⟨yLift, owner, hylift, hsource⟩ :=
      secondStage_chain_of_exact_indexed D T₁ _hT₁ _hTiles hn y ownerA hchain
    rw [← (hylift 0).trans hy₀]
    exact (yLift 0).property
  let lift : E → C.coordinateSpace := fun a => ⟨a.1, endpoint_mem a⟩
  have hlift (a : E) : (lift a : ℝ) = a.1 := rfl
  have hstep : ∀ a b : E, a.1 < b.1 →
      ∃ n : ℕ, 0 < n ∧ b.1 - a.1 ≤ (n : ℝ) * L ∧
        mapScalar φ (lift a) + (n : ℝ) * m ≤ mapScalar φ (lift b) := by
    intro a b _hab
    obtain ⟨n, hn, y, ownerA, hy0, hylast, hchain, _⟩ :=
      hbetween' a.1 a.2 b.1 b.2 _hab
    obtain ⟨yLift, owner, hylift, hsource⟩ :=
      secondStage_chain_of_exact_indexed D T₁ _hT₁ _hTiles hn y ownerA hchain
    have hL0 : yLift 0 = lift a := by
      apply Subtype.ext
      exact (hylift 0).trans hy0
    have hLlast : yLift (Fin.last n) = lift b := by
      apply Subtype.ext
      exact (hylift (Fin.last n)).trans hylast
    have hraw (i : Fin n) :
        y i.succ - y i.castSucc ∈ (rawGaps : Set ℝ) := by
      obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ := hsource.2.2 i
      have hvF : v ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF : w ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      have hvw : v.im < w.im := by
        simpa [Axis.coord, Complex.sub_im] using _hpos
      have hpair : (⟨v, hvF⟩, ⟨w, hwF⟩) ∈ pairs := by
        simp [pairs, hvw]
      have hmem : (w.im - v.im) ∈ rawGaps := Finset.mem_image.mpr
        ⟨(⟨v, hvF⟩, ⟨w, hwF⟩),
          hpair, rfl⟩
      rw [hleft, hright]
      simpa [Axis.coord, Complex.sub_im] using hmem
    have hmap (i : Fin n) :
        mapScalar φ (yLift i.succ) - mapScalar φ (yLift i.castSucc) ∈
          (mappedGaps : Set ℝ) := by
      obtain ⟨v, w, hv, hw, hleft, hright, _hpos, _⟩ := hsource.2.2 i
      have hvF : v ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hv
      have hwF : w ∈ C.region.vertexFinset :=
        (C.region.isPolygonal.vertexSet_finite.mem_toFinset).2 hw
      have hvw : v.im < w.im := by
        simpa [Axis.coord, Complex.sub_im] using _hpos
      have hleft' := secondStage_endpoint_formula D v hv (owner i)
        (y i.castSucc) (yLift i.castSucc) (hsource.1 _) hleft
      have hright' := secondStage_endpoint_formula D w hw (owner i)
        (y i.succ) (yLift i.succ) (hsource.1 _) hright
      have hpair : (⟨v, hvF⟩, ⟨w, hwF⟩) ∈ pairs := by
        simp [pairs, hvw]
      have hmem : D.secondHomeomorph w.im - D.secondHomeomorph v.im ∈
          mappedGaps := Finset.mem_image.mpr
        ⟨(⟨v, hvF⟩, ⟨w, hwF⟩),
          hpair, rfl⟩
      rw [hleft', hright']
      simpa [add_comm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hmem
    have hrawle (i : Fin n) :
        y i.succ - y i.castSucc ≤ L := by
      exact Finset.le_max' rawGaps _ (hraw i)
    have hmapge (i : Fin n) : m ≤
        mapScalar φ (yLift i.succ) - mapScalar φ (yLift i.castSucc) := by
      dsimp [m]
      exact Finset.min'_le mappedGaps _ (hmap i)
    have hsumraw :
        (∑ i : Fin n, (y i.succ - y i.castSucc)) ≤
          ∑ _i : Fin n, L := Finset.sum_le_sum fun i _ => hrawle i
    have hsummap :
        (∑ i : Fin n,
          (mapScalar φ (yLift i.succ) - mapScalar φ (yLift i.castSucc))) ≥
          ∑ _i : Fin n, m :=
      Finset.sum_le_sum fun i _ => hmapge i
    have htelraw := fin_sum_step_sub_local y
    have htelmap := fin_sum_step_sub_local (fun i => mapScalar φ (yLift i))
    have hspan : b.1 - a.1 ≤ (n : ℝ) * L := by
      have hba : b.1 - a.1 = y (Fin.last n) - y 0 := by
        rw [← hy0, ← hylast]
      calc
        b.1 - a.1 = y (Fin.last n) - y 0 := hba
        _ = ∑ i : Fin n, (y i.succ - y i.castSucc) := htelraw.symm
        _ ≤ ∑ _i : Fin n, L := hsumraw
        _ = (n : ℝ) * L := by simp [nsmul_eq_mul]
    have hmapspan : mapScalar φ (lift a) + (n : ℝ) * m ≤
        mapScalar φ (lift b) := by
      rw [htelmap] at hsummap
      rw [hL0, hLlast] at hsummap
      have hsummap' : (n : ℝ) * m ≤
          mapScalar φ (lift b) - mapScalar φ (lift a) := by
        simpa [nsmul_eq_mul] using hsummap
      linarith
    exact ⟨n, hn, hspan, hmapspan⟩
  have hcof := finite_step_cofinal_local m L hm hL hE hupper hlower hstep
  refine ⟨lift, hlift, ?_, hcof.1, hcof.2⟩
  intro a b _hab
  obtain ⟨n, hn, _hspan, hmapspan⟩ := hstep a b _hab
  have hnm : 0 < (n : ℝ) * m :=
    mul_pos (Nat.cast_pos.mpr hn) hm
  linarith

private theorem secondStage_sourceSliceChains_local_impl
    (hlocal :
      ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
        {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
        (T₁ : ↥C.centres ↪ Tiling.Plane)
        (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
        (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
        ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
          ∀ a b : ℝ, a < b →
            ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
              (yLift : Fin (n + 1) → C.coordinateSpace)
              (owner : Fin n → ↥C.centres),
              y 0 ≤ a ∧ b ≤ y (Fin.last n) ∧
                IsSecondStageBandSliceChain C φ D T₁ q y yLift owner) :
    secondStage_sourceSliceChainsSpec.{u} := by
  unfold secondStage_sourceSliceChainsSpec
  intro C P φ D T₁ _hT₁ _hTiles
  exact hlocal (C := C) (P := P) (φ := φ) D T₁ _hT₁ _hTiles

private theorem secondStage_targetExhaustingSliceChains_impl
    (hcofinal :
      ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
        {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
        (T₁ : ↥C.centres ↪ Tiling.Plane)
        (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
        (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
        ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
          ∀ a b : ℝ, a < b →
            ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
              (yLift : Fin (n + 1) → C.coordinateSpace)
              (owner : Fin n → ↥C.centres),
              mapScalar φ (yLift 0) ≤ a ∧
                b ≤ mapScalar φ (yLift (Fin.last n)) ∧
                IsSecondStageBandSliceChain C φ D T₁ q y yLift owner) :
    secondStage_targetExhaustingSliceChainsSpec.{u} := by
  unfold secondStage_targetExhaustingSliceChainsSpec
  intro C P ε _hFine φ _hφ D T₁ _hT₁ _hTiles
  exact hcofinal (C := C) (P := P) (φ := φ) D T₁ _hT₁ _hTiles

private theorem secondStage_sourceSliceChains :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      {φ : C.coordinateSpace →ₗ[ℚ] ℚ} (D : CoordinateDeformation C φ)
      (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
        ∀ a b : ℝ, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
            (yLift : Fin (n + 1) → C.coordinateSpace)
            (owner : Fin n → ↥C.centres),
            y 0 ≤ a ∧ b ≤ y (Fin.last n) ∧
              IsSecondStageBandSliceChain C φ D T₁ q y yLift owner := by
  exact secondStage_sourceSliceChains_impl

private theorem secondStage_sourceSliceChain_transport_impl :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (q : ℝ) {n : ℕ} (y : Fin (n + 1) → ℝ)
      (yLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      IsSecondStageBandSliceChain C φ D T₁ q y yLift owner →
      StrictMono (fun i ↦ mapScalar φ (yLift i)) ∧
      ∀ i : Fin n,
        {z : Tiling.Plane | z.re = q ∧
          z.im ∈ Ioo (mapScalar φ (yLift i.castSucc))
            (mapScalar φ (yLift i.succ))} ⊆
          mapPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ
            D.deformedRegion.openCarrier := by
  intro C P ε hFine φ hφ D T₁ hT₁ q n y yLift owner hchain
  rcases hchain with ⟨hLift, hmono, hsteps⟩
  constructor
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hsteps i
    have hvw : v.im < w.im := by
      have hpositive' : 0 < w.im - v.im := by simpa using hpositive
      linarith
    rw [second_endpoint_formula D v hv (owner i) (y i.castSucc)
      (yLift i.castSucc) (hLift i.castSucc) hleft,
      second_endpoint_formula D w hw (owner i) (y i.succ)
        (yLift i.succ) (hLift i.succ) hright]
    simpa [add_comm] using
      (add_lt_add_right (D.secondHomeomorph_strictMono hvw)
        (mapPoint φ (C.centrePoint (owner i).1 (owner i).2)).im)
  · intro i
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hsteps i
    let t := owner i
    let c₁ : Tiling.Plane := T₁ t
    let c₂ : Tiling.Plane := mapPoint φ (C.centrePoint t.1 t.2)
    have hc₁ : c₁ = mapFirstPoint φ (C.centrePoint t.1 t.2) := hT₁ t
    have hc₁_re : c₁.re = mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      rw [hc₁]
      simp [mapFirstPoint, ApproximationContext.centrePoint]
    have hc₁_im : c₁.im = t.1.im := by
      rw [hc₁]
      simp [mapFirstPoint, ApproximationContext.centrePoint]
    have hc₂_re : c₂.re = c₁.re := by
      rw [hc₁]
      simp [c₂, mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
    have hc₂_im : c₂.im = mapScalar φ
        ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := by
      simp [c₂, mapPoint, ApproximationContext.centrePoint]
    intro z hz
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier]
    let r : ℝ := D.secondHomeomorph.symm (z.im - c₂.im)
    let p : Tiling.Plane := ((q - c₁.re : ℝ) : ℂ) +
      (r : ℂ) * Complex.I
    have hend₀ := second_endpoint_formula D v hv t (y i.castSucc)
      (yLift i.castSucc) (hLift i.castSucc) hleft
    have hend₁ := second_endpoint_formula D w hw t (y i.succ)
      (yLift i.succ) (hLift i.succ) hright
    have hvr : v.im < r := by
      apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
      rw [D.secondHomeomorph.apply_symm_apply]
      have hzre := hz.2.1
      have hzlo := hz.2.1
      linarith [hend₀]
    have hrw : r < w.im := by
      apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
      rw [D.secondHomeomorph.apply_symm_apply]
      have hzre := hz.2.1
      have hzhi := hz.2.2
      linarith [hend₁]
    have hleft' : y i.castSucc = v.im + t.1.im := by
      simpa using hleft
    have hright' : y i.succ = w.im + t.1.im := by
      simpa using hright
    have hsource : c₁ + p ∈
        {u : Tiling.Plane | u.re = q ∧
          u.im ∈ Ioo (y i.castSucc) (y i.succ)} := by
      constructor
      · simp [p]
      · simp only [p, Complex.add_im, Complex.ofReal_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, Complex.ofReal_im, zero_mul]
        rw [hc₁_im]
        constructor <;> linarith [hleft', hright']
    have hsource' := hinside hsource
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.firstRegion_openCarrier] at hsource'
    obtain ⟨k, hk, hkmap⟩ := hsource'
    refine ⟨k, hk, ?_⟩
    apply Complex.ext
    · rw [D.planarHomeomorph_apply]
      have hkreal : D.firstHomeomorph k.re = q - c₁.re := by
        have h := congrArg Complex.re hkmap
        rw [D.firstPlanarHomeomorph_apply] at h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
          zero_mul, sub_zero, vadd_eq_add] at h
        convert h using 1 <;> simp [p]
        ring
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, vadd_eq_add, Complex.neg_re]
      rw [hkreal]
      rw [hz.1, hc₂_re]
      ring
    · rw [D.planarHomeomorph_apply]
      have hkim : k.im = r := by
        have h := congrArg Complex.im hkmap
        rw [D.firstPlanarHomeomorph_apply] at h
        simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, Complex.ofReal_im,
          zero_mul, vadd_eq_add] at h
        convert h using 1 <;> simp [p]
        ring
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
        mul_zero, add_zero, zero_add, vadd_eq_add, Complex.neg_im]
      rw [hkim]
      dsimp [r]
      rw [D.secondHomeomorph.apply_symm_apply]
      ring

private theorem secondStage_sourceSliceChain_transport :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (q : ℝ) {n : ℕ} (y : Fin (n + 1) → ℝ)
      (yLift : Fin (n + 1) → C.coordinateSpace)
      (owner : Fin n → ↥C.centres),
      IsSecondStageBandSliceChain C φ D T₁ q y yLift owner →
      StrictMono (fun i ↦ mapScalar φ (yLift i)) ∧
      ∀ i : Fin n,
        {z : Tiling.Plane | z.re = q ∧
          z.im ∈ Ioo (mapScalar φ (yLift i.castSucc))
            (mapScalar φ (yLift i.succ))} ⊆
          mapPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ
            D.deformedRegion.openCarrier := by
  exact secondStage_sourceSliceChain_transport_impl

private theorem secondStage_targetExhaustingSliceChains :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
        ∀ a b : ℝ, a < b →
          ∃ (n : ℕ) (_hn : 0 < n) (y : Fin (n + 1) → ℝ)
            (yLift : Fin (n + 1) → C.coordinateSpace)
            (owner : Fin n → ↥C.centres),
            mapScalar φ (yLift 0) ≤ a ∧
              b ≤ mapScalar φ (yLift (Fin.last n)) ∧
              IsSecondStageBandSliceChain C φ D T₁ q y yLift owner := by
  intro C P ε _hFine φ _hφ D T₁ _hT₁ _hTiles
  filter_upwards [
    secondStage_vertical_fibre_ae D T₁ _hTiles,
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints_of_local_ae
      D.firstRegion
      (deformedCenterCarrier T₁) _hTiles.2.1 Axis.vertical,
    secondStage_mappedEndpointCofinality_local D T₁ _hT₁ _hTiles] with
      q hfull hbetween hcofinal
  intro hq a b hab
  have hfull' := hfull hq
  let E : Set ℝ := sliceEndpointSet D.firstRegion
    (deformedCenterCarrier T₁) Axis.vertical q
  have hcover : ∀ c d : ℝ, c < d →
      ∀ᵐ x : ℝ ∂volume, x ∈ Ioo c d →
        slicePoint Axis.vertical q x ∈
          openUnion D.firstRegion (deformedCenterCarrier T₁) := by
    intro c d hcd
    filter_upwards [hfull'] with x hx hxI
    exact hx.mpr (Set.mem_univ x)
  obtain ⟨lift, hlift, hmono, hunboundedAbove, hunboundedBelow⟩ := hcofinal hq
  obtain ⟨l, hlE, hla⟩ := not_bddBelow_iff.mp hunboundedBelow a
  obtain ⟨r, hrE, hbr⟩ := not_bddAbove_iff.mp hunboundedAbove b
  obtain ⟨l, rfl⟩ := hlE
  obtain ⟨r, rfl⟩ := hrE
  have hlr : l.1 < r.1 := by
    have hll : mapScalar φ (lift l) < mapScalar φ (lift r) :=
      lt_trans hla (lt_trans hab hbr)
    exact (hmono.lt_iff_lt).mp hll
  have hlocal : ∀ᵐ x : ℝ ∂volume, x ∈ Ioo l.1 r.1 →
      slicePoint Axis.vertical q x ∈
        openUnion D.firstRegion (deformedCenterCarrier T₁) :=
    hcover l.1 r.1 hlr
  obtain ⟨n, hn, y, ownerA, hy0, hylast, hchain, _hendpoints⟩ :=
    hbetween l l.property r r.property hlr hlocal
  obtain ⟨yLift, owner, hylift, hsource⟩ :=
    secondStage_chain_of_exact_indexed D T₁ _hT₁ _hTiles hn y ownerA hchain
  refine ⟨n, hn, y, yLift, owner, ?_, ?_, hsource⟩
  · have hmap0 : mapScalar φ (yLift 0) = mapScalar φ (lift l) := by
      apply congrArg (mapScalar φ)
      apply Subtype.ext
      exact (hylift 0).trans (hy0.trans (hlift l).symm)
    rw [hmap0]
    exact hla.le
  · have hmaplast : mapScalar φ (yLift (Fin.last n)) =
        mapScalar φ (lift r) := by
      apply congrArg (mapScalar φ)
      apply Subtype.ext
      exact (hylift (Fin.last n)).trans (hylast.trans (hlift r).symm)
    rw [hmaplast]
    exact hbr.le

end Tiling.AxisParallel.Approximation

/- Canonical append-only A04 slots 24--26. -/

namespace Tiling.AxisParallel.Approximation

open Tiling.AxisParallel
open Tiling.AxisParallel.Foundations.FilledSliceChains

universe u

private theorem secondStage_globalGenericSliceOrder :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
        ∀ s t : ↥C.centres, ∀ x y : ℝ,
          x ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q →
          y ∈ placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q →
          x < y →
            secondStageRunningMap φ D s x < secondStageRunningMap φ D t y := by
  exact secondStage_globalGenericSliceOrder_impl

private theorem secondStage_vertical_perturbation_local
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (c p : Tiling.Plane)
    (_hp : p ∈ D.firstRegion.openCarrier) {q : ℝ}
    (δ : ℝ) (_hδ : 0 < δ)
    (hball : Metric.ball (c + p) δ ⊆ c +ᵥ D.firstRegion.openCarrier)
    (hq : |q - (c.re + p.re)| < δ) :
    c.im + p.im ∈ placedAxisSlice D.firstRegion c Axis.vertical q := by
  change slicePoint Axis.vertical q (c.im + p.im) ∈ c +ᵥ D.firstRegion.openCarrier
  have hclose : dist (slicePoint Axis.vertical q (c.im + p.im)) (c + p) < δ := by
    rw [dist_eq_norm]
    have heq : slicePoint Axis.vertical q (c.im + p.im) - (c + p) =
        ((q - (c.re + p.re) : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [slicePoint]
    rw [heq]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    exact hq
  exact hball hclose

private theorem secondStage_good_base_real_interval
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ})
    (c : Tiling.Plane) (hc : c ∈ deformedCenterCarrier T₁)
    (p : Tiling.Plane) (_hp : p ∈ D.firstRegion.openCarrier)
    {δ : ℝ} (hδ : 0 < δ)
    (hball : Metric.ball (c + p) δ ⊆ c +ᵥ D.firstRegion.openCarrier) :
    ∃ q : ℝ, q ∈ deformedBandBase P φ ∧
      q ∈ Ioo (c.re + p.re - δ / 4) (c.re + p.re + δ / 4) := by
  have hAE : ∀ᵐ z : Tiling.Plane ∂volume,
      z ∈ openUnion D.firstRegion (deformedCenterCarrier T₁) →
        z.re ∈ deformedBandBase P φ := by
    filter_upwards [hTiles.2.2] with z hz
    intro hzU
    apply hz.mpr
    simpa only [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier.eq_def, Set.mem_iUnion] using hzU
  have hdense : Dense {z : Tiling.Plane |
      z ∈ openUnion D.firstRegion (deformedCenterCarrier T₁) →
      z.re ∈ deformedBandBase P φ} := Measure.dense_of_ae hAE
  let V : Set Tiling.Plane := Metric.ball (c + p) δ ∩
      {z : Tiling.Plane | z.re ∈ Ioo (c.re + p.re - δ / 4) (c.re + p.re + δ / 4)}
  have hVopen : IsOpen V := by
    exact Metric.isOpen_ball.inter (isOpen_Ioo.preimage Complex.continuous_re)
  have hVne : V.Nonempty := by
    refine ⟨c + p, Metric.mem_ball_self hδ, ?_⟩
    change c.re + p.re ∈ Ioo (c.re + p.re - δ / 4) (c.re + p.re + δ / 4)
    constructor <;> linarith
  obtain ⟨z, hzgood, hzV⟩ := hdense.exists_mem_open hVopen hVne
  have hzopen : z ∈ openUnion D.firstRegion (deformedCenterCarrier T₁) := by
    apply Set.mem_iUnion.mpr
    exact ⟨⟨c, hc⟩, hball hzV.1⟩
  have hzbase := hzgood hzopen
  exact ⟨z.re, hzbase, hzV.2⟩

private theorem secondStage_exists_mem_Ioo_of_ae_real {P : ℝ → Prop} {a b : ℝ}
    (hab : a < b) (hP : ∀ᵐ x : ℝ ∂volume, P x) :
    ∃ x ∈ Ioo a b, P x := by
  have hμ : volume.restrict (Ioo a b) ≠ 0 := by
    intro hz
    have : volume (Ioo a b) = 0 := by
      rw [← Measure.restrict_apply_univ (Ioo a b), hz]
      simp
    rw [Real.volume_Ioo] at this
    simp [ENNReal.ofReal_eq_zero, not_le.mpr (sub_pos.mpr hab)] at this
  let hne : (ae (volume.restrict (Ioo a b))).NeBot := ae_neBot.mpr hμ
  have hp' : ∀ᵐ x : ℝ ∂volume.restrict (Ioo a b), P x :=
    hP.filter_mono ae_restrict_le
  rcases @Filter.Eventually.exists ℝ _ (ae (volume.restrict (Ioo a b))) hne
      (hp'.and (ae_restrict_mem measurableSet_Ioo)) with ⟨x, hp, hx⟩
  exact ⟨x, hx, hp⟩

private theorem secondStageCentreMap_injective
    : ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      Function.Injective
        (fun t : ↥C.centres => mapPoint φ (C.centrePoint t.1 t.2)) := by
  intro C P ε hFine φ hφ D T₁ hT₁ hTiles s t heq
  by_contra hst
  obtain ⟨p, hp⟩ := D.firstRegion.isPolygonal.interior_nonempty D.firstRegion.nonempty
  obtain ⟨Hopen, _, _, _, _, _, _, _⟩ :=
    deformedBandBase_geometry P ε hFine φ hφ
  obtain ⟨δs, hδs, hballs⟩ := Metric.isOpen_iff.1
    (D.firstRegion.openCarrier_regularOpen.1.vadd (T₁ s))
    (T₁ s + p) ⟨p, hp, rfl⟩
  obtain ⟨δt, hδt, hballt⟩ := Metric.isOpen_iff.1
    (D.firstRegion.openCarrier_regularOpen.1.vadd (T₁ t))
    (T₁ t + p) ⟨p, hp, rfl⟩
  have hTreal : (T₁ s).re = (T₁ t).re := by
    rw [hT₁ s, hT₁ t]
    simpa [mapPoint, mapFirstPoint, ApproximationContext.centrePoint] using
      congrArg Complex.re heq
  have himap : mapScalar φ ⟨s.1.im, C.centre_im_mem s.1 s.2⟩ =
      mapScalar φ ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := by
    simpa [mapPoint, ApproximationContext.centrePoint] using congrArg Complex.im heq
  have hTsim : (T₁ s).im = s.1.im := by
    simp [hT₁, mapFirstPoint, ApproximationContext.centrePoint]
  have hTtim : (T₁ t).im = t.1.im := by
    simp [hT₁, mapFirstPoint, ApproximationContext.centrePoint]
  have himne : s.1.im ≠ t.1.im := by
    intro him
    apply hst
    apply T₁.injective
    apply Complex.ext
    · exact hTreal
    · simp [hT₁, mapFirstPoint, ApproximationContext.centrePoint, him]
  let δ : ℝ := min δs δt
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδs hδt
  rcases lt_or_gt_of_ne himne with hst_im | hts_im
  · obtain ⟨q₀, hq₀base, hq₀I⟩ := secondStage_good_base_real_interval
      D T₁ hTiles (T₁ s) ⟨s, rfl⟩ p hp hδ
        (fun z hz => by
          apply hballs
          change dist z (T₁ s + p) < δs
          change dist z (T₁ s + p) < δ at hz
          exact lt_of_lt_of_le hz (min_le_left _ _))
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.1 Hopen q₀ hq₀base
    let ρ : ℝ := min (η / 2) (min (δs / 4) (δt / 4))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    obtain ⟨q, hqI, hqgood⟩ := secondStage_exists_mem_Ioo_of_ae_real
      (by linarith : q₀ - ρ < q₀ + ρ)
      (secondStage_globalGenericSliceOrder
        (C := C) (P := P) ε hFine φ hφ D T₁ hT₁ hTiles)
    have hqbase : q ∈ deformedBandBase P φ := by
      apply hηball
      change dist q q₀ < η
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hqI.1, hqI.2,
        show ρ ≤ η / 2 from min_le_left _ _]
    let x : ℝ := (T₁ s).im + p.im
    let y : ℝ := (T₁ t).im + p.im
    have hqs : |q - ((T₁ s).re + p.re)| < δs := by
      rw [abs_lt]
      constructor <;> linarith [hqI.1, hqI.2, hq₀I.1, hq₀I.2,
        show ρ ≤ δs / 4 from le_trans (min_le_right _ _) (min_le_left _ _),
        show δ ≤ δs from min_le_left _ _]
    have hqt : |q - ((T₁ t).re + p.re)| < δt := by
      rw [← hTreal]
      rw [abs_lt]
      constructor <;> linarith [hqI.1, hqI.2, hq₀I.1, hq₀I.2,
        show ρ ≤ δt / 4 from le_trans (min_le_right _ _) (min_le_right _ _),
        show δ ≤ δt from min_le_right _ _]
    have hx : x ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q := by
      dsimp [x]
      exact secondStage_vertical_perturbation_local (q := q) D (T₁ s) p hp δs hδs hballs hqs
    have hy : y ∈ placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q := by
      dsimp [y]
      exact secondStage_vertical_perturbation_local (q := q) D (T₁ t) p hp δt hδt hballt hqt
    have hlt := hqgood hqbase s t x y hx hy (by
      dsimp [x, y]
      rw [hTsim, hTtim]
      linarith)
    have hEqRun : secondStageRunningMap φ D s x =
        secondStageRunningMap φ D t y := by
      dsimp [secondStageRunningMap, x, y]
      rw [hTsim, hTtim]
      rw [himap]
      congr 1; ring_nf
    exact (ne_of_lt hlt) hEqRun
  · obtain ⟨q₀, hq₀base, hq₀I⟩ := secondStage_good_base_real_interval
      D T₁ hTiles (T₁ t) ⟨t, rfl⟩ p hp hδ
        (fun z hz => by
          apply hballt
          change dist z (T₁ t + p) < δt
          change dist z (T₁ t + p) < δ at hz
          exact lt_of_lt_of_le hz (min_le_right _ _))
    obtain ⟨η, hη, hηball⟩ := Metric.isOpen_iff.1 Hopen q₀ hq₀base
    let ρ : ℝ := min (η / 2) (min (δs / 4) (δt / 4))
    have hρ : 0 < ρ := by
      dsimp [ρ]
      exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
    obtain ⟨q, hqI, hqgood⟩ := secondStage_exists_mem_Ioo_of_ae_real
      (by linarith : q₀ - ρ < q₀ + ρ)
      (secondStage_globalGenericSliceOrder
        (C := C) (P := P) ε hFine φ hφ D T₁ hT₁ hTiles)
    have hqbase : q ∈ deformedBandBase P φ := by
      apply hηball
      change dist q q₀ < η
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hqI.1, hqI.2,
        show ρ ≤ η / 2 from min_le_left _ _]
    let x : ℝ := (T₁ t).im + p.im
    let y : ℝ := (T₁ s).im + p.im
    have hqt : |q - ((T₁ t).re + p.re)| < δt := by
      rw [abs_lt]
      constructor <;> linarith [hqI.1, hqI.2, hq₀I.1, hq₀I.2,
        show ρ ≤ δt / 4 from le_trans (min_le_right _ _) (min_le_right _ _),
        show δ ≤ δt from min_le_right _ _]
    have hqs : |q - ((T₁ s).re + p.re)| < δs := by
      rw [hTreal]
      rw [abs_lt]
      constructor <;> linarith [hqI.1, hqI.2, hq₀I.1, hq₀I.2,
        show ρ ≤ δs / 4 from le_trans (min_le_right _ _) (min_le_left _ _),
        show δ ≤ δs from min_le_left _ _]
    have hx : x ∈ placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q := by
      dsimp [x]
      exact secondStage_vertical_perturbation_local (q := q) D (T₁ t) p hp δt hδt hballt hqt
    have hy : y ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q := by
      dsimp [y]
      exact secondStage_vertical_perturbation_local (q := q) D (T₁ s) p hp δs hδs hballs hqs
    have hlt := hqgood hqbase t s x y hx hy (by
      dsimp [x, y]
      rw [hTtim, hTsim]
      linarith)
    have hEqRun : secondStageRunningMap φ D t x =
        secondStageRunningMap φ D s y := by
      dsimp [secondStageRunningMap, x, y]
      rw [hTtim, hTsim]
      rw [himap]
      congr 1; ring_nf
    exact (ne_of_lt hlt) hEqRun
private def secondStagePlanarHomeomorphLocal
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) : Tiling.Plane ≃ₜ Tiling.Plane :=
  Complex.equivRealProdCLM.toHomeomorph.trans
    (((Homeomorph.refl ℝ).prodCongr D.secondHomeomorph).trans
      Complex.equivRealProdCLM.toHomeomorph.symm)

private theorem secondStagePlanarHomeomorphLocal_apply
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (z : Tiling.Plane) :
    secondStagePlanarHomeomorphLocal D z =
      z.re + D.secondHomeomorph z.im * Complex.I := by
  rw [secondStagePlanarHomeomorphLocal]
  change Complex.equivRealProdCLM.symm
    (z.re, D.secondHomeomorph z.im) = _
  rw [Complex.equivRealProdCLM_symm_apply]

private theorem secondStageRegionImageLocal
    {C : ApproximationContext.{u}} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) :
    D.deformedRegion.openCarrier =
      secondStagePlanarHomeomorphLocal D '' D.firstRegion.openCarrier := by
  rw [D.deformedRegion_openCarrier, D.firstRegion_openCarrier, Set.image_image]
  congr 1
  funext z
  rw [secondStagePlanarHomeomorphLocal_apply,
    D.firstPlanarHomeomorph_apply, D.planarHomeomorph_apply]
  apply Complex.ext <;> simp

private theorem secondStage_fullTile_enclosure_local
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ})
    (hBaseOpen : IsOpen (deformedBandBase P φ))
    (hBaseRegular : interior (closure (deformedBandBase P φ)) =
      deformedBandBase P φ) (t : ↥C.centres) :
    mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier ⊆
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
  have hcarrierOpen : IsOpen {z : Tiling.Plane |
      z.re ∈ deformedBandBase P φ} :=
    hBaseOpen.preimage Complex.continuous_re
  have hcarrierRegular : interior (closure {z : Tiling.Plane |
      z.re ∈ deformedBandBase P φ}) =
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
    change interior (closure (Complex.re ⁻¹' deformedBandBase P φ)) =
      Complex.re ⁻¹' deformedBandBase P φ
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hBaseRegular]
  have hsupport : regularSupport D.firstRegion (deformedCenterCarrier T₁) =
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} :=
    regularSupport_eq_of_tilesOn hcarrierOpen hcarrierRegular hTiles
  have hopenUnion : IsOpen (openUnion D.firstRegion
      (deformedCenterCarrier T₁)) :=
    isOpen_iUnion fun s : deformedCenterCarrier T₁ ↦
      D.firstRegion.openCarrier_regularOpen.1.vadd (s : Tiling.Plane)
  have hopenSubset : openUnion D.firstRegion
      (deformedCenterCarrier T₁) ⊆
      regularSupport D.firstRegion (deformedCenterCarrier T₁) := by
    rw [regularSupport]
    intro x hx
    have hxint : x ∈ interior (openUnion D.firstRegion
        (deformedCenterCarrier T₁)) := by
      simpa [hopenUnion.interior_eq] using hx
    exact interior_mono subset_closure hxint
  intro z hz
  obtain ⟨k, hk, hzk⟩ := hz
  obtain ⟨w, hw, hwk⟩ := (secondStageRegionImageLocal D) ▸ hk
  have hfirst : T₁ t + w ∈ openUnion D.firstRegion
      (deformedCenterCarrier T₁) := by
    rw [openUnion, Tiling.Polygonal.openUnion, ← Tiling.AxisParallel.Region.openCarrier, Set.mem_iUnion]
    refine ⟨⟨T₁ t, ⟨t, rfl⟩⟩, ?_⟩
    exact ⟨w, hw, rfl⟩
  have hbase : (T₁ t + w).re ∈ deformedBandBase P φ := by
    have h := hopenSubset hfirst
    rw [hsupport] at h
    exact h
  have hcentre :
      (mapPoint φ (C.centrePoint t.1 t.2)).re = (T₁ t).re := by
    rw [hT₁ t]
    simp [mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
  have hsecondre :
      (secondStagePlanarHomeomorphLocal D w).re = w.re := by
    rw [secondStagePlanarHomeomorphLocal_apply]
    simp
  have hreal : z.re = (T₁ t + w).re := by
    change mapPoint φ (C.centrePoint t.1 t.2) +ᵥ k = z at hzk
    rw [vadd_eq_add] at hzk
    calc
      z.re = (mapPoint φ (C.centrePoint t.1 t.2) + k).re := by rw [hzk]
      _ = (mapPoint φ (C.centrePoint t.1 t.2)).re + k.re := by simp
      _ = (T₁ t).re + w.re := by rw [hcentre, ← hwk, hsecondre]
      _ = (T₁ t + w).re := by simp
  change z.re ∈ deformedBandBase P φ
  rw [hreal]
  exact hbase
private theorem secondStage_sourceSliceChain_transport_local
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (q : ℝ) {n : ℕ} (y : Fin (n + 1) → ℝ)
    (yLift : Fin (n + 1) → C.coordinateSpace)
    (owner : Fin n → ↥C.centres)
    (hchain : IsSecondStageBandSliceChain C φ D T₁ q y yLift owner) :
    StrictMono (fun i ↦ mapScalar φ (yLift i)) ∧
      ∀ i : Fin n,
        {z : Tiling.Plane | z.re = q ∧
          z.im ∈ Ioo (mapScalar φ (yLift i.castSucc))
            (mapScalar φ (yLift i.succ))} ⊆
          mapPoint φ (C.centrePoint (owner i).1 (owner i).2) +ᵥ
            D.deformedRegion.openCarrier := by
  rcases hchain with ⟨hLift, hmono, hsteps⟩
  constructor
  · apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, _⟩ := hsteps i
    have hvw : v.im < w.im := by simpa [Complex.sub_im] using hpositive
    rw [secondStage_endpoint_formula D v hv (owner i) (y i.castSucc)
      (yLift i.castSucc) (hLift i.castSucc) hleft,
      secondStage_endpoint_formula D w hw (owner i) (y i.succ)
        (yLift i.succ) (hLift i.succ) hright]
    simpa [add_comm] using
      add_lt_add_right (D.secondHomeomorph_strictMono hvw)
        (mapPoint φ (C.centrePoint (owner i).1 (owner i).2)).im
  · intro i z hz
    obtain ⟨v, w, hv, hw, hleft, hright, hpositive, hinside⟩ := hsteps i
    let t := owner i
    let c₁ : Tiling.Plane := T₁ t
    let c₂ : Tiling.Plane := mapPoint φ (C.centrePoint t.1 t.2)
    have hc₁ : c₁ = mapFirstPoint φ (C.centrePoint t.1 t.2) := hT₁ t
    have hc₁_re : c₁.re = mapScalar φ ⟨t.1.re, C.centre_re_mem t.1 t.2⟩ := by
      rw [hc₁]
      simp [mapFirstPoint, ApproximationContext.centrePoint]
    have hc₁_im : c₁.im = t.1.im := by
      rw [hc₁]
      simp [mapFirstPoint, ApproximationContext.centrePoint]
    have hc₂_re : c₂.re = c₁.re := by
      rw [hc₁]
      simp [c₂, mapPoint, mapFirstPoint, ApproximationContext.centrePoint]
    have hc₂_im : c₂.im = mapScalar φ
        ⟨t.1.im, C.centre_im_mem t.1 t.2⟩ := by
      simp [c₂, mapPoint, ApproximationContext.centrePoint]
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.deformedRegion_openCarrier]
    let r : ℝ := D.secondHomeomorph.symm (z.im - c₂.im)
    let p : Tiling.Plane := ((q - c₁.re : ℝ) : ℂ) + (r : ℂ) * Complex.I
    have hend₀ := secondStage_endpoint_formula D v hv t (y i.castSucc)
      (yLift i.castSucc) (hLift i.castSucc) hleft
    have hend₁ := secondStage_endpoint_formula D w hw t (y i.succ)
      (yLift i.succ) (hLift i.succ) hright
    have hvr : v.im < r := by
      apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
      rw [D.secondHomeomorph.apply_symm_apply]
      linarith [hz.2.1, hend₀]
    have hrw : r < w.im := by
      apply D.secondHomeomorph_strictMono.lt_iff_lt.mp
      rw [D.secondHomeomorph.apply_symm_apply]
      linarith [hz.2.2, hend₁]
    have hsource : c₁ + p ∈ {u : Tiling.Plane | u.re = q ∧
        u.im ∈ Ioo (y i.castSucc) (y i.succ)} := by
      constructor
      · simp [p]
      · simp only [p, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.I_im, mul_one, Complex.ofReal_re, zero_mul]
        rw [hc₁_im]
        have hleft' : y i.castSucc = v.im + t.1.im := by
          simpa using hleft
        have hright' : y i.succ = w.im + t.1.im := by
          simpa using hright
        constructor <;> linarith
    have hsource' := hinside hsource
    rw [Set.mem_vadd_set_iff_neg_vadd_mem, D.firstRegion_openCarrier] at hsource'
    obtain ⟨k, hk, hkmap⟩ := hsource'
    refine ⟨k, hk, ?_⟩
    apply Complex.ext
    · rw [D.planarHomeomorph_apply]
      have hkreal : D.firstHomeomorph k.re = q - c₁.re := by
        have h := congrArg Complex.re hkmap
        rw [D.firstPlanarHomeomorph_apply] at h
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.I_im, mul_zero, Complex.ofReal_im,
          zero_mul, sub_zero, vadd_eq_add] at h
        convert h using 1 <;> (simp [p] <;> ring)
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im,
        mul_one, sub_self, add_zero, vadd_eq_add, Complex.neg_re]
      rw [hkreal, hz.1, hc₂_re]
      ring
    · rw [D.planarHomeomorph_apply]
      have hkim : k.im = r := by
        have h := congrArg Complex.im hkmap
        rw [D.firstPlanarHomeomorph_apply] at h
        simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im,
          Complex.I_re, Complex.I_im, mul_one, Complex.ofReal_im,
          zero_mul, vadd_eq_add] at h
        convert h using 1 <;> (simp [p] <;> ring)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
        mul_zero, add_zero, zero_add, vadd_eq_add, Complex.neg_im]
      rw [hkim]
      dsimp [r]
      rw [D.secondHomeomorph.apply_symm_apply]
      ring

private theorem secondStage_target_fibre_ae_local
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    (ε : ℝ) (hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hφ : IsEpsilonApproximation C ε φ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) :
    ∀ᵐ q : ℝ ∂volume, q ∈ deformedBandBase P φ →
      ∀ᵐ y : ℝ ∂volume, ∃ t : ↥C.centres,
        slicePoint Axis.vertical q y ∈
          mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier := by
  filter_upwards [secondStage_mappedEndpointCofinality_local D T₁ hT₁ hTiles,
    Tiling.AxisParallel.Foundations.FilledSliceChains.genericSliceChain_betweenEndpoints_of_local_ae
      D.firstRegion
      (deformedCenterCarrier T₁) hTiles.2.1 Axis.vertical,
    secondStage_vertical_fibre_ae D T₁ hTiles] with q hends hbetween hfull
  intro hq
  obtain ⟨lift, hlift, hmono, habove, hbelow⟩ := hends hq
  let E : Set ℝ := sliceEndpointSet D.firstRegion
    (deformedCenterCarrier T₁) Axis.vertical q
  have hcover : ∀ a b : ℝ, a < b →
      ∀ᵐ x : ℝ ∂volume, x ∈ Ioo a b →
        slicePoint Axis.vertical q x ∈
          openUnion D.firstRegion (deformedCenterCarrier T₁) := by
    intro a b hab
    filter_upwards [hfull hq] with x hx hxI
    exact hx.mpr (Set.mem_univ x)
  have hbetween' : ∀ a ∈ E, ∀ b ∈ E, a < b →
      ∃ (n : ℕ) (_hn : 0 < n) (x : Fin (n + 1) → ℝ)
        (ownerA : Fin n → ↥(deformedCenterCarrier T₁)),
        x 0 = a ∧ x (Fin.last n) = b ∧
          IsFilledIndexedSliceChain D.firstRegion
            (deformedCenterCarrier T₁) Axis.vertical q x ownerA ∧
          (∀ i, x i ∈ E) := by
    intro a ha b hb hab
    exact hbetween a ha b hb hab (hcover a b hab)
  have hmapCountable : (Set.range (mapScalar φ)).Countable := by
    apply (Set.countable_range (fun r : ℚ => (r : ℝ))).mono
    rintro z ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  filter_upwards [hmapCountable.ae_notMem volume] with y hy
  obtain ⟨_, ⟨a, rfl⟩, hay⟩ := not_bddBelow_iff.mp hbelow y
  obtain ⟨_, ⟨b, rfl⟩, hby⟩ := not_bddAbove_iff.mp habove y
  have hab : a.1 < b.1 := hmono.lt_iff_lt.mp (hay.trans hby)
  obtain ⟨n, hn, x, ownerA, hx0, hxlast, hchain, hendpoints⟩ :=
    hbetween' a.1 a.2 b.1 b.2 hab
  obtain ⟨yLift, owner, hylift, hsource⟩ :=
    secondStage_chain_of_exact_indexed D T₁ hT₁ hTiles hn x ownerA hchain
  have h0 : yLift 0 = lift a := by
    apply Subtype.ext
    calc
      (yLift 0 : ℝ) = x 0 := hylift 0
      _ = a := hx0
      _ = (lift a : ℝ) := (hlift a).symm
  have hlast : yLift (Fin.last n) = lift b := by
    apply Subtype.ext
    calc
      (yLift (Fin.last n) : ℝ) = x (Fin.last n) := hylift (Fin.last n)
      _ = b := hxlast
      _ = (lift b : ℝ) := (hlift b).symm
  have hleft : mapScalar φ (yLift 0) < y := by
    simpa [h0] using hay
  have hright : y < mapScalar φ (yLift (Fin.last n)) := by
    simpa [hlast] using hby
  have hyne : ∀ k, y ≠ mapScalar φ (yLift k) := by
    intro k heq
    exact hy ⟨yLift k, heq.symm⟩
  obtain ⟨i, hi⟩ := strictMono_exists_gap_local
    (fun k => mapScalar φ (yLift k))
    (secondStage_sourceSliceChain_transport_local ε hFine φ hφ D T₁ hT₁
      q x yLift owner hsource).1 hleft hright hyne
  have htransport := secondStage_sourceSliceChain_transport_local ε hFine φ hφ
    D T₁ hT₁ q x yLift owner hsource
  refine ⟨owner i, htransport.2 i ?_⟩
  exact ⟨by simp [slicePoint], by simpa [slicePoint] using hi⟩

private def secondSourcePointLocal
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    Tiling.Plane :=
  z.re + (D.secondHomeomorph.symm
      (z.im - (mapPoint φ (C.centrePoint t.1 t.2)).im) + t.1.im) * Complex.I

private theorem secondSourcePointLocal_re
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    (secondSourcePointLocal D t z).re = z.re := by
  simp [secondSourcePointLocal]

private theorem secondStageRunningMap_sourcePointLocal_im
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (t : ↥C.centres) (z : Tiling.Plane) :
    secondStageRunningMap φ D t (secondSourcePointLocal D t z).im = z.im := by
  simp [secondStageRunningMap, secondSourcePointLocal, mapPoint,
    ApproximationContext.centrePoint]

private theorem secondSourcePointLocal_mem
    {C : ApproximationContext} {φ : C.coordinateSpace →ₗ[ℚ] ℚ}
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (t : ↥C.centres) (z : Tiling.Plane)
    (hz : z ∈ mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
      D.deformedRegion.openCarrier) :
    secondSourcePointLocal D t z ∈
      T₁ t +ᵥ D.firstRegion.openCarrier := by
  rw [Set.mem_vadd_set_iff_neg_vadd_mem, secondStageRegionImageLocal D] at hz
  obtain ⟨p, hp, hpz⟩ := hz
  have hc₁ : T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2) := hT₁ t
  have hpre : secondStagePlanarHomeomorphLocal D
      (-mapFirstPoint φ (C.centrePoint t.1 t.2) +
        secondSourcePointLocal D t z) =
      -mapPoint φ (C.centrePoint t.1 t.2) + z := by
    rw [secondStagePlanarHomeomorphLocal_apply]
    apply Complex.ext
    · simp [secondSourcePointLocal, mapFirstPoint, mapPoint,
        ApproximationContext.centrePoint]
    · simp [secondSourcePointLocal, mapFirstPoint, mapPoint,
        ApproximationContext.centrePoint]
      ring
  have heq := (secondStagePlanarHomeomorphLocal D).injective (hpre.trans hpz.symm)
  rw [Set.mem_vadd_set_iff_neg_vadd_mem]
  change -T₁ t + secondSourcePointLocal D t z ∈ D.firstRegion.openCarrier
  rw [hc₁, heq]
  exact hp

private theorem secondStage_target_tiles_disjoint_local
    {C : ApproximationContext.{u}} {P : PeriodicBandData C}
    (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
    (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
    (_hφ : IsEpsilonApproximation C ε φ)
    (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
    (hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
    (hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
      {z : Tiling.Plane | z.re ∈ deformedBandBase P φ})
    (_hBaseOpen : IsOpen (deformedBandBase P φ))
    (hEnclose : ∀ t : ↥C.centres,
      mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier ⊆
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) :
    ∀ s t : ↥C.centres, s ≠ t →
      Disjoint
        (mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier)
        (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro z hzs hzt
  let O :=
    (mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier) ∩
      (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier)
  have hOopen : IsOpen O :=
    (D.deformedRegion.openCarrier_regularOpen.1.vadd _).inter
      (D.deformedRegion.openCarrier_regularOpen.1.vadd _)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hOopen z ⟨hzs, hzt⟩
  obtain ⟨Hopen, _, _, _, _, _, _, _⟩ :=
    deformedBandBase_geometry P ε _hFine φ _hφ
  have hzbase : z.re ∈ deformedBandBase P φ := hEnclose s hzs
  obtain ⟨δ, hδ, hδball⟩ := Metric.isOpen_iff.1 Hopen z.re hzbase
  let ρ : ℝ := min (η / 4) (δ / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  obtain ⟨q, hqI, hqgood⟩ := secondStage_exists_mem_Ioo_of_ae_real
    (by linarith : z.re - ρ < z.re + ρ)
    (secondStage_globalGenericSliceOrder
      (C := C) (P := P) ε _hFine φ _hφ D T₁ hT₁ hTiles)
  have hqbase : q ∈ deformedBandBase P φ := by
    apply hδball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hqI.1, hqI.2, show ρ ≤ δ / 2 from min_le_right _ _]
  let w : Tiling.Plane := slicePoint Axis.vertical q z.im
  have hwball : w ∈ Metric.ball z η := by
    rw [Metric.mem_ball, dist_eq_norm, show w - z =
      ((q - z.re : ℝ) : ℂ) + ((z.im - z.im : ℝ) : ℂ) * Complex.I by
        apply Complex.ext <;> simp [w, slicePoint]]
    have habs : |q - z.re| < η := by
      exact (abs_lt.2 ⟨by linarith [hqI.1, show ρ ≤ η / 4 from min_le_left _ _],
        by linarith [hqI.2, show ρ ≤ η / 4 from min_le_left _ _]⟩)
    simp only [sub_self, Complex.ofReal_zero, zero_mul, add_zero]
    change ‖((q - z.re : ℝ) : ℂ)‖ < η
    simpa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using habs
  have hwo : w ∈ O := hball hwball
  have hws := secondSourcePointLocal_mem D T₁ hT₁ s w hwo.1
  have hwt := secondSourcePointLocal_mem D T₁ hT₁ t w hwo.2
  let rs := (secondSourcePointLocal D s w).im
  let rt := (secondSourcePointLocal D t w).im
  have hrs : rs ∈ placedAxisSlice D.firstRegion (T₁ s) Axis.vertical q := by
    change slicePoint Axis.vertical q rs ∈ T₁ s +ᵥ D.firstRegion.openCarrier
    rw [show slicePoint Axis.vertical q rs = secondSourcePointLocal D s w by
      apply Complex.ext <;> simp [rs, secondSourcePointLocal, w, slicePoint]]
    exact hws
  have hrt : rt ∈ placedAxisSlice D.firstRegion (T₁ t) Axis.vertical q := by
    change slicePoint Axis.vertical q rt ∈ T₁ t +ᵥ D.firstRegion.openCarrier
    rw [show slicePoint Axis.vertical q rt = secondSourcePointLocal D t w by
      apply Complex.ext <;> simp [rt, secondSourcePointLocal, w, slicePoint]]
    exact hwt
  have hrun_s : secondStageRunningMap φ D s rs = w.im := by
    simpa [rs] using secondStageRunningMap_sourcePointLocal_im D s w
  have hrun_t : secondStageRunningMap φ D t rt = w.im := by
    simpa [rt] using secondStageRunningMap_sourcePointLocal_im D t w
  rcases lt_trichotomy rs rt with hrslt | hrseq | hrtlt
  · have := hqgood hqbase s t rs rt hrs hrt hrslt
    linarith [hrun_s, hrun_t]
  · have hsourdisj := (isPacking_iff_openCarrier_disjoint D.firstRegion
      (deformedCenterCarrier T₁)).mp hTiles.2.1
      (show T₁ s ∈ deformedCenterCarrier T₁ from ⟨s, rfl⟩)
      (show T₁ t ∈ deformedCenterCarrier T₁ from ⟨t, rfl⟩) (by
        intro heq
        exact hst (T₁.injective heq))
    rw [← hrseq] at hrt
    exact Set.disjoint_left.mp hsourdisj hrs hrt
  · have := hqgood hqbase t s rt rs hrt hrs hrtlt
    linarith [hrun_s, hrun_t]

private theorem secondStage_properCylinderSlices :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane)
      (_hT₁ : ∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2))
      (_hTiles : TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}),
      (∀ t : ↥C.centres,
        mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier ⊆
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) ∧
      (∀ s t : ↥C.centres, s ≠ t →
        Disjoint
          (mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier)
          (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier)) ∧
      (∀ᵐ q : ℝ ∂volume,
        (q ∈ deformedBandBase P φ → ∀ᵐ y : ℝ ∂volume,
          ∃ t : ↥C.centres,
            slicePoint Axis.vertical q y ∈
              mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
                D.deformedRegion.openCarrier) ∧
        (q ∉ deformedBandBase P φ → ∀ y : ℝ,
          ¬ ∃ t : ↥C.centres,
            slicePoint Axis.vertical q y ∈
              mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
                D.deformedRegion.openCarrier)) := by
  intro C P ε hFine φ hφ D T₁ hT₁ hTiles
  obtain ⟨hBaseOpen, hBaseRegular, _, _, _, _, _, _⟩ :=
    deformedBandBase_geometry P ε hFine φ hφ
  have henclose : ∀ t : ↥C.centres,
      mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier ⊆
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
    intro t
    exact secondStage_fullTile_enclosure_local D T₁ hT₁ hTiles
      hBaseOpen hBaseRegular t
  have hdisj := secondStage_target_tiles_disjoint_local ε hFine φ hφ D T₁
    hT₁ hTiles hBaseOpen henclose
  have hcover := secondStage_target_fibre_ae_local ε hFine φ hφ D T₁ hT₁ hTiles
  refine ⟨henclose, hdisj, ?_⟩
  filter_upwards [hcover] with q hq
  constructor
  · intro hqbase
    exact hq hqbase
  · intro hqnot y hex
    obtain ⟨t, ht⟩ := hex
    apply hqnot
    simpa [slicePoint] using henclose t ht



end Tiling.AxisParallel.Approximation
namespace Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Foundations.FilledSliceChains
universe u

/- The exact slot-26-to-slot-27 bridge.  The first three arguments are direct
   canonical predecessor fields; no statement aliases are used. -/
private theorem periodicBand_secondStageTilesOn_of_properCylinderSlices
    (hBaseOpen :
      ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
        (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
        (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
        (_hφ : IsEpsilonApproximation C ε φ),
        IsOpen (deformedBandBase P φ))
    (hInjective :
      ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
        (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
        (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
        (_hφ : IsEpsilonApproximation C ε φ)
        (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane),
        (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) →
        TilesOn D.firstRegion (deformedCenterCarrier T₁)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} →
        Function.Injective
          (fun t : ↥C.centres => mapPoint φ (C.centrePoint t.1 t.2)))
    (hProper :
      ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
        (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
        (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
        (_hφ : IsEpsilonApproximation C ε φ)
        (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane),
        (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) →
        TilesOn D.firstRegion (deformedCenterCarrier T₁)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} →
        (∀ t : ↥C.centres,
          mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier ⊆
            {z : Tiling.Plane | z.re ∈ deformedBandBase P φ}) ∧
        (∀ s t : ↥C.centres, s ≠ t →
          Disjoint
            (mapPoint φ (C.centrePoint s.1 s.2) +ᵥ D.deformedRegion.openCarrier)
            (mapPoint φ (C.centrePoint t.1 t.2) +ᵥ D.deformedRegion.openCarrier)) ∧
        (∀ᵐ q : ℝ ∂volume,
          (q ∈ deformedBandBase P φ → ∀ᵐ y : ℝ ∂volume,
            ∃ t : ↥C.centres,
              slicePoint Axis.vertical q y ∈
                mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
                  D.deformedRegion.openCarrier) ∧
          (q ∉ deformedBandBase P φ → ∀ y : ℝ,
            ¬ ∃ t : ↥C.centres,
              slicePoint Axis.vertical q y ∈
                mapPoint φ (C.centrePoint t.1 t.2) +ᵥ
                  D.deformedRegion.openCarrier))) :
    ∀ {C : ApproximationContext.{u}} {P : PeriodicBandData C}
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ) (T₁ : ↥C.centres ↪ Tiling.Plane),
      (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) →
      TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} →
      ∃ Tφ : ↥C.centres ↪ Tiling.Plane,
        (∀ t, Tφ t = mapPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn D.deformedRegion (deformedCenterCarrier Tφ)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
  intro C P ε hFine φ hφ D T₁ hT₁ hTiles
  let Tφ : ↥C.centres ↪ Tiling.Plane :=
    ⟨fun t => mapPoint φ (C.centrePoint t.1 t.2),
      hInjective ε hFine φ hφ D T₁ hT₁ hTiles⟩
  obtain ⟨_henclose, hdisjoint, hslice⟩ :=
    hProper ε hFine φ hφ D T₁ hT₁ hTiles
  let _ : Countable ↥C.centres := P.source_tilesOn.1.to_subtype
  have hcount : (deformedCenterCarrier Tφ).Countable := by
    exact Set.countable_range Tφ
  have hpack : Set.Pairwise (deformedCenterCarrier Tφ)
      (Disjoint on ((· +ᵥ D.deformedRegion.openCarrier) :
        Tiling.Plane → Set Tiling.Plane)) := by
    intro s hs t ht hst
    obtain ⟨s', rfl⟩ := hs
    obtain ⟨t', rfl⟩ := ht
    by_cases heq : s' = t'
    · subst heq
      exact False.elim (hst rfl)
    · exact hdisjoint s' t' heq
  have hDmeas : MeasurableSet {z : Tiling.Plane |
      z.re ∈ deformedBandBase P φ} :=
    (hBaseOpen ε hFine φ hφ).measurableSet.preimage Complex.continuous_re.measurable
  have hslice' : ∀ᵐ q : ℝ ∂volume, ∀ᵐ y : ℝ ∂volume,
      (slicePoint Axis.vertical q y ∈
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} ↔
        ∃ s : ↥(deformedCenterCarrier Tφ),
          slicePoint Axis.vertical q y ∈
            (s : Tiling.Plane) +ᵥ D.deformedRegion.openCarrier) := by
    filter_upwards [hslice] with q hq
    by_cases hqbase : q ∈ deformedBandBase P φ
    · filter_upwards [hq.1 hqbase] with y hy
      constructor
      · intro _
        obtain ⟨t, ht⟩ := hy
        exact ⟨⟨Tφ t, ⟨t, rfl⟩⟩, by simpa [Tφ] using ht⟩
      · intro _
        simp [slicePoint, hqbase]
    · filter_upwards [] with y
      constructor
      · intro hz
        exfalso
        apply hqbase
        simpa [slicePoint] using hz
      · rintro ⟨s, hs⟩
        obtain ⟨t, ht⟩ := s.property
        rw [← ht] at hs
        exact False.elim ((hq.2 hqbase y) ⟨t, by simpa [Tφ] using hs⟩)
  have hTile := tilesOn_of_axisSlices D.deformedRegion
    (deformedCenterCarrier Tφ)
    {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} Axis.vertical
    hDmeas hcount hpack hslice'
  refine ⟨Tφ, ?_, hTile⟩
  intro t
  rfl

end Tiling.AxisParallel.Approximation
namespace Tiling.AxisParallel.Approximation
universe u

private theorem periodicBand_secondStageTilesOn :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ)
      (T₁ : ↥C.centres ↪ Tiling.Plane),
      (∀ t, T₁ t = mapFirstPoint φ (C.centrePoint t.1 t.2)) →
      TilesOn D.firstRegion (deformedCenterCarrier T₁)
        {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} →
      ∃ Tφ : ↥C.centres ↪ Tiling.Plane,
        (∀ t, Tφ t = mapPoint φ (C.centrePoint t.1 t.2)) ∧
        TilesOn D.deformedRegion (deformedCenterCarrier Tφ)
          {z : Tiling.Plane | z.re ∈ deformedBandBase P φ} := by
  intro C P ε hFine φ hφ D T₁ hT₁ hTiles
  exact periodicBand_secondStageTilesOn_of_properCylinderSlices
    (fun {C' : ApproximationContext.{u}} {P' : PeriodicBandData C'}
        (ε' : ℝ) (hFine' : IsPeriodicBandFineness P' ε')
        (φ' : C'.coordinateSpace →ₗ[ℚ] ℚ)
        (hφ' : IsEpsilonApproximation C' ε' φ') =>
      (deformedBandBase_geometry P' ε' hFine' φ' hφ').1)
    secondStageCentreMap_injective secondStage_properCylinderSlices
    ε hFine φ hφ D T₁ hT₁ hTiles

/-- Public historical A04 endpoint, after the private slot-27 bridge. -/
theorem periodicBandDeformation :
    ∀ {C : ApproximationContext.{u}} (P : PeriodicBandData C)
      (ε : ℝ) (_hFine : IsPeriodicBandFineness P ε)
      (φ : C.coordinateSpace →ₗ[ℚ] ℚ)
      (_hφ : IsEpsilonApproximation C ε φ)
      (D : CoordinateDeformation C φ),
      ∃ (Tφ : ↥C.centres ↪ Tiling.Plane) (Xφ : Set ℝ) (αφ : ℝ),
        (∀ t : ↥C.centres, Tφ t = mapPoint φ (C.centrePoint t.1 t.2)) ∧
        IsOpen Xφ ∧ interior (closure Xφ) = Xφ ∧ Xφ.Nonempty ∧
        Xφ ≠ Set.univ ∧
        αφ = mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩ ∧
        0 < αφ ∧ αφ +ᵥ Xφ = Xφ ∧
        frontier Xφ = Set.range (P.deformedBoundary φ) ∧
        (∀ j : ℤ, P.occupied j = true ↔
          Ioo (P.deformedBoundary φ j) (P.deformedBoundary φ (j + 1)) ⊆ Xφ) ∧
        TilesOn D.deformedRegion (deformedCenterCarrier Tφ)
          {z : Tiling.Plane | z.re ∈ Xφ} ∧
        regularSupport D.deformedRegion (deformedCenterCarrier Tφ) =
          {z : Tiling.Plane | z.re ∈ Xφ} := by
  intro C P ε hFine φ hφ D
  obtain ⟨T₁, hT₁, hFirstTiles⟩ :=
    periodicBand_firstStageTilesOn P ε hFine φ hφ D
  obtain ⟨Tφ, hTφ, hFullTiles⟩ :=
    periodicBand_secondStageTilesOn P ε hFine φ hφ D T₁ hT₁ hFirstTiles
  obtain ⟨hopen, hregular, hnonempty, hproper, hperiodpos, hperiodic,
      hfrontier, hchamber⟩ := deformedBandBase_geometry P ε hFine φ hφ
  let Xφ : Set ℝ := deformedBandBase P φ
  let αφ : ℝ := mapScalar φ ⟨P.period, P.period_mem_coordinateSpace⟩
  have hopenPlane : IsOpen {z : Tiling.Plane | z.re ∈ Xφ} :=
    hopen.preimage Complex.continuous_re
  have hregularPlane : interior (closure {z : Tiling.Plane | z.re ∈ Xφ}) =
      {z : Tiling.Plane | z.re ∈ Xφ} := by
    change interior (closure (Complex.re ⁻¹' Xφ)) = Complex.re ⁻¹' Xφ
    rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hregular]
  have hsupp := regularSupport_eq_of_tilesOn hopenPlane hregularPlane hFullTiles
  refine ⟨Tφ, Xφ, αφ, hTφ, hopen, hregular, hnonempty, hproper, rfl,
    hperiodpos, hperiodic, hfrontier, hchamber, hFullTiles, ?_⟩
  simpa [Xφ] using hsupp

end Tiling.AxisParallel.Approximation
