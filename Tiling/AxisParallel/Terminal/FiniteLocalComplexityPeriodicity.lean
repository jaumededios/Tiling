import Tiling.AxisParallel.Terminal.CommonPeriodAssembly
import Tiling.AxisParallel.Terminal.SimultaneousSlabRationalization
import Tiling.AxisParallel.Approximation.AnchoredRationalApproximation
import Tiling.AxisParallel.Approximation.FiniteLocalComplexityControl
import Tiling.AxisParallel.Approximation.FLCIncidenceGermsAndColumns
import Tiling.AxisParallel.Approximation.RationalPolygonDeformation
import Tiling.AxisParallel.Approximation.GoodApproximationPreservesTilings
import Tiling.AxisParallel.Terminal.RationalSliceCore
import Tiling.AxisParallel.Terminal.RationalFinerStructure
import Tiling.AxisParallel.Terminal.GappedSlices
import Tiling.AxisParallel.Terminal.ObliqueSliceTransport
import Tiling.AxisParallel.Terminal.HorizontalSliceTransport
import Mathlib.LinearAlgebra.Basis.VectorSpace

import Tiling.AxisParallel.Foundations.QuadrantGermGeometry
import Tiling.RationalPolygonal.WeakPeriodicity
import Tiling.AxisParallel.Foundations.IntrinsicVertices
import Tiling.AxisParallel.Continuous.PersistentTransientSlabs

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Tiling.AxisParallel.Foundations.LatticeOrbitRepresentatives
import Tiling.AxisParallel.Terminal.AssemblyCore
import Tiling.AxisParallel.Terminal.TerminalRegionDecomposition

import Tiling.AxisParallel.Approximation.PeriodicBandDeformation
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Terminal.LatticeIntersection
import Tiling.AxisParallel.Approximation.ControlledPeriodLifting
import Tiling.AxisParallel.Terminal.BoundaryCore

import Tiling.AxisParallel.Continuous.PlateCore
import Tiling.AxisParallel.Terminal.PeriodicReplacementCore
import Tiling.AxisParallel.Terminal.VerticalPackingsNoColumn
import Tiling.AxisParallel.Terminal.VerticalPackingsWithColumn
import Tiling.AxisParallel.Terminal.NoGapSliceGeometry

/-!
# Periodic replacements for finite-local-complexity tilings

The main synchronization theorem is built from the terminal slice and slab modules.  This file
starts with its independent null-carrier branch, whose empty centre set is periodic under an
explicit full-rank lattice.
-/

open Set
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

private noncomputable def standardPlanarLattice : Tiling.AxisParallel.PlanarLattice where
  basis := Complex.basisOneI
  independent := Complex.basisOneI.linearIndependent

/-- The empty target has the canonical empty replacement and is weakly periodic. -/
theorem nullCarrier_periodicReplacement (K : Tiling.AxisParallel.Region) :
    Tiling.RationalPolygonal.WeaklyPeriodic (∅ : Set Tiling.Plane) ∧
      Nonempty (PeriodicReplacement K ∅) := by
  constructor
  · refine ⟨{
      numberOfParts := 0
      part := Fin.elim0
      period := Fin.elim0
      period_ne_zero := fun i ↦ Fin.elim0 i
      periodic_part := fun i ↦ Fin.elim0 i
      pairwiseDisjoint := ?_
      iUnion_parts := ?_ }⟩
    · rintro i _hi
      exact Fin.elim0 i
    · simp
  · refine ⟨{
      centres := ∅
      tiles := ?_
      lattice := standardPlanarLattice
      lattice_periods := ?_ }⟩
    · refine ⟨Set.countable_empty, ?_, ?_⟩
      · rw [Tiling.IsPacking]
        rintro i hi
        simp at hi
      · simp
    · intro v _hv
      change v +ᵥ (∅ : Set Tiling.Plane) = ∅
      simp

end Tiling.AxisParallel.Terminal


set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation

private theorem finite_bound (n : ℕ) (a : Fin n → ℝ) :
    ∃ B : ℝ, ∀ i, a i < B := by
  induction n with
  | zero =>
      exact ⟨0, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
      obtain ⟨B, hB⟩ := ih (fun i ↦ a i.succ)
      refine ⟨max (a 0 + 1) B, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact lt_of_lt_of_le (lt_add_one _) (le_max_left _ _)
      · exact lt_of_lt_of_le (hB j) (le_max_right _ _)

private theorem commonOriginalSwappedRecoveryScale_exists
    (C : ApproximationContext.{0}) (delta G Gswap : ℝ) (N0 : ℕ)
    {n m : ℕ} (sourceRadius : Fin n → ℝ)
    (swappedRadius : Fin m → ℝ)
    (hdelta : 0 < delta) (hG : 0 < G) (hGswap : 0 < Gswap)
        (_hN0 : (N0 : ℝ) * delta > 4 * Metric.diam C.region.support) :
    ∃ M : ℝ, 0 < M ∧
      (∀ i, sourceRadius i < M) ∧
      (∀ i, swappedRadius i < M) ∧
      (N0 : ℝ) * G + 2 * Metric.diam C.region.support < M ∧
      (N0 : ℝ) * Gswap + 2 * Metric.diam C.region.support < M ∧
      2 / delta < M ∧
      G + M⁻¹ < M / 2 ∧ Gswap + M⁻¹ < M / 2 := by
  obtain ⟨Bsource, hBsource⟩ := finite_bound n sourceRadius
  obtain ⟨Bswap, hBswap⟩ := finite_bound m swappedRadius
  let d : ℝ := Metric.diam C.region.support
  let A : ℝ := (N0 : ℝ) * G + 2 * d
  let Aswap : ℝ := (N0 : ℝ) * Gswap + 2 * d
  let M : ℝ := 2 + max 0 Bsource + max 0 Bswap +
    max 0 A + max 0 Aswap + 2 / delta + 2 * G + 2 * Gswap
  have hdel : 0 < 2 / delta := div_pos (by norm_num) hdelta
  have hBsource0 : 0 ≤ max 0 Bsource := le_max_left _ _
  have hBswap0 : 0 ≤ max 0 Bswap := le_max_left _ _
  have hA0 : 0 ≤ max 0 A := le_max_left _ _
  have hAswap0 : 0 ≤ max 0 Aswap := le_max_left _ _
  have hM : 0 < M := by
    dsimp [M]
    linarith
  have hMone : 1 < M := by
    dsimp [M]
    linarith
  have hMsource : Bsource < M := by
    dsimp [M]
    have h := le_max_right 0 Bsource
    linarith
  have hMswap : Bswap < M := by
    dsimp [M]
    have h := le_max_right 0 Bswap
    linarith
  have hMA : A < M := by
    dsimp [M]
    have h := le_max_right 0 A
    linarith
  have hMAswap : Aswap < M := by
    dsimp [M]
    have h := le_max_right 0 Aswap
    linarith
  have hMdelta : 2 / delta < M := by
    dsimp [M]
    linarith
  have hMinv : M⁻¹ < 1 := by
    rw [inv_lt_one₀ hM]
    exact hMone
  refine ⟨M, hM, ?_, ?_, ?_, ?_, hMdelta, ?_, ?_⟩
  · intro i
    exact hBsource i |>.trans hMsource
  · intro i
    exact hBswap i |>.trans hMswap
  · dsimp only [A] at hMA
    exact hMA
  · dsimp only [Aswap] at hMAswap
    exact hMAswap
  · have hMG : 2 * G + 2 < M := by
      dsimp [M]
      linarith [le_max_left 0 Bsource, le_max_left 0 Bswap,
        le_max_left 0 A, le_max_left 0 Aswap, hdel]
    linarith
  · have hMGswap : 2 * Gswap + 2 < M := by
      dsimp [M]
      linarith [le_max_left 0 Bsource, le_max_left 0 Bswap,
        le_max_left 0 A, le_max_left 0 Aswap, hdel]
    linarith

private theorem finiteDecoration_hasFLC
    {V P : Set Tiling.Plane} (hV : V.Finite) (hP : HasFLC P) :
    HasFLC (V + P) := by
  let F : Finset Tiling.Plane := hV.toFinset
  have hFV : (F : Set Tiling.Plane) = V := hV.coe_toFinset
  rw [← hFV]
  simpa [add_comm] using hP.add_finset F


private theorem connectedIndexedPeriodLift :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (S : Set ↥C.centres) (G : ℝ),
      S.Nonempty → Linked G (Subtype.val '' S) →
      (∃ c, ∀ s : S, axis.transverseCoord (Tphi s.1) = c) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ imagePeriod : Tiling.Plane,
      imagePeriod ≠ 0 →
      axis.transverseCoord imagePeriod = 0 →
      imagePeriod +ᵥ deformedCenterCarrierOn Tphi S =
        deformedCenterCarrierOn Tphi S →
      ∃ alpha : {z : Tiling.Plane |
          z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        alpha.1 ≠ 0 ∧
        axis.transverseCoord alpha.1 = 0 ∧
        mapPoint phi alpha = imagePeriod ∧
        alpha.1 +ᵥ Subtype.val '' S = Subtype.val '' S := by
  intro C P phi hphi Tphi hTphi axis S G hSne hLinked hcol hG hmargin
    imagePeriod hne haxis hperiod
  obtain ⟨hSnonempty, hconn⟩ := hLinked
  have hIndexed : IndexedShortEdgeConnected C G S := by
    intro x hx y hy
    exact hconn x hx y hy
  exact connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis S G
    hSne hIndexed hcol hG hmargin imagePeriod hne haxis hperiod

private theorem connectedPhasePeriodLifts_synchronize :
    ∀ {C : ApproximationContext.{0}} (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
    IsEpsilonApproximation C P.threshold phi →
    ∀ (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
    ∀ (axis : Axis) (phase : ℤ → Set ↥C.centres) (G : ℝ),
      (∀ m, (phase m).Nonempty) →
      (∀ m, Linked G (Subtype.val '' phase m)) →
      (∀ m, ∃ c, ∀ s : phase m,
        axis.transverseCoord (Tphi s.1) = c) →
      G < P.scale → G + P.localError < P.scale / 2 →
    ∀ (imagePeriod : Tiling.Plane),
      imagePeriod ≠ 0 →
      axis.transverseCoord imagePeriod = 0 →
      (∀ m, imagePeriod +ᵥ deformedCenterCarrierOn Tphi (phase m) =
        deformedCenterCarrierOn Tphi (phase m)) →
    ∀ (beta : ℤ → {z : Tiling.Plane |
        z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace})
      (imageShift : ℤ → Tiling.Plane),
      (∀ m,
        regularSupport C.region (Subtype.val '' phase m) =
          (beta m).1 +ᵥ regularSupport C.region (Subtype.val '' phase 0)) →
      (∀ m, mapPoint phi (beta m) = imageShift m) →
      (properVertices
        (regularSupport C.region (Subtype.val '' phase 0))).Nonempty →
      ∃ alpha : {z : Tiling.Plane |
          z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        alpha.1 ≠ 0 ∧
        axis.transverseCoord alpha.1 = 0 ∧
        mapPoint phi alpha = imagePeriod ∧
        ∀ m, alpha.1 +ᵥ Subtype.val '' phase m = Subtype.val '' phase m := by
  intro C P phi hphi Tphi hTphi axis phase G hnonempty hlinked hcol hG hmargin
    imagePeriod hne haxis hperiod beta imageShift hsupp hmapBeta hproper
  have hphase : ∀ m : ℤ, ∃ alpha : ControlledDisplacement C,
      alpha.1 ≠ 0 ∧ axis.transverseCoord alpha.1 = 0 ∧
      mapPoint phi alpha = imagePeriod ∧
      alpha.1 +ᵥ Subtype.val '' phase m = Subtype.val '' phase m := by
    intro m
    obtain ⟨hSnonempty, hconn⟩ := hlinked m
    have hIndexed : IndexedShortEdgeConnected C G (phase m) := by
      intro x hx y hy
      exact hconn x hx y hy
    exact connectedAlignedIndexedPeriodLift P phi hphi Tphi hTphi axis
      (phase m) G (hnonempty m) hIndexed (hcol m) hG hmargin imagePeriod hne haxis
      (hperiod m)
  let alpha : ℤ → ControlledDisplacement C := fun m => Classical.choose (hphase m)
  have halpha (m : ℤ) := Classical.choose_spec (hphase m)
  have hsynchronized : ∀ m : ℤ, alpha m = alpha 0 := by
    intro m
    exact periodLifts_synchronizeFamily P phi hphi 0 phase alpha beta imagePeriod
      (fun j ↦ (halpha j).2.2.1)
      (fun j ↦ (halpha j).2.2.2)
      hsupp hproper m
  refine ⟨alpha 0, (halpha 0).1, (halpha 0).2.1, (halpha 0).2.2.1, ?_⟩
  intro m
  rw [← hsynchronized m]
  exact (halpha m).2.2.2
private theorem properVertices_regularSupport_subset_vertices_add
    {K : Region} {T S E : Set Tiling.Plane}
    (hTiles : TilesOn K T E) (hS : S ⊆ T) :
    properVertices (regularSupport K S) ⊆ K.vertices + S := by
  intro x hx
  let A := K.polygonalProtoTiling S
  have hpack : Tiling.IsPacking A.prototiles A.placements := by
    intro i hi j hj hij
    apply hTiles.2.1
    · exact hS hi
    · exact hS hj
    · exact hij
  have hcarrier : A.placementCarrier Set.univ =
      closure (openUnion K S) := by
    rw [Tiling.PolygonalProtoTiling.placementCarrier]
    rw [closure_openUnion_eq_iUnion_support hpack]
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      rw [Set.mem_iUnion]
      exact ⟨⟨i.1.1.1, i.1.2⟩, hi⟩
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨s, hs⟩ := hz
      rw [Set.mem_iUnion]
      let i : A.placements := ⟨((s : Tiling.Plane), ()), s.2⟩
      refine ⟨⟨i, trivial⟩, ?_⟩
      exact hs
  have hfrontier_eq :
      frontier (A.placementCarrier Set.univ) =
        frontier (regularSupport K S) := by
    rw [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion, ← hcarrier]
    simp [frontier, A.placementCarrier_closure_interior hpack Set.univ,
      (A.placementCarrier_isClosed hpack Set.univ).closure_eq]
  have hxfrontier : x ∈ frontier (A.placementCarrier Set.univ) := by
    rw [hfrontier_eq]
    exact hx.1
  have hxnotstraight : ¬Tiling.BoundaryLocallyStraightAt
      (A.placementCarrier Set.univ) x := by
    intro hstraight
    apply hx.2
    simpa only [Tiling.BoundaryLocallyStraightAt, hfrontier_eq] using hstraight
  obtain ⟨i, hiQ, hxi⟩ :=
    A.exists_vertex_of_not_boundaryLocallyStraightAt hpack Set.univ
      hxfrontier hxnotstraight
  have hcenterS : i.1.1 ∈ S := i.2
  have hplaced : x ∈ i.1.1 +ᵥ K.vertices := by
    simpa only [A, Region.polygonalProtoTiling_placedVertices] using hxi
  obtain ⟨v, hv, hvx⟩ := Set.mem_vadd_set.mp hplaced
  refine ⟨v, hv, i.1.1, hcenterS, ?_⟩
  simpa [vadd_eq_add, add_comm] using hvx

end Tiling.AxisParallel.Terminal

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation

private theorem rankTwo_of_flcCoset_and_independentRationalImages
    {P V : Set Tiling.Plane} {lambda gamma : Tiling.Plane}
    (hP : HasFLC P) (hV : V.Finite)
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (hfind : LinearIndependent ℚ ![f lambda, f gamma])
    (hcoset : ∃ v : Tiling.Plane,
      {x : Tiling.Plane | ∃ m n : ℤ,
        x = v + m • lambda + n • gamma} ⊆ V + P) :
    LinearIndependent ℝ ![lambda, gamma] := by
  classical
  have hQ : HasFLC (V + P) := finiteDecoration_hasFLC hV hP
  obtain ⟨delta, hdelta, hsep⟩ := hQ.uniformlyDiscrete
  have hlambda : lambda ≠ 0 := by
    intro hzero
    have hfzero : f lambda = 0 := by simp [hzero]
    have hbad := hfind.eq_zero_of_pair (s := (1 : ℚ)) (t := (0 : ℚ))
      (by simp [hfzero])
    exact one_ne_zero hbad.1
  have hgamma : gamma ≠ 0 := by
    intro hzero
    have hfzero : f gamma = 0 := by simp [hzero]
    have hbad := hfind.eq_zero_of_pair (s := (0 : ℚ)) (t := (1 : ℚ))
      (by simp [hfzero])
    exact one_ne_zero hbad.2
  by_contra hli
  have hrel_data : ∃ (a b : ℝ),
      (a ≠ 0 ∨ b ≠ 0) ∧ a • lambda + b • gamma = 0 := by
    have hdep : ∃ g : Fin 2 → ℝ,
        (∑ i, g i • ![lambda, gamma] i = 0) ∧ ∃ i, g i ≠ 0 :=
      (Fintype.not_linearIndependent_iff (v := ![lambda, gamma])).mp hli
    obtain ⟨g, hg, hgzero⟩ := hdep
    have hrel' : g 0 • lambda + g 1 • gamma = 0 := by
      simpa [Fin.sum_univ_two] using hg
    have hab' : g 0 ≠ 0 ∨ g 1 ≠ 0 := by
      obtain ⟨i, hi⟩ := hgzero
      fin_cases i
      · exact Or.inl hi
      · exact Or.inr hi
    exact ⟨g 0, g 1, hab', hrel'⟩
  obtain ⟨a, b, hab, hrel⟩ := hrel_data
  have hb : b ≠ 0 := by
    intro hb
    have hal : a • lambda = 0 := by simpa [hb] using hrel
    have ha : a ≠ 0 := by
      intro ha
      exact hab.elim (fun h => h ha) (fun h => h hb)
    exact hlambda ((smul_eq_zero.mp hal).resolve_left ha)
  let r : ℝ := -a / b
  have hratio : gamma = r • lambda := by
    have hbg : b • gamma = -(a • lambda) :=
      eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hrel)
    calc
      gamma = (1 : ℝ) • gamma := by simp
      _ = (b⁻¹ * b) • gamma := by rw [inv_mul_cancel₀ hb]
      _ = b⁻¹ • (b • gamma) := by rw [mul_smul]
      _ = b⁻¹ • (-(a • lambda)) := by rw [hbg]
      _ = r • lambda := by
        dsimp [r]
        simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hri : Irrational r := by
    rw [irrational_iff_ne_rational]
    intro a b hb hq
    let q : ℚ := a / b
    have hqreal : r = (q : ℝ) := by
      dsimp [q]
      simpa using hq
    have hqrel : gamma = q • lambda := by
      calc
        gamma = r • lambda := hratio
        _ = (q : ℝ) • lambda := by rw [hqreal]
        _ = q • lambda := Rat.cast_smul_eq_qsmul ℝ q lambda
    have hfq : f gamma = (q : ℚ) • f lambda := by
      rw [hqrel, map_smul]
    have hzero : (q : ℚ) • f lambda + (-1 : ℚ) • f gamma = 0 := by
      rw [hfq]
      module
    have hbad := hfind.eq_zero_of_pair hzero
    norm_num at hbad
  have hnormlambda : 0 < ‖lambda‖ := norm_pos_iff.mpr hlambda
  obtain ⟨n, hn⟩ := exists_nat_gt (‖lambda‖ / delta)
  have hnpos : 0 < n := by
    by_contra hnzero
    have hn' : n = 0 := Nat.eq_zero_of_not_pos hnzero
    have hn0 : ‖lambda‖ / delta < (0 : ℝ) := by
      simpa only [hn', Nat.cast_zero] using hn
    exact (not_lt_of_ge (div_nonneg (norm_nonneg _) hdelta.le)) hn0
  obtain ⟨k, hkpos, hkn, hkapprox⟩ :=
    Real.exists_nat_abs_mul_sub_round_le r (n_pos := hnpos)
  let l : ℤ := round ((k : ℝ) * r)
  have hlapprox : |(k : ℝ) * r - (l : ℝ)| ≤ 1 / ((n : ℝ) + 1) := by
    simpa [l] using hkapprox
  have hnormsmall :
      |(k : ℝ) * r - (l : ℝ)| * ‖lambda‖ < delta := by
    have hquot : ‖lambda‖ / ((n : ℝ) + 1) < delta := by
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).2
      have hnmul : ‖lambda‖ < (n : ℝ) * delta :=
        (div_lt_iff₀ hdelta).mp hn
      have hstep : (n : ℝ) < (n : ℝ) + 1 := by linarith
      have := mul_lt_mul_of_pos_right hstep hdelta
      nlinarith
    have hquot' : ‖lambda‖ * ((n : ℝ) + 1)⁻¹ < delta := by
      simpa [div_eq_mul_inv] using hquot
    exact (mul_le_mul_of_nonneg_right hlapprox (norm_nonneg lambda)).trans_lt
      (by simpa [mul_comm] using hquot')
  have hcomb_eq :
      (k : ℤ) • gamma + (-l) • lambda =
        (((k : ℝ) * r - (l : ℝ)) • lambda) := by
    rw [hratio]
    simp [← Int.cast_smul_eq_zsmul ℝ]
    ring
  have hcomb_ne : (k : ℤ) • gamma + (-l) • lambda ≠ 0 := by
    intro hzero
    have hfzero := congrArg f hzero
    have hfzero_z : (-l : ℤ) • f lambda + (k : ℤ) • f gamma = 0 := by
      rw [← map_zsmul, ← map_zsmul, ← map_add]
      simpa [add_comm] using hfzero
    have hfzero' : ((↑(-l) : ℚ) • f lambda + (↑(k : ℤ) : ℚ) • f gamma = 0) := by
      rw [Int.cast_neg, neg_smul, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
      simpa [neg_zsmul] using hfzero_z
    have hbad := hfind.eq_zero_of_pair hfzero'
    have hkq : ((k : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkpos)
    exact hkq hbad.2
  obtain ⟨v, hv⟩ := hcoset
  let c : Tiling.Plane := (k : ℤ) • gamma + (-l) • lambda
  let x : Tiling.Plane := c + v
  have hxQ : x ∈ V + P := by
    apply hv
    refine ⟨-l, k, ?_⟩
    dsimp [x, c]
    ac_rfl
  have hvQ : v ∈ V + P := by
    apply hv
    exact ⟨0, 0, by simp⟩
  have hxne : x ≠ v := by
    intro hxeq
    dsimp [x] at hxeq
    have hc_eq : c + v = 0 + v := by simpa using hxeq
    have hc : c = 0 := add_right_cancel hc_eq
    exact hcomb_ne (by simpa [c] using hc)
  have hdist : dist x v < delta := by
    change dist (c + v) v < delta
    rw [← vadd_eq_add, dist_vadd_left]
    dsimp [c]
    rw [hcomb_eq, norm_smul, Real.norm_eq_abs]
    exact hnormsmall
  exact (not_lt_of_ge (hsep x hxQ v hvQ hxne)) hdist


private theorem finite_inter_of_bounded_of_pairwise_le_dist
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {S Q : Set E} {delta : ℝ} (hdelta : 0 < delta)
    (hS : S.Pairwise fun x y ↦ delta ≤ dist x y)
    (hQ : Bornology.IsBounded Q) : (S ∩ Q).Finite := by
  have hSclosed : IsClosed S := Metric.isClosed_of_pairwise_le_dist hdelta hS
  have hSdiscrete : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    intro s hs
    refine ⟨Metric.ball s delta, Metric.isOpen_ball, ?_⟩
    ext t
    constructor
    · rintro ⟨htball, htS⟩
      by_cases hts : t = s
      · simp [hts]
      · have hsep := hS htS hs hts
        simp only [Metric.mem_ball] at htball
        exfalso
        linarith
    · rintro rfl
      exact ⟨Metric.mem_ball_self hdelta, hs⟩
  obtain ⟨R, hR⟩ := hQ.subset_closedBall (0 : E)
  have hcompact : IsCompact (S ∩ Metric.closedBall 0 R) :=
    Metric.isCompact_of_isClosed_isBounded
      (hSclosed.inter Metric.isClosed_closedBall)
      (Metric.isBounded_closedBall.subset inter_subset_right)
  apply (hcompact.finite (hSdiscrete.mono inter_subset_left)).subset
  exact inter_subset_inter_right S hR

private theorem periodicOrbitSupports_finite
    {K : Region} {I : Type} (D : I → Set Tiling.Plane)
      (Lambda : PlanarLattice) :
    (∀ i, IsOpen (D i)) →
    (∀ i, interior (closure (D i)) = D i) →
    (∀ i, (D i).Nonempty) →
    (∀ i j, i ≠ j → AEDisjoint volume (D i) (D j)) →
    (∀ i, Lambda.toAddSubgroup ≤ periodGroup (D i)) →
    (∀ i, ∃ t : Tiling.Plane, t +ᵥ K.openCarrier ⊆ D i) →
      Finite I := by
  intro hopen hregular hnonempty hdisjoint hperiod hcontain
  obtain ⟨u, hu⟩ := K.isPolygonal.interior_nonempty K.nonempty
  change u ∈ K.openCarrier at hu
  have hnhds : K.openCarrier ∈ 𝓝 u :=
    (Region.openCarrier_regularOpen K).1.mem_nhds hu
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let raw : I → Tiling.Plane := fun i => (Classical.choose (hcontain i)) + u
  let centres : I → Tiling.Plane := fun i =>
    ZSpan.fract Lambda.realBasis (raw i)
  have hraw_mem (i : I) : raw i ∈ (Classical.choose (hcontain i)) +ᵥ K.openCarrier := by
    exact ⟨u, hu, rfl⟩
  have hfloor (i : I) :
      (ZSpan.floor Lambda.realBasis (raw i) : Tiling.Plane) ∈ Lambda.toAddSubgroup := by
    rw [← Lambda.span_realBasis_toAddSubgroup]
    exact (ZSpan.floor Lambda.realBasis (raw i)).property
  have hcentre_mem (i : I) : centres i ∈ ZSpan.fundamentalDomain Lambda.realBasis := by
    exact ZSpan.fract_mem_fundamentalDomain Lambda.realBasis (raw i)
  have hcentre_ball (i : I) :
      Metric.ball (centres i) r ⊆ D i := by
    intro z hz
    let f : Tiling.Plane := ZSpan.floor Lambda.realBasis (raw i)
    have hcentre_eq : centres i = raw i - f := by
      simp [centres, f, ZSpan.fract_apply]
    have hperiodic : (-f) +ᵥ D i = D i := by
      apply (periodGroup_isAddSubgroup (D i) (-f)).mp
      apply hperiod i
      exact neg_mem (hfloor i)
    rw [← hperiodic]
    refine ⟨z + f, ?_, ?_⟩
    · rw [show centres i = raw i - f by
        exact hcentre_eq] at hz
      have hzraw : z + f ∈ Metric.ball (raw i) r := by
        simpa [Metric.mem_ball, dist_eq_norm_sub, sub_eq_add_neg, add_assoc,
          add_comm, add_left_comm] using hz
      have hballraw : Metric.ball (raw i) r ⊆
          (Classical.choose (hcontain i)) +ᵥ K.openCarrier := by
        intro w hw
        refine Set.mem_vadd_set.mpr ⟨w - Classical.choose (hcontain i), ?_, ?_⟩
        · apply hball
          simpa [raw, dist_eq_norm_sub, sub_eq_add_neg, add_assoc,
            add_comm, add_left_comm] using hw
        · simp only [vadd_eq_add]
          abel
      exact (Classical.choose_spec (hcontain i)) (hballraw hzraw)
    · simp only [vadd_eq_add]
      abel
  have hDdisjoint : ∀ i j, i ≠ j → Disjoint (D i) (D j) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro z hzi hzj
    have hopen_inter : IsOpen (D i ∩ D j) := (hopen i).inter (hopen j)
    have hpos : volume (D i ∩ D j) ≠ 0 :=
      hopen_inter.measure_ne_zero volume ⟨z, hzi, hzj⟩
    exact hpos ((hdisjoint i j hij).eq)
  have hcentres_sep : ∀ i j, i ≠ j → 2 * r ≤ dist (centres i) (centres j) := by
    intro i j hij
    simpa [two_mul] using
      (disjoint_ball_ball_iff hr hr).mp
        ((hDdisjoint i j hij).mono (hcentre_ball i) (hcentre_ball j))
  have hrange : (Set.range centres ∩ ZSpan.fundamentalDomain Lambda.realBasis).Finite :=
    finite_inter_of_bounded_of_pairwise_le_dist (delta := 2 * r) (by linarith)
      (by
        rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne
        exact hcentres_sep i j (by
          intro hij
          apply hne
          rw [hij]))
      (ZSpan.fundamentalDomain_isBounded Lambda.realBasis)
  have hrange_finite : (Set.range centres).Finite := by
    apply hrange.subset
    intro x hx
    exact ⟨hx, by
      obtain ⟨i, rfl⟩ := hx
      exact hcentre_mem i⟩
  have hrange' : (centres '' (Set.univ : Set I)).Finite := by
    rw [Set.image_univ]
    exact hrange_finite
  have huniv : (Set.univ : Set I).Finite :=
    hrange'.of_finite_image (s := Set.univ) (f := centres) (by
      intro i hi j hj hij
      by_contra hne
      have hsep := hcentres_sep i j hne
      rw [hij, dist_self] at hsep
      linarith)
  exact @Finite.of_injective I (↥(Set.univ : Set I)) huniv.to_subtype
    (fun i : I => (⟨i, trivial⟩ : ↥(Set.univ : Set I)))
    (by
      intro i j hij
      exact congrArg Subtype.val hij)


private structure DecompositionColumnReplacement
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) where
  family : ColumnReplacementFamily D.selectedRegion
  family_base : family.base = D.slabs.columnBase
  family_source : family.sourceCentres = D.selectedColumnCentres

private theorem periodicBy_mem_periodGroup
    {S : Set Tiling.Plane} {u : Tiling.Plane}
    (hS : Tiling.RationalPolygonal.SetPeriodicBy S u) :
    u ∈ Tiling.AxisParallel.periodGroup S := by
  apply (Tiling.AxisParallel.periodGroup_isAddSubgroup S u).mpr
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [add_comm] using (hS y).mpr hy
  · intro hx
    refine ⟨x - u, ?_, ?_⟩
    · apply (hS (x - u)).mp
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hx
    · simp [sub_eq_add_neg]

private theorem terminalDecomposition_columnReplacementFamily
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    D.selectedColumnCentres.Nonempty →
      Nonempty (DecompositionColumnReplacement D) := by
  intro hselected
  have hsubset : D.selectedColumnCentres ⊆ D.selectedCentres := by
    rw [D.selectedColumnCentres_eq_slabs]
    intro z hz
    rw [← D.slabs.centres_partition]
    exact Or.inl hz
  have hpacking : Tiling.IsPacking D.selectedRegion.toPolygonalRegion.prototileFamily
      (D.selectedRegion.toPolygonalRegion.placements D.selectedColumnCentres) := by
    intro s hs t ht hst
    exact D.selected_tiles.2.1 (hsubset hs) (hsubset ht) hst
  have hcount : D.selectedColumnCentres.Countable :=
    (IsPacking.locallyFinite_centres hpacking).2
  have hsource_tiles :
      TilesOn D.selectedRegion D.selectedColumnCentres
        {z : Tiling.Plane | z.re ∈ D.slabs.columnBase} := by
    refine ⟨hcount, hpacking, ?_⟩
    have hae := openUnion_aeEq_regularSupport hpacking
    have hsupport : regularSupport D.selectedRegion D.selectedColumnCentres =
        Complex.re ⁻¹' D.slabs.columnBase := by
      rw [D.selectedColumnCentres_eq_slabs]
      exact D.slabs.columnSupport_eq
    filter_upwards [hae] with z hz
    change (z ∈ Complex.re ⁻¹' D.slabs.columnBase ↔
      ∃ s : D.selectedColumnCentres,
        z ∈ ((s : Tiling.Plane) +ᵥ D.selectedRegion.openCarrier))
    rw [← hsupport]
    have hopen : z ∈ openUnion D.selectedRegion D.selectedColumnCentres ↔
        ∃ s : D.selectedColumnCentres,
          z ∈ ((s : Tiling.Plane) +ᵥ D.selectedRegion.openCarrier) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact Set.mem_iUnion
    exact (Iff.of_eq hz.symm).trans hopen
  obtain ⟨haxes, hcolumn, ⟨alpha, beta, halpha, hbeta, hbetaAxes,
    halphaFibre, hfree⟩⟩ := D.slabs.columnInterface
      (by simpa [D.selectedColumnCentres_eq_slabs] using hselected)
  let replacement : ℝ → Set Tiling.Plane := fun shear ↦
    Classical.choose (hfree shear)
  have replacement_spec : ∀ shear : ℝ,
      Tiling.IsPacking D.selectedRegion.toPolygonalRegion.prototileFamily
        (D.selectedRegion.toPolygonalRegion.placements (replacement shear)) ∧
      regularSupport D.selectedRegion (replacement shear) =
        regularSupport D.selectedRegion D.slabs.columnCentres ∧
      Tiling.RationalPolygonal.SetPeriodicBy (replacement shear)
        ((alpha : ℂ) * Complex.I) ∧
      Tiling.RationalPolygonal.SetPeriodicBy (replacement shear)
        ((beta : ℂ) + (shear : ℂ) * Complex.I) ∧
      Tiling.AxisParallel.IsLatticePeriodic (replacement shear) := by
    intro shear
    exact Classical.choose_spec (hfree shear)
  have replacement_tiles : ∀ shear : ℝ,
      TilesOn D.selectedRegion (replacement shear)
        {z : Tiling.Plane | z.re ∈ D.slabs.columnBase} := by
    intro shear
    have hpack := (replacement_spec shear).1
    have hcount : (replacement shear).Countable :=
      (IsPacking.locallyFinite_centres hpack).2
    refine ⟨hcount, hpack, ?_⟩
    have hae := openUnion_aeEq_regularSupport hpack
    have hsupport : regularSupport D.selectedRegion (replacement shear) =
        Complex.re ⁻¹' D.slabs.columnBase := by
      rw [(replacement_spec shear).2.1]
      rw [D.slabs.columnSupport_eq]
    filter_upwards [hae] with z hz
    change (z ∈ Complex.re ⁻¹' D.slabs.columnBase ↔
      ∃ s : replacement shear,
        z ∈ ((s : Tiling.Plane) +ᵥ D.selectedRegion.openCarrier))
    rw [← hsupport]
    have hopen : z ∈ openUnion D.selectedRegion (replacement shear) ↔
        ∃ s : replacement shear,
          z ∈ ((s : Tiling.Plane) +ᵥ D.selectedRegion.openCarrier) := by
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier]
      exact Set.mem_iUnion
    exact (Iff.of_eq hz.symm).trans hopen
  let family : ColumnReplacementFamily D.selectedRegion := {
    base := D.slabs.columnBase
    base_measurable := by
      rw [← D.slabs.columnBase_regular]
      exact measurableSet_interior
    sourceCentres := D.selectedColumnCentres
    source_nonempty := hselected
    source_tiles := hsource_tiles
    verticalPeriod := alpha
    axisPeriod := beta
    verticalPeriod_pos := halpha
    axisPeriod_pos := hbeta
    replacement := replacement
    replacement_tiles := replacement_tiles
    replacement_verticalPeriod := fun shear ↦
      periodicBy_mem_periodGroup (replacement_spec shear).2.2.1
    replacement_axisPeriod := fun shear ↦
      periodicBy_mem_periodGroup (replacement_spec shear).2.2.2.1
  }
  exact ⟨⟨family, rfl, rfl⟩⟩


end Tiling.AxisParallel.Terminal


set_option linter.unusedVariables false

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel
open Tiling.AxisParallel.Approximation
open Tiling.AxisParallel.Continuous

private def SelectedTerminalConclusion
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) : Prop :=
  Tiling.RationalPolygonal.WeaklyPeriodic R.selectedCentres ∧
    Nonempty (PeriodicReplacement R.selectedRegion
      (regularSupport R.selectedRegion R.selectedCentres)) ∧
    ∃ (v : Tiling.Plane) (Lambda : PlanarLattice),
      v +ᵥ (Lambda.toAddSubgroup : Set Tiling.Plane) ⊆
        R.selectedRegion.vertices + R.selectedCentres

private def mapLattice (L : PlanarLattice) : PlanarLattice where
  basis := fun i ↦ coordinateSwap (L.basis i)
  independent := L.independent.map' coordinateSwap.toLinearMap coordinateSwap.ker

private theorem mapLattice_preimage_mem
    (L : PlanarLattice) {z : Tiling.Plane}
    (hz : z ∈ (mapLattice L).toAddSubgroup) :
    coordinateSwap z ∈ L.toAddSubgroup := by
  refine AddSubgroup.closure_induction (p := fun z _ ↦
      coordinateSwap z ∈ L.toAddSubgroup) ?_ ?_ ?_ ?_ hz
  · rintro z ⟨i, rfl⟩
    change coordinateSwap (coordinateSwap (L.basis i)) ∈ L.toAddSubgroup
    rw [coordinateSwap_apply_apply]
    exact AddSubgroup.subset_closure (Set.mem_range_self i)
  · exact L.toAddSubgroup.zero_mem
  · intro a b _ _ ha hb
    simpa only [map_add] using L.toAddSubgroup.add_mem ha hb
  · intro a _ ha
    simpa only [map_neg] using L.toAddSubgroup.neg_mem ha

private def mapReplacement
    {K : Region} {E : Set Tiling.Plane}
    (P : PeriodicReplacement K E) :
    PeriodicReplacement K.coordinateSwap (coordinateSwap '' E) := by
  refine {
    centres := coordinateSwap '' P.centres
    tiles := tilesOn_coordinateSwap P.tiles
    lattice := mapLattice P.lattice
    lattice_periods := ?_ }
  intro z hz
  refine AddSubgroup.closure_induction
      (p := fun z _ ↦ z ∈ periodGroup (coordinateSwap '' P.centres))
    ?_ ?_ ?_ ?_ hz
  · rintro z ⟨i, rfl⟩
    exact Tiling.AxisParallel.coordinateSwap_periodGroup (P.lattice_periods
      (AddSubgroup.subset_closure (Set.mem_range_self i)))
  · exact (periodGroup (coordinateSwap '' P.centres)).zero_mem
  · exact fun a b _ _ ha hb => (periodGroup (coordinateSwap '' P.centres)).add_mem ha hb
  · exact fun a _ ha => (periodGroup (coordinateSwap '' P.centres)).neg_mem ha

private theorem selectedTerminalConclusion_to_original
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) :
    SelectedTerminalConclusion R →
      Tiling.RationalPolygonal.WeaklyPeriodic R.centres ∧
      Nonempty (PeriodicReplacement K (regularSupport K R.centres)) ∧
      ∃ (v : Tiling.Plane) (Lambda : PlanarLattice),
        v +ᵥ (Lambda.toAddSubgroup : Set Tiling.Plane) ⊆ K.vertices + R.centres := by
  intro h
  rcases h with ⟨hweak, hrep, v, L, hcoset⟩
  cases hO : R.orientation with
  | vertical =>
    have hK := R.selectedRegion_vertical hO
    have hS := R.selectedCentres_vertical hO
    have hrep' : Nonempty (PeriodicReplacement K (regularSupport K R.centres)) := by
      simpa [hK, hS] using hrep
    have hcoset' : v +ᵥ (L.toAddSubgroup : Set Tiling.Plane) ⊆
        K.vertices + R.centres := by
      simpa [hK, hS] using hcoset
    exact ⟨by simpa [hS] using hweak, hrep', v, L, hcoset'⟩
  | horizontal =>
    have hK := R.selectedRegion_horizontal hO
    have hS := R.selectedCentres_horizontal hO
    constructor
    · simpa only [hS, IntrinsicVertices.coordinateSwap_image_image] using
        Tiling.AxisParallel.coordinateSwap_weaklyPeriodic hweak
    constructor
    · rcases hrep with ⟨P⟩
      have P0 : PeriodicReplacement K.coordinateSwap
          (regularSupport K.coordinateSwap R.selectedCentres) := by
        simpa [hK] using P
      have P' := mapReplacement P0
      rw [hS, regularSupport_coordinateSwap] at P'
      rw [Region.coordinateSwap_involutive] at P'
      rw [IntrinsicVertices.coordinateSwap_image_image] at P'
      exact ⟨P'⟩
    · refine ⟨coordinateSwap v, mapLattice L, ?_⟩
      intro x hx
      rcases hx with ⟨z, hz, rfl⟩
      have hz' : coordinateSwap z ∈ L.toAddSubgroup := mapLattice_preimage_mem L hz
      have hy : coordinateSwap (coordinateSwap v + z) ∈
          v +ᵥ (L.toAddSubgroup : Set Tiling.Plane) := by
        refine ⟨coordinateSwap z, hz', ?_⟩
        simp only [vadd_eq_add, map_add, coordinateSwap_apply_apply]
      have hmem := hcoset hy
      rcases hmem with ⟨a, ha, b, hb, hab⟩
      rw [hK] at ha
      have hverts : (K.coordinateSwap).vertices =
          coordinateSwap '' K.vertices := by
        exact Region.vertices_coordinateSwap K
      have ha' : a ∈ coordinateSwap '' K.vertices := by
        rw [← hverts]
        exact ha
      rcases ha' with ⟨a₀, ha₀, haa₀⟩
      have hb' : b ∈ coordinateSwap '' R.centres := by
        rw [hS] at hb
        exact hb
      rcases hb' with ⟨b₀, hb₀, hbb₀⟩
      have hxeq : coordinateSwap v + z =
          coordinateSwap a + coordinateSwap b := by
        simpa only [map_add, coordinateSwap_apply_apply] using
          (congrArg coordinateSwap hab).symm
      refine ⟨coordinateSwap a, ?_, coordinateSwap b, ?_, ?_⟩
      · have haa : coordinateSwap a = a₀ := by
          rw [← haa₀, coordinateSwap_apply_apply]
        exact haa ▸ ha₀
      · have hbb : coordinateSwap b = b₀ := by
          rw [← hbb₀, coordinateSwap_apply_apply]
        exact hbb ▸ hb₀
      · exact hxeq.symm

private theorem regularSupport_nonempty_of_centres_local
    (K : Region) {Q : Set Tiling.Plane} (hQ : Q.Nonempty) :
    (regularSupport K Q).Nonempty := by
  have hOpenCarrier : K.openCarrier.Nonempty :=
    K.isPolygonal.interior_nonempty K.nonempty
  obtain ⟨q, hq⟩ := hQ
  obtain ⟨k, hk⟩ := hOpenCarrier
  refine ⟨q + k, ?_⟩
  change q + k ∈ interior (closure (openUnion K Q))
  have hopen : IsOpen (openUnion K Q) := by
    exact isOpen_iUnion fun s ↦
      (Region.openCarrier_regularOpen K).1.vadd (s : Tiling.Plane)
  apply interior_maximal subset_closure hopen
  rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
  exact ⟨⟨q, hq⟩, k, hk, rfl⟩

private theorem terminalRegion_properVertex_of_properSubfamily
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    {S : Set Tiling.Plane}
    (hSne : S.Nonempty) (hS : S ⊆ R.selectedCentres)
    (hSneq : S ≠ R.selectedCentres) :
    (properVertices (regularSupport R.selectedRegion S)).Nonempty := by
  have hpack : Tiling.IsPacking R.selectedRegion.toPolygonalRegion.prototileFamily
      (R.selectedRegion.toPolygonalRegion.placements S) := by
    intro s hs t ht hst
    exact R.tiles.2.1 (hS hs) (hS ht) hst
  have hregular := regularSupport_isRegularOpen R.selectedRegion S
  have hcross : ∀ x, ∃ r > 0, ∀ z ∈ Metric.ball x r,
      z ∈ frontier (regularSupport R.selectedRegion S) →
        z.re = x.re ∨ z.im = x.im :=
    fun x ↦ regularSupport_localBoundaryCross hpack x
  by_contra hnone
  have hvertices : properVertices (regularSupport R.selectedRegion S) = ∅ := by
    exact Set.not_nonempty_iff_eq_empty.mp hnone
  have hclass := noProperVertexSupport_isAxisSlab_of_localBoundaryCross
      hregular.1 hregular.2 hcross hvertices
  rcases hclass with hVertical | hHorizontal
  · obtain ⟨Y, hYopen, hYregular, hDY⟩ := hVertical
    have hEq := R.propagationIrreducible.vertical S hSne hS
      ⟨Y, hYregular.symm, hDY⟩
    exact hSneq hEq
  · obtain ⟨Y, hYopen, hYregular, hDY⟩ := hHorizontal
    have hopenSub : openUnion R.selectedRegion S ⊆
        openUnion R.selectedRegion R.selectedCentres := by
      intro z hz
      rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz ⊢
      obtain ⟨s, hs⟩ := hz
      exact ⟨⟨s, hS s.2⟩, hs⟩
    have hDsub : regularSupport R.selectedRegion S ⊆
        regularSupport R.selectedRegion R.selectedCentres := by
      change interior (closure (openUnion R.selectedRegion S)) ⊆
        interior (closure (openUnion R.selectedRegion R.selectedCentres))
      exact interior_mono (closure_mono hopenSub)
    have hDnonempty : (regularSupport R.selectedRegion S).Nonempty :=
      regularSupport_nonempty_of_centres_local R.selectedRegion hSne
    obtain ⟨z, hz⟩ := hDnonempty
    have hzY : z.im ∈ Y := by simpa [hDY] using hz
    have hbase : R.base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro a
      let w : Tiling.Plane := (a : ℂ) + z.im * Complex.I
      have hwY : w.im ∈ Y := by
        dsimp [w]
        simpa using hzY
      have hwD : w ∈ regularSupport R.selectedRegion S := by
        rw [hDY]
        exact hwY
      have hwFull := hDsub hwD
      rw [R.support_eq] at hwFull
      simpa [w] using hwFull
    have hEq := R.propagationIrreducible.horizontal_of_full hbase S hSne hS
      ⟨Y, hYregular.symm, hDY⟩
    exact hSneq hEq


/-!
## Atom displacement synchronization

The neutral quadrant geometry is imported from Foundations. Finite atom activity,
regularization, individual attribution, and indexed injectivity remain private consumers.
-/

open Tiling AxisParallel Foundations
open Filter _root_.Topology

local instance (p : Prop) : Decidable p := Classical.propDecidable p

private theorem finite_pos_min_active {J : Type*} [Finite J] [Nonempty J]
    (r : J → ℝ) (hr : ∀ j, 0 < r j) :
    ∃ ρ > 0, ∀ j, ρ ≤ r j := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let j₀ : J := Classical.choice inferInstance
  let ρ := (Finset.univ : Finset J).inf' ⟨j₀, Finset.mem_univ _⟩ r
  refine ⟨ρ, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff (Finset.univ_nonempty)).2 (fun j _ => hr j)
  · intro j
    exact Finset.inf'_le _ (Finset.mem_univ _)

/-- Only finitely many atom supports can meet a sufficiently small ball about `w`. -/
private theorem finite_active_atom_labels
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    {I : Type} (atom : I → Set Tiling.Plane)
    (hparts : Set.PairwiseDisjoint Set.univ atom)
    (hunion : (⋃ i, atom i) = R.selectedCentres)
    (w : Tiling.Plane) :
    ∃ active : Set I, ∃ r : ℝ,
      active.Finite ∧ 0 < r ∧
      (∀ i, i ∉ active →
        Disjoint (Metric.ball w r)
          (regularSupport R.selectedRegion (atom i))) := by
  classical
  have hatom_subset (i : I) : atom i ⊆ R.selectedCentres := by
    rw [← hunion]
    exact subset_iUnion atom i
  have hcover (s : R.selectedCentres) : ∃ i, (s : Tiling.Plane) ∈ atom i := by
    have hs : (s : Tiling.Plane) ∈ ⋃ i, atom i := by
      rw [hunion]
      exact s.2
    exact Set.mem_iUnion.mp hs
  choose label hlabel using hcover
  have hlabel_unique {s : R.selectedCentres} {i : I}
      (hi : (s : Tiling.Plane) ∈ atom i) : label s = i := by
    by_contra hne
    exact Set.disjoint_left.mp
      (hparts (Set.mem_univ _) (Set.mem_univ _) hne)
      (hlabel s) hi
  have hpack : Tiling.IsPacking
      R.selectedRegion.toPolygonalRegion.prototileFamily
      (R.selectedRegion.toPolygonalRegion.placements R.selectedCentres) :=
    R.tiles.2.1
  let P := R.selectedRegion.polygonalProtoTiling R.selectedCentres
  let toPlacement : R.selectedCentres → P.placements :=
    fun s => ⟨(s, ()), s.2⟩
  have htoPlacement : Function.Injective toPlacement := by
    intro s t hst
    exact Subtype.ext (congrArg (fun i : P.placements ↦ i.1.1) hst)
  have hlocal : LocallyFinite
      (fun s : R.selectedCentres ↦
        (s : Tiling.Plane) +ᵥ R.selectedRegion.support) := by
    exact (P.locallyFinite_placedTile hpack).comp_injective htoPlacement
  have hclosed : ∀ s : R.selectedCentres, IsClosed
      ((s : Tiling.Plane) +ᵥ R.selectedRegion.support) := by
    intro s
    have hsupport :
        (R.selectedRegion.toPolygonalRegion.prototileFamily ()).support =
          R.selectedRegion.support := rfl
    rw [← hsupport]
    change IsClosed (Tiling.placedTile P.prototiles ((toPlacement s).1))
    exact P.isClosed_placedTile ((toPlacement s).1)
  let J : Set R.selectedCentres := {s |
    w ∈ (s : Tiling.Plane) +ᵥ R.selectedRegion.support}
  have hJ : J.Finite := by
    simpa [J] using hlocal.point_finite w
  have hincident : ∀ᶠ z in 𝓝 w, ∀ s : R.selectedCentres,
      z ∈ (s : Tiling.Plane) +ᵥ R.selectedRegion.support → s ∈ J :=
    hlocal.eventually_subset hclosed w
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hincident
  let active : Set I := label '' J
  have hactive : active.Finite := hJ.image label
  have hpack_atom (i : I) : Tiling.IsPacking
      R.selectedRegion.toPolygonalRegion.prototileFamily
      (R.selectedRegion.toPolygonalRegion.placements (atom i)) := by
    intro p hp q hq hpq
    exact hpack (hatom_subset i hp) (hatom_subset i hq) hpq
  have hmiss (i : I) (hi : i ∉ active) :
      Disjoint (Metric.ball w r)
        (regularSupport R.selectedRegion (atom i)) := by
    rw [Set.disjoint_left]
    intro z hzball hzi
    have hzclosure : z ∈ closure (openUnion R.selectedRegion (atom i)) :=
      interior_subset hzi
    rw [closure_openUnion_eq_iUnion_support (hpack_atom i)] at hzclosure
    obtain ⟨s, hzs⟩ := Set.mem_iUnion.mp hzclosure
    let sc : R.selectedCentres := ⟨(s : Tiling.Plane), hatom_subset i s.2⟩
    have hsc_support : z ∈
        (sc : Tiling.Plane) +ᵥ R.selectedRegion.support := by
      simpa [sc] using hzs
    have hscJ : sc ∈ J := hball hzball sc hsc_support
    have hsc_active : label sc ∈ active := ⟨sc, hscJ, rfl⟩
    have hlabel_eq : label sc = i := hlabel_unique s.2
    exact hi (hlabel_eq ▸ hsc_active)
  exact ⟨active, r, hactive, hr, hmiss⟩

/-- Active labels carry individual regular-support quadrant germs on one common ball. -/
private theorem finite_active_atom_germs
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    {I : Type} (atom : I → Set Tiling.Plane)
    (hparts : Set.PairwiseDisjoint Set.univ atom)
    (hunion : (⋃ i, atom i) = R.selectedCentres)
    (w : Tiling.Plane) :
    ∃ r : ℝ, 0 < r ∧ ∃ p : I → QuadrantPattern,
      ∀ i,
        QuadrantGermOccupancy
          (regularSupport R.selectedRegion (atom i)) w r (p i) := by
  classical
  obtain ⟨active, r₀, hactive, hr₀, hmiss⟩ :=
    finite_active_atom_labels R atom hparts hunion w
  have hpack_atom (i : I) : Tiling.IsPacking
      R.selectedRegion.toPolygonalRegion.prototileFamily
      (R.selectedRegion.toPolygonalRegion.placements (atom i)) := by
    have hpack : Tiling.IsPacking
        R.selectedRegion.toPolygonalRegion.prototileFamily
        (R.selectedRegion.toPolygonalRegion.placements R.selectedCentres) :=
      R.tiles.2.1
    intro a ha b hb hab
    exact hpack (by rw [← hunion]; exact subset_iUnion atom i ha)
      (by rw [← hunion]; exact subset_iUnion atom i hb) hab
  have hlocal (i : I) : ∃ ρ > 0, ∃ pi : QuadrantPattern,
      QuadrantGermOccupancy
        (regularSupport R.selectedRegion (atom i)) w ρ pi := by
    obtain ⟨ρ, hρ, pi, hg, _⟩ := exists_quadrantPattern_germ_of_localBoundaryCross
      (regularSupport_isRegularOpen R.selectedRegion (atom i)).1
      (regularSupport_isRegularOpen R.selectedRegion (atom i)).2
      w (regularSupport_localBoundaryCross (hpack_atom i) w)
    exact ⟨ρ, hρ, pi, hg⟩
  let pattern : I → QuadrantPattern := fun i => (hlocal i).choose_spec.2.choose
  let ρ : I → ℝ := fun i => (hlocal i).choose
  have hρ : ∀ i, 0 < ρ i := fun i => (hlocal i).choose_spec.1
  let : Fintype active := hactive.fintype
  by_cases hne : active.Nonempty
  · have : Nonempty active := ⟨⟨Classical.choose hne, hne.choose_spec⟩⟩
    obtain ⟨r', hr', hmin⟩ := finite_pos_min_active (fun i : active => ρ i.1)
      (fun i => hρ i.1)
    let radius := min r₀ r'
    let p : I → QuadrantPattern := fun i =>
      if hi : i ∈ active then pattern i else fun _ => false
    refine ⟨radius, lt_min hr₀ hr', p, ?_⟩
    intro i
    by_cases hi : i ∈ active
    · intro q z hzball hzq
      simpa [p, hi] using (hlocal i).choose_spec.2.choose_spec q z
        (Metric.ball_subset_ball
          ((min_le_right r₀ r').trans (hmin ⟨i, hi⟩)) hzball) hzq
    · intro q z hzball hzq
      have hnot : z ∉ regularSupport R.selectedRegion (atom i) := by
        intro hzi
        exact Set.disjoint_left.mp (hmiss i hi)
          (Metric.ball_subset_ball (min_le_left r₀ r') hzball) hzi
      have hp : p i q = false := by simp [p, hi]
      rw [hp]
      simp [hnot]
  · let p : I → QuadrantPattern := fun i => fun _ => false
    refine ⟨r₀, hr₀, p, ?_⟩
    intro i q z hzball hzq
    have hi : i ∉ active := fun hm => hne ⟨i, hm⟩
    have hnot : z ∉ regularSupport R.selectedRegion (atom i) :=
      fun hzi => Set.disjoint_left.mp (hmiss i hi) hzball hzi
    simp [p, hnot]

/-- The regularization of any locally germ-constant union has the OR quadrant pattern. -/
private theorem atom_patterns_pairwise_exclusive
    {I : Type} {A : I → Set Tiling.Plane} {w : Tiling.Plane} {r : ℝ}
    {p : I → QuadrantPattern}
    (hr : 0 < r)
    (hcommon : ∀ i, QuadrantGermOccupancy (A i) w r (p i))
    (hdisjoint : Set.PairwiseDisjoint Set.univ A) :
    ∀ i j, i ≠ j → ∀ q, ¬(p i q = true ∧ p j q = true) := by
  intro i j hij q hboth
  obtain ⟨z, hzball, hzq⟩ := quadrant_ball_nonempty hr q
  have hzi : z ∈ A i := (hcommon i q z hzball hzq).mpr hboth.1
  have hzj : z ∈ A j := (hcommon j q z hzball hzq).mpr hboth.2
  exact Set.disjoint_left.mp
    (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij) hzi hzj

private theorem finite_active_regularization_union_germ
    {J : Type*}
    {A : J → Set Tiling.Plane} {w : Tiling.Plane} {r : ℝ}
    {p : J → QuadrantPattern}
    (hr : 0 < r)
    (hcommon : ∀ j, QuadrantGermOccupancy (A j) w r (p j)) :
    QuadrantGermOccupancy
      (interior (closure (⋃ j, A j))) w (r / 2)
      (fun q => if ∃ j, p j q = true then true else false) := by
  classical
  intro q z hzball hzq
  have hzorig : z ∈ Metric.ball w r :=
    Metric.ball_subset_ball (by linarith) hzball
  have hzQ : z ∈ Metric.ball w r ∩ quadrantAt q w := ⟨hzorig, hzq⟩
  obtain ⟨ε, hε, hεsub⟩ :=
    (Metric.isOpen_iff.mp (Metric.isOpen_ball.inter (by
      cases q <;> first
        | exact (isOpen_lt Complex.continuous_re continuous_const).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        | exact (isOpen_lt continuous_const Complex.continuous_re).inter
            (isOpen_lt Complex.continuous_im continuous_const)
        | exact (isOpen_lt Complex.continuous_re continuous_const).inter
            (isOpen_lt continuous_const Complex.continuous_im)
        | exact (isOpen_lt continuous_const Complex.continuous_re).inter
            (isOpen_lt continuous_const Complex.continuous_im)))) z hzQ
  by_cases hq : ∃ j, p j q = true
  · change z ∈ interior (closure (⋃ j, A j)) ↔
      (if ∃ j, p j q = true then true else false) = true
    rw [if_pos hq]
    constructor
    · intro _; trivial
    · intro _
      obtain ⟨j, hpj⟩ := hq
      have hballClosure : Metric.ball z ε ⊆ closure (⋃ j, A j) := by
        intro y hy
        apply subset_closure
        exact Set.mem_iUnion.mpr ⟨j,
          (hcommon j q y (hεsub hy).1 (hεsub hy).2).mpr hpj⟩
      exact (interior_maximal hballClosure Metric.isOpen_ball)
        (Metric.mem_ball_self hε)
  · change z ∈ interior (closure (⋃ j, A j)) ↔
      (if ∃ j, p j q = true then true else false) = true
    rw [if_neg hq]
    have hdisj : Disjoint (Metric.ball z ε) (⋃ j, A j) := by
      apply Set.disjoint_left.2
      intro y hyball hyU
      obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyU
      have hpj : p j q ≠ true := fun hpj => hq ⟨j, hpj⟩
      exact hpj ((hcommon j q y (hεsub hyball).1 (hεsub hyball).2).mp hyj)
    have hznot : z ∉ closure (⋃ j, A j) := by
      intro hzcl
      obtain ⟨y, hyU, hydist⟩ := Metric.mem_closure_iff.mp hzcl ε hε
      have hyball : y ∈ Metric.ball z ε := by
        rw [Metric.mem_ball, dist_comm]
        exact hydist
      exact Set.disjoint_left.mp hdisj hyball hyU
    constructor
    · intro hzD
      exact False.elim (hznot (interior_subset hzD))
    · intro hfalse
      cases hfalse

private theorem properVertex_translate_germ
    {D : Set Tiling.Plane} {w u : Tiling.Plane} {r : ℝ}
    {p : QuadrantPattern} (hr : 0 < r)
    (hg : QuadrantGermOccupancy D w r p) (hp : nonstraightPattern p) :
    IsProperVertex (u +ᵥ D) (w + u) := by
  apply properVertex_of_nonstraightPattern hr p _ hp
  intro q z hz hq
  have hz' : z - u ∈ Metric.ball w r := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_sub, add_comm, add_left_comm,
      add_assoc] using hz
  have hq' : z - u ∈ quadrantAt q w := by
    cases q <;> dsimp [quadrantAt] at hq ⊢ <;>
      constructor <;> linarith [hq.1, hq.2]
  rw [show z ∈ u +ᵥ D ↔ z - u ∈ D by
    rw [mem_vadd_set_iff_neg_vadd_mem]
    simp [vadd_eq_add, sub_eq_add_neg, add_comm]]
  exact hg q (z - u) hz' hq'

private theorem carrier_germ_column_comparisons
    {B : Set ℝ} {w : Tiling.Plane} {r : ℝ} {p : QuadrantPattern}
    (hr : 0 < r) (hg : QuadrantGermOccupancy (Complex.re ⁻¹' B) w r p) :
    p .southwest = p .northwest ∧ p .southeast = p .northeast := by
  let d : ℝ := r / 4
  have hd : 0 < d := by dsimp [d]; linarith
  have hball (s t : ℝ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) :
      w + s * (d : ℂ) + t * (d : ℂ) * Complex.I ∈ Metric.ball w r := by
    rw [Metric.mem_ball, dist_eq_norm, Complex.norm_def, Real.sqrt_lt' hr]
    have heq : w + s * (d : ℂ) + t * (d : ℂ) * Complex.I - w =
        s * (d : ℂ) + t * (d : ℂ) * Complex.I := by ring
    rw [heq]
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;>
      norm_num [Complex.normSq_apply] <;> dsimp [d] <;> nlinarith
  have hsw := hg .southwest (w + (-1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I)
    (hball (-1) (-1) (Or.inr rfl) (Or.inr rfl))
    (by constructor <;> simp [hd])
  have hnw := hg .northwest (w + (-1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I)
    (hball (-1) 1 (Or.inr rfl) (Or.inl rfl))
    (by constructor <;> simp [hd])
  have hse := hg .southeast (w + (1 : ℝ) * (d : ℂ) + (-1 : ℝ) * (d : ℂ) * Complex.I)
    (hball 1 (-1) (Or.inl rfl) (Or.inr rfl))
    (by constructor <;> simp [hd])
  have hne := hg .northeast (w + (1 : ℝ) * (d : ℂ) + (1 : ℝ) * (d : ℂ) * Complex.I)
    (hball 1 1 (Or.inl rfl) (Or.inl rfl))
    (by constructor <;> simp [hd])
  simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul, mem_preimage,
    Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero, add_zero]
    at hsw hnw hse hne
  have hleft : (p .southwest = true ↔ p .northwest = true) := by
    exact hsw.symm.trans hnw
  have hright : (p .southeast = true ↔ p .northeast = true) := by
    exact hse.symm.trans hne
  constructor
  · exact Bool.eq_iff_iff.mpr hleft
  · exact Bool.eq_iff_iff.mpr hright

private def selectedOr {I : Type*} (p : I → QuadrantPattern)
    (G : I → Prop) : QuadrantPattern :=
  fun q => if ∃ i, G i ∧ p i q = true then true else false

private theorem selectedOr_true_iff {I : Type*} (p : I → QuadrantPattern)
    (G : I → Prop) (q : Quadrant) :
    selectedOr p G q = true ↔ ∃ i, G i ∧ p i q = true := by
  simp [selectedOr]

private theorem selectedOr_false_iff {I : Type*} (p : I → QuadrantPattern)
    (G : I → Prop) (q : Quadrant) :
    selectedOr p G q = false ↔ ¬ ∃ i, G i ∧ p i q = true := by
  simp [selectedOr]

/-- Under coverage and pairwise exclusivity, the OR of the unselected labels is the
carrier with the selected OR removed. -/
private theorem complementaryOr_true_iff {I : Type*}
    (p : I → QuadrantPattern) (G : I → Prop)
    (carrier : QuadrantPattern)
    (hexclusive : ∀ i j, i ≠ j → ∀ q,
      ¬ (p i q = true ∧ p j q = true))
    (hcover : ∀ q, carrier q = true ↔ ∃ i, p i q = true)
    (q : Quadrant) :
    selectedOr p (fun i => ¬ G i) q = true ↔
      carrier q = true ∧ selectedOr p G q = false := by
  rw [selectedOr_true_iff]
  constructor
  · rintro ⟨i, hnotG, hqi⟩
    constructor
    · rw [hcover]
      exact ⟨i, hqi⟩
    · rw [selectedOr_false_iff]
      intro hselected
      obtain ⟨j, hjG, hqj⟩ := hselected
      by_cases hij : i = j
      · exact hnotG (hij ▸ hjG)
      · exact hexclusive i j hij q ⟨hqi, hqj⟩
  · rintro ⟨hcarrier, hnotselected⟩
    obtain ⟨i, hqi⟩ := (hcover q).mp hcarrier
    have hnotG : ¬ G i := by
      intro hiG
      apply (selectedOr_false_iff p G q).mp hnotselected
      exact ⟨i, hiG, hqi⟩
    exact ⟨i, hnotG, hqi⟩

private theorem selectedOr_rowConstant_of_rowAnchor {I : Type*}
    (p : I → QuadrantPattern) (G : I → Prop) (i : I)
    (_hi : G i)
    (hrow : p i .southwest = p i .southeast ∧
      p i .northwest = p i .northeast)
    (hrowOccupied : (p i .southwest = true ∧ p i .southeast = true) ∨
      (p i .northwest = true ∧ p i .northeast = true))
    (hstraight : ∀ j, G j → straightPattern (p j))
    (hexclusive : ∀ j k, j ≠ k → ∀ q,
      ¬ (p j q = true ∧ p k q = true)) :
    selectedOr p G .southwest = selectedOr p G .southeast ∧
      selectedOr p G .northwest = selectedOr p G .northeast := by
  have hrows : ∀ j, G j →
      (p j .southwest = p j .southeast ∧
        p j .northwest = p j .northeast) := by
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hrow
    · rcases hrowOccupied with hlow | hhigh
      · have hswFalse : p j .southwest = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .southwest ⟨hlow.1, hp⟩
        have hseFalse : p j .southeast = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .southeast ⟨hlow.2, hp⟩
        rcases hstraight j hj with ⟨hrowj, htopj⟩ | ⟨hcolj, hcolj'⟩
        · exact ⟨hrowj, htopj⟩
        · have hnwFalse : p j .northwest = false := by rw [← hcolj, hswFalse]
          have hneFalse : p j .northeast = false := by rw [← hcolj', hseFalse]
          exact ⟨by rw [hswFalse, hseFalse], by rw [hnwFalse, hneFalse]⟩
      · have hnwFalse : p j .northwest = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .northwest ⟨hhigh.1, hp⟩
        have hneFalse : p j .northeast = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .northeast ⟨hhigh.2, hp⟩
        rcases hstraight j hj with ⟨hrowj, htopj⟩ | ⟨hcolj, hcolj'⟩
        · exact ⟨hrowj, htopj⟩
        · have hswFalse : p j .southwest = false := by rw [hcolj, hnwFalse]
          have hseFalse : p j .southeast = false := by rw [hcolj', hneFalse]
          exact ⟨by rw [hswFalse, hseFalse], by rw [hnwFalse, hneFalse]⟩
  have hbottom : selectedOr p G .southwest = selectedOr p G .southeast := by
    apply Bool.eq_iff_iff.mpr
    rw [selectedOr_true_iff, selectedOr_true_iff]
    constructor
    · rintro ⟨j, hj, hjsw⟩
      exact ⟨j, hj, (hrows j hj).1 ▸ hjsw⟩
    · rintro ⟨j, hj, hjse⟩
      exact ⟨j, hj, (hrows j hj).1.symm ▸ hjse⟩
  have htop : selectedOr p G .northwest = selectedOr p G .northeast := by
    apply Bool.eq_iff_iff.mpr
    rw [selectedOr_true_iff, selectedOr_true_iff]
    constructor
    · rintro ⟨j, hj, hjnw⟩
      exact ⟨j, hj, (hrows j hj).2 ▸ hjnw⟩
    · rintro ⟨j, hj, hjne⟩
      exact ⟨j, hj, (hrows j hj).2.symm ▸ hjne⟩
  exact ⟨hbottom, htop⟩

private theorem selectedOr_columnConstant_of_columnAnchor {I : Type*}
    (p : I → QuadrantPattern) (G : I → Prop) (i : I)
    (_hi : G i)
    (hcol : p i .southwest = p i .northwest ∧
      p i .southeast = p i .northeast)
    (hcolOccupied : (p i .southwest = true ∧ p i .northwest = true) ∨
      (p i .southeast = true ∧ p i .northeast = true))
    (hstraight : ∀ j, G j → straightPattern (p j))
    (hexclusive : ∀ j k, j ≠ k → ∀ q,
      ¬ (p j q = true ∧ p k q = true)) :
    selectedOr p G .southwest = selectedOr p G .northwest ∧
      selectedOr p G .southeast = selectedOr p G .northeast := by
  have hcols : ∀ j, G j →
      (p j .southwest = p j .northwest ∧
        p j .southeast = p j .northeast) := by
    intro j hj
    by_cases hji : j = i
    · subst j
      exact hcol
    · rcases hcolOccupied with hleft | hright
      · have hswFalse : p j .southwest = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .southwest ⟨hleft.1, hp⟩
        have hnwFalse : p j .northwest = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .northwest ⟨hleft.2, hp⟩
        rcases hstraight j hj with ⟨hrowj, hrowj'⟩ | ⟨hcolj, hcolj'⟩
        · have hseFalse : p j .southeast = false := by rw [← hrowj, hswFalse]
          have hneFalse : p j .northeast = false := by rw [← hrowj', hnwFalse]
          exact ⟨by rw [hswFalse, hnwFalse], by rw [hseFalse, hneFalse]⟩
        · exact ⟨hcolj, hcolj'⟩
      · have hseFalse : p j .southeast = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .southeast ⟨hright.1, hp⟩
        have hneFalse : p j .northeast = false := by
          apply Bool.eq_false_of_not_eq_true
          intro hp
          exact hexclusive i j (Ne.symm hji) .northeast ⟨hright.2, hp⟩
        rcases hstraight j hj with ⟨hrowj, hrowj'⟩ | ⟨hcolj, hcolj'⟩
        · have hswFalse : p j .southwest = false := by rw [hrowj, hseFalse]
          have hnwFalse : p j .northwest = false := by rw [hrowj', hneFalse]
          exact ⟨by rw [hswFalse, hnwFalse], by rw [hseFalse, hneFalse]⟩
        · exact ⟨hcolj, hcolj'⟩
  have hleft : selectedOr p G .southwest = selectedOr p G .northwest := by
    apply Bool.eq_iff_iff.mpr
    rw [selectedOr_true_iff, selectedOr_true_iff]
    constructor
    · rintro ⟨j, hj, hjsw⟩
      exact ⟨j, hj, (hcols j hj).1 ▸ hjsw⟩
    · rintro ⟨j, hj, hjnw⟩
      exact ⟨j, hj, (hcols j hj).1.symm ▸ hjnw⟩
  have hright : selectedOr p G .southeast = selectedOr p G .northeast := by
    apply Bool.eq_iff_iff.mpr
    rw [selectedOr_true_iff, selectedOr_true_iff]
    constructor
    · rintro ⟨j, hj, hjse⟩
      exact ⟨j, hj, (hcols j hj).2 ▸ hjse⟩
    · rintro ⟨j, hj, hjne⟩
      exact ⟨j, hj, (hcols j hj).2.symm ▸ hjne⟩
  exact ⟨hleft, hright⟩

private theorem nonstraightLabel_of_nonstraightOr {I : Type*}
    (p : I → QuadrantPattern) (G : I → Prop)
    (hexclusive : ∀ i j, i ≠ j → ∀ q,
      ¬ (p i q = true ∧ p j q = true))
    (hselected : nonstraightPattern (selectedOr p G)) :
    ∃ i, G i ∧ nonstraightPattern (p i) := by
  by_contra hnone
  have hstraight : ∀ i, G i → straightPattern (p i) := by
    intro i hi
    by_contra hnot
    exact hnone ⟨i, hi, hnot⟩
  have hoccupied : ∃ q, selectedOr p G q = true := by
    by_contra hno
    have hsw : selectedOr p G .southwest = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hno ⟨.southwest, htrue⟩
    have hse : selectedOr p G .southeast = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hno ⟨.southeast, htrue⟩
    have hnw : selectedOr p G .northwest = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hno ⟨.northwest, htrue⟩
    have hne : selectedOr p G .northeast = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hno ⟨.northeast, htrue⟩
    apply hselected
    exact Or.inl ⟨by rw [hsw, hse], by rw [hnw, hne]⟩
  obtain ⟨q, hq⟩ := hoccupied
  obtain ⟨i, hi, hpiq⟩ := (selectedOr_true_iff p G q).mp hq
  have hpiStraight := hstraight i hi
  rcases hpiStraight with hrow | hcol
  · have hrowOccupied :
        (p i .southwest = true ∧ p i .southeast = true) ∨
        (p i .northwest = true ∧ p i .northeast = true) := by
      cases q <;> simp_all [straightPattern]
    have hunionRow := selectedOr_rowConstant_of_rowAnchor
      p G i hi hrow hrowOccupied hstraight hexclusive
    apply hselected
    exact Or.inl hunionRow
  · have hcolOccupied :
        (p i .southwest = true ∧ p i .northwest = true) ∨
        (p i .southeast = true ∧ p i .northeast = true) := by
      cases q <;> simp_all [straightPattern]
    have hunionCol := selectedOr_columnConstant_of_columnAnchor
      p G i hi hcol hcolOccupied hstraight hexclusive
    apply hselected
    exact Or.inr hunionCol

private theorem nonstraight_columnComplement {carrier selected : QuadrantPattern}
    (hcolumns : carrier .southwest = carrier .northwest ∧
      carrier .southeast = carrier .northeast)
    (hsubset : ∀ q, selected q = true → carrier q = true)
    (hselected : nonstraightPattern selected) :
    nonstraightPattern (fun q =>
      if carrier q = true ∧ selected q = false then true else false) := by
  rcases Bool.eq_false_or_eq_true (carrier .southwest) with hcsw | hcsw <;>
    rcases Bool.eq_false_or_eq_true (carrier .southeast) with hcse | hcse <;>
    rcases Bool.eq_false_or_eq_true (selected .southwest) with hssw | hssw <;>
    rcases Bool.eq_false_or_eq_true (selected .southeast) with hsse | hsse <;>
    rcases Bool.eq_false_or_eq_true (selected .northwest) with hsnw | hsnw <;>
    rcases Bool.eq_false_or_eq_true (selected .northeast) with hsne | hsne <;>
    simp_all [nonstraightPattern, straightPattern]

private theorem nonstraightComplementaryLabel_of_columnConstantCarrier {I : Type*}
    (p : I → QuadrantPattern) (G : I → Prop)
    (carrier : QuadrantPattern)
    (hexclusive : ∀ i j, i ≠ j → ∀ q,
      ¬ (p i q = true ∧ p j q = true))
    (hcover : ∀ q, carrier q = true ↔ ∃ i, p i q = true)
    (hcolumns : carrier .southwest = carrier .northwest ∧
      carrier .southeast = carrier .northeast)
    (hselected : nonstraightPattern (selectedOr p G)) :
    ∃ j, ¬ G j ∧ nonstraightPattern (p j) := by
  have hsubset : ∀ q, selectedOr p G q = true → carrier q = true := by
    intro q hq
    obtain ⟨i, hi, hqi⟩ := (selectedOr_true_iff p G q).mp hq
    exact (hcover q).2 ⟨i, hqi⟩
  have hcomplement := nonstraight_columnComplement hcolumns hsubset hselected
  have hpattern : selectedOr p (fun i => ¬ G i) =
      (fun q => if carrier q = true ∧ selectedOr p G q = false
        then true else false) := by
    funext q
    have hiff := complementaryOr_true_iff p G carrier hexclusive hcover q
    apply Bool.eq_iff_iff.mpr
    rw [hiff]
    by_cases hcond : carrier q = true ∧ selectedOr p G q = false <;>
      simp [hcond]
  rw [← hpattern] at hcomplement
  exact nonstraightLabel_of_nonstraightOr p (fun i => ¬ G i)
    hexclusive hcomplement

private theorem atomDisplacements_synchronize :
    ∀ {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
        {I : Type} (atom : I → Set Tiling.Plane),
      (∀ i, (atom i).Nonempty) →
      Set.PairwiseDisjoint Set.univ atom →
      (⋃ i, atom i) = R.selectedCentres →
      ∀ (next : Equiv.Perm I) (displacement : I → Tiling.Plane)
        (imagePoint : Tiling.Plane → Tiling.Plane) (eta : Tiling.Plane),
        (∀ i,
          displacement i +ᵥ regularSupport R.selectedRegion (atom i) =
            regularSupport R.selectedRegion (atom (next i))) →
        (∀ i x,
          x ∈ R.selectedRegion.vertices + atom i →
          x + displacement i ∈
            R.selectedRegion.vertices + atom (next i) →
          imagePoint (x + displacement i) = imagePoint x + eta) →
        Set.InjOn imagePoint
          (R.selectedRegion.vertices + R.selectedCentres) →
        ∃ d : Tiling.Plane, ∀ i, displacement i = d := by
  classical
  intro K T R I atom hatom hparts hunion next displacement imagePoint eta htranslate hmap hinj
  have hsub (i : I) : atom i ⊆ R.selectedCentres := by
    rw [← hunion]
    exact subset_iUnion atom i
  have hselected : R.selectedCentres.Nonempty := by
    cases haxis : R.orientation with
    | vertical => simpa [R.selectedCentres_vertical haxis] using R.centres_nonempty
    | horizontal =>
        rw [R.selectedCentres_horizontal haxis]
        exact R.centres_nonempty.image coordinateSwap
  obtain ⟨s, hs⟩ := hselected
  have hsunion : s ∈ ⋃ i, atom i := hunion.symm ▸ hs
  obtain ⟨i₀, _⟩ := Set.mem_iUnion.mp hsunion
  let centre : I → Tiling.Plane := fun i => (hatom i).choose
  have hcentre : ∀ i, centre i ∈ atom i := fun i => (hatom i).choose_spec
  let c : I → R.selectedCentres := fun i => ⟨centre i, hsub i (hcentre i)⟩
  have hc : Function.Injective c := by
    intro i j hij
    by_contra hne
    have heq : centre i = centre j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hparts (Set.mem_univ i) (Set.mem_univ j) hne)
      (hcentre i) (heq.symm ▸ hcentre j)
  have : Countable R.selectedCentres := R.tiles.1.to_subtype
  have : Countable I := hc.countable
  have hdisjoint : Set.PairwiseDisjoint Set.univ
      (fun i => regularSupport R.selectedRegion (atom i)) :=
    (regularSupport_pairwiseDisjoint atom hparts hunion R.tiles).1
  refine ⟨displacement i₀, ?_⟩
  intro k
  by_contra hk
  let G : Set I := {i | displacement i = displacement i₀}
  let S : Set Tiling.Plane := ⋃ i : G, atom i.1
  have hSsub : S ⊆ R.selectedCentres := Set.iUnion_subset fun i => hsub i.1
  have hSne : S.Nonempty :=
    (hatom i₀).mono (subset_iUnion (fun i : G => atom i.1) ⟨i₀, rfl⟩)
  have hSneq : S ≠ R.selectedCentres := by
    intro heq
    obtain ⟨x, hx⟩ := hatom k
    have hxS : x ∈ S := heq.symm ▸ hsub k hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxS
    have hki : k = i.1 := by
      by_contra hne
      exact Set.disjoint_left.mp (hparts (Set.mem_univ k) (Set.mem_univ i.1) hne) hx hxi
    exact hk (hki.symm ▸ i.2)
  obtain ⟨w, hw⟩ := terminalRegion_properVertex_of_properSubfamily R hSne hSsub hSneq
  obtain ⟨r, hr, p, hcommon⟩ := finite_active_atom_germs R atom hparts hunion w
  have hexclusive : ∀ i j, i ≠ j → ∀ q,
      ¬ (p i q = true ∧ p j q = true) :=
    atom_patterns_pairwise_exclusive hr hcommon hdisjoint
  have hGgerm : QuadrantGermOccupancy (regularSupport R.selectedRegion S) w (r / 2)
      (selectedOr p (fun i => i ∈ G)) := by
    rw [show S = ⋃ i : G, atom i.1 from rfl, regularSupport_iUnion]
    have hlocal := finite_active_regularization_union_germ hr (fun i : G => hcommon i.1)
    convert hlocal using 1
    funext q
    apply congrArg (fun t : Prop => if t then true else false)
    apply propext
    constructor
    · rintro ⟨i, hi, hpi⟩
      exact ⟨⟨i, hi⟩, hpi⟩
    · rintro ⟨i, hpi⟩
      exact ⟨i.1, i.2, hpi⟩
  have hcarrier : QuadrantGermOccupancy (Complex.re ⁻¹' R.base) w (r / 2)
      (fun q => if ∃ i, p i q = true then true else false) := by
    rw [← R.support_eq, ← hunion, regularSupport_iUnion]
    exact finite_active_regularization_union_germ hr hcommon
  have hnonstraight : nonstraightPattern (selectedOr p (fun i => i ∈ G)) :=
    (properVertex_iff_nonstraightPattern
      (regularSupport_isRegularOpen R.selectedRegion S).1
      (regularSupport_isRegularOpen R.selectedRegion S).2
      (by linarith : 0 < r / 2) _ hGgerm).mp hw
  have hcolumns := carrier_germ_column_comparisons (by linarith : 0 < r / 2) hcarrier
  obtain ⟨i, hiG, hpi⟩ := nonstraightLabel_of_nonstraightOr p (fun i => i ∈ G)
    hexclusive hnonstraight
  obtain ⟨j, hjG, hpj⟩ := nonstraightComplementaryLabel_of_columnConstantCarrier
    p (fun i => i ∈ G) (fun q => if ∃ i, p i q = true then true else false)
    hexclusive (by intro q; simp) hcolumns hnonstraight
  have hproper_i := properVertex_of_nonstraightPattern hr (p i) (hcommon i) hpi
  have hproper_j := properVertex_of_nonstraightPattern hr (p j) (hcommon j) hpj
  have htarget_i : IsProperVertex
      (regularSupport R.selectedRegion (atom (next i))) (w + displacement i) := by
    rw [← htranslate i]
    exact properVertex_translate_germ hr (hcommon i) hpi
  have htarget_j : IsProperVertex
      (regularSupport R.selectedRegion (atom (next j))) (w + displacement j) := by
    rw [← htranslate j]
    exact properVertex_translate_germ hr (hcommon j) hpj
  have hsource_i := properVertices_regularSupport_subset_vertices_add R.tiles (hsub i) hproper_i
  have hsource_j := properVertices_regularSupport_subset_vertices_add R.tiles (hsub j) hproper_j
  have htarget_mem_i := properVertices_regularSupport_subset_vertices_add R.tiles
    (hsub (next i)) htarget_i
  have htarget_mem_j := properVertices_regularSupport_subset_vertices_add R.tiles
    (hsub (next j)) htarget_j
  have hdecor (a : I) : R.selectedRegion.vertices + atom a ⊆
      R.selectedRegion.vertices + R.selectedCentres := add_subset_add Set.Subset.rfl (hsub a)
  have hpoints : w + displacement i = w + displacement j := by
    apply hinj (hdecor (next i) htarget_mem_i) (hdecor (next j) htarget_mem_j)
    rw [hmap i w hsource_i htarget_mem_i, hmap j w hsource_j htarget_mem_j]
  have hsame : displacement j = displacement i := (add_left_cancel hpoints).symm
  exact hjG (hsame.trans hiG)

private theorem nonColumnableVerticalNoGapOrbitTransport_of_imagePacking :
  ∀ {C : ApproximationContext.{0}} (_hFLC : HasFLC C.centres)
    (_hNoColumn : ¬ ∃ Col : Set Tiling.Plane,
      IsCenterColumn Axis.vertical C.region Col),
    ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
      ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ),
        IsEpsilonApproximation C P.threshold phi →
      ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) →
      ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
        (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
          RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
      (∀ i Q, Q ∈ (Dcmp.orbit i).phases → originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
      ∀ (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)),
      (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i)
          (60 * Metric.diam C.region.openCarrier)) →
      (Dcmp.direction i).toPlane.re = 0 →
      ∃ alpha : {z : Tiling.Plane // z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        (alpha : Tiling.Plane) ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
        (∀ m : ℤ, (alpha : Tiling.Plane) +ᵥ
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
        ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
            z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
          regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
            (beta : Tiling.Plane) +ᵥ regularSupport C.region (originalSlice i Q) ∧
          mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
          properVertices (regularSupport C.region
            (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C hFLC hNoColumn
  obtain ⟨recoveryScale, hRecovery, hAxis⟩ :=
    nonColumnableAxisLocalTransport hFLC Axis.vertical hNoColumn
  refine ⟨recoveryScale, hRecovery, ?_⟩
  intro P hScale phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice
    hOriginalSlice i Q hNoGap hVertical
  let phase : ℤ → Set ↥C.centres := fun m =>
    {t | Tphi t ∈ (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i)}
  have hPhase : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈ (Dcmp.orbit i).phases :=
    fun m ↦ (hNoGap m).1
  have hPhaseSlice (m : ℤ) :
      originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        Subtype.val '' phase m :=
    hOriginalSlice i _ (hPhase m)
  have hPhaseImage (m : ℤ) :
      Tphi '' phase m =
        (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      have hxT : x ∈ Set.range Tphi := by
        rw [← Dcmp.parts_union]
        exact Set.mem_iUnion.2 ⟨i, hx.1⟩
      obtain ⟨t, rfl⟩ := Set.mem_range.mp hxT
      exact ⟨t, hx, rfl⟩
  have hPreimageNonempty :
      ∀ q, q ∈ (Dcmp.orbit i).phases →
        ({t : ↥C.centres | Tphi t ∈ q.centres (Dcmp.part i)}).Nonempty := by
    intro q hq
    obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty q).mp hq
    have hxT : x ∈ Set.range Tphi := by
      rw [← Dcmp.parts_union]
      exact Set.mem_iUnion.2 ⟨i, hx.1⟩
    obtain ⟨t, ht⟩ := Set.mem_range.mp hxT
    refine ⟨t, ?_⟩
    change Tphi t ∈ q.centres (Dcmp.part i)
    simpa only [ht] using hx
  have hPhaseNonempty (m : ℤ) : (phase m).Nonempty :=
    hPreimageNonempty _ (hPhase m)
  have hSourcePacking (m : ℤ) : Tiling.IsPacking
      C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' phase m)) := by
    apply (isPacking_iff_openCarrier_disjoint C.region _).2
    intro x hx y hy hxy
    have hsub : Subtype.val '' phase m ⊆ C.centres := by
      rintro z ⟨t, _ht, rfl⟩
      exact t.2
    exact (isPacking_iff_openCarrier_disjoint C.region C.centres).1
      P.source_tilesOn.2.1 (hsub hx) (hsub hy) hxy
  have hTargetPacking (m : ℤ) : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Tphi '' phase m)) := by
    apply (isPacking_iff_openCarrier_disjoint D.deformedRegion _).2
    intro x hx y hy hxy
    have hsub : Tphi '' phase m ⊆ Set.range Tphi := by
      rintro z ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
    exact (isPacking_iff_openCarrier_disjoint D.deformedRegion (Set.range Tphi)).1
      hImagePacking (hsub hx) (hsub hy) hxy
  have hPhaseAligned (m : ℤ) : ∃ c : ℝ, ∀ t : phase m,
      Axis.vertical.transverseCoord (Tphi t.1) = c := by
    obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty _).mp (hPhase m)
    refine ⟨x.re, ?_⟩
    intro t
    change (Tphi t.1).re = x.re
    have htQ : QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
        (Tphi t.1) = Q.vadd (m • Dcmp.gamma.toPlane) := t.2.2
    have hxQ : QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
        x = Q.vadd (m • Dcmp.gamma.toPlane) := hx.2
    have hdiff : Tphi t.1 - x ∈ realDirectionSubgroup (Dcmp.direction i) :=
      QuotientAddGroup.eq_iff_sub_mem.mp (htQ.trans hxQ.symm)
    obtain ⟨r, hr⟩ := hdiff
    have hre : (Tphi t.1 - x).re = 0 := by
      rw [hr]
      simp only [Complex.smul_re, hVertical, smul_zero]
    have hsub : (Tphi t.1).re - x.re = 0 := by
      simpa only [Complex.sub_re] using hre
    exact sub_eq_zero.mp hsub
  have hImagePeriod (m : ℤ) :
      (Dcmp.direction i).toPlane +ᵥ Tphi '' phase m = Tphi '' phase m := by
    rw [hPhaseImage m]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic _ (hPhase m))
  have hImageSupport (m : ℤ) :
      regularSupport D.deformedRegion (Tphi '' phase m) =
        (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion (Tphi '' phase 0) := by
    rw [hPhaseImage m, hPhaseImage 0]
    have hQphase : Q ∈ (Dcmp.orbit i).phases := by
      simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hPhase 0
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using
      ((Dcmp.orbit i).regularSupport_transport Q hQphase m).symm
  let G : ℝ := 60 * Metric.diam C.region.openCarrier
  have hOriginalNonempty : ∀ q, q ∈ (Dcmp.orbit i).phases →
      (originalSlice i q).Nonempty := by
    intro q hq
    rw [hOriginalSlice i q hq]
    exact (hPreimageNonempty q hq).image Subtype.val
  have hLinked (m : ℤ) : Linked G (Subtype.val '' phase m) := by
    rw [← hPhaseSlice m]
    exact (Dcmp.orbit i).linked_originalSlice_of_mem_noGapPhases
      (originalSlice i) hOriginalNonempty (hNoGap m)
  let imagePeriod : Tiling.Plane := (Dcmp.direction i).toPlane
  have hImagePeriodNe : imagePeriod ≠ 0 := by
    intro hz
    apply (Dcmp.direction i).property
    funext j
    fin_cases j
    · have hzero : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.re hz
      change (Dcmp.direction i).coordinates 0 = 0
      exact_mod_cast hzero
    · have hzero : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.im hz
      change (Dcmp.direction i).coordinates 1 = 0
      exact_mod_cast hzero
  have hImagePeriodAxis : Axis.vertical.transverseCoord imagePeriod = 0 := by
    simpa only [imagePeriod, Axis.transverseCoord, Axis.coord] using hVertical
  have hSliceZero : originalSlice i Q = Subtype.val '' phase 0 := by
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hPhaseSlice 0
  have hOrbitTransport : ∀ m : ℤ,
      ∃ beta alpha : ControlledDisplacement C,
        regularSupport C.region (Subtype.val '' phase m) =
          (beta : Tiling.Plane) +ᵥ
            regularSupport C.region (Subtype.val '' phase 0) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        (alpha : Tiling.Plane) ≠ 0 ∧
        (alpha : Tiling.Plane) +ᵥ Subtype.val '' phase m = Subtype.val '' phase m ∧
        mapPoint phi alpha = imagePeriod ∧
        properVertices (regularSupport C.region (Subtype.val '' phase m)) ≠ ∅ := by
    intro m
    obtain ⟨beta, alpha, hSupport, hMapBeta, hAlphaNe, _hAlphaAligned,
      _hPeriodZero, hPeriod, hMapAlpha, _hProperZero, hProper⟩ :=
      hAxis P hScale phi hphi D Tphi hTphi (phase 0) (phase m) G rfl
        ⟨hSourcePacking 0, hSourcePacking m, hTargetPacking 0, hTargetPacking m⟩
        ⟨hPhaseNonempty 0, hPhaseNonempty m⟩
        ⟨hPhaseAligned 0, hPhaseAligned m⟩
        ⟨hLinked 0, hLinked m⟩ imagePeriod hImagePeriodNe hImagePeriodAxis
        ⟨hImagePeriod 0, hImagePeriod m⟩
        (m • Dcmp.gamma.toPlane) (hImageSupport m)
    exact ⟨beta, alpha, hSupport, hMapBeta, hAlphaNe, hPeriod, hMapAlpha, hProper⟩
  choose beta alpha hSupport hMapBeta hAlphaNe hPeriod hMapAlpha hProper
    using hOrbitTransport
  have hSynchronize : ∀ m : ℤ, alpha m = alpha 0 :=
    periodLifts_synchronizeFamily P phi hphi 0 phase alpha beta imagePeriod
      hMapAlpha hPeriod hSupport (Set.nonempty_iff_ne_empty.mpr (hProper 0))
  refine ⟨alpha 0, hAlphaNe 0, hMapAlpha 0, ?_, ?_⟩
  · intro m
    rw [hPhaseSlice m, ← hSynchronize m]
    exact hPeriod m
  · intro m
    refine ⟨beta m, ?_, hMapBeta m, ?_⟩
    · simpa only [← hPhaseSlice m, ← hSliceZero] using hSupport m
    · simpa only [← hPhaseSlice m] using hProper m

private theorem verticalFLCNoGapOrbitTransport_of_imagePacking :
  ∀ {C : ApproximationContext.{0}} (_hFLC : HasFLC C.centres)
    (_hColumnable : ∃ Col : Set Tiling.Plane,
      IsCenterColumn Axis.vertical C.region Col),
    ∃ recoveryScale : ℝ, 0 < recoveryScale ∧
      ∀ (P : FLCControlPackage C), recoveryScale < P.scale →
      ∀ (phi : C.coordinateSpace →ₗ[ℚ] ℚ), IsEpsilonApproximation C P.threshold phi →
      ∀ (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane),
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) →
      Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
        (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)) →
      ∀ (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
        (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
          RationalSlice (Dcmp.direction i) → Set Tiling.Plane),
      (∀ i Q, Q ∈ (Dcmp.orbit i).phases → originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}) →
      ∀ (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)),
      (∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).noGapPhases (originalSlice i)
          (60 * Metric.diam C.region.openCarrier)) →
      (Dcmp.direction i).toPlane.re = 0 →
      (¬ IsCenterColumn Axis.vertical C.region (originalSlice i Q)) →
      ∀ m : ℤ, ∃ beta : {z : Tiling.Plane //
        z.re ∈ C.coordinateSpace ∧ z.im ∈ C.coordinateSpace},
        regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          (beta : Tiling.Plane) +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi beta = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  intro C hFLC hColumnable
  obtain ⟨recoveryScale, hRecovery, hAxis⟩ :=
    columnableAxisLocalTransport hFLC Axis.vertical hColumnable
  refine ⟨recoveryScale, hRecovery, ?_⟩
  intro P hScale phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice
    hOriginalSlice i Q hNoGap hVertical hNotColumn
  let phase : ℤ → Set ↥C.centres := fun m =>
    {t | Tphi t ∈ (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i)}
  have hPhase : ∀ m : ℤ,
      Q.vadd (m • Dcmp.gamma.toPlane) ∈ (Dcmp.orbit i).phases :=
    fun m ↦ (hNoGap m).1
  have hPhaseSlice (m : ℤ) :
      originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
        Subtype.val '' phase m :=
    hOriginalSlice i _ (hPhase m)
  have hPhaseImage (m : ℤ) :
      Tphi '' phase m =
        (Q.vadd (m • Dcmp.gamma.toPlane)).centres (Dcmp.part i) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      have hxT : x ∈ Set.range Tphi := by
        rw [← Dcmp.parts_union]
        exact Set.mem_iUnion.2 ⟨i, hx.1⟩
      obtain ⟨t, rfl⟩ := Set.mem_range.mp hxT
      exact ⟨t, hx, rfl⟩
  have hPreimageNonempty :
      ∀ q, q ∈ (Dcmp.orbit i).phases →
        ({t : ↥C.centres | Tphi t ∈ q.centres (Dcmp.part i)}).Nonempty := by
    intro q hq
    obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty q).mp hq
    have hxT : x ∈ Set.range Tphi := by
      rw [← Dcmp.parts_union]
      exact Set.mem_iUnion.2 ⟨i, hx.1⟩
    obtain ⟨t, ht⟩ := Set.mem_range.mp hxT
    refine ⟨t, ?_⟩
    change Tphi t ∈ q.centres (Dcmp.part i)
    simpa only [ht] using hx
  have hPhaseNonempty (m : ℤ) : (phase m).Nonempty :=
    hPreimageNonempty _ (hPhase m)
  have hSourcePacking (m : ℤ) : Tiling.IsPacking
      C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (Subtype.val '' phase m)) := by
    apply (isPacking_iff_openCarrier_disjoint C.region _).2
    intro x hx y hy hxy
    have hsub : Subtype.val '' phase m ⊆ C.centres := by
      rintro z ⟨t, _ht, rfl⟩
      exact t.2
    exact (isPacking_iff_openCarrier_disjoint C.region C.centres).1
      P.source_tilesOn.2.1 (hsub hx) (hsub hy) hxy
  have hTargetPacking (m : ℤ) : Tiling.IsPacking
      D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Tphi '' phase m)) := by
    apply (isPacking_iff_openCarrier_disjoint D.deformedRegion _).2
    intro x hx y hy hxy
    have hsub : Tphi '' phase m ⊆ Set.range Tphi := by
      rintro z ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
    exact (isPacking_iff_openCarrier_disjoint D.deformedRegion (Set.range Tphi)).1
      hImagePacking (hsub hx) (hsub hy) hxy
  have hPhaseAligned (m : ℤ) : ∃ c : ℝ, ∀ t : phase m,
      Axis.vertical.transverseCoord (Tphi t.1) = c := by
    obtain ⟨x, hx⟩ := ((Dcmp.orbit i).phase_iff_nonempty _).mp (hPhase m)
    refine ⟨x.re, ?_⟩
    intro t
    change (Tphi t.1).re = x.re
    have htQ : QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
        (Tphi t.1) = Q.vadd (m • Dcmp.gamma.toPlane) := t.2.2
    have hxQ : QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
        x = Q.vadd (m • Dcmp.gamma.toPlane) := hx.2
    have hdiff : Tphi t.1 - x ∈ realDirectionSubgroup (Dcmp.direction i) :=
      QuotientAddGroup.eq_iff_sub_mem.mp (htQ.trans hxQ.symm)
    obtain ⟨r, hr⟩ := hdiff
    have hre : (Tphi t.1 - x).re = 0 := by
      rw [hr]
      simp only [Complex.smul_re, hVertical, smul_zero]
    have hsub : (Tphi t.1).re - x.re = 0 := by
      simpa only [Complex.sub_re] using hre
    exact sub_eq_zero.mp hsub
  have hImagePeriod (m : ℤ) :
      (Dcmp.direction i).toPlane +ᵥ Tphi '' phase m = Tphi '' phase m := by
    rw [hPhaseImage m]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic _ (hPhase m))
  have hImageSupport (m : ℤ) :
      regularSupport D.deformedRegion (Tphi '' phase m) =
        (m • Dcmp.gamma.toPlane) +ᵥ
          regularSupport D.deformedRegion (Tphi '' phase 0) := by
    rw [hPhaseImage m, hPhaseImage 0]
    have hQphase : Q ∈ (Dcmp.orbit i).phases := by
      simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hPhase 0
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using
      ((Dcmp.orbit i).regularSupport_transport Q hQphase m).symm
  let G : ℝ := 60 * Metric.diam C.region.openCarrier
  have hOriginalNonempty : ∀ q, q ∈ (Dcmp.orbit i).phases →
      (originalSlice i q).Nonempty := by
    intro q hq
    rw [hOriginalSlice i q hq]
    exact (hPreimageNonempty q hq).image Subtype.val
  have hLinked (m : ℤ) : Linked G (Subtype.val '' phase m) := by
    rw [← hPhaseSlice m]
    exact (Dcmp.orbit i).linked_originalSlice_of_mem_noGapPhases
      (originalSlice i) hOriginalNonempty (hNoGap m)
  let imagePeriod : Tiling.Plane := (Dcmp.direction i).toPlane
  have hImagePeriodNe : imagePeriod ≠ 0 := by
    intro hz
    apply (Dcmp.direction i).property
    funext j
    fin_cases j
    · have hzero : ((Dcmp.direction i).coordinates 0 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.re hz
      change (Dcmp.direction i).coordinates 0 = 0
      exact_mod_cast hzero
    · have hzero : ((Dcmp.direction i).coordinates 1 : ℝ) = 0 := by
        simpa [imagePeriod, RationalDirection.toPlane] using congrArg Complex.im hz
      change (Dcmp.direction i).coordinates 1 = 0
      exact_mod_cast hzero
  have hImagePeriodAxis : Axis.vertical.transverseCoord imagePeriod = 0 := by
    simpa only [imagePeriod, Axis.transverseCoord, Axis.coord] using hVertical
  have hSliceZero : originalSlice i Q = Subtype.val '' phase 0 := by
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hPhaseSlice 0
  have hNotColumnIndices :
      ¬ IsCenterColumn Axis.vertical C.region (Subtype.val '' phase 0) := by
    rw [← hSliceZero]
    exact hNotColumn
  intro m
  obtain ⟨beta, hSupport, hMapBeta, _hProperZero, hProper⟩ :=
    hAxis P hScale phi hphi D Tphi hTphi (phase 0) (phase m) G rfl
      ⟨hSourcePacking 0, hSourcePacking m, hTargetPacking 0, hTargetPacking m⟩
      ⟨hPhaseNonempty 0, hPhaseNonempty m⟩
      ⟨hPhaseAligned 0, hPhaseAligned m⟩
      ⟨hLinked 0, hLinked m⟩ imagePeriod hImagePeriodNe hImagePeriodAxis
      ⟨hImagePeriod 0, hImagePeriod m⟩ hNotColumnIndices
      (m • Dcmp.gamma.toPlane) (hImageSupport m)
  refine ⟨beta, ?_, hMapBeta, ?_⟩
  · simpa only [← hPhaseSlice m, ← hSliceZero] using hSupport
  · simpa only [← hPhaseSlice m] using hProper

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private structure CoupledSelectedTerminalResult
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) where
  weak : Tiling.RationalPolygonal.WeaklyPeriodic R.selectedCentres
  replacement : PeriodicReplacement R.selectedRegion
    (regularSupport R.selectedRegion R.selectedCentres)
  vertexOrigin : Tiling.Plane
  replacementLattice_coset :
    vertexOrigin +ᵥ
        (replacement.lattice.toAddSubgroup : Set Tiling.Plane) ⊆
      R.selectedRegion.vertices + R.selectedCentres

/-- NEW definition distinguishing the complement of saturated gap ORBITS from
the unsaturated `noGapPhases` seed set. It is invariant under every integer
transverse shift by reindexing the universal quantifier. -/
private def IsUngappedOrbitPhase
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts)
    (Q : RationalSlice (Dcmp.direction i)) : Prop :=
  ∀ m : ℤ,
    Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i) G
end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Scratch checkpoint, not a new allocated production target: exact signed
invariance and complement-of-saturated-gap facts. No finite index is assumed. -/
private theorem ungappedOrbitPhase_saturatedGapCheckpoint
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts)
    (Q : RationalSlice (Dcmp.direction i)) (hQ : Q ∈ (Dcmp.orbit i).phases) :
    (∀ n : ℤ, IsUngappedOrbitPhase Dcmp originalSlice G i
        (Q.vadd (n • Dcmp.gamma.toPlane)) ↔
      IsUngappedOrbitPhase Dcmp originalSlice G i Q) ∧
    (IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      Disjoint (Q.centres (Dcmp.part i))
        (⋃ j, (Dcmp.orbit j).gappedCentres (originalSlice j) G)) ∧
    (¬ IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      Q.centres (Dcmp.part i) ⊆
        ⋃ j, (Dcmp.orbit j).gappedCentres (originalSlice j) G) := by
  classical
  have hshift (A : RationalSlice (Dcmp.direction i)) (n m : ℤ) :
      (A.vadd (n • Dcmp.gamma.toPlane)).vadd (m • Dcmp.gamma.toPlane) =
        A.vadd ((n + m) • Dcmp.gamma.toPlane) := by
    dsimp [RationalSlice.vadd]
    rw [add_assoc, ← add_zsmul]
  have hcancel (A : RationalSlice (Dcmp.direction i)) (n : ℤ) :
      (A.vadd (n • Dcmp.gamma.toPlane)).vadd (-n • Dcmp.gamma.toPlane) = A := by
    rw [hshift]
    simp [RationalSlice.vadd]
  constructor
  · intro n
    constructor
    · intro hgood m
      have hm := hgood (m - n)
      rw [hshift] at hm
      have heq : n + (m - n) = m := by omega
      rw [heq] at hm
      exact hm
    · intro hgood m
      rw [hshift]
      exact hgood (n + m)
  constructor
  · intro hgood
    rw [Set.disjoint_left]
    intro x hx hgap
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hgap
    obtain ⟨A, hA⟩ := Set.mem_iUnion.mp hj
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hA
    by_cases hij : i = j
    · subst j
      have heq : Q = A.1.vadd (n • Dcmp.gamma.toPlane) := by
        exact hx.2.symm.trans hn.2
      have hbad := (hgood (-n)).2
      have hseed : Q.vadd (-n • Dcmp.gamma.toPlane) = A.1 := by
        rw [heq, hcancel]
      rw [hseed] at hbad
      exact hbad A.2
    · exact Set.disjoint_left.mp
        (Dcmp.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)
        hx.1 hn.1
  · intro hnot
    have hbad : ∃ n : ℤ,
        Q.vadd (n • Dcmp.gamma.toPlane) ∉
          (Dcmp.orbit i).noGapPhases (originalSlice i) G := by
      simpa only [IsUngappedOrbitPhase, not_forall] using hnot
    obtain ⟨n, hn⟩ := hbad
    have hphase := (Dcmp.orbit i).phase_translate_mem Q hQ n
    have hgapped : Q.vadd (n • Dcmp.gamma.toPlane) ∈
        (Dcmp.orbit i).gappedPhases (originalSlice i) G := by
      by_contra hng
      exact hn ⟨hphase, hng⟩
    intro x hx
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    refine Set.mem_iUnion.mpr ⟨⟨Q.vadd (n • Dcmp.gamma.toPlane), hgapped⟩, ?_⟩
    refine Set.mem_iUnion.mpr ⟨-n, ?_⟩
    change x ∈ ((Q.vadd (n • Dcmp.gamma.toPlane)).vadd
      (-n • Dcmp.gamma.toPlane)).centres (Dcmp.part i)
    rw [hcancel]
    exact hx

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Scratch checkpoint for the initial body of the coupled constructor. It uses
the two canonical private adapters, obtains their applicable bounds
before the control package/map, and produces one rational image decomposition.
This is not an inhabitant of the final coupled-result statement. -/
private theorem selectedTerminalConstruction_rationalPrefix
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) :
    ∃ (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
      (X : Set ℝ) (P : FLCControlPackage C)
      (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (D : CoordinateDeformation C phi)
      (Tphi : ↥C.centres ↪ Tiling.Plane)
      (Y : Set ℝ) (beta : ℝ)
      (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi)) (N : ℕ),
      v₀ ∈ R.selectedRegion.vertices ∧ t₀ ∈ R.selectedCentres ∧
      C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier ∧
      C.centres = (-t₀) +ᵥ R.selectedCentres ∧
      C.target = Complex.re ⁻¹' X ∧
      C.target = (-(v₀ + t₀)) +ᵥ (Complex.re ⁻¹' R.base) ∧
      IsEpsilonApproximation C P.threshold phi ∧
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) ∧
      IsOpen Y ∧ interior (closure Y) = Y ∧ Y.Nonempty ∧
      0 < beta ∧ beta +ᵥ Y = Y ∧
      TilesOn D.deformedRegion (Set.range Tphi) (Complex.re ⁻¹' Y) ∧
      0 < Dcmp.numberOfParts ∧
      60 * Metric.diam C.region.openCarrier < P.scale ∧
      60 * Metric.diam C.region.openCarrier + P.localError < P.scale / 2 ∧
      max (3 * (60 * Metric.diam C.region.openCarrier)) 3 < P.scale ∧
      10 * (Metric.diam C.region.openCarrier + 1) < P.scale ∧
      P.scale⁻¹ < Metric.diam C.region.openCarrier ∧
      Metric.diam C.region.support < P.scale ∧
      (∀ hc : ∃ Col : Set Tiling.Plane, IsCenterColumn Axis.vertical C.region Col,
        (verticalFLCNoGapOrbitTransport_of_imagePacking P.source_hasFLC hc).choose < P.scale) ∧
      (∀ hn : ¬ ∃ Col : Set Tiling.Plane, IsCenterColumn Axis.vertical C.region Col,
        (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking
          P.source_hasFLC hn).choose < P.scale) ∧
      (horizontalNoGapOrbitTransport_of_imagePacking P.source_hasFLC).choose < P.scale ∧
      0 < N ∧ (∀ i, Dcmp.lambdaCoefficient i ∣ (N : ℤ)) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (⋃ i, (Dcmp.orbit i).gappedCentres
          (fun Q => Set.image Subtype.val
            {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
          (60 * Metric.diam C.region.openCarrier)) ((N : ℤ) • Dcmp.lambda.toPlane) ∧
      Tiling.RationalPolygonal.SetPeriodicBy
        (⋃ i, (Dcmp.orbit i).gappedCentres
          (fun Q => Set.image Subtype.val
            {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
          (60 * Metric.diam C.region.openCarrier)) ((N : ℤ) • Dcmp.gamma.toPlane) := by
  classical
  have hselected : R.selectedCentres.Nonempty := by
    cases haxis : R.orientation with
    | vertical => simpa [R.selectedCentres_vertical haxis] using R.centres_nonempty
    | horizontal =>
      rw [R.selectedCentres_horizontal haxis]
      exact R.centres_nonempty.image coordinateSwap
  obtain ⟨v₀, hv₀, w₀, hw₀, hmax, hdiam⟩ :=
    IntrinsicVertices.exists_intrinsicDiameterPair R.selectedRegion
  obtain ⟨t₀, ht₀⟩ := hselected
  obtain ⟨C, hK, hcentres, htarget, htiles⟩ :=
    normalizeApproximationContext.{0} R.selectedRegion R.selectedCentres
      (Complex.re ⁻¹' R.base) v₀ hv₀ t₀ ht₀
  let X : Set ℝ := (-(v₀ + t₀).re) +ᵥ R.base
  have htargetX : C.target = Complex.re ⁻¹' X := by
    rw [htarget]
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, mem_preimage, X,
      vadd_eq_add, Complex.add_re, neg_neg]
  have hXnonempty : X.Nonempty := by
    have hbasene : R.base.Nonempty := by
      by_contra hnone
      exact R.base_nonnull (by rw [Set.not_nonempty_iff_eq_empty.mp hnone]; simp)
    obtain ⟨x, hx⟩ := hbasene
    exact ⟨-(v₀ + t₀).re + x, x, hx, rfl⟩
  have hXopen : IsOpen X := R.base_open.vadd _
  have hXregular : interior (closure X) = X := by
    dsimp [X]
    rw [closure_vadd, interior_vadd, R.base_regular]
  have hXperiod : R.supportPeriod +ᵥ X = X := by
    dsimp [X]
    rw [vadd_comm, R.support_periodic]
  have hsourceTiles : TilesOn C.region C.centres C.target := htiles.mp R.tiles
  have hFLC : HasFLC C.centres := by
    rw [hcentres]
    exact R.selected_flc.vadd _
  let d : ℝ := Metric.diam C.region.openCarrier
  let G : ℝ := 60 * d
  have hd : 0 < d := region_openCarrier_diam_pos C.region
  have hG : 0 < G := mul_pos (by norm_num) hd
  have hdiamEq : Metric.diam C.region.support = d := by
    dsimp [d]
    rw [← C.region.isPolygonal.closure_interior]
    exact Metric.diam_closure _
  obtain ⟨delta, hdelta, hseparation⟩ := hFLC.uniformlyDiscrete
  let rV : ℝ := if hc : ∃ Col : Set Tiling.Plane,
      IsCenterColumn Axis.vertical C.region Col
    then (verticalFLCNoGapOrbitTransport_of_imagePacking hFLC hc).choose
    else (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking hFLC hc).choose
  have hrV : 0 < rV := by
    dsimp [rV]
    split_ifs with hc
    · exact (verticalFLCNoGapOrbitTransport_of_imagePacking hFLC hc).choose_spec.1
    · exact (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking hFLC hc).choose_spec.1
  let rH : ℝ := (horizontalNoGapOrbitTransport_of_imagePacking hFLC).choose
  have hrH : 0 < rH :=
    (horizontalNoGapOrbitTransport_of_imagePacking hFLC).choose_spec.1
  let B : ℝ := max (3 * G) 3 + 10 * (d + 1) + d⁻¹ + d
  have hBmax : max (3 * G) 3 < B := by
    dsimp [B]
    have hdInv : 0 < d⁻¹ := inv_pos.mpr hd
    nlinarith
  have hBten : 10 * (d + 1) < B := by
    dsimp [B]
    have hmax : 0 ≤ max (3 * G) 3 := (by positivity)
    have hdInv : 0 < d⁻¹ := inv_pos.mpr hd
    linarith
  have hBrec : d⁻¹ < B := by
    dsimp [B]
    have hmax : 0 ≤ max (3 * G) 3 := (by positivity)
    linarith
  have hBdiam : d < B := by
    dsimp [B]
    have hmax : 0 ≤ max (3 * G) 3 := (by positivity)
    have hdInv : 0 < d⁻¹ := inv_pos.mpr hd
    linarith
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * Metric.diam C.region.support / delta)
  have hN₀delta : (N₀ : ℝ) * delta > 4 * Metric.diam C.region.support :=
    (div_lt_iff₀ hdelta).mp hN₀
  obtain ⟨M, hM, hsource, hswap, hlarge, hlargeSwap, hdeltaM, hmargin, hmarginSwap⟩ :=
    commonOriginalSwappedRecoveryScale_exists C delta G G N₀ ![rV, rH, B]
      (fun i : Fin 0 => Fin.elim0 i) hdelta hG hG hN₀delta
  have hrVM : rV < M := by simpa using hsource 0
  have hrHM : rH < M := by simpa using hsource 1
  have hBM : B < M := by simpa using hsource 2
  have hGM : G < M := by
    have hmax := le_max_left (3 * G) 3
    linarith [hBmax.trans hBM]
  have hreciprocal : M⁻¹ < d := by
    have hInv := (inv_lt_inv₀ hM (inv_pos.mpr hd)).2 (hBrec.trans hBM)
    simpa using hInv
  obtain ⟨P, hPbase, hPperiod, hPscale⟩ :=
    exists_flcControlPackage C X R.supportPeriod M hFLC hXnonempty hXopen
      R.supportPeriod_pos hXperiod htargetX hsourceTiles hM
  have hImage : ∃ (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
      (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
      (Y : Set ℝ) (beta : ℝ),
      IsEpsilonApproximation C P.threshold phi ∧
      (∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2)) ∧
      IsOpen Y ∧ interior (closure Y) = Y ∧ Y.Nonempty ∧
      0 < beta ∧ beta +ᵥ Y = Y ∧
      TilesOn D.deformedRegion (Set.range Tphi) (Complex.re ⁻¹' Y) := by
    by_cases hXfull : X = Set.univ
    · obtain ⟨phi, hphi⟩ := exists_epsilonApproximation C P.threshold P.threshold_pos
      obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi (P.forces_good phi hphi)
      have hplane : TilesOn C.region C.centres Set.univ := by
        simpa [htargetX, hXfull] using hsourceTiles
      obtain ⟨Tphi, hTphi, htilephi⟩ := coordinateDeformation_tilesOn D hplane
      refine ⟨phi, D, Tphi, Set.univ, 1, hphi, hTphi, isOpen_univ, ?_,
        Set.univ_nonempty, by norm_num, ?_, ?_⟩
      · simp
      · simp
      · simpa only [Set.preimage_univ, deformedCenterCarrier, Set.image_univ] using htilephi
    · obtain ⟨Band, hBandbase, hBandperiod⟩ :=
        exists_periodicBandData C X R.supportPeriod hXnonempty hXopen hXregular
          hXfull R.supportPeriod_pos hXperiod htargetX hsourceTiles
      obtain ⟨epsilon, hFine, hbandPeriod⟩ := exists_deformedBandPeriod Band
      obtain ⟨phi, hsmall⟩ := exists_epsilonApproximation C
        (min epsilon P.threshold) (lt_min hFine.epsilon_pos P.threshold_pos)
      have hphi := hsmall.of_le (min_le_right epsilon P.threshold)
      have hfinephi := hsmall.of_le (min_le_left epsilon P.threshold)
      obtain ⟨D⟩ := exists_rationalPolygonDeformation C phi (P.forces_good phi hphi)
      obtain ⟨Tphi, Y, beta, hTphi, hYopen, hYregular, hYne, hYproper, hbetamap,
        hbetapos, hbetaperiod, hfront, hoccupied, hTileImage, hSupportImage⟩ :=
        periodicBandDeformation Band epsilon hFine phi hfinephi D
      exact ⟨phi, D, Tphi, Y, beta, hphi, hTphi, hYopen, hYregular, hYne,
        hbetapos, hbetaperiod, hTileImage⟩
  obtain ⟨phi, D, Tphi, Y, beta, hphi, hTphi, hYopen, hYregular, hYne,
    hbetapos, hbetaperiod, hTileImage⟩ := hImage
  obtain ⟨mesh, hmesh, hmeshCentres, hmeshVertices⟩ := P.mesh_after_map phi
  have hmeshPoint (p q : ℤ) :
      (((p : ℝ) / (mesh : ℝ) : ℝ) : ℂ) +
        (((q : ℝ) / (mesh : ℝ) : ℝ) : ℂ) * Complex.I ∈ rationalMesh mesh := by
    refine ⟨![p, q], ?_⟩
    apply Complex.ext <;>
      simp [Tiling.AxisParallel.RationalMesh.rationalScale]
  have hmeshAll : OnRationalMesh mesh (D.deformedRegion.vertices ∪ Set.range Tphi) := by
    intro x hx
    rcases hx with hx | hx
    · rw [D.vertices_image] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      rw [D.vertex_agreement v hv]
      obtain ⟨p, q, heq⟩ := hmeshVertices ⟨v, hv⟩
      rw [heq]
      exact hmeshPoint p q
    · obtain ⟨t, rfl⟩ := hx
      rw [hTphi]
      obtain ⟨p, q, heq⟩ := hmeshCentres t
      rw [heq]
      exact hmeshPoint p q
  have hvertical (r : ℝ) :
      (r * Complex.I) +ᵥ (Complex.re ⁻¹' Y) = Complex.re ⁻¹' Y := by
    ext z
    simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  have hhorizontal : (beta : Tiling.Plane) +ᵥ (Complex.re ⁻¹' Y) =
      Complex.re ⁻¹' Y := by
    ext z
    have hy := congrArg (fun S : Set ℝ => z.re ∈ S) hbetaperiod
    simpa [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add] using hy
  obtain ⟨Dcmp⟩ := exists_rationalFinerStructure hmesh hmeshAll
    (hYopen.preimage Complex.continuous_re) (by
      rw [Complex.closure_preimage_re, Complex.interior_preimage_re, hYregular])
    hvertical ⟨beta, ne_of_gt hbetapos, hhorizontal⟩ hTileImage
  have hparts : 0 < Dcmp.numberOfParts := by
    by_contra hnpos
    have hzero := Nat.eq_zero_of_not_pos hnpos
    have hempty := Dcmp.number_zero_iff.mp hzero
    have htimage : Tphi ⟨0, C.zero_mem_centres⟩ ∈ Set.range Tphi := Set.mem_range_self _
    rw [hempty] at htimage
    exact htimage
  let originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane :=
    fun i Q => Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}
  let decorated : ↥C.centres → ↥C.translatedVertices := fun t =>
    ⟨t, 0, C.zero_mem_vertices, t, t.2, zero_add _⟩
  have hdecoratedMap (t : ↥C.centres) :
      mapTranslatedVertex phi (decorated t) = Tphi t := by
    rw [hTphi]
    rfl
  have hLocal : ∀ Q : Set Tiling.Plane, Bornology.IsBounded Q →
      (C.centres ∩ Q).Finite := hFLC.1
  have hCoarse : ∀ v w : ↥C.centres,
      dist (Tphi v) (Tphi w) < P.scale / 2 → dist (v : Tiling.Plane) w < P.scale := by
    intro v w hclose
    exact P.coarse_inverse phi hphi (decorated v) (decorated w)
      (by simpa only [hdecoratedMap] using hclose)
  have hAccurate : ∀ v w : ↥C.centres,
      dist (v : Tiling.Plane) w < P.scale →
      dist (Tphi w - Tphi v) ((w : Tiling.Plane) - v) < P.scale⁻¹ := by
    intro v w hclose
    simpa only [hdecoratedMap, P.localError_eq] using
      P.local_accuracy phi hphi (decorated w) (decorated v)
        (by simpa only [dist_comm] using hclose)
  have hImageBounded : Bornology.IsBounded D.deformedRegion.openCarrier :=
    D.deformedRegion.isPolygonal.isCompact.isBounded.subset interior_subset
  have hImageOpen : IsOpen D.deformedRegion.openCarrier :=
    (Region.openCarrier_regularOpen D.deformedRegion).1
  have hImagePositive : 0 < volume D.deformedRegion.openCarrier :=
    hImageOpen.measure_pos volume
      (D.deformedRegion.isPolygonal.interior_nonempty D.deformedRegion.nonempty)
  have hImageDiameter : Metric.diam D.deformedRegion.openCarrier ≤ 2 * d := by
    have hsupportBound := deformedRegion_diam_le_add_localError P hphi D
      (by rw [hPscale, hdiamEq]; exact hBdiam.trans hBM)
    have hopenBound := Metric.diam_mono (show D.deformedRegion.openCarrier ⊆
        D.deformedRegion.support from interior_subset)
      D.deformedRegion.isPolygonal.isCompact.isBounded
    rw [hdiamEq, P.localError_eq, hPscale] at hsupportBound
    linarith
  obtain ⟨N, hN, hdivide, hgapLambda, hgapGamma⟩ :=
    gappedSliceUnion_twoPeriods (K := C.region) Dcmp originalSlice Tphi rfl
      (fun _ _ _ => rfl) d P.scale rfl hd
      (by simpa only [hPscale, G] using hGM)
      (by simpa only [hPscale] using hreciprocal)
      ⟨hImageOpen, hImageBounded, hImagePositive, Region.volume_frontier _, hImageDiameter⟩
      hTileImage.2.1 hLocal hCoarse hAccurate
  refine ⟨v₀, t₀, C, X, P, phi, D, Tphi, Y, beta, Dcmp, N, hv₀, ht₀, hK,
    hcentres, htargetX, htarget, hphi, hTphi, hYopen, hYregular, hYne,
    hbetapos, hbetaperiod, hTileImage, hparts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hN, hdivide, hgapLambda, hgapGamma⟩
  · simpa [hPscale, G, d] using hGM
  · simpa [hPscale, P.localError_eq, G, d] using hmargin
  · simpa [hPscale, G, d] using hBmax.trans hBM
  · simpa [hPscale, d] using hBten.trans hBM
  · simpa [hPscale, d] using hreciprocal
  · simpa [hPscale, hdiamEq] using hBdiam.trans hBM
  · intro hc
    have hrv : rV = (verticalFLCNoGapOrbitTransport_of_imagePacking P.source_hasFLC hc).choose := by
      dsimp only [rV]
      rw [dif_pos hc]
    rw [hPscale]
    exact hrv ▸ hrVM
  · intro hn
    have hrv : rV =
        (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking P.source_hasFLC hn).choose := by
      dsimp only [rV]
      rw [dif_neg hn]
    rw [hPscale]
    exact hrv ▸ hrVM
  · simpa [hPscale, rH] using hrHM

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Scratch checkpoint for the literal normalized centre partition. Good phases
are indexed by an unrestricted sigma type; finiteness is not assumed. -/
private theorem selectedTerminalConstruction_partitionPrefix
    {Kphi : Region} {source Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (Phi : ↥source ↪ Tiling.Plane) (hPhi : Set.range Phi = Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) :
    let Gap := ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G
    let GapSource := Set.image Subtype.val {t : ↥source | Phi t ∈ Gap}
    let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}
    let Slice : GoodIndex → Set Tiling.Plane := fun s =>
      Set.image Subtype.val {t : ↥source | Phi t ∈ s.2.1.centres (Dcmp.part s.1)}
    (∀ s, (Slice s).Nonempty) ∧
    Set.PairwiseDisjoint Set.univ Slice ∧
    Disjoint GapSource (⋃ s, Slice s) ∧
    GapSource ∪ (⋃ s, Slice s) = source := by
  classical
  dsimp only
  let Gap := ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  let Slice : GoodIndex → Set Tiling.Plane := fun s =>
    Set.image Subtype.val {t : ↥source | Phi t ∈ s.2.1.centres (Dcmp.part s.1)}
  have hphase (s : GoodIndex) : s.2.1 ∈ (Dcmp.orbit s.1).phases := by
    have hzero := (s.2.2 (0 : ℤ)).1
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hzero
  have hpartSubset (i : Fin Dcmp.numberOfParts) : Dcmp.part i ⊆ Tphi := by
    calc
      Dcmp.part i ⊆ ⋃ j, Dcmp.part j := subset_iUnion Dcmp.part i
      _ = Tphi := Dcmp.parts_union
  have hSliceNonempty (s : GoodIndex) : (Slice s).Nonempty := by
    obtain ⟨y, hy⟩ := (Dcmp.orbit s.1).phase_iff_nonempty s.2.1 |>.mp (hphase s)
    have hyrange : y ∈ Set.range Phi := hPhi.symm ▸ hpartSubset s.1 hy.1
    obtain ⟨t, rfl⟩ := hyrange
    exact ⟨t, t, hy, rfl⟩
  have hSliceDisjoint : Set.PairwiseDisjoint Set.univ Slice := by
    rintro ⟨i, Q⟩ _ ⟨j, Q'⟩ _ hne
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    subst b
    by_cases hij : i = j
    · subst j
      have hQQ : Q.1 = Q'.1 := ha.2.symm.trans hb.2
      exact hne (by congr 1; exact Subtype.ext hQQ)
    · exact Set.disjoint_left.mp
        (Dcmp.parts_pairwiseDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)
        ha.1 hb.1
  have hGapDisjoint : Disjoint (Set.image Subtype.val
      {t : ↥source | Phi t ∈ Gap}) (⋃ s, Slice s) := by
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, hax⟩ hx
    obtain ⟨s, b, hb, hbx⟩ := Set.mem_iUnion.mp hx
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    subst b
    exact Set.disjoint_left.mp
      ((ungappedOrbitPhase_saturatedGapCheckpoint Dcmp originalSlice G
        s.1 s.2.1 (hphase s)).2.1 s.2.2) hb ha
  have hCover : Set.image Subtype.val {t : ↥source | Phi t ∈ Gap} ∪
      (⋃ s, Slice s) = source := by
    apply Set.Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨t, ht, rfl⟩ := hx
        exact t.2
      · obtain ⟨s, t, ht, rfl⟩ := Set.mem_iUnion.mp hx
        exact t.2
    · intro x hx
      let t : ↥source := ⟨x, hx⟩
      by_cases hgap : Phi t ∈ Gap
      · exact Or.inl ⟨t, hgap, rfl⟩
      · have htphi : Phi t ∈ Tphi := hPhi ▸ Set.mem_range_self t
        rw [← Dcmp.parts_union, Set.mem_iUnion] at htphi
        obtain ⟨i, hi⟩ := htphi
        let Q : RationalSlice (Dcmp.direction i) :=
          QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i)) (Phi t)
        have hslice : Phi t ∈ Q.centres (Dcmp.part i) := ⟨hi, rfl⟩
        have hQ : Q ∈ (Dcmp.orbit i).phases :=
          ((Dcmp.orbit i).phase_iff_nonempty Q).mpr ⟨Phi t, hslice⟩
        have hgood : IsUngappedOrbitPhase Dcmp originalSlice G i Q := by
          by_contra hnot
          exact hgap ((ungappedOrbitPhase_saturatedGapCheckpoint Dcmp
            originalSlice G i Q hQ).2.2 hnot hslice)
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, Q, hgood⟩, t, hslice, rfl⟩)
  exact ⟨hSliceNonempty, hSliceDisjoint, hGapDisjoint, hCover⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Scratch algebra checkpoint for the signed synchronization identity. -/
private theorem signedIntegralSynchronizationCheckpoint
    (k l p N : ℤ) (alpha gamma lambda : Tiling.Plane)
    (hpk : p * k = N)
    (hlambda : lambda = p • (N • alpha - l • gamma)) :
    k • lambda = (N ^ 2) • alpha - (N * l) • gamma := by
  rw [hlambda, smul_smul, mul_comm k p, hpk, smul_sub, smul_smul, smul_smul, pow_two]

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- A normalized phase of a selected noncolumn terminal plate cannot be a
complete vertical centre column. The exact indexed preimage is retained. -/
private theorem selectedTerminal_normalizedPhase_notVerticalColumn
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    {Kphi : Region} (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (hQ : Q ∈ (Dcmp.orbit i).phases) :
    ¬ IsCenterColumn Axis.vertical C.region (originalSlice i Q) := by
  intro hColumn
  have hSlice : originalSlice i Q ⊆ C.centres := by
    rw [hPreimage i Q hQ]
    rintro x ⟨t, _ht, rfl⟩
    exact t.2
  let S : Set Tiling.Plane := t₀ +ᵥ originalSlice i Q
  have hS : S ⊆ R.selectedCentres := by
    rintro x ⟨s, hs, rfl⟩
    have hs' := hSlice hs
    rw [hcentres, Set.mem_vadd_set_iff_neg_vadd_mem] at hs'
    simpa only [neg_neg] using hs'
  have hSne : S.Nonempty := by
    obtain ⟨s, hs⟩ := hColumn.2.1
    exact ⟨t₀ + s, s, hs, rfl⟩
  have hUnion : openUnion C.region (originalSlice i Q) =
      (-v₀) +ᵥ openUnion R.selectedRegion (originalSlice i Q) := by
    ext z
    simp only [openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier.eq_def, Set.mem_iUnion, hK,
      Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg,
      add_assoc, add_comm]
  have hRegular : regularSupport C.region (originalSlice i Q) =
      (-v₀) +ᵥ regularSupport R.selectedRegion (originalSlice i Q) := by
    simp only [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion.eq_def]
    rw [hUnion, closure_vadd, interior_vadd]
  have hSupport : regularSupport R.selectedRegion S =
      (v₀ + t₀) +ᵥ regularSupport C.region (originalSlice i Q) := by
    dsimp only [S]
    rw [regularSupport_vadd, hRegular, vadd_vadd]
    congr 1
    abel
  obtain ⟨c, _hne, hline, hColumnSupport⟩ := centerColumn_regularSupport hColumn
  let B : Set ℝ := interior (closure (c +ᵥ (Complex.re '' C.region.openCarrier)))
  let Y : Set ℝ := (v₀ + t₀).re +ᵥ B
  have hYregular : Y = interior (closure Y) := by
    dsimp only [Y]
    rw [closure_vadd, interior_vadd]
    simp [B]
  have hSY : regularSupport R.selectedRegion S = Complex.re ⁻¹' Y := by
    rw [hSupport]
    have hCB : regularSupport C.region (originalSlice i Q) = Complex.re ⁻¹' B := by
      simpa only [B, Axis.transverseCoord, Set.preimage] using hColumnSupport
    rw [hCB]
    ext z
    simp only [Y, Set.mem_vadd_set_iff_neg_vadd_mem, mem_preimage,
      vadd_eq_add, Complex.add_re, Complex.neg_re]
  have hWhole : S = R.selectedCentres :=
    R.propagationIrreducible.vertical S hSne hS ⟨Y, hYregular, hSY⟩
  apply R.plate_noncolumn
  refine ⟨t₀.re + c, ?_⟩
  intro x hx
  have hxS : x ∈ S := by
    rw [hWhole, R.selectedCentres_eq_plate]
    exact hx
  obtain ⟨s, hs, rfl⟩ := hxS
  change (t₀ + s).re = t₀.re + c
  rw [Complex.add_re]
  exact congrArg (t₀.re + ·) (hline s hs)

private theorem direction_toPlane_ne_zero (u : RationalDirection) :
    u.toPlane ≠ 0 := by
  intro hz
  apply u.2
  funext j
  fin_cases j
  · have h := congrArg Complex.re hz
    have h' : (u.coordinates 0 : ℝ) = 0 := by
      simpa [RationalDirection.toPlane] using h
    exact_mod_cast h'
  · have h := congrArg Complex.im hz
    have h' : (u.coordinates 1 : ℝ) = 0 := by
      simpa [RationalDirection.toPlane] using h
    exact_mod_cast h'

/-- The literal columnable vertical Goal 2, starting from the adapter's beta
and proper-vertex tail and the actual rational-prefix control margins. -/
private theorem verticalCommonNativeLift
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    {Kphi : Region}
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (hgood : ∀ m : ℤ, Q.vadd (m • Dcmp.gamma.toPlane) ∈
      (Dcmp.orbit i).noGapPhases (originalSlice i)
        (60 * Metric.diam C.region.openCarrier))
    (hRe : (Dcmp.direction i).toPlane.re = 0)
    (hG : 60 * Metric.diam C.region.openCarrier < P.scale)
    (hmargin : 60 * Metric.diam C.region.openCarrier + P.localError < P.scale / 2)
    (hBetas : ∀ m : ℤ, ∃ b : ControlledDisplacement C,
      regularSupport C.region
        (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
        b.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
      mapPoint phi b = m • Dcmp.gamma.toPlane ∧
      properVertices (regularSupport C.region
        (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅) :
    ∃ alpha : ControlledDisplacement C,
      alpha.1 ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
      (∀ m : ℤ, alpha.1 +ᵥ
        originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ, ∃ b : ControlledDisplacement C,
        regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
          b.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi b = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region
          (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  classical
  let phaseQ : ℤ → RationalSlice (Dcmp.direction i) :=
    fun m => Q.vadd (m • Dcmp.gamma.toPlane)
  let phase : ℤ → Set ↥C.centres :=
    fun m => {t | Tphi t ∈ (phaseQ m).centres (Dcmp.part i)}
  have hphase (m : ℤ) : phaseQ m ∈ (Dcmp.orbit i).phases := (hgood m).1
  have hsource (m : ℤ) :
      originalSlice i (phaseQ m) = Subtype.val '' phase m :=
    hPreimage i (phaseQ m) (hphase m)
  have hzero : phaseQ 0 = Q := by
    simp only [phaseQ, zero_smul, RationalSlice.vadd, map_zero, add_zero]
  have hbase : originalSlice i Q = Subtype.val '' phase 0 := by
    rw [← hzero]
    exact hsource 0
  have hpartSubset : Dcmp.part i ⊆ Set.range Tphi := by
    calc
      Dcmp.part i ⊆ ⋃ j, Dcmp.part j := subset_iUnion Dcmp.part i
      _ = Set.range Tphi := Dcmp.parts_union
  have hnonempty (m : ℤ) : (phase m).Nonempty := by
    obtain ⟨y, hy⟩ :=
      ((Dcmp.orbit i).phase_iff_nonempty (phaseQ m)).mp (hphase m)
    obtain ⟨t, rfl⟩ := hpartSubset hy.1
    exact ⟨t, hy⟩
  have himage (m : ℤ) : deformedCenterCarrierOn Tphi (phase m) =
      (phaseQ m).centres (Dcmp.part i) := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, ht, rfl⟩
      exact ht
    · intro z hz
      obtain ⟨t, rfl⟩ := hpartSubset hz.1
      exact ⟨t, hz, rfl⟩
  have hlinked (m : ℤ) : Linked (60 * Metric.diam C.region.openCarrier)
      (Subtype.val '' phase m) := by
    rw [← hsource m]
    apply (linked_iff_not_isGappedSlice (by
      rw [hsource m]
      exact (hnonempty m).image Subtype.val)).2
    intro hgap
    exact (hgood m).2 ⟨hphase m, hgap⟩
  have hline (m : ℤ) : ∃ c : ℝ, ∀ s : phase m,
      Axis.vertical.transverseCoord (Tphi s.1) = c := by
    obtain ⟨s₀, hs₀⟩ := hnonempty m
    refine ⟨(Tphi s₀).re, ?_⟩
    intro s
    have hsQ : Tphi s.1 ∈ (phaseQ m).carrier := s.2.2
    have hs₀Q : Tphi s₀ ∈ (phaseQ m).carrier := hs₀.2
    change QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
      (Tphi s.1) = phaseQ m at hsQ
    change QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
      (Tphi s₀) = phaseQ m at hs₀Q
    obtain ⟨r, hr⟩ := QuotientAddGroup.eq_iff_sub_mem.mp (hsQ.trans hs₀Q.symm)
    have hre := congrArg Complex.re hr
    simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul, hRe, mul_zero] at hre
    change (Tphi s.1).re = (Tphi s₀).re
    linarith
  have himagePeriodNe : (Dcmp.direction i).toPlane ≠ 0 :=
    direction_toPlane_ne_zero _
  have himageVertical : Axis.vertical.transverseCoord (Dcmp.direction i).toPlane = 0 :=
    hRe
  have himagePeriod (m : ℤ) :
      (Dcmp.direction i).toPlane +ᵥ deformedCenterCarrierOn Tphi (phase m) =
        deformedCenterCarrierOn Tphi (phase m) := by
    rw [himage m]
    exact (setPeriodicBy_iff_vadd_eq _ _).mp
      ((Dcmp.orbit i).slice_periodic (phaseQ m) (hphase m))
  let beta : ℤ → ControlledDisplacement C := fun m => Classical.choose (hBetas m)
  have hbeta (m : ℤ) := Classical.choose_spec (hBetas m)
  have hsupport (m : ℤ) : regularSupport C.region (Subtype.val '' phase m) =
      (beta m).1 +ᵥ regularSupport C.region (Subtype.val '' phase 0) := by
    rw [← hsource m, ← hbase]
    exact (hbeta m).1
  have hproper :
      (properVertices (regularSupport C.region (Subtype.val '' phase 0))).Nonempty := by
    rw [← hsource 0]
    exact Set.nonempty_iff_ne_empty.mpr (hbeta 0).2.2
  obtain ⟨alpha, hne, _haligned, hmap, hperiod⟩ :=
    connectedPhasePeriodLifts_synchronize P phi hphi Tphi hTphi Axis.vertical
      phase (60 * Metric.diam C.region.openCarrier) hnonempty hlinked hline hG hmargin
      (Dcmp.direction i).toPlane himagePeriodNe himageVertical himagePeriod beta
      (fun m => m • Dcmp.gamma.toPlane) hsupport (fun m => (hbeta m).2.1) hproper
  refine ⟨alpha, hne, hmap, ?_, hBetas⟩
  intro m
  rw [hsource m]
  exact hperiod m


/-- A selected terminal carrier admits no horizontal row after vertex/centre
normalization. The arbitrary row need only lie in the normalized centre set. -/
private theorem normalizedTerminalRegion_noHorizontalRow
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    {S : Set Tiling.Plane} (hS : S ⊆ C.centres) :
    ¬ IsCenterColumn Axis.horizontal C.region S := by
  have hsupport (A : Set Tiling.Plane) :
      regularSupport C.region A =
        (-(v₀ + t₀)) +ᵥ regularSupport R.selectedRegion (t₀ +ᵥ A) := by
    have hopen : openUnion C.region A =
        (-v₀) +ᵥ openUnion R.selectedRegion A := by
      ext z
      constructor
      · rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        rintro ⟨a, k, hk, rfl⟩
        rw [hK] at hk
        obtain ⟨u, hu, rfl⟩ := hk
        refine ⟨a + u, ?_, by simp only [vadd_eq_add]; abel⟩
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
        exact ⟨a, u, hu, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion] at hz ⊢
        obtain ⟨a, u, hu, rfl⟩ := hz
        refine ⟨a, (-v₀) + u, ?_, by simp only [vadd_eq_add]; abel⟩
        rw [hK]
        exact ⟨u, hu, rfl⟩
    rw [regularSupport, Tiling.Polygonal.regularSupport,
      ← openUnion, hopen, closure_vadd, interior_vadd,
      regularSupport_vadd, vadd_vadd]
    congr 1
    abel
  let X : Set ℝ := {r | (v₀ + t₀).re + r ∈ R.base}
  have hCarrier : regularSupport C.region C.centres =
      {z : Tiling.Plane | z.re ∈ X} := by
    rw [hsupport, hcentres, vadd_vadd, add_neg_cancel, zero_vadd, R.support_eq]
    ext z
    simp only [Set.mem_vadd_set_iff_neg_vadd_mem, neg_neg, mem_preimage,
      Set.mem_ofPred_eq, vadd_eq_add, Complex.add_re, X]
  have hIrreducible : X = Set.univ →
      ∀ A : Set Tiling.Plane, A.Nonempty → A ⊆ C.centres →
        (∀ r : ℝ, (r : Tiling.Plane) +ᵥ regularSupport C.region A =
          regularSupport C.region A) → A = C.centres := by
    intro hX A hAne hAsub hAperiod
    have hbase : R.base = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx : x - (v₀ + t₀).re ∈ X := hX ▸ Set.mem_univ _
      change (v₀ + t₀).re + (x - (v₀ + t₀).re) ∈ R.base at hx
      convert hx using 1
      ring
    have hback : regularSupport R.selectedRegion (t₀ +ᵥ A) =
        (v₀ + t₀) +ᵥ regularSupport C.region A := by
      rw [hsupport, vadd_vadd, add_neg_cancel, zero_vadd]
    have hbackPeriod : ∀ r : ℝ,
        (r : Tiling.Plane) +ᵥ regularSupport R.selectedRegion (t₀ +ᵥ A) =
          regularSupport R.selectedRegion (t₀ +ᵥ A) := by
      intro r
      rw [hback, vadd_comm, hAperiod]
    obtain ⟨Y, hY⟩ :=
      (horizontalInvariant_iff_product
        (regularSupport R.selectedRegion (t₀ +ᵥ A))).mp hbackPeriod
    change regularSupport R.selectedRegion (t₀ +ᵥ A) = Complex.im ⁻¹' Y at hY
    have hYregular : Y = interior (closure Y) := by
      have hpre : Complex.im ⁻¹' interior (closure Y) = Complex.im ⁻¹' Y := by
        calc
          Complex.im ⁻¹' interior (closure Y) =
              interior (Complex.im ⁻¹' closure Y) :=
            (Complex.interior_preimage_im _).symm
          _ = interior (closure (Complex.im ⁻¹' Y)) := by
            rw [Complex.closure_preimage_im]
          _ = interior (closure
              (regularSupport R.selectedRegion (t₀ +ᵥ A))) := by rw [hY]
          _ = regularSupport R.selectedRegion (t₀ +ᵥ A) :=
            (regularSupport_isRegularOpen R.selectedRegion (t₀ +ᵥ A)).2
          _ = Complex.im ⁻¹' Y := hY
      apply Eq.symm
      apply (Set.preimage_injective.mpr ?_) hpre
      intro r
      exact ⟨(r : ℂ) * Complex.I, by simp⟩
    have hbackSub : t₀ +ᵥ A ⊆ R.selectedCentres := by
      intro z hz
      have hz' : z ∈ t₀ +ᵥ C.centres :=
        Set.vadd_set_mono hAsub hz
      simpa only [hcentres, vadd_vadd, add_neg_cancel, zero_vadd] using hz'
    have hEq := R.propagationIrreducible.horizontal_of_full hbase
      (t₀ +ᵥ A) (by obtain ⟨a, ha⟩ := hAne; exact ⟨t₀ + a, a, ha, rfl⟩)
      hbackSub ⟨Y, hYregular, hY⟩
    rw [hcentres, ← hEq, vadd_vadd, neg_add_cancel, zero_vadd]
  intro hrow
  exact irreducibleRegion_noHorizontalRow
    ⟨0, C.zero_mem_centres⟩ hS hrow.2.1 X hCarrier hIrreducible hrow


/-- Exhaustive axis/oblique dispatch in the selected normalized carrier.  Every
native period is a literal centre period; each beta remains a support shift. -/
private theorem selectedTerminalConstruction_nativeDispatch
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    (P : FLCControlPackage C) (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi)
    (D : CoordinateDeformation C phi) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (hImagePacking : Tiling.IsPacking D.deformedRegion.toPolygonalRegion.prototileFamily
      (D.deformedRegion.toPolygonalRegion.placements (Set.range Tphi)))
    (Dcmp : RationalDirectionalDecomposition D.deformedRegion (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (hG : 60 * Metric.diam C.region.openCarrier < P.scale)
    (hmargin : 60 * Metric.diam C.region.openCarrier + P.localError < P.scale / 2)
    (hMax : max (3 * (60 * Metric.diam C.region.openCarrier)) 3 < P.scale)
    (hTen : 10 * (Metric.diam C.region.openCarrier + 1) < P.scale)
    (hVc : ∀ hc : ∃ Col : Set Tiling.Plane, IsCenterColumn Axis.vertical C.region Col,
      (verticalFLCNoGapOrbitTransport_of_imagePacking P.source_hasFLC hc).choose < P.scale)
    (hVnc : ∀ hn : ¬ ∃ Col : Set Tiling.Plane, IsCenterColumn Axis.vertical C.region Col,
      (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking
        P.source_hasFLC hn).choose < P.scale)
    (hH : (horizontalNoGapOrbitTransport_of_imagePacking P.source_hasFLC).choose < P.scale) :
    ∀ (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)),
      IsUngappedOrbitPhase Dcmp originalSlice
        (60 * Metric.diam C.region.openCarrier) i Q →
      ∃ alpha : ControlledDisplacement C,
        alpha.1 ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction i).toPlane ∧
        (∀ m : ℤ, alpha.1 +ᵥ
          originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) =
            originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) ∧
        ∀ m : ℤ, ∃ b : ControlledDisplacement C,
          regularSupport C.region (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
            b.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
          mapPoint phi b = m • Dcmp.gamma.toPlane ∧
          properVertices (regularSupport C.region
            (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ := by
  classical
  intro i Q hgood
  by_cases hRe : (Dcmp.direction i).toPlane.re = 0
  · by_cases hc : ∃ Col : Set Tiling.Plane, IsCenterColumn Axis.vertical C.region Col
    · have hNotColumn : ¬ IsCenterColumn Axis.vertical C.region (originalSlice i Q) := by
        have hQ : Q ∈ (Dcmp.orbit i).phases := by
          simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using (hgood (0 : ℤ)).1
        exact selectedTerminal_normalizedPhase_notVerticalColumn R v₀ t₀ C hK hcentres
          Tphi Dcmp originalSlice hPreimage i Q hQ
      have hBetas :=
        (verticalFLCNoGapOrbitTransport_of_imagePacking P.source_hasFLC hc).choose_spec.2
        P (hVc hc) phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice hPreimage
        i Q hgood hRe hNotColumn
      exact verticalCommonNativeLift P phi hphi Tphi hTphi
        Dcmp originalSlice hPreimage i Q hgood hRe hG hmargin hBetas
    · exact (nonColumnableVerticalNoGapOrbitTransport_of_imagePacking
        P.source_hasFLC hc).choose_spec.2
        P (hVnc hc) phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice hPreimage
        i Q hgood hRe
  · by_cases hIm : (Dcmp.direction i).toPlane.im = 0
    · have hNotRow : (∃ Row : Set Tiling.Plane, IsCenterColumn Axis.horizontal C.region Row) →
          ¬ IsCenterColumn Axis.horizontal C.region (originalSlice i Q) := by
        intro _hHasRow
        apply normalizedTerminalRegion_noHorizontalRow R v₀ t₀ C hK hcentres
        rw [hPreimage i Q (by simpa [RationalSlice.vadd] using (hgood 0).1)]
        rintro z ⟨t, _ht, rfl⟩
        exact t.2
      obtain ⟨alpha, hne, _haligned, hmap, hperiod, hbetas⟩ :=
        (horizontalNoGapOrbitTransport_of_imagePacking P.source_hasFLC).choose_spec.2
          P hH phi hphi D Tphi hTphi hImagePacking Dcmp originalSlice hPreimage
          i hIm Q hgood hNotRow
      exact ⟨alpha, hne, hmap, hperiod, hbetas⟩
    · exact obliqueNoGapOrbitTransport_of_imagePacking P phi hphi D Tphi hTphi
        hImagePacking Dcmp originalSlice hPreimage
        (Metric.diam C.region.openCarrier) (60 * Metric.diam C.region.openCarrier)
        P.scale rfl
        ⟨region_openCarrier_diam_pos C.region, rfl, hMax, le_rfl, hTen⟩
        i (mul_ne_zero hRe hIm) Q hgood

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem rationalSlice_signedShift_add
    (u : RationalDirection) (Q : RationalSlice u) (gamma : Tiling.Plane) (n m : ℤ) :
    (Q.vadd (n • gamma)).vadd (m • gamma) = Q.vadd ((n + m) • gamma) := by
  dsimp only [RationalSlice.vadd]
  rw [add_zsmul, map_add, add_assoc]

/-- Actual signed good-phase permutation, before any orbit-finiteness claim. -/
private noncomputable def ungappedPhaseShiftEquiv
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts) (n : ℤ) :
    Equiv.Perm {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q} where
  toFun Q := ⟨Q.1.vadd (n • Dcmp.gamma.toPlane), by
    have hQ : Q.1 ∈ (Dcmp.orbit i).phases := by
      simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using (Q.2 0).1
    exact ((ungappedOrbitPhase_saturatedGapCheckpoint Dcmp originalSlice G i Q.1 hQ).1 n).mpr Q.2⟩
  invFun Q := ⟨Q.1.vadd (-n • Dcmp.gamma.toPlane), by
    have hQ : Q.1 ∈ (Dcmp.orbit i).phases := by
      simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using (Q.2 0).1
    exact ((ungappedOrbitPhase_saturatedGapCheckpoint
      Dcmp originalSlice G i Q.1 hQ).1 (-n)).mpr Q.2⟩
  left_inv Q := by
    apply Subtype.ext
    change (Q.1.vadd (n • Dcmp.gamma.toPlane)).vadd
      (-n • Dcmp.gamma.toPlane) = Q.1
    rw [rationalSlice_signedShift_add]
    simp only [add_neg_cancel, zero_smul, RationalSlice.vadd, map_zero, add_zero]
  right_inv Q := by
    apply Subtype.ext
    change (Q.1.vadd (-n • Dcmp.gamma.toPlane)).vadd
      (n • Dcmp.gamma.toPlane) = Q.1
    rw [rationalSlice_signedShift_add]
    simp only [neg_add_cancel, zero_smul, RationalSlice.vadd, map_zero, add_zero]

/-- Genuine signed-orbit equivalence relation, not a chosen representative list. -/
private def ungappedPhaseSetoid
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts) :
    Setoid {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q} where
  r Q Q' := ∃ m : ℤ, Q'.1 = Q.1.vadd (m • Dcmp.gamma.toPlane)
  iseqv := {
    refl := fun Q => ⟨0, by
      simp only [zero_smul, RationalSlice.vadd, map_zero, add_zero]⟩
    symm := by
      rintro Q Q' ⟨m, hm⟩
      refine ⟨-m, ?_⟩
      rw [hm, rationalSlice_signedShift_add]
      simp only [add_neg_cancel, zero_smul, RationalSlice.vadd, map_zero, add_zero]
    trans := by
      rintro Q Q' Q'' ⟨m, hm⟩ ⟨n, hn⟩
      exact ⟨m + n, by rw [hn, hm, rationalSlice_signedShift_add]⟩ }

/-- Orbit centre unions are independent of every signed representative shift. -/
private theorem ungappedOrbitUnion_shift
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)) (n : ℤ) :
    (⋃ m : ℤ, originalSlice i
      ((Q.vadd (n • Dcmp.gamma.toPlane)).vadd (m • Dcmp.gamma.toPlane))) =
      ⋃ m : ℤ, originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + m, by
      rwa [rationalSlice_signedShift_add] at hm⟩
  · intro hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    refine Set.mem_iUnion.mpr ⟨m - n, ?_⟩
    rw [rationalSlice_signedShift_add]
    simpa only [show n + (m - n) = m by omega] using hm

/-- The unrestricted native atom family: singletons only in the saturated gap
part, and every actual good phase otherwise. No Finite or Fintype is assumed. -/
private theorem nativeAtomPartition
    {J : Type} (source GapSource : Set Tiling.Plane) (Slice : J → Set Tiling.Plane)
    (hne : ∀ j, (Slice j).Nonempty)
    (hdis : Set.PairwiseDisjoint Set.univ Slice)
    (hgap : Disjoint GapSource (⋃ j, Slice j))
    (hcover : GapSource ∪ (⋃ j, Slice j) = source) :
    let atom : Sum ↥GapSource J → Set Tiling.Plane :=
      Sum.elim (fun t => {t.1}) Slice
    (∀ a, (atom a).Nonempty) ∧ Set.PairwiseDisjoint Set.univ atom ∧
      (⋃ a, atom a) = source := by
  classical
  dsimp only
  constructor
  · intro a
    cases a with
    | inl t => exact Set.singleton_nonempty _
    | inr j => exact hne j
  constructor
  · intro a _ b _ hab
    cases a with
    | inl t =>
      cases b with
      | inl s =>
        apply Set.disjoint_singleton.mpr
        intro hts
        apply hab
        exact congrArg Sum.inl (Subtype.ext hts)
      | inr j =>
        apply Set.disjoint_singleton_left.mpr
        intro ht
        exact Set.disjoint_left.mp hgap t.2 (Set.mem_iUnion.mpr ⟨j, ht⟩)
    | inr j =>
      cases b with
      | inl t =>
        apply Set.disjoint_singleton_right.mpr
        intro ht
        exact Set.disjoint_left.mp hgap t.2 (Set.mem_iUnion.mpr ⟨j, ht⟩)
      | inr k =>
        exact hdis (Set.mem_univ _) (Set.mem_univ _) (fun hjk => hab (congrArg Sum.inr hjk))
  · rw [← hcover]
    ext x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      cases a with
      | inl t =>
        have hx : x = t.1 := Set.mem_singleton_iff.mp ha
        exact Or.inl (hx.symm ▸ t.2)
      | inr j => exact Or.inr (Set.mem_iUnion.mpr ⟨j, ha⟩)
    · rintro (hx | hx)
      · exact Set.mem_iUnion.mpr ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨Sum.inr j, hj⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- One total rational-linear map extending the same controlled coordinate map.
Only decorated source vertices are claimed to lie in its injectivity domain. -/
private theorem coordinatePlaneExtension_exists
    {C : ApproximationContext.{0}} (P : FLCControlPackage C)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ)
    (hphi : IsEpsilonApproximation C P.threshold phi) :
    ∃ f : Tiling.Plane →ₗ[ℚ] Tiling.Plane,
      (∀ x : ControlledDisplacement C, f x.1 = mapPoint phi x) ∧
      Set.InjOn f C.translatedVertices := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_extend phi
  have hrestrict (x : C.coordinateSpace) : g x.1 = phi x := by
    exact congrArg (fun L : C.coordinateSpace →ₗ[ℚ] ℚ => L x) hg
  let f : Tiling.Plane →ₗ[ℚ] Tiling.Plane :=
    (g.smulRight (1 : Tiling.Plane)).comp (Complex.reLm.restrictScalars ℚ) +
      (g.smulRight Complex.I).comp (Complex.imLm.restrictScalars ℚ)
  have hext (x : ControlledDisplacement C) : f x.1 = mapPoint phi x := by
    change g x.1.re • (1 : Tiling.Plane) + g x.1.im • Complex.I = mapPoint phi x
    rw [hrestrict ⟨x.1.re, x.2.1⟩, hrestrict ⟨x.1.im, x.2.2⟩]
    apply Complex.ext <;>
      simp [mapPoint, mapScalar, Complex.smul_re, Complex.smul_im]
  refine ⟨f, hext, ?_⟩
  intro x hx y hy hxy
  let a : ↥C.translatedVertices := ⟨x, hx⟩
  let b : ↥C.translatedVertices := ⟨y, hy⟩
  have hab : mapTranslatedVertex phi a = mapTranslatedVertex phi b := by
    rw [mapTranslatedVertex, mapTranslatedVertex, ← hext, ← hext]
    exact hxy
  exact congrArg Subtype.val (deformation_injectiveOnTranslatedVertices P phi hphi hab)

/-- An image-period acts on the actual indexed preimage by conjugation.  Its
source displacement is the difference of the successor centres, not eta. -/
private theorem indexedImagePeriod_successor_exists
    {source : Set Tiling.Plane} (Phi : ↥source ↪ Tiling.Plane)
    (Gap : Set Tiling.Plane) (hsub : Gap ⊆ Set.range Phi)
    (eta : Tiling.Plane) (hperiod : eta +ᵥ Gap = Gap) :
    ∃ next : Equiv.Perm {t : ↥source // Phi t ∈ Gap},
      ∀ t, Phi (next t).1 = Phi t.1 + eta := by
  classical
  let indexed : Set ↥source := {t | Phi t ∈ Gap}
  have hforward (t : ↥indexed) : Phi t.1 + eta ∈ Gap := by
    rw [← hperiod]
    exact ⟨Phi t.1, t.2, by simp only [vadd_eq_add]; abel⟩
  have hbackward (t : ↥indexed) : Phi t.1 - eta ∈ Gap := by
    have hneg : (-eta) +ᵥ Gap = Gap := by
      calc
        (-eta) +ᵥ Gap = (-eta) +ᵥ (eta +ᵥ Gap) :=
          congrArg ((-eta) +ᵥ ·) hperiod.symm
        _ = Gap := by rw [vadd_vadd, neg_add_cancel, zero_vadd]
    rw [← hneg]
    exact ⟨Phi t.1, t.2, by simp only [vadd_eq_add]; abel⟩
  have hpreimage (x : Tiling.Plane) (hx : x ∈ Gap) :
      ∃ t : ↥indexed, Phi t.1 = x := by
    obtain ⟨t, ht⟩ := hsub hx
    exact ⟨⟨t, by change Phi t ∈ Gap; rw [ht]; exact hx⟩, ht⟩
  let forward (t : ↥indexed) : ↥indexed :=
    (hpreimage (Phi t.1 + eta) (hforward t)).choose
  let backward (t : ↥indexed) : ↥indexed :=
    (hpreimage (Phi t.1 - eta) (hbackward t)).choose
  have hf (t : ↥indexed) : Phi (forward t).1 = Phi t.1 + eta :=
    (hpreimage _ (hforward t)).choose_spec
  have hb (t : ↥indexed) : Phi (backward t).1 = Phi t.1 - eta :=
    (hpreimage _ (hbackward t)).choose_spec
  refine ⟨⟨forward, backward, ?_, ?_⟩, hf⟩
  · intro t
    apply Subtype.ext
    apply Phi.injective
    rw [hb, hf]
    abel
  · intro t
    apply Subtype.ext
    apply Phi.injective
    rw [hf, hb]
    abel

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem normalizedSelectedSupport_eq
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (S : Set Tiling.Plane) :
    regularSupport R.selectedRegion (t₀ +ᵥ S) =
      (v₀ + t₀) +ᵥ regularSupport C.region S := by
  have hUnion : openUnion C.region S = (-v₀) +ᵥ openUnion R.selectedRegion S := by
    ext z
    simp only [openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier.eq_def, Set.mem_iUnion, hK,
      Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_neg, add_assoc, add_comm]
  have hRegular : regularSupport C.region S =
      (-v₀) +ᵥ regularSupport R.selectedRegion S := by
    simp only [regularSupport, Tiling.Polygonal.regularSupport, ← openUnion.eq_def]
    rw [hUnion, closure_vadd, interior_vadd]
  rw [regularSupport_vadd, hRegular, vadd_vadd]
  congr 1
  abel

/-- The total map's injectivity is transported to the original SELECTED
decorated vertices by the combined vertex/centre normalization offset. -/
private theorem normalizedSelectedTranslatedVertices_eq
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres) :
    C.translatedVertices = (-(v₀ + t₀)) +ᵥ
      (R.selectedRegion.vertices + R.selectedCentres) := by
  have hsupport : C.region.support = (-v₀) +ᵥ R.selectedRegion.support := by
    calc
      C.region.support = closure C.region.openCarrier := C.region.isPolygonal.closure_interior.symm
      _ = closure ((-v₀) +ᵥ R.selectedRegion.openCarrier) := congrArg closure hK
      _ = (-v₀) +ᵥ closure R.selectedRegion.openCarrier := closure_vadd _ _
      _ = (-v₀) +ᵥ R.selectedRegion.support :=
        congrArg ((-v₀) +ᵥ ·) R.selectedRegion.isPolygonal.closure_interior
  have hvertices : C.region.vertices = (-v₀) +ᵥ R.selectedRegion.vertices := by
    rw [Region.vertices, hsupport, Tiling.vertexSet_vadd]
    rfl
  rw [ApproximationContext.translatedVertices, hvertices, hcentres]
  ext x
  constructor
  · rintro ⟨v, ⟨a, ha, rfl⟩, t, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨a + b, ⟨a, ha, b, hb, rfl⟩, by simp only [vadd_eq_add]; abel⟩
  · rintro ⟨z, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    refine ⟨-v₀ + a, ⟨a, ha, rfl⟩, -t₀ + b, ⟨b, hb, rfl⟩, ?_⟩
    simp only [vadd_eq_add]
    abel

private theorem selectedDecoratedMap_injOn
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane) (hinj : Set.InjOn f C.translatedVertices) :
    Set.InjOn (fun x => f (x - (v₀ + t₀)))
      (R.selectedRegion.vertices + R.selectedCentres) := by
  intro x hx y hy hxy
  have hnorm (z : Tiling.Plane)
      (hz : z ∈ R.selectedRegion.vertices + R.selectedCentres) :
      z - (v₀ + t₀) ∈ C.translatedVertices := by
    rw [normalizedSelectedTranslatedVertices_eq R v₀ t₀ C hK hcentres]
    exact ⟨z, hz, by simp only [vadd_eq_add]; abel⟩
  exact sub_left_inj.mp (hinj (hnorm x hx) (hnorm y hy) hxy)

/-- Image-period successors yield their ACTUAL source displacement and the
correct image increment on every decorated point via this same linear map. -/
private theorem indexedImagePeriod_sourceDisplacement
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (hext : ∀ x : ControlledDisplacement C, f x.1 = mapPoint phi x)
    (Gap : Set Tiling.Plane) (eta : Tiling.Plane)
    (next : Equiv.Perm {t : ↥C.centres // Tphi t ∈ Gap})
    (hnext : ∀ t, Tphi (next t).1 = Tphi t.1 + eta) :
    ∀ t, f ((next t).1.1 - t.1.1) = eta ∧
      ∀ x : Tiling.Plane,
        f (x + ((next t).1.1 - t.1.1)) = f x + eta := by
  intro t
  have hCentre (s : ↥C.centres) : f s.1 = Tphi s := by
    calc
      f s.1 = f (C.centrePoint s.1 s.2).1 := rfl
      _ = mapPoint phi (C.centrePoint s.1 s.2) := hext _
      _ = Tphi s := (hTphi s).symm
  have hmap : f ((next t).1.1 - t.1.1) = eta := by
    rw [map_sub, hCentre, hCentre, hnext]
    abel
  exact ⟨hmap, fun x => by rw [map_add, hmap]⟩

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal

open scoped Pointwise

private theorem signedSupportIteration (D : ℤ → Set Tiling.Plane) (gamma : Tiling.Plane)
    (N : ℤ) (hstep : ∀ m : ℤ, gamma +ᵥ D m = D (m + N)) :
    ∀ q m : ℤ, (q • gamma) +ᵥ D m = D (m + q * N) := by
  have hback (m : ℤ) : (-gamma) +ᵥ D m = D (m - N) := by
    have h := congrArg (fun A : Set Tiling.Plane ↦ (-gamma) +ᵥ A) (hstep (m - N))
    simpa only [sub_add_cancel, neg_vadd_vadd] using h.symm
  intro q
  refine Int.induction_on q ?_ ?_ ?_
  · intro m
    simp only [zero_zsmul, zero_vadd, zero_mul, add_zero]
  · intro n ih m
    calc
      (((n : ℤ) + 1) • gamma) +ᵥ D m =
          gamma +ᵥ (((n : ℤ) • gamma) +ᵥ D m) := by
        rw [add_zsmul, one_zsmul, add_comm, add_vadd]
      _ = D (m + (n : ℤ) * N + N) := by rw [ih, hstep]
      _ = D (m + ((n : ℤ) + 1) * N) := by congr 1; ring
  · intro n ih m
    calc
      (((-(n : ℤ)) - 1) • gamma) +ᵥ D m =
          (-gamma) +ᵥ (((-(n : ℤ)) • gamma) +ᵥ D m) := by
        rw [sub_zsmul, one_zsmul, add_comm, add_vadd]
      _ = D (m + (-(n : ℤ)) * N - N) := by rw [ih, hback]
      _ = D (m + ((-(n : ℤ)) - 1) * N) := by congr 1; ring

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- The gap source atom subtype is genuinely equivalent to its indexed
preimage, including exact source-centre equality. -/
private noncomputable def indexedPreimageValEquiv
    {source : Set Tiling.Plane} (Phi : ↥source ↪ Tiling.Plane)
    (Gap : Set Tiling.Plane) :
    {t : ↥source // Phi t ∈ Gap} ≃
      ↥(Set.image Subtype.val {t : ↥source | Phi t ∈ Gap}) :=
  Equiv.ofBijective
    (fun t => ⟨t.1.1, ⟨t.1, t.2, rfl⟩⟩) (by
      constructor
      · intro t s hts
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun x : ↥(Set.image Subtype.val {t : ↥source | Phi t ∈ Gap}) => x.1) hts
      · rintro ⟨x, t, ht, htx⟩
        exact ⟨⟨t, ht⟩, Subtype.ext htx⟩)

/-- Every normalized native atom is moved back to the original SELECTED
centres, with support transport by the combined normalization offset. -/
private theorem nativeAtom_selectedCoordinateTransport
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    {I : Type} (atom : I → Set Tiling.Plane)
    (hne : ∀ i, (atom i).Nonempty)
    (hdis : Set.PairwiseDisjoint Set.univ atom)
    (hcover : (⋃ i, atom i) = C.centres) :
    (∀ i, (t₀ +ᵥ atom i).Nonempty) ∧
      Set.PairwiseDisjoint Set.univ (fun i => t₀ +ᵥ atom i) ∧
      (⋃ i, t₀ +ᵥ atom i) = R.selectedCentres ∧
      ∀ i, regularSupport R.selectedRegion (t₀ +ᵥ atom i) =
        (v₀ + t₀) +ᵥ regularSupport C.region (atom i) := by
  constructor
  · intro i
    obtain ⟨x, hx⟩ := hne i
    exact ⟨t₀ + x, x, hx, rfl⟩
  constructor
  · intro i _ j _ hij
    change Disjoint (t₀ +ᵥ atom i) (t₀ +ᵥ atom j)
    rw [Set.disjoint_left]
    rintro z ⟨x, hx, hxt⟩ ⟨y, hy, hyt⟩
    have hxy : x = y := add_left_cancel (hxt.trans hyt.symm)
    exact Set.disjoint_left.mp (hdis (Set.mem_univ _) (Set.mem_univ _) hij)
      hx (hxy.symm ▸ hy)
  constructor
  · calc
      (⋃ i, t₀ +ᵥ atom i) = t₀ +ᵥ (⋃ i, atom i) := (Set.vadd_set_iUnion _ _).symm
      _ = t₀ +ᵥ C.centres := congrArg (t₀ +ᵥ ·) hcover
      _ = R.selectedCentres := by rw [hcentres, vadd_vadd, add_neg_cancel, zero_vadd]
  · intro i
    exact normalizedSelectedSupport_eq R v₀ t₀ C hK (atom i)

/-- The genuine quotient orbit has a well-defined original-centre union:
equality of quotient representatives gives equality of the full signed unions. -/
private theorem ungappedOrbitUnion_quotientIndependent
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts)
    (Q Q' : {A : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i A})
    (heq : Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G i) Q =
      Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G i) Q') :
    (⋃ m : ℤ, originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))) =
      ⋃ m : ℤ, originalSlice i (Q'.1.vadd (m • Dcmp.gamma.toPlane)) := by
  obtain ⟨n, hn⟩ := Quotient.exact heq
  rw [hn]
  exact (ungappedOrbitUnion_shift Dcmp originalSlice i Q.1 n).symm

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Actual gap-source permutation obtained by conjugating the image-period
permutation through the exact indexed/source preimage equivalence. -/
private theorem gapSourcePeriod_successor_exists
    {C : ApproximationContext.{0}}
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (hext : ∀ x : ControlledDisplacement C, f x.1 = mapPoint phi x)
    (Gap : Set Tiling.Plane) (hsub : Gap ⊆ Set.range Tphi)
    (eta : Tiling.Plane) (hperiod : eta +ᵥ Gap = Gap) :
    ∃ next : Equiv.Perm
        ↥(Set.image Subtype.val {t : ↥C.centres | Tphi t ∈ Gap}),
      ∀ t, f ((next t).1 - t.1) = eta := by
  classical
  obtain ⟨nextIndexed, hnextIndexed⟩ :=
    indexedImagePeriod_successor_exists Tphi Gap hsub eta hperiod
  let e := indexedPreimageValEquiv Tphi Gap
  let next : Equiv.Perm
      ↥(Set.image Subtype.val {t : ↥C.centres | Tphi t ∈ Gap}) :=
    e.symm.trans (nextIndexed.trans e)
  have hmapIndexed := indexedImagePeriod_sourceDisplacement
    phi Tphi hTphi f hext Gap eta nextIndexed hnextIndexed
  refine ⟨next, ?_⟩
  intro t
  let u := e.symm t
  have hbase : u.1.1 = t.1 := by
    have h := congrArg Subtype.val (e.apply_symm_apply t)
    exact h
  have hsuccessor : (next t).1 = (nextIndexed u).1.1 := rfl
  rw [hsuccessor, ← hbase]
  exact (hmapIndexed u).1

/-- Signed good-phase successors on the entire unrestricted dependent phase
index; finiteness is still neither assumed nor inferred. -/
private noncomputable def ungappedNativePhaseShiftEquiv
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (n : ℤ) :
    Equiv.Perm (Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}) :=
  Equiv.sigmaCongrRight (fun i => ungappedPhaseShiftEquiv Dcmp originalSlice G i n)

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open scoped Pointwise

private theorem correctedReplacementLattice_exists
    {A : Set Tiling.Plane} (v lambda gamma : Tiling.Plane) (k N : ℤ)
    (hkN : k ∣ N) (hN : N ≠ 0)
    (hli : LinearIndependent ℝ ![k • lambda, gamma])
    (hcoset : ∀ m n : ℤ, v + m • (k • lambda) + n • gamma ∈ A) :
    ∃ L : PlanarLattice, L.basis = ![N • lambda, gamma] ∧
      v +ᵥ (L.toAddSubgroup : Set Tiling.Plane) ⊆ A := by
  obtain ⟨p, rfl⟩ := hkN
  have hp : p ≠ 0 := right_ne_zero_of_mul hN
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp
  have hscale : (k * p) • lambda = (p : ℝ) • (k • lambda) := by
    rw [Int.cast_smul_eq_zsmul, ← mul_smul, mul_comm]
  have hli' : LinearIndependent ℝ ![(k * p) • lambda, gamma] := by
    rw [hscale]
    simpa only [one_smul] using
      (LinearIndependent.pair_smul_smul_iff
        (isUnit_iff_ne_zero.mpr hpR) (isUnit_one : IsUnit (1 : ℝ))).mpr hli
  let L : PlanarLattice := { basis := ![(k * p) • lambda, gamma], independent := hli' }
  refine ⟨L, rfl, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  change x ∈ AddSubgroup.closure (Set.range (![(k * p) • lambda, gamma])) at hx
  rw [Matrix.range_cons_cons_empty, AddSubgroup.mem_closure_pair] at hx
  obtain ⟨m, n, rfl⟩ := hx
  change v + (m • ((k * p) • lambda) + n • gamma) ∈ A
  simpa only [← mul_smul, mul_assoc, mul_comm p k, add_assoc] using hcoset (m * p) n

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Well-defined original-centre union indexed by the genuine signed phase
quotient. No representative finiteness or finite phase list occurs here. -/
private def ungappedOrbitCentres
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts) :
    Quotient (ungappedPhaseSetoid Dcmp originalSlice G i) → Set Tiling.Plane :=
  Quotient.lift
    (fun Q => ⋃ m : ℤ, originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane)))
    (by
      rintro Q Q' ⟨n, hn⟩
      rw [hn]
      exact (ungappedOrbitUnion_shift Dcmp originalSlice i Q.1 n).symm)

/-- A native alpha is a literal period of the ORIGINAL orbit centre union.
No transverse support shift is substituted for a centre period. -/
private theorem ungappedOrbitCentres_nativePeriod
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts)
    (Q : {A : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i A})
    (alpha : Tiling.Plane)
    (hperiod : ∀ m : ℤ, alpha +ᵥ originalSlice i
      (Q.1.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))) :
    alpha +ᵥ ungappedOrbitCentres Dcmp originalSlice G i
      (Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G i) Q) =
      ungappedOrbitCentres Dcmp originalSlice G i
        (Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G i) Q) := by
  change alpha +ᵥ (⋃ m : ℤ, originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))) =
    ⋃ m : ℤ, originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))
  rw [Set.vadd_set_iUnion]
  exact Set.iUnion_congr hperiod

end Tiling.AxisParallel.Terminal
open scoped Pointwise

namespace Tiling.AxisParallel.Terminal

/-- These two periods belong to the repeated replacement centres, not to an
original orbit-centre set. Scaling the integral identity by the divisibility
witness avoids cancellation and also covers `N = 0`. -/
private theorem residueRepetition_twoPeriods
    (N : ℕ) (slice : Fin N → Set Tiling.Plane)
    (alpha gamma lambda : Tiling.Plane) (k l : ℤ)
    (hkN : k ∣ (N : ℤ))
    (hAlpha : ∀ r, alpha +ᵥ slice r = slice r)
    (hIntegral : k • lambda = ((N : ℤ) ^ 2) • alpha - ((N : ℤ) * l) • gamma) :
    let replacement := ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice r
    gamma +ᵥ replacement = replacement ∧
      ((N : ℤ) • lambda) +ᵥ replacement = replacement := by
  let replacement := ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice r
  change gamma +ᵥ replacement = replacement ∧
    ((N : ℤ) • lambda) +ᵥ replacement = replacement
  have hGamma : gamma +ᵥ replacement = replacement := by
    dsimp [replacement]
    simp_rw [Set.vadd_set_iUnion]
    apply Set.iUnion_congr
    intro r
    have hshift (q : ℤ) :
        gamma +ᵥ ((q • gamma) +ᵥ slice r) = ((q + 1) • gamma) +ᵥ slice r := by
      rw [add_smul, one_smul, add_comm (q • gamma), add_vadd]
    simp_rw [hshift]
    exact (show Function.Surjective (fun q : ℤ => q + 1) from
      fun q => ⟨q - 1, sub_add_cancel q 1⟩).iUnion_comp
        (fun q : ℤ => (q • gamma) +ᵥ slice r)
  have hAlphaReplacement : alpha +ᵥ replacement = replacement := by
    dsimp [replacement]
    simp_rw [Set.vadd_set_iUnion]
    apply Set.iUnion_congr
    intro r
    apply Set.iUnion_congr
    intro q
    rw [← add_vadd, add_comm alpha, add_vadd, hAlpha r]
  obtain ⟨p, hp⟩ := hkN
  have hScaled : (N : ℤ) • lambda =
      (p * (N : ℤ) ^ 2) • alpha - (p * ((N : ℤ) * l)) • gamma := by
    calc
      (N : ℤ) • lambda = p • (k • lambda) := by
        rw [smul_smul, mul_comm p k, ← hp]
      _ = (p * (N : ℤ) ^ 2) • alpha - (p * ((N : ℤ) * l)) • gamma := by
        rw [hIntegral, smul_sub, smul_smul, smul_smul]
  have hAlphaMem : alpha ∈ Tiling.AxisParallel.periodGroup replacement :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup replacement alpha).mpr hAlphaReplacement
  have hGammaMem : gamma ∈ Tiling.AxisParallel.periodGroup replacement :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup replacement gamma).mpr hGamma
  refine ⟨hGamma, ?_⟩
  rw [hScaled]
  apply (Tiling.AxisParallel.periodGroup_isAddSubgroup replacement _).mp
  exact sub_mem
    ((Tiling.AxisParallel.periodGroup replacement).zsmul_mem hAlphaMem _)
    ((Tiling.AxisParallel.periodGroup replacement).zsmul_mem hGammaMem _)

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem ungappedOrbitCentres_membership
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (G : ℝ) (i : Fin Dcmp.numberOfParts)
    (o : Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)) (x : Tiling.Plane) :
    x ∈ ungappedOrbitCentres Dcmp originalSlice G i o ↔
      ∃ Q : {A : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i A},
        Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G i) Q = o ∧
          x ∈ originalSlice i Q.1 := by
  refine Quotient.inductionOn o ?_
  intro Q₀
  constructor
  · intro hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    let Q := ungappedPhaseShiftEquiv Dcmp originalSlice G i m Q₀
    refine ⟨Q, ?_, hm⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨m, rfl⟩
  · rintro ⟨Q, heq, hx⟩
    have horbit := congrArg (ungappedOrbitCentres Dcmp originalSlice G i) heq
    rw [← horbit]
    change x ∈ ⋃ m : ℤ, originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))
    apply Set.mem_iUnion.mpr
    refine ⟨0, ?_⟩
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hx

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem selectedTerminalConstruction_transverseSynchronization
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (hext : ∀ x : ControlledDisplacement C, f x.1 = mapPoint phi x)
    (hinj : Set.InjOn f C.translatedVertices)
    {Kphi : Region}
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (G : ℝ) (N : ℤ)
    (hGapGamma : Tiling.RationalPolygonal.SetPeriodicBy
      (⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G)
      (N • Dcmp.gamma.toPlane))
    (hBetasN : ∀ (i : Fin Dcmp.numberOfParts)
        (Q : RationalSlice (Dcmp.direction i)),
      IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      ∃ b : ControlledDisplacement C,
        regularSupport C.region (originalSlice i (Q.vadd (N • Dcmp.gamma.toPlane))) =
          b.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi b = N • Dcmp.gamma.toPlane) :
    let GapSource := Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈
        ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G}
    ∃ gamma : Tiling.Plane, f gamma = N • Dcmp.gamma.toPlane ∧
      gamma +ᵥ GapSource = GapSource ∧
      ∀ (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)),
        IsUngappedOrbitPhase Dcmp originalSlice G i Q →
        gamma +ᵥ regularSupport C.region (originalSlice i Q) =
          regularSupport C.region (originalSlice i (Q.vadd (N • Dcmp.gamma.toPlane))) := by
  classical
  let Gap := ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G
  let GapSource := Set.image Subtype.val {t : ↥C.centres | Tphi t ∈ Gap}
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  let Slice : GoodIndex → Set Tiling.Plane := fun s => originalSlice s.1 s.2.1
  have hphase (s : GoodIndex) : s.2.1 ∈ (Dcmp.orbit s.1).phases := by
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using (s.2.2 0).1
  have hSlice : Slice = fun s : GoodIndex => Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ s.2.1.centres (Dcmp.part s.1)} := by
    funext s
    exact hPreimage s.1 s.2.1 (hphase s)
  have hparts := selectedTerminalConstruction_partitionPrefix
    Dcmp Tphi rfl originalSlice G
  have hSliceNonempty : ∀ s, (Slice s).Nonempty := by
    rw [hSlice]
    exact hparts.1
  have hSliceDisjoint : Set.PairwiseDisjoint Set.univ Slice := by
    rw [hSlice]
    exact hparts.2.1
  have hGapDisjoint : Disjoint GapSource (⋃ s, Slice s) := by
    rw [hSlice]
    exact hparts.2.2.1
  have hcover : GapSource ∪ (⋃ s, Slice s) = C.centres := by
    rw [hSlice]
    exact hparts.2.2.2
  let atom : Sum ↥GapSource GoodIndex → Set Tiling.Plane :=
    Sum.elim (fun t => {t.1}) Slice
  obtain ⟨hatomNonempty, hatomDisjoint, hatomCover⟩ :=
    nativeAtomPartition C.centres GapSource Slice
      hSliceNonempty hSliceDisjoint hGapDisjoint hcover
  have hGapSubset : Gap ⊆ Set.range Tphi := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp hi
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hQ
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.mpr ⟨i, hn.1⟩
  have hGapPeriod : (N • Dcmp.gamma.toPlane) +ᵥ Gap = Gap := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [vadd_eq_add, add_comm] using (hGapGamma y).mpr hy
    · intro hx
      refine ⟨x - N • Dcmp.gamma.toPlane, ?_, ?_⟩
      · exact (hGapGamma _).mp (by simpa only [sub_add_cancel] using hx)
      · simp only [vadd_eq_add]
        abel
  obtain ⟨nextGap, hnextGap⟩ := gapSourcePeriod_successor_exists
    phi Tphi hTphi f hext Gap hGapSubset (N • Dcmp.gamma.toPlane) hGapPeriod
  let nextGood : Equiv.Perm GoodIndex :=
    ungappedNativePhaseShiftEquiv Dcmp originalSlice G N
  let next : Equiv.Perm (Sum ↥GapSource GoodIndex) :=
    Equiv.sumCongr nextGap nextGood
  let beta : GoodIndex → ControlledDisplacement C := fun s =>
    (hBetasN s.1 s.2.1 s.2.2).choose
  have hbeta (s : GoodIndex) := (hBetasN s.1 s.2.1 s.2.2).choose_spec
  let displacement : Sum ↥GapSource GoodIndex → Tiling.Plane :=
    Sum.elim (fun t => (nextGap t).1 - t.1) (fun s => (beta s).1)
  have hmapDisplacement : ∀ a, f (displacement a) = N • Dcmp.gamma.toPlane := by
    intro a
    cases a with
    | inl t => exact hnextGap t
    | inr s => exact (hext (beta s)).trans (hbeta s).2
  have htranslate : ∀ a, displacement a +ᵥ regularSupport C.region (atom a) =
      regularSupport C.region (atom (next a)) := by
    intro a
    cases a with
    | inl t =>
      change ((nextGap t).1 - t.1) +ᵥ regularSupport C.region {t.1} =
        regularSupport C.region {(nextGap t).1}
      rw [← regularSupport_vadd]
      congr 1
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_singleton_iff, vadd_eq_add]
      constructor <;> intro hx <;> linear_combination hx
    | inr s => exact (hbeta s).1.symm
  obtain ⟨hselectedNonempty, hselectedDisjoint, hselectedCover, hselectedSupport⟩ :=
    nativeAtom_selectedCoordinateTransport R v₀ t₀ C hK hcentres atom
      hatomNonempty hatomDisjoint hatomCover
  have hselectedTranslate (a : Sum ↥GapSource GoodIndex) :
      displacement a +ᵥ regularSupport R.selectedRegion (t₀ +ᵥ atom a) =
        regularSupport R.selectedRegion (t₀ +ᵥ atom (next a)) := by
    rw [hselectedSupport a, hselectedSupport (next a)]
    calc
      displacement a +ᵥ ((v₀ + t₀) +ᵥ regularSupport C.region (atom a)) =
          (v₀ + t₀) +ᵥ (displacement a +ᵥ regularSupport C.region (atom a)) := by
        rw [vadd_vadd, vadd_vadd, add_comm (displacement a)]
      _ = (v₀ + t₀) +ᵥ regularSupport C.region (atom (next a)) := by
        rw [htranslate a]
  obtain ⟨gamma, hdisplacement⟩ := atomDisplacements_synchronize R
    (fun a => t₀ +ᵥ atom a) hselectedNonempty hselectedDisjoint hselectedCover
    next displacement (fun x => f (x - (v₀ + t₀))) (N • Dcmp.gamma.toPlane)
    hselectedTranslate (by
      intro a x _hx _htarget
      rw [show x + displacement a - (v₀ + t₀) =
        (x - (v₀ + t₀)) + displacement a by abel, map_add, hmapDisplacement a])
    (selectedDecoratedMap_injOn R v₀ t₀ C hK hcentres f hinj)
  have hselected : R.selectedCentres.Nonempty := by
    cases haxis : R.orientation with
    | vertical => simpa [R.selectedCentres_vertical haxis] using R.centres_nonempty
    | horizontal =>
      rw [R.selectedCentres_horizontal haxis]
      exact R.centres_nonempty.image coordinateSwap
  obtain ⟨x, hx⟩ := hselected
  obtain ⟨a, _ha⟩ := Set.mem_iUnion.mp (hselectedCover.symm ▸ hx)
  have hmapGamma : f gamma = N • Dcmp.gamma.toPlane := by
    rw [← hdisplacement a]
    exact hmapDisplacement a
  have hgapShift (t : ↥GapSource) : gamma +ᵥ t.1 = (nextGap t).1 := by
    have h := hdisplacement (Sum.inl t)
    change (nextGap t).1 - t.1 = gamma at h
    rw [vadd_eq_add, ← h]
    abel
  refine ⟨gamma, hmapGamma, ?_, ?_⟩
  · change gamma +ᵥ GapSource = GapSource
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      change gamma +ᵥ t ∈ GapSource
      rw [hgapShift ⟨t, ht⟩]
      exact (nextGap ⟨t, ht⟩).2
    · intro hx
      let t : ↥GapSource := ⟨x, hx⟩
      refine ⟨(nextGap.symm t).1, (nextGap.symm t).2, ?_⟩
      change gamma +ᵥ (nextGap.symm t).1 = x
      rw [hgapShift, nextGap.apply_symm_apply]
  · intro i Q hgood
    let s : GoodIndex := ⟨i, Q, hgood⟩
    have h := htranslate (Sum.inr s)
    rw [hdisplacement (Sum.inr s)] at h
    exact h

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Signed Euclidean residue exhaustion of support phases. In particular,
negative phase indices are included; there is no finite phase-list hypothesis. -/
private theorem residueRepetition_supportUnion
    (N : ℕ) (hN : 0 < N) (D : ℤ → Set Tiling.Plane) (gamma : Tiling.Plane)
    (hstep : ∀ m : ℤ, gamma +ᵥ D m = D (m + (N : ℤ))) :
    (⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ D (r.1 : ℤ)) = ⋃ m : ℤ, D m := by
  have hNpos : 0 < (N : ℤ) := by exact_mod_cast hN
  have hiterate := signedSupportIteration D gamma (N : ℤ) hstep
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hr
    exact Set.mem_iUnion.mpr ⟨(r.1 : ℤ) + q * (N : ℤ), by
      rwa [hiterate q (r.1 : ℤ)] at hq⟩
  · intro hx
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    have hrem : 0 ≤ m % (N : ℤ) := Int.emod_nonneg m (ne_of_gt hNpos)
    have hremLt : m % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos m hNpos
    let r : Fin N := ⟨(m % (N : ℤ)).toNat, (Int.toNat_lt hrem).mpr hremLt⟩
    have hr : (r.1 : ℤ) = m % (N : ℤ) := Int.toNat_of_nonneg hrem
    have hindex : (r.1 : ℤ) + (m / (N : ℤ)) * (N : ℤ) = m := by
      rw [hr]
      simpa only [mul_comm] using Int.emod_add_mul_ediv m (N : ℤ)
    apply Set.mem_iUnion.mpr
    refine ⟨r, Set.mem_iUnion.mpr ⟨m / (N : ℤ), ?_⟩⟩
    rw [hiterate, hindex]
    exact hm

/-- The NEW residue-repeat centres have exactly the regularized support of the
ORIGINAL signed phase union. This states no literal equality of their centres. -/
private theorem residueRepetition_regularSupport
    (K : Region) (N : ℕ) (hN : 0 < N)
    (slice : ℤ → Set Tiling.Plane) (gamma : Tiling.Plane)
    (hstep : ∀ m : ℤ,
      gamma +ᵥ regularSupport K (slice m) =
        regularSupport K (slice (m + (N : ℤ)))) :
    regularSupport K (⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice (r.1 : ℤ)) =
      regularSupport K (⋃ m : ℤ, slice m) := by
  let newSlice : Fin N × ℤ → Set Tiling.Plane :=
    fun p => (p.2 • gamma) +ᵥ slice (p.1.1 : ℤ)
  have hcentres : (⋃ p, newSlice p) =
      ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice (r.1 : ℤ) :=
    Set.iUnion_prod' newSlice
  rw [← hcentres, Tiling.AxisParallel.regularSupport_iUnion K newSlice,
    Tiling.AxisParallel.regularSupport_iUnion K slice]
  apply congrArg (fun D : Set Tiling.Plane => interior (closure D))
  rw [Set.iUnion_prod']
  simp only [newSlice, regularSupport_vadd]
  exact residueRepetition_supportUnion N hN
    (fun m => regularSupport K (slice m)) gamma hstep

/-- Support-preserving replacement packing has the SAME a.e. target as the old
tiling. Countability follows from packing; raw open unions are compared a.e. -/
private theorem tilesOn_of_replacementPacking_and_regularSupport_eq
    {K : Region} {old new target : Set Tiling.Plane}
    (hOld : TilesOn K old target)
    (hNewPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements new))
    (hSupport : regularSupport K new = regularSupport K old) :
    TilesOn K new target := by
  refine ⟨(IsPacking.locallyFinite_centres hNewPacking).2, hNewPacking, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hNewPacking,
    openUnion_aeEq_regularSupport hOld.2.1, hOld.2.2] with x hnew hold htarget
  rw [hSupport] at hnew
  change (x ∈ openUnion K new) = (x ∈ regularSupport K old) at hnew
  change (x ∈ openUnion K old) = (x ∈ regularSupport K old) at hold
  simp only [openUnion, Tiling.Polygonal.openUnion,
    ← Region.openCarrier.eq_def, Set.mem_iUnion] at hnew hold
  exact htarget.trans ((Iff.of_eq hold).trans (Iff.of_eq hnew).symm)

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Grouping the unrestricted good-phase partition by its actual signed
quotient preserves nonemptiness, disjointness, and the exact source cover. -/
private theorem ungappedOrbitCentres_partition
    {C : ApproximationContext.{0}} {Kphi : Region}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (G : ℝ) :
    let OrbitIndex := Σ i : Fin Dcmp.numberOfParts,
      Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)
    let Orbit : OrbitIndex → Set Tiling.Plane := fun o =>
      ungappedOrbitCentres Dcmp originalSlice G o.1 o.2
    let GapSource := Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}
    (∀ o, (Orbit o).Nonempty) ∧
      Set.PairwiseDisjoint Set.univ Orbit ∧
      Disjoint GapSource (⋃ o, Orbit o) ∧
      GapSource ∪ (⋃ o, Orbit o) = C.centres := by
  classical
  dsimp only
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  let Slice : GoodIndex → Set Tiling.Plane := fun s =>
    Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ s.2.1.centres (Dcmp.part s.1)}
  let OrbitIndex := Σ i : Fin Dcmp.numberOfParts,
    Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)
  let Orbit : OrbitIndex → Set Tiling.Plane := fun o =>
    ungappedOrbitCentres Dcmp originalSlice G o.1 o.2
  let orbitClass : GoodIndex → OrbitIndex := fun s =>
    ⟨s.1, Quotient.mk (ungappedPhaseSetoid Dcmp originalSlice G s.1) s.2⟩
  obtain ⟨hSliceNonempty, hSliceDisjoint, hGapDisjoint, hCover⟩ :=
    selectedTerminalConstruction_partitionPrefix Dcmp Tphi rfl originalSlice G
  have hphase (s : GoodIndex) : s.2.1 ∈ (Dcmp.orbit s.1).phases := by
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero]
      using (s.2.2 (0 : ℤ)).1
  have hSliceOrbit (s : GoodIndex) (x : Tiling.Plane) (hx : x ∈ Slice s) :
      x ∈ Orbit (orbitClass s) := by
    apply (ungappedOrbitCentres_membership Dcmp originalSlice G s.1 _ x).mpr
    refine ⟨s.2, rfl, ?_⟩
    rw [hPreimage s.1 s.2.1 (hphase s)]
    exact hx
  have hOrbitSlice (o : OrbitIndex) (x : Tiling.Plane) (hx : x ∈ Orbit o) :
      ∃ s : GoodIndex, orbitClass s = o ∧ x ∈ Slice s := by
    obtain ⟨Q, hQ, hxQ⟩ :=
      (ungappedOrbitCentres_membership Dcmp originalSlice G o.1 o.2 x).mp hx
    refine ⟨⟨o.1, Q⟩, ?_, ?_⟩
    · exact congrArg (Sigma.mk o.1) hQ
    · rwa [hPreimage o.1 Q.1 (hphase ⟨o.1, Q⟩)] at hxQ
  have hUnion : (⋃ o, Orbit o) = ⋃ s, Slice s := by
    ext x
    constructor
    · intro hx
      obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hx
      obtain ⟨s, _hs, hxS⟩ := hOrbitSlice o x ho
      exact Set.mem_iUnion.mpr ⟨s, hxS⟩
    · intro hx
      obtain ⟨s, hs⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨orbitClass s, hSliceOrbit s x hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨i, o⟩
    refine Quotient.inductionOn o ?_
    intro Q
    obtain ⟨x, hx⟩ := hSliceNonempty ⟨i, Q⟩
    exact ⟨x, hSliceOrbit ⟨i, Q⟩ x hx⟩
  · intro o _ho p _hp hop
    apply Set.disjoint_left.mpr
    intro x hxo hxp
    obtain ⟨s, hs, hxS⟩ := hOrbitSlice o x hxo
    obtain ⟨t, ht, hxT⟩ := hOrbitSlice p x hxp
    have hst : s = t := by
      by_contra hne
      exact Set.disjoint_left.mp
        (hSliceDisjoint (Set.mem_univ s) (Set.mem_univ t) hne) hxS hxT
    exact hop (hs.symm.trans ((congrArg orbitClass hst).trans ht))
  · rw [hUnion]
    exact hGapDisjoint
  · rw [hUnion]
    exact hCover

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Every tile in an actual centre subfamily lies inside that subfamily's
regular-open support. This uses openness, not a support-to-centre inference. -/
private theorem tileOpen_subset_regularSupport
    (K : Region) (S : Set Tiling.Plane) (t : Tiling.Plane) (ht : t ∈ S) :
    t +ᵥ K.openCarrier ⊆ regularSupport K S := by
  have hsub : t +ᵥ K.openCarrier ⊆ openUnion K S :=
    subset_iUnion (fun s : S => s.1 +ᵥ K.openCarrier) ⟨t, ht⟩
  calc
    t +ᵥ K.openCarrier = interior (t +ᵥ K.openCarrier) :=
      (isOpen_interior.vadd t).interior_eq.symm
    _ ⊆ interior (closure (openUnion K S)) := interior_mono (hsub.trans subset_closure)

/-- Packing is preserved under one literal common centre translation. -/
private theorem isPacking_centres_vadd
    (K : Region) (S : Set Tiling.Plane) (a : Tiling.Plane)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (a +ᵥ S)) := by
  apply (isPacking_iff_openCarrier_disjoint K _).mpr
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ hst
  have hne : s ≠ t := fun h => hst (congrArg (a + ·) h)
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hzS' : z - a ∈ s +ᵥ K.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzS ⊢
    convert hzS using 1
    simp only [vadd_eq_add]
    abel
  have hzT' : z - a ∈ t +ᵥ K.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzT ⊢
    convert hzT using 1
    simp only [vadd_eq_add]
    abel
  exact Set.disjoint_left.mp
    ((isPacking_iff_openCarrier_disjoint K S).mp hpack hs ht hne) hzS' hzT'

/-- Actual packing pieces with disjoint regular supports form a packing. -/
private theorem isPacking_iUnion_of_regularSupportDisjoint
    {I : Type} (K : Region) (S : I → Set Tiling.Plane)
    (hpack : ∀ i, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (S i)))
    (hdis : Set.PairwiseDisjoint Set.univ (fun i => regularSupport K (S i))) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (⋃ i, S i)) := by
  apply (isPacking_iff_openCarrier_disjoint K _).mpr
  intro s hs t ht hst
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hs
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp ht
  by_cases hij : i = j
  · subst j
    exact (isPacking_iff_openCarrier_disjoint K _).mp (hpack i) hi hj hst
  · exact (hdis (Set.mem_univ i) (Set.mem_univ j) hij).mono
      (tileOpen_subset_regularSupport K (S i) s hi)
      (tileOpen_subset_regularSupport K (S j) t hj)

/-- Integer residue coordinates parametrize signed phases injectively. -/
private theorem signedResidueIndex_injective
    (N : ℕ) (hN : 0 < N) :
    Function.Injective
      (fun p : Fin N × ℤ => (p.1.1 : ℤ) + p.2 * (N : ℤ)) := by
  have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hrem (p : Fin N × ℤ) :
      ((p.1.1 : ℤ) + p.2 * (N : ℤ)) % (N : ℤ) = (p.1.1 : ℤ) := by
    rw [Int.add_mul_emod_self_right]
    exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast p.1.2)
  intro p q hpq
  dsimp only at hpq
  have hfirst : p.1 = q.1 := by
    apply Fin.ext
    have h := congrArg (fun m : ℤ => m % (N : ℤ)) hpq
    rw [hrem, hrem] at h
    exact_mod_cast h
  apply Prod.ext hfirst
  have hsecond : p.2 * (N : ℤ) = q.2 * (N : ℤ) := by
    rw [hfirst] at hpq
    exact add_left_cancel hpq
  exact mul_right_cancel₀ hNne hsecond

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem tilesOn_regularSupport_of_packing
    (K : Region) (S : Set Tiling.Plane)
    (hpack : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements S)) :
    TilesOn K S (regularSupport K S) := by
  refine ⟨(IsPacking.locallyFinite_centres hpack).2, hpack, ?_⟩
  filter_upwards [openUnion_aeEq_regularSupport hpack] with x hx
  change (x ∈ openUnion K S) = (x ∈ regularSupport K S) at hx
  apply Iff.of_eq
  rw [← hx, openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]

/-- The NEW signed residue-repeat centres form a packing and tile the regular
support of the ORIGINAL phase union. The old phase family is countable because
it is indexed by ℤ; no orbit finiteness is used here. -/
private theorem residueRepetition_packing_tilesOn
    (K : Region) (N : ℕ) (hN : 0 < N)
    (slice : ℤ → Set Tiling.Plane) (gamma : Tiling.Plane)
    (hOldPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (⋃ m, slice m)))
    (hOldDisjoint : Set.PairwiseDisjoint Set.univ slice)
    (hstep : ∀ m : ℤ, gamma +ᵥ regularSupport K (slice m) =
      regularSupport K (slice (m + (N : ℤ)))) :
    let replacement := ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice (r.1 : ℤ)
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
        (K.toPolygonalRegion.placements replacement) ∧
      TilesOn K replacement (regularSupport K (⋃ m : ℤ, slice m)) := by
  let newSlice : Fin N × ℤ → Set Tiling.Plane :=
    fun p => (p.2 • gamma) +ᵥ slice (p.1.1 : ℤ)
  have hcentres : (⋃ p, newSlice p) =
      ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ slice (r.1 : ℤ) :=
    Set.iUnion_prod' newSlice
  have hOldTiles := tilesOn_regularSupport_of_packing K (⋃ m, slice m) hOldPacking
  have hOldSupportDisjoint :=
    (regularSupport_pairwiseDisjoint slice hOldDisjoint rfl hOldTiles).1
  have hSlicePacking (m : ℤ) : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (slice m)) := by
    intro x hx y hy hxy
    exact hOldPacking (Set.mem_iUnion.mpr ⟨m, hx⟩)
      (Set.mem_iUnion.mpr ⟨m, hy⟩) hxy
  have hNewSlicePacking (p : Fin N × ℤ) : Tiling.IsPacking
      K.toPolygonalRegion.prototileFamily (K.toPolygonalRegion.placements (newSlice p)) :=
    isPacking_centres_vadd K (slice (p.1.1 : ℤ)) (p.2 • gamma) (hSlicePacking _)
  have hNewSupport (p : Fin N × ℤ) :
      regularSupport K (newSlice p) =
        regularSupport K (slice ((p.1.1 : ℤ) + p.2 * (N : ℤ))) := by
    dsimp only [newSlice]
    rw [regularSupport_vadd]
    exact signedSupportIteration (fun m => regularSupport K (slice m))
      gamma (N : ℤ) hstep p.2 (p.1.1 : ℤ)
  have hNewDisjoint : Set.PairwiseDisjoint Set.univ
      (fun p : Fin N × ℤ => regularSupport K (newSlice p)) := by
    intro p _ q _ hpq
    change Disjoint (regularSupport K (newSlice p)) (regularSupport K (newSlice q))
    rw [hNewSupport p, hNewSupport q]
    exact hOldSupportDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (fun h => hpq (signedResidueIndex_injective N hN h))
  have hNewPacking := isPacking_iUnion_of_regularSupportDisjoint
    K newSlice hNewSlicePacking hNewDisjoint
  rw [hcentres] at hNewPacking
  refine ⟨hNewPacking, ?_⟩
  exact tilesOn_of_replacementPacking_and_regularSupport_eq hOldTiles hNewPacking
    (residueRepetition_regularSupport K N hN slice gamma hstep)

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

private theorem rationalDirectional_phaseShift_injective
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i)) :
    Function.Injective (fun m : ℤ => Q.vadd (m • Dcmp.gamma.toPlane)) := by
  intro m n hmn
  have hquot := add_left_cancel (show
      Q + QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
          (m • Dcmp.gamma.toPlane) =
      Q + QuotientAddGroup.mk' (realDirectionSubgroup (Dcmp.direction i))
          (n • Dcmp.gamma.toPlane) from hmn)
  have hmem : (m - n) • Dcmp.gamma.toPlane ∈
      realDirectionSubgroup (Dcmp.direction i) := by
    simpa only [sub_smul] using QuotientAddGroup.eq_iff_sub_mem.mp hquot
  obtain ⟨r, hr⟩ := hmem
  have hdir : (Dcmp.direction i).toPlane =
      Dcmp.lambdaCoefficient i • Dcmp.lambda.toPlane +
      Dcmp.gammaCoefficient i • Dcmp.gamma.toPlane := by
    change ((Dcmp.direction i).coordinates 0 : ℝ) +
        (Dcmp.direction i).coordinates 1 * Complex.I = _
    rw [Dcmp.direction_coordinates i]
    apply Complex.ext
    · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
        Complex.add_re, Complex.mul_re]
    · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
        Complex.add_im, Complex.mul_im]
  have hrel : (r * (Dcmp.lambdaCoefficient i : ℝ)) • Dcmp.lambda.toPlane +
      (r * (Dcmp.gammaCoefficient i : ℝ) - ((m - n : ℤ) : ℝ)) •
        Dcmp.gamma.toPlane = 0 := by
    rw [hdir] at hr
    simp only [← Int.cast_smul_eq_zsmul (R := ℝ)] at hr
    calc
      _ = r • ((Dcmp.lambdaCoefficient i : ℝ) • Dcmp.lambda.toPlane +
          (Dcmp.gammaCoefficient i : ℝ) • Dcmp.gamma.toPlane) -
          ((m - n : ℤ) : ℝ) • Dcmp.gamma.toPlane := by module
      _ = 0 := by rw [← hr, sub_self]
  obtain ⟨hrk, ht⟩ := LinearIndependent.pair_iff.mp Dcmp.basisIndependent _ _ hrel
  have hk : (Dcmp.lambdaCoefficient i : ℝ) ≠ 0 := by
    exact_mod_cast Dcmp.lambdaCoefficient_ne_zero i
  have hr0 : r = 0 := (mul_eq_zero.mp hrk).resolve_right hk
  have hmn0 : (m - n : ℤ) = 0 := by
    have hcast : ((m - n : ℤ) : ℝ) = 0 := by simpa only [hr0, zero_mul, zero_sub,
      neg_eq_zero] using ht
    exact_mod_cast hcast
  exact sub_eq_zero.mp hmn0

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

private theorem weaklyPeriodic_finite_disjoint_iUnion
    {n : ℕ} (S : Fin n → Set Tiling.Plane)
    (hdisjoint : Set.PairwiseDisjoint Set.univ S)
    (hweak : ∀ i, Tiling.RationalPolygonal.WeaklyPeriodic (S i)) :
    Tiling.RationalPolygonal.WeaklyPeriodic (⋃ i, S i) := by
  classical
  let D (i : Fin n) : Tiling.RationalPolygonal.WeakPeriodicDecomposition (S i) :=
    Classical.choice (hweak i)
  let J := Σ i : Fin n, Fin (D i).numberOfParts
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hsubset (i : Fin n) (j : Fin (D i).numberOfParts) :
      (D i).part j ⊆ S i := by
    intro x hx
    rw [← (D i).iUnion_parts]
    exact Set.mem_iUnion.mpr ⟨j, hx⟩
  have hflat (a b : J) (hab : a ≠ b) :
      Disjoint ((D a.1).part a.2) ((D b.1).part b.2) := by
    rcases a with ⟨i, k⟩
    rcases b with ⟨j, l⟩
    by_cases hij : i = j
    · subst j
      apply (D i).pairwiseDisjoint (Set.mem_univ k) (Set.mem_univ l)
      intro hkl
      apply hab
      cases hkl
      rfl
    · exact (hdisjoint (Set.mem_univ i) (Set.mem_univ j) hij).mono
        (hsubset i k) (hsubset j l)
  refine ⟨{
    numberOfParts := Fintype.card J
    part := fun k ↦ (D (e k).1).part (e k).2
    period := fun k ↦ (D (e k).1).period (e k).2
    period_ne_zero := fun k ↦ (D (e k).1).period_ne_zero (e k).2
    periodic_part := fun k ↦ (D (e k).1).periodic_part (e k).2
    pairwiseDisjoint := ?_
    iUnion_parts := ?_ }⟩
  · intro i _ j _ hij
    exact hflat (e i) (e j) (fun h ↦ hij (e.injective h))
  · ext x
    constructor
    · intro hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨(e k).1, hsubset (e k).1 (e k).2 hxk⟩
    · intro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      rw [← (D i).iUnion_parts] at hxi
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxi
      refine Set.mem_iUnion.mpr ⟨e.symm ⟨i, j⟩, ?_⟩
      rw [e.apply_symm_apply]
      exact hxj

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem selectedTerminalConstruction_longitudinalSynchronization
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    (phi : C.coordinateSpace →ₗ[ℚ] ℚ) (Tphi : ↥C.centres ↪ Tiling.Plane)
    (hTphi : ∀ t, Tphi t = mapPoint phi (C.centrePoint t.1 t.2))
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (hext : ∀ x : ControlledDisplacement C, f x.1 = mapPoint phi x)
    (hinj : Set.InjOn f C.translatedVertices)
    {Kphi : Region}
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (G : ℝ) (N : ℤ) (hN : N ≠ 0)
    (hdivide : ∀ i, Dcmp.lambdaCoefficient i ∣ N)
    (gamma : Tiling.Plane) (hmapGamma : f gamma = N • Dcmp.gamma.toPlane)
    (hGammaSupport : ∀ i Q, IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      gamma +ᵥ regularSupport C.region (originalSlice i Q) =
        regularSupport C.region (originalSlice i (Q.vadd (N • Dcmp.gamma.toPlane))))
    (hGapLambda : Tiling.RationalPolygonal.SetPeriodicBy
      (⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G)
      (N • Dcmp.lambda.toPlane))
    (alpha : (Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}) → ControlledDisplacement C)
    (hAlphaMap : ∀ s, mapPoint phi (alpha s) = (Dcmp.direction s.1).toPlane)
    (hAlphaPeriod : ∀ s (m : ℤ), (alpha s).1 +ᵥ
      originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane))) :
    let GapSource := Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈
        ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G}
    ∃ lambda : Tiling.Plane,
      f lambda = (N ^ 2) • Dcmp.lambda.toPlane ∧
      lambda +ᵥ GapSource = GapSource ∧
      ∀ s, Dcmp.lambdaCoefficient s.1 • lambda =
        (N ^ 2) • (alpha s).1 - (N * Dcmp.gammaCoefficient s.1) • gamma := by
  classical
  let Gap := ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G
  let GapSource := Set.image Subtype.val {t : ↥C.centres | Tphi t ∈ Gap}
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  let Slice : GoodIndex → Set Tiling.Plane := fun s => originalSlice s.1 s.2.1
  let p : Fin Dcmp.numberOfParts → ℤ := fun i => (hdivide i).choose
  have hp (i : Fin Dcmp.numberOfParts) :
      Dcmp.lambdaCoefficient i * p i = N := (hdivide i).choose_spec.symm
  have hpne (i : Fin Dcmp.numberOfParts) : p i ≠ 0 :=
    right_ne_zero_of_mul (hp i ▸ hN)
  have hDirection (i : Fin Dcmp.numberOfParts) :
      (Dcmp.direction i).toPlane =
        Dcmp.lambdaCoefficient i • Dcmp.lambda.toPlane +
          Dcmp.gammaCoefficient i • Dcmp.gamma.toPlane := by
    change ((Dcmp.direction i).coordinates 0 : ℝ) +
      (Dcmp.direction i).coordinates 1 * Complex.I = _
    rw [Dcmp.direction_coordinates i]
    apply Complex.ext
    · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
        Complex.add_re, Complex.mul_re]
    · simp [RationalDirection.toPlane, RationalDirection.linearCombination,
        Complex.add_im, Complex.mul_im]
  have hphase (s : GoodIndex) : s.2.1 ∈ (Dcmp.orbit s.1).phases := by
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using (s.2.2 0).1
  have hSlice : Slice = fun s : GoodIndex => Set.image Subtype.val
      {t : ↥C.centres | Tphi t ∈ s.2.1.centres (Dcmp.part s.1)} := by
    funext s
    exact hPreimage s.1 s.2.1 (hphase s)
  have hparts := selectedTerminalConstruction_partitionPrefix
    Dcmp Tphi rfl originalSlice G
  have hSliceNonempty : ∀ s, (Slice s).Nonempty := by
    rw [hSlice]
    exact hparts.1
  have hSliceDisjoint : Set.PairwiseDisjoint Set.univ Slice := by
    rw [hSlice]
    exact hparts.2.1
  have hGapDisjoint : Disjoint GapSource (⋃ s, Slice s) := by
    rw [hSlice]
    exact hparts.2.2.1
  have hcover : GapSource ∪ (⋃ s, Slice s) = C.centres := by
    rw [hSlice]
    exact hparts.2.2.2
  let atom : Sum ↥GapSource GoodIndex → Set Tiling.Plane :=
    Sum.elim (fun t => {t.1}) Slice
  obtain ⟨hatomNonempty, hatomDisjoint, hatomCover⟩ :=
    nativeAtomPartition C.centres GapSource Slice
      hSliceNonempty hSliceDisjoint hGapDisjoint hcover
  have hGapSubset : Gap ⊆ Set.range Tphi := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨Q, hQ⟩ := Set.mem_iUnion.mp hi
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hQ
    rw [← Dcmp.parts_union]
    exact Set.mem_iUnion.mpr ⟨i, hn.1⟩
  have hGapPeriodN : (N • Dcmp.lambda.toPlane) +ᵥ Gap = Gap :=
    (setPeriodicBy_iff_vadd_eq Gap _).mp hGapLambda
  have hGapPeriod : ((N ^ 2) • Dcmp.lambda.toPlane) +ᵥ Gap = Gap := by
    apply (periodGroup_isAddSubgroup Gap _).mp
    have hmem := (periodGroup_isAddSubgroup Gap _).mpr hGapPeriodN
    simpa only [smul_smul, pow_two] using (periodGroup Gap).zsmul_mem hmem N
  obtain ⟨nextGap, hnextGap⟩ := gapSourcePeriod_successor_exists
    phi Tphi hTphi f hext Gap hGapSubset ((N ^ 2) • Dcmp.lambda.toPlane) hGapPeriod
  let nextGood : Equiv.Perm GoodIndex :=
    Equiv.sigmaCongrRight (fun i => ungappedPhaseShiftEquiv
      Dcmp originalSlice G i (-(p i * Dcmp.gammaCoefficient i * N)))
  let next : Equiv.Perm (Sum ↥GapSource GoodIndex) :=
    Equiv.sumCongr nextGap nextGood
  let displacement : Sum ↥GapSource GoodIndex → Tiling.Plane :=
    Sum.elim (fun t => (nextGap t).1 - t.1)
      (fun s => p s.1 • (N • (alpha s).1 - Dcmp.gammaCoefficient s.1 • gamma))
  have hmapDisplacement : ∀ a, f (displacement a) = (N ^ 2) • Dcmp.lambda.toPlane := by
    intro a
    cases a with
    | inl t => exact hnextGap t
    | inr s =>
      change f (p s.1 • (N • (alpha s).1 -
        Dcmp.gammaCoefficient s.1 • gamma)) = _
      rw [map_zsmul, map_sub, map_zsmul, map_zsmul,
        hext, hAlphaMap, hmapGamma, hDirection]
      calc
        p s.1 • (N • (Dcmp.lambdaCoefficient s.1 • Dcmp.lambda.toPlane +
            Dcmp.gammaCoefficient s.1 • Dcmp.gamma.toPlane) -
            Dcmp.gammaCoefficient s.1 • (N • Dcmp.gamma.toPlane)) =
            (Dcmp.lambdaCoefficient s.1 * p s.1 * N) • Dcmp.lambda.toPlane := by
          module
        _ = (N ^ 2) • Dcmp.lambda.toPlane := by rw [hp, pow_two]
  have hGammaIter (s : GoodIndex) (q : ℤ) :
      (q • gamma) +ᵥ regularSupport C.region (Slice s) =
        regularSupport C.region
          (originalSlice s.1 (s.2.1.vadd ((q * N) • Dcmp.gamma.toPlane))) := by
    have hstep (m : ℤ) :
        gamma +ᵥ regularSupport C.region
            (originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane))) =
          regularSupport C.region
            (originalSlice s.1 (s.2.1.vadd ((m + N) • Dcmp.gamma.toPlane))) := by
      have hgood := ((ungappedOrbitPhase_saturatedGapCheckpoint
        Dcmp originalSlice G s.1 s.2.1 (hphase s)).1 m).mpr s.2.2
      have h := hGammaSupport s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane)) hgood
      rw [rationalSlice_signedShift_add] at h
      exact h
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero, zero_add] using
      signedSupportIteration
        (fun m => regularSupport C.region
          (originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane))))
        gamma N hstep q 0
  have hAlphaSupport (s : GoodIndex) :
      ((p s.1 * N) • (alpha s).1) +ᵥ regularSupport C.region (Slice s) =
        regularSupport C.region (Slice s) := by
    have hsource : (alpha s).1 +ᵥ Slice s = Slice s := by
      simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hAlphaPeriod s 0
    have hsupport : (alpha s).1 +ᵥ regularSupport C.region (Slice s) =
        regularSupport C.region (Slice s) := by
      rw [← regularSupport_vadd, hsource]
    exact (periodGroup_isAddSubgroup _ _).mp
      ((periodGroup _).zsmul_mem ((periodGroup_isAddSubgroup _ _).mpr hsupport) (p s.1 * N))
  have htranslate : ∀ a, displacement a +ᵥ regularSupport C.region (atom a) =
      regularSupport C.region (atom (next a)) := by
    intro a
    cases a with
    | inl t =>
      change ((nextGap t).1 - t.1) +ᵥ regularSupport C.region {t.1} =
        regularSupport C.region {(nextGap t).1}
      rw [← regularSupport_vadd]
      congr 1
      ext x
      simp only [Set.mem_vadd_set_iff_neg_vadd_mem, Set.mem_singleton_iff, vadd_eq_add]
      constructor <;> intro hx <;> linear_combination hx
    | inr s =>
      change (p s.1 • (N • (alpha s).1 - Dcmp.gammaCoefficient s.1 • gamma)) +ᵥ
        regularSupport C.region (Slice s) =
          regularSupport C.region
            (originalSlice s.1 (s.2.1.vadd
              ((-(p s.1 * Dcmp.gammaCoefficient s.1 * N)) • Dcmp.gamma.toPlane)))
      rw [show p s.1 • (N • (alpha s).1 - Dcmp.gammaCoefficient s.1 • gamma) =
          (-(p s.1 * Dcmp.gammaCoefficient s.1)) • gamma +
            (p s.1 * N) • (alpha s).1 by module,
        add_vadd, hAlphaSupport, hGammaIter]
      simp only [neg_mul]
  obtain ⟨hselectedNonempty, hselectedDisjoint, hselectedCover, hselectedSupport⟩ :=
    nativeAtom_selectedCoordinateTransport R v₀ t₀ C hK hcentres atom
      hatomNonempty hatomDisjoint hatomCover
  have hselectedTranslate (a : Sum ↥GapSource GoodIndex) :
      displacement a +ᵥ regularSupport R.selectedRegion (t₀ +ᵥ atom a) =
        regularSupport R.selectedRegion (t₀ +ᵥ atom (next a)) := by
    rw [hselectedSupport a, hselectedSupport (next a)]
    calc
      displacement a +ᵥ ((v₀ + t₀) +ᵥ regularSupport C.region (atom a)) =
          (v₀ + t₀) +ᵥ (displacement a +ᵥ regularSupport C.region (atom a)) := by
        rw [vadd_vadd, vadd_vadd, add_comm (displacement a)]
      _ = (v₀ + t₀) +ᵥ regularSupport C.region (atom (next a)) := by
        rw [htranslate a]
  obtain ⟨lambda, hdisplacement⟩ := atomDisplacements_synchronize R
    (fun a => t₀ +ᵥ atom a) hselectedNonempty hselectedDisjoint hselectedCover
    next displacement (fun x => f (x - (v₀ + t₀))) ((N ^ 2) • Dcmp.lambda.toPlane)
    hselectedTranslate (by
      intro a x _hx _htarget
      rw [show x + displacement a - (v₀ + t₀) =
        (x - (v₀ + t₀)) + displacement a by abel, map_add, hmapDisplacement a])
    (selectedDecoratedMap_injOn R v₀ t₀ C hK hcentres f hinj)
  have hselected : R.selectedCentres.Nonempty := by
    cases haxis : R.orientation with
    | vertical => simpa [R.selectedCentres_vertical haxis] using R.centres_nonempty
    | horizontal =>
      rw [R.selectedCentres_horizontal haxis]
      exact R.centres_nonempty.image coordinateSwap
  obtain ⟨x, hx⟩ := hselected
  obtain ⟨a, _ha⟩ := Set.mem_iUnion.mp (hselectedCover.symm ▸ hx)
  have hmapLambda : f lambda = (N ^ 2) • Dcmp.lambda.toPlane := by
    rw [← hdisplacement a]
    exact hmapDisplacement a
  have hgapShift (t : ↥GapSource) : lambda +ᵥ t.1 = (nextGap t).1 := by
    have h := hdisplacement (Sum.inl t)
    change (nextGap t).1 - t.1 = lambda at h
    rw [vadd_eq_add, ← h]
    abel
  refine ⟨lambda, hmapLambda, ?_, ?_⟩
  · change lambda +ᵥ GapSource = GapSource
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      change lambda +ᵥ t ∈ GapSource
      rw [hgapShift ⟨t, ht⟩]
      exact (nextGap ⟨t, ht⟩).2
    · intro hx
      let t : ↥GapSource := ⟨x, hx⟩
      refine ⟨(nextGap.symm t).1, (nextGap.symm t).2, ?_⟩
      change lambda +ᵥ (nextGap.symm t).1 = x
      rw [hgapShift, nextGap.apply_symm_apply]
  · intro s
    rw [← hdisplacement (Sum.inr s)]
    change Dcmp.lambdaCoefficient s.1 •
      (p s.1 • (N • (alpha s).1 - Dcmp.gammaCoefficient s.1 • gamma)) = _
    rw [smul_smul, hp, smul_sub, smul_smul, smul_smul, pow_two]

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

private theorem nativeOrbit_provenanceCoset
    {K : Region} {P E : Set Tiling.Plane} (hTiles : TilesOn K P E)
    (slice : ℤ → Set Tiling.Plane) (hsub : ∀ j, slice j ⊆ P)
    (alpha gamma lambda w : Tiling.Plane) (k l N : ℤ)
    (hAlpha : ∀ j, alpha +ᵥ slice j = slice j)
    (hGamma : ∀ j, gamma +ᵥ regularSupport K (slice j) = regularSupport K (slice (j + N)))
    (hIntegral : k • lambda = (N ^ 2) • alpha - (N * l) • gamma)
    (hw : w ∈ properVertices (regularSupport K (slice 0))) :
    ∀ m n : ℤ, w + m • (k • lambda) + n • gamma ∈ K.vertices + P := by
  have hAlphaSupport (j : ℤ) :
      alpha +ᵥ regularSupport K (slice j) = regularSupport K (slice j) := by
    rw [← regularSupport_vadd, hAlpha j]
  have hAlphaZ (q j : ℤ) :
      (q • alpha) +ᵥ regularSupport K (slice j) = regularSupport K (slice j) := by
    simpa only [zero_mul, add_zero] using
      signedSupportIteration (fun _ : ℤ => regularSupport K (slice j)) alpha 0
        (fun _ => hAlphaSupport j) q 0
  intro m n
  let q : ℤ := n - m * (N * l)
  have hdisplacement :
      m • (k • lambda) + n • gamma = (m * N ^ 2) • alpha + q • gamma := by
    dsimp only [q]
    rw [hIntegral, smul_sub, smul_smul, smul_smul, sub_smul]
    abel
  have hmove :
      (m • (k • lambda) + n • gamma) +ᵥ regularSupport K (slice 0) =
        regularSupport K (slice (q * N)) := by
    rw [hdisplacement, add_vadd,
      signedSupportIteration (fun j => regularSupport K (slice j)) gamma N hGamma q 0,
      zero_add, hAlphaZ]
  have hproper :
      w + m • (k • lambda) + n • gamma ∈
        properVertices (regularSupport K (slice (q * N))) := by
    rw [← hmove, properVertices_vadd_eq]
    exact ⟨w, hw, by simp only [vadd_eq_add]; abel⟩
  obtain ⟨v, hv, t, ht, heq⟩ :=
    properVertices_regularSupport_subset_vertices_add hTiles (hsub (q * N)) hproper
  exact ⟨v, hv, t, hsub (q * N) ht, heq⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Actual rational source phases satisfy the hypotheses of the signed residue
replacement theorem. Packing comes from the original source placements. -/
private theorem selectedOrbit_residueReplacement_tilesOn
    {C : ApproximationContext.{0}} {Kphi : Region}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Set.image Subtype.val
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (hSourcePacking : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements C.centres))
    (G : ℝ) (i : Fin Dcmp.numberOfParts) (Q : RationalSlice (Dcmp.direction i))
    (hgood : IsUngappedOrbitPhase Dcmp originalSlice G i Q)
    (N : ℕ) (hN : 0 < N) (gamma : Tiling.Plane)
    (hstep : ∀ m : ℤ, gamma +ᵥ regularSupport C.region
      (originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))) =
      regularSupport C.region
        (originalSlice i (Q.vadd ((m + (N : ℤ)) • Dcmp.gamma.toPlane)))) :
    let replacement := ⋃ r : Fin N, ⋃ q : ℤ,
      (q • gamma) +ᵥ originalSlice i (Q.vadd ((r.1 : ℤ) • Dcmp.gamma.toPlane))
    TilesOn C.region replacement
      (regularSupport C.region
        (⋃ m : ℤ, originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane)))) := by
  let slice : ℤ → Set Tiling.Plane :=
    fun m => originalSlice i (Q.vadd (m • Dcmp.gamma.toPlane))
  have hsub (m : ℤ) : slice m ⊆ C.centres := by
    dsimp only [slice]
    rw [hPreimage i _ (hgood m).1]
    rintro x ⟨t, _ht, rfl⟩
    exact t.2
  have hUnionSub : (⋃ m, slice m) ⊆ C.centres := Set.iUnion_subset hsub
  have hpack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements (⋃ m, slice m)) := by
    intro x hx y hy hxy
    exact hSourcePacking (hUnionSub hx) (hUnionSub hy) hxy
  have hdis : Set.PairwiseDisjoint Set.univ slice := by
    intro m _ n _ hmn
    change Disjoint (slice m) (slice n)
    dsimp only [slice]
    rw [hPreimage i _ (hgood m).1, hPreimage i _ (hgood n).1]
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs, hsx⟩ ⟨t, ht, htx⟩
    have hst : s = t := Subtype.ext (hsx.trans htx.symm)
    subst t
    exact hmn (rationalDirectional_phaseShift_injective Dcmp i Q (hs.2.symm.trans ht.2))
  exact (residueRepetition_packing_tilesOn C.region N hN slice gamma hpack hdis hstep).2

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

/-- Gamma is a period of the orbit support, not necessarily of its centres.
The integral identity is scaled by the divisibility witness, so no cancellation
or nonzero assumption on `k` or `N` is needed. -/
private theorem nativeOrbit_regularSupport_twoPeriods
    (K : Region) (slice : ℤ → Set Tiling.Plane)
    (alpha gamma lambda : Tiling.Plane) (k l N : ℤ)
    (hAlpha : ∀ m, alpha +ᵥ slice m = slice m)
    (hGamma : ∀ m, gamma +ᵥ regularSupport K (slice m) = regularSupport K (slice (m + N)))
    (hkN : k ∣ N)
    (hIntegral : k • lambda = (N ^ 2) • alpha - (N * l) • gamma) :
    gamma +ᵥ regularSupport K (⋃ m, slice m) = regularSupport K (⋃ m, slice m) ∧
      (N • lambda) +ᵥ regularSupport K (⋃ m, slice m) = regularSupport K (⋃ m, slice m) := by
  have hGammaUnion :
      gamma +ᵥ (⋃ m, regularSupport K (slice m)) =
        ⋃ m, regularSupport K (slice m) := by
    rw [Set.vadd_set_iUnion]
    simp_rw [hGamma]
    exact (show Function.Surjective (fun m : ℤ => m + N) from
      fun m => ⟨m - N, sub_add_cancel m N⟩).iUnion_comp
        (fun m : ℤ => regularSupport K (slice m))
  have hGammaSupport :
      gamma +ᵥ regularSupport K (⋃ m, slice m) =
        regularSupport K (⋃ m, slice m) := by
    rw [Tiling.AxisParallel.regularSupport_iUnion, ← interior_vadd,
      ← closure_vadd, hGammaUnion]
  have hAlphaUnion : alpha +ᵥ (⋃ m, slice m) = ⋃ m, slice m := by
    rw [Set.vadd_set_iUnion]
    exact Set.iUnion_congr hAlpha
  have hAlphaSupport :
      alpha +ᵥ regularSupport K (⋃ m, slice m) =
        regularSupport K (⋃ m, slice m) := by
    rw [← Tiling.AxisParallel.regularSupport_vadd, hAlphaUnion]
  obtain ⟨p, hp⟩ := hkN
  have hScaled : N • lambda =
      (p * N ^ 2) • alpha - (p * (N * l)) • gamma := by
    calc
      N • lambda = p • (k • lambda) := by
        rw [smul_smul, mul_comm p k, ← hp]
      _ = (p * N ^ 2) • alpha - (p * (N * l)) • gamma := by
        rw [hIntegral, smul_sub, smul_smul, smul_smul]
  have hAlphaMem : alpha ∈ Tiling.AxisParallel.periodGroup
      (regularSupport K (⋃ m, slice m)) :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup _ alpha).mpr hAlphaSupport
  have hGammaMem : gamma ∈ Tiling.AxisParallel.periodGroup
      (regularSupport K (⋃ m, slice m)) :=
    (Tiling.AxisParallel.periodGroup_isAddSubgroup _ gamma).mpr hGammaSupport
  refine ⟨hGammaSupport, ?_⟩
  rw [hScaled]
  apply (Tiling.AxisParallel.periodGroup_isAddSubgroup _ _).mp
  exact sub_mem
    ((Tiling.AxisParallel.periodGroup _).zsmul_mem hAlphaMem _)
    ((Tiling.AxisParallel.periodGroup _).zsmul_mem hGammaMem _)

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem synchronizedImages_linearIndependent
    {Kphi : Region} {Tphi : Set Tiling.Plane}
    (Dcmp : RationalDirectionalDecomposition Kphi Tphi)
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane)
    (lambda gamma : Tiling.Plane) (k N : ℤ)
    (hk : k ≠ 0) (hN : N ≠ 0)
    (hMapLambda : f lambda = (N ^ 2) • Dcmp.lambda.toPlane)
    (hMapGamma : f gamma = N • Dcmp.gamma.toPlane) :
    LinearIndependent ℚ ![f (k • lambda), f gamma] := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have hScaled : LinearIndependent ℝ
      ![((k : ℝ) * (N : ℝ) ^ 2) • Dcmp.lambda.toPlane,
        (N : ℝ) • Dcmp.gamma.toPlane] :=
    (LinearIndependent.pair_smul_smul_iff
      (isUnit_iff_ne_zero.mpr (mul_ne_zero hkR (pow_ne_zero 2 hNR)))
      (isUnit_iff_ne_zero.mpr hNR)).mpr Dcmp.basisIndependent
  rw [map_zsmul, hMapLambda, hMapGamma, smul_smul]
  simpa only [← Int.cast_smul_eq_zsmul (R := ℝ), Int.cast_mul, Int.cast_pow] using
    hScaled.restrict_scalars' ℚ

/-- Both the shape and the actual centres are unnormalized. No equality of
regular supports is used to infer a centre displacement. -/
private theorem normalizedSelectedPacking
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (S : Set Tiling.Plane)
    (hpack : Tiling.IsPacking C.region.toPolygonalRegion.prototileFamily
      (C.region.toPolygonalRegion.placements S)) :
    Tiling.IsPacking R.selectedRegion.toPolygonalRegion.prototileFamily
      (R.selectedRegion.toPolygonalRegion.placements (t₀ +ᵥ S)) := by
  apply (isPacking_iff_openCarrier_disjoint R.selectedRegion _).mpr
  rintro x ⟨s, hs, rfl⟩ y ⟨t, ht, rfl⟩ hst
  have hne : s ≠ t := fun h => hst (congrArg (t₀ + ·) h)
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  have hzS' : z - (v₀ + t₀) ∈ s +ᵥ C.region.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzS
    rw [hK, Set.mem_vadd_set_iff_neg_vadd_mem,
      Set.mem_vadd_set_iff_neg_vadd_mem]
    convert hzS using 1
    simp only [vadd_eq_add]
    abel
  have hzT' : z - (v₀ + t₀) ∈ t +ᵥ C.region.openCarrier := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hzT
    rw [hK, Set.mem_vadd_set_iff_neg_vadd_mem,
      Set.mem_vadd_set_iff_neg_vadd_mem]
    convert hzT using 1
    simp only [vadd_eq_add]
    abel
  exact Set.disjoint_left.mp
    ((isPacking_iff_openCarrier_disjoint C.region S).mp hpack hs ht hne) hzS' hzT'

/-- A normalized replacement tiling is transported to the original selected
region and centres, with the target fixed as their original regular support. -/
private theorem normalizedSelectedReplacement_tilesOn
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T)
    (v₀ t₀ : Tiling.Plane) (C : ApproximationContext.{0})
    (hK : C.region.openCarrier = (-v₀) +ᵥ R.selectedRegion.openCarrier)
    (hcentres : C.centres = (-t₀) +ᵥ R.selectedCentres)
    (S : Set Tiling.Plane)
    (hTiles : TilesOn C.region S (regularSupport C.region C.centres)) :
    TilesOn R.selectedRegion (t₀ +ᵥ S)
      (regularSupport R.selectedRegion R.selectedCentres) := by
  have hRegular := regularSupport_isRegularOpen C.region C.centres
  have hSupport : regularSupport C.region S =
      regularSupport C.region C.centres :=
    regularSupport_eq_of_tilesOn hRegular.1 hRegular.2 hTiles
  have hOriginal : t₀ +ᵥ C.centres = R.selectedCentres := by
    rw [hcentres, vadd_vadd, add_neg_cancel, zero_vadd]
  have hSelectedSupport : regularSupport R.selectedRegion (t₀ +ᵥ S) =
      regularSupport R.selectedRegion R.selectedCentres := by
    rw [normalizedSelectedSupport_eq R v₀ t₀ C hK, hSupport,
      ← normalizedSelectedSupport_eq R v₀ t₀ C hK, hOriginal]
  have hSelected := tilesOn_regularSupport_of_packing R.selectedRegion
    (t₀ +ᵥ S) (normalizedSelectedPacking R v₀ t₀ C hK S hTiles.2.1)
  rw [hSelectedSupport] at hSelected
  exact hSelected

end Tiling.AxisParallel.Terminal
namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- The genuine ungapped quotient is finite only after its original source
orbit supports carry the two periods of the actual full-rank lattice. -/
private theorem ungappedOrbitQuotient_finite
    {C : ApproximationContext.{0}} {Kphi : Region}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (hSource : TilesOn C.region C.centres C.target)
    (G : ℝ) (N : ℤ) (lambda gamma : Tiling.Plane)
    (L : PlanarLattice) (hBasis : L.basis = ![N • lambda, gamma])
    (hdivide : ∀ i, Dcmp.lambdaCoefficient i ∣ N)
    (hGammaSupport : ∀ i Q,
      IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      gamma +ᵥ regularSupport C.region (originalSlice i Q) =
        regularSupport C.region
          (originalSlice i (Q.vadd (N • Dcmp.gamma.toPlane))))
    (alpha : (Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}) → Tiling.Plane)
    (hAlphaPeriod : ∀ s (m : ℤ), alpha s +ᵥ originalSlice s.1
      (s.2.1.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane)))
    (hIntegral : ∀ s, Dcmp.lambdaCoefficient s.1 • lambda =
      (N ^ 2) • alpha s - (N * Dcmp.gammaCoefficient s.1) • gamma) :
    Finite (Σ i : Fin Dcmp.numberOfParts,
      Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)) := by
  classical
  let OrbitIndex := Σ i : Fin Dcmp.numberOfParts,
    Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)
  let Orbit : OrbitIndex → Set Tiling.Plane := fun o =>
    ungappedOrbitCentres Dcmp originalSlice G o.1 o.2
  obtain ⟨hNonempty, hDisjoint, _hGapDisjoint, hCover⟩ :=
    ungappedOrbitCentres_partition Tphi Dcmp originalSlice hPreimage G
  have hSub (o : OrbitIndex) : Orbit o ⊆ C.centres := by
    intro x hx
    rw [← hCover]
    exact Or.inr (Set.mem_iUnion.mpr ⟨o, hx⟩)
  -- Countability is inherited from distinct original packing centres, not
  -- from a finite or countable list of phase representatives.
  let centre : OrbitIndex → ↥C.centres := fun o =>
    ⟨(hNonempty o).choose, hSub o (hNonempty o).choose_spec⟩
  have hCentreInjective : Function.Injective centre := by
    intro o p hop
    by_contra hne
    have hEq : (hNonempty o).choose = (hNonempty p).choose :=
      congrArg Subtype.val hop
    exact Set.disjoint_left.mp
      (hDisjoint (Set.mem_univ o) (Set.mem_univ p) hne)
      (hNonempty o).choose_spec (hEq.symm ▸ (hNonempty p).choose_spec)
  have : Countable ↥C.centres := hSource.1.to_subtype
  have : Countable OrbitIndex := hCentreInjective.countable
  let Support : OrbitIndex → Set Tiling.Plane := fun o =>
    regularSupport C.region (Orbit o)
  have hSupportDisjoint : Set.PairwiseDisjoint Set.univ Support :=
    (regularSupport_disjointSubfamilies Orbit hDisjoint hSub hSource).1
  have hPeriods (o : OrbitIndex) : L.toAddSubgroup ≤ periodGroup (Support o) := by
    obtain ⟨i, q⟩ := o
    refine Quotient.inductionOn q ?_
    intro Q
    have hStep (m : ℤ) :
        gamma +ᵥ regularSupport C.region
          (originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane))) =
        regularSupport C.region
          (originalSlice i (Q.1.vadd ((m + N) • Dcmp.gamma.toPlane))) := by
      simpa only [rationalSlice_signedShift_add] using
        hGammaSupport i (Q.1.vadd (m • Dcmp.gamma.toPlane))
          (ungappedPhaseShiftEquiv Dcmp originalSlice G i m Q).2
    have hTwo := nativeOrbit_regularSupport_twoPeriods C.region
      (fun m => originalSlice i (Q.1.vadd (m • Dcmp.gamma.toPlane)))
      (alpha ⟨i, Q⟩) gamma lambda (Dcmp.lambdaCoefficient i)
      (Dcmp.gammaCoefficient i) N (hAlphaPeriod ⟨i, Q⟩) hStep
      (hdivide i) (hIntegral ⟨i, Q⟩)
    rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
      AddSubgroup.closure_le]
    rintro x ⟨j, rfl⟩
    rw [hBasis]
    fin_cases j
    · exact (periodGroup_isAddSubgroup _ _).mpr hTwo.2
    · exact (periodGroup_isAddSubgroup _ _).mpr hTwo.1
  exact periodicOrbitSupports_finite (K := C.region) Support L
    (fun o => (regularSupport_isRegularOpen C.region (Orbit o)).1)
    (fun o => (regularSupport_isRegularOpen C.region (Orbit o)).2)
    (fun o => regularSupport_nonempty_of_centres_local C.region (hNonempty o))
    (fun o p hop => (hSupportDisjoint (Set.mem_univ o) (Set.mem_univ p) hop).aedisjoint)
    hPeriods
    (fun o => ⟨(hNonempty o).choose,
      tileOpen_subset_regularSupport C.region (Orbit o) _ (hNonempty o).choose_spec⟩)

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

/-- Independently tile each regular support of a countable old partition.
No finiteness, period, or literal centre-translation hypothesis is needed. -/
private theorem replacementPartition_tilesOn
    {I : Type*} [Countable I] {K : Region}
    {old target : Set Tiling.Plane}
    (oldParts newParts : I → Set Tiling.Plane)
    (hOldTiles : TilesOn K old target)
    (hOldUnion : (⋃ i, oldParts i) = old)
    (hOldDisjoint : Set.PairwiseDisjoint Set.univ oldParts)
    (hNewTiles : ∀ i, TilesOn K (newParts i) (regularSupport K (oldParts i))) :
    TilesOn K (⋃ i, newParts i) target := by
  classical
  have hPieceSupport (i : I) :
      regularSupport K (newParts i) = regularSupport K (oldParts i) :=
    regularSupport_eq_of_tilesOn
      (regularSupport_isRegularOpen K (oldParts i)).1
      (regularSupport_isRegularOpen K (oldParts i)).2 (hNewTiles i)
  have hOldSupportDisjoint :=
    (regularSupport_pairwiseDisjoint oldParts hOldDisjoint hOldUnion hOldTiles).1
  have hNewSupportDisjoint : Set.PairwiseDisjoint Set.univ
      (fun i => regularSupport K (newParts i)) := by
    intro i hi j hj hij
    change Disjoint (regularSupport K (newParts i)) (regularSupport K (newParts j))
    rw [hPieceSupport i, hPieceSupport j]
    exact hOldSupportDisjoint hi hj hij
  -- The existing packing helper has a universe-zero index. Countability
  -- reindexes this arbitrary-universe family without changing any centres.
  let : Encodable I := Encodable.ofCountable I
  let e := Encodable.equivRangeEncode I
  have hReindexUnion :
      (⋃ j : Set.range (Encodable.encode : I → ℕ), newParts (e.symm j)) =
        ⋃ i, newParts i := e.symm.surjective.iUnion_comp newParts
  have hNewPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (⋃ i, newParts i)) := by
    rw [← hReindexUnion]
    apply isPacking_iUnion_of_regularSupportDisjoint K (fun j => newParts (e.symm j))
    · intro j
      exact (hNewTiles (e.symm j)).2.1
    · intro j _hj k _hk hjk
      exact hNewSupportDisjoint (Set.mem_univ _) (Set.mem_univ _)
        (e.symm.injective.ne hjk)
  apply tilesOn_of_replacementPacking_and_regularSupport_eq hOldTiles hNewPacking
  calc
    regularSupport K (⋃ i, newParts i) =
        interior (closure (⋃ i, regularSupport K (newParts i))) :=
      Tiling.AxisParallel.regularSupport_iUnion K newParts
    _ = interior (closure (⋃ i, regularSupport K (oldParts i))) := by
      simp_rw [hPieceSupport]
    _ = regularSupport K (⋃ i, oldParts i) :=
      (Tiling.AxisParallel.regularSupport_iUnion K oldParts).symm
    _ = regularSupport K old := by rw [hOldUnion]

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem synchronizedReplacementLattice_exists
    {C : ApproximationContext.{0}} {Kphi : Region}
    (Tphi : ↥C.centres ↪ Tiling.Plane)
    (Dcmp : RationalDirectionalDecomposition Kphi (Set.range Tphi))
    (originalSlice : ∀ i : Fin Dcmp.numberOfParts,
      RationalSlice (Dcmp.direction i) → Set Tiling.Plane)
    (hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)})
    (hSource : TilesOn C.region C.centres C.target)
    (hFLC : HasFLC C.centres)
    (G : ℝ) (N : ℤ) (hN : N ≠ 0)
    (hdivide : ∀ i, Dcmp.lambdaCoefficient i ∣ N)
    (f : Tiling.Plane →ₗ[ℚ] Tiling.Plane) (lambda gamma : Tiling.Plane)
    (hMapLambda : f lambda = (N ^ 2) • Dcmp.lambda.toPlane)
    (hMapGamma : f gamma = N • Dcmp.gamma.toPlane)
    (hGapLambda : lambda +ᵥ (Subtype.val ''
      {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}) =
      (Subtype.val '' {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}))
    (hGapGamma : gamma +ᵥ (Subtype.val ''
      {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}) =
      (Subtype.val '' {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}))
    (hGammaSupport : ∀ i Q, IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      gamma +ᵥ regularSupport C.region (originalSlice i Q) =
        regularSupport C.region (originalSlice i (Q.vadd (N • Dcmp.gamma.toPlane))))
    (alpha : (Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}) → Tiling.Plane)
    (hAlphaPeriod : ∀ s (m : ℤ),
      alpha s +ᵥ originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane)))
    (hIntegral : ∀ s, Dcmp.lambdaCoefficient s.1 • lambda =
      (N ^ 2) • alpha s - (N * Dcmp.gammaCoefficient s.1) • gamma)
    (hProper : ∀ s : (Σ i : Fin Dcmp.numberOfParts,
      {Q : RationalSlice (Dcmp.direction i) //
        IsUngappedOrbitPhase Dcmp originalSlice G i Q}),
      properVertices (regularSupport C.region (originalSlice s.1 s.2.1)) ≠ ∅) :
    ∃ (L : PlanarLattice) (w : Tiling.Plane),
      L.basis = ![N • lambda, gamma] ∧
      w +ᵥ (L.toAddSubgroup : Set Tiling.Plane) ⊆ C.region.vertices + C.centres := by
  classical
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  have hVertices : C.region.vertices.Finite := C.region.isPolygonal.vertexSet_finite
  by_cases hgood : Nonempty GoodIndex
  · obtain ⟨s⟩ := hgood
    let slice : ℤ → Set Tiling.Plane :=
      fun m => originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane))
    have hsub (m : ℤ) : slice m ⊆ C.centres := by
      dsimp only [slice]
      rw [hPreimage s.1 _ (s.2.2 m).1]
      rintro x ⟨t, _ht, rfl⟩
      exact t.2
    have hGamma (m : ℤ) : gamma +ᵥ regularSupport C.region (slice m) =
        regularSupport C.region (slice (m + N)) := by
      have hshiftgood : IsUngappedOrbitPhase Dcmp originalSlice G s.1
          (s.2.1.vadd (m • Dcmp.gamma.toPlane)) :=
        (ungappedPhaseShiftEquiv Dcmp originalSlice G s.1 m s.2).2
      simpa only [slice, rationalSlice_signedShift_add] using
        hGammaSupport s.1 _ hshiftgood
    obtain ⟨w, hw⟩ := Set.nonempty_iff_ne_empty.mpr (hProper s)
    have hw0 : w ∈ properVertices (regularSupport C.region (slice 0)) := by
      simpa only [slice, zero_smul, RationalSlice.vadd, map_zero, add_zero] using hw
    have hcoset := nativeOrbit_provenanceCoset hSource slice hsub
      (alpha s) gamma lambda w (Dcmp.lambdaCoefficient s.1)
      (Dcmp.gammaCoefficient s.1) N (hAlphaPeriod s) hGamma (hIntegral s) hw0
    have hfind := synchronizedImages_linearIndependent Dcmp f lambda gamma
      (Dcmp.lambdaCoefficient s.1) N (Dcmp.lambdaCoefficient_ne_zero s.1) hN
      hMapLambda hMapGamma
    have hli : LinearIndependent ℝ ![Dcmp.lambdaCoefficient s.1 • lambda, gamma] :=
      rankTwo_of_flcCoset_and_independentRationalImages hFLC hVertices f hfind
        ⟨w, by rintro x ⟨m, n, rfl⟩; exact hcoset m n⟩
    obtain ⟨L, hL, hcosetL⟩ := correctedReplacementLattice_exists
      w lambda gamma (Dcmp.lambdaCoefficient s.1) N (hdivide s.1) hN hli hcoset
    exact ⟨L, w, hL, hcosetL⟩
  · let : IsEmpty GoodIndex := ⟨fun s => hgood ⟨s⟩⟩
    have hGapEq : (Subtype.val '' {t : ↥C.centres | Tphi t ∈ ⋃ i,
        (Dcmp.orbit i).gappedCentres (originalSlice i) G}) = C.centres := by
      simpa only [Set.iUnion_of_empty, Set.union_empty] using
        (selectedTerminalConstruction_partitionPrefix Dcmp Tphi rfl originalSlice G).2.2.2
    have hLambda : lambda ∈ periodGroup C.centres := by
      apply (periodGroup_isAddSubgroup C.centres lambda).mpr
      simpa only [hGapEq] using hGapLambda
    have hGamma : gamma ∈ periodGroup C.centres := by
      apply (periodGroup_isAddSubgroup C.centres gamma).mpr
      simpa only [hGapEq] using hGapGamma
    have hcoset (m n : ℤ) :
        (0 : Tiling.Plane) + m • ((1 : ℤ) • lambda) + n • gamma ∈
          C.region.vertices + C.centres := by
      have hperiod : (m • lambda + n • gamma) +ᵥ C.centres = C.centres :=
        (periodGroup_isAddSubgroup C.centres _).mp
          (add_mem ((periodGroup C.centres).zsmul_mem hLambda m)
            ((periodGroup C.centres).zsmul_mem hGamma n))
      have hcentre : m • lambda + n • gamma ∈ C.centres := by
        rw [← hperiod]
        exact ⟨0, C.zero_mem_centres, by simp only [vadd_eq_add, add_zero]⟩
      simpa only [one_smul, zero_add] using
        (show (0 : Tiling.Plane) + (m • lambda + n • gamma) ∈
          C.region.vertices + C.centres from
            ⟨0, C.zero_mem_vertices, m • lambda + n • gamma, hcentre, rfl⟩)
    have hfind := synchronizedImages_linearIndependent Dcmp f lambda gamma
      1 N one_ne_zero hN hMapLambda hMapGamma
    have hli : LinearIndependent ℝ ![(1 : ℤ) • lambda, gamma] :=
      rankTwo_of_flcCoset_and_independentRationalImages hFLC hVertices f hfind
        ⟨0, by rintro x ⟨m, n, rfl⟩; exact hcoset m n⟩
    obtain ⟨L, hL, hcosetL⟩ := correctedReplacementLattice_exists
      0 lambda gamma 1 N (one_dvd N) hN hli hcoset
    exact ⟨L, 0, hL, hcosetL⟩

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel Tiling.AxisParallel.Approximation

private theorem coupledSelectedTerminalResult_exists
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) :
    Nonempty (CoupledSelectedTerminalResult R) := by
  classical
  obtain ⟨v₀, t₀, C, X, P, phi, D, Tphi, Y, beta, Dcmp, N,
    hv₀, ht₀, hK, hcentres, htargetX, htarget, hphi, hTphi,
    hYopen, hYregular, hYne, hbeta, hbetaPeriod, hImageTiles,
    hParts, hG, hmargin, hMax, hTen, hReciprocal, hDiameter,
    hVc, hVnc, hH, hN, hdivide, hGapLambdaImage, hGapGammaImage⟩ :=
    selectedTerminalConstruction_rationalPrefix R
  let originalSlice := fun (i : Fin Dcmp.numberOfParts)
      (Q : RationalSlice (Dcmp.direction i)) =>
    Subtype.val '' {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)}
  have hPreimage : ∀ i Q, Q ∈ (Dcmp.orbit i).phases →
      originalSlice i Q = Subtype.val ''
        {t : ↥C.centres | Tphi t ∈ Q.centres (Dcmp.part i)} := fun _ _ _ => rfl
  let G : ℝ := 60 * Metric.diam C.region.openCarrier
  let GoodIndex := Σ i : Fin Dcmp.numberOfParts,
    {Q : RationalSlice (Dcmp.direction i) //
      IsUngappedOrbitPhase Dcmp originalSlice G i Q}
  have hNative : ∀ s : GoodIndex, ∃ alpha : ControlledDisplacement C,
      alpha.1 ≠ 0 ∧ mapPoint phi alpha = (Dcmp.direction s.1).toPlane ∧
      (∀ m : ℤ, alpha.1 +ᵥ originalSlice s.1
        (s.2.1.vadd (m • Dcmp.gamma.toPlane)) =
        originalSlice s.1 (s.2.1.vadd (m • Dcmp.gamma.toPlane))) ∧
      ∀ m : ℤ, ∃ b : ControlledDisplacement C,
        regularSupport C.region (originalSlice s.1
          (s.2.1.vadd (m • Dcmp.gamma.toPlane))) =
          b.1 +ᵥ regularSupport C.region (originalSlice s.1 s.2.1) ∧
        mapPoint phi b = m • Dcmp.gamma.toPlane ∧
        properVertices (regularSupport C.region (originalSlice s.1
          (s.2.1.vadd (m • Dcmp.gamma.toPlane)))) ≠ ∅ :=
    fun s => selectedTerminalConstruction_nativeDispatch R v₀ t₀ C hK hcentres
      P phi hphi D Tphi hTphi hImageTiles.2.1 Dcmp originalSlice hPreimage
      hG hmargin hMax hTen hVc hVnc hH s.1 s.2.1 s.2.2
  choose alpha hAlphaNe hAlphaMap hAlphaPeriod hBetas using hNative
  obtain ⟨f, hext, hinj⟩ := coordinatePlaneExtension_exists P phi hphi
  have hNne : (N : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hBetasN : ∀ i Q, IsUngappedOrbitPhase Dcmp originalSlice G i Q →
      ∃ b : ControlledDisplacement C,
        regularSupport C.region (originalSlice i
          (Q.vadd ((N : ℤ) • Dcmp.gamma.toPlane))) =
          b.1 +ᵥ regularSupport C.region (originalSlice i Q) ∧
        mapPoint phi b = (N : ℤ) • Dcmp.gamma.toPlane := by
    intro i Q hQ
    obtain ⟨b, hb, hm, _hp⟩ := hBetas ⟨i, Q, hQ⟩ (N : ℤ)
    exact ⟨b, hb, hm⟩
  obtain ⟨gamma, hMapGamma, hGapGamma, hGammaSupport⟩ :=
    selectedTerminalConstruction_transverseSynchronization R v₀ t₀ C hK hcentres
      phi Tphi hTphi f hext hinj Dcmp originalSlice hPreimage G (N : ℤ)
      hGapGammaImage hBetasN
  obtain ⟨lambda, hMapLambda, hGapLambda, hIntegral⟩ :=
    selectedTerminalConstruction_longitudinalSynchronization R v₀ t₀ C hK hcentres
      phi Tphi hTphi f hext hinj Dcmp originalSlice hPreimage G (N : ℤ)
      hNne hdivide gamma hMapGamma hGammaSupport hGapLambdaImage
      alpha hAlphaMap hAlphaPeriod
  have hProper : ∀ s : GoodIndex,
      properVertices (regularSupport C.region (originalSlice s.1 s.2.1)) ≠ ∅ := by
    intro s
    obtain ⟨b, _hb, _hm, hp⟩ := hBetas s (0 : ℤ)
    simpa only [zero_smul, RationalSlice.vadd, map_zero, add_zero] using hp
  obtain ⟨L, w, hBasis, hCoset⟩ :=
    synchronizedReplacementLattice_exists Tphi Dcmp originalSlice hPreimage
      P.source_tilesOn P.source_hasFLC G (N : ℤ) hNne hdivide
      f lambda gamma hMapLambda hMapGamma hGapLambda hGapGamma hGammaSupport
      (fun s => (alpha s).1) hAlphaPeriod hIntegral hProper
  have hFinite := ungappedOrbitQuotient_finite Tphi Dcmp originalSlice hPreimage
    P.source_tilesOn G (N : ℤ) lambda gamma L hBasis hdivide hGammaSupport
    (fun s => (alpha s).1) hAlphaPeriod hIntegral
  let OrbitIndex := Σ i : Fin Dcmp.numberOfParts,
    Quotient (ungappedPhaseSetoid Dcmp originalSlice G i)
  let : Finite OrbitIndex := hFinite
  let : Fintype OrbitIndex := Fintype.ofFinite OrbitIndex
  let rep (o : OrbitIndex) : GoodIndex := ⟨o.1, o.2.out⟩
  let Orbit (o : OrbitIndex) : Set Tiling.Plane :=
    ungappedOrbitCentres Dcmp originalSlice G o.1 o.2
  let Gap := ⋃ i, (Dcmp.orbit i).gappedCentres (originalSlice i) G
  let GapSource := Subtype.val '' {t : ↥C.centres | Tphi t ∈ Gap}
  let NewOrbit (o : OrbitIndex) : Set Tiling.Plane :=
    ⋃ r : Fin N, ⋃ q : ℤ, (q • gamma) +ᵥ
      originalSlice o.1 ((rep o).2.1.vadd ((r.1 : ℤ) • Dcmp.gamma.toPlane))
  have hOrbitUnion (o : OrbitIndex) :
      Orbit o = ⋃ m : ℤ, originalSlice o.1
        ((rep o).2.1.vadd (m • Dcmp.gamma.toPlane)) := by
    dsimp only [Orbit, rep]
    conv_lhs => rw [← Quotient.out_eq o.2]
    rfl
  have hGammaStep (s : GoodIndex) (m : ℤ) :
      gamma +ᵥ regularSupport C.region (originalSlice s.1
        (s.2.1.vadd (m • Dcmp.gamma.toPlane))) =
        regularSupport C.region (originalSlice s.1
          (s.2.1.vadd ((m + (N : ℤ)) • Dcmp.gamma.toPlane))) := by
    simpa only [rationalSlice_signedShift_add] using hGammaSupport s.1
      (s.2.1.vadd (m • Dcmp.gamma.toPlane))
      (ungappedPhaseShiftEquiv Dcmp originalSlice G s.1 m s.2).2
  obtain ⟨hOrbitNe, hOrbitDisjoint, hGapDisjoint, hCover⟩ :=
    ungappedOrbitCentres_partition Tphi Dcmp originalSlice hPreimage G
  let oldPart : Option OrbitIndex → Set Tiling.Plane :=
    fun i => i.elim GapSource Orbit
  let newPart : Option OrbitIndex → Set Tiling.Plane :=
    fun i => i.elim GapSource NewOrbit
  have hOldUnion : (⋃ i, oldPart i) = C.centres := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      rw [← hCover]
      cases i with
      | none => exact Or.inl hi
      | some o => exact Or.inr (Set.mem_iUnion.mpr ⟨o, hi⟩)
    · intro hx
      rw [← hCover] at hx
      rcases hx with hx | hx
      · exact Set.mem_iUnion.mpr ⟨none, hx⟩
      · obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨some o, ho⟩
  have hOldDisjoint : Set.PairwiseDisjoint Set.univ oldPart := by
    intro i _ j _ hij
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some o => exact hGapDisjoint.mono_right (subset_iUnion Orbit o)
    | some o =>
      cases j with
      | none => exact (hGapDisjoint.mono_right (subset_iUnion Orbit o)).symm
      | some p =>
        exact hOrbitDisjoint (Set.mem_univ o) (Set.mem_univ p)
          (fun hop => hij (congrArg some hop))
  have hOldSub (i : Option OrbitIndex) : oldPart i ⊆ C.centres := by
    rw [← hOldUnion]
    exact subset_iUnion oldPart i
  have hNewTiles (i : Option OrbitIndex) :
      TilesOn C.region (newPart i) (regularSupport C.region (oldPart i)) := by
    cases i with
    | none =>
      apply tilesOn_regularSupport_of_packing C.region GapSource
      intro x hx y hy hxy
      exact P.source_tilesOn.2.1 (hOldSub none hx) (hOldSub none hy) hxy
    | some o =>
      change TilesOn C.region (NewOrbit o) (regularSupport C.region (Orbit o))
      rw [hOrbitUnion]
      exact selectedOrbit_residueReplacement_tilesOn Tphi Dcmp originalSlice hPreimage
        P.source_tilesOn.2.1 G o.1 (rep o).2.1 (rep o).2.2
        N hN gamma (hGammaStep (rep o))
  let NewCentres := ⋃ i, newPart i
  have hNewTilesAll : TilesOn C.region NewCentres (regularSupport C.region C.centres) :=
    replacementPartition_tilesOn oldPart newPart
      (tilesOn_regularSupport_of_packing C.region C.centres P.source_tilesOn.2.1)
      hOldUnion hOldDisjoint hNewTiles
  have hNewGamma (i : Option OrbitIndex) : gamma +ᵥ newPart i = newPart i := by
    cases i with
    | none => exact hGapGamma
    | some o =>
      exact (residueRepetition_twoPeriods N
        (fun r => originalSlice o.1
          ((rep o).2.1.vadd ((r.1 : ℤ) • Dcmp.gamma.toPlane)))
        (alpha (rep o)).1 gamma lambda (Dcmp.lambdaCoefficient o.1)
        (Dcmp.gammaCoefficient o.1) (hdivide o.1)
        (fun r => hAlphaPeriod (rep o) (r.1 : ℤ)) (hIntegral (rep o))).1
  have hNewLambda (i : Option OrbitIndex) :
      ((N : ℤ) • lambda) +ᵥ newPart i = newPart i := by
    cases i with
    | none =>
      exact (periodGroup_isAddSubgroup _ _).mp
        ((periodGroup GapSource).zsmul_mem
          ((periodGroup_isAddSubgroup _ _).mpr hGapLambda) (N : ℤ))
    | some o =>
      exact (residueRepetition_twoPeriods N
        (fun r => originalSlice o.1
          ((rep o).2.1.vadd ((r.1 : ℤ) • Dcmp.gamma.toPlane)))
        (alpha (rep o)).1 gamma lambda (Dcmp.lambdaCoefficient o.1)
        (Dcmp.gammaCoefficient o.1) (hdivide o.1)
        (fun r => hAlphaPeriod (rep o) (r.1 : ℤ)) (hIntegral (rep o))).2
  have hNewLattice : L.toAddSubgroup ≤ periodGroup NewCentres := by
    rw [PlanarLattice.toAddSubgroup, Tiling.Polygonal.PlanarLattice.toAddSubgroup,
      AddSubgroup.closure_le]
    rintro z ⟨j, rfl⟩
    rw [hBasis]
    fin_cases j
    · apply (periodGroup_isAddSubgroup _ _).mpr
      rw [Set.vadd_set_iUnion]
      exact Set.iUnion_congr hNewLambda
    · apply (periodGroup_isAddSubgroup _ _).mpr
      rw [Set.vadd_set_iUnion]
      exact Set.iUnion_congr hNewGamma
  let selectedPart (i : Option OrbitIndex) := t₀ +ᵥ oldPart i
  let period : Option OrbitIndex → Tiling.Plane :=
    fun i => i.elim gamma (fun o => (alpha (rep o)).1)
  have hPeriodNe (i : Option OrbitIndex) : period i ≠ 0 := by
    cases i with
    | none =>
      change gamma ≠ 0
      simpa [hBasis] using L.independent.ne_zero (1 : Fin 2)
    | some o => exact hAlphaNe (rep o)
  have hOldPeriod (i : Option OrbitIndex) : period i +ᵥ oldPart i = oldPart i := by
    cases i with
    | none => exact hGapGamma
    | some o =>
      have h := ungappedOrbitCentres_nativePeriod Dcmp originalSlice G o.1
        (rep o).2 (alpha (rep o)).1 (hAlphaPeriod (rep o))
      rw [Quotient.out_eq] at h
      exact h
  have hSelectedPeriod (i : Option OrbitIndex) :
      period i +ᵥ selectedPart i = selectedPart i := by
    dsimp only [selectedPart]
    rw [← add_vadd, add_comm (period i), add_vadd, hOldPeriod]
  have hSelectedUnion : (⋃ i, selectedPart i) = R.selectedCentres := by
    rw [← Set.vadd_set_iUnion, hOldUnion, hcentres,
      vadd_vadd, add_neg_cancel, zero_vadd]
  have hSelectedDisjoint : Set.PairwiseDisjoint Set.univ selectedPart := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, hxt⟩ ⟨y, hy, hyt⟩
    have hxy : x = y := add_left_cancel (hxt.trans hyt.symm)
    exact Set.disjoint_left.mp (hOldDisjoint (Set.mem_univ i) (Set.mem_univ j) hij)
      hx (hxy.symm ▸ hy)
  let e : Fin (Fintype.card (Option OrbitIndex)) ≃ Option OrbitIndex :=
    (Fintype.equivFin (Option OrbitIndex)).symm
  have hColourWeak (i : Fin (Fintype.card (Option OrbitIndex))) :
      Tiling.RationalPolygonal.WeaklyPeriodic (selectedPart (e i)) := by
    refine ⟨{
      numberOfParts := 1
      part := fun _ => selectedPart (e i)
      period := fun _ => period (e i)
      period_ne_zero := fun _ => hPeriodNe (e i)
      periodic_part := fun _ => (setPeriodicBy_iff_vadd_eq _ _).mpr (hSelectedPeriod (e i))
      pairwiseDisjoint := ?_
      iUnion_parts := ?_ }⟩
    · intro a _ b _ hab
      exact False.elim (hab (Subsingleton.elim a b))
    · change (⋃ _ : Fin 1, selectedPart (e i)) = selectedPart (e i)
      exact Set.iUnion_const (ι := Fin 1) (selectedPart (e i))
  have hWeak := weaklyPeriodic_finite_disjoint_iUnion
    (fun i => selectedPart (e i))
    (fun i _ j _ hij => hSelectedDisjoint (Set.mem_univ _) (Set.mem_univ _)
      (fun heq => hij (e.injective heq))) hColourWeak
  rw [e.surjective.iUnion_comp selectedPart, hSelectedUnion] at hWeak
  let replacement : PeriodicReplacement R.selectedRegion
      (regularSupport R.selectedRegion R.selectedCentres) := {
    centres := t₀ +ᵥ NewCentres
    tiles := normalizedSelectedReplacement_tilesOn R v₀ t₀ C hK hcentres
      NewCentres hNewTilesAll
    lattice := L
    lattice_periods := by
      intro z hz
      apply (periodGroup_isAddSubgroup _ _).mpr
      rw [← add_vadd, add_comm z, add_vadd]
      rw [(periodGroup_isAddSubgroup _ _).mp (hNewLattice hz)] }
  refine ⟨{
    weak := hWeak
    replacement := replacement
    vertexOrigin := (v₀ + t₀) + w
    replacementLattice_coset := ?_ }⟩
  rintro z ⟨u, hu, rfl⟩
  have hwu := hCoset (show w + u ∈ w +ᵥ (L.toAddSubgroup : Set Tiling.Plane) from
    ⟨u, hu, rfl⟩)
  change w + u ∈ C.translatedVertices at hwu
  rw [normalizedSelectedTranslatedVertices_eq R v₀ t₀ C hK hcentres] at hwu
  obtain ⟨x, hx, hxeq⟩ := hwu
  have heq : (v₀ + t₀) + w + u = x := by
    calc
      (v₀ + t₀) + w + u = (v₀ + t₀) + (w + u) := add_assoc _ _ _
      _ = (v₀ + t₀) + (-(v₀ + t₀) + x) := congrArg ((v₀ + t₀) + ·) hxeq.symm
      _ = x := add_neg_cancel_left _ _
  change (v₀ + t₀) + w + u ∈ R.selectedRegion.vertices + R.selectedCentres
  rw [heq]
  exact hx

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

private theorem selectedTerminalConclusion_exists
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) :
    SelectedTerminalConclusion R := by
  obtain ⟨result⟩ := coupledSelectedTerminalResult_exists R
  exact ⟨result.weak, ⟨result.replacement⟩, result.vertexOrigin,
    result.replacement.lattice, result.replacementLattice_coset⟩

theorem irreducibleTerminalRegion_periodicReplacement
    {K : Region} {T : Set Tiling.Plane} (R : TerminalRegion K T) :
    Tiling.RationalPolygonal.WeaklyPeriodic R.centres ∧
      Nonempty (PeriodicReplacement K (regularSupport K R.centres)) ∧
      ∃ (v : Tiling.Plane) (Lambda : PlanarLattice),
        v +ᵥ (Lambda.toAddSubgroup : Set Tiling.Plane) ⊆
          K.vertices + R.centres :=
  selectedTerminalConclusion_to_original R (selectedTerminalConclusion_exists R)

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel

private theorem terminalDecomposition_selectedColumns_weaklyPeriodic
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    Tiling.RationalPolygonal.WeaklyPeriodic D.selectedColumnCentres := by
  classical
  by_cases hselected : D.selectedColumnCentres.Nonempty
  · obtain ⟨_, _, alpha, _beta, halpha, _, _, halphaFibre, _⟩ :=
      D.slabs.columnInterface
        (by simpa only [D.selectedColumnCentres_eq_slabs] using hselected)
    have hperiod : Tiling.RationalPolygonal.SetPeriodicBy D.selectedColumnCentres
        ((alpha : ℂ) * Complex.I) := by
      have hfibre (h : ℝ) (hh : h ∈ D.slabs.columnAxes) (y : ℝ) :
          y + alpha ∈ D.slabs.columnFibre h ↔ y ∈ D.slabs.columnFibre h := by
        have hmem : y + alpha ∈ alpha +ᵥ D.slabs.columnFibre h ↔
            y ∈ D.slabs.columnFibre h := by
          simp [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add,
            add_comm, add_assoc]
        rw [halphaFibre h hh] at hmem
        exact hmem
      intro z
      rw [D.selectedColumnCentres_eq_slabs, D.slabs.columnCentres_formula]
      simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one]
      constructor
      · rintro ⟨h, hh, hreal, him⟩
        exact ⟨h, hh, hreal, (hfibre h hh z.im).mp him⟩
      · rintro ⟨h, hh, hreal, him⟩
        exact ⟨h, hh, hreal, (hfibre h hh z.im).mpr him⟩
    have hnonzero : (alpha : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt halpha)) Complex.I_ne_zero
    refine ⟨{
      numberOfParts := 1
      part := fun _ ↦ D.selectedColumnCentres
      period := fun _ ↦ (alpha : ℂ) * Complex.I
      period_ne_zero := fun _ ↦ hnonzero
      periodic_part := fun _ ↦ hperiod
      pairwiseDisjoint := ?_
      iUnion_parts := ?_ }⟩
    · intro i _ j _ hij
      exact (hij (Subsingleton.elim i j)).elim
    · ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        exact hi
      · intro hz
        exact Set.mem_iUnion.mpr ⟨(0 : Fin 1), hz⟩
  · have hempty : D.selectedColumnCentres = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hselected
    rw [hempty]
    exact (nullCarrier_periodicReplacement D.selectedRegion).1

/-- The exact finite terminal partition is weakly periodic, using the actual
irreducible endpoint and the original aggregate column centres. -/
private theorem terminalDecomposition_weaklyPeriodic
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    Tiling.RationalPolygonal.WeaklyPeriodic D.selectedCentres := by
  have hregional (i : Fin D.slabs.numberOfNonColumnPlates) :
      Tiling.RationalPolygonal.WeaklyPeriodic (D.region i).selectedCentres := by
    have hweak := (irreducibleTerminalRegion_periodicReplacement (D.region i)).1
    cases haxis : (D.region i).orientation with
    | vertical =>
        simpa only [(D.region i).selectedCentres_vertical haxis] using hweak
    | horizontal =>
        rw [(D.region i).selectedCentres_horizontal haxis]
        exact coordinateSwap_weaklyPeriodic hweak
  let S : Fin (D.slabs.numberOfNonColumnPlates + 1) → Set Tiling.Plane :=
    Fin.cases D.selectedColumnCentres (fun i ↦ (D.region i).selectedCentres)
  have hdisjoint : Set.PairwiseDisjoint Set.univ S := by
    intro i _ j _ hij
    change Disjoint (S i) (S j)
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ b =>
            simpa only [S, Fin.cases_zero, Fin.cases_succ,
              D.selectedColumnCentres_eq_slabs, D.region_selectedCentres b] using
              D.slabs.column_nonColumn_disjoint b
    | succ a =>
        cases j using Fin.cases with
        | zero =>
            simpa only [S, Fin.cases_zero, Fin.cases_succ,
              D.selectedColumnCentres_eq_slabs, D.region_selectedCentres a] using
              (D.slabs.column_nonColumn_disjoint a).symm
        | succ b =>
            have hab : a ≠ b := fun h ↦ hij (congrArg Fin.succ h)
            simpa only [S, Fin.cases_succ, D.region_selectedCentres a,
              D.region_selectedCentres b] using
              D.slabs.nonColumnCentres_pairwise
                (Set.mem_univ a) (Set.mem_univ b) hab
  have hweak : ∀ i, Tiling.RationalPolygonal.WeaklyPeriodic (S i) := by
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · exact terminalDecomposition_selectedColumns_weaklyPeriodic D
    · exact hregional j
  have hunion : (⋃ i, S i) = D.selectedCentres := by
    have hcolours : (⋃ i, S i) =
        D.selectedColumnCentres ∪ ⋃ i, (D.region i).selectedCentres := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
        cases i using Fin.cases with
        | zero => exact Or.inl hi
        | succ j => exact Or.inr (Set.mem_iUnion.mpr ⟨j, hi⟩)
      · intro hz
        rcases hz with hz | hz
        · exact Set.mem_iUnion.mpr ⟨0, hz⟩
        · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨i.succ, hi⟩
    rw [hcolours, D.selectedColumnCentres_eq_slabs]
    simp_rw [D.region_selectedCentres]
    exact D.slabs.centres_partition
  rw [← hunion]
  exact weaklyPeriodic_finite_disjoint_iUnion S hdisjoint hweak

/-- Every FLC tiling of the periodic carrier is weakly periodic. -/
theorem flcTiling_weaklyPeriodic
    {K : Region} {X : Set ℝ} {T : Set Tiling.Plane}
    (hXopen : IsOpen X)
    {beta : ℝ} (hbeta : 0 < beta)
    (hperiod : ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X)
    (hTile : TilesOn K T {z : Tiling.Plane | z.re ∈ X})
    (hFLC : HasFLC T) :
    Tiling.RationalPolygonal.WeaklyPeriodic T := by
  let Xr := interior (closure X)
  let Er := Complex.re ⁻¹' Xr
  have hSupport : regularSupport K T = Er := by
    have h := regularSupport_eq_regularization_of_tilesOn
      (hXopen.preimage Complex.continuous_re) hTile
    simpa only [Complex.closure_preimage_re, Complex.interior_preimage_re] using h
  have hEU : Complex.re ⁻¹' X =ᵐ[volume] openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    apply propext
    change z ∈ Complex.re ⁻¹' X ↔ z ∈ openUnion K T
    simpa only [Set.mem_preimage, openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier.eq_def, Set.mem_iUnion] using hz
  have hEEr : Complex.re ⁻¹' X =ᵐ[volume] Er :=
    hEU.trans ((openUnion_aeEq_regularSupport hTile.2.1).trans
      (Filter.Eventually.of_forall fun z ↦ congrArg (z ∈ ·) hSupport))
  have hTileR : TilesOn K T Er := hTile.congr_ae hEEr
  by_cases hnull : volume Xr = 0
  · have hXrEmpty : Xr = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hne
      exact (show IsOpen Xr from isOpen_interior).measure_ne_zero volume hne hnull
    have hXEmpty : X = ∅ := by
      apply Set.Subset.antisymm
      · have hsubset : X ⊆ Xr := hXopen.subset_interior_closure
        simpa only [hXrEmpty] using hsubset
      · exact Set.empty_subset X
    have hSupportEmpty : regularSupport K T = ∅ := by
      simpa only [Er, hXrEmpty, Set.preimage_empty] using hSupport
    have hTEmpty : T = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hne
      have hneSupport := regularSupport_nonempty_of_centres_local K hne
      rw [hSupportEmpty] at hneSupport
      exact Set.not_nonempty_empty hneSupport
    rw [hTEmpty]
    exact (nullCarrier_periodicReplacement K).1
  have hbasePeriod : beta +ᵥ X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [vadd_eq_add, add_comm] using (hperiod x).mpr hx
    · intro hy
      refine ⟨y - beta, ?_, ?_⟩
      · apply (hperiod (y - beta)).mp
        simpa only [sub_add_cancel] using hy
      · change beta + (y - beta) = y
        abel
  have hbasePeriodR : beta +ᵥ Xr = Xr := by
    dsimp [Xr]
    rw [← interior_vadd, ← closure_vadd, hbasePeriod]
  let carrier : PeriodicVerticalCarrier := {
    base := Xr
    base_open := isOpen_interior
    base_regular := interior_closure_idem
    base_nonnull := hnull
    period := beta
    period_pos := hbeta
    base_periodic := hbasePeriodR }
  obtain ⟨D⟩ := exists_terminalRegionDecomposition carrier hTileR hFLC
  have hweak := terminalDecomposition_weaklyPeriodic D
  cases haxis : D.orientation with
  | vertical =>
      simpa only [D.selectedCentres_vertical haxis] using hweak
  | horizontal =>
      simpa only [D.selectedCentres_horizontal haxis,
        IntrinsicVertices.coordinateSwap_image_image] using
        coordinateSwap_weaklyPeriodic hweak

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal
open Tiling.AxisParallel
open MeasureTheory

private theorem ae_re_descend {p : ℝ → Prop}
    (h : ∀ᵐ z : Tiling.Plane ∂volume, p z.re) : ∀ᵐ x : ℝ ∂volume, p x := by
  have hp : ∀ᵐ z : ℝ × ℝ ∂volume, p z.1 := by
    simpa only [Complex.measurableEquivRealProd_symm_apply] using
      Complex.volume_preserving_equiv_real_prod.symm.quasiMeasurePreserving.ae h
  have hxy := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hxy] with x hx
  obtain ⟨y, hy⟩ := hx.exists
  exact hy

private theorem tilesOn_cylinder_centres_nonempty
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (h : TilesOn K S (Complex.re ⁻¹' X)) (hX : volume X ≠ 0) : S.Nonempty := by
  by_contra hS
  have hSempty := Set.not_nonempty_iff_eq_empty.mp hS
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume, z.re ∉ X := by
    filter_upwards [h.2.2] with z hz
    simpa [hSempty] using hz
  exact hX (measure_eq_zero_iff_ae_notMem.mpr (ae_re_descend hplane))

private theorem bounded_positive_window {X : Set ℝ}
    (hX : IsOpen X) (hne : X.Nonempty) :
    ∃ I : Set ℝ, Bornology.IsBounded I ∧ 0 < (volume (X ∩ I)).toReal := by
  obtain ⟨a, b, hab, hsub⟩ := hX.exists_Ioo_subset hne
  refine ⟨Icc a b, isCompact_Icc.isBounded, ?_⟩
  have hpos : 0 < volume (X ∩ Icc a b) := by
    apply lt_of_lt_of_le (show 0 < volume (Ioo a b) by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
    exact measure_mono fun x hx ↦ ⟨hsub hx, hx.1.le, hx.2.le⟩
  exact ENNReal.toReal_pos hpos.ne' (ne_of_lt
    (lt_of_le_of_lt (measure_mono inter_subset_right) isCompact_Icc.measure_lt_top))

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel

private theorem cylinder_regular {X : Set ℝ}
    (h : interior (closure X) = X) :
    interior (closure (Complex.re ⁻¹' X)) = Complex.re ⁻¹' X := by
  rw [Complex.closure_preimage_re, Complex.interior_preimage_re, h]

private theorem selected_piece_support
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X)
    (i : Fin D.slabs.numberOfNonColumnPlates) :
    (D.slabs.nonColumnPlate i).support = Complex.re ⁻¹' (D.region i).base := by
  change regularSupport D.selectedRegion (D.slabs.nonColumnPlate i).centres = _
  rw [← D.region_selectedCentres i, ← D.region_selectedRegion i]
  exact (D.region i).support_eq

private theorem selected_base_partition
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    (∀ i j : Fin D.slabs.numberOfNonColumnPlates, i ≠ j →
      Disjoint (D.region i).base (D.region j).base) ∧
    (∀ i, Disjoint (D.region i).base D.slabs.columnBase) ∧
    (Set.union (⋃ i, (D.region i).base) D.slabs.columnBase =ᵐ[volume]
      D.selectedCarrier.base) := by
  let A : Option (Fin D.slabs.numberOfNonColumnPlates) → Set Tiling.Plane :=
    fun i ↦ i.elim D.slabs.columnCentres (fun j ↦ (D.slabs.nonColumnPlate j).centres)
  have hparts : Set.PairwiseDisjoint Set.univ A := by
    intro i _ j _ hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact D.slabs.column_nonColumn_disjoint j
    | some i =>
      cases j with
      | none => exact (D.slabs.column_nonColumn_disjoint i).symm
      | some j =>
        exact D.slabs.nonColumnCentres_pairwise (mem_univ i) (mem_univ j)
          (fun h ↦ hij (congrArg some h))
  have hcover : (⋃ i, A i) = D.selectedCentres := by
    rw [Set.iUnion_option]
    exact D.slabs.centres_partition
  have hae := (regularSupport_pairwiseDisjoint A hparts hcover D.selected_tiles).2
  have hsupports : (⋃ i, regularSupport D.selectedRegion (A i)) =
      Complex.re ⁻¹' (D.slabs.columnBase ∪ ⋃ i, (D.region i).base) := by
    rw [Set.iUnion_option]
    change regularSupport D.selectedRegion D.slabs.columnCentres ∪
      (⋃ i, (D.slabs.nonColumnPlate i).support) = _
    simp_rw [D.slabs.columnSupport_eq, selected_piece_support D]
    rw [← Set.preimage_iUnion, ← Set.preimage_union]
  have hplane : ∀ᵐ z : Tiling.Plane ∂volume,
      (z.re ∈ (⋃ i, (D.region i).base) ∪ D.slabs.columnBase) =
        (z.re ∈ D.selectedCarrier.base) := by
    filter_upwards [hae] with z hz
    rw [hsupports] at hz
    change (z.re ∈ D.slabs.columnBase ∪ ⋃ i, (D.region i).base) =
      (z.re ∈ D.selectedCarrier.base) at hz
    simpa only [Set.mem_union, or_comm] using hz
  refine ⟨?_, ?_, ae_re_descend hplane⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hs := D.slabs.nonColumnSupports_pairwise (mem_univ i) (mem_univ j) hij
    change Disjoint (D.slabs.nonColumnPlate i).support (D.slabs.nonColumnPlate j).support at hs
    rw [selected_piece_support D i, selected_piece_support D j] at hs
    exact Set.disjoint_left.mp hs (show (x : ℂ) ∈ Complex.re ⁻¹' (D.region i).base by
      simpa using hxi) (show (x : ℂ) ∈ Complex.re ⁻¹' (D.region j).base by
      simpa using hxj)
  · intro i
    rw [Set.disjoint_left]
    intro x hxi hxc
    have hs := (D.slabs.column_nonColumnSupport_disjoint i).symm
    rw [selected_piece_support D i, D.slabs.columnSupport_eq] at hs
    exact Set.disjoint_left.mp hs (show (x : ℂ) ∈ Complex.re ⁻¹' (D.region i).base by
      simpa using hxi) (show (x : ℂ) ∈ Complex.re ⁻¹' D.slabs.columnBase by
      simpa using hxc)

private theorem finite_cylinder_regularization
    {n : ℕ} {K : Region} (S : Fin n → Set Tiling.Plane) (X : Fin n → Set ℝ)
    (hopen : ∀ i, IsOpen (X i))
    (hregular : ∀ i, interior (closure (X i)) = X i)
    (htiles : ∀ i, TilesOn K (S i) (Complex.re ⁻¹' X i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (X i) (X j)) :
    (⋃ i, X i) =ᵐ[volume] interior (closure (⋃ i, X i)) ∧
    TilesOn K (⋃ i, S i) (Complex.re ⁻¹' interior (closure (⋃ i, X i))) := by
  have ht : TilesOn K (⋃ i, S i) (Complex.re ⁻¹' (⋃ i, X i)) :=
    tilesOn_finite_iUnion_of_aePartition htiles
      (fun i j hij ↦ (hdisjoint i j hij).aedisjoint) Filter.EventuallyEq.rfl
  have hs : regularSupport K (⋃ i, S i) =
      Complex.re ⁻¹' interior (closure (⋃ i, X i)) := by
    rw [regularSupport_iUnion]
    simp_rw [regularSupport_eq_of_tilesOn
      ((hopen _).preimage Complex.continuous_re) (cylinder_regular (hregular _)) (htiles _)]
    rw [← Set.preimage_iUnion, Complex.closure_preimage_re, Complex.interior_preimage_re]
  have hraw : openUnion K (⋃ i, S i) =ᵐ[volume] Complex.re ⁻¹' (⋃ i, X i) := by
    filter_upwards [ht.2.2] with z hz
    apply propext
    change (z ∈ openUnion K (⋃ i, S i)) ↔ z ∈ Complex.re ⁻¹' (⋃ i, X i)
    rw [openUnion, Tiling.Polygonal.openUnion, ← Region.openCarrier, Set.mem_iUnion]
    exact hz.symm
  have hcyl : Complex.re ⁻¹' (⋃ i, X i) =ᵐ[volume]
      Complex.re ⁻¹' interior (closure (⋃ i, X i)) := by
    rw [← hs]
    exact hraw.symm.trans (openUnion_aeEq_regularSupport ht.2.1)
  refine ⟨ae_re_descend hcyl, ht.1, ht.2.1, ?_⟩
  filter_upwards [ht.2.2, hcyl] with z hz hc
  exact (Iff.of_eq hc.symm).trans hz

private theorem centre_mem_regularSupport
    {K : Region} {S : Set Tiling.Plane} {s c : Tiling.Plane}
    (hs : s ∈ S) (hc : c ∈ K.openCarrier) : s + c ∈ regularSupport K S := by
  have hopen : IsOpen (openUnion K S) :=
    isOpen_iUnion (fun t : S ↦ (Region.openCarrier_regularOpen K).1.vadd t.1)
  apply hopen.subset_interior_closure
  exact Set.mem_iUnion_of_mem (⟨s, hs⟩ : S) (Set.mem_vadd_set.mpr ⟨c, hc, rfl⟩)

private theorem regular_cylinder_base_nonempty
    {K : Region} {S : Set Tiling.Plane} {X : Set ℝ}
    (ht : TilesOn K S (Complex.re ⁻¹' X)) (ho : IsOpen X)
    (hr : interior (closure X) = X) (hS : S.Nonempty) : X.Nonempty := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hsc := centre_mem_regularSupport hs hc
  rw [regularSupport_eq_of_tilesOn (ho.preimage Complex.continuous_re)
    (cylinder_regular hr) ht] at hsc
  exact ⟨(s + c).re, hsc⟩

private theorem regular_cylinder_centres_disjoint
    {K : Region} {S T : Set Tiling.Plane} {X Y : Set ℝ}
    (hS : TilesOn K S (Complex.re ⁻¹' X)) (hT : TilesOn K T (Complex.re ⁻¹' Y))
    (hoX : IsOpen X) (hrX : interior (closure X) = X)
    (hoY : IsOpen Y) (hrY : interior (closure Y) = Y)
    (hXY : Disjoint X Y) : Disjoint S T := by
  rw [Set.disjoint_left]
  intro s hs ht
  obtain ⟨c, hc⟩ := K.isPolygonal.interior_nonempty K.nonempty
  have hs' := centre_mem_regularSupport hs hc
  have ht' := centre_mem_regularSupport ht hc
  rw [regularSupport_eq_of_tilesOn (hoX.preimage Complex.continuous_re)
    (cylinder_regular hrX) hS] at hs'
  rw [regularSupport_eq_of_tilesOn (hoY.preimage Complex.continuous_re)
    (cylinder_regular hrY) hT] at ht'
  exact Set.disjoint_left.mp hXY hs' ht'

end Tiling.AxisParallel.Terminal

namespace Tiling.AxisParallel.Terminal

open Tiling.AxisParallel

private theorem terminalDecomposition_commonPeriodAssemblyData
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    Nonempty (CommonPeriodAssemblyData D.selectedRegion D.selectedCarrier.base) := by
  classical
  let n := D.slabs.numberOfNonColumnPlates
  let result : ∀ i : Fin n, CoupledSelectedTerminalResult (D.region i) :=
    fun i ↦ Classical.choice (coupledSelectedTerminalResult_exists (D.region i))
  let centres : Fin n → Set Tiling.Plane := fun i ↦ (result i).replacement.centres
  let lattices : Fin n → PlanarLattice := fun i ↦ (result i).replacement.lattice
  let bases : Fin n → Set ℝ := fun i ↦ (D.region i).base
  have htiles : ∀ i : Fin n, TilesOn D.selectedRegion (centres i) (Complex.re ⁻¹' bases i) := by
    intro i
    have ht := (result i).replacement.tiles
    change TilesOn (D.region i).selectedRegion (centres i)
      (regularSupport (D.region i).selectedRegion (D.region i).selectedCentres) at ht
    rw [(D.region i).support_eq] at ht
    simpa only [D.region_selectedRegion i] using ht
  have hnonempty : ∀ i : Fin n, (centres i).Nonempty :=
    fun i ↦ tilesOn_cylinder_centres_nonempty (htiles i) (D.region i).base_nonnull
  have hperiodic : ∀ i : Fin n, (lattices i).toAddSubgroup ≤ periodGroup (centres i) :=
    fun i ↦ (result i).replacement.lattice_periods
  have hcoset : ∀ i : Fin n,
      (result i).vertexOrigin +ᵥ ((lattices i).toAddSubgroup : Set Tiling.Plane) ⊆
        D.selectedRegion.vertices + D.selectedCentres := by
    intro i
    have hsrc : (D.region i).selectedCentres ⊆ D.selectedCentres := by
      rw [D.region_selectedCentres i]
      intro z hz
      rw [← D.slabs.centres_partition]
      exact Or.inr (Set.mem_iUnion_of_mem i hz)
    have h := (result i).replacementLattice_coset
    change (result i).vertexOrigin +ᵥ ((lattices i).toAddSubgroup : Set Tiling.Plane) ⊆
      (D.region i).selectedRegion.vertices + (D.region i).selectedCentres at h
    rw [D.region_selectedRegion i] at h
    exact h.trans (add_subset_add Set.Subset.rfl hsrc)
  obtain ⟨common, hcommonSome, hcommonLe⟩ :
      ∃ common : Option PlanarLattice,
        (common ≠ none ↔ 0 < n) ∧
        ∀ Lambda, common = some Lambda → ∀ i : Fin n,
          Lambda.toAddSubgroup ≤ (lattices i).toAddSubgroup := by
    by_cases hn : n = 0
    · refine ⟨none, by simp [hn], ?_⟩
      intro Lambda hLambda
      cases hLambda
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      obtain ⟨Lambda, hLambda⟩ := finitePlanarLattices_commonSublattice_of_cosets_subset_flc
        hnpos (D.selected_flc.add_vertexOffsets D.selectedRegion)
        (fun i ↦ (result i).vertexOrigin) lattices hcoset
      refine ⟨some Lambda, by simp [hnpos], ?_⟩
      intro Lambda' hLambda' i
      have heq : Lambda = Lambda' := Option.some.inj hLambda'
      rw [← heq, hLambda]
      exact iInf_le (fun j : Fin n ↦ (lattices j).toAddSubgroup) i
  have hcolumnOpen : IsOpen D.slabs.columnBase := by
    rw [← D.slabs.columnBase_regular]
    exact isOpen_interior
  obtain ⟨column, hcolumnFields, hcolumnBase⟩ :
      ∃ column : Option (ColumnReplacementFamily D.selectedRegion),
        (∀ C, column = some C → C.base = D.slabs.columnBase ∧
          C.sourceCentres = D.selectedColumnCentres) ∧
        {x : ℝ | ∃ C, column = some C ∧ x ∈ C.base} = D.slabs.columnBase := by
    by_cases hc : D.selectedColumnCentres.Nonempty
    · obtain ⟨F⟩ := terminalDecomposition_columnReplacementFamily D hc
      refine ⟨some F.family, ?_, ?_⟩
      · intro C hC
        cases Option.some.inj hC
        exact ⟨F.family_base, F.family_source⟩
      · rw [← F.family_base]
        ext x
        simp only [Set.mem_ofPred_eq, Option.some.injEq, exists_eq_left']
    · have hcem : D.selectedColumnCentres = ∅ := Set.not_nonempty_iff_eq_empty.mp hc
      have hcylinder : Complex.re ⁻¹' D.slabs.columnBase = (∅ : Set Tiling.Plane) := by
        rw [← D.slabs.columnSupport_eq, ← D.selectedColumnCentres_eq_slabs, hcem]
        simp [regularSupport, Tiling.Polygonal.regularSupport, Tiling.Polygonal.openUnion]
      have hbaseEmpty : D.slabs.columnBase = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' : (x : ℂ) ∈ Complex.re ⁻¹' D.slabs.columnBase := by simpa using hx
        rw [hcylinder] at hx'
        exact hx'
      refine ⟨none, ?_, ?_⟩
      · intro C hC
        cases hC
      · simp [hbaseEmpty]
  have hpartition := selected_base_partition D
  have hbaseDisjoint : ∀ i j : Fin n, i ≠ j → Disjoint (bases i) (bases j) :=
    hpartition.1
  have hcolDisjoint : ∀ C, column = some C → ∀ i : Fin n, Disjoint (bases i) C.base := by
    intro C hC i
    rw [(hcolumnFields C hC).1]
    exact hpartition.2.1 i
  have hcover : Set.union (⋃ i : Fin n, bases i)
      {x : ℝ | ∃ C, column = some C ∧ x ∈ C.base} =ᵐ[volume] D.selectedCarrier.base := by
    rw [hcolumnBase]
    exact hpartition.2.2
  refine ⟨{
    target_measurable := D.selectedCarrier.base_open.measurableSet
    numberOfNonColumnPieces := n
    nonColumnCentres := centres
    nonColumnBase := bases
    nonColumnBase_measurable := fun i ↦ (D.region i).base_open.measurableSet
    nonColumn_nonempty := hnonempty
    nonColumn_tiles := htiles
    nonColumnLattice := lattices
    nonColumn_periodic := hperiodic
    commonNonColumnLattice := common
    commonNonColumnLattice_isSome_iff := hcommonSome
    commonNonColumnLattice_le := hcommonLe
    column := column
    bases_pairwise_aeDisjoint := ⟨fun i j hij ↦ (hbaseDisjoint i j hij).aedisjoint,
      fun C hC i ↦ (hcolDisjoint C hC i).aedisjoint⟩
    bases_cover := hcover
    mixed_nonColumnBase_positive := ?_
    mixed_columnBase_positive := ?_
    mixed_rationalization := ?_ }⟩
  · intro hn _hc
    let i : Fin n := ⟨0, hn⟩
    have hi : (bases i).Nonempty := by
      by_contra he
      have hem := Set.not_nonempty_iff_eq_empty.mp he
      have hz : volume (bases i) = 0 := by rw [hem]; exact measure_empty
      exact (D.region i).base_nonnull hz
    exact bounded_positive_window (isOpen_iUnion fun j ↦ (D.region j).base_open)
      (hi.mono (Set.subset_iUnion bases i))
  · intro _hn C hC
    have ho : IsOpen C.base := by rw [(hcolumnFields C hC).1]; exact hcolumnOpen
    have hr : interior (closure C.base) = C.base := by
      rw [(hcolumnFields C hC).1]; exact D.slabs.columnBase_regular
    exact bounded_positive_window ho
      (regular_cylinder_base_nonempty C.source_tiles ho hr C.source_nonempty)
  · intro Lambda C hLambda hC F B _hB hm hmC
    obtain ⟨m, hmpos, hmEq⟩ := hm
    obtain ⟨mC, hmCpos, hmCEq⟩ := hmC
    let SN : Set Tiling.Plane := ⋃ i, centres i
    let Xraw : Set ℝ := ⋃ i, bases i
    let XN : Set ℝ := interior (closure Xraw)
    have hregularized := finite_cylinder_regularization centres bases
      (fun i ↦ (D.region i).base_open) (fun i ↦ (D.region i).base_regular)
      htiles hbaseDisjoint
    have hNtiles : TilesOn D.selectedRegion SN (Complex.re ⁻¹' XN) := hregularized.2
    have hNopen : IsOpen XN := isOpen_interior
    have hNregular : interior (closure XN) = XN := interior_closure_idem
    have hCopen : IsOpen C.base := by rw [(hcolumnFields C hC).1]; exact hcolumnOpen
    have hCregular : interior (closure C.base) = C.base := by
      rw [(hcolumnFields C hC).1]; exact D.slabs.columnBase_regular
    have hCne : C.base.Nonempty :=
      regular_cylinder_base_nonempty C.source_tiles hCopen hCregular C.source_nonempty
    have hCSne : (C.replacement 0).Nonempty := tilesOn_cylinder_centres_nonempty
      (C.replacement_tiles 0) (hCopen.measure_ne_zero volume hCne)
    have hnpos : 0 < n := hcommonSome.mp (by rw [hLambda]; simp)
    have hNSne : SN.Nonempty :=
      (hnonempty ⟨0, hnpos⟩).mono (Set.subset_iUnion centres ⟨0, hnpos⟩)
    have hrawDis : Disjoint Xraw C.base := by
      rw [Set.disjoint_left]
      intro x hx hc
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact Set.disjoint_left.mp (hcolDisjoint C hC i) hi hc
    have hdis : Disjoint XN C.base := (hrawDis.closure_left hCopen).mono_left interior_subset
    have hblockCover : Set.union XN C.base =ᵐ[volume] D.selectedCarrier.base := by
      have hrawCover : Set.union Xraw C.base =ᵐ[volume] D.selectedCarrier.base := by
        have hoption : {x : ℝ | ∃ C', column = some C' ∧ x ∈ C'.base} = C.base := by
          ext x
          simp only [Set.mem_ofPred_eq, hC, Option.some.injEq, exists_eq_left']
        simpa only [hoption] using hcover
      exact (hregularized.1.union Filter.EventuallyEq.rfl).symm.trans hrawCover
    have hrestrictDis : Disjoint (volume.restrict XN) (volume.restrict C.base) := by
      apply Measure.MutuallySingular.disjoint
      refine ⟨C.base, hCopen.measurableSet, ?_, ?_⟩
      · rw [Measure.restrict_apply hCopen.measurableSet,
          Set.inter_comm, Set.disjoint_iff_inter_eq_empty.mp hdis, measure_empty]
      · rw [Measure.restrict_apply hCopen.measurableSet.compl,
          Set.compl_inter_self, measure_empty]
    have hrestrictCover : volume.restrict D.selectedCarrier.base =
        volume.restrict XN + volume.restrict C.base := by
      rw [← Measure.restrict_congr_set hblockCover]
      exact Measure.restrict_union hdis hCopen.measurableSet
    have hwhole : TilesOn D.selectedRegion (SN ∪ C.replacement 0)
        (Complex.re ⁻¹' D.selectedCarrier.base) := by
      let SS : Fin 2 → Set Tiling.Plane := ![SN, C.replacement 0]
      let XX : Fin 2 → Set ℝ := ![XN, C.base]
      have ht : ∀ i, TilesOn D.selectedRegion (SS i) (Complex.re ⁻¹' XX i) := by
        intro i
        fin_cases i
        · exact hNtiles
        · exact C.replacement_tiles 0
      have hd : ∀ i j : Fin 2, i ≠ j → AEDisjoint volume (XX i) (XX j) := by
        intro i j hij
        fin_cases i <;> fin_cases j
        · exact (hij rfl).elim
        · exact hdis.aedisjoint
        · exact hdis.symm.aedisjoint
        · exact (hij rfl).elim
      have hu : (⋃ i, XX i) = Set.union XN C.base := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          fin_cases i
          · exact Or.inl hi
          · exact Or.inr hi
        · rintro (hx | hx)
          · exact Set.mem_iUnion_of_mem 0 hx
          · exact Set.mem_iUnion_of_mem 1 hx
      have hs : (⋃ i, SS i) = SN ∪ C.replacement 0 := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
          fin_cases i
          · exact Or.inl hi
          · exact Or.inr hi
        · rintro (hx | hx)
          · exact Set.mem_iUnion_of_mem 0 hx
          · exact Set.mem_iUnion_of_mem 1 hx
      rw [← hs]
      exact tilesOn_finite_iUnion_of_aePartition ht hd (hu ▸ hblockCover)
    have hNperiod : Lambda.toAddSubgroup ≤ periodGroup SN :=
      iUnion_periodGroup_of_common_subgroup
        (fun i ↦ (hcommonLe Lambda hLambda i).trans (hperiodic i))
    have hv : verticalPeriodVector F.verticalPeriod ∈ periodGroup SN := by
      apply hNperiod
      rw [F.subgroup_eq]
      exact ⟨1, 0, by simp⟩
    have hh : skewPeriodVector F.horizontalPeriod F.shear ∈ periodGroup SN := by
      apply hNperiod
      rw [F.subgroup_eq]
      exact ⟨0, 1, by simp⟩
    obtain ⟨R, _hShearN, _hShearC⟩ := exists_twoBlockMixedRationalizationDatum
      D.selectedCarrier.base_open D.selectedCarrier.base_regular D.selectedCarrier.base_nonnull
      hNopen hNregular hCopen hCregular
      ⟨regular_cylinder_centres_disjoint hNtiles (C.replacement_tiles 0)
        hNopen hNregular hCopen hCregular hdis, rfl⟩
      ⟨hNSne, hCSne⟩ hrestrictDis hrestrictCover hwhole hNtiles (C.replacement_tiles 0)
      F.verticalPeriod_pos C.verticalPeriod_pos F.horizontalPeriod_pos C.axisPeriod_pos
      hv hh (C.replacement_verticalPeriod 0) (C.replacement_axisPeriod 0)
      hmpos hmCpos ⟨hmEq.symm, hmCEq.symm⟩
    exact ⟨R⟩

private theorem terminalDecomposition_periodicReplacement
    {K : Region} {T : Set Tiling.Plane} {X : PeriodicVerticalCarrier}
    (D : TerminalRegionDecomposition K T X) :
    Nonempty (PeriodicReplacement D.selectedRegion D.selectedCarrier.carrier) := by
  obtain ⟨data⟩ := terminalDecomposition_commonPeriodAssemblyData D
  obtain ⟨A⟩ := exists_completeCommonPeriodAssembly data
  exact ⟨{ centres := A.centres
           tiles := A.tiles
           lattice := A.lattice
           lattice_periods := A.lattice_periods }⟩

theorem exists_flcPeriodicReplacement
    {K : Region} {X : Set ℝ} {T : Set Tiling.Plane}
    (hXopen : IsOpen X)
    {beta : ℝ} (hbeta : 0 < beta)
    (hperiod : ∀ x : ℝ, x + beta ∈ X ↔ x ∈ X)
    (hTile : TilesOn K T {z : Tiling.Plane | z.re ∈ X})
    (hFLC : HasFLC T) :
    Nonempty (PeriodicReplacement K {z : Tiling.Plane | z.re ∈ X}) := by
  change Nonempty (PeriodicReplacement K (Complex.re ⁻¹' X))
  let Xr := interior (closure X)
  let Er := Complex.re ⁻¹' Xr
  have hSupport : regularSupport K T = Er := by
    have h := regularSupport_eq_regularization_of_tilesOn
      (hXopen.preimage Complex.continuous_re) hTile
    simpa only [Complex.closure_preimage_re, Complex.interior_preimage_re] using h
  have hEU : Complex.re ⁻¹' X =ᵐ[volume] openUnion K T := by
    filter_upwards [hTile.2.2] with z hz
    apply propext
    change z ∈ Complex.re ⁻¹' X ↔ z ∈ openUnion K T
    simpa only [Set.mem_preimage, openUnion, Tiling.Polygonal.openUnion,
      ← Region.openCarrier.eq_def, Set.mem_iUnion] using hz
  have hEEr : Complex.re ⁻¹' X =ᵐ[volume] Er :=
    hEU.trans ((openUnion_aeEq_regularSupport hTile.2.1).trans
      (Filter.Eventually.of_forall fun z ↦ congrArg (z ∈ ·) hSupport))
  have hTileR : TilesOn K T Er := hTile.congr_ae hEEr
  by_cases hnull : volume Xr = 0
  · have hXrEmpty : Xr = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hne
      exact (show IsOpen Xr from isOpen_interior).measure_ne_zero volume hne hnull
    have hXEmpty : X = ∅ := by
      apply Set.Subset.antisymm
      · have hsubset : X ⊆ Xr := hXopen.subset_interior_closure
        simpa only [hXrEmpty] using hsubset
      · exact Set.empty_subset X
    have hSupportEmpty : regularSupport K T = ∅ := by
      simpa only [Er, hXrEmpty, Set.preimage_empty] using hSupport
    have hTEmpty : T = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hne
      have hneSupport := regularSupport_nonempty_of_centres_local K hne
      rw [hSupportEmpty] at hneSupport
      exact Set.not_nonempty_empty hneSupport
    rw [hXEmpty, Set.preimage_empty]
    exact (nullCarrier_periodicReplacement K).2
  have hbasePeriod : beta +ᵥ X = X := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [vadd_eq_add, add_comm] using (hperiod x).mpr hx
    · intro hy
      refine ⟨y - beta, ?_, ?_⟩
      · apply (hperiod (y - beta)).mp
        simpa only [sub_add_cancel] using hy
      · change beta + (y - beta) = y
        abel
  have hbasePeriodR : beta +ᵥ Xr = Xr := by
    dsimp [Xr]
    rw [← interior_vadd, ← closure_vadd, hbasePeriod]
  let carrier : PeriodicVerticalCarrier := {
    base := Xr
    base_open := isOpen_interior
    base_regular := interior_closure_idem
    base_nonnull := hnull
    period := beta
    period_pos := hbeta
    base_periodic := hbasePeriodR }
  have hReplacementR : Nonempty (PeriodicReplacement K Er) := by
    obtain ⟨D⟩ := exists_terminalRegionDecomposition carrier hTileR hFLC
    obtain ⟨P⟩ := terminalDecomposition_periodicReplacement D
    cases hO : D.orientation with
    | vertical =>
      simpa only [D.selectedRegion_vertical hO, D.selectedCarrier_vertical hO,
        PeriodicVerticalCarrier.carrier, carrier] using (Nonempty.intro P)
    | horizontal =>
      obtain ⟨hXr, _hSelectedBase, hSelectedCarrier⟩ := D.selectedCarrier_horizontal hO
      have P0 : PeriodicReplacement K.coordinateSwap (Set.univ : Set Tiling.Plane) := by
        simpa only [D.selectedRegion_horizontal hO, hSelectedCarrier] using P
      have P' := mapReplacement P0
      rw [Region.coordinateSwap_involutive,
        Set.image_univ, coordinateSwap.surjective.range_eq] at P'
      have hXr' : Xr = Set.univ := hXr
      change Nonempty (PeriodicReplacement K (Complex.re ⁻¹' Xr))
      rw [hXr', Set.preimage_univ]
      exact ⟨P'⟩
  obtain ⟨P⟩ := hReplacementR
  exact ⟨{
    centres := P.centres
    tiles := P.tiles.congr_ae hEEr.symm
    lattice := P.lattice
    lattice_periods := P.lattice_periods }⟩

end Tiling.AxisParallel.Terminal
