import Tiling.AxisParallel.Foundations.ExternalInputs
import Tiling.AxisParallel.Foundations.RegularOpenAxisParallelTilings
import Tiling.AxisParallel.Topology.HullCore
import Tiling.AxisParallel.Topology.LocallyFellMatching
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Metrizable.Basic

set_option linter.style.header false

/-!
# Compact weak topology for fixed-carrier tilings

This module develops the theorem layer over the Fell compactification and fixed-carrier tiling
space.  Results are added only once they are proved from the native topology and tiling APIs.
-/

open Function MeasureTheory Set
open scoped Pointwise Topology

noncomputable section

namespace Tiling.AxisParallel.Continuous

private theorem locallyFellConverges_eventually_exists_mem_ball
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    {x : Tiling.Plane} (hx : x ∈ L) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in Filter.atTop, ∃ y ∈ A n, dist y x < epsilon := by
  exact Tiling.AxisParallel.Topology.locallyFellConverges_eventually_exists_mem_ball
    hconv hx hepsilon

/-- A compact set disjoint from a local Fell limit is eventually disjoint from the converging
sequence. -/
theorem locallyFellConverges_eventually_disjoint_compact
    {A : ℕ → Set Tiling.Plane} {L C : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    (hC : IsCompact C) (hLC : Disjoint L C) :
    ∀ᶠ n : ℕ in Filter.atTop, Disjoint (A n) C := by
  exact Tiling.AxisParallel.Topology.locallyFellConverges_eventually_disjoint_compact
    hconv hC hLC

/-- A convergent sequence of marked points in locally Fell-convergent closed sets has its limit
in the limiting closed set. -/
theorem mem_of_locallyFellConverges_of_tendsto_mem
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L)
    {zseq : ℕ → Tiling.Plane} {z : Tiling.Plane}
    (hzmem : ∀ n, zseq n ∈ A n)
    (hzlim : Filter.Tendsto zseq Filter.atTop (nhds z)) : z ∈ L := by
  exact Tiling.AxisParallel.Topology.mem_of_locallyFellConverges_of_tendsto_mem
    hconv hzmem hzlim

private theorem isDiscrete_of_uniformlySeparated
    {delta : ℝ} (hdelta : 0 < delta) {S : Set Tiling.Plane}
    (hS : Tiling.AxisParallel.Topology.IsUniformlySeparated delta S) :
    IsDiscrete S := by
  exact Tiling.AxisParallel.Topology.isDiscrete_of_uniformlySeparated hdelta hS

/-- A fixed polygonal tile gives one separation constant for every target-relative packing. -/
theorem tilesOn_uniformlySeparated
    (K : Tiling.AxisParallel.Region) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (E : Set Tiling.Plane) (T : Set Tiling.Plane),
        Tiling.AxisParallel.TilesOn K T E →
          Tiling.AxisParallel.Topology.IsUniformlySeparated delta T := by
  obtain ⟨delta, hdelta, hsep⟩ :=
    Tiling.AxisParallel.exists_packingSeparation K
  refine ⟨delta, hdelta, fun E T hT ↦ ?_⟩
  exact hsep T hT.2.1

/-- On uniformly separated closed sets, local Fell convergence is equivalent to eventual unique
matching in every compact window. -/
theorem locallyFell_matchingPoints
    {delta : ℝ} (hdelta : 0 < delta)
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hclosedS : ∀ n : ℕ, IsClosed (S n)) (hclosedL : IsClosed L)
    (hsepS : ∀ n : ℕ,
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta (S n))
    (hsepL : Tiling.AxisParallel.Topology.IsUniformlySeparated delta L) :
    Tiling.AxisParallel.Topology.LocallyFellConverges S L ↔
      ∀ (C : Set Tiling.Plane), IsCompact C →
        ∀ epsilon : ℝ, 0 < epsilon → epsilon < delta / 3 →
          ∀ᶠ n : ℕ in Filter.atTop,
            (∀ x ∈ L ∩ C, ∃! y : Tiling.Plane,
              y ∈ S n ∧ dist x y < epsilon) ∧
            (∀ y ∈ S n ∩ C, ∃! x : Tiling.Plane,
              x ∈ L ∧ dist x y < epsilon) := by
  exact Tiling.AxisParallel.Topology.locallyFell_matchingPoints
    hdelta hclosedS hclosedL hsepS hsepL
private theorem isPacking_of_locallyFellConverges
    {K : Tiling.AxisParallel.Region}
    {A : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hA : ∀ n, Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements (A n)))
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges A L) :
    Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements L) := by
  rw [Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint]
  intro s hsL t htL hst
  change Disjoint (s +ᵥ K.openCarrier) (t +ᵥ K.openCarrier)
  rw [Set.disjoint_left]
  intro x hxs hxt
  let U : Set Tiling.Plane := {c | x - c ∈ K.openCarrier}
  have hUopen : IsOpen U :=
    K.openCarrier_regularOpen.1.preimage (continuous_const.sub continuous_id)
  have hsU : s ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxs
    simp only [vadd_eq_add] at hxs
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxs
  have htU : t ∈ U := by
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hxt
    simp only [vadd_eq_add] at hxt
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hxt
  obtain ⟨rs, hrs, hrsU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
  obtain ⟨rt, hrt, hrtU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds htU)
  let epsilon := min rs (min rt (dist s t / 3))
  have hdist : 0 < dist s t := dist_pos.mpr hst
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    exact lt_min hrs (lt_min hrt (by positivity))
  have heps_rs : epsilon ≤ rs := min_le_left _ _
  have heps_rt : epsilon ≤ rt := (min_le_right _ _).trans (min_le_left _ _)
  have heps_dist : epsilon ≤ dist s t / 3 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsEventually :=
    locallyFellConverges_eventually_exists_mem_ball hconv hsL hepsilon
  have htEventually :=
    locallyFellConverges_eventually_exists_mem_ball hconv htL hepsilon
  obtain ⟨n, ⟨s', hs'A, hs'dist⟩, ⟨t', ht'A, ht'dist⟩⟩ :=
    (hsEventually.and htEventually).exists
  have hs'U : s' ∈ U := hrsU (by
    rw [Metric.mem_ball]
    exact hs'dist.trans_le heps_rs)
  have ht'U : t' ∈ U := hrtU (by
    rw [Metric.mem_ball]
    exact ht'dist.trans_le heps_rt)
  have hs't' : s' ≠ t' := by
    intro heq
    subst t'
    have htriangle : dist s t ≤ dist s s' + dist s' t := dist_triangle _ _ _
    rw [dist_comm s s'] at htriangle
    have hsBound : dist s' s < dist s t / 3 := hs'dist.trans_le heps_dist
    have htBound : dist s' t < dist s t / 3 := ht'dist.trans_le heps_dist
    linarith
  have hdisjoint :=
    (Tiling.AxisParallel.isPacking_iff_openCarrier_disjoint K (A n)).mp
      (hA n) hs'A ht'A hs't'
  apply Set.disjoint_left.mp hdisjoint
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using hs'U
  · rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simpa only [vadd_eq_add, U, Set.mem_ofPred_eq, sub_eq_add_neg,
      add_comm] using ht'U

/-- The metric installed on fixed-carrier tilings induces exactly Fell convergence of centres. -/
theorem locallyFell_metrizable
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    TopologicalSpace.MetrizableSpace
        (Tiling.AxisParallel.Topology.TilingSpace K E) ∧
      ∀ (T : ℕ → Tiling.AxisParallel.Topology.TilingSpace K E)
        (L : Tiling.AxisParallel.Topology.TilingSpace K E),
        Filter.Tendsto T Filter.atTop (nhds L) ↔
          Tiling.AxisParallel.Topology.LocallyFellConverges
            (Tiling.AxisParallel.Topology.TilingSpace.centresSequence T)
            (L.centres : Set Tiling.Plane) := by
  refine ⟨inferInstance, ?_⟩
  intro T L
  let compactify : Tiling.AxisParallel.Topology.TilingSpace K E →
      TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) := fun U =>
    Tiling.AxisParallel.Topology.fellCompactification
      (U.centres : Set Tiling.Plane) U.centres.isClosed
  have hcompactify : Continuous compactify := by
    exact continuous_induced_dom
  constructor
  · intro hT
    refine ⟨fun n ↦ (T n).centres.isClosed, L.centres.isClosed, ?_⟩
    have h := (hcompactify.tendsto L).comp hT
    simpa [compactify, Function.comp_def,
      Tiling.AxisParallel.Topology.TilingSpace.centresSequence] using h
  · rintro ⟨hclosedT, hclosedL, hT⟩
    have hT' : Filter.Tendsto (compactify ∘ T) Filter.atTop
        (nhds (compactify L)) := by
      simpa [compactify, Function.comp_def,
        Tiling.AxisParallel.Topology.TilingSpace.centresSequence] using hT
    rw [show nhds L = Filter.comap compactify (nhds (compactify L)) by
      exact nhds_induced compactify L]
    exact (Filter.tendsto_comap_iff.mpr hT')

private theorem pointSum_eq_sum_of_zero_outside
    (F : Tiling.Plane → ℝ) (S C : Set Tiling.Plane)
    (hfinite : (S ∩ C).Finite)
    (hzero : ∀ x ∈ S, x ∉ C → F x = 0) :
    Tiling.AxisParallel.Topology.pointSum F S =
      ∑ x ∈ hfinite.toFinset, F x := by
  rw [Tiling.AxisParallel.Topology.pointSum, tsum_subtype]
  rw [tsum_eq_sum (s := hfinite.toFinset)]
  · apply Finset.sum_congr rfl
    intro x hx
    have hxSC := hfinite.mem_toFinset.mp hx
    simp [Set.indicator_of_mem hxSC.1]
  · intro x hx
    by_cases hxS : x ∈ S
    · rw [Set.indicator_of_mem hxS]
      exact hzero x hxS (fun hxC ↦ hx (hfinite.mem_toFinset.mpr ⟨hxS, hxC⟩))
    · exact Set.indicator_of_notMem hxS F

/-- Compactly supported continuous point sums are continuous along uniformly separated Fell
convergence. -/
theorem locallyFell_pointSums
    {delta : ℝ} (hdelta : 0 < delta)
    {S : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hsepS : ∀ n : ℕ,
      Tiling.AxisParallel.Topology.IsUniformlySeparated delta (S n))
    (hsepL : Tiling.AxisParallel.Topology.IsUniformlySeparated delta L)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges S L)
    (F : Tiling.Plane → ℝ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    Filter.Tendsto (Tiling.AxisParallel.Topology.pointSum F ∘ S) Filter.atTop
      (nhds (Tiling.AxisParallel.Topology.pointSum F L)) := by
  classical
  obtain ⟨hclosedS, hclosedL, hFell⟩ := hconv
  have hconv' : Tiling.AxisParallel.Topology.LocallyFellConverges S L :=
    ⟨hclosedS, hclosedL, hFell⟩
  by_cases hsupport : tsupport F = ∅
  · have hFzero : F = 0 := tsupport_eq_empty_iff.mp hsupport
    have hzeroPoint (U : Set Tiling.Plane) :
        Tiling.AxisParallel.Topology.pointSum (0 : Tiling.Plane → ℝ) U = 0 := by
      rw [Tiling.AxisParallel.Topology.pointSum]
      exact tsum_zero
    subst F
    rw [show Tiling.AxisParallel.Topology.pointSum 0 ∘ S =
        (fun _ : ℕ ↦ (0 : ℝ)) by
      funext n
      exact hzeroPoint (S n), hzeroPoint L]
    exact tendsto_const_nhds
  have hsupportNonempty : (tsupport F).Nonempty :=
    nonempty_iff_ne_empty.mpr hsupport
  obtain ⟨R, hR⟩ := hFc.isCompact.isBounded.subset_ball (0 : Tiling.Plane)
  have hRpos : 0 < R := by
    obtain ⟨x, hx⟩ := hsupportNonempty
    have := Metric.mem_ball.mp (hR hx)
    exact lt_of_le_of_lt (dist_nonneg) this
  let C : Set Tiling.Plane := Metric.closedBall (0 : Tiling.Plane) (R + 1)
  let C' : Set Tiling.Plane := Metric.closedBall (0 : Tiling.Plane) (R + 2)
  have hCcompact : IsCompact C := isCompact_closedBall _ _
  have hC'compact : IsCompact C' := isCompact_closedBall _ _
  have hsupportC : tsupport F ⊆ C := by
    intro x hx
    rw [Metric.mem_closedBall]
    exact (Metric.mem_ball.mp (hR hx)).le.trans (by linarith)
  have hCC' : C ⊆ C' := Metric.closedBall_subset_closedBall (by linarith)
  have hLfinite : (L ∩ C).Finite :=
    (hCcompact.inter_left hclosedL).finite
      ((isDiscrete_of_uniformlySeparated hdelta hsepL).mono inter_subset_left)
  let A : Finset Tiling.Plane := hLfinite.toFinset
  rw [Metric.tendsto_nhds]
  intro tolerance htolerance
  let termTolerance : ℝ := tolerance / (A.card + 1)
  have htermTolerance : 0 < termTolerance := by
    dsimp [termTolerance]
    positivity
  have huniform : UniformContinuousOn F C' :=
    hC'compact.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨rho, hrho, hFrho⟩ :=
    Metric.uniformContinuousOn_iff.mp huniform termTolerance htermTolerance
  let eta : ℝ := min (rho / 2) (min (1 / 2) (delta / 6))
  have heta : 0 < eta := by
    dsimp [eta]
    exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hetaRho : eta < rho := by
    dsimp [eta]
    have := min_le_left (rho / 2) (min (1 / 2) (delta / 6))
    linarith
  have hetaOne : eta < 1 := by
    dsimp [eta]
    have := (min_le_right (rho / 2) (min (1 / 2) (delta / 6))).trans
      (min_le_left (1 / 2) (delta / 6))
    linarith
  have hetaDelta : eta < delta / 3 := by
    dsimp [eta]
    have := (min_le_right (rho / 2) (min (1 / 2) (delta / 6))).trans
      (min_le_right (1 / 2) (delta / 6))
    linarith
  have hmatching :=
    (locallyFell_matchingPoints hdelta hclosedS hclosedL hsepS hsepL).mp
      hconv' C hCcompact eta heta hetaDelta
  filter_upwards [hmatching] with n hn
  let m : Tiling.Plane → Tiling.Plane := fun x ↦
    if hx : x ∈ L ∩ C then Classical.choose (hn.1 x hx) else x
  have hm_spec (x : Tiling.Plane) (hx : x ∈ L ∩ C) :
      m x ∈ S n ∧ dist x (m x) < eta := by
    rw [show m x = Classical.choose (hn.1 x hx) by simp [m, hx.1, hx.2]]
    exact (Classical.choose_spec (hn.1 x hx)).1
  have hm_injective : Set.InjOn m (L ∩ C) := by
    intro x hx y hy hmxy
    by_contra hxy
    have hsep := hsepL hx.1 hy.1 hxy
    have hxclose := (hm_spec x hx).2
    have hyclose := (hm_spec y hy).2
    have htri := dist_triangle x (m x) y
    rw [hmxy] at htri
    have hxclose' : dist x (m y) < eta := by simpa only [hmxy] using hxclose
    have hym : dist (m y) y < eta := by simpa [dist_comm] using hyclose
    have : dist x y < 2 * eta := lt_of_le_of_lt htri (by linarith)
    linarith
  let B : Finset Tiling.Plane := A.image m
  have hpointL :
      Tiling.AxisParallel.Topology.pointSum F L = ∑ x ∈ A, F x := by
    apply pointSum_eq_sum_of_zero_outside F L C hLfinite
    intro x hxL hxC
    apply Function.notMem_support.mp
    intro hxSupport
    exact hxC (hsupportC (subset_tsupport F hxSupport))
  have hBS : (B : Set Tiling.Plane) ⊆ S n := by
    intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨x, hxA, rfl⟩ := hy
    exact (hm_spec x (hLfinite.mem_toFinset.mp hxA)).1
  have hinter : S n ∩ (B : Set Tiling.Plane) = (B : Set Tiling.Plane) :=
    inter_eq_right.mpr hBS
  have hBfinite : (S n ∩ (B : Set Tiling.Plane)).Finite := by
    rw [hinter]
    exact B.finite_toSet
  have hpointS :
      Tiling.AxisParallel.Topology.pointSum F (S n) = ∑ y ∈ B, F y := by
    have h := pointSum_eq_sum_of_zero_outside F (S n)
      (B : Set Tiling.Plane) hBfinite (by
        intro y hyS hyB
        apply Function.notMem_support.mp
        intro hySupport
        have hyC : y ∈ C := hsupportC (subset_tsupport F hySupport)
        obtain ⟨x, ⟨hxL, hxy⟩, _⟩ := hn.2 y ⟨hyS, hyC⟩
        have hxC : x ∈ C := by
          rw [Metric.mem_closedBall]
          have hyR := Metric.mem_ball.mp (hR (subset_tsupport F hySupport))
          have htri := dist_triangle x y 0
          linarith
        have hmxy : m x = y := by
          rw [show m x = Classical.choose (hn.1 x ⟨hxL, hxC⟩) by
            simp [m, hxL, hxC]]
          exact ((Classical.choose_spec (hn.1 x ⟨hxL, hxC⟩)).2 y
            ⟨hyS, hxy⟩).symm
        apply hyB
        rw [Finset.mem_coe, Finset.mem_image]
        exact ⟨x, hLfinite.mem_toFinset.mpr ⟨hxL, hxC⟩, hmxy⟩)
    simpa [hinter] using h
  rw [Function.comp_apply, hpointS, hpointL]
  rw [show ∑ y ∈ B, F y = ∑ x ∈ A, F (m x) by
    dsimp [B]
    rw [Finset.sum_image]
    intro x hx y hy hmxy
    exact hm_injective (hLfinite.mem_toFinset.mp hx)
      (hLfinite.mem_toFinset.mp hy) hmxy]
  change |∑ x ∈ A, F (m x) - ∑ x ∈ A, F x| < tolerance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ x ∈ A, (F (m x) - F x)| ≤
        ∑ x ∈ A, |F (m x) - F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ A, termTolerance := by
      apply Finset.sum_le_sum
      intro x hx
      have hxLC := hLfinite.mem_toFinset.mp hx
      have hmx := hm_spec x hxLC
      have hxC' : x ∈ C' := hCC' hxLC.2
      have hmxC' : m x ∈ C' := by
        rw [Metric.mem_closedBall]
        have hxbound := Metric.mem_closedBall.mp hxLC.2
        have htri := dist_triangle (m x) x 0
        have hmxclose : dist (m x) x < eta := by
          simpa [dist_comm] using hmx.2
        linarith
      simpa [Real.dist_eq, abs_sub_comm] using
        (hFrho x hxC' (m x) hmxC' (hmx.2.trans hetaRho)).le
    _ < tolerance := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp [termTolerance]
      have hdenom : (0 : ℝ) < A.card + 1 := by positivity
      calc
        (A.card : ℝ) * (tolerance / (A.card + 1)) <
            ((A.card : ℝ) + 1) * (tolerance / (A.card + 1)) := by
          apply mul_lt_mul_of_pos_right
          · linarith
          · exact div_pos htolerance hdenom
        _ = tolerance := by field_simp

/-- The target-relative tiling equation is closed under local Fell convergence of the centres. -/
theorem tilesOn_isClosed
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    {T : ℕ → Set Tiling.Plane} {L : Set Tiling.Plane}
    (hT : ∀ n : ℕ, Tiling.AxisParallel.TilesOn K (T n) E)
    (hconv : Tiling.AxisParallel.Topology.LocallyFellConverges T L) :
    Tiling.AxisParallel.TilesOn K L E := by
  have hPacking : Tiling.IsPacking K.toPolygonalRegion.prototileFamily
      (K.toPolygonalRegion.placements L) :=
    isPacking_of_locallyFellConverges (fun n ↦ (hT n).2.1) hconv
  have hLocal :=
    Tiling.AxisParallel.IsPacking.locallyFinite_centres hPacking
  let _ : Countable ↥L := hLocal.2.to_subtype
  have hBoundaryNull : MeasureTheory.volume
      (⋃ s : L, (s.1 : Tiling.Plane) +ᵥ frontier K.support) = 0 := by
    apply measure_iUnion_null
    intro s
    simpa only [MeasureTheory.measure_vadd] using K.isPolygonal.volume_frontier
  have hNoBoundary : ∀ᵐ x : Tiling.Plane ∂MeasureTheory.volume,
      x ∉ ⋃ s : L, (s.1 : Tiling.Plane) +ᵥ frontier K.support :=
    measure_eq_zero_iff_ae_notMem.mp hBoundaryNull
  have hEveryTarget : ∀ᵐ x : Tiling.Plane ∂MeasureTheory.volume,
      ∀ n : ℕ, (x ∈ E ↔ ∃ s : T n,
        x ∈ ((s : Tiling.Plane) +ᵥ K.openCarrier)) :=
    ae_all_iff.mpr fun n ↦ (hT n).2.2
  refine ⟨hLocal.2, hPacking, ?_⟩
  filter_upwards [hEveryTarget, hNoBoundary] with x hxTarget hxBoundary
  constructor
  · intro hxE
    by_contra hxOpen
    let C : Set Tiling.Plane :=
      (fun y : Tiling.Plane ↦ x - y) '' K.support
    have hCcompact : IsCompact C :=
      K.isPolygonal.isCompact.image (continuous_const.sub continuous_id)
    have hLC : Disjoint L C := by
      rw [Set.disjoint_left]
      intro l hlL hlC
      rcases hlC with ⟨y, hyK, hyl⟩
      change x - y = l at hyl
      have hxy : x - l = y := by
        calc
          x - l = x - (x - y) := by rw [hyl]
          _ = y := sub_sub_cancel x y
      by_cases hyInterior : y ∈ interior K.support
      · apply hxOpen
        refine ⟨⟨l, hlL⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        rw [add_comm, ← sub_eq_add_neg, hxy]
        simpa only [Tiling.AxisParallel.Region.openCarrier,
          Tiling.RationalPolygonal.PolygonalRegion.openCarrier] using hyInterior
      · have hyFrontier : y ∈ frontier K.support :=
          (mem_frontier_iff_notMem_interior hyK).mpr hyInterior
        apply hxBoundary
        rw [Set.mem_iUnion]
        refine ⟨⟨l, hlL⟩, ?_⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem]
        simp only [vadd_eq_add]
        rw [add_comm, ← sub_eq_add_neg, hxy]
        exact hyFrontier
    have hEventually := locallyFellConverges_eventually_disjoint_compact
      hconv hCcompact hLC
    obtain ⟨n, hn⟩ := hEventually.exists
    obtain ⟨s, hsCover⟩ := (hxTarget n).mp hxE
    have hsC : (s : Tiling.Plane) ∈ C := by
      refine ⟨x - (s : Tiling.Plane), ?_, ?_⟩
      · rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsCover
        simp only [vadd_eq_add] at hsCover
        exact interior_subset (by
          simpa only [Tiling.AxisParallel.Region.openCarrier,
            Tiling.RationalPolygonal.PolygonalRegion.openCarrier,
            sub_eq_add_neg, add_comm] using hsCover)
      · abel_nf
    exact Set.disjoint_left.mp hn s.2 hsC
  · intro hxOpen
    change ∃ s : L, x ∈ (s : Tiling.Plane) +ᵥ K.openCarrier at hxOpen
    obtain ⟨s, hsOpen⟩ := hxOpen
    let U : Set Tiling.Plane := {c | x - c ∈ K.openCarrier}
    have hUopen : IsOpen U :=
      K.openCarrier_regularOpen.1.preimage (continuous_const.sub continuous_id)
    have hsU : (s : Tiling.Plane) ∈ U := by
      rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hsOpen
      simp only [vadd_eq_add] at hsOpen
      simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hsOpen
    obtain ⟨epsilon, hepsilon, hballU⟩ :=
      Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
    have hEventually := locallyFellConverges_eventually_exists_mem_ball
      hconv s.2 hepsilon
    obtain ⟨n, y, hyT, hydist⟩ := hEventually.exists
    apply (hxTarget n).mpr
    refine ⟨⟨y, hyT⟩, ?_⟩
    have hyU : y ∈ U := hballU (Metric.mem_ball.mpr hydist)
    rw [Set.mem_vadd_set_iff_neg_vadd_mem]
    simp only [vadd_eq_add]
    simpa only [U, Set.mem_ofPred_eq, sub_eq_add_neg, add_comm] using hyU

/-- Every sequence of fixed-target tilings has a Fell-convergent tiling subsequence. -/
theorem exists_tilesOn_locallyFellSubsequence
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : ℕ → Set Tiling.Plane)
    (hT : ∀ n : ℕ, Tiling.AxisParallel.TilesOn K (T n) E) :
    ∃ (phi : ℕ → ℕ) (L : Set Tiling.Plane),
      StrictMono phi ∧ Tiling.AxisParallel.TilesOn K L E ∧ IsClosed L ∧
      Tiling.AxisParallel.Topology.LocallyFellConverges (T ∘ phi) L ∧
      ∀ a : Tiling.Plane, (∀ n : ℕ, a ∈ T (phi n)) → a ∈ L := by
  obtain ⟨delta, hdelta, hseparation⟩ := tilesOn_uniformlySeparated K
  have hclosed (n : ℕ) : IsClosed (T n) := by
    exact Metric.isClosed_of_pairwise_le_dist hdelta
      (hseparation E (T n) (hT n))
  obtain ⟨phi, L, hphi, hLclosed, _hLseparated, hconv⟩ :=
    Tiling.AxisParallel.Foundations.exists_locallyFellConvergent_subsequence
      delta hdelta T hclosed (fun n ↦ hseparation E (T n) (hT n))
  have hLTiles : Tiling.AxisParallel.TilesOn K L E :=
    tilesOn_isClosed (fun n ↦ hT (phi n)) hconv
  refine ⟨phi, L, hphi, hLTiles, hLclosed, hconv, ?_⟩
  intro a ha
  by_contra haL
  have hdisjoint : Disjoint L ({a} : Set Tiling.Plane) := by
    rw [Set.disjoint_singleton_right]
    exact haL
  have hEventually := locallyFellConverges_eventually_disjoint_compact hconv
    (isCompact_singleton : IsCompact ({a} : Set Tiling.Plane)) hdisjoint
  obtain ⟨n, hn⟩ := hEventually.exists
  exact Set.disjoint_left.mp hn (ha n) (Set.mem_singleton a)

/-- The space of fixed-carrier tilings is compact in its Fell metric. -/
theorem tilingSpace_compact
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    IsCompact (Set.univ : Set (Tiling.AxisParallel.Topology.TilingSpace K E)) := by
  rw [isCompact_iff_isSeqCompact]
  intro U _hU
  let centres : ℕ → Set Tiling.Plane := fun n ↦ (U n).centres
  obtain ⟨phi, L, hphi, hLTiles, hLclosed, hconv, _⟩ :=
    exists_tilesOn_locallyFellSubsequence centres (fun n ↦ (U n).tilesOn)
  let V : Tiling.AxisParallel.Topology.TilingSpace K E :=
    ⟨⟨L, hLclosed⟩, hLTiles⟩
  refine ⟨V, Set.mem_univ V, phi, hphi, ?_⟩
  apply (locallyFell_metrizable K E).2 (U ∘ phi) V |>.mpr
  change Tiling.AxisParallel.Topology.LocallyFellConverges
    (fun n ↦ ((U (phi n)).centres : Set Tiling.Plane)) L
  simpa [centres, Function.comp_def] using hconv

private def onePointTranslate :
    Tiling.Plane × OnePoint Tiling.Plane → OnePoint Tiling.Plane
  | (_, OnePoint.infty) => OnePoint.infty
  | (g, (x : Tiling.Plane)) => ((x + g : Tiling.Plane) : OnePoint Tiling.Plane)

private theorem onePointTranslate_continuous : Continuous onePointTranslate := by
  rw [continuous_iff_continuousAt]
  rintro ⟨g, z⟩
  induction z using OnePoint.rec with
  | coe x =>
      rw [continuousAt_def]
      intro A hA
      obtain ⟨A₀, hA₀A, hA₀open, hxgA₀⟩ := mem_nhds_iff.mp hA
      let B : Set Tiling.Plane :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' A₀
      have hBopen : IsOpen B := hA₀open.preimage OnePoint.continuous_coe
      have hxgB : x + g ∈ B := hxgA₀
      let H : Set (Tiling.Plane × Tiling.Plane) :=
        (fun p ↦ p.2 + p.1) ⁻¹' B
      have hHnhds : H ∈ 𝓝 (g, x) :=
        (continuous_snd.add continuous_fst).continuousAt.preimage_mem_nhds
          (hBopen.mem_nhds hxgB)
      obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp hHnhds
      let V' : Set (OnePoint Tiling.Plane) :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' V
      have hV' : V' ∈ 𝓝 (x : OnePoint Tiling.Plane) := by
        rw [OnePoint.nhds_coe_eq]
        exact Filter.image_mem_map hV
      apply Filter.mem_of_superset (prod_mem_nhds hU hV')
      rintro ⟨g', z'⟩ ⟨hg', hz'⟩
      rcases hz' with ⟨x', hx', rfl⟩
      apply hA₀A
      exact hUV (show (g', x') ∈ U ×ˢ V from ⟨hg', hx'⟩)
  | infty =>
      rw [continuousAt_def]
      intro A hA
      obtain ⟨A₀, hA₀A, hA₀open, hinftyA₀⟩ := mem_nhds_iff.mp hA
      let C : Set Tiling.Plane :=
        ((fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) ⁻¹' A₀)ᶜ
      have hC : IsClosed C ∧ IsCompact C :=
        (OnePoint.isOpen_iff_of_mem hinftyA₀).mp hA₀open
      let U : Set Tiling.Plane := Metric.ball g 1
      let D : Set Tiling.Plane :=
        (fun p : Tiling.Plane × Tiling.Plane ↦ p.1 - p.2) ''
          (C ×ˢ Metric.closedBall g 1)
      have hDcompact : IsCompact D :=
        (hC.2.prod (isCompact_closedBall g 1)).image
          (continuous_fst.sub continuous_snd)
      have hDclosed : IsClosed D := hDcompact.isClosed
      let V : Set (OnePoint Tiling.Plane) :=
        (fun y : Tiling.Plane ↦ (y : OnePoint Tiling.Plane)) '' Dᶜ ∪
          {OnePoint.infty}
      have hV : V ∈ 𝓝 (OnePoint.infty : OnePoint Tiling.Plane) := by
        exact OnePoint.hasBasis_nhds_infty.mem_iff.mpr
          ⟨D, ⟨hDclosed, hDcompact⟩, Subset.rfl⟩
      have hU : U ∈ 𝓝 g := Metric.ball_mem_nhds g zero_lt_one
      apply Filter.mem_of_superset (prod_mem_nhds hU hV)
      rintro ⟨g', z'⟩ ⟨hg', hz'⟩
      apply hA₀A
      induction z' using OnePoint.rec with
      | infty => exact hinftyA₀
      | coe x =>
          have hxD : x ∉ D := by
            simpa [V] using hz'
          have hxgC : x + g' ∉ C := by
            intro hxgC
            apply hxD
            refine ⟨(x + g', g'), ⟨hxgC, ?_⟩, ?_⟩
            · exact Metric.mem_closedBall.mpr
                (le_of_lt (Metric.mem_ball.mp (show g' ∈ U from hg')))
            · simp only
              abel
          exact not_not.mp hxgC

private theorem fellCompactification_translate
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (g : Tiling.AxisParallel.aePeriodGroup E)
    (T : Tiling.AxisParallel.Topology.TilingSpace K E) :
    Tiling.AxisParallel.Topology.fellCompactification
        ((Tiling.AxisParallel.Topology.TilingSpace.translate g T).centres :
          Set Tiling.Plane)
        (Tiling.AxisParallel.Topology.TilingSpace.translate g T).centres.isClosed =
      TopologicalSpace.NonemptyCompacts.map
        ((Homeomorph.addRight (g : Tiling.Plane)).onePointCongr)
        ((Homeomorph.addRight (g : Tiling.Plane)).onePointCongr.continuous)
        (Tiling.AxisParallel.Topology.fellCompactification
          (T.centres : Set Tiling.Plane) T.centres.isClosed) := by
  apply TopologicalSpace.NonemptyCompacts.ext
  change
    ((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) ''
          ((fun x : Tiling.Plane ↦ x + (g : Tiling.Plane)) ''
            (T.centres : Set Tiling.Plane)) ∪ {OnePoint.infty}) =
      ((Homeomorph.addRight (g : Tiling.Plane)).onePointCongr ''
        (((fun x : Tiling.Plane ↦ (x : OnePoint Tiling.Plane)) ''
          (T.centres : Set Tiling.Plane)) ∪ {OnePoint.infty}))
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe x =>
      simp only [Set.mem_union, Set.mem_image, Set.mem_singleton_iff,
        OnePoint.coe_ne_infty, or_false, Homeomorph.onePointCongr]
      constructor
      · rintro ⟨y, ⟨t, ht, hty⟩, hyx⟩
        subst y
        refine ⟨(t : OnePoint Tiling.Plane), Or.inl ⟨t, ht, rfl⟩, ?_⟩
        exact hyx
      · rintro ⟨z, hz, hzx⟩
        rcases hz with ⟨t, ht, rfl⟩ | rfl
        · exact ⟨t + (g : Tiling.Plane), ⟨t, ht, rfl⟩, hzx⟩
        · simp at hzx

private theorem tilingSpace_translate_continuous
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (g : Tiling.AxisParallel.aePeriodGroup E) :
    Continuous (Tiling.AxisParallel.Topology.TilingSpace.translate g :
      Tiling.AxisParallel.Topology.TilingSpace K E →
        Tiling.AxisParallel.Topology.TilingSpace K E) := by
  rw [continuous_iff_seqContinuous]
  intro U V hUV
  apply (locallyFell_metrizable K E).2
      (Tiling.AxisParallel.Topology.TilingSpace.translate g ∘ U)
      (Tiling.AxisParallel.Topology.TilingSpace.translate g V) |>.mpr
  obtain ⟨hUclosed, hVclosed, hFell⟩ :=
    (locallyFell_metrizable K E).2 U V |>.mp hUV
  let mapCompact := TopologicalSpace.NonemptyCompacts.map
    ((Homeomorph.addRight (g : Tiling.Plane)).onePointCongr)
    ((Homeomorph.addRight (g : Tiling.Plane)).onePointCongr.continuous)
  have hmap : Continuous mapCompact :=
    (Homeomorph.addRight (g : Tiling.Plane)).onePointCongr.continuous.nonemptyCompacts_map
  have hmapped := (hmap.tendsto
    (Tiling.AxisParallel.Topology.fellCompactification
      (V.centres : Set Tiling.Plane) hVclosed)).comp hFell
  refine ⟨fun n ↦ (Tiling.AxisParallel.Topology.TilingSpace.translate g (U n)).centres.isClosed,
    (Tiling.AxisParallel.Topology.TilingSpace.translate g V).centres.isClosed, ?_⟩
  simpa [Tiling.AxisParallel.Topology.TilingSpace.centresSequence,
    Function.comp_def, mapCompact, fellCompactification_translate] using hmapped

/-- Translation of a fixed-carrier tiling depends continuously on both the carrier period and the
tiling. -/
theorem translationAction_continuous
    (K : Tiling.AxisParallel.Region) (E : Set Tiling.Plane) :
    Continuous
      (Tiling.AxisParallel.Topology.TilingSpace.translationAction K E) := by
  let compactify : Tiling.AxisParallel.Topology.TilingSpace K E →
      TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) := fun U ↦
    Tiling.AxisParallel.Topology.fellCompactification
      (U.centres : Set Tiling.Plane) U.centres.isClosed
  let compactifyAction :
      Tiling.AxisParallel.aePeriodGroup E ×
          Tiling.AxisParallel.Topology.TilingSpace K E →
        TopologicalSpace.NonemptyCompacts (OnePoint Tiling.Plane) := fun p ↦
    TopologicalSpace.NonemptyCompacts.map
      (fun z ↦ onePointTranslate ((p.1 : Tiling.Plane), z))
      (by
        exact onePointTranslate_continuous.comp
          (continuous_const.prodMk continuous_id))
      (compactify p.2)
  have hcompactify : Continuous compactify := continuous_induced_dom
  have hmap : Continuous compactifyAction := by
    apply Continuous.nonemptyCompacts_map'
    · exact hcompactify.comp continuous_snd
    · apply onePointTranslate_continuous.comp
      exact
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk
          continuous_snd)
  apply (continuous_induced_rng (f := compactify)).mpr
  have heq : compactify ∘
      Tiling.AxisParallel.Topology.TilingSpace.translationAction K E =
        compactifyAction := by
    funext p
    apply TopologicalSpace.NonemptyCompacts.ext
    ext z
    induction z using OnePoint.rec with
    | infty =>
        simp [compactify, compactifyAction, onePointTranslate,
          Tiling.AxisParallel.Topology.TilingSpace.translationAction,
          Tiling.AxisParallel.Topology.TilingSpace.translate,
          Tiling.AxisParallel.Topology.fellCompactification,
          Tiling.Topology.fellCompactification]
    | coe x =>
        simp only [Tiling.AxisParallel.Topology.fellCompactification,
          Tiling.Topology.fellCompactification, union_singleton,
          comp_apply, Tiling.AxisParallel.Topology.TilingSpace.translationAction,
          Tiling.AxisParallel.Topology.TilingSpace.translate, image_add_right,
          TopologicalSpace.Closeds.coe_mk, TopologicalSpace.NonemptyCompacts.coe_mk,
          TopologicalSpace.Compacts.coe_mk, mem_insert_iff, OnePoint.coe_ne_infty,
          mem_image, mem_preimage, SetLike.mem_coe, OnePoint.some_eq_iff,
          exists_eq_right, false_or, onePointTranslate,
          TopologicalSpace.NonemptyCompacts.coe_map, exists_eq_or_imp,
          OnePoint.infty_ne_coe, ↓existsAndEq, and_true, compactify, compactifyAction]
        constructor
        · intro hx
          refine ⟨x - (p.1 : Tiling.Plane), hx, ?_⟩
          abel
        · rintro ⟨y, hy, hyx⟩
          have hxy : x - (p.1 : Tiling.Plane) = y := by
            rw [← hyx]
            abel
          change x - (p.1 : Tiling.Plane) ∈ (p.2.centres : Set Tiling.Plane)
          rw [hxy]
          exact hy
  rw [heq]
  exact hmap

/-- Orbit hulls are compact, nonempty, and invariant under every carrier symmetry. -/
theorem orbitHull_compact
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : Tiling.AxisParallel.Topology.TilingSpace K E) :
    IsCompact (Tiling.AxisParallel.Topology.orbitHull T) ∧
    (Tiling.AxisParallel.Topology.orbitHull T).Nonempty ∧
    ∀ g : Tiling.AxisParallel.aePeriodGroup E,
      Tiling.AxisParallel.Topology.TilingSpace.translate g ''
        Tiling.AxisParallel.Topology.orbitHull T =
          Tiling.AxisParallel.Topology.orbitHull T := by
  let G := Tiling.AxisParallel.aePeriodGroup E
  let X := Tiling.AxisParallel.Topology.TilingSpace K E
  have hcompact : IsCompact (Tiling.AxisParallel.Topology.orbitHull T) :=
    (tilingSpace_compact K E).of_isClosed_subset isClosed_closure (subset_univ _)
  have hnonempty : (Tiling.AxisParallel.Topology.orbitHull T).Nonempty :=
    ⟨T, subset_closure (AddAction.mem_orbit_self T)⟩
  refine ⟨hcompact, hnonempty, fun g ↦ ?_⟩
  let e : X ≃ₜ X := {
    toFun := Tiling.AxisParallel.Topology.TilingSpace.translate g
    invFun := Tiling.AxisParallel.Topology.TilingSpace.translate (-g)
    left_inv U := by
      change (-g) +ᵥ (g +ᵥ U) = U
      rw [← add_vadd]
      simp
    right_inv U := by
      change g +ᵥ ((-g) +ᵥ U) = U
      rw [← add_vadd]
      simp
    continuous_toFun := tilingSpace_translate_continuous g
    continuous_invFun := tilingSpace_translate_continuous (-g)
  }
  change e '' closure (AddAction.orbit G T) =
    closure (AddAction.orbit G T)
  rw [e.image_closure]
  congr 1
  change g +ᵥ AddAction.orbit G T = AddAction.orbit G T
  exact AddAction.vadd_orbit g T

/-- Every compact orbit hull contains a minimal nonempty closed invariant subsystem. -/
theorem exists_minimalInvariantSubset
    {K : Tiling.AxisParallel.Region} {E : Set Tiling.Plane}
    (T : Tiling.AxisParallel.Topology.TilingSpace K E) :
    ∃ Y : Set (Tiling.AxisParallel.Topology.TilingSpace K E),
      Y ⊆ Tiling.AxisParallel.Topology.orbitHull T ∧ Y.Nonempty ∧ IsClosed Y ∧
      (∀ g : Tiling.AxisParallel.aePeriodGroup E,
        Tiling.AxisParallel.Topology.TilingSpace.translate g '' Y = Y) ∧
      Tiling.AxisParallel.Topology.IsTopologicallyMinimal Y := by
  let G := Tiling.AxisParallel.aePeriodGroup E
  let X := Tiling.AxisParallel.Topology.TilingSpace K E
  let H : Set X := Tiling.AxisParallel.Topology.orbitHull T
  let admissible : Set (Set X) :=
    {Y | Y ⊆ H ∧ Y.Nonempty ∧ IsClosed Y ∧
      ∀ g : G, Tiling.AxisParallel.Topology.TilingSpace.translate g '' Y = Y}
  have hHcompact : IsCompact H := orbitHull_compact T |>.1
  have hHadmissible : H ∈ admissible := by
    exact ⟨Subset.rfl, (orbitHull_compact T).2.1, isClosed_closure,
      (orbitHull_compact T).2.2⟩
  obtain ⟨Y, hYH, hYminimal⟩ := zorn_superset_nonempty admissible (by
    intro c hc hchain hcne
    refine ⟨⋂₀ c, ?_, fun S hS ↦ Set.sInter_subset_of_mem hS⟩
    have hsubset : ⋂₀ c ⊆ H := by
      obtain ⟨S, hS⟩ := hcne
      exact (Set.sInter_subset_of_mem hS).trans (hc hS).1
    have hnonempty : (⋂₀ c : Set X).Nonempty := by
      let _ : Nonempty ↥c := hcne.to_subtype
      rw [Set.sInter_eq_iInter]
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · exact DirectedOn.directed_val (IsChain.directedOn hchain.symm)
      · intro S
        exact (hc S.2).2.1
      · intro S
        exact hHcompact.of_isClosed_subset (hc S.2).2.2.1 (hc S.2).1
      · intro S
        exact (hc S.2).2.2.1
    have hclosed : IsClosed (⋂₀ c : Set X) :=
      isClosed_sInter fun S hS ↦ (hc hS).2.2.1
    have hinvariant (g : G) :
        Tiling.AxisParallel.Topology.TilingSpace.translate g '' (⋂₀ c : Set X) =
          ⋂₀ c := by
      apply Set.Subset.antisymm
      · rintro _ ⟨U, hU, rfl⟩
        rw [Set.mem_sInter]
        intro S hS
        have hmem : Tiling.AxisParallel.Topology.TilingSpace.translate g U ∈
            Tiling.AxisParallel.Topology.TilingSpace.translate g '' S :=
          ⟨U, Set.mem_sInter.mp hU S hS, rfl⟩
        rwa [(hc hS).2.2.2 g] at hmem
      · intro U hU
        let V : X := Tiling.AxisParallel.Topology.TilingSpace.translate (-g) U
        have hV : V ∈ ⋂₀ c := by
          rw [Set.mem_sInter]
          intro S hS
          have hmem : Tiling.AxisParallel.Topology.TilingSpace.translate (-g) U ∈
              Tiling.AxisParallel.Topology.TilingSpace.translate (-g) '' S :=
            ⟨U, Set.mem_sInter.mp hU S hS, rfl⟩
          rwa [(hc hS).2.2.2 (-g)] at hmem
        refine ⟨V, hV, ?_⟩
        change g +ᵥ ((-g) +ᵥ U) = U
        rw [← add_vadd]
        simp
    exact ⟨hsubset, hnonempty, hclosed, hinvariant⟩) H hHadmissible
  have hYdata := (minimal_iff.mp hYminimal).1
  refine ⟨Y, hYdata.1, hYdata.2.1, hYdata.2.2.1, hYdata.2.2.2, ?_⟩
  refine ⟨hYdata.2.1, hYdata.2.2.1, hYdata.2.2.2, ?_⟩
  intro U hUY
  let Z : Set X := Tiling.AxisParallel.Topology.orbitHull U
  have hZY : Z ⊆ Y := by
    apply closure_minimal
    · rintro V ⟨g, rfl⟩
      have hmem : Tiling.AxisParallel.Topology.TilingSpace.translate g U ∈
          Tiling.AxisParallel.Topology.TilingSpace.translate g '' Y :=
        ⟨U, hUY, rfl⟩
      rwa [hYdata.2.2.2 g] at hmem
    · exact hYdata.2.2.1
  have hZadmissible : Z ∈ admissible := by
    refine ⟨hZY.trans hYdata.1, (orbitHull_compact U).2.1,
      isClosed_closure, (orbitHull_compact U).2.2⟩
  exact ((minimal_iff.mp hYminimal).2 hZadmissible hZY).symm

end Tiling.AxisParallel.Continuous
