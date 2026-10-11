import Tiling.AxisParallel.Terminal.CommonPeriodAssembly.LinePeriodGroup
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Measure.ContinuousPreimage
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory Set
open scoped Pointwise Topology ENNReal symmDiff

noncomputable section

namespace Tiling.AxisParallel.Terminal

private def subtractRightMap (t : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x => x - t, continuous_id.sub continuous_const⟩

private lemma continuous_subtractRightMap : Continuous subtractRightMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.sub continuous_fst

private lemma preimage_subtractRightMap (t : ℝ) (B : Set ℝ) :
    subtractRightMap t ⁻¹' B = t +ᵥ B := by
  ext x
  constructor
  · intro hx
    exact ⟨x - t, hx, by simp⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [subtractRightMap] using hy

private lemma measurableSet_vadd (t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    MeasurableSet (t +ᵥ B) := by
  rw [← preimage_subtractRightMap]
  exact hB.preimage (subtractRightMap t).measurable

private lemma continuous_measureReal_symmDiff_translate
    {B : Set ℝ} (hB : MeasurableSet B) (hBb : Bornology.IsBounded B) (t₀ : ℝ) :
    Filter.Tendsto (fun t : ℝ => (volume ((t +ᵥ B) ∆ (t₀ +ᵥ B))).toReal)
      (𝓝 t₀) (𝓝 0) := by
  have hENN := tendsto_measure_symmDiff_preimage_nhds_zero
    (continuous_subtractRightMap.tendsto t₀)
    (Filter.Eventually.of_forall fun t => measurePreserving_add_right volume (-t))
    (measurePreserving_add_right volume (-t₀)) hB.nullMeasurableSet hBb.measure_lt_top.ne
  simp_rw [preimage_subtractRightMap] at hENN
  have hReal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hENN
  change Filter.Tendsto
    (fun t : ℝ => ENNReal.toReal (volume ((t +ᵥ B) ∆ (t₀ +ᵥ B))))
      (𝓝 t₀) (𝓝 (ENNReal.toReal 0)) at hReal
  simpa only [ENNReal.toReal_zero] using hReal

private lemma continuous_bounded_overlap
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : Bornology.IsBounded A) (hBb : Bornology.IsBounded B) :
    Continuous fun t : ℝ => (volume (A ∩ (t +ᵥ B))).toReal := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hsym := (continuous_measureReal_symmDiff_translate hB hBb t₀)
  apply tendsto_iff_dist_tendsto_zero.2
  have habs : Filter.Tendsto
      (fun t : ℝ => |(volume (A ∩ (t +ᵥ B))).toReal -
        (volume (A ∩ (t₀ +ᵥ B))).toReal|) (𝓝 t₀) (𝓝 0) := by
    refine squeeze_zero (fun _ => abs_nonneg _) (fun t => ?_) hsym
    calc
      |(volume (A ∩ (t +ᵥ B))).toReal -
          (volume (A ∩ (t₀ +ᵥ B))).toReal|
          ≤ (volume ((A ∩ (t +ᵥ B)) ∆ (A ∩ (t₀ +ᵥ B)))).toReal :=
            abs_measureReal_sub_le_measureReal_symmDiff'
              (hA.inter (measurableSet_vadd t hB)).nullMeasurableSet
              (hA.inter (measurableSet_vadd t₀ hB)).nullMeasurableSet
              (ne_top_of_le_ne_top hAb.measure_lt_top.ne (measure_mono inter_subset_left))
              (ne_top_of_le_ne_top hAb.measure_lt_top.ne (measure_mono inter_subset_left))
      _ = (volume (A ∩ ((t +ᵥ B) ∆ (t₀ +ᵥ B)))).toReal := by
            rw [inter_symmDiff_distrib_left]
      _ ≤ (volume ((t +ᵥ B) ∆ (t₀ +ᵥ B))).toReal :=
            measureReal_mono inter_subset_right
              (ne_top_of_le_ne_top
                ((hBb.vadd t).union (hBb.vadd t₀)).measure_lt_top.ne
                (measure_mono symmDiff_subset_union))
  simpa only [Real.dist_eq] using habs

theorem overlapCorrelation_continuous_of_left_bounded :
    ∀ {A Y : Set ℝ}, MeasurableSet A → MeasurableSet Y →
      Bornology.IsBounded A →
      Continuous fun t : ℝ => (volume (A ∩ (t +ᵥ Y))).toReal := by
  intro A Y hA hY hAb
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hAb
  let J : Set ℝ := Metric.closedBall (-t₀) (r + 1)
  have hJ : MeasurableSet J := measurableSet_closedBall
  have hJb : Bornology.IsBounded J := Metric.isBounded_closedBall
  have hlocal :
      (fun t : ℝ => (volume (A ∩ (t +ᵥ Y))).toReal) =ᶠ[𝓝 t₀]
        (fun t : ℝ => (volume (A ∩ (t +ᵥ (Y ∩ J)))).toReal) := by
    filter_upwards [Metric.ball_mem_nhds t₀ zero_lt_one] with t ht
    congr 2
    ext x
    constructor
    · rintro ⟨hxA, y, hyY, rfl⟩
      refine ⟨hxA, y, ⟨hyY, ?_⟩, rfl⟩
      have hxy : |t + y| < r := by
        simpa [Real.dist_eq] using hr hxA
      have htt : |t - t₀| < 1 := by
        simpa [Real.dist_eq] using ht
      change dist y (-t₀) ≤ r + 1
      rw [Real.dist_eq]
      calc
        |y - -t₀| = |(t + y) - (t - t₀)| := by ring_nf
        _ ≤ |t + y| + |t - t₀| := abs_sub _ _
        _ ≤ r + 1 := (add_lt_add hxy htt).le
    · rintro ⟨hxA, y, ⟨hyY, -⟩, rfl⟩
      exact ⟨hxA, y, hyY, rfl⟩
  exact ((continuous_bounded_overlap hA (hY.inter hJ) hAb
    (Bornology.IsBounded.subset hJb inter_subset_right)).continuousAt).congr_of_eventuallyEq
    hlocal

private lemma aePeriod_add {S : Set ℝ} {a c : ℝ}
    (ha : (a +ᵥ S) =ᵐ[volume] S) (hc : (c +ᵥ S) =ᵐ[volume] S) :
    ((a + c) +ᵥ S) =ᵐ[volume] S := by
  have htranslate :=
    (quasiMeasurePreserving_add_left volume (-a)).vadd_ae_eq_of_ae_eq a hc
  have hfirst : ((a + c) +ᵥ S) =ᵐ[volume] (a +ᵥ S) := by
    simpa only [add_vadd] using htranslate
  exact hfirst.trans ha

private lemma aePeriod_neg {S : Set ℝ} {a : ℝ}
    (ha : (a +ᵥ S) =ᵐ[volume] S) : ((-a) +ᵥ S) =ᵐ[volume] S := by
  have hq : Measure.QuasiMeasurePreserving (fun x : ℝ => -(-a) + x) volume volume := by
    simpa using quasiMeasurePreserving_add_left volume a
  have htranslate :=
    hq.vadd_ae_eq_of_ae_eq (-a) ha
  have hfirst : S =ᵐ[volume] ((-a) +ᵥ S) := by
    have hset : (-a) +ᵥ (a +ᵥ S) = S := by
      rw [vadd_vadd]
      simp
    rw [hset] at htranslate
    exact htranslate
  exact hfirst.symm

private def aePeriodGroup (S : Set ℝ) : AddSubgroup ℝ where
  carrier := {a | (a +ᵥ S) =ᵐ[volume] S}
  zero_mem' := by simpa using (ae_eq_refl S : S =ᵐ[volume] S)
  add_mem' := aePeriod_add
  neg_mem' := aePeriod_neg

private lemma aePeriod_zsmul {S : Set ℝ} {b : ℝ}
    (hb : (b +ᵥ S) =ᵐ[volume] S) (n : ℤ) :
    ((n • b) +ᵥ S) =ᵐ[volume] S := by
  exact (aePeriodGroup S).zsmul_mem hb n

private lemma restrict_periodic_vaddInvariant
    {Y : Set ℝ} {b : ℝ} (_hY : MeasurableSet Y)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) :
    VAddInvariantMeasure (AddSubgroup.zmultiples b) ℝ (volume.restrict Y) := by
  constructor
  rintro ⟨c, hc⟩ s hs
  rcases hc with ⟨n, hn⟩
  have hcY : (c +ᵥ Y) =ᵐ[volume] Y := by
    rw [← hn]
    exact aePeriod_zsmul hbY n
  have hpre :
      (fun x : ℝ => c + x) ⁻¹' s ∩ Y =
        (fun x : ℝ => c + x) ⁻¹' (s ∩ (c +ᵥ Y)) := by
    ext x
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hxs, hxY⟩
      exact ⟨hxs, ⟨x, hxY, rfl⟩⟩
    · rintro ⟨hxs, y, hyY, hxy⟩
      have : x = y := add_left_cancel hxy.symm
      exact ⟨hxs, this ▸ hyY⟩
  change (volume.restrict Y) ((fun x : ℝ => c + x) ⁻¹' s) =
    (volume.restrict Y) s
  calc
    (volume.restrict Y) ((fun x : ℝ => c + x) ⁻¹' s) =
        volume ((fun x : ℝ => c + x) ⁻¹' s ∩ Y) :=
      Measure.restrict_apply (hs.preimage (measurable_const.add measurable_id))
    _ = volume ((fun x : ℝ => c + x) ⁻¹' (s ∩ (c +ᵥ Y))) := by rw [hpre]
    _ = volume (s ∩ (c +ᵥ Y)) := measure_preimage_add volume c _
    _ = volume (s ∩ Y) := measure_congr (ae_eq_set_inter (ae_eq_refl s) hcY)
    _ = (volume.restrict Y) s := (Measure.restrict_apply hs).symm

private lemma periodic_cell_measure_eq
    {Y : Set ℝ} {b : ℝ} (hY : MeasurableSet Y) (hb : 0 < b)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) (x : ℝ) :
    volume (Y ∩ Ioc (x - b) x) = volume (Y ∩ Ioc 0 b) := by
  have : VAddInvariantMeasure (AddSubgroup.zmultiples b) ℝ (volume.restrict Y) :=
    restrict_periodic_vaddInvariant hY hbY
  have h0 := isAddFundamentalDomain_Ioc hb 0 (volume.restrict Y)
  have hx := isAddFundamentalDomain_Ioc hb (x - b) (volume.restrict Y)
  have heq := hx.measure_eq h0
  simp only [sub_add_cancel, zero_add, Measure.restrict_apply measurableSet_Ioc] at heq
  simpa only [inter_comm] using heq

private lemma setIntegral_indicator_one
    {Y C : Set ℝ} (hY : MeasurableSet Y) :
    (∫ x in C, Y.indicator (fun _ => (1 : ℝ)) x) =
      (volume (Y ∩ C)).toReal := by
  have h := integral_indicator_one (μ := volume.restrict C) hY
  rw [Measure.real, Measure.restrict_apply hY] at h
  exact h

private lemma overlap_measureReal_eq_integral
    {A Y : Set ℝ} (_hA : MeasurableSet A) (hY : MeasurableSet Y) (t : ℝ) :
    (volume (A ∩ (t +ᵥ Y))).toReal =
      ∫ x, Y.indicator (fun _ => (1 : ℝ)) (x - t) ∂volume.restrict A := by
  have hpre : (fun x : ℝ => x - t) ⁻¹' Y = t +ᵥ Y :=
    preimage_subtractRightMap t Y
  have hm : MeasurableSet ((fun x : ℝ => x - t) ⁻¹' Y) :=
    hY.preimage (measurable_id.sub measurable_const)
  have h := integral_indicator_one (μ := volume.restrict A) hm
  rw [Measure.real, Measure.restrict_apply hm, hpre, inter_comm] at h
  have hfun : (t +ᵥ Y).indicator (fun _ => (1 : ℝ)) =
      fun x => Y.indicator (fun _ => (1 : ℝ)) (x - t) := by
    funext x
    have hx : x ∈ t +ᵥ Y ↔ x - t ∈ Y := by
      rw [← hpre]
      rfl
    by_cases hxt : x ∈ t +ᵥ Y
    · simp [hxt, hx.mp hxt]
    · simp [hxt, mt hx.mpr hxt]
  change (∫ x in A, (t +ᵥ Y).indicator (fun _ => (1 : ℝ)) x) =
    (volume (A ∩ (t +ᵥ Y))).toReal at h
  rw [hfun] at h
  exact h.symm

private lemma periodic_fiber_integral
    {Y : Set ℝ} {b : ℝ} (hY : MeasurableSet Y) (hb : 0 < b)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) (x : ℝ) :
    (∫ t in Ioc 0 b, Y.indicator (fun _ => (1 : ℝ)) (x - t)) =
      (volume (Y ∩ Ioc 0 b)).toReal := by
  calc
    (∫ t in Ioc 0 b, Y.indicator (fun _ => (1 : ℝ)) (x - t)) =
        ∫ t in 0..b, Y.indicator (fun _ => (1 : ℝ)) (x - t) := by
      rw [intervalIntegral.integral_of_le hb.le]
    _ = ∫ t in x - b..x, Y.indicator (fun _ => (1 : ℝ)) t := by
      rw [intervalIntegral.integral_comp_sub_left, sub_zero]
    _ = ∫ t in Ioc (x - b) x, Y.indicator (fun _ => (1 : ℝ)) t := by
      rw [intervalIntegral.integral_of_le (sub_le_self x hb.le)]
    _ = (volume (Y ∩ Ioc (x - b) x)).toReal := setIntegral_indicator_one hY
    _ = (volume (Y ∩ Ioc 0 b)).toReal := by
      rw [periodic_cell_measure_eq hY hb hbY x]

theorem periodic_overlap_average :
    ∀ {A Y : Set ℝ} {b : ℝ},
      MeasurableSet A → MeasurableSet Y → Bornology.IsBounded A →
      0 < b → (b +ᵥ Y) =ᵐ[volume] Y →
      ∫ t in Set.Ioc 0 b, (volume (A ∩ (t +ᵥ Y))).toReal =
        (volume A).toReal * (volume (Y ∩ Set.Ioc 0 b)).toReal := by
  intro A Y b hA hY hAb hb hbY
  let F : ℝ × ℝ → ℝ := fun p => Y.indicator (fun _ => (1 : ℝ)) (p.2 - p.1)
  have hFm : StronglyMeasurable F := by
    exact (measurable_const.indicator hY).comp
      (measurable_snd.sub measurable_fst) |>.stronglyMeasurable
  have : IsFiniteMeasure (volume.restrict A) :=
    isFiniteMeasure_restrict.mpr hAb.measure_lt_top.ne
  have hFint : Integrable F
      ((volume.restrict (Ioc 0 b)).prod (volume.restrict A)) := by
    refine (integrable_const (μ :=
      (volume.restrict (Ioc 0 b)).prod (volume.restrict A)) (1 : ℝ)).mono'
      hFm.aestronglyMeasurable ?_
    filter_upwards with p
    by_cases hp : p.2 - p.1 ∈ Y <;> simp [F, hp]
  have hswap := integral_integral_swap (f := fun t x => F (t, x)) hFint
  have hleft :
      (∫ t in Ioc 0 b, (volume (A ∩ (t +ᵥ Y))).toReal) =
        ∫ t, ∫ x, F (t, x) ∂volume.restrict A ∂volume.restrict (Ioc 0 b) := by
    apply integral_congr_ae
    filter_upwards with t
    simpa only [F] using overlap_measureReal_eq_integral hA hY t
  have hright :
      (∫ x, ∫ t, F (t, x) ∂volume.restrict (Ioc 0 b) ∂volume.restrict A) =
        (volume A).toReal * (volume (Y ∩ Ioc 0 b)).toReal := by
    calc
      (∫ x, ∫ t, F (t, x) ∂volume.restrict (Ioc 0 b) ∂volume.restrict A) =
          ∫ x, (volume (Y ∩ Ioc 0 b)).toReal ∂volume.restrict A := by
        apply integral_congr_ae
        filter_upwards with x
        simpa only [F] using periodic_fiber_integral hY hb hbY x
      _ = (volume A).toReal * (volume (Y ∩ Ioc 0 b)).toReal := by
        rw [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ]
        simp
  exact hleft.trans (hswap.trans hright)

private lemma overlap_zero_of_mem_pairClosure
    {A X Y : Set ℝ} {a b d : ℝ}
    (hAX : A ⊆ X) (hXY : AEDisjoint volume X Y)
    (haX : (a +ᵥ X) =ᵐ[volume] X) (hbY : (b +ᵥ Y) =ᵐ[volume] Y)
    (hd : d ∈ AddSubgroup.closure ({a, b} : Set ℝ)) :
    volume (A ∩ (d +ᵥ Y)) = 0 := by
  rcases AddSubgroup.mem_closure_pair.mp hd with ⟨m, n, hmn⟩
  have hmX : ((m • a) +ᵥ X) =ᵐ[volume] X := aePeriod_zsmul haX m
  have hnY : ((n • b) +ᵥ Y) =ᵐ[volume] Y := aePeriod_zsmul hbY n
  have hq : Measure.QuasiMeasurePreserving
      (fun x : ℝ => -(m • a) + x) volume volume :=
    quasiMeasurePreserving_add_left volume (-(m • a))
  have htranslated := hXY.preimage hq
  have hpre (S : Set ℝ) : (fun x : ℝ => -(m • a) + x) ⁻¹' S =
      (m • a) +ᵥ S := by
    rw [← preimage_subtractRightMap]
    congr 1
    funext x
    simp [subtractRightMap]
    ring
  have htranslated' : AEDisjoint volume ((m • a) +ᵥ X) ((m • a) +ᵥ Y) := by
    rw [← hpre X, ← hpre Y]
    exact htranslated
  have hXshiftY : AEDisjoint volume X ((m • a) +ᵥ Y) :=
    htranslated'.congr hmX.symm (ae_eq_refl _)
  have hAshifY : AEDisjoint volume A ((m • a) +ᵥ Y) :=
    hXshiftY.mono hAX Subset.rfl
  have hdY : (d +ᵥ Y) =ᵐ[volume] ((m • a) +ᵥ Y) := by
    have htranslate :=
      (quasiMeasurePreserving_add_left volume (-(m • a))).vadd_ae_eq_of_ae_eq
        (m • a) hnY
    have htranslate' : (((m • a) + (n • b)) +ᵥ Y) =ᵐ[volume]
        ((m • a) +ᵥ Y) := by
      simpa only [add_vadd] using htranslate
    rw [hmn] at htranslate'
    exact htranslate'
  exact (hAshifY.congr (ae_eq_refl _) hdY).eq

private lemma periodic_cell_measureReal_pos
    {Y : Set ℝ} {b : ℝ} (hY : MeasurableSet Y) (hb : 0 < b)
    (hbY : (b +ᵥ Y) =ᵐ[volume] Y) (hYne : volume Y ≠ 0) :
    0 < (volume (Y ∩ Ioc 0 b)).toReal := by
  have hcellne : volume (Y ∩ Ioc 0 b) ≠ 0 := by
    intro hcell
    have : VAddInvariantMeasure (AddSubgroup.zmultiples b) ℝ (volume.restrict Y) :=
      restrict_periodic_vaddInvariant hY hbY
    have hfd := isAddFundamentalDomain_Ioc hb 0 (volume.restrict Y)
    have hsum := hfd.measure_eq_tsum (Set.univ : Set ℝ)
    simp only [zero_add] at hsum
    have hcell' : (volume.restrict Y) (Ioc 0 b) = 0 := by
      rw [Measure.restrict_apply measurableSet_Ioc, inter_comm, hcell]
    have hterms :
        (fun g : AddSubgroup.zmultiples b =>
          (volume.restrict Y) ((g +ᵥ (Set.univ : Set ℝ)) ∩ Ioc 0 b)) =
        fun _ => 0 := by
      funext g
      have hguniv : g +ᵥ (Set.univ : Set ℝ) = Set.univ := by
        apply eq_univ_of_forall
        intro x
        refine ⟨x - (g : ℝ), Set.mem_univ _, ?_⟩
        change (g : ℝ) + (x - (g : ℝ)) = x
        ring
      calc
        (volume.restrict Y) ((g +ᵥ (Set.univ : Set ℝ)) ∩ Ioc 0 b) =
            (volume.restrict Y) (Set.univ ∩ Ioc 0 b) := by rw [hguniv]
        _ = (volume.restrict Y) (Ioc 0 b) := by rw [univ_inter]
        _ = 0 := hcell'
    have hrhs : (∑' g : AddSubgroup.zmultiples b,
        (volume.restrict Y) ((g +ᵥ (Set.univ : Set ℝ)) ∩ Ioc 0 b)) = 0 := by
      rw [hterms, tsum_zero]
    rw [hrhs] at hsum
    apply hYne
    simpa [Measure.restrict_apply MeasurableSet.univ] using hsum
  have hCb : Bornology.IsBounded (Ioc 0 b) := by
    rw [Metric.isBounded_iff_subset_ball (0 : ℝ)]
    refine ⟨b + 1, ?_⟩
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1.le]
    linarith [hx.2]
  exact ENNReal.toReal_pos hcellne
    (Bornology.IsBounded.subset hCb inter_subset_right).measure_lt_top.ne

theorem disjointPeriodicLineSets_periods_commensurable :
    ∀ {X Y : Set ℝ} {a b : ℝ},
      MeasurableSet X → MeasurableSet Y →
      (∃ I : Set ℝ, Bornology.IsBounded I ∧
        0 < (volume (X ∩ I)).toReal) →
      (∃ I : Set ℝ, Bornology.IsBounded I ∧
        0 < (volume (Y ∩ I)).toReal) →
      MeasureTheory.AEDisjoint volume X Y →
      0 < a → 0 < b →
      (a +ᵥ X) =ᵐ[volume] X →
      (b +ᵥ Y) =ᵐ[volume] Y →
      ∃ q : ℚ, a = (q : ℝ) * b := by
  intro X Y a b hX hY hXpos hYpos hXY ha hb haX hbY
  rcases hXpos with ⟨IX, -, hIXpos⟩
  rcases hYpos with ⟨IY, -, hIYpos⟩
  have hXne : volume X ≠ 0 := volume_ne_zero_of_positive_inter hIXpos
  have hYne : volume Y ≠ 0 := volume_ne_zero_of_positive_inter hIYpos
  obtain ⟨A, hAm, hAb, hAX, hApos⟩ :=
    exists_boundedPositive_measurable_subset hX hXne
  by_contra hrat
  have hirr : Irrational (a / b) := by
    rw [Irrational]
    rintro ⟨q, hq⟩
    apply hrat
    refine ⟨q, ?_⟩
    calc
      a = (a / b) * b := (div_mul_cancel₀ a hb.ne').symm
      _ = (q : ℝ) * b := by rw [← hq]
  have hdense : Dense (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirr
  let H : ℝ → ℝ := fun t => (volume (A ∩ (t +ᵥ Y))).toReal
  have hHcont : Continuous H := overlapCorrelation_continuous_of_left_bounded hAm hY hAb
  have hzeroD :
      (AddSubgroup.closure ({a, b} : Set ℝ) : Set ℝ) ⊆ {t : ℝ | H t = 0} := by
    intro d hd
    change (volume (A ∩ (d +ᵥ Y))).toReal = 0
    rw [overlap_zero_of_mem_pairClosure hAX hXY haX hbY hd, ENNReal.toReal_zero]
  have hclosed : IsClosed {t : ℝ | H t = 0} :=
    isClosed_eq hHcont continuous_const
  have hall : ∀ t : ℝ, H t = 0 := by
    intro t
    exact (closure_minimal hzeroD hclosed) (hdense t)
  have havg := periodic_overlap_average hAm hY hAb hb hbY
  change (∫ t in Ioc 0 b, H t) =
    (volume A).toReal * (volume (Y ∩ Ioc 0 b)).toReal at havg
  have hleftzero : (∫ t in Ioc 0 b, H t) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with t
    exact hall t
  have hcellpos := periodic_cell_measureReal_pos hY hb hbY hYne
  rw [hleftzero] at havg
  nlinarith

end Tiling.AxisParallel.Terminal
