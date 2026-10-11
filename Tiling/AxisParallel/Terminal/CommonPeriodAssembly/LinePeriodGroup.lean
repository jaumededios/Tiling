/-
Copyright (c) 2026 The Tiling Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tiling Authors
-/
import Tiling.AxisParallel.Terminal.AssemblyCore
import Mathlib.Analysis.Convolution
import Mathlib.Topology.Algebra.Order.Archimedean
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Measure.ContinuousPreimage

/-!
# A.e. period groups of measurable subsets of the line

Translation continuity on bounded windows makes the a.e. period group closed.
A nonnull, nonconull periodic set consequently has a unique positive generator.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Function MeasureTheory Set
open scoped ENNReal Pointwise symmDiff Topology

noncomputable section

namespace Tiling.AxisParallel.Terminal

theorem volume_ne_zero_of_positive_inter :
    ∀ {X I : Set ℝ}, 0 < (volume (X ∩ I)).toReal → volume X ≠ 0 := by
  intro X I hpos hzero
  have hsub : X ∩ I ⊆ X := inter_subset_left
  have : volume (X ∩ I) = 0 := measure_mono_null hsub hzero
  simp [this] at hpos

theorem exists_boundedPositive_measurable_subset :
    ∀ {X : Set ℝ}, MeasurableSet X → volume X ≠ 0 →
      ∃ A : Set ℝ, MeasurableSet A ∧ Bornology.IsBounded A ∧
        A ⊆ X ∧ 0 < (volume A).toReal := by
  intro X hX hX0
  have hcover : X = ⋃ n : ℕ, X ∩ Set.Icc (-(n : ℝ)) n := by
    apply Set.ext
    intro x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt |x|
      refine ⟨n, hx, ?_, ?_⟩
      · exact (abs_lt.mp hn).1.le
      · exact (abs_lt.mp hn).2.le
    · rintro ⟨n, hx, -, -⟩
      exact hx
  have hex : ∃ n : ℕ, volume (X ∩ Set.Icc (-(n : ℝ)) n) ≠ 0 := by
    by_contra h
    push Not at h
    apply hX0
    rw [hcover]
    exact measure_iUnion_null h
  obtain ⟨n, hn⟩ := hex
  have hbdd : Bornology.IsBounded (Set.Icc (-(n : ℝ)) n) := by
    rw [Metric.isBounded_iff]
    refine ⟨2 * n, ?_⟩
    intro x hx y hy
    rw [Real.dist_eq]
    rcases hx with ⟨hx₁, hx₂⟩
    rcases hy with ⟨hy₁, hy₂⟩
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith
  refine ⟨X ∩ Set.Icc (-(n : ℝ)) n, hX.inter measurableSet_Icc,
    hbdd.subset inter_subset_right, inter_subset_left, ?_⟩
  apply ENNReal.toReal_pos hn
  exact ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    (measure_mono inter_subset_right)

private theorem positive_cyclic_generator_unique_aux
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hcd : ∃ n : ℤ, c = n • d) (hdc : ∃ m : ℤ, d = m • c) :
    c = d := by
  rcases hcd with ⟨n, hn⟩
  rcases hdc with ⟨m, hm⟩
  rw [zsmul_eq_mul] at hn hm
  have hnpos : 0 < n := by
    have hnreal : 0 < (n : ℝ) :=
      (mul_pos_iff_of_pos_right hd).mp (hn ▸ hc)
    exact_mod_cast hnreal
  have hmpos : 0 < m := by
    have hmreal : 0 < (m : ℝ) :=
      (mul_pos_iff_of_pos_right hc).mp (hm ▸ hd)
    exact_mod_cast hmreal
  have hprodReal : (((n * m : ℤ) : ℝ)) = 1 := by
    apply mul_right_cancel₀ hc.ne'
    calc
      (((n * m : ℤ) : ℝ)) * c = (n : ℝ) * ((m : ℝ) * c) := by
        push_cast
        ring
      _ = (n : ℝ) * d := by rw [← hm]
      _ = c := by rw [← hn]
      _ = 1 * c := by ring
  have hprod : n * m = 1 := by exact_mod_cast hprodReal
  have hn_one : n = 1 := by nlinarith [hprod]
  subst n
  simpa using hn

theorem positive_cyclic_generator_unique :
    ∀ {c d : ℝ}, 0 < c → 0 < d →
    (∀ a : ℝ, ((∃ n : ℤ, a = n • c) ↔ ∃ n : ℤ, a = n • d)) →
    c = d := by
  intro c d hc hd h
  apply positive_cyclic_generator_unique_aux hc hd
  · exact (h c).mp ⟨1, by simp⟩
  · exact (h d).mpr ⟨1, by simp⟩

private def subtractTranslation (a : ℝ) : C(ℝ, ℝ) :=
  ⟨fun x ↦ x - a, continuous_id.sub continuous_const⟩

private lemma continuous_subtractTranslation : Continuous subtractTranslation := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous fun p : ℝ × ℝ ↦ p.2 - p.1
  fun_prop

private lemma measurePreserving_subtractTranslation (a : ℝ) :
    MeasurePreserving (subtractTranslation a) volume volume := by
  simpa only [subtractTranslation, ContinuousMap.coe_mk, sub_eq_add_neg] using
    measurePreserving_add_right volume (-a)

private lemma preimage_truncation_inter_Icc
    {X : Set ℝ} {a M r : ℝ} (ha : |a| ≤ M) :
    (subtractTranslation a ⁻¹' (X ∩ Set.Icc (-(r + M)) (r + M))) ∩
        Set.Icc (-r) r =
      (a +ᵥ X) ∩ Set.Icc (-r) r := by
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Icc]
  constructor
  · rintro ⟨⟨hxX, -, -⟩, hxI⟩
    refine ⟨?_, hxI⟩
    simpa [subtractTranslation, mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg,
      add_comm] using hxX
  · rintro ⟨hxX, hxlo, hxhi⟩
    have hxX' : x - a ∈ X := by
      simpa [subtractTranslation, mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg,
        add_comm] using hxX
    have ha' := abs_le.mp ha
    refine ⟨⟨hxX', ?_, ?_⟩, hxlo, hxhi⟩
    · change -(r + M) ≤ x - a
      linarith
    · change x - a ≤ r + M
      linarith

theorem lineAEPeriodSet_isClosed : ∀ {X : Set ℝ}, MeasurableSet X →
    IsClosed {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} := by
  intro X hX
  apply IsSeqClosed.isClosed
  intro u a hperiod hu
  change ∀ n, (u n +ᵥ X) =ᵐ[volume] X at hperiod
  change (a +ᵥ X) =ᵐ[volume] X
  rw [← measure_symmDiff_eq_zero_iff]
  have hcover : ((a +ᵥ X) ∆ X) =
      ⋃ m : ℕ, ((a +ᵥ X) ∆ X) ∩ Set.Icc (-(m : ℝ)) m := by
    apply Set.ext
    intro x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := exists_nat_gt |x|
      exact ⟨m, hx, (abs_lt.mp hm).1.le, (abs_lt.mp hm).2.le⟩
    · rintro ⟨m, hx, -, -⟩
      exact hx
  rw [hcover]
  apply measure_iUnion_null
  intro m
  have hub : ∀ᶠ n in atTop, |u n| ≤ |a| + 1 := by
    have hnear : ∀ᶠ n in atTop, dist (u n) a < 1 :=
      (Metric.tendsto_nhds.mp hu) 1 zero_lt_one
    filter_upwards [hnear] with n hn
    rw [Real.dist_eq] at hn
    calc
      |u n| = |(u n - a) + a| := by ring_nf
      _ ≤ |u n - a| + |a| := abs_add_le _ _
      _ ≤ |a| + 1 := by linarith
  let I : Set ℝ := Set.Icc (-(m : ℝ)) m
  let J : Set ℝ :=
    Set.Icc (-((m : ℝ) + (|a| + 1))) ((m : ℝ) + (|a| + 1))
  let q : ℕ → ℝ≥0∞ := fun n ↦
    volume (((subtractTranslation (u n)) ⁻¹' (X ∩ J)) ∆
      ((subtractTranslation a) ⁻¹' (X ∩ J)))
  have hJm : NullMeasurableSet (X ∩ J) volume :=
    (hX.inter measurableSet_Icc).nullMeasurableSet
  have hJfin : volume (X ∩ J) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
      (measure_mono inter_subset_right)
  have hq : Tendsto q atTop (nhds 0) := by
    apply MeasureTheory.tendsto_measure_symmDiff_preimage_nhds_zero
      (X := ℝ) (Y := ℝ) (μ := volume) (ν := volume)
    · exact continuous_subtractTranslation.continuousAt.tendsto.comp hu
    · exact Filter.Eventually.of_forall
        (fun n ↦ measurePreserving_subtractTranslation (u n))
    · exact measurePreserving_subtractTranslation a
    · exact hJm
    · exact hJfin
  have hqbound : ∀ᶠ n in atTop,
      volume ((((a +ᵥ X) ∆ X) ∩ I)) ≤ q n := by
    filter_upwards [hub] with n hn
    have hun := preimage_truncation_inter_Icc (X := X) (r := (m : ℝ)) hn
    have ha_le : |a| ≤ |a| + 1 := by linarith
    have ha' := preimage_truncation_inter_Icc (X := X) (r := (m : ℝ)) ha_le
    have hpI : (((u n +ᵥ X) ∩ I : Set ℝ) : ℝ → Prop) =ᵐ[volume]
        (((X ∩ I : Set ℝ) : ℝ → Prop)) :=
      (hperiod n).inter (Filter.EventuallyEq.refl (ae volume) (I : ℝ → Prop))
    have hsymmI : (((a +ᵥ X) ∆ X) ∩ I) =
        (((a +ᵥ X) ∩ I) ∆ (X ∩ I)) := by
      ext x
      simp only [mem_inter_iff, mem_symmDiff]
      tauto
    calc
      volume (((a +ᵥ X) ∆ X) ∩ I) =
          volume (((a +ᵥ X) ∩ I) ∆ (X ∩ I)) := congrArg volume hsymmI
      _ = volume (((a +ᵥ X) ∩ I) ∆ ((u n +ᵥ X) ∩ I)) :=
        measure_congr
          ((Filter.EventuallyEq.refl (ae volume)
            ((((a +ᵥ X) ∩ I : Set ℝ) : ℝ → Prop))).symmDiff hpI.symm)
      _ = volume (((u n +ᵥ X) ∩ I) ∆ ((a +ᵥ X) ∩ I)) := by
        rw [symmDiff_comm]
      _ = volume (((((subtractTranslation (u n)) ⁻¹' (X ∩ J)) ∆
          ((subtractTranslation a) ⁻¹' (X ∩ J))) ∩ I)) := by
        rw [inter_symmDiff_distrib_right, hun, ha']
      _ ≤ q n := measure_mono inter_subset_left
  exact bot_unique (ge_of_tendsto hq hqbound)

private def setIndicator (A : Set ℝ) : ℝ → ℝ :=
  A.indicator fun _ ↦ 1

private lemma integrable_setIndicator {A : Set ℝ}
    (hA : MeasurableSet A) (hAbdd : Bornology.IsBounded A) :
    Integrable (setIndicator A) := by
  rw [setIndicator, integrable_indicator_iff hA]
  exact integrableOn_const hAbdd.measure_lt_top.ne

private lemma convolution_setIndicator_eq_overlap
    {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (_hAbdd : Bornology.IsBounded A) (_hBbdd : Bornology.IsBounded B) (t : ℝ) :
    MeasureTheory.convolution (setIndicator A) (setIndicator (-B))
        (ContinuousLinearMap.mul ℝ ℝ) volume t =
      (volume (A ∩ (t +ᵥ B))).toReal := by
  rw [MeasureTheory.convolution]
  change _ = volume.real (A ∩ (t +ᵥ B))
  rw [← integral_indicator_one (hA.inter (hB.const_vadd t))]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxA : x ∈ A
  · by_cases hxB : x ∈ t +ᵥ B
    · have hneg : t - x ∈ -B := by
        simpa [mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hxB
      simp [setIndicator, hxA, hxB, hneg]
    · have hneg : t - x ∉ -B := by
        contrapose! hxB
        simpa [mem_vadd_set_iff_neg_vadd_mem, sub_eq_add_neg, add_comm] using hxB
      simp [setIndicator, hxA, hxB, hneg]
  · simp [setIndicator, hxA]

theorem translateOverlap_integral : ∀ {A B : Set ℝ},
    MeasurableSet A → MeasurableSet B →
    Bornology.IsBounded A → Bornology.IsBounded B →
    ∫ t : ℝ, (volume (A ∩ (t +ᵥ B))).toReal =
      (volume A).toReal * (volume B).toReal := by
  intro A B hA hB hAbdd hBbdd
  have hiA : Integrable (setIndicator A) := integrable_setIndicator hA hAbdd
  have hiB : Integrable (setIndicator (-B)) :=
    integrable_setIndicator hB.neg hBbdd.neg
  calc
    ∫ t : ℝ, (volume (A ∩ (t +ᵥ B))).toReal =
        ∫ t : ℝ, MeasureTheory.convolution (setIndicator A) (setIndicator (-B))
          (ContinuousLinearMap.mul ℝ ℝ) volume t := by
      apply integral_congr_ae
      filter_upwards with t
      exact (convolution_setIndicator_eq_overlap hA hB hAbdd hBbdd t).symm
    _ = (ContinuousLinearMap.mul ℝ ℝ) (∫ x, setIndicator A x)
          (∫ x, setIndicator (-B) x) :=
      MeasureTheory.integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hiA hiB
    _ = (volume A).toReal * (volume B).toReal := by
      simp only [setIndicator]
      rw [integral_indicator_const (1 : ℝ) hA,
        integral_indicator_const (1 : ℝ) hB.neg]
      simp [measureReal_def, volume.measure_neg]

theorem all_lineAEPeriods_null_or_conull :
    ∀ {X : Set ℝ}, MeasurableSet X →
    (∀ a : ℝ, (a +ᵥ X) =ᵐ[volume] X) →
    volume X = 0 ∨ volume Xᶜ = 0 := by
  intro X hX hperiod
  by_contra hproper
  push Not at hproper
  obtain ⟨A, hAm, hAbdd, hAX, hApos⟩ := exists_boundedPositive_measurable_subset hX hproper.1
  obtain ⟨B, hBm, hBbdd, hBX, hBpos⟩ := exists_boundedPositive_measurable_subset hX.compl hproper.2
  have hzero : ∀ t : ℝ, volume (A ∩ (t +ᵥ B)) = 0 := by
    intro t
    have hcomp : (t +ᵥ Xᶜ) =ᵐ[volume] Xᶜ := by
      have hset : t +ᵥ Xᶜ = (t +ᵥ X)ᶜ := by
        ext x
        simp [mem_vadd_set_iff_neg_vadd_mem]
      rw [hset]
      exact (hperiod t).compl
    have hnull : volume (X ∩ (t +ᵥ Xᶜ)) = 0 := by
      calc
        volume (X ∩ (t +ᵥ Xᶜ)) = volume (X ∩ Xᶜ) :=
          measure_congr
            (Filter.EventuallyEq.inter (Filter.EventuallyEq.refl (ae volume) X) hcomp)
        _ = 0 := by simp
    apply measure_mono_null _ hnull
    rintro x ⟨hxA, hxB⟩
    refine ⟨hAX hxA, ?_⟩
    exact Set.image_mono hBX hxB
  have hint := translateOverlap_integral hAm hBm hAbdd hBbdd
  have hintzero : ∫ t : ℝ, (volume (A ∩ (t +ᵥ B))).toReal = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with t
    simp [hzero t]
  rw [hintzero] at hint
  nlinarith

theorem dense_lineAEPeriods_null_or_conull :
    ∀ {X : Set ℝ}, MeasurableSet X →
    Dense {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} →
    volume X = 0 ∨ volume Xᶜ = 0 := by
  intro X hX hdense
  apply all_lineAEPeriods_null_or_conull hX
  have hclosed := lineAEPeriodSet_isClosed hX
  have huniv : {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} = Set.univ := by
    calc
      {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} =
          closure {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} := hclosed.closure_eq.symm
      _ = Set.univ := dense_iff_closure_eq.mp hdense
  intro a
  have ha : a ∈ {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} := by
    rw [huniv]
    exact Set.mem_univ a
  exact ha

theorem properPeriodicLine_periodGroup_cyclic :
    ∀ {X : Set ℝ},
    MeasurableSet X →
    volume X ≠ 0 →
    volume Xᶜ ≠ 0 →
    (∃ a : ℝ, a ≠ 0 ∧ (a +ᵥ X) =ᵐ[volume] X) →
    ∃! c : ℝ, 0 < c ∧
      ∀ a : ℝ, ((a +ᵥ X) =ᵐ[volume] X ↔ ∃ n : ℤ, a = n • c) := by
  intro X hX hX0 hXc0 hnonzero
  let G : AddSubgroup ℝ := AddAction.aestabilizer ℝ volume X
  have hmem (a : ℝ) : a ∈ G ↔ (a +ᵥ X) =ᵐ[volume] X := Iff.rfl
  rcases AddSubgroup.dense_or_cyclic G with hdense | ⟨d, hd⟩
  · change Dense {a : ℝ | (a +ᵥ X) =ᵐ[volume] X} at hdense
    have hnull := dense_lineAEPeriods_null_or_conull hX hdense
    exact (hnull.elim hX0 hXc0).elim
  · obtain ⟨p, hp0, hp⟩ := hnonzero
    have hpG : p ∈ G := (hmem p).mpr hp
    have hd0 : d ≠ 0 := by
      intro hd0
      subst d
      rw [hd, AddSubgroup.mem_closure_singleton] at hpG
      obtain ⟨n, hn⟩ := hpG
      apply hp0
      simpa using hn.symm
    have hGabs : G = AddSubgroup.zmultiples |d| := by
      calc
        G = AddSubgroup.closure {d} := hd
        _ = AddSubgroup.zmultiples d := (AddSubgroup.zmultiples_eq_closure d).symm
        _ = AddSubgroup.zmultiples |d| := by
          rcases lt_or_gt_of_ne hd0 with hneg | hpos
          · rw [abs_of_neg hneg, AddSubgroup.zmultiples_neg]
          · rw [abs_of_pos hpos]
    have hcharacterization (a : ℝ) :
        ((a +ᵥ X) =ᵐ[volume] X ↔ ∃ n : ℤ, a = n • |d|) := by
      rw [← hmem, hGabs, AddSubgroup.mem_zmultiples_iff]
      exact exists_congr fun n ↦ eq_comm
    refine ⟨|d|, ⟨abs_pos.mpr hd0, hcharacterization⟩, ?_⟩
    intro c hc
    rcases hc with ⟨hcpos, hcchar⟩
    exact (positive_cyclic_generator_unique (abs_pos.mpr hd0) hcpos fun a ↦
      (hcharacterization a).symm.trans (hcchar a)).symm


end Tiling.AxisParallel.Terminal
